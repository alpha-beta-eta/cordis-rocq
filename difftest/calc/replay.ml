(* Replay Cordis traces on the extracted calculus.

   Usage: replay <trace.txt>   (the output of cordis/run.mjs)

   For every case, each Cordis event is mapped to the calculus labels it
   corresponds to; [step] (extracted from Calculus.v) must accept each of
   them, and afterwards the calculus state must agree with the snapshot that
   came with the event: every fiber's lifecycle state, and every binding's
   owner and registry contents. Where Cordis settles, the calculus must be
   quiet (no lifecycle rule enabled). The first disagreement ends the case.

   Output, one line per case:  <id> ok
                               <id> diverge <event#> <kind> <detail>

   The mapping (see README.md for why each line is sound):
     create (top level)      OInsert c
     create (child of p)     LStep p          (p's next instruction is PSpawn c)
     op ok / op refused      LStep n          (next instruction POp k (Register x v))
     provide                 LStep n          (next instruction PProvide k)
     LOADING -> ACTIVE       LStep n          (PDone)
     LOADING -> UNLOADING    LStep n if the load failed, else ORestart n if a
                             restart or reset is pending, else LDivert n
     ACTIVE -> UNLOADING     ORestart n if pending, else LLeave n
     undo / withdraw         LUndo n          (head of n's accumulator is that item)
     UNLOADING -> X          LUnloaded n, then LBegin n (X = LOADING) or
                             LRemove n (X = DISPOSED)
     PENDING -> LOADING      LBegin n
     FAILED -> PENDING/LOADING  OReset n (then LBegin n)
     uid cleared (disposal began): ODispose n for a top-level fiber,
                             LRetireChild p for a child of p
   and after every event, an Unloading fiber whose head is USpawn m with m
   already removed takes its LUndo (Cordis has no event for it). *)

open Calculus

exception Diverge of string * string

type instr = IOp of int * int * int | IProv of int | ISpawn of int | IFail

let split_on c s = List.filter (fun x -> x <> "") (String.split_on_char c s)
let ints s = if s = "-" then [] else List.map int_of_string (split_on ',' s)

let parse_instr s =
  match split_on '.' s with
  | [ "op"; k; x; v ] -> IOp (int_of_string k, int_of_string x, int_of_string v)
  | [ "provide"; k ] -> IProv (int_of_string k)
  | [ "spawn"; c ] -> ISpawn (int_of_string c)
  | [ "fail" ] -> IFail
  | _ -> failwith ("bad instruction " ^ s)

let rec prog_of = function
  | [] -> ddone
  | IOp (k, x, v) :: r -> dop k x v (prog_of r)
  | IProv k :: r -> dprovide k [] (prog_of r)
  | ISpawn c :: r -> dspawn c (prog_of r)
  | IFail :: _ -> dfail

let show_label = function
  | OInsert c -> Printf.sprintf "OInsert(c%d)" c
  | ODispose n -> Printf.sprintf "ODispose(%d)" n
  | OReset n -> Printf.sprintf "OReset(%d)" n
  | LBegin n -> Printf.sprintf "LBegin(%d)" n
  | LStep n -> Printf.sprintf "LStep(%d)" n
  | LDivert n -> Printf.sprintf "LDivert(%d)" n
  | LLeave n -> Printf.sprintf "LLeave(%d)" n
  | LUndo n -> Printf.sprintf "LUndo(%d)" n
  | LRetireChild n -> Printf.sprintf "LRetireChild(%d)" n
  | LUnloaded n -> Printf.sprintf "LUnloaded(%d)" n
  | LRemove n -> Printf.sprintf "LRemove(%d)" n
  | OReact (n, i) -> Printf.sprintf "OReact(%d,%d)" n i
  | ORestart n -> Printf.sprintf "ORestart(%d)" n

(* One case being replayed. Cordis fibers are numbered by creation; [name]
   maps that number to the calculus name. *)
type rs = {
  comps : (int, dComp) Hashtbl.t;
  mutable gamma : dState;
  name : (int, int) Hashtbl.t;
  id : (int, int) Hashtbl.t;      (* calculus name -> Cordis number *)
  pending : (int, unit) Hashtbl.t; (* restart or reset requested, not yet visible *)
  mutable keys : int list;
  mutable xs : int list;
}

let prog r c = Hashtbl.find r.comps c
let fiber r n = r.gamma.fibers n
let name_of r i =
  match Hashtbl.find_opt r.name i with
  | Some n -> n
  | None -> raise (Diverge ("unknown-fiber", string_of_int i))
let id_of r n = match Hashtbl.find_opt r.id n with Some i -> string_of_int i | None -> "?"

let step r l why =
  match dstep (prog r) r.gamma l with
  | Some g -> r.gamma <- g
  | None -> raise (Diverge ("disabled", Printf.sprintf "%s (%s)" (show_label l) why))

let life_of r n = match fiber r n with Some f -> Some f.life0 | None -> None

let tag = function
  | None -> "DISPOSED"
  | Some (Inactive None) -> "PENDING"
  | Some (Inactive (Some _)) -> "FAILED"
  | Some (Loading _) -> "LOADING"
  | Some (Active _) -> "ACTIVE"
  | Some (Unloading _) -> "UNLOADING"

let acc_head r n =
  match life_of r n with
  | Some (Unloading (u :: _, _, _)) -> Some u
  | _ -> None

let show_undo r = function
  | UOp (k, _, tok, _) ->
      Printf.sprintf "UOp(k%d,x%s)" k
        (match dop_name r.gamma tok with Some x -> string_of_int x | None -> "?")
  | UProv (k, _) -> Printf.sprintf "UProv(k%d)" k
  | USpawn m -> Printf.sprintf "USpawn(%s)" (id_of r m)

let next_instr r n =
  match life_of r n with
  | Some (Loading (p, _, _)) -> Some (dinstr p)
  | _ -> None

let show_instr = function
  | Some (0, _) -> "PDone"
  | Some (1, _) -> "PFail"
  | Some (2, [ k; x; v ]) -> Printf.sprintf "POp(k%d,%d:=%d)" k x v
  | Some (3, [ k ]) -> Printf.sprintf "PProvide(k%d)" k
  | Some (4, [ c ]) -> Printf.sprintf "PSpawn(c%d)" c
  | Some _ -> "?"
  | None -> "(not loading)"

let expect_instr r n want what =
  let got = next_instr r n in
  if got <> Some want then
    raise (Diverge ("instr", Printf.sprintf "Cordis %s on %s; calculus next is %s" what (id_of r n) (show_instr got)))

(* LUndo for parents whose head is a spawn item of a removed child. *)
let rec drain r =
  let progress = ref false in
  List.iter
    (fun n ->
      match acc_head r n with
      | Some (USpawn m) when fiber r m = None ->
          step r (LUndo n) "spawn item of a removed child";
          progress := true
      | _ -> ())
    (names _UU03a3_R r.gamma);
  if !progress then drain r

(* Snapshot: "F 0=ACTIVE 1=UNLOADING! ..." and "B 0=1:5/-" *)
type snap = { fs : (int * string * bool) list; bs : (int * int * string list) list }

let parse_snap parts =
  let fs = ref [] and bs = ref [] and mode = ref ' ' in
  List.iter
    (fun w ->
      match w with
      | "|" -> ()
      | "F" -> mode := 'F'
      | "B" -> mode := 'B'
      | _ -> (
          match (!mode, split_on '=' w) with
          | 'F', [ i; st ] ->
              let gone = String.length st > 0 && st.[String.length st - 1] = '!' in
              let st = if gone then String.sub st 0 (String.length st - 1) else st in
              fs := (int_of_string i, st, gone) :: !fs
          | 'B', [ k; rest ] -> (
              match split_on ':' rest with
              | [ o; vals ] -> bs := (int_of_string k, int_of_string o, split_on '/' vals) :: !bs
              | _ -> failwith ("bad binding " ^ w))
          | _ -> failwith ("bad snapshot word " ^ w)))
    parts;
  { fs = List.rev !fs; bs = List.rev !bs }

(* Cordis began disposing a fiber (its uid is cleared). *)
let sync_disposal r snap =
  List.iter
    (fun (i, _, gone) ->
      if gone then
        match Hashtbl.find_opt r.name i with
        | None -> ()
        | Some n -> (
            match fiber r n with
            | Some f when not f.disposed ->
                (match f.parent with
                | None -> step r (ODispose n) "Cordis began disposing it"
                | Some p ->
                    let head = acc_head r p in
                    if head <> Some (USpawn n) then
                      raise
                        (Diverge
                           ( "retire-early",
                             Printf.sprintf "Cordis retires child %d while parent %s's next undo is %s" i (id_of r p)
                               (match head with Some u -> show_undo r u | None -> tag (life_of r p)) ));
                    step r (LRetireChild p) "Cordis began disposing the child");
                (* A fiber that never loaded has nothing to undo. The calculus
                   removes it here; Cordis may still report it UNLOADING for a
                   while (dsh drains effects registered before activation, the
                   upstream removes it at once). See compare_state. *)
                (match life_of r n with
                | Some (Inactive _) when dstep (prog r) r.gamma (LRemove n) <> None ->
                    step r (LRemove n) "disposal of a fiber that never loaded"
                | _ -> ())
            | _ -> ()))
    snap.fs

let compare_state r snap =
  List.iter
    (fun (i, st, gone) ->
      let n = name_of r i in
      let calc = tag (life_of r n) in
      let ok =
        calc = st
        (* Cordis passes a disposed fiber that never loaded through UNLOADING
           (draining effects registered before activation); the calculus
           removes it straight from Inactive (see sync_disposal). *)
        || (gone && st = "UNLOADING" && List.mem calc [ "PENDING"; "FAILED"; "DISPOSED" ])
      in
      if not ok then raise (Diverge ("fiber-state", Printf.sprintf "fiber %d: Cordis %s, calculus %s" i st calc)))
    snap.fs;
  List.iter
    (fun k ->
      let cordis = List.find_opt (fun (k', _, _) -> k' = k) snap.bs in
      let calc = dbinding r.gamma k r.xs in
      let show_vals vs = String.concat "/" (List.map (function Some v -> string_of_int v | None -> "-") vs) in
      match (cordis, calc) with
      | None, None -> ()
      | Some (_, o, vals), Some (o', vals') ->
          let o' = id_of r o' in
          let vals' = if r.xs = [] then [ "." ] else String.split_on_char '/' (show_vals vals') in
          if string_of_int o <> o' || vals <> vals' then
            raise
              (Diverge
                 ( "binding",
                   Printf.sprintf "key %d: Cordis %d:%s, calculus %s:%s" k o (String.concat "/" vals) o'
                     (String.concat "/" vals') ))
      | Some (_, o, _), None -> raise (Diverge ("binding", Printf.sprintf "key %d: Cordis bound by %d, calculus unbound" k o))
      | None, Some (o', _) ->
          raise (Diverge ("binding", Printf.sprintf "key %d: Cordis unbound, calculus bound by %s" k (id_of r o'))))
    r.keys

(* LUndo, naming the guard when it is what blocks the step. *)
let undo r n what =
  (match life_of r n with
  | Some (Unloading (acc, _, _)) when held _UU03a3_R r.gamma n acc ->
      raise
        (Diverge
           ("guard", Printf.sprintf "Cordis %s while another installed fiber still resolves a provision of the unloading fiber" what))
  | _ -> ());
  step r (LUndo n) what

let event r words snap =
  sync_disposal r snap;
  (match words with
  | [ "create"; i; c; "-" ] ->
      let i = int_of_string i and c = int_of_string c in
      let n = r.gamma.next in
      (match dstep (prog r) r.gamma (OInsert c) with
      | Some g -> r.gamma <- g
      | None -> raise (Diverge ("insert-refused", Printf.sprintf "Cordis accepts fiber %d (c%d); OInsert is disabled (provider conflict)" i c)));
      Hashtbl.replace r.name i n;
      Hashtbl.replace r.id n i
  | [ "create"; i; c; p ] ->
      let i = int_of_string i and c = int_of_string c and p = name_of r (int_of_string p) in
      expect_instr r p (4, [ c ]) (Printf.sprintf "spawns c%d" c);
      let n = r.gamma.next in
      step r (LStep p) "spawn";
      Hashtbl.replace r.name i n;
      Hashtbl.replace r.id n i
  | [ "op"; i; k; x; v; ok ] ->
      let n = name_of r (int_of_string i) in
      let k = int_of_string k and x = int_of_string x and v = int_of_string v in
      expect_instr r n (2, [ k; x; v ]) (Printf.sprintf "registers %d:=%d on k%d" x v k);
      (* A refused operation fails the load in one calculus step; in Cordis the
         exception still has to leave apply, and the fiber stays LOADING until
         then. The step is taken at that status event. *)
      if ok = "1" then step r (LStep n) "operation"
  | [ "provide"; i; k ] ->
      let n = name_of r (int_of_string i) in
      let k = int_of_string k in
      expect_instr r n (3, [ k ]) (Printf.sprintf "provides k%d" k);
      step r (LStep n) "provide"
  | [ "undo"; i; k; x ] -> (
      let n = name_of r (int_of_string i) in
      let k = int_of_string k and x = int_of_string x in
      match acc_head r n with
      | Some (UOp (k', _, tok, _)) when k' = k && dop_name r.gamma tok = Some x -> undo r n (Printf.sprintf "undoes x%d" x)
      | h ->
          raise
            (Diverge
               ( "undo-order",
                 Printf.sprintf "Cordis undoes UOp(k%d,x%d) of %s; calculus next undo is %s" k x i
                   (match h with Some u -> show_undo r u | None -> tag (life_of r n)) )))
  | [ "withdraw"; i; k ] -> (
      let n = name_of r (int_of_string i) in
      let k = int_of_string k in
      match acc_head r n with
      | Some (UProv (k', _)) when k' = k -> undo r n (Printf.sprintf "withdraws k%d" k)
      | h ->
          raise
            (Diverge
               ( "undo-order",
                 Printf.sprintf "Cordis withdraws k%d of %s; calculus next undo is %s" k i
                   (match h with Some u -> show_undo r u | None -> tag (life_of r n)) )))
  | [ "orch"; ("restart" | "reset"); i ] -> Hashtbl.replace r.pending (name_of r (int_of_string i)) ()
  | [ "orch"; "dispose"; _ ] -> ()
  | [ "status"; i; from; to_; err ] -> (
      let n = name_of r (int_of_string i) in
      let pending = Hashtbl.mem r.pending n in
      let consume () = Hashtbl.remove r.pending n in
      match (from, to_) with
      | "PENDING", "LOADING" -> step r (LBegin n) "load starts"
      | "LOADING", "ACTIVE" ->
          expect_instr r n (0, []) "finishes loading";
          step r (LStep n) "load finishes"
      | "LOADING", "UNLOADING" ->
          if err = "1" then (
            (* PFail, a refused POp, or a PProvide of a taken key *)
            step r (LStep n) "load fails";
            match life_of r n with
            | Some (Unloading (_, _, Some _)) -> ()
            | l -> raise (Diverge ("fail", Printf.sprintf "Cordis load of %s failed; calculus is %s" i (tag l))))
          else if pending then (
            consume ();
            step r (ORestart n) "restart while loading")
          else step r (LDivert n) "load abandoned"
      | "ACTIVE", "UNLOADING" ->
          if pending then (
            consume ();
            step r (ORestart n) "restart")
          else step r (LLeave n) "leaves"
      | "UNLOADING", ("PENDING" | "FAILED" | "LOADING" | "DISPOSED") ->
          (match life_of r n with Some (Unloading _) -> step r (LUnloaded n) "unloaded" | _ -> ());
          if to_ = "LOADING" then step r (LBegin n) "reloads";
          if to_ = "DISPOSED" && fiber r n <> None then step r (LRemove n) "removed"
      | ("PENDING" | "FAILED"), "UNLOADING" -> () (* disposal of a fiber that never loaded; see compare_state *)
      | ("PENDING" | "FAILED"), "DISPOSED" -> if fiber r n <> None then step r (LRemove n) "removed"
      | "FAILED", ("PENDING" | "LOADING") ->
          consume ();
          step r (OReset n) "reset";
          if to_ = "LOADING" then step r (LBegin n) "reloads after reset"
      | _ -> raise (Diverge ("transition", Printf.sprintf "fiber %s: %s -> %s has no mapping" i from to_)))
  | _ -> failwith ("bad event " ^ String.concat " " words));
  drain r;
  compare_state r snap

let settled r =
  (* Requests that never became visible (restart of a PENDING fiber) lapse. *)
  Hashtbl.reset r.pending;
  match denabled (prog r) r.gamma with
  | [] -> ()
  | ls -> raise (Diverge ("not-quiet", "Cordis settled; calculus can still take " ^ String.concat "," (List.map show_label ls)))

let () =
  let ic = open_in Sys.argv.(1) in
  let fresh () =
    { comps = Hashtbl.create 8; gamma = dinit; name = Hashtbl.create 8; id = Hashtbl.create 8;
      pending = Hashtbl.create 4; keys = []; xs = [] }
  in
  let r = ref (fresh ()) and id = ref "" and nev = ref 0 and verdict = ref None in
  (try
     while true do
       let line = input_line ic in
       let words = split_on ' ' line in
       match words with
       | [ "case"; i ] ->
           r := fresh ();
           id := i;
           nev := 0;
           verdict := None
       | [ "comp"; c; deps; provs; body ] ->
           let body = if body = "-" then [] else List.map parse_instr (split_on ';' body) in
           Hashtbl.replace !r.comps (int_of_string c) (dcomp (ints deps) (ints provs) (prog_of body))
       | [ "keys"; ks ] -> !r.keys <- ints ks
       | [ "names"; xs ] -> !r.xs <- ints xs
       | "end" :: _ ->
           print_endline (match !verdict with None -> !id ^ " ok" | Some v -> !id ^ " " ^ v)
       | _ when !verdict <> None -> ()
       | _ -> (
           incr nev;
           try
             match words with
             | "ev" :: rest ->
                 let rec cut acc = function
                   | "|" :: tl -> (List.rev acc, "|" :: tl)
                   | w :: tl -> cut (w :: acc) tl
                   | [] -> (List.rev acc, [])
                 in
                 let ev, snapw = cut [] rest in
                 event !r ev (parse_snap snapw)
             | [ "settled" ] -> settled !r
             | [ "stuck" ] -> raise (Diverge ("stuck", "Cordis did not settle"))
             | "throw" :: op :: i :: why -> (
                 (* Cordis refused an orchestration request; the calculus must refuse it too. *)
                 let l =
                   match op with
                   | "restart" -> Some (ORestart (name_of !r (int_of_string i)))
                   | "reset" -> Some (OReset (name_of !r (int_of_string i)))
                   | "dispose" -> Some (ODispose (name_of !r (int_of_string i)))
                   | _ -> None
                 in
                 (match l with Some l -> Hashtbl.remove !r.pending (match l with ORestart n | OReset n | ODispose n -> n | _ -> -1) | None -> ());
                 match l with
                 | Some l when dstep (prog !r) !r.gamma l = None -> ()
                 | _ -> raise (Diverge ("throw", Printf.sprintf "Cordis refuses %s %s (%s); the calculus accepts it" op i (String.concat " " why))))
             | _ -> failwith ("bad line " ^ line)
           with Diverge (kind, detail) -> verdict := Some (Printf.sprintf "diverge %d %s %s" !nev kind detail))
     done
   with End_of_file -> ());
  close_in ic
