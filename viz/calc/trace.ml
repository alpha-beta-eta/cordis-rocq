(* Run scenarios on the extracted calculus and print the states as JSON.

   Usage: trace <scenarios.txt> > traces.json
          trace -js <scenarios.txt> > traces.js    (window.CORDIS_TRACES = ...)

   Every state in the output is computed by a step function extracted from
   Rocq (viz/Extract.v): the core [step], Admit's [astep], Queue's [qstep]
   or ViewFail's [vstep]. The driver parses the scenario file, builds the
   component table, applies the labels one by one and reads the states; it
   decides nothing itself. A label the step function refuses is recorded as
   refused and leaves the state unchanged.

   Scenario file, one directive per line; '#' starts a comment line; a line
   that starts with whitespace continues the previous directive (for label
   lists, a line break separates labels like a comma):

     scenario <id>
     title <text>
     source <text>
     note <text>                      (repeatable)
     mode core|admit|queue|view       (default for the schedules below)
     key <k> <name>
     comp <c> <name> | deps <k,..|-> | provs <k,..|-> | <instr>; <instr>; ...
         instr: provide <k> [<x>=<v> ...] | op <k> <x> <v> | lookup <k> <x>
                | spawn <c> | fail | done      (a missing final done is added)
     prefix <labels>                  (shared by every schedule)
     schedule <name> [mode=<m>] [extends=<schedule>] [noprefix] [| <labels>]
     compare <schedule> <schedule>    (shown side by side by default)

   Labels: OInsert c, ODispose n, OReset n, ORestart n, OReact n i, LBegin n,
   LStep n, LDivert n, LLeave n, LUndo n, LRetireChild n, LUnloaded n,
   LRemove n; in queue mode also QIns c, QCancel t, QAdmit (OInsert is not a
   queue label); in view mode also VClear n. *)

open Calculus

(* ---------- small helpers ---------- *)

let trim = String.trim
let words s = List.filter (fun w -> w <> "") (String.split_on_char ' ' (trim s))
let split_on c s = List.map trim (String.split_on_char c s)

let ints s =
  if trim s = "-" || trim s = "" then []
  else List.map int_of_string (List.filter (fun x -> x <> "") (split_on ',' s))

let starts_with p s = String.length s >= String.length p && String.sub s 0 (String.length p) = p

let json_string s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter
    (fun c ->
      match c with
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n"
      | c when Char.code c < 0x20 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char b c)
    s;
  Buffer.add_char b '"';
  Buffer.contents b

type json =
  | S of string
  | I of int
  | B of bool
  | Null
  | L of json list
  | O of (string * json) list

let rec emit b = function
  | S s -> Buffer.add_string b (json_string s)
  | I i -> Buffer.add_string b (string_of_int i)
  | B x -> Buffer.add_string b (if x then "true" else "false")
  | Null -> Buffer.add_string b "null"
  | L xs ->
      Buffer.add_char b '[';
      List.iteri (fun i x -> if i > 0 then Buffer.add_char b ','; emit b x) xs;
      Buffer.add_char b ']'
  | O kvs ->
      Buffer.add_char b '{';
      List.iteri
        (fun i (k, v) ->
          if i > 0 then Buffer.add_char b ',';
          Buffer.add_string b (json_string k);
          Buffer.add_char b ':';
          emit b v)
        kvs;
      Buffer.add_char b '}'

let opt f = function Some x -> f x | None -> Null

(* ---------- scenarios ---------- *)

type instr =
  | IProvide of int * (int * int) list
  | IOp of int * int * int
  | ILookup of int * int
  | ISpawn of int
  | IFail
  | IDone

type comp_spec = { c : int; cname : string; deps : int list; provs : int list; body : instr list }

type sched_spec = {
  sname : string;
  smode : string option;
  extends : string option;
  noprefix : bool;
  slabels : string list;
}

type scenario = {
  id : string;
  mutable title : string;
  mutable source : string;
  mutable notes : string list;
  mutable mode : string;
  mutable keys : (int * string) list;
  mutable comps : comp_spec list;
  mutable prefix : string list;
  mutable scheds : sched_spec list;
  mutable compares : (string * string) list;
}

let labels_of s = List.filter (fun x -> x <> "") (split_on ',' s)

let parse_instr s =
  match words s with
  | "provide" :: k :: entries ->
      let entry e =
        match split_on '=' e with
        | [ x; v ] -> (int_of_string x, int_of_string v)
        | _ -> failwith ("bad entry " ^ e)
      in
      IProvide (int_of_string k, List.map entry entries)
  | [ "op"; k; x; v ] -> IOp (int_of_string k, int_of_string x, int_of_string v)
  | [ "lookup"; k; x ] -> ILookup (int_of_string k, int_of_string x)
  | [ "spawn"; c ] -> ISpawn (int_of_string c)
  | [ "fail" ] -> IFail
  | [ "done" ] -> IDone
  | _ -> failwith ("bad instruction: " ^ s)

let parse_comp rest =
  match split_on '|' rest with
  | [ head; deps; provs; body ] ->
      let c, cname =
        match words head with
        | [ c; n ] -> (int_of_string c, n)
        | _ -> failwith ("bad comp head: " ^ head)
      in
      let field name s =
        match words s with
        | n :: v when n = name -> ints (String.concat "" v)
        | _ -> failwith ("expected " ^ name ^ ": " ^ s)
      in
      let body = List.map parse_instr (List.filter (fun x -> x <> "") (split_on ';' body)) in
      { c; cname; deps = field "deps" deps; provs = field "provs" provs; body }
  | _ -> failwith ("bad comp: " ^ rest)

let parse_sched rest =
  let head, labels =
    let cut i = (String.sub rest 0 i, String.sub rest (i + 1) (String.length rest - i - 1)) in
    match (String.index_opt rest '|', String.index_opt rest ',') with
    | Some i, _ | None, Some i -> cut i
    | None, None -> (rest, "")
  in
  match words head with
  | name :: opts ->
      let get k =
        List.find_map
          (fun o ->
            if starts_with (k ^ "=") o then Some (String.sub o (String.length k + 1) (String.length o - String.length k - 1))
            else None)
          opts
      in
      { sname = name; smode = get "mode"; extends = get "extends"; noprefix = List.mem "noprefix" opts;
        slabels = labels_of labels }
  | [] -> failwith "schedule needs a name"

(* Logical lines: continuation lines are joined to the previous one with ','
   (only label lists span lines). *)
let logical_lines text =
  let lines = String.split_on_char '\n' text in
  let lines = List.map (fun l -> if String.length l > 0 && l.[String.length l - 1] = '\r' then String.sub l 0 (String.length l - 1) else l) lines in
  let acc = ref [] in
  List.iter
    (fun l ->
      let t = trim l in
      if t = "" || t.[0] = '#' then ()
      else if (l.[0] = ' ' || l.[0] = '\t') && !acc <> [] then
        acc := (List.hd !acc ^ " , " ^ t) :: List.tl !acc
      else acc := t :: !acc)
    lines;
  List.rev !acc

let parse_file text =
  let out = ref [] in
  let cur = ref None in
  let get () = match !cur with Some s -> s | None -> failwith "directive before 'scenario'" in
  List.iter
    (fun line ->
      let d, rest =
        match String.index_opt line ' ' with
        | Some i -> (String.sub line 0 i, trim (String.sub line i (String.length line - i)))
        | None -> (line, "")
      in
      match d with
      | "scenario" ->
          let s =
            { id = rest; title = rest; source = ""; notes = []; mode = "core"; keys = []; comps = [];
              prefix = []; scheds = []; compares = [] }
          in
          out := s :: !out;
          cur := Some s
      | "title" -> (get ()).title <- rest
      | "source" -> (get ()).source <- rest
      | "note" -> (get ()).notes <- (get ()).notes @ [ rest ]
      | "mode" -> (get ()).mode <- rest
      | "key" -> (
          match words rest with
          | [ k; n ] -> (get ()).keys <- (get ()).keys @ [ (int_of_string k, n) ]
          | _ -> failwith ("bad key: " ^ rest))
      | "comp" -> (get ()).comps <- (get ()).comps @ [ parse_comp rest ]
      | "prefix" -> (get ()).prefix <- (get ()).prefix @ labels_of rest
      | "schedule" -> (get ()).scheds <- (get ()).scheds @ [ parse_sched rest ]
      | "compare" -> (
          match words rest with
          | [ a; b ] -> (get ()).compares <- (get ()).compares @ [ (a, b) ]
          | _ -> failwith ("bad compare: " ^ rest))
      | _ -> failwith ("unknown directive: " ^ d))
    (logical_lines text);
  List.rev !out

(* ---------- the component table ---------- *)

let rec prog_of = function
  | [] | IDone :: _ -> xdone
  | IFail :: _ -> xfail
  | IProvide (k, es) :: r -> xprovide k es (prog_of r)
  | IOp (k, x, v) :: r -> xop k x v (prog_of r)
  | ILookup (k, x) :: r -> xlookup k x (prog_of r)
  | ISpawn c :: r -> xspawn c (prog_of r)

let table sc =
  let tbl = Hashtbl.create 8 in
  List.iter (fun cs -> Hashtbl.replace tbl cs.c (xcomp cs.deps cs.provs (prog_of cs.body))) sc.comps;
  fun c ->
    match Hashtbl.find_opt tbl c with
    | Some x -> x
    | None -> failwith (Printf.sprintf "component %d is not in the table" c)

(* The registry names worth showing: every name a program registers, looks
   up or provides. *)
let reg_names sc =
  let xs = ref [] in
  let add x = if not (List.mem x !xs) then xs := x :: !xs in
  List.iter
    (fun cs ->
      List.iter
        (function
          | IProvide (_, es) -> List.iter (fun (x, _) -> add x) es
          | IOp (_, x, _) | ILookup (_, x) -> add x
          | _ -> ())
        cs.body)
    sc.comps;
  List.sort compare !xs

(* ---------- labels ---------- *)

type xl = Core of xLabel | QI of int | QC of int | QA | VC of int

let parse_label s =
  let n x = int_of_string x in
  match words s with
  | [ "OInsert"; c ] -> Core (OInsert (n c))
  | [ "ODispose"; x ] -> Core (ODispose (n x))
  | [ "OReset"; x ] -> Core (OReset (n x))
  | [ "ORestart"; x ] -> Core (ORestart (n x))
  | [ "OReact"; x; i ] -> Core (OReact (n x, n i))
  | [ "LBegin"; x ] -> Core (LBegin (n x))
  | [ "LStep"; x ] -> Core (LStep (n x))
  | [ "LDivert"; x ] -> Core (LDivert (n x))
  | [ "LLeave"; x ] -> Core (LLeave (n x))
  | [ "LUndo"; x ] -> Core (LUndo (n x))
  | [ "LRetireChild"; x ] -> Core (LRetireChild (n x))
  | [ "LUnloaded"; x ] -> Core (LUnloaded (n x))
  | [ "LRemove"; x ] -> Core (LRemove (n x))
  | [ "QIns"; c ] -> QI (n c)
  | [ "QCancel"; t ] -> QC (n t)
  | [ "QAdmit" ] -> QA
  | [ "VClear"; x ] -> VC (n x)
  | _ -> failwith ("bad label: " ^ s)

let show_core = function
  | OInsert c -> Printf.sprintf "OInsert %d" c
  | ODispose n -> Printf.sprintf "ODispose %d" n
  | OReset n -> Printf.sprintf "OReset %d" n
  | ORestart n -> Printf.sprintf "ORestart %d" n
  | OReact (n, i) -> Printf.sprintf "OReact %d %d" n i
  | LBegin n -> Printf.sprintf "LBegin %d" n
  | LStep n -> Printf.sprintf "LStep %d" n
  | LDivert n -> Printf.sprintf "LDivert %d" n
  | LLeave n -> Printf.sprintf "LLeave %d" n
  | LUndo n -> Printf.sprintf "LUndo %d" n
  | LRetireChild n -> Printf.sprintf "LRetireChild %d" n
  | LUnloaded n -> Printf.sprintf "LUnloaded %d" n
  | LRemove n -> Printf.sprintf "LRemove %d" n

let show = function
  | Core l -> show_core l
  | QI c -> Printf.sprintf "QIns %d" c
  | QC t -> Printf.sprintf "QCancel %d" t
  | QA -> "QAdmit"
  | VC n -> Printf.sprintf "VClear %d" n

(* Orchestrator input or lifecycle step; and the fiber a lifecycle step is about. *)
let kind = function
  | Core (OInsert _ | ODispose _ | OReset _ | ORestart _ | OReact _) | QI _ | QC _ -> "orch"
  | _ -> "life"

let subject = function
  | Core (ODispose n | OReset n | ORestart n | OReact (n, _) | LBegin n | LStep n | LDivert n
         | LLeave n | LUndo n | LRetireChild n | LUnloaded n | LRemove n)
  | VC n -> Some n
  | _ -> None

(* ---------- machines ---------- *)

type mstate = MCore of xState | MQ of xQState | MV of xVState

let core_of = function MCore g -> g | MQ q -> xq_core q | MV v -> xv_core v

let init_of = function
  | "core" | "admit" -> MCore xinit
  | "queue" -> MQ xqinit
  | "view" -> MV xvinit
  | m -> failwith ("unknown mode " ^ m)

let mstep prog mode st l =
  match (mode, st, l) with
  | "core", MCore g, Core l -> Option.map (fun g -> MCore g) (xstep prog g l)
  | "admit", MCore g, Core l -> Option.map (fun g -> MCore g) (xastep prog g l)
  | "queue", MQ q, Core l -> Option.map (fun q -> MQ q) (xqstep prog q (QCore l))
  | "queue", MQ q, QI c -> Option.map (fun q -> MQ q) (xqstep prog q (QIns c))
  | "queue", MQ q, QC t -> Option.map (fun q -> MQ q) (xqstep prog q (QCancel t))
  | "queue", MQ q, QA -> Option.map (fun q -> MQ q) (xqstep prog q QAdmit)
  | "view", MV v, Core l -> Option.map (fun v -> MV v) (xvstep prog v (VCore l))
  | "view", MV v, VC n -> Option.map (fun v -> MV v) (xvstep prog v (VClear n))
  | _ -> failwith (Printf.sprintf "label %s is not a %s label" (show l) mode)

(* The lifecycle labels enabled at a state, in this mode. *)
let enabled prog mode st =
  let g = core_of st in
  let ns = List.init g.next (fun i -> i) in
  let core = List.concat_map (fun n -> List.map (fun l -> Core l) (lifecycle_labels n)) ns in
  let extra =
    match mode with
    | "queue" -> [ QA ]
    | "view" -> List.map (fun n -> VC n) ns
    | _ -> []
  in
  List.filter (fun l -> mstep prog mode st l <> None) (core @ extra)

(* ---------- reading states ---------- *)

let key_name sc k = match List.assoc_opt k sc.keys with Some n -> n | None -> "k" ^ string_of_int k
let comp_name sc c =
  match List.find_opt (fun cs -> cs.c = c) sc.comps with Some cs -> cs.cname | None -> "c" ^ string_of_int c

let show_instr sc (code, args) =
  let k x = key_name sc x in
  match (code, args) with
  | 0, _ -> "done"
  | 1, _ -> "fail"
  | 2, [ kk; x; v ] -> Printf.sprintf "register %s %d↦%d" (k kk) x v
  | 3, [ kk ] -> Printf.sprintf "provide %s" (k kk)
  | 4, [ c ] -> Printf.sprintf "spawn %s" (comp_name sc c)
  | 5, [ kk; x ] -> Printf.sprintf "lookup %s %d" (k kk) x
  | _ -> "?"

let show_err = function EUser -> "EUser" | EOp -> "EOp" | EUnresolved -> "EUnresolved" | EConflict -> "EConflict"

let view_json w = L (List.map (fun (k, p) -> L [ I k; I p ]) w)

let undo_json g = function
  | UOp (k, p, tok, _) ->
      O [ ("kind", S "op"); ("k", I k); ("pid", I p); ("tok", I tok); ("name", opt (fun x -> I x) (xop_name g tok)) ]
  | UProv (k, p) -> O [ ("kind", S "prov"); ("k", I k); ("pid", I p) ]
  | USpawn m -> O [ ("kind", S "spawn"); ("m", I m) ]

let fiber_json sc prog st n (f : (int, int) fiber) =
  let g = core_of st in
  let tag, err, acc, view, rest =
    match f.life0 with
    | Inactive z -> ("Inactive", z, [], None, None)
    | Loading (p, acc, w) -> ("Loading", None, acc, Some w, Some p)
    | Active (acc, w) -> ("Active", None, acc, Some w, None)
    | Unloading (acc, w, z) -> ("Unloading", z, acc, Some w, None)
  in
  let fview = match st with MV v -> [ ("fview", opt view_json (xv_fview v n)) ] | _ -> [] in
  O
    ([ ("n", I n);
       ("comp", I f.comp);
       ("parent", opt (fun p -> I p) f.parent);
       ("disposed", B f.disposed);
       ("life", S tag);
       ("err", opt (fun z -> S (show_err z)) err);
       ("prog", opt (fun p -> L (List.map (fun i -> S (show_instr sc i)) (xlisting 32 p))) rest);
       ("acc", L (List.map (undo_json g) acc));
       ("view", opt view_json view);
       ("target", opt view_json (xtarget prog g n));
       ("held", B (xheld g n)) ]
    @ fview)

let state_json sc prog mode st =
  let g = core_of st in
  let xs = reg_names sc in
  let fibers =
    List.filter_map (fun n -> Option.map (fiber_json sc prog st n) (g.fibers n)) (List.init g.next (fun i -> i))
  in
  let binds =
    List.filter_map
      (fun (k, _) ->
        Option.map
          (fun ((p, o), vs) ->
            let entries = List.filter_map (fun (x, v) -> Option.map (fun v -> L [ I x; I v ]) v) (List.combine xs vs) in
            O [ ("k", I k); ("pid", I p); ("owner", I o); ("entries", L entries) ])
          (xbinding g k xs))
      sc.keys
  in
  let queue = match st with MQ q -> [ ("queue", L (List.map (fun (t, c) -> L [ I t; I c ]) (xq_queue q))) ] | _ -> [] in
  let en = enabled prog mode st in
  O
    ([ ("next", I g.next);
       ("fibers", L fibers);
       ("binds", L binds);
       ("enabled", L (List.map (fun l -> S (show l)) en));
       ("quiet", B (en = [])) ]
    @ queue)

let run_sched sc prog (sp : sched_spec) =
  let mode = match sp.smode with Some m -> m | None -> sc.mode in
  let rec own name =
    match List.find_opt (fun s -> s.sname = name) sc.scheds with
    | Some s -> (match s.extends with Some e -> own e | None -> []) @ s.slabels
    | None -> failwith ("unknown schedule " ^ name)
  in
  let prefix = if sp.noprefix then [] else sc.prefix in
  let labels = prefix @ own sp.sname in
  let st = ref (init_of mode) in
  let states = ref [ state_json sc prog mode !st ] in
  let steps =
    List.map
      (fun s ->
        let l = parse_label s in
        let ok =
          match mstep prog mode !st l with
          | Some st' -> st := st'; true
          | None -> false
        in
        states := state_json sc prog mode !st :: !states;
        O [ ("label", S (show l)); ("ok", B ok); ("kind", S (kind l)); ("subject", opt (fun n -> I n) (subject l)) ])
      labels
  in
  O
    [ ("name", S sp.sname);
      ("mode", S mode);
      ("prefix", I (List.length prefix));
      ("steps", L steps);
      ("states", L (List.rev !states)) ]

let instr_text sc = function
  | IProvide (k, []) -> Printf.sprintf "provide %s" (key_name sc k)
  | IProvide (k, es) ->
      Printf.sprintf "provide %s {%s}" (key_name sc k)
        (String.concat ", " (List.map (fun (x, v) -> Printf.sprintf "%d↦%d" x v) es))
  | IOp (k, x, v) -> Printf.sprintf "register %s %d↦%d" (key_name sc k) x v
  | ILookup (k, x) -> Printf.sprintf "lookup %s %d" (key_name sc k) x
  | ISpawn c -> Printf.sprintf "spawn %s" (comp_name sc c)
  | IFail -> "fail"
  | IDone -> "done"

let scenario_json sc =
  let prog = table sc in
  let body cs =
    let b = List.map (instr_text sc) cs.body in
    match List.rev cs.body with IFail :: _ | IDone :: _ -> b | _ -> b @ [ "done" ]
  in
  O
    [ ("id", S sc.id);
      ("title", S sc.title);
      ("source", S sc.source);
      ("notes", L (List.map (fun s -> S s) sc.notes));
      ("keys", L (List.map (fun (k, n) -> O [ ("k", I k); ("name", S n) ]) sc.keys));
      ( "comps",
        L
          (List.map
             (fun cs ->
               O
                 [ ("c", I cs.c);
                   ("name", S cs.cname);
                   ("deps", L (List.map (fun k -> I k) cs.deps));
                   ("provs", L (List.map (fun k -> I k) cs.provs));
                   ("body", L (List.map (fun s -> S s) (body cs))) ])
             sc.comps) );
      ("schedules", L (List.map (run_sched sc prog) sc.scheds));
      ("compare", L (List.map (fun (a, b) -> L [ S a; S b ]) sc.compares)) ]

let () =
  let js, file =
    match Array.to_list Sys.argv with
    | [ _; "-js"; f ] -> (true, f)
    | [ _; f ] -> (false, f)
    | _ -> prerr_endline "usage: trace [-js] <scenarios.txt>"; exit 2
  in
  let ic = open_in_bin file in
  let text = really_input_string ic (in_channel_length ic) in
  close_in ic;
  let b = Buffer.create 65536 in
  emit b (L (List.map scenario_json (parse_file text)));
  if js then print_string "window.CORDIS_TRACES = ";
  print_string (Buffer.contents b);
  if js then print_string ";";
  print_newline ()
