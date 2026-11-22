(* interp.ml —— 三个解释: 初始 AST, JS 生成, 静态分析. 输出格式与 Racket 版逐字相同. *)

open Sym

(* ------------------------------------------------------------------ *)
(* 解释 1: 初始 AST *)

type sx = A of string | S of string | I of int | B of bool | L of sx list

let rec sx_to_string = function
  | A a -> a
  | S s -> json_str s
  | I n -> string_of_int n
  | B b -> if b then "true" else "false"
  | L l -> "(" ^ String.concat " " (List.map sx_to_string l) ^ ")"

module Ast = struct
  type ('a, 'o, 'p) prog = gen -> sx
  type value = gen -> sx
  type plugin = { name : string; inject : string list; optional : string list;
                  provide : string list; body : gen -> sx }

  let bind g k =
    let x = fresh_var g in
    let b = k (fun _ -> L [ A "var"; A x ]) g in
    (x, b)

  let done_ _ = L [ A "done" ]
  let fail m _ = L [ A "fail"; S m ]
  let read k kont g = let x, b = bind g kont in L [ A "read"; S (Key.name k); A x; b ]
  let read_opt k kont g = let x, b = bind g kont in L [ A "read?"; S (Key.name k); A x; b ]
  let put k e p g = let e = e g in let p = p g in L [ A "put"; S (Key.name k); e; p ]
  let provide k e p g = let e = e g in let p = p g in L [ A "provide"; S (Key.name k); e; p ]
  let spawn c p g = L [ A "spawn"; S c.name; p g ]
  let on ev kont p g = let x, h = bind g kont in let p = p g in L [ A "on"; S ev; A x; h; p ]
  let resource path args p g =
    let args = List.map (fun a -> a g) args in
    let p = p g in
    L [ A "resource"; S path; L args; p ]
  let if_ c a b g = let c = c g in let a = a g in let b = b g in L [ A "if"; c; a; b ]
  let seq a b g = let a = a g in let b = b g in L [ A "seq"; a; b ]
  let str s _ = L [ A "lit"; S s ]
  let int n _ = L [ A "lit"; I n ]
  let bool b _ = L [ A "lit"; B b ]
  let field e f g = L [ A "field"; e g; S f ]
  let record kvs g = L (A "record" :: List.map (fun (k, e) -> L [ S k; e g ]) kvs)
  let present e g = L [ A "present"; e g ]
  let js path args g = L (A "js" :: S path :: List.map (fun a -> a g) args)
  let eq a b g = let a = a g in let b = b g in L [ A "eq"; a; b ]
  let not_ a g = L [ A "not"; a g ]

  let plugin ~name ~inject ~optional ~provide body =
    { name; inject = List.map Key.name inject; optional = List.map Key.name optional;
      provide = List.map Key.name provide; body }

  let render p =
    sx_to_string
      (L [ A "plugin"; S p.name; L (A "inject" :: List.map (fun s -> S s) p.inject);
           L (A "optional" :: List.map (fun s -> S s) p.optional);
           L (A "provide" :: List.map (fun s -> S s) p.provide); p.body (new_gen ()) ])
end

(* ------------------------------------------------------------------ *)
(* 解释 2: JS 生成 *)

let ln ind s = String.make (2 * ind) ' ' ^ s
let js_ident s = String.map (fun c -> if c = '-' then '_' else c) s
let js_array ss = "[" ^ String.concat ", " (List.map json_str ss) ^ "]"

module Js = struct
  type ('a, 'o, 'p) prog = gen -> int -> string -> string list
  type value = gen -> string
  type plugin = { name : string; inject : string list; optional : string list;
                  provide : string list; body : gen -> int -> string -> string list }

  let done_ _ ind d = [ ln ind d ]
  let fail m _ ind _ =
    [ ln ind (Printf.sprintf "yield I.fail(%s);" (json_str m)); ln ind "return;" ]
  let read_gen op k kont g ind d =
    let x = fresh_var g in
    ln ind (Printf.sprintf "const %s = yield I.%s(%s);" x op (json_str (Key.name k)))
    :: kont (fun _ -> x) g ind d
  let read k = read_gen "read" k
  let read_opt k = read_gen "readOpt" k
  let put k e p g ind d =
    let s = ln ind (Printf.sprintf "yield I.put(%s, %s);" (json_str (Key.name k)) (e g)) in
    s :: p g ind d
  let provide k e p g ind d =
    let s = ln ind (Printf.sprintf "yield I.provide(%s, %s);" (json_str (Key.name k)) (e g)) in
    s :: p g ind d
  let spawn (c : plugin) p g ind d =
    ln ind (Printf.sprintf "yield I.spawn(%s);" (js_ident c.name)) :: p g ind d
  let on ev kont p g ind d =
    let x = fresh_var g in
    let head = ln ind (Printf.sprintf "yield I.on(%s, function* (%s) {" (json_str ev) x) in
    let h = kont (fun _ -> x) g (ind + 1) "return;" in
    let tail = ln ind "});" in
    let rest = p g ind d in
    (head :: h) @ (tail :: rest)
  let resource path args p g ind d =
    let args = String.concat ", " (List.map (fun a -> a g) args) in
    let s = ln ind (Printf.sprintf "yield I.resource(payload(%s), [%s]);" (json_str path) args) in
    s :: p g ind d
  let if_ c a b g ind d =
    let cs = c g in
    let a = a g (ind + 1) d in
    let b = b g (ind + 1) d in
    [ ln ind (Printf.sprintf "if (%s) {" cs) ] @ a @ [ ln ind "} else {" ] @ b @ [ ln ind "}" ]
  let seq a b g ind d =
    let l = fresh_label g in
    let a = a g (ind + 1) (Printf.sprintf "break %s;" l) in
    let b = b g ind d in
    [ ln ind (l ^ ": {") ] @ a @ [ ln ind "}" ] @ b
  let str s _ = json_str s
  let int n _ = string_of_int n
  let bool b _ = if b then "true" else "false"
  let field e f g = Printf.sprintf "%s[%s]" (e g) (json_str f)
  let record kvs g =
    "{" ^ String.concat ", " (List.map (fun (k, e) -> Printf.sprintf "%s: %s" (json_str k) (e g)) kvs) ^ "}"
  let present e g = Printf.sprintf "(%s !== null)" (e g)
  let js path args g =
    Printf.sprintf "I.lazy(%s, [%s])" (json_str path) (String.concat ", " (List.map (fun a -> a g) args))
  let eq a b g = let a = a g in let b = b g in Printf.sprintf "(%s === %s)" a b
  let not_ a g = Printf.sprintf "(!%s)" (a g)

  let plugin ~name ~inject ~optional ~provide body =
    { name; inject = List.map Key.name inject; optional = List.map Key.name optional;
      provide = List.map Key.name provide; body }

  let render_plugin p =
    [ Printf.sprintf "const %s = {" (js_ident p.name);
      ln 1 (Printf.sprintf "name: %s," (json_str p.name));
      ln 1 (Printf.sprintf "inject: %s," (js_array p.inject));
      ln 1 (Printf.sprintf "optional: %s," (js_array p.optional));
      ln 1 (Printf.sprintf "provide: %s," (js_array p.provide));
      ln 1 "body: function* () {" ]
    @ p.body (new_gen ()) 2 "return;"
    @ [ ln 1 "},"; "};"; "" ]

  let render_module ps =
    String.concat "\n"
      ([ "\"use strict\";"; "// generated by cordis-edsl; do not edit";
         "const { I, payload } = require(\"../../runtime/rt.js\");"; "" ]
       @ List.concat_map render_plugin ps
       @ [ Printf.sprintf "module.exports = { %s };"
             (String.concat ", " (List.map (fun (p : plugin) -> js_ident p.name) ps)); "" ])
end

(* ------------------------------------------------------------------ *)
(* 解释 3: 静态分析. 路径 = 事件列表 * 是否到达 done *)

type ev =
  | Read of string | ReadOpt of string | Put of string | Provide of string
  | Spawn of string | On of string * path list | Resource of string
and path = ev list * bool

module Ana = struct
  type ('a, 'o, 'p) prog = path list
  type value = unit
  type plugin = { name : string; inject : string list; optional : string list;
                  provide : string list; paths : path list }

  let prefix e ps = List.map (fun (es, d) -> (e :: es, d)) ps
  let done_ = [ ([], true) ]
  let fail _ = [ ([], false) ]
  let read k kont = prefix (Read (Key.name k)) (kont ())
  let read_opt k kont = prefix (ReadOpt (Key.name k)) (kont ())
  let put k () p = prefix (Put (Key.name k)) p
  let provide k () p = prefix (Provide (Key.name k)) p
  let spawn (c : plugin) p = prefix (Spawn c.name) p
  let on ev kont p = prefix (On (ev, kont ())) p
  let resource path _ p = prefix (Resource path) p
  let if_ () a b = a @ b
  let seq a b =
    List.concat_map (fun (ea, da) -> if da then List.map (fun (eb, db) -> (ea @ eb, db)) b
                                     else [ (ea, da) ]) a
  let str _ = () let int _ = () let bool _ = ()
  let field () _ = () let record _ = () let present () = ()
  let js _ _ = () let eq () () = () let not_ () = ()

  let plugin ~name ~inject ~optional ~provide paths =
    { name; inject = List.map Key.name inject; optional = List.map Key.name optional;
      provide = List.map Key.name provide; paths }

  let uniq_sorted l = List.sort_uniq compare l

  (* 返回 (报告行, 错误, spawn 的名字) *)
  let analyze p =
    let errors = ref [] and seen = Hashtbl.create 8 in
    let err s = errors := s :: !errors in
    let see kind k = Hashtbl.replace seen kind (k :: (try Hashtbl.find seen kind with Not_found -> [])) in
    let mem k l = List.mem k l in
    let rec walk reacting (es, _) =
      List.iter
        (function
          | Read k -> see "read" k; if not (mem k (p.inject @ p.provide)) then err ("undeclared key " ^ k)
          | ReadOpt k -> see "read?" k; if not (mem k p.optional) then err ("undeclared optional key " ^ k)
          | Put k -> see "put" k; if not (mem k (p.inject @ p.provide)) then err ("undeclared key " ^ k)
          | Provide k ->
              see "provide" k;
              if reacting then err ("provide in reaction " ^ k);
              if not (mem k p.provide) then err ("undeclared provide " ^ k)
          | Spawn n -> see "spawn" n
          | Resource _ -> ()
          | On (_, hs) -> List.iter (walk true) hs)
        es
    in
    List.iter (walk false) p.paths;
    List.iter
      (fun (es, d) ->
        if d then
          let provided = List.filter_map (function Provide k -> Some k | _ -> None) es in
          List.iter
            (fun k ->
              let n = List.length (List.filter (( = ) k) provided) in
              if n = 0 then err ("a path to done misses provide " ^ k)
              else if n > 1 then err ("a path to done provides " ^ k ^ " twice"))
            p.provide)
      p.paths;
    let errs = uniq_sorted !errors in
    let keys kind = uniq_sorted (try Hashtbl.find seen kind with Not_found -> []) in
    let lst kind = "(" ^ String.concat " " (keys kind) ^ ")" in
    let maxlen = List.fold_left (fun m (es, _) -> max m (List.length es)) 0 p.paths in
    let line =
      Printf.sprintf "%s: paths=%d maxlen=%d read=%s read?=%s put=%s provide=%s spawn=%s %s"
        p.name (List.length p.paths) maxlen (lst "read") (lst "read?") (lst "put")
        (lst "provide") (lst "spawn")
        (if errs = [] then "OK" else "ERRORS: " ^ String.concat "; " errs)
    in
    (line, errs, keys "spawn")

  (* 链接期: 有秩 (依赖与 spawn 无环) 与提供冲突 *)
  let link_check ps =
    let by_name n = List.find_opt (fun p -> p.name = n) ps in
    let spawns p = let _, _, s = analyze p in s in
    let succ p =
      uniq_sorted
        (List.filter_map
           (fun q ->
             if List.exists (fun k -> List.mem k (q.inject @ q.optional)) p.provide then Some q.name
             else None)
           ps
        @ spawns p)
    in
    let rank = Hashtbl.create 8 and cycle = ref None in
    let rec take_until n = function [] -> [] | m :: r -> if m = n then [] else m :: take_until n r in
    let rec visit n stack =
      if List.mem n stack then begin
        if !cycle = None then cycle := Some ((n :: List.rev (take_until n stack)) @ [ n ]);
        0
      end
      else
        match Hashtbl.find_opt rank n with
        | Some r -> r
        | None ->
            let r =
              match by_name n with
              | None -> 0
              | Some p -> List.fold_left (fun r m -> max r (1 + visit m (n :: stack))) 0 (succ p)
            in
            Hashtbl.replace rank n r;
            r
    in
    List.iter (fun p -> ignore (visit p.name [])) ps;
    let h = Hashtbl.fold (fun _ r m -> max r m) rank 0 in
    let conflicts =
      List.filter_map
        (fun k ->
          let owners = uniq_sorted (List.filter_map (fun p -> if List.mem k p.provide then Some p.name else None) ps) in
          if List.length owners > 1 then Some (Printf.sprintf "conflict %s: %s" k (String.concat " " owners))
          else None)
        (uniq_sorted (List.concat_map (fun p -> p.provide) ps))
    in
    (match !cycle with
     | Some c -> [ "cycle: " ^ String.concat " -> " c ]
     | None ->
         List.map (fun n -> Printf.sprintf "rank %s = %d" n (h - Hashtbl.find rank n))
           (uniq_sorted (Hashtbl.fold (fun n _ acc -> n :: acc) rank [])))
    @ conflicts
end
