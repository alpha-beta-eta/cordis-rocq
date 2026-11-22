(* sym.ml —— 插件 EDSL 的签名 (tagless final).

   与 Racket 版的不同在于纪律由类型保证:
   - 键带一个多态变体的幻影类型. 程序的类型 ('a, 'o, 'p) prog 记下可访问的键 'a (d ∪ p),
     可选依赖 'o, 可提供的键 'p. 插件把它们标注成闭的变体, 用到别的键就是类型错误.
   - 反应的程序的 'p 是 no_provide, 任何键都与它不合一, 所以反应中不能 provide.
   - 程序对 value 是参数化的: 插件写在 functor (S : S) 里, 拿不到 value 的表示, 检查不了操作结果
     (参数性). *)

module Key : sig
  type +'k t
  val v : string -> 'k t
  val name : 'k t -> string
end = struct
  type 'k t = string
  let v s = s
  let name s = s
end

type no_provide = [ `No_provide_in_reaction ]

module type S = sig
  type ('a, 'o, 'p) prog
  type value
  type plugin

  val done_ : ('a, 'o, 'p) prog
  val fail : string -> ('a, 'o, 'p) prog
  val read : 'a Key.t -> (value -> ('a, 'o, 'p) prog) -> ('a, 'o, 'p) prog
  val read_opt : 'o Key.t -> (value -> ('a, 'o, 'p) prog) -> ('a, 'o, 'p) prog
  val put : 'a Key.t -> value -> ('a, 'o, 'p) prog -> ('a, 'o, 'p) prog
  val provide : 'p Key.t -> value -> ('a, 'o, 'p) prog -> ('a, 'o, 'p) prog
  val spawn : plugin -> ('a, 'o, 'p) prog -> ('a, 'o, 'p) prog
  val on : string -> (value -> ('a, 'o, no_provide) prog) -> ('a, 'o, 'p) prog -> ('a, 'o, 'p) prog
  val resource : string -> value list -> ('a, 'o, 'p) prog -> ('a, 'o, 'p) prog
  val if_ : value -> ('a, 'o, 'p) prog -> ('a, 'o, 'p) prog -> ('a, 'o, 'p) prog
  val seq : ('a, 'o, 'p) prog -> ('a, 'o, 'p) prog -> ('a, 'o, 'p) prog

  val str : string -> value
  val int : int -> value
  val bool : bool -> value
  val field : value -> string -> value
  val record : (string * value) list -> value
  val present : value -> value
  val js : string -> value list -> value
  val eq : value -> value -> value
  val not_ : value -> value

  val plugin :
    name:string -> inject:'a Key.t list -> optional:'o Key.t list -> provide:'p Key.t list ->
    ('a, 'o, 'p) prog -> plugin
end

(* 与 Racket 版的 when 展开方式相同, 以便两边的 AST 逐字一致 *)
module Sugar (S : S) = struct
  open S
  let when_ c p = if_ c p done_
  let ( >> ) a b = seq a b
end

(* 生成名字的状态, 按渲染顺序 (从左到右, 深度优先) 分配 *)
type gen = { mutable vars : int; mutable labels : int }
let new_gen () = { vars = 0; labels = 0 }
let fresh_var g = g.vars <- g.vars + 1; Printf.sprintf "x%d" g.vars
let fresh_label g = g.labels <- g.labels + 1; Printf.sprintf "L%d" g.labels

let json_str s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter (function '"' -> Buffer.add_string b "\\\"" | '\\' -> Buffer.add_string b "\\\\"
                      | c -> Buffer.add_char b c) s;
  Buffer.add_char b '"';
  Buffer.contents b
