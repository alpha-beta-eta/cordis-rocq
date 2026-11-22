(* 键. 'k 是协变的, 所以这些定义在宽松值限制下仍然是多态的. *)
open Sym
let tools : [> `Tools ] Key.t = Key.v "tools"
let config : [> `Config ] Key.t = Key.v "config"
let api : [> `Api ] Key.t = Key.v "api"
let x : [> `X ] Key.t = Key.v "x"
let y : [> `Y ] Key.t = Key.v "y"
let agents : [> `Agents ] Key.t = Key.v "agents"
