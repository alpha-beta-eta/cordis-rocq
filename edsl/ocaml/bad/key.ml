(* 访问未声明的键: 类型错误 *)
open Keys
module M (S : Sym.S) = struct
  open S
  let sneaky =
    plugin ~name:"sneaky" ~inject:[ tools ] ~optional:[] ~provide:[]
      (put agents (record [ ("name", str "x") ]) done_ : ([ `Tools ], _, _) prog)
end
