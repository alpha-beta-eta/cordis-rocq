(* 想在宿主层面检查读到的值. value 是抽象的, 模式匹配和 if 都写不出来;
   但 OCaml 的多态相等 (=) 对抽象类型照样能用, 这是参数性的一个漏洞:
   这个文件能通过类型检查, 只在生成时因比较函数值而抛异常. *)
open Keys
module M (S : Sym.S) = struct
  open S
  let peek =
    plugin ~name:"peek" ~inject:[] ~optional:[ config ] ~provide:[]
      (read_opt config (fun cfg -> if cfg = str "x" then fail "no" else done_)
        : (_, [ `Config ], _) prog)
end
let () = let module A = M (Interp.Ast) in print_endline (Interp.Ast.render A.peek)
