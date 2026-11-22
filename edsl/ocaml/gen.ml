(* gen.exe <示例集> <输出目录>: 对一组插件运行三个解释, 写出 <示例集>.{ast,analysis,js}.
   分析出错时不生成 JS, 退出码为 1. *)
open Interp

module type SET = functor (S : Sym.S) -> sig val plugins : S.plugin list end

let run (module M : SET) base out =
  let module A = M (Ast) in
  let module J = M (Js) in
  let module N = M (Ana) in
  let write ext s =
    let oc = open_out_bin (Filename.concat out (base ^ ext)) in
    output_string oc s; close_out oc
  in
  let results = List.map Ana.analyze N.plugins in
  let link = Ana.link_check N.plugins in
  let analysis = String.concat "\n" (List.map (fun (l, _, _) -> l) results @ link) ^ "\n" in
  write ".analysis" analysis;
  write ".ast" (String.concat "\n" (List.map Ast.render A.plugins) ^ "\n");
  print_string analysis;
  let bad = List.exists (fun (_, e, _) -> e <> []) results
            || List.exists (fun l -> String.length l >= 5 && String.sub l 0 5 = "cycle") link in
  if bad then (prerr_endline "分析未通过, 不生成 JS"; exit 1)
  else write ".js" (Js.render_module J.plugins)

let () =
  let set = Sys.argv.(1) and out = Sys.argv.(2) in
  let m : (module SET) =
    match set with
    | "examples" -> (module Examples.Make)
    | "partial" -> (module Negative.Partial)
    | "cycle" -> (module Negative.Cycle)
    | s -> failwith ("unknown set " ^ s)
  in
  run m set out
