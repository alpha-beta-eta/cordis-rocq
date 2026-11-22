(* 类型检查通过, 但分析器或链接期检查拒绝的插件 (与 ../racket/bad/{partial,cycle}.rkt 相同) *)
open Keys

module Partial (S : Sym.S) = struct
  open S
  open Sym.Sugar (S)
  (* 只在某个分支提供键: 完整提供不成立 *)
  let partial =
    plugin ~name:"partial" ~inject:[] ~optional:[ config ] ~provide:[ api ]
      (read_opt config (fun cfg -> when_ (present cfg) (provide api (record [ ("v", int 1) ]) done_))
        : (_, [ `Config ], [ `Api ]) prog)
  let plugins = [ partial ]
end

module Cycle (S : Sym.S) = struct
  open S
  (* 依赖成环 *)
  let a = plugin ~name:"a" ~inject:[ y ] ~optional:[] ~provide:[ x ]
            (provide x (record []) done_ : ([ `X | `Y ], _, [ `X ]) prog)
  let b = plugin ~name:"b" ~inject:[ x ] ~optional:[] ~provide:[ y ]
            (provide y (record []) done_ : ([ `X | `Y ], _, [ `Y ]) prog)
  let plugins = [ a; b ]
end
