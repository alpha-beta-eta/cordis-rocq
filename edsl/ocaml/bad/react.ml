(* 反应中提供键: 类型错误 (反应的 'p 是 no_provide) *)
open Keys
module M (S : Sym.S) = struct
  open S
  let late =
    plugin ~name:"late" ~inject:[] ~optional:[] ~provide:[ api ]
      (provide api (record []) (on "tick" (fun _ -> provide api (record []) done_) done_)
        : ([ `Api ], _, [ `Api ]) prog)
end
