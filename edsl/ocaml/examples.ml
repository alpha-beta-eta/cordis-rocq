(* 示例插件, 与 ../racket/examples.rkt 是同一组. 每个插件把它的键集标注成闭的变体:
   ([可访问的键], [可选依赖], [可提供的键]) prog; 用到别的键是类型错误. *)
open Keys

module Make (S : Sym.S) = struct
  open S
  open Sym.Sugar (S)

  let tools_host =
    plugin ~name:"tools-host" ~inject:[] ~optional:[] ~provide:[ tools ]
      (provide tools (record [ ("kind", str "tools") ]) done_ : ([ `Tools ], _, [ `Tools ]) prog)

  let config =
    plugin ~name:"config" ~inject:[] ~optional:[] ~provide:[ config ]
      (provide config (record [ ("enabled", bool true); ("prefix", str "pet") ]) done_
        : ([ `Config ], _, [ `Config ]) prog)

  let shell =
    plugin ~name:"shell" ~inject:[ tools ] ~optional:[] ~provide:[]
      (put tools (record [ ("name", str "ls"); ("prio", int 0); ("exec", js "payload/echo.js" [ str "ls" ]) ])
         (put tools (record [ ("name", str "cat"); ("prio", int 0); ("exec", js "payload/echo.js" [ str "cat" ]) ])
            done_)
        : ([ `Tools ], _, _) prog)

  let alias =
    plugin ~name:"alias" ~inject:[ tools ] ~optional:[] ~provide:[]
      (put tools (record [ ("name", str "dir"); ("prio", int 0); ("alias", str "ls"); ("when", str "ls") ]) done_
        : ([ `Tools ], _, _) prog)

  let pet_helper =
    plugin ~name:"pet-helper" ~inject:[ tools ] ~optional:[] ~provide:[]
      (put tools
         (record [ ("name", str "pet-help"); ("prio", int 0); ("exec", js "payload/echo.js" [ str "pet-help" ]) ])
         done_
        : ([ `Tools ], _, _) prog)

  let pet =
    plugin ~name:"pet" ~inject:[ tools ] ~optional:[ Keys.config ] ~provide:[]
      (read_opt Keys.config (fun cfg ->
           when_ (present cfg)
             (when_ (field cfg "enabled")
                (put tools
                   (record [ ("name", field cfg "prefix"); ("prio", int 1);
                             ("exec", js "payload/echo.js" [ field cfg "prefix" ]) ])
                   done_))
           >> resource "payload/timer.js" [ str "pet" ]
                (on "agent/created"
                   (fun ev -> put tools (record [ ("restrict", field ev "agent"); ("deny", str "rm") ]) done_)
                   (spawn pet_helper done_)))
        : ([ `Tools ], [ `Config ], _) prog)

  let shell_plus =
    plugin ~name:"shell-plus" ~inject:[ tools ] ~optional:[] ~provide:[]
      (put tools (record [ ("name", str "ls"); ("prio", int 5); ("exec", js "payload/echo.js" [ str "ls --color" ]) ])
         done_
        : ([ `Tools ], _, _) prog)

  let plugins = [ tools_host; config; shell; alias; pet_helper; pet; shell_plus ]
end
