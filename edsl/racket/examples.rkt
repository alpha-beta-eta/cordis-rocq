#lang s-exp "lang.rkt"
;;; 示例插件. 同一组插件在 ../ocaml/examples.ml 中用 OCaml 版写了一遍, 两边生成的 AST 与 JS 应逐字相同.

;; 提供工具注册表. F 是冻结的元数据; 工具本身是贡献.
(define-plugin tools-host
  #:provide (tools)
  (provide tools (record [kind "tools"])))

;; 提供配置. 别的插件以可选依赖读取它.
(define-plugin config
  #:provide (config)
  (provide config (record [enabled #t] [prefix "pet"])))

(define-plugin shell
  #:inject (tools)
  (put tools (record [name "ls"] [prio 0] [exec (js "payload/echo.js" "ls")]))
  (put tools (record [name "cat"] [prio 0] [exec (js "payload/echo.js" "cat")])))

;; 有条件生效的贡献: 由宿主的 view 判断 ls 是否存在, 启动程序本身不去查.
(define-plugin alias
  #:inject (tools)
  (put tools (record [name "dir"] [prio 0] [alias "ls"] [when "ls"])))

(define-plugin pet-helper
  #:inject (tools)
  (put tools (record [name "pet-help"] [prio 0] [exec (js "payload/echo.js" "pet-help")])))

;; 可选依赖, 资源, 运行期反应, spawn.
(define-plugin pet
  #:inject (tools)
  #:optional (config)
  (cfg <- read? config)
  (when (present? cfg)
    (when (field cfg enabled)
      (put tools (record [name (field cfg prefix)] [prio 1]
                         [exec (js "payload/echo.js" (field cfg prefix))]))))
  (resource "payload/timer.js" "pet")
  (on "agent/created" (ev)
    (put tools (record [restrict (field ev agent)] [deny "rm"])))
  (spawn pet-helper))

;; 与 shell 抢同一个名字: 冲突由 view 按优先级解决, 登记本身不会失败.
(define-plugin shell-plus
  #:inject (tools)
  (put tools (record [name "ls"] [prio 5] [exec (js "payload/echo.js" "ls --color")])))
