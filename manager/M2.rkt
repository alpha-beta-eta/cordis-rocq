#lang racket
;渐进的插件管理器, 第2层: 服务与依赖.
;计划与各层的说明见 README.md. 每层是一个完整的文件, 不依赖前面的层; 相邻两层的差别见 diffs/.
;本层新增: 插件声明它提供的服务 (provides) 和要用的服务 (deps). 程序多了 serve: 建立一个服务 (provision),
;  它的状态由提供者和使用者共同操作, 卸载时撤回. 管理器不再预置共享状态: 共享状态都是某个服务的状态.
;  装上的插件先停在 inactive, 等它的依赖都由 active 的提供者提供了, 才由 settle! 加载; 所以安装次序随意.
;  两个插件声明提供同一个服务时, 后装的被拒绝.
;义务: 依赖不能成环 (包括依赖自己提供的服务). 成环的插件永远停在 inactive 等待;
;  运行时不检查, 同 Cordis (测试中有反例).
;本层的限制: 正被使用的提供者不能移除 (dispose! 报错).
;留给下一层的问题: 想重启或卸掉 core, 就得先手工卸掉所有用它的插件, 再按次序装回来.
(provide (all-defined-out))

;operation : 令牌 状态 -> op-result 或 #f (#f 表示操作被拒绝)
;令牌是运行时交给这次操作的新鲜编号, 用作操作生成出来的东西的身份 (如事件处理器)
;undo : 状态 -> 状态, 撤销这次操作; 它作用在撤销时的状态上
(struct op-result (state undo value))

;program ir
(struct Provide (key init next))
;cont : value -> ir
(struct Op (key operation cont))
(struct Done ())
(struct Fail (why))
(define-syntax prog
  (syntax-rules (serve <-)
    [(_ last) last]
    [(_ (serve key init) rest ...)
     (Provide key init (prog rest ...))]
    [(_ (var <- key operation) rest ...)
     (Op key operation (λ (var) (prog rest ...)))]
    [(_ (key operation) rest ...)
     (Op key operation (λ (ignored) (prog rest ...)))]))

(struct plugin (name deps provides body))
;phase 是 'inactive (等待依赖, 或加载失败后停下), 'loading, 'active 或 'unloading;
;failure 是失败的原因
(struct instance
  (plugin phase undo-stack failure)
  #:mutable)
(define instance-deps
  (compose plugin-deps instance-plugin))
(define instance-provides
  (compose plugin-provides instance-plugin))
(define instance-name
  (compose plugin-name instance-plugin))
(define (fail! why i)
  (set-instance-phase! i 'unloading)
  (set-instance-failure! i why)
  (format "失败 (~a), 开始卸载" why))
(define (push-undo! entry i)
  (set-instance-undo-stack!
   i (cons entry (instance-undo-stack i))))
;tok是执行这次操作时用的令牌
(struct undo-op (key tok undo))
(struct undo-provide (key))
;provision包含提供者实例owner的id, 以及服务的状态
(struct provision
  (owner [state #:mutable]))
;instances是实例id和实例的字典
;provisions是键 (服务名) 和provision的字典
;next-id由实例id和操作令牌共用
(struct manager
  ([next-id #:mutable] instances provisions))
(define (make-manager)
  (manager 0 (make-hash) (make-hash)))
(define (fresh-id! m)
  (define id (manager-next-id m))
  (set-manager-next-id! m (add1 id))
  id)
(define (provision-ref m key)
  (hash-ref (manager-provisions m) key #f))
(define (instance-ref m id)
  (hash-ref (manager-instances m) id #f))
;服务可用: 有provision, 且它的提供者是active
(define (available? m key)
  (match (provision-ref m key)
    [(provision owner _)
     (eq? (instance-phase (instance-ref m owner)) 'active)]
    [#f #f]))
;可以开始加载: inactive, 没有失败过, 依赖都可用
(define (ready? m i)
  (and (eq? (instance-phase i) 'inactive)
       (not (instance-failure i))
       (andmap (λ (key) (available? m key)) (instance-deps i))))
;与plug提供相同服务的现存实例, 没有则为#f
(define (provider-conflict m plug)
  (for/first ([i (in-hash-values (manager-instances m))]
              #:when (for/or ([key (plugin-provides plug)])
                       (memq key (instance-provides i))))
    i))
;正在使用实例id所提供的服务的其他实例 (loading或active)
(define (users m id)
  (for/list ([(j i) (manager-instances m)]
             #:when (and (not (= j id))
                         (memq (instance-phase i) '(loading active))
                         (for/or ([key (instance-deps i)])
                           (match (provision-ref m key)
                             [(provision owner _) (= owner id)]
                             [#f #f]))))
    j))
;实例能否在key上操作: 是它的依赖, 或是它自己提供的; 可以时返回对应的provision
(define (resolve m id i key)
  (define p (provision-ref m key))
  (and p
       (or (memq key (instance-deps i))
           (= (provision-owner p) id))
       p))

;运行实例的程序一步; 返回 (values 剩余程序或#f 描述)
(define (run-instruction! m id i P)
  (define provisions
    (manager-provisions m))
  (match P
    [(Done)
     (set-instance-phase! i 'active)
     (values #f "加载完毕 -> active")]
    [(Fail why) (values #f (fail! why i))]
    [(Op key operation cont)
     (define p (resolve m id i key))
     (cond
       [(not p) (values #f (fail! (format "实例无法访问服务 ~a" key) i))]
       [else
        ;操作失败时令牌也已用掉
        (define tok (fresh-id! m))
        (match (operation tok (provision-state p))
          [(op-result new-state undo value)
           (set-provision-state! p new-state)
           (push-undo! (undo-op key tok undo) i)
           (values (cont value) (format "在 ~a 上执行操作 (令牌 ~a), 结果 ~a" key tok value))]
          [#f (values #f (fail! (format "~a 上的操作被拒绝" key) i))])])]
    [(Provide key init next)
     (cond [(not (memq key (instance-provides i)))
            (values #f (fail! (format "~a 不在声明的 provides ~a 中"
                                      key (instance-provides i))
                              i))]
           [(hash-ref provisions key #f)
            => (λ (existing)
                 (values #f (fail! (if (= (provision-owner existing) id)
                                       (format "~a 已由自身提供过" key)
                                       (format "~a 已由实例 ~a 提供" key (provision-owner existing)))
                                   i)))]
           [else
            (hash-set! provisions key (provision id init))
            (push-undo! (undo-provide key) i)
            (values next (format "提供 ~a" key))])]))

;弹出一项撤销; 撤销栈已空时返回 #f
;本层中提供者不会先于使用者卸载 (dispose! 会拒绝), 所以要撤的服务总还在
(define (undo-one! m i)
  (define provisions
    (manager-provisions m))
  (match (instance-undo-stack i)
    ['() #f]
    [(cons (undo-op key tok undo) rest)
     ;; 逆作用在"现在"的状态上, 所以别人在中间做过的事会保留下来 (前提是撤销独立性, 见 M1 开头)
     (define p (hash-ref provisions key))
     (set-instance-undo-stack! i rest)
     (set-provision-state! p (undo (provision-state p)))
     (format "撤销 ~a 上的一次操作 (令牌 ~a)" key tok)]
    [(cons (undo-provide key) rest)
     (hash-remove! provisions key)
     (set-instance-undo-stack! i rest)
     (format "撤销提供 ~a" key)]))
;按 LIFO 撤销全部
(define (unload! m id i trace)
  (let loop ()
    (define message (undo-one! m i))
    (when message
      (trace id message)
      (loop))))

;加载实例: 把它的程序从头跑到尾; 失败时撤掉已做的操作, 停在 inactive
(define (load! m id i trace)
  (set-instance-phase! i 'loading)
  (set-instance-undo-stack! i '())
  (trace id (format "实例 ~a (插件 ~a) 开始加载" id (instance-name i)))
  (let loop ([P (plugin-body (instance-plugin i))])
    (define-values (next message) (run-instruction! m id i P))
    (trace id message)
    (when next (loop next)))
  (when (eq? (instance-phase i) 'unloading)
    (unload! m id i trace)
    (set-instance-phase! i 'inactive)
    (trace id (format "卸载完毕 -> inactive (此次卸载由加载失败引起: ~a)"
                      (instance-failure i)))))

;反复加载可以开始加载的实例, 直到没有为止
(define (settle! m #:trace [trace void])
  (let loop ()
    (define id
      (for/first ([id (sort (hash-keys (manager-instances m)) <)]
                  #:when (ready? m (instance-ref m id)))
        id))
    (when id
      (load! m id (instance-ref m id) trace)
      (loop))))

;;; 服务操作的例子

;注册表: 状态是 名字 -> 值 的hash; 名字已被占用时拒绝
(define ((register name value) tok state)
  (and (not (hash-has-key? state name))
       (op-result
        (hash-set state name value)
        (λ (state) (hash-remove state name))
        'ok)))
;事件处理器表: 状态是 令牌 -> (事件名 . 处理器) 的hash, 令牌的大小即登记的顺序
;同一个处理器可以登记多次, 令牌区分各次登记, 逆只删掉自己这一次
(define ((on event handler) tok state)
  (op-result
   (hash-set state tok (cons event handler))
   (λ (state) (hash-remove state tok))
   tok))

;;; 编排操作 (外部输入); 前提不满足时报错

(define (existing-instance who m id)
  (or (instance-ref m id)
      (error who "没有编号为 ~a 的实例" id)))
;装上插件: 先停在 inactive, 再 settle!; 依赖都可用时它 (和因它而可用的插件) 随即加载. 返回实例id
(define (install! m plug #:trace [trace void])
  (cond [(provider-conflict m plug)
         => (λ (existing)
              (error 'install! "~a 与 ~a 提供了相同的服务"
                     (plugin-name plug) (instance-name existing)))])
  (define id (fresh-id! m))
  (hash-set! (manager-instances m) id (instance plug 'inactive '() #f))
  (trace id (format "装上实例 ~a (插件 ~a), 依赖 ~a" id (plugin-name plug) (plugin-deps plug)))
  (settle! m #:trace trace)
  id)
;移除实例: 按 LIFO 撤掉它做过的全部操作, 再从管理器中删除.
;它提供的服务正被别的实例使用时拒绝
(define (dispose! m id #:trace [trace void])
  (define i (existing-instance 'dispose! m id))
  (define using (users m id))
  (unless (null? using)
    (error 'dispose! "实例 ~a 提供的服务正被实例 ~a 使用" id using))
  (set-instance-phase! i 'unloading)
  (trace id (format "实例 ~a (插件 ~a) 开始卸载, 原因: 被要求移除" id (instance-name i)))
  (unload! m id i trace)
  (hash-remove! (manager-instances m) id)
  (trace id (format "实例 ~a 卸载完毕, 从管理器中移除" id)))

;事件 event 发生时依次调用的处理器
(define (handlers-for m event)
  (define p (provision-ref m 'events))
  (define state (if p (provision-state p) (hash)))
  (for/list ([tok (sort (hash-keys state) <)]
             #:when (equal? (car (hash-ref state tok)) event))
    (cdr (hash-ref state tok))))

(define (print-step id message)
  (printf "  [~a] ~a\n" id message))

(define (show m)
  (printf "  -- 实例:")
  (for ([id (sort (hash-keys (manager-instances m)) <)])
    (define i (instance-ref m id))
    (printf " ~a#~a=~a~a" (instance-name i) id (instance-phase i)
            (cond [(instance-failure i) "(失败)"]
                  [(eq? (instance-phase i) 'inactive) "(等待)"]
                  [else ""])))
  (newline)
  (printf "  -- 服务:")
  (when (zero? (hash-count (manager-provisions m))) (printf " (无)"))
  (for ([key '(tools events)] #:when (provision-ref m key))
    (define p (provision-ref m key))
    (printf " ~a[由#~a提供]=~a" key (provision-owner p)
            (if (eq? key 'tools)
                (sort (hash-keys (provision-state p)) string<?)
                (sort (hash->list (provision-state p)) < #:key car))))
  (newline))

;;; 示例插件

(define core
  (plugin "core" '() '(tools)
          (prog (serve 'tools (hash))
                (Done))))
(define shell
  (plugin "shell" '(tools) '()
          (prog ('tools (register "ls" "列出文件"))
                ('tools (register "cat" "打印文件"))
                (Done))))
(define git
  (plugin "git" '(tools) '()
          (prog ('tools (register "git" "版本控制"))
                (Done))))
;先登记 grep, 再登记已被占用的 ls -> 失败; grep 会被自动撤掉
(define bad
  (plugin "bad" '(tools) '()
          (prog ('tools (register "grep" "搜索"))
                ('tools (register "ls" "冒牌 ls"))
                (Done))))
(define bus
  (plugin "bus" '() '(events)
          (prog (serve 'events (hash))
                (Done))))
(define ping
  (plugin "ping" '(events) '()
          (prog ('events (on "tick" "ping"))
                (Done))))

(define (tools-of m)
  (define p (provision-ref m 'tools))
  (and p (sort (hash-keys (provision-state p)) string<?)))

(module+ main
  (define m (make-manager))
  (define (scene title thunk)
    (printf "\n== ~a\n" title)
    (thunk)
    (show m))
  (define (attempt thunk)
    (with-handlers ([exn:fail? (λ (e) (printf "  !! ~a\n" (exn-message e)))])
      (thunk)))
  (define ids (make-hash))
  (define (install name plug) (hash-set! ids name (install! m plug #:trace print-step)))
  (define (dispose name) (dispose! m (hash-ref ids name) #:trace print-step))
  (scene "先装 shell 和 git: 还没有 tools, 停在 inactive 等待"
         (λ () (install 'shell shell)
               (install 'git git)))
  (scene "装 core: 它提供 tools, 等待的 shell 和 git 随即加载"
         (λ () (install 'core core)))
  (scene "再装一个 core: 两个插件提供同一个服务, 被拒绝"
         (λ () (attempt (λ () (install! m core)))))
  (scene "装 bad: 登记 ls 被拒绝, 加载失败; 它先登记的 grep 被自动撤掉"
         (λ () (install 'bad bad)))
  (scene "想移除 core: 被拒绝, shell 和 git 正在用 tools"
         (λ () (attempt (λ () (dispose 'core)))))
  (scene "移除 shell 和 git, 再移除 core"
         (λ () (dispose 'shell)
               (dispose 'git)
               (dispose 'core)))
  (scene "装 ping 再装 bus: 次序随意"
         (λ () (install 'ping ping)
               (install 'bus bus))))

(module+ test
  (require rackunit)

  ;; 依赖没有时等待, 有了随即加载; 安装次序随意
  (define m (make-manager))
  (define shell-id (install! m shell))
  (check-eq? (instance-phase (instance-ref m shell-id)) 'inactive)
  (check-false (tools-of m))
  (define git-id (install! m git))
  (define core-id (install! m core))
  (check-equal? (tools-of m) '("cat" "git" "ls"))
  (check-eq? (instance-phase (instance-ref m shell-id)) 'active)
  (check-eq? (instance-phase (instance-ref m core-id)) 'active)

  ;; 两个插件提供同一个服务: 后装的被拒绝
  (check-exn #rx"相同的服务" (λ () (install! m core)))

  ;; 加载失败时, 已经做了的操作被撤掉; 失败的实例不再自动重试
  (define bad-id (install! m bad))
  (check-eq? (instance-phase (instance-ref m bad-id)) 'inactive)
  (check-equal? (instance-failure (instance-ref m bad-id)) "tools 上的操作被拒绝")
  (check-equal? (tools-of m) '("cat" "git" "ls"))
  (settle! m)
  (check-eq? (instance-phase (instance-ref m bad-id)) 'inactive)
  (dispose! m bad-id)

  ;; 正被使用的提供者不能移除; 使用者都走了之后可以
  (check-exn #rx"正被实例" (λ () (dispose! m core-id)))
  (dispose! m shell-id)
  (check-equal? (tools-of m) '("git"))
  (check-exn #rx"正被实例" (λ () (dispose! m core-id)))
  (dispose! m git-id)
  (dispose! m core-id)
  (check-false (tools-of m))
  (check-equal? (hash-count (manager-instances m)) 0)

  ;; 义务: 依赖不成环. 依赖自己提供的服务 (长度为 1 的环) 的插件永远等待, 运行时不检查 (同 Cordis);
  ;; 别的插件也来不了: 提供同一个服务会冲突
  (let ([m (make-manager)])
    (define s (install! m (plugin "selfdep" '(tools) '(tools) (prog (serve 'tools (hash)) (Done)))))
    (check-eq? (instance-phase (instance-ref m s)) 'inactive)
    (check-false (instance-failure (instance-ref m s)))
    (check-exn #rx"相同的服务" (λ () (install! m core))))

  ;; 等待中的实例可以直接移除
  (let ([m (make-manager)])
    (define s (install! m shell))
    (dispose! m s)
    (check-equal? (hash-count (manager-instances m)) 0))

  ;; 只能在依赖和自己提供的服务上操作; 只能提供声明过的服务
  (let ([m (make-manager)])
    (void (install! m core))
    (define sneaky (install! m (plugin "sneaky" '() '() (prog ('tools (register "x" 1)) (Done)))))
    (check-equal? (instance-failure (instance-ref m sneaky)) "实例无法访问服务 tools")
    (define liar (install! m (plugin "liar" '() '() (prog (serve 'db (hash)) (Done)))))
    (check-equal? (instance-failure (instance-ref m liar)) "db 不在声明的 provides () 中")
    ;; 在自己提供的服务上操作
    (void (install! m (plugin "local" '() '(local)
                              (prog (serve 'local (hash))
                                    ('local (register "x" 1))
                                    (Done)))))
    (check-equal? (provision-state (provision-ref m 'local)) (hash "x" 1)))

  ;; 提供者加载失败: 它提供的服务随之撤回, 使用者继续等待
  (let ([m (make-manager)])
    (define s (install! m shell))
    (void (install! m (plugin "broken-core" '() '(tools)
                              (prog (serve 'tools (hash)) (Fail "坏了")))))
    (check-false (tools-of m))
    (check-eq? (instance-phase (instance-ref m s)) 'inactive)
    (check-false (instance-failure (instance-ref m s))))

  ;; 令牌: 同一个处理器登记两次, 移除第一个, 留下的是第二个的那一项
  (let ([m (make-manager)])
    (define p1 (install! m ping))
    (define p2 (install! m ping))
    (void (install! m bus))
    (define t2 (undo-op-tok (car (instance-undo-stack (instance-ref m p2)))))
    (check-equal? (handlers-for m "tick") '("ping" "ping"))
    (dispose! m p1)
    (check-equal? (handlers-for m "tick") '("ping"))
    (check-equal? (hash-keys (provision-state (provision-ref m 'events))) (list t2))))
