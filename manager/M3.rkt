#lang racket
;渐进的插件管理器, 第3层: 依赖变化.
;计划与各层的说明见 README.md. 每层是一个完整的文件, 不依赖前面的层; 相邻两层的差别见 diffs/.
;本层新增: 每次提供服务都得到一个新编号; 实例开始加载时记下视图: 每个依赖用的是哪个编号.
;  settle! 不再只管加载: active 的实例发现视图过期 (依赖不再可用, 或换了编号, 或自己被要求移除) 就开始卸载;
;  卸载中的实例只要它提供的服务还被别的实例用着, 就什么都不撤 (守卫 held), 等使用者先卸载完.
;  所以 dispose! 一个提供者时, 使用者先卸载, 回到等待; 提供者回来后它们重新加载.
;  restart! 强制卸载后重新加载; reset! 让加载失败的实例重试.
;  插件市场, 自更新, 热重载这些编排者不需要新机制: 它们只是 install! dispose! restart! 的调用者.
;留给下一层的问题: 一个插件想把几个小插件打包装上, 让它们的生命期跟着自己.
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
;view 是开始加载时记下的视图: 依赖名 -> provision的编号; failure 是失败的原因;
;disposed? 表示已被要求移除
(struct instance
  (plugin phase undo-stack view failure disposed?)
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
;tok是执行这次操作时用的令牌, used-id是操作时那个provision的编号
(struct undo-op (key used-id tok undo))
(struct undo-provide (key used-id))
;provision包含自己的id, 实例owner的id, 以及服务的状态
(struct provision
  (id owner [state #:mutable]))
;instances是实例id和实例的字典
;provisions是键 (服务名) 和provision的字典
;next-id由实例id, provision的id和操作令牌共用
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
;provision可用等价于作为实例的owner存在且状态为active
;可用时返回provision的id
(define (available-provision m key)
  (match (provision-ref m key)
    [(provision id owner _)
     (define provider
       (instance-ref m owner))
     (and provider
          (eq? (instance-phase provider) 'active)
          id)]
    [#f #f]))
;如果实例没有弃置, 那么判断其所有依赖是否可用.
;如果均可用, 那么返回依赖名 (也就是键) 和provision的id的字典.
(define (wanted-view m i)
  (and (not (instance-disposed? i))
       (let loop ([keys (instance-deps i)]
                  [view (hash)])
         (if (null? keys)
             view
             (let ([available-id (available-provision m (car keys))])
               (and available-id
                    (loop (cdr keys)
                          (hash-set view (car keys) available-id))))))))
;与plug提供相同服务的现存实例, 没有则为#f
(define (provider-conflict m plug)
  (for/first ([i (in-hash-values (manager-instances m))]
              #:when (for/or ([key (plugin-provides plug)])
                       (memq key (instance-provides i))))
    i))
(define (add-instance! m plug)
  (define id (fresh-id! m))
  (hash-set! (manager-instances m) id
             (instance plug 'inactive '() #f #f #f))
  id)
;检查实例是否能够访问相应服务
;如果可以就返回对应的provision
(define (resolve m id i key)
  (define p (provision-ref m key))
  (cond
    [(not p) #f]
    ;情况1: 比较视图中记录的编号和当前编号
    [(memq key (instance-deps i))
     (define expected-id
       (hash-ref (instance-view i) key #f))
     (and (number? expected-id)
          (= expected-id (provision-id p))
          p)]
    ;情况2: 检查是否为自己提供
    [else (and (= (provision-owner p) id) p)]))

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
        (define pid (provision-id p))
        ;操作失败时令牌也已用掉
        (define tok (fresh-id! m))
        (match (operation tok (provision-state p))
          [(op-result new-state undo value)
           (set-provision-state! p new-state)
           (push-undo! (undo-op key pid tok undo) i)
           (values (cont value) (format "在 ~a (编号 ~a) 上执行操作 (令牌 ~a), 结果 ~a"
                                        key pid tok value))]
          [#f (values #f (fail! (format "~a (编号 ~a) 上的操作被拒绝" key pid) i))])])]
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
            (define new-id (fresh-id! m))
            (hash-set! provisions key (provision new-id id init))
            (push-undo! (undo-provide key new-id) i)
            (values next (format "提供 ~a (编号 ~a)" key new-id))])]))

;检查编号为used-id的provision是否仍被其他实例使用
(define (in-use? m self-id used-id)
  (ormap
   (match-lambda
     [(cons id i)
      (and
       ;自己的视图不算
       (not (= id self-id))
       ;已经inactive的实例卸载完毕, 不再持有任何东西
       (not (eq? (instance-phase i) 'inactive))
       ;视图可能尚未建立 (为#f)
       (instance-view i)
       (member used-id (hash-values (instance-view i))))])
   (hash->list (manager-instances m))))
;卸载的守卫 held: 实例尚未撤回的某个provision仍被别的实例使用.
;成立时它什么都不撤, 依赖者因此在它的全部效应都还在时卸载
;(同Cordis: 先等全部provision的依赖者退出, 再启动任何disposer)
(define (held? m id i)
  (for/or ([entry (instance-undo-stack i)])
    (match entry
      [(undo-provide _ used-id) (in-use? m id used-id)]
      [_ #f])))
;弹出一项撤销; 撤销栈已空时返回 #f. 只在held?不成立时调用
(define (undo-one! m i)
  (define provisions
    (manager-provisions m))
  (match (instance-undo-stack i)
    ['() #f]
    [(cons (undo-op key used-id tok undo) rest)
     ;; 逆作用在"现在"的状态上, 所以别人在中间做过的事会保留下来
     (define p (hash-ref provisions key #f))
     (set-instance-undo-stack! i rest)
     (cond
       [(not p)
        (format "跳过撤销: ~a (编号 ~a) 已被移除, 其上的操作随之失效"
                key used-id)]
       [(not (= (provision-id p) used-id))
        (format "跳过撤销: ~a 已从编号 ~a 换成编号 ~a, 旧状态已不存在"
                key used-id (provision-id p))]
       [else
        (set-provision-state! p (undo (provision-state p)))
        (format "撤销 ~a (编号 ~a) 上的一次操作 (令牌 ~a)" key used-id tok)])]
    [(cons (undo-provide key used-id) rest)
     (define p (hash-ref provisions key #f))
     ;由守卫held?, 这时已没有别的实例使用它
     (cond [(and p (= (provision-id p) used-id))
            (hash-remove! provisions key)
            (set-instance-undo-stack! i rest)
            (format "撤销提供 ~a (编号 ~a)" key used-id)]
           [else
            (set-instance-undo-stack! i rest)
            (format "跳过撤销提供: ~a (编号 ~a) 已不存在" key used-id)])]))
;按 LIFO 撤销全部
(define (unload! m id i trace)
  (let loop ()
    (define message (undo-one! m i))
    (when message
      (trace id message)
      (loop))))

;加载实例: 以视图wanted把它的程序从头跑到尾; 失败时停在 unloading, 由 settle! 卸载
(define (load! m id i wanted trace)
  (set-instance-phase! i 'loading)
  (set-instance-undo-stack! i '())
  (set-instance-view! i wanted)
  (trace id (format "实例 ~a (插件 ~a) 开始加载, 依赖 (服务 . 编号): ~a"
                    id (instance-name i) (hash->list wanted)))
  (let loop ([P (plugin-body (instance-plugin i))])
    (define-values (next message) (run-instruction! m id i P))
    (trace id message)
    (when next (loop next))))

;让实例做一件事: 整段加载, 开始卸载, 整段卸载, 或从管理器中移除; 无事可做时返回#f
(define (step-instance! m id i trace)
  (define name (instance-name i))
  (define wanted (wanted-view m i))
  (match (instance-phase i)
    ['inactive
     (cond [(instance-disposed? i)
            (hash-remove! (manager-instances m) id)
            (trace id (format "实例 ~a (插件 ~a) 已弃置且卸载完毕, 从管理器中移除"
                              id name))
            #t]
           [(and (not (instance-failure i)) wanted)
            (load! m id i wanted trace)
            #t]
           [else #f])]
    ;视图过期时开始卸载
    ['active
     #:when (not (equal? wanted (instance-view i)))
     (set-instance-phase! i 'unloading)
     (trace id (format "实例 ~a (插件 ~a) 开始卸载, 原因: ~a"
                       id name
                       (if (instance-disposed? i)
                           "被要求移除"
                           (format "依赖变化, 原视图 ~a, 现在~a"
                                   (hash->list (instance-view i))
                                   (if wanted
                                       (format "应为 ~a" (hash->list wanted))
                                       "有依赖不可用")))))
     #t]
    ['active #f]
    ['unloading
     (cond [(held? m id i) #f]
           [else
            (unload! m id i trace)
            (set-instance-phase! i 'inactive)
            (trace id (if (instance-failure i)
                          (format "卸载完毕 -> inactive (此次卸载由加载失败引起: ~a)"
                                  (instance-failure i))
                          "卸载完毕 -> inactive"))
            #t])]))

;反复挑一个有事可做的实例做一件事, 直到没有为止 (静止)
(define (settle! m #:trace [trace void])
  (let loop ()
    (when (for/or ([id (sort (hash-keys (manager-instances m)) <)])
            (define i (instance-ref m id))
            (and i (step-instance! m id i trace)))
      (loop))))

;静止时每个实例都安定: 加载失败, 或应当不运行且未运行, 或以正确视图active;
;并且没有已弃置的实例
(define (settled? m)
  (for/and ([(id i) (manager-instances m)])
    (define wanted (wanted-view m i))
    (match (instance-phase i)
      ['inactive (and (or (instance-failure i) (not wanted))
                      (not (instance-disposed? i)))]
      ['active (equal? wanted (instance-view i))]
      [_ #f])))

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

;;; 编排操作 (外部输入); 前提不满足时报错. 每个操作之后 settle!

(define (existing-instance who m id)
  (or (instance-ref m id)
      (error who "没有编号为 ~a 的实例" id)))
;装上插件: 先停在 inactive, 依赖都可用时随即加载. 返回实例id
(define (install! m plug #:trace [trace void])
  (cond [(provider-conflict m plug)
         => (λ (existing)
              (error 'install! "~a 与 ~a 提供了相同的服务"
                     (plugin-name plug) (instance-name existing)))])
  (define id (add-instance! m plug))
  (trace id (format "装上实例 ~a (插件 ~a), 依赖 ~a" id (plugin-name plug) (plugin-deps plug)))
  (settle! m #:trace trace)
  id)
;移除实例: 标记为已弃置; 它的使用者先卸载, 它再卸载, 最后从管理器中删除
(define (dispose! m id #:trace [trace void])
  (set-instance-disposed?!
   (existing-instance 'dispose! m id) #t)
  (trace id (format "要求移除实例 ~a" id))
  (settle! m #:trace trace))
;重启: 强制卸载, 卸载完后重新加载
(define (restart! m id #:trace [trace void])
  (define i (existing-instance 'restart! m id))
  (unless (and (not (instance-disposed? i))
               (eq? (instance-phase i) 'active))
    (error 'restart! "实例 ~a 不是未弃置的active实例" id))
  (set-instance-phase! i 'unloading)
  (trace id (format "实例 ~a (插件 ~a) 开始卸载, 原因: 被要求重启" id (instance-name i)))
  (settle! m #:trace trace))
;重试: 只对加载失败后停在inactive的实例有效
(define (reset! m id #:trace [trace void])
  (define i (existing-instance 'reset! m id))
  (unless (and (eq? (instance-phase i) 'inactive) (instance-failure i))
    (error 'reset! "实例 ~a 不是加载失败后的inactive实例" id))
  (set-instance-failure! i #f)
  (trace id (format "重试实例 ~a" id))
  (settle! m #:trace trace))

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
    (printf " ~a[编号~a, 由#~a提供]=~a" key (provision-id p) (provision-owner p)
            (if (eq? key 'tools)
                (sort (hash-keys (provision-state p)) string<?)
                (sort (hash->list (provision-state p)) < #:key car))))
  (newline))

;;; 示例插件

(define core
  (plugin "core" '() '(tools)
          (prog (serve 'tools (hash))
                (Done))))
;提供 tools 之后自己再登记一个条目
(define core+
  (plugin "core+" '() '(tools)
          (prog (serve 'tools (hash))
                ('tools (register "builtin" "内建"))
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
;git 的新版本: 登记的说明不同
(define git2
  (plugin "git2" '(tools) '()
          (prog ('tools (register "git" "版本控制 (新版)"))
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
  (define ids (make-hash))
  (define (install name plug) (hash-set! ids name (install! m plug #:trace print-step)))
  (define (dispose name) (dispose! m (hash-ref ids name) #:trace print-step))
  (scene "先装 shell 和 git, 再装 core"
         (λ () (install 'shell shell)
               (install 'git git)
               (install 'core core)))
  (scene "重启 core: shell 和 git 先卸载 (core 被守卫挡着), core 以新编号重新提供, 它们再加载"
         (λ () (restart! m (hash-ref ids 'core) #:trace print-step)))
  (scene "移除 core: shell 和 git 卸载后回到等待"
         (λ () (dispose 'core)))
  (scene "再装一个 core: 等待的 shell 和 git 重新加载"
         (λ () (install 'core core)))
  (scene "装 bad: 加载失败, 停下"
         (λ () (install 'bad bad)))
  (scene "reset! bad: 重试, 再次失败"
         (λ () (reset! m (hash-ref ids 'bad) #:trace print-step)))
  (scene "编排者换版本: 移除 git, 装上 git2 (插件市场, 自更新都是这样的调用)"
         (λ () (dispose 'git)
               (install 'git2 git2))))

(module+ test
  (require rackunit)

  ;; 依赖没有时等待, 有了随即加载; 安装次序随意
  (define m (make-manager))
  (define shell-id (install! m shell))
  (check-eq? (instance-phase (instance-ref m shell-id)) 'inactive)
  (define git-id (install! m git))
  (define core-id (install! m core))
  (check-equal? (tools-of m) '("cat" "git" "ls"))
  (check-true (settled? m))

  ;; 两个插件提供同一个服务: 后装的被拒绝
  (check-exn #rx"相同的服务" (λ () (install! m core)))

  ;; restart: 结果不变, 但 tools 换了编号; 使用者的视图跟着换
  (define old-pid (provision-id (provision-ref m 'tools)))
  (restart! m core-id)
  (check-equal? (tools-of m) '("cat" "git" "ls"))
  (define new-pid (provision-id (provision-ref m 'tools)))
  (check-not-equal? new-pid old-pid)
  (check-equal? (instance-view (instance-ref m shell-id)) (hash 'tools new-pid))
  (check-true (settled? m))
  (check-exn exn:fail? (λ () (restart! m 999)))

  ;; reset: 只对失败的实例有效; 重置后重新加载, 再次失败
  (define bad-id (install! m bad))
  (check-equal? (instance-failure (instance-ref m bad-id))
                (format "tools (编号 ~a) 上的操作被拒绝" new-pid))
  (check-exn exn:fail? (λ () (reset! m shell-id)))
  (check-exn exn:fail? (λ () (restart! m bad-id)))
  (reset! m bad-id)
  (check-true (string? (instance-failure (instance-ref m bad-id))))
  (check-equal? (tools-of m) '("cat" "git" "ls"))
  (dispose! m bad-id)
  (check-false (instance-ref m bad-id))

  ;; 移除提供者: 使用者先卸载, 回到等待 (不算失败); 提供者回来后重新加载
  (dispose! m core-id)
  (check-false (tools-of m))
  (check-false (instance-ref m core-id))
  (check-eq? (instance-phase (instance-ref m shell-id)) 'inactive)
  (check-false (instance-failure (instance-ref m shell-id)))
  (check-true (settled? m))
  (void (install! m core))
  (check-equal? (tools-of m) '("cat" "git" "ls"))

  ;; 守卫作用于整个卸载: core+ 在提供之后登记了 builtin; 重启时 shell 先卸载完,
  ;; core+ 才开始撤 builtin, shell 卸载时看到的是 core+ 的全部效应 (同 Cordis)
  (let ([m (make-manager)] [log '()])
    (define c (install! m core+))
    (define s (install! m shell))
    (restart! m c #:trace (λ (id message) (set! log (cons (cons id message) log))))
    (define (index-of-step id prefix)
      (for/first ([entry (reverse log)] [k (in-naturals)]
                  #:when (and (= (car entry) id) (string-prefix? (cdr entry) prefix)))
        k))
    (check-true (< (index-of-step s "卸载完毕") (index-of-step c "撤销 tools")))
    (check-true (< (index-of-step c "撤销提供")
                   (index-of-step c (format "实例 ~a (插件 core+) 开始加载" c))))
    (check-equal? (tools-of m) '("builtin" "cat" "ls"))
    (check-true (settled? m)))

  ;; 按守卫, 跳过撤销的分支不会被走到
  (let ([m (make-manager)] [messages '()])
    (define (record id message) (set! messages (cons message messages)))
    (define c (install! m core #:trace record))
    (void (install! m shell #:trace record))
    (define g (install! m git #:trace record))
    (void (install! m bus #:trace record))
    (void (install! m ping #:trace record))
    (restart! m c #:trace record)
    (dispose! m g #:trace record)
    (dispose! m c #:trace record)
    (check-false (findf (λ (s) (string-prefix? s "跳过")) messages))
    (check-equal? (handlers-for m "tick") '("ping")))

  ;; 令牌: 同一个处理器登记两次, 移除第一个, 留下的是第二个的那一项
  (let ([m (make-manager)])
    (define p1 (install! m ping))
    (define p2 (install! m ping))
    (void (install! m bus))
    (define t2 (undo-op-tok (car (instance-undo-stack (instance-ref m p2)))))
    (check-equal? (handlers-for m "tick") '("ping" "ping"))
    (dispose! m p1)
    (check-equal? (handlers-for m "tick") '("ping"))
    (check-equal? (hash-keys (provision-state (provision-ref m 'events))) (list t2)))

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
    (check-equal? (instance-failure (instance-ref m liar)) "db 不在声明的 provides () 中"))

  ;; 提供者加载失败: 它提供的服务随之撤回, 使用者继续等待
  (let ([m (make-manager)])
    (define s (install! m shell))
    (void (install! m (plugin "broken-core" '() '(tools)
                              (prog (serve 'tools (hash)) (Fail "坏了")))))
    (check-false (tools-of m))
    (check-eq? (instance-phase (instance-ref m s)) 'inactive)
    (check-false (instance-failure (instance-ref m s)))))
