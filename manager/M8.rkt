#lang racket
;渐进的插件管理器, 第8层: 交集生命期.
;计划与各层的说明见 README.md. 每层是一个完整的文件, 不依赖前面的层; 相邻两层的差别见 diffs/.
;本层新增: 事件处理器可以是一族 (载荷 -> 插件), react! 带上载荷 (如 agent 的编号),
;  装上这一族在该载荷处的插件. 这解决的是: 插件 P 给 agent A 挂一个效应 (如限制 A 能用的工具),
;  P 和 A 任一方结束时都要撤掉它. 编码不需要新的卸载机制:
;  - agent A 提供一个以自己编号为名的服务 (它的上下文);
;  - 效应是 P 的一次反应, 也就是 P 的子实例, 它依赖 A 的上下文, 并在其中登记;
;  - P 结束: 子实例先退出 (第4层); A 结束: 子实例的依赖不可用了, 它卸载,
;    而 A 被守卫挡着, 在效应撤掉之前一项也不撤 (第3层).
;  A 结束后效应的实例停在 inactive, 直到 P 卸载才被移除.
;取舍与义务: 效应不随 A 结束而移除, 换来的是不需要新的规则. 代价是一条编排者义务: agent 编号不复用.
;  复用时, 停在 inactive 的旧效应会在新 agent 的上下文里重新加载 (测试中有反例). dsh 的 agent 编号不复用;
;  需要"一次性"语义时, P 可以在"agent 结束"事件的处理器里 dispose! 这个子实例.
;  对应 programs/cordis3.rkt 的扩展3 (见 docs/EXTENSIONS.md 第3节).
;留给下一层的问题: 到这里插件还是一段程序 (数据), 而 Cordis 的插件是拿到 ctx 的一段代码.
(provide (all-defined-out))

;operation : 令牌 状态 -> op-result 或 #f (#f 表示操作被拒绝)
;令牌是运行时交给这次操作的新鲜编号, 用作操作生成出来的东西的身份 (如事件处理器)
;undo : 状态 -> 状态, 撤销这次操作; 它作用在撤销时的状态上
(struct op-result (state undo value))

;program ir
(struct Provide (key init next))
;cont : value -> ir
(struct Op (key operation cont))
;安装子插件child, 其生命期不超过当前实例
(struct Spawn (child next))
(struct Done ())
(struct Fail (why))
(define-syntax prog
  (syntax-rules (serve spawn <-)
    [(_ last) last]
    [(_ (serve key init) rest ...)
     (Provide key init (prog rest ...))]
    [(_ (spawn child) rest ...)
     (Spawn child (prog rest ...))]
    [(_ (var <- key operation) rest ...)
     (Op key operation (λ (var) (prog rest ...)))]
    [(_ (key operation) rest ...)
     (Op key operation (λ (ignored) (prog rest ...)))]))

;reacts是插件列表: 实例active时的事件处理器, 每次反应是一个子实例 (见react!)
;构造时reacts可以省略, 默认没有事件处理器
;optional是可选依赖, 默认没有; body是程序, 或者 (在场的可选依赖列表 -> 程序)
(struct plugin (name deps optional provides body reacts)
  #:constructor-name make-plugin
  #:omit-define-syntaxes)
(define (plugin name deps provides body [reacts '()] #:optional [optional '()])
  (make-plugin name deps optional provides body reacts))
;phase 是 'inactive (等待依赖, 或加载失败后停下), 'loading, 'active 或 'unloading;
;remaining 是剩余需要执行的程序;
;view 是开始加载时记下的视图: 依赖名 -> provision的编号; failure 是失败的原因;
;disposed? 表示已被要求移除; parent是父实例的id, 直接install!的实例为#f
(struct instance
  (plugin phase remaining undo-stack view failure disposed? parent)
  #:mutable)
(define instance-deps
  (compose plugin-deps instance-plugin))
(define instance-optional
  (compose plugin-optional instance-plugin))
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
;安装过子实例child-id
(struct undo-spawn (child-id))
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
             (with-present m i view)
             (let ([available-id (available-provision m (car keys))])
               (and available-id
                    (loop (cdr keys)
                          (hash-set view (car keys) available-id))))))))
;再加上此刻可用的可选依赖. 视图因此记下在场集;
;在场集一变, 视图就和wanted不同, 已有的"视图不符就卸载"规则使实例重载
(define (with-present m i view)
  (for/fold ([view view]) ([key (instance-optional i)])
    (define available-id (available-provision m key))
    (if available-id (hash-set view key available-id) view)))
;视图中在场的可选依赖, 按声明顺序
(define (present-optional i view)
  (filter (λ (key) (hash-has-key? view key)) (instance-optional i)))
;实例id是否还有子实例
(define (has-children? m id)
  (for/or ([i (in-hash-values (manager-instances m))])
    (equal? (instance-parent i) id)))
;与plug提供相同服务的现存实例, 没有则为#f
(define (provider-conflict m plug)
  (for/first ([i (in-hash-values (manager-instances m))]
              #:when (for/or ([key (plugin-provides plug)])
                       (member key (instance-provides i))))
    i))
(define (add-instance! m plug parent)
  (define id (fresh-id! m))
  (hash-set! (manager-instances m) id
             (instance plug 'inactive #f '() #f #f #f parent))
  id)
;检查实例是否能够访问相应服务
;如果可以就返回对应的provision
(define (resolve m id i key)
  (define p (provision-ref m key))
  (cond
    [(not p) #f]
    ;情况1: 比较视图中记录的编号和当前编号 (必需依赖, 以及在场的可选依赖)
    [(hash-has-key? (instance-view i) key)
     (define expected-id
       (hash-ref (instance-view i) key #f))
     (and (number? expected-id)
          (= expected-id (provision-id p))
          p)]
    ;情况2: 检查是否为自己提供
    [else (and (= (provision-owner p) id) p)]))

;运行实例的剩余程序一步; 返回描述
(define (run-instruction! m id i)
  (define provisions
    (manager-provisions m))
  (match (instance-remaining i)
    [(Done)
     (set-instance-phase! i 'active)
     "加载完毕 -> active"]
    [(Fail why) (fail! why i)]
    [(Op key operation cont)
     (define p (resolve m id i key))
     (cond
       [(not p) (fail! (format "实例无法访问服务 ~a" key) i)]
       [else
        (define pid (provision-id p))
        ;操作失败时令牌也已用掉
        (define tok (fresh-id! m))
        (match (operation tok (provision-state p))
          [(op-result new-state undo value)
           (set-provision-state! p new-state)
           (push-undo! (undo-op key pid tok undo) i)
           (set-instance-remaining! i (cont value))
           (format "在 ~a (编号 ~a) 上执行操作 (令牌 ~a), 结果 ~a"
                   key pid tok value)]
          [#f (fail! (format "~a (编号 ~a) 上的操作被拒绝" key pid) i)])])]
    [(Provide key init next)
     (cond [(not (member key (instance-provides i)))
            (fail! (format "~a 不在声明的 provides ~a 中"
                           key (instance-provides i))
                   i)]
           [(hash-ref provisions key #f)
            => (λ (existing)
                 (fail! (if (= (provision-owner existing) id)
                            (format "~a 已由自身提供过" key)
                            (format "~a 已由实例 ~a 提供" key (provision-owner existing)))
                        i))]
           [else
            (define new-id (fresh-id! m))
            (hash-set! provisions key (provision new-id id init))
            (push-undo! (undo-provide key new-id) i)
            (set-instance-remaining! i next)
            (format "提供 ~a (编号 ~a)" key new-id)])]
    [(Spawn child next)
     (cond [(provider-conflict m child)
            => (λ (existing)
                 (fail! (format "子插件 ~a 与 ~a 提供了相同的服务"
                                (plugin-name child) (instance-name existing))
                        i))]
           [else
            (define child-id (add-instance! m child id))
            (push-undo! (undo-spawn child-id) i)
            (set-instance-remaining! i next)
            (format "安装子插件 ~a (实例 ~a)" (plugin-name child) child-id)])]))

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
;弹出一项撤销 (遇到还在的子实例时先请它退出), 撤销栈已空时卸载完毕; 返回描述,
;在等子实例时返回 #f. 只在held?不成立时调用
(define (undo-one! m i)
  (define provisions
    (manager-provisions m))
  (match (instance-undo-stack i)
    ['()
     (set-instance-phase! i 'inactive)
     (if (instance-failure i)
         (format "卸载完毕 -> inactive (此次卸载由加载失败引起: ~a)"
                 (instance-failure i))
         "卸载完毕 -> inactive")]
    [(cons (undo-op key used-id tok undo) rest)
     ;; 逆作用在"现在"的状态上, 所以别人在中间做过的事会保留下来 (前提是撤销独立性, 见 M1 开头)
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
            (format "跳过撤销提供: ~a (编号 ~a) 已不存在" key used-id)])]
    [(cons (undo-spawn child-id) rest)
     ;; 先请子实例退出, 等它真的被移除了再弹出这一项
     (define child (instance-ref m child-id))
     (cond [(not child)
            (set-instance-undo-stack! i rest)
            (format "子实例 ~a 已被移除, 弹出它的spawn项" child-id)]
           [(not (instance-disposed? child))
            (set-instance-disposed?! child #t)
            (format "要求子实例 ~a (插件 ~a) 退出"
                    child-id (instance-name child))]
           [else #f])]))   ; 已经请它退出了, 等着

;让实例id走一步; 返回描述字符串, 无事可做 (或实例不存在) 时返回#f
(define (step! m id)
  (define i (instance-ref m id))
  (and i (step-instance! m id i)))
(define (step-instance! m id i)
  (define name (instance-name i))
  (define wanted (wanted-view m i))
  (match (instance-phase i)
    ['inactive
     (cond [(and (instance-disposed? i) (has-children? m id))
            ;有子实例的实例不能被移除 (防御性的检查: 按 LIFO 卸载到 inactive 时,
            ;子实例都已经被移除了, 所以实际走不到这里)
            #f]
           [(instance-disposed? i)
            (hash-remove! (manager-instances m) id)
            (format "实例 ~a (插件 ~a) 已弃置且卸载完毕, 从管理器中移除"
                    id name)]
           [(and (not (instance-failure i)) wanted)
            (define body (plugin-body (instance-plugin i)))
            (define present (present-optional i wanted))
            (set-instance-phase! i 'loading)
            ;按在场集选变体
            (set-instance-remaining!
             i (if (procedure? body) (body present) body))
            (set-instance-undo-stack! i '())
            (set-instance-view! i wanted)
            (format "实例 ~a (插件 ~a) 开始加载, 依赖 (服务 . 编号): ~a~a"
                    id name (hash->list wanted)
                    (if (null? (instance-optional i))
                        ""
                        (format ", 在场的可选依赖: ~a" present)))]
           [else #f])]
    ;视图过期时开始卸载; 加载到一半时也一样 (中途改道), 已经走完的那一步留在撤销栈里
    ;总是立即改道. 演算还允许视图过期后让在途的步骤落地 (差异 h), 这里只取立即改道这一种调度
    [(or 'loading 'active)
     #:when (not (equal? wanted (instance-view i)))
     (set-instance-phase! i 'unloading)
     (format "实例 ~a (插件 ~a) 开始卸载, 原因: ~a"
             id name
             (if (instance-disposed? i)
                 "被要求移除"
                 (format "依赖变化, 原视图 ~a, 现在~a~a"
                         (hash->list (instance-view i))
                         (if wanted
                             (format "应为 ~a" (hash->list wanted))
                             "有依赖不可用")
                         ;在场集变化引起的重载
                         (let ([before (present-optional i (instance-view i))]
                               [after (and wanted (present-optional i wanted))])
                           (if (and after (not (equal? before after)))
                               (format "; 在场的可选依赖从 ~a 变为 ~a" before after)
                               "")))))]
    ['loading (run-instruction! m id i)]
    ['active #f]
    ['unloading (and (not (held? m id i)) (undo-one! m i))]))

;反复挑一个能走的实例走一步, 直到没有实例能走 (静止)
;order决定尝试实例的顺序; 返回 (实例id . 描述) 的列表
(define (settle! m
                 #:order [order (λ (ids) (sort ids <))]
                 #:trace [trace void])
  (let loop ([log '()])
    (define entry
      (for/or ([id (order (hash-keys (manager-instances m)))])
        (define message (step! m id))
        (and message (cons id message))))
    (cond [entry
           (trace (car entry) (cdr entry))
           (loop (cons entry log))]
          [else (reverse log)])))
;随机顺序, 用于检查不同调度下的结果是否一致
(define (random-order seed)
  (define rng (make-pseudo-random-generator))
  (parameterize ([current-pseudo-random-generator rng])
    (random-seed seed))
  (λ (ids)
    (parameterize ([current-pseudo-random-generator rng])
      (shuffle ids))))

;静止时每个实例都安定: 加载失败, 或应当不运行且未运行, 或以正确视图active;
;并且没有可以移除的实例 (已弃置, inactive, 没有子实例)
(define (settled? m)
  (for/and ([(id i) (manager-instances m)])
    (define wanted (wanted-view m i))
    (match (instance-phase i)
      ['inactive (and (or (instance-failure i) (not wanted))
                      (not (and (instance-disposed? i)
                                (not (has-children? m id)))))]
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

;;; 编排操作 (外部输入); 前提不满足时报错.
;;; 不再自动 settle!: 编排可以在任何时候插进来, 包括别的实例加载到一半的时候

(define (existing-instance who m id)
  (or (instance-ref m id)
      (error who "没有编号为 ~a 的实例" id)))
;装上插件: 先停在 inactive, 依赖都可用时由 settle! 加载. 返回实例id
(define (install! m plug #:trace [trace void])
  (cond [(provider-conflict m plug)
         => (λ (existing)
              (error 'install! "~a 与 ~a 提供了相同的服务"
                     (plugin-name plug) (instance-name existing)))])
  (unless (null? (set-intersect (plugin-optional plug) (plugin-provides plug)))
    (error 'install! "~a 可选依赖自己提供的服务" (plugin-name plug)))
  (define id (add-instance! m plug #f))
  (trace id (format "装上实例 ~a (插件 ~a), 依赖 ~a" id (plugin-name plug) (plugin-deps plug)))
  id)
;移除实例: 标记为已弃置; 它的使用者先卸载, 它再卸载, 最后从管理器中删除
(define (dispose! m id #:trace [trace void])
  (set-instance-disposed?!
   (existing-instance 'dispose! m id) #t)
  (trace id (format "要求移除实例 ~a" id)))
;重启: 强制卸载, 卸载完后重新加载; 加载到一半时也可以
(define (restart! m id #:trace [trace void])
  (define i (existing-instance 'restart! m id))
  (unless (and (not (instance-disposed? i))
               (memq (instance-phase i) '(loading active)))
    (error 'restart! "实例 ~a 不在loading或active, 或已弃置" id))
  (set-instance-phase! i 'unloading)
  (trace id (format "实例 ~a (插件 ~a) 开始卸载, 原因: 被要求重启" id (instance-name i))))
;重试: 只对加载失败后停在inactive的实例有效
(define (reset! m id #:trace [trace void])
  (define i (existing-instance 'reset! m id))
  (unless (and (eq? (instance-phase i) 'inactive) (instance-failure i))
    (error 'reset! "实例 ~a 不是加载失败后的inactive实例" id))
  (set-instance-failure! i #f)
  (trace id (format "重试实例 ~a" id)))
;实例对一个事件作出反应, 反应是reacts中第index个插件的子实例
;返回子实例的id; 提前撤销这次反应就是dispose!这个子实例
;第index个处理器是一族时, 装上它在载荷payload处的插件
(define (react! m id index [payload (void)] #:trace [trace void])
  (define i (existing-instance 'react! m id))
  (define reactions (plugin-reacts (instance-plugin i)))
  (unless (and (eq? (instance-phase i) 'active)
               (not (instance-disposed? i)))
    (error 'react! "实例 ~a 不是未弃置的active实例" id))
  (unless (and (exact-nonnegative-integer? index)
               (< index (length reactions)))
    (error 'react! "实例 ~a 没有第 ~a 个事件处理器" id index))
  (define handler (list-ref reactions index))
  (define child
    (cond [(plugin? handler)
           (unless (void? payload)
             (error 'react! "实例 ~a 的第 ~a 个事件处理器不是一族, 不接受载荷" id index))
           handler]
          [(void? payload)
           (error 'react! "实例 ~a 的第 ~a 个事件处理器是一族, 需要载荷" id index)]
          [else (handler payload)]))
  (cond [(provider-conflict m child)
         => (λ (existing)
              (error 'react! "~a 与 ~a 提供了相同的服务"
                     (plugin-name child) (instance-name existing)))])
  (define child-id (add-instance! m child id))
  (push-undo! (undo-spawn child-id) i)
  (trace id (format "实例 ~a 作出反应: 子实例 ~a (插件 ~a)" id child-id (plugin-name child)))
  child-id)

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
    (printf " ~a#~a~a=~a~a" (instance-name i) id
            (if (instance-parent i) (format "(父#~a)" (instance-parent i)) "")
            (instance-phase i)
            (cond [(instance-failure i) "(失败)"]
                  [(eq? (instance-phase i) 'inactive) "(等待)"]
                  [else ""])))
  (newline)
  (printf "  -- 服务:")
  (when (zero? (hash-count (manager-provisions m))) (printf " (无)"))
  (for ([key (sort (hash-keys (manager-provisions m)) string<? #:key ~a)])
    (define p (provision-ref m key))
    (printf " ~a[编号~a, 由#~a提供]=~a" key (provision-id p) (provision-owner p)
            (case key
              [(tools) (sort (hash-keys (provision-state p)) string<?)]
              [(events) (sort (hash->list (provision-state p)) < #:key car)]
              [else (state-of m key)])))
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
;spawn: 父插件在加载中安装两个子插件, 中间自己再登记一个条目
(define grep-tool
  (plugin "grep-tool" '(tools) '()
          (prog ('tools (register "grep" "搜索")) (Done))))
(define sed-tool
  (plugin "sed-tool" '(tools) '()
          (prog ('tools (register "sed" "流编辑")) (Done))))
(define toolkit
  (plugin "toolkit" '(tools) '()
          (prog (spawn grep-tool)
                ('tools (register "help" "工具箱帮助"))
                (spawn sed-tool)
                (Done))))
(define bus
  (plugin "bus" '() '(events)
          (prog (serve 'events (hash))
                (Done))))
(define ping
  (plugin "ping" '(events) '()
          (prog ('events (on "tick" "ping"))
                (Done))))
;watcher 自己登记一个处理器; 每次反应装上一个 ping, 登记一个相同的处理器
(define watcher
  (plugin "watcher" '(events) '()
          (prog ('events (on "start" "watcher"))
                (Done))
          (list ping)))

;登记两个条目, 用来演示加载到一半时改道
(define cat-tool
  (plugin "cat-tool" '(tools) '()
          (prog ('tools (register "cat2" "打印文件 2"))
                ('tools (register "tac" "倒序打印"))
                (Done))))

;assistant 可选依赖 llm. 有 llm 时往 llm 登记自己, 并提供用 llm 的 summarize;
;没有时提供退化的 summarize. 两个变体都提供 skills
(define llm-provider
  (plugin "llm" '() '(llm)
          (prog (serve 'llm (hash))
                (Done))))
(define assistant
  (plugin "assistant" '() '(skills)
          (λ (present)
            (if (member 'llm present)
                (prog (serve 'skills (hash))
                      ('llm (register "assistant" "使用中"))
                      ('skills (register "summarize" "用 llm 总结"))
                      (Done))
                (prog (serve 'skills (hash))
                      ('skills (register "summarize" "截取前几行"))
                      (Done))))
          #:optional '(llm)))

;agent n 的上下文是服务 (agent n); restrict n 是挂在它上面的效应,
;依赖 (agent n) 并在其中登记一项; guard 的事件处理器是 restrict 这一族
(define (agent-key n) (list 'agent n))
(define (agent n)
  (plugin (format "agent~a" n) '() (list (agent-key n))
          (prog (serve (agent-key n) (hash))
                (Done))))
(define (restrict n)
  (plugin (format "restrict~a" n) (list (agent-key n)) '()
          (prog ((agent-key n) (register "restricted" #t))
                (Done))))
(define guard
  (plugin "guard" '() '()
          (prog (Done))
          (list restrict)))

;服务的内容, 按名字排序; 没有这个服务时为#f
(define (state-of m key)
  (define p (provision-ref m key))
  (and p (sort (hash->list (provision-state p)) string<? #:key (λ (e) (~a (car e))))))
(define (tools-of m)
  (define p (provision-ref m 'tools))
  (and p (sort (hash-keys (provision-state p)) string<?)))

(module+ main
  (define m (make-manager))
  (define (scene title thunk)
    (printf "\n== ~a\n" title)
    (thunk)
    (void (settle! m #:trace print-step))
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
  (scene "装 toolkit: 它在加载中装上两个子插件"
         (λ () (install 'toolkit toolkit)))
  (scene "重启 core: toolkit 和它的子插件也用 tools, 一起卸载再加载, 子插件换了新的实例"
         (λ () (restart! m (hash-ref ids 'core) #:trace print-step)))
  (scene "移除 toolkit: 按 LIFO 拆除, 先请 sed-tool 退出, 再撤 help, 再请 grep-tool 退出"
         (λ () (dispose 'toolkit)))
  (scene "装 bus 和 watcher"
         (λ () (install 'bus bus)
               (install 'watcher watcher)))
  (scene "watcher 反应两次: 两个 ping 子实例各登记一个相同的处理器"
         (λ () (hash-set! ids 'ping (react! m (hash-ref ids 'watcher) 0 #:trace print-step))
               (react! m (hash-ref ids 'watcher) 0 #:trace print-step)))
  (scene "单独撤销第一次反应: 只删掉它用自己令牌登记的那一项"
         (λ () (dispose 'ping)))
  (scene "移除 watcher: 剩下的反应先退出"
         (λ () (dispose 'watcher)))
  (scene "装 bad: 加载失败, 停下"
         (λ () (install 'bad bad)))
  (scene "reset! bad: 重试, 再次失败"
         (λ () (reset! m (hash-ref ids 'bad) #:trace print-step)))
  (scene "编排者换版本: 移除 git, 装上 git2 (插件市场, 自更新都是这样的调用)"
         (λ () (dispose 'git)
               (install 'git2 git2)))
  (scene "中途改道: 新装 cat-tool, 它登记了 cat2 之后 core 重启; 它放弃加载, 撤掉 cat2, 等 core 回来再从头加载"
         (λ () (define c (install! m cat-tool #:trace print-step))
               (print-step c (step! m c))          ; 开始加载
               (print-step c (step! m c))          ; 登记 cat2
               (restart! m (hash-ref ids 'core) #:trace print-step)))
  (scene "先装 assistant: 它可选依赖的 llm 还没有, 不等, 用退化的变体"
         (λ () (install 'assistant assistant)))
  (scene "装 llm: assistant 的在场集变了, 重载, 换成用 llm 的变体"
         (λ () (install 'llm llm-provider)))
  (scene "移除 llm: assistant 先卸载 (llm 被守卫挡着), 撤掉它在 llm 上登记的一项, 再按退化的变体加载"
         (λ () (dispose 'llm)))
  (scene "装 agent3, agent4 与 guard"
         (λ () (install 'agent3 (agent 3))
               (install 'agent4 (agent 4))
               (install 'guard guard)))
  (scene "guard 对两个 agent 的事件各反应一次, 以载荷 3 和 4 装上 restrict 一族, 在各自的上下文里挂一项限制"
         (λ () (react! m (hash-ref ids 'guard) 0 3 #:trace print-step)
               (react! m (hash-ref ids 'guard) 0 4 #:trace print-step)))
  (scene "agent3 结束: 它被守卫挡着, 限制先撤销, agent3 才拆除; agent4 的限制不受影响"
         (λ () (dispose 'agent3)))
  (scene "guard 结束: agent4 上的限制随它撤销, agent4 照常运行"
         (λ () (dispose 'guard))))

(module+ test
  (require rackunit
           (rename-in (submod "..")
                      [install! install!/raw] [dispose! dispose!/raw] [restart! restart!/raw]
                      [reset! reset!/raw] [react! react!/raw]))

  ;; 下面沿用第5层的测试: 每个编排操作之后立即 settle! (#:trace 也传给 settle!).
  ;; 穿插的情形在后面用 /raw 的版本和 step! 单独测
  (define (settling f)
    (make-keyword-procedure
     (λ (kws vals m . args)
       (begin0 (keyword-apply f kws vals m args)
               (keyword-apply settle! kws vals (list m))))))
  (define install! (settling install!/raw))
  (define dispose! (settling dispose!/raw))
  (define restart! (settling restart!/raw))
  (define reset! (settling reset!/raw))
  (define react! (settling react!/raw))

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

  ;; spawn: 子实例跟着父实例加载; 移除父实例时按 LIFO 拆除, 子实例先于父实例被移除
  (let ([m (make-manager)] [log '()])
    (define c (install! m core))
    (define t (install! m toolkit))
    (check-equal? (tools-of m) '("grep" "help" "sed"))
    (check-equal? (hash-count (manager-instances m)) 4)
    (define kids
      (sort (for/list ([(id i) (manager-instances m)] #:when (equal? (instance-parent i) t)) id) <))
    (check-equal? (length kids) 2)
    (dispose! m t #:trace (λ (id message) (set! log (cons (cons id message) log))))
    (check-equal? (tools-of m) '())
    (check-equal? (hash-count (manager-instances m)) 1)
    (define (index-of-step id prefix)
      (for/first ([entry (reverse log)] [k (in-naturals)]
                  #:when (and (= (car entry) id) (string-prefix? (cdr entry) prefix)))
        k))
    ;; 后装的 sed-tool 先退出; 父实例撤 help 在两个子实例之间; 父实例最后被移除
    (check-true (< (index-of-step (cadr kids) "实例") (index-of-step t "撤销 tools")))
    (check-true (< (index-of-step t "撤销 tools") (index-of-step (car kids) "实例")))
    (check-true (< (index-of-step (car kids) (format "实例 ~a (插件 grep-tool) 已弃置" (car kids)))
                   (index-of-step t (format "实例 ~a (插件 toolkit) 已弃置" t))))
    (check-true (settled? m)))

  ;; 重启提供者: 父子实例都用着 tools, 一起卸载再加载; 结果不变
  (let ([m (make-manager)])
    (define c (install! m core))
    (define t (install! m toolkit))
    (restart! m c)
    (check-equal? (tools-of m) '("grep" "help" "sed"))
    (check-equal? (hash-count (manager-instances m)) 4)
    (check-true (settled? m)))

  ;; 单独移除一个启动时装的子实例: 父实例不受影响; 之后移除父实例时弹出失效的spawn项
  (let ([m (make-manager)])
    (void (install! m core))
    (define t (install! m toolkit))
    (define grep-id
      (for/first ([(id i) (manager-instances m)]
                  #:when (equal? (instance-name i) "grep-tool"))
        id))
    (dispose! m grep-id)
    (check-equal? (tools-of m) '("help" "sed"))
    (check-eq? (instance-phase (instance-ref m t)) 'active)
    (define log '())
    (dispose! m t #:trace (λ (id message) (set! log (cons message log))))
    (check-not-false (member (format "子实例 ~a 已被移除, 弹出它的spawn项" grep-id) log))
    (check-equal? (tools-of m) '()))

  ;; 子插件与现存实例提供相同的服务: 父实例加载失败
  (let ([m (make-manager)])
    (void (install! m core))
    (define p (install! m (plugin "bundle" '() '() (prog (spawn core) (Done)))))
    (check-equal? (instance-failure (instance-ref m p)) "子插件 core 与 core 提供了相同的服务"))

  ;; react: 相同的处理器登记两次, 令牌让撤销只删自己那一项
  (let ([m (make-manager)])
    (void (install! m bus))
    (define w (install! m watcher))
    (check-exn exn:fail? (λ () (react! m w 1)))
    (define ping1 (react! m w 0))
    (define ping2 (react! m w 0))
    (check-equal? (handlers-for m "tick") '("ping" "ping"))
    (check-equal? (instance-parent (instance-ref m ping1)) w)
    ;; 各次登记的令牌: watcher 自己的一项, 以及第二次反应的一项
    (define (tok-of id) (undo-op-tok (last (instance-undo-stack (instance-ref m id)))))
    (define keep (sort (list (tok-of w) (tok-of ping2)) <))
    (dispose! m ping1)
    (check-equal? (handlers-for m "tick") '("ping"))
    (check-equal? (sort (hash-keys (provision-state (provision-ref m 'events))) <) keep)
    (check-false (instance-ref m ping1))
    (check-true (and (instance-ref m ping2) #t))
    (check-eq? (instance-phase (instance-ref m w)) 'active)
    ;; 父实例卸载时, 还在的反应先退出
    (dispose! m w)
    (check-equal? (handlers-for m "tick") '())
    (check-equal? (handlers-for m "start") '())
    (check-false (instance-ref m ping2))
    (check-true (settled? m)))

  ;; 反应不会重放: 重启 bus 之后 watcher 重新加载, 之前的反应都已撤掉
  (let ([m (make-manager)])
    (define b (install! m bus))
    (define w (install! m watcher))
    (void (react! m w 0))
    (restart! m b)
    (check-eq? (instance-phase (instance-ref m w)) 'active)
    (check-equal? (handlers-for m "start") '("watcher"))
    (check-equal? (handlers-for m "tick") '())
    (check-equal? (hash-count (manager-instances m)) 2)
    ;; react! 要求未弃置的active实例
    (check-exn exn:fail? (λ () (react! m b 0)))
    (dispose! m b)
    (check-exn exn:fail? (λ () (react! m w 0))))

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
    (check-false (instance-failure (instance-ref m s))))

  ;;; 可选依赖

  ;; 两种安装次序 (先 llm 或先 assistant) 终于同一状态; assistant 后见到 llm 时重载.
  ;; 第一个装上之后只先走 k 步就装第二个, 所以两者的加载可以交错
  (define (optional-run first second order [k +inf.0])
    (define m (make-manager))
    (define ids (make-hash))
    (hash-set! ids first (install!/raw m (if (eq? first 'llm) llm-provider assistant)))
    (define log1
      (let loop ([k k] [log '()])
        (define entry
          (and (> k 0)
               (for/or ([id (order (hash-keys (manager-instances m)))])
                 (define message (step! m id))
                 (and message (cons id message)))))
        (if entry (loop (sub1 k) (cons entry log)) (reverse log))))
    (hash-set! ids second (install!/raw m (if (eq? second 'llm) llm-provider assistant)))
    (define log2 (settle! m #:order order))
    (check-true (settled? m))
    (values m ids (map cdr (append log1 log2))))
  (define-values (m-a ids-a log-a) (optional-run 'llm 'assistant (λ (ids) (sort ids <))))
  (define-values (m-b ids-b log-b) (optional-run 'assistant 'llm (λ (ids) (sort ids <))))
  (check-equal? (state-of m-a 'skills) '(("summarize" . "用 llm 总结")))
  (check-equal? (state-of m-a 'llm) '(("assistant" . "使用中")))
  (check-equal? (list (state-of m-b 'skills) (state-of m-b 'llm))
                (list (state-of m-a 'skills) (state-of m-a 'llm)))
  (check-not-false (findf (λ (s) (string-contains? s "在场的可选依赖从")) log-b))
  (check-false (findf (λ (s) (string-contains? s "在场的可选依赖从")) log-a))
  ;; 各种调度顺序下, 第二个插件在第一个加载到不同阶段时装上: 结果相同
  (define optional-logs
    (for*/list ([firsts (list '(llm assistant) '(assistant llm))]
                [seed (in-range 50)])
      (define-values (m ids log)
        (optional-run (car firsts) (cadr firsts) (random-order seed) (modulo seed 5)))
      (check-equal? (list (state-of m 'skills) (state-of m 'llm))
                    (list (state-of m-a 'skills) (state-of m-a 'llm))
                    (format "~a 种子 ~a" firsts seed))
      log))
  ;; 这些执行确实各不相同, 不是同一个调度跑了一百遍
  (check-true (> (set-count (list->set optional-logs)) 10))
  ;; llm 消失: llm 的卸载被守卫挡住; assistant 先卸载, 撤掉它在 llm 上登记的一项, 再按退化的变体加载
  (dispose! m-a (hash-ref ids-a 'llm))
  (check-true (settled? m-a))
  (check-equal? (state-of m-a 'skills) '(("summarize" . "截取前几行")))
  (check-false (state-of m-a 'llm))
  (check-eq? (instance-phase (instance-ref m-a (hash-ref ids-a 'assistant))) 'active)

  ;; 不在场的可选依赖不能操作; 可选依赖不阻止加载
  (let ([m (make-manager)])
    (define peek
      (install! m (plugin "peek" '() '() (prog ('llm (register "x" 1)) (Done))
                          #:optional '(llm))))
    (check-equal? (instance-failure (instance-ref m peek)) "实例无法访问服务 llm")
    (define a (install! m assistant))
    (check-eq? (instance-phase (instance-ref m a)) 'active))

  ;;; 可选依赖的义务 (取舍见文件开头): 违反时活锁, 运行时不检查

  ;; 最多走 n 步; 静止了返回 #t
  (define (quiet-within? m n)
    (let loop ([n n])
      (cond [(not (for/or ([id (hash-keys (manager-instances m))]) (step! m id))) #t]
            [(zero? n) #f]
            [else (loop (sub1 n))])))
  ;; install! 只拦下最简单的一种: 直接装上的插件可选依赖自己提供的服务
  (check-exn #rx"可选依赖自己提供的服务"
             (λ () (install! (make-manager)
                             (plugin "self" '() '(llm) (prog (Done)) #:optional '(llm)))))
  ;; 反例1: 经 spawn 装上的子插件可选依赖自己提供的服务, install! 管不到; 它一上线就重载自己
  (let ([m (make-manager)])
    (define selfie (plugin "selfie" '() '(x) (prog (serve 'x (hash)) (Done)) #:optional '(x)))
    (void (install!/raw m (plugin "par" '() '() (prog (spawn selfie) (Done)))))
    (check-false (quiet-within? m 1000)))
  ;; 反例2: 经可选依赖成环. A 可选依赖 b, B 依赖 a 并提供 b:
  ;; A 一见到 b 就重载, a 随之不可用, B 卸载, b 消失, A 再重载 ...
  (let ([m (make-manager)])
    (void (install!/raw m (plugin "A" '() '(a) (prog (serve 'a (hash)) (Done)) #:optional '(b))))
    (void (install!/raw m (plugin "B" '(a) '(b) (prog (serve 'b (hash)) (Done)))))
    (check-false (quiet-within? m 1000)))
  ;; 对照: 必需依赖成环时不活锁, 而是谁也不加载, 静止
  (let ([m (make-manager)])
    (void (install!/raw m (plugin "C" '(d) '(c) (prog (serve 'c (hash)) (Done)))))
    (void (install!/raw m (plugin "D" '(c) '(d) (prog (serve 'd (hash)) (Done)))))
    (check-true (quiet-within? m 10))
    (check-true (settled? m)))

  ;;; 交集生命期

  (define (agent-setup)
    (define m (make-manager))
    (define a (install! m (agent 3)))
    (define g (install! m guard))
    (define r (react! m g 0 3))
    (values m a g r))
  ;; 一族处理器要载荷; 效应在 agent 的上下文里登记
  (let-values ([(m a g r) (agent-setup)])
    (check-exn #rx"需要载荷" (λ () (react! m g 0)))
    (check-equal? (state-of m (agent-key 3)) '(("restricted" . #t)))
    (check-eq? (instance-phase (instance-ref m r)) 'active)
    (check-equal? (instance-parent (instance-ref m r)) g))
  ;; agent 结束: 限制先撤销, agent 才撤回自己的上下文
  (let-values ([(m a g r) (agent-setup)])
    (dispose!/raw m a)
    (check-not-false (step! m a))                    ; agent 开始卸载
    (check-false (step! m a))                        ; 被守卫挡住: 限制还解析着它
    (check-equal? (state-of m (agent-key 3)) '(("restricted" . #t)))
    (check-not-false (step! m r))                    ; 限制的依赖没了, 开始卸载
    (check-not-false (step! m r))                    ; 撤销登记
    (check-equal? (state-of m (agent-key 3)) '())
    (check-not-false (step! m r))                    ; 限制 -> inactive
    (void (settle! m))
    (check-true (settled? m))
    (check-false (instance-ref m a))
    (check-false (state-of m (agent-key 3)))
    ;; 限制的实例停在 inactive, 直到 guard 卸载才被移除
    (check-eq? (instance-phase (instance-ref m r)) 'inactive)
    (check-eq? (instance-phase (instance-ref m g)) 'active)
    (dispose! m g)
    (check-false (instance-ref m r)))
  ;; 插件结束: 限制随插件撤销, agent 照常运行, 上下文完整
  (let-values ([(m a g r) (agent-setup)])
    (dispose! m g)
    (check-true (settled? m))
    (check-false (instance-ref m g))
    (check-false (instance-ref m r))
    (check-eq? (instance-phase (instance-ref m a)) 'active)
    (check-equal? (state-of m (agent-key 3)) '()))
  ;; 编排者义务的反例: 复用 agent 编号时, 停在 inactive 的旧限制在新的上下文里重新加载
  (let-values ([(m a g r) (agent-setup)])
    (dispose! m a)
    (check-eq? (instance-phase (instance-ref m r)) 'inactive)
    (void (install! m (agent 3)))
    (check-eq? (instance-phase (instance-ref m r)) 'active)
    (check-equal? (state-of m (agent-key 3)) '(("restricted" . #t))))
  ;; 普通的处理器不接受载荷
  (let ([m (make-manager)])
    (void (install! m bus))
    (define w (install! m watcher))
    (check-exn #rx"不接受载荷" (λ () (react! m w 0 5))))
  ;; 两个 agent: 一个结束只撤掉它自己的限制
  (let ([m (make-manager)])
    (define a3 (install! m (agent 3)))
    (define a4 (install! m (agent 4)))
    (define g (install! m guard))
    (define r3 (react! m g 0 3))
    (define r4 (react! m g 0 4))
    (dispose! m a3)
    (check-equal? (state-of m (agent-key 4)) '(("restricted" . #t)))
    (check-eq? (instance-phase (instance-ref m r4)) 'active)
    (check-eq? (instance-phase (instance-ref m r3)) 'inactive)
    (check-true (settled? m)))

  ;;; 以下是第6层新增的测试: 编排与生命周期步穿插

  ;; 中途改道: cat-tool 加载到一半时 core 重启, tools 不再可见, cat-tool 放弃加载,
  ;; 撤掉已经登记的 cat2 (不算失败), 等 core 重新提供后再从头加载
  (let ()
    (define m (make-manager))
    (define c (install!/raw m core))
    (define t (install!/raw m cat-tool))
    (define (step-until! id phase)
      (let loop ()
        (unless (eq? (instance-phase (instance-ref m id)) phase)
          (step! m id)
          (loop))))
    (step-until! c 'active)
    (check-not-false (step! m t))                    ; 开始加载
    (check-eq? (instance-phase (instance-ref m t)) 'loading)
    (check-not-false (step! m t))                    ; 登记 cat2
    (check-equal? (tools-of m) '("cat2"))
    (restart!/raw m c)
    (check-false (step! m c))                        ; 被守卫挡着: cat-tool 的视图里还有 tools
    (check-not-false (step! m t))                    ; 改道
    (check-eq? (instance-phase (instance-ref m t)) 'unloading)
    (check-false (instance-failure (instance-ref m t)))
    (check-not-false (step! m t))                    ; 撤销 cat2
    (check-equal? (tools-of m) '())
    (void (settle! m))
    (check-true (settled? m))
    (check-equal? (tools-of m) '("cat2" "tac")))

  ;; 守卫逐步看: core+ 在提供之后登记了 builtin; 重启时只要 shell 还在使用 tools,
  ;; core+ 一步也不走, shell 卸载时看到的是 core+ 的全部效应
  (let ()
    (define m (make-manager))
    (define c (install!/raw m core+))
    (define s (install!/raw m shell))
    (void (settle! m))
    (restart!/raw m c)
    (check-false (step! m c))                        ; 被守卫挡着
    (check-not-false (step! m s))                    ; shell 开始卸载
    (check-not-false (step! m s))
    (check-not-false (step! m s))                    ; 撤掉 cat, ls
    (check-equal? (tools-of m) '("builtin"))
    (check-false (step! m c))                        ; shell 还没卸载完
    (check-not-false (step! m s))                    ; shell -> inactive
    (check-not-false (step! m c))                    ; 现在才撤 builtin
    (check-equal? (tools-of m) '())
    (void (settle! m))
    (check-true (settled? m))
    (check-equal? (tools-of m) '("builtin" "cat" "ls")))

  ;; settled?: 已弃置且卸载完毕, 但还没被移除的实例不算安定
  (let ()
    (define m (make-manager))
    (void (install!/raw m core))
    (define g (install!/raw m git))
    (void (settle! m))
    (dispose!/raw m g)
    (let loop ()
      (unless (eq? (instance-phase (instance-ref m g)) 'inactive)
        (step! m g)
        (loop)))
    (check-false (settled? m))
    (check-not-false (step! m g))                    ; 移除
    (check-false (instance-ref m g))
    (check-true (settled? m)))

  ;; 与调度无关: 编排操作的次序固定, 每个编排操作在随机的几步 (k 步) 之后插进来
  ;; (react! 要等 watcher active, 所以在静止之后),
  ;; 实例按随机顺序走; 静止后的结果总是相同 (比较插件名, 阶段和服务内容, 不比较编号)
  (define (run-scenario seed)
    (define m (make-manager))
    (define order (if seed (random-order seed) (λ (ids) (sort ids <))))
    (define rng (make-pseudo-random-generator))
    (parameterize ([current-pseudo-random-generator rng]) (random-seed (or seed 0)))
    (define messages '())
    ;; 先只走随机的几步 (seed 为 #f 时走到静止), 然后施加下一个编排操作
    (define (some-steps!)
      (define k (if seed
                    (parameterize ([current-pseudo-random-generator rng]) (random 6))
                    +inf.0))
      (let loop ([k k])
        (define entry
          (and (> k 0)
               (for/or ([id (order (hash-keys (manager-instances m)))])
                 (define message (step! m id))
                 (and message (cons id message)))))
        (when entry
          (set! messages (cons (cdr entry) messages))
          (loop (sub1 k)))))
    (install!/raw m shell)
    (some-steps!)
    (define t (install!/raw m toolkit))
    (some-steps!)
    (define c (install!/raw m core))
    (some-steps!)
    (install!/raw m git)
    (install!/raw m bus)
    (define w (install!/raw m watcher))
    (some-steps!)
    ;; 重启只对 loading 或 active 的实例有效; 还没开始加载时先走到它开始
    (let loop ()
      (unless (memq (instance-phase (instance-ref m c)) '(loading active))
        (void (settle! m #:order order))
        (loop)))
    (restart!/raw m c)
    (some-steps!)
    (dispose!/raw m t)
    (some-steps!)
    (set! messages (append (map cdr (settle! m #:order order)) messages))
    ;; 反应要等 watcher active
    (react!/raw m w 0)
    (react!/raw m w 0)
    (some-steps!)
    (restart!/raw m w)
    (set! messages (append (map cdr (settle! m #:order order)) messages))
    (check-true (settled? m))
    (values
     (list (sort (for/list ([i (in-hash-values (manager-instances m))])
                   (format "~a:~a:~a" (instance-name i) (instance-phase i)
                           (and (instance-failure i) #t)))
                 string<?)
           (tools-of m)
           (sort (map ~a (hash-values (provision-state (provision-ref m 'events))))
                 string<?))
     messages))
  (define-values (expected _) (run-scenario #f))
  (check-equal? (car expected) '("bus:active:#f" "core:active:#f" "git:active:#f"
                                 "shell:active:#f" "watcher:active:#f"))
  (check-equal? (cadr expected) '("cat" "git" "ls"))
  (for ([seed (in-range 200)])
    (define-values (result messages) (run-scenario seed))
    (check-equal? result expected (format "种子 ~a" seed))
    ;; 按守卫, 跳过撤销的分支不会被走到
    (check-false (findf (λ (s) (string-prefix? s "跳过")) messages)
                 (format "种子 ~a" seed))))
