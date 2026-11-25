#lang racket
;渐进的插件管理器, 第11层: 作用域与事件.
;计划与各层的说明见 README.md. 每层是一个完整的文件, 不依赖前面的层; 相邻两层的差别见 diffs/.
;本层新增三件事, 都是 Cordis 的 ctx 作用域带来的:
;  1. 沿父链查找服务 (Cordis: locate): 子实例不声明依赖, 也能用祖先实例提供的服务.
;     父实例先提供, 再装子实例时这是安全的: 父实例按 LIFO 卸载, 子实例在服务撤回之前就退出了.
;     反过来 (先装子实例, 再提供) 时, 服务先于子实例撤回, 子实例的撤销被跳过 ——
;     这就是 docs/DESIGN.md 2.1 节 e 所说的、上游 Cordis 由测试确认的问题.
;  2. 隔离 (Cordis: isolate): (isolate 插件 键 标签) 把插件 (连同它的子插件和处理器) 里的键改名,
;     改名后的服务是另一个服务, 两个作用域各有一份, 互不冲突. 不需要新机制, 只是改名.
;     事件总线也可以隔离; 这时分发要指明是哪一个 (emit 的 #:service).
;  3. 事件分发: emit 依次调用处理器, 返回结果的列表; bail 返回第一个不是 #f 的结果.
;     ctx-on 可以带 #:prepend, 排到前面. 分发看得到处理器的次序, 而登记的次序随调度而变:
;     两个都不 prepend 的处理器抢同一个事件时, 谁先处理与调度有关 (合流不成立, 见 layers/L3.rkt 的反例).
;     分发不是生命周期的一步: 它只读状态, 处理器在操作之外被调用 (见 docs/DESIGN.md D6).
;留给下一层的问题: 到这里管理器一直守着一条纪律 —— 共享状态只能经带逆的操作改动.
;  真实的 Cordis 不守, 下一层把它放开, 看哪些保证会失效.
(require (only-in racket/control reset-at shift-at))
(provide (all-defined-out))

;operation : 令牌 状态 -> op-result 或 #f (#f 表示操作被拒绝)
;令牌是运行时交给这次操作的新鲜编号, 用作操作生成出来的东西的身份 (如事件处理器)
;undo : 状态 -> 状态, 撤销这次操作; 它作用在撤销时的状态上
(struct op-result (state undo value))

;program ir: 运行时内部的表示, 插件作者不再直接写它
;next : void -> ir 是续延: 指令执行之后才运行 apply 里后面的代码
(struct Provide (key init next))
;cont : value -> ir
(struct Op (key operation cont))
;安装子插件child, 其生命期不超过当前实例
(struct Spawn (child config next))
(struct Done ())
(struct Fail (why))

;;; ctx 与 apply

;apply 外面的提示符; ctx 调用中止到这里
(define apply-tag (make-continuation-prompt-tag 'apply))
;ctx 记下开始加载时在场的可选依赖, 实例的配置, 以及作用域的改名 (键 -> 键, 见isolate);
;load 是这次加载的标识, ctx 只在这次加载的 apply 里有效
(struct ctx (present config rename load))
;把 apply 变成程序: 运行到第一次 ctx 调用为止. apply 可以拿 (ctx) 或 (ctx config)
;抛出的任何值都是加载失败; 只有用户中断 (break) 照常传出去
(define (apply->program apply c)
  (reset-at apply-tag
    (with-continuation-mark load-key (ctx-load c)
      (with-handlers ([(λ (e) (not (exn:break? e))) (λ (e) (Fail (raised->why e)))])
        (if (procedure-arity-includes? apply 2)
            (apply c (ctx-config c))
            (apply c))
        (Done)))))
(define (raised->why e)
  (format "apply 抛出异常: ~a" (if (exn? e) (exn-message e) e)))
;当前正在运行的是哪次加载的 apply
(define load-key (make-continuation-mark-key 'load))
(define (check-in-apply who c)
  (unless (and (continuation-prompt-available? apply-tag)
               (eq? (continuation-mark-set-first #f load-key #f apply-tag) (ctx-load c)))
    (error who "ctx 只能在它所属实例的这次 apply 里同步使用")))
;在服务key上执行操作, 返回操作的结果 (Cordis: ctx.<服务>.<方法>(...))
(define (ctx-use c key operation)
  (check-in-apply 'ctx-use c)
  (define key* ((ctx-rename c) key))
  (shift-at apply-tag k (Op key* operation k)))
;提供服务 (Cordis: ctx.provide)
(define (ctx-provide c key init)
  (check-in-apply 'ctx-provide c)
  (define key* ((ctx-rename c) key))
  (shift-at apply-tag k (Provide key* init k)))
;装上子插件, 其生命期不超过当前实例 (Cordis: ctx.plugin(child, config));
;子插件在同一个作用域里, 所以也按当前的改名改写
(define (ctx-plugin c child [config #f])
  (check-in-apply 'ctx-plugin c)
  (check-config 'ctx-plugin child config)
  (define child* (rename-plugin child (ctx-rename c)))
  (shift-at apply-tag k (Spawn child* config k)))
;可选依赖是否在场
(define (ctx-has? c key)
  (and (member ((ctx-rename c) key) (ctx-present c)) #t))
;在事件总线上登记处理器, 返回令牌 (Cordis: ctx.on, 返回 disposer);
;prepend 为真时排在不 prepend 的处理器前面
(define (ctx-on c event handler #:prepend [prepend #f])
  (ctx-use c 'events (on event handler #:prepend prepend)))

;reacts是插件列表: 实例active时的事件处理器, 每次反应是一个子实例 (见react!)
;构造时reacts可以省略, 默认没有事件处理器
;optional是可选依赖, 默认没有; apply 是 (ctx -> 任意) 或 (ctx 配置 -> 任意);
;schema 检查配置, 默认什么配置都接受
(struct plugin (name deps optional provides apply reacts schema)
  #:constructor-name make-plugin
  #:omit-define-syntaxes)
(define (plugin name deps provides apply [reacts '()]
                #:optional [optional '()] #:schema [schema (λ (config) #t)])
  (make-plugin name deps optional provides apply reacts schema))
(define (check-config who plug config)
  (unless ((plugin-schema plug) config)
    (error who "插件 ~a 的配置不合法: ~a" (plugin-name plug) config)))
;按改名 rename (键 -> 键) 改写插件: 声明里的键改名; apply 拿到的 ctx 在原有改名之前先做这次改名;
;处理器 (插件或一族) 也同样改写
(define (rename-plugin plug rename)
  (define inner (plugin-apply plug))
  (define (rename-handler h)
    (if (plugin? h)
        (rename-plugin h rename)
        (λ (payload) (rename-plugin (h payload) rename))))
  (make-plugin (plugin-name plug)
               (map rename (plugin-deps plug))
               (map rename (plugin-optional plug))
               (map rename (plugin-provides plug))
               (λ (c [config #f])
                 (define c* (struct-copy ctx c [rename (compose (ctx-rename c) rename)]))
                 (if (procedure-arity-includes? inner 2)
                     (inner c* config)
                     (inner c*)))
               (map rename-handler (plugin-reacts plug))
               (plugin-schema plug)))
;隔离 (Cordis: isolate): 插件里的键key改名为 (key . label), 成为另一个服务
(define (isolate plug key label)
  (rename-plugin plug (λ (k) (if (equal? k key) (cons key label) k))))
;phase 是 'inactive (等待依赖, 或加载失败后停下), 'loading, 'active 或 'unloading;
;remaining 是剩余需要执行的程序;
;view 是开始加载时记下的视图: 依赖名 -> provision的编号; failure 是失败的原因;
;disposed? 表示已被要求移除; parent是父实例的id, 直接install!的实例为#f; config是配置
(struct instance
  (plugin phase remaining undo-stack view failure disposed? parent config)
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
;与plug提供相同服务的现存实例 (不算except), 没有则为#f
(define (provider-conflict m plug #:except [except #f])
  (for/first ([i (in-hash-values (manager-instances m))]
              #:when (and (not (eq? i except))
                          (for/or ([key (plugin-provides plug)])
                            (member key (instance-claims i)))))
    i))
;实例占着的服务: 它声明提供的, 加上撤销栈里还没撤回的.
;replace! 之后两者可以不同: 换下来的插件提供的服务, 要等卸载撤回之后才空出来
(define (instance-claims i)
  (append (instance-provides i)
          (for/list ([entry (instance-undo-stack i)] #:when (undo-provide? entry))
            (undo-provide-key entry))))
(define (add-instance! m plug parent [config #f])
  (define id (fresh-id! m))
  (hash-set! (manager-instances m) id
             (instance plug 'inactive #f '() #f #f #f parent config))
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
    ;情况2: 自己或某个祖先实例提供的 (沿父链查找, Cordis: locate)
    [else (and (ancestor-or-self? m id (provision-owner p)) p)]))
;owner 是 id 自己, 或 id 的某个祖先实例
(define (ancestor-or-self? m id owner)
  (let loop ([id id])
    (cond [(not id) #f]
          [(= id owner) #t]
          [else (loop (match (instance-ref m id)
                        [#f #f]
                        [i (instance-parent i)]))])))

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
            (set-instance-remaining! i (next (void)))
            (format "提供 ~a (编号 ~a)" key new-id)])]
    [(Spawn child config next)
     (cond [(provider-conflict m child)
            => (λ (existing)
                 (fail! (format "子插件 ~a 与 ~a 提供了相同的服务"
                                (plugin-name child) (instance-name existing))
                        i))]
           [else
            (define child-id (add-instance! m child id config))
            (push-undo! (undo-spawn child-id) i)
            (set-instance-remaining! i (next (void)))
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
            (define present (present-optional i wanted))
            (set-instance-phase! i 'loading)
            ;apply 拿到的 ctx 记下在场集, 由 ctx-has? 选变体
            (set-instance-remaining!
             i (apply->program (plugin-apply (instance-plugin i))
                               (ctx present (instance-config i) values (gensym 'load))))
            (set-instance-undo-stack! i '())
            (set-instance-view! i wanted)
            (format "实例 ~a (插件 ~a) 开始加载, 依赖 (服务 . 编号): ~a~a"
                    id name (hash->list wanted)
                    (if (null? (instance-optional i))
                        ""
                        (format ", 在场的可选依赖: ~a" present)))]
           [else #f])]
    ;视图过期时开始卸载; 加载到一半时也一样 (中途改道), 已经走完的那一步留在撤销栈里
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
;事件处理器表: 状态是 令牌 -> hook 的hash, 令牌的大小即登记的顺序
;同一个处理器可以登记多次, 令牌区分各次登记, 逆只删掉自己这一次
;处理器是过程 (分发时以事件参数调用), 或任意值 (分发时就是结果)
(struct hook (event handler prepend?) #:transparent)
(define ((on event handler #:prepend [prepend #f]) tok state)
  (op-result
   (hash-set state tok (hook event handler prepend))
   (λ (state) (hash-remove state tok))
   tok))

;;; 编排操作 (外部输入); 前提不满足时报错.
;;; 不再自动 settle!: 编排可以在任何时候插进来, 包括别的实例加载到一半的时候

(define (existing-instance who m id)
  (or (instance-ref m id)
      (error who "没有编号为 ~a 的实例" id)))
;装上插件: 先停在 inactive, 依赖都可用时由 settle! 加载. 返回实例id
(define (install! m plug #:config [config #f] #:trace [trace void])
  (cond [(provider-conflict m plug)
         => (λ (existing)
              (error 'install! "~a 与 ~a 提供了相同的服务"
                     (plugin-name plug) (instance-name existing)))])
  (unless (null? (set-intersect (plugin-optional plug) (plugin-provides plug)))
    (error 'install! "~a 可选依赖自己提供的服务" (plugin-name plug)))
  (check-config 'install! plug config)
  (define id (add-instance! m plug #f config))
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
;换配置 (Cordis: fiber.update): 在线或加载中的实例卸载后按新配置加载; 失败的实例清除失败, 重试
(define (update! m id config #:trace [trace void])
  (define i (existing-instance 'update! m id))
  (when (instance-disposed? i)
    (error 'update! "实例 ~a 已弃置" id))
  (check-config 'update! (instance-plugin i) config)
  (set-instance-config! i config)
  (set-instance-failure! i #f)
  (when (memq (instance-phase i) '(loading active))
    (set-instance-phase! i 'unloading))
  (trace id (format "实例 ~a (插件 ~a) 换配置为 ~a" id (instance-name i) config)))
;原地换插件 (Cordis: registry.replace): 实例编号不变; 清除失败, 按新插件重新加载
(define (replace! m id plug #:config [config #f] #:trace [trace void])
  (define i (existing-instance 'replace! m id))
  (when (instance-disposed? i)
    (error 'replace! "实例 ~a 已弃置" id))
  (cond [(provider-conflict m plug #:except i)
         => (λ (existing)
              (error 'replace! "~a 与 ~a 提供了相同的服务"
                     (plugin-name plug) (instance-name existing)))])
  (unless (null? (set-intersect (plugin-optional plug) (plugin-provides plug)))
    (error 'replace! "~a 可选依赖自己提供的服务" (plugin-name plug)))
  (check-config 'replace! plug config)
  (define old-name (instance-name i))
  (set-instance-plugin! i plug)
  (set-instance-config! i config)
  (set-instance-failure! i #f)
  (when (memq (instance-phase i) '(loading active))
    (set-instance-phase! i 'unloading))
  (trace id (format "实例 ~a 的插件从 ~a 换成 ~a" id old-name (plugin-name plug))))
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
  (check-config 'react! child #f)
  (cond [(provider-conflict m child)
         => (λ (existing)
              (error 'react! "~a 与 ~a 提供了相同的服务"
                     (plugin-name child) (instance-name existing)))])
  (define child-id (add-instance! m child id))
  (push-undo! (undo-spawn child-id) i)
  (trace id (format "实例 ~a 作出反应: 子实例 ~a (插件 ~a)" id child-id (plugin-name child)))
  child-id)

;事件 event 发生时依次调用的处理器: prepend 的在前 (后登记的更靠前), 其余按登记的顺序
(define (handlers-for m event #:service [key 'events])
  (define p (provision-ref m key))
  (define state (if p (provision-state p) (hash)))
  (define hooks
    (for/list ([tok (sort (hash-keys state) <)]
               #:when (equal? (hook-event (hash-ref state tok)) event))
      (hash-ref state tok)))
  (map hook-handler
       (append (reverse (filter hook-prepend? hooks))
               (filter (negate hook-prepend?) hooks))))
;分发 (Cordis: ctx.emit): 依次调用处理器, 返回结果的列表
(define (emit m event #:service [key 'events] . args)
  (for/list ([h (handlers-for m event #:service key)])
    (if (procedure? h) (apply h args) h)))
;分发到第一个不是 #f 的结果为止 (Cordis: ctx.bail)
(define (bail m event #:service [key 'events] . args)
  (for/or ([h (handlers-for m event #:service key)])
    (if (procedure? h) (apply h args) h)))

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
              [(events) (sort (for/list ([(tok h) (in-hash (provision-state p))])
                                (list tok (hook-event h) (hook-handler h)))
                              < #:key car)]
              [else (state-of m key)])))
  (newline))

;;; 示例插件

(define core
  (plugin "core" '() '(tools)
          (λ (ctx)
            (ctx-provide ctx 'tools (hash)))))
;提供 tools 之后自己再登记一个条目
(define core+
  (plugin "core+" '() '(tools)
          (λ (ctx)
            (ctx-provide ctx 'tools (hash))
            (ctx-use ctx 'tools (register "builtin" "内建")))))
(define shell
  (plugin "shell" '(tools) '()
          (λ (ctx)
            (ctx-use ctx 'tools (register "ls" "列出文件"))
            (ctx-use ctx 'tools (register "cat" "打印文件")))))
(define git
  (plugin "git" '(tools) '()
          (λ (ctx)
            (ctx-use ctx 'tools (register "git" "版本控制")))))
;git 的新版本: 登记的说明不同
(define git2
  (plugin "git2" '(tools) '()
          (λ (ctx)
            (ctx-use ctx 'tools (register "git" "版本控制 (新版)")))))
;先登记 grep, 再登记已被占用的 ls -> 失败; grep 会被自动撤掉
(define bad
  (plugin "bad" '(tools) '()
          (λ (ctx)
            (ctx-use ctx 'tools (register "grep" "搜索"))
            (ctx-use ctx 'tools (register "ls" "冒牌 ls")))))
;spawn: 父插件在加载中安装两个子插件, 中间自己再登记一个条目
(define grep-tool
  (plugin "grep-tool" '(tools) '()
          (λ (ctx) (ctx-use ctx 'tools (register "grep" "搜索")))))
(define sed-tool
  (plugin "sed-tool" '(tools) '()
          (λ (ctx) (ctx-use ctx 'tools (register "sed" "流编辑")))))
(define toolkit
  (plugin "toolkit" '(tools) '()
          (λ (ctx)
            (ctx-plugin ctx grep-tool)
            (ctx-use ctx 'tools (register "help" "工具箱帮助"))
            (ctx-plugin ctx sed-tool))))
(define bus
  (plugin "bus" '() '(events)
          (λ (ctx)
            (ctx-provide ctx 'events (hash)))))
(define ping
  (plugin "ping" '(events) '()
          (λ (ctx)
            (ctx-on ctx "tick" "ping"))))
;watcher 自己登记一个处理器; 每次反应装上一个 ping, 登记一个相同的处理器
(define watcher
  (plugin "watcher" '(events) '()
          (λ (ctx)
            (ctx-on ctx "start" "watcher"))
          (list ping)))

;登记两个条目, 用来演示加载到一半时改道
(define cat-tool
  (plugin "cat-tool" '(tools) '()
          (λ (ctx)
            (ctx-use ctx 'tools (register "cat2" "打印文件 2"))
            (ctx-use ctx 'tools (register "tac" "倒序打印")))))

;assistant 可选依赖 llm. 有 llm 时往 llm 登记自己, 并提供用 llm 的 summarize;
;没有时提供退化的 summarize. 两个变体都提供 skills
(define llm-provider
  (plugin "llm" '() '(llm)
          (λ (ctx)
            (ctx-provide ctx 'llm (hash)))))
(define assistant
  (plugin "assistant" '() '(skills)
          (λ (ctx)
            (ctx-provide ctx 'skills (hash))
            (cond [(ctx-has? ctx 'llm)
                   (ctx-use ctx 'llm (register "assistant" "使用中"))
                   (ctx-use ctx 'skills (register "summarize" "用 llm 总结"))]
                  [else
                   (ctx-use ctx 'skills (register "summarize" "截取前几行"))]))
          #:optional '(llm)))

;agent n 的上下文是服务 (agent n); restrict n 是挂在它上面的效应,
;依赖 (agent n) 并在其中登记一项; guard 的事件处理器是 restrict 这一族
(define (agent-key n) (list 'agent n))
(define (agent n)
  (plugin (format "agent~a" n) '() (list (agent-key n))
          (λ (ctx)
            (ctx-provide ctx (agent-key n) (hash)))))
(define (restrict n)
  (plugin (format "restrict~a" n) (list (agent-key n)) '()
          (λ (ctx)
            (ctx-use ctx (agent-key n) (register "restricted" #t)))))
(define guard
  (plugin "guard" '() '()
          (λ (ctx) (void))
          (list restrict)))

;workspace 提供 files, 再装上子插件 editor; editor 不声明依赖, 沿父链用 files
(define editor
  (plugin "editor" '() '()
          (λ (ctx) (ctx-use ctx 'files (register "draft.txt" "草稿")))))
(define workspace
  (plugin "workspace" '() '(files)
          (λ (ctx)
            (ctx-provide ctx 'files (hash))
            (ctx-plugin ctx editor))))
;反过来: 先装 editor, 再提供 files
(define workspace/bad
  (plugin "workspace/bad" '() '(files)
          (λ (ctx)
            (ctx-plugin ctx editor)
            (ctx-provide ctx 'files (hash)))))

;两个插件都处理审批请求; ask-user 声明 prepend, 总是先问用户
(define (approve request) 'approve)
(define (ask request) 'ask)
(define auto-approve
  (plugin "auto-approve" '(events) '()
          (λ (ctx) (ctx-on ctx "approval" approve))))
(define ask-user
  (plugin "ask-user" '(events) '()
          (λ (ctx) (ctx-on ctx "approval" ask #:prepend #t))))

;alias 按配置登记一个别名; 配置是 (名字 . 指向), 名字必须是字符串
(define alias
  (plugin "alias" '(tools) '()
          (λ (ctx config)
            (ctx-use ctx 'tools (register (car config) (cdr config))))
          #:schema (λ (config) (and (pair? config) (string? (car config))))))

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
         (λ () (dispose 'guard)))
  (scene "装 alias, 配置为 ll -> ls -l"
         (λ () (hash-set! ids 'alias (install! m alias #:config '("ll" . "ls -l") #:trace print-step))))
  (scene "update! alias 为 la -> ls -a: 卸载后按新配置重新加载, 实例编号不变"
         (λ () (update! m (hash-ref ids 'alias) '("la" . "ls -a") #:trace print-step)))
  (scene "update! alias 为 ls -> ls --color: 与 shell 撞名, 加载失败"
         (λ () (update! m (hash-ref ids 'alias) '("ls" . "ls --color") #:trace print-step)))
  (scene "update! alias 回 ll -> ls -l: 失败清除, 按新配置重试"
         (λ () (update! m (hash-ref ids 'alias) '("ll" . "ls -l") #:trace print-step)))
  (scene "replace! 把 git2 的实例原地换回 git: 编号不变"
         (λ () (replace! m (hash-ref ids 'git2) git #:trace print-step)))
  (scene "装 workspace: 它提供 files, 再装上 editor; editor 没有声明依赖, 沿父链用 files"
         (λ () (install 'workspace workspace)))
  (scene "移除 workspace: 按 LIFO, editor 先退出, files 后撤回"
         (λ () (dispose 'workspace)))
  (scene "隔离: 在作用域 sandbox 里另装一套 core 和 toolkit, 与外面的 tools 互不冲突"
         (λ () (install 'sandbox-core (isolate core 'tools "sandbox"))
               (install 'sandbox-toolkit (isolate toolkit 'tools "sandbox"))))
  (scene "装 auto-approve 和 ask-user, 分发审批请求"
         (λ () (install 'auto-approve auto-approve)
               (install 'ask-user ask-user)))
  (printf "  emit approval: ~a, bail approval: ~a\n" (emit m "approval" 'req) (bail m "approval" 'req)))

(module+ test
  (require rackunit
           (rename-in (submod "..")
                      [install! install!/raw] [dispose! dispose!/raw] [restart! restart!/raw]
                      [reset! reset!/raw] [react! react!/raw]
                      [update! update!/raw] [replace! replace!/raw]))

  ;; 下面沿用第5层的测试: 每个编排操作之后立即 settle! (#:trace 也传给 settle!).
  ;; 穿插的情形在后面用 /raw 的版本和 step! 单独测
  (define (settling f)
    (make-keyword-procedure
     (λ (kws vals m . args)
       (define trace (for/first ([k kws] [v vals] #:when (eq? k '#:trace)) v))
       (begin0 (keyword-apply f kws vals m args)
               (settle! m #:trace (or trace void))))))
  (define install! (settling install!/raw))
  (define dispose! (settling dispose!/raw))
  (define restart! (settling restart!/raw))
  (define reset! (settling reset!/raw))
  (define react! (settling react!/raw))
  (define update! (settling update!/raw))
  (define replace! (settling replace!/raw))

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
    (define p (install! m (plugin "bundle" '() '() (λ (ctx) (ctx-plugin ctx core)))))
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
    (define s (install! m (plugin "selfdep" '(tools) '(tools) (λ (ctx) (ctx-provide ctx 'tools (hash))))))
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
    (define sneaky (install! m (plugin "sneaky" '() '() (λ (ctx) (ctx-use ctx 'tools (register "x" 1))))))
    (check-equal? (instance-failure (instance-ref m sneaky)) "实例无法访问服务 tools")
    (define liar (install! m (plugin "liar" '() '() (λ (ctx) (ctx-provide ctx 'db (hash))))))
    (check-equal? (instance-failure (instance-ref m liar)) "db 不在声明的 provides () 中"))

  ;; 提供者加载失败: 它提供的服务随之撤回, 使用者继续等待
  (let ([m (make-manager)])
    (define s (install! m shell))
    (void (install! m (plugin "broken-core" '() '(tools)
                              (λ (ctx) (ctx-provide ctx 'tools (hash)) (error "坏了")))))
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
      (install! m (plugin "peek" '() '() (λ (ctx) (ctx-use ctx 'llm (register "x" 1)))
                          #:optional '(llm))))
    (check-equal? (instance-failure (instance-ref m peek)) "实例无法访问服务 llm")
    (define a (install! m assistant))
    (check-eq? (instance-phase (instance-ref m a)) 'active))

  ;;; 可选依赖的义务 (取舍见第7层的开头): 违反时活锁, 运行时不检查

  ;; 最多走 n 步; 静止了返回 #t
  (define (quiet-within? m n)
    (let loop ([n n])
      (cond [(not (for/or ([id (hash-keys (manager-instances m))]) (step! m id))) #t]
            [(zero? n) #f]
            [else (loop (sub1 n))])))
  ;; install! 只拦下最简单的一种: 直接装上的插件可选依赖自己提供的服务
  (check-exn #rx"可选依赖自己提供的服务"
             (λ () (install! (make-manager)
                             (plugin "self" '() '(llm) (λ (ctx) (void)) #:optional '(llm)))))
  ;; 反例1: 经 ctx-plugin 装上的子插件可选依赖自己提供的服务, install! 管不到; 它一上线就重载自己
  (let ([m (make-manager)])
    (define selfie
      (plugin "selfie" '() '(x) (λ (ctx) (ctx-provide ctx 'x (hash))) #:optional '(x)))
    (void (install!/raw m (plugin "par" '() '() (λ (ctx) (ctx-plugin ctx selfie)))))
    (check-false (quiet-within? m 1000)))
  ;; 反例2: 经可选依赖成环. A 可选依赖 b, B 依赖 a 并提供 b:
  ;; A 一见到 b 就重载, a 随之不可用, B 卸载, b 消失, A 再重载 ...
  (let ([m (make-manager)])
    (void (install!/raw m (plugin "A" '() '(a) (λ (ctx) (ctx-provide ctx 'a (hash))) #:optional '(b))))
    (void (install!/raw m (plugin "B" '(a) '(b) (λ (ctx) (ctx-provide ctx 'b (hash))))))
    (check-false (quiet-within? m 1000)))
  ;; 对照: 必需依赖成环时不活锁, 而是谁也不加载, 静止
  (let ([m (make-manager)])
    (void (install!/raw m (plugin "C" '(d) '(c) (λ (ctx) (ctx-provide ctx 'c (hash))))))
    (void (install!/raw m (plugin "D" '(c) '(d) (λ (ctx) (ctx-provide ctx 'd (hash))))))
    (check-true (quiet-within? m 10))
    (check-true (settled? m)))

  ;;; ctx 与 apply

  ;; apply 是普通代码: 可以用操作的结果做分支
  (define ((lookup name) tok state)
    (op-result state (λ (state) state) (hash-ref state name #f)))
  (define which
    (plugin "which" '(tools) '()
            (λ (ctx)
              (when (ctx-use ctx 'tools (lookup "ls"))
                (ctx-use ctx 'tools (register "which-ls" "ls 在哪"))))))
  (let ([m (make-manager)])
    (void (install! m core))
    (void (install! m which))
    (check-equal? (tools-of m) '())
    (void (install! m shell))
    (void (install! m which))
    (check-equal? (tools-of m) '("cat" "ls" "which-ls")))

  ;; apply 抛出异常: 加载失败, 已做的撤掉
  (let ([m (make-manager)])
    (void (install! m core))
    (define thrower
      (install! m (plugin "thrower" '(tools) '()
                          (λ (ctx)
                            (ctx-use ctx 'tools (register "x" 1))
                            (error 'thrower "出错了")))))
    (check-equal? (instance-failure (instance-ref m thrower)) "apply 抛出异常: thrower: 出错了")
    ;; 抛出的不是异常, 而是任意值: 同样是加载失败, 已做的撤掉, 只做了一次
    (define runs 0)
    (define raiser
      (install! m (plugin "raiser" '(tools) '()
                          (λ (ctx)
                            (set! runs (add1 runs))
                            (ctx-use ctx 'tools (register "y" 1))
                            (raise 'oops)))))
    (check-equal? (instance-failure (instance-ref m raiser)) "apply 抛出异常: oops")
    (check-equal? runs 1)
    (check-eq? (instance-phase (instance-ref m thrower)) 'inactive)
    (check-equal? (tools-of m) '()))

  ;; ctx-provide 和 ctx-plugin 也是 await 点: 它们之后的代码在指令执行之后才运行
  (let ([m (make-manager)] [log '()])
    (define s
      (install!/raw m (plugin "lazy" '() '(files)
                              (λ (ctx)
                                (set! log (cons 'a log))
                                (ctx-provide ctx 'files (hash))
                                (set! log (cons (if (provision-ref m 'files) 'b 'b-too-early) log))
                                (ctx-plugin ctx git)
                                (set! log (cons 'c log))))))
    (check-not-false (step! m s))                    ; 开始加载: 运行到 ctx-provide
    (check-equal? log '(a))
    (check-not-false (step! m s))                    ; 提供 files, 再运行到 ctx-plugin
    (check-equal? log '(b a))
    (check-not-false (step! m s))                    ; 装上 git, apply 返回
    (check-equal? log '(c b a)))

  ;; 每次 ctx 调用是一步: 两次调用之间的代码属于同一步, 别的插件只能插在调用之间
  (let ([m (make-manager)] [log '()])
    (void (install! m core))
    (define s
      (install!/raw m (plugin "steps" '(tools) '()
                              (λ (ctx)
                                (set! log (cons 'a log))
                                (ctx-use ctx 'tools (register "s1" 1))
                                (set! log (cons 'b log))
                                (ctx-use ctx 'tools (register "s2" 2))
                                (set! log (cons 'c log))))))
    (check-not-false (step! m s))                    ; 开始加载: 运行到第一次 ctx 调用
    (check-equal? log '(a))
    (check-not-false (step! m s))                    ; 执行 s1, 运行到第二次 ctx 调用
    (check-equal? log '(b a))
    (check-equal? (tools-of m) '("s1"))
    (check-not-false (step! m s))                    ; 执行 s2, apply 返回
    (check-equal? log '(c b a))
    (check-not-false (step! m s))                    ; 加载完毕
    (check-eq? (instance-phase (instance-ref m s)) 'active))

  ;; ctx 只能在 apply 里同步使用
  (let ([m (make-manager)] [saved #f])
    (void (install! m core))
    (void (install! m (plugin "hoarder" '(tools) '() (λ (ctx) (set! saved ctx)))))
    (check-exn #rx"只能在它所属实例" (λ () (ctx-use saved 'tools (register "late" 1))))
    ;; 在别的插件的 apply 里用也不行
    (define borrower
      (install! m (plugin "borrower" '(tools) '()
                          (λ (ctx) (ctx-use saved 'tools (register "borrowed" 1))))))
    (check-equal? (instance-failure (instance-ref m borrower))
                  "apply 抛出异常: ctx-use: ctx 只能在它所属实例的这次 apply 里同步使用")
    (check-equal? (tools-of m) '()))

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

  ;;; 作用域与事件

  ;; 沿父链查找: editor 不声明依赖也能用父实例提供的 files; 移除时 editor 先退出
  (let ([m (make-manager)] [messages '()])
    (define (record id message) (set! messages (cons message messages)))
    (define w (install! m workspace #:trace record))
    (check-equal? (state-of m 'files) '(("draft.txt" . "草稿")))
    (check-equal? (hash-count (manager-instances m)) 2)
    (dispose! m w #:trace record)
    (check-false (state-of m 'files))
    (check-equal? (hash-count (manager-instances m)) 0)
    (check-false (findf (λ (s) (string-prefix? s "跳过")) messages)))
  ;; 不是祖先提供的服务仍不能用
  (let ([m (make-manager)])
    (void (install! m workspace))
    (define e (install! m editor))
    (check-equal? (instance-failure (instance-ref m e)) "实例无法访问服务 files"))
  ;; 先装子实例再提供: 父实例按 LIFO 先撤回 files, 子实例的撤销被跳过
  (let ([m (make-manager)] [messages '()])
    (define w (install! m workspace/bad))
    (check-equal? (state-of m 'files) '(("draft.txt" . "草稿")))
    (dispose! m w #:trace (λ (id message) (set! messages (cons message messages))))
    (check-not-false (findf (λ (s) (string-prefix? s "跳过撤销")) messages))
    (check-equal? (hash-count (manager-instances m)) 0))

  ;; 隔离: 改名后的服务是另一个服务; 子插件和处理器也在同一个作用域里
  (let ([m (make-manager)])
    (void (install! m core))
    (void (install! m shell))
    (void (install! m (isolate core 'tools "sandbox")))
    (define t (install! m (isolate toolkit 'tools "sandbox")))
    (check-equal? (tools-of m) '("cat" "ls"))
    (check-equal? (map car (state-of m '(tools . "sandbox"))) '("grep" "help" "sed"))
    ;; 隔离过的插件不与外面的冲突, 但同一作用域里仍冲突
    (check-exn #rx"相同的服务" (λ () (install! m (isolate core 'tools "sandbox"))))
    (dispose! m t)
    (check-equal? (state-of m '(tools . "sandbox")) '())
    ;; 处理器族也在作用域里: guard 的 restrict 挂在隔离过的 agent 上下文里
    (define a (install! m (isolate (agent 5) (agent-key 5) "sandbox")))
    (define g (install! m (isolate guard (agent-key 5) "sandbox")))
    (void (react! m g 0 5))
    (check-equal? (state-of m (cons (agent-key 5) "sandbox")) '(("restricted" . #t))))

  ;; 事件: prepend 的处理器在前; emit 返回所有结果, bail 返回第一个
  (let ([m (make-manager)])
    (void (install! m bus))
    (void (install! m auto-approve))
    (void (install! m ask-user))
    (check-equal? (emit m "approval" 'req) '(ask approve))
    (check-equal? (bail m "approval" 'req) 'ask)
    (check-equal? (emit m "tick") '())
    ;; 隔离过的事件总线: 分发时指明是哪一个
    (void (install! m (isolate bus 'events "sandbox")))
    (void (install! m (isolate ping 'events "sandbox")))
    (check-equal? (emit m "tick" #:service '(events . "sandbox")) '("ping"))
    (check-equal? (emit m "tick") '()))
  ;; 只有一方 prepend 时, 谁先处理与调度无关; 都不 prepend 时与调度有关
  (define (approval-run plugins seed)
    (define m (make-manager))
    (for ([p (shuffle-with seed plugins)]) (void (install!/raw m p)))
    (void (settle! m #:order (random-order seed)))
    (bail m "approval" 'req))
  (define (shuffle-with seed xs)
    (define rng (make-pseudo-random-generator))
    (parameterize ([current-pseudo-random-generator rng])
      (random-seed seed)
      (shuffle xs)))
  (check-equal? (for/set ([seed (in-range 30)]) (approval-run (list bus auto-approve ask-user) seed))
                (set 'ask))
  (define auto-deny
    (plugin "auto-deny" '(events) '()
            (λ (ctx) (ctx-on ctx "approval" (λ (request) 'deny)))))
  (check-equal? (for/set ([seed (in-range 30)]) (approval-run (list bus auto-approve auto-deny) seed))
                (set 'approve 'deny))

  ;;; 配置

  ;; apply 拿到配置; update! 换配置后按新配置重新加载, 实例编号不变
  (let ([m (make-manager)])
    (void (install! m core))
    (define a (install! m alias #:config '("ll" . "ls -l")))
    (check-equal? (state-of m 'tools) '(("ll" . "ls -l")))
    (update! m a '("la" . "ls -a"))
    (check-equal? (state-of m 'tools) '(("la" . "ls -a")))
    (check-eq? (instance-phase (instance-ref m a)) 'active)
    (check-equal? (instance-config (instance-ref m a)) '("la" . "ls -a"))
    ;; 不合法的配置当场被拒绝, 实例不受影响
    (check-exn #rx"配置不合法" (λ () (update! m a 'oops)))
    (check-exn #rx"配置不合法" (λ () (install! m alias #:config #f)))
    (check-equal? (state-of m 'tools) '(("la" . "ls -a")))
    ;; 坏配置导致加载失败; 再 update! 一个好配置就修好了
    (void (install! m shell))
    (update! m a '("ls" . "ls --color"))
    (check-true (string? (instance-failure (instance-ref m a))))
    (check-equal? (tools-of m) '("cat" "ls"))
    (update! m a '("ll" . "ls -l"))
    (check-false (instance-failure (instance-ref m a)))
    (check-equal? (tools-of m) '("cat" "ll" "ls"))
    (check-true (settled? m)))

  ;; 等待中的实例换配置: 依赖来了按新配置加载
  (let ([m (make-manager)])
    (define a (install! m alias #:config '("ll" . "ls -l")))
    (update! m a '("la" . "ls -a"))
    (void (install! m core))
    (check-equal? (state-of m 'tools) '(("la" . "ls -a"))))

  ;; apply 也可以只拿 ctx, 用 ctx-config 读; 子插件的配置由 ctx-plugin 给
  (let ([m (make-manager)])
    (void (install! m core))
    (void (install! m (plugin "aliases" '(tools) '()
                              (λ (ctx)
                                (for ([c (ctx-config ctx)])
                                  (ctx-plugin ctx alias c))))
                    #:config '(("ll" . "ls -l") ("la" . "ls -a"))))
    (check-equal? (tools-of m) '("la" "ll")))

  ;; replace!: 编号不变, 换成新插件; 依赖它的实例跟着重载
  (let ([m (make-manager)])
    (define c (install! m core))
    (define s (install! m shell))
    (define old-pid (provision-id (provision-ref m 'tools)))
    (replace! m c core+)
    (check-equal? (instance-name (instance-ref m c)) "core+")
    (check-equal? (tools-of m) '("builtin" "cat" "ls"))
    (check-not-equal? (provision-id (provision-ref m 'tools)) old-pid)
    (check-eq? (instance-phase (instance-ref m s)) 'active)
    ;; 换成与别的实例冲突的插件: 被拒绝
    (define b (install! m bus))
    (check-exn #rx"相同的服务" (λ () (replace! m b core)))
    ;; 失败的实例 replace! 之后清除失败
    (define bad-id (install! m bad))
    (check-true (string? (instance-failure (instance-ref m bad-id))))
    (replace! m bad-id git)
    (check-false (instance-failure (instance-ref m bad-id)))
    (check-equal? (tools-of m) '("builtin" "cat" "git" "ls"))
    (check-true (settled? m)))
  ;; replace! 之后, 换下来的插件提供的服务还没撤回时, 别的插件不能来提供它
  (for ([seed (in-range 20)])
    (define m (make-manager))
    (define c (install!/raw m core))
    (void (settle! m))
    (replace!/raw m c bus)
    (check-exn #rx"相同的服务" (λ () (install!/raw m core)) (format "种子 ~a" seed))
    (void (settle! m #:order (random-order seed)))
    (define c2 (install!/raw m core))                ; 撤回之后就可以了
    (void (settle! m #:order (random-order seed)))
    (check-false (instance-failure (instance-ref m c2)) (format "种子 ~a" seed)))
  ;; replace! 同样不接受可选依赖自己提供的服务的插件
  (let ([m (make-manager)])
    (define c (install! m core))
    (check-exn #rx"可选依赖自己提供的服务"
               (λ () (replace! m c (plugin "self" '() '(llm) (λ (ctx) (void)) #:optional '(llm))))))
  ;; react! 也检查处理器的配置 (反应的配置是 #f)
  (let ([m (make-manager)])
    (void (install! m bus))
    (define strict-ping (plugin "strict-ping" '(events) '() (λ (ctx) (void)) #:schema string?))
    (define w (install! m (plugin "w" '(events) '() (λ (ctx) (void)) (list strict-ping))))
    (check-exn #rx"配置不合法" (λ () (react! m w 0))))

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
