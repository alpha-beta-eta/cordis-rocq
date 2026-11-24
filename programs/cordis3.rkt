#lang racket
;cordis.rkt 加上三项扩展, 对应 cordis-rocq 的 theories/Ext/ (设计见 docs/EXTENSIONS.md).
;核心部分从 cordis.rkt 复制而来, 两个文件互不依赖; 核心改动时两边都要改.
;扩展:
;  1. 可选依赖: 插件声明 optional, 有就用, 没有不等. 开始加载时在场的可选依赖进入视图,
;     程序可以按在场集选变体; 在场集变化 (出现或消失) 时重载. 对应 Ext/Optional.v.
;  2. 编排者: 不加规则. 插件市场, 自更新, bundle 都是 install!/dispose!/restart! 的输入源,
;     见 test 中"编排者"一节. 对应 Ext/Orchestrator.v.
;  3. 交集生命期: 事件处理器可以是一族 (载荷 -> 插件), react! 带上载荷 (如 agent id),
;     运行该载荷的实例. 效应依赖 agent 的条目键, 插件或 agent 任一方结束即撤销.
;     对应 Ext/Intersect.v.
(struct op-result (state undo value))

;program ir
(struct Provide (key init next))
;operation : 令牌 状态 -> op-result 或 #f
;令牌是运行时交给这次操作的新鲜编号, 用作操作生成出来的身份 (如事件处理器)
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

;optional是可选依赖: 有就用, 没有不等 (扩展1)
;body是程序, 或者 (在场的可选依赖列表 -> 程序): 开始加载时按在场集选变体
;reacts是事件处理器: 实例active时, 每次反应是一个子实例 (见react!).
;一个处理器是插件, 或者 (载荷 -> 插件) 的一族 (扩展3)
(struct plugin (name deps optional provides body reacts))
;remaining是剩余需要执行的程序
;parent是父实例的id, 直接install!的实例为#f
(struct instance
  (plugin phase remaining undo-stack view failure disposed? parent)
  #:mutable)
(define (fail! why i)
  (set-instance-phase! i 'unloading)
  (set-instance-failure! i why)
  (format "失败 (~a), 开始卸载" why))
(define (push-undo! entry i)
  (set-instance-undo-stack!
   i (cons entry (instance-undo-stack i))))
(define instance-deps
  (compose plugin-deps instance-plugin))
(define instance-optional
  (compose plugin-optional instance-plugin))
(define instance-provides
  (compose plugin-provides instance-plugin))
(define instance-name
  (compose plugin-name instance-plugin))
;tok是执行这次操作时用的令牌
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
;扩展1: 再加上此刻可用的可选依赖. 视图因此记下在场集;
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
    [(and (instance-view i) (hash-has-key? (instance-view i) key))
     (define expected-id
       (hash-ref (instance-view i) key #f))
     (and (number? expected-id)
          (= expected-id (provision-id p))
          p)]
    ;情况2: 检查是否为自己提供
    [else (and (= (provision-owner p) id) p)]))
;运行实例的剩余程序一步 (L-Step)
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
       [(not p) (fail! "实例无法访问相应服务" i)]
       [else
        (define pid (provision-id p))
        ;操作失败时令牌也已用掉, 与Rocq一致
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
                            (format "~a 已由自身提供过 (编号 ~a)"
                                    key (provision-id existing))
                            (format "~a 已由实例 ~a 提供 (编号 ~a)"
                                    key (provision-owner existing)
                                    (provision-id existing)))
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

;检查编号为used-id的provision是否仍被其他实例使用 (Rocq中的relied)
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
;卸载的守卫 (Rocq中的held): 实例尚未撤回的某个provision仍被别的实例使用.
;成立时它什么都不撤, 也不请子实例退出, 依赖者因此在它的全部效应都还在时卸载
;(同Cordis: 先等全部provision的依赖者退出, 再启动任何disposer)
(define (held? m id i)
  (for/or ([entry (instance-undo-stack i)])
    (match entry
      [(undo-provide _ used-id) (in-use? m id used-id)]
      [_ #f])))
;弹出一项撤销 (L-Undo, 以及USpawn处的L-RetireChild); 只在held?不成立时调用
(define (undo-one! m id i)
  (define provisions
    (manager-provisions m))
  (match (instance-undo-stack i)
    ['()
     (set-instance-phase! i 'inactive)
     (if (instance-failure i)
         (format "卸载完毕 -> inactive (此次卸载由加载失败引起: ~a)"
                 (instance-failure i))
         "卸载完毕 -> inactive (正常卸载)")]
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
            ;L-Remove要求没有子实例
            #f]
           [(instance-disposed? i)
            (hash-remove! (manager-instances m) id)
            (format "实例 ~a (插件 ~a) 已弃置且卸载完毕, 从管理器中移除"
                    id name)]
           [(and (not (instance-failure i)) wanted)
            (define body (plugin-body (instance-plugin i)))
            (define present (present-optional i wanted))
            (set-instance-phase! i 'loading)
            ;扩展1: 按在场集选变体
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
    ;视图变化时总是立即放弃 (L-Divert/L-Leave). 演算也允许先让剩余的迭代落地 (差异 h),
    ;这里取的是其中一种调度
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
                         ;扩展1: 在场集变化引起的重载
                         (let ([before (present-optional i (instance-view i))]
                               [after (and wanted (present-optional i wanted))])
                           (if (and after (not (equal? before after)))
                               (format "; 在场的可选依赖从 ~a 变为 ~a" before after)
                               "")))))]
    ['loading (run-instruction! m id i)]
    ['active #f]
    ['unloading (and (not (held? m id i)) (undo-one! m id i))]))

;;; 服务操作的例子

;注册表: 状态是 名字 -> 值 的hash
(define ((register name value) tok state)
  (and (not (hash-has-key? state name))
       (op-result
        (hash-set state name value)
        (λ (state) (hash-remove state name))
        'ok)))
;事件总线: 状态是 令牌 -> (事件名 . 处理器) 的hash
;同一个处理器可以登记多次, 令牌区分各次登记, 逆只删掉自己这一次
(define ((on event handler) tok state)
  (op-result
   (hash-set state tok (cons event handler))
   (λ (state) (hash-remove state tok))
   tok))

;;; 编排操作 (外部输入); 前提不满足时报错, 对应Rocq中step返回None

(define (existing-instance who m id)
  (or (instance-ref m id)
      (error who "没有编号为 ~a 的实例" id)))
;O-Insert
(define (install! m plug)
  (cond [(provider-conflict m plug)
         => (λ (existing)
              (error 'install! "~a 与 ~a 提供了相同的服务"
                     (plugin-name plug) (instance-name existing)))])
  (add-instance! m plug #f))
;O-Dispose
(define (dispose! m id)
  (set-instance-disposed?!
   (existing-instance 'dispose! m id) #t))
;O-Reset: 只对加载失败后停在inactive的实例有效
(define (reset! m id)
  (define i (existing-instance 'reset! m id))
  (unless (and (eq? (instance-phase i) 'inactive) (instance-failure i))
    (error 'reset! "实例 ~a 不是加载失败后的inactive实例" id))
  (set-instance-failure! i #f))
;O-Restart: 强制卸载, 卸载完后由L-Begin重新加载; 返回一行描述
(define (restart! m id)
  (define i (existing-instance 'restart! m id))
  (unless (and (not (instance-disposed? i))
               (memq (instance-phase i) '(loading active)))
    (error 'restart! "实例 ~a 不在loading或active, 或已弃置" id))
  (set-instance-phase! i 'unloading)
  (format "实例 ~a (插件 ~a) 开始卸载, 原因: 被要求重启" id (instance-name i)))
;O-React: 实例对一个事件作出反应, 反应是reacts中第index个插件的子实例
;返回子实例的id; 提前撤销这次反应就是dispose!这个子实例
;扩展3 (I-React): 第index个处理器是一族时, 运行它在载荷payload处的实例
(define (react! m id index [payload (void)])
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
    (cond [(plugin? handler) handler]
          [(void? payload)
           (error 'react! "实例 ~a 的第 ~a 个事件处理器是一族, 需要载荷" id index)]
          [else (handler payload)]))
  (cond [(provider-conflict m child)
         => (λ (existing)
              (error 'react! "~a 与 ~a 提供了相同的服务"
                     (plugin-name child) (instance-name existing)))])
  (define child-id (add-instance! m child id))
  (push-undo! (undo-spawn child-id) i)
  child-id)

;;; 调度

;反复挑一个能走的实例走一步, 直到没有实例能走 (静止, 即Rocq中的quiet)
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
(define (print-step id message)
  (printf "  [~a] ~a\n" id message))

;静止时每个实例都安定: 加载失败, 或应当不运行且未运行, 或以正确视图active;
;并且没有可以执行的L-Remove (已弃置, inactive, 没有子实例的实例应当已被移除)
(define (settled? m)
  (for/and ([(id i) (manager-instances m)])
    (define wanted (wanted-view m i))
    (match (instance-phase i)
      ['inactive (and (or (instance-failure i) (not wanted))
                      (not (and (instance-disposed? i)
                                (not (has-children? m id)))))]
      ['active (equal? wanted (instance-view i))]
      [_ #f])))

(define (show m)
  (printf "  -- 实例:")
  (for ([id (sort (hash-keys (manager-instances m)) <)])
    (define i (instance-ref m id))
    (printf " ~a#~a~a=~a~a" (instance-name i) id
            (if (instance-parent i) (format "(父#~a)" (instance-parent i)) "")
            (instance-phase i)
            (if (instance-failure i) "(失败)" "")))
  (newline)
  (printf "  -- 服务:")
  (when (zero? (hash-count (manager-provisions m))) (printf " (无)"))
  (for ([(key p) (manager-provisions m)])
    (printf " ~a[编号~a]=~a" key (provision-id p)
            (hash->list (provision-state p))))
  (newline))

;;; 示例插件

(define core
  (plugin "core" '() '() '(tools)
          (prog (serve 'tools (hash))
                (Done))
          '()))
(define shell
  (plugin "shell" '(tools) '() '()
          (prog ('tools (register "ls" "列出文件"))
                ('tools (register "cat" "打印文件"))
                (Done))
          '()))
(define git
  (plugin "git" '(tools) '() '()
          (prog ('tools (register "git" "版本控制"))
                (Done))
          '()))
;提供 tools 之后自己再登记一个条目
(define core+
  (plugin "core+" '() '() '(tools)
          (prog (serve 'tools (hash))
                ('tools (register "builtin" "内建"))
                (Done))
          '()))
;先登记 grep, 再登记已被占用的 ls -> 失败; grep 会被自动撤掉
(define bad
  (plugin "bad" '(tools) '() '()
          (prog ('tools (register "grep" "搜索"))
                ('tools (register "ls" "冒牌 ls"))
                (Done))
          '()))
;spawn: 父插件在加载中安装两个子插件, 中间自己再登记一个条目
(define grep-tool
  (plugin "grep-tool" '(tools) '() '()
          (prog ('tools (register "grep" "搜索")) (Done))
          '()))
(define sed-tool
  (plugin "sed-tool" '(tools) '() '()
          (prog ('tools (register "sed" "流编辑")) (Done))
          '()))
(define toolkit
  (plugin "toolkit" '(tools) '() '()
          (prog (spawn grep-tool)
                ('tools (register "help" "工具箱帮助"))
                (spawn sed-tool)
                (Done))
          '()))
;事件: bus提供事件总线; watcher每次反应都登记一个相同的处理器
(define bus
  (plugin "bus" '() '() '(events)
          (prog (serve 'events (hash))
                (Done))
          '()))
(define ping
  (plugin "ping" '(events) '() '()
          (prog ('events (on "tick" "ping"))
                (Done))
          '()))
(define watcher
  (plugin "watcher" '(events) '() '()
          (prog ('events (on "start" "watcher"))
                (Done))
          (list ping)))

(define (tools-of m)
  (define p (provision-ref m 'tools))
  (and p (sort (hash-keys (provision-state p)) string<?)))
(define (handlers-of m)
  (define p (provision-ref m 'events))
  (and p (hash-count (provision-state p))))

;;; 扩展的示例插件

;扩展1: assistant 可选依赖 llm. 有 llm 时往 llm 登记自己, 并提供用 llm 的 summarize;
;没有时提供退化的 summarize. 两个变体都提供 skills (每个变体完整提供)
(define llm-provider
  (plugin "llm" '() '() '(llm)
          (prog (serve 'llm (hash))
                (Done))
          '()))
(define assistant
  (plugin "assistant" '() '(llm) '(skills)
          (λ (present)
            (if (member 'llm present)
                (prog (serve 'skills (hash))
                      ('llm (register "assistant" "使用中"))
                      ('skills (register "summarize" "用 llm 总结"))
                      (Done))
                (prog (serve 'skills (hash))
                      ('skills (register "summarize" "截取前几行"))
                      (Done))))
          '()))

;扩展3: agent n 的上下文是键 (agent n); restrict n 是挂在它上面的效应,
;依赖 (agent n) 并在其中登记一项; guard 的事件处理器是 restrict 这一族
(define (agent-key n) (list 'agent n))
(define (agent n)
  (plugin (format "agent~a" n) '() '() (list (agent-key n))
          (prog (serve (agent-key n) (hash))
                (Done))
          '()))
(define (restrict n)
  (plugin (format "restrict~a" n) (list (agent-key n)) '() '()
          (prog ((agent-key n) (register "restricted" #t))
                (Done))
          '()))
(define guard
  (plugin "guard" '() '() '()
          (prog (Done))
          (list restrict)))

;服务 key 的内容, 排好序; 服务不存在时为#f
(define (state-of m key)
  (define p (provision-ref m key))
  (and p (sort (hash->list (provision-state p))
               (λ (a b) (string<? (~a (car a)) (~a (car b)))))))

(module+ main
  (define m (make-manager))
  (define (scene title thunk)
    (printf "\n== ~a\n" title)
    (thunk)
    (settle! m #:trace print-step)
    (show m))
  (define core-id #f)
  (define toolkit-id #f)
  (define watcher-id #f)
  (define ping-id #f)
  (scene "先装依赖者 shell, git, 再装提供者 core"
         (λ () (install! m shell)
               (install! m git)
               (set! core-id (install! m core))))
  (scene "装 toolkit: 它在加载中 spawn 两个子插件"
         (λ () (set! toolkit-id (install! m toolkit))))
  (scene "移除 toolkit: 按 LIFO 拆除, 先 sed-tool, 再撤 help, 再 grep-tool"
         (λ () (dispose! m toolkit-id)))
  (scene "restart core: 依赖者先卸载, core 重新提供 tools (换了编号), 依赖者再加载"
         (λ () (print-step core-id (restart! m core-id))))
  (scene "装 bus 和 watcher"
         (λ () (install! m bus)
               (set! watcher-id (install! m watcher))))
  (scene "watcher 反应两次: 两个 ping 子实例各登记一个相同的处理器"
         (λ () (set! ping-id (react! m watcher-id 0))
               (react! m watcher-id 0)))
  (scene "单独撤销第一次反应: 只删掉它用自己令牌登记的那一项"
         (λ () (dispose! m ping-id)))
  (scene "移除 watcher: 剩下的反应先退出"
         (λ () (dispose! m watcher-id)))
  ;; 扩展
  (define llm-id #f)
  (scene "扩展1: 先装 assistant, 它可选依赖的 llm 还没有, 用退化的变体"
         (λ () (install! m assistant)))
  (scene "装 llm: assistant 的在场集变了, 重载, 换成用 llm 的变体"
         (λ () (set! llm-id (install! m llm-provider))))
  (scene "移除 llm: assistant 先卸载 (llm 的卸载被守卫挡住), 再按退化的变体加载"
         (λ () (dispose! m llm-id)))
  (define agent-id #f)
  (define guard-id #f)
  (scene "扩展3: 装 agent3 与 guard"
         (λ () (set! agent-id (install! m (agent 3)))
               (set! guard-id (install! m guard))))
  (scene "guard 对 agent3 的事件反应, 以载荷 3 运行 restrict 一族, 在 agent3 上挂一项限制"
         (λ () (react! m guard-id 0 3)))
  (scene "agent3 结束: 它的卸载被守卫挡住, 限制先撤销, agent3 才拆除"
         (λ () (dispose! m agent-id))))

(module+ test
  (require rackunit)

  ;; 注册表, spawn
  (define m (make-manager))
  (define shell-id (install! m shell))
  (void (install! m git))
  (define core-id (install! m core))
  (void (settle! m))
  (check-equal? (tools-of m) '("cat" "git" "ls"))
  (define toolkit-id (install! m toolkit))
  (void (settle! m))
  (check-equal? (tools-of m) '("cat" "git" "grep" "help" "ls" "sed"))
  (check-equal? (hash-count (manager-instances m)) 6)
  (dispose! m toolkit-id)
  (void (settle! m))
  (check-equal? (tools-of m) '("cat" "git" "ls"))
  (check-equal? (hash-count (manager-instances m)) 3)

  ;; restart: 结果不变, 但 tools 换了编号
  (define old-pid (provision-id (provision-ref m 'tools)))
  (void (restart! m core-id))
  (void (settle! m))
  (check-equal? (tools-of m) '("cat" "git" "ls"))
  (check-not-equal? (provision-id (provision-ref m 'tools)) old-pid)
  (check-exn exn:fail? (λ () (restart! m 999)))

  ;; reset: 只对失败的实例有效; 重置后重新加载, 再次失败
  (define bad-id (install! m bad))
  (void (settle! m))
  (check-equal? (tools-of m) '("cat" "git" "ls"))
  (check-exn exn:fail? (λ () (reset! m shell-id)))
  (reset! m bad-id)
  (void (settle! m))
  (check-true (string? (instance-failure (instance-ref m bad-id))))
  (check-equal? (tools-of m) '("cat" "git" "ls"))

  ;; react: 相同的处理器登记两次, 令牌让撤销只删自己那一项
  (void (install! m bus))
  (define watcher-id (install! m watcher))
  (void (settle! m))
  (check-exn exn:fail? (λ () (react! m watcher-id 1)))
  (define ping1 (react! m watcher-id 0))
  (define ping2 (react! m watcher-id 0))
  (void (settle! m))
  (check-equal? (handlers-of m) 3)
  (dispose! m ping1)
  (void (settle! m))
  (check-equal? (handlers-of m) 2)
  (check-false (instance-ref m ping1))
  (check-true (and (instance-ref m ping2) #t))
  (dispose! m watcher-id)
  (void (settle! m))
  (check-equal? (handlers-of m) 0)
  (check-false (instance-ref m ping2))

  ;; divert: shell 加载到一半时 core 重启, tools 不再可见, shell 中途放弃加载,
  ;; 撤掉已经登记的 ls, 等 core 重新提供后再从头加载
  (let ()
    (define m (make-manager))
    (define c (install! m core))
    (define s (install! m shell))
    (define (step-until! id phase)
      (let loop ()
        (unless (eq? (instance-phase (instance-ref m id)) phase)
          (step! m id)
          (loop))))
    (step-until! c 'active)
    (check-not-false (step! m s))                    ; L-Begin
    (check-eq? (instance-phase (instance-ref m s)) 'loading)
    (check-not-false (step! m s))                    ; 登记 ls
    (check-equal? (tools-of m) '("ls"))
    (restart! m c)
    (check-not-false (step! m s))                    ; L-Divert
    (check-eq? (instance-phase (instance-ref m s)) 'unloading)
    (check-false (instance-failure (instance-ref m s)))
    (check-not-false (step! m s))                    ; 撤销 ls
    (check-equal? (tools-of m) '())
    (void (settle! m))
    (check-true (settled? m))
    (check-equal? (tools-of m) '("cat" "ls")))

  ;; 守卫作用于整个卸载: core+ 在提供之后登记了 builtin; 重启时只要 shell 还在使用 tools,
  ;; core+ 连 builtin 也不撤, shell 卸载时看到的是 core+ 的全部效应 (同 Cordis)
  (let ()
    (define m (make-manager))
    (define c (install! m core+))
    (define s (install! m shell))
    (void (settle! m))
    (restart! m c)
    (check-false (step! m c))                        ; 被守卫挡住
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

  ;; settled?: 已弃置且卸载完毕, 但还没被移除的实例不算安定 (L-Remove 仍可执行)
  (let ()
    (define m (make-manager))
    (void (install! m core))
    (define g (install! m git))
    (void (settle! m))
    (check-true (settled? m))
    (dispose! m g)
    (let loop ()
      (unless (eq? (instance-phase (instance-ref m g)) 'inactive)
        (step! m g)
        (loop)))
    (check-false (settled? m))
    (check-not-false (step! m g))                    ; L-Remove
    (check-false (instance-ref m g))
    (check-true (settled? m)))

  ;; 合流: 不同调度顺序得到相同的结果 (实例名和编号可以不同, 比较名字和服务内容)
  ;; 注意例子里没有同名登记, 也没有查询别人登记的名字, 这是注册表满足合流假设的条件
  ;; 场景含 O-React; 已证的合流定理不覆盖 O-React (RULES 第 5 节第 4 条), 这里只是经验检查
  (define (run-scenario order)
    (define m (make-manager))
    (define messages '())
    (define (go!)
      (set! messages (append messages (map cdr (settle! m #:order order))))
      (check-true (settled? m)))
    (install! m shell)
    (define t (install! m toolkit))
    (define c (install! m core))
    (install! m git)
    (install! m bus)
    (define w (install! m watcher))
    (go!)
    (react! m w 0)
    (react! m w 0)
    (restart! m c)
    (go!)
    (dispose! m t)
    (restart! m w)
    (go!)
    (values
     (list (sort (for/list ([i (in-hash-values (manager-instances m))])
                   (format "~a:~a:~a" (instance-name i) (instance-phase i)
                           (and (instance-failure i) #t)))
                 string<?)
           (tools-of m)
           (sort (map ~a (hash-values (provision-state (provision-ref m 'events))))
                 string<?))
     messages))
  (define-values (expected expected-messages)(run-scenario (λ (ids) (sort ids <))))
  (for ([seed (in-range 200)])
    (define-values (result messages) (run-scenario (random-order seed)))
    (check-equal? result expected (format "种子 ~a" seed))
    ;; 按不变量, 跳过撤销的分支不会被走到
    (check-false (findf (λ (s) (string-prefix? s "跳过")) messages)
                 (format "种子 ~a" seed)))

  ;;; 扩展1: 可选依赖

  ;; 两种调度 (先 llm 或先 assistant) 终于同一状态; assistant 后见到 llm 时重载
  (define (optional-run first second order)
    (define m (make-manager))
    (define ids (make-hash))
    (hash-set! ids first (install! m (if (eq? first 'llm) llm-provider assistant)))
    (define log1 (settle! m #:order order))
    (hash-set! ids second (install! m (if (eq? second 'llm) llm-provider assistant)))
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
  ;; 各种调度顺序下结果相同
  (for* ([firsts (list '(llm assistant) '(assistant llm))]
         [seed (in-range 50)])
    (define-values (m ids _) (optional-run (car firsts) (cadr firsts) (random-order seed)))
    (check-equal? (list (state-of m 'skills) (state-of m 'llm))
                  (list (state-of m-a 'skills) (state-of m-a 'llm))
                  (format "~a 种子 ~a" firsts seed)))
  ;; llm 消失: llm 的卸载被守卫挡住; assistant 先卸载, 自己撤掉它在 llm 上登记的一项, 再按退化的变体加载
  (dispose! m-a (hash-ref ids-a 'llm))
  (void (settle! m-a))
  (check-true (settled? m-a))
  (check-equal? (state-of m-a 'skills) '(("summarize" . "截取前几行")))
  (check-false (state-of m-a 'llm))

  ;;; 扩展2: 编排者 (不加规则, 只看输入)

  ;; 插件市场按任意顺序装同一组插件, 中间随意穿插生命期步, 终态相同
  (define (install-all plugs order)
    (define m (make-manager))
    (for ([p plugs])
      (install! m p)
      (void (settle! m #:order order)))
    (check-true (settled? m))
    (list (sort (for/list ([i (in-hash-values (manager-instances m))])
                  (format "~a:~a" (instance-name i) (instance-phase i)))
                string<?)
          (tools-of m)))
  (define base-plugs (list core shell git toolkit))
  (define expected-install (install-all base-plugs (λ (ids) (sort ids <))))
  (for* ([perm (in-permutations base-plugs)]
         [seed (in-range 3)])
    (check-equal? (install-all perm (random-order seed)) expected-install))
  ;; 自更新: 旧版 core 换成新版 core+. 次序同论文 4.4 节的修订:
  ;; 先弃置旧版, 等它卸载并移除 (依赖者随之卸载), 再插入新版; 两者不能同时提供 tools
  ;; 终态与直接装新版相同
  (let ()
    (define m (make-manager))
    (define old (install! m core))
    (void (install! m shell))
    (void (settle! m))
    (dispose! m old)
    (check-exn exn:fail? (λ () (install! m core+)))  ; 旧版还在, 插入被拒绝
    (void (settle! m))
    (check-false (instance-ref m old))
    (void (install! m core+))
    (void (settle! m))
    (check-true (settled? m))
    (check-equal? (tools-of m) '("builtin" "cat" "ls"))
    (define fresh (make-manager))
    (void (install! fresh core+))
    (void (install! fresh shell))
    (void (settle! fresh))
    (check-equal? (tools-of fresh) (tools-of m))
    (define (phases m)
      (sort (for/list ([i (in-hash-values (manager-instances m))])
              (format "~a:~a" (instance-name i) (instance-phase i)))
            string<?))
    (check-equal? (phases fresh) (phases m)))

  ;;; 扩展3: 交集生命期

  (define (agent-setup)
    (define m (make-manager))
    (define a (install! m (agent 3)))
    (define g (install! m guard))
    (void (settle! m))
    (define r (react! m g 0 3))
    (void (settle! m))
    (values m a g r))
  ;; 一族处理器要载荷
  (let-values ([(m a g r) (agent-setup)])
    (check-exn exn:fail? (λ () (react! m g 0)))
    (check-equal? (state-of m (agent-key 3)) '(("restricted" . #t)))
    (check-eq? (instance-phase (instance-ref m r)) 'active))
  ;; agent 结束: 限制先撤销, agent 才撤回自己的上下文
  (let-values ([(m a g r) (agent-setup)])
    (dispose! m a)
    (check-not-false (step! m a))                    ; agent 开始卸载
    (check-false (step! m a))                        ; 被守卫挡住: 限制还解析着它
    (check-equal? (state-of m (agent-key 3)) '(("restricted" . #t)))
    (check-not-false (step! m r))                    ; 限制的目标没了, 开始卸载
    (check-not-false (step! m r))                    ; 撤销登记
    (check-equal? (state-of m (agent-key 3)) '())
    (check-not-false (step! m r))                    ; 限制 -> inactive
    (void (settle! m))
    (check-true (settled? m))
    (check-false (instance-ref m a))
    (check-false (state-of m (agent-key 3)))
    (check-eq? (instance-phase (instance-ref m r)) 'inactive)
    (check-eq? (instance-phase (instance-ref m g)) 'active))
  ;; 插件结束: 限制随插件撤销, agent 照常运行, 上下文完整
  (let-values ([(m a g r) (agent-setup)])
    (dispose! m g)
    (void (settle! m))
    (check-true (settled? m))
    (check-false (instance-ref m g))
    (check-false (instance-ref m r))
    (check-eq? (instance-phase (instance-ref m a)) 'active)
    (check-equal? (state-of m (agent-key 3)) '())))
