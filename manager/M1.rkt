#lang racket
;渐进的插件管理器, 第1层: 卸载.
;计划与各层的说明见 README.md. 每层是一个完整的文件, 不依赖前面的层; 相邻两层的差别见 diffs/.
;本层新增: 每个操作除了新状态, 还交出一个逆 (undo); 实例把逆压进自己的撤销栈.
;  dispose! 按 LIFO 弹出撤销栈, 逐项施加逆, 然后移除实例. 加载失败时同样撤掉已做的, 停在 inactive.
;  逆作用在撤销时的状态上, 所以别的插件在中间做的事可以保留下来. 但这要两条前提:
;  实例内部靠 LIFO (后做的先撤, 每个逆面对的正是它的操作留下的状态);
;  实例之间靠服务自己的规格, 即撤销独立性: 一个实例的逆不碰别的实例的操作留下的东西.
;  只有每个操作都带逆还不够. 反例见测试中的 set-slot: A、B 先后写同一个槽, 卸 A 删掉的是 B 写的值,
;  再卸 B 又把 A 的值写了回来. 演算中这条前提是 revert-independence (theories/Bridge.v 的 paper_revert_indep).
;  每次操作还拿到一个新鲜的令牌, 用来标记它产生的东西: 同一个处理器登记两次, 各自的逆只删自己那一项.
;留给下一层的问题: 共享状态是创建管理器时给定的, 插件之间只能通过它合作;
;  插件不能把服务提供给别的插件, 也不能声明自己要用什么.
(provide (all-defined-out))

;operation : 令牌 状态 -> op-result 或 #f (#f 表示操作被拒绝)
;令牌是运行时交给这次操作的新鲜编号, 用作操作生成出来的东西的身份 (如事件处理器)
;undo : 状态 -> 状态, 撤销这次操作; 它作用在撤销时的状态上
(struct op-result (state undo value))

;program ir
;cont : value -> ir
(struct Op (key operation cont))
(struct Done ())
(struct Fail (why))
(define-syntax prog
  (syntax-rules (<-)
    [(_ last) last]
    [(_ (var <- key operation) rest ...)
     (Op key operation (λ (var) (prog rest ...)))]
    [(_ (key operation) rest ...)
     (Op key operation (λ (ignored) (prog rest ...)))]))

(struct plugin (name body))
;phase 是 'loading, 'active, 'unloading 或 'inactive (加载失败, 已撤掉做过的操作);
;failure 是失败的原因
(struct instance
  (plugin phase undo-stack failure)
  #:mutable)
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
;instances是实例id和实例的字典
;states是键和共享状态的字典; 本层的键在创建管理器时给定, 插件不能增加
;next-id由实例id和操作令牌共用
(struct manager
  ([next-id #:mutable] instances states))
(define (make-manager)
  (manager 0 (make-hash) (make-hash (list (cons 'tools (hash)) (cons 'events (hash))))))
(define (fresh-id! m)
  (define id (manager-next-id m))
  (set-manager-next-id! m (add1 id))
  id)
(define (state-ref m key)
  (hash-ref (manager-states m) key #f))
(define (instance-ref m id)
  (hash-ref (manager-instances m) id #f))

;运行实例的程序一步; 返回 (values 剩余程序或#f 描述)
(define (run-instruction! m i P)
  (match P
    [(Done)
     (set-instance-phase! i 'active)
     (values #f "加载完毕 -> active")]
    [(Fail why) (values #f (fail! why i))]
    [(Op key operation cont)
     (define state (state-ref m key))
     (cond
       [(not state) (values #f (fail! (format "没有共享状态 ~a" key) i))]
       [else
        ;操作失败时令牌也已用掉
        (define tok (fresh-id! m))
        (match (operation tok state)
          [(op-result new-state undo value)
           (hash-set! (manager-states m) key new-state)
           (push-undo! (undo-op key tok undo) i)
           (values (cont value) (format "在 ~a 上执行操作 (令牌 ~a), 结果 ~a" key tok value))]
          [#f (values #f (fail! (format "~a 上的操作被拒绝" key) i))])])]))

;弹出一项撤销; 撤销栈已空时返回 #f
(define (undo-one! m i)
  (match (instance-undo-stack i)
    ['() #f]
    [(cons (undo-op key tok undo) rest)
     ;; 逆作用在"现在"的状态上, 所以别人在中间做过的事会保留下来 (前提是撤销独立性, 见 M1 开头)
     (set-instance-undo-stack! i rest)
     (hash-set! (manager-states m) key (undo (state-ref m key)))
     (format "撤销 ~a 上的一次操作 (令牌 ~a)" key tok)]))
;按 LIFO 撤销全部
(define (unload! m id i trace)
  (let loop ()
    (define message (undo-one! m i))
    (when message
      (trace id message)
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
;对照: 逆按处理器删, 删掉的是第一个相同的处理器 (Cordis 早先的做法)
(define ((on/by-handler event handler) tok state)
  (op-result
   (hash-set state tok (cons event handler))
   (λ (state)
     (define first
       (for/first ([t (sort (hash-keys state) <)]
                   #:when (equal? (hash-ref state t) (cons event handler)))
         t))
     (if first (hash-remove state first) state))
   tok))
;对照: 写槽, 逆恢复写之前的值. 每个逆都撤得掉自己刚做的那次写,
;但两个实例写同一个槽时, 逆互相干扰 (不满足撤销独立性)
(define ((set-slot name value) tok state)
  (define old (hash-ref state name #f))
  (op-result
   (hash-set state name value)
   (λ (state) (if old (hash-set state name old) (hash-remove state name)))
   'ok))

;;; 编排操作 (外部输入); 前提不满足时报错

(define (existing-instance who m id)
  (or (instance-ref m id)
      (error who "没有编号为 ~a 的实例" id)))
;装上插件: 立即把它的程序从头跑到尾; 失败时撤掉已做的操作. 返回实例id
(define (install! m plug #:trace [trace void])
  (define id (fresh-id! m))
  (define i (instance plug 'loading '() #f))
  (hash-set! (manager-instances m) id i)
  (trace id (format "实例 ~a (插件 ~a) 开始加载" id (plugin-name plug)))
  (let loop ([P (plugin-body plug)])
    (define-values (next message) (run-instruction! m i P))
    (trace id message)
    (when next (loop next)))
  (when (eq? (instance-phase i) 'unloading)
    (unload! m id i trace)
    (set-instance-phase! i 'inactive)
    (trace id (format "卸载完毕 -> inactive (此次卸载由加载失败引起: ~a)"
                      (instance-failure i))))
  id)
;移除实例: 按 LIFO 撤掉它做过的全部操作, 再从管理器中删除
(define (dispose! m id #:trace [trace void])
  (define i (existing-instance 'dispose! m id))
  (set-instance-phase! i 'unloading)
  (trace id (format "实例 ~a (插件 ~a) 开始卸载, 原因: 被要求移除" id (instance-name i)))
  (unload! m id i trace)
  (hash-remove! (manager-instances m) id)
  (trace id (format "实例 ~a 卸载完毕, 从管理器中移除" id)))

;事件 event 发生时依次调用的处理器
(define (handlers-for m event)
  (define state (state-ref m 'events))
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
            (if (instance-failure i) "(失败)" "")))
  (newline)
  (printf "  -- 共享状态:")
  (printf " tools=~a" (sort (hash-keys (state-ref m 'tools)) string<?))
  (printf " events=~a" (sort (hash->list (state-ref m 'events)) < #:key car))
  (newline))

;;; 示例插件

(define shell
  (plugin "shell"
          (prog ('tools (register "ls" "列出文件"))
                ('tools (register "cat" "打印文件"))
                (Done))))
(define git
  (plugin "git"
          (prog ('tools (register "git" "版本控制"))
                (Done))))
;先登记 grep, 再登记已被占用的 ls -> 失败; grep 会被自动撤掉
(define bad
  (plugin "bad"
          (prog ('tools (register "grep" "搜索"))
                ('tools (register "ls" "冒牌 ls"))
                (Done))))
(define ping
  (plugin "ping"
          (prog ('events (on "tick" "ping"))
                (Done))))

(define (tools-of m)
  (sort (hash-keys (state-ref m 'tools)) string<?))

(module+ main
  (define m (make-manager))
  (define (scene title thunk)
    (printf "\n== ~a\n" title)
    (thunk)
    (show m))
  (define shell-id #f)
  (define bad-id #f)
  (define ping-id #f)
  (scene "装 shell 和 git"
         (λ () (set! shell-id (install! m shell #:trace print-step))
               (install! m git #:trace print-step)))
  (scene "装 bad: 登记 ls 被拒绝, 加载失败; 它先登记的 grep 被自动撤掉"
         (λ () (set! bad-id (install! m bad #:trace print-step))))
  (scene "移除 shell: 按 LIFO 撤掉 cat, ls; 之后装的 git 留着"
         (λ () (dispose! m shell-id #:trace print-step)))
  (scene "装 ping 两次: 同一个处理器登记了两次, 令牌不同"
         (λ () (set! ping-id (install! m ping #:trace print-step))
               (install! m ping #:trace print-step)))
  (scene "移除第一个 ping: 令牌让撤销只删它自己那一项"
         (λ () (dispose! m ping-id #:trace print-step)))
  (scene "移除失败的 bad: 它已经没有要撤的了"
         (λ () (dispose! m bad-id #:trace print-step))))

(module+ test
  (require rackunit)

  (define m (make-manager))
  (define shell-id (install! m shell))
  (define git-id (install! m git))
  (check-equal? (tools-of m) '("cat" "git" "ls"))
  (check-eq? (instance-phase (instance-ref m shell-id)) 'active)

  ;; 同一个插件装第二次: 第一个操作 (登记 ls) 就被拒绝, 没有要撤的
  (define shell2 (install! m shell))
  (check-eq? (instance-phase (instance-ref m shell2)) 'inactive)
  (check-equal? (tools-of m) '("cat" "git" "ls"))

  ;; 加载失败时, 已经做了的操作被撤掉
  (define bad-id (install! m bad))
  (check-eq? (instance-phase (instance-ref m bad-id)) 'inactive)
  (check-equal? (instance-failure (instance-ref m bad-id)) "tools 上的操作被拒绝")
  (check-equal? (tools-of m) '("cat" "git" "ls"))
  (check-equal? (instance-undo-stack (instance-ref m bad-id)) '())

  ;; 移除: 只撤掉自己的操作, 之后装的 git 留着
  (dispose! m shell-id)
  (check-equal? (tools-of m) '("git"))
  (check-false (instance-ref m shell-id))
  ;; 失败的实例也可以移除
  (dispose! m bad-id)
  (check-false (instance-ref m bad-id))
  (check-exn exn:fail? (λ () (dispose! m bad-id)))

  ;; 按 LIFO 撤销
  (let ([m (make-manager)] [log '()])
    (define id (install! m shell))
    (dispose! m id #:trace (λ (id message) (set! log (cons message log))))
    (check-equal? (filter (λ (s) (string-prefix? s "撤销")) (reverse log))
                  '("撤销 tools 上的一次操作 (令牌 2)" "撤销 tools 上的一次操作 (令牌 1)")))

  ;; 令牌: 同一个处理器登记两次, 移除第一个, 留下的是第二个的那一项
  (let ([m (make-manager)])
    (define p1 (install! m ping))
    (define p2 (install! m ping))
    (check-equal? (handlers-for m "tick") '("ping" "ping"))
    (dispose! m p1)
    (check-equal? (handlers-for m "tick") '("ping"))
    (check-equal? (hash-keys (state-ref m 'events)) (list (add1 p2))))
  ;; 对照: 逆按处理器删, 移除第二个时删掉的却是第一个的那一项
  (let ([m (make-manager)]
        [old-ping (plugin "old-ping" (prog ('events (on/by-handler "tick" "ping")) (Done)))])
    (define p1 (install! m old-ping))
    (define p2 (install! m old-ping))
    (dispose! m p2)
    (check-equal? (handlers-for m "tick") '("ping"))
    (check-equal? (hash-keys (state-ref m 'events)) (list (add1 p2))))

  ;; 反例: 都带逆, 也按 LIFO 撤, 但两个实例的逆不独立, 别人做的事没有保留下来
  (let* ([m (make-manager)]
         [a (install! m (plugin "a" (prog ('tools (set-slot "slot" 1)) (Done))))]
         [b (install! m (plugin "b" (prog ('tools (set-slot "slot" 2)) (Done))))])
    (dispose! m a)
    ;; b 仍在, 它写的值却没了
    (check-eq? (instance-phase (instance-ref m b)) 'active)
    (check-false (hash-ref (state-ref m 'tools) "slot" #f))
    (dispose! m b)
    ;; 两个都卸了, 留下的是 a 写的值
    (check-equal? (hash-ref (state-ref m 'tools) "slot" #f) 1))

  ;; 没有的共享状态
  (define nowhere (install! m (plugin "nowhere" (prog ('db (register "x" 1)) (Done)))))
  (check-equal? (instance-failure (instance-ref m nowhere)) "没有共享状态 db")

  ;; Fail: 撤掉之前做的操作
  (define quitter
    (install! m (plugin "quitter" (prog ('tools (register "tmp" "临时")) (Fail "不想装")))))
  (check-equal? (instance-failure (instance-ref m quitter)) "不想装")
  (check-equal? (tools-of m) '("git")))
