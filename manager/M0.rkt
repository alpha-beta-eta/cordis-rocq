#lang racket
;渐进的插件管理器, 第0层: 注册.
;计划与各层的说明见 README.md. 每层是一个完整的文件, 不依赖前面的层; 相邻两层的差别见 diffs/.
;本层: 插件是一个名字加一段程序 (body). install! 立即把 body 从头跑到尾,
;  body 里的每个操作改动管理器里的一份共享状态 (工具注册表, 事件处理器表).
;留给下一层的问题: 装上去的插件卸不掉; 加载到一半失败时, 已经做了的事留在共享状态里.
(provide (all-defined-out))

;operation : 状态 -> op-result 或 #f (#f 表示操作被拒绝)
(struct op-result (state value))

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
;phase 是 'loading, 'active (装好了) 或 'failed (加载失败, 停下); failure 是失败的原因
(struct instance
  (plugin phase failure)
  #:mutable)
(define instance-name
  (compose plugin-name instance-plugin))
(define (fail! why i)
  (set-instance-phase! i 'failed)
  (set-instance-failure! i why)
  (format "失败 (~a), 停下; 已经做了的操作留在共享状态里" why))
;instances是实例id和实例的字典
;states是键和共享状态的字典; 本层的键在创建管理器时给定, 插件不能增加
(struct manager
  ([next-id #:mutable] instances states))
(define (make-manager)
  (manager 0 (make-hash) (make-hash (list (cons 'tools (hash)) (cons 'events '())))))
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
        (match (operation state)
          [(op-result new-state value)
           (hash-set! (manager-states m) key new-state)
           (values (cont value) (format "在 ~a 上执行操作, 结果 ~a" key value))]
          [#f (values #f (fail! (format "~a 上的操作被拒绝" key) i))])])]))

;;; 服务操作的例子

;注册表: 状态是 名字 -> 值 的hash; 名字已被占用时拒绝
(define ((register name value) state)
  (and (not (hash-has-key? state name))
       (op-result
        (hash-set state name value)
        'ok)))
;事件处理器表: 状态是 (事件名 . 处理器) 的列表, 按登记的顺序
(define ((on event handler) state)
  (op-result
   (append state (list (cons event handler)))
   'ok))

;;; 编排操作 (外部输入)

;装上插件: 立即把它的程序从头跑到尾; 返回实例id
(define (install! m plug #:trace [trace void])
  (define id (fresh-id! m))
  (define i (instance plug 'loading #f))
  (hash-set! (manager-instances m) id i)
  (trace id (format "实例 ~a (插件 ~a) 开始加载" id (plugin-name plug)))
  (let loop ([P (plugin-body plug)])
    (define-values (next message) (run-instruction! m i P))
    (trace id message)
    (when next (loop next)))
  id)

;事件 event 发生时依次调用的处理器
(define (handlers-for m event)
  (for/list ([h (state-ref m 'events)] #:when (equal? (car h) event))
    (cdr h)))

(define (print-step id message)
  (printf "  [~a] ~a\n" id message))

(define (show m)
  (printf "  -- 实例:")
  (for ([id (sort (hash-keys (manager-instances m)) <)])
    (define i (instance-ref m id))
    (printf " ~a#~a=~a" (instance-name i) id (instance-phase i)))
  (newline)
  (printf "  -- 共享状态:")
  (for ([key '(tools events)])
    (define state (state-ref m key))
    (printf " ~a=~a" key (if (hash? state) (sort (hash-keys state) string<?) state)))
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
;先登记 grep, 再登记已被占用的 ls -> 失败; grep 留在注册表里
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
  (scene "装 shell 和 git"
         (λ () (install! m shell #:trace print-step)
               (install! m git #:trace print-step)))
  (scene "装 ping 两次: 同一个处理器登记了两次"
         (λ () (install! m ping #:trace print-step)
               (install! m ping #:trace print-step)
               (printf "  tick 的处理器: ~a\n" (handlers-for m "tick"))))
  (scene "装 bad: 登记 ls 被拒绝, 加载失败; 但它先登记的 grep 留在了注册表里"
         (λ () (install! m bad #:trace print-step)))
  (printf "\n本层没有卸载: shell, git, 两个 ping 和半截的 bad 都只能留着.\n"))

(module+ test
  (require rackunit)

  (define m (make-manager))
  (define shell-id (install! m shell))
  (void (install! m git))
  (check-equal? (tools-of m) '("cat" "git" "ls"))
  (check-eq? (instance-phase (instance-ref m shell-id)) 'active)

  ;; 同一个插件装第二次: 第一个操作 (登记 ls) 就被拒绝
  (define shell2 (install! m shell))
  (check-eq? (instance-phase (instance-ref m shell2)) 'failed)
  (check-equal? (tools-of m) '("cat" "git" "ls"))

  ;; 同一个处理器可以登记多次, 按顺序排着
  (void (install! m ping))
  (void (install! m ping))
  (check-equal? (handlers-for m "tick") '("ping" "ping"))

  ;; 本层的问题: 加载失败时, 已经做了的操作留在共享状态里
  (define bad-id (install! m bad))
  (check-eq? (instance-phase (instance-ref m bad-id)) 'failed)
  (check-equal? (instance-failure (instance-ref m bad-id)) "tools 上的操作被拒绝")
  (check-equal? (tools-of m) '("cat" "git" "grep" "ls"))

  ;; 没有的共享状态
  (define nowhere (install! m (plugin "nowhere" (prog ('db (register "x" 1)) (Done)))))
  (check-equal? (instance-failure (instance-ref m nowhere)) "没有共享状态 db")

  ;; Fail
  (define quitter (install! m (plugin "quitter" (prog (Fail "不想装")))))
  (check-equal? (instance-failure (instance-ref m quitter)) "不想装"))
