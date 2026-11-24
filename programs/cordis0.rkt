#lang racket
;对应 cordis-rocq 的 theories/Calculus.v, 逐条照搬, 不加任何优化或便利.
;与 cordis.rkt 的区别:
;  * 纯函数式: 状态 γ 是不可变的值, 一切规则都是 (step Σ prog γ ℓ) 的一个分支,
;    返回新状态或 #f (对应 None, 规则不适用).
;  * 规则以标签 (Label) 区分, 与 Rocq 的 Label 一一对应, 包括 LRetireChild,
;    LUnloaded, LRemove 等在 cordis.rkt 中被合并进别的步骤的规则.
;  * 服务是一等的 Σ: run 接收操作 (数据, 不是闭包), 令牌和状态.
;    多个服务先用 Sum 组合成一个 (theories/Compose.v).
;  * 错误只有四种: EUser EOp EUnresolved EConflict, 不带说明文字.
;  * 保留幽灵记录 oplog 和 inilog (没有规则读它们).
;记号: Rocq 的 option 用 #f 表示 None, 其余值表示 Some.
;      (所有可能为 None 的地方, Some 里的值都不会是 #f.)
;      K 的相等用 equal?.
(provide (all-defined-out))

;;; Service.v: 服务

;run : Op -> Tok -> St -> (list St (St -> St) Out) 或 #f
(struct service (run))
(define (run Σ a t s) ((service-run Σ) a t s))

;;; Prelude.v

(define (id x) x)

;;; Calculus.v: 程序与组件

(struct PDone () #:transparent)
(struct PFail () #:transparent)
;κ : Out -> Prog
(struct POp (k a κ) #:transparent)
(struct PProvide (k s P) #:transparent)
(struct PSpawn (c P) #:transparent)

;reacts: 实例 Active 时可以作为子 fiber 运行的处理器 (规则 O-React)
(struct component (deps provs body reacts) #:transparent)

;;; 状态

;Err: 'EUser 'EOp 'EUnresolved 'EConflict

(struct UOp (k pid tok g) #:transparent)
(struct UProv (k pid) #:transparent)
(struct USpawn (m) #:transparent)

;View: (k . pid) 的列表, 次序同 deps

;Life; z 是 Err 或 #f
(struct Inactive (z) #:transparent)
(struct Loading (P acc w) #:transparent)
(struct Active (acc w) #:transparent)
(struct Unloading (acc w z) #:transparent)

;parent 为 #f 表示由编排者插入
(struct fiber (comp parent disposed life) #:transparent)
(struct binding (pid owner bst) #:transparent)

;所有用过的名字 (fiber 编号), pid 和令牌都小于 next
;fibers : nat -> option Fiber, binds : K -> option Binding,
;oplog : nat -> option Op, inilog : nat -> option St; 都用不可变 hash 表示,
;不在 hash 中即为 None
(struct state (next fibers binds oplog inilog) #:transparent)

(define init (state 0 (hash) (hash) (hash) (hash)))

;;; 辅助函数

(define (kmem k ks) (and (member k ks) #t))
(define (overlaps ks1 ks2) (ormap (λ (k) (kmem k ks2)) ks1))

(define (fupd F n o) (if o (hash-set F n o) (hash-remove F n)))
(define (bupd B k o) (if o (hash-set B k o) (hash-remove B k)))

(define (fibers γ n) (hash-ref (state-fibers γ) n #f))
(define (binds γ k) (hash-ref (state-binds γ) k #f))

(define (names γ) (range (state-next γ)))

(define (is-active l) (Active? l))
(define (is-installed l) (not (Inactive? l)))
(define (view-of l)
  (match l
    [(or (Loading _ _ w) (Active _ w) (Unloading _ w _)) w]
    [(Inactive _) '()]))

(define (lookup-view k w)
  (match w
    ['() #f]
    [(cons (cons k* p) w*) (if (equal? k k*) p (lookup-view k w*))]))

;;; 派生概念

;键可见: 已绑定, 且绑定的 owner 处于 Active
(define (visible γ k)
  (match (binds γ k)
    [(binding pid owner _)
     (match (fibers γ owner)
       [(? fiber? f) (and (is-active (fiber-life f)) pid)]
       [#f #f])]
    [#f #f]))

(define (resolve γ ks)
  (match ks
    ['() '()]
    [(cons k ks*)
     (define p (visible γ k))
     (define w (resolve γ ks*))
     (and p w (cons (cons k p) w))]))

;#f 即 ⊥: 该 fiber 不应运行
(define (target prog γ n)
  (match (fibers γ n)
    [(? fiber? f)
     (if (fiber-disposed f)
         #f
         (resolve γ (component-deps (prog (fiber-comp f)))))]
    [#f #f]))

(define (target-is prog γ n w)
  (define w* (target prog γ n))
  (and w* (equal? w w*)))

(define (resolves γ m p)
  (match (fibers γ m)
    [(? fiber? f)
     (and (is-installed (fiber-life f))
          (ormap (λ (kp) (= (cdr kp) p)) (view-of (fiber-life f))))]
    [#f #f]))

;除 n 以外有已安装的 fiber 把某个键解析到 p
(define (relied γ n p)
  (ormap (λ (m) (and (not (= m n)) (resolves γ m p))) (names γ)))

;卸载的守卫: acc 中某个尚未撤回的 provision 仍被别的已安装 fiber 解析.
;成立时 n 既不撤销任何一项, 也不请子 fiber 退出 (Cordis 先等全部依赖者再启动 disposer)
(define (held γ n acc)
  (ormap (λ (u) (match u [(UProv _ p) (relied γ n p)] [_ #f])) acc))

(define (has-child γ n)
  (ormap (λ (m)
           (match (fibers γ m)
             [(? fiber? f) (match (fiber-parent f) [#f #f] [q (= q n)])]
             [#f #f]))
         (names γ)))

;组件 c 会提供某个现存 fiber 可能提供的键
(define (conflict prog γ c)
  (ormap (λ (m)
           (match (fibers γ m)
             [(? fiber? f)
              (overlaps (component-provs (prog c))
                        (component-provs (prog (fiber-comp f))))]
             [#f #f]))
         (names γ)))

;;; 状态更新

(define (with-fibers γ F) (struct-copy state γ [fibers F]))
(define (with-binds γ B) (struct-copy state γ [binds B]))
(define (bump γ) (struct-copy state γ [next (add1 (state-next γ))]))
(define (log-op γ t a)
  (struct-copy state γ [oplog (hash-set (state-oplog γ) t a)]))
(define (log-ini γ p s)
  (struct-copy state γ [inilog (hash-set (state-inilog γ) p s)]))

(define (set-fiber γ n f)
  (with-fibers γ (fupd (state-fibers γ) n f)))
(define (set-life γ n f l)
  (set-fiber γ n (fiber (fiber-comp f) (fiber-parent f) (fiber-disposed f) l)))

;;; 标签

(struct OInsert (c) #:transparent)
(struct ODispose (n) #:transparent)
(struct OReset (n) #:transparent)
(struct LBegin (n) #:transparent)
(struct LStep (n) #:transparent)
(struct LDivert (n) #:transparent)
(struct LLeave (n) #:transparent)
(struct LUndo (n) #:transparent)
(struct LRetireChild (n) #:transparent)
(struct LUnloaded (n) #:transparent)
(struct LRemove (n) #:transparent)
(struct OReact (n i) #:transparent)
(struct ORestart (n) #:transparent)   ;强制重新加载: Cordis 的 restart

;;; Loading 中的 fiber 走一步

(define (load-step Σ prog γ n f P acc w)
  (define (fail z) (set-life γ n f (Unloading acc w z)))
  (match P
    [(PDone) (set-life γ n f (Active acc w))]
    [(PFail) (fail 'EUser)]
    [(POp k a κ)
     (define rp
       (if (kmem k (component-deps (prog (fiber-comp f))))
           (lookup-view k w)
           (match (binds γ k)
             [(? binding? b) (and (= (binding-owner b) n) (binding-pid b))]
             [#f #f])))
     (match* (rp (binds γ k))
       [((? number? p) (? binding? b))
        (if (= (binding-pid b) p)
            (match (run Σ a (state-next γ) (binding-bst b))
              [(list s* g o)
               (define γ1
                 (bump (log-op (with-binds γ (bupd (state-binds γ) k
                                                   (binding (binding-pid b) (binding-owner b) s*)))
                               (state-next γ) a)))
               (set-life γ1 n f (Loading (κ o) (cons (UOp k p (state-next γ) g) acc) w))]
              [#f (set-life (bump γ) n f (Unloading acc w 'EOp))])
            (fail 'EUnresolved))]
       [(_ _) (fail 'EUnresolved)])]
    [(PProvide k s P*)
     (if (kmem k (component-provs (prog (fiber-comp f))))
         (match (binds γ k)
           [#f
            (define p (state-next γ))
            (define γ1
              (bump (log-ini (with-binds γ (bupd (state-binds γ) k (binding p n s))) p s)))
            (set-life γ1 n f (Loading P* (cons (UProv k p) acc) w))]
           [_ (fail 'EConflict)])
         (fail 'EConflict))]
    [(PSpawn c P*)
     (if (conflict prog γ c)
         (fail 'EConflict)
         (let* ([m (state-next γ)]
                [γ1 (bump (with-fibers γ (fupd (state-fibers γ) m
                                               (fiber c n #f (Inactive #f)))))])
           (set-life γ1 n f (Loading P* (cons (USpawn m) acc) w))))]))

;;; Unloading 中的 fiber 撤销一项
;step 只在 held 不成立时调用它, 那时表头 UProv 的 relied 必然不成立; 这里的检查让 undo-step 自身也完整

(define (undo-step γ n f u acc w z)
  (define (continue γ*) (set-life γ* n f (Unloading acc w z)))
  (match u
    [(UOp k p _ g)
     (match (binds γ k)
       [(? binding? b)
        (if (= (binding-pid b) p)
            (continue (with-binds γ (bupd (state-binds γ) k
                                          (binding (binding-pid b) (binding-owner b)
                                                   (g (binding-bst b))))))
            (continue γ))]
       [#f (continue γ)])]
    [(UProv k p)
     (if (relied γ n p)
         #f
         (match (binds γ k)
           [(? binding? b)
            (if (= (binding-pid b) p)
                (continue (with-binds γ (bupd (state-binds γ) k #f)))
                (continue γ))]
           [#f (continue γ)]))]
    [(USpawn m)
     (match (fibers γ m)
       [#f (continue γ)]
       [_ #f])]))

;;; 转移函数

(define (step Σ prog γ ℓ)
  (match ℓ
    [(OInsert c)
     (if (conflict prog γ c)
         #f
         (bump (with-fibers γ (fupd (state-fibers γ) (state-next γ)
                                    (fiber c #f #f (Inactive #f))))))]
    [(ODispose n)
     (match (fibers γ n)
       [(? fiber? f) (set-fiber γ n (fiber (fiber-comp f) (fiber-parent f) #t (fiber-life f)))]
       [#f #f])]
    [(OReset n)
     (match (fibers γ n)
       [(? fiber? f)
        (match (fiber-life f)
          [(Inactive (? symbol?)) (set-life γ n f (Inactive #f))]
          [_ #f])]
       [#f #f])]
    [(LBegin n)
     (match (fibers γ n)
       [(? fiber? f)
        (match* ((fiber-life f) (target prog γ n))
          [((Inactive #f) (? list? w))
           (set-life γ n f (Loading (component-body (prog (fiber-comp f))) '() w))]
          [(_ _) #f])]
       [#f #f])]
    [(LStep n)
     (match (fibers γ n)
       [(? fiber? f)
        (match (fiber-life f)
          [(Loading P acc w)
           ;may_step: 只有收尾的 PDone 要求 target 未变, 其余步可以落地
           (if (or (not (PDone? P)) (target-is prog γ n w)) (load-step Σ prog γ n f P acc w) #f)]
          [_ #f])]
       [#f #f])]
    [(LDivert n)
     (match (fibers γ n)
       [(? fiber? f)
        (match (fiber-life f)
          [(Loading _ acc w)
           (if (target-is prog γ n w) #f (set-life γ n f (Unloading acc w #f)))]
          [_ #f])]
       [#f #f])]
    [(LLeave n)
     (match (fibers γ n)
       [(? fiber? f)
        (match (fiber-life f)
          [(Active acc w)
           (if (target-is prog γ n w) #f (set-life γ n f (Unloading acc w #f)))]
          [_ #f])]
       [#f #f])]
    [(LUndo n)
     (match (fibers γ n)
       [(? fiber? f)
        (match (fiber-life f)
          [(Unloading (cons u acc) w z)
           (if (held γ n (cons u acc)) #f (undo-step γ n f u acc w z))]
          [_ #f])]
       [#f #f])]
    [(LRetireChild n)
     (match (fibers γ n)
       [(? fiber? f)
        (match (fiber-life f)
          [(Unloading (cons (USpawn m) acc) _ _)
           (match (fibers γ m)
             [(? fiber? g)
              (if (or (held γ n (cons (USpawn m) acc)) (fiber-disposed g))
                  #f
                  (set-fiber γ m (fiber (fiber-comp g) (fiber-parent g) #t (fiber-life g))))]
             [#f #f])]
          [_ #f])]
       [#f #f])]
    [(LUnloaded n)
     (match (fibers γ n)
       [(? fiber? f)
        (match (fiber-life f)
          [(Unloading '() _ z) (set-life γ n f (Inactive z))]
          [_ #f])]
       [#f #f])]
    [(LRemove n)
     (match (fibers γ n)
       [(? fiber? f)
        (match (fiber-life f)
          [(Inactive _)
           (if (and (fiber-disposed f) (not (has-child γ n)))
               (with-fibers γ (fupd (state-fibers γ) n #f))
               #f)]
          [_ #f])]
       [#f #f])]
    [(OReact n i)
     (match (fibers γ n)
       [(? fiber? f)
        (match (fiber-life f)
          [(Active acc w)
           (define reacts (component-reacts (prog (fiber-comp f))))
           (match (and (< i (length reacts)) (list-ref reacts i))
             [#f #f]
             [c
              (if (or (fiber-disposed f) (conflict prog γ c))
                  #f
                  (let* ([m (state-next γ)]
                         [γ1 (bump (with-fibers γ (fupd (state-fibers γ) m
                                                        (fiber c n #f (Inactive #f)))))])
                    (set-life γ1 n f (Active (cons (USpawn m) acc) w))))])]
          [_ #f])]
       [#f #f])]
    [(ORestart n)
     (match (fibers γ n)
       [(? fiber? f)
        (if (fiber-disposed f)
            #f
            (match (fiber-life f)
              [(or (Loading _ acc w) (Active acc w)) (set-life γ n f (Unloading acc w #f))]
              [_ #f]))]
       [#f #f])]))

;;; 执行: 初始状态和标签列表

(define (run-labels Σ prog γ ls)
  (match ls
    ['() γ]
    [(cons ℓ ls*)
     (define γ* (step Σ prog γ ℓ))
     (and γ* (run-labels Σ prog γ* ls*))]))

(define (lifecycle-labels n)
  (list (LBegin n) (LStep n) (LDivert n) (LLeave n) (LUndo n)
        (LRetireChild n) (LUnloaded n) (LRemove n)))

;静止: 任何地方都没有生命周期规则适用.
;Rocq 中对一切 n 量化; n ≥ next 时 fibers γ n = None, 所有规则都不适用,
;所以只需检查 names γ.
(define (quiet? Σ prog γ)
  (for*/and ([n (names γ)] [ℓ (lifecycle-labels n)])
    (not (step Σ prog γ ℓ))))

;;; ======== 以下不属于 Calculus.v ========

;;; 程序的写法 (与 cordis.rkt 的 prog 宏相同, 改名以免与程序表 prog 冲突)

(define-syntax program
  (syntax-rules (serve spawn <-)
    [(_ last) last]
    [(_ (serve k s) rest ...) (PProvide k s (program rest ...))]
    [(_ (spawn c) rest ...) (PSpawn c (program rest ...))]
    [(_ (x <- k a) rest ...) (POp k a (λ (x) (program rest ...)))]
    [(_ (k a) rest ...) (POp k a (λ (_) (program rest ...)))]))

;;; 服务: Services/Registry.v, Services/EventBus.v, Compose.v 中的 Sum

;注册表: 状态是 名字 -> 值 的不可变 hash (逐点比较即 equal?)
(struct Register (x v) #:transparent)
(struct Lookup (x) #:transparent)
(define Registry
  (service
   (λ (a t s)
     (match a
       [(Register x v)
        (if (hash-has-key? s x)
            #f
            (list (hash-set s x v) (λ (s*) (hash-remove s* x)) #f))]
       [(Lookup x) (list s id (hash-ref s x #f))]))))

;事件总线: 状态是 (令牌 . 回调) 的有序列表
(struct On (cb) #:transparent)
(struct Prepend (cb) #:transparent)
(struct Emit () #:transparent)
(struct OnByCallback (cb) #:transparent)
(define (mem t s) (ormap (λ (h) (= (car h) t)) s))
(define ((remove-tok t) s) (filter (λ (h) (not (= (car h) t))) s))
(define ((remove-first-cb cb) s)
  (match s
    ['() '()]
    [(cons h s*) (if (equal? (cdr h) cb) s* (cons h ((remove-first-cb cb) s*)))]))
(define EventBus
  (service
   (λ (a t s)
     (match a
       [(On cb) (if (mem t s) #f (list (append s (list (cons t cb))) (remove-tok t) '()))]
       [(Prepend cb) (if (mem t s) #f (list (cons (cons t cb) s) (remove-tok t) '()))]
       [(Emit) (list s id (map cdr s))]
       [(OnByCallback cb)
        (if (mem t s) #f (list (append s (list (cons t cb))) (remove-first-cb cb) '()))]))))

;两个服务并列; 一方的操作作用在另一方的状态上时失败
(struct inl (v) #:transparent)
(struct inr (v) #:transparent)
(define ((lift1 g) x) (match x [(inl a) (inl (g a))] [(inr _) x]))
(define ((lift2 g) x) (match x [(inl _) x] [(inr b) (inr (g b))]))
(define (Sum Σ1 Σ2)
  (service
   (λ (a t x)
     (match* (a x)
       [((inl a1) (inl s1))
        (match (run Σ1 a1 t s1) [(list s* g o) (list (inl s*) (lift1 g) (inl o))] [#f #f])]
       [((inr a2) (inr s2))
        (match (run Σ2 a2 t s2) [(list s* g o) (list (inr s*) (lift2 g) (inr o))] [#f #f])]
       [(_ _) #f]))))

;;; 调度 (外部): 反复选一条可用的生命周期标签, 直到静止

;可用的生命周期标签
(define (enabled Σ prog γ)
  (for*/list ([n (names γ)] [ℓ (lifecycle-labels n)]
              #:when (step Σ prog γ ℓ))
    ℓ))

;choose : 非空的标签列表 -> 其中一个; 返回 (values 静止状态 标签序列)
(define (settle Σ prog γ #:choose [choose car] #:trace [trace void])
  (let loop ([γ γ] [log '()])
    (match (enabled Σ prog γ)
      ['() (values γ (reverse log))]
      [ℓs (define ℓ (choose ℓs))
          (define γ* (step Σ prog γ ℓ))
          (trace ℓ γ*)
          (loop γ* (cons ℓ log))])))

(define (random-choose seed)
  (define rng (make-pseudo-random-generator))
  (parameterize ([current-pseudo-random-generator rng]) (random-seed seed))
  (λ (ℓs) (parameterize ([current-pseudo-random-generator rng])
            (list-ref ℓs (random (length ℓs))))))

;编排标签必须适用, 否则报错
(define (orchestrate Σ prog γ ℓ)
  (or (step Σ prog γ ℓ)
      (error 'orchestrate "标签 ~a 不适用" ℓ)))

;下一步 LUndo 是否会走"过期"分支 (绑定已不在或 pid 已变);
;按 Preservation.v 的不变量, 从 init 出发这不会发生
(define (stale-undo? γ n)
  (match (fibers γ n)
    [(fiber _ _ _ (Unloading (cons (or (UOp k p _ _) (UProv k p)) _) _ _))
     (match (binds γ k)
       [(? binding? b) (not (= (binding-pid b) p))]
       [#f #t])]
    [_ #f]))

;;; 显示

(define (life-tag l)
  (match l
    [(Inactive z) (if z (format "inactive(~a)" z) "inactive")]
    [(Loading _ _ _) "loading"]
    [(Active _ _) "active"]
    [(Unloading _ _ z) (if z (format "unloading(~a)" z) "unloading")]))

(define (show γ)
  (printf "  -- fibers:")
  (for ([n (names γ)])
    (match (fibers γ n)
      [#f (void)]
      [(fiber c parent disposed l)
       (printf " ~a#~a~a~a=~a" c n
               (if parent (format "(父#~a)" parent) "")
               (if disposed "(弃置)" "")
               (life-tag l))]))
  (newline)
  (printf "  -- binds:")
  (when (zero? (hash-count (state-binds γ))) (printf " (无)"))
  (for ([(k b) (state-binds γ)])
    (printf " ~a[pid ~a, owner #~a]=~a" k (binding-pid b) (binding-owner b)
            (match (binding-bst b)
              [(inl s) (sort (hash-keys s) string<?)]
              [(inr s) s])))
  (newline))

;;; 示例: 与 cordis.rkt 相同的插件, 只是服务换成 Registry ⊕ EventBus

(define Σ (Sum Registry EventBus))
(define (reg x v) (inl (Register x v)))
(define (on cb) (inr (On cb)))

(define components
  (hash
   'core (component '() '(tools) (program (serve 'tools (inl (hash))) (PDone)) '())
   ;提供 tools 之后自己再登记一个条目, 用来检查卸载守卫作用于整个卸载
   'core+ (component '() '(tools)
                     (program (serve 'tools (inl (hash)))
                              ('tools (reg "builtin" "内建"))
                              (PDone))
                     '())
   'shell (component '(tools) '()
                     (program ('tools (reg "ls" "列出文件"))
                              ('tools (reg "cat" "打印文件"))
                              (PDone))
                     '())
   'git (component '(tools) '() (program ('tools (reg "git" "版本控制")) (PDone)) '())
   ;先登记 grep, 再登记已被占用的 ls -> EOp; grep 会被撤掉
   'bad (component '(tools) '()
                   (program ('tools (reg "grep" "搜索"))
                            ('tools (reg "ls" "冒牌 ls"))
                            (PDone))
                   '())
   'grep-tool (component '(tools) '() (program ('tools (reg "grep" "搜索")) (PDone)) '())
   'sed-tool (component '(tools) '() (program ('tools (reg "sed" "流编辑")) (PDone)) '())
   'toolkit (component '(tools) '()
                       (program (spawn 'grep-tool)
                                ('tools (reg "help" "工具箱帮助"))
                                (spawn 'sed-tool)
                                (PDone))
                       '())
   'bus (component '() '(events) (program (serve 'events (inr '())) (PDone)) '())
   'ping (component '(events) '() (program ('events (on "ping")) (PDone)) '())
   'watcher (component '(events) '() (program ('events (on "watcher")) (PDone)) '(ping))))
(define (prog c) (hash-ref components c))

(define (tools-of γ)
  (match (binds γ 'tools)
    [(binding _ _ (inl s)) (sort (hash-keys s) string<?)]
    [#f #f]))
(define (handlers-of γ)
  (match (binds γ 'events)
    [(binding _ _ (inr s)) (sort (map cdr s) string<?)]
    [#f #f]))
;编号为 n 的 fiber 的组件为 c 时返回 n
(define (fiber-named γ c)
  (for/first ([n (names γ)]
              #:when (match (fibers γ n) [(fiber c* _ _ _) (equal? c c*)] [#f #f]))
    n))

(module+ main
  (define γ init)
  (define (scene title . ℓs)
    (printf "\n== ~a\n" title)
    (for ([ℓ ℓs])
      (printf "  ~v\n" ℓ)
      (set! γ (orchestrate Σ prog γ ℓ)))
    (define-values (γ* _)
      (settle Σ prog γ #:trace (λ (ℓ γ) (printf "    ~v\n" ℓ))))
    (set! γ γ*)
    (show γ))
  (scene "先装依赖者 shell, git, 再装提供者 core"
         (OInsert 'shell) (OInsert 'git) (OInsert 'core))
  (scene "装 toolkit: 它在加载中 spawn 两个子插件" (OInsert 'toolkit))
  (scene "移除 toolkit: 先 LRetireChild 让 sed-tool 弃置, 等它被移除后再撤 help, 再 grep-tool"
         (ODispose (fiber-named γ 'toolkit)))
  (scene "restart core: 依赖者先 LLeave, core 在它们卸载完之前什么都不撤 (held), 再重新提供"
         (ORestart (fiber-named γ 'core)))
  (scene "装 bad: 第二次 Register 失败, Unloading(EOp), 卸完停在 Inactive(EOp)"
         (OInsert 'bad))
  (scene "装 bus 和 watcher" (OInsert 'bus) (OInsert 'watcher))
  (scene "watcher 反应两次" (OReact (fiber-named γ 'watcher) 0)
         (OReact (fiber-named γ 'watcher) 0))
  (scene "单独撤销第一次反应 (ODispose 子 fiber)" (ODispose (fiber-named γ 'ping)))
  (scene "移除 watcher: 剩下的反应先退出" (ODispose (fiber-named γ 'watcher))))

(module+ test
  (require rackunit)

  (define (orch γ . ℓs)
    (for/fold ([γ γ]) ([ℓ ℓs]) (orchestrate Σ prog γ ℓ)))
  (define (go γ)
    (define-values (γ* _) (settle Σ prog γ))
    (check-true (quiet? Σ prog γ*))
    γ*)

  ;; 服务: 每个操作的逆在应用处撤销它 (Witnessed)
  (for ([a (list (reg "x" 1) (inl (Lookup "x")) (on "cb") (inr (Prepend "cb"))
                 (inr (Emit)))]
        [s (list (inl (hash)) (inl (hash "x" 0)) (inr '((3 . "cb"))) (inr '((3 . "cb")))
                 (inr '((3 . "cb"))))])
    (match (run Σ a 7 s)
      [(list s* g _) (check-equal? (g s*) s)]
      [#f (void)]))
  ;; OnByCallback 不满足 Witnessed (EventBus.v 中的反例):
  ;; 逆删掉第一个同回调的钩子, 即别人更早登记的那个
  (match-let ([(list s* g _) (run Σ (inr (OnByCallback "cb")) 7 (inr '((3 . "cb"))))])
    (check-equal? (g s*) (inr '((7 . "cb")))))
  (check-false (run Σ (reg "x" 1) 0 (inr '())))   ;跨服务的操作失败

  ;; 守卫作用于整个卸载 (held): core+ 在 provide 之后登记了 builtin;
  ;; 重启时只要 shell 还解析着 tools, core+ 连 builtin 也不撤, 也就是
  ;; shell 卸载时看到的是 core+ 的全部效应
  (let* ([γ (go (orch init (OInsert 'core+) (OInsert 'shell)))]
         [γ (orch γ (ORestart 0))])
    (check-false (step Σ prog γ (LUndo 0)))
    (define γ1 (run-labels Σ prog γ (list (LLeave 1))))
    (check-false (step Σ prog γ1 (LUndo 0)))
    (check-equal? (tools-of γ1) '("builtin" "cat" "ls"))
    (define γ2 (run-labels Σ prog γ1 (list (LUndo 1) (LUndo 1))))
    (check-equal? (tools-of γ2) '("builtin"))
    (check-false (step Σ prog γ2 (LUndo 0)))          ; shell 还没卸载完
    (define γ3 (run-labels Σ prog γ2 (list (LUnloaded 1))))
    (check-not-false (step Σ prog γ3 (LUndo 0)))
    (check-equal? (tools-of (go γ3)) '("builtin" "cat" "ls")))

  ;; Examples/Basic.v: consumer 在 provider Active 之前不能 LBegin
  (let* ([γ (orch init (OInsert 'shell) (OInsert 'core))])
    (check-false (step Σ prog γ (LBegin 0)))
    ;; 状态里有闭包 (κ, 逆), 不能直接 equal?, 比较观察
    (define γ* (run-labels Σ prog γ (list (LBegin 1) (LStep 1) (LStep 1)
                                          (LBegin 0) (LStep 0) (LStep 0) (LStep 0))))
    (check-true (quiet? Σ prog γ*))
    (check-equal? (tools-of γ*) '("cat" "ls"))
    (check-equal? (map (λ (n) (life-tag (fiber-life (fibers γ* n)))) '(0 1))
                  '("active" "active")))

  ;; 注册表, spawn
  (define γ1 (go (orch init (OInsert 'shell) (OInsert 'git) (OInsert 'core))))
  (check-equal? (tools-of γ1) '("cat" "git" "ls"))
  (define γ2 (go (orch γ1 (OInsert 'toolkit))))
  (check-equal? (tools-of γ2) '("cat" "git" "grep" "help" "ls" "sed"))
  (check-equal? (hash-count (state-fibers γ2)) 6)
  (define γ3 (go (orch γ2 (ODispose (fiber-named γ2 'toolkit)))))
  (check-equal? (tools-of γ3) '("cat" "git" "ls"))
  (check-equal? (hash-count (state-fibers γ3)) 3)
  ;; 幽灵记录: 每个用过的令牌都记下了操作
  (check-equal? (hash-ref (state-oplog γ3) (car (sort (hash-keys (state-oplog γ3)) <)))
                (reg "ls" "列出文件"))

  ;; restart: 结果不变, tools 换了 pid
  (define core (fiber-named γ3 'core))
  (define γ4 (go (orch γ3 (ORestart core))))
  (check-equal? (tools-of γ4) '("cat" "git" "ls"))
  (check-not-equal? (binding-pid (binds γ4 'tools)) (binding-pid (binds γ3 'tools)))
  (check-false (step Σ prog γ4 (ORestart 999)))

  ;; reset: 只对 Inactive(Some _) 适用
  (define γ5 (go (orch γ4 (OInsert 'bad))))
  (define bad (fiber-named γ5 'bad))
  (check-equal? (fiber-life (fibers γ5 bad)) (Inactive 'EOp))
  (check-equal? (tools-of γ5) '("cat" "git" "ls"))
  (check-false (step Σ prog γ5 (OReset (fiber-named γ5 'shell))))
  (define γ6 (go (orch γ5 (OReset bad))))
  (check-equal? (fiber-life (fibers γ6 bad)) (Inactive 'EOp))
  (check-equal? (tools-of γ6) '("cat" "git" "ls"))

  ;; react: 相同的回调登记两次, 令牌让撤销只删自己那一项
  (define γ7 (go (orch γ6 (OInsert 'bus) (OInsert 'watcher))))
  (define watcher (fiber-named γ7 'watcher))
  (check-false (step Σ prog γ7 (OReact watcher 1)))
  (define γ8 (go (orch γ7 (OReact watcher 0) (OReact watcher 0))))
  (check-equal? (handlers-of γ8) '("ping" "ping" "watcher"))
  (define ping1 (fiber-named γ8 'ping))
  (define γ9 (go (orch γ8 (ODispose ping1))))
  (check-equal? (handlers-of γ9) '("ping" "watcher"))
  (check-false (fibers γ9 ping1))
  (define γ10 (go (orch γ9 (ODispose watcher))))
  (check-equal? (handlers-of γ10) '())
  (check-false (fiber-named γ10 'ping))

  ;; 合流: 同一个初始状态, 不同调度得到相同的观察
  ;; (fiber 编号和 pid 可以不同, 比较组件名, 生命期和服务内容)
  (define (observe γ)
    (list (sort (for/list ([n (names γ)] #:when (fibers γ n))
                  (match-define (fiber c _ d l) (fibers γ n))
                  (format "~a:~a:~a" c d (life-tag l)))
                string<?)
          (tools-of γ)
          (handlers-of γ)))
  (define (scenario choose)
    (define (go! γ)
      (let loop ([γ γ])
        (match (enabled Σ prog γ)
          ['() γ]
          [ℓs (define ℓ (choose ℓs))
              (match ℓ
                [(LUndo n) (check-false (stale-undo? γ n))]
                [_ (void)])
              (loop (step Σ prog γ ℓ))])))
    (define γa (go! (orch init (OInsert 'shell) (OInsert 'toolkit) (OInsert 'core)
                          (OInsert 'git) (OInsert 'bus) (OInsert 'watcher))))
    (define w (fiber-named γa 'watcher))
    (define γb (go! (orch γa (OReact w 0) (OReact w 0) (ORestart (fiber-named γa 'core)))))
    (define γc (go! (orch γb (ODispose (fiber-named γb 'toolkit)) (ORestart w))))
    (check-true (quiet? Σ prog γc))
    (map observe (list γa γb γc)))
  (define expected (scenario car))
  (for ([seed (in-range 200)])
    (check-equal? (scenario (random-choose seed)) expected (format "种子 ~a" seed))))
