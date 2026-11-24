#lang racket
;按博客文章 "deepseek harness笔记2" (alpha-beta-eta.github.io/source/dsh2.rkt) 组织的演算.
;章节, 记号和名字都跟着文章走:
;  服务 Σ 带等价关系 ≃; 程序 Prog(d,p) 由构造保证只碰声明过的键; 状态 ⟨next, F, B⟩;
;  fiber ⟨c, π, τ, θ⟩; 绑定 ⟨ι, q, s⟩; 视图 ω 是 K ⇀ N 的有限映射;
;  规则 O-Insert ... L-Remove; 派生概念 installed, visible, target, resolves, held, quiet, settled.
;文章的定理在这里变成可以运行的检查:
;  保持性 (不变式 WF), 恢复精确性 (影子存储), 进展 (quiet ⇒ settled),
;  合流 (规范名下与静态组装一致), 附录A (程序的解释与单独加载一致), 附录B (测试与不可交换).
;与 cordis0.rkt (逐条照搬 Calculus.v) 相比: 没有幽灵记录 oplog/inilog; 视图是 hash 而非列表;
;程序的键限制在构造时检查; 多了上面这些元理论的检查.
;记号: ⊥ / None 用 #f 表示.
(provide (all-defined-out))

;;; ======== 1 服务 ========

;run : Op -> Tok -> S -> (list S (S -> S) Out) 或 #f
;eq 即 ≃
(struct service (eq run))
(define (run Σ a t s) ((service-run Σ) a t s))
(define (≃ Σ s1 s2) ((service-eq Σ) s1 s2))
(define (id x) x)

;操作 a 在令牌 t 下, 在给定的状态 s 上带见证: 成功时 g s' ≃ s
(define (witnessed-at? Σ a t s)
  (match (run Σ a t s)
    [(list s* g _) (≃ Σ (g s*) s)]
    [#f #t]))

;例1 注册表: 名字 -> 值, 逐点比较
(struct Register (x v) #:transparent)
(struct Lookup (x) #:transparent)
(define Registry
  (service
   equal?
   (λ (a t s)
     (match a
       [(Register x v)
        (and (not (hash-has-key? s x))
             (list (hash-set s x v) (λ (s*) (hash-remove s* x)) #f))]
       [(Lookup x) (list s id (hash-ref s x #f))]))))

;例2 有序事件总线: (令牌 . 回调) 的列表, 用相等比较 (分发看得到顺序)
(struct On (c) #:transparent)
(struct Emit () #:transparent)
(struct OnByCallback (c) #:transparent)   ;Cordis 的旧做法: 逆按回调删
(define ((remove-tok t) s) (filter (λ (h) (not (= (car h) t))) s))
(define ((remove-first c) s)
  (match s
    ['() '()]
    [(cons h s*) (if (equal? (cdr h) c) s* (cons h ((remove-first c) s*)))]))
;表中已有令牌为 t 的钩子时注册失败
(define (has-tok? t s) (assv t s))
(define EventBus
  (service
   equal?
   (λ (a t s)
     (match a
       [(On c)
        (and (not (has-tok? t s))
             (list (append s (list (cons t c))) (remove-tok t) '()))]
       [(OnByCallback c)
        (and (not (has-tok? t s))
             (list (append s (list (cons t c))) (remove-first c) '()))]
       [(Emit) (list s id (map cdr s))]))))

;例2末尾 监听器注册: 回调的列表, 按多重集比较; 逆删去第一个 c, 不需要令牌
(struct Listen (c) #:transparent)
(define (multiset=? l1 l2)
  (equal? (sort (map ~s l1) string<?) (sort (map ~s l2) string<?)))
(define (remove-first-elem c s)
  (match s ['() '()] [(cons x s*) (if (equal? x c) s* (cons x (remove-first-elem c s*)))]))
(define Listeners
  (service
   multiset=?
   (λ (a t s)
     (match a
       [(Listen c) (list (append s (list c)) (λ (s*) (remove-first-elem c s*)) '())]))))

;例 (汇总一节) 变量存储: "把 x 设为 v" 的逆是改回原来的值, 依赖于起点
(struct SetVar (x v) #:transparent)
(define Vars
  (service
   equal?
   (λ (a t s)
     (match a
       [(SetVar x v)
        (define old (hash-ref s x #f))
        (list (hash-set s x v)
              (λ (s*) (if old (hash-set s* x old) (hash-remove s* x)))
              #f)]))))

;两个服务之和: 一方的操作在另一方的状态上失败
(struct inl (v) #:transparent)
(struct inr (v) #:transparent)
(define (Sum Σ1 Σ2)
  (service
   (λ (x y)
     (match* (x y)
       [((inl a) (inl b)) (≃ Σ1 a b)]
       [((inr a) (inr b)) (≃ Σ2 a b)]
       [(_ _) #f]))
   (λ (a t x)
     (match* (a x)
       [((inl a) (inl s))
        (match (run Σ1 a t s)
          [(list s* g o) (list (inl s*) (match-lambda [(inl v) (inl (g v))] [y y]) o)]
          [#f #f])]
       [((inr a) (inr s))
        (match (run Σ2 a t s)
          [(list s* g o) (list (inr s*) (match-lambda [(inr v) (inr (g v))] [y y]) o)]
          [#f #f])]
       [(_ _) #f]))))

;;; ======== 2 程序 ========

;P ::= Done | Fail | Call k a κ | Provide k s P | Spawn c P
(struct Done () #:transparent)
(struct Fail () #:transparent)
(struct Call (k a κ) #:transparent)
(struct Provide (k s P) #:transparent)
(struct Spawn (c P) #:transparent)

;Prog(d,p): Call k 要求 k ∈ d ∪ p, Provide k 要求 k ∈ p; 延续也在 Prog(d,p) 中.
;文章中这由类型保证; 这里在构造组件时把程序包起来, 每展开一段就检查一段.
;违反时是类型错误 (抛异常), 不是程序的 Fail.
(define (Prog d p P)
  (define (bad what k)
    (error 'Prog "~a ~a 不在允许的键中 (d = ~a, p = ~a)" what k d p))
  (match P
    [(or (Done) (Fail)) P]
    [(Call k a κ)
     (unless (or (member k d) (member k p)) (bad "Call" k))
     (Call k a (λ (o) (Prog d p (κ o))))]
    [(Provide k s P*)
     (unless (member k p) (bad "Provide" k))
     (Provide k s (Prog d p P*))]
    [(Spawn c P*) (Spawn c (Prog d p P*))]))

(define-syntax program
  (syntax-rules (serve spawn <-)
    [(_ last) last]
    [(_ (serve k s) rest ...) (Provide k s (program rest ...))]
    [(_ (spawn c) rest ...) (Spawn c (program rest ...))]
    [(_ (x <- k a) rest ...) (Call k a (λ (x) (program rest ...)))]
    [(_ (k a) rest ...) (Call k a (λ (_) (program rest ...)))]))

;;; ======== 3 组件, fiber 与状态 ========

;组件 ⟨d, p, body, reacts⟩, body ∈ Prog(d,p)
(struct component (d p body reacts))
(define (make-component d p body [reacts '()])
  (component d p (Prog d p body) reacts))

;fiber ⟨c, π, τ, θ⟩: 组件, 父fiber (根fiber为 'root), 已请求移除, 生命周期状态
(struct fiber (c π τ θ) #:transparent)
;绑定 ⟨ι, q, s⟩: 提供编号, 提供者的名字, 服务状态
(struct binding (ι q s) #:transparent)
;状态 ⟨next, F, B⟩; F : N ⇀ Fiber, B : K ⇀ Binding
(struct state (next F B) #:transparent)
(define init (state 0 (hash) (hash)))

;θ ::= Inactive ζ | Loading P acc ω | Active acc ω | Unloading acc ω ζ
;ζ 为 #f (⊥) 或错误 ξ: 'EUser 'EOp 'EUnresolved 'EConflict
(struct Inactive (ζ) #:transparent)
(struct Loading (P acc ω) #:transparent)
(struct Active (acc ω) #:transparent)
(struct Unloading (acc ω ζ) #:transparent)

;u ::= UOp k ι t g | UProv k ι | USpawn m
(struct UOp (k ι t g) #:transparent)
(struct UProv (k ι) #:transparent)
(struct USpawn (m) #:transparent)

(define (F γ n) (hash-ref (state-F γ) n #f))
(define (B γ k) (hash-ref (state-B γ) k #f))
(define (names γ) (range (state-next γ)))
(define (acc-of θ)
  (match θ [(or (Loading _ acc _) (Active acc _) (Unloading acc _ _)) acc] [(Inactive _) '()]))
(define (ω-of θ)
  (match θ [(or (Loading _ _ ω) (Active _ ω) (Unloading _ ω _)) ω] [(Inactive _) #f]))

;;; ======== 4 派生概念 ========

(define (installed? γ n)
  (match (F γ n) [(fiber _ _ _ θ) (not (Inactive? θ))] [#f #f]))

;visible(k) = ι, 若 B(k) = ⟨ι, o, _⟩ 且 θ_o = Active; 否则 ⊥
(define (visible γ k)
  (match (B γ k)
    [(binding ι o _) (match (F γ o) [(fiber _ _ _ (Active _ _)) ι] [_ #f])]
    [#f #f]))

;target(n) = ⊥, 若 τ_n 或某个依赖不可见; 否则 k ∈ d(c_n) ↦ visible(k)
(define (target prog γ n)
  (match (F γ n)
    [(fiber c _ τ _)
     (and (not τ)
          (let ([ks (component-d (prog c))])
            (and (andmap (λ (k) (visible γ k)) ks)
                 (for/hash ([k ks]) (values k (visible γ k))))))]
    [#f #f]))

;resolves(m, ι) ⟺ installed(m) ∧ ∃k. ω_m(k) = ι
(define (resolves? γ m ι)
  (and (installed? γ m)
       (for/or ([(k ι*) (ω-of (fiber-θ (F γ m)))]) (= ι* ι))))

;held(n, acc) ⟺ ∃ UProv k ι ∈ acc. ∃m ≠ n. resolves(m, ι)
;卸载的守卫: n 尚未撤回的某个提供仍被别的已安装 fiber 解析
(define (held? γ n acc)
  (for/or ([u acc])
    (match u
      [(UProv _ ι) (for/or ([m (names γ)]) (and (not (= m n)) (resolves? γ m ι)))]
      [_ #f])))

;p(c) 与某个现存 fiber 的 p 相交
(define (conflict? prog γ c)
  (for/or ([(n f) (state-F γ)])
    (for/or ([k (component-p (prog c))])
      (member k (component-p (prog (fiber-c f)))))))

;;; ======== 5 规则 ========

;标签
(struct O-Insert (c) #:transparent)
(struct O-Dispose (n) #:transparent)
(struct O-Reset (n) #:transparent)
(struct O-Restart (n) #:transparent)
(struct O-React (n i) #:transparent)
(struct L-Begin (n) #:transparent)
(struct L-Step (n) #:transparent)
(struct L-Divert (n) #:transparent)
(struct L-Leave (n) #:transparent)
(struct L-Undo (n) #:transparent)
(struct L-RetireChild (n) #:transparent)
(struct L-Unloaded (n) #:transparent)
(struct L-Remove (n) #:transparent)

;L(n): n 上的八种生命周期标签
(define (L n)
  (list (L-Begin n) (L-Step n) (L-Divert n) (L-Leave n)
        (L-Undo n) (L-RetireChild n) (L-Unloaded n) (L-Remove n)))

;状态更新 (文章中的 ←)
(define (F← γ n f)
  (struct-copy state γ [F (if f (hash-set (state-F γ) n f) (hash-remove (state-F γ) n))]))
(define (B← γ k b)
  (struct-copy state γ [B (if b (hash-set (state-B γ) k b) (hash-remove (state-B γ) k))]))
(define (θ← γ n θ)
  (match-define (fiber c π τ _) (F γ n))
  (F← γ n (fiber c π τ θ)))
(define (τ← γ n)
  (match-define (fiber c π _ θ) (F γ n))
  (F← γ n (fiber c π #t θ)))
;取 next 的当前值之后把 next 加一
(define (next+1 γ) (struct-copy state γ [next (add1 (state-next γ))]))
;以 m := next 为名插入 f
(define (insert γ f) (next+1 (F← γ (state-next γ) f)))

;step : State -> Label -> Maybe State
(define (step Σ prog γ ℓ)
  (define (θ n) (fiber-θ (F γ n)))
  (define (c n) (fiber-c (F γ n)))
  (define (exists? n) (and (F γ n) #t))
  (match ℓ
    ;;; 编排规则
    ;p(c) 不冲突: 以 m := next 为名插入 ⟨c, root, false, Inactive ⊥⟩
    [(O-Insert c)
     (and (not (conflict? prog γ c))
          (insert γ (fiber c 'root #f (Inactive #f))))]
    ;n ∈ dom F: τ_n ← true
    [(O-Dispose n)
     (and (exists? n) (τ← γ n))]
    ;θ_n = Inactive ξ: θ_n ← Inactive ⊥
    [(O-Reset n)
     (and (exists? n)
          (match (θ n) [(Inactive (? symbol?)) (θ← γ n (Inactive #f))] [_ #f]))]
    ;θ_n 为 Loading _ acc ω 或 Active acc ω, 且 ¬τ_n: θ_n ← Unloading acc ω ⊥
    [(O-Restart n)
     (and (exists? n) (not (fiber-τ (F γ n)))
          (match (θ n)
            [(or (Loading _ acc ω) (Active acc ω)) (θ← γ n (Unloading acc ω #f))]
            [_ #f]))]
    ;θ_n = Active acc ω, ¬τ_n, reacts(c_n) 的第 i 项为 c', p(c') 不冲突:
    ;插入子fiber ⟨c', n, false, Inactive ⊥⟩, 名为 m := next, θ_n ← Active (USpawn m :: acc) ω
    [(O-React n i)
     (and (exists? n) (not (fiber-τ (F γ n)))
          (match (θ n)
            [(Active acc ω)
             (define reacts (component-reacts (prog (c n))))
             (and (< i (length reacts))
                  (let ([c* (list-ref reacts i)] [m (state-next γ)])
                    (and (not (conflict? prog γ c*))
                         (θ← (insert γ (fiber c* n #f (Inactive #f)))
                             n (Active (cons (USpawn m) acc) ω)))))]
            [_ #f]))]
    ;;; 加载
    ;θ_n = Inactive ⊥ 且 target(n) = ω ≠ ⊥: θ_n ← Loading (body c_n) [] ω
    [(L-Begin n)
     (and (exists? n)
          (match (θ n)
            [(Inactive #f)
             (define ω (target prog γ n))
             (and ω (θ← γ n (Loading (component-body (prog (c n))) '() ω)))]
            [_ #f]))]
    ;θ_n = Loading P acc ω 且 target(n) ≠ ω: θ_n ← Unloading acc ω ⊥
    [(L-Divert n)
     (and (exists? n)
          (match (θ n)
            [(Loading _ acc ω)
             (and (not (equal? (target prog γ n) ω)) (θ← γ n (Unloading acc ω #f)))]
            [_ #f]))]
    ;θ_n = Loading P acc ω 且 target(n) = ω: 按 P 分情况
    [(L-Step n)
     (and (exists? n)
          (match (θ n)
            [(Loading P acc ω)
             (and (equal? (target prog γ n) ω) (load-step Σ prog γ n P acc ω))]
            [_ #f]))]
    ;;; 卸载
    ;θ_n = Active acc ω 且 target(n) ≠ ω: θ_n ← Unloading acc ω ⊥
    [(L-Leave n)
     (and (exists? n)
          (match (θ n)
            [(Active acc ω)
             (and (not (equal? (target prog γ n) ω)) (θ← γ n (Unloading acc ω #f)))]
            [_ #f]))]
    ;θ_n = Unloading (u :: acc) ω ζ, ¬held(n, u :: acc), 且按 u 分的前提成立:
    ;θ_n ← Unloading acc ω ζ, 并且 ...
    [(L-Undo n)
     (and (exists? n)
          (match (θ n)
            [(Unloading (cons u acc) ω ζ)
             (define (continue γ*) (θ← γ* n (Unloading acc ω ζ)))
             (and
              (not (held? γ n (cons u acc)))
              (match u
               ;若绑定 ι 仍在, 把它的状态 s 改为 g(s)
               [(UOp k ι _ g)
                (match (B γ k)
                  [(binding (== ι) o s) (continue (B← γ k (binding ι o (g s))))]
                  [_ (continue γ)])]
               ;删除 B(k); 由守卫, 没有 m ≠ n 满足 resolves(m, ι)
               [(UProv k ι) (continue (B← γ k #f))]
               ;要求 m ∉ dom F, 即子fiber已被移除
               [(USpawn m) (and (not (exists? m)) (continue γ))]))]
            [_ #f]))]
    ;θ_n = Unloading (USpawn m :: acc) _ _, ¬held(n, USpawn m :: acc), m ∈ dom F 且 ¬τ_m: τ_m ← true
    [(L-RetireChild n)
     (and (exists? n)
          (match (θ n)
            [(Unloading (cons (USpawn m) acc) _ _)
             (and (not (held? γ n (cons (USpawn m) acc)))
                  (exists? m) (not (fiber-τ (F γ m))) (τ← γ m))]
            [_ #f]))]
    ;θ_n = Unloading [] ω ζ: θ_n ← Inactive ζ
    [(L-Unloaded n)
     (and (exists? n)
          (match (θ n) [(Unloading '() _ ζ) (θ← γ n (Inactive ζ))] [_ #f]))]
    ;τ_n, θ_n = Inactive _, 且没有 m 满足 π_m = n: 删除 F(n)
    [(L-Remove n)
     (and (exists? n) (fiber-τ (F γ n)) (Inactive? (θ n))
          (not (for/or ([(m f) (state-F γ)]) (equal? (fiber-π f) n)))
          (F← γ n #f))]))

;L-Step 的各情况
(define (load-step Σ prog γ n P acc ω)
  (define c (fiber-c (F γ n)))
  (define (fail ξ [γ γ]) (θ← γ n (Unloading acc ω ξ)))
  (match P
    [(Done) (θ← γ n (Active acc ω))]
    [(Fail) (fail 'EUser)]
    ;k ∈ d(c_n) 时查视图 ω, 否则查当前绑定 B (提供者必须是 n), 得到编号 ι;
    ;取令牌 t := next, 在该绑定的状态 s 上运行 run a t s
    [(Call k a κ)
     (define ι
       (if (member k (component-d (prog c)))
           (hash-ref ω k #f)
           (match (B γ k) [(binding ι (== n) _) ι] [_ #f])))
     (match (and ι (B γ k))
       [(binding (== ι) o s)
        (define t (state-next γ))
        (match (run Σ a t s)
          [(list s* g out)
           (θ← (next+1 (B← γ k (binding ι o s*)))
               n (Loading (κ out) (cons (UOp k ι t g) acc) ω))]
          [#f (fail 'EOp (next+1 γ))])]
       [_ (fail 'EUnresolved)])]   ;解析失败视为失败
    ;要求 k ∈ p(c_n) 且 B(k) 未定义; 以 ι := next 为编号令 B(k) ← ⟨ι, n, s⟩
    [(Provide k s P*)
     (if (and (member k (component-p (prog c))) (not (B γ k)))
         (let ([ι (state-next γ)])
           (θ← (next+1 (B← γ k (binding ι n s)))
               n (Loading P* (cons (UProv k ι) acc) ω)))
         (fail 'EConflict))]
    ;要求 p(c') 不冲突; 插入子fiber ⟨c', n, false, Inactive ⊥⟩, 名为 m := next
    [(Spawn c* P*)
     (if (conflict? prog γ c*)
         (fail 'EConflict)
         (let ([m (state-next γ)])
           (θ← (insert γ (fiber c* n #f (Inactive #f)))
               n (Loading P* (cons (USpawn m) acc) ω))))]))

(define (run-labels Σ prog γ ℓs)
  (for/fold ([γ γ]) ([ℓ ℓs]) #:break (not γ) (step Σ prog γ ℓ)))

;quiet(γ) ⟺ ∀n. ∀ℓ ∈ L(n). step γ ℓ = None (n ∉ names γ 时显然成立)
(define (quiet? Σ prog γ)
  (for*/and ([n (names γ)] [ℓ (L n)]) (not (step Σ prog γ ℓ))))

;;; ======== 6 元理论: 可运行的检查 ========

;;; 6.1 保持性: 不变式 WF 的八条; 返回违反的条目 (空表即成立)
(define (wf-violations prog γ)
  (define next (state-next γ))
  (define (d n) (component-d (prog (fiber-c (F γ n)))))
  (define (p n) (component-p (prog (fiber-c (F γ n)))))
  (define (acc n) (acc-of (fiber-θ (F γ n))))
  (define ns (sort (hash-keys (state-F γ)) <))
  (define bad '())
  (define (check! ok? fmt . args)
    (unless ok? (set! bad (cons (apply format fmt args) bad))))
  ;1 dom F 中的名字, B 中的提供编号, 各累加器的 USpawn 中的名字都小于 next
  (for ([n ns])
    (check! (< n next) "1: 名字 ~a" n)
    (for ([u (acc n)] #:when (USpawn? u))
      (check! (< (USpawn-m u) next) "1: USpawn ~a" (USpawn-m u))))
  (for ([(k b) (state-B γ)]) (check! (< (binding-ι b) next) "1: 编号 ~a" (binding-ι b)))
  ;2 子fiber的父fiber存在, 已安装, 且累加器中有对应的 USpawn
  (for ([m ns])
    (match (fiber-π (F γ m))
      ['root (void)]
      [n (check! (and (installed? γ n) (member (USpawn m) (acc n)))
                 "2: 子fiber ~a 的父fiber ~a" m n)]))
  ;3 现存 fiber 的 p 两两不相交
  (for* ([n ns] [m ns] #:when (< n m))
    (check! (null? (set-intersect (p n) (p m))) "3: ~a 与 ~a 的 p 相交" n m))
  (for ([n ns] #:when (installed? γ n))
    (define ω (ω-of (fiber-θ (F γ n))))
    ;4 已解析的每个依赖都有绑定, 编号与视图一致, 提供者不是自己
    (for ([(k ι) ω])
      (check! (match (B γ k) [(binding (== ι) o _) (not (= o n))] [_ #f])
              "4: fiber ~a 的依赖 ~a" n k))
    ;5 已安装 fiber 的视图的键恰为 d
    (check! (set=? (hash-keys ω) (d n)) "5: fiber ~a 的视图" n))
  ;6 每个绑定的提供者 q 存在, 已安装, k ∈ p(c_q), 且 q 的累加器中有对应的 UProv
  (for ([(k b) (state-B γ)])
    (match-define (binding ι o _) b)
    (check! (and (installed? γ o) (member k (p o)) (member (UProv k ι) (acc o)))
            "6: 绑定 ~a" k))
  (for ([n ns])
    (define provs (filter UProv? (acc n)))
    ;7 累加器中的每个 UProv k ι 都对应一个现存绑定, 编号为 ι, 提供者为自己
    (for ([u provs])
      (match-define (UProv k ι) u)
      (check! (match (B γ k) [(binding (== ι) (== n) _) #t] [_ #f])
              "7: fiber ~a 的 UProv ~a" n k))
    ;8 一个累加器中每个键至多有一个 UProv
    (check! (= (length provs) (length (remove-duplicates (map UProv-k provs))))
            "8: fiber ~a" n))
  (reverse bad))

;来源不变式与编号与spawn不变式中能直接检查的部分; 返回违反的条目.
;来源不变式第1条 (剩余程序是 body 的后段) 与第2条的后半 (g 是某个 a 给出的逆),
;以及编号与spawn不变式第2条 (c_n 可能spawn c_m) 涉及程序的全部路径, 而延续是闭包, 不在此检查.
(define (inv-violations γ)
  (define next (state-next γ))
  (define bad '())
  (define (check! ok? fmt . args)
    (unless ok? (set! bad (cons (apply format fmt args) bad))))
  (define ops
    (for*/list ([(n f) (state-F γ)] [u (acc-of (fiber-θ f))] #:when (UOp? u)) (cons n u)))
  ;来源2 (前半): 每个 UOp k ι t g 有 ι, t < next
  (for ([nu ops])
    (match-define (cons n (UOp _ ι t _)) nu)
    (check! (and (< ι next) (< t next)) "来源2: fiber ~a 的 UOp ~a ~a" n ι t))
  ;来源3: 不同 fiber 的 UOp 项所用的令牌互不相同
  (for* ([x ops] [y ops] #:when (< (car x) (car y)))
    (check! (not (= (UOp-t (cdr x)) (UOp-t (cdr y))))
            "来源3: fiber ~a 与 ~a 共用令牌 ~a" (car x) (car y) (UOp-t (cdr x))))
  ;编号1: 不同绑定的提供编号不同
  (define ιs (map binding-ι (hash-values (state-B γ))))
  (check! (= (length ιs) (length (remove-duplicates ιs))) "编号1: ~a" ιs)
  (reverse bad))

;;; 6.2 恢复精确性: 存储, 待撤销操作, 影子存储

;store(γ): k ↦ 当前绑定的服务状态
(define (store γ)
  (for/hash ([(k b) (state-B γ)]) (values k (binding-s b))))
(define (store≃ Σ σ1 σ2)
  (and (set=? (hash-keys σ1) (hash-keys σ2))
       (for/and ([(k s) σ1]) (≃ Σ s (hash-ref σ2 k)))))

;n 有待撤销操作: 存在, 已安装, 累加器中有 UOp
(define (pending? γ n)
  (match (F γ n)
    [(fiber _ _ _ θ) (and (not (Inactive? θ)) (ormap UOp? (acc-of θ)))]
    [#f #f]))

;沿一步 γ --ℓ--> γ* 更新对 n 的影子存储 σ^
(define (shadow-step Σ n γ ℓ γ* σ^)
  (match ℓ
    [(L-Step m)
     (match* ((fiber-θ (F γ m)) (fiber-θ (F γ* m)))
       ;m 的 L-Step 在键 k 上以令牌 t 成功运行了 a: 若 m ≠ n, σ^(k) 有定义,
       ;且 a 在 σ^(k) 上成功, 则令 σ^(k) ← s'; 否则不变 (在定理的假设下不会出现).
       ;运行失败的 L-Step 转入 Unloading, 落到最后一支, σ^ 不变.
       [((Loading (Call k a _) _ _) (Loading _ (cons (UOp k _ t _) _) _))
        (match (and (not (= m n)) (hash-has-key? σ^ k) (run Σ a t (hash-ref σ^ k)))
          [(list s* _ _) (hash-set σ^ k s*)]
          [#f σ^])]
       ;Provide 步以初始状态 s 建立键 k 的绑定
       [((Loading (Provide k s _) _ _) (Loading _ (cons (UProv k _) _) _))
        (hash-set σ^ k s)]
       [(_ _) σ^])]
    [(L-Undo m)
     (match (fiber-θ (F γ m))
       ;撤销 UOp k ι t g 并作用于现存的绑定
       [(Unloading (cons (UOp k ι _ g) _) _ _)
        (if (and (not (= m n)) (match (B γ k) [(binding (== ι) _ _) #t] [_ #f])
                 (hash-has-key? σ^ k))
            (hash-set σ^ k (g (hash-ref σ^ k)))
            σ^)]
       ;撤销 UProv k ι 删除绑定
       [(Unloading (cons (UProv k _) _) _ _) (hash-remove σ^ k)]
       [_ σ^])]
    [_ σ^]))

;对一次执行 (γ0 ℓ1 γ1 ℓ2 γ2 ...) 中的每个名字 n: 在每个 n 没有待撤销操作的状态,
;store(γ) ≃ 影子存储. 返回不成立的 (n . 步数) 列表.
(define (recovery-failures Σ γs ℓs)
  (define γ0 (car γs))
  (for*/list ([n (names (last γs))]
              [bad (in-value
                    (let loop ([γ γ0] [γs (cdr γs)] [ℓs ℓs] [σ^ (store γ0)] [i 0])
                      (cond [(and (not (pending? γ n)) (not (store≃ Σ (store γ) σ^))) i]
                            [(null? ℓs) #f]
                            [else (loop (car γs) (cdr γs) (cdr ℓs)
                                        (shadow-step Σ n γ (car ℓs) (car γs) σ^)
                                        (add1 i))])))]
              #:when bad)
    (cons n bad)))

;;; 6.3 进展: settled(γ)
(define (settled? prog γ)
  (for/and ([(n f) (state-F γ)])
    (match f
      [(fiber _ _ #f (Inactive (? symbol?))) #t]                           ;失败并停下
      [(fiber _ _ #f (Inactive #f)) (not (target prog γ n))]               ;不该运行
      [(fiber _ _ _ (Active _ ω)) (equal? (target prog γ n) ω)]            ;该运行且视图正确
      [_ #f])))

;;; 6.4 合流: 规范名
;根fiber按插入次序 (即名字的次序) 编号; 子fiber由父fiber的规范名和它在父fiber的 spawn 中的位置命名
(define (canonical γ)
  (define roots (sort (for/list ([(n f) (state-F γ)] #:when (eq? (fiber-π f) 'root)) n) <))
  (define table (make-hash))
  (for ([n roots] [i (in-naturals)]) (hash-set! table n (list i)))
  (let loop ()
    (define changed #f)
    (for ([(n f) (state-F γ)] #:when (hash-ref table n #f))
      (define spawned
        (for/list ([u (reverse (acc-of (fiber-θ f)))] #:when (USpawn? u)) (USpawn-m u)))
      (for ([m spawned] [j (in-naturals)] #:when (and (F γ m) (not (hash-ref table m #f))))
        (hash-set! table m (append (hash-ref table n) (list j)))
        (set! changed #t)))
    (when changed (loop)))
  table)

;在规范名下的观察: fiber (规范名, 组件, 是否 Active), 绑定 (键, 提供者的规范名, 规范化的状态)
(define (observe γ normalize)
  (define cn (canonical γ))
  (list (sort (for/list ([(n f) (state-F γ)])
                (list (hash-ref cn n #f) (fiber-c f) (Active? (fiber-θ f))))
              string<? #:key ~s)
        (sort (for/list ([(k b) (state-B γ)])
                (list k (hash-ref cn (binding-q b) #f) (normalize (binding-s b))))
              string<? #:key ~s)))

(define (has-failed? γ)
  (for/or ([(n f) (state-F γ)])
    (match (fiber-θ f) [(Inactive (? symbol?)) #t] [_ #f])))

;;; ======== 调度 (不在演算之内) ========

(define (enabled Σ prog γ)
  (for*/list ([n (names γ)] [ℓ (L n)] #:when (step Σ prog γ ℓ)) ℓ))

;只走生命周期步直到静止; 返回 (values γ 标签序列)
(define (settle Σ prog γ #:choose [choose car] #:trace [trace void])
  (let loop ([γ γ] [log '()])
    (match (enabled Σ prog γ)
      ['() (values γ (reverse log))]
      [ℓs (define ℓ (choose ℓs))
          (trace ℓ)
          (loop (step Σ prog γ ℓ) (cons ℓ log))])))

(define (random-choose seed)
  (define rng (make-pseudo-random-generator))
  (parameterize ([current-pseudo-random-generator rng]) (random-seed seed))
  (λ (xs) (parameterize ([current-pseudo-random-generator rng])
            (list-ref xs (random (length xs))))))

;编排标签必须适用
(define (orchestrate Σ prog γ ℓ)
  (or (step Σ prog γ ℓ) (error 'orchestrate "标签 ~v 不适用" ℓ)))

;穿插执行: script 是 (γ -> 标签或 #f) 的列表, 按顺序施加; 其间随机走生命周期步.
;某一项暂不适用时先走生命周期步再试, 静止时仍不适用就跳过它.
;返回 (values 状态序列 标签序列), 最后一个状态静止.
(define (interleave Σ prog γ script choose)
  (let loop ([γ γ] [script script] [γs (list γ)] [ℓs '()])
    (define lifecycle (enabled Σ prog γ))
    (define orch
      (and (pair? script)
           (let ([ℓ ((car script) γ)]) (and ℓ (step Σ prog γ ℓ) ℓ))))
    (define (take ℓ rest)
      (define γ* (step Σ prog γ ℓ))
      (loop γ* rest (cons γ* γs) (cons ℓ ℓs)))
    (cond [(and orch (or (null? lifecycle) (zero? (choose '(0 1 2)))))
           (take orch (cdr script))]
          [(pair? lifecycle) (take (choose lifecycle) script)]
          [(pair? script) (loop γ (cdr script) γs ℓs)]
          [else (values (reverse γs) (reverse ℓs))])))

;;; ======== 附录A 单个组件的语义 ========

;PEff(Γ) = Γ -> Maybe (Γ × End Γ); 结果是 (list δ g) 或 #f
(define ((η) γ) (list γ id))
(define ((◇ e1 e2) γ)
  (match (e2 γ)
    [(list δ g) (match (e1 δ) [(list ε h) (list ε (compose g h))] [#f #f])]
    [#f #f]))
;a : Γ -> Maybe (Γ × End Γ × Out), κ : Out -> PEff Γ
(define ((bind a κ) γ)
  (match (a γ)
    [(list δ g o) (match ((κ o) δ) [(list ε h) (list ε (compose g h))] [#f #f])]
    [#f #f]))
;存储 Store = K ⇀ S, 用不可变 hash 表示
(define ((set-k k s) σ)
  (and (not (hash-has-key? σ k))
       (list (hash-set σ k s) (λ (σ*) (hash-remove σ* k)))))
(define ((lift Σ k a t) σ)
  (and (hash-has-key? σ k)
       (match (run Σ a t (hash-ref σ k))
         [(list s* g o)
          (list (hash-set σ k s*)
                (λ (σ*) (if (hash-has-key? σ* k) (hash-set σ* k (g (hash-ref σ* k))) σ*))
                o)]
         [#f #f])))
;⟦P⟧_t
(define (den Σ P t)
  (match P
    [(Done) (η)]
    [(Fail) (λ (σ) #f)]
    [(Call k a κ) (bind (lift Σ k a t) (λ (o) (den Σ (κ o) (add1 t))))]
    [(Provide k s P*) (◇ (den Σ P* (add1 t)) (set-k k s))]
    [(Spawn _ P*) (den Σ P* (add1 t))]))

;撤销项作用在存储上; 累加器按 LIFO 复合 (表头最先施加)
(define (undo->store u)
  (match u
    [(UOp k _ _ g) (λ (σ) (if (hash-has-key? σ k) (hash-set σ k (g (hash-ref σ k))) σ))]
    [(UProv k _) (λ (σ) (hash-remove σ k))]
    [(USpawn _) id]))
(define ((acc->store acc) σ)
  (for/fold ([σ σ]) ([u acc]) ((undo->store u) σ)))

;;; ======== 附录B 观察等价 ========

;测试是字母的列表: (LF a t) 运行操作并记录结果, (LI g) 施加一个逆
(struct LF (a t) #:transparent)
(struct LI (g) #:transparent)
(define (runTest Σ w s)
  (let loop ([w w] [s s] [outs '()])
    (match w
      ['() (reverse outs)]
      [(cons (LF a t) w*) (match (run Σ a t s)
                            [(list s* _ o) (loop w* s* (cons o outs))]
                            [#f #f])]
      [(cons (LI g) w*) (loop w* (g s) outs)])))

;;; ======== 示例 ========

;Σ = Registry ⊕ EventBus, 用于演示, 保持性与恢复精确性
(define Σ (Sum Registry EventBus))
(define (reg x v) (inl (Register x v)))
(define (on c) (inr (On c)))

(define components
  (hash
   'core (make-component '() '(tools) (program (serve 'tools (inl (hash))) (Done)))
   ;提供 tools 之后自己再登记一个条目, 用来检查守卫作用于整个卸载
   'core+ (make-component '() '(tools)
                          (program (serve 'tools (inl (hash)))
                                   ('tools (reg "builtin" "内建"))
                                   (Done)))
   'shell (make-component '(tools) '()
                          (program ('tools (reg "ls" "列出文件"))
                                   ('tools (reg "cat" "打印文件"))
                                   (Done)))
   'git (make-component '(tools) '() (program ('tools (reg "git" "版本控制")) (Done)))
   ;先登记 grep, 再登记已被占用的 ls -> EOp; grep 会被撤掉
   'bad (make-component '(tools) '()
                        (program ('tools (reg "grep" "搜索"))
                                 ('tools (reg "ls" "冒牌 ls"))
                                 (Done)))
   'grep-tool (make-component '(tools) '() (program ('tools (reg "grep" "搜索")) (Done)))
   'sed-tool (make-component '(tools) '() (program ('tools (reg "sed" "流编辑")) (Done)))
   'toolkit (make-component '(tools) '()
                            (program (spawn 'grep-tool)
                                     ('tools (reg "help" "工具箱帮助"))
                                     (spawn 'sed-tool)
                                     (Done)))
   ;提供自己的键并在上面操作: Call 的键不在 d 中, 查当前绑定, 提供者必须是自己
   'local (make-component '() '(local)
                          (program (serve 'local (inl (hash)))
                                   ('local (reg "x" 1))
                                   (Done)))
   'bus (make-component '() '(events) (program (serve 'events (inr '())) (Done)))
   'ping (make-component '(events) '() (program ('events (on "ping")) (Done)))
   'watcher (make-component '(events) '() (program ('events (on "watcher")) (Done)) '(ping))))
(define (prog c) (hash-ref components c))

(define (tools-of γ)
  (match (B γ 'tools) [(binding _ _ (inl s)) (sort (hash-keys s) string<?)] [#f #f]))
(define (handlers-of γ)
  (match (B γ 'events) [(binding _ _ (inr s)) (sort (map cdr s) string<?)] [#f #f]))
;组件为 c 的第一个 fiber
(define (fiber-of γ c)
  (for/first ([n (names γ)] #:when (match (F γ n) [(fiber (== c) _ _ _) #t] [_ #f])) n))

(define (θ-tag θ)
  (match θ
    [(Inactive ζ) (if ζ (format "Inactive(~a)" ζ) "Inactive")]
    [(Loading _ _ _) "Loading"]
    [(Active _ _) "Active"]
    [(Unloading _ _ ζ) (if ζ (format "Unloading(~a)" ζ) "Unloading")]))

(define (show γ)
  (printf "  -- F:")
  (for ([n (names γ)] #:when (F γ n))
    (match-define (fiber c π τ θ) (F γ n))
    (printf " ~a#~a~a~a=~a" c n (if (eq? π 'root) "" (format "(π=~a)" π)) (if τ "(τ)" "")
            (θ-tag θ)))
  (newline)
  (printf "  -- B:")
  (when (zero? (hash-count (state-B γ))) (printf " (无)"))
  (for ([(k b) (state-B γ)])
    (printf " ~a=⟨~a, ~a, ~a⟩" k (binding-ι b) (binding-q b)
            (match (binding-s b) [(inl s) (sort (hash-keys s) string<?)] [(inr s) s])))
  (newline))

(module+ main
  (define γ init)
  (define (scene title . ℓs)
    (printf "\n== ~a\n" title)
    (for ([ℓ ℓs])
      (printf "  ~v\n" (ℓ γ))
      (set! γ (orchestrate Σ prog γ (ℓ γ))))
    (define-values (γ* _) (settle Σ prog γ #:trace (λ (ℓ) (printf "    ~v\n" ℓ))))
    (set! γ γ*)
    (show γ)
    (unless (null? (wf-violations prog γ))
      (printf "  !! 不变式不成立: ~a\n" (wf-violations prog γ))))
  (define (insert c) (λ (γ) (O-Insert c)))
  (define ((by c make) γ) (make (fiber-of γ c)))
  (scene "先装依赖者 shell, git, 再装提供者 core"
         (insert 'shell) (insert 'git) (insert 'core))
  (scene "装 toolkit: 它在加载中 spawn 两个子fiber" (insert 'toolkit))
  (scene "移除 toolkit: L-RetireChild 请 sed-tool 退出, 等它被 L-Remove 后再撤 help, 再到 grep-tool"
         (by 'toolkit O-Dispose))
  (scene "重启 core: 依赖者先 L-Leave, core 在它们卸载完之前什么都不撤 (守卫 held), 再以新编号提供"
         (by 'core O-Restart))
  (scene "装 bad: 第二次 Register 失败, 停在 Inactive(EOp)" (insert 'bad))
  (scene "装 local: 在自己提供的键上操作" (insert 'local))
  (scene "装 bus 和 watcher" (insert 'bus) (insert 'watcher))
  (scene "watcher 反应两次" (by 'watcher (λ (n) (O-React n 0))) (by 'watcher (λ (n) (O-React n 0))))
  (scene "单独撤销第一次反应: O-Dispose 子fiber" (by 'ping O-Dispose))
  (scene "移除 watcher: 剩下的反应先退出" (by 'watcher O-Dispose)))

(module+ test
  (require rackunit)

  (define (orch γ . ℓs) (for/fold ([γ γ]) ([ℓ ℓs]) (orchestrate Σ prog γ ℓ)))
  (define (go γ)
    (define-values (γ* _) (settle Σ prog γ))
    (check-true (quiet? Σ prog γ*))
    (check-true (settled? prog γ*))          ;进展: quiet ⇒ settled
    (check-equal? (wf-violations prog γ*) '())
    γ*)

  ;;; 服务
  ;每个操作带见证
  (for ([a (list (Register "x" 1) (Lookup "x"))] [s (list (hash) (hash "x" 0))])
    (check-true (witnessed-at? Registry a 0 s)))
  (for ([a (list (On "c") (Emit))])
    (check-true (witnessed-at? EventBus a 7 '((3 . "c")))))
  (check-true (witnessed-at? Listeners (Listen "c") 0 '("c" "d")))
  (check-true (witnessed-at? Vars (SetVar 'x 5) 0 (hash 'x 1)))
  ;按回调注销不是精确的逆: 撤销第二次注册删掉的是第一次的钩子
  (check-false (witnessed-at? EventBus (OnByCallback "c") 7 '((3 . "c"))))
  ;变量存储的逆依赖于起点 (违反合流假设第2条)
  (match-let ([(list _ g1 _) (run Vars (SetVar 'x 5) 0 (hash 'x 1))]
              [(list _ g2 _) (run Vars (SetVar 'x 5) 0 (hash 'x 2))])
    (check-not-equal? (g1 (hash 'x 5)) (g2 (hash 'x 5))))
  ;有序事件总线: 表中已有同一令牌的钩子时注册失败
  (check-false (run EventBus (On "d") 3 '((3 . "c"))))
  ;和: 一方的操作在另一方的状态上失败
  (check-false (run Σ (reg "x" 1) 0 (inr '())))
  ;例 (汇总一节): 撤销独立第1条在状态 x 上的一个反例 ——
  ;b 在 x 与 g x 上不同时成功, 或结果不同, 或后继不满足 x2 ≃ g x1
  (define (ri1-fails-at? Σ g b tb x)
    (match* ((run Σ b tb x) (run Σ b tb (g x)))
      [(#f #f) #f]
      [((list x1 _ o1) (list x2 _ o2)) (not (and (equal? o1 o2) (≃ Σ x2 (g x1))))]
      [(_ _) #t]))
  ;注册表: 同名的两次登记不撤销独立 (后一次实际失败, 撤销前一次之后却成功)
  (match-let ([(list s1 g _) (run Registry (Register "x" 1) 0 (hash))])
    (check-true (ri1-fails-at? Registry g (Register "x" 2) 1 s1)))
  ;监听器注册: f 不在 x 中时, 两次注册 f 不撤销独立 (要求 x 加上 f 之后 ≃ x)
  (match-let ([(list _ g _) (run Listeners (Listen "f") 0 '("c"))])
    (check-true (ri1-fails-at? Listeners g (Listen "f") 1 '("c"))))
  ;回调不同的两次注册撤销独立 (在这个状态上)
  (match-let ([(list s1 g _) (run Listeners (Listen "f") 0 '("c"))])
    (check-false (ri1-fails-at? Listeners g (Listen "h") 1 s1)))

  ;;; 程序: Prog(d,p) 的限制由构造保证
  (check-exn #rx"Provide" (λ () (make-component '(tools) '() (program (serve 'tools (inl (hash))) (Done)))))
  (check-exn #rx"Call" (λ () (make-component '() '() (program ('tools (reg "x" 1)) (Done)))))
  ;延续中的违反在展开到那一段时才发现
  (let ([c (make-component '(tools) '() (program ('tools (reg "x" 1)) (serve 'tools #f) (Done)))])
    (match (component-body c)
      [(Call _ _ κ) (check-exn #rx"Provide" (λ () (κ #f)))]))

  ;;; 规则
  ;依赖者在提供者 Active 之前不能 L-Begin
  (let ([γ (orch init (O-Insert 'shell) (O-Insert 'core))])
    (check-false (step Σ prog γ (L-Begin 0)))
    (define γ* (run-labels Σ prog γ (list (L-Begin 1) (L-Step 1) (L-Step 1)
                                          (L-Begin 0) (L-Step 0) (L-Step 0) (L-Step 0))))
    (check-true (quiet? Σ prog γ*))
    (check-equal? (tools-of γ*) '("cat" "ls")))
  ;守卫作用于整个卸载: core+ 在提供之后登记了 builtin; 重启时只要 shell 还解析着 tools,
  ;core+ 连 builtin 也不撤, shell 卸载时看到的是 core+ 的全部效应
  (let* ([γ (go (orch init (O-Insert 'core+) (O-Insert 'shell)))]
         [γ (orch γ (O-Restart 0))])
    (check-false (step Σ prog γ (L-Undo 0)))
    (define γ1 (run-labels Σ prog γ (list (L-Leave 1) (L-Undo 1) (L-Undo 1))))
    (check-equal? (tools-of γ1) '("builtin"))
    (check-false (step Σ prog γ1 (L-Undo 0)))          ;shell 还没卸载完
    (define γ2 (run-labels Σ prog γ1 (list (L-Unloaded 1))))
    (check-true (and (step Σ prog γ2 (L-Undo 0)) #t))
    (check-equal? (tools-of (go γ2)) '("builtin" "cat" "ls")))
  ;O-Insert 要求不冲突
  (check-false (step Σ prog (orch init (O-Insert 'core)) (O-Insert 'core)))

  (define γ1 (go (orch init (O-Insert 'shell) (O-Insert 'git) (O-Insert 'core))))
  (check-equal? (tools-of γ1) '("cat" "git" "ls"))
  (define γ2 (go (orch γ1 (O-Insert 'toolkit))))
  (check-equal? (tools-of γ2) '("cat" "git" "grep" "help" "ls" "sed"))
  (define γ3 (go (orch γ2 (O-Dispose (fiber-of γ2 'toolkit)))))
  (check-equal? (tools-of γ3) '("cat" "git" "ls"))
  (check-equal? (hash-count (state-F γ3)) 3)
  ;O-Restart: 结果不变, 提供编号改变
  (define γ4 (go (orch γ3 (O-Restart (fiber-of γ3 'core)))))
  (check-equal? (tools-of γ4) '("cat" "git" "ls"))
  (check-not-equal? (binding-ι (B γ4 'tools)) (binding-ι (B γ3 'tools)))
  ;失败的 fiber 停在 Inactive ξ, O-Reset 后重试, 再次失败
  (define γ5 (go (orch γ4 (O-Insert 'bad))))
  (define bad (fiber-of γ5 'bad))
  (check-equal? (fiber-θ (F γ5 bad)) (Inactive 'EOp))
  (check-false (step Σ prog γ5 (O-Reset (fiber-of γ5 'shell))))
  (define γ6 (go (orch γ5 (O-Reset bad))))
  (check-equal? (fiber-θ (F γ6 bad)) (Inactive 'EOp))
  (check-equal? (tools-of γ6) '("cat" "git" "ls"))
  ;在自己提供的键上操作
  (define γ7 (go (orch γ6 (O-Insert 'local))))
  (check-equal? (binding-s (B γ7 'local)) (inl (hash "x" 1)))
  ;O-React: 同一个回调登记两次, 令牌让撤销只删自己那一项
  (define γ8 (go (orch γ7 (O-Insert 'bus) (O-Insert 'watcher))))
  (define w (fiber-of γ8 'watcher))
  (check-false (step Σ prog γ8 (O-React w 1)))
  (define γ9 (go (orch γ8 (O-React w 0) (O-React w 0))))
  (check-equal? (handlers-of γ9) '("ping" "ping" "watcher"))
  (define γ10 (go (orch γ9 (O-Dispose (fiber-of γ9 'ping)))))
  (check-equal? (handlers-of γ10) '("ping" "watcher"))
  (define γ11 (go (orch γ10 (O-Dispose w))))
  (check-equal? (handlers-of γ11) '())
  (check-false (fiber-of γ11 'ping))

  ;;; 保持性与恢复精确性: 随机穿插的执行
  ;不含 bad, 以满足假设(H): 可能相遇的登记名字都不同
  (define recovery-script
    (list (λ (γ) (O-Insert 'core)) (λ (γ) (O-Insert 'bus)) (λ (γ) (O-Insert 'watcher))
          (λ (γ) (O-Insert 'shell)) (λ (γ) (O-Insert 'toolkit)) (λ (γ) (O-Insert 'local))
          (λ (γ) (O-React (fiber-of γ 'watcher) 0))
          (λ (γ) (O-React (fiber-of γ 'watcher) 0))
          (λ (γ) (O-Insert 'git))
          (λ (γ) (O-Dispose (fiber-of γ 'ping)))
          (λ (γ) (O-Restart (fiber-of γ 'core)))
          (λ (γ) (O-Dispose (fiber-of γ 'toolkit)))
          (λ (γ) (O-React (fiber-of γ 'watcher) 0))
          (λ (γ) (O-Restart (fiber-of γ 'watcher)))
          (λ (γ) (O-Dispose (fiber-of γ 'shell)))
          (λ (γ) (O-Dispose (fiber-of γ 'watcher)))))
  (for ([seed (in-range 60)])
    (define-values (γs ℓs) (interleave Σ prog init recovery-script (random-choose seed)))
    (define final (last γs))
    ;保持性: 每个可达状态满足不变式
    (check-false (for/first ([γ γs] #:unless (null? (wf-violations prog γ)))
                   (wf-violations prog γ))
                 (format "种子 ~a" seed))
    ;来源不变式与编号与spawn不变式 (可检查的部分)
    (check-false (for/first ([γ γs] #:unless (null? (inv-violations γ))) (inv-violations γ))
                 (format "种子 ~a" seed))
    ;进展
    (check-true (and (quiet? Σ prog final) (settled? prog final)) (format "种子 ~a" seed))
    ;恢复精确性: 对每个名字 n, 在 n 没有待撤销操作的每个状态, store ≃ 影子存储
    (check-equal? (recovery-failures Σ γs ℓs) '() (format "种子 ~a" seed))
    (check-equal? (handlers-of final) '() (format "种子 ~a" seed)))

  ;;; 合流: 根编排, 规范名下一致, 并与静态组装一致
  ;服务取 Registry ⊕ Listeners (满足合流假设; 有序事件总线的令牌会进入状态, 不满足)
  (define ΣC (Sum Registry Listeners))
  (define conf-components
    (hash
     'core (hash-ref components 'core) 'shell (hash-ref components 'shell)
     'git (hash-ref components 'git) 'toolkit (hash-ref components 'toolkit)
     'grep-tool (hash-ref components 'grep-tool) 'sed-tool (hash-ref components 'sed-tool)
     'hub (make-component '() '(listeners) (program (serve 'listeners (inr '())) (Done)))
     'lis (make-component '(listeners) '() (program ('listeners (inr (Listen "a"))) (Done)))
     'lis2 (make-component '(listeners tools) '()
                           (program ('listeners (inr (Listen "a")))
                                    ('tools (reg "lis2" "监听器"))
                                    (Done)))))
  (define (progC c) (hash-ref conf-components c))
  (define (normalize s)
    (match s
      [(inl h) (sort (hash->list h) string<? #:key ~s)]
      [(inr l) (sort l string<? #:key ~s)]))
  ;根编排以插入次序指称根fiber: 第 i 个 O-Insert 得到的名字
  (define (root i γ)
    (list-ref (sort (for/list ([(n f) (state-F γ)] #:when (eq? (fiber-π f) 'root)) n) <) i))
  (define roots-inserted '(shell toolkit core git hub lis lis2 lis))
  ;root 按现存根fiber的次序编号, 被移除的根fiber之后的编号会前移;
  ;所以把唯一的 O-Dispose 放在最后, 之前的编号就是插入次序.
  (define conf-script*
    (append
     (for/list ([c roots-inserted]) (λ (γ) (O-Insert c)))
     (list (λ (γ) (O-Restart (root 2 γ)))          ;core
           (λ (γ) (O-Restart (root 5 γ)))          ;第一个 lis
           (λ (γ) (O-Dispose (root 1 γ))))))       ;toolkit
  (define-values (γ-static _)
    (settle ΣC progC (for/fold ([γ init]) ([c '(shell core git hub lis lis2 lis)])
                       (orchestrate ΣC progC γ (O-Insert c)))))
  (check-false (has-failed? γ-static))
  (define expected (observe γ-static normalize))
  (for ([seed (in-range 200)])
    (define-values (γs _) (interleave ΣC progC init conf-script* (random-choose seed)))
    (define final (last γs))
    (check-true (quiet? ΣC progC final))
    (check-false (has-failed? final) (format "种子 ~a" seed))
    (check-equal? (observe final normalize) expected (format "种子 ~a" seed)))

  ;;; 附录A: 单独加载与程序的解释一致
  ;base 中已有 shell 登记的 ls, 所以 bad 的解释失败, 单独加载也失败
  (define base (go (orch init (O-Insert 'core) (O-Insert 'bus) (O-Insert 'shell))))
  (for ([c '(git toolkit local watcher bad)])
    (define γ (orch base (O-Insert c)))
    (define n (fiber-of γ c))
    (define t (state-next γ))
    (define σ (store γ))
    ;只让 n 走步, 直到它离开 Loading
    (define γ*
      (let loop ([γ γ])
        (define ℓ (for/first ([ℓ (L n)] #:when (step Σ prog γ ℓ)) ℓ))
        (if (and ℓ (not (Active? (fiber-θ (F γ n))))
                 (not (Unloading? (fiber-θ (F γ n)))))
            (loop (step Σ prog γ ℓ))
            γ)))
    (match ((den Σ (component-body (prog c)) t) σ)
      [(list σ* g)
       (check-true (Active? (fiber-θ (F γ* n))) (~a c))
       ;结束时的存储 ≃ σ'
       (check-true (store≃ Σ (store γ*) σ*) (~a c))
       ;g σ' ≃ σ (定理: 解释带见证)
       (check-true (store≃ Σ (g σ*) σ) (~a c))
       ;累加器按 LIFO 复合起来逐点 ≃ g
       (define undo (acc->store (acc-of (fiber-θ (F γ* n)))))
       (for ([τ (list σ* (store γ*) (hash-set σ* 'tools (inl (hash "zz" 0))))])
         (check-true (store≃ Σ (undo τ) (g τ)) (~a c)))]
      ;解释失败 (bad 的第二次 Register): 单独加载也失败
      [#f (check-equal? c 'bad)
          (check-match (fiber-θ (F γ* n)) (Unloading _ _ 'EOp))]))

  ;;; 附录B: 分发暴露注册顺序, 两次注册不可交换
  (define (reg2 first second)
    (match-let* ([(list s1 _ _) (run EventBus (On first) 1 '())]
                 [(list s2 _ _) (run EventBus (On second) 2 s1)])
      s2))
  (define s12 (reg2 "c1" "c2"))
  (define s21 (reg2 "c2" "c1"))
  (check-not-equal? (runTest EventBus (list (LF (Emit) 9)) s12)
                    (runTest EventBus (list (LF (Emit) 9)) s21))
  ;去掉分发, 监听器注册在多重集意义下可交换
  (check-true (≃ Listeners '("c1" "c2") '("c2" "c1"))))
