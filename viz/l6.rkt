#lang racket
;; layers/L6.rkt 的执行, 输出为 S-表达式序列, 格式与 viz/Text.v 相同 (见 viz/DESIGN.md 第 A 节).
;;
;; 状态是项的集合: (fiber ...), (bind ...); 一次执行是
;;   (run "标题") (init 项 ... (enabled ...))
;;   (step i 标签 (del 项 ...) (add 项 ...) (enabled ...))   或   (step i 标签 refused)
;;   (final 项 ... (quiet #t))
;; 两次执行并排是 (compare ..) (labels a ..) (labels b ..) (final a ..) (final b ..) (differ ..) (same ..).
;;
;; 与 Rocq 一侧唯一的不同在累加器的 UOp 项: L6 的 UOp 只记逆 g, 不记操作本身; 这里像 Calculus.v 的
;; ghost 记录 oplog 一样, 在每次 L-Step 落地一个操作时按令牌记下它 (只用于打印, 规则不读它).
;;
;; racket viz/l6.rkt: 取 viz/text/ 中核心演算 (step) 的那些执行的标签序列, 在 L6 上重放,
;; 把输出写到 viz/text/l6/, 并逐个表达式与 Rocq 的输出比较.

(require (prefix-in l6: "../layers/L6.rkt"))
(provide run-sexps compare-sexps summary print-sexps parse-label show-label
         Basic ViewFail)

;;; ======== 打印 ========

(define cols 120)
(define (flat e) (format "~s" e))
(define (atom? e) (not (pair? e)))

;放不下 cols 列的表: 开头的原子留在第一行, 其余每个元素另起一行, 缩进两格 (与 Text.v 的 pp 相同)
(define (pp ind e)
  (define f (flat e))
  (cond
    [(or (<= (+ ind (string-length f)) cols) (not (pair? e))) f]
    [else
     (define out (open-output-string))
     (write-string "(" out)
     (let loop ([l e] [first? #t] [lead? #t])
       (unless (null? l)
         (define x (car l))
         (cond [first? (write-string (pp (add1 ind) x) out) (loop (cdr l) #f (atom? x))]
               [(and lead? (atom? x)) (write-string (string-append " " (flat x)) out) (loop (cdr l) #f #t)]
               [else (write-string (string-append "\n" (make-string (+ ind 2) #\space) (pp (+ ind 2) x)) out)
                     (loop (cdr l) #f #f)])))
     (write-string ")" out)
     (get-output-string out)]))

;顶层的 step 把标签也留在第一行
(define (pp-top e)
  (match e
    [(list 'step i lb rest ...)
     (define f (flat e))
     (if (<= (string-length f) cols)
         f
         (string-append "(step " (flat i) " " (flat lb)
                        (apply string-append (for/list ([x rest]) (string-append "\n  " (pp 2 x))))
                        ")"))]
    [_ (pp 0 e)]))

(define (print-sexps es [out (current-output-port)])
  (for ([e es]) (write-string (pp-top e) out) (newline out)))

;;; ======== 一个实例: 组件表, 服务, 打印函数 ========

;Σ, prog, 要显示的键 (按次序) 与组件, 服务状态的条目, 操作
(struct inst (Σ prog keys comps entries sop))

(define (reg-entries s) (for/list ([x (sort (hash-keys s) <)]) (list x (hash-ref s x))))
(define (reg-op a)
  (match a
    [(l6:Register x v) (list 'register x v)]
    [(l6:Lookup x) (list 'lookup x)]))

;Examples/Basic.v: provider 提供 tools (空登记表), consumer 依赖 tools 并登记 7 ↦ 42
(define basic-components
  (hash 'provider (l6:make-component '() '(tools) (l6:Provide 'tools (hash) (l6:Done)))
        'consumer (l6:make-component '(tools) '() (l6:Call 'tools (l6:Register 7 42) (λ (_) (l6:Done))))))
(define Basic (inst l6:Registry (λ (c) (hash-ref basic-components c)) '(tools) '(provider consumer)
                    reg-entries reg-op))

;errors/theories/ViewFail.v: provider7 提供 tools 时 7 已被占用 (7 ↦ 0)
(define vf-components
  (hash-set* basic-components
             'provider7 (l6:make-component '() '(tools) (l6:Provide 'tools (hash 7 0) (l6:Done)))))
(define ViewFail (inst l6:Registry (λ (c) (hash-ref vf-components c)) '(tools) '(provider7 consumer provider)
                       reg-entries reg-op))

;;; ======== 标签 ========

(define (parse-label e)
  (match e
    [(list 'OInsert c) (l6:O-Insert c)]
    [(list 'ODispose n) (l6:O-Dispose n)]
    [(list 'OReset n) (l6:O-Reset n)]
    [(list 'ORestart n) (l6:O-Restart n)]
    [(list 'OReact n i) (l6:O-React n i)]
    [(list 'LBegin n) (l6:L-Begin n)]
    [(list 'LStep n) (l6:L-Step n)]
    [(list 'LDivert n) (l6:L-Divert n)]
    [(list 'LLeave n) (l6:L-Leave n)]
    [(list 'LUndo n) (l6:L-Undo n)]
    [(list 'LRetireChild n) (l6:L-RetireChild n)]
    [(list 'LUnloaded n) (l6:L-Unloaded n)]
    [(list 'LRemove n) (l6:L-Remove n)]))

(define (show-label ℓ)
  (match ℓ
    [(l6:O-Insert c) (list 'OInsert c)]
    [(l6:O-Dispose n) (list 'ODispose n)]
    [(l6:O-Reset n) (list 'OReset n)]
    [(l6:O-Restart n) (list 'ORestart n)]
    [(l6:O-React n i) (list 'OReact n i)]
    [(l6:L-Begin n) (list 'LBegin n)]
    [(l6:L-Step n) (list 'LStep n)]
    [(l6:L-Divert n) (list 'LDivert n)]
    [(l6:L-Leave n) (list 'LLeave n)]
    [(l6:L-Undo n) (list 'LUndo n)]
    [(l6:L-RetireChild n) (list 'LRetireChild n)]
    [(l6:L-Unloaded n) (list 'LUnloaded n)]
    [(l6:L-Remove n) (list 'LRemove n)]))

;;; ======== 状态的项 ========

;视图按组件的依赖次序列出 (与 Calculus.v 的 View 相同); 目标 ⊥ 为 none
(define (view-pairs I c ω) (for/list ([k (l6:component-d ((inst-prog I) c))]) (list k (hash-ref ω k))))
(define (target-item I γ n c)
  (define w (l6:target (inst-prog I) γ n))
  (cons 'target (if w (view-pairs I c w) '(none))))

(define (undo-item I oplog u)
  (match u
    [(l6:UOp k ι t _) (list 'op k ι (let ([a (hash-ref oplog t #f)]) (if a ((inst-sop I) a) '?)))]
    [(l6:UProv k ι) (list 'prov k ι)]
    [(l6:USpawn m) (list 'spawn m)]))

(define (instr I P)
  (match P
    [(l6:Done) 'done]
    [(l6:Fail) 'fail]
    [(l6:Call k a _) (list 'op k ((inst-sop I) a))]
    [(l6:Provide k _ _) (list 'provide k)]
    [(l6:Spawn c _) (list 'spawn c)]))

(define (fiber-item I oplog γ n)
  (match-define (l6:fiber c π τ θ) (l6:F γ n))
  (define par (if (eq? π 'root) '() (list (list 'parent π))))
  (define dsp (if τ '(disposed) '()))
  (define (life t ζ) (if ζ (list 'life t ζ) (list 'life t)))
  (define (acc a) (cons 'acc (for/list ([u a]) (undo-item I oplog u))))
  (define (view ω) (cons 'view (view-pairs I c ω)))
  (define tg (target-item I γ n c))
  (append
   (list 'fiber n c)
   (match θ
     [(l6:Inactive ζ) (append (list (life 'Inactive ζ)) par dsp (list tg))]
     [(l6:Loading P a ω) (append (list (life 'Loading #f)) par dsp (list (view ω) tg (list 'next (instr I P)) (acc a)))]
     [(l6:Active a ω) (append (list (life 'Active #f)) par dsp (list (view ω) tg (acc a)))]
     [(l6:Unloading a ω ζ)
      (append (list (life 'Unloading ζ)) par dsp (if (l6:held? γ n a) '(held) '()) (list (view ω) tg (acc a)))])))

(define (bind-items I γ)
  (for*/list ([k (inst-keys I)] [b (in-value (l6:B γ k))] #:when b)
    (match-define (l6:binding ι q s) b)
    (list 'bind k (list 'pid ι) (list 'owner q) (cons 'entries ((inst-entries I) s)))))

(define (items I oplog γ)
  (append (for/list ([n (l6:names γ)] #:when (l6:F γ n)) (fiber-item I oplog γ n))
          (bind-items I γ)))

(define (enabled I γ) (l6:enabled (inst-Σ I) (inst-prog I) γ))
(define (enabled-item I γ) (cons 'enabled (map show-label (enabled I γ))))

;;; ======== 执行 ========

;一步, 连同 ghost 操作记录: 落地的操作按令牌记下
(define (step+log I oplog γ ℓ)
  (define γ* (l6:step (inst-Σ I) (inst-prog I) γ ℓ))
  (define oplog*
    (match* (ℓ γ*)
      [((l6:L-Step n) (? l6:state?))
       (match* ((l6:fiber-θ (l6:F γ n)) (l6:fiber-θ (l6:F γ* n)))
         [((l6:Loading (l6:Call _ a _) _ _) (l6:Loading _ (cons (l6:UOp _ _ t _) _) _)) (hash-set oplog t a)]
         [(_ _) oplog])]
      [(_ _) oplog]))
  (values γ* oplog*))

;返回 (values 表达式序列 标签列 终态 静止?)
(define (go I γ0 labels)
  (for/fold ([γ γ0] [oplog (hash)] [out '()] [col '()]
             #:result (values (reverse out) (reverse col) γ oplog))
            ([ℓ labels] [i (in-naturals 1)])
    (define-values (γ* oplog*) (step+log I oplog γ ℓ))
    (if γ*
        (let ([old (items I oplog γ)] [new (items I oplog* γ*)])
          (values γ* oplog*
                  (cons (list 'step i (show-label ℓ)
                              (cons 'del (filter (λ (x) (not (member x new))) old))
                              (cons 'add (filter (λ (x) (not (member x old))) new))
                              (enabled-item I γ*))
                        out)
                  (cons (show-label ℓ) col)))
        (values γ oplog (cons (list 'step i (show-label ℓ) 'refused) out)
                (cons (list 'refused (show-label ℓ)) col)))))

(define (run-sexps I title labels [γ0 l6:init])
  (define-values (steps _ γ oplog) (go I γ0 labels))
  (append (list (list 'run title) (append (list 'init) (items I (hash) γ0) (list (enabled-item I γ0))))
          steps
          (list (append (list 'final) (items I oplog γ) (list (list 'quiet (null? (enabled I γ))))))))

;;; ======== 两次执行并排 ========

(define (summary I labels [γ0 l6:init])
  (define-values (_ col γ __) (go I γ0 labels))
  (list col γ (null? (enabled I γ))))

(define (life-sig f)
  (match-define (l6:fiber _ _ τ θ) f)
  (append (match θ
            [(l6:Inactive ζ) (if ζ (list 'Inactive ζ) '(Inactive))]
            [(l6:Loading _ _ _) '(Loading)]
            [(l6:Active _ _) '(Active)]
            [(l6:Unloading _ _ ζ) (if ζ (list 'Unloading ζ) '(Unloading))])
          (if τ '(disposed) '())))

(define (signature I γ)
  (append
   (for/list ([c (inst-comps I)])
     (list* 'comp c (for/list ([n (l6:names γ)] #:when (match (l6:F γ n) [(l6:fiber (== c) _ _ _) #t] [_ #f]))
                      (life-sig (l6:F γ n)))))
   (for/list ([k (inst-keys I)])
     (list* 'key k
            (match (l6:B γ k)
              [(l6:binding _ q s)
               (list (list 'by (match (l6:F γ q) [(l6:fiber c _ _ _) c] [#f q]))
                     (cons 'entries ((inst-entries I) s)))]
              [#f '(unbound)])))))

(define (compare-sexps I na nb A B)
  (match-define (list ca fa qa) A)
  (match-define (list cb fb qb) B)
  (define sa (append (signature I fa) (list (list 'quiet qa))))
  (define sb (append (signature I fb) (list (list 'quiet qb))))
  (define differ (for/list ([x sa] [y sb] #:unless (equal? x y)) (take x 2)))
  (list (list 'compare na nb)
        (list* 'labels 'a ca) (list* 'labels 'b cb)
        (list* 'final 'a sa) (list* 'final 'b sb)
        (cons 'differ differ)
        (list 'same (null? differ))))

;;; ======== 与 Rocq 的输出对照 ========

(module+ main
  (define here (path-only (path->complete-path (find-system-path 'run-file))))
  (define text (build-path here "text"))
  (define out-dir (build-path text "l6"))
  (make-directory* out-dir)
  (define (read-all f) (with-input-from-file f (λ () (for/list ([x (in-port read)]) x))))
  ;一个执行文件的标签 (被拒的也算)
  (define (run-labels forms)
    (for/list ([x forms] #:when (eq? (car x) 'step)) (parse-label (third x))))
  (define (col-labels col) (for/list ([x col]) (parse-label (match x [(list 'refused l) l] [l l]))))
  (define (title forms) (second (first forms)))
  ;Rocq 一侧用核心 step 的文件, 及其组件表
  (define runs '(("basic" . Basic) ("divert" . Basic) ("core358" . Basic) ("vfA" . ViewFail) ("vfB" . ViewFail)))
  (define compares '(("interleave" . Basic) ("vf_core" . ViewFail)))
  (define (inst-of s) (if (eq? s 'Basic) Basic ViewFail))
  (define bad 0)
  (define (emit name forms rocq)
    (call-with-output-file (build-path out-dir (string-append name ".sexp")) #:exists 'truncate
      (λ (o) (print-sexps forms o)))
    (define same (equal? forms rocq))
    (unless same (set! bad (add1 bad)))
    (printf "~a: ~a 个表达式, ~a\n" name (length forms) (if same "与 Rocq 的输出相同" "与 Rocq 的输出不同")))
  (for ([r runs])
    (define rocq (read-all (build-path text (string-append (car r) ".sexp"))))
    (emit (car r) (run-sexps (inst-of (cdr r)) (title rocq) (run-labels rocq)) rocq))
  (for ([r compares])
    (define rocq (read-all (build-path text (string-append (car r) ".sexp"))))
    (define I (inst-of (cdr r)))
    (define la (col-labels (cddr (second rocq))))
    (define lb (col-labels (cddr (third rocq))))
    (emit (car r)
          (compare-sexps I (second (first rocq)) (third (first rocq)) (summary I la) (summary I lb))
          rocq))
  (unless (zero? bad) (exit 1)))
