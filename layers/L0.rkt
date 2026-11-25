#lang racket
;Cordis 的渐进原型, 第0层: 可撤销的服务.
;各层的说明见 README.md. 每层是一个完整的文件, 不依赖前面的层; 相邻两层的差别见 diffs/.
;本层新增: 服务 Σ. 它在状态 s 上运行操作 a, 成功时交出新状态 s', 一个逆 g 和结果;
;  运行时还给每次操作一个新鲜的令牌 t, 操作可以用它标记自己产生的东西.
;本层的性质: 见证 —— 成功时 g s' ≃ s.
;引出下一层的问题: 逆由谁保管, 何时施加? 别人在中间也动过状态时, 逆还对吗?
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

;例: 注册表: 名字 -> 值, 逐点比较
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

;例: 有序事件总线: (令牌 . 回调) 的列表, 用相等比较 (分发看得到顺序)
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

;;; ======== 示例 ========

;Σ = Registry ⊕ EventBus
(define Σ (Sum Registry EventBus))
(define (reg x v) (inl (Register x v)))
(define (on c) (inr (On c)))

(module+ main
  ;两次注册, 各自交出逆; 按 LIFO 施加回到起点
  (match-define (list s1 g1 _) (run Registry (Register "ls" "列出文件") 0 (hash)))
  (match-define (list s2 g2 _) (run Registry (Register "cat" "打印文件") 1 s1))
  (printf "注册 ls, cat: ~a\n" (sort (hash-keys s2) string<?))
  (printf "撤销 cat: ~a\n" (sort (hash-keys (g2 s2)) string<?))
  (printf "再撤销 ls: ~a\n" (hash-keys (g1 (g2 s2))))
  ;同一个回调注册两次: 令牌让每次的逆只删自己那一项
  (match-define (list e1 _ _) (run EventBus (On "c") 3 '()))
  (match-define (list e2 h2 _) (run EventBus (On "c") 4 e1))
  (printf "On 两次后撤销第二次: ~a\n" (h2 e2))
  ;按回调删: 删掉的是第一次的
  (match-define (list f1 _ _) (run EventBus (OnByCallback "c") 3 '()))
  (match-define (list f2 k2 _) (run EventBus (OnByCallback "c") 4 f1))
  (printf "OnByCallback 两次后撤销第二次: ~a (留下的是第二次的)\n" (k2 f2)))

(module+ test
  (require rackunit)

  ;每个操作带见证
  (for ([a (list (Register "x" 1) (Lookup "x"))] [s (list (hash) (hash "x" 0))])
    (check-true (witnessed-at? Registry a 0 s)))
  (for ([a (list (On "c") (Emit))])
    (check-true (witnessed-at? EventBus a 7 '((3 . "c")))))
  ;按回调注销不是精确的逆: 撤销第二次注册删掉的是第一次的钩子
  (check-false (witnessed-at? EventBus (OnByCallback "c") 7 '((3 . "c"))))
  ;有序事件总线: 表中已有同一令牌的钩子时注册失败
  (check-false (run EventBus (On "d") 3 '((3 . "c"))))
  ;注册表: 同名的第二次登记失败
  (check-false (run Registry (Register "x" 2) 0 (hash "x" 1)))
  ;和: 一方的操作在另一方的状态上失败
  (check-false (run Σ (reg "x" 1) 0 (inr '())))
  (check-true (witnessed-at? Σ (reg "x" 1) 0 (inl (hash))))
  (check-true (witnessed-at? Σ (on "c") 0 (inr '()))))
