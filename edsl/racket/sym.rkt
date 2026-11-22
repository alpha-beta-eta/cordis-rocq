#lang racket/base
;;; sym.rkt —— 插件 EDSL 的签名 (tagless final) 与三个解释: 初始 AST, JS 生成, 静态分析.
;;;
;;; 一个解释就是一个 sym 结构体. 插件体是一个 thunk, 在 (current-sym) 下求值, 得到该解释的 repr.
;;; 程序的 repr 只能交给签名中的方法; 操作结果 (read 的续延参数) 也是 repr, 宿主层面检查不了它.

(require racket/string racket/list)
(provide (struct-out plugin) current-sym
         done/r fail/r read/r read?/r put/r provide/r spawn/r on/r resource/r if/r seq/r
         lit/r field/r record/r present/r js/r eq/r not/r
         render-ast render-js-module analyze link-check sx->string)

;;; ------------------------------------------------------------------
;;; 签名
(struct sym (done fail read read? put provide spawn on resource if seq
             lit field record present js eq not))
(define current-sym (make-parameter #f))

;; name: 字符串; inject/optional/provide: 字符串列表; body: (-> repr)
(struct plugin (name inject optional provide body))

(define-syntax-rule (define-methods [name acc] ...)
  (begin (define (name . args) (apply (acc (current-sym)) args)) ...))
(define-methods
  [done/r sym-done] [fail/r sym-fail] [read/r sym-read] [read?/r sym-read?]
  [put/r sym-put] [provide/r sym-provide] [spawn/r sym-spawn] [on/r sym-on]
  [resource/r sym-resource] [if/r sym-if] [seq/r sym-seq]
  [lit/r sym-lit] [field/r sym-field] [record/r sym-record] [present/r sym-present]
  [js/r sym-js] [eq/r sym-eq] [not/r sym-not])

;; 续延在渲染时才被调用, 所以整个渲染过程都要在 current-sym 之下进行
(define (run-under s p . args)
  (parameterize ([current-sym s])
    (define r ((plugin-body p)))
    (if (null? args) r (apply r args))))

;;; ------------------------------------------------------------------
;;; 生成名字的状态: 变量与标签各一个计数器, 按渲染顺序 (从左到右, 深度优先) 分配
(struct gen ([vars #:mutable] [labels #:mutable]))
(define (new-gen) (gen 0 0))
(define (fresh-var! g) (set-gen-vars! g (add1 (gen-vars g))) (format "x~a" (gen-vars g)))
(define (fresh-label! g) (set-gen-labels! g (add1 (gen-labels g))) (format "L~a" (gen-labels g)))

(define (json-str s)
  (string-append "\"" (string-replace (string-replace s "\\" "\\\\") "\"" "\\\"") "\""))

;;; ------------------------------------------------------------------
;;; 解释 1: 初始 AST (与 Rocq 的 Prog 对应; 也用于和 OCaml 版逐字比较)
;;; repr = (gen -> s-expr)
(define (sx->string x)
  (cond [(pair? x) (string-append "(" (string-join (map sx->string x) " ") ")")]
        [(null? x) "()"]
        [(symbol? x) (symbol->string x)]
        [(string? x) (json-str x)]
        [(exact-integer? x) (number->string x)]
        [(eq? x #t) "true"]
        [(eq? x #f) "false"]))

(define (bind-var g k)
  (define x (string->symbol (fresh-var! g)))
  (values x ((k (λ (g) `(var ,x))) g)))

(define ast-sym
  (sym (λ () (λ (g) '(done)))
       (λ (m) (λ (g) `(fail ,m)))
       (λ (k κ) (λ (g) (let-values ([(x b) (bind-var g κ)]) `(read ,k ,x ,b))))
       (λ (k κ) (λ (g) (let-values ([(x b) (bind-var g κ)]) `(read? ,k ,x ,b))))
       (λ (k e p) (λ (g) (let* ([e (e g)] [p (p g)]) `(put ,k ,e ,p))))
       (λ (k e p) (λ (g) (let* ([e (e g)] [p (p g)]) `(provide ,k ,e ,p))))
       (λ (c p) (λ (g) `(spawn ,(plugin-name c) ,(p g))))
       (λ (ev κ p) (λ (g) (let*-values ([(x h) (bind-var g κ)] [(p) (p g)])
                            `(on ,ev ,x ,h ,p))))
       (λ (path args p) (λ (g) (let* ([as (for/list ([a args]) (a g))] [p (p g)])
                                 `(resource ,path ,as ,p))))
       (λ (c a b) (λ (g) (let* ([c (c g)] [a (a g)] [b (b g)]) `(if ,c ,a ,b))))
       (λ (a b) (λ (g) (let* ([a (a g)] [b (b g)]) `(seq ,a ,b))))
       (λ (v) (λ (g) `(lit ,v)))
       (λ (e f) (λ (g) `(field ,(e g) ,f)))
       (λ (kvs) (λ (g) `(record ,@(for/list ([kv kvs]) (list (car kv) ((cdr kv) g))))))
       (λ (e) (λ (g) `(present ,(e g))))
       (λ (path args) (λ (g) `(js ,path ,@(for/list ([a args]) (a g)))))
       (λ (a b) (λ (g) (let* ([a (a g)] [b (b g)]) `(eq ,a ,b))))
       (λ (a) (λ (g) `(not ,(a g))))))

(define (render-ast p)
  (sx->string
   `(plugin ,(plugin-name p) (inject ,@(plugin-inject p)) (optional ,@(plugin-optional p))
            (provide ,@(plugin-provide p)) ,(run-under ast-sym p (new-gen)))))

;;; ------------------------------------------------------------------
;;; 解释 2: JS 生成 (目标是 runtime/rt.js 的指令)
;;; 程序 repr = (gen 缩进 done语句 -> 行的列表); 表达式 repr = (gen -> 字符串)
(define (ln ind s) (string-append (make-string (* 2 ind) #\space) s))
(define (js-ident s) (string-replace s "-" "_"))
(define (js-array ss) (string-append "[" (string-join (map json-str ss) ", ") "]"))

(define js-sym
  (sym (λ () (λ (g ind d) (list (ln ind d))))
       (λ (m) (λ (g ind d) (list (ln ind (format "yield I.fail(~a);" (json-str m)))
                                 (ln ind "return;"))))
       (λ (k κ) (λ (g ind d)
                  (define x (fresh-var! g))
                  (cons (ln ind (format "const ~a = yield I.read(~a);" x (json-str k)))
                        ((κ (λ (g) x)) g ind d))))
       (λ (k κ) (λ (g ind d)
                  (define x (fresh-var! g))
                  (cons (ln ind (format "const ~a = yield I.readOpt(~a);" x (json-str k)))
                        ((κ (λ (g) x)) g ind d))))
       (λ (k e p) (λ (g ind d)
                    (define s (ln ind (format "yield I.put(~a, ~a);" (json-str k) (e g))))
                    (cons s (p g ind d))))
       (λ (k e p) (λ (g ind d)
                    (define s (ln ind (format "yield I.provide(~a, ~a);" (json-str k) (e g))))
                    (cons s (p g ind d))))
       (λ (c p) (λ (g ind d)
                  (cons (ln ind (format "yield I.spawn(~a);" (js-ident (plugin-name c))))
                        (p g ind d))))
       (λ (ev κ p) (λ (g ind d)
                     (define x (fresh-var! g))
                     (define head (ln ind (format "yield I.on(~a, function* (~a) {" (json-str ev) x)))
                     (define h ((κ (λ (g) x)) g (add1 ind) "return;"))
                     (append (list head) h (list (ln ind "});")) (p g ind d))))
       (λ (path args p) (λ (g ind d)
                          (define as (string-join (for/list ([a args]) (a g)) ", "))
                          (cons (ln ind (format "yield I.resource(payload(~a), [~a]);" (json-str path) as))
                                (p g ind d))))
       (λ (c a b) (λ (g ind d)
                    (define cs (c g))
                    (define as (a g (add1 ind) d))
                    (define bs (b g (add1 ind) d))
                    (append (list (ln ind (format "if (~a) {" cs))) as
                            (list (ln ind "} else {")) bs (list (ln ind "}")))))
       (λ (a b) (λ (g ind d)
                  (define l (fresh-label! g))
                  (define as (a g (add1 ind) (format "break ~a;" l)))
                  (append (list (ln ind (format "~a: {" l))) as (list (ln ind "}")) (b g ind d))))
       (λ (v) (λ (g) (cond [(string? v) (json-str v)]
                           [(exact-integer? v) (number->string v)]
                           [v "true"] [else "false"])))
       (λ (e f) (λ (g) (format "~a[~a]" (e g) (json-str f))))
       (λ (kvs) (λ (g) (string-append
                         "{" (string-join (for/list ([kv kvs])
                                            (format "~a: ~a" (json-str (car kv)) ((cdr kv) g)))
                                          ", ") "}")))
       (λ (e) (λ (g) (format "(~a !== null)" (e g))))
       (λ (path args) (λ (g) (format "I.lazy(~a, [~a])" (json-str path)
                                     (string-join (for/list ([a args]) (a g)) ", "))))
       (λ (a b) (λ (g) (format "(~a === ~a)" (a g) (b g))))
       (λ (a) (λ (g) (format "(!~a)" (a g))))))

(define (render-js-plugin p)
  (define body (run-under js-sym p (new-gen) 2 "return;"))
  (append
   (list (format "const ~a = {" (js-ident (plugin-name p)))
         (ln 1 (format "name: ~a," (json-str (plugin-name p))))
         (ln 1 (format "inject: ~a," (js-array (plugin-inject p))))
         (ln 1 (format "optional: ~a," (js-array (plugin-optional p))))
         (ln 1 (format "provide: ~a," (js-array (plugin-provide p))))
         (ln 1 "body: function* () {"))
   body
   (list (ln 1 "},") "};" "")))

(define (render-js-module ps)
  (string-join
   (append (list "\"use strict\";"
                 "// generated by cordis-edsl; do not edit"
                 "const { I, payload } = require(\"../../runtime/rt.js\");"
                 "")
           (append-map render-js-plugin ps)
           (list (format "module.exports = { ~a };"
                         (string-join (map (λ (p) (js-ident (plugin-name p))) ps) ", "))
                 ""))
   "\n"))

;;; ------------------------------------------------------------------
;;; 解释 3: 静态分析. repr = 路径的列表; 路径 = 事件列表, 以 'done 或 'fail 结尾.
;;; 语言中没有递归, 所以路径有限 (有界由构造保证), 这里只是把它们列出来.
(define (prefix ev ps) (for/list ([p ps]) (cons ev p)))
(define ana-sym
  (sym (λ () '((done)))
       (λ (m) '((fail)))
       (λ (k κ) (prefix `(read ,k) (κ 'sym)))
       (λ (k κ) (prefix `(read? ,k) (κ 'sym)))
       (λ (k e p) (prefix `(put ,k) p))
       (λ (k e p) (prefix `(provide ,k) p))
       (λ (c p) (prefix `(spawn ,(plugin-name c)) p))
       (λ (ev κ p) (prefix `(on ,ev ,(κ 'sym)) p))
       (λ (path args p) (prefix `(resource ,path) p))
       (λ (c a b) (append a b))
       (λ (a b) (append* (for/list ([pa a])
                           (if (eq? (last pa) 'done)
                               (for/list ([pb b]) (append (drop-right pa 1) pb))
                               (list pa)))))
       (λ (v) 'sym) (λ (e f) 'sym) (λ (kvs) 'sym) (λ (e) 'sym)
       (λ (path args) 'sym) (λ (a b) 'sym) (λ (a) 'sym)))

;; 返回 (values 报告行 错误列表 spawn的名字)
(define (analyze p)
  (define paths (run-under ana-sym p))
  (define inj (plugin-inject p)) (define opt (plugin-optional p)) (define prv (plugin-provide p))
  (define errors '())
  (define (err! fmt . xs) (set! errors (cons (apply format fmt xs) errors)))
  (define seen (make-hash)) ; 种类 -> 键集合
  (define (see! kind k) (hash-update! seen kind (λ (s) (cons k s)) '()))
  ;; 走一条路径 (反应中的路径 reacting? = #t)
  (define (walk path reacting?)
    (for ([ev path] #:unless (symbol? ev))
      (case (car ev)
        [(read) (see! 'read (cadr ev))
                (unless (member (cadr ev) (append inj prv)) (err! "undeclared key ~a" (cadr ev)))]
        [(read?) (see! 'read? (cadr ev))
                 (unless (member (cadr ev) opt) (err! "undeclared optional key ~a" (cadr ev)))]
        [(put) (see! 'put (cadr ev))
               (unless (member (cadr ev) (append inj prv)) (err! "undeclared key ~a" (cadr ev)))]
        [(provide) (see! 'provide (cadr ev))
                   (when reacting? (err! "provide in reaction ~a" (cadr ev)))
                   (unless (member (cadr ev) prv) (err! "undeclared provide ~a" (cadr ev)))]
        [(spawn) (see! 'spawn (cadr ev))]
        [(resource) (void)]
        [(on) (for ([h (caddr ev)]) (walk h #t))])))
  (for ([path paths]) (walk path #f))
  ;; 完整提供: 每条到达 done 的路径恰好提供每个声明的键一次
  (for ([path paths] #:when (eq? (last path) 'done))
    (define provided (for/list ([ev path] #:when (and (pair? ev) (eq? (car ev) 'provide))) (cadr ev)))
    (for ([k prv])
      (define n (count (λ (x) (equal? x k)) provided))
      (cond [(= n 0) (err! "a path to done misses provide ~a" k)]
            [(> n 1) (err! "a path to done provides ~a twice" k)])))
  (define errs (sort (remove-duplicates errors) string<?))
  (define (keys kind) (sort (remove-duplicates (hash-ref seen kind '())) string<?))
  (define (lst kind) (string-append "(" (string-join (keys kind) " ") ")"))
  (define line
    (format "~a: paths=~a maxlen=~a read=~a read?=~a put=~a provide=~a spawn=~a ~a"
            (plugin-name p) (length paths)
            (apply max (map (λ (pa) (sub1 (length pa))) paths))
            (lst 'read) (lst 'read?) (lst 'put) (lst 'provide) (lst 'spawn)
            (if (null? errs) "OK" (string-append "ERRORS: " (string-join errs "; ")))))
  (values line errs (keys 'spawn)))

;;; ------------------------------------------------------------------
;;; 链接期: 有秩 (依赖与 spawn 无环), 以及提供冲突
(define (link-check ps)
  (define by-name (for/hash ([p ps]) (values (plugin-name p) p)))
  (define spawns (for/hash ([p ps]) (let-values ([(l e s) (analyze p)]) (values (plugin-name p) s))))
  ;; c -> c' 当 c 提供 c' 依赖 (含可选依赖) 的键, 或 c 可能 spawn c'
  (define (succ p)
    (sort (remove-duplicates
           (append (for/list ([q ps]
                              #:when (for/or ([k (plugin-provide p)])
                                       (member k (append (plugin-inject q) (plugin-optional q)))))
                     (plugin-name q))
                   (hash-ref spawns (plugin-name p))))
          string<?))
  (define rank (make-hash))
  (define cycle #f)
  (define (visit n stack)
    (cond [(member n stack)
           (unless cycle
             (set! cycle (append (list n) (reverse (takef stack (λ (m) (not (equal? m n))))) (list n))))
           0]
          [(hash-ref rank n #f)]
          [else
           (define r (for/fold ([r 0]) ([m (succ (hash-ref by-name n))])
                       (max r (add1 (visit m (cons n stack))))))
           (hash-set! rank n r) r]))
  ;; 高度 h = 到最远后继的距离; 秩取 H - h, 于是 c ≺ c' 蕴涵 rank c < rank c'
  (for ([p ps]) (visit (plugin-name p) '()))
  (define H (apply max 0 (hash-values rank)))
  (define conflicts
    (for*/list ([k (sort (remove-duplicates (append-map plugin-provide ps)) string<?)]
                [owners (in-value (sort (for/list ([p ps] #:when (member k (plugin-provide p)))
                                          (plugin-name p)) string<?))]
                #:when (> (length owners) 1))
      (format "conflict ~a: ~a" k (string-join owners " "))))
  (append
   (if cycle
       (list (format "cycle: ~a" (string-join cycle " -> ")))
       (for/list ([n (sort (hash-keys rank) string<?)])
         (format "rank ~a = ~a" n (- H (hash-ref rank n)))))
   conflicts))
