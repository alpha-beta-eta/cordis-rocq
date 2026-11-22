#lang racket/base
;;; lang.rkt —— 插件 EDSL 的模块语言. 插件文件写作  #lang s-exp "lang.rkt".
;;;
;;; 这个语言只导出 define-plugin. 插件模块拿不到 Racket 的 if, set!, require, 函数应用,
;;; 所以宿主层面检查操作结果的代码写不出来: 语言限制代替了 Haskell/OCaml 中的参数性.
;;; 键是否声明在展开期检查, 错误指向源码位置.

(require (for-syntax racket/base racket/list racket/string syntax/parse) racket/stxparam "sym.rkt")
(provide (rename-out [module-begin #%module-begin]) define-plugin)

;; (list inject optional provide), 每项是符号列表; 在 define-plugin 外为 #f
(define-syntax-parameter declared #f)
(define-syntax-parameter reacting? #f)

(define-for-syntax (check-key! who k kinds)
  (define d (syntax-parameter-value #'declared))
  (define names (append* (for/list ([kind kinds])
                           (case kind [(inject) (car d)] [(optional) (cadr d)] [(provide) (caddr d)]))))
  (unless (memq (syntax-e k) names)
    (raise-syntax-error who (format "键 ~a 没有在 ~a 中声明" (syntax-e k)
                                    (string-join (for/list ([x kinds]) (format "#:~a" x)) " 或 "))
                        k)))

(define-syntax (module-begin stx)
  (syntax-parse stx
    #:datum-literals (define-plugin)
    [(_ (~and form (define-plugin name:id . _)) ...)
     #'(#%module-begin form ... (define plugins (list name ...)) (provide plugins name ...))]))

(define-syntax (define-plugin stx)
  (syntax-parse stx
    [(_ name:id
        (~alt (~optional (~seq #:inject (i:id ...)))
              (~optional (~seq #:optional (o:id ...)))
              (~optional (~seq #:provide (p:id ...))))
        ...
        body ...)
     (with-syntax ([(i ...) (or (attribute i) '())]
                   [(o ...) (or (attribute o) '())]
                   [(p ...) (or (attribute p) '())])
       #'(define name
           (plugin (symbol->string 'name)
                   (list (symbol->string 'i) ...)
                   (list (symbol->string 'o) ...)
                   (list (symbol->string 'p) ...)
                   (λ ()
                     (syntax-parameterize ([declared (list '(i ...) '(o ...) '(p ...))])
                       (stmts body ...))))))]))

;; 语句序列 -> 程序
(define-syntax (stmts stx)
  (syntax-parse stx
    #:datum-literals (<- read read? put provide spawn on resource when if fail)
    [(_) #'(done/r)]
    [(_ (x:id <- read k:id) rest ...)
     (check-key! 'read #'k '(inject provide))
     #'(read/r (symbol->string 'k) (λ (x) (stmts rest ...)))]
    [(_ (x:id <- read? k:id) rest ...)
     (check-key! 'read? #'k '(optional))
     #'(read?/r (symbol->string 'k) (λ (x) (stmts rest ...)))]
    [(_ (put k:id e) rest ...)
     (check-key! 'put #'k '(inject provide))
     #'(put/r (symbol->string 'k) (expr e) (stmts rest ...))]
    [(_ (provide k:id e) rest ...)
     (when (syntax-parameter-value #'reacting?)
       (raise-syntax-error 'provide "反应中不能提供键" #'k))
     (check-key! 'provide #'k '(provide))
     #'(provide/r (symbol->string 'k) (expr e) (stmts rest ...))]
    [(_ (spawn c:id) rest ...)
     #'(spawn/r c (stmts rest ...))]
    [(_ (on ev:str (x:id) body ...) rest ...)
     #'(on/r 'ev (λ (x) (syntax-parameterize ([reacting? #t]) (stmts body ...)))
             (stmts rest ...))]
    [(_ (resource path:str e ...) rest ...)
     #'(resource/r 'path (list (expr e) ...) (stmts rest ...))]
    [(_ (fail m:str)) #'(fail/r 'm)]
    [(_ (when c s ...)) #'(if/r (expr c) (stmts s ...) (done/r))]
    [(_ (when c s ...) rest ...+) #'(seq/r (stmts (when c s ...)) (stmts rest ...))]
    [(_ (if c (s ...) (t ...))) #'(if/r (expr c) (stmts s ...) (stmts t ...))]
    [(_ (if c (s ...) (t ...)) rest ...+) #'(seq/r (stmts (if c (s ...) (t ...))) (stmts rest ...))]))

;; 表达式 -> repr. 变量只能是 <- 或 on 绑定的 repr.
(define-syntax (expr stx)
  (syntax-parse stx
    #:datum-literals (field record present? js eq? not)
    [(_ v:str) #'(lit/r 'v)]
    [(_ v:exact-integer) #'(lit/r 'v)]
    [(_ v:boolean) #'(lit/r 'v)]
    [(_ x:id) #'x]
    [(_ (field e f:id)) #'(field/r (expr e) (symbol->string 'f))]
    [(_ (record [k:id e] ...)) #'(record/r (list (cons (symbol->string 'k) (expr e)) ...))]
    [(_ (present? e)) #'(present/r (expr e))]
    [(_ (js path:str e ...)) #'(js/r 'path (list (expr e) ...))]
    [(_ (eq? a b)) #'(eq/r (expr a) (expr b))]
    [(_ (not a)) #'(not/r (expr a))]))
