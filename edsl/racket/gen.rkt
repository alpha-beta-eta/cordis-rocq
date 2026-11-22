#lang racket/base
;;; gen.rkt —— 对一个插件模块运行三个解释, 写出 out/racket/<名字>.{ast,analysis,js}.
;;; 用法: racket gen.rkt examples.rkt
;;; 分析出错的插件不生成 JS, 退出码为 1.

(require racket/string racket/file racket/list racket/path "sym.rkt")

(define (main file)
  (define ps (dynamic-require (path->complete-path file) 'plugins))
  (define base (path->string (path-replace-extension (file-name-from-path file) #"")))
  (define out (build-path (current-directory) 'up "out" "racket"))
  (make-directory* out)
  (define lines+errs (for/list ([p ps]) (let-values ([(l e s) (analyze p)]) (cons l e))))
  (define link (link-check ps))
  (define bad? (or (ormap (λ (le) (pair? (cdr le))) lines+errs)
                   (ormap (λ (l) (regexp-match? #rx"^cycle" l)) link)))
  (define (write! ext s) (display-to-file s (build-path out (string-append base ext)) #:exists 'replace))
  (write! ".analysis" (string-append (string-join (append (map car lines+errs) link) "\n") "\n"))
  (write! ".ast" (string-append (string-join (map render-ast ps) "\n") "\n"))
  (display (file->string (build-path out (string-append base ".analysis"))))
  (cond [bad? (eprintf "分析未通过, 不生成 JS\n") (exit 1)]
        [else (write! ".js" (render-js-module ps))]))

(main (vector-ref (current-command-line-arguments) 0))
