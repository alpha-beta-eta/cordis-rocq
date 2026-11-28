#lang racket
;; 读 viz/text/*.sexp（TextExamples.v 输出的 S-表达式序列），做两项检查：
;;   1. 每个文件都能被 read 读完；
;;   2. 对每个 (run ...)：从 init 出发，逐步删去 del、加上 add，得到的项集合等于 final 的项。
;; 用法：racket viz/check.rkt viz/text/*.sexp
;; 这也是处理这种输出的一个例子：状态就是项的集合，一步就是 del 与 add。

(define (read-all f) (with-input-from-file f (λ () (for/list ([x (in-port read)]) x))))

;; 状态的项：去掉 (enabled ...) 与 (quiet ...)。
(define (items xs) (filter (λ (x) (not (memq (car x) '(enabled quiet)))) xs))

(define (replay forms)
  (for/fold ([s (items (cdr (assq 'init forms)))])
            ([x forms] #:when (and (eq? (car x) 'step) (pair? (fourth x))))
    (match-define (list 'step _ _ (cons 'del del) (cons 'add add) _) x)
    (append (filter (λ (i) (not (member i del))) s) add)))

(for ([f (current-command-line-arguments)])
  (define forms (read-all f))
  (define kind (car (first forms)))
  (printf "~a: ~a 个表达式" f (length forms))
  (when (eq? kind 'run)
    (define ok (equal? (list->set (replay forms)) (list->set (items (cdr (assq 'final forms))))))
    (printf "，重放~a" (if ok "与 final 一致" "与 final 不一致"))
    (unless ok (exit 1)))
  (newline))
