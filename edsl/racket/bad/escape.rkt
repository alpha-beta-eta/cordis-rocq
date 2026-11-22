#lang s-exp "../lang.rkt"
;; 想在宿主层面检查读到的值: 语言里没有 Racket 的函数应用
(define-plugin peek
  #:optional (config)
  (cfg <- read? config)
  (when (string? cfg) (fail "no")))
