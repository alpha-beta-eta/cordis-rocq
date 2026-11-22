#lang s-exp "../lang.rkt"
;; 访问未声明的键: 展开期报错
(define-plugin sneaky
  #:inject (tools)
  (put agents (record [name "x"])))
