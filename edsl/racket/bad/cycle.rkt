#lang s-exp "../lang.rkt"
;; 依赖成环: 链接期报错
(define-plugin a #:inject (y) #:provide (x) (provide x (record)))
(define-plugin b #:inject (x) #:provide (y) (provide y (record)))
