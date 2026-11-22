#lang s-exp "../lang.rkt"
;; 反应中提供键: 展开期报错
(define-plugin late
  #:provide (api)
  (provide api (record))
  (on "tick" (ev) (provide api (record))))
