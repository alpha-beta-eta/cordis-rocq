#lang s-exp "../lang.rkt"
;; 只在某个分支提供键: 完整提供不成立, 分析器拒绝
(define-plugin partial
  #:optional (config)
  #:provide (api)
  (cfg <- read? config)
  (when (present? cfg) (provide api (record [v 1]))))
