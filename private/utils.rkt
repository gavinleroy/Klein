#lang racket/base

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

(provide define-formatted)

;; ------------------------------------------------

(define-syntax (define-formatted stx)
  (syntax-parse stx
    [(_ name:id)
     (with-syntax ([n (format-id #'name "~a-format" #'name)])
       #'(define-syntax (n stx)
           (syntax-case stx ()
             [(_ msg (... ...))
              #'(name (format msg (... ...)))])))]))

