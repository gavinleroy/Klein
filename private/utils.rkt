#lang racket/base

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         racket/match)

(provide define-formatted
         foldr1)

;; ------------------------------------------------

(define-syntax (define-formatted stx)
  (syntax-parse stx
    [(_ name:id)
     (with-syntax ([n (format-id #'name "~a-format" #'name)])
       #'(define-syntax (n stx)
           (syntax-case stx ()
             [(_ msg (... ...))
              #'(name (format msg (... ...)))])))]))

(define (foldr1 f ls)
  (define/match (loop rs)
    [((list)) (error "foldr1 expects non-null? lists")]
    [((list a)) a]
    [((list a b ...)) (f a (loop (cdr rs)))])
  (loop ls))
