#lang racket/base

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         racket/match
         racket/function)

(provide define-formatted
         foldr1)

;; ------------------------------------------------

(define-syntax (define-formatted stx)
  (syntax-parse stx
    [(_ name:id)
     (with-syntax ([n (format-id #'name "~a-format" #'name)])
       #'(define (n fmt-msg . args)
           (name (apply (curry format fmt-msg) args))))]))

(define (foldr1 f ls)
  (define/match (loop rs)
    [((list)) (error "foldr1 expects non-null? lists")]
    [((list a)) a]
    [((list a b ...)) (f a (loop (cdr rs)))])
  (loop ls))
