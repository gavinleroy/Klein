#lang nanopass

(provide integer? float? character? #;string? literal?
         )

;; KleinS Base Language

(define (literal? l)
  (or (integer? l)
      (float? l)
      (character? l)
      #;(string? l)))


;; == All Literal values ==
;; Integer 32 bits
(define integer? fixnum?)
;; Character
(define character? char?)
;; Float
(define float? flonum?)
;; String
;; (define string? string?)

(define (variable? v)
  (symbol? v))

(define (primitive? p)
  (memq p '(%!integer+ %!float+)))

#;(define-language KleinS
  (terminals
   (variable (x))
   (primitive (p))
   (constant (c)))
  (Expr (e body)
        x
        p
        c
        (lambda (x) body)
        (e1 e2)))
