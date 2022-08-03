#lang nanopass

(require racket/struct)

(provide
 ;; Languages and their parsers
 K0 parse-K0 unparse-K0
 K1 parse-K1 unparse-K1

 ;; Primitives
 primitive?
 ;; Literal predicates
 integer? float? character? #;string? literal?
 )

;; ------------------------------------------------
;; Klein high-level language constructs
;; TODO remove

;; TODO expressions are currently a subset of what should be available in Klein.
(struct expression ())
(struct expr-var expression (id)
  #:transparent #:sealed
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (o) 'VarE)
      (lambda (o) (list (expr-var-id o)))))])

(struct expr-lit expression (lit)
  #:transparent
  #:sealed
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (o) 'LitE)
      (lambda (o) (list (expr-lit-lit o)))))])

(struct expr-const expression (assumpt)
  #:transparent
  #:sealed)

(struct expr-app expression (e1 e2)
  #:transparent
  #:sealed)

(struct expr-let expression (bg e)
  #:transparent
  #:sealed
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (o) 'LetE)
      (lambda (o) (list (expr-let-bg o)
                   (expr-let-e o)))))])

;; Patterns may occur on the left hand side of a function declaration. Here,
;; values may be destructured.
;; TODO support the full slew of patterns.
(struct pattern ())
(struct pat-id pattern (id)
  #:transparent
  #:sealed
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (o) 'IdP)
      (lambda (o) (list (pat-id-id o)))))])

(struct pat-lit (lit)
  #:transparent
  #:sealed
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (o) 'LitP)
      (lambda (o) (list (pat-lit-lit o)))))])

;; An alternative is used to bind a list of function binding patterns (left hand sides)
;; to a cooresponding body expression (right hand side).
(struct alternative (pats expr)
  #:transparent
  #:sealed
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (o) 'Alt)
      (lambda (o) (list (alternative-pats o)
                   (alternative-expr o)))))])


(struct bind-group (expls impls)
  #:transparent
  #:sealed
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (o) 'BindGroup)
      (lambda (o) (list (bind-group-expls o)
                   (bind-group-impls o)))))])

;; For a given list of explicit bindings,
;;
;; Example: given a group of explicitly typed bindings `es`, impls would be a
;; list of implicitly typed bindings of the form `im_0, im_1, ..., im_n`. An
;; implicit bindings `im_i` should only depend on those bindings in es or `im_j`
;; such that `0 <= j && j < i`.
(struct bg-explicit (id scm alts)
  #:transparent
  #:sealed)

#;(define explicit/c
  (struct/dc bg-explicit
             [id ...]
             [scm ...]
             [alts ...]))

(struct bg-implicit (id alts)
  #:transparent
  #:sealed)

(define implicit/c
  (struct/dc bg-implicit
             [id symbol?]
             [alts (listof alternative?)]))


(struct ambiguity (tv ps)
  #:transparent
  #:sealed)

;; ------------------------------------------------
;; KleinS Base Language

(define (literal? l)
  (or (integer? l)
      (float? l)
      (character? l)
      (boolean? l)
      #;(string? l)))

;; ------------------------------------------------
;; All literal values

(define integer? fixnum?) ;; Integer 32 bits
(define character? char?) ;; Character
(define float? flonum?)   ;; Float
;; (define string? string?)  ;;String

(define variable? symbol?)

(define (primitive? p)
  (memq p '(#%int+ #%float+)))

;; XXX the initial Klein `K_0` source language, this is expected to
;; change  but subsequent changes shouldn't be too large.
(define-language K0
  (entry Program)
  (terminals (variable (var))
             (primitive (prim))
             (literal (lit)))
  (Expr (e body)
        prim
        var
        lit
        (lambda alt* ... alt)
        (e0 e1 ...))
  (Pattern (pat) ;; TODO expand the full set of patterns
           var
           lit)
  (Alternative (alt)
               ((pat ...) df* ... body0))
  (Definition (df)
              (define var e)
              (define var alt* ... alt))
  ;; TODO a "program" should really be a module. Each module
  ;; /may/ have its own entry point but any program that interfaces
  ;; with OCaml must have exactly one entry (named properly).
  ;; This distinction can be made later though.
  (Program (prog)
           ;; Should have a:
           ;; - module name
           ;; - list of imports
           ;; - interface list
           ;; ...
           (df* ... e)))

;; Remove definitions and turn them into `Let` expressions.
;; This is happening fairly early on, but the goal until typed
;; languages is to turn things into a language the typechecker
;; understands (which define is not).
(define-language K1
  (extends K0)
  (Expr (e body)
        (- (lambda alt* ... alt))
        (+ (letrec #;() ;; TODO add explicitly typed bindings
               (df ...)
             body0)))
  (Alternative (alt)
               (- ((pat ...) df* ... body0))
               (+ ((pat ...) body)))
  (Definition (df)
              (- (define var e)
                 (define var alt* ... alt))
              (+ (var e)
                 (var alt* ... alt)))
  (Program (prog)
           (- (df* ... e))
           ;; Keep the expression in double parens because
           ;; later this will still be a module definition.
           (+ (e))))

;; ------------------------------------------------
;; Typed languages

;; TODO type checking should use nanopass-case form
;; to nicely interact with the languages level.

(define-parser parse-K0 K0)
(define-parser parse-K1 K1)

(module+ test

  (parse-K0 '((define x 10)
              (define y 3)
              (define f
                [(0) 0]
                [(n) 1])
              ((#%int+ x) (f 1))))

  (parse-K0 '((define x 10)
              (define y 3)
              (#%int+ x ((lambda [(0) 0]
                           [(n) 1]) 1))))

  (parse-K1 '(let ([x 10]
                   [y 3]
                   [f [(0) 0]
                      [(n) 1]])
               (#%int+ x (f 1))))

  (parse-K1 '((define x 10)
              (define y 3)
              (#%int+ x ((lambda [(0) 0]
                           [(n) 1]) 1)))))
