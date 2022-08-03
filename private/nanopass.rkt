#lang nanopass

(require (for-syntax syntax/parse
                     racket/list
                     racket/sequence)
         racket/syntax
         "list-set.rkt"
         "languages.rkt"
         "utils.rkt")


(define-formatted error)


;; When trace-passes is truthy each pass in the framework will
;; display its result. This is useful for debugging and demonstrations.
(define trace-passes
  (make-parameter #false))


;; ------------------------------------------------
;; Utilities


(define lambda-id
  (let ([c -1])
    (lambda () (set! c (add1 c))
      (format-symbol "lambda:~a" c))))


;; ------------------------------------------------
;; This file contains the Klein language passes

(define-pass remove-defines : K0 (ir) -> K1 ()
  (Expr : Expr (ir) -> Expr ()
    [(lambda ,[alt*] ... ,[alt])
     (define fresh-name (lambda-id))
     `(letrec ((,fresh-name ,alt* ... ,alt)) ,fresh-name)])
  (Alternative : Alternative (ir) -> Alternative ()
    [((,[pat] ...) ,[df*] ... ,[body0])
    `((,pat ...) (letrec (,df* ...) ,body0))])
  (Definition : Definition (ir) -> Definition ()
    [(define ,var ,[e]) `(,var ,e)]
    [(define ,var ,[alt*] ... ,[alt]) `(,var ,alt* ... ,alt)])
  (Program : Program (ir) -> Program ()
    [(,[df*] ... ,[e]) `((letrec (,df* ...) ,e))]))


(define-pass check-unbound-vars : K1 (ir) -> K1 ()
  (definitions
    (define (combine ls)
      (apply list-union ls))
    (define (extract-def-var d)
      (nanopass-case (K1 Definition) d
        [(,var ,e) var]
        [(,var ,alt* ... ,alt) var]
        [else #false])))
  (Expr : Expr (ir) -> Expr ('())
        [,var (values var (list var))]
        [(,[e0 uses0] ,[e1 uses*] ...)
         (values `(,e0 ,e1 ...)
                 (combine (list* uses0 uses*)))]
        [(letrec (,[df used*] ...) ,[body used0])
         (define bound (filter-map extract-def-var df))
         (values `(letrec (,df ...) ,body)
                 (list-diff (combine (list* used0 used*))
                            bound))])
  (Definition : Definition (ir) -> Definition ('())
    [(,var ,[e used])
     (values `(,var ,e) used)]
    [(,var ,[alt* used*] ... ,[alt used0])
     (values `(,var ,alt* ... ,alt)
             (list-diff (combine (list* used0 used*))
                        (list var)))])
  (Pattern : Pattern (ir) -> Pattern ('())
           [,var (values var (list var))])
  (Alternative : Alternative (ir) -> Alternative ('())
               [((,[pat bound] ...) ,[body used])
                (values `((,pat ...) ,body)
                        (list-diff used (combine bound)))])
  (Program : Program (ir) -> Program ()
           [(,[e used*])
            ;; HACK All primitives need to be removed from the list
            ;; of unbound variables. This should theoretically be
            ;; handled by the language pass already but it isn't.
            (define used (filter-not primitive? used*))
            (unless (null? used)
              (error (string-join (map (curry format "Unbound identifier: ~a")
                                       used)
                                  "\n")))
            `(,e)]))


(define-pass remove-empty-letrec : K1 (ir) -> K1 ()
  (Expr : Expr (ir) -> Expr ()
        [(letrec () ,[body]) body]))

;; [ ] TODO group letrec bindings better (SCCs)

;; Is there anything else that should happen /before/ tyepchecking?
;; e.g. rename variables?

;; [ ] TODO typechecking phase
;; This will involve rewriting the typechecker (again ...) to use
;; the nanopass forms when destructuring. This will be much easier to
;; integrate rather than useing separate structs which need to be
;; converted to / from.

(define-syntax (make-compiler stx)
  (syntax-parse stx
    [(_ kc:id (pass printer) ...)
     (with-syntax ([final-p (last (syntax->list #'(printer ...)))])
       #`(define (kc src)
           (#,(for/foldr ([next-phase #'final-p])
                         ([pass* (in-syntax #'(pass ...))]
                          [printer* (in-syntax #'(printer ...))])
                #`(lambda (curr-ir)
                    (define next-ir (#,pass* curr-ir))
                    (when (trace-passes)
                      (displayln (#,printer* next-ir)))
                    (#,next-phase next-ir))) src)))]))

;; ------------------------------------------------
;; Main compiler passes

;; TODO create a parser or use the parse-K0 as a language parser
;; that then gives control to `kleinc`.

(make-compiler
 kleinc
 (remove-defines unparse-K1)
 (check-unbound-vars unparse-K1)
 (remove-empty-letrec unparse-K1))

(module+ test
  (require rackunit)
  (define parse-src parse-K0)
  (define (parse-and-run dtm) (kleinc (parse-src dtm)))
  (define-syntax-rule (test-fail? cd ...)
    (check-exn exn:fail? (lambda () (parse-and-run (quote (cd ...))))))
  (define-syntax-rule (test-success? cd ...)
    (check-not-exn (lambda () (parse-and-run (quote (cd ...))))))

  (test-success?
   10)

  (test-success?
   (define x 10)
   x)

  (test-fail?
   y)

  (test-success?
   (#%int+ 1 2))

  (test-success?
   (define x 10)
   (define y 3)
   (#%int+ x ((lambda [(0) 0]
                [(n) 1]) 1)))

  (test-success?
   (define x 10)
   (define y 3)
   (#%int+ x ((lambda [(0) 0]
                [(n) 1]) y)))

  (test-fail?
   (define x 10)
   (#%int+ x ((lambda [(0) 0]
                [(n) 1]) y)))

  (test-fail?
   (#%int+ 4 z))

  (test-fail?
   (define f [(n) n])
   (g 10))

  (test-fail?
   (define f [(n) o])
   (f 10))

  (test-success?
   (define a 10.0)
   (define b 5.0)
   (define c 2.5)
   ((lambda [(0 0 0) 0]
      [(0 y 0) y]
      [(x 0 0) x]
      [(0 0 z) z]
      [(x y z) (#%float+ x y z)]) a b c))

  (test-fail?
   (define a 10.0)
   (define b 5.0)
   (define c 2.5)
   ((lambda [(0 0 0) 0]
      [(0 y 0) x]
      [(x 0 0) x]
      [(0 0 z) z]
      [(x y z) (#%float+ x y z)]) a b c))

  (test-success?
   (define a 10.0)
   (define b 5.0)
   (define c 2.5)
   ((lambda [(0 0 0) 0]
      [(0 y 0) b]
      [(x 0 0) x]
      [(0 0 z) z]
      [(x y z) (#%float+ x y z)]) a b c))

  (test-success?
   (define even?
     [(0) #true]
     [(n) (odd? (#%int+ n -1))])
   (define odd?
     [(0) #false]
     [(n) (even? (#%int+ n -1))])
   (even? 100)))
