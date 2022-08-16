#lang nanopass

(require (for-syntax syntax/parse
                     racket/list
                     racket/sequence)
         racket/syntax
         racket/format
         (prefix-in graph: graph)
         "list-set.rkt"
         "languages.rkt"
         "typing.rkt"
         "utils.rkt")


(define-formatted error)


;; ------------------------------------------------
;; Compiler parameters

;; When trace-passes is truthy each pass in the framework will
;; display its result.
;; This is useful for debugging and demonstrations.
(define trace-passes (make-parameter #false))

;; When `until-pass` is a number N, the compiler will run until it has
;; performed N passes.
;; When `until-pass` is a symbol P, it will run the compiler until the
;; pass P has been performed. NOTE, it will first run P and then break.
;; Otherwise, no alterations.
(define pass-until (make-parameter #false))


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
    [(lambda ,[alt] ,[alt*] ...)
     (define fresh-name (lambda-id))
     `(letrec ((procedure ,fresh-name ,alt ,alt* ...)) ,fresh-name)])
  (Alternative : Alternative (ir) -> Alternative ()
    [((,[pat] ...) ,[df*] ... ,[body0])
    `((,pat ...) (letrec (,df* ...) ,body0))])
  (Definition : Definition (ir) -> Definition ()
    [(defvar ,var ,[e]) `(variable ,var ,e)]
    [(defun ,var ,[alt] ,[alt*] ...) `(procedure ,var ,alt ,alt* ...)])
  (Program : Program (ir) -> Program ()
    [(,[df*] ... ,[e]) `((letrec (,df* ...) ,e))]))


(define-pass check-unbound-vars : K1 (ir) -> K1 ()
  (definitions
    (define (combine ls)
      (apply list-union ls))
    (define (extract-def-var d)
      (nanopass-case (K1 Definition) d
        [(variable ,var ,e) var]
        [(procedure ,var ,alt ,alt* ...) var]
        [else #false])))
  (Expr : Expr (ir) -> Expr ('())
        [,var (values var (list var))]
        [(,[e0 uses0] ,[e1 uses*] ...)
         (values `(,e0 ,e1 ...)
                 (combine (list* uses0 uses*)))]
        [(letrec (,[df used*] ...) ,[body used0])
         (define bound (filter-map extract-def-var df))
         (when (list-duplicates? bound)
           (error
            "Declarations at the same level may not shadow each other"
            bound))
         (values `(letrec (,df ...) ,body)
                 (list-diff (combine (list* used0 used*))
                            bound))])
  (Definition : Definition (ir) -> Definition ('())
    [(variable ,var ,[e used])
     (values `(variable ,var ,e) used)]
    [(procedure ,var ,[alt used0] ,[alt* used*] ...)
     (values `(procedure ,var ,alt ,alt* ...)
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
              (error
               (string-join
                (map (curry format "Unbound identifier: ~a")
                     used)
                "\n")))
            `(,e)]))


;; TODO this doesn't /need/ to be its own pass
(define-pass remove-empty-letrec : K1 (ir) -> K1 ()
  (Expr : Expr (ir) -> Expr ()
        [(letrec () ,[body]) body]))

;; Binding group refinement is a step that will allow mutually recursive
;; functions to be typechecked together, but keep as much separation as
;; possible in order to infer the most general type.
;; Example:
;;
;; ```scheme
;; (defun add
;;   [(x y) (+ x y)])
;; (add 1 2)
;; (add 1.0 2.5)
;; ```
;;
;; This above example should still typecheck because add is of type
;; (: (=> Num a) (-> a a a))
;;
;; 1. Gather used variables within a let body and build dependency graph
;; 2. Find the strongly connected components for bindings in a Let
;; 3. Within an SCC order the elements topologically
;; 4. Order the components topologically
;; NOTE this pass is needlessly expensive and could be optimized.
(define-pass refine-binding-groups : K1 (ir) -> K2 ()
  (definitions
    ;; Gather the usages within a language form
    (define (used-vars-def df)
      (nanopass-case (K2 Definition) df
        [(variable ,var ,e) (used-vars-expr e)]
        [(procedure ,var ,alt0 ,alt* ...)
        (apply list-union (map used-vars-alt (list* alt0 alt*)))]))
    (define (used-vars-expr e)
      (nanopass-case (K2 Expr) e
        [,var (list var)]
        [(,e0 ,e1 ...)
        (apply list-union (map used-vars-expr (cons e0 e1)))]
        [(letrec ((,df ...) ...) ,body)
        (map (lambda (dfs) (map used-vars-def dfs)) df)]
        [else '()]))
    (define (used-vars-alt alt)
      (define (pattern-vars p)
        (nanopass-case (K2 Pattern) p
          [,var var]
          [else #false]))
      (nanopass-case (K2 Alternative) alt
        [((,pat ...) ,body)
        (list-diff (used-vars-expr body)
                    (filter-map pattern-vars pat))]))
    (define (defined-var df)
      (nanopass-case (K2 Definition) df
        [(variable ,var ,e) var]
        [(procedure ,var ,alt ,alt0* ...) var])))
  (Expr : Expr (ir) -> Expr ()
        [(letrec (,[df] ...) ,[body])
         ;; Connecting everything to the sink will keep single
         ;; bound variables within the bindings as well.
         (define $sink (gensym '*SINK*))
         (define dependency-graph
           (let* ([g (graph:unweighted-graph/directed '())])
             (for* ([df (in-list df)]
                    [v (in-list (cons $sink
                                      (filter-not
                                       primitive?
                                       (used-vars-def df))))])
               (define bound-var (defined-var df))
               (graph:add-directed-edge! g bound-var v))
             g))
         (define sccs-topo
           (let* ([sccs (graph:scc dependency-graph)]
                  [g (graph:unweighted-graph/directed '())])
             (for* ([(scc1 i) (in-indexed sccs)]
                    [(scc2 j) (in-indexed sccs)]
                    #:unless (= i j)
                    [v1 (in-list scc1)]
                    [v2 (in-list scc2)]
                    #:when (graph:has-edge? dependency-graph v1 v2))
               ;; purposfully transposed
               (graph:add-directed-edge! g j i))
             (map (curry list-ref sccs) (graph:tsort g))))
         (define df*
           (for/list ([scc (in-list sccs-topo)]
                      #:unless (memq $sink scc)
                      #:do [(define l (filter-map
                                       (lambda (id)
                                         (findf (compose (curry symbol=? id)
                                                         defined-var) df)) scc))]
                      #:unless (null? l))
             l))
         `(letrec ((,df* ...) ...) ,body)]))

;; This phase transforms the previously "Expression-based" syntax,
;; to a list of simple binding forms. This is suitable for a full
;; module typechecking and (if-applicable) will bind the resulting
;; expression into a `main` procedure.
;; FIXME the entry of main and a module specification needs to
;; be better extended, but hopefully nothing too crazy changes.
(define-pass transform-to-binding : K2 (ir) -> K3 ()
  (definitions
    (define (letrec? e)
      (nanopass-case (K3 Expr) e
        [(letrec ((,df* ...) ...) ,body) (cons 'letrec (cons df* body))]
        [else (cons 'expr e)])))
  (Definition : Definition (ir) -> Definition ()
    [(variable ,var ,[e]) `(bind ,var (() ,e))]
    [(procedure ,var ,[alt] ,[alt*] ...)
     `(bind ,var ,alt ,alt* ...)])
  (Expr : Expr (ir) -> Expr ()
    [(,[e0] ,[e1] ...)
     (let loop ([exprs (cons e0 e1)])
       (match exprs
         [(list e0 e1) `(,e0 ,e1)]
         [(list e0 e1 e2 ...)
          (loop (cons `(,e0 ,e1) e2) )]))])
  (Program : Program (ir) -> Program ()
    ;; If there exists previous binding forms at the top-level
    ;; we don't want to push them down
    ;; But the last expression (for now) needs to get pushed
    ;; into a binding, here I'll call it "result" but really
    ;; we need either no expr, or a main. XXX
    [((letrec ((,[df] ...) ...) ,[body]))
    (define main (gensym 'result))
    (define df* (list* df (list `((((bind ,main (() ,body))))))))
    `(((,df* ...) ...) ...)]
    [(,[e])
     (define main (gensym 'result))
     `((((bind ,main (() ,e)))))]))

;; Typechecking pass sequestered in `typing.rkt`.
#;(define-pass typecheck-K3 : K3 (ir) -> K3 () ...)

(define-syntax (make-compiler stx)
  (syntax-parse stx
    [(_ kc:id (pass printer) ...)
     (with-syntax ([final-p (last (syntax->list #'(printer ...)))])
       #`(define (kc src)
           (#,(for/foldr ([next-phase #'final-p])
                         ([pass* (in-syntax #'(pass ...))]
                          [printer* (in-syntax #'(printer ...))]
                          [idx (in-naturals)])
                #`(lambda (curr-ir)
                    (define next-ir (#,pass* curr-ir))
                    (when (trace-passes)
                      (begin
                        (display (string-join
                                  (list "[pass]"
                                        (~a '#,pass*
                                            #:align 'left
                                            #:width 20
                                            #:pad-string " ")
                                        ": ") " "))
                        (displayln (#,printer* next-ir))))
                    (#,next-phase next-ir))) src)))]))

;; ------------------------------------------------
;; Main compiler passes

;; TODO create a parser or use the parse-K0 as a language parser
;; that then gives control to `kleinc`.

(make-compiler
 kleinc
 (remove-defines unparse-K1)
 (check-unbound-vars unparse-K1)
 (remove-empty-letrec unparse-K1)
 (refine-binding-groups unparse-K2)
 (transform-to-binding unparse-K3)
 (typecheck-K3 (lambda (v) v)))

(module+ test
  (require rackunit)
  (define parse-src parse-K0)
  (define (parse-and-run dtm) (kleinc (parse-src dtm)))
  (define-syntax-rule (test-fail? cd ...)
    (check-exn exn:fail? (lambda () (parse-and-run (quote (cd ...))))))
  (define-syntax-rule (test-success? cd ...)
    (check-not-exn (lambda () (parse-and-run (quote (cd ...))))))

  ;; (test-success?
  ;;  10)

  ;; (test-success?
  ;;  (defvar x 10)
  ;;  x)

  ;; (test-fail?
  ;;  y)

  (parameterize ([trace-passes #true])
    (test-success?
     (#%int+ 1 2)))

  ;; (test-success?
  ;;  (defun zero [(z) 0])
  ;;  (zero 100))

  ;; (test-success?
  ;;  (defvar x 10)
  ;;  (defvarλ y 3)
  ;;  (#%int+ x ((lambda [(0) 0]
  ;;               [(n) 1]) 1)))

  ;; (test-success?
  ;;  (defvar x 10)
  ;;  (defvar y 3)
  ;;  (#%int+ x ((lambda [(0) 0]
  ;;               [(n) 1]) y)))

  ;; (test-fail?
  ;;  (defvar x 10)
  ;;  (#%int+ x ((lambda [(0) 0]
  ;;               [(n) 1]) y)))

  ;; (test-fail?
  ;;  (#%int+ 4 z))

  ;; (test-fail?
  ;;  (defun f [(n) n])
  ;;  (g 10))

  ;; (test-fail?
  ;;  (defun f [(n) o])
  ;;  (f 10))

  ;; (test-success?
  ;;  (defvar a 10.0)
  ;;  (defvar b 5.0)
  ;;  (defvar c 2.5)
  ;;  ((lambda [(0 0 0) 0]
  ;;     [(0 y 0) y]
  ;;     [(x 0 0) x]
  ;;     [(0 0 z) z]
  ;;     [(x y z) (#%float+ x y z)]) a b c))

  ;; (test-fail?
  ;;  (defvar a 10.0)
  ;;  (defvar b 5.0)
  ;;  (defvar c 2.5)
  ;;  ((lambda [(0 0 0) 0]
  ;;     [(0 y 0) x]
  ;;     [(x 0 0) x]
  ;;     [(0 0 z) z]
  ;;     [(x y z) (#%float+ x y z)]) a b c))

  ;; (test-fail?
  ;;  (defvar a 10)
  ;;  (defun a [n n])
  ;;  a)

  ;; (test-success?
  ;;  (defvar a 10)
  ;;  (defun id [(a) a])
  ;;  (id a))

  ;; (test-success?
  ;;  (defvar a 10.0)
  ;;  (defvar b 5.0)
  ;;  (defvar c 2.5)
  ;;  ((lambda [(0 0 0) 0]
  ;;     [(0 y 0) b]
  ;;     [(x 0 0) x]
  ;;     [(0 0 z) z]
  ;;     [(x y z) (#%float+ x y z)]) a b c))

  ;; (test-success?
  ;;  (defun even?
  ;;    [(0) #true]
  ;;    [(n) (odd? (#%int+ n -1))])
  ;;  (defun odd?
  ;;    [(0) #false]
  ;;    [(n) (even? (#%int+ n -1))])
  ;;  (even? 100))

  ;; (test-success?
  ;;  (defun foo
  ;;    [(0) (bar 0)]
  ;;    [(n) (baz 0)])
  ;;  (defun baz
  ;;    [(0) (bar 0)]
  ;;    [(n) (baz 0)])
  ;;  (defun bar
  ;;    [(n) n]
  ;;    [(n) (baz 0)])
  ;;  (bar 100))

  ;; (test-success?
  ;;  (defun foo
  ;;    [(0) (bar 0)]
  ;;    [(1) (#%int+ 1 1)])
  ;;  (defun bar
  ;;    [(0) (bar (#%int+ 1 1))]
  ;;    [(1) (foo (#%int+ 1 1))])
  ;;  (defun baz
  ;;    [(0) 0]
  ;;    [(n) (foo n)])
  ;;  ;;
  ;;  (defun xee
  ;;    [(0) 0]
  ;;    [(n) (xee n)])
  ;;  (bar (xee 0)))

  ;; (test-success?
  ;;  (defvar a 10)
  ;;  (defvar b 5)
  ;;  (defun add-a
  ;;    [(x) (#%int+ a x)])
  ;;  (add-a b))

  ;; ;; TODO Typechecking failures

  ;; (test-success?
  ;;  (defun add4
  ;;    [(a b c d) (#%int+ a b c d)])
  ;;  (add4 1 2 3 4))

  ;; (test-fail?
  ;;  (defvar x 10)
  ;;  (defvar y 5)
  ;;  (defvar x 5)
  ;;  (#%int+ x y))

  #;(test-fail?
   (0 1))

  #;(test-fail?
   (defvar x 0)
   (defvar y 1.5)
   (#%int+ x y)))
