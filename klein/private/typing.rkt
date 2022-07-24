#lang racket/base

(require (for-syntax racket/base
                     syntax/parse)
         racket/contract
         racket/function
         racket/list
         racket/match
         racket/set
         racket/struct

         ;; TODO get rid of the monadic interface and use macros instead. Use of
         ;; macros wil also gain you syntax highlighting + many other things in DrRacket.
         (prefix-in df: data/functor)
         (prefix-in da: data/applicative)
         data/monad
         data/either
         (prefix-in r: racket/base)

         "list-set.rkt"
         "languages.rkt")

(module+ test (require rackunit))

;; A Star kind represents nullary (simple) types. E.g. Int, FLoat, Char, ...
;; A KFun represents a type constructor from k1 -> k2
(struct kind ())
(struct %#kind-star kind ()
  #:transparent
  #:sealed
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (o) 'StarK)
      (lambda (o) '())))])
(struct kind-fun kind (k1  k2)
  #:transparent
  #:sealed
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (o) 'ArrowK)
      (lambda (o) (list (kind-fun-k1 o)
                   (kind-fun-k2 o)))))])
;; Only one Star kind is required
(define kind-star (%#kind-star))
(define (kind-star? s)
  (eq? s kind-star))

(struct type ())
(struct type-variable type (id k)
  #:transparent
  #:sealed
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (o) 'VarT)
      (lambda (o) (list (type-variable-id o)
                   (type-variable-k o)))))])

(struct type-const type (id k)
  #:transparent
  #:sealed
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (o) 'ConstT)
      (lambda (o) (list (type-const-id o)
                   (type-const-k o)))))])
(struct type-app type (t1 t2)
  #:sealed
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (o) 'AppT)
      (lambda (o) (list (type-app-t1 o)
                   (type-app-t2 o)))))])
(struct type-gen type (hsh)
  #:sealed
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (o) 'GenT)
      (lambda (o) (list (type-gen-hsh o)))))])

;; Representation of a `qualified` type. The head represents a type? that must
;; fulfil the list of predicates.
(struct qualified type (predicates head)
  #:transparent
  #:sealed
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (o) 'Qualified)
      (lambda (o) (list (qualified-predicates o)
                   (qualified-head)))))])
(define (qualified/c t?)
  (and/c qualified? (compose t? qualified-head)))

;; A predicate of the form id t states that type? `t` is a member of class `id`.
(struct predicate type (id t #;type?)
  #:transparent
  #:sealed
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (o) 'Predicate)
      (lambda (o) (list (predicate-t o)
                   (predicate-id o)))))])

;; A type scheme relates all universally quantified  variables in the qualified
;; types with a kind in `kinds`. These variables are ordered and the nth
;; variables has type scheme `(list-ref kinds n)`.
(struct scheme type (kinds qs)
  #:transparent
  #:sealed)

(struct tclass type (ids ints)
  #:transparent
  #:sealed)

(struct assumption type (id scheme)
  #:transparent
  #:sealed)

;; Class environments partially map ids to class values.
(struct tclass-env (classes defaults))

;; TODO expressions are currently a subset of what should be available in Klein.
(struct expression ())
(struct expr-var expression (id)
  #:transparent
  #:sealed)

(struct expr-lit expression (lit)
  #:transparent
  #:sealed)

(struct expr-const expression (assumpt)
  #:transparent
  #:sealed)

(struct expr-app expression (e1 e2)
  #:transparent
  #:sealed)

(struct expr-let expression (bg e)
  #:transparent
  #:sealed)

;; Patterns may occur on the left hand side of a function declaration. Here,
;; values may be destructured.
;; TODO support the full slew of patterns.
(struct pattern ())
(struct pat-id pattern (id)
  #:transparent
  #:sealed)

;; An alternative is used to bind a list of function binding patterns (left hand sides)
;; to a cooresponding body expression (right hand side).
(struct alternative (pats expr)
  #:transparent
  #:sealed)

(struct bind-group (expls impls))
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
             [id string?]
             [alts (listof alternative?)]))


(struct ambiguity (tv ps)
  #:transparent
  #:sealed)

;; Contract for results that could fail, all results must include a message
;; describing why the computation failed. This probably should be augmented in
;; the future to include value / syntax information allowing the error engine to
;; produce cohesive messages to the user.
(define (result/c ctc) (either/c string? ctc))
(define subst/c (listof pair?))

;; Type Inference monad for passing state (currently a single substitution TODO)
;; TI also embeds a result (failure / success) to signify type checking
;; errors.
(struct TI (proc)
  #:transparent
  #:sealed
  #:methods df:gen:functor
  [(define (map f x)
     (TI (lambda (s)
           (define t ((TI-proc x) s))
           (cons (car t) (df:map f (cdr t))))))]
  #:methods da:gen:applicative
  [(define (pure _ x) (->TI x))
   (define (apply f xs)
     (do [g <- f]
         [args <- (map/m values xs)]
         (->TI (r:apply g args))))]
  #:methods gen:monad
  [(define (chain f x)
     (TI (lambda (s)
           (match-define (TI fx) x)
           (match (fx s)
             [(cons st (success v))
              (match-let ([(TI fg) (f v)])
                (fg st))]
             [oth oth]))))])

;; Helpers for working with a Type Inference state
(define (->TI x) (TI (lambda (s) (cons s (success x)))))
(define (get-state) (TI (lambda (s) (cons s (success s)))))
(define/contract (<-TI ti)
  (TI? . -> . (result/c any/c))
  (match-define (TI f) ti)
  (cdr (f empty-subst)))
(define/contract (ext-state sp)
  (subst/c . -> . TI?)
  (TI (lambda (s) (cons (sp . @@ . s) (success 'dummy)))))
(define/contract (fail/m msg)
  (string? . -> . TI?)
  (TI (lambda (s) (cons s (failure msg)))))
(define-syntax (sequence/m stx)
  (syntax-case stx ()
    [(_ f ms ...)
     #'(map/m (curry apply f) (map list ms ...))]))

(module+ test
  (define-syntax (check-success? stx)
    (syntax-parse stx
      [(_ f:expr s:expr) #'(check-equal? f (success s))]))
  (define-syntax (check-fail? stx)
    (syntax-parse stx
      [(_ f:expr) #'(let ([v f]) (check-pred failure? v))]))

  (define (push-state e) (TI (lambda (s) (cons (cons e s) (success (void))))))
  (define (%add x y) (->TI (+ x y)))

  (check-success? (<-TI (->TI 0)) 0)
  (check-success? (<-TI (df:map (compose add1 add1) (->TI 0))) 2)
  (check-success? (<-TI ((->TI identity) (->TI 0))) 0)
  (check-success? (<-TI ((->TI add1) (->TI 0))) 1)
  (check-success? (<-TI (((->TI compose) (->TI add1) (->TI add1)) (->TI 0))) 2)
  (check-success? (<-TI (do (->TI 0)
                            (push-state 0)
                            (push-state 1)
                            (push-state 2)
                            (get-state))) '(2 1 0))
  (check-success? (<-TI (sequence/m %add '(1 2 3) '(3 2 1)))
                  '(4 4 4))
  (check-fail? (<-TI (do [x <- (->TI 0)]
                         [y <- (%add x x)]
                         [z <- (fail/m "whoops!")]
                         (%add z y)))))

;; ;; -------------------------

(define-syntax (def-ty-prim x)
  (syntax-case x ()
    [(_ pattern name)
     (with-syntax ([%name #'name]
                   [%pat #'pattern])
       #'(define %name (type-const %pat kind-star)))]))

(define-syntax (def-ty-arr x)
  (syntax-case x ()
    [(_ pattern name)
     (with-syntax ([%name #'name]
                   [%pat #'pattern])
       #'(define %name (type-const %pat (kind-fun kind-star kind-star))))]))

(def-ty-prim "()" %unit)
(def-ty-prim "Char" %char)
(def-ty-prim "Int" %int)
(def-ty-prim "Float" %float)

(def-ty-arr "[]" %list)
(def-ty-arr "(->)" %arrow)
(def-ty-arr "(,)" %tuple2)

(define-syntax ($make-func stx)
  (syntax-case stx ()
    [(_ a b) #'(type-app (type-app %arrow a) b)]
    [(_ a b ...) #'(type-app (type-app %arrow a) ($make-func b ...))]))

(define-syntax ($make-list stx)
  (syntax-case stx ()
    [(_ a) #'(type-app %list a)]))

(define-syntax ($make-pair stx)
  (syntax-case stx ()
    [(_ a b) #'(type-app (type-app %tuple2 a) b)]))

(define (get-kind t)
  (match t
    [(type-variable _ k) k]
    [(type-const _ k) k]
    [(type-app t1 _) (kind-fun-k1 (get-kind t1))]))

(define (genid)
  (symbol->string (gensym)))

;; Kind substitutions
;; Substitution map is represented using association lists

(define empty-subst '())
(define/contract (+-> u t)
  (type-variable? type? . -> . subst/c)
  (list (cons u t)))

(define/contract (substitute sub t)
  (subst/c (or/c (listof type?) type?) . -> . (or/c (listof type?) type?))
  (cond [(list? t) (map (curry substitute sub) t)]
        ;; Singleton case
        [else (match t
                [(type-variable _ _)
                 (match (assoc t sub)
                   [#false t]
                   [(cons _ ty) ty])]
                [(type-app t1 t2) (type-app (substitute sub t1)
                                            (substitute sub t2))]
                [(qualified ps head)
                 (qualified (substitute sub ps)
                            (substitute sub head))]
                [(predicate i t) (predicate i (substitute sub t))]
                [(scheme ks qt) (scheme ks (substitute sub qt))]
                [(assumption i ts) (assumption i (substitute sub ts))]
                [else t])]))

(define/contract (get-type-vars t0)
  ((or/c (listof type?) type?) . -> . (listof type?))
  (define (tv t)
    (cond [(list? t) (apply list-union (map tv t))]
          [else (match t
                  [(type-variable _ _) (list t)]
                  [(type-app l r) (list-union (tv l) (tv r))]
                  [(qualified ps head) (list-union (tv ps)
                                                   (tv head))]
                  [(predicate _ t) (tv t)]
                  [(scheme _ qt) (tv qt)]
                  [(assumption _ ts) (tv ts)]
                  [else (list)])]))
  (tv t0))

;; @@ is the infix operator for substitution composition
(define/contract (@@ s1 s2)
  (subst/c subst/c . -> . subst/c)
  (let ([ls (for/list ([tup (in-list s2)])
              (match-let ([(cons u t) tup])
                (cons u (substitute s1 t))))])
    (append ls s1)))

(define/contract (merge s1 s2)
  (subst/c subst/c . -> . (result/c subst/c))
  (define (heads ls) (map car ls))
  (define (list-intersect l1 l2)
    (set->list (set-intersect (list->set l1)
                              (list->set l2))))
  (let ([agreeable (andmap (lambda (v) (equal? (substitute s1 v)
                                               (substitute s2 v)))
                           (list-intersect (heads s1) (heads s2)))])
    (if agreeable
        (success (append s1 s2))
        (failure "merge fail"))))

;; Unification

(define/contract (most-general-unifier t1 t2)
  (type? type? . -> . (result/c subst/c))
  (match (cons t1 t2)
    [(cons (predicate i t) (predicate ii tt))
     #:when (equal? i ii)
     (most-general-unifier t tt)]
    [(cons (type-app ll rl) (type-app lr rr))
     (do [s1 <- (most-general-unifier ll lr)]
         [s2 <- (most-general-unifier lr rr)]
       (success (s2 . @@ . s1)))]
    [(cons u t)
     #:when (type-variable? u)
     (bind-variable u t)]
    [(cons t u)
     #:when (type-variable? u)
     (bind-variable u t)]
    [(cons (type-const _ tc1) (type-const _ tc2))
     #:when (equal? tc1 tc2)
     (success empty-subst)]
    [_ (failure "types do not unify")]))

(define/contract (bind-variable u t)
  (type-variable? type? . -> . (result/c subst/c))
  (cond [(and (type-variable? t)
              (equal? u t))
         (success empty-subst)]
        [(member u (get-type-vars t))
         (failure "occurs check fails")]
        [(not (equal? (get-kind u)
                      (get-kind t)))
         (failure "kinds do not match")]
        [else (success (u . +-> . t))]))

(define/contract (type-match t1 t2)
  (type? type? . -> . (result/c subst/c))
  (match (cons t1 t2)
    [(cons (predicate i t) (predicate ii tt))
     #:when (equal? i ii)
     (type-match t tt)]
    [(cons (type-app ll rl) (type-app lr rr))
     (do [le <- (type-match ll lr)]
         [re <- (type-match lr rr)]
       (merge le re))]
    [(cons u t)
     #:when (and (type-variable? u)
                 (equal? (get-kind u) (get-kind t)))
     (success (u . +-> . t))]
    [(cons (type-const _ tc1) (type-const _ tc2))
     #:when (equal? tc1 tc2)
     (success empty-subst)]
    [else (failure "types do not match")]))

;; Class environemnts

(define/contract (env-super env i)
  (tclass-env? string? . -> . (result/c (listof string?)))
  (match ((tclass-env-classes env) i)
    [(success (tclass ids _)) ids]
    [else '()]))

(define/contract (env-insts env i)
  (tclass-env? string? . -> . (listof (qualified/c predicate?)))
  (match ((tclass-env-classes env) i)
    [(success (tclass _ is)) is]
    [else '()]))

(define/contract (defined? m)
  ((either/c any/c any/c) . -> . boolean?)
  (success? m))

(define/contract (env-bind env i c)
  (tclass-env? string? tclass? . -> . tclass-env?)
  (struct-copy tclass-env env
               [classes (lambda (j)
                          (if (equal? i j)
                              (success c)
                              (tclass-env-classes env i)))]))

(define env->env/c (tclass-env? . -> . (result/c tclass-env?)))

(define empty-env
  (tclass-env (lambda (x) (failure "ID not found in class environment"))
              (list %int %float)))

(define/contract (<:> f g)
  (env->env/c env->env/c . -> . env->env/c)
  (lambda (env) (do [envp <- (f env)]
                    (g envp))))

(define/contract (env-add-class i is)
  (string? (listof string?) . -> . env->env/c)
  (lambda (env) (cond [(defined? (tclass-env-classes env i))
                       (failure "class is already defined")]
                      [(ormap (compose not defined? (curry tclass-env-classes env))
                              is)
                       (failure "superclass is not defined")]
                      [else (success (env-bind env i (tclass is '())))])))

(define/contract (env-add-inst ps p env)
  ((listof predicate?) predicate? tclass-env? . -> . (result/c tclass-env?))
  (define (overlap? p q) (defined? (most-general-unifier p q)))
  (match-define (predicate i _) p)
  (define its (env-insts env i))
  (define qs (for/list ([qd (in-list its)])
               (match-let ([(qualified _ q) qd]) q)))
  (define c (tclass (env-super env i)
                    (cons (qualified ps p) its)))
  (cond [(not (defined? (tclass-env-classes env i)))
         (failure "no class for instance")]
        [(ormap (curry overlap? p) qs) (failure "")]
        [else (success (env-bind env i c))]))

(define/contract (by-super env p)
  (tclass-env? predicate? . -> . (listof predicate?))
  (match-define (predicate i t) p)
  (define ll (for/list ([ip (in-list (env-super env i))])
               (by-super env (predicate ip t))))
  (cons p (apply append ll)))

(define/contract (by-inst env p)
  (tclass-env? predicate? . -> . (result/c (listof predicate?)))
  (match-define (predicate i t) p)
  (define try-inst
    (match-lambda [(qualified ps h)
                   (do [u <- (type-match h p)]
                       (success (map (curry substitute u) ps)))]))
  (define ll (for/list ([it (in-list (env-insts env i))])
               (try-inst it)))
  (define ls (filter success? ll))
  (if (null? ls)
      (failure "no suitable instance found")
      (success (car ls))))

;; Given a type class environment, report whether or not p
;; holds when all predicates ps are satisfied.
(define/contract (entails? env ps p)
  (tclass-env? (listof predicate?) predicate? . -> . boolean?)
  ;; predicate p is deduced by a super
  (or (ormap (curry member p) (map (curry by-super env) ps))
      ;; otherwise, for all predicates qs of a matching instance
      ;; the predicates ps must follow.
      (match (by-inst env p)
        [(failure _) #false]
        [(success qs) (andmap (curry entails? env ps) qs)])))

(define/contract (head-normal-form? prd)
  (predicate? . -> . boolean?)
  (define (r v)
    (cond [(type-variable? v) #true]
          [(type-const? v) #false]
          [(type-app? v) (r (type-app-t1 v))]
          [else (error "invalid type")]))
  (match-define (predicate c t) prd)
  (r t))

(define/contract (->head-normal-form env p)
  (tclass-env? (or/c (listof predicate?) predicate?) . -> . TI?)
  (cond [(list? p)
         (do [ps <- (map/m (curry ->head-normal-form env) p)]
             (->TI (apply append ps)))]
        [(head-normal-form? p) (->TI (list p))]
        [else (match (by-inst env p)
                [(failure _) (fail/m "context reduction")]
                [(success ps) (->head-normal-form env ps)])]))

(define/contract (simplify env ps)
  (tclass-env? (listof predicate?) . -> . (listof predicate?))
  (define (loop rs ps)
    (match ps
      [(list) rs]
      [(list p ps ...)
       #:when (entails? env (append rs ps) p)
       (loop rs ps)]
      [(list p ps ...) (loop (cons p rs) ps)]))
  (loop '() ps))

(define/contract (reduce env ps)
  (tclass-env? (listof predicate?) . -> . TI?)
  (do [qs <- (->head-normal-form env ps)]
      (->TI (simplify env qs))))

(define/contract (quantify vs qt)
  ((listof type-variable?) (qualified/c type?) . -> . scheme?)
  (define vsp
    (for/list ([v (in-list (get-type-vars qt))]
               #:when (member v vs)) v))
  (define ks (map get-kind vsp))
  (define s
    (for/list ([(v i) (in-indexed vsp)])
      (cons v (type-gen i))))
  (scheme ks (substitute s qt)))

(define/contract (type->scheme t)
  (type? . -> . scheme?)
  (scheme '() (qualified '() t)))

(define/contract (find-in-assumptions id as)
  (string? (listof assumption?) . -> . TI?)
  (match as
    [(list) (fail/m "unbound identifier")]
    [(list (assumption i ts) as ...)
     (if (equal? id i)
         (->TI ts)
         (find-in-assumptions id as))]))

(define/contract (unify t1 t2)
  (type? type? . -> . TI?)
  (do [s <- (get-state)]
      [u <- (most-general-unifier (substitute s t1)
                                  (substitute s t2))]
    (ext-state u)))

(define/contract (fresh-tv k)
  (kind? . -> . TI?)
  (->TI (type-variable (genid) k)))

(define/contract (fresh-inst tscm)
  (scheme? . -> . TI?)
  (match-define (scheme ks qt) tscm)
  ;; Instantiate a scheme with a fresh list of type variables ts and a
  ;; qualified type qt.
  (do [ts <- (map/m fresh-tv ks)]
      (->TI (instantiate ts qt))))

;; instantiate is similar to the form of "substitute" however it works by
;; instantiating generic variables of the form type-gen.
(define/contract (instantiate ts o)
  ;; Saying that the second argument and return value are any/c is inaccurate
  ;; but it will be sufficient for now. Ideally, this should restrict the second
  ;; param `t` to be something "instantiatable".
  ((listof type?) any/c . -> . any/c)
  (match o
    [(type-app l r) (type-app (instantiate ts l)
                              (instantiate ts r))]
    [(type-gen idx) (list-ref ts idx)]
    [(list vs ...) (map (curry instantiate ts) vs)]
    [(qualified ps t) (qualified
                       (instantiate ts ps)
                       (instantiate ts t))]
    [(predicate c t) (predicate c (instantiate ts t))]
    [t t]))

;; --------------
;; Type Inference

(define/contract (ti-literal lit)
  (literal? . -> . TI?)
  (cond [(character? lit) (->TI (cons '() %char))]
        [(integer? lit)
         (do [v <- (fresh-tv kind-star)]
             (->TI (cons (list (predicate "Numeric" v))  v)))]
        [(float? lit)
         (do [v <- (fresh-tv kind-star)]
             (->TI (cons (list (predicate "Fractional" v))  v)))]
        #;[(string? lit) (values '() %list of %char)]
        ;; NOTE this case shouldn't happen due to the contract,
        ;; but I may change that before updating the match.
        [else  (fail/m (format "unsupported literal: ~a" lit))]))

(module+ test
  (define (ti-value p)
    (match p [(success (cons _ v)) (success v)] [o o]))
  (define-syntax (check-relation? stx)
    (syntax-parse stx
      [(_ f:expr l:string)
       #'(match-let ([(success (cons ps tv)) f])
           (check-equal?
            (let loop ([ps ps])
              (cond [(null? ps) (fail)]
                    [(equal? (predicate-t (car ps))
                             tv) (predicate-id (car ps))]
                    [else (loop (cdr ps))]))
            l))]))

  (check-success? (ti-value (<-TI (ti-literal #\U))) %char)
  #;(check-fail? (<-TI (ti-literal "strings unsupported")))
  (check-relation? (<-TI (ti-literal 100))
                   "Numeric"))

;; TODO pattern inference all other variants
(define/contract (ti-pattern p)
  (pattern? . -> . TI?)
  (match p
    [(pat-id i)
     (do [v <- (fresh-tv kind-star)]
         (->TI `(() ,(list (assumption i (type->scheme v))) . ,v)))]))

(define/contract (ti-pattern+ ps)
  ((listof pattern?) . -> . TI?)
  (do [psasts <- (map/m ti-pattern ps)]
      (define ps (apply append (map car psasts)))
    (define as (apply append (map cadr psasts)))
    (define ts (apply append (map cddr psasts)))
    (->TI (cons ps (cons as ts)))))

(define/contract (ti-expr env as e)
  (tclass-env? (listof assumption?) expression? . -> . TI?)
  (define (return ss t) (->TI (cons ss t)))
  (match e
    [(expr-var i)
     (do [sc <- (find-in-assumptions i as)]
         [(qualified ps t) <- (fresh-inst sc)]
       (return ps t))]
    [(expr-lit l) (ti-literal l)]
    [(expr-const (assumption id scm))
     (do [(qualified ps t) <- (fresh-inst scm)]
         (return ps t))]
    [(expr-app e f)
     (do [(cons ps te) <- (ti-expr env as e)]
         [(cons qs tf) <- (ti-expr env as f)]
       [t <- (fresh-tv kind-star)]
       (unify ($make-func tf t) te)
       (return (append ps qs) t))]
    [(expr-let bg e)
     (do [(cons ps asp) <- (ti-bind-group env as bg)]
         [(cons qs t) <- (ti-expr env (append asp as) e)]
       (return (append ps qs) t))]))

(module+ test
  (check-success? (ti-value (<-TI (ti-expr empty-env '() (expr-lit #\U))))
                  %char)
  (check-fail? (ti-value (<-TI (ti-expr empty-env '() (expr-var "x")))))
  (check-success?
   (ti-value (<-TI (ti-expr empty-env
                            (list (assumption "x" (type->scheme %int)))
                            (expr-var "x")))) %int)
  (check-fail? (<-TI
                (ti-expr empty-env '()
                         (expr-let (bind-group '()
                                               '())
                                   (expr-var "x")))))
  (check-relation?
   (<-TI (ti-expr empty-env '()
                  (expr-let
                   (bind-group
                    '()
                    (list (list (bg-implicit
                                 "x"
                                 (list (alternative
                                        '()
                                        (expr-lit 10)))))))
                   (expr-var "x")))) "Numeric")
  ;; Test for explicit binding with arithmetic
  ;; Test with non-empty env
  ;; Test for functions
  ;; ...
  )

(define/contract (ti-alternative env as a)
  (tclass-env? (listof assumption?) alternative? . -> . TI?)
  (match a
    [(alternative pats expr)
     (do [(cons ps (cons asp ts)) <- (ti-pattern+ pats)]
         [(cons qs t) <- (ti-expr env (append asp as) expr)]
       (->TI (cons (append ps qs) (foldr (lambda (t1 t2) ($make-func t1 t2))
                                         t ts))))]))

(define/contract (ti-alternative+ env as alts t)
  (tclass-env? (listof assumption?)
               (listof alternative?) type? . -> . TI?)
  (do [psts <- (map/m (curry ti-alternative env as) alts)]
      (map/m (curry unify t) (map cdr psts))
    (->TI (apply append (map car psts)))))

(define/contract (split env fs gs ps)
  (tclass-env? (listof type-variable?)
               (listof type-variable?)
               (listof predicate?)
               . -> . monad?)
  (do [psp <- (reduce env ps)]
      (define-values (ds rs)
        (partition (compose (curryr member fs)
                            get-type-vars) psp))
    [rsp <- (default-predicates env (append fs gs) rs)]
    (->TI (cons ds (list-diff rs rsp)))))

(define/contract (ambiguities env vs ps)
  (tclass-env? (listof type-variable?)
               (listof predicate?) . -> . (listof ambiguity?))
  (for/list ([v (in-list (list-diff (get-type-vars ps) vs))])
    (define preds (filter (compose (curry member v)
                                   get-type-vars) ps))
    (ambiguity v preds)))

(define (default-candidates env amb)
  ;; An ambiguity can be defaulted if it meets specific criteria. Currently, no
  ;; ambiguities will be defaulted and must be specified by the programmer.
  ;; These conditions are as follows:
  ;; - All QS predicates are of the form: (predicate _ (type-variable _)).
  ;; - One of the classes involved is a numeric class.
  ;; - All classes involved are from the standard library.
  ;; https://web.cecs.pdx.edu/~mpj/thih/TypingHaskellInHaskell.html#Haskell98
  '())

(define #;/contract (with-defaults f env vs ps)
  #;(((listof ambiguity?) (listof type? . -> . any/c))
   tclass-env? (listof type-variable?)
   (listof predicate?)
   . -> . (result/c any/c))
  (define vps (ambiguities env vs ps))
  (define tss (map (curry default-candidates env) vps))
  (cond [(ormap null? tss) (failure "cannot resolve ambiguity")]
        [else (success (f vps (map car tss)))]))

(define (default-predicates env vs ps)
  (with-defaults (lambda (vps ts)
                   (apply append (map cadr vps))) env vs ps))

(define (default-subst env vs ps)
  (with-defaults (lambda (vps ts)
                   (map cons (map car vps) ts)) env vs ps))

(define/contract (ti-explicit env as bgex)
  (tclass-env? (listof assumption?) bg-explicit? . -> . TI?)
  (match-define (bg-explicit i scm alts) bgex)
  (do [(qualified qs t) <- (fresh-inst scm)]
      [ps <- (ti-alternative+ env as alts t)]
    [s <- (get-state)]
    (define qsp (substitute s qs))
    (define tp (substitute s t))
    (define fs (get-type-vars (substitute s as)))
    (define gs (list-diff (get-type-vars tp) fs))
    (define scmp (quantify gs (qualified qsp tp)))
    (define psp (filter (compose not (curry entails? env qsp))
                        (substitute s ps)))
    [(cons ds rs) <- (split env fs gs psp)]
    ;; TODO change these to fail with the state monad (or a monad stack).
    (cond [(not (equal? scm scmp)) (error "signature too general")]
          [(not (null? rs)) (error "context too weak")]
          [else (->TI ds)])))

(define/contract (restricted? bs)
  ((listof implicit/c) . -> . boolean?)
  (define/contract (simple impls)
    (implicit/c . -> . boolean?)
    (match impls [(bg-implicit _ alts)
                  (ormap (compose null? alternative-pats) alts)]))
  (ormap simple bs))

(define/contract (ti-implicit+ env as bs)
  (tclass-env? (listof assumption?) (listof implicit/c) . -> . TI?)
  (do [ts <- (map/m (lambda _ (fresh-tv kind-star)) bs)]
      (define is (map bg-implicit-id bs))
    (define scs (map type->scheme ts))
    (define asp (map assumption is (append scs as)))
    (define altss (map bg-implicit-alts bs))
    [pss <- (sequence/m (curry ti-alternative+ env asp) altss ts)]
    [s <- (get-state)]
    (define psp (substitute s (apply append pss)))
    (define tsp (substitute s ts))
    (define fs (get-type-vars (substitute s as)))
    (define vss (map get-type-vars tsp))
    (define gs (foldr1 list-union (list-diff vss fs)))
    [(cons ds rs) <- (split env fs (foldr1 list-intersect vss) psp)]
    (if (restricted? bs)
        (let* ([gsp (list-diff gs (get-type-vars rs))]
               [scsp (map (compose (curry quantify gsp)
                                   (curry qualified '())) tsp)])
          (->TI (cons (append ds rs) (map assumption is scsp))))
        (let ([scsp (map (compose (curry quantify gs)
                                  (curry qualified rs)) tsp)])
          (->TI (cons ds (map assumption is scsp)))))))

(define/contract (ti-bind-group env as bg)
  (tclass-env? (listof assumption?) bind-group? . -> . TI?)
  (match-define (bind-group es iss) bg)
  (do (define asp (for/list ([e (in-list es)])
                    (match-define (bg-explicit v scm alts) e)
                    (assumption v scm)))
      [(cons ps aspp) <- (ti-seq ti-implicit+ env (append asp as) iss)]
      [qss <- (map/m (curry ti-explicit env (append aspp asp as)) es)]
      (->TI (cons (append ps (apply append qss))
                  (append aspp asp)))))

(define (ti-seq ti-f env as bs)
  (match bs
    [(list) (->TI (cons '() '()))]
    [(list bs bss ...)
     (do [(cons ps asp) <- (ti-f env as bs)]
         [(cons qs aspp) <- (ti-seq ti-f env (append asp as) bss)]
         (->TI (cons (append ps qs) (append aspp asp))))]))

(define/contract (ti-program env as bgs)
  (tclass-env? (listof assumption?) (listof bind-group?) . -> . (listof assumption?))
  (<-TI
   (do [(cons ps asp) <- (ti-seq ti-bind-group env as bgs)]
       [s <- (get-state)]
       [rs <- (reduce env (substitute s ps))]
       [sp <- (default-subst env '() rs)]
       (->TI (substitute (sp . @@ . s) asp)))))
