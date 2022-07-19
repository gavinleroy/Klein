#lang racket/base

(require (for-syntax racket/base
                     syntax/parse)
         racket/set
         racket/bool
         racket/list
         racket/match
         racket/function
         racket/contract

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
(struct %#kind-star kind () #:sealed)
(struct kind-fun kind (k1  k2) #:sealed)
;; Only one Star kind is required
(define kind-star (%#kind-star))
(define (kind-star? s)
  (eq? s kind-star))

(struct type ())
(struct type-variable type (id k) #:sealed)
(struct type-const type (id k) #:sealed)
(struct type-app type (t1 t2) #:sealed)
(struct type-gen type (hsh) #:sealed)
;; Representation of a `qualified` type. The head represents a type? that must
;; fulfil the list of predicates.
(struct qualified type (predicates #;predicate? head #;type?))
(define (qualified/c t?)
  (and/c qualified? (compose t? qualified-head)))

;; A predicate of the form id t states that type? `t` is a member of class `id`.
(struct predicate type (id t #;type?))
;; A type scheme relates all universally quantified  variables in the qualified
;; types with a kind in `kinds`. These variables are ordered and the nth
;; variables has type scheme `(list-ref kinds n)`.
(struct scheme type (kinds #;(listof kind)
                     qs #;qualified?) #:sealed)
(struct tclass type (ids ints) #:sealed)
(struct assumption type (id scheme))

;; Class environments partially map ids to class values.
(struct tclass-env (classes #;(id? . -> . (option/c tclass?))
                    defaults #;(listof type?)))

;; TODO expressions are currently a subset of what should be available in Klein.
(struct expression ())
(struct expr-var expression (id) #:sealed)
(struct expr-lit expression (lit) #:sealed)
(struct expr-const expression (assumpt) #:sealed)
(struct expr-app expression (e1 e2) #:sealed)
(struct expr-let expression (bg e) #:sealed)

;; Patterns may occur on the left hand side of a function declaration. Here,
;; values may be destructured.
;; TODO support the full slew of patterns.
(struct pattern ())
(struct pat-id pattern (id) #:sealed)

;; An alternative is used to bind a list of function binding patterns (left hand sides)
;; to a cooresponding body expression (right hand side).
(struct alternative (pats expr) #:sealed)

;; For a given list of explicit bindings,
;;
;; Example: given a group of explicitly typed bindings `es`, impls would be a
;; list of implicitly typed bindings of the form `im_0, im_1, ..., im_n`. An
;; implicit bindings `im_i` should only depend on those bindings in es or `im_j`
;; such that `0 <= j && j < i`.
(struct bg-explicit (id scm alts))
(struct bg-implicit (id alts))

(struct bind-group (expls impls))

(struct ambiguity (tv ps))

;; Contract for results that could fail, all results must include a message
;; describing why the computation failed. This probably should be augmented in
;; the future to include value / syntax information allowing the error engine to
;; produce cohesive messages to the user.
(define (result/c ctc) (either/c string? ctc))
(define subst/c (listof pair?))

;; Type Inference monad for passing state (currently a single substitution TODO)
(struct TI (proc)
  #:transparent
  #:methods df:gen:functor
  [(define (map f x)
     (TI (lambda (s)
           ;; (match-define (cons s v) ((TI-proc x) s))
           (define t ((TI-proc x) s))
           (cons (car t) (f (cdr t))))))]
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
           (match-define (cons st v) (fx s))
           (match-define (TI fg) (f v))
           (fg st))))])

;; Helpers for working with a Type Inference state
(define (->TI x) (TI (lambda (s) (cons s x))))
(define (get-state) (TI (lambda (s) (cons s s))))
(define/contract (run-ti ti)
  (TI? . -> . any/c)
  (match-define (TI f) ti)
  (cdr (f empty-subst)))
(define/contract (ext-state sp)
  (subst/c . -> . TI?)
  (TI (lambda (s) (cons (sp . @@ . s) 'dummy))))
(define-syntax (sequence/m stx)
  (syntax-case stx ()
    [(_ f ms ...)
     #'(map/m (curry apply f) (map list ms ...))]))

(module+ test
  (define (push-state e) (TI (lambda (s) (cons (cons e s) (void)))))
  (define (run-state ti) (car ((TI-proc ti) empty-subst)))
  (define (%add x y) (TI (lambda (s) (cons s (+ x y)))))
  #;(define (double x)
      (do [y <- (%add x x)]
          (return-ti y y)))
  #;(define (quadruple x)
      (do [(TI<- y y) <- (double x)]
          [(TI<- z z) <- (double y)]
        (return-ti z z z z)))
  (check-equal? (run-ti (->TI 0)) 0)
  (check-equal? (run-ti (df:map (compose add1 add1) (->TI 0))) 2)
  (check-equal? (run-ti ((->TI identity) (->TI 0))) 0)
  (check-equal? (run-ti ((->TI add1) (->TI 0))) 1)
  (check-equal? (run-ti (((->TI compose) (->TI add1) (->TI add1)) (->TI 0))) 2)
  (check-equal? (run-state
                 (do (->TI 0)
                     (push-state 0)
                   (push-state 1)
                   (push-state 2)
                   (get-state))) '(2 1 0))
  (check-equal? (run-ti (sequence/m %add '(1 2 3) '(3 2 1)))
                '(4 4 4))
  #;(check-equal? (run-ti
                   (do [(TI<- a b c d) <- (quadruple 2)]
                       (return-ti (= 8 a b c d)))) #true))

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
                   [ty ty])]
                [(type-app t1 t2) (type-app (substitute sub t1)
                                            (substitute sub t2))]
                [(qualified ps head)
                 (qualified (substitute sub ps)
                            (substitute sub head))]
                [(predicate i t) (predicate i (substitute i t))]
                [(scheme ks qt) (scheme ks (substitute sub qt))]
                [(assumption i ts) (assumption i (substitute sub ts))]
                [else t])]))

(define/contract (get-type-vars t0)
  ((or/c (listof type?) type?) . -> . (listof type?))
  (define (tv t)
    (cond [(list? t) (apply set-union (map tv t))]
          [else (match t
                  [(type-variable _ _) (set t)]
                  [(type-app l r) (set-union (tv l) (tv r))]
                  [(qualified ps head) (set-union (tv ps)
                                                  (tv head))]
                  [(predicate _ t) (tv t)]
                  [(scheme _ qt) (tv qt)]
                  [(assumption _ ts) (tv ts)]
                  [else (set)])]))
  (set->list (tv t0)))

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

(define (env-super env i)
  (match ((tclass-env-classes env) i)
    [(success (tclass ids _)) ids]
    [else (error "internal error, no super found")]))

(define (env-insts env i)
  (match ((tclass-env-classes env) i)
    [(success (tclass _ is)) is]
    [else (error "internal error, no instances found")]))

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
  (cond [(not (defined? (tclass-env-classes env i))) (failure "no class for instance")]
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
  (tclass-env? (or/c (listof predicate?) predicate?)
               . -> . (result/c (listof predicate?)))
  (cond [(list? p) (do [ps <- (map/m (curry ->head-normal-form env) p)]
                       (success (apply append ps)))]
        [(head-normal-form? p) (list p)]
        [else (match (by-inst env p)
                [(failure _) (failure "context reduction")]
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
  (tclass-env? (listof predicate?) . -> . (result/c (listof predicate?)))
  (do [qs <- (->head-normal-form env ps)]
      (success (simplify env qs))))

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
  (string? (listof assumption?) . -> . (result/c scheme?))
  (match as
    [(list) (failure "unbound identifier")]
    [(list (assumption i ts) as ...)
     (if (equal? id i)
         (success ts)
         (find-in-assumptions id as))]))

(define/contract (unify t1 t2)
  (type? type? . -> . TI?)
  (do [s <- (get-state)]
      [u <- (most-general-unifier (substitute s t1)
                                  (substitute s t2))]
      (ext-state u)))

(define/contract (fresh-tv k)
  (kind? . -> . TI?)
  (TI (lambda (s) (cons s (type-variable (genid) k)))))

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
        #;[(string? lit) (values '() %list of %char)]))

(module+ test
  (check-equal? (cdr (run-ti (ti-literal #\U))) %char)
  #;(check-equal? (cdr (run-ti (ti-literal 100))) 'TODO))

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

(define #;/contract (ti-expr env as e)
  #;(tclass-env? (listof assumption?) expr? . -> . TI?)
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

(define/contract (with-defaults f env vs ps)
  (((listof ambiguity?) (listof type? . -> . any/c))
                       tclass-env? (listof type-variable?)
                       (listof predicate?)
                       . -> . (result/c any/c))
  (define vps (ambiguities env vs ps))
  (define tss (map (curry default-candidates env)
                 vps))
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
  ((listof bg-implicit?) . -> . boolean?)
  (define/match (simple impls)
    [((bg-implicit i alts)) (ormap (compose null? car) alts)])
  (ormap simple bs))

(define/contract (ti-implicit+ env as bs)
  (tclass-env? (listof assumption?) (listof bg-implicit?) . -> . TI?)
  (do [ts <- (map/m (lambda _ (fresh-tv kind-star)))]
      (define is (map bg-implicit-id bs))
      (define scs (map type->scheme ts))
      (define asp (map assumption is (append scs as)))
      (define altss (map bg-implicit-alts bs))
      [pss <- (sequence/m ti-alternative+ altss ts)]
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
      (->TI (apply append (cons ps qss) (append aspp asp)))))

(define (ti-seq ti-f env as bs)
    (match bs
      [(list) (->TI (cons '() '()))]
      [(list bs bss ...)
       (do [(cons ps asp) <- (ti-f env as bs)]
           [(cons qs aspp) <- (ti-seq env (append asp as) bss)]
           (->TI (cons (append ps qs) (append aspp asp))))]))

(define/contract (ti-program env as bgs)
  (tclass-env? (listof assumption?) (listof bind-group?) . -> . (listof assumption?))
  (run-ti
   (do [(cons ps asp) <- (ti-seq ti-bind-group env as bgs)]
       [s <- (get-state)]
       [rs <- (reduce env (substitute s ps))]
       [sp <- (default-subst env '() asp)]
       (->TI (substitute (sp . @@ . s) asp)))))

(module+ test
  )
