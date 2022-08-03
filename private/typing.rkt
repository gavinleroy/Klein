#lang racket/base

(require (for-syntax racket/base
                     syntax/parse
                     racket/syntax

                     "utils.rkt")
         racket/bool
         racket/contract
         racket/syntax
         racket/function
         racket/list
         racket/match
         racket/struct

         ;; TODO get rid of the monadic interface and use macros instead. Use of
         ;; macros wil also gain you syntax highlighting + many other things in DrRacket.
         (prefix-in r: racket/base)
         (prefix-in df: data/functor)
         (prefix-in da: data/applicative)
         data/monad
         data/either

         "list-set.rkt"
         "languages.rkt"
         "utils.rkt")

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
  #:transparent
  #:sealed
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (o) 'AppT)
      (lambda (o) (list (type-app-t1 o)
                   (type-app-t2 o)))))])

(struct type-gen type (hsh)
  #:transparent
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
                   (qualified-head o)))))])
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
  #:sealed
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (o) 'Scheme)
      (lambda (o) (list (scheme-kinds o)
                   (scheme-qs o)))))])

(struct tclass type (ids ints)
  #:transparent
  #:sealed
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (o) 'ClassT)
      (lambda (o) (list (tclass-ids o)
                   (tclass-ints o)))))])

(struct assumption type (id scheme)
  #:transparent
  #:sealed
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (o) 'Assump)
      (lambda (o) (list (assumption-id o)
                   (assumption-scheme o)))))])

;; Class environments partially map ids to class values.
(struct tclass-env (classes defaults)
  #:transparent
  #:sealed
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (o) 'ClassEnv)
      (lambda (o) (list #;TODO))))])

;; TI also embeds a result (failure / success) to signify type checking
;; errors. This is essentially an `ExceptT State`.
(struct state (subst genid))
(struct TI (proc)
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


;; Contract for results that could fail, all results must include a message
;; describing why the computation failed. This probably should be augmented in
;; the future to include value / syntax information allowing the error engine to
;; produce cohesive messages to the user.
(define (result/c ctc) (or/c (either/c string? ctc)
                             (da:pure/c (either/c string? ctc))))
(define TI/c (or/c (da:pure/c TI?) TI?))
(define subst/c (listof pair?))

;; Helpers for working with a Type Inference state
(define (->TI x) (TI (lambda (s) (cons s (success x)))))

(define (get-state) (TI (lambda (s) (cons s (success s)))))
(define (get-subst) (TI (lambda (s) (cons s (success (state-subst s))))))
(define (get-genid)
  (TI (lambda (s)
        (match-define (cons c i) (state-genid s))
        (if (= c 122)
            (begin (set! c 96)
                   (set! i (add1 i)))
            (void))
        (set! c (add1 c))
        (cons (struct-copy state s
                           [genid (cons c i)])
              (success (format-symbol "~a~a" (integer->char c) i))))))

;; Define showrtcut methods
(define-formatted error)
(define-formatted failure)

(define/contract (<-TI ti)
  (TI/c . -> . (result/c any/c))
  (match-define (TI f) ti)
  (cdr (f (state empty-subst (cons 96 0)))))

(define/contract (ext-state sp)
  (subst/c . -> . TI/c)
  (TI (lambda (s)
        (cons
         (struct-copy state s
                      [subst (sp . @@ . (state-subst s))])
              (success 'dummy)))))

(define/contract (fail/m msg)
  (string? . -> . TI/c)
  (TI (lambda (s) (cons s (failure msg)))))
(define-syntax (sequence/m stx)
  (syntax-case stx ()
    [(_ f ms ...)
     #'(map/m (curry apply f) (map list ms ...))]))

(define/contract (concat lss)
  ((listof (listof any/c)) . -> . (listof any/c))
  (apply append lss))

(module+ test
  (define-syntax (check-success? stx)
    (syntax-parse stx
      [(_ f:expr s:expr) #'(check-equal? f (success s))]))
  (define-syntax (check-fail? stx)
    (syntax-parse stx
      [(_ f:expr) #'(let ([v f]) (check-pred failure? v))]))

  (define (push-state e)
    (TI (lambda (s)
          (cons (struct-copy state s
                             [subst (cons e (state-subst s))])
                (success (void))))))
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
                            (get-subst))) '(2 1 0))
  (check-success? (<-TI (sequence/m %add '(1 2 3) '(3 2 1)))
                  '(4 4 4))
  #;(check-fail? (<-TI (do [x <- (->TI 0)]
                         [y <- (%add x x)]
                         [z <- (fail/m "whoops!")]
                         (%add z y)))))

;; -----------------------------------------------

(define-syntax (def-ty-prim x)
  (syntax-case x ()
    [(_ pattern name)
     (with-syntax ([%name #'name]
                   [%pat #'pattern])
       #'(define %name (type-const %pat kind-star)))]))

(def-ty-prim '() %unit)
(def-ty-prim 'Char %char)
(def-ty-prim 'Int %int)
(def-ty-prim 'Float %float)

;; TODO make sure these are turned into internal Klein definitions

(define %list
  (type-const '[] (kind-fun kind-star kind-star)))
(define %arrow
  (type-const '->
              (kind-fun kind-star
                        (kind-fun kind-star kind-star))))
(define %tuple2
  (type-const '*
              (kind-fun kind-star
                        (kind-fun kind-star kind-star))))

(define-syntax ($make-func stx)
  (syntax-case stx ()
    [(_ a b) #'(type-app (type-app %arrow a) b)]
    [(_ a b ...) #'(type-app (type-app %arrow a)
                             ($make-func b ...))]))

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
    [(type-app t1 _)
     (kind-fun-k2 (get-kind t1))]))




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

(define/contract (get-type-vars t)
  ((or/c (listof type?) type?) . -> . (listof type?))
    (cond [(list? t) (apply list-union (map get-type-vars t))]
          [else (match t
                  [(type-variable _ _) (list t)]
                  [(type-app l r) (list-union (get-type-vars l) (get-type-vars r))]
                  [(qualified ps head) (list-union (get-type-vars ps)
                                                   (get-type-vars head))]
                  [(predicate _ t) (get-type-vars t)]
                  [(scheme _ qt) (get-type-vars qt)]
                  [(assumption _ ts) (get-type-vars ts)]
                  [else (list)])]))

;; @@ is the infix operator for substitution composition
(define/contract (@@ s1 s2)
  (subst/c subst/c . -> . subst/c)
  (let ([ls (for/list ([tup (in-list s2)])
              (match-let ([(cons u t) tup])
                (cons u (substitute s1 t))))])
    (append ls s1)))

(define/contract (merge s1 s2)
  (subst/c subst/c . -> . monad?)
  (define (heads ls) (map car ls))
  (let ([agreeable (andmap (lambda (v) (equal? (substitute s1 v)
                                          (substitute s2 v)))
                           (list-intersect (heads s1) (heads s2)))])
    (if agreeable
        (da:pure (append s1 s2))
        (error "merge fail"))))

;; Unification

(define/contract (most-general-unifier t1 t2)
  (type? type? . -> . monad?)
  (match (cons t1 t2)
    [(cons (predicate i t) (predicate ii tt))
     #:when (equal? i ii)
     (most-general-unifier t tt)]

    [(cons (type-app ll rl) (type-app lr rr))
     (do [s1 <- (most-general-unifier ll lr)]
         [s2 <- (most-general-unifier (substitute s1 rl)
                                      (substitute s1 rr))]
       (da:pure (s2 . @@ . s1)))]
    [(cons u t)
     #:when (type-variable? u)
     (bind-variable u t)]
    [(cons t u)
     #:when (type-variable? u)
     (bind-variable u t)]
    [(cons tc1 tc2)
     #:when (and (type-const? tc1)
                 (type-const? tc2)
                 (equal? tc1 tc2))
     (da:pure empty-subst)]
    [else (error-format "Types: ~a\n~a do not unify." t1 t2)]))

(define/contract (bind-variable u t)
  (type-variable? type? . -> . monad?)
  (cond [(and (type-variable? t)
              (equal? u t))
         (da:pure empty-subst)]
        [(member u (get-type-vars t))
         (error "occurs check fails")]
        [(not (equal? (get-kind u)
                      (get-kind t)))
         (error "kinds do not match")]
        [else (success (u . +-> . t))]))

(define/contract (type-match t1 t2)
  (type? type? . -> . monad?)
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
     (da:pure (u . +-> . t))]
    [(cons (type-const _ tc1) (type-const _ tc2))
     #:when (equal? tc1 tc2)
     (da:pure empty-subst)]
    [else (error-format "Types t1 and t2 do not match" t1 t2)]))

(define/contract (lift-unifier f p1 p2)
  ((predicate? predicate? . -> . (result/c subst/c))
   predicate? predicate? . -> . (result/c subst/c))
  (define i (predicate-id p1))
  (define ii (predicate-id p2))
  (if (symbol=? i ii)
      (f p1 p2)
      (failure-format "Differing classes '~a '~a" i ii)))

(define/contract (most-general-unifier/predicate p1 p2)
  (predicate? predicate? . -> . (result/c subst/c))
  (lift-unifier most-general-unifier p1 p2))

(define/contract (type-match/predicate p1 p2)
  (predicate? predicate? . -> . (result/c subst/c))
  (lift-unifier type-match p1 p2))

;; Class environemnts

(define/contract #;INTERNAL (env-super env i)
  (tclass-env? symbol? . -> . (listof symbol?))
  (match ((tclass-env-classes env) i)
    [(success (tclass ids _)) ids]
    [(failure msg) '()]))

(define/contract #;INTERNAL (env-insts env i)
  (tclass-env? symbol? . -> . (listof (qualified/c predicate?)))
  (match ((tclass-env-classes env) i)
    [(success (tclass _ is)) is]
    [(failure msg) '()]))

(define/contract #;INTERNAL (defined? m)
  ((result/c any/c) . -> . boolean?)
  (success? m))

(define/contract (env-bind env i c)
  (tclass-env? symbol? tclass? . -> . tclass-env?)
  (define check-up (tclass-env-classes env))
  (struct-copy tclass-env env
               [classes (lambda (j) (if (symbol=? i j)
                                   (success c)
                                   (check-up j)))]))

(define env->env/c (tclass-env? . -> . (result/c tclass-env?)))

(define (from-success! either)
  (match either [(success v) v]))

(define/contract (<:> g f)
  (env->env/c env->env/c . -> . env->env/c)
  (lambda (env) (do [envp <- (f env)]
               (g envp))))

;; Extend the environment `env` with the given
;; extensions, no extension should fail as this is
;; an internal function.
;;
;; NOTE the list of extensions is reversed because it
;; is more natural to define the classes /top-down/
(define #;INTERNAL (%extend-environment env . exts)
  ((compose from-success!
            (foldr1 <:> (reverse exts))) env))

(define/contract (env-add-class i is)
  (symbol? (listof symbol?) . -> . env->env/c)
  (let ([find-undefined (lambda (env) (curry findf
                                        (compose not defined?
                                                 (tclass-env-classes env))))])
    (lambda (env)
      (define any-undefined? (find-undefined env))
      (cond [(defined? ((tclass-env-classes env) i))
             (failure-format "Class '~a is already defined" i)]
            [(any-undefined? is)
             (define undef (any-undefined? is))
             (failure-format "Superclass '~a of '~a is not defined" undef i)]
            [else (success (env-bind env i (tclass is '())))]))))

(define/contract (env-add-inst ps p)
  ((listof predicate?) predicate? . -> . env->env/c)
  (lambda (env)
    (define (overlap? p q)
      (defined? (most-general-unifier/predicate p q)))
    (match-define (predicate i _) p)
    (define its (env-insts env i))
    (define qs (for/list ([qd (in-list its)])
                 (match-let ([(qualified _ q) qd]) q)))
    (define c (tclass (env-super env i)
                      (cons (qualified ps p) its)))
    (cond [(not (defined? ((tclass-env-classes env) i)))
           (failure "no class for instance")]
          [(ormap (curry overlap? p) qs) (failure "")]
          [else (success (env-bind env i c))])))

(module+ test
  ;; FIXME
  (define-syntax (check-list-eqv? stx)
    (syntax-case stx ()
      [(_ ac ex)
       #'(let ([r1 ac] [r2 ex])
           (check list-eqv? r1 r2
                  (format "List difference: ~a" (list-diff r1 r2))))]))

  (define a-ty (type-variable 'a0 kind-star))
  (define b-ty (type-variable 'b0 kind-star))
  (define fishy-env
    (%extend-environment empty-env
                         (env-add-class 'Fish '())
                         (env-add-class 'BlueFish '(Fish))
                         (env-add-class 'RedFish '(Fish))
                         (env-add-class 'PurpleFish '(RedFish BlueFish))
                         (env-add-class 'HungryFish '(PurpleFish))
                         (env-add-inst '() (predicate 'Fish %unit))
                         #;(env-add-inst (list (predicate 'Fish a-ty))
                                         (predicate 'Fish ($make-list a-ty)))))
  ;; (check-equal? a-ty a-ty)
  ;; (check-equal? %unit %unit)
  ;; (check-equal? (predicate 'Fish %unit)
  ;;               (predicate 'Fish %unit))
  ;; (check-equal? (qualified '() (predicate 'Fish %unit))
  ;;               (qualified '() (predicate 'Fish %unit)))

  (check-list-eqv? (env-super fishy-env 'Fish) '())
  (check-list-eqv? (env-super fishy-env 'BlueFish) '(Fish))
  (check-list-eqv? (env-super fishy-env 'RedFish) '(Fish))
  (check-list-eqv? (env-super fishy-env 'PurpleFish) '(RedFish BlueFish))
  (check-list-eqv? (env-super fishy-env 'HungryFish) '(PurpleFish))
  #;(check-list-eqv? (env-insts fishy-env 'Fish)
                   (list (qualified (predicate 'Fish a-ty)
                                    (predicate 'Fish ($make-list a-ty)))
                         (qualified '() (predicate 'Fish %unit)))))

(define/contract (by-super env p)
  (tclass-env? predicate? . -> . (listof predicate?))
  (match-define (predicate i t) p)
  (define ll (for/list ([ip (in-list (env-super env i))])
               (by-super env (predicate ip t))))
  (cons p (concat ll)))

(define/contract (by-inst env p)
  (tclass-env? predicate? . -> . (result/c (listof predicate?)))
  (match-define (predicate i _) p)
  (define try-inst
    (match-lambda [(qualified ps h)
                   (do [u <- (type-match/predicate h p)]
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
  (tclass-env? (or/c (listof predicate?) predicate?) . -> . monad?)
  (cond [(list? p)
         (do [ps <- (map/m (curry ->head-normal-form env) p)]
             (da:pure (concat ps)))]
        [(head-normal-form? p) (->TI (list p))]
        [else (match (by-inst env p)
                [(failure _) (error "context reduction")]
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
  (tclass-env? (listof predicate?) . -> . monad?)
  (do [qs <- (->head-normal-form env ps)]
      (da:pure (simplify env qs))))

(define/contract (quantify vs qt)
  ((listof type-variable?) (qualified/c type?) . -> . scheme?)
  (define vsp
    (for/list ([v (in-list (get-type-vars qt))]
               #:when (member v vs)) v))
  (define ks (map get-kind vsp))
  (define s (for/list ([(v i) (in-indexed vsp)])
              (cons v (type-gen i))))
  (scheme ks (substitute s qt)))

(define/contract (type->scheme t)
  (type? . -> . scheme?)
  (scheme '() (qualified '() t)))

(define/contract (find-in-assumptions id as)
  (symbol? (listof assumption?) . -> . monad?)
  (match as
    [(list) (error-format "unbound identifier: ~a" id)]
    [(list (assumption i ts) as ...)
     (if (equal? id i)
         (da:pure ts)
         (find-in-assumptions id as))]))

(define/contract (unify t1 t2)
  (type? type? . -> . TI/c)
  (do [s <- (get-subst)]
      [u <- (most-general-unifier (substitute s t1)
                                  (substitute s t2))]
    (ext-state u)))

(define/contract (fresh-tv k)
  (kind? . -> . TI/c)
  (do [id <- (get-genid)]
      (->TI (type-variable id k))))

(define/contract (fresh-inst tscm)
  (scheme? . -> . TI/c)
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
  ;; Furthermore, both type variables any/c should be equal.
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

;; -----------------------------------------------

(define empty-env
  (tclass-env (lambda (id) (failure-format "identifier '~a not found in class environment" id ))
              (list %int %float)))

(define core-env
  empty-env
  #;(%extend-environment empty-env
                       #;(env-add-class 'Equal '())
                       ;; (env-add-class 'Numeric '(Equal))
                       ;; (env-add-class 'Fractional '(Numeric))
                       ;; (env-add-class 'Int '(Numeric))
                       ;; (env-add-class 'Float '(Fractional))
                       #;(env-add-class 'Ord '(Equal))
                       #;(env-add-inst '() (predicate 'Numeric %int))
                       #;(env-add-inst '() (predicate 'Fractional %float))))

(define empty-assumptions '())

(define core-assumptions
  ;; TODO synchronize this with the primitives
  (list* (assumption '#%int+
                     (type->scheme
                      (type-app (type-app %arrow %int) %int)))
         (assumption '#%float+
                     (type->scheme
                      (type-app (type-app %arrow %float) %float)))
         empty-assumptions))

;; -----------------------------------------------
;; Type Inference

(define/contract (ti-literal lit)
  (literal? . -> . TI/c)
  (cond [(character? lit) (->TI (cons '() %char))]
        [(integer? lit)
         (do [v <- (fresh-tv kind-star)]
             (->TI (cons (list (predicate 'Numeric v))  v)))]
        [(float? lit)
         (do [v <- (fresh-tv kind-star)]
             (->TI (cons (list (predicate 'Fractional v))  v)))]
        #;[(string? lit) (values '() %list of %char)]
        ;; NOTE this case shouldn't happen due to the contract,
        ;; but I may change that before updating the match.
        [else  (fail/m (format "unsupported literal: ~a" lit))]))

(module+ test
  (define (ti-value p)
    (match p [(success (cons _ v)) (success v)] [o o]))
  (define-syntax (check-class-relation? stx)
    (syntax-parse stx
      [(_ f:expr l:expr)
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
  (check-class-relation? (<-TI (ti-literal 100))
                   'Numeric))

;; TODO pattern inference all other variants
(define/contract (ti-pattern p)
  (pattern? . -> . TI/c)
  (match p
    [(pat-id i)
     (do [v <- (fresh-tv kind-star)]
         (->TI `(() ,(list (assumption i (type->scheme v))) . ,v)))]
    [(pat-lit l)
     (do [(cons ps t) <- (ti-literal l)]
         (->TI `(,ps () . ,t)))]))

(define/contract (ti-pattern+ ps)
  ((listof pattern?) . -> . TI/c)
  (do [psasts <- (map/m ti-pattern ps)]
      (define ps (concat (map car psasts)))
    (define as (concat (map cadr psasts)))
    (define ts (map cddr psasts))
    (->TI (cons ps (cons as ts)))))

(define/contract (ti-expr env as e)
  (tclass-env? (listof assumption?) expression? . -> . TI/c)
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
    [(expr-app f e)
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
  (check-exn exn:fail?
             (lambda () (ti-value (<-TI (ti-expr empty-env '() (expr-var 'x))))))
  (check-success?
   (ti-value (<-TI (ti-expr empty-env
                            (list (assumption 'x (type->scheme %int)))
                            (expr-var 'x)))) %int)
  #;(check-fail? (<-TI
                (ti-expr empty-env '()
                         (expr-let (bind-group '()
                                               '())
                                   (expr-var 'x)))))

#;(<-TI (ti-expr empty-env '()
                  (expr-let
                   (bind-group
                    '()
                    (list (list (bg-implicit
                                 'x
                                 (list (alternative
                                        '()
                                        (expr-lit 10)))))))
                   (expr-var 'x))))

  #;(check-class-relation?
   #;(let ([x 10]) x)
   (<-TI (ti-expr empty-env '()
                  (expr-let
                   (bind-group
                    '()
                    (list (list (bg-implicit
                                 'x
                                 (list (alternative
                                        '()
                                        (expr-lit 10)))))))
                   (expr-var 'x)))) 'Numeric)
  ;; Test for explicit binding with arithmetic
  #;(let ([f (lambda (x y) x)]) f)
  #;(<-TI (ti-expr empty-env '()
                   (expr-let
                    (bind-group
                     '()
                     (list (list (bg-implicit
                                  "f"
                                  (list (alternative
                                         (list (pat-id "x"))
                                         (expr-var "x")))))))
                    (expr-var "f"))))

  (<-TI (ti-expr empty-env '()
                   (expr-let
                    (bind-group
                     '()
                     (list (list (bg-implicit
                                  'f
                                  (list (alternative
                                         (list (pat-id 'x))
                                         (expr-var 'x)))))))
                    (expr-app (expr-var 'f)
                              (expr-lit 10)))))

  #;(<-TI (ti-bind-group
         core-env
         core-assumptions
         (bind-group
          '()
          (list (list (bg-implicit
                       'x
                       (list (alternative
                              '()
                              (expr-app (expr-app (expr-var '#%int+)
                                                  (expr-lit 1))
                                        (expr-lit 3))))))))))

  #;(<-TI (ti-expr core-env core-assumptions
                 (expr-let
                  (bind-group
                   '()
                   (list (list (bg-implicit
                                'x
                                (list (alternative
                                       '()
                                       (expr-app (expr-app (expr-var '#%int+)
                                                           (expr-lit 1))
                                                 (expr-lit 3))))))))
                  (expr-var 'x))))


  #;(check-class-relation?
   #;(let ([x (#%int+ 1 3)]) x)
    'Int)

  ;; Test for functions
  ;; ...
  )

(define/contract (ti-alternative env as a)
  (tclass-env? (listof assumption?) alternative? . -> . TI/c)
  (match a
    [(alternative pats expr)
     (do [(cons ps (cons asp ts)) <- (ti-pattern+ pats)]
         [(cons qs t) <- (ti-expr env (append asp as) expr)]
         (->TI (cons (append ps qs)
                     (foldr (lambda (t1 t2)
                              ($make-func t1 t2)) t ts))))]))

(module+ test
  #;(<-TI (ti-alternative
         empty-env '()
         (alternative (list (pat-id "x"))
                      (expr-var "x")))))

(define/contract (ti-alternative+ env as alts t)
  (tclass-env? (listof assumption?)
               (listof alternative?) type? . -> . TI/c)
  (do [psts <- (map/m (curry ti-alternative env as) alts)]
      (map/m (curry unify t) (map cdr psts))
      (->TI (concat (map car psts)))))


(module+ test
  #;(<-TI
   (do [t <- (fresh-tv kind-star)]
       (ti-alternative+
        empty-env '()
        (list (alternative (list (pat-id "x"))
                           (expr-var "x")))
        t))))

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
                   (concat (map cadr vps))) env vs ps))

(define (default-subst env vs ps)
  (with-defaults (lambda (vps ts)
                   (map cons (map car vps) ts)) env vs ps))

(define/contract (ti-explicit env as bgex)
  (tclass-env? (listof assumption?) bg-explicit? . -> . TI/c)
  (match-define (bg-explicit i scm alts) bgex)
  (do [(qualified qs t) <- (fresh-inst scm)]
      [ps <- (ti-alternative+ env as alts t)]
    [s <- (get-subst)]
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
  (tclass-env? (listof assumption?) (listof implicit/c) . -> . TI/c)
  (do [ts <- (map/m (lambda _ (fresh-tv kind-star)) bs)]
      (define is (map bg-implicit-id bs))
      (define scs (map type->scheme ts))
      ;; TODO REMOVE FIXME
      (define _ (printf "mapping assumptions:\n~a\n~a\n" is (append scs as)))
      (define asp (map assumption is (append scs as)))
      (define altss (map bg-implicit-alts bs))
      [pss <- (sequence/m (curry ti-alternative+ env asp) altss ts)]
      [s <- (get-subst)]
      (define psp (substitute s (concat pss)))
      (define tsp (substitute s ts))
      (define fs (get-type-vars (substitute s as)))
      (define vss (map get-type-vars tsp))
      (define gs (list-diff (foldr1 list-union vss) fs))
      [(cons ds rs) <- (split env fs (foldr1 list-intersect vss) psp)]
      (if (restricted? bs)
          (let* ([gsp (list-diff gs (get-type-vars rs))]
                 [scsp (map (compose (curry quantify gsp)
                                     (curry qualified '())) tsp)])
            (->TI (cons (append ds rs) (map assumption is scsp))))
          (let ([scsp (map (compose (curry quantify gs)
                                    (curry qualified rs)) tsp)])
            (->TI (cons ds (map assumption is scsp)))))))

(module+ test
  #;(<-TI (ti-implicit+
           empty-env '()
           (list (bg-implicit
                  'id
                  (list (alternative
                         (list (pat-id 'x))
                         (expr-var 'x)))))))

  #;(<-TI (ti-implicit+
         empty-env '()
         (list (bg-implicit
                'x
                (list (alternative
                       '()
                       (expr-lit 10))))))))

(define/contract (ti-bind-group env as bg)
  (tclass-env? (listof assumption?) bind-group? . -> . TI/c)
  (match-define (bind-group es iss) bg)
  (do (define asp (for/list ([e (in-list es)])
                    (match-define (bg-explicit v scm alts) e)
                    (assumption v scm)))
      [(cons ps aspp) <- (ti-seq ti-implicit+ env (append asp as) iss)]
      [qss <- (map/m (curry ti-explicit env (append aspp asp as)) es)]
      (->TI (cons (append ps (concat qss))
                  (append aspp asp)))))

(define (ti-seq ti-f env as bs)
  (match bs
    [(list) (->TI (cons '() '()))]
    [(list bs bss ...)
     (do [(cons ps asp) <- (ti-f env as bs)]
         [(cons qs aspp) <- (ti-seq ti-f env (append asp as) bss)]
         (->TI (cons (append ps qs) (append aspp asp))))]))

(module+ test
  #;(<-TI (ti-bind-group empty-env '()
                       (bind-group
                        (list)
                        (list (list (bg-implicit
                                     'id
                                     (list (alternative
                                            (list (pat-id 'x))
                                            (expr-var 'x))))))))))

(define/contract (ti-program env as bgs)
  (tclass-env? (listof assumption?) (listof bind-group?) . -> . (listof assumption?))
  (<-TI
   (do [(cons ps asp) <- (ti-seq ti-bind-group env as bgs)]
       [s <- (get-subst)]
       [rs <- (reduce env (substitute s ps))]
       [sp <- (default-subst env '() rs)]
       (->TI (substitute (sp . @@ . s) asp)))))
