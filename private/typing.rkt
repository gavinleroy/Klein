#lang racket/base

(require (for-syntax racket/base
                     syntax/parse
                     racket/syntax
                     racket/bool
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
         nanopass/base
         "list-set.rkt"
         "languages.rkt"
         "utils.rkt")

(provide typecheck-K3
         core-environment core-assumptions
         empty-environment empty-assumptions)

(module+ test
  (require rackunit)
  (define-syntax (check-success? stx)
    (syntax-parse stx
      [(_ f:expr s:expr) #'(check-equal? f (success s))]))
  (define-syntax (check-fail? stx)
    (syntax-parse stx
      [(_ f:expr) #'(let ([v f]) (check-pred failure? v))]))
  (define-syntax (check-typed-prog? stx)
    (syntax-parse stx
      [(_ (~optional (~seq #:run-from stage:expr))
          (~optional (~seq #:unwrap-value uwrp:expr #:value-equal? val:expr))
          (~optional #:use-core) ;; include the core-env/ass
          args ...)
       (with-syntax ([run-state (if (attribute stage)
                                    #'stage
                                    #'#%typecheck-K3)]
                     [inner-pred? (if (attribute val)
                                      #'(lambda (v) (equal? val (success (uwrp v))))
                                      #'success?)])
         #;(unless (= (length (syntax->list #'args))
                    (procedure-arity (syntax->datum #'run-state)))
           (raise-syntax-error 'check-typed-prog?
                               "Incorrect arguments for stage"
                               run-state))
         #'(check-pred inner-pred?
                       (<-TI (run-state args ...))))])))


;; TODO FIXME REMOVE
(define-syntax (define/print stx)
  (syntax-case stx ()
    [(_ id expr)
     #'(define id
         (let* ([e expr]
                [_ (printf "~a: ~a\n" 'id e)])
           e))]))

;; A Star kind represents nullary (simple) types. E.g. Int, FLoat, Char, ...
;; A KFun represents a type constructor from k1 -> k2
(struct kind () #:transparent)
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
(define kind-star? %#kind-star?)

(struct type () #:transparent)
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
                   ':=>
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
      (lambda (o) (list (predicate-id o)
                   (predicate-t o)))))])

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

(struct ambiguity (tv ps)
  #:transparent
  #:sealed)

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
(define (entry? p)
  (and (pair? p)
       (type-variable? (car p))
       (type? (cdr p))))
(define subst/c (listof entry?))

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

;; Formatted versionis of string error handlers.
(define-formatted error)
(define-formatted failure)

(define (fail-proc/c res/c)
  (->* (string?) #:rest (listof any/c) res/c))

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

(define/contract (fail/m msg . args)
  (fail-proc/c TI?)
  (TI (lambda (s) (cons s (apply (curry failure-format msg)
                            args)))))

(define-syntax (sequence/m stx)
  (syntax-case stx ()
    [(_ f ms ...)
     #'(map/m (curry apply f) (map list ms ...))]))

(define/contract (concat lss)
  ((listof (listof any/c)) . -> . (listof any/c))
  (apply append lss))

(module+ test
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
  (check-fail? (<-TI (do [x <- (->TI 0)]
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

(def-ty-prim '<!> %unit)
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
  `((,u . ,t)))

(define/contract (substitute sub t)
  (subst/c (or/c (listof type?) type?) . -> . (or/c (listof type?) type?))
  (if (list? t)
      (map (curry substitute sub) t)
      (match t
        [(type-variable _ _)
         (let ([assc (assoc t sub)])
           (if assc
               (cdr assc)
               t))]
        [(type-app t1 t2) (type-app (substitute sub t1)
                                    (substitute sub t2))]
        [(qualified ps head)
         (qualified (substitute sub ps)
                    (substitute sub head))]
        [(predicate i t) (predicate i (substitute sub t))]
        [(scheme ks qt) (scheme ks (substitute sub qt))]
        [(assumption i ts) (assumption i (substitute sub ts))]
        [else t])))

(define/contract (get-type-vars t)
  ((or/c (listof type?) type?) . -> . (listof type-variable?))
  (if (list? t)
      (apply list-union (map get-type-vars t))
      (match t
        [(type-variable _ _) (list t)]
        [(type-app l r) (list-union (get-type-vars l) (get-type-vars r))]
        [(qualified ps head) (list-union (get-type-vars ps)
                                         (get-type-vars head))]
        [(predicate _ t) (get-type-vars t)]
        [(scheme _ qt) (get-type-vars qt)]
        [(assumption _ ts) (get-type-vars ts)]
        [else (list)])))

;; @@ is the infix operator for substitution composition
(define/contract (@@ s1 s2)
  (subst/c subst/c . -> . subst/c)
  (define ls (for/list ([tup (in-list s2)])
               (cons (car tup) (substitute s1 (cdr tup)))))
  (append ls s1))

(define/contract (merge s1 s2 #:fail-with [fw error-format])
  (->* (subst/c subst/c) (#:fail-with (fail-proc/c monad?)) monad?)
  (define (heads ls) (map car ls))
  (let ([agreeable (andmap (lambda (v) (equal? (substitute s1 v)
                                          (substitute s2 v)))
                           (list-intersect (heads s1) (heads s2)))])
    (if agreeable
        (da:pure (append s1 s2))
        (fw "merge fail"))))

(define/contract (most-general-unifier t1 t2 #:fail-with [fw error-format])
  (->* (type? type?) (#:fail-with (fail-proc/c monad?)) monad?)
  (match (cons t1 t2)
    [(cons (predicate i t) (predicate ii tt))
     #:when (symbol=? i ii)
     (most-general-unifier t tt #:fail-with fw)]

    [(cons (type-app ll rl) (type-app lr rr))
     (do [s1 <- (most-general-unifier ll lr #:fail-with fw)]
         [s2 <- (most-general-unifier (substitute s1 rl)
                                      (substitute s1 rr)
                                      #:fail-with fw)]
       (da:pure (s2 . @@ . s1)))]
    [(cons u t)
     #:when (type-variable? u)
     (bind-variable u t #:fail-with fw)]
    [(cons t u)
     #:when (type-variable? u)
     (bind-variable u t #:fail-with fw)]
    [(cons tc1 tc2)
     #:when (and (type-const? tc1)
                 (type-const? tc2)
                 (equal? tc1 tc2))
     (da:pure empty-subst)]
    [else (fw "Types: ~a\n~a do not unify." t1 t2)]))

(define/contract (bind-variable u t #:fail-with [fw error-format])
  (->* (type-variable? type?)
       (#:fail-with (fail-proc/c monad?)) monad?)
  (cond [(and (type-variable? t)
              (equal? u t))
         (da:pure empty-subst)]
        [(member u (get-type-vars t))
         (fw "Occurs check fails")]
        [(not (equal? (get-kind u)
                      (get-kind t)))
         (fw "Kinds do not match")]
        [else (success (u . +-> . t))]))

(define/contract (type-match t1 t2 #:fail-with [fw failure])
  (->* (type? type?)
       (#:fail-with (fail-proc/c monad?)) monad?)
  (match (cons t1 t2)
    [(cons (type-app ll rl) (type-app lr rr))
     (do [le <- (type-match ll lr #:fail-with fw)]
         [re <- (type-match lr rr #:fail-with fw)]
       (merge le re #:fail-with fw))]
    [(cons (type-variable u kl) t)
     #:when (equal? kl (get-kind t))
     (da:pure (t1 . +-> . t))]
    [(cons (type-const idl kc1) (type-const idr kc2))
     #:when (and (symbol=? idl idr)
                 (equal? kc1 kc2))
     (da:pure empty-subst)]
    [else (fw "Types do not match")]))

(define/contract (lift-unifier f p1 p2)
  ((predicate? predicate? . -> . (result/c subst/c))
   predicate? predicate? . -> . (result/c subst/c))
  (define i (predicate-id p1))
  (define ii (predicate-id p2))
  (if (symbol=? i ii)
      (f p1 p2)
      (failure-format "Differing classes ~a ~a" i ii)))

(define/contract (most-general-unifier/predicate p1 p2)
  (predicate? predicate? . -> . (result/c subst/c))
  (lift-unifier (curry most-general-unifier
                       #:fail-with failure-format) p1 p2))

(define/contract (type-match/predicate p1 p2)
  (predicate? predicate? . -> . (result/c subst/c))
  (lift-unifier (curry type-match
                       #:fail-with failure-format) p1 p2))

;; ------------------------------------------------
;; Class environemnts

(define/contract #;INTERNAL (env-super env i)
  (tclass-env? symbol? . -> . (listof symbol?))
  (match ((tclass-env-classes env) i)
    [(success (tclass ids _)) ids]
    [(failure msg)
     (error-format "INTERNAL: env-super shouldn't return failure ~a" msg)]))

(define/contract #;INTERNAL (env-insts env i)
  (tclass-env? symbol? . -> . (listof (qualified/c predicate?)))
  (match ((tclass-env-classes env) i)
    [(success (tclass _ is)) is]
    [(failure msg)
     (error-format "INTERNAL: env-insts shouldn't return failure ~a" msg)]))

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
           (failure-format "No class for instance '~a" i)]
          [(ormap (curry overlap? p) qs)
           (define first-overlap (findf (curry overlap? p) qs))
           (failure-format "Overlapping instances\n~a \n~a" p first-overlap)]
          [else (success (env-bind env i c))])))

(module+ test
  (define-syntax (check-list-eqv? stx)
    (syntax-case stx ()
      [(_ ac ex)
       #'(let ([r1 ac] [r2 ex])
           (check list-eqv? r1 r2
                  (format "List difference: ~a" (list-diff r1 r2))))]))

  (define a-ty (type-variable 'a0 kind-star))
  (define b-ty (type-variable 'b0 kind-star))
  (define fishy-env
    (%extend-environment empty-environment
                         (env-add-class 'Fish '())
                         (env-add-class 'BlueFish '(Fish))
                         (env-add-class 'RedFish '(Fish))
                         (env-add-class 'PurpleFish '(RedFish BlueFish))
                         (env-add-class 'HungryFish '(PurpleFish))
                         (env-add-inst '() (predicate 'Fish %unit))
                         #;(env-add-inst (list (predicate 'Fish a-ty))
                                         (predicate 'Fish ($make-list a-ty)))))

  (check-equal? a-ty a-ty)
  (check-equal? %unit %unit)
  (check-equal? (predicate 'Fish %unit)
                (predicate 'Fish %unit))
  (check-equal? (qualified '() (predicate 'Fish %unit))
                (qualified '() (predicate 'Fish %unit)))
  (check-list-eqv? (env-super fishy-env 'Fish) '())
  (check-list-eqv? (env-super fishy-env 'BlueFish) '(Fish))
  (check-list-eqv? (env-super fishy-env 'RedFish) '(Fish))
  (check-list-eqv? (env-super fishy-env 'PurpleFish) '(RedFish BlueFish))
  (check-list-eqv? (env-super fishy-env 'HungryFish) '(PurpleFish))
  (check-list-eqv? (env-insts fishy-env 'Fish)
                   (list (qualified '() (predicate 'Fish %unit)))))

(define/contract (by-super env p)
  (tclass-env? predicate? . -> . (listof predicate?))
  (match-define (predicate i t) p)
  (define ll (for/list ([ip (in-list (env-super env i))])
               (by-super env (predicate ip t))))
  (cons p (concat ll)))

(define/contract (by-inst env p)
  (tclass-env? predicate? . -> . (result/c (listof predicate?)))
  (match-define (predicate i _) p)
  (define/contract (try-inst ql)
    (qualified? . -> . (result/c (listof (listof predicate?))))
    (match-define (qualified ps h) ql)
    (do [u <- (type-match/predicate h p)]
        (success (map (curry substitute u) ps))))
  (define ll (map try-inst (env-insts env i)))
  (define ls (filter success? ll))
  (if (null? ls)
      (failure "No suitable instance found")
      (success (car ls))))

;; Given a type class environment, report whether or not p
;; holds when all predicates ps are satisfied.
(define/contract (entails? env ps p)
  (tclass-env? (listof predicate?) predicate? . -> . boolean?)
  ;; predicate p is deduced by a super
  (and (or (ormap (curry member p) (map (curry by-super env) ps))
           ;; otherwise, for all predicates qs of a matching instance
           ;; the predicates ps must follow.
           (match (by-inst env p)
             [(failure _) #false]
             [(success qs) (andmap (curry entails? env ps) qs)]))
       #true))

(define/contract (head-normal-form? prd)
  (predicate? . -> . boolean?)
  (define (r v)
    (cond [(type-variable? v) #true]
          [(type-const? v) #false]
          [(type-app? v) (r (type-app-t1 v))]
          [else (error-format "INTERNAL: invalid type ~a" v)]))
  (r (predicate-t prd)))

(define/contract (->head-normal-form+ env ps #:fail-with [fw error-format])
  (->* (tclass-env? (listof predicate?)) (#:fail-with (fail-proc/c monad?)) monad?)
  (do [pss <- (map/m (curry ->head-normal-form env #:fail-with fw) ps)]
      (da:pure (concat pss))))

(define/contract (->head-normal-form env p #:fail-with [fw error-format])
  (->* (tclass-env? predicate?) (#:fail-with (fail-proc/c monad?)) monad?)
  (if (head-normal-form? p)
      (->TI (list p))
      (match (by-inst env p)
        [(failure msg) (fw "Context reduction: ~s" msg)]
        [(success ps) (->head-normal-form+ env ps #:fail-with fw)])))

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

(define/contract (reduce env ps #:fail-with [fw error-format])
  (->* (tclass-env? (listof predicate?))
       (#:fail-with (fail-proc/c monad?)) monad?)
  (do [qs <- (->head-normal-form+ env ps #:fail-with fw)]
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

(define/contract (find-in-assumptions id as #:fail-with [fw error-format])
  (->* (symbol? (listof assumption?))
       (#:fail-with (fail-proc/c monad?)) monad?)
  (match as
    [(list) (fw "unbound identifier: ~a" id)]
    [(list (assumption i ts) as ...)
     (if (symbol=? id i)
         (da:pure ts)
         (find-in-assumptions id as #:fail-with fw))]))

(define/contract (unify t1 t2)
  (type? type? . -> . TI/c)
  (do [s <- (get-subst)]
      [u <- (most-general-unifier (substitute s t1)
                                  (substitute s t2)
                                  #:fail-with fail/m)]
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
;; Core standard library
;; -----------------------------------------------
;;
;; XXX This /very unstable/ version of the Core library
;; needs to get expanded drastically. It also should
;; be written in Klein code when the expansion happens.
;; For this to happen:
;; [ ] the typechecker needs to be stable
;; [ ] explicit types / classes allowed in parsing K0
;; -----------------------------------------------

(define empty-environment
  (tclass-env
   (lambda (id) (failure-format "Identifier '~a unbound in class environment" id ))
   (list %int %float)))

;; A list of the STD numeric class tower.
;; [ ] TODO extend me.
;; [ ] TODO remove me and write Klein code that replaces me.
(define numeric-classes
  '(Numeric
    Fractional
    Int
    Float))

;; A list of the Core Klein classes.
;; [ ] TODO extend me.
(define core-classes
  '(Equal))

(define env+core-classes
  (lambda (env)
    (%extend-environment
     env
     (env-add-class 'Equal '()))))

(define env+numeric-classes
  (lambda (env)
    (%extend-environment
     env
     (env-add-class 'Numeric '(Equal))
     (env-add-class 'Fractional '(Numeric))
     (env-add-class 'Int '(Numeric))
     (env-add-class 'Float '(Fractional)))))

;; TODO split the instances up by numeric and core
;; TODO remove me and write Klein code that replaces me
(define env+pervasive-instances
  (let ([ty-a (type-variable 'a kind-star)])
    (lambda (env)
      (%extend-environment
       env
       (env-add-inst '() (predicate 'Equal %unit))
       (env-add-inst '() (predicate 'Equal %char))
       (env-add-inst '() (predicate 'Equal %int))
       (env-add-inst '() (predicate 'Equal %float))
       ;; ---
       (env-add-inst '() (predicate 'Numeric %int))
       (env-add-inst '() (predicate 'Float %float))
       ;; ---
       #;(env-add-inst (list (predicate 'Int ty-a)) (predicate 'Numeric ty-a))
       #;(env-add-inst (list (predicate 'Float ty-a)) (predicate 'Fractional ty-a))
       ;; ---
       #;(env-add-inst (list (predicate 'Fractional ty-a)) (predicate 'Numeric ty-a))
       ))))

(define env+pervasives
  (compose env+pervasive-instances
           env+numeric-classes
           env+core-classes))

(define core-environment
  (env+pervasives empty-environment))

(define empty-assumptions '())

(define core-assumptions
  ;; TODO synchronize this with the primitives
  (list* (assumption'#%identity ;; TODO REMOVE
          (scheme (list kind-star)
                  (qualified '()
                             ($make-func (type-gen 0)
                                         (type-gen 0)))))
         ;; ---
         (let ([t (type-gen 0)])
           (assumption '#%num+
                       (scheme (list kind-star)
                               (qualified (list (predicate 'Numeric t))
                                          ($make-func t t t)))))
         empty-assumptions))

;; -----------------------------------------------

(define/contract (ambiguities env vs ps)
  (tclass-env? (listof type-variable?)
               (listof predicate?) . -> . (listof ambiguity?))
  (for/list ([v (in-list (list-diff (get-type-vars ps) vs))])
    (define preds (filter (compose (curry member v)
                                   get-type-vars) ps))
    (ambiguity v preds)))

(define/contract (default-candidates env amb)
  (tclass-env? ambiguity? . -> . (listof type?))
  (error "YELP finish defaulting")
  ;; An ambiguity can be defaulted if it meets specific criteria. Currently, no
  ;; ambiguities will be defaulted and must be specified by the programmer.
  ;; These conditions are as follows:
  ;; - All QS predicates are of the form: (predicate _ (type-variable _)).
  ;; - One of the classes involved is a numeric class.
  ;; - All classes involved are from the standard library.
  ;; https://web.cecs.pdx.edu/~mpj/thih/TypingHaskellInHaskell.html#Haskell98
  ;; (match-define (ambiguity v qs) amb)
  ;; (define is (map ... qs))
  ;; (define ts (map ... qs))
  #;(for/list (#:do [(define )])))

(define/contract (with-defaults f env vs ps #:fail-with [fw error-format])
  (->* (((listof ambiguity?) (listof type?) . -> . any/c)
        tclass-env? (listof type-variable?)
        (listof predicate?))
       (#:fail-with (fail-proc/c monad?)) monad?)
  (define vps (ambiguities env vs ps))
  (define tss (map (curry default-candidates env) vps))
  (cond [(ormap null? tss) (failure "cannot resolve ambiguity")]
        [else (success (f vps (map car tss)))]))

(define (default-predicates env vs ps #:fail-with [fw error-format])
  (with-defaults (lambda (vps ts)
                   (concat (map cadr vps))) env vs ps #:fail-with fw))

(define (default-subst env vs ps #:fail-with [fw error-format])
  (with-defaults (lambda (vps ts)
                   (map cons (map car vps) ts)) env vs ps #:fail-with fw))

;; -----------------------------------------------
;; Type inference for K3 constructs
;; -----------------------------------------------

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
  (check-typed-prog? #:run-from ti-literal
                     ;; #:unwrap-value ti-value
                     ;; #:value-equal? %char
                     #\U)
  (check-typed-prog? #:run-from ti-literal 100))

(define (ti-pattern p)
  (nanopass-case (K3 Pattern) p
    [,var
     (do [v <- (fresh-tv kind-star)]
         (->TI `(() ,(list (assumption var (type->scheme v))) . ,v)))]
    [,lit
     (do [(cons ps t) <- (ti-literal lit)]
         (->TI `(,ps () . ,t)))]))

(define (ti-pattern+ ps)
  #;((listof pattern?) . -> . TI/c)
  (do [psasts <- (map/m ti-pattern ps)]
      (define ps (concat (map car psasts)))
      (define as (concat (map cadr psasts)))
      (define ts (map cddr psasts))
      (->TI (cons ps (cons as ts)))))

;; TODO get rid of this struct once explicit bindings are allowed
;; in letrec statements.
(struct bind-group (expls impls)
  #:transparent
  #:sealed
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (o) 'BindGroup)
      (lambda (o) (list (bind-group-expls o)
                   (bind-group-impls o)))))])

  (define (ti-seq ti-f env as bs)
    (match bs
      [(list) (->TI (cons '() '()))]
      [(list bs bss ...)
       (do [(cons ps asp) <- (ti-f env as bs)]
           [(cons qs aspp) <- (ti-seq ti-f env (append asp as) bss)]
         (->TI (cons (append ps qs) (append aspp asp))))]))


(define (ti-expr env as e)
  ;; A quick return for Expressions
  (define (return ss t) (->TI (cons ss t)))
  (nanopass-case (K3 Expr) e
    [,var
     (do [sc <- (find-in-assumptions var as #:fail-with fail/m)]
         [(qualified ps t) <- (fresh-inst sc)]
         (return ps t))]
    [,prim ;; Typecheck the same way a variable would be
    (do [sc <- (find-in-assumptions prim as #:fail-with fail/m)]
        [(qualified ps t) <- (fresh-inst sc)]
      (return ps t))]
    [,lit (ti-literal lit)]
    ;; TODO not ported to nanopass style
    #;[(expr-const (assumption id scm))
      (do [(qualified ps t) <- (fresh-inst scm)]
          (return ps t))]
    [(,e0 ,e1)
     (do [(cons ps te) <- (ti-expr env as e0)]
         [(cons qs tf) <- (ti-expr env as e1)]
         [t <- (fresh-tv kind-star)]
         (unify ($make-func tf t) te)
         (return (append ps qs) t))]
    [(letrec ((,df ...) ...) ,e)
     (do (define bg (bind-group '() df)) ;; TODO FIXME explicitly typed bgs
         [(cons ps asp) <- (ti-bind-group env as bg)]
         [(cons qs t) <- (ti-expr env (append asp as) e)]
         (return (append ps qs) t))]))

(module+ test
  (check-typed-prog?
   #:run-from ti-expr
   core-environment core-assumptions
   (with-output-language (K3 Expr)
     `0))

  (check-typed-prog?
   #:run-from ti-expr
   core-environment core-assumptions
   (with-output-language (K3 Expr)
     `((#%num+ 0) 1))))

(define (ti-alternative env as a)
  #;(tclass-env? (listof assumption?) alternative? . -> . TI/c)
  (nanopass-case (K3 Alternative) a
    [((,pat ...) ,body)
     (do [(cons ps (cons asp ts)) <- (ti-pattern+ pat)]
         [(cons qs t) <- (ti-expr env (append asp as) body)]
         (->TI (cons (append ps qs)
                     (foldr (lambda (t1 t2)
                              ($make-func t1 t2)) t ts))))]))

(define (ti-alternative+ env as alts t)
  #;(tclass-env? (listof assumption?)
                 (listof alternative?) type? . -> . TI/c)
  (do [psts <- (map/m (curry ti-alternative env as) alts)]
      (map/m (curry unify t) (map cdr psts))
      (->TI (concat (map car psts)))))

(define (ti-explicit env as bgex)
  (error "INTERNAL ERROR : explicitly typed bindings unsupported" bgex)
  #;(tclass-env? (listof assumption?) bg-explicit? . -> . TI/c)
  #;(match-define (bg-explicit i scm alts) bgex)
  #;(do [(qualified qs t) <- (fresh-inst scm)]
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

(define (df-var df)
  (nanopass-case (K3 Definition) df
    [(bind ,var ,alt ,alt0* ...) var]))
(define (df-alts df)
  (nanopass-case (K3 Definition) df
    [(bind ,var ,alt0 ,alt* ...) (list* alt0 alt*)]))

(define (restricted? bs)
  ;; simple? returns whether or not the binding is a variable binding.
  ;; As opposed to a procedure binding.
  (define (simple? impls)
    (nanopass-case (K3 Definition) impls
      [(bind ,var ,alt0 ,alt* ...)
       (ormap (lambda (alt)
                (nanopass-case (K3 Alternative) alt
                  [((,pat ...) ,body)
                  (null? pat)])) (list* alt0 alt*))]))
  (ormap simple? bs))

;; NOTE bs is a lsit of implicitly typed bindings,
;; howver, at the K3 level this is a `(df ...).
(define (ti-implicit+ env as bs)
  #;(tclass-env? (listof assumption?) (listof implicit/c) . -> . TI/c)
  (do [ts <- (map/m (lambda _ (fresh-tv kind-star)) bs)]
      (define is (map df-var bs))
      (define scs (map type->scheme ts))
      (define asp (append (map assumption is scs) as))
      (define altss (map df-alts bs))
      [pss <- (map/m values (map (curry ti-alternative+ env asp) altss ts))]
      [s <- (get-subst)]
      (define psp (substitute s (concat pss)))
      (define tsp (substitute s ts))
      (define fs (get-type-vars (substitute s as)))
      (define vss (map get-type-vars tsp))
      (define gs (list-diff (foldr1 list-union vss) fs))
      [(cons ds rs) <- (split env fs (foldr1 list-intersect vss) psp
                              #:fail-with fail/m)]
      (if (restricted? bs)
          (let* ([gsp (list-diff gs (get-type-vars rs))]
                [scsp (map (compose (curry quantify gsp)
                                    (curry qualified '())) tsp)])
            (->TI (cons (append ds rs) (map assumption is scsp))))
          (let ([scsp (map (compose (curry quantify gs)
                                    (curry qualified rs)) tsp)])
            (->TI (cons ds (map assumption is scsp)))))))

(module+ test
  (check-typed-prog?
   #:run-from ti-implicit+
   core-environment core-assumptions
   (list (with-output-language (K3 Definition)
           `(bind main (() 0)))))

  (check-typed-prog?
   #:run-from ti-implicit+
   core-environment core-assumptions
   (list (with-output-language (K3 Definition)
           `(bind main (() #%identity)))))

  (check-typed-prog?
   #:run-from ti-implicit+
   core-environment core-assumptions
   (list (with-output-language (K3 Definition)
           `(bind main (() (#%identity 0))))))

  (check-typed-prog?
   #:run-from ti-implicit+
   core-environment core-assumptions
   (list (with-output-language (K3 Definition)
           `(bind main (() ((#%num+ 0) 1)))))))

(define (ti-bind-group env as bg)
  #;(tclass-env? (listof assumption?) bind-group? . -> . TI/c)
  (match-define (bind-group es iss) bg)
  (unless (null? es)
    (error "INTERNAL: explicitly typed bindings unsupported"))
  (do (define asp '()
        #;(for/list ([e (in-list es)])
          (match-define (bg-explicit v scm alts) e)
          (assumption v scm)))
      [(cons ps aspp) <- (ti-seq ti-implicit+ env (append asp as) iss)]
    [qss <- (map/m (curry ti-explicit env (append aspp asp as)) es)]
    (->TI (cons (append ps (concat qss))
                (append aspp asp)))))

(define/contract (split env fs gs ps #:fail-with [fw error-format])
  (->* (tclass-env? (listof type-variable?)
                    (listof type-variable?)
                    (listof predicate?))
       (#:fail-with (fail-proc/c monad?)) monad?)
  (do [psp <- (reduce env ps #:fail-with fw)]
      (define-values (ds rs)
        (partition
         (compose (curry andmap (curryr member fs))
                  get-type-vars) psp))
      [rsp <- (default-predicates env (append fs gs) rs
                #:fail-with fw)]
      (->TI (cons ds (list-diff rs rsp)))))

(module+ test
  (check-typed-prog?
   #:run-from ti-bind-group
   core-environment core-assumptions
   (bind-group '()
               (list
                (list
                 (with-output-language (K3 Definition)
                   `(bind main (() ((#%num+ 0) 1)))))))))

(define (#%typecheck-K3 env as p)
  (nanopass-case (K3 Program) p
                 [(((,df ...) ...) ...)
                  (define bgs (map (lambda (df*) (bind-group '() df*)) df))
                  (do [(cons ps asp) <- (ti-seq ti-bind-group env as bgs)]
                      [s <- (get-subst)]
                      [rs <- (reduce env (substitute s ps) #:fail-with fail/m)]
                      [sp <- (default-subst env '() rs #:fail-with fail/m)]
                      (->TI (substitute (sp . @@ . s) asp)))]))

;; TODO This pass should output a language K4 which has explicit type information added
;; to each construcut. This will need a few tweaks, for now, just fail and output
;; the same language.
(define (typecheck-K3 env as p)
  (match (<-TI (#%typecheck-K3 env as p))
    [(success asps) p]
    [(failure msg)
     (error "Failed to typecheck" msg)]))

#;(module+ test
  (check-typed-prog?
   core-environment core-assumptions
   (with-output-language (K3 Program)
     `((((bind main (() ((#%num+ 0) 1))))))))

  (typecheck-K3
   core-environment core-assumptions
   (with-output-language (K3 Program)
     `((((bind id ((x) x)))
        ((bind main (() ((#%num+ 0) (x 1))))))))))
