#lang racket/base

(require racket/match)

(provide list-diff
         list-union
         list-intersect
         foldr1)

(define (list-diff as bs)
  (cond [(null? as) as]
        [else (if (member (car as) bs)
                  (list-diff (cdr as) bs)
                  (cons (car as) (list-diff (cdr as) bs)))]))

(define (list-union as bs)
  (define (loop ls)
    (cond [(null? ls) bs]
          [else (let ([i (list-union (cdr ls))]
                      [a (car ls)])
                  (if (member a i)
                      i
                      (cons a i)))]))
  (loop as))

(define (list-intersect as bs)
  (define (loop ls)
    (cond [(null? ls) '()]
          [else (if (member (car ls) bs)
                    (cons (car ls) (loop (cdr ls)))
                    (loop (cdr ls)))]))
  (loop as))

(define (foldr1 f ls)
  (define/match (loop rs)
    [((list)) (error "foldr1 expects non-null? lists")]
    [((list a)) a]
    [((list a b ...)) (f a (loop (cdr rs)))])
  (loop ls))
