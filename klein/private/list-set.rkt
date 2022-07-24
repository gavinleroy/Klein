#lang racket/base

(require racket/match
         racket/list)

(provide list-diff
         list-union
         list-intersect
         foldr1)

(define (list-diff as bs)
  (foldr (lambda (e s)
            (if (member e bs)
                s
                (cons e s))) '() as))

(define (list-union . as)
  (remove-duplicates (apply append as)))

(define (list-intersect . as)
  (define (outer is bs)
    (let loop ([ls is])
      (cond [(null? ls) '()]
            [else (if (member (car ls) bs)
                      (cons (car ls) (loop (cdr ls)))
                      (loop (cdr ls)))])))
  (foldr1 outer as))

(define (foldr1 f ls)
  (define/match (loop rs)
    [((list)) (error "foldr1 expects non-null? lists")]
    [((list a)) a]
    [((list a b ...)) (f a (loop (cdr rs)))])
  (loop ls))

(module+ test
  (require rackunit)
  (check-equal? (list-union '(1) '(2) '(4) '(3)) '(1 2 4 3))
  (check-equal? (list-union '(1 2 3) '(3 2 1)) '(1 2 3))
  (check-equal? (list-union '(3 2 1) '(1 2 3)) '(3 2 1))
  (check-equal? (list-union '(3 3 2 3 1) '(1 2 5 3)) '(3 2 1 5))

  (check-equal? (list-intersect '(1) '(2) '(4) '(3)) '())
  (check-equal? (list-intersect '(1 2 3)) '(1 2 3))
  (check-equal? (list-intersect '(3 2 1) '(1 2 3)) '(3 2 1))
  (check-equal? (list-intersect '(3 5 2 1 7 1 1) '(8 8  9 7 5)) '(5 7))

  (check-equal? (list-diff '(1 2 3) '(1 2)) '(3))
  (check-equal? (list-diff '(1 2 3) '(1 2 3)) '())
  (check-equal? (list-diff '(1 2 3) '()) '(1 2 3))
  (check-equal? (list-diff '(1) '(5 6 7)) '(1))
  (check-equal? (list-diff '() '(5 6 7)) '()))
