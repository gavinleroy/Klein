#lang racket/base

(require racket/match
         racket/list
         "utils.rkt")

(provide list-diff
         list-union
         list-intersect
         foldr1
         list-eqv?
         list-duplicates?)

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

;; NOTE only for use in internal tests
(define (list-eqv? l1 l2)
  (and (= (length l1)
          (length l2))
       (null? (list-diff l1 l2))))

(define (list-duplicates? ls)
  (if (null? ls)
      #false
      (or (member (car ls) (cdr ls))
          (list-duplicates? (cdr ls)))))

(module+ test
  (require rackunit)
  (check-equal? (list-union '(1) '(2) '(4) '(3)) '(1 2 4 3))
  (check-equal? (list-union '(1) '(2) '() '(3)) '(1 2 3))
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
  (check-equal? (list-diff '(1 2 3) '(1 2 3)) '())
  (check-equal? (list-diff '(1) '(5 6 7)) '(1))
  (check-equal? (list-diff '() '(5 6 7)) '()))
