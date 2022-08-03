#lang racket/base

(require "private/typing.rkt")

(define (usage l)
  (cond [(kind-fun? l) #true]))

(module+ main
  (display 'hello))
