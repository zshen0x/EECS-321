#lang racket
(require plai/random-mutator)
(save-random-mutator "tmp.rkt" "two-space-copying-gc.rkt" #:gc2? #t)
