#lang racket
(require plai/random-mutator)
(save-random-mutator "tmp.rkt" "collector.rkt" #:gc2? #t)
