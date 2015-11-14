#lang plai/gc2/mutator
(allocator-setup "collector.rkt" 100)

(cons 1 2)
'()

(((λ (y z)
  (λ (x)
    (+ y x z))) 10 12) 11)



