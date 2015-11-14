#lang plai

#|
FAE := ...
| ...
| ...
| ...
| ...
| ...
|#

;; generate randmo FAE : -> expr
;; h is the height of tree
(define (generate-fae h)
  ; 6 braches in FAE
  (case (if (zero? h) (random 2) (random 6))
    [(0) (random-nat)]
    [(1) (random-symbol)]
    [(2) `{}]
    [(3) `{}]
    [(4) `{}]
    [(5) `{}]))


(define (random-nat)
  (case (random 2)
    [(0) 0]
    [(1) (add1 (random-nat))]))

(define (random-symbol)
  (first (shuffle '(x d y a b c o z))))

;; random test
;; property should holds
