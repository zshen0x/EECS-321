#lang racket
;(λ (f x)
;  x)
;(λ (f x)
;  (f x))
;(λ (f x)
;  (f (f x)))
;(λ (f x)
;  (f (f (f x)))) ...

; church encoding 

;; (-> church number next church number
(define (church-add1 church-num)
  (λ (f x) (f (church-num f x))))

(define (church n)
  (if (zero? n)
      (λ (f x) x)
      (church-add1 (church (sub1 n)))))

(define (church-add cn1 cn2)
  (λ (f x)
    (cn1 f (cn2 f x))))

(let ([church (λ (n)
                (let ([chch (λ (recur n)
                              (if (zero? n)
                                  (λ (f x) x)
                                  ((λ (chn) (λ (f x) (f (chn f x)))) (recur recur (sub1 n)))))])
                  (chch chch n)))]
      [de-church (λ (chn)
                   (chn (λ (x) (add1 x)) 0))]
      [church-add (λ (cn1 cn2)
                    (λ (f x)
                      (cn1 f (cn2 f x))))]
      ;; this is wrong
      [church-mult (λ (cn1 cn2)
                     (λ (f x) (cn1 f (cn2 f x))))])
  (de-church (church-add (church 10) (church 123))))