#lang plai


(let ([fac 10])
  (begin
    (set! fac
          (λ (n)
            (if (zero? n)
                1
                (* n (fac (sub1 n))))))
    (fac 10)))