#lang racket

; same as define
(local [(define fact
          (λ (x)
            (if (zero? x)
                1
                (* x (fact (sub1 x))))))]
  (fact 10))

(let ([facX
       (λ (f x)
         (if (zero? x)
             1
             (* x (f f (sub1 x)))))])
  (facX facX 10))

;; but we still want fact back
;; Wrap this to get fac back...
(let ([fact
       (λ (n)
         (let [(facX
                (λ (f n)
                  (if (zero? n)
                      1
                      (* n (f f (sub1 n))))))]
           (facX facX n)))])
  (fact 10))

(define f
  (λ (x)
    (λ (y)
      (λ (z)
        (list z x y)))))
(((f 1) 2) 3)

;; we want to implement multiple params


(let ([facX
       (λ (f n)
         (if (zero? n)
             1
             (* n (f f (sub1 n)))))])
  (facX facX 10))

(let ([fact
       (λ (n)
         (let ([facX
                (λ (f n)
                  (if (zero? n)
                      1
                      (* n (f f (sub1 n)))))])
           (facX facX n)))])
  (fact 10))


(let [(facX
       (λ (f)
         (λ (n)
           (if (zero? n)
               1
               (* n ((f f) (sub1 n)))))))]
  ((facX facX) 10))

(let ([fact
       (λ (n)
         (let [(facX
                (λ (f)
                  (λ (n)
                    (if (zero? n)
                        1
                        (* n ((f f) (sub1 n)))))))]
           ((facX facX) 10)))])
  (fact 20))

;; remove (λ (n) ...)
(let ([fact
         (let [(facX
                (λ (f)
                  (λ (n)
                    (if (zero? n)
                        1
                        (* n ((f f) (sub1 n)))))))]
           (facX facX))])
  (fact 10))

;; evaluate too early (f f)
;; infinte loop
;(let ([foo
;       (λ (f)
;         (f f))])
;  (foo foo))

;(let ([fact
;       (let [(facX
;              (λ (f)
;                (let ([fac (f f)])
;                  (λ (n)
;                    (if (zero? n)
;                        1
;                        (* n (fac (sub1 n))))))))]
;         (facX facX))])
;  (fact 10))

(let ([fact
         (let [(facX
                (λ (f)
                  (λ (n)
                    (let ([fac (λ (x)
                                 ((f f) x))])
                      (if (zero? n)
                        1
                        (* n (fac (sub1 n))))))))]
           (facX facX))])
  (fact 10))

;; y-conbination
(define (mk-rec body-proc)
  (let ([fX
         (λ (fX)
           (let ([f (λ (x)
                      ((fX fX) x))])
             (body-proc f)))])
(fX fX)))

(let ([fac (mk-rec
            (λ (fac)
              ; Exactly like original fac:
              (λ (n)
                (if (zero? n)
                    1
                    (* n (fac (- n 1)))))))])
  (fac 10))
  
;; generalize these pattern

;(let ([fact (λ (fact n)
;             (if (zero? n)
;                 1
;                 (* n (fact fact (- n 1)))))])
;  (fact fact 2))