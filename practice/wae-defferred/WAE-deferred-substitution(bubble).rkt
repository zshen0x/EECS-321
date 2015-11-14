#lang plai

(define-type WAE
  [num (n number?)]
  [add (rhs WAE?)
       (lhs WAE?)]
  [sub (rhs WAE?)
       (lhs WAE?)]
  [with (name symbol?)
        (expr WAE?)
        (body WAE?)]
  [id (name symbol?)])

(define-type DefSub
  [mtSub]               ;empty bubble
  [aSub (name symbol?)
        (value number?)
        (rest DefSub?)])

;; using deferred substitution rather than nomal substitution
;; change the way of interp

(define/contract (defsub-lookup name a-defsub)
  (-> symbol? DefSub? number?)
  (type-case DefSub a-defsub
    [mtSub () (error "error free identifier" name)]
    [aSub (n val rest) (if (symbol=? name n)
                           val
                           (defsub-lookup name rest))]))

(define/contract (interp a-wae a-defsub)
  (-> WAE? DefSub? number?)
  (type-case WAE a-wae
    [num (n) n]
    [add (l r) (+ (interp l a-defsub)
                  (interp r a-defsub))]
    [sub (l r) (- (interp l a-defsub)
                  (interp r a-defsub))]
    [with (with-id with-expr with-body) (interp with-body
                                                (aSub with-id
                                                      (interp with-expr
                                                              a-defsub)
                                                      a-defsub))]
    [id (name) (defsub-lookup name a-defsub)]))



;; test case
(test (interp (num 10) (mtSub)) 10)
(test (interp (add (num 1) (num 2)) (mtSub)) 3)
(test (interp (sub (num 2) (num 1)) (mtSub)) 1)
(test (interp (add (add (num 1) (num 2))
                   (sub (num 8) (num 1))) (mtSub)) 10)

(test/exn (interp (id 'x) (mtSub)) "free identifier")
(test (interp (with 'x (num 1) (add (num 2) (num 4))) (mtSub)) 6)
(test (interp (with 'x (num 1) (add (id 'x) (num 5))) (mtSub)) 6)
(test (interp (with 'x (num 1)
                    (with 'x (num 2)
                          (add (id 'x) (id 'x))))
              (mtSub))
      4)
(test (interp (with 'x (num 1)
                    (add (with 'x (num 2)
                               (add (id 'x) (id 'x)))
                         (id 'x)))
              (mtSub))
      5)