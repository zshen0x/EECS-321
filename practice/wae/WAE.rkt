#lang plai

;; representation of a Arithmatic Expression
;; With Arithmetic Expression
(define-type WAE
  [num (n number?)]
  [add (rhs WAE?)
       (lhs WAE?)]
  [sub (rhs WAE?)
       (lhs WAE?)]
  [with (name symbol?)
        (expr WAE?)
        (body WAE?)] ; with is a binding also suppose with statement as a data structure and a syntax
  [id (name symbol?)]
  )

;; interp take a AE and return the expression number

(define/contract (subst a-wae sub-id val)
  ; subst function substitute all free identifier in the wae by a val
  ; be careful to shadowing
  (-> WAE? symbol? number? WAE?)
  (type-case WAE a-wae
    [num (n) a-wae]
    [add (l r) (add (subst l sub-id val)
                    (subst r sub-id val))]
    [sub (l r) (sub (subst l sub-id val)
                    (subst r sub-id val))]
    [with (with-id with-expr with-body)
          (with with-id
                (subst with-expr sub-id val)
                (if (symbol=? with-id sub-id)
                    with-body                       ; when id is not free variable in the with-body
                    (subst with-body sub-id val)))] ; else
    [id (a-symbol) (if (symbol=? a-symbol sub-id)
                       (num val)
                       a-wae)]))

(test (subst (add (id 'x) (id 'x)) 'x 1)
      (add (num 1) (num 1)))
(test (subst (sub (id 'y) (id 'y)) 'x 1)
      (sub (id 'y) (id 'y)))
;; important!!! when you do subst in with
;; with expression if named-id is
;; important!!! with statement is just defined
;;in our language(don't mix up with others)
(test (subst (with 'x (id 'y) (id 'x)) 'x 10)
      (with 'x (id 'y) (id 'x)))
(test (subst (with 'x (num 1) (id 'y)) 'y 10)
      (with 'x (num 1) (num 10)))
(test (subst (add (num 1) (id 'x)) 'x 10)
      (add (num 1) (num 10)))
(test (subst (id 'x) 'x 10)
      (num 10))
;; also we should notice that subst should work in expr
#|
say when interp (with 'x (num 1) (with 'y (id 'x) (id 'y)))
|#
(test (subst (with 'y (id 'x) (id 'y)) 'x 10)
      (with 'y (num 10) (id 'y)))


(define/contract (interp a-wae)
  (-> WAE? number?)
  (type-case WAE a-wae
    [num (n) n]
    [add (r l) (+ (interp r) (interp l))]
    [sub (r l) (- (interp r) (interp l))]
    ;with itself means subsitute all the free-identifier in body with named-expr
    [with (bind-id named-expr body) (interp (subst body bind-id
                                                   (interp named-expr)))]
    [id (name) (error "error free identifier " name)]))

(test (interp (num 10)) 10)
(test (interp (add (num 1) (num 2))) 3)
(test (interp (sub (num 2) (num 1))) 1)
(test (interp (add (add (num 1) (num 2))
                   (sub (num 8) (num 1)))) 10)
(test/exn (interp (id 'x)) "free identifier")
(test (interp (with 'x (num 1) (add (num 2) (num 4)))) 6)
(test (interp (with 'x (num 1) (add (id 'x) (num 5)))) 6)
(test (interp (with 'x (num 1)
                    (with 'x (num 2)
                          (add (id 'x) (id 'x))))) 4)
(test (interp (with 'x (num 1)
                    (add (with 'x (num 2)
                               (add (id 'x) (id 'x)))
                         (id 'x)))) 5)






