#lang plai
;; include define of function and call of function (single parameter)
;; data structure
(define-type F1WAE
  [num (n number?)]
  [add (lhs F1WAE?)
       (rhs F1WAE?)]
  [sub (lhs F1WAE?)
       (rhs F1WAE?)]
  [with (id symbol?)
        (expr F1WAE?)
        (body F1WAE?)]
  [id (name symbol?)]
  ;; app is a function call
  [app (func-name symbol?)
       (arg-expr F1WAE?)])

;; structure F1WAE and function definiation type
(define-type FunDef
  [fundef (func-name symbol? )
          (arg-name symbol? )
          (body F1WAE?)])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; we still need a subst function to replace all
;; the free identifiers with number
(define/contract (subst a-f1wae sub-id val)
  ; subst function substitute all free identifier in the wae by a val
  ; be careful to shadowing
  ; it is innitally used in local variable binding but we can apply it to function
  (-> F1WAE? symbol? number? F1WAE?)
  (type-case F1WAE a-f1wae
    [num (n) a-f1wae]
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
                       a-f1wae)]
    [app (func-name arg-expr) (app func-name        ; function and local variable are seperate
                                   (subst arg-expr sub-id val))]))

;; takes a func-name return the funcdef
(define/contract (func-lookup f-name fundefs)
  (-> symbol? (listof fundef?) fundef?)
  (cond
    [(empty? fundefs)
     (error "error function" f-name 'not 'found)]
    [(symbol=? (fundef-func-name (first fundefs))
               f-name) (first fundefs)]
    [else (func-lookup f-name (rest fundefs))]))


;; input f1wae and list of function def -> number
(define (interp a-fwae fundefs)
  (-> F1WAE? (listof fundef?))
  (type-case F1WAE a-fwae
    [num (n) n]
    [add (l r) (+ (interp l fundefs) (interp r fundefs))]
    [sub (l r) (- (interp l fundefs) (interp r fundefs))]
    [with (with-id with-expr with-body)
          (interp (subst with-body
                         with-id
                         (interp with-expr fundefs))
                  fundefs)]
    [id (name) (error "free identifier" name)]
    [app (func-name arg-expr)
         (type-case FunDef (func-lookup func-name fundefs)
           [fundef (f-name f-arg f-body) (interp (subst f-body
                                                        f-arg
                                                        (interp arg-expr
                                                                fundefs))
                                                 fundefs)])]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; test cases
(test (interp (num 10) empty) 10)
(test (interp (add (num 1) (num 2)) empty) 3)
(test (interp (sub (num 2) (num 1)) empty) 1)
(test (interp (add (add (num 1) (num 2))
                   (sub (num 8) (num 1)))
              empty) 10)
(test/exn (interp (id 'x) empty) "free identifier")
(test (interp (with 'x (num 1) (add (num 2) (num 4))) empty) 6)
(test (interp (with 'x (num 1) (add (id 'x) (num 5))) empty) 6)
(test (interp (with 'x (num 1)
                    (with 'x (num 2)
                          (add (id 'x) (id 'x)))) empty) 4)
(test (interp (with 'x (num 1)
                    (add (with 'x (num 2)
                               (add (id 'x) (id 'x)))
                         (id 'x))) empty) 5)

(test (interp (add (app 'double (add (num 1) (num 2)))
                   (num 2))
              (list (fundef 'double 'x (add (id 'x) (id 'x)))))
      8)
;; with statement is like a loccal binding,
;; which can not intervene the bound occurence in functions
(test (interp (with 'x (num 10) (app 'double (id 'x)))
              (list (fundef 'double 'y (add (id 'y) (id 'y)))))
      20)

(test (interp (app 'f (num 10))
              (list
               (fundef 'f 'x
                       (sub (num 20)
                            (app 'twice (id 'x))))
               (fundef 'twice 'y
                       (add (id 'y) (id 'y)))))
      0)
(test/exn (interp (app 'foo (num 10)) '())
          "not found")
              




