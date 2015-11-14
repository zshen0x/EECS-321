#lang plai

;; BNF grammar
#|
<FWAE> ::= <num>
| <number>
| {+ <FWAE> <FWAE>}
| {- <FWAE> <FWAE>}
| <id>
| {fun {<id>} <FWAE>}
| {<FWAE> <FWAE>}
|#

;; without with
;; using deferred evaluation
;; first class + higher order function powers
;; how to implement higher order function
;; to implement that we will using closure
;; higher order function will return a closure
(define-type FAE
  [num (n number?)]
  [add (lhs FAE?)
       (rhs FAE?)]
  [sub (lhs FAE?)
       (rhs FAE?)]
  [id (name symbol?)]
  [fun (param symbol?)
       (body FAE?)]
  [app (fun-expr FAE?)
       (arg-expr FAE?)])

;; FAE-Value is part of FAE (fun and num)
(define-type FAE-Value
  [numV (n number?)]
  ;; use closureV as function value
  ;; which contains param body and
  ;; its context when created
  [closureV (param symbol?)
            (body FAE?)
            (ds DefSub?)])
;; deprecated code
;;  [funV (param symbol?)
;;        (body FAE?)])

;; defsub data structure
;; order matters when evaluation with defsub
(define-type DefSub
  [mtSub]
  [aSub (id symbol?)
        (value FAE-Value?)
        (rest DefSub?)])


(define/contract (parse s-expr)
  (-> any/c FAE?)
  (match s-expr
    [(? number?) (num s-expr)]
    [(? symbol?) (id s-expr)]
    [`{+ ,lhs ,rhs} (add (parse lhs) (parse rhs))]
    [`{- ,lhs ,rhs} (sub (parse lhs) (parse rhs))]
    [`{with {,id ,e1} ,e2} (parse `{{fun {,id} ,e2} ,e1})]
    [`{fun {,param} ,body} (fun param (parse body))]
    [`{,fun-expr ,arg-expr} (app (parse fun-expr) (parse arg-expr))]
    [_ (error "bad syntax when parsing:\n~a" s-expr)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; interp part
(define/contract (num-op op)
  (-> (-> number? number? number?)
      (-> FAE-Value? FAE-Value? numV?))
  (λ (x y)
    (if (and (numV? x) (numV? y))
        (numV (op (numV-n x) (numV-n y)))
        (error "not a number"))))
(define num+ (num-op +))
(define num- (num-op -))

(define/contract (defsub-lookup id ds)
  (-> symbol? DefSub? FAE-Value?)
  (type-case DefSub ds
    [mtSub () (error "free identifier:\n" id)]
    [aSub (sub-id val rest) (if (symbol=? id sub-id)
                                val
                                (defsub-lookup id rest))]))

(define/contract (interp a-fae ds)
  (-> FAE? DefSub? FAE-Value?)
  (type-case FAE a-fae
    [num (n) (numV n)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [id (name) (defsub-lookup name ds)]
    [fun (param body) (closureV param body ds)]
    [app (fun-expr arg-expr)
         (type-case FAE-Value (interp fun-expr ds)
           [numV (n)
                 (error "called number~a not a function" n)]
           [closureV (param body closure-ds)
                     (interp body
                             (aSub param
                                   (interp arg-expr ds)
                                   closure-ds))])]))

;; test case
;; test case parse create a syntax valid FAE
(print-only-errors)
(test (parse '1) (num 1))
(test (parse '{+ 1 2}) (add (num 1) (num 2)))
(test (parse '{fun {x} {+ x 1}})
      (fun 'x (add (id 'x) (num 1))))
(test (parse '{{fun {x} {+ x 1}} 10})
      (app (fun 'x (add (id 'x) (num 1))) (num 10)))
(test (parse '{fun {x} {+ x x}}) (fun 'x (add (id 'x) (id 'x))))
(test/exn (parse '{1 2 3}) "bad syntax")
;; interp test case
(test (interp (parse '{+ 1 2}) (mtSub)) (numV 3))
(test/exn (interp (parse '{- x 1}) (mtSub)) "free")
(test (interp (parse '{fun {x} 1}) (mtSub)) (closureV 'x (num 1) (mtSub)))
(test (interp (parse '{{fun {x} {+ x x}} 2}) (mtSub)) (numV 4))
(test (interp (parse '{{fun {x} {x 2}} {fun {x} {+ x {+ x x}}}}) (mtSub)) (numV 6))
(test (interp (parse '{{{fun {x} {fun {y} {+ x y}}} 1} 2}) (mtSub)) (numV 3))

(test/exn (interp (parse '{+ {fun {x} x} 1}) (mtSub)) "not a number")
(test/exn (interp (parse '{1 2}) (mtSub)) "not a function")

