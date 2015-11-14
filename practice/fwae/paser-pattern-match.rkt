#lang plai

;; BNF grammar
#|
<FWAE> ::= <num>
| {+ <FWAE> <FWAE>}
| {- <FWAE> <FWAE>}
| {with {<id> <FWAE>} <FWAE>}
| <id>
| {fun {<id>} <FWAE>}
| {<FWAE> <FWAE>}
|#

;; data structure
(define-type FWAE
  [num (n number?)]
  [add (rhs FWAE?)
       (lhs FWAE?)]
  [sub (rhs FWAE?)
       (lhs FWAE?)]
  [with (name symbol?)
        (expr FWAE?)
        (body FWAE?)]
  [id (name symbol?)]
  [fun (param symbol?)
       (body FWAE?)]
  [app (fun-expr FWAE?)
       (arg-expr FWAE?)]
  )

;; paser using pattern match
(define/contract (parse s-expr)
  (-> any/c FWAE?)
  (match s-expr
    [`{+ ,lhs ,rhs} (add (parse lhs) (parse rhs))]
    [`{- ,lhs ,rhs} (sub (parse lhs) (parse rhs))]
    [`{with {,id ,rhs} ,body} (with id (parse rhs) (parse body))]
    [`{fun {,id} ,body} (fun id (parse body))]
    [`{,e1 ,e2} (app (parse e1) (parse e2))]
    [_ (cond
         [(number? s-expr) (num s-expr)]
         [(symbol? s-expr) (id s-expr)]
         [else (error "syntax error in:\n~a" s-expr)])]))

;; test case
(test (parse '1) (num 1))
(test (parse '{+ 1 2}) (add (num 1) (num 2)))
(test (parse '{with {x {- 4 2}} x}) (with 'x (sub (num 4) (num 2)) (id 'x)))
(test (parse 'bar) (id 'bar))
(test (parse '{fun {x} {+ x x}}) (fun 'x (add (id 'x) (id 'x))))
(test (parse '{foo {with {f2 y} {f2 5}}}) (app (id 'foo)
                                              (with 'f2
                                                    (id 'y)
                                                    (app (id 'f2) (num 5)))))
(test (parse '{fun {x} {+ x 1}})
      (fun 'x (add (id 'x) (num 1))))
(test (parse '{{fun {x} {+ x 1}} 10})
      (app (fun 'x (add (id 'x) (num 1))) (num 10)))
