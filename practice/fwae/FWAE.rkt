#lang plai

;; BNF grammar
#|
<FWAE> ::= <num>
| {+ <FWAE> <FWAE>}
| {- <FWAE> <FWAE>}
| {with {<id> <FWAE>} <FWAE>}
| <id>
| {fun {<id>} <FWAE>}         ;anonymous funcion
| {<FWAE> <FWAE>}
|#

;; this is internal programe representations
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
       (arg-expr FWAE?)])

;; a return type for
;; number or function in interp
(define-type FWAE-Value
  [numV (n number?)]
  [funV (param symbol?)
        (body FWAE?)])

;; paser using pattern match
;; take a s-expr -> FWAE
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
         [else (error "syntax error in:\n" s-expr)])]))

; interp FWAE .... -> FWAE-Value
;; interp behave little different from previous
;; because of we introduced fucntion as first class

;; two more function to process add, sub operation with numV
(define/contract (num-op op)
  (-> (-> number? number? number?)
      (-> FWAE-Value? FWAE-Value? numV?))
  (lambda (x y)
    (if (and (numV? x) (numV? y))
        (numV (op (numV-n x) (numV-n y)))
        (error "not a number"))))

(define num+ (num-op +))
(define num- (num-op -))

;; subst free variable with val
(define/contract (subst a-fwae sub-id val)
  (-> FWAE? symbol? FWAE-Value? FWAE?)
  (type-case FWAE a-fwae
    [num (n) a-fwae]
    [add (l r) (add (subst l sub-id val)
                    (subst r sub-id val))]
    [sub (l r) (sub (subst l sub-id val)
                    (subst r sub-id val))]
    [with (with-id with-expr with-body)
          (with with-id
                (subst with-expr sub-id val)
                (if (symbol=? sub-id with-id)
                    with-body
                    (subst with-body sub-id val)))]
    [id (name) (if (symbol=? sub-id name)
                   (type-case FWAE-Value val
                     [numV (n) (num n)]
                     [funV (param body) (fun param body)])
                   a-fwae)]
    [fun (param bd) (fun param (if (symbol=? param sub-id)
                                   bd
                                   (subst bd sub-id val)))]
    [app (f-expr param-expr) (app (subst f-expr sub-id val)
                                  (subst param-expr sub-id val))]))

(define/contract (interp a-fwae)
  (-> FWAE? FWAE-Value?)
  (type-case FWAE a-fwae
    [num (n) (numV n)]
    [add (l r) (num+ (interp l) (interp r))]
    [sub (l r) (num- (interp l) (interp r))]
    [with (with-id with-expr with-body)
          (interp (subst with-body
                         with-id
                         (interp with-expr)))]
    [id (name) (error "free identifier:\n~a" name)]
    [fun (param body) (funV param body)]
    [app (fun-expr arg-expr)
         (type-case FWAE-Value (interp fun-expr)
           [numV (n) (error "not a function:\n" n)]
           [funV (param body)
                 (interp (subst body
                                param
                                (interp arg-expr)))])]))

;; test case
(test (interp (parse '10)) (numV 10))
(test (interp (parse '{+ 1 2})) (numV 3))
(test (interp (parse '{with {x 10} {- x x}})) (numV 0))
(test/exn (interp (parse 'x)) "free identifier")
(test (interp (parse '{fun {a} {+ a a}})) (funV 'a (add (id 'a) (id 'a))))
(test (interp (parse '{with {triple {fun {x} {+ x {+ x x}}}}
                            {triple 10}})) (numV 30))
(test/exn (interp (parse '{1 20})) "not a function")
(test/exn (interp (parse '{+ 1 {fun {x} x}})) "not a number")
(test (interp (parse '{{{fun {a}
                             {fun {x} {- x a}}} 5}
                       10})) (numV 5))
(test (interp (parse '{{{fun {x} {fun {y} {+ x y}}} 1} 2})) (numV 3))
