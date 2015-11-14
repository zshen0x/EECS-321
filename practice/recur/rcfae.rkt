#lang plai

;; recursion with mutation
;(let ([fac 10])
;  (begin
;    (set! fac
;          (λ (n)
;            (if (zero? n)
;                1
;                (* n (fac (sub1 n))))))
;    (fac 10)))

; BNF grammer
;<RCFAE> ::= <num>
;| {+ <RCFAE> <RCFAE>}
;| {- <RCFAE> <RCFAE>}
;| <id>
;| {fun {<id>} <RCFAE>}
;| {<RCFAE> <RCFAE>}
;| {if0 <RCFAE> <RCFAE> <RCFAE>}
;| {rec {<id> <RCFAE>} <RCFAE>}

;; define data structure
(define-type RCFAE
  [num (n number?)]
  [add (lhs RCFAE?) (rhs RCFAE?)]
  [sub (lhs RCFAE?) (rhs RCFAE?)]
  [id (name symbol?)]
  [fun (param symbol?) (body RCFAE?)]
  [app (fun-expr RCFAE?) (arg-expr RCFAE?)]
  [if0 (test-expr RCFAE?) (then-expr RCFAE?) (else-expr RCFAE?)]
  [rec (name symbol?) (named-expr RCFAE?) (body RCFAE?)])

(define-type DefrdSub
  [mtSub]
  [aSub (id symbol?)
        (value RCFAE-Value?)
        (rest DefrdSub?)]
  [aRecSub (id symbol?)
           (value-box (box/c RCFAE-Value?))
           (rest DefrdSub?)])

(define-type RCFAE-Value
  [numV (n number?)]
  [closureV (param symbol?)
            (body RCFAE?)
            (ds DefrdSub?)])
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; parser s-expr -> internal ast
(define/contract (parse s-expr)
  (-> any/c RCFAE?)
  (match s-expr
    [(? number?) (num s-expr)]
    [(? symbol?) (id s-expr)]
    [`{+ ,lhs ,rhs} (add (parse lhs) (parse rhs))]
    [`{- ,lhs ,rhs} (sub (parse lhs) (parse rhs))]
    [`{with {,id ,e1} ,e2} (parse `{{fun {,id} ,e2} ,e1})]
    [`{if0 ,test ,then-expr ,else-expr} (if0 (parse test)
                                             (parse then-expr)
                                             (parse else-expr))]
    [`{rec {,id ,e1} ,e2} (rec id (parse e1) (parse e2))]
    [`{fun {,(? symbol? param)} ,body} (fun param (parse body))]
    [`{fun {,(? symbol? params) ..2} ,body} (parse `{fun {,(first params)}
                                                         {fun ,(rest params) ,body}})]
    [`{,fun-expr ,arg-expr} (app (parse fun-expr) (parse arg-expr))]
    [`{,fun-expr ,arg-exprs ..2} (parse (append `{{,fun-expr ,(first arg-exprs)}}
                                                (rest arg-exprs)))]
    [_ (error "bad syntax when parsing:\n" s-expr)]))

(define/contract (numV-op op)
  (-> (-> number? number? number?)
      (-> RCFAE-Value? RCFAE-Value? numV?))
  (λ (lhs rhs)
    (if (and (numV? lhs) (numV? rhs))
        (numV (op (numV-n lhs) (numV-n rhs)))
        (error 'add-or-sub "numeric operation expected number"))))
(define numV+ (numV-op +))
(define numV- (numV-op -))

;; interpreter

(define/contract (lookup-ds name ds)
  (-> symbol? DefrdSub? RCFAE-Value?)
  (type-case DefrdSub ds
    [mtSub () (error "free identifier:\n" name)]
    [aSub (id val rest) (if (symbol=? id name)
                              val
                              (lookup-ds name rest))]
    [aRecSub (id val-box rest) (if (symbol=? id name)
                                    (unbox val-box)
                                    (lookup-ds name rest))]))

(define/contract (interp a-rcfae ds)
  (-> RCFAE? DefrdSub? RCFAE-Value?)
  (type-case RCFAE a-rcfae
    [num (n) (numV n)]
    [add (l r) (numV+ (interp l ds) (interp r ds))]
    [sub (l r) (numV- (interp l ds) (interp r ds))]
    [id (name) (lookup-ds name ds)]
    [fun (param body) (closureV param body ds)]
    [app (fun-expr arg-expr)
         (let ([appV (interp fun-expr ds)])
           (let ([argV (interp arg-expr ds)])
             (type-case RCFAE-Value appV
               [numV (n) (error 'app "given: ~a\napplication expected procedure" n)]
               [closureV (param body ds)
                         (interp body
                                 (aSub param argV ds))])))]
    [if0 (test then else) (if (equal? (interp test ds)
                                      (numV 0))
                              (interp then ds)
                              (interp else ds))]
    [rec (bound-id named-expr body-expr)
      (let ([value-houlder (box 'free-identifier)])
        (let ([new-ds (aRecSub bound-id value-houlder ds)])
          (begin (set-box! value-houlder (interp named-expr new-ds))
                 (interp body-expr new-ds))))]))

(define/contract (interp-expr a-rcfae)
  (-> RCFAE? (or/c number? (symbols 'procedure)))
  (type-case RCFAE-Value (interp a-rcfae (mtSub))
    [numV (n) n]
    [closureV (param body ds) 'procedure]))


(interp-expr (parse '{rec {sum {fun {n}
                                    {if0 n
                                         0
                                         {+ n {sum {- n 1}}}}}}
                       {sum 0}}))
