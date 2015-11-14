#lang plai

; BNF grammar
; FAE ::= {+ FAE FAE}
;       | {- FAE FAE}
;       | number
;       | {with {ID FAE} FAE}
;       | ID
;       | {if0 FAE FAE FAE}
;       | {fun {x x ...} FAE}
;       | {FAE FAE FAE ...} ;; application expressions

(define eight-principles
  (list
   "Know your rights."
   "Acknowledge your sources."
   "Protect your work."
   "Avoid suspicion."
   "Do your own work."
   "Never falsify a record or permit another person to do so."
   "Never fabricate data, citations, or experimental results."
   "Always tell the truth when discussing your work with your instructor."))

(define-type FAE
  [num (n number?)]
  [add (lhs FAE?) (rhs FAE?)]
  [sub (lhs FAE?) (rhs FAE?)]
  [id (name symbol?)]
  [if0 (test FAE?) (then FAE?) (else FAE?)]
  [fun (param symbol?) (body FAE?)]
  [app (fun FAE?) (arg FAE?)])

(define-type DefrdSub
  [mtSub]
  [aSub (id symbol?)
        (value FAE-Value?)
        (rest DefrdSub?)])

(define-type FAE-Value
  [numV (n number?)]
  [closureV (param symbol?)
            (body FAE?)
            (ds DefrdSub?)])

;; parser
(define/contract (parse s-expr)
  (-> any/c FAE?)
  (match s-expr
    [(? number?) (num s-expr)]
    [(? symbol?) (id s-expr)]
    [`{+ ,lhs ,rhs} (add (parse lhs) (parse rhs))]
    [`{- ,lhs ,rhs} (sub (parse lhs) (parse rhs))]
    [`{with {,id ,e1} ,e2} (parse `{{fun {,id} ,e2} ,e1})]
    [`{if0 ,test ,then-expr ,else-expr} (if0 (parse test)
                                             (parse then-expr)
                                             (parse else-expr))]
    [`{fun {,(? symbol? param)} ,body} (fun param (parse body))]
    [`{fun {,(? symbol? params) ..2} ,body} (parse `{fun {,(first params)}
                                                         {fun ,(rest params) ,body}})]
    [`{,fun-expr ,arg-expr} (app (parse fun-expr) (parse arg-expr))]
    [`{,fun-expr ,arg-exprs ..2} (parse (append `{{,fun-expr ,(first arg-exprs)}}
                                                (rest arg-exprs)))]
    [_ (error "bad syntax when parsing:\n" s-expr)]))

(define/contract (numV-op op)
  (-> (-> number? number? number?)
      (-> FAE-Value? FAE-Value? numV?))
  (λ (lhs rhs)
    (if (and (numV? lhs) (numV? rhs))
        (numV (op (numV-n lhs) (numV-n rhs)))
        (error 'add-or-sub "numeric operation expected number"))))
(define numV+ (numV-op +))
(define numV- (numV-op -))

(define/contract (lookup-ds name ds)
  (-> symbol? DefrdSub? FAE-Value?)
  (type-case DefrdSub ds
    [mtSub () (error "free identifier:\n" name)]
    [aSub (id val rest) (if (symbol=? id name)
                              val
                              (lookup-ds name rest))]))

(define/contract (interp a-fae ds)
  (-> FAE? DefrdSub? FAE-Value?)
  (type-case FAE a-fae
    [num (n) (numV n)]
    [add (l r) (numV+ (interp l ds) (interp r ds))]
    [sub (l r) (numV- (interp l ds) (interp r ds))]
    [id (name) (lookup-ds name ds)]
    [if0 (test then else) (if (equal? (interp test ds)
                                      (numV 0))
                              (interp then ds)
                              (interp else ds))]
    [fun (param body) (closureV param body ds)]
    [app (fun-expr arg-expr)
         (let ([appV (interp fun-expr ds)])
           (let ([argV (interp arg-expr ds)])
             (type-case FAE-Value appV
               [numV (n) (error 'app "given: ~a\napplication expected procedure" n)]
               [closureV (param body ds)
                         (interp body
                                 (aSub param argV ds))])))]))

(define/contract (interp-expr a-fae)
  (-> FAE? (or/c number? (symbols 'procedure)))
  (type-case FAE-Value (interp a-fae (mtSub))
    [numV (n) n]
    [closureV (param body ds) 'procedure]))

;(define n-to-f `{fun {n} {fun {f}
;                              {fun {x}
;                                   {}}}})
;(define f-to-n `{fun {f} ...})
;(define plus `{fun {f1 f2} ...})
;(define times `{fun {f1 f2} ...})

; recursive calls 

;(interp-expr (parse '{with {sum {fun {sum n}
;                                     {if0 n
;                                          0
;                                          {+ n {sum sum {- n 1}}}}}}
;                           {sum sum 10}}))
;(interp (parse '{{fun {body-proc} 
;                      {with {fx {fun {fx}
;                                     {with {f {fun {x}
;                                                   {{fx fx} x}}}
;                                                {body-proc f}}}}
;                            {fx fx}}}
;                 {fun {x} x}})
;        (mtSub))
;
;'{with {n-to-f-help {fun {recur n}
;                         {fun {x}
;                              {if0 n
;                                   x
;                                   {f {recur f {- n 1}}}}}}}
;       {n-to-f-help n-to-f-help 0}}
;;
;(define f-to-n '{with {f-to-n {fun {num-f}
;                                   {num-f {fun {num} {+ num 1}}}}}
;                      {{f-to-n {fun {f} {fun {x} x}}} 0}})


(define n-to-f `{fun {num}
                     {with {church {fun {recur n}
                                        {if0 n
                                             {fun {f} {fun {x} x}}
                                             {fun {f} {fun {x} {f {recur recur {- n 1}} f x}}}}}}
                           {church church num}}})


(define f-to-n `{fun {num-fun}
                     {{{fun {num-f}
                            {num-f {fun {num} {+ num 1}}}} num-fun} 0}})

(define plus `{fun {n1 n2}
                   {fun {f x}
                        {n1 f (n2 f x)}}})
(define times `{})
;; test cases
(print-only-errors)
(test (parse `1) (num 1))
(test (parse `x) (id 'x))
(test (parse `{fun {x} {- x x}})
      (fun 'x (sub (id 'x) (id 'x))))
(test (parse `{with {x {+ 1 2}} {- x x}})
      (parse `{{fun {x} {- x x}} {+ 1 2}}))
(test/exn (parse `{1}) "bad")
(test/exn (parse `{x}) "bad")
(test/exn (parse `{fun {1 2 3} {x}}) "bad")
(test (parse `{fun {a b c} {a {b c}}})
      (parse `{fun {a}
                   {fun {b}
                        {fun {c}
                             {a {b c}}}}}))
(test (parse `{foo 1 z {+ 2 b}})
      (parse `{{{foo 1} z} {+ 2 b}}))

(test (parse `{fun {a b c} {+ a {+ b c}}})
      (parse `{fun {a}
                   {fun {b}
                        {fun {c}
                             {+ a {+ b c}}}}}))
(test (parse `{foo 1 2 3 4 {foo {+ x y}}})
      (parse `{{{{{foo 1} 2} 3} 4} {foo {+ x y}}}))

(test/exn (interp-expr (parse `{+ {fun {x} x}
                                  {1 2}}))
          "application expected procedure")

(test (interp (parse '{+ 1 2}) (mtSub)) (numV 3))
(test/exn (interp (parse '{- x 1}) (mtSub)) "free")
(test (interp (parse '{fun {x} 1}) (mtSub)) (closureV 'x (num 1) (mtSub)))
(test (interp (parse '{{fun {x} {+ x x}} 2}) (mtSub)) (numV 4))
(test (interp (parse '{{fun {x} {x 2}} {fun {x} {+ x {+ x x}}}}) (mtSub)) (numV 6))
(test (interp (parse '{{{fun {x} {fun {y} {+ x y}}} 1} 2}) (mtSub)) (numV 3))

(test/exn (interp (parse '{+ {fun {x} x} 1}) (mtSub)) "numeric operation expected number")
(test/exn (interp (parse '{1 2}) (mtSub)) "application expected procedure")
(test (interp-expr (parse '{+ {{fun {x y z}
                                    {+ x {- y z}}}
                               5 6 7}
                              {- 7 6}})) 5)

(test (interp-expr (parse '{{fun {num-fun}
               {{{fun {num-f}
                      {num-f {fun {num} {+ num 1}}}} num-fun} 0}} {fun {f} {fun {x} {f {f {f {f x}}}}}}}))
4)