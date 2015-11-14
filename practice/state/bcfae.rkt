#lang plai

;FAE + BOX
;<BCFAE> ::= <num>
;| {+ <BCFAE> <BCFAE>}
;| {- <BCFAE> <BCFAE>}
;| <id>
;| {fun {<id>} <BCFAE>}
;| {<BCFAE> <BCFAE>}
;| {newbox <BCFAE>}
;| {setbox <BCFAE> <BCFAE>}
;| {openbox <BCFAE>}
;| {seqn <BCFAE> <BCFAE>}

(define-type BCFAE
  [num (n number?)]
  [add (lhs BCFAE?) (rhs BCFAE?)]
  [sub (lhs BCFAE?) (rhs BCFAE?)]
  [id (name symbol?)]
  [fun (param symbol?) (body BCFAE?)]
  [app (fun-expr BCFAE?) (arg-expr BCFAE?)]
  [newbox (val-expr BCFAE?)]
  [setbox (box-expr BCFAE?) (val-expr BCFAE?)]
  [openbox (box-expr BCFAE?)]
  [seqn (expr1 BCFAE?) (expr2 BCFAE?)])

(define-type DefrdSub
  [mtSub]
  [aSub (id symbol?)
        (value BCFAE-Value?)
        (rest DefrdSub?)])

(define-type BCFAE-Value
  [numV (n number?)]
  [closureV (param symbol?)
            (body BCFAE?)
            (ds DefrdSub?)]
  [boxV (container (box/c BCFAE-Value?))])

;; interperter
;; numV operation
(define/contract (numV-op op)
  (-> (-> number? number? number?)
      (-> BCFAE-Value? BCFAE-Value? numV?))
  (λ (lhs rhs)
    (if (and (numV? lhs) (numV? rhs))
        (numV (op (numV-n lhs) (numV-n rhs)))
        (error 'add-or-sub "numeric operation expected number"))))
(define numV+ (numV-op +))
(define numV- (numV-op -))

(define/contract (lookup-ds name ds)
  (-> symbol? DefrdSub? BCFAE-Value?)
  (type-case DefrdSub ds
    [mtSub () (error "free identifier:\n" name)]
    [aSub (id val rest) (if (symbol=? id name)
                              val
                              (lookup-ds name rest))]))

(define/contract (interp a-bcfae ds)
  (-> BCFAE? DefrdSub? BCFAE-Value?)
  (type-case BCFAE a-bcfae
    [num (n) (numV n)]
    [add (l r) (numV+ (interp l ds) (interp r ds))]
    [sub (l r) (numV- (interp l ds) (interp r ds))]
    [id (name) (lookup-ds name ds)]
    [fun (param body) (closureV param body ds)]
    [app (fun-expr arg-expr)
         (let ([appV (interp fun-expr ds)])
           (let ([argV (interp arg-expr ds)])
             (type-case BCFAE-Value appV
               [closureV (param body ds)
                         (interp body
                                 (aSub param argV ds))]
               [else (error 'app "given: ~a\napplication expected procedure" fun-expr)])))]
  [newbox (val-expr) (boxV (box (interp val-expr ds)))]
  [setbox (box-expr val-expr)
          (let ([bxV (interp box-expr ds)])
            (let ([val (interp val-expr ds)])
              (type-case BCFAE-Value bxV
                [boxV (container) (begin
                                    (set-box! container val)
                                    bxV)]
                [else (error 'setbox "given: ~a\n expected a box" box-expr)])))]
  [openbox (box-expr)
           (type-case BCFAE-Value (interp box-expr ds)
             [boxV (container) (unbox container)]
             [else (error 'openbox "given: ~a\n expected a box" box-expr)])]
  [seqn (e1 e2)
        (begin
          (interp e1 ds)
          (interp e2 ds))]))

;; test case
(print-only-errors)
(test (interp (openbox (setbox (newbox (num 1)) (num 2))) (mtSub))
      (numV 2))
(test (interp (setbox (newbox (num 1)) (num 1)) (mtSub))
      (interp (newbox (num 1)) (mtSub)))
(test (interp (seqn (newbox (fun 'x (add (id 'x) (id 'x))))
                    (app (openbox (newbox (fun 'x (add (id 'x) (id 'x))))) (num 10)))
              (mtSub))
      (numV 20))
