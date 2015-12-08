#lang plai

;; data define

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

(define-type FAE-Value
  [numV (n number?)]
  [cloV (param symbol?)
        (body FAE?)
        (ds DefrdSub?)])

(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?)
        (value FAE-Value?)
        (rest DefrdSub?)])


(define/contract (numop op l r ds)
  (-> (-> number? number? number?)
      FAE?
      FAE?
      DefrdSub?
      numV?)
  (interp-expr l ds (λ (l-v)
                      (interp-expr r ds (λ (r-v)
                                          (type-case FAE-Value l-v
                                            [numV (l-num)
                                                  (type-case FAE-Value r-v
                                                    [numV (r-num) (numV (op l-num r-num))]
                                                    [else (error "not a number")])]
                                            [else (error "not a number")]))))))

(define/contract (lookup-id name ds)
  (-> symbol? DefrdSub? FAE-Value?)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free identifier: ~a" name)]
    [aSub (named-id val rst) (if (symbol=? name named-id)
                                 val
                                 (lookup-id name rst))]))


(define/contract (interp-expr a-fae ds k)
  (-> FAE? DefrdSub? (-> FAE-Value? any) FAE-Value?)
  (type-case FAE a-fae
    [num (n) (k (numV n))]
    [add (l r) (k (numop + l r ds))]
    [sub (l r) (k (numop - l r ds))]
    [id (name) (k (lookup-id name ds))]
    [fun (param body) (k (cloV param body ds))]
    [app (fun-expr arg-expr)
         (interp-expr arg-expr
                      ds
                      (λ (arg-v)
                        (interp-expr fun-expr
                                     ds
                                     (λ (closure-v)
                                       (type-case FAE-Value closure-v
                                         [cloV (param body d2)
                                               (interp-expr body
                                                            (aSub param
                                                                  arg-v
                                                                  d2)
                                                            k)]
                                         [else (error "not a function")])))))]))

(define/contract (interp a-fae)
  (-> FAE? (or/c number? symbol?))
  (type-case FAE-Value (interp-expr a-fae (mtSub) (λ (x) x))
    [numV (n) n]
    [cloV (praram body ds) 'a-function]))
  


(test (interp (app (fun 'x (add (id 'x ) (id 'x))) (num 10))) 20)
(test (interp (fun 'x (add (id 'x) (sub (num 1) (id 'x))))) 'a-function)
(test (interp (add (num 1) (num 2))) 3)



  