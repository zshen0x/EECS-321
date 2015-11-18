#lang plai-typed

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

;<TFAE> = ...
;          | {cons <TFAE> <TFAE>}
;          | {first <TFAE>}
;          | {rest <TFAE>}
;          | {nil <type>}
;          | {empty? <TFAE>}
;  <type> = number
;          | bool
;          | {<type> -> <type>}
;          | {listof <type>}

;; define data, abstract syntax
(define-type TFAE
  [num (n : number)]
  [bool (b : boolean)]
  [add (l : TFAE) (r : TFAE)]
  [sub (l : TFAE) (r : TFAE)]
  [eql (l : TFAE) (r : TFAE)]
  [id (name : symbol)]
  [ifthenelse (tst : TFAE) (thn : TFAE) (els : TFAE)]
  [fun (arg : symbol) (typ : Type) (body : TFAE)]
  [app (rator : TFAE) (rand : TFAE)]
  [consl (fst : TFAE) (rst : TFAE)]
  [firstl (lst : TFAE)]
  [restl (lst : TFAE)]
  [nil (typ : Type)]
  [mtl? (lst : TFAE)])

(define-type Type 
  [numT]
  [boolT]
  [arrowT (dom : Type) (codom : Type)]
  [listT (typ : Type)])

(define-type Env
  [mtEnv]
  [aEnv (id : symbol)
        (typ : Type)
        (rst : Env)])

(define (same-type? [left : TFAE]
                    [right : TFAE]
                    [exp-typ : Type]
                    [env : Env]) : boolean
  (let ([l-typ (type-check left env)]
        [r-typ (type-check right env)])
    (and (equal? l-typ exp-typ) (equal? r-typ exp-typ))))

(define (lookup-env [name : symbol] [env : Env]) : Type
  (type-case Env env
    [mtEnv () (error 'type-check-lookup-env
                     "type-error: free variable while typechecking")]
    [aEnv (id typ rst) (cond
                         [(symbol=? name id) typ]
                         [else (lookup-env name rst)])]))

;; try to construct type judgement tree, otherwise signal a error
(define (type-check [a-tfae : TFAE] [env : Env]) : Type
  (type-case TFAE a-tfae
    [num (n) (numT)]
    [bool (b) (boolT)]
    [add (l r) (if (same-type? l r (numT) env)
                   (numT)
                   (error 'type-check "type-error expected numT"))]
    [sub (l r) (if (same-type? l r (numT) env)
                   (numT)
                   (error 'type-check "type-error expected numT"))]
    [eql (l r) (if (same-type? l r (numT) env)
                   (boolT)
                   (error 'type-check "type-error expected numT"))]
    [id (name) (lookup-env name env)]
    [ifthenelse (tst thn els) (let ([tst-typ (type-check tst env)]
                                    [thn-typ (type-check thn env)]
                                    [els-typ (type-check els env)])
                                (cond
                                  [(equal? tst-typ (boolT)) (cond
                                                              [(equal? thn-typ els-typ) thn-typ]
                                                              [else (error 'type-check
                                                                           "type-error: expected same type")])]
                                  [else (error 'type-check
                                               "type-error: expected boolean")]))]
    [fun (arg typ body) (let ([body-typ (type-check body (aEnv arg typ env))])
                          (arrowT typ body-typ))]
    [app (rator rand) (let ([rator-typ (type-check rator env)]
                            [rand-typ (type-check rand env)])
                        (type-case Type rator-typ
                          [arrowT (dom codom) (cond
                                                [(equal? dom rand-typ) codom]
                                                [else (error 'type-check
                                                             "type-error: expected function match argument")])]
                          [else (error 'type-check
                                       "type-error: expected arrowT")]))]
    [consl (fst rst) (numT)]
    [firstl (lst) (numT)]
    [restl (lst) (numT)]
    [nil (typ) (numT)]
    [mtl? (lst) (numT)]))

(define (type-check-expr [a-tfae : TFAE]) : Type
  (type-check a-tfae (mtEnv)))


(test (type-check-expr (num 2)) (numT))
(test (type-check-expr (bool #f)) (boolT))
(test (type-check-expr (add (num 10) (sub (num 1) (num 2)))) (numT))
(test (type-check-expr (eql (num 10) (num 1))) (boolT))
(test/exn (type-check-expr (id 'x)) "free variable")
(test (type-check-expr (ifthenelse (bool #f) (num 1) (num 2))) (numT))
(test/exn (type-check-expr (ifthenelse (bool #f) (bool #f) (num 2))) "type-error")
(test/exn (type-check-expr (ifthenelse (num 10) (bool #f) (bool #t))) "type-error")
(test (type-check-expr (fun 'x (numT) (add (id 'x) (num 0)))) (arrowT (numT) (numT)))
(test (type-check-expr (app (fun 'x (numT) (add (id 'x) (num 0))) (num 2))) (numT))
(test/exn (type-check-expr (app (fun 'x (numT) (add (id 'x) (num 0))) (bool #t))) "type-error")







