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
    [nil (typ) (listT typ)]
    [consl (fst rst) (let ([fst-typ (type-check fst env)]
                           [rst-typ (type-check rst env)])
                       (type-case Type rst-typ
                         [listT (τ) (cond
                                        [(equal? fst-typ τ) rst-typ]
                                        [else (error 'type-check "type-error expected same type")])]
                         [else (error 'type-check "type-error expected listT")]))]
    [firstl (lst) (type-case Type (type-check lst env)
                    [listT (τ) τ]
                    [else (error 'type-check "type-error expected listT")])]
    [restl (lst) (type-check lst env)]
    [mtl? (lst) (type-case Type (type-check lst env)
                  [listT (τ) (boolT)]
                  [else (error 'type-check "type-error expected listT")])]))

(define (type-check-expr [a-tfae : TFAE]) : Type
  (type-check a-tfae (mtEnv)))


(print-only-errors #t)
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
(test (type-check-expr (fun 'x (numT) (fun 'y (boolT) (ifthenelse (id 'y) (id 'x) (id 'x)))))
      (arrowT (numT) (arrowT (boolT) (numT))))

(test (type-check-expr (nil (boolT))) (listT (boolT)))
(test (type-check-expr (consl (num 1) (consl (num 2) (nil (numT))))) (listT (numT)))
(test/exn (type-check-expr (consl (num 1) (nil (boolT)))) "type-error")
(test (type-check-expr (firstl (consl (bool #t) (consl (bool #f) (nil (boolT))))))
      (type-check-expr (restl (firstl (consl (bool #t) (consl (bool #f) (nil (boolT))))))))
(test (type-check-expr (nil (boolT))) (listT (boolT)))
(test/exn (type-check-expr (consl (bool #f) (nil (arrowT (numT) (boolT))))) "type-error")
(test (type-check-expr (app (fun 'x (boolT)
                                 (mtl? (consl (bool #t) (consl (id 'x) (nil (boolT))))))
                            (bool #f)))
      (boolT))
(test/exn (type-check-expr (add (num 1) (bool #f))) "type-error")
(test/exn (type-check-expr (sub (num 1) (fun 'sks (boolT) (id 'sks)))) "type-error")
(test/exn (type-check-expr (eql (num 1) (app (fun 'x (boolT) (id 'x)) (bool #f)))) "type-error")
(test/exn (type-check-expr (app (add (num 1) (num 2)) (num 1))) "type-error")
(test/exn (type-check-expr (consl (num 1) (bool #t))) "type-error")
(test/exn (type-check-expr (mtl? (consl (num 1) (bool #t)))) "type-error")
(test/exn (type-check-expr (mtl? (num 1))) "type-error")

(test (type-check-expr (fun 'x (boolT)
                            (fun 'y (numT)
                                 (fun 'z (numT)
                                      (ifthenelse (id 'x)
                                                  (id 'y)
                                                  (id 'z))))))
      (arrowT (boolT) (arrowT (numT) (arrowT (numT) (numT)))))

(test (type-check-expr (app (fun 'x (boolT)
                                 (fun 'y (numT)
                                      (fun 'z (numT)
                                           (ifthenelse (id 'x)
                                                       (id 'y)
                                                       (id 'z)))))
                            (bool #f)))
      (arrowT (numT) (arrowT (numT) (numT))))

(test (type-check-expr (firstl (consl (num 4) (consl (num 5) (nil (numT))))))
      (numT))

(test (type-check-expr
       (firstl (consl (fun 'x (numT) (num 6)) (nil (arrowT (numT) (numT))))))
      (arrowT (numT) (numT)))
(test (type-check-expr (firstl (nil (numT))))
      (numT))
(test (type-check-expr (firstl (consl (bool #f) (nil (boolT))))) (boolT))
(test (type-check-expr
       (firstl
        (consl
         (fun 'x (numT) (eql (id 'x) (num 6)))
         (nil (arrowT (numT) (boolT))))))
      (arrowT (numT) (boolT)))
      
(test (type-check-expr (firstl (nil (boolT)))) (boolT))
(test (type-check-expr
       (firstl
        (restl
         (consl
          (ifthenelse
           (bool #f)
           (fun 'x (numT) (id 'x))
           (fun 'y (numT) (add (id 'y) (num 3))))
          (nil (arrowT (numT) (numT)))))))
      (arrowT (numT) (numT)))
      
(test (type-check-expr
       (app
        (firstl
         (restl
          (consl
           (ifthenelse
            (bool #f)
            (fun 'x (numT) (id 'x))
            (fun 'y (numT) (add (id 'y) (num 3))))
           (nil (arrowT (numT) (numT))))))
        (num 5)))
      (numT))








