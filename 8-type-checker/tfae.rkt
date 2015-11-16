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

(define (fib [x : number]) : number
  (cond
    [(eq? x 0) 1]
    [(eq? x 1) 1]
    [else (+ (fib (- x 1)) (fib (- x 2)))]))



