#lang plai

; a parser take a list produce a F1WAE

;; {} style list
;; {+ op1 op2} -> (add epxr1 expr2)
;; {- op1 op2} -> (sub expr1 expr2)
;; {with {a expr1} expr2} -> (with 'a expr1 expr2)
;; a -> (id 'a)
;; {app fname expr} -> (app fname expr)
;; {defn {fname arg} {expr}} -> (fundef 'fname 'arg (expr))

;; data structure
(define-type F1WAE
  [num (n number?)]
  [add (lhs F1WAE?)
       (rhs F1WAE?)]
  [sub (lhs F1WAE?)
       (rhs F1WAE?)]
  [with (id symbol?)
        (expr F1WAE?)
        (body F1WAE?)]
  [id (name symbol?)]
  ;; app is a function call
  [app (func-name symbol?)
       (arg-expr F1WAE?)])

(define-type FunDef
  [fundef (func-name symbol? )
          (arg-name symbol? )
          (body F1WAE?)])

;; todo parse fundef lists could be seperate function
;; todo syntax error check during parsing
(define (parse exp)
  (cond
    [(number? exp) (num exp)]
    [(symbol? exp) (id exp)]
    [else (case (first exp)
            [(+) (add (parse (second exp))
                      (parse (third exp)))]
            [(-) (sub (parse (second exp))
                      (parse (third exp)))]
            [(with) (with (first (second exp))
                          (parse (second (second exp)))
                          (parse (third exp)))]
            [(app) (app (second exp) (parse (third exp)))]
            [else (if (symbol? (first exp))
                      (id (first exp))
                      (error "syntax error" '@ exp))])]))


;; test case

(test (parse 1) (num 1))
(test (parse 'z) (id 'z))
(test (parse '{+ 1 2}) (add (num 1) (num 2)))
