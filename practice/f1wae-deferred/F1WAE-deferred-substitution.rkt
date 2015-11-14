#lang plai

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

(define-type DefSub
  [mtSub]               ;empty bubble
  [aSub (name symbol?)
        (value number?)
        (rest DefSub?)])

(define/contract (func-lookup f-name fundefs)
  (-> symbol? (listof fundef?) fundef?)
  (cond
    [(empty? fundefs)
     (error "error function" f-name 'not 'found)]
    [(symbol=? (fundef-func-name (first fundefs))
               f-name) (first fundefs)]
    [else (func-lookup f-name (rest fundefs))]))

(define/contract (defsub-lookup name a-defsub)
  (-> symbol? DefSub? number?)
  (type-case DefSub a-defsub
    [mtSub () (error "error free identifier" name)]
    [aSub (n val rest) (if (symbol=? name n)
                           val
                           (defsub-lookup name rest))]))

;; interp with function calls
;; interp take a f1wae a defsub and a fundef lsit -> number
(define/contract (interp a-f1wae a-defsub fundefs)
  (-> F1WAE? DefSub? (listof fundef?) number?)
  (type-case F1WAE a-f1wae
    [num (n) n]
    [add (l r) (+ (interp l a-defsub fundefs)
                  (interp r a-defsub fundefs))]
    [sub (l r) (- (interp l a-defsub fundefs)
                  (interp r a-defsub fundefs))]
    [with (with-id with-expr with-body) (interp with-body
                                                (aSub with-id
                                                      (interp with-expr
                                                              a-defsub
                                                              fundefs)
                                                      a-defsub)
                                                fundefs)]
    [id (name) (defsub-lookup name a-defsub)]
    ;; attention we use stattic scope in this language
    [app (fname expr) (let ([foo (func-lookup fname fundefs)])
                        (interp (fundef-body foo)
                                (aSub (fundef-arg-name foo)
                                      (interp expr a-defsub fundefs)
                                      (mtSub))
                                fundefs))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; test case
(test (interp (num 10) (mtSub) empty) 10)
(test (interp (add (num 1) (num 2)) (mtSub) empty) 3)
(test (interp (sub (num 2) (num 1)) (mtSub) empty) 1)
(test (interp (add (add (num 1) (num 2))
                   (sub (num 8) (num 1)))
              (mtSub)
              empty) 10)
(test/exn (interp (id 'x) (mtSub) empty) "free identifier")
(test (interp (with 'x (num 1) (add (num 2) (num 4))) (mtSub) empty) 6)
(test (interp (with 'x (num 1) (add (id 'x) (num 5))) (mtSub) empty) 6)
(test (interp (with 'x (num 1)
                    (with 'x (num 2)
                          (add (id 'x) (id 'x))))
              (mtSub)
              empty) 4)
(test (interp (with 'x (num 1)
                    (add (with 'x (num 2)
                               (add (id 'x) (id 'x)))
                         (id 'x)))
              (mtSub)
              empty) 5)

(test (interp (add (app 'double (add (num 1) (num 2)))
                   (num 2))
              (mtSub)
              (list (fundef 'double 'x (add (id 'x) (id 'x))))) 8)
;; with statement is like a loccal binding,
;; which can not intervene the bound occurence in functions
(test (interp (with 'x (num 10) (app 'double (id 'x)))
              (mtSub)
              (list (fundef 'double 'y (add (id 'y) (id 'y))))) 20)

(test (interp (app 'f (num 10))
              (mtSub)
              (list
               (fundef 'f 'x
                       (sub (num 20)
                            (app 'twice (id 'x))))
               (fundef 'twice 'y
                       (add (id 'y) (id 'y))))) 0)

(test/exn (interp (app 'foo (num 10)) (mtSub) '())
          "not found")