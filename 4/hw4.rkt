#lang plai

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

;<FunDef> = {deffun {<id> <id>*} <FnWAE>}
;<FnWAE> = <number>
;| {+ <FnWAE> <FnWAE>}
;| {- <FnWAE> <FnWAE>}
;| {with {<id> <FnWAE>} <FnWAE>}
;| <id>
;| {<id> <FnWAE>*}
;| {if0 <FnWAE> <FnWAE> <FnWAE>}

;; support multiple args
(define-type FnWAE
  [num (n number?)]
  [add (lhs FnWAE?)
       (rhs FnWAE?)]
  [sub (lhs FnWAE?)
       (rhs FnWAE?)]
  [with (name symbol?)
        (named-expr FnWAE?)
        (body FnWAE?)]
  [id (name symbol?)]
  [if0 (test-expr FnWAE?)
       (then-expr FnWAE?)
       (else-expr FnWAE?)]
  ;; app is a function call
  [app (fun-name symbol?)
       (arg-expr-lst (listof FnWAE?))])

(define-type FunDef
  [fundef (fun-name symbol?)
          (arg-lst (listof symbol?))
          (body FnWAE?)])

(define-type DefSub
  [mtSub]
  [aSub (id symbol?)
        (val number?)
        (rest DefSub?)])

(define/contract (parse s-expr)
  (-> any/c FnWAE?)
  (match s-expr
    [(? number?) (num s-expr)]
    [(? symbol?) (id s-expr)]
    [`{+ ,lhs ,rhs} (add (parse lhs) (parse rhs))]
    [`{- ,lhs ,rhs} (sub (parse lhs) (parse rhs))]
    [`{with {,id ,rhs} ,body} (with id (parse rhs) (parse body))]
    [`{if0 ,test-expr ,then-expr ,else-expr} (if0 (parse test-expr)
                                                  (parse then-expr)
                                                  (parse else-expr))]
    [`{,(? symbol? fun-name) ,arg-expr ...} (app fun-name (map parse arg-expr))]
    [_ (error "program bad syntax at:\n" s-expr)]))

;; 
(define/contract (check-dup a-list)
  (-> (listof symbol?) boolean?)
  (define/contract (check-dup-help first-item a-sorted-list)
    (-> symbol? (listof symbol?) boolean?)
    (cond
      [(empty? a-sorted-list) #f]
      [(symbol=? first-item (first a-sorted-list)) #t]
      [else (check-dup-help (first a-sorted-list)
                            (rest a-sorted-list))]))
  (if (empty? a-list)
      #f
      (let ([sorted-lst (sort a-list symbol<?)])
        (check-dup-help (first sorted-lst)
                        (rest sorted-lst)))))

(define/contract (parse-defn s-expr)
  (-> any/c FunDef?)
  (match s-expr
    [`{deffun {,(? symbol? fun-name) ,(? symbol? args) ...} ,body}
     (if (check-dup args)
         (error "bad syntax:\n duplicate args")
         (fundef fun-name args (parse body)))]
    [_ "function bad syntax at:\n" s-expr]))


;; interp
;; helper functions
;; defsub-lookup find value of a id
(define/contract (defsub-lookup a-id ds)
  (-> symbol? DefSub? number?)
  (type-case DefSub ds
    [mtSub () (error "free variable:\n" a-id)]
    [aSub (sub-id val rest) (if (symbol=? sub-id a-id)
                                val
                                (defsub-lookup a-id rest))]))


(define/contract (fun-name-lookup fname fundefs)
  (-> symbol? (listof fundef?) (listof fundef?))
  (let ([fds-lst (filter (λ (a-fundef)
                              (symbol=? (fundef-fun-name a-fundef)
                                        fname))
                            fundefs)])
    (if (empty? fds-lst)
        (error "undefined function:~\n" fname)
        fds-lst)))

(define/contract (fun-arg-lookup arg-num fundefs)
  (-> number? (listof fundef?) (listof fundef?))
        (let ([fds-lst (filter (λ (a-fundef)
                                 (= (length (fundef-arg-lst a-fundef))
                                    arg-num))
                               fundefs)])
          (if (empty? fds-lst)
              (error "function: wrong arity")
              fds-lst)))

;; lst->ds
(define/contract (lst->ds arg-lst num-lst a-ds)
  (-> (listof symbol?) (listof number?) DefSub? DefSub?)
  (cond
    [(empty? arg-lst) a-ds]
    [else (lst->ds (rest arg-lst)
                   (rest num-lst)
                   (aSub (first arg-lst)
                         (first num-lst)
                         a-ds))]))

;; 
(define/contract (interp a-fnwae ds fundefs)
  (-> FnWAE? DefSub? (listof fundef?) number?)
  (type-case FnWAE a-fnwae
    [num (n) n]
    [add (l r) (+ (interp l ds fundefs) (interp r ds fundefs))]
    [sub (l r) (- (interp l ds fundefs) (interp r ds fundefs))]
    [with (name named-expr body)
          (interp body
                  (aSub name (interp named-expr ds fundefs) ds)
                  fundefs)]   
    [id (name) (defsub-lookup name ds)]
    [if0 (test-expr then-expr else-expr)
         (case (interp test-expr ds fundefs)
           [(0) (interp then-expr ds fundefs)]
           [else (interp else-expr ds fundefs)])]
    [app (fun-name arg-expr-lst)
           (let ([same-name-fds (fun-name-lookup fun-name fundefs)])
             (let ([arg-num-val (map (λ (expr)
                                   (interp expr ds fundefs))
                                 arg-expr-lst)])
               (let ([match-fds (fun-arg-lookup (length arg-expr-lst)
                                                same-name-fds)])
                 (type-case FunDef (first match-fds)
                   [fundef (name arg-lst body)
                           (interp body (lst->ds arg-lst
                                                 arg-num-val
                                                 (mtSub))
                                   fundefs)]))))]))

;; interp-expr
(define/contract (interp-expr a-fnwae fundefs)
  (-> FnWAE? (listof FunDef?) number?)
  (interp a-fnwae (mtSub) fundefs))

;; part 3 negtive predicate
;; use recursive calls this implementation like c programming language
;; first order function

;; part 4 mult

(define mult-and-neg-deffuns
  (list `{deffun {mult x y}
           {if0 {neg? y}
                {- 0 {mult x {- 0 y}}}
                {if0 y
                     0
                     {+ x {mult x {- y 1}}}}}}
        `{deffun {neg? x} {neg-help x x}}
        `{deffun {neg-help x y} {if0 x
                                     1
                                     {if0 y
                                          0
                                          {neg-help {- x 1}
                                                    {+ y 1}}}}}))


(print-only-errors)
;; test case
;; case for parse
(test (parse '1) (num 1))
(test (parse '{+ 1 2}) (add (num 1) (num 2)))
(test (parse '{with {x {- 4 2}} x}) (with 'x (sub (num 4) (num 2)) (id 'x)))
(test (parse 'bar) (id 'bar))
(test (parse '{foo 1 2 x}) (app 'foo (list (num 1) (num 2) (id 'x))))
(test/exn (parse '(1 2 3)) "bad")
(test (parse '{f}) (app 'f '()))

(test (parse-defn '{deffun {foo x y z} {+ x {+ y z}}})
      (fundef 'foo '(x y z) (add (id 'x) (add (id 'y) (id 'z)))))
(test (parse-defn '{deffun {f} 4}) (fundef 'f '() (num 4)))

(test (interp-expr (parse '{f 1 2})
                   (list (parse-defn '{deffun {f x y} {+ x y}})))
      3)
(test (interp-expr (parse '{+ {f} {f}})
                   (list (parse-defn '{deffun {f} 5})))
      10)
(test/exn (interp-expr (parse '{f 1})
                       (list (parse-defn '{deffun {f x y} {+ x y}})))
          "wrong arity")

(test/exn (interp-expr (parse '{f x})
                       (list (parse-defn '{deffun {f a b c} c})))
          "free variable")

(test/exn (interp-expr (parse '{f x})
                       (list (parse-defn '{deffun {g a b c} c})))
          "undefined function")

(test (interp (parse '{if0 {+ 0 0} 0 1}) (mtSub) '())
      0)
(test (interp-expr (parse '{if0 0 1 2}) '()) 1)
(test (interp-expr (parse '{if0 1 2 3}) '()) 3)


(test/exn (parse-defn '{deffun {x y y } {y}})
          "bad syntax")
(test (interp-expr (parse '{if0 0 1 2}) '()) 1)
(test (interp-expr (parse '{if0 1 2 3}) '()) 3)

(test (interp-expr (parse '{mult 102 20})
                   (list (parse-defn (first mult-and-neg-deffuns))
                   (parse-defn (second mult-and-neg-deffuns))
                   (parse-defn (third mult-and-neg-deffuns))))
      2040)
