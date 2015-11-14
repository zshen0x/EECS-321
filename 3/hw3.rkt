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

;; function and variables are in seperate space
(define-type FunDef
  [fundef (func-name symbol?)
          (param-list (listof symbol?))
          (body FnWAE?)])

;; data structure for code (internal representive for code)
(define-type FnWAE
  [num (n number?)]
  [add (lhs FnWAE?)
       (rhs FnWAE?)]
  [sub (lhs FnWAE?)
       (rhs FnWAE?)]
  [with (id symbol?)
        (expr FnWAE?)
        (body FnWAE?)]
  [id (name symbol?)]
  ;; function call
  [app (func-name symbol?)
       (param-expr-list (listof FnWAE?))])

;; parser code from s-expression(list of symbols) to FnWAE
(define (parse-error what expression)
  (error 'parser
         "expected: ~a, found:\n~a"
         what
         (pretty-format expression 30)))

(define (check-pieces expression size what)
  (unless (and (list? expression)
               (= (length expression) size))
    (parse-error what expression)))

(define (parse s-expr)
  (cond
    [(number? s-expr) (num s-expr)]
    [(symbol? s-expr) (id s-expr)]
    [(pair? s-expr)
     (let ([lead (first s-expr)])
       (case lead
         [(+) (check-pieces s-expr 3 "add")
              (add (parse (second s-expr))
                   (parse (third s-expr)))]
         [(-) (check-pieces s-expr 3 "sub")
              (sub (parse (second s-expr))
                   (parse (third s-expr)))]
         [(with) (check-pieces s-expr 3 "with")
                 (with (first (second s-expr))
                       (parse (second (second s-expr)))
                       (parse (third s-expr)))]
         ;; others are assumed as function calls
         [else (if (symbol? lead)
                   (app lead (map parse (rest s-expr)))
                   (error "syntax error at:\n" s-expr))]))]
    ;; a empty list
    [else (error "syntax error at:\n" s-expr)]))


;; todo improve check-dup
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
  (-> list? FunDef?)
  (local [(define lead (first s-expr))]
    (case lead
      [(deffun)
       (check-pieces s-expr 3 "deffun")
       (cond
         [(empty? (second s-expr))
          (error "bad syntax, lack function name at deffun:\n" s-expr)]
         [(check-dup (rest (second s-expr)))
          (error "bad syntax, dulplicate param at deffun:\n" s-expr)]    
         [else (fundef (first (second s-expr))
                       (rest (second s-expr))
                       (parse (third s-expr)))])]
      [else (parse-error "deffun" s-expr)])))

;; to be finished the interpreter
;;; substitute free identifiers: sub-id in a FnWAE with val
(define/contract (subst a-fnwae sub-id val)
  (-> FnWAE? symbol? number? FnWAE?)
  (type-case FnWAE a-fnwae
    [num (n) a-fnwae]
    [add (l r) (add (subst l sub-id val)
                    (subst r sub-id val))]
    [sub (l r) (sub (subst l sub-id val)
                    (subst r sub-id val))]
    [with (bind-id bind-expr body)
          (with bind-id
                (subst bind-expr sub-id val)
                (if (symbol=? bind-id sub-id)
                    body
                    (subst body sub-id val)))]
    [id (name) (if (symbol=? name sub-id)
                   (num val)
                   a-fnwae)]
    [app (fname param-expr-list)
         (app fname
              (map (lambda (param-expr)
                      (subst param-expr
                             sub-id
                             val))
                   param-expr-list))]))

;; look up function from fundefs
(define/contract (func-lookup fname param-num fundefs)
  (-> symbol? number? (listof FunDef?) fundef?)
  ;; fundefs with same name
  (let ([f1-lst (filter (lambda (a-fundef)
                          (symbol=? (fundef-func-name a-fundef)
                                    fname))
                          fundefs)])
    (if (empty? f1-lst)
        (error "function:" fname 'not 'found)
        (let ([f2-lst (filter (lambda (a-fundef)
                               (= (length (fundef-param-list a-fundef))
                                          param-num))
                               f1-lst)])
          (if (empty? f2-lst)
              (error 'mismatch "function ~a: wrong arity" fname)
              (first f2-lst))))))

;; test case for func-lookup

(define/contract (interp a-fnwae fundefs)
  (-> FnWAE? (listof FunDef?) number?)

  (define/contract (multi-subst body param-list param-exprs)
  (-> FnWAE? (listof symbol?) (listof FnWAE?) FnWAE?)
  (if (empty? param-list)
      body
      (multi-subst
       (subst body
              (first param-list)
              (interp (first param-exprs) fundefs))
       (rest param-list)
       (rest param-exprs))))
  
  (type-case FnWAE a-fnwae
    [num (n) n]
    [add (l r) (+ (interp l fundefs)
                  (interp r fundefs))]
    [sub (l r) (- (interp l fundefs)
                  (interp r fundefs))]
    [with (bind-id bind-expr body)
          (interp (subst body
                         bind-id
                         (interp bind-expr
                                 fundefs))
                  fundefs)]
    ; all symbols meet here are free identifiers
    [id (name) (error "free identifiers:\n" name)]
    [app (fname param-exprs)
         (type-case FunDef (func-lookup fname
                                        (length param-exprs)
                                        fundefs)
           [fundef (fname param-lst body)
                   (interp (multi-subst body
                                        param-lst
                                        param-exprs)
                           fundefs)])]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;test case
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test (parse 'x) (id 'x))
(test/exn (parse '{}) "error")
(test (parse '{+ 1 2}) (add (num 1) (num 2)))
(test (parse '{x e a b})
      (app 'x (list (id 'e)
                    (id 'a)
                    (id 'b))))

(test (parse '{with {x y} {with {k 4} {f 1 a b {+ j k}}}})
      (with 'x (id 'y) (with 'k
                             (num 4)
                             (app 'f (list (num 1)
                                           (id 'a)
                                           (id 'b)
                                           (add (id 'j)
                                                (id 'k)))))))

(test (parse '{sum 2 {with {a {+ 1 2}} a}})
      (app 'sum (list (num 2)
                      (with 'a
                            (add (num 1) (num 2))
                            (id 'a)))))

(test/exn (func-lookup 'foo 0 (list (fundef 'fooo '() (num 1))))
          "not found")

(test/exn (func-lookup 'foo 0 (list (fundef 'foo '(x) (id 'x))))
          "wrong arity")

(test (func-lookup 'foo 2 (list (fundef 'fooo '(x y) (add (id 'x)
                                                          (id 'y)))
                                (parse-defn '{deffun {foo a b} {+ a b}})))
      (fundef 'foo '(a b) (add (id 'a) (id 'b))))

(test (parse-defn '{deffun {a x y z} {+ {+ x y} z}})
      (fundef 'a '(x y z) (add (add (id 'x) (id 'y))
                               (id 'z))))

(test (parse-defn '{deffun {sd ds} {sdf}})
      (fundef 'sd '(ds) (app 'sdf '())))

(test (parse-defn '{deffun {union m n} {+ {with {m 100} m} {with {n 200} n}}})
      (fundef 'union
              '(m n)
              (add (with 'm (num 100) (id 'm))
                   (with 'n (num 200) (id 'n)))))

(test/exn (parse-defn '{deffun {f x x} x}) "bad syntax")

(test (interp (parse '{f 1 2})
                (list (parse-defn '{deffun {f x y} {+ x y}}))) 3)

(test (interp (app 'f '())
              (list (parse-defn '{deffun {f} 2}))) 2)

(test (interp (parse '{f})
                (list (parse-defn '{deffun {f} 2}))) 2)

(test (interp (parse '{+ {f} {f}})
              (list (parse-defn '{deffun {f} 5}))) 10)

(test/exn (interp (parse '{f 1})
                  (list (parse-defn '{deffun {f x y} {+ x y}})))
          "wrong arity")

(test/exn (interp (parse '{with {x y} 1})
                  (list)) "free")

(test/exn (interp (parse '{with {x 100} {f}})
              (list (parse-defn '{deffun {f} x})))
          "free identifier")

(test (interp (parse '{with {x 100} {twice x}})
              (list (parse-defn '{deffun {twice x} {+ x x}}))) 200)

(test (interp (parse '{with {a 2}
                            {with {b a}
                                  {with {c {- {twice a} b}}
                                        {sum a b c}}}})
              (list (parse-defn '{deffun {sum x y z} {+ {+ x y} z}})
                    (parse-defn '{deffun {twice x} {+ x x}}))) 6)

(test (interp (parse '{with {a 8}
                            {a a}})
              (list (parse-defn '{deffun {a a} {with {a a} a}}))) 8)

(test (interp (parse '{with {k {f1 3}} {f1 k}})
              (list (parse-defn '{deffun {f1 k} {twice k}})
                    (parse-defn '{deffun {twice x} {+ x x}}))) 12)