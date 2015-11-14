#lang plai

(print-only-errors)
;; honor code
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

;; let's begin

(define-type WAE
  [num (n number?)]
  [add (rhs WAE?)
       (lhs WAE?)]
  [sub (rhs WAE?)
       (lhs WAE?)]
  [with (name symbol?)
        (expr WAE?)
        (body WAE?)]
  [id (name symbol?)])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; part 1 
;; take a a-wae return a un filtered free id list
(define/contract (free-ids-help a-wae not-free-ids)
  (-> WAE? (listof symbol?) (listof symbol?))
  (type-case WAE a-wae
    [num (n) '()]
    [add (l r) (append (free-ids-help l not-free-ids)
                       (free-ids-help r not-free-ids))]
    [sub (l r) (append (free-ids-help l not-free-ids)
                       (free-ids-help r not-free-ids))]
    [with (with-id with-expr with-body)
          (append (free-ids-help with-expr not-free-ids)
                  (free-ids-help with-body (cons with-id not-free-ids)))]
    [id (name) (if (member name not-free-ids)
                   '()
                   (list name))]))

(define/contract (free-ids a-wae)
  (-> WAE? (listof symbol?))
  (sort (remove-duplicates (free-ids-help a-wae '())) symbol<?))

(test (free-ids (add (num 1) (num 2))) '())
(test (free-ids (sub (id 'x) (id 'y))) '(x y))
(test (free-ids (id 'a)) '(a))
(test (free-ids (with 'x (num 1) (id 'x))) '())
(test (free-ids (with 'x (id 'x) (sub (id 'y) (id 'x)))) (list 'x 'y))
(test (free-ids (add (with 'x (id 'x) (add (id 'a) (id 'a)))
                     (with 'x (id 'y) (add (id 'c) (id 'd)))))
      '(a c d x y))
(test (free-ids (with 'x (with 'x (id 'y) (id 'x)) (num 1))) '(y))
(test (free-ids (with 'x
                      (with 'x (id 'x) (id 'c))
                      (with 'a (id 'a) (sub (id 'x)
                                            (with 'a (num 1) (id 'b))))))
      '(a b c x))

;; part 2
;; count all the 
(define/contract (binding-ids-help a-wae)
  (-> WAE? (listof symbol?))
  (type-case WAE a-wae
  [num (n) '()]
  [add (l r) (append (binding-ids-help l) (binding-ids-help r))]
  [sub (l r) (append (binding-ids-help l) (binding-ids-help r))]
  [with (with-id with-expr with-body) (cons with-id
                                            (append (binding-ids-help with-expr)
                                                    (binding-ids-help with-body)))]
  [id (name) '()]))

(define/contract (binding-ids a-wae)
  (-> WAE? (listof symbol?))
  (sort (remove-duplicates (binding-ids-help a-wae)) symbol<?))

(test (binding-ids (num 1)) '())
(test (binding-ids (id 'x)) '())
(test (binding-ids (with 'y
                         (with 'x (num 1) (add (id 'x) (id 'x)))
                         (add (with 'y (num 2) (id 'y))
                              (with 'c (sub (num 4) (num 3)) (id 'c)))))
      '(c x y))
(test (binding-ids (with 'x (with 'x (id 'y) (id 'x)) (num 1)))
      '(x))
(test (binding-ids (with 'x
                         (with 'x (num 1) (id 'x))
                         (with 'a (num 1) (sub (id 'x)
                                               (with 'a (num 1) (id 'b))))))
      '(a x))

;; part 3
(define/contract (bound-ids-help a-wae bd-ids)
  (-> WAE? (listof symbol?) (listof symbol?))
  (type-case WAE a-wae
    [num (n) '()]
    [sub (l r) (append (bound-ids-help l bd-ids)
                       (bound-ids-help r bd-ids))]
    [add (l r) (append (bound-ids-help l bd-ids)
                       (bound-ids-help r bd-ids))]
    [with (with-id with-expr with-body)
          (append (bound-ids-help with-expr
                                  bd-ids)
                  (bound-ids-help with-body
                                  (cons with-id bd-ids)))]
    [id (name) (if (member name bd-ids)
                   (list name)
                   '())]))
  
(define/contract (bound-ids a-wae)
  (-> WAE? (listof symbol?))
  (sort (remove-duplicates (bound-ids-help a-wae '())) symbol<?)
  )

(test (bound-ids (num 1)) '())
(test (bound-ids (id 'a)) '())
(test (bound-ids (add (id 'x) (id 'y))) '())
(test (bound-ids (sub (id 'y) (with 'x (num 1) (add (id 'x) (id 'x)))))
      '(x))
(test (bound-ids (with 'x
                       (num 1)
                       (with 'y (id 'c) (add (id 'x) (id 'y)))))
      '(x y))
(test (bound-ids (with 'x
                       (with 'x (num 2) (id 'z))
                       (with 'd (with 'x (id 'x) (id 'd)) (num 1))))
      '(x))
(test (bound-ids (with 'x (with 'x (id 'y) (id 'x)) (num 1)))
      '(x))
(test (bound-ids (with 'x
                       (with 'x (num 1) (id 'x))
                       (with 'a (num 1) (sub (id 'x)
                                             (with 'a (num 1) (id 'a))))))
      '(a x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; part 4

(define/contract (shadowed-variable-help a-wae bd-ids)
  (-> WAE? (listof symbol?) boolean?)
  (type-case WAE a-wae
    [num (n) #f]
    [add (l r) (or (shadowed-variable-help l bd-ids)
                   (shadowed-variable-help r bd-ids))]
    [sub (l r) (or (shadowed-variable-help l bd-ids)
                   (shadowed-variable-help r bd-ids))]
    [with (with-id with-expr with-body)
          (or (shadowed-variable-help with-expr
                                      bd-ids)
              (shadowed-variable-help with-body
                                      (cons with-id
                                            bd-ids)))]
    [id (name) (if (member name (remove name bd-ids))
                   #t
                   #f)]))

(define/contract (shadowed-variable? a-wae)
  (-> WAE? boolean?)
  (shadowed-variable-help a-wae '()))

(test (shadowed-variable? (id 'x)) #f)
(test (shadowed-variable? (with 'x (with 'x (id 'y) (id 'x)) (id 'y))) #f)
(test (shadowed-variable? (with 'x (num 1) (add (with 'x (num 2) (id 'x))
                                                (num 2)))) #t)
(test (shadowed-variable? (with 'a (add (with 'b (num 1) (id 'b))
                                        (with 'a (with 'a (num 2) (id 'a)) (id 'a))) (id 'a))) #f)
(test (shadowed-variable? (with 'x
                                (with 'x (num 1) (id 'x))
                                (with 'a (num 1) (sub (id 'x)
                                                      (with 'a (num 1) (id 'a)))))) #t)

(test (free-ids (with 'a (id 'x) (num +inf.0))) '(x))
(test (binding-ids (with 'a (with 'x (num +inf.0) (id 'x)) (num +inf.0))) '(a x))

