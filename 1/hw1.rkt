#lang plai

;; part 1 honor code
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

;; part 2 tree
;;; tree definition
(define-type Tree
    [leaf]   ; leaf is a child with out child
    [node (val number?)
          (left Tree?)
          (right Tree?)])

;;; smallest function
(define/contract (smallest root)
  (-> Tree? number?)
  (type-case Tree root
    [leaf () +inf.0]
    [node (v l r) (min v (smallest l) (smallest r))]))

;;; test case
(test (Tree? (node 15 (node 10 (node 5 (leaf) (leaf)) (leaf)) (leaf))) #t)
(test (smallest (leaf)) +inf.0)              ; empty 
(test (smallest (node 5 (leaf) (leaf))) 5)  ; 1 node

(test (smallest (node 15
                      (node 10
                            (node 5
                                  (leaf) (leaf))
                            (leaf))
                      (leaf)))
      5)         ; liner tree

(test (smallest (node 15
                      (node 10 (leaf) (leaf))
                      (node 5 (leaf) (leaf)))
                ) 5)  ; full b-tree

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Part 3 Negate

(define/contract (negate root)
  (-> Tree? Tree?)
  (type-case Tree root
    [leaf () (leaf)]
    [node (v l r) (node (- v) (negate l) (negate r))]))

;;; test case

(test (negate (leaf)) ;empty
      (leaf))
(test (negate (node -5 (leaf) (leaf)))
      (node 5 (leaf) (leaf)))
(test (negate (node 15 (node 10 (node 5 (leaf) (leaf)) (leaf)) (leaf)))
      (node -15 (node -10 (node -5 (leaf) (leaf)) (leaf)) (leaf)))
(test (negate (node -15 (node -10 (leaf) (leaf)) (node -5 (leaf) (leaf))))
      (node 15 (node 10 (leaf) (leaf)) (node 5 (leaf) (leaf))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; part 4 contains?
(define/contract (contains? root num)
  (-> Tree? number? boolean?)
  (type-case Tree root
    [leaf () #f]
    [node (v l r) (if (= v num)
                      #t
                      (or (contains? l num) (contains? r num)))]))

;;; test case
(test (contains? (leaf) 1) #f)
(test (contains? (node 5 (leaf) (leaf)) 6) #f)
(test (contains? (node 15 (node 10 (leaf) (leaf)) (node 5 (leaf) (leaf))) 10) #t)
(test (contains? (node 15 (node 10 (leaf) (leaf)) (node 5 (leaf) (leaf))) 6) #f)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; part 5 sorted? (wether sorted in inorder)
; inorder means in every sub-tree, left < node-num < right
; use append --- this is a bad example won't pass all the test
#|
(define/contract (sorted? root)
  (-> Tree? boolean?)
  (define (inorder-append root)
    (type-case Tree root
      [leaf () empty]
      [node (v l r) (append (inorder-append l)
                            (list v)
                            (inorder-append r))]))
  (let ([num-list (inorder-append root)])
    (or (empty? num-list) (apply < num-list))))
|#

(define/contract (sorted? root)
  (-> Tree? boolean?)
  (type-case Tree root
    [leaf () #t]
    [node (v l r) (and (sorted? l)
                       (cond
                         [(and (leaf? l) (leaf? r)) #t]
                         [(leaf? r) (<= (node-val l) v)]
                         [(leaf? l) (<= v (node-val r))]
                         [else (<= (node-val l) v (node-val r))])
                       (sorted? r))]))

;;; test case

(test (sorted? (leaf)) #t)
(test (sorted? (node 2 (node 1 (leaf) (leaf)) (node 3 (leaf) (leaf)))) #t)
(test (sorted? (node 3 (node 4 (leaf) (leaf)) (leaf))) #f)
(test (sorted? (node 1 (node 2 (node 4 (leaf) (leaf)) (node 5 (leaf) (leaf))) (node 3 (leaf) (leaf)))) #f)
(test (sorted? (node -1 (leaf) (node -1 (leaf) (leaf)))) #t)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; part 6 is-braun?
(define/contract (is-braun? root)
  (-> Tree? boolean?)
  ; input: tree -> output: tree element
  ; return -1 if not a braun or the depth
  (define/contract (braun-elements rt)
    (-> Tree? number?)
    (type-case Tree rt
      [leaf () 0]
      [node (v l r) (let ([lelem (braun-elements l)]
                          [relem (braun-elements r)])
                      (cond
                        [(and (<= 0 relem lelem) (<= (- lelem relem) 1)) (+ lelem relem 1)]
                        [else -1]))]))
  (let ([result (braun-elements root)])
    (if (= -1 result) #f #t)))

;;; test case
(test (is-braun? (leaf)) #t)
(test (is-braun? (node 1 (node 2 (leaf) (leaf)) (node 3 (leaf) (leaf)))) #t)
(test (is-braun? (node 1 (node 2 (node 4 (leaf) (leaf)) (node 5 (leaf) (leaf))) (node 3 (leaf) (leaf)))) #f)
(test (is-braun? (node 1
                       (node 2
                             (node 4 (leaf) (leaf))
                             (node 5 (leaf) (leaf)))
                       (node 3
                             (node 6 (leaf) (leaf))
                             (node 7 (leaf) (leaf))))) #t)
(test (is-braun? (node 2
                       (node 1
                             (node 0 (leaf) (leaf))
                             (leaf))
                       (node 3 (leaf) (leaf)))) #t)
(test (is-braun? (node 1 (leaf) (node 2 (leaf) (leaf)))) #f)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; part 7 make make-sorted-braun
(define/contract (make-sorted-braun num)
  (-> number? Tree?)
  (define/contract (mk-srted-brn-hlp elemts val)
    (-> number? number? Tree?)
    (cond
      [(= elemts 0) (leaf)]
      [(> elemts 0) (let ([lh-elemts (+ (quotient (- elemts 1) 2) (remainder (- elemts 1) 2))]
                          [rh-elemts (quotient (- elemts 1) 2)])
                      (node val
                            (mk-srted-brn-hlp lh-elemts
                                              (+ (- val lh-elemts) (quotient lh-elemts 2)))
                            (mk-srted-brn-hlp rh-elemts
                                              (+ (+ val 1) (quotient rh-elemts 2)))))]))
  (mk-srted-brn-hlp num (quotient num 2)))
    
;;; test case

(let* ([n 300]
       [braun-tree (make-sorted-braun n)])
  (test (is-braun? braun-tree) #t)
  (test (sorted? braun-tree) #t)
  (test (smallest braun-tree) 0)
  (test (smallest (negate braun-tree)) (- 1 n))
  )
(test (make-sorted-braun 0) (leaf))
(test (make-sorted-braun 4) (node 2
                         (node 1
                               (node 0 (leaf) (leaf))
                               (leaf))
                         (node 3 (leaf) (leaf))))
