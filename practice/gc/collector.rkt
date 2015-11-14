#lang plai/gc2/collector

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
; flat: 'flat, val
; 

(define (init-allocator)
  (heap-set! 0 1))

(define (gc:deref fl-loc)
  (if (gc:flat? fl-loc)
      (heap-ref (+ fl-loc 1))
      (error 'gc:deref "expected a flat value")))
;procedure
;(gc:alloc-flat val) → location?
;  val : heap-value?
; gc here
(define/contract (malloc size)
  (-> exact-nonnegative-integer? location?)
  (let ([loc (heap-ref 0)])
    (if (location? (+ loc (sub1 size)))
        (begin
          (heap-set! 0 (+ loc size))
          loc)
        (error 'allocator "out of memory"))))

(define (gc:alloc-flat fv)
  (let ([loc (malloc 2)])
    (begin
      (heap-set! loc 'flat)
      (heap-set! (+ loc 1) fv))
    loc))

(define (gc:cons hd tl)
  (let ([loc (malloc 3)]
        [head (read-root hd)]
        [tail (read-root tl)])
    (begin
      (heap-set! loc 'cons)
      (heap-set! (+ loc 1) head)
      (heap-set! (+ loc 2) tail)
      loc)))
(define/contract (chk-pair pr who)
  (-> location? symbol? void?)
  (unless (gc:cons? pr)
    (error who "expected a cons @ loc ~a" pr)))

(define (gc:first pr-loc)
  (chk-pair pr-loc 'gc:first)
  (heap-ref (+ pr-loc 1)))

(define (gc:rest pr-loc)
  (chk-pair pr-loc 'gc:rest)
  (heap-ref (+ pr-loc 2)))


(define (gc:flat? loc) (equal? (heap-ref loc) 'flat))
(define (gc:cons? loc) (equal? (heap-ref loc) 'cons))

(define (gc:set-first! pr-ptr new)
  (chk-pair pr-ptr 'gc:set-first!)
  (heap-set! (+ pr-ptr 1) new))

(define (gc:set-rest! pr-ptr new)
  (chk-pair pr-ptr 'gc:set-rest!)
  (heap-set! (+ pr-ptr 2) new))

; 'closure size-of-variables code-ptr free-varible ...
(define (gc:closure code-ptr free-vars)
  (let ([fv-count (length free-vars)])
    (let ([loc (malloc (+ fv-count 3))])
      (begin
        (heap-set! loc 'closure)
        (heap-set! (+ loc 1) fv-count)
        (heap-set! (+ loc 2) code-ptr)
        (for ([i (in-naturals)]
              [r free-vars])
          (heap-set! (+ loc 3 i) (read-root r)))
        loc))))

(define/contract (chk-closure loc who)
  (-> location? symbol? void?)
  (unless (gc:closure? loc)
    (error who "expected a closure @ loc ~a" loc)))

(define (gc:closure-code-ptr loc)
  (chk-closure loc 'gc:closure-code-ptr)
  (heap-ref (+ loc 2)))

(define (gc:closure-env-ref loc i)
  (chk-closure loc 'gc:closure-env-ref)
  (heap-ref (+ loc 3 i)))
    

(define (gc:closure? loc) (equal? (heap-ref loc) 'closure))


(test (let ([v (vector #f #f #f #f #f #f #f #f #f #f #f #f)])
        (with-heap v
                   (init-allocator)
                   (malloc 1)
                   (malloc 1)
                   (malloc 9))
        v)
      #(12 #f #f #f #f #f #f #f #f #f #f #f))

(test (let ([v (vector #f #f #f #f #f #f #f #f #f)])
        (with-heap v
                   (init-allocator)
                   (gc:alloc-flat 9)
                   (gc:alloc-flat #t)
                   (gc:alloc-flat '())
                   (gc:alloc-flat 'afk)
                   (gc:deref 7)))
      'afk)

(let ([h (vector 'x 'x 'x 'x 'x)])
  (test (with-heap h
                   (init-allocator)
                   (gc:alloc-flat #f)
                   h)
        (vector 3 'flat #f 'x 'x)))


(define (make-simple-root n)
  (define b (box n))
  (make-root 'simple-root
             (λ () (unbox b))
             (λ (n) (set-box! b n))))
(let ([h (vector 'x 'x 'x 'x 'x 'x 'x 'x 'x)])
  (test (with-heap
         h
         (init-allocator)
         (gc:cons
          (make-simple-root (gc:alloc-flat #f))
          (make-simple-root (gc:alloc-flat #t)))
         h)
        (vector 8 'flat #f 'flat #t 'cons 1 3 'x)))
