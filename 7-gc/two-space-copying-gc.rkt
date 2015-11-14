
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
; heap structure 4 reserved space, and allocate space
;
;(define active-space-ptr 0)
;(define alloc-pr-ptr 1)
;(define left-pr-ptr 2)
;(define right-pr-ptr 3)

(define (memory-set-free! start size)
  (for ([loc (in-range start (+ start size))])
    (heap-set! loc 'free)))

(define (init-allocator)
  (unless ((heap-size) . > . 6)
    (error 'init-allocator "no enough memory for init"))
;  (for ([loc (in-range 0 (heap-size))])
;    (heap-set! loc 'free))
  (memory-set-free! 0 (heap-size))
  (begin
    (heap-set! 0 4)
    (heap-set! 1 (heap-ref 0))
    (heap-set! 2 (+ (heap-ref 0)
                    (quotient (- (heap-size) 4) 2)))
    (heap-set! 3 (heap-ref 2))))

(define (gc:deref fl-loc)
  (if (gc:flat? fl-loc)
      (heap-ref (+ fl-loc 1))
      (error 'gc:deref "expected a flat value")))
;procedure
;(gc:alloc-flat val) → location?
;  val : heap-value?
; gc here

(define/contract (find-n-free-space size)
  (-> exact-nonnegative-integer? (or/c location? #f))
  (let ([loc (heap-ref 1)])
    (if ((+ loc size) . <= . (+ (heap-ref 0)
                                (quotient (- (heap-size) 4) 2)))
        loc
        #f)))

(define/contract (enqueue from-loc)
  (-> location? location?)
  (let ([active-space (heap-ref 2)]
        [left-pr (heap-ref 2)]
        [right-pr (heap-ref 3)])
    (match (heap-ref from-loc)
      ['marked (heap-ref (+ from-loc 1))]
      ['flat (begin
               (heap-set! right-pr 'flat)
               (heap-set! (+ right-pr 1) (heap-ref (+ from-loc 1)))
               (heap-set! from-loc 'marked)
               (heap-set! (+ from-loc 1) right-pr)
               (heap-set! 3 (+ right-pr 2))
               right-pr)]
      ['cons (begin
               (heap-set! right-pr 'cons)
               (heap-set! (+ right-pr 1) (heap-ref (+ from-loc 1)))
               (heap-set! (+ right-pr 2) (heap-ref (+ from-loc 2)))
               (heap-set! from-loc 'marked)
               (heap-set! (+ from-loc 1) right-pr)
               (heap-set! 3 (+ right-pr 3))
               right-pr)]
      ['closure (let ([fv-count (heap-ref (+ from-loc 1))])
                  (begin
                    (heap-set! right-pr 'closure)
                    (heap-set! (+ right-pr 1) fv-count)
                    (heap-set! (+ right-pr 2) (heap-ref (+ from-loc 2)))
                    (for ([i (in-range fv-count)])
                      (heap-set! (+ right-pr 3 i)
                                 (heap-ref (+ from-loc 3 i))))
                    (heap-set! from-loc 'marked)
                    (heap-set! (+ from-loc 1) right-pr)
                    (heap-set! 3 (+ right-pr 3 fv-count))
                    right-pr))])))

;traverse in the to space only left pointer moves here
(define (traverse-queue)
  (let ([active-space (heap-ref 2)]
        [left-pr (heap-ref 2)]
        [right-pr (heap-ref 3)])
    (unless (left-pr . >= . right-pr)
      (match (heap-ref left-pr)
        ['flat (heap-set! 2 (+ left-pr 2))
               (traverse-queue)]
        ['cons (let ([ptr1 (heap-ref (+ left-pr 1))]
                     [ptr2 (heap-ref (+ left-pr 2))])
                 (let ([new-ptr1 (enqueue ptr1)]
                       [new-ptr2 (enqueue ptr2)])
                   (begin
                     (heap-set! (+ left-pr 1) new-ptr1)
                     (heap-set! (+ left-pr 2) new-ptr2)
                     (heap-set! 2 (+ left-pr 3)))
                   (traverse-queue)))]
        ['closure (let ([fv-count (heap-ref (+ left-pr 1))])
                    (for ([i (in-range 0 fv-count)])
                      (let ([new-ptr (enqueue (heap-ref (+ left-pr 3 i)))])
                        (heap-set! (+ left-pr 3 i) new-ptr)))
                    (heap-set! 2 (+ left-pr 3 fv-count))
                    (traverse-queue))]))))


(define/contract (traverse/copy rt)
  (-> root? void?)
  (begin
    ; copy root 
    (let ([from-loc (read-root rt)])
      (let ([to-loc (enqueue from-loc)])
        (set-root! rt to-loc)))
    ; copy the rest
    (traverse-queue)))

;(define/contract (traverse/root rt)
;  (-> root? void?)
;  (cond
;    [(root? thing) (traverse/copy (read-root rt))]
;    [else (error 'collect-garbage-2space "not a root or location")]))

(define/contract (collect-garbage-2space roots)
  (-> (listof root?) void?)
  (let ([old-active-space (heap-ref 0)] ;left
        [old-allocator-pointer (heap-ref 1)]
        [old-left-pr (heap-ref 2)]
        [old-right-pr (heap-ref 3)])
    (begin
      (for-each traverse/copy roots)
      (heap-set! 0 old-left-pr)
      (heap-set! 1 (heap-ref 2))
      (heap-set! 2 old-active-space)
      (heap-set! 3 old-active-space)
      (memory-set-free! old-active-space (quotient (- (heap-size) 4) 2)))))

(define/contract (malloc size extra-roots)
  (-> exact-nonnegative-integer? (listof root?) location?)
  (let ([first-try (find-n-free-space size)])
    (if first-try
        (begin
          (heap-set! 1 (+ first-try size))
          first-try)
        (begin
          (collect-garbage-2space (append (get-root-set) extra-roots))
          (let ([second-try (find-n-free-space size)])
            (if second-try
                (begin
                  (heap-set! 1 (+ second-try size))
                  second-try)
                (error 'malloc "run out of memory")))))))


(define (gc:alloc-flat fv)
  (let ([loc (malloc 2 empty)])
    (begin
      (heap-set! loc 'flat)
      (heap-set! (+ loc 1) fv))
    loc))

(define (gc:cons hd tl)
  (let ([loc (malloc 3 (list hd tl))]
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
    (let ([loc (malloc (+ fv-count 3) free-vars)])
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

#|
(print-only-errors)
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
|#