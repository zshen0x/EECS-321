#lang plai/gc2/mutator
(allocator-setup "collector.rkt" 200)
(define (build-one)
  (let* ((x0 0)
         (x1 #t)
         (x2
          (lambda (x)
            (if (= x 0)
              x0
              (if (= x 1)
                x1
                (if (= x 2)
                  x1
                  (if (= x 3) x0 (if (= x 4) x0 (if (= x 5) x1 x1)))))))))
    x2))
(define (traverse-one x2) (= 0 (x2 3)))
(define (trigger-gc n)
  (if (zero? n) 0 (begin (cons n n) (trigger-gc (- n 1)))))
(define (loop i)
  (if (zero? i)
    'passed
    (let ((obj (build-one)))
      (trigger-gc 200)
      (if (traverse-one obj) (loop (- i 1)) 'failed))))
(loop 200)
