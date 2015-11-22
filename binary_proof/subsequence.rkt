#lang racket


;; returns #f if the content of p1 is a subsequence
;; of the content of p2, otherwise returns the first line
;; in p1 that isn't in p2.
(define/contract (is-sub-sequence p1 p2)
  (-> input-port? input-port? (or/c string? #f))
  (let loop ()
    (define l1 (read-line p1))
    (cond
      [(eof-object? l1) #f]
      [else
       (define l1-result
         (let loop ()
           (define l2 (read-line p2))
           (cond
             [(eof-object? l2) l1]
             [(matches? l1 l2) #f]
             [else (loop)])))
       (if (string? l1-result)
           l1-result
           (loop))])))

(define (matches? l1 l2)
  (regexp-match?
   (regexp-quote
    (regexp-replace
     #rx" *$"
     (regexp-replace #rx"^ *" l1 "")
     ""))
   l2))

(module+ test
  (require rackunit)

  (check-true (matches? "x" "x"))
  (check-true (matches? "x " "x"))
  (check-true (matches? " x" "x"))
  (check-true (matches? "    x y z   " " x y z "))
  (check-false (matches? "x" "y"))

  (define (is-sub/str s1 s2)
    (is-sub-sequence (open-input-string s1)
                     (open-input-string s2)))
  
  (check-equal? (is-sub/str "" "") #f)
  (check-equal? (is-sub/str "" " ") #f)
  (check-equal? (is-sub/str "x" "y") "x")
  (check-equal? (is-sub/str "a\nb\nc\n" "a\nb\nc\n") #f)
  (check-equal? (is-sub/str "a\nb\nc\n" "b\na\nb\nc\n") #f)
  (check-equal? (is-sub/str "a\nb\nc\n" "b\na\nc\n") "b"))

(define (run f1 f2)
  (define s
    (call-with-input-file f1
      (λ (p1)
        (call-with-input-file f2
          (λ (p2)
            (is-sub-sequence p1 p2))))))
  (cond
    [(string? s)
     (eprintf
      (string-append
       "in ~a, expected to find this line but didn't:\n~a\n"
       "(warning: this line may be out of order wrt to the first file, tho)\n")
      f2
      s)]
    [else (void)]))

(module+ main
  (command-line
   #:args (file1.v file2.v)
   (run file1.v file2.v)))
