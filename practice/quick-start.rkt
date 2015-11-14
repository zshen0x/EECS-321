#lang slideshow
(define c (circle 10))
(define r (rectangle 10 20))

(define (square c)
  ; semicolon start a line comment
  ; the expression below is the function body
  (filled-rectangle c c))

(define (four p)
  (define two-p (hc-append p p))
  (vc-append two-p two-p))

(define (checker p1 p2)
  (let ([p12 (hc-append p1 p2)]
        [p21 (hc-append p2 p1)])
  (vc-append p12 p21)))

(define (checkerboard p)
  (let* ([rp (colorize p "red")]
         [bp (colorize p "black")]
         [c (checker rp bp)]
         [c4 (four c)])
    (four c4)))

(define (series mk)
  (hc-append 10 (mk 1) (mk 2) (mk 3) (mk 5) (mk 8) (mk 11)))

(define (rainbow p)
  (map (lambda (color)
         (colorize p color))
       (list "red" "orange" "yellow" "green" "blue" "purple")))


(require slideshow/code)
(define-syntax pict+code
  (syntax-rules ()
    [(pict+code expr)
     (hc-append 10
                expr
                (code expr))]))

(require racket/class
         racket/gui/base)

(define f (new frame% [label "my name"]
                      [width 300]
                      [height 300]
                      [alignment '(center center)]))

(define (add-drawing p)
  ;pict as input
  (let ([drawer (make-pict-drawer p)])
    (new canvas% [parent f]
                 [style '(border)]
                 [paint-callback (lambda (self dc)
                                   (drawer dc 0 0))])))



