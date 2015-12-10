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

;<TRFAE> = <number>
;        | {+ <RFAE> <RFAE>}
;        | {- <RFAE> <RFAE>}
;        | {fun {<id>} <RFAE>}
;        | {<RFAE> <RFAE>}             ;; function application
;        | <id>
;        | {with {<id> <RFAE>} <RFAE>} ;; shorthand for fun & app
;        | {struct {<id> <RFAE>} ...}  ;; all fields must be distinct
;        | {get <RFAE> <id>}
;        | {set <RFAE> <id> <RFAE>}
;        | {spawn <RFAE>}
;        | {deliver <RFAE> <RFAE>}
;        | {receive}
;        | {seqn <RFAE> <RFAE>}
;; data structure
;;

(define-type TRFAE
  [num (n number?)]
  [add (lhs TRFAE?)
       (rhs TRFAE?)]
  [sub (lhs TRFAE?)
       (rhs TRFAE?)]
  [fun (param symbol?)
       (body TRFAE?)]
  [app (fun-expr TRFAE?)
       (arg-expr TRFAE?)]
  [id (name symbol?)]
  [record (listof list?)]
  [record-get (rcd TRFAE?)
              (id symbol?)]
  [record-set (rcd TRFAE?)
              (name symbol?)
              (value TRFAE?)]
  [spawn (thread TRFAE?)]
  [deliver (thread TRFAE?)
           (value TRFAE?)]
  [receive]
  [seqn (expr1 TRFAE?)
        (expr2 TRFAE?)])

;; map: name -> store location
(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?)
        (address number?)
        (rest DefrdSub?)])

(define-type TRFAE-Value
  [numV (n number?)]
  [closureV (param symbol?)
            (body TRFAE?)
            (ds DefrdSub?)]
  [recV (address integer?)
        (ids (listof symbol?))
        (ptrs (listof integer?))] ;; records

  ;; thd values hold the location in the
  ;; store where undelivered values wait
  ;; to be delivered
  [thdV (address integer?)])

;; map: address -> value
(define-type Store 
  [mtSto]
  [aSto (address integer?)
        (value (or/c TRFAE-Value?
                     ;; lists mean that this
                     ;; location in the store
                     ;; belongs to a thd
                     (listof TRFAE-Value?)))
        (rest Store?)])

(define-type Thds*Store
  [thds*store (thds (listof Thd?)) (store Store?)])

;; the tid's are the store locations for those thds
(define-type Thd
  [active (tid integer?) (go (-> Store? Thds*Store?))] ;; a trick
  [blocked (tid integer?) (continue (-> TRFAE-Value? Store? Thds*Store?))]
  [notify (tid integer?) (message (listof TRFAE-Value?))]
  [done (v TRFAE-Value?)])

;; parser: s-expr -> TRFAE
(define/contract (parse s-expr)
  (-> any/c TRFAE?)
  (match s-expr
    [(? number?) (num s-expr)]
    [(? symbol?) (id s-expr)]
    [`{+ ,e1 ,e2} (add (parse e1) (parse e2))]
    [`{- ,e1 ,e2} (sub (parse e1) (parse e2))]
    [`{with {,id ,e1} ,e2} (parse `{{fun {,id} ,e2} ,e1})]
    [`{fun {,(? symbol? param)} ,bd} (fun param (parse bd))]
    [`{struct ,(? cons? fields) ...}
     (record (map (λ (p) (cons (first p) (parse (last p)))) fields))]
    [`{get ,e1 ,(? symbol? id)} (record-get (parse e1) id)]
    [`{set ,e1 ,(? symbol? id) ,e2} (record-set (parse e1) id (parse e2))]
    [`{spawn ,expr} (spawn (parse expr))]
    [`{deliver ,e1 ,e2} (deliver (parse e1) (parse e2))]
    [`{receive} (receive)]
    [`{seqn ,e1 ,e2} (seqn (parse e1) (parse e2))]
    [`{,fun-expr ,arg-expr} (app (parse fun-expr) (parse arg-expr))]
    [_ (error "bad syntax when parsing:\n" s-expr)]))

;; map relation function
; lookup, set-store and get-store to be atom operation

; variable -> location
(define/contract (lookup-defrdsub named-id ds)
  (-> symbol? DefrdSub? exact-nonnegative-integer?)
  (type-case DefrdSub ds
    [mtSub () (error "free identifier: " named-id)]
    [aSub (name loc rst) (cond
                           [(equal? name named-id) loc]
                           [else (lookup-defrdsub named-id rst)])]))

; loc -> value
(define/contract (lookup-store loc st)
  (-> exact-nonnegative-integer? Store? (or/c TRFAE-Value? (listof TRFAE-Value?)))
  (type-case Store st
    [mtSto () (error "unknow store location: " loc)]
    [aSto (addr val rst)(cond
                          [(equal? addr loc) val]
                          [else (lookup-store loc rst)])]))

; alloc-store
(define/contract (top-store st)
  (-> Store? exact-nonnegative-integer?)
  (type-case Store st
    [mtSto () 0]
    [aSto (addr val rst) addr]))

(define/contract (alloc-store loc val st)
  (-> exact-nonnegative-integer? (or/c TRFAE-Value? (listof TRFAE-Value?)) Store? Store?)
  (aSto loc val st))

; set-store
(define/contract (set-store loc new-val st)
  (-> exact-nonnegative-integer? (or/c TRFAE-Value? (listof TRFAE-Value?)) Store? Store?)
  (type-case Store st
    [mtSto () (error "unknow store location: " loc)]
    [aSto (addr val rst)(cond
                          [(equal? addr loc) (aSto addr new-val rst)]
                          [else (aSto addr val (set-store loc new-val rst))])]))

;; binary operation over numbers
(define/contract (numVop op l r ds addr st k)
  (-> (-> number? number? number?)
      TRFAE?
      TRFAE?
      DefrdSub?
      exact-nonnegative-integer?
      Store?
      (-> TRFAE-Value? Store? Thds*Store?)
      Thds*Store?)
  (execute-thd l
               ds
               addr
               st
               (λ (l-v st1)
                 (execute-thd r
                              ds
                              addr
                              st1
                              (λ (r-v st2)
                                (k (numV (cond
                                           [(and (numV? l-v) (numV? r-v)) (op (numV-n l-v)
                                                                              (numV-n r-v))]
                                           [else (error "numeric operation expected number")]))
                                   st2))))))
;; create and allocate a record
;; like num and fun be atomatic operation

;; spawn create thds
;; one running thread
(define/contract (execute-thd a-trfae ds addr st k)
  (-> TRFAE? DefrdSub? integer? Store?
      (-> TRFAE-Value? Store? Thds*Store?)
      Thds*Store?)
  (type-case TRFAE a-trfae
    [num (n) (thds*store (list (active addr
                                       (λ (sto)
                                         (k (numV n) sto))))
                         st)]
    [add (l r) (thds*store (list (active addr
                                         (λ (sto)
                                           (numVop + l r ds addr sto k))))
                           st)]
    [sub (l r) (thds*store (list (active addr (λ (sto)
                                                (numVop - l r ds addr sto k))))
                           st)]
    [fun (param body) (thds*store (list (active addr (λ (sto)
                                                       (k (closureV param body ds) sto))))
                                  st)]
    ;; to do evaluate function first
    [app (fun-expr arg-expr)
         (thds*store (list (active addr
                                   (λ (sto)
                                     (execute-thd fun-expr
                                                  ds
                                                  addr
                                                  sto
                                                  (λ (clo-v sto1)
                                                    (execute-thd arg-expr
                                                                 ds
                                                                 addr
                                                                 sto1
                                                                 (λ (arg-v sto2)
                                                                   (type-case TRFAE-Value clo-v
                                                                     [closureV (param body clo-ds)
                                                                               (letrec ([top-loc (add1 (top-store sto2))]
                                                                                        [sto3 (alloc-store top-loc
                                                                                                           arg-v
                                                                                                           sto2)])
                                                                                 (execute-thd body
                                                                                              (aSub param
                                                                                                    top-loc
                                                                                                    clo-ds)
                                                                                              addr
                                                                                              sto3
                                                                                              k))]
                                                                     [else (error 'execute-thd "application expected procedure")]))))))))
                     st)]
    
    [id (name) (thds*store (list (active addr (λ (sto) (k (lookup-store (lookup-defrdsub name ds) sto) sto)))) st)]
    [record (fields)
            (thds*store (list (active addr (λ (sto)
                                             (cond
                                               [(empty? fields) (letrec ([top-loc (add1 (top-store sto))]
                                                                         [a-recv (recV top-loc empty empty)]
                                                                         [sto2 (alloc-store top-loc a-recv sto)])
                                                                  (k a-recv sto2))]
                                               [else
                                                (letrec ([fst (first fields)]
                                                         [id (car fst)]
                                                         [val-expr (cdr fst)]
                                                         [rst (rest fields)])
                                                  (execute-thd val-expr
                                                               ds
                                                               addr
                                                               sto
                                                               (λ (v1 sto1)
                                                                 (execute-thd (record rst)
                                                                              ds
                                                                              addr
                                                                              sto1
                                                                              (λ (v2 sto2)
                                                                                (letrec ([recv-loc (recV-address v2)]
                                                                                         [ids (recV-ids v2)]
                                                                                         [ptrs (recV-ptrs v2)]
                                                                                         [v1-ptr (add1 (top-store sto2))]
                                                                                         [sto3 (alloc-store v1-ptr v1 sto2)]
                                                                                         [nrecv (recV recv-loc
                                                                                                      (cons id ids)
                                                                                                      (cons v1-ptr ptrs))])
                                                                                  (k nrecv (set-store recv-loc nrecv sto3))))))))]))))
                        st)]
    [record-get (rcd-expr named-id)
                (thds*store (list (active addr
                                          (λ (sto)
                                            (execute-thd rcd-expr
                                                         ds
                                                         addr
                                                         sto
                                                         (λ (v1 sto1)
                                                           (type-case TRFAE-Value v1
                                                             [recV (addr ids ptrs)
                                                                   (let ([ptr (for/first ([id ids]
                                                                                          [ptr ptrs]
                                                                                          #:when (equal? id named-id))
                                                                                ptr)])
                                                                       (cond
                                                                         [(integer? ptr) (k (lookup-store ptr sto1) sto1)]
                                                                         [else (error 'execute-thd "unknown field")]))]
                                                             [else (error 'execute-thd "record operation expected record")]))))))
                            st)]
    
    [record-set (rcd-expr named-id val-expr)
                (thds*store (list (active addr
                                          (λ (sto)
                                            (execute-thd rcd-expr
                                                         ds
                                                         addr
                                                         sto
                                                         (λ (v1 sto1)
                                                           (execute-thd val-expr
                                                                        ds
                                                                        addr
                                                                        sto1
                                                                        (λ (v2 sto2)
                                                                          (type-case TRFAE-Value v1
                                                                            [recV (addr ids ptrs)
                                                                                  (let ([ptr (for/first ([id ids]
                                                                                                         [ptr ptrs]
                                                                                                         #:when (equal? id named-id))
                                                                                               ptr)])
                                                                                    (cond
                                                                                      [(integer? ptr) (let ([oldv (lookup-store ptr sto2)])
                                                                                                        (k oldv (set-store ptr v2 sto2)))]
                                                                                      [else (error 'execute-thd "unknown field")]))]
                                                                            [else (error 'execute-thd "record operation expected record")]))))))))
                            st)]
    [spawn (thd-expr) (letrec ([new-loc (add1 (top-store st))]
                               [thd-val (thdV new-loc)]
                               [st1 (alloc-store new-loc (list thd-val) st)])
                        (thds*store (list (active new-loc
                                                  (λ (st2)
                                                    (execute-thd thd-expr
                                                                 ds
                                                                 new-loc
                                                                 st2
                                                                 (λ (v3 st3)
                                                                   (let ([st4 (set-store new-loc (list v3) st3)])
                                                                     (thds*store (list (done v3)) st4))))))
                                          (notify new-loc empty)
                                          (active addr (λ (a-st)
                                                         (k thd-val a-st))))
                              st1))]
    [deliver (thd-expr val-expr)
             (thds*store (list (active addr
                                       (λ (sto)
                                         (execute-thd val-expr
                                                      ds
                                                      addr
                                                      sto
                                                      (λ (v1 st1)
                                                        (execute-thd thd-expr
                                                                     ds
                                                                     addr
                                                                     st1
                                                                     (λ (v2 st2)
                                                                       (type-case TRFAE-Value v2
                                                                         [thdV (loc)
                                                                               (thds*store (list (notify loc (list v1))
                                                                                                 (active addr
                                                                                                         (λ (a-st)
                                                                                                           (k v1 a-st))))
                                                                                           st2)]
                                                                         [else (error 'execute-id "deliver expected thd")]))))))))
                         st)]
    
    [receive () (thds*store
                 (list (blocked addr (λ (v1 st1)
                                       (k v1 st1))))
                 st)]
    [seqn (e1 e2) (thds*store (list (active addr
                                            (λ (sto)
                                              (execute-thd e1
                                                           ds
                                                           addr
                                                           sto
                                                           (λ (v1 st1)
                                                             (execute-thd e2
                                                                          ds
                                                                          addr
                                                                          st1
                                                                          k))))))
                              st)]))

; init thread and scheduler
; run - update - cycle
(define/contract (thds-merge thds-lst others)
  (-> (listof Thd?) (listof Thd?) (listof Thd?))
  (letrec ([old-ms (filter (λ (td) (notify? td)) thds-lst)]
           [others-ms (filter (λ (td) (notify? td)) others)]
           [rest-others (filter (λ (td) (not (notify? td))) others)]
           [old-ms-update (map (λ (ele1)
                                 (let ([m (findf (λ (ele2) (equal? (notify-tid ele1) (notify-tid ele2))) others-ms)])
                                   (if m
                                       (notify (notify-tid m) (append (notify-message ele1)
                                                                      (notify-message m)))
                                       ele1)))
                                 old-ms)]
           [new-ms-to-add (filter (λ (td)
                                    (not (findf (λ (ele) (equal? (notify-tid td) (notify-tid ele))) old-ms)))
                                  others-ms)]
           [messages (append old-ms-update new-ms-to-add)]
           [rest-thds (remove* old-ms thds-lst)]
           [all-thds (append rest-thds rest-others messages)]
           [blocked-thds (filter (λ (td) (blocked? td)) all-thds)]
           [to-be-wakeup (for/list ([m messages]
                                    #:when (blocked? (findf (λ (ele) (and (not (empty? (notify-message m)))
                                                                          (equal? (blocked-tid ele) (notify-tid m))))
                                                            blocked-thds)))
                           (cons m (findf (λ (ele) (equal? (blocked-tid ele) (notify-tid m))) blocked-thds)))]
           [wakeups (map (λ (p) (active (notify-tid (car p))
                                        (λ (sto)
                                          ((blocked-continue (cdr p)) (first (notify-message (car p)))
                                                                      sto))))
                         to-be-wakeup)]
           [ms-updated (map (λ (p) (notify (notify-tid (car p)) (rest (notify-message (car p))))) to-be-wakeup)]
           [to-remove (flatten to-be-wakeup)])
    (append (remove* to-remove all-thds)
            wakeups
            ms-updated)))

(define (threads-scheduler t*s)
  (type-case Thds*Store t*s
    [thds*store (thds st)
                (cond
                  [(not (for/or ([td thds]) (active? td))) (filter (λ (td) (not (notify? td))) thds)] ;no active thread, output thds, 
                  [else (let ([active-thds (filter (λ (thd) (active? thd)) thds)])
                          (cond
                            [(not (empty? active-thds)) (letrec ([a-thd (list-ref active-thds
                                                                                  (random (length active-thds)))]
                                                                 [rst-thds (remove a-thd thds)]
                                                                 [t1*s1 ((active-go a-thd) st)])
                                                          (type-case Thds*Store t1*s1
                                                            [thds*store (thds1 st1) (let ([t2*s1 (thds*store (thds-merge rst-thds
                                                                                                                         thds1)
                                                                                                             st1)])
                                                                                      (threads-scheduler t2*s1))]))]
                            [else (threads-scheduler t*s)]))])])) ;; when all thread are blocked forever loop

(define (interp-expr a-trfae)
  (letrec ([init-thds-pool (thds*store (list (active 0 (λ (sto)
                                                         (execute-thd a-trfae
                                                                      (mtSub)
                                                                        0
                                                                        (aSto 0
                                                                              (list (thdV 0))
                                                                              sto)
                                                                        (λ (v st)
                                                                          (let ([st1 (set-store 0 (list v) st)])
                                                                            (thds*store (list (done v)) st1))))))
                                             (notify 0 empty))
                                       (mtSto))])
    (map (λ (done-thd)
           (type-case Thd done-thd
             [done (v) (type-case TRFAE-Value v
                         [numV (n) n]
                         [closureV (x y z) 'procedure]
                         [thdV (addr) 'thd]
                         [recV (x y z) (error 'bug "never reach here!")])]
             [blocked (tid continue) 'blocked]
             [else (error 'bug "never reach here!")]))
         (threads-scheduler init-thds-pool))))


;(define (threads-scheduler-debug t*s)
;  (type-case Thds*Store t*s
;    [thds*store (thds st)
;                (cond
;                  [(not (for/or ([td thds]) (active? td))) t*s] ;no active thread, output thds
;                  [else (let ([active-thds (filter (λ (thd) (active? thd)) thds)])
;                          (cond
;                            [(not (empty? active-thds)) (letrec ([a-thd (list-ref active-thds
;                                                                                  (random (length active-thds)))]
;                                                                 [rst-thds (remove a-thd thds)]
;                                                                 [t1*s1 ((active-go a-thd) st)])
;                                                          (type-case Thds*Store t1*s1
;                                                            [thds*store (thds1 st1) (let ([t2*s1 (thds*store (thds-merge rst-thds
;                                                                                                                         thds1)
;                                                                                                             st1)])
;                                                                                      (threads-scheduler-debug t2*s1))]))]
;                            [else (threads-scheduler t*s)]))])]))
;
;(define (interp-expr-debug a-trfae)
;  (let ([thds-pool (execute-thd a-trfae
;                                (mtSub)
;                                0
;                                (aSto 0 (list (thdV 0)) (mtSto))
;                                (λ (v st)
;                                  (let ([st1 (set-store 0 (list v) st)])
;                                    (thds*store (list (done v)) st1))))])
;         (println (threads-scheduler-debug thds-pool))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; test case
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(print-only-errors)

(test (parse '5) (num 5))
(test (parse '((fun (x) (+ x 1)) 10))
      (app (fun 'x (add (id 'x) (num 1))) (num 10)))
(test (parse '(with (f (fun (x) (+ x 1))) (f 10)))
      (app (fun 'f (app (id 'f) (num 10))) (fun 'x (add (id 'x) (num 1)))))

(define (same-elements? l1 l2)
  (define (sub-mutiset? l1 l2)
    (cond
      [(null? l1) #t]
      [else (and (member (car l1) l2)
                 (subset? (cdr l1) (remove (car l1) l2)))]))
  (and (sub-mutiset? l1 l2) (sub-mutiset? l2 l1)))

;; basic test cases
(test (interp-expr (parse '5)) '(5))
(test (interp-expr (parse '{+ 5 5})) '(10))
(test (interp-expr (parse '{- 3 5})) '(-2))
(test/exn (interp-expr (parse 'x)) "free identifier")
#;#;#;
(test (interp (id 'x) (aSub 'x (numV 5) (mtSub)) (mtSto) (λ (ev s) (v*s ev s))) (v*s (numV 5) (mtSto)))
(test (interp (id 'x) (aSub 'y (numV 6) (aSub 'x (numV 5) (mtSub))) (mtSto) (λ (ev s) (v*s ev s))) (v*s (numV 5) (mtSto)))
(test (interp (add (num 5) (sub (add (num 3) (id 'x)) (id 'y)))
              (aSub 'y (numV 6) (aSub 'x (numV 5) (mtSub))) (mtSto) (λ (ev s) (v*s ev s)))
      (v*s (numV 7) (mtSto)))
(test (interp-expr (parse '{with {x 5} {+ x x}})) '(10))
#;
(test (interp (parse '{fun {x} {+ x 1}}) (mtSub) (mtSto) (λ (ev s) (v*s ev s)))
      (v*s (closureV 'x (add (id 'x) (num 1)) (mtSub)) (mtSto)))
(test (interp-expr (parse '{{fun {x} {+ x 1}} 10})) '(11))
(test/exn (interp-expr (parse '{with {x x} x}))
          "free identifier")
#;#;#;#;#;#;
(test (interp (parse '{struct}) (mtSub) (mtSto) (λ (ev s) (v*s ev s)))
      (v*s (recV '()) (mtSto)))
(test (interp (parse '{struct {x 1}}) (mtSub) (mtSto) (λ (ev s) (v*s ev s)))
      (v*s (recV '(0)) (aSto 0 'x (numV 1) (mtSto))))
(test (interp (parse '{struct {x 1} {y 2}}) (mtSub) (mtSto) (λ (ev s) (v*s ev s)))
      (v*s (recV '(0 1)) (aSto 1 'y (numV 2) (aSto 0 'x (numV 1) (mtSto)))))
(test (interp (parse '{struct {x 1} {y 2} {z 3}}) (mtSub) (mtSto) (λ (ev s) (v*s ev s)))
      (v*s (recV '(0 1 2)) (aSto 2 'z (numV 3) (aSto 1 'y (numV 2) (aSto 0 'x (numV 1) (mtSto))))))
(test (interp (parse '{get {struct {x 1} {y 2} {z 3}} y}) (mtSub) (mtSto) (λ (ev s) (v*s ev s)))
      (v*s (numV 2) (aSto 2 'z (numV 3) (aSto 1 'y (numV 2) (aSto 0 'x (numV 1) (mtSto))))))
(test (interp (parse '{set {struct {x 1} {y 2} {z 3}} y 100}) (mtSub) (mtSto) (λ (ev s) (v*s ev s)))
      (v*s (numV 2) (aSto 2 'z (numV 3) (aSto 1 'y (numV 100) (aSto 0 'x (numV 1) (mtSto))))))
(test (interp-expr (parse '{with {q {struct {x 10}}}
                                 {seqn {set q x 12} {get q x}}})) '(12))

;; more test cases
(test (interp-expr (parse '{with {x {+ 5 5}} {with {y {- x 3}} {+ y y}}}))
      '(14))
(test (interp-expr (parse '{with {x 5} {with {y {- x 3}} {+ y y}}}))
      '(4))
(test (interp-expr (parse '{with {x 5} {+ x {with {x 3} 10}}})) '(15))
(test (interp-expr (parse '{with {x 5} {+ x {with {x 3} x}}})) '(8))
(test (interp-expr (parse '{with {x 5} {with {x x} x}})) '(5))
(test (interp-expr (parse '{with {x 5} {{fun {y} {+ x y}} 10}})) '(15))
(test (interp-expr (parse '{with {x 5} {{fun {x} {+ x x}} 10}})) '(20))
(test (interp-expr (parse '{with {f {fun {x} {+ x 1}}} {f 10}})) '(11))
(test (interp-expr (parse '{with {x 3}
                                 {with {f {fun {y} {+ x y}}}
                                       {with {x 5} {f 4}}}}))
      '(7))
(test (interp-expr (parse '{{with {y 10} {fun {x} {+ y x}}} {with {y 7} y}}))
      '(17))

;; tests come with HW
(test/exn (interp-expr (parse '{struct {z {get {struct {z 0}} y}}}))
            "unknown field")
(test (interp-expr (parse '{{fun {r} {get r x}} {struct {x 1}}})) '(1))
(test (interp-expr (parse '{{fun {r} {seqn {set r x 5} {get r x}}}
                            {struct {x 1}}})) '(5))
(test (interp-expr (parse `{set {struct {x 42}} x 2})) '(42))
(test (interp-expr (parse '{{{{{fun {g}
                                    {fun {s}
                                         {fun {r1}
                                              {fun {r2}
                                                   {+ {get r1 b}
                                                      {seqn
                                                       {{s r1} {g r2}}
                                                       {+ {seqn
                                                           {{s r2} {g r1}}
                                                           {get r1 b}}
                                                          {get r2 b}}}}}}}}
                               {fun {r} {get r a}}}            ; g
                              {fun {r} {fun {v} {set r b v}}}} ; s
                             {struct {a 0} {b 2}}}             ; r1
                            {struct {a 3} {b 4}}}))            ; r2
      '(5))

#;
(interp-expr (parse '{with {b {struct {x 1}}}
                           {with {f {fun {f}
                                         {seqn {set b x 2}
                                               {f f}}}}
                                 {f f}}}))

;; error testing
(test/exn (interp-expr (parse '{with {q {struct}} {get q x}})) "unknown field")
(test/exn (interp-expr (parse '{with {q {struct {y 1} {z 2}}} {get q x}})) "unknown field")
(test/exn (interp-expr (parse '{get (+ 5 6) x})) "record operation expected record")
(test/exn (interp-expr (parse '{deliver 1 2})) "deliver expected thd")

;; multi thd test
(test (same-elements? (interp-expr (parse `{seqn {spawn 1} 2})) (list 1 2)) #t)
(test (same-elements? (interp-expr (parse `{with {x 1} {seqn {spawn x} 2}})) (list 1 2)) #t)
(test/exn (interp-expr (parse '{spawn {0 0}})) "application expected procedure")
(test (same-elements? (interp-expr
                       (parse `{with {t1 {spawn {seqn {receive} {receive}}}}
                                     {seqn {deliver t1 1}
                                           {seqn {deliver t1 2}
                                                 3}}}))
                      (list 2 3)) #t)
#;
(interp-expr (parse '{with {b {struct {x 1}}}
                           {seqn {spawn {set b x 2}}
                                 {seqn {spawn {set b x 3}}
                                       {get b x}}}}))
(test/exn (interp-expr
           (parse '{seqn {spawn {{fun {x} {x x}} {fun {x} {x x}}}}
                         {0 0}}))
          "application expected procedure")
(test/exn (interp-expr
           (parse '{seqn {spawn {0 0}}
                         {{fun {x} {x x}} {fun {x} {x x}}}}))
          "application expected procedure")
(test
 (same-elements?
  (interp-expr
   (parse '{seqn {spawn {{{{{fun {g}
                                 {fun {s}
                                      {fun {r1}
                                           {fun {r2}
                                                {+ {get r1 b}
                                                   {seqn
                                                    {{s r1} {g r2}}
                                                    {+ {seqn
                                                        {{s r2} {g r1}}
                                                        {get r1 b}}
                                                       {get r2 b}}}}}}}}
                            {fun {r} {get r a}}}            ; g
                           {fun {r} {fun {v} {set r b v}}}} ; s
                          {struct {a 0} {b 2}}}             ; r1
                         {struct {a 3} {b 4}}}}
                 {{fun {r} {get r x}} {struct {x 1}}}}))
  (list 1 5)) #t)
(test (same-elements? (interp-expr
                       (parse `{with {t1 {spawn {seqn {receive} {receive}}}}
                                     {with {t2 {spawn {seqn {receive} {receive}}}}
                                           {with {t3 {spawn {seqn {receive} {receive}}}}
                                                 {seqn {deliver t1 1}
                                                       {seqn {deliver t1 2}
                                                             {seqn {deliver t2 3}
                                                                   {seqn {deliver t2 4}
                                                                         {seqn {deliver t3 5}
                                                                               {seqn {deliver t3 6}
                                                                                     0}}}}}}}}}))
                      (list 0 2 4 6)) #t)

(test (local
        [(define result (interp-expr
                         (parse `{with {t1 {spawn {seqn {receive} {receive}}}}
                                       {with {t2 {spawn {seqn {deliver t1 1} {receive}}}}
                                             {with {t3 {spawn {seqn {deliver t2 2} {receive}}}}
                                                   {seqn {deliver t1 3}
                                                         {seqn {deliver t3 4}
                                                               5}}}}})))]
        (or (same-elements? result (list 1 4 2 5))
            (same-elements? result (list 3 4 2 5)))) #t)
(test (local
        [(define result (interp-expr
                         (parse `{with {t1 {spawn {seqn {receive} {receive}}}}
                                       {with {t2 {spawn {seqn {deliver t1 1} {receive}}}}
                                             {with {t3 {spawn {seqn {deliver t2 2} {receive}}}}
                                                   {seqn {deliver t1 3}
                                                         5}}}})))]
        (or (same-elements? result (list 1 'blocked 2 5))
            (same-elements? result (list 3 'blocked 2 5)))) #t)
(test/exn (interp-expr
           (parse '{seqn {spawn {with {q {struct {y 1} {z 2}}} {get q x}}} 6}))
          "unknown field")

(test
 (same-elements?
  (interp-expr
   (parse `{with {z {spawn {- 15 {receive}}}}
                 {with {x {spawn {deliver z {receive}}}}
                       {seqn {deliver x 6}
                             1}}}))
  (list 1 6 9)) #t)

(test
 (same-elements?
  (interp-expr
   (parse `{with {z {spawn {- 15 {receive}}}}
                 {deliver z {receive}}}))
  (list 'blocked 'blocked)) #t)

(test
 (same-elements?
  (interp-expr
   (parse
    `(with
      (b (struct (x 1111)))
      (seqn ((seqn (set b x 0) (fun (x) x))
             (seqn (set b x 1) 0))
            (get b x)))))
  (list 1)) #t)

(test (same-elements?
       (interp-expr (parse `{seqn {receive} {receive}}))
       (list 'blocked))
      #t)

(test (same-elements?
       (interp-expr (parse `{with {t1 {spawn {+ 1 {+ 2 3}}}}
                                      {deliver t1 4}}))
       (list 6 4))
      #t)

(test (same-elements?
       (interp-expr (parse `{with {t1 {spawn {seqn {+ 1 2} {receive}}}}
                                  {seqn {deliver t1 0}
                                        {deliver t1 1}}}))
      '(0 1))
      #t)

