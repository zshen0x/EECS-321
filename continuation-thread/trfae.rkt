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
  [record (listof pair?)]
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
  [recV (name symbol?)
        (value TRFAE-Value?)
        (next (or/c integer? void?))] ;; records

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
  [active (tid integer?) (go (-> Store? Thds*Store?))]
  [blocked (tid integer?) (continue (-> TRFAE-Value? Store? Thds*Store?))]
  [done (v TRFAE-Value?)])

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
    [mtSub () (error "free identifier: ~a" named-id)]
    [aSub (name loc rst) (cond
                           [(equal? name named-id) loc]
                           [else (lookup-defrdsub named-id rst)])]))

; loc -> value
(define/contract (lookup-store loc st)
  (-> exact-nonnegative-integer? Store? (or/c TRFAE-Value? (listof TRFAE-Value?)))
  (type-case Store st
    [mtSto () (error "unknow store location: ~a" loc)]
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
    [num (n) (thds*store (list (active addr (λ (sto)
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
    [app (fun-expr arg-expr)
         (thds*store (list (active addr
                                   (λ (sto)
                                     (execute-thd arg-expr
                                                  ds
                                                  addr
                                                  sto
                                                  (λ (arg-v sto1)
                                                    (execute-thd fun-expr
                                                                 ds
                                                                 addr
                                                                 sto1
                                                                 (λ (clo-v sto2)
                                                                   (type-case TRFAE-Value clo-v
                                                                     [closureV (param body clo-ds)
                                                                               (letrec ([top-loc (add1 (top-store sto2))]
                                                                                        [sto3 (alloc-store top-loc arg-v sto2)])
                                                                                 (execute-thd body
                                                                                              (aSub param
                                                                                                    top-loc
                                                                                                    clo-ds)
                                                                                              addr
                                                                                              sto3
                                                                                              k))]
                                                                     [else (error "application expected procedure")]))))))))
                     st)]
    
    [id (name) (thds*store (list (active addr (λ (sto) (k (lookup-store (lookup-defrdsub name ds) sto) sto)))) st)]
    [record (kv-lst) (error "to be complete")]
    [record-get (rcd name) (error "to be complete")]
    [record-set (rcd name val) (error "to be complete")]
    [spawn (td) (letrec ([new-loc (add1 (top-store st))]
                         [thd-val (thdV new-loc)]
                         [st1 (alloc-store new-loc thd-val st)])
                  (thds*store (list (active new-loc
                                            (λ (st2)
                                              (execute-thd td
                                                           ds
                                                           new-loc
                                                           st2
                                                           (λ (v3 st3)
                                                             (let ([st4 (set-store new-loc (list v3) st3)])
                                                               (thds*store (list (done v3)) st4))))))
                                    (active addr (λ (a-st)
                                                   (k thd-val a-st))))
                              st1))]
    [deliver (td val) (error "to be complete")]
    [receive () (thds*store
                 (listof (blocked addr (λ (v1 st1)
                                         (k v1 st1)))))]
    [seqn (e1 e2) (thds*store (list (active addr
                                            (λ (sto)
                                              (execute-thd e1
                                                           ds
                                                           addr
                                                           st
                                                           (λ (v1 st1)
                                                             (execute-thd e2 ds addr st1 k))))))
                              st)]))

; init thread and scheduler
; run - update - cycle
(define (threads-scheduler t*s)
  (type-case Thds*Store t*s
    [thds*store (thds st)
                (cond
                  [((listof done?) thds) thds]
                  [else (let ([active-thds (filter (λ (thd) (active? thd)) thds)])
                          (cond
                            [(not (empty? active-thds)) (letrec ([a-thd (list-ref active-thds
                                                                                  (random (length active-thds)))]
                                                                 [rst-thds (remove a-thd thds)]
                                                                 [t1*s1 ((active-go a-thd) st)])
                                                          (type-case Thds*Store t1*s1
                                                            [thds*store (thds1 st1) (let ([t2*s1 (thds*store (append rst-thds
                                                                                                                     thds1)
                                                                                                             st1)])
                                                                                      (threads-scheduler t2*s1))]))]
                            [else (threads-scheduler t*s)]))])])) ;; when all thread are blocked forever loop

(define (interp-expr a-trfae)
  ;; initialize
  (let ([thds-pool (execute-thd a-trfae
                                (mtSub)
                                0
                                (aSto 0 (list (thdV 0)) (mtSto))
                                (λ (v st)
                                  (let ([st1 (set-store 0 (list v) st)])
                                    (thds*store (list (done v)) st1))))])
    (map (λ (done-thd)
           (type-case Thd done-thd
             [done (v) (type-case TRFAE-Value v
                         [numV (n) n]
                         [closureV (p b d) 'procedure]
                         [recV (a b c) 'struct]
                         [thdV (addr) addr])]
             [blocked (tid continue) 'blocked]
             [else (error 'bug "never reach here!")]))
         (threads-scheduler thds-pool))))

;; test cases
;(print-only-errors)

(define (same-elements? l1 l2)
  (define (sub-mutiset? l1 l2)
    (cond
      [(null? l1) #t]
      [else (and (member (car l1) l2)
                 (subset? (cdr l1) (remove (car l1) l2)))]))
  (and (sub-mutiset? l1 l2) (sub-mutiset? l2 l1)))

(test (same-elements?
       (interp-expr (parse `{seqn {spawn 1} 2}))
       (list 1 2))
      #t)
(test (same-elements?
           (interp-expr (parse `{with {x 1} {seqn {spawn x} 2}}))
           (list 1 2))
      #t)


;; exceptions raised in a thread kill the entire program
(test/exn (interp-expr (parse '{spawn {0 0}}))
          "application expected procedure")


(test/exn (interp-expr
           (parse '{seqn {spawn {0 0}}
                         {{fun {x} {x x}} {fun {x} {x x}}}}))
          "application expected procedure")

(interp-expr (parse '{seqn {spawn {+ 1 {- 10 1}}}
                           {{fun {x} {+ x 1}} 1}}))

;; these two tests make sure that your implementation
;; doesn't commit to a particular thread forever
(test/exn (interp-expr
           (parse '{seqn {spawn {{fun {x} {x x}} {fun {x} {x x}}}}
                         {0 0}}))
          "application expected procedure")



;(test/exn (interp-expr (parse '{struct {z {get {struct {z 0}} y}}}))
;            "unknown field")
;
;  (test (interp-expr (parse '{{fun {r}
;                                {get r x}}
;                              {struct {x 1}}}))
;        1)
;
;  (test (interp-expr (parse '{{fun {r}
;                                {seqn
;                                  {set r x 5}
;                                  {get r x}}}
;                              {struct {x 1}}}))
;        5)
;
;  (test (interp-expr (parse `{set {struct {x 42}} x 2}))
;        42)
;
;  (test (interp-expr (parse '{{{{{fun {g}
;                                   {fun {s}
;                                     {fun {r1}
;                                       {fun {r2}
;                                         {+ {get r1 b}
;                                            {seqn
;                                              {{s r1} {g r2}}
;                                              {+ {seqn
;                                                   {{s r2} {g r1}}
;                                                   {get r1 b}}
;                                                 {get r2 b}}}}}}}}
;                                 {fun {r} {get r a}}}            ; g
;                                {fun {r} {fun {v} {set r b v}}}} ; s
;                               {struct {a 0} {b 2}}}             ; r1
;                              {struct {a 3} {b 4}}}))            ; r2
;        5)
