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
(print-only-errors)

; BNF grammar
;<RFAE> = <number>
;| {+ <RFAE> <RFAE>}
;| {- <RFAE> <RFAE>}
;| {fun {<id>} <RFAE>}
;| {<RFAE> <RFAE>}             ;; function application
;| <id>
;| {with {<id> <RFAE>} <RFAE>} ;; shorthand for fun & app
;| {struct {<id> <RFAE>} ...}  ;; all fields must be distinct
;| {get <RFAE> <id>}
;| {set <RFAE> <id> <RFAE>}
;| {seqn <RFAE> <RFAE>}

(define-type RFAE
  [num (n number?)]
  [add (lhs RFAE?) (rhs RFAE?)]
  [sub (lhs RFAE?) (rhs RFAE?)]
  [fun (param symbol?) (body RFAE?)]
  [app (fun-expr RFAE?) (arg-expr RFAE?)]
  [id (name symbol?)]
  [struct/rfae (records (listof pair?))]
  [get/rfae (struct-expr RFAE?) (name symbol?)]
  [set/rfae (struct-expr RFAE?) (name symbol?) (value-expr RFAE?)]
  [seqn/rfae (expr1 RFAE?) (expr2 RFAE?)])

;; struct record is like box -> pointer
(define-type RFAE-Value
  [numV (n number?)]
  [closureV (param symbol?)
            (body RFAE?)
            (ds DefrdSub?)]
  [structV (address integer?)])

; store all the data in the store as a list
(define-type Store
  [mtSto]
  [rdEnd(address integer?)
        (next Store?)]
  [aSto (address integer?)
        (name symbol?)
        (value RFAE-Value?)
        (rest Store?)])

(define-type DefrdSub
  [mtSub]
  [aSub (id symbol?)
        (val RFAE-Value?)
        (rest DefrdSub?)])

(define-type Value*Store
  [v*s (value RFAE-Value?)
       (store Store?)])

;; parser s-expr -> internal structure
(define/contract (parse s-expr)
  (-> any/c RFAE?)
  (match s-expr
    [(? number?) (num s-expr)]
    [(? symbol?) (id s-expr)]
    [`{+ ,lhs ,rhs} (add (parse lhs) (parse rhs))]
    [`{- ,lhs ,rhs} (sub (parse lhs) (parse rhs))]
    [`{with {,id ,e1} ,e2} (parse `{{fun {,id} ,e2} ,e1})]
    [`{fun {,(? symbol? param)} ,body} (fun param (parse body))]
    [`{struct ,(? cons? fields) ...}
     (struct/rfae (map (λ (p) (cons (first p) (parse (last p)))) fields))]
    [`{get ,e1 ,id} (get/rfae (parse e1) id)]
    [`{set ,e1 ,id ,e2} (set/rfae (parse e1) id (parse e2))]
    [`{seqn ,e1 ,e2} (seqn/rfae (parse e1) (parse e2))]
    [`{,fun-expr ,arg-expr} (app (parse fun-expr) (parse arg-expr))]
    [_ (error "bad syntax when parsing:\n" s-expr)]))


;; interpreter

;; because we have state now,
;; he interpreter need to return the state also

(define/contract (numV-op op)
  (-> (-> number? number? number?)
      (-> RFAE-Value? RFAE-Value? numV?))
  (λ (lhs rhs)
    (if (and (numV? lhs) (numV? rhs))
        (numV (op (numV-n lhs) (numV-n rhs)))
        (error 'add-or-sub "numeric operation expected number"))))
(define numV+ (numV-op +))
(define numV- (numV-op -))

;; abstract 
(define (interp-two expr1 expr2 ds st handle)
  (type-case Value*Store (interp expr1 ds st)
    [v*s (val1 st2)
         (type-case Value*Store (interp expr2 ds st2)
           [v*s (val2 st3)
                (handle val1 val2 st3)])]))

(define/contract (lookup-ds name ds)
  (-> symbol? DefrdSub? RFAE-Value?)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup-ds "free identifier:\n~a" name)]
    [aSub (id val rest) (if (symbol=? id name)
                            val
                            (lookup-ds name rest))]))

(define/contract (lookup-st-rd addr st)
  (-> integer? Store? Store?)
  (type-case Store st
    [mtSto () (error 'lookup-st-rd "unknown field")]
    [rdEnd (adr rest) (if (eq? addr adr)
                          st
                          (lookup-st-rd addr rest))]
    [aSto (adr named-id val rest) (if (eq? addr adr)
                                      st
                                      (lookup-st-rd addr rest))]))

(define/contract (lookup-st-rd-field name st)
  (-> symbol? Store? RFAE-Value?)
  (type-case Store st
    [mtSto () (error 'lookup-st-rd "unknown field")] ;can't reach here
    [rdEnd (addr rest) (error 'lookup-st-rd-field "unknown field:\n~a" name)]
    [aSto (addr named-id val rest)
          (if (symbol=? name named-id)
              val
              (lookup-st-rd-field name rest))]))

(define/contract (lookup-st addr a-field st)
  (-> integer? symbol? Store? RFAE-Value?)
  (lookup-st-rd-field a-field
                      (lookup-st-rd addr st)))

(define/contract (set-st-2 a-field new-val st)
  (-> symbol? RFAE-Value? Store? Store?)
  (type-case Store st
    [aSto (adr named-id val rest)
          (if (symbol=? a-field named-id)
              (aSto adr a-field new-val rest)
              (aSto adr named-id val (set-st-2 a-field new-val rest)))]
    [else (error 'set "unknown field")]))

(define/contract (set-st-1 rd-addr a-field new-val st)
  (-> integer? symbol? RFAE-Value? Store? Store?)
  (type-case Store st
    [mtSto () (error 'set "unknown field")]
    [rdEnd (adr rest)
           (if (eq? rd-addr adr)
               (error 'set "unknown field")
               (rdEnd adr (set-st-1 rd-addr a-field new-val rest)))]
    [aSto (adr named-id val rest)
          (if (eq? rd-addr adr)
              (set-st-2 a-field new-val st)
              (aSto adr named-id val (set-st-1 rd-addr a-field new-val rest)))]))
(define/contract (set-st rd-addr a-field new-val st)
  ;this function return a totally new ###Store###
  ;this addr and val must exits
  (-> integer? symbol? RFAE-Value? Store? Store?)
  (set-st-1 rd-addr a-field new-val st))

(define/contract (store-top st)
  (-> Store? integer?)
  (type-case Store st
    [mtSto () 0]
    [rdEnd (addr rest) addr]
    [aSto (addr n v rst) addr]))
;;
(define/contract (struct-rd records ds st)
  (-> (listof pair?) DefrdSub? Store? Value*Store?)
  (if (empty? records)
      (v*s (structV (store-top st)) st)
      (let ([a-pair (first records)]
            [rest-rds (rest records)])
        (let ([named-id (car a-pair)]
              [struct-expr (cdr a-pair)])
          (type-case Value*Store (interp struct-expr ds st)
            [v*s (val1 st2)
                 (let ([new-addr (malloc st2)])
                   (let ([st3 (aSto new-addr
                                    named-id
                                    val1
                                    st2)])
                     (struct-rd rest-rds ds st3)))])))))

;; always look at the top in st
(define/contract (malloc st)
  (-> Store? integer?)
  (type-case Store st
    [mtSto () 1]
    [rdEnd (addr rest) (add1 addr)]
    [aSto (addr name val rest) (add1 addr)]))
;; with store evaluate order matters
(define/contract (interp a-rfae ds st)
  (-> RFAE? DefrdSub? Store? Value*Store?)
  (type-case RFAE a-rfae
    [num (n) (v*s (numV n) st)]
    [add (l r) (interp-two l r ds st (λ (l r st)
                                       (v*s (numV+ l r) st)))]
    [sub (l r) (interp-two l r ds st (λ (l r st)
                                       (v*s (numV- l r) st)))]
    [id (name) (v*s (lookup-ds name ds) st)]
    [fun (param body) (v*s (closureV param body ds) st)]
    [app (fun-expr arg-expr)
         (type-case Value*Store (interp fun-expr ds st)
           [v*s (fun-val st2)
                (type-case Value*Store (interp arg-expr ds st2)
                  [v*s (arg-val st3)
                       (type-case RFAE-Value fun-val
                         [closureV (param body ds2)
                                   (interp body
                                           (aSub param arg-val ds2)
                                           st3)]
                         [else (error 'app
                                      "application expected procedure:\n~a"
                                      fun-expr)])])])]                      
    [struct/rfae (records) (struct-rd records
                                      ds
                                      (rdEnd (malloc st) st))]
    [get/rfae (struct-expr named-id)
              (type-case Value*Store (interp struct-expr ds st)
                [v*s (val1 st2) (type-case RFAE-Value val1
                                  [structV (addr) (v*s (lookup-st addr named-id st2)
                                                       st2)]
                                  [else (error 'get
                                               "record operation expected record:\n~a"
                                               struct-expr)])])]
    ;return old value
    [set/rfae (struct-expr named-id val-expr)
              (type-case Value*Store (interp struct-expr ds st)
                [v*s (val1 st2)
                     (type-case RFAE-Value val1
                       [structV (addr) (type-case Value*Store (interp val-expr ds st2)
                                         [v*s (val2 st3) (v*s (lookup-st addr named-id st3)
                                                              (set-st addr named-id val2 st3))])]
                       [else (error 'set
                                    "record operation expected record"
                                    struct-expr)])])]
    [seqn/rfae (expr1 expr2) (interp-two expr1 expr2 ds st (λ (v1 v2 st)
                                                             (v*s v2 st)))]))

(define/contract (interp-expr a-rfae)
  (-> RFAE? (or/c number? symbol?))
  (type-case Value*Store (interp a-rfae (mtSub) (mtSto))
    [v*s (a-val a-sto)
         (type-case RFAE-Value a-val
           [numV (n) n]
           [closureV (param body ds) 'procedure]
           [structV (addr) 'struct])]))


;; test case
(test/exn (interp-expr (parse '{struct {z {get {struct {z 0}} y}}}))
          "unknown field")

(test (interp-expr (parse '{{fun {r}
                                 {get r x}}
                            {struct {x 1}}}))
      1)

(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {set r x 5}
                                  {get r x}}}
                            {struct {x 1}}}))
      5)

(test (interp-expr (parse `{set {struct {x 42}} x 2}))
      42)

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
      5)

(test (interp-expr (parse '{with {s {struct {a 1} {b 2}}}
                                    {set s a {get s a}}}))
      1)
(test (interp-expr
       (parse `(with (r (struct (x 1) (y 2) (z 3))) (seqn (set r x 17) (get r x)))))
      17)
(test (interp-expr
       (parse `(with (r (struct (x 1) (y 2) (z 3))) (seqn (set r y 17) (get r y)))))
      17)
(test (interp-expr
       (parse '(with (x (struct (a 1) (b 2) (c 3))) (set x b (seqn (set x b 5) 7)))))
      5)
