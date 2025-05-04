#lang typed/racket
(require typed/rackunit)

; Assignment by Aryan Baldua and Sathvik Chikala
; This assignment is not yet completed

; Define ExprC lang
(define-type ExprC (U NumC IdC AppC IfLeC BinOpC))
(struct IdC ([s : Symbol]) #:transparent)                        
(struct AppC ([fun : Symbol] [args : (Listof ExprC)]) #:transparent)
(struct IfLeC ([test : ExprC] [th : ExprC] [el : ExprC]) #:transparent)
(struct BinOpC ([op : Symbol] [l : ExprC] [r : ExprC]) #:transparent)
(struct NumC ([n : Real]) #:transparent)
(struct FunDefC ([name : Symbol] [params : (Listof Symbol)] [body : ExprC]) #:transparent)


(define-type Value (U NumV BoolV StringV CloV PrimOpV))
(struct NumV ([n : Real]) #:transparent)
(struct BoolV ([b : Boolean]) #:transparent)
(struct StringV ([s : String]) #:transparent)
(struct CloV ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimOpV  ([name : Symbol] [impl : (-> (Listof Value) Value)]) #:transparent)


(define-type Binding (Pairof Symbol Value))
(define-type Env (Listof Binding))


(define (serialize [v : Value]) : String
  (match v
    [(NumV  n) (~v n)]                    
    [(BoolV b) (if b "true" "false")]   
    [(StringV s) (format "~v" s)]           
    [(CloV _ _ _) "#<procedure>"]
    [(PrimOpV _ _) "#<primop>"]))


;*********************ALL PRIM OPS***************************
(define (add-prim [args : (Listof Value)]) : Value
  (match args
    [(list (NumV a) (NumV b)) (NumV (+ a b))]
    [_ (error 'add-prim "QTUM: + expects two numbers")]))


(define (sub-prim [args : (Listof Value)]) : Value
  (match args
    [(list (NumV a) (NumV b)) (NumV (- a b))]
    [_ (error 'sub-prim "QTUM: - expects two numbers")]))


(define (mul-prim [args : (Listof Value)]) : Value
  (match args
    [(list (NumV a) (NumV b)) (NumV (* a b))]
    [_ (error 'mul-prim "QTUM: * expects two numbers")]))


(define (div-prim [args : (Listof Value)]) : Value
  (match args
    [(list (NumV _) (NumV 0))
     (error 'div-prim "QTUM: / division by zero")]
    [(list (NumV a) (NumV b)) (NumV (/ a b))]
    [_ (error 'div-prim "QTUM: / expects two numbers")]))


(define (leq-prim [args : (Listof Value)]) : Value
  (match args
    [(list (NumV a) (NumV b)) (BoolV (<= a b))]
    [_ (error 'leq-prim "QTUM: <= expects two numbers")]))


(define (equalQ-prim [args : (Listof Value)]) : Value
  (match args
    [(list (NumV a)    (NumV b))    (BoolV (= a b))]
    [(list (BoolV a)   (BoolV b))   (BoolV (eq? a b))]
    [(list (StringV a) (StringV b)) (BoolV (equal? a b))]
    [_ (BoolV #f)]))                       ; closures & primops ⇒ false


(define (strlen-prim [args : (Listof Value)]) : Value
  (match args
    [(list (StringV s)) (NumV (string-length s))]
    [_ (error 'strlen-prim "QTUM: strlen expects one string")]))

(define (substring-prim [args : (Listof Value)]) : Value
  (match args
    [(list (StringV s) (NumV st) (NumV sp))
     (cond
       [(and (integer? st) (integer? sp)
             (<= 0 st sp (string-length s)))
        (define ist (cast st Integer))
        (define isp (cast sp Integer))
        (StringV (substring s ist isp))]
       [else
        (error 'substring-prim "QTUM: substring index error")])]
    [_ (error 'substring-prim
              "QTUM: substring expects (string num num)")]))


(define (user-error-prim [args : (Listof Value)]) : Nothing
  (match args
    [(list v)
     (error 'user-error-prim
            (string-append "QTUM user-error: " (serialize v)))]
    [_ (error 'user-error-prim
              "QTUM: error expects exactly one argument")]))

;********************END PRIM OPS***************************

(: make-binding (-> Symbol Value Binding))
(define (make-binding [k : Symbol] [v : Value]): Binding
  (cons k v))

(define top-env
  (list (make-binding '+      (PrimOpV '+ add-prim))
        (make-binding '-      (PrimOpV '- sub-prim))
        (make-binding '*      (PrimOpV '* mul-prim))
        (make-binding '/      (PrimOpV '/ div-prim))
        (make-binding '<=     (PrimOpV '<= leq-prim))
        (make-binding 'equal? (PrimOpV 'equal? equalQ-prim))
        (make-binding 'strlen (PrimOpV 'strlen strlen-prim))
        (make-binding 'substring (PrimOpV 'substring substring-prim))
        (make-binding 'error  (PrimOpV 'error user-error-prim))
        (make-binding 'true   (BoolV #t))
        (make-binding 'false  (BoolV #f))))

; takes in user input and actually returns the final output
(define (top-interp [prog-sexps : (Listof Sexp)]) : String
  (serialize (interp-fns (parse-prog prog-sexps))))


; run main and get an actual value
(define (interp-fns [funs : (Listof FunDefC)]) : Value
  (define main-fn (lookup-fun funs 'main))
  (unless (empty? (FunDefC-params main-fn))
    (error 'interp-fns "QTUM: main must take zero parameters"))
  (interp (FunDefC-body main-fn) funs top-env))


; turns list into structured fun defs
(define (parse-prog [prog : (Listof Sexp)]) : (Listof FunDefC)
  (define funs (map parse-fundef prog))
  (define seen (cast (make-hash) (HashTable Symbol Boolean)))
  (for ([fd (in-list funs)])
    (define nm (FunDefC-name fd))
    (when (hash-ref seen nm #f)
      (error 'parse-prog "QTUM: duplicate function name ~a" nm))
    (hash-set! seen nm #t))
  (unless (hash-has-key? seen 'main)
    (error 'parse-prog "QTUM: program must contain a main function"))
  funs)


; helper to return validate a param
(define (parse-fundef [prog : Sexp]) : FunDefC
  (match prog
    [(list 'fun (? symbol? name) params ... body)
     (when (hash-has-key? binop-table name)
       (error 'parse-fundef
              "QTUM: function name ~a collides with binary operator" name))
     (define ps : (Listof Symbol)
       (map validate-param params))
     (define seen (cast (make-hash) (HashTable Symbol Boolean)))
     (for ([p (in-list ps)])
       (when (hash-ref seen p #f)
         (error 'parse-fundef
                "QTUM: duplicate parameter in definition of ~a" name))
       (hash-set! seen p #t))
     (FunDefC name ps (parse body))]
    [_ (error 'parse-fundef "QTUM: bad function syntax ~e" prog)]))

; func to validate params
(define (validate-param [p : Any]) : Symbol
  (cond
    [(symbol? p) (cast p Symbol)]
    [(null? p) (error 'parse-fundef "QTUM: empty list in parameter position")]
    [else (error 'parse-fundef "QTUM: parameter not symbol ~e" p)]))


; takes in an ExprC and then returns a real number after breaking it down
(define (interp [expr : ExprC] [fun_defs : (Listof FunDefC)] [env : Env]) : Value
  (match expr
    [(NumC n) (NumV n)]
    [(BinOpC op l r)
     (define proc (hash-ref binop-table op
                            (lambda () (error 'interp "QTUM: operator is incorrect ~a" op))))
     ;; You need to unwrap to Real, call proc, then wrap back
     (define lhs (interp l fun_defs env))
     (define rhs (interp r fun_defs env))
     (match* (lhs rhs)
       [((NumV n1) (NumV n2)) (NumV (proc n1 n2))]
       [(_ _) (error 'interp "QTUM: numeric op on non-numbers")])]
    [(IfLeC test then else)
     (define tv (interp test fun_defs env))
     (match tv
       [(NumV n) (if (<= n 0)
                     (interp then fun_defs env)
                     (interp else fun_defs env))]
       [_ (error 'interp "QTUM: ifleq0? test not a number")])]
    [(AppC fname arg-exprs)
     ;; find the function definition
     (define fd (lookup-fun fun_defs fname))
     (define params (FunDefC-params fd))
     (define body   (FunDefC-body fd))

      ;; arity check
     (when (not (= (length params) (length arg-exprs)))
       (error 'interp "QTUM: wrong number of args"))

     ;; evaluate actual arguments in the *current* environment
     (define arg-vals
       (map (lambda ([e : ExprC]) (interp e fun_defs env)) arg-exprs))
     
     ;; build new bindings and extend the environment *safely*
     (define new-bindings : (Listof Binding)
       (map make-binding params arg-vals))

     (define extended-env : Env
       (foldr (λ ([b : Binding] [acc : Env]) : Env (cons b acc))
              env
              new-bindings))

     (interp body fun_defs extended-env)]
    
     ;; build a fresh environment that extends the current one
    [(IdC s) (lookup-env env s)]))

 ; lookup-fun finds func and substitues
(define (lookup-fun [funs : (Listof FunDefC)] [fun-name : Symbol]) : FunDefC
  (match funs
    ['() (error 'lookup-fun "QTUM: undefined function ~a" fun-name)]
    [(cons fd rest) (if (eq? (FunDefC-name fd) fun-name) fd (lookup-fun rest fun-name))]))

; lookup var in the curr environment
(define (lookup-env [env : Env] [x : Symbol]) : Value
  (match env
    ['() (error 'lookup-env "QTUM: unbound identifier ~a" x)]
    [(cons (cons y v) rest)
     (if (eq? x y) v (lookup-env rest x))]))

; this is the lab 3 parse function
; parser for ArithC, mapping Sexp to ExprC
(define (parse [prog : Sexp]) : ExprC
  (match prog
    [(? real? n) (NumC n)]
    [(list 'ifleq0? t th el)
     (IfLeC (parse t) (parse th) (parse el))]
    [(list (? symbol? sym) args ...)
     (cond
       [(and (hash-has-key? binop-table sym) (= (length args) 2))
        (BinOpC sym (parse (first args)) (parse (second args)))]
       [else
        (AppC sym (map parse args))])]
    [(? symbol? s) (IdC s)]
    [other (error 'parse "QTUM: incorrect syntax, got ~e" other)]))


; binop table lookup for operators
(define binop-table : (Immutable-HashTable Symbol (Real Real -> Real))
  (make-immutable-hash
   (list (cons '+ +) (cons '- -) (cons '* *) (cons '/ /))))


; just extra functions for help with test
; adding for testing purposes
(define fd-add
  (FunDefC 'add '(x y) (BinOpC '+ (IdC 'x) (IdC 'y))))

(define fd-inc
  (FunDefC 'inc '(n) (BinOpC '+ (IdC 'n) (NumC 1))))

; acting as main just for testing purposes
(define fd-main-0
  (FunDefC 'main '() (NumC 0)))

; helping with substitution
(define expr-z (IfLeC (IdC 'z)
         (BinOpC '+ (IdC 'z) (NumC 1))
         (BinOpC '- (IdC 'z) (NumC 1))))



;; ------------------------------------------------------------------
;;  PARSING  — unchanged
;; ------------------------------------------------------------------
(check-equal? (parse 3.5)          (NumC 3.5))
(check-equal? (parse 'v)           (IdC 'v))
(check-equal? (parse '{+ 1 2})     (BinOpC '+ (NumC 1) (NumC 2)))
(check-exn     #px"QTUM" (λ () (parse '((1 2) 3))))

;; ------------------------------------------------------------------
;;  INTERPRETER  (unit-level) — now run with top-env + expect Value
;; ------------------------------------------------------------------
;; primitive +, * via BinOpC
(check-equal? (interp (parse '{+ 1 2})
                      '()                   ; no user fun-defs
                      top-env)              ; <-- prim-op env
              (NumV 3))

(check-equal? (interp (parse '{* 1 2}) '() top-env)
              (NumV 2))

;; direct BinOpC syntax node
(check-equal? (interp (BinOpC '- (NumC 7) (NumC 2))
                      '()
                      top-env)
              (NumV 5))

;; ifleq0?
(check-equal? (interp (IfLeC (NumC 1) (NumC 9) (NumC 8))
                      '()
                      top-env)
              (NumV 8))

;; call to user-defined inc (needs both fun-defs *and* prim-op env)
(check-equal? (interp (AppC 'inc (list (NumC 10)))
                      (list fd-inc fd-main-0)
                      top-env)
              (NumV 11))

(check-exn #px"QTUM"
  (λ () (interp (AppC 'inc (list (NumC 1) (NumC 2)))
                (list fd-inc fd-main-0)
                top-env)))

;; ------------------------------------------------------------------
;;  HIGH-LEVEL DRIVER TESTS
;; ------------------------------------------------------------------
;; interp-fns now returns a Value
(check-equal? (interp-fns
               (parse-prog
                '{{fun fact n {ifleq0? n 1 {* n {fact {- n 1}}}}}
                  {fun main     {fact 5}}}))
              (NumV 120))

;; top-interp gives back a *string* (serialize applied)
(check-equal? (top-interp
               '{{fun add   a b {+ a b}}
                 {fun triple t {* 3 t}}
                 {fun main      {add {triple 3} 4}}})
              "13")

;; ------------------------------------------------------------------
;;  FUNCTION LOOK-UP (still unchanged)
;; ------------------------------------------------------------------
(check-equal? (lookup-fun (list fd-add fd-main-0) 'add) fd-add)
(check-exn     #px"QTUM"
  (λ () (lookup-fun (list fd-add) 'absent)))
