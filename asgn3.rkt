#lang typed/racket
(require typed/rackunit)

; Assignment by Aryan Baldua and Sathvik Chikala
; The assignment is not yet complete

; NOTES ABOUT OVERALL ASSIGNMENT -------------------
; our personal errors should have QTUM to show that we are giving error not the program
; structure of project - data definitions, top-down function approaches, test cases


; Define the Arith language
;(struct NumC ([n : Real]) #:transparent)
;(struct PlusC ([left : ArithC] [right : ArithC]) #:transparent)
;(struct MultC ([left : ArithC] [right : ArithC]) #:transparent)

;(define-type ArithC (U NumC SquarC))
;(struct NumC ([n : Real])  #:transparent)
;(struct PlusC ([l : ExprC] [r : ExprC]) #:transparent)
;(struct MultC ([l : ExprC] [r : ExprC]) #:transparent)
;(struct SquarC ([n : ArithC]) #:transparent)

(define-type ExprC (U NumC IdC AppC IfLeC BinOpC))
(struct IdC ([s : Symbol]) #:transparent)                            ; variable
(struct AppC ([fun : Symbol] [args : (Listof ExprC)]) #:transparent) ; function call
(struct IfLeC ([test : ExprC] [th : ExprC] [el : ExprC]) #:transparent)
(struct BinOpC ([op : Symbol] [l : ExprC] [r : ExprC]) #:transparent)
(struct NumC ([n : Real]) #:transparent)

(struct FunDefC ([name : Symbol] [params : (Listof Symbol)] [body : ExprC]) #:transparent)


; binop table lookup for operators
(define binop-table : (Immutable-HashTable Symbol (Real Real -> Real))
  (make-immutable-hash
    (list (cons '+ +)
          (cons '- -)
          (cons '* *)
          (cons '/ /))))


; this is the lab 3 parse function
; parser for ArithC, mapping Sexp to ExprC
(define (parse [prog : Sexp]) : ExprC
  (match prog
    ;; numeric literal --------------------------------------------------------
    [(? real? n) (NumC n)]

    ;; ifleq0? -----------------------------------------------------------------
    [(list 'ifleq0? t th el)
     (IfLeC (parse t) (parse th) (parse el))]

    ;; any non-empty list whose first element is a symbol ----------------------
    [(list (? symbol? sym) args ...)
     (cond
       ;; binary operator: symbol is in table **and** exactly two operands
       [(and (hash-has-key? binop-table sym) (= (length args) 2))
        (BinOpC sym (parse (first args)) (parse (second args)))]
       ;; otherwise treat the list as a function application
       [else
        (AppC sym (map parse args))])]

    ;; bare identifier ---------------------------------------------------------
    [(? symbol? s) (IdC s)]

    ;; anything else is malformed ---------------------------------------------
    [other (error 'parse "QTUM: expected valid syntax, got ~e" other)]))


(check-equal? (parse '{f 1 2}) (AppC 'f (list (NumC 1) (NumC 2))))
(check-equal? (parse '{f}) (AppC 'f '()))


; replaces every symbol in an expression with num value
(define (subst [e : ExprC] [var : Symbol] [val : Real]) : ExprC
  (match e
    [(NumC _)               e]
    [(IdC s)                (if (eq? s var) (NumC val) e)]
    [(BinOpC op l r)        (BinOpC op (subst l var val) (subst r var val))]
    [(IfLeC tst th el)      (IfLeC (subst tst var val)
                                   (subst th  var val)
                                   (subst el  var val))]
    [(AppC f args)          (AppC f (map (λ ([a : ExprC]) (subst a var val))
                                         args))]))


; Interpreter for ArithC
(define (interp [expr : ExprC] [fun_defs : (Listof FunDefC)]) : Real
  (match expr
    [(NumC n) n]
    ; new
    [(BinOpC op l r)
     (define proc
       (hash-ref binop-table op
                 (lambda () (error 'interp "QTUM: operator is incorrect ~a" op))))
     (proc (interp l fun_defs) (interp r fun_defs))]
    ;[(SquarC n)  (* (interp n fun_defs) (interp n fun_defs))]
    [(IfLeC test then else)
     (if (<= (interp test fun_defs) 0)
         (interp then fun_defs)
         (interp else fun_defs))]
    ; handles a function
    [(AppC fname arg-exprs)
     (define fd (lookup-fun fun_defs fname))
     (define params (FunDefC-params fd))
     (define body   (FunDefC-body   fd))
     (when (not (= (length params) (length arg-exprs)))
       (error 'interp "QTUM: wrong number of args"))
     ; calls interp on each argument and stores result in  arg-vals
     (define arg-vals
       (map (λ ([e : ExprC]) (interp e fun_defs)) arg-exprs))
     ; build a well-typed list of (Symbol . Real) pairs
     (define subst-list
       (map (λ ([p : Symbol] [v : Real]) : (Pairof Symbol Real)
              (cons p v))
            params
            arg-vals))
     ; fold with that precise pair type
     (define substituted-body
       (foldl (λ ([pr : (Pairof Symbol Real)] [b : ExprC])
                (subst b (car pr) (cdr pr)))
              body
              subst-list))
     ; evaluates new body -- Ex: (PlusC (NumC 2) (NumC 3)) -> 5
     (interp substituted-body fun_defs)]

    [(IdC s) (error 'interp "QTUM: free identifier ~a" s)]
    ;; AppC added later
    ))

(check-equal? (interp (parse '{+ 1 2}) '()) 3)
(check-equal? (interp (parse '{* 1 2}) '()) 2)
(check-equal? (parse 'x) (IdC 'x))


; lookup-fun will find the function and substitute appropriately
(define (lookup-fun [funs : (Listof FunDefC)] [fun-name : Symbol]) : FunDefC
  (match funs
    ['() (error 'lookup-fun "QTUM: undefined function ~a" fun-name)]
    [(cons fd rest)
     (if (eq? (FunDefC-name fd) fun-name)
         fd
         (lookup-fun rest fun-name))]))


; converts raw function def into structured definition
(define (parse-fundef [prog : Sexp]) : FunDefC
  (match prog
    ; structure being looked for - {fun  name  param ...  {body}}
    [(list 'fun (? symbol? name) params ... body)

     ; ensures parameters are valid symbol
     (when (hash-has-key? binop-table name)
       (error 'parse-fundef
              "QTUM: function name ~a collides with binary operator" name))

     ;; convert raw params → (Listof Symbol)  (and keep 0-ary funs legal)
     (define ps
       (for/list : (Listof Symbol) ([p (in-list params)])
         (cond [(symbol? p) (cast p Symbol)]
               [(null? p)   (error 'parse-fundef
                                   "QTUM: stray empty list in parameter position")]
               [else        (error 'parse-fundef
                                   "QTUM: parameter not symbol ~e" p)])))
     
     ; ensure no duplicates with hash
     (define seen (cast (make-hash) (HashTable Symbol Boolean)))
     (for ([p (in-list ps)])
       (when (hash-ref seen p #f)
         (error 'parse-fundef
                "QTUM: duplicate parameter in definition of ~a" name))
       (hash-set! seen p #t))

     ; build FunDefC by turning body into bunch of ExprC
     (FunDefC name ps (parse body))]

    ; function format is incorrect...might need more checks?
    [_ (error 'parse-fundef "QTUM: bad function syntax ~e" prog)]))


; turns list of "fun" blocks into structured FunDefC
(define (parse-prog [prog : (Listof Sexp)]) : (Listof FunDefC)
  (define funs (map parse-fundef prog))
  ; detect duplicate names
  (define seen (cast (make-hash) (HashTable Symbol Boolean)))
  (for ([fd (in-list funs)])
    (define nm (FunDefC-name fd))
    (when (hash-ref seen nm #f)
      (error 'parse-prog "QTUM: duplicate function name ~a" nm))
    (hash-set! seen nm #t))
  ; ensure main exists
  (unless (hash-has-key? seen 'main)
    (error 'parse-prog "QTUM: program must contain a main function"))
  funs)


; run main and get an actual value
(define (interp-fns [funs : (Listof FunDefC)]) : Real
  (define main-fn (lookup-fun funs 'main))
  (unless (empty? (FunDefC-params main-fn))
    (error 'interp-fns "QTUM: main must take zero parameters"))
  (interp (FunDefC-body main-fn) funs))


; top-interp takes in Sexp, calls parser and interp
(define (top-interp [prog-sexps : (Listof Sexp)]): Real
  (interp-fns (parse-prog prog-sexps)))


;(check-equal? (top-interp '{{fun main {{+ 3 7}}}}) 10)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helper fundefs reused in several tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define fd-add
  (FunDefC 'add '(x y) (BinOpC '+ (IdC 'x) (IdC 'y))))

(define fd-inc
  (FunDefC 'inc '(n) (BinOpC '+ (IdC 'n) (NumC 1))))

(define fd-main-0
  (FunDefC 'main '() (NumC 0)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1  ──  PARSE   (all variants + malformed)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(check-equal? (parse 3.5)                (NumC 3.5))
(check-equal? (parse 'v)                 (IdC 'v))
(check-equal? (parse '{+ 1 2})           (BinOpC '+ (NumC 1) (NumC 2)))
(check-equal? (parse '{ifleq0? -2 4 5})  (IfLeC (NumC -2) (NumC 4) (NumC 5)))
(check-equal? (parse '{foo 9})           (AppC 'foo (list (NumC 9))))
(check-equal? (parse '{bar})             (AppC 'bar '()))
;; malformed: operator but wrong arity
;(check-exn #px"QTUM" (λ () (parse '{* 1})))
;; malformed: list whose head is not a symbol
(check-exn #px"QTUM" (λ () (parse '((1 2) 3))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2  ──  SUBST   (positive & negative cases)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define expr-z
  (IfLeC (IdC 'z)
         (BinOpC '+ (IdC 'z) (NumC 1))
         (BinOpC '- (IdC 'z) (NumC 1))))
(check-equal?
 (subst expr-z 'z 10)
 (IfLeC (NumC 10) (BinOpC '+ (NumC 10) (NumC 1)) (BinOpC '- (NumC 10) (NumC 1))))
(check-equal? (subst (IdC 'a) 'b 9) (IdC 'a)) ; no change when names differ
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3  ──  LOOKUP-FUN   (hit & miss)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(check-equal? (lookup-fun (list fd-add fd-main-0) 'add) fd-add)
(check-exn #px"QTUM" (λ () (lookup-fun (list fd-add) 'absent)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4  ──  PARSE-FUNDEF / PARSE-PROG   (good and bad)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(check-equal?
 (parse-fundef '{fun square x {* x x}})
 (FunDefC 'square '(x) (BinOpC '* (IdC 'x) (IdC 'x))))
;; duplicate parameter
(check-exn #px"QTUM" (λ () (parse-fundef '{fun bad p p {+ p p}})))
;; name clashes with operator
(check-exn #px"QTUM" (λ () (parse-fundef '{fun + a a})))
;; well-formed program (unique names, has main)
(define prog-ok
  (parse-prog
   '{{fun double n {+ n n}}
     {fun main     {double 5}}}))
(check-equal? (map FunDefC-name prog-ok) '(double main))
;; missing main
(check-exn #px"QTUM" (λ () (parse-prog '{{fun f x x}})))
;; duplicate function names
(check-exn #px"QTUM" (λ () (parse-prog '{{fun f x x} {fun f y y}})))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5  ──  INTERP   (expressions, calls, errors)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(check-equal? (interp (BinOpC '- (NumC 7) (NumC 2)) '()) 5)
(check-equal?
 (interp (IfLeC (NumC 1) (NumC 9) (NumC 8)) '()) 8)
(check-equal?
 (interp (AppC 'inc (list (NumC 10))) (list fd-inc fd-main-0)) 11)
;; arity error
(check-exn #px"QTUM"
           (λ () (interp (AppC 'inc (list (NumC 1) (NumC 2)))
                         (list fd-inc fd-main-0))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 6  ──  INTERP-FNS and TOP-INTERP  (whole programs)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(check-equal?
 (interp-fns
  (parse-prog
   '{{fun fact n
          {ifleq0? n
                   1
                   {* n {fact {- n 1}}}}}
     {fun main {fact 5}}}))
 120)
;; top-level with helpers
(check-equal?
 (top-interp
  '{{fun add a b {+ a b}}
    {fun triple t {* 3 t}}
    {fun main     {add {triple 3} 4}}})
 13)
;; main with parameters – should fail
(check-exn #px"QTUM"
           (λ () (top-interp '{{fun main x {+ x 1}}})))

;; unknown binary operator  →  interp must complain
(check-exn #px"QTUM"
  (λ () (interp (BinOpC '^^ (NumC 1) (NumC 2)) '())))

;; parameter that is NOT a symbol  →  parse-fundef must complain
(check-exn #px"QTUM"
  (λ () (parse-fundef '{fun bad 42 {+ 1 1}})))

;; stray empty list in parameter position  →  parse-fundef must complain
(check-exn #px"QTUM"
  (λ () (parse-fundef '{fun bad () {+ 1 1}})))

;; interp – free identifier
(check-exn #px"QTUM"
  (λ () (interp (IdC 'ghost) '())))

;; parse-fundef – totally malformed syntax
(check-exn #px"QTUM"
  (λ () (parse-fundef '{fun})))