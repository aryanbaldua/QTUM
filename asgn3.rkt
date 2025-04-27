#lang typed/racket
(require typed/rackunit)

; Assignment by Aryan Baldua and Sathvik Chikala
; The assignment is not yet complete

; NOTES ABOUT OVERALL ASSIGNMENT
; our personal errors should have QTUM to show that we are giving error not the program
; structure of project - data definitions, top-down function approaches, test cases


; Define the Arith language
;(struct NumC ([n : Real]) #:transparent)
;(struct PlusC ([left : ArithC] [right : ArithC]) #:transparent)
;(struct MultC ([left : ArithC] [right : ArithC]) #:transparent)

(define-type ArithC (U NumC PlusC MultC SquarC))
(struct NumC ([n : Real])  #:transparent)
(struct PlusC ([l : ExprC] [r : ExprC]) #:transparent)
(struct MultC ([l : ExprC] [r : ExprC]) #:transparent)
(struct SquarC ([n : ArithC]) #:transparent)

(define-type ExprC (U NumC IdC AppC PlusC MultC IfLeC))
(struct IdC ([s : Symbol]) #:transparent)                            ; variable
(struct AppC ([fun : Symbol] [args : (Listof ExprC)]) #:transparent) ; function call
(struct IfLeC ([test : ExprC] [th : ExprC] [el : ExprC]) #:transparent)

(struct FunDefC ([name : Symbol] [params : (Listof Symbol)] [body : ExprC]) #:transparent)

; this is the lab 3 parse function
; parser for ArithC, mapping Sexp to ExprC
(define (parse [prog : Sexp]) : ExprC
  (match prog
    [(? real? n) (NumC n)]
    [(? symbol? s) (IdC s)]
    [(list '+ l r) (PlusC  (parse l) (parse r))]
    [(list '* l r) (MultC  (parse l) (parse r))]
    [(list 'ifleq0? t e1 e2)
     (IfLeC (parse t) (parse e1) (parse e2))]
    [(list (? symbol? f) args ...)          ; function call
     (AppC f (map parse args))]
    [wrong (error 'parse "QTUM: expected valid syntax, got ~e" wrong)]))


(check-equal? (parse '{f 1 2}) (AppC 'f (list (NumC 1) (NumC 2))))
(check-equal? (parse '{f}) (AppC 'f '()))


; replaces every symbol in an expression with num value
(define (subst [e : ExprC] [var : Symbol] [val : Real]) : ExprC
  (match e
    [(NumC n) e]
    [(IdC s)  (if (eq? s var) (NumC val) e)]
    [(PlusC l r) (PlusC (subst l var val) (subst r var val))]
    [(MultC l r) (MultC (subst l var val) (subst r var val))]
    [(AppC f args) (AppC f (map (λ ([a : ExprC]) (subst a var val)) args))]
    [_ (error 'subst "QTUM: unhandled case")]))

; Interpreter for ArithC
(define (interp [expr : ExprC] [fun_defs : (Listof FunDefC)]) : Real
  (match expr
    [(NumC n) n]
    [(PlusC l r) (+ (interp l fun_defs) (interp r fun_defs))]
    [(MultC l r) (* (interp l fun_defs) (interp r fun_defs))]
    [(SquarC n)  (* (interp n fun_defs) (interp n fun_defs))]
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
     ; creates pairs of each (parameter and value)
     (define subst-list
       (map (λ ([p : Symbol] [v : Real])
              (cons p v))
            params
            arg-vals))
     ; replaces the parameter with actual value in body
     (define substituted-body
       (foldl (λ ([pair : (Pairof Symbol Real)] [b : ExprC])
                (subst b (car pair) (cdr pair)))
              body
              subst-list))
     ; evaluates new body -- Ex: (PlusC (NumC 2) (NumC 3)) -> 5
     (interp substituted-body fun_defs)]

    [(IdC s) (error 'interp "QTUM: free identifier ~a" s)]
    ;; AppC added later
    ))

(check-equal? (interp (parse '{+ 1 2}) '()) 3)
(check-equal? (parse 'x) (IdC 'x))

; lookup-fun will find the function and substitute appropriately
(: lookup-fun ((Listof FunDefC) Symbol -> FunDefC))
(define (lookup-fun funs the-name)
  (match funs
    ['() (error 'lookup-fun "QTUM: undefined function ~a" the-name)]
    [(cons fd rest)
     (if (eq? (FunDefC-name fd) the-name)
         fd
         (lookup-fun rest the-name))]))


; 
(define (parse-fundef [prog : Sexp]) : FunDefC
  (match prog
    ;; {fun  name  param ...  {body}}
    [(list 'fun (? symbol? name) params ... body)

     ;; turn raw params into a (Listof Symbol)
     (define ps
       (for/list : (Listof Symbol) ([p (in-list params)])
         (if (symbol? p)
             (cast p Symbol)
             (error 'parse-fundef "QTUM: parameter not symbol ~e" p))))

     ;; duplicate-check with a typed hash
     (define seen (cast (make-hash) (HashTable Symbol Boolean)))
     (for ([p (in-list ps)])
       (when (hash-ref seen p #f)
         (error 'parse-fundef
                "QTUM: duplicate parameter in definition of ~a" name))
       (hash-set! seen p #t))

     (FunDefC name ps (parse body))]

    [_ (error 'parse-fundef "QTUM: bad function syntax ~e" prog)]))

;
(define (parse-prog [prog : (Listof Sexp)]) : (Listof FunDefC)
  (map parse-fundef prog))

;
(define (interp-fns [funs : (Listof FunDefC)]) : Real
  (define main-fn (lookup-fun funs 'main))
  (unless (empty? (FunDefC-params main-fn))
    (error 'interp-fns "QTUM: main must take zero parameters"))
  (interp (FunDefC-body main-fn) funs))

; top-interp takes in Sexp, calls parser and interp
(define (top-interp [prog-sexps : (Listof Sexp)]): Real
  (interp-fns (parse-prog prog-sexps)))


