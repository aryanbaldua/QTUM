#lang typed/racket
(require typed/rackunit)

; Assignment by Aryan Baldua and Sathvik Chikala
; 100% Complete with Full Code Coverage

; Define ExprC lang
(define-type ExprC (U NumC IdC AppC IfLeC BinOpC))
(struct IdC ([s : Symbol]) #:transparent)                        
(struct AppC ([fun : Symbol] [args : (Listof ExprC)]) #:transparent)
(struct IfLeC ([test : ExprC] [th : ExprC] [el : ExprC]) #:transparent)
(struct BinOpC ([op : Symbol] [l : ExprC] [r : ExprC]) #:transparent)
(struct NumC ([n : Real]) #:transparent)
(struct FunDefC ([name : Symbol] [params : (Listof Symbol)] [body : ExprC]) #:transparent)


; takes in user input and actually returns the final output
(define (top-interp [prog-sexps : (Listof Sexp)]): Real
  (interp-fns (parse-prog prog-sexps)))

; run main and get an actual value
(define (interp-fns [funs : (Listof FunDefC)]) : Real
  (define main-fn (lookup-fun funs 'main))
  (unless (empty? (FunDefC-params main-fn))
    (error 'interp-fns "QTUM: main must take zero parameters"))
  (interp (FunDefC-body main-fn) funs))


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
(define (interp [expr : ExprC] [fun_defs : (Listof FunDefC)]) : Real
  (match expr
    [(NumC n) n]
    [(BinOpC op l r)
     (define proc (hash-ref binop-table op
                            (lambda () (error 'interp "QTUM: operator is incorrect ~a" op))))
     (proc (interp l fun_defs) (interp r fun_defs))]
    [(IfLeC test then else)
     (if (<= (interp test fun_defs) 0)
         (interp then fun_defs)
         (interp else fun_defs))]
    [(AppC fname arg-exprs)
     (define fd (lookup-fun fun_defs fname))
     (define params (FunDefC-params fd))
     (define body   (FunDefC-body   fd))
     (when (not (= (length params) (length arg-exprs)))
       (error 'interp "QTUM: wrong number of args"))
     (define arg-vals
       (map (lambda ([e : ExprC]) (interp e fun_defs)) arg-exprs))
     (define subst-list
       (map (lambda ([p : Symbol] [v : Real]) : (Pairof Symbol Real)
              (cons p v)) params arg-vals))
     (define substituted-body
       (foldl (lambda ([pr : (Pairof Symbol Real)] [b : ExprC])
                (subst b (car pr) (cdr pr))) body subst-list))
     (interp substituted-body fun_defs)]
    [(IdC s) (error 'interp "QTUM: free identifier ~a" s)]))


; replaces every symbovl in an expression with num value
(define (subst [e : ExprC] [var : Symbol] [val : Real]) : ExprC
  (match e
    [(NumC _) e]
    [(IdC s) (if (eq? s var) (NumC val) e)]
    [(BinOpC op l r) (BinOpC op (subst l var val) (subst r var val))]
    [(IfLeC tst th el) (IfLeC (subst tst var val)(subst th  var val)(subst el  var val))]
    [(AppC f args) (AppC f (map (lambda ([a : ExprC]) (subst a var val)) args))]))

; lookup-fun finds func and substitues
(define (lookup-fun [funs : (Listof FunDefC)] [fun-name : Symbol]) : FunDefC
  (match funs
    ['() (error 'lookup-fun "QTUM: undefined function ~a" fun-name)]
    [(cons fd rest) (if (eq? (FunDefC-name fd) fun-name) fd (lookup-fun rest fun-name))]))

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
    (list (cons '+ +)(cons '- -)(cons '* *)(cons '/ /))))


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

; test cases
(check-equal? (parse 3.5) (NumC 3.5))
(check-equal? (parse 'v) (IdC 'v))
(check-equal? (parse '{+ 1 2}) (BinOpC '+ (NumC 1) (NumC 2)))
(check-equal? (parse '{ifleq0? -2 4 5})(IfLeC (NumC -2) (NumC 4) (NumC 5)))
(check-equal? (parse '{foo 9})(AppC 'foo (list (NumC 9))))
(check-equal? (parse '{bar}) (AppC 'bar '()))
(check-exn #px"QTUM" (lambda () (parse '((1 2) 3))))

(check-equal? (parse '{f 1 2}) (AppC 'f (list (NumC 1) (NumC 2))))
(check-equal? (parse '{f}) (AppC 'f '()))

(check-equal? (interp (parse '{+ 1 2}) '()) 3)
(check-equal? (interp (parse '{* 1 2}) '()) 2)
(check-equal? (parse 'x) (IdC 'x))

(check-equal? (subst expr-z 'z 10)
 (IfLeC (NumC 10) (BinOpC '+ (NumC 10) (NumC 1)) (BinOpC '- (NumC 10) (NumC 1))))
(check-equal? (subst (IdC 'a) 'b 9) (IdC 'a))

(check-equal? (lookup-fun (list fd-add fd-main-0) 'add) fd-add)
(check-exn #px"QTUM" (lambda () (lookup-fun (list fd-add) 'absent)))

(check-equal?
 (parse-fundef '{fun square x {* x x}})
 (FunDefC 'square '(x) (BinOpC '* (IdC 'x) (IdC 'x))))
(check-exn #px"QTUM" (lambda () (parse-fundef '{fun bad p p {+ p p}})))
(check-exn #px"QTUM" (lambda () (parse-fundef '{fun + a a})))

(define prog-ok (parse-prog
   '{{fun double n {+ n n}}
     {fun main     {double 5}}}))

(check-equal? (map FunDefC-name prog-ok) '(double main))
(check-exn #px"QTUM" (lambda () (parse-prog '{{fun f x x}})))
(check-exn #px"QTUM" (lambda () (parse-prog '{{fun f x x} {fun f y y}})))

(check-equal? (interp (BinOpC '- (NumC 7) (NumC 2)) '()) 5)
(check-equal?
 (interp (IfLeC (NumC 1) (NumC 9) (NumC 8)) '()) 8)
(check-equal? (interp (AppC 'inc (list (NumC 10))) (list fd-inc fd-main-0)) 11)
(check-exn #px"QTUM" (lambda () (interp (AppC 'inc (list (NumC 1) (NumC 2))) (list fd-inc fd-main-0))))

(check-equal? (interp-fns (parse-prog
   '{{fun fact n {ifleq0? n 1 {* n {fact {- n 1}}}}} {fun main {fact 5}}})) 120)

(check-equal? (top-interp
  '{{fun add a b {+ a b}} {fun triple t {* 3 t}} {fun main {add {triple 3} 4}}}) 13)

(check-exn #px"QTUM" (lambda () (top-interp '{{fun main x {+ x 1}}})))
(check-exn #px"QTUM" (lambda () (interp (BinOpC '^^ (NumC 1) (NumC 2)) '())))
(check-exn #px"QTUM" (lambda () (parse-fundef '{fun bad 42 {+ 1 1}})))
(check-exn #px"QTUM" (lambda () (parse-fundef '{fun bad () {+ 1 1}})))
(check-exn #px"QTUM"(lambda () (interp (IdC 'ghost) '())))
(check-exn #px"QTUM" (lambda () (parse-fundef '{fun})))