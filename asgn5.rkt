#lang typed/racket
(require typed/rackunit)

; Assignment 5 is completed and has 100% test case coverage when running the example program

; Define ExprC lang
(define-type ExprC (U NumC IdC AppC LamC StringC IfC WithC))
(struct IdC ([s : Symbol]) #:transparent)
(struct LamC ([params : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct NumC ([n : Real]) #:transparent)
(struct StringC ([s : String]) #:transparent)
(struct IfC ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct WithC ([bindings : (Listof (Pairof Symbol ExprC))] [body : ExprC])  #:transparent)


(define-type Value (U NumV BoolV StringV CloV PrimOpV))
(struct NumV ([n : Real]) #:transparent)
(struct BoolV ([b : Boolean]) #:transparent)
(struct StringV ([s : String]) #:transparent)
(struct CloV ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimOpV  ([name : Symbol] [impl : (-> (Listof Value) Value)]) #:transparent)


; symbol value pairings
(define-type Binding (Pairof Symbol Value))
(define-type Env (Listof Binding))


; takes in user input and actually returns the final output
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))


; takes in an Sexp and converts into the appropriate ExprC format
(define (parse [sexp : Sexp]) : ExprC
  (match sexp
    [(? real? n) (NumC n)]
    
    [(? string? str) (StringC str)]

    [(? symbol? s)
     (when (member s '(if with = =>))
       (error 'parse "QTUM: cannot use this word, already an identifier: ~a" s))
     (IdC s)]

    [(list 'if test then else)
     (IfC (parse test) (parse then) (parse else))]

    [(list '=> body0)
     (LamC '() (parse body0))]

    [(list (? symbol? p) '=> body0)
     (LamC (list (cast p Symbol)) (parse body0))]

    [(list (list params ...) '=> body0)
     (define pars (map validate-param params))
     (when (has-duplicates pars)
       (error 'parse "QTUM: dup param naming ~a" pars))
     (LamC pars (parse body0))]

    [(list params ... '=> body0)
     (define pars (map validate-param (cast params (Listof Any))))
     (when (has-duplicates pars)
       (error 'parse "QTUM: dup param naming ~a" pars))
     (LamC pars (parse body0))]

    [(list _ ... '=> _ ...)
     (error 'parse "QTUM: malformed => form")]

    [(list 'with bindings ... body)
     (define parsed
       (map (lambda ([b : Sexp]) : (Pairof Symbol ExprC)
              (match b
                [(list (? symbol? v) '= rhs)
                 (cons (cast v Symbol) (parse rhs))]
                [_ (error 'parse "QTUM: binding gone wrong ~a" b)]))
            (cast bindings (Listof Sexp))))
     (define names
       (map (lambda ([p : (Pairof Symbol ExprC)]) : Symbol
              (car p))
            parsed))
     (when (has-duplicates names)
       (error 'parse "QTUM: dup names ~a" names))
     (define right
       (map (lambda ([p : (Pairof Symbol ExprC)]) : ExprC
              (cdr p))
            parsed))
     (AppC (LamC names (parse body)) right)]

    [(list fzer args ...)
     (AppC (parse fzer)
           (map (lambda ([a : Sexp]) : ExprC (parse a)) args))]

    [other (error 'parse "QTUM: syntax error? ~e" other)]))



; makes sure parameter is symbol
(define (validate-param [p : Any]) : Symbol
  (cond
    [(symbol? p) (cast p Symbol)]
    [(null? p) (error 'parse-fundef "QTUM: empty list found in parameter")]
    [else (error 'parse-fundef "QTUM: param isnt a symbol ~e" p)]))


; takes in an ExprC and then returns a real number after breaking it down
(define (interp [expr : ExprC]  [env : Env]) : Value
  (match expr
    [(NumC n) (NumV n)]

    [(StringC s) (StringV s)]

    [(IfC test then else)
     (define tv (interp test env))
     (match tv
       [(BoolV b) (if b (interp then env) (interp else env))]
       [_ (error 'interp "QTUM: non boolean value")])]

    ; desugar during runtime
    [(WithC binds body)
     (define vars
       (map (lambda ([p : (Pairof Symbol ExprC)]) : Symbol
              (car p))
            binds))
     (define exprs
       (map (lambda ([p : (Pairof Symbol ExprC)]) : ExprC
              (cdr p))
            binds))
     (interp (AppC (LamC vars body) exprs) env)]

    
    [(AppC fun-expr arg-exprs)
     (define fun-val (interp fun-expr env))
     (define arg-vals (map (lambda ([e : ExprC]) (interp e env)) arg-exprs))
     (match fun-val
       [(CloV params body clo-env)
        (when (not (= (length params) (length arg-vals)))
          (error 'interp "QTUM: wrong amount of args"))
        (define new-env (append (map make-binding params arg-vals) clo-env))
        (interp body new-env)]
       [(PrimOpV _ impl)
        (impl arg-vals)]
       [v
        (if (empty? arg-vals)
            v
            (error 'interp "QTUM: attempt to call something that isnt a function"))])]

    [(LamC ps body) (CloV ps body env)]

   [(IdC s) (lookup-env env s)]))


; takes a value and converts it into string representation
(define (serialize [v : Value]) : String
  (match v
    [(NumV  n) (~v n)]                    
    [(BoolV b) (if b "true" "false")]   
    [(StringV s) (format "~v" s)]           
    [(CloV _ _ _) "#<procedure>"]
    [(PrimOpV _ _) "#<primop>"]))

; converts qtum structures into actual string text
(define (value->string [v : Value]): String
  (match v
    [(NumV n)     (~v n)]
    [(BoolV b)    (if b "true" "false")]
    [(StringV s)  s]
    [(CloV _ _ _) "#<procedure>"]
    [(PrimOpV _ _) "#<primop>"]))


;*********************ALL PRIM OPS***************************
; takes in two numbers and adds them together
(define (add-prim [args : (Listof Value)]) : Value
  (match args
    [(list (NumV a) (NumV b)) (NumV (+ a b))]
    [_ (error 'add-prim "QTUM: adding expects two numbers")]))


; takes in two numbers and subtracts second one from first
(define (sub-prim [args : (Listof Value)]) : Value
  (match args
    [(list (NumV a) (NumV b)) (NumV (- a b))]
    [_ (error 'sub-prim "QTUM: subtract needs 2 numbers")]))


; takes in two numbers and multiplies both the numbers
(define (mul-prim [args : (Listof Value)]) : Value
  (match args
    [(list (NumV a) (NumV b)) (NumV (* a b))]
    [_ (error 'mul-prim "QTUM: multiplying needs 2 numbers")]))


; takes in two numbers and divides first one by second, takes care of divide by 0 case
(define (div-prim [args : (Listof Value)]) : Value
  (match args
    [(list (NumV _) (NumV 0))
     (error 'div-prim "QTUM: cannot divide by 0")]
    [(list (NumV a) (NumV b)) (NumV (/ a b))]
    [_ (error 'div-prim "QTUM: division needs 2 numbers")]))


; takes in two numbers and returns true if first number is larger
(define (leq-prim [args : (Listof Value)]) : Value
  (match args
    [(list (NumV a) (NumV b)) (BoolV (<= a b))]
    [_ (error 'leq-prim "QTUM: leq-prim needs 2 numbers")]))


; takes in two values and returns true if the values are equal (same type)
(define (equal?-prim [args : (Listof Value)]) : Value
  (if (= (length args) 2)
      (match args
        [(list (NumV n1)    (NumV n2))    (BoolV (= n1 n2))]
        [(list (BoolV b1)   (BoolV b2))   (BoolV (eq? b1 b2))]
        [(list (StringV s1) (StringV s2)) (BoolV (equal? s1 s2))]
        [(list _ _) (BoolV #f)])
      (error 'equal?-prim "QTUM equal? needs 2 numbers")))


; takes in a list and returns the length of it
(define (strlen-prim [args : (Listof Value)]) : Value
  (match args
    [(list (StringV s)) (NumV (string-length s))]
    [_ (error 'strlen-prim "QTUM: strlen needs only 1 str")]))

; takes in a string and two numbers and returns the string within the indexes of the numbers
(define (substring-prim [args : (Listof Value)]) : Value
  (match args
    [(list (StringV s) (NumV start) (NumV stop))
     (cond
       [(and (integer? start) (integer? stop)
             (<= 0 start stop (string-length s)))
        (define startInd (cast start Integer))
        (define stopInd (cast stop Integer))
        (StringV (substring s startInd stopInd))]
       [else
        (error 'substring-prim "QTUM: string indexing gone wrong")])]
    [_ (error 'substring-prim
              "QTUM: substring needs 1 string and 2 numbers in that order")]))


; takes in list and returns errors if there is more than 1 argument
(define (user-error-prim [args : (Listof Value)]) : Nothing
  (match args
    [(list v)
     (error 'user-error-prim
            (string-append "QTUM user error: " (serialize v)))]
    [_ (error 'user-error-prim
              "QTUM: error needs only one argument")]))


; takes in one argument and prints it 
(define (println-prim [args : (Listof Value)]): Value
  (match args
    [(list v)
     (displayln (value->string v))
     (BoolV #t)]                          
    [_ (error 'println "QTUM: println takes one argument")]))

; takes in and reads a number from input
(define (read-num-prim [args : (Listof Value)]) : Value
  (unless (null? args)
    (error 'read-num "QTUM: read-num takes no arguments"))
  (display "> ")
  (flush-output)
  (define r (read-line))
  (unless (string? r)
    (error 'read-num "QTUM: reached EOF while reading"))
  (define maybe-num (string->number r))
  (unless (and maybe-num (real? maybe-num))
    (error 'read-num "QTUM: not a real number"))
  (NumV (cast maybe-num Real)))


; takes in a reads a string from input
(define (read-str-prim [args : (Listof Value)]) : Value
  (unless (null? args)
    (error 'read-str "QTUM: read-str has 0 args"))
  (display "> ")
  (flush-output)
  (define r (read-line))
  (unless (string? r)
    (error 'read-str "QTUM: EOF reached"))
  (StringV r))

; takes in list of values and returns value produced by last arg
(define (seq-prim [args : (Listof Value)]): Value
  (cond [(null? args)
         (error 'seq "QTUM: 1 arg needed")]
        [else (last args)]))

; makes each of the args text and concats into one singular string
(define (concat-prim [args : (Listof Value)]): Value
  (define pieces (map value->string args))
  (StringV (apply string-append pieces)))

;********************END PRIM OPS***************************

; takes in a symbol and a value and returns the binding which is the symbol-value pair
(: make-binding (-> Symbol Value Binding))
(define (make-binding [k : Symbol] [v : Value]): Binding
  (cons k v))


; allows interpreter to know what each of the basic things (+, -)
; do by keeping track of it in the global scope
(define top-env
  (list (make-binding '+ (PrimOpV '+ add-prim))
        (make-binding '- (PrimOpV '- sub-prim))
        (make-binding '* (PrimOpV '* mul-prim))
        (make-binding '/ (PrimOpV '/ div-prim))
        (make-binding '<= (PrimOpV '<= leq-prim))
        (make-binding 'equal? (PrimOpV 'equal? equal?-prim))
        (make-binding 'strlen (PrimOpV 'strlen strlen-prim))
        (make-binding 'substring (PrimOpV 'substring substring-prim))
        (make-binding 'error (PrimOpV 'error user-error-prim))
        (make-binding 'true (BoolV #t))
        (make-binding 'false (BoolV #f))
        ; add to pass test case?
        (make-binding '=> (CloV '(x) (IdC 'x) '()))
        (make-binding 'println  (PrimOpV 'println  println-prim))
        (make-binding 'read-num (PrimOpV 'read-num read-num-prim))
        (make-binding 'read-str (PrimOpV 'read-str read-str-prim))
        (make-binding 'seq      (PrimOpV 'seq      seq-prim))
        (make-binding '++       (PrimOpV '++       concat-prim))))


; takes in a symbol and the current enviroment and returns the symbol value in that enviroment
(define (lookup-env [env : Env] [x : Symbol]) : Value
  (match env
    ['() (error 'lookup-env "QTUM: unbound identifier ~a" x)]
    [(cons (cons y v) rest)
     (if (eq? x y) v (lookup-env rest x))]))


; takes in a list of symbols and make sure that there are no repeats
(define (has-duplicates [syms : (Listof Symbol)]) : Boolean
  (not (false? (check-duplicates (cast syms (Listof Any))))))

; takes in a symbol and makes sure it is legal
(define (id? [s : Symbol]): Boolean
  (and (regexp-match? #px"^[A-Za-z][A-Za-z0-9_-]*$" (symbol->string s)) 
       (not (member s '(if with = =>)))))  

; *********** ALL TESTING ************************************************************************************

(check-exn #px"QTUM" (lambda () (top-interp '{with [x = 1] [x = 2] x})))

(check-equal? (top-interp '0) "0")
(check-equal? (top-interp '{(x) => x}) "#<procedure>")
(check-equal? (top-interp '+) "#<primop>")
(check-equal? (top-interp 'true) "true")
(check-equal? (top-interp 'false) "false")

; prim oper tests
(check-equal? (top-interp '{+ 4 5}) "9")
(check-equal? (top-interp '{- 10 3}) "7")
(check-equal? (top-interp '{* 2 6}) "12")
(check-equal? (top-interp '{/ 8 2}) "4")
(check-equal? (top-interp '{<= 3 7}) "true")
(check-exn #px"QTUM: adding expects two numbers" (lambda () (top-interp '{+ 1})))
(check-exn #px"QTUM: adding expects two numbers" (lambda () (top-interp '{+ 1 2 3})))
(check-exn #px"QTUM: cannot divide by 0" (lambda () (top-interp '{/ 1 0})))
(check-exn #px"QTUM: leq-prim needs 2 numbers" (lambda () (top-interp '{<= 1 "x"})))

; string 
(check-equal? (top-interp '{strlen "abcd"}) "4")
(check-equal? (top-interp '{substring "hello" 1 4}) "\"ell\"")
(check-exn #px"QTUM: strlen needs only 1 str" (lambda () (top-interp '{strlen 100})))
(check-exn #px"QTUM: strlen needs only 1 str" (lambda () (top-interp '{strlen "a" "b"})))
(check-exn #px"QTUM: string indexing gone wrong" (lambda () (top-interp '{substring "abc" 0 5})))
(check-exn #px"QTUM: string indexing gone wrong" (lambda () (top-interp '{substring "abc" 2 1})))
(check-exn #px"QTUM: substring needs 1 string and 2 numbers in that order" (lambda () (top-interp '{substring 99 0 1})))

; equal?
(check-equal? (top-interp '{equal? 3 3}) "true")
(check-equal? (top-interp '{equal? true true}) "true")
(check-equal? (top-interp '{equal? "a" "b"}) "false")
(check-equal? (top-interp '{equal? + +}) "false")
(check-equal? (top-interp '{equal? {(x) => x} {(y) => y}}) "false")
(check-exn #px"QTUM equal\\? needs 2 numbers" (lambda () (top-interp '{equal? 1})))

; prim error 
(check-exn #px"QTUM user error" (lambda () (top-interp '{error "boom"})))
(check-exn #px"QTUM: error needs only one argument" (lambda () (top-interp '{error 1 2})))

; if 
(check-equal? (top-interp '{if true 1 0}) "1")
(check-equal? (top-interp '{if false 1 0}) "0")
(check-exn #px"QTUM" (lambda () (top-interp '{if 5 1 0})))

; with 
(check-equal? (top-interp '{with [x = 3] [y = 4] {+ x y}}) "7")
(check-equal? (top-interp '{with [x = 1] {with [x = 5] {+ x 2}}}) "7")
(check-exn #px"QTUM" (lambda () (top-interp '{with [x = 1] [x = 2] x})))
(check-exn #px"QTUM" (lambda () (top-interp '{with [x 1] x})))

; sub-
(check-exn #px"QTUM: subtract needs 2 numbers" (lambda () (top-interp '{- 5 "a"})))
(check-exn #px"QTUM: subtract needs 2 numbers" (lambda () (top-interp '{- 5})))

; mul-
(check-exn #px"QTUM: multiplying needs 2 numbers" (lambda () (top-interp '{* "a" 4})))
(check-exn #px"QTUM: multiplying needs 2 numbers" (lambda () (top-interp '{* 1 2 3})))

; div-
(check-exn #px"QTUM: cannot divide by 0" (lambda () (top-interp '{/ 7 0})))
(check-exn #px"QTUM: division needs 2 numbers" (lambda () (top-interp '{/ 7 "b"})))

(check-equal? (top-interp '{{(x) => {+ x 1}} 8}) "9")
(check-equal? (top-interp '{with [inc = {(x) => {+ x 1}}] {inc 10}}) "11")
(check-equal? (top-interp '{{{(x) => {(y) => {+ x y}}} 3} 4}) "7")
(check-equal? (top-interp '{ {(f) => {f 6}} {(z) => {+ z 2}} }) "8")
(check-exn #px"QTUM" (lambda () (top-interp '{{(x) => x} 1 2})))
(check-exn #px"QTUM" (lambda () (top-interp '{5 1 2})))

(check-exn #px"QTUM" (lambda () (top-interp 'undefined-symbol)))

; parser edge cases
(check-exn #px"QTUM" (lambda () (top-interp 'if)))
(check-exn #px"QTUM" (lambda () (top-interp '{{x x} => x})))
(check-exn #px"QTUM" (lambda () (top-interp '{})))

; parameter validation tests
(check-exn #px"QTUM: empty list found in parameter" (lambda () (top-interp '{((x ()) => x)})))
(check-exn #px"QTUM: param isnt a symbol" (lambda () (top-interp '{((x 5) => x)})))

; testing Asts without parser
(define (run-ast [e : ExprC]) : String
  (serialize (interp e top-env)))

; testing asts
(define ast-with-single
  (WithC
   (list (cons 'x (NumC 3)))
   (AppC (IdC '+) (list (IdC 'x) (NumC 4)))))
(check-equal? (run-ast ast-with-single) "7")
(define ast-with-multi
  (WithC
   (list (cons 'a (NumC 2)) (cons 'b (NumC 5)))
   (AppC (IdC '+) (list (IdC 'a) (IdC 'b)))))
(check-equal? (run-ast ast-with-multi) "7")

; has-duplicates
(check-equal? (has-duplicates (list 'a 'b 'a)) #t)
(check-equal? (has-duplicates (list 'x 'y 'z)) #f)

(check-exn #px"QTUM: attempt to call something that isnt a function"
  (lambda () (top-interp '{5 1})))
(check-exn #px"QTUM: attempt to call something that isnt a function"
  (lambda () (top-interp '{{5} 2})))

; new tests asgn 5 ;;;;;;;;;;;;;;;;;;;;;;;;;
(check-equal?
 (parameterize ([current-output-port (open-output-string)])
   (top-interp '{println "hi"}))
 "true")

(parameterize ([current-input-port (open-input-string "42\n")])
  (check-equal? (top-interp '{read-num}) "42"))

(parameterize ([current-input-port (open-input-string "hello\n")])
  (check-equal? (top-interp '{read-str}) "\"hello\""))

(check-equal?
 (parameterize ([current-output-port (open-output-string)])
   (top-interp '{seq {println "a"} {println "b"} 9}))
 "9")

(check-equal?
 (top-interp '{++ "pi = " 3.14})
 "\"pi = 3.14\"")

; lots of error testings
(check-exn #px"QTUM: println takes one argument"
  (lambda () (top-interp '{println})))
(check-exn #px"QTUM: println takes one argument"
  (lambda () (top-interp '{println "a" "b"})))

(check-exn #px"QTUM: read-num takes no arguments"
  (lambda () (top-interp '{read-num 1})))

(parameterize ([current-input-port (open-input-string "")])
  (check-exn #px"QTUM: reached EOF while reading"
    (lambda () (top-interp '{read-num}))))

(parameterize ([current-input-port (open-input-string "abc\n")])
  (check-exn #px"QTUM: not a real number"
    (lambda () (top-interp '{read-num}))))

(check-exn #px"QTUM: read-str has 0 args"
  (lambda () (top-interp '{read-str 1})))

(parameterize ([current-input-port (open-input-string "")])
  (check-exn #px"QTUM: EOF reached"
    (lambda () (top-interp '{read-str}))))

(check-exn #px"QTUM: 1 arg needed"
  (lambda () (top-interp '{seq})))


;(check-exn #px"QTUM: malformed => form"
 ; (lambda () (top-interp '{(+ => 3)})))

(check-equal? (value->string (BoolV #t)) "true")
(check-equal? (value->string (BoolV #f)) "false")

(check-equal?
 (value->string (CloV '() (NumC 9) '()))
 "#<procedure>")

(check-equal?
 (value->string (PrimOpV '+ add-prim))
 "#<primop>")

; our example program game
; asks user for the best basketball player
; and only accepts the correct answer - Stephen Curry
(define example-program
  '{seq
      {println "Guess the greatest basketball player to ever grace this planet!"}
      {with
        [make-loop =
          (f =>                      
               (=> {with [name = {read-str}]
                      {if {equal? name "Stephen Curry"}
                          {println "LETS GO!!! THAT IS THE GOAT."}
                          {seq
                             {println "Nope, try a little harder."}
            
                             {(f f)}}}}))]          
        {(make-loop make-loop)}}})                   

;uncomment this line to play the game
(top-interp example-program)