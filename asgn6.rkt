#lang typed/racket
(require typed/rackunit)

; Assignment 6 is completed and has 100% test case coverage when running the example program

; Define ExprC lang
(define-type ExprC (U NumC IdC AppC LamC StringC IfC WithC SetC))
(struct IdC ([s : Symbol]) #:transparent)
(struct LamC ([params : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct NumC ([n : Real]) #:transparent)
(struct StringC ([s : String]) #:transparent)
(struct IfC ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct WithC ([bindings : (Listof (Pairof Symbol ExprC))] [body : ExprC])  #:transparent)
(struct SetC ([id : Symbol] [rhs : ExprC]) #:transparent)


(define-type Value (U NumV BoolV StringV CloV PrimOpV NullV ArrayV))
(struct NumV ([n : Real]) #:transparent)
(struct BoolV ([b : Boolean]) #:transparent)
(struct StringV ([s : String]) #:transparent)
(struct CloV ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimOpV ([name : Symbol] [impl : (-> (Listof Value) Store Value)]) #:transparent)
(struct NullV () #:transparent)
(struct ArrayV ([len : Natural] [base : Location]) #:transparent)


(define-type Location Natural)
(define-type Store (Vectorof Value))


; symbol value pairings
(define-type Binding (Pairof Symbol Location))
(define-type Env (Listof Binding))


; takes in user input and actually returns the final output
(define (top-interp [s : Sexp] [memsize : Natural  10000]) : String
  (define sto (make-initial-store memsize))
  (define top-env (build-top-env sto))
  (serialize (interp (parse s) top-env sto)))


; initialized vecotr-based memory store used to simulate memory allocation in interp
(define (make-initial-store [memsize : Natural]) : Store
  (unless (>= memsize 2)
    (error 'make-initial-store "QTUM: memory too small"))
  (define v (make-vector memsize (ann (NullV) Value)))
  ; use hints on course website
  (vector-set! v (ann 0 Natural) (NumV 1))
  v)


; makes initial top level env for interp
(define (build-top-env [sto : Store]) : Env
  (list
   (make-binding '+ (PrimOpV '+ add-prim) sto)
   (make-binding '- (PrimOpV '- sub-prim) sto)
   (make-binding '* (PrimOpV '* mul-prim) sto)
   (make-binding '/ (PrimOpV '/ div-prim)sto)
   (make-binding '< (PrimOpV '< lt-prim) sto)
   (make-binding '<= (PrimOpV '<= leq-prim) sto)
   (make-binding 'equal? (PrimOpV 'equal? equal?-prim) sto)
   (make-binding 'strlen (PrimOpV 'strlen strlen-prim) sto)
   (make-binding 'substring(PrimOpV 'substring substring-prim) sto)
   (make-binding 'println (PrimOpV 'println  println-prim) sto)
   (make-binding 'read-num (PrimOpV 'read-num read-num-prim) sto)
   (make-binding 'read-str (PrimOpV 'read-str read-str-prim) sto)
   (make-binding 'seq (PrimOpV 'seq seq-prim) sto)
   (make-binding '++ (PrimOpV '++ concat-prim) sto)
   (make-binding 'make-array (PrimOpV 'make-array make-array-prim) sto)
   (make-binding 'array (PrimOpV 'array array-prim)    sto)
   (make-binding 'aref (PrimOpV 'aref aref-prim)     sto)
   (make-binding 'aset! (PrimOpV 'aset! aset!-prim)    sto)
   (make-binding 'error (PrimOpV 'error user-error-prim) sto)
   (make-binding 'null (NullV)  sto)
   (make-binding 'true (BoolV #t) sto)
   (make-binding 'false (BoolV #f) sto)))


; takes in an Sexp and converts into the appropriate ExprC format
(define (parse [sexp : Sexp]) : ExprC
  (match sexp
    [(? real? n) (NumC n)]
    [(? string? str) (StringC str)]

    [(? symbol? s)
     (when (member s '(if with = =>))
       (error 'parse "QTUM: cannot use this word, already an identifier: ~a" s))
     (IdC s)]

    [(list (? symbol? id) ':= rhs)
     (SetC id (parse rhs))]

    [(list 'if test then else)
     (IfC (parse test) (parse then) (parse else))]

    [(list '=> body0)
     (LamC '() (parse body0))]

    [(list (? symbol? p) '=> body0)
     (LamC (list (cast p Symbol)) (parse body0))]

    [(list p1 p2 '=> body0)
     (let ([checked (map validate-param (list p1 p2))])
       (when (has-duplicates checked)
         (error 'parse "QTUM: dup param naming ~a" checked))
       (LamC checked (parse body0)))]
    
    [(list p1 p2 p3 ps ... '=> body0)
     (let* ([params (cons p1 (cons p2 (cons p3 ps)))]
            [checked (map validate-param params)])
       (when (has-duplicates checked)
         (error 'parse "QTUM: dup param naming ~a" checked))
       (LamC checked (parse body0)))]

    [(list (list params ...) '=> body0)
     (define checked (map validate-param params))
     (when (has-duplicates checked)
       (error 'parse "QTUM: dup param naming ~a" checked))
     (LamC checked (parse body0))]

    [(list _ ... '=> _ ...)
     (error 'parse "QTUM: malformed => form")]

    [(list 'with bindings ... body)
     (define parsed
       (map (lambda ([b : Sexp]) : (List Symbol ExprC)
              (match b
                [(list (? symbol? v) '= rhs)
                 (list (cast v Symbol) (parse rhs))]
                [_ (error 'parse "QTUM: binding gone wrong ~a" b)]))
            (cast bindings (Listof Sexp))))
     (define names
       (map (lambda ([p : (List Symbol ExprC)]) : Symbol
              (first p))
            parsed))
     (when (has-duplicates names)
       (error 'parse "QTUM: dup names ~a" names))
     (define right
       (map (lambda ([p : (List Symbol ExprC)]) : ExprC
              (second p))
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


; takes in a store and the amount of space and returns index of memory allocation
(define (allocate [sto : Store] [n : Natural]) : Location
  (define first-free
    (match (vector-ref sto (ann 0 Natural))
      	[(NumV k) (cast k Natural)]
      [_ (error 'allocate "QTUM: corrupted header")]))
  (define new-free (+ first-free n))
  (when (> new-free (vector-length sto))
    (error 'allocate "QTUM: out of memory"))
  (vector-set! sto (ann 0 Natural) (NumV new-free))
  first-free)


; takes in an ExprC and then returns a real number after breaking it down
(define (interp [expr : ExprC]  [env : Env] [sto : Store]) : Value
  (match expr
    [(NumC n) (NumV n)]

    [(StringC s) (StringV s)]

    [(IfC test then else)
     (define tv (interp test env sto))
     (match tv
       [(BoolV b) (if b (interp then env sto) (interp else env sto))]
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
     (interp (AppC (LamC vars body) exprs) env sto)]

    [(SetC id rhs)
     (define loc (lookup-env env id))
     (define rhs-val (interp rhs env sto))
     (vector-set! sto loc rhs-val)
     (NullV)]
    
    [(AppC fun-expr arg-exprs)
     (define fun-val (interp fun-expr env sto))
     (define arg-vals (map (lambda ([e : ExprC]) (interp e env sto)) arg-exprs))
     (match fun-val
       [(CloV params body clo-env)
        (when (not (= (length params) (length arg-vals)))
          (error 'interp "QTUM: wrong amount of args"))
        (define new-env (append (map (lambda ([p : Symbol] [v : Value]) : Binding
                                       (make-binding p v sto)) params arg-vals) clo-env))
        (interp body new-env sto)]
       [(PrimOpV _ impl)
        (impl arg-vals sto)]
       [v (error 'interp "QTUM: attempt to call something that isnt a function")])]

    [(LamC ps body) (CloV ps body env)]

   [(IdC s) (fetch sto (lookup-env env s))]))


; takes a value and converts it into string representation
(define (serialize [v : Value]) : String
  (match v
    [(NumV  n) (~v n)]                    
    [(BoolV b) (if b "true" "false")]   
    [(StringV s) (format "~v" s)]           
    [(CloV _ _ _) "#<procedure>"]
    [(PrimOpV _ _) "#<primop>"]
    [(ArrayV _ _) "#<array>"]
    [(NullV) "null"]))


; converts qtum structures into actual string text
(define (value->string [v : Value]): String
  (match v
    [(NumV n) (~v n)]
    [(BoolV b) (if b "true" "false")]
    [(StringV s) s]
    [(CloV _ _ _) "#<procedure>"]
    [(PrimOpV _ _) "#<primop>"]))


;*********************ALL PRIM OPS***************************
; takes in two numbers and adds them together
(define (add-prim [args : (Listof Value)] [sto : Store]) : Value
  (match args
    [(list (NumV a) (NumV b)) (NumV (+ a b))]
    [_ (error 'add-prim "QTUM: adding expects two numbers")]))


; takes in two numbers and subtracts second one from first
(define (sub-prim [args : (Listof Value)] [sto : Store]) : Value
  (match args
    [(list (NumV a) (NumV b)) (NumV (- a b))]
    [_ (error 'sub-prim "QTUM: subtract needs 2 numbers")]))


; takes in two numbers and multiplies both the numbers
(define (mul-prim [args : (Listof Value)] [sto : Store]) : Value
  (match args
    [(list (NumV a) (NumV b)) (NumV (* a b))]
    [_ (error 'mul-prim "QTUM: multiplying needs 2 numbers")]))


; takes in two numbers and divides first one by second, takes care of divide by 0 case
(define (div-prim [args : (Listof Value)] [sto : Store]) : Value
  (match args
    [(list (NumV _) (NumV 0))
     (error 'div-prim "QTUM: cannot divide by 0")]
    [(list (NumV a) (NumV b)) (NumV (/ a b))]
    [_ (error 'div-prim "QTUM: division needs 2 numbers")]))


; takes in two numbers and returns true if first number is larger
(define (leq-prim [args : (Listof Value)] [sto : Store]) : Value
  (match args
    [(list (NumV a) (NumV b)) (BoolV (<= a b))]
    [_ (error 'leq-prim "QTUM: leq-prim needs 2 numbers")]))


; takes in two values and returns true if the values are equal (same type)
(define (equal?-prim [args : (Listof Value)] [sto : Store]) : Value
  (if (= (length args) 2)
      (match args
        [(list (NumV n1) (NumV n2)) (BoolV (= n1 n2))]
        [(list (BoolV b1) (BoolV b2)) (BoolV (eq? b1 b2))]
        [(list (StringV s1) (StringV s2)) (BoolV (equal? s1 s2))]
        [(list (ArrayV _ base1) (ArrayV _ base2)) (BoolV (eq? base1 base2))]
        [(list (NullV) (NullV)) (BoolV #t)]
        [(list _ _) (BoolV #f)])
      (error 'equal?-prim "QTUM equal? needs 2 numbers")))


; takes in a list and returns the length of it
(define (strlen-prim [args : (Listof Value)] [sto : Store]) : Value
  (match args
    [(list (StringV s)) (NumV (string-length s))]
    [_ (error 'strlen-prim "QTUM: strlen needs only 1 str")]))


; takes in a string and two numbers and returns the string within the indexes of the numbers
(define (substring-prim [args : (Listof Value)] [sto : Store]) : Value
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
(define (user-error-prim [args : (Listof Value)] [sto : Store]) : Nothing
  (match args
    [(list v)
     (error 'user-error-prim
            (string-append "QTUM user error: " (serialize v)))]
    [_ (error 'user-error-prim
              "QTUM: error needs only one argument")]))


; takes in one argument and prints it 
(define (println-prim [args : (Listof Value)] [sto : Store]): Value
  (match args
    [(list v)
     (displayln (value->string v))
     (BoolV #t)]                          
    [_ (error 'println "QTUM: println takes one argument")]))

; takes in and reads a number from input
(define (read-num-prim [args : (Listof Value)] [sto : Store]) : Value
  (if (null? args)
      (begin
        (display "> ")
        (flush-output)
        (let ([r (read-line)])
          (if (string? r)
              (let ([maybe-num (string->number r)])
                (if (and maybe-num (real? maybe-num))
                    (NumV (cast maybe-num Real))
                    (error 'read-num "QTUM: not a real number")))
              (error 'read-num "QTUM: reached EOF while reading"))))
      (error 'read-num "QTUM: read-num takes no arguments")))


; takes in a reads a string from input
(define (read-str-prim [args : (Listof Value)] [sto : Store]) : Value
  (if (null? args)
      (begin
        (display "> ")
        (flush-output)
        (let ([r (read-line)])
          (if (string? r)
              (StringV r)
              (error 'read-str "QTUM: EOF reached"))))
      (error 'read-str "QTUM: read-str has 0 args")))


; takes in list of values and returns value produced by last arg
(define (seq-prim [args : (Listof Value)] [sto : Store]): Value
  (cond [(null? args)
         (error 'seq "QTUM: 1 arg needed")]
        [else (last args)]))


; makes each of the args text and concats into one singular string
(define (concat-prim [args : (Listof Value)] [sto : Store]): Value
  (define pieces (map value->string args))
  (StringV (apply string-append pieces)))


; takes in args and actually creates an array
(define (make-array-prim [args : (Listof Value)] [sto : Store])
  (match args
    [(list (NumV n) v)
     (if (and (integer? n) (positive? n))
         (let ([len (cast n Natural)]
               [base (allocate sto (cast n Natural))])
           (for ([i (in-range len)])
             (vector-set! sto (+ base i) v))
           (ArrayV len base))
         (error 'make-array "QTUM: size must be positive integer"))]
    [_ (error 'make-array "QTUM: expects size then value")]))


; takes in a list of args, allocates memory for them, and stores them in array
(define (array-prim [args : (Listof Value)] [sto : Store])
  (if (positive? (length args))
      (let ([len (length args)]
            [base (allocate sto (length args))])
        (for ([i (in-naturals)] [v args])
          (vector-set! sto (+ base i) v))
        (ArrayV len base))
      (error 'array "QTUM: empty array")))


; checks if input is valid array and returns value stored at index
(define (aref-prim [args : (Listof Value)] [sto : Store])
  (match args
    [(list (ArrayV len base) (NumV k))
     (if (and (integer? k) (<= 0 k (- len 1)))
         (fetch sto (+ base (cast k Natural)))
         (error 'aref "QTUM: index out of range"))]
    [_ (error 'aref "QTUM: need array and index")]))

; updates element in a given array
(define (aset!-prim [args : (Listof Value)] [sto : Store])
  (match args
    [(list (ArrayV len base) (NumV k) v)
     (if (and (integer? k) (<= 0 k (- len 1)))
         (begin
           (vector-set! sto (+ base (cast k Natural)) v)
           (NullV))
         (error 'aset! "QTUM: index out of range"))]
    [_ (error 'aset! "QTUM: need array index value")]))


(define (lt-prim [args : (Listof Value)] [sto : Store]) : Value
  (match args
    [(list (NumV a) (NumV b)) (BoolV (< a b))]
    [_ (error 'lt-prim "QTUM: < expects two numbers")]))

;********************END PRIM OPS***************************

; takes in a symbol and a value and returns the binding which is the symbol-value pair
(define (make-binding [k : Symbol] [v : Value] [sto : Store]) : Binding
  (define loc (allocate sto 1))
  (vector-set! sto loc v)
  (cons k loc))


; takes in a symbol and the current enviroment and returns the symbol value in that enviroment
(define (lookup-env [env : Env] [x : Symbol]) : Location
  (match env
    ['() (error 'lookup-env "QTUM: unbound identifier ~a" x)]
    [(cons (cons y loc) rest)
     (if (eq? x y) loc (lookup-env rest x))]))


; takes in a store and location and gives the value stored at that location 
(define (fetch [sto : Store] [loc : Location]): Value
  (vector-ref sto loc))


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
  (define sto (make-initial-store 1000))
  (define env (build-top-env sto))
  (serialize (interp e env sto)))

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

(check-equal? (value->string (BoolV #t)) "true")
(check-equal? (value->string (BoolV #f)) "false")

(check-equal?
 (value->string (CloV '() (NumC 9) '()))
 "#<procedure>")


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
;(top-interp example-program)


; while function accepting guard function and a body function and keeps runnig till guard returns false
; in-order accepts an array of numbers and its size and returns if array is strictly in increasing order


(define while
  '(with (while = "bogus")
     (seq
       (while := ((g b) => (if (g) (seq (b) (while g b)) null)))
       while)))


(define in-order
  '(with (while = "bogus")
     (seq
       (while := ((g b) => (if (g) (seq (b) (while g b)) null)))
       (with (in-order = "bogus")
         (seq
           (in-order :=
             ((arr size) =>
              (with (ok = true) (i = 0)
                (seq
                  (while
                    (=> (if ok (< i (- size 1)) false))
                    (=> (if (< (aref arr i) (aref arr (+ i 1)))
                            (i := (+ i 1))
                            (seq (ok := false) (i := size)))))
                  ok))))
           in-order)))))


(check-equal?
 (value->string (PrimOpV '+ add-prim))
 "#<primop>")

(check-exn
 (lambda (e)
   (and (exn:fail? e)
        (regexp-match? #rx"QTUM: memory too small" (exn-message e))))
 (lambda () (make-initial-store 1)))

; more parser tests
(check-equal? (parse '(x := 5)) (SetC 'x (NumC 5)))
(check-equal? (parse '(=> 42)) (LamC '() (NumC 42)))

(check-exn
 (lambda (e)
   (and (exn:fail? e)
        (regexp-match? #rx"QTUM: dup param naming" (exn-message e))))
 (lambda () (parse '((x x) => 10))))

(check-equal? (parse '((x y) => (+ x y)))
              (LamC '(x y) (AppC (IdC '+) (list (IdC 'x) (IdC 'y)))))

(check-exn
 (lambda (e)
   (and (exn:fail? e)
        (regexp-match? #rx"QTUM: malformed => form" (exn-message e))))
 (lambda () (parse '(5 6 => 7 8))))

(check-equal?
 (parse '(x => (+ x 1)))
 (LamC '(x)
       (AppC (IdC '+) (list (IdC 'x) (NumC 1)))))

; allocate tests
(let ([sto (make-initial-store 5)])   
  (check-equal? (allocate sto 2) 1)   
  (check-equal? (vector-ref sto (ann 0 Natural))    
                (NumV 3)))

(let ([bad-sto (make-initial-store 3)]) 
  (vector-set! bad-sto (ann 0 Natural) (NullV))     
  (check-exn
   (lambda (e)
     (and (exn:fail? e)
          (regexp-match? #rx"QTUM: corrupted header"
                         (exn-message e))))
   (lambda () (allocate bad-sto 1))))


(let ([sto-small (make-initial-store 3)])
  (check-exn
   (lambda (e)
     (and (exn:fail? e)
          (regexp-match? #rx"QTUM: out of memory"
                         (exn-message e))))
   (lambda () (allocate sto-small 3))))

; interp more
(define sto  (make-initial-store 5))
(define loc  (allocate sto 1))
(define env (list (cons 'x loc)))
(define expr (SetC 'x (NumC 99)))

(check-equal? (interp expr env sto)
              (NullV))
(check-equal? (vector-ref sto loc)
              (NumV 99))

; ArrayV and NullV tests
(check-equal? (serialize (ArrayV 3 0)) "#<array>")
(check-equal? (serialize (NullV)) "null")

(let* ([dummy-sto (make-initial-store 4)]
       [a1 (ArrayV 3 7)]
       [a2 (ArrayV 5 7)])
  (check-equal? (equal?-prim (list a1 a2) dummy-sto)
                (BoolV #t)))

(let* ([dummy-sto (make-initial-store 4)]
       [a1 (ArrayV 3 7)]
       [a2 (ArrayV 3 9)])
  (check-equal? (equal?-prim (list a1 a2) dummy-sto)
                (BoolV #f)))

(let ([dummy-sto (make-initial-store 4)])
  (check-equal? (equal?-prim (list (NullV) (NullV)) dummy-sto)
                (BoolV #t)))

; new primop tests
(define (fresh-store) (make-initial-store 30))
(let ([sto (fresh-store)])
  (define arr (make-array-prim (list (NumV 3) (NumV 42)) sto))
  (check-true (ArrayV? arr)))

(check-exn #rx"size must be positive"
           (λ () (make-array-prim (list (NumV 0) (BoolV #t))
                                  (fresh-store))))

(check-exn #rx"expects size then value"
  (λ () (make-array-prim (list (NumV 5)) (fresh-store))))

(let ([sto (fresh-store)])
  (define arr (array-prim (list (NumV 1) (NumV 2) (NumV 3)) sto))
  (check-true (ArrayV? arr)))

(check-exn #rx"empty array"
  (λ () (array-prim '() (fresh-store))))

(let* ([sto (fresh-store)]
       [arr (array-prim (list (StringV "a") (StringV "b")) sto)])

  (check-equal? (aref-prim (list arr (NumV 1)) sto)
                (StringV "b"))
  (check-exn #rx"index out of range"
    (λ () (aref-prim (list arr (NumV 5)) sto))))

(check-exn #rx"need array and index"
  (λ () (aref-prim (list (BoolV #f) (NumV 0)) (fresh-store))))

(let* ([sto (fresh-store)]
       [arr (make-array-prim (list (NumV 2) (NumV 0)) sto)])
  (check-equal? (aset!-prim (list arr (NumV 1) (BoolV #t)) sto)
                (NullV))

(check-exn #px"QTUM: < expects two numbers"
  (lambda () (top-interp '{< 1 "apple"})))

 (check-equal? (top-interp '{< 1 5}) "true")
  
; checkign mutation
  (check-equal? (aref-prim (list arr (NumV 1)) sto) (BoolV #t))

  (check-exn #rx"index out of range"
             (λ () (aset!-prim (list arr (NumV -1) (NumV 9)) sto)))

  (check-exn #rx"need array index value"
             (λ () (aset!-prim (list (NullV) (NumV 0)) (fresh-store)))))

; id? tests
(check-equal? (id? 'foo) #t)
(check-equal? (id? 'if) #f)

; asgn6 failing tests
(check-equal?
  (parse '(z y x => (w => (+ z (w y)))))
  (LamC '(z y x)
        (LamC '(w)
              (AppC (IdC '+)
                    (list (IdC 'z)
                          (AppC (IdC 'w) (list (IdC 'y))))))))
(check-exn #px"QTUM: dup param naming"
  (lambda () (parse '(a b a => (+ a b)))))


(check-equal? (top-interp
  '((minus => (minus 8 5))
    (a b => (+ a (* -1 b))))
  1000) "3")

(check-exn #px"QTUM: dup param naming"
  (lambda () (parse '(foo foo => (+ foo 1)))))
