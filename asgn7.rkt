#lang typed/racket
(require typed/rackunit)

; Assignment 7 is completed and has 100% test case coverage when running the example program


; QTUM 7 structures
(struct NumT () #:transparent)
(struct BoolT () #:transparent)
(struct StrT () #:transparent)
(struct ArrowT ([args : (Listof Ty)] [ret : Ty]) #:transparent)

(define-type Ty (U NumT BoolT StrT ArrowT))
(struct BindAnn ([name : Symbol] [ty : Ty] [rhs : ExprC]) #:transparent)

(define-type BindingT (Pairof Symbol Ty))
(define-type TEnv (Listof BindingT))

; Define ExprC lang
(define-type ExprC (U NumC IdC AppC LamC StringC IfC WithC RecC))
(struct IdC ([s : Symbol]) #:transparent)
(struct LamC ([params : (Listof Symbol)] [param-tys : (Listof Ty)][body : ExprC]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct NumC ([n : Real]) #:transparent)
(struct StringC ([s : String]) #:transparent)
(struct IfC ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct WithC ([bindings : (Listof (Pairof Symbol ExprC))] [body : ExprC])  #:transparent)
;(struct SetC ([id : Symbol] [rhs : ExprC]) #:transparent)
(struct RecC ([names : (Listof Symbol)] [tys : (Listof Ty)] [rhss : (Listof ExprC)] [body  : ExprC]) #:transparent)


(define-type Value (U NumV BoolV StringV CloV PrimOpV))
(struct NumV ([n : Real]) #:transparent)
(struct BoolV ([b : Boolean]) #:transparent)
(struct StringV ([s : String]) #:transparent)
(struct CloV ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimOpV ([name : Symbol] [impl : (-> (Listof Value) Store Value)]) #:transparent)
;(struct NullV () #:transparent)
;(struct ArrayV ([len : Natural] [base : Location]) #:transparent)

(define-type Location Natural)
(define-type Store (Vectorof Value))


; symbol value pairings
(define-type Binding (Pairof Symbol Location))
(define-type Env (Listof Binding))

(define base-tenv
  (list
   (cons '+ (ArrowT (list (NumT) (NumT)) (NumT)))
   (cons '- (ArrowT (list (NumT) (NumT)) (NumT)))
   (cons '* (ArrowT (list (NumT) (NumT)) (NumT)))
   (cons '/ (ArrowT (list (NumT) (NumT)) (NumT)))
   (cons '<= (ArrowT (list (NumT) (NumT)) (BoolT)))
   (cons 'num-eq? (ArrowT (list (NumT) (NumT)) (BoolT)))
   (cons 'str-eq? (ArrowT (list (StrT) (StrT)) (BoolT)))
   (cons 'true (BoolT))
   (cons 'false (BoolT))))


; takes Sexpr that represents type and converts into internal Ty structure
(define (parse-type [s : Sexp]) : Ty
  (match s
    ['num (NumT)]
    ['bool (BoolT)]
    ['str (StrT)]
    
    [(list argsexp ... '-> retsexp)
     (ArrowT (map parse-type (cast argsexp (Listof Sexp))) (parse-type retsexp))]
    
    [else
     (error 'parse-type "QTUM: bad type ~a" s)]))

; searches up variables type in the type enviroment
(define (lookup-type [tenv : TEnv] [x : Symbol]) : Ty
  (match tenv
    ['() (error 'type-check "QTUM: unbound id ~a" x)]
    [(cons (cons y ty) rest)
     (if (eq? x y) ty (lookup-type rest x))]))


; go through expression e and make sure all operations are used according to their type
(define (type-check [e : ExprC] [tenv : TEnv]) : Ty
  (match e
    [(NumC _) (NumT)]
    [(StringC _) (StrT)]
    [(IdC x) (lookup-type tenv x)] 

    [(IfC t c a)
     (unless (equal? (type-check t tenv) (BoolT))
       (error 'type-check "QTUM: if test not bool"))
     (define ct (type-check c tenv))
     (define at (type-check a tenv))
     (unless (equal? ct at)
       (error 'type-check "QTUM: branches differ ~a vs ~a" ct at))
     ct]

    [(AppC f args)
     (define ft (type-check f tenv))
     (match ft
       [(ArrowT argtys ret)
        (unless (= (length argtys) (length args))
          (error 'type-check "QTUM: wrong arity"))
  
        (define actual-types (map (lambda ([a : ExprC]) (type-check a tenv)) args))
  
        (for-each 
         (lambda (expected actual)
           (unless (equal? actual expected)
             (error 'type-check
                    "QTUM: arg type mismatch – expected ~a, got ~a"
                    expected actual)))
         argtys
         actual-types)
  
        ret]
       [_ (error 'type-check "QTUM: trying to call non-function")])]

    [(LamC ps ptys body)
     (when (not (= (length ps) (length ptys)))
       (error 'type-check "QTUM: internal lamC length mismatch"))
     (define new-tenv (append (map (lambda ([p : Symbol] [t : Ty]) : BindingT
                 (cons p t)) ps ptys) tenv))
     (ArrowT ptys (type-check body new-tenv))]

    [(RecC names tys rhss body)
     (define tenv* (append (map (lambda ([nm  : Symbol] [ty  : Ty]) : BindingT
          (cons nm ty)) names tys) tenv))
     (for ([rhs rhss] [tau tys] [nm names])
       (unless (equal? (type-check rhs tenv*) tau)
         (error 'type-check
                "QTUM: rhs of ~a expected ~a, got ~a"
                nm tau (type-check rhs tenv*))))
     (type-check body tenv*)]
    
    [(WithC bindings body)
     (define names
       (map (lambda ([p : (Pairof Symbol ExprC)]) : Symbol
              (car p)) bindings))
     (define rhss (map (lambda ([p : (Pairof Symbol ExprC)]) : ExprC
              (cdr p)) bindings))
     (define tys (make-list (length names) (NumT)))
     (type-check (AppC (LamC names tys body) rhss) tenv)]
    
    ;[_ (error 'type-check "QTUM: unhandled expression in type-check")]
    ))


; takes in user input and actually returns the final output
(define (top-interp [s : Sexp]) : String
  (define expr (parse s))
  (type-check expr base-tenv)
  (define sto (make-initial-store 2000))
  (define top-env (build-top-env sto))
  (serialize (interp (parse s) top-env sto)))


; initialized vecotr-based memory store used to simulate memory allocation in interp
(define (make-initial-store [memsize : Natural]) : Store
  (unless (>= memsize 2)
    (error 'make-initial-store "QTUM: memory too small"))
  (define v (make-vector memsize (ann (NumV 0) Value)))
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
   ;(make-binding '< (PrimOpV '< lt-prim) sto)
   (make-binding '<= (PrimOpV '<= leq-prim) sto)
   ;(make-binding 'equal? (PrimOpV 'equal? equal?-prim) sto)
   ;(make-binding 'strlen (PrimOpV 'strlen strlen-prim) sto)
   ;(make-binding 'substring(PrimOpV 'substring substring-prim) sto)
   ;(make-binding 'println (PrimOpV 'println  println-prim) sto)
   ;(make-binding 'read-num (PrimOpV 'read-num read-num-prim) sto)
   ;(make-binding 'read-str (PrimOpV 'read-str read-str-prim) sto)
   ;(make-binding 'num-eq? (PrimOpV 'num-eq? num-eq-prim) sto)
   ;(make-binding 'str-eq? (PrimOpV 'str-eq? str-eq-prim) sto)
   ;(make-binding 'seq (PrimOpV 'seq seq-prim) sto)
   ;(make-binding '++ (PrimOpV '++ concat-prim) sto)
   ;(make-binding 'make-array (PrimOpV 'make-array make-array-prim) sto)
   ;(make-binding 'array (PrimOpV 'array array-prim)    sto)
   ;(make-binding 'aref (PrimOpV 'aref aref-prim)     sto)
   ;(make-binding 'aset! (PrimOpV 'aset! aset!-prim)    sto)
   ;(make-binding 'error (PrimOpV 'error user-error-prim) sto)
   ;(make-binding 'null (NullV)  sto)
   (make-binding 'true (BoolV #t) sto)
   (make-binding 'false (BoolV #f) sto)))


; helps parse function parameters of different syntaxes into proper structure
(define (parse-param [p : Sexp]) : (Pairof Symbol Ty)
  (match p
    [(list (? symbol? id) ': tysexp)
     (cons (cast id Symbol) (parse-type tysexp))]

    [(list (? symbol? id:ty))
     (define pieces (string-split (symbol->string (cast id:ty Symbol)) ":"))
     (cond
       [(= (length pieces) 2)
        (define id-sym  (string->symbol (first  pieces)))
        (define ty-sym  (string->symbol (second pieces)))
        (cons id-sym (parse-type ty-sym))]
       [else (cons (cast id:ty Symbol) (NumT))])]

    [(? symbol? id)
     (cons (cast id Symbol) (NumT))]

    [_ (error 'parse "QTUM: bad param spec ~a" p)]))



; turns each binding from user into internal BindAnn struct
(define (parse-binding [b : Sexp]) : BindAnn
  (match b
    
    [(list (? symbol? id) ': tysexp '= rhs)
     (BindAnn id (parse-type tysexp) (parse rhs))]
    
    [(list (? symbol? id) '= rhs)
     (let ([pieces (string-split (symbol->string id) ":")])
       (if (= (length pieces) 2)
           (BindAnn (string->symbol (first pieces))
                    (parse-type (string->symbol (second pieces)))
                    (parse rhs))
           (BindAnn id (NumT) (parse rhs))))]
    [_ (error 'parse "QTUM: bad binding ~a" b)]))

; takes raw Sexpr and converts into AST
(define (parse [sexp : Sexp]) : ExprC
  (match sexp
    [(? real? n) (NumC n)]
    
    [(? string? s) (StringC s)]

    [(? symbol? s)
     (when (member s '(if with rec = => :))
       (error 'parse "QTUM: keyword used as identifier: ~a" s))
     (IdC s)]

    [(list 'if t c a) (IfC (parse t) (parse c) (parse a))]

    [(list (? symbol? id) ': tysexp '=> body)
     (LamC (list id) (list (parse-type tysexp)) (parse body))]
    
    [(list params ... '=> body)
     (define parsed  (map parse-param (cast params (Listof Sexp))))
     (define names   (map (lambda ([p : (Pairof Symbol Ty)]) : Symbol (car p)) parsed))
     (when (has-duplicates names)
       (error 'parse "QTUM: duplicate params ~a" names))
     (define ptys (map (lambda ([p : (Pairof Symbol Ty)]) : Ty (cdr p))  parsed))
     (LamC names ptys (parse body))]

    ;[(list '=> body)
     ;(LamC '() '() (parse body))]

    [(list 'with bindings ... body)
     (define b* (map parse-binding (cast bindings (Listof Sexp))))
     (define names (map (lambda ([b : BindAnn]) : Symbol (BindAnn-name b)) b*))
     (when (has-duplicates names)
       (error 'parse "QTUM: dup names ~a" names))
     (define tys  (map (lambda ([b : BindAnn]) : Ty     (BindAnn-ty  b)) b*))
     (define rhss (map (lambda ([b : BindAnn]) : ExprC  (BindAnn-rhs b)) b*))
     (AppC (LamC names tys (parse body)) rhss)]

    [(list 'rec bindings ... body)
     (define b*    (map parse-binding (cast bindings (Listof Sexp))))
     (define names (map BindAnn-name b*))
     (when (has-duplicates names)
       (error 'parse "QTUM: dup names in rec ~a" names))
     (RecC names
           (map BindAnn-ty  b*)
           (map BindAnn-rhs b*)
           (parse body))]

    [(list f args ...)
     (AppC (parse f) (map parse (cast args (Listof Sexp))))]

    [other (error 'parse "QTUM: syntax error ~e" other)]))


; makes sure parameter is symbol
;(define (validate-param [p : Any]) : Symbol
 ; (cond
  ;  [(symbol? p) p]
   ; [(null? p) (error 'parse-fundef "QTUM: empty list found in parameter")]
    ;[else (error 'parse-fundef "QTUM: param isnt a symbol ~e" p)]))


; takes in a store and the amount of space and returns index of memory allocation
(define (allocate [sto : Store] [n : Natural]) : Location
  (define header (vector-ref sto (ann 0 Natural)))
  (define first-free
    (match header
      [(NumV k)
       (if (and (integer? k) (exact-nonnegative-integer? k))
           k
           (error 'allocate "QTUM: header is not a natural number"))]
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
    (interp (AppC (LamC vars (map (lambda _ (NumT)) vars) body) exprs) env sto)] 

    ;[(SetC id rhs)
     ;(define loc (lookup-env env id))
     ;(define rhs-val (interp rhs env sto))
     ;(vector-set! sto loc rhs-val)
     ;(NullV)]
    
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

    [(LamC ps _ body) (CloV ps body env)]

    [(RecC names tys rhss body)
     (define locs
       (map (lambda ([nm : Symbol]) : Location
              (allocate sto 1))
            names))

     (define env* (append (map (lambda ([nm  : Symbol] [loc : Location]) : Binding
               (cons nm loc)) names locs) env))

     (for ([rhs rhss] [loc locs])
       (vector-set! sto loc (interp rhs env* sto)))
     (interp body env* sto)]

   [(IdC s) (fetch sto (lookup-env env s))]))


; takes a value and converts it into string representation
(define (serialize [v : Value]) : String
  (match v
    [(NumV  n) (~v n)]                    
    [(BoolV b) (if b "true" "false")]   
    [(StringV s) (format "~v" s)]           
    [(CloV _ _ _) "#<procedure>"]
    [(PrimOpV _ _) "#<primop>"]
    ;[(ArrayV _ _) "#<array>"]
    ;[(NullV) "null"]
    ))

#|
; converts qtum structures into actual string text
(define (value->string [v : Value]): String
  (match v
    [(NumV n) (~v n)]
    [(BoolV b) (if b "true" "false")]
    [(StringV s) s]
    [(CloV _ _ _) "#<procedure>"]
    [(PrimOpV _ _) "#<primop>"]))
|#

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

#|
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

; takes in list of values and returns value produced by last arg
(define (seq-prim [args : (Listof Value)] [sto : Store]): Value
  (cond [(null? args)
         (error 'seq "QTUM: 1 arg needed")]
        [else (last args)]))

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




(define (num-eq-prim [args : (Listof Value)] [sto : Store]) : Value
  (match args
    [(list (NumV a) (NumV b)) (BoolV (= a b))]
    [_ (error 'num-eq? "QTUM: num-eq? needs 2 numbers")]))


(define (str-eq-prim [args : (Listof Value)] [sto : Store]) : Value
  (match args
    [(list (StringV a) (StringV b)) (BoolV (string=? a b))]
    [_ (error 'str-eq? "QTUM: str-eq? needs 2 strings")]))


; takes in one argument and prints it 
(define (println-prim [args : (Listof Value)] [sto : Store]): Value
  (match args
    [(list v)
     (displayln (serialize v))
     (BoolV #t)]                          
    [_ (error 'println "QTUM: println takes one argument")]))

; takes in and reads a number from input
(define (read-num-prim [args : (Listof Value)] [sto : Store]) : Value
  (if (null? args)
      (begin
        (display "> ")
        (flush-output)
        (let ([r (read-line)])
          (cond
            [(string? r)
             (let ([maybe-num (string->number r)])
               (cond
                 [(real? maybe-num) (NumV maybe-num)]
                 [else (error 'read-num "QTUM: not a real number")]))]
            [else (error 'read-num "QTUM: reached EOF while reading")])))
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



; makes each of the args text and concats into one singular string
(define (concat-prim [args : (Listof Value)] [sto : Store]): Value
  (define pieces (map serialize args))
  (StringV (apply string-append pieces)))
|#
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
  (not (false? (check-duplicates (map (lambda (s) s) syms)))))

; takes in a symbol and makes sure it is legal
;(define (id? [s : Symbol]): Boolean
 ; (and (regexp-match? #px"^[A-Za-z][A-Za-z0-9_-]*$" (symbol->string s)) 
  ;     (not (member s '(if with = =>)))))


; *********** ALL TESTING ************************************************************************************

(check-equal? (top-interp '0) "0")
(check-equal? (top-interp '{(x) => x}) "#<procedure>")
(check-equal? (top-interp '+) "#<primop>")
(check-equal? (top-interp 'true) "true")
(check-equal? (top-interp 'false) "false")

; arithmetic
(check-equal? (top-interp '{+ 4 5}) "9")
(check-equal? (top-interp '{- 10 3}) "7")
(check-equal? (top-interp '{* 2 6}) "12")
(check-equal? (top-interp '{/ 8 2}) "4")
(check-equal? (top-interp '{<= 3 7}) "true")

(check-exn #px"QTUM" (lambda () (top-interp '{+ 1})))
(check-exn #px"QTUM" (lambda () (top-interp '{+ 1 2 3})))
(check-exn #px"QTUM" (lambda () (top-interp '{/ 1 0})))
(check-exn #px"QTUM" (lambda () (top-interp '{<= 1 "x"})))

; if / with 
(check-equal? (top-interp '{if true 1 0})  "1")
(check-equal? (top-interp '{if false 1 0}) "0")
(check-exn    #px"QTUM" (lambda () (top-interp '{if 5 1 0})))


(check-equal?
 (parse-binding '(x = 3))
 (BindAnn 'x (NumT) (NumC 3)))

(check-equal?
 (top-interp '{with [x = 3] [y = 4] {+ x y}})
 "7")

; edge case parser
(check-exn #px"QTUM" (lambda () (top-interp 'if)))
(check-exn #px"QTUM" (lambda () (top-interp '{{x x} => x})))
(check-exn #px"QTUM" (lambda () (top-interp '{})))

(check-exn #px"QTUM" (lambda () (top-interp '{with [x = 1] [x = 2] x})))

(check-exn #px"QTUM" (lambda () (top-interp '{((x ()) => x)})))
(check-exn #px"QTUM" (lambda () (top-interp '{((x 5) => x)})))

; new strcutrue for types
(check-equal? (parse-type 'num)           (NumT))
(check-equal? (parse-type '(num -> num))  (ArrowT (list (NumT)) (NumT)))
(check-equal? (parse-type '(num str -> bool))
              (ArrowT (list (NumT) (StrT)) (BoolT)))

;(displayln (read (open-input-string "([x:num] [y:str] => x)")))
(check-equal?
 (parse '([x:num] [y:str] => x))
 (LamC '(x y) (list (NumT) (StrT)) (IdC 'x)))

(check-equal? (parse-type '(num -> num)) (ArrowT (list (NumT)) (NumT)))
(check-equal? (parse-type '(num str -> bool)) (ArrowT (list (NumT) (StrT)) (BoolT)))

; recursion plus type checking
(check-equal?
 (top-interp
  '{rec [fact : {num -> num}
         = {{n : num}
            => {if {<= n 1}
                   1
                   {* n {fact {- n 1}}}}}]
       {fact 5}})
 "120")

(check-exn #px"QTUM"
           (lambda () (top-interp
                   '{rec [bad : {num -> num}
                          = {{s : str} => s}] 0})))

; errors coverage
(check-exn #px"QTUM: bad type"
  (lambda () (parse-type '"not-a-type")))

(check-exn #px"QTUM: unbound id"
  (lambda () (lookup-type '() 'foo)))

(check-exn #px"QTUM: branches differ"
  (lambda ()
    (type-check
     (IfC (IdC 'b)
          (NumC 5)
          (StringC "oops"))
     (list (cons 'b (BoolT))))))

(check-exn #px"QTUM: trying to call non-function"
  (lambda ()
    (type-check
     (AppC (NumC 5) (list (NumC 2)))
     '())))

(check-exn #px"QTUM: internal lamC length mismatch"
  (lambda ()
    (type-check
     (LamC '(x y) (list (NumT)) (IdC 'x))
     '())))

(check-equal?
 (type-check
  (WithC
   (list (cons 'x (NumC 3)))
   (AppC (IdC '+) (list (IdC 'x) (NumC 2))))
  base-tenv)
 (NumT))

(check-exn #px"QTUM: memory too small"
  (lambda () (make-initial-store 1)))


(check-exn #px"QTUM: bad binding"
  (lambda () (parse-binding '(= x 1)))) ; malformed — starts with '='

(check-exn #px"QTUM: duplicate params"
  (lambda () (parse '([x:num] [x:num] => x))))

(check-equal?
 (parse '(x : num => x))
 (LamC '(x) (list (NumT)) (IdC 'x)))

(check-equal?
 (parse '(=> 42))
 (LamC '() '() (NumC 42)))

(check-exn #px"QTUM: dup names in rec"
  (lambda () (parse '(rec [x : num = 1] [x : num = 2] x))))

(let ([sto (make-initial-store 3)])
   (vector-set! sto (ann 0 Natural) (NumV -1))
  (check-exn #px"QTUM: header is not a natural number"
    (lambda () (allocate sto 1))))

(let ([sto (make-initial-store 3)])
  (vector-set! sto (ann 0 Natural) (BoolV #t))
  (check-exn #px"QTUM: corrupted header"
    (lambda () (allocate sto 1))))

(define (fresh-sto-env)
  (let ([sto (make-initial-store 20)])
    (values sto (build-top-env sto))))

(let-values ([(sto env) (fresh-sto-env)])
  (check-exn #px"QTUM: non boolean value"
    (lambda () (interp (IfC (NumC 5) (NumC 1) (NumC 0)) env sto))))

(define with-wrong-arity
  (WithC
   (list (cons 'f (LamC '(x y) '() (NumC 0))))
   (AppC (IdC 'f) (list (NumC 1)))))

(let-values ([(sto env) (fresh-sto-env)])
  (check-exn #px"QTUM: wrong amount of args"
    (lambda () (interp with-wrong-arity env sto))))

(let-values ([(sto env) (fresh-sto-env)])
  (check-exn #px"QTUM: attempt to call something that isnt a function"
    (lambda () (interp (AppC (NumC 5) (list (NumC 1))) env sto))))

(let-values ([(sto env) (fresh-sto-env)])
  (check-equal? (interp (StringC "hi") env sto)
                (StringV "hi")))

(check-exn #px"QTUM: out of memory"
  (lambda ()
    (allocate (make-initial-store 3) 3)))

(define (fresh-store) (make-initial-store 10))

(check-exn #px"QTUM: adding expects two numbers"
  (lambda () (add-prim (list (NumV 1)) (fresh-store))))

(check-exn #px"QTUM: subtract needs 2 numbers"
  (lambda () (sub-prim (list (NumV 5) (StringV "oops")) (fresh-store))))

(check-exn #px"QTUM: multiplying needs 2 numbers"
  (lambda () (mul-prim (list (NumV 2) (NumV 3) (NumV 4)) (fresh-store))))

(check-exn #px"QTUM: division needs 2 numbers"
  (lambda () (div-prim (list (NumV 8)) (fresh-store))))

(check-exn #px"QTUM: leq-prim needs 2 numbers"
  (lambda () (leq-prim (list (StringV "x") (NumV 3)) (fresh-store))))

(check-exn #px"QTUM: unbound identifier"
  (lambda () (lookup-env '() 'foo)))


; others
(check-equal? (parse-param 'foo)
              (cons 'foo (NumT)))

(check-equal?
 (parse '(=> 42))
 (LamC '() '() (NumC 42)))

(check-equal? (top-interp '"hello") "\"hello\"")

(check-equal? (top-interp '{with [x = 1] {+ x 2}}) "3")

(check-equal?
 (parse-binding '(foo:num = 1))
 (BindAnn 'foo (NumT) (NumC 1)))