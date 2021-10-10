#lang plai

(require test-engine/racket-tests)

(define-type RVCFWAE
  [rvcfwae-num (n number?)]
  [rvcfwae-add (lhs RVCFWAE?) (rhs RVCFWAE?)]
  [rvcfwae-sub (lhs RVCFWAE?) (rhs RVCFWAE?)]
  [rvcfwae-with (name symbol?) (named-expression RVCFWAE?) (body RVCFWAE?)]
  [rvcfwae-id (name symbol?)]
  [rvcfwae-refun (param symbol?) (body RVCFWAE?)]
  [rvcfwae-fun (param symbol?) (body RVCFWAE?)]
  [rvcfwae-app (fun-expr RVCFWAE?) (arg-expr RVCFWAE?)]
  [rvcfwae-if0 (condition RVCFWAE?) (expr0 RVCFWAE?) (expr1 RVCFWAE?)]
  [rvcfwae-setv (name symbol?) (val RVCFWAE?)]
  [rvcfwae-seqn (expr RVCFWAE?) (val RVCFWAE?)])

(define-type RVCFAE
  [num (n number?)]
  [add (lhs RVCFAE?) (rhs RVCFAE?)]
  [sub (lhs RVCFAE?) (rhs RVCFAE?)]
  [id (name symbol?)]
  [refun (param symbol?) (body RVCFAE?)]
  [fun (param symbol?) (body RVCFAE?)]
  [app (fun-expr RVCFAE?) (arg-expr RVCFAE?)]
  [if0 (condition RVCFAE?) (expr0 RVCFAE?) (expr1 RVCFAE?)]
  [setv (name symbol?) (val RVCFAE?)]
  [seqn (expr RVCFAE?) (val RVCFAE?)])

(define-type RVCFAE-Value
  [numV (n number?)]
  [closureV (param symbol?) (body RVCFAE?) (env Env?)]
  [refclosV (param symbol?) (body RVCFAE?) (env Env?)])

(define-type Env
  [mtSub]
  [aSub (name symbol?) (location number?) (env Env?)])

(define-type Store
  [mtSto]
  [aSto (location number?) (val RVCFAE-Value?) (store Store?)])

(define-type ValuexStore
  [vxs (val RVCFAE-Value?) (store Store?)])

(define (parse sexp)
  (cond [(number? sexp) (rvcfwae-num sexp)]
        [(symbol? sexp) (rvcfwae-id sexp)]
        [(list? sexp)
         (case (first sexp)
           [(+) (rvcfwae-add (parse (second sexp)) (parse (third sexp)))]
           [(-) (rvcfwae-sub (parse (second sexp)) (parse (third sexp)))]
           [(with) (rvcfwae-with (first (second sexp)) (parse (second (second sexp))) (parse (third sexp)))]
           [(fun) (rvcfwae-fun (first (second sexp)) (parse (third sexp)))]
           [(refun) (rvcfwae-refun (first (second sexp)) (parse (third sexp)))]
           [(if0) (rvcfwae-if0 (parse (second sexp)) (parse (third sexp)) (parse (fourth sexp)))]
           [(setv) (rvcfwae-setv (second sexp) (parse (third sexp)))]
           [(seqn) (rvcfwae-seqn (parse (second sexp)) (parse (third sexp)))]
           (else
            (rvcfwae-app (parse (first sexp)) (parse (second sexp)))))]))

(define (preprocess expr)
  (type-case RVCFWAE expr
    [rvcfwae-num (n) (num n)]
    [rvcfwae-add (l r) (add (preprocess l) (preprocess r))]
    [rvcfwae-sub (l r) (sub (preprocess l) (preprocess r))]
    [rvcfwae-with (bound-id named-expr bound-body) (app (fun bound-id (preprocess bound-body)) (preprocess named-expr))]
    [rvcfwae-id (v) (id v)]
    [rvcfwae-refun (param body) (refun param (preprocess body))]
    [rvcfwae-fun (param body) (fun param (preprocess body))]
    [rvcfwae-app (fun-expr arg-expr) (app (preprocess fun-expr) (preprocess arg-expr))]
    [rvcfwae-if0 (condition expr0 expr1) (if0 (preprocess condition) (preprocess expr0) (preprocess expr1))]
    [rvcfwae-setv (name val) (setv name (preprocess val))]
    [rvcfwae-seqn (expr val) (seqn (preprocess expr) (preprocess val))]))

(define (interp expr env store)
  (type-case RVCFAE expr
    
    [num (n) (vxs (numV n) store)]
    
    [add (l-expr r-expr)
         (type-case ValuexStore (interp l-expr env store)
           [vxs (l-val l-store)
                (type-case ValuexStore (interp r-expr env l-store)
                  [vxs (r-val r-store)
                       (vxs (num+ l-val r-val) r-store)])])]
    
    [sub (l-expr r-expr)
         (type-case ValuexStore (interp l-expr env store)
           [vxs (l-val l-store)
                (type-case ValuexStore (interp r-expr env l-store)
                  [vxs (r-val r-store)
                       (vxs (num- l-val r-val) r-store)])])]
    
    [id (v) (vxs (lookup v env store) store)]
    
    [refun (param body) (vxs (refclosV param body env) store)]
    
    [fun (param body) (vxs (closureV param body env) store)]
    
    [app (fun-expr arg-expr)
         (type-case ValuexStore (interp fun-expr env store)
           [vxs (fun-val fun-store)
                (type-case RVCFAE-Value fun-val
                  [closureV (fun-param fun-body fun-env)
                            (type-case ValuexStore (interp arg-expr env fun-store)
                              [vxs (arg-val arg-store)
                                   (local ([define new-loc (next-location arg-store)])
                                     (interp fun-body
                                             (aSub fun-param new-loc fun-env)
                                             (aSto new-loc arg-val arg-store)))])]
                  
                  [refclosV (fun-param fun-body fun-env)
                            (local ([define arg-loc (env-lookup (id-name arg-expr) env)])
                              (interp fun-body (aSub fun-param arg-loc fun-env) fun-store))]
                  [numV (_) (error `interp "trying to apply a number")])]
           )]
    
    
    
    
    [if0 (condition-expr expr0 expr1)
         (type-case ValuexStore (interp condition-expr env store)
           [vxs (condition-val store-1)
                (if (num-zero? condition-val)
                    (interp expr0 env store-1)
                    (interp expr1 env store-1))])]
    
    [setv (name val)
          (type-case ValuexStore (interp val env store)
            [vxs (val-val val-store)
                 (local ([define the-loc (env-lookup name env)])
                   (vxs val-val (aSto the-loc val-val val-store)))])]
    
    [seqn (expr val)
          (type-case ValuexStore (interp expr env store)
            [vxs (expr-val expr-store)
                 (interp val env expr-store)])]))

(define (run sexp)
  (vxs-val (interp (preprocess (parse sexp)) (mtSub) (mtSto))))

(define (num+ l r)
  (numV (+ (numV-n l) (numV-n r))))

(define (num- l r)
  (numV (- (numV-n l) (numV-n r))))

(define (num-zero? number)
  (eq? (numV-n number) 0))

(define (env-lookup name env)
  (type-case Env env
    [mtSub () (error 'env-lookup "no binding for identifier")]
    [aSub (bound-name location rest-env)
          (if (symbol=? bound-name name)
              location
              (env-lookup name rest-env))]))

(define (store-lookup loc-index sto)
  (type-case Store sto
    [mtSto () (error 'store-lookup "no value at location")]
    [aSto (location val rest-store)
          (if (= location loc-index)
              val
              (store-lookup loc-index rest-store))]))

(define next-location
  (local ([define last-loc (box -1)])
    (lambda (store)
      (begin (set-box! last-loc (+ 1 (unbox last-loc)))
             (unbox last-loc)))))

(define (lookup name env store) (store-lookup (env-lookup name env) store))

(check-expect (parse '((fun (x) (+ x 4)) 5)) (rvcfwae-app (rvcfwae-fun 'x (rvcfwae-add (rvcfwae-id 'x) (rvcfwae-num 4))) (rvcfwae-num 5)))

(check-expect
 (parse '(with (double (fun (x) (+ x x))) (+ (double 10) (double 5))))
 (rvcfwae-with 'double (rvcfwae-fun 'x (rvcfwae-add (rvcfwae-id 'x) (rvcfwae-id 'x))) (rvcfwae-add (rvcfwae-app (rvcfwae-id 'double) (rvcfwae-num 10)) (rvcfwae-app (rvcfwae-id 'double) (rvcfwae-num 5)))))

(check-expect (parse '(fun (x) x)) (rvcfwae-fun 'x (rvcfwae-id 'x)))

(check-expect
 (parse '(setv a 0))
 (rvcfwae-setv 'a (rvcfwae-num 0)))

(check-expect
 (parse '(refun (a) a))
 (rvcfwae-refun 'a (rvcfwae-id 'a)))

(check-expect (run '(+ 3 4)) (numV 7))

(check-expect (run '3) (numV 3))
(check-expect (run '(- 3 4)) (numV -1))
(check-expect (run '(+ (+ 1 1) 1)) (numV 3))
(check-expect (run '(+ (- 3 4) 7)) (numV 6))

(check-expect (run '5) (numV 5))
(check-expect (run '(+ 5 5 )) (numV 10))

(check-expect (run '(with (x 5) x)) (numV 5))

(check-expect (run '(with (x (+ 5 5)) x)) (numV 10))
(check-expect (run '(with (x 5) (+ x x))) (numV 10))
(check-expect (run '(with (x (+ 5 5)) (+ x x))) (numV 20))

(check-expect (run '(with (x (+ 5 5)) (with (y (- x 3)) (+ y y)))) (numV 14))
(check-expect (run '(with (x 5) (with (y (- x 3)) (+ y y )))) (numV 4))
(check-expect (run '(with (x 5) (+ x (with (x 3) 10)))) (numV 15))
(check-expect (run '(with (x 5) (+ x (with (y 3) x)))) (numV 10))
(check-expect (run '(with (x 5) (with (y x) y))) (numV 5))
(check-expect (run '(with (x 5) (with (x x) x))) (numV 5))

(check-expect (run
               '(with (x 3)
                      (with (f (fun (y) (+ x y)))
                            (with (x 5)
                                  (f 4)))))
              (numV 7))

(check-expect (run '(if0 0 1 2)) (numV 1))
(check-expect (run '(if0 1 1 2)) (numV 2))

(check-expect
 (run '(with (x 0) (seqn (setv x 1) x)))
 (numV 1))

(check-expect
 (run '(with (x 0) (seqn ((refun (y) (setv y 1)) x) x)))
 (numV 1))

(check-expect
 (run '(with (x 0) (seqn ((fun (y) (setv y 1)) x) x)))
 (numV 0))

(test)
