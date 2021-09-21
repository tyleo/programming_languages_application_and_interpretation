#lang plai

(require test-engine/racket-tests)

(define-type RFWAE
  [rfwae-num (n number?)]
  [rfwae-add (lhs RFWAE?) (rhs RFWAE?)]
  [rfwae-sub (lhs RFWAE?) (rhs RFWAE?)]
  [rfwae-with (name symbol?) (named-expr RFWAE?) (body RFWAE?)]
  [rfwae-id (name symbol?)]
  [rfwae-fun (param symbol?) (body RFWAE?)]
  [rfwae-app (fun-expr RFWAE?) (arg-expr RFWAE?)]
  [rfwae-if0 (condition RFWAE?) (expr0 RFWAE?) (expr1 RFWAE?)]
  [rfwae-rec (name symbol?) (named-expr RFWAE?) (body RFWAE?)])

(define-type RCFAE
  [num (n number?)]
  [add (lhs RCFAE?) (rhs RCFAE?)]
  [sub (lhs RCFAE?) (rhs RCFAE?)]
  [id (name symbol?)]
  [fun (param symbol?) (body RCFAE?)]
  [app (fun-expr RCFAE?) (arg-expr RCFAE?)]
  [if0 (condition RCFAE?) (expr0 RCFAE?) (expr1 RCFAE?)]
  [rec (name symbol?) (named-expr RCFAE?) (body RCFAE?)])

(define-type RCFAE-Value
  [numV (n number?)]
  [closureV (param symbol?) (body RCFAE?) (env Env?)]
  [exprV (expr RCFAE?) (env Env?) (cache boxed-boolean/RCFAE-Value?)])

(define (boxed-boolean/RCFAE-Value? v)
  (and (box? v)
       (or (boolean? (unbox v))
           (numV? (unbox v))
           (closureV? (unbox v)))))

(define (boxed-RCFAE-Value? v)
  (and (box? v) (RCFAE-Value? (unbox v))))

(define-type Env
  [mtSub]
  [aSub (name symbol?) (value RCFAE-Value?) (env Env?)]
  [aRecSub (name symbol?) (value boxed-RCFAE-Value?) (env Env?)])

(define (cyclically-bind-and-interp bound-id named-expr env)
  (local ([define value-holder (box (numV 1729))]
          [define new-env (aRecSub bound-id value-holder env)]
          [define named-expr-val (interp named-expr new-env)])
    (begin
      (set-box! value-holder named-expr-val)
      new-env)))

(define (parse sexp)
  (cond [(number? sexp) (rfwae-num sexp)]
        [(symbol? sexp) (rfwae-id sexp)]
        [(list? sexp)
         (case (first sexp)
           [(+) (rfwae-add (parse (second sexp)) (parse (third sexp)))]
           [(-) (rfwae-sub (parse (second sexp)) (parse (third sexp)))]
           [(with) (rfwae-with (first (second sexp)) (parse (second (second sexp))) (parse (third sexp)))]
           [(fun) (rfwae-fun (first (second sexp)) (parse (third sexp)))]
           [(if0) (rfwae-if0 (parse (second sexp)) (parse (third sexp)) (parse (fourth sexp)))]
           [(rec) (rfwae-rec (first (second sexp)) (parse (second (second sexp))) (parse (third sexp)))]
           (else
            (rfwae-app (parse (first sexp)) (parse (second sexp)))))]))

(define (preprocess expr)
  (type-case RFWAE expr
    [rfwae-num (n) (num n)]
    [rfwae-add (l r) (add (preprocess l) (preprocess r))]
    [rfwae-sub (l r) (sub (preprocess l) (preprocess r))]
    [rfwae-with (bound-id named-expr bound-body) (app (fun bound-id (preprocess bound-body)) (preprocess named-expr))]
    [rfwae-id (v) (id v)]
    [rfwae-fun (param body) (fun param (preprocess body))]
    [rfwae-app (fun-expr arg-expr) (app (preprocess fun-expr) (preprocess arg-expr))]
    [rfwae-if0 (condition expr0 expr1) (if0 (preprocess condition) (preprocess expr0) (preprocess expr1))]
    [rfwae-rec (name named-expr body) (rec name (preprocess named-expr) (preprocess body))]))

(define (interp expr env)
  (type-case RCFAE expr
    [num (n) (numV n)]
    [add (l r) (num+ (interp l env) (interp r env))]
    [sub (l r) (num- (interp l env) (interp r env))]
    [id (v) (lookup v env)]
    [fun (bound-id bound-body) (closureV bound-id bound-body env)]
    [app (fun-expr arg-expr)
         (local ([define fun-val (strict (interp fun-expr env))]
                 [define arg-val (exprV arg-expr env (box false))])
           (interp (closureV-body fun-val)
                   (aSub (closureV-param fun-val)
                         arg-val
                         (closureV-env fun-val))))]
    [if0 (condition expr0 expr1)
         (if (num-zero? (interp condition env))
             (interp expr0 env)
             (interp expr1 env))]
    [rec (name named-expr body) (interp body (cyclically-bind-and-interp name named-expr env))]))

(define (run sexp)
  (strict (interp (preprocess (parse sexp)) (mtSub))))

(define (num+ l r)
  (numV (+ (numV-n (strict l)) (numV-n (strict r)))))

(define (num- l r)
  (numV (- (numV-n (strict l)) (numV-n (strict r)))))

(define (num-zero? number)
  (eq? (numV-n (strict number)) 0))

(define (strict e)
  (type-case RCFAE-Value e
    [exprV (expr env cache)
           (if (boolean? (unbox cache))
               (local [(define the-value (strict (interp expr env)))]
                 (begin
                   (set-box! cache the-value)
                   the-value))
               (unbox cache))]
    [else e]))

(define (lookup name env)
  (type-case Env env
    [mtSub () (error 'lookup "no binding for identifier")]
    [aSub (bound-name bound-value rest-ds)
          (if (symbol=? bound-name name)
              bound-value
              (lookup name rest-ds))]
    [aRecSub (bound-name boxed-bound-value rest-env)
             (if (symbol=? bound-name name)
                 (unbox boxed-bound-value)
                 (lookup name rest-env))]))

(check-expect (parse '((fun (x) (+ x 4)) 5)) (rfwae-app (rfwae-fun 'x (rfwae-add (rfwae-id 'x) (rfwae-num 4))) (rfwae-num 5)))

(check-expect
 (parse '(with (double (fun (x) (+ x x))) (+ (double 10) (double 5))))
 (rfwae-with 'double (rfwae-fun 'x (rfwae-add (rfwae-id 'x) (rfwae-id 'x))) (rfwae-add (rfwae-app (rfwae-id 'double) (rfwae-num 10)) (rfwae-app (rfwae-id 'double) (rfwae-num 5)))))

(check-expect (parse '(fun (x) x)) (rfwae-fun 'x (rfwae-id 'x)))

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

(check-expect (run
               '(rec (sum (fun (n)
                               (if0 n 0 (+ n (sum (- n 1))))))
                  (sum 5)))
              (numV 15))

(check-expect (run
               '(rec (sum (fun (n)
                               (if0 n 0 (+ n (sum (- n 1))))))
                  (sum 1)))
              (numV 1))

(test)
