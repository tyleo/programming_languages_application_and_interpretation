#lang plai

(require test-engine/racket-tests)

(define-type BCFWAE
  [fwae-num (n number?)]
  [fwae-add (lhs BCFWAE?) (rhs BCFWAE?)]
  [fwae-sub (lhs BCFWAE?) (rhs BCFWAE?)]
  [fwae-with (name symbol?) (named-expression BCFWAE?) (body BCFWAE?)]
  [fwae-id (name symbol?)]
  [fwae-fun (param symbol?) (body BCFWAE?)]
  [fwae-app (fun-expr BCFWAE?) (arg-expr BCFWAE?)]
  [fwae-if0 (condition BCFWAE?) (expr0 BCFWAE?) (expr1 BCFWAE?)]
  [fwae-newbox (expr BCFWAE?)]
  [fwae-setbox (expr BCFWAE?) (val BCFWAE?)]
  [fwae-openbox (expr BCFWAE?)]
  [fwae-seqn (expr BCFWAE?) (val BCFWAE?)])

(define-type BCFAE
  [num (n number?)]
  [add (lhs BCFAE?) (rhs BCFAE?)]
  [sub (lhs BCFAE?) (rhs BCFAE?)]
  [id (name symbol?)]
  [fun (param symbol?) (body BCFAE?)]
  [app (fun-expr BCFAE?) (arg-expr BCFAE?)]
  [if0 (condition BCFAE?) (expr0 BCFAE?) (expr1 BCFAE?)]
  [newbox (expr BCFWAE?)]
  [setbox (expr BCFWAE?) (val BCFWAE?)]
  [openbox (expr BCFWAE?)]
  [seqn (expr BCFWAE?) (val BCFWAE?)])

(define-type BCFAE-Value
  [numV (n number?)]
  [closureV (param symbol?) (body BCFAE?) (env Env?)]
  [boxV (location number?)])

(define-type Env
  [mtSub]
  [aSub (name symbol?) (location number?) (env Env?)])

(define-type Store
  [mtSto]
  [aSto (location number?) (val BCFAE-Value?) (store Store?)])

(define-type ValuexStore
  [vxs (val BCFAE-Value?) (store Store?)])

(define (parse sexp)
  (cond [(number? sexp) (fwae-num sexp)]
        [(symbol? sexp) (fwae-id sexp)]
        [(list? sexp)
         (case (first sexp)
           [(+) (fwae-add (parse (second sexp)) (parse (third sexp)))]
           [(-) (fwae-sub (parse (second sexp)) (parse (third sexp)))]
           [(with) (fwae-with (first (second sexp)) (parse (second (second sexp))) (parse (third sexp)))]
           [(fun) (fwae-fun (first (second sexp)) (parse (third sexp)))]
           [(if0) (fwae-if0 (parse (second sexp)) (parse (third sexp)) (parse (fourth sexp)))]
           [(newbox) (fwae-newbox (parse (second sexp)))]
           [(setbox) (fwae-setbox (parse (second sexp)) (parse (third sexp)))]
           [(openbox) (fwae-openbox (parse (second sexp)))]
           [(seqn) (fwae-seqn (parse (second sexp)) (parse (third sexp)))]
           (else
            (fwae-app (parse (first sexp)) (parse (second sexp)))))]))

(define (preprocess expr)
  (type-case BCFWAE expr
    [fwae-num (n) (num n)]
    [fwae-add (l r) (add (preprocess l) (preprocess r))]
    [fwae-sub (l r) (sub (preprocess l) (preprocess r))]
    [fwae-with (bound-id named-expr bound-body) (app (fun bound-id (preprocess bound-body)) (preprocess named-expr))]
    [fwae-id (v) (id v)]
    [fwae-fun (param body) (fun param (preprocess body))]
    [fwae-app (fun-expr arg-expr) (app (preprocess fun-expr) (preprocess arg-expr))]
    [fwae-if0 (condition expr0 expr1) (if0 (preprocess condition) (preprocess expr0) (preprocess expr1))]
    [fwae-newbox (expr) (newbox expr)]
    [fwae-setbox (expr val) (setbox expr val)]
    [fwae-openbox (expr) (openbox expr)]
    [fwae-seqn (expr val) (seqn expr val)]))

(define (interp expr env store)
  (type-case BCFAE expr
    
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
    
    [fun (bound-id bound-body) (vxs (closureV bound-id bound-body env) store)]
    
    [app (fun-expr arg-expr)
         (type-case ValuexStore (interp fun-expr env store)
           [vxs (fun-val fun-store)
                (type-case ValuexStore (interp arg-expr env fun-store)
                  [vxs (arg-val arg-store)
                       (local ([define new-loc (next-location arg-store)])
                         (interp (closureV-body fun-val)
                                 (aSub (closureV-param fun-val)
                                       new-loc
                                       (closureV-env fun-val))
                                 (aSto new-loc arg-val arg-store)))])])]
    
    [if0 (condition-expr expr0 expr1)
         (type-case ValuexStore (interp condition-expr env store)
           [vxs (condition-val store-1)
                (if (num-zero? condition-val)
                    (interp expr0 env store-1)
                    (interp expr1 env store-1))])]
    
    [newbox (expr)
            (type-case ValuexStore (interp expr env store)
              [vxs (expr-val expr-store)
                   (local ([define new-loc (next-location expr-store)])
                     (vxs (boxV new-loc)
                          (aSto new-loc expr-val expr-store)))])]
    
    [setbox (expr val)
            (type-case ValuexStore (interp expr env store)
              [vxs (expr-val expr-store)
                   (type-case ValuexStore (interp val env expr-store)
                     [vxs (val-val val-store)
                          (aSto (boxV-location expr-val) val-val val-store)])])]
    
    [openbox (expr)
             (type-case ValuexStore (interp expr env store)
               [vxs (expr-val expr-store)
                    (vxs (store-lookup (boxV-location expr-val) expr-store)
                         expr-store)])]
    
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

(check-expect (parse '((fun (x) (+ x 4)) 5)) (fwae-app (fwae-fun 'x (fwae-add (fwae-id 'x) (fwae-num 4))) (fwae-num 5)))

(check-expect
 (parse '(with (double (fun (x) (+ x x))) (+ (double 10) (double 5))))
 (fwae-with 'double (fwae-fun 'x (fwae-add (fwae-id 'x) (fwae-id 'x))) (fwae-add (fwae-app (fwae-id 'double) (fwae-num 10)) (fwae-app (fwae-id 'double) (fwae-num 5)))))

(check-expect (parse '(fun (x) x)) (fwae-fun 'x (fwae-id 'x)))

(check-expect
 (parse '(newbox 0))
 (fwae-newbox (fwae-num 0)))

(check-expect
 (parse '(setbox (newbox 0) 1))
 (fwae-setbox (fwae-newbox (fwae-num 0)) (fwae-num 1)))

(check-expect
 (parse '(openbox (newbox 0)))
 (fwae-openbox (fwae-newbox (fwae-num 0))))

(check-expect
 (parse '(with (x (newbox 0)) (seqn (setbox x 0) (openbox x))))
 (fwae-with 'x (fwae-newbox (fwae-num 0)) (fwae-seqn (fwae-setbox (fwae-id 'x) (fwae-num 0)) (fwae-openbox (fwae-id 'x)))))

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

(test)
