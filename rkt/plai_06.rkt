#lang plai

(require test-engine/racket-tests)

(define-type FWAE
  [fwae-num (n number?)]
  [fwae-add (lhs FWAE?) (rhs FWAE?)]
  [fwae-sub (lhs FWAE?) (rhs FWAE?)]
  [fwae-with (name symbol?) (named-expression FWAE?) (body FWAE?)]
  [fwae-id (name symbol?)]
  [fwae-fun (param symbol?) (body FWAE?)]
  [fwae-app (fun-expr FWAE?) (arg-expr FWAE?)])

(define-type FAE
  [num (n number?)]
  [add (lhs FAE?) (rhs FAE?)]
  [sub (lhs FAE?) (rhs FAE?)]
  [id (name symbol?)]
  [fun (param symbol?) (body FAE?)]
  [app (fun-expr FAE?) (arg-expr FAE?)])

(define-type FAE-Value
  [numV (n number?)]
  [closureV (param symbol?) (body FAE?) (ds DefrdSub?)])

(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (value FAE-Value?) (ds DefrdSub?)])

(define (parse sexp)
  (cond [(number? sexp) (fwae-num sexp)]
        [(symbol? sexp) (fwae-id sexp)]
        [(list? sexp)
         (case (first sexp)
           [(+) (fwae-add (parse (second sexp)) (parse (third sexp)))]
           [(-) (fwae-sub (parse (second sexp)) (parse (third sexp)))]
           [(with) (fwae-with (first (second sexp)) (parse (second (second sexp))) (parse (third sexp)))]
           [(fun) (fwae-fun (first (second sexp)) (parse (third sexp)))]
           (else
            (fwae-app (parse (first sexp)) (parse (second sexp)))))]))

(define (preprocess expr)
  (type-case FWAE expr
    [fwae-num (n) (num n)]
    [fwae-add (l r) (add (preprocess l) (preprocess r))]
    [fwae-sub (l r) (sub (preprocess l) (preprocess r))]
    [fwae-with (bound-id named-expr bound-body) (app (fun bound-id (preprocess bound-body)) (preprocess named-expr))]
    [fwae-id (v) (id v)]
    [fwae-fun (param body) (fun param (preprocess body))]
    [fwae-app (fun-expr arg-expr) (app (preprocess fun-expr) (preprocess arg-expr))]))

(define (interp expr ds)
  (type-case FAE expr
    [num (n) (numV n)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [id (v) (lookup v ds)]
    [fun (bound-id bound-body) (closureV bound-id bound-body ds)]
    [app (fun-expr arg-expr)
         (local ([define fun-val (interp fun-expr ds)])
           (interp (closureV-body fun-val)
                   (aSub (closureV-param fun-val)
                         (interp arg-expr ds)
                         (closureV-ds fun-val))))]))

(define (run sexp)
  (interp (preprocess (parse sexp)) (mtSub)))

(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "no binding for identifier")]
    [aSub (bound-name bound-value rest-ds)
          (if (symbol=? bound-name name)
              bound-value
              (lookup name rest-ds))]))

(define (num+ l r)
  (numV (+ (numV-n l) (numV-n r))))

(define (num- l r)
  (numV (- (numV-n l) (numV-n r))))

(check-expect (parse '((fun (x) (+ x 4)) 5)) (fwae-app (fwae-fun 'x (fwae-add (fwae-id 'x) (fwae-num 4))) (fwae-num 5)))

(check-expect
 (parse '(with (double (fun (x) (+ x x))) (+ (double 10) (double 5))))
 (fwae-with 'double (fwae-fun 'x (fwae-add (fwae-id 'x) (fwae-id 'x))) (fwae-add (fwae-app (fwae-id 'double) (fwae-num 10)) (fwae-app (fwae-id 'double) (fwae-num 5)))))

(check-expect (parse '(fun (x) x)) (fwae-fun 'x (fwae-id 'x)))

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

(test)
