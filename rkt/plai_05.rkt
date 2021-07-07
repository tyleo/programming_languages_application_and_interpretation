#lang plai

(require test-engine/racket-tests)

(define-type F1WAE
  [num (n number?)]
  [add (lhs F1WAE?) (rhs F1WAE?)]
  [sub (lhs F1WAE?) (rhs F1WAE?)]
  [with (name symbol?) (named-expression F1WAE?) (body F1WAE?)]
  [id (name symbol?)]
  [app (fun-name symbol?) (arg F1WAE?)])

(define-type FunDef
  [fundef (fun-name symbol?) (arg-name symbol?) (body F1WAE?)])

(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (value number?) (ds DefrdSub?)])

(define (subst expr sub-id val)
  (type-case F1WAE expr
    [num (n) expr]
    [add (l r) (add (subst l sub-id val) (subst r sub-id val))]
    [sub (l r) (sub (subst l sub-id val) (subst r sub-id val))]
    [with (bound-id named-expr bound-body)
          (if (symbol=? bound-id sub-id)
              (with bound-id
                    (subst named-expr sub-id val)
                    bound-body)
              (with bound-id
                    (subst named-expr sub-id val)
                    (subst bound-body sub-id val)))]
    [id (v) (if (symbol=? v sub-id) val expr)]
    [app (fun-name arg) (app fun-name (subst arg sub-id val))]))

(define (parse sexp)
  (cond [(number? sexp) (num sexp)]
        [(symbol? sexp) (id sexp)]
        [(list? sexp)
         (case (first sexp)
           [(+) (add (parse (second sexp)) (parse (third sexp)))]
           [(-) (sub (parse (second sexp)) (parse (third sexp)))]
           [(with) (with (first (second sexp)) (parse (second (second sexp))) (parse (third sexp)))]
           [else (cond
                   [(symbol? (first sexp)) (app (first sexp) (parse (second sexp)))])])]))

(define (parse-fundef sexp)
  (fundef (first sexp) (second sexp) (parse (third sexp))))

(define (lookup-fundef fun-name fundefs)
  (cond
    [(empty? fundefs) (error fun-name "function not found")]
    [(symbol=? fun-name (fundef-fun-name (first fundefs))) (first fundefs)]
    [else (lookup-fundef fun-name (rest fundefs))]))

(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "no binding for identifier")]
    [aSub (bound-name bound-value rest-ds)
          (if (symbol=? bound-name name)
              bound-value
              (lookup name rest-ds))]))

(define (interp expr fun-defs ds)
  (type-case F1WAE expr
    [num (n) n]
    [add (l r) (+ (interp l fun-defs ds) (interp r fun-defs ds))]
    [sub (l r) (- (interp l fun-defs ds) (interp r fun-defs ds))]
    [with (bound-id named-expr bound-body)
          (interp bound-body fun-defs (aSub bound-id (interp named-expr fun-defs ds) ds))]
    [id (v) (lookup v ds)]
    [app (fun-name arg-expr)
         (local ([define the-fun-def (lookup-fundef fun-name fun-defs)])
           (interp
            (fundef-body the-fun-def)
            fun-defs
            (aSub (fundef-arg-name the-fun-def) (interp arg-expr fun-defs ds) (mtSub))))]))

(check-expect (interp (parse '3) '() (mtSub)) 3)
(check-expect (interp (parse '(+ 3 4)) '() (mtSub)) 7)
(check-expect (interp (parse '(+ (- 3 4) 7)) '() (mtSub)) 6)

(check-expect (interp (parse '5) '() (mtSub)) 5)
(check-expect (interp (parse '(+ 5 5 )) '() (mtSub)) 10)

(check-expect (interp (parse '(with (x 5) x)) '() (mtSub)) 5)

(check-expect (interp (parse '(with (x (+ 5 5)) x)) '() (mtSub)) 10)
(check-expect (interp (parse '(with (x 5) (+ x x))) '() (mtSub)) 10)
(check-expect (interp (parse '(with (x (+ 5 5)) (+ x x))) '() (mtSub)) 20)

(check-expect (interp (parse '(with (x (+ 5 5)) (with (y (- x 3)) (+ y y)))) '() (mtSub)) 14)
(check-expect (interp (parse '(with (x 5) (with (y (- x 3)) (+ y y )))) '() (mtSub)) 4)
(check-expect (interp (parse '(with (x 5) (+ x (with (x 3) 10)))) '() (mtSub)) 15)
(check-expect (interp (parse '(with (x 5) (+ x (with (y 3) x)))) '() (mtSub)) 10)
(check-expect (interp (parse '(with (x 5) (with (y x) y))) '() (mtSub)) 5)
(check-expect (interp (parse '(with (x 5) (with (x x) x))) '() (mtSub)) 5)

(check-expect (parse-fundef '(a n (+ n n))) (fundef 'a 'n (add (id 'n) (id 'n))))
(check-error (lookup-fundef 'a '()) "a: function not found")
(check-expect (lookup-fundef 'a (list (fundef 'a 'n (add (id 'n) (id 'n))))) (fundef 'a 'n (add (id 'n) (id 'n))))
(check-expect (lookup-fundef 'a (list (parse-fundef '(a n (+ n n))))) (fundef 'a 'n (add (id 'n) (id 'n))))

(define (a-fundef) (parse-fundef '(a n (+ n n))))
(define (b-fundef) (parse-fundef '(b n (+ n n))))
(check-expect (lookup-fundef 'b (list (a-fundef) (b-fundef))) (b-fundef))

(define (f-fundef) (parse-fundef '(f n (g (+ n 5)))))
(define (g-fundef) (parse-fundef '(g m (- m 1))))
(check-expect (interp (parse '(f 5)) (list (f-fundef) (g-fundef)) (mtSub)) 9)

(define (with-breaker) (parse-fundef '(f p n)))
(check-error (interp (parse '(with (n 5) (f 10))) (list (with-breaker)) (mtSub)) "lookup: no binding for identifier")

(test)
