#lang plai

(define-type WAE
  [num (n number?)]
  [add (lhs WAE?) (rhs WAE?)]
  [sub (lhs WAE?) (rhs WAE?)]
  [with (name symbol?) (named-expression WAE?) (body WAE?)]
  [id (name symbol?)])

(define (subst expr sub-id val)
  (type-case WAE expr
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
    [id (v) (if (symbol=? v sub-id) val expr)]))

(define (parse sexp)
  (cond [(number? sexp) (num sexp)]
        [(symbol? sexp) (id sexp)]
        [(list? sexp)
         (case (first sexp)
           [(+) (add (parse (second sexp)) (parse (third sexp)))]
           [(-) (sub (parse (second sexp)) (parse (third sexp)))]
           [(with) (with (first (second sexp)) (parse (second (second sexp))) (parse (third sexp)))])]))

(define (calc an-ae)
  (type-case WAE an-ae
    [num (n) n]
    [add (l r) (+ (calc l) (calc r))]
    [sub (l r) (- (calc l) (calc r))]
    [with (bound-id named-expr bound-body)
          (calc (subst bound-body bound-id (num (calc named-expr))))]
    [id (v) (error 'calc "free identifier")]))

(test (calc (parse '3)) 3)
(test (calc (parse '(+ 3 4))) 7)
(test (calc (parse '(+ (- 3 4) 7))) 6)

(test (calc (parse '5)) 5)
(test (calc (parse '(+ 5 5 ))) 10)
(test (calc (parse '(with (x 5) x))) 5)
(test (calc (parse '(with (x (+ 5 5)) x))) 10)
(test (calc (parse '(with (x 5) (+ x x)))) 10)
(test (calc (parse '(with (x (+ 5 5)) (+ x x)))) 20)
(test (calc (parse '(with (x (+ 5 5)) (with (y (- x 3)) (+ y y))))) 14)
(test (calc (parse '(with (x 5) (with (y (- x 3)) (+ y y ))))) 4)
(test (calc (parse '(with (x 5) (+ x (with (x 3) 10))))) 15)
(test (calc (parse '(with (x 5) (+ x (with (y 3) x))))) 10)
(test (calc (parse '(with (x 5) (with (y x) y)))) 5)
(test (calc (parse '(with (x 5) (with (x x) x)))) 5)
