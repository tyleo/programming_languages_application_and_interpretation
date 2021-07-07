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

(define (interp expr fun-defs)
  (type-case F1WAE expr
    [num (n) n]
    [add (l r) (+ (interp l fun-defs) (interp r fun-defs))]
    [sub (l r) (- (interp l fun-defs) (interp r fun-defs))]
    [with (bound-id named-expr bound-body)
          (interp (subst bound-body bound-id (num (interp named-expr fun-defs))) fun-defs)]
    [id (v) (error 'interp "free identifier")]
    [app (fun-name arg-expr)
         (local ([define the-fun-def (lookup-fundef fun-name fun-defs)])
           (interp (subst (fundef-body the-fun-def) (fundef-arg-name the-fun-def) (num (interp arg-expr fun-defs)))
                   fun-defs))]))

(check-expect (interp (parse '3) '()) 3)
(check-expect (interp (parse '(+ 3 4)) '()) 7)
(check-expect (interp (parse '(+ (- 3 4) 7)) '()) 6)

(check-expect (interp (parse '5) '()) 5)
(check-expect (interp (parse '(+ 5 5 )) '()) 10)
(check-expect (interp (parse '(with (x 5) x)) '()) 5)
(check-expect (interp (parse '(with (x (+ 5 5)) x)) '()) 10)
(check-expect (interp (parse '(with (x 5) (+ x x))) '()) 10)
(check-expect (interp (parse '(with (x (+ 5 5)) (+ x x))) '()) 20)
(check-expect (interp (parse '(with (x (+ 5 5)) (with (y (- x 3)) (+ y y)))) '()) 14)
(check-expect (interp (parse '(with (x 5) (with (y (- x 3)) (+ y y )))) '()) 4)
(check-expect (interp (parse '(with (x 5) (+ x (with (x 3) 10)))) '()) 15)
(check-expect (interp (parse '(with (x 5) (+ x (with (y 3) x)))) '()) 10)
(check-expect (interp (parse '(with (x 5) (with (y x) y))) '()) 5)
(check-expect (interp (parse '(with (x 5) (with (x x) x))) '()) 5)

(check-expect (parse-fundef '(a n (+ n n))) (fundef 'a 'n (add (id 'n) (id 'n))))
(check-error (lookup-fundef 'a '()) "a: function not found")
(check-expect (lookup-fundef 'a (list (fundef 'a 'n (add (id 'n) (id 'n))))) (fundef 'a 'n (add (id 'n) (id 'n))))
(check-expect (lookup-fundef 'a (list (parse-fundef '(a n (+ n n))))) (fundef 'a 'n (add (id 'n) (id 'n))))

(define (a-fundef) (parse-fundef '(a n (+ n n))))
(define (b-fundef) (parse-fundef '(b n (+ n n))))
(check-expect (lookup-fundef 'b (list (a-fundef) (b-fundef))) (b-fundef))

(define (f-fundef) (parse-fundef '(f n (g (+ n 5)))))
(define (g-fundef) (parse-fundef '(g m (- m 1))))
(check-expect (interp (parse '(f 5)) (list (f-fundef) (g-fundef))) 9)

(test)
