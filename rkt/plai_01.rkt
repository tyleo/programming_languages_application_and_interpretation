#lang plai

(define-type AE
    [num (n number?)]
    [add (lhs AE?) (rhs AE?)]
    [sub (lhs AE?) (rhs AE?)]
)

(define (parse sexp)
  (cond [(number? sexp) (num sexp)]
        [(list? sexp)
         (case (first sexp)
           [(+) (add (parse (second sexp)) (parse (third sexp)))]
           [(-) (sub (parse (second sexp)) (parse (third sexp)))])]))