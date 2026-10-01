;;; basic.lisp — ported from isa-physics lisp_tests/basic_lisp_statements.lisp
;;; assert-form subset (no floats/negatives/set!/strings)

;;; atoms
(assert (number? 42) "integer literal")
(assert (eq t t) "t")
(assert (null? nil) "nil")
(assert (symbol? 'hello) "quoted symbol")
(assert (list? '(a b c)) "quoted list")

;;; arithmetic
(assert (= (+ 2 3) 5) "add")
(assert (= (- 10 4) 6) "sub")
(assert (= (* 6 7) 42) "mul")
(assert (= (/ 10 2) 5) "div")
(assert (= (mod 10 3) 1) "mod")
(assert (= (abs 42) 42) "abs")

;;; list operations
(assert (eq? (car '(a b c)) 'a) "car")
(assert (equal? (cdr '(a b c)) '(b c)) "cdr")
(assert (equal? (cons 'a '(b c)) '(a b c)) "cons")
(assert (equal? (list 'x 'y 'z) '(x y z)) "list")
(assert (= (length '(1 2 3 4 5)) 5) "length")

;;; comparisons
(assert (= 42 42) "num =")
(assert (< 1 2) "lt")
(assert (> 5 3) "gt")
(assert (<= 1 1) "le")
(assert (>= 5 5) "ge")

;;; conditionals
(assert (eq? (if t 'yes 'no) 'yes) "if t")
(assert (eq? (if nil 'yes 'no) 'no) "if nil")
(assert (eq? (if 42 'yes 'no) 'yes) "if non-nil truthy")

;;; variables and functions
(define x 10)
(assert (= x 10) "define")
(define (add a b) (+ a b))
(assert (= (add 5 7) 12) "define fn")

;;; lambda
(assert (= ((lambda (x) (+ x 1)) 41) 42) "inline lambda")
