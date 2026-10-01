;;; features.lisp — ported from isa-physics lisp_tests/language_feature_test.lisp
;;; sections 4-10 minus floats/set!/macros

;;; predicates
(assert (atom? 'a) "symbol is atom")
(assert (atom? 42) "number is atom")
(assert (not (atom? '(a b))) "list is not atom")
(assert (list? '(a b c)) "list?")
(assert (not (list? 'a)) "symbol not list")
(assert (number? 42) "number?")
(assert (symbol? 'test) "symbol?")
(assert (eq? 'a 'a) "eq? symbols")
(assert (equal? '(a b) '(a b)) "equal? lists")
(assert (not (equal? '(a b) '(a c))) "equal? false")

;;; variable binding
(assert (let ((x 10) (y 20)) (= (+ x y) 30)) "let")
(assert (let* ((x 10) (y (+ x 10)) (z (+ y x)))
          (= z 30)) "let* chaining")

;;; conditionals
(assert (eq? (cond (nil 'first) (t 'second)) 'second) "cond fallthrough")
(assert (eq? (cond ((= 1 1) 'one) ((= 2 2) 'two)) 'one) "cond match")

;;; recursion
(define (identity x) x)
(assert (eq? (identity 'test) 'test) "identity")
(define (factorial n)
  (if (= n 0) 1 (* n (factorial (- n 1)))))
(assert (= (factorial 5) 120) "factorial")
(assert (= (factorial 0) 1) "factorial base")
(define (fib n)
  (cond ((= n 0) 0) ((= n 1) 1)
        (t (+ (fib (- n 1)) (fib (- n 2))))))
(assert (= (fib 10) 55) "fib 10")

;;; higher-order (user-defined, shadow-checking vs builtins)
(define (mapcar f xs)
  (if (null? xs) '() (cons (f (car xs)) (mapcar f (cdr xs)))))
(assert (equal? (mapcar (lambda (x) (+ x 1)) '(1 2 3 4))
                '(2 3 4 5)) "user map")
(define (mfilter p xs)
  (cond ((null? xs) '())
        ((p (car xs)) (cons (car xs) (mfilter p (cdr xs))))
        (t (mfilter p (cdr xs)))))
(assert (equal? (mfilter (lambda (x) (> x 2)) '(1 2 3 4 5))
                '(3 4 5)) "user filter")
(define (mreduce f xs acc)
  (if (null? xs) acc
      (mreduce f (cdr xs) (f acc (car xs)))))
(assert (= (mreduce + '(1 2 3 4 5) 0) 15) "user reduce")

;;; builtin higher-order
(assert (equal? (map (lambda (x) (* x x)) '(1 2 3)) '(1 4 9)) "map")
(assert (equal? (filter (lambda (x) (< x 3)) '(1 4 2 5)) '(1 2)) "filter")
(assert (= (reduce + 0 '(1 2 3 4 5)) 15) "reduce")

;;; closures
(define (make-adder n) (lambda (x) (+ x n)))
(define add5 (make-adder 5))
(define add10 (make-adder 10))
(assert (= (add5 10) 15) "closure 5")
(assert (= (add10 10) 20) "closure 10")

;;; quote / quasiquote
(assert (eq? (quote test) 'test) "quote")
(assert (equal? (quote (a b c)) '(a b c)) "quote list")
(define x 10)
(assert (equal? `(list ,x 20) '(list 10 20)) "quasiquote")
(define y 5)
(assert (equal? `(+ ,x ,y) '(+ 10 5)) "multi unquote")

;;; logic
(assert (and t 1 'x) "and truthy")
(assert (not (and t nil)) "and nil")
(assert (or nil nil 7) "or")
(assert (not (or nil nil)) "or all nil")
