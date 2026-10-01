;;; lists.lisp — adapted from isa-physics runtime/native/tinylisp/list.lisp
;;; user-level list library on top of cons/car/cdr/null?
;;; (list params renamed t -> xs: `t` is the boolean literal here)

(define (cadr xs) (car (cdr xs)))
(define (caddr xs) (car (cdr (cdr xs))))

(define (nthcdr xs n)
  (if (= n 0) xs (nthcdr (cdr xs) (- n 1))))
(define (nth xs n) (car (nthcdr xs n)))

(define (reverse-tr r xs)
  (if (null? xs) r (reverse-tr (cons (car xs) r) (cdr xs))))
(define (myreverse xs) (reverse-tr '() xs))

(define (member x xs)
  (if (null? xs)
      nil
      (if (equal? x (car xs)) xs (member x (cdr xs)))))

(define (foldr f x xs)
  (if (null? xs) x (f (car xs) (foldr f x (cdr xs)))))
(define (myfoldl f x xs)
  (if (null? xs) x (myfoldl f (f x (car xs)) (cdr xs))))

(define (myall? f xs)
  (if (null? xs) t
      (if (f (car xs)) (myall? f (cdr xs)) nil)))
(define (myany? f xs)
  (if (null? xs) nil
      (if (f (car xs)) t (myany? f (cdr xs)))))

(define (mymap f xs)
  (if (null? xs) '() (cons (f (car xs)) (mymap f (cdr xs)))))
(define (myfilter f xs)
  (if (null? xs) '()
      (if (f (car xs))
          (cons (car xs) (myfilter f (cdr xs)))
          (myfilter f (cdr xs)))))

(assert (eq? (cadr '(a b c)) 'b) "cadr")
(assert (eq? (caddr '(a b c)) 'c) "caddr")
(assert (eq? (nth '(a b c d) 2) 'c) "nth")
(assert (equal? (myreverse '(1 2 3 4)) '(4 3 2 1)) "reverse")
(assert (equal? (member 3 '(1 2 3 4)) '(3 4)) "member hit")
(assert (not (member 9 '(1 2 3))) "member miss")
(assert (= (myfoldl + 0 '(1 2 3 4 5)) 15) "foldl")
(assert (= (foldr + 0 '(1 2 3)) 6) "foldr")
(assert (myall? (lambda (x) (> x 0)) '(1 2 3)) "all? t")
(assert (not (myall? (lambda (x) (> x 0)) '(1 0 3))) "all? nil")
(assert (not (myany? (lambda (x) (< x 0)) '(1 2 3))) "any? nil")
(assert (equal? (mymap (lambda (x) (* x 2)) '(1 2 3)) '(2 4 6)) "map")
(assert (equal? (myfilter (lambda (x) (= (mod x 2) 0)) '(1 2 3 4 5 6))
                '(2 4 6)) "filter evens")
(assert (equal? (seq 1 5) '(1 2 3 4 5)) "seq builtin")
(assert (equal? (append '(a b) '(c d) '(e)) '(a b c d e))
        "append multi")
