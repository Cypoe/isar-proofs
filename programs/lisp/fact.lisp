;;; fact.lisp — adapted from isa-physics runtime/native/tinylisp/fact.lisp
;;; factorial three ways: letrec*, explicit Y, seq+apply

;;; tail-recursive via letrec*
(define fact
  (lambda (n)
    (letrec* (f (lambda (r k)
                  (if (< k 2) r (f (* r k) (- k 1)))))
      (f 1 n))))

;;; via the Y combinator (self-referencing define -> Y wrap)
(define facty
  (lambda (n)
    ((Y (lambda (f)
          (lambda (k) (if (< 1 k) (* k (f (- k 1))) 1))))
     n)))

;;; via seq + spread apply: (* 1 . (2..n))
(define factseq
  (lambda (n) (* 1 . (seq 2 n))))

;;; plain self-recursive define
(define (dumbfact n)
  (if (< n 2) 1 (* n (dumbfact (- n 1)))))

(assert (= (fact 5) 120) "letrec* fact")
(assert (= (facty 5) 120) "Y fact")
(assert (= (factseq 5) 120) "seq+apply fact")
(assert (= (dumbfact 5) 120) "self-recursive fact")
(assert (= (fact 0) 1) "fact 0")
(assert (equal? (map fact '(1 2 3 4)) '(1 2 6 24)) "fact map")
