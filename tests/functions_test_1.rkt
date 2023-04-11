(define (tail_sum [n : Integer] [r : Integer]) : Integer
(if (eq? n 0)
r
(tail_sum (- n 1) (+ n r))))
(+ (tail_sum 3 0) 36)
