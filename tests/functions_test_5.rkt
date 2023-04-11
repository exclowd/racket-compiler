(define (apply [f : (Integer -> Integer)] [value : Integer]) : Integer
    (f value))

(define (inc [x : Integer]) : Integer
    (+ x 1))

(apply inc 41)
