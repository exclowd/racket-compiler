(define (map [f : (Integer -> Integer)]) : Integer
    42)

(define (inc [x : Integer]) : Integer
    (+ x 1))

(map inc)