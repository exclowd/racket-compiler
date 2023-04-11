(define (map [f : (Integer -> Integer)]) : Integer
    (f 42))

(define (inc [x : Integer]) : Integer
    (+ x 1))

(define (ret-inc [x : Integer]) : (Integer -> Integer)
  inc)

(map (ret-inc 11))
