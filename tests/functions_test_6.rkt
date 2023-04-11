(define (map [f : (Integer -> Integer)]) : Integer
    (f 41))

(define (inc [x : Integer]) : Integer
    (+ x 1))

(define (ret_inc [x : Integer]) : (Integer -> Integer)
  inc)

(map (ret_inc 11))
