 (define
 (id [a : Integer] [b : Integer]
  [c : Integer] [d : Integer] [e : Integer]
  [f : Integer]) : Integer
 (+ a (+ b (+ c (+ d (+ e  f ))))))

 (id 1 2 3 4 5 27)
