 (define
 (id [a : (Vector Integer)]
  [d : (Vector Integer Integer)] 
  [h : (Vector Integer Integer)]) : Integer
 (+ (vector-ref a 0) 
    (if (eq? (vector-ref d 0) (- (vector-ref h 1) 2))
      12
      0))
 )

;;;  (id (vector 1) 2 3 4 5 6 7 (vector 42 (vector 42 7)))
 (id (vector 30) (vector 40 4) (vector 7 42))

