(let ([k #t])
  (if k
      (let ([res (let ([y (if #t
                              (read)
                              (if (eq? (read) 0)
                                  777
                                  (let ([x (read)])
                                    (+ 1 x))))])
                   (let ([z (if #f
                                (if (eq? (read) 2)
                                    777
                                    (let ([j (read)])
                                      (+ 2 j)))
                                (read))])
                     (let ([x (if #t
                                  #t
                                  (> 1 (read)))])
                       (if x
                           (+ y z)
                           777))))])
        (if (eq? res 42)
            res
            777))
      666))
