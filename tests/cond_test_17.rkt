(if (eq? (let ([a (not #f)])
           (if (if a #f #t)
               #t
               (let ([b 5])
                 (<= b 1))))
         #t)
    (+ 3 1)
    (- 50 8))
