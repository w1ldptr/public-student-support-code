(let ([x 1])
  (let ([y (begin
             (if (eq? x 1)
                 (begin
                   (read)
                   1)
                 2)
             (+ x 1)
             (read)
             (void)
             (read))])
    (+ 12 y)))
