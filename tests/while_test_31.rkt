(let ([i 10])
  (let ([res 1])
    (begin
      (if (begin
            (while (> i 0)
              (begin
                (set! res 2)
                (set! i (- i 1))))
            (eq? res 2))
          (begin
            (set! res 42)
            1)
          2)
      res)))
