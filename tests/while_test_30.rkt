(let ([i 10])
  (let ([res 0])
    (begin
      (while (> i 0)
        (begin
          (if (eq? i 1)
              (begin
                (set! res 2)
                (void)
                (set! res 42)
                1)
              (begin
                (set! res 12)
                2))
          (set! res 42)
          (set! i (- i 1))))
      res)))
