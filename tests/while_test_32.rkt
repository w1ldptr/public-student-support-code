(let ([i 10])
  (let ([res (begin
               (while (> i 0)
                 (set! i (- i 1)))
               i)])
    (+ res 42)))
