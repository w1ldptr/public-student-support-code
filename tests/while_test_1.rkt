(let ([sum 0])
  (let ([i 5])
    (begin
      (while (> i 0)
        (begin
          (set! sum (+ sum 1))
          (set! i (- i 1))))
      (+ sum 37))))
