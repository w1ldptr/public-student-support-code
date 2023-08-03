(let ([a 1])
  (let ([b 2])
    (let ([c 42])
      (let ([d 10])
        (let ([a (<= a 1)])
          (let ([b (> b 5)])
            (if (and a (not b))
                a
                (+ 1 1))))))))
