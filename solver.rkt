#lang racket

(struct nonogram (rows columns) #:prefab)

(define (spermute nums cb)
  (match nums
    [(or '() (list _)) (cb nums)]
    [(list-rest 1 right)
     (spermute right (λ (result)
                       (cb (cons 1 result))))]
    [(list-rest fst right)
     (cb nums)
     (let loop ([next-cons (sub1 fst)]
                [right right]
                [cb cb])
       (match right
         ['() (void)]
         [(list-rest head tail)
          (spermute (list* next-cons (add1 head) tail) cb)
          (loop head tail
                (λ (result)
                  (cb (cons next-cons result))))]))]))

(define (spermute/leading-zero nums cb)
  (cond [(zero? (car nums)) (spermute (cdr nums)
                                      (λ (result)
                                        (cb (cons 0 result))))]
        [else (spermute nums cb)
              (match nums
                [(list-rest fst snd rst)
                 (spermute (cons (+ fst snd) rst)
                           (λ (result)
                             (cb (cons 0 result))))]
                [_ (void)])]))

(define (permute-row len runs make-var cb)
  (let* ([run-count (length runs)]
         [blackspace (apply + runs)]
         [whitespace (- len blackspace)])
    (when (< whitespace (sub1 run-count))
      (error (format "Row ~A is too large for length ~A"
                     runs len)))
    (spermute/leading-zero
     (cons (- whitespace (sub1 run-count))
           (make-list (sub1 run-count) 1))
     (λ (permutation)
       (displayln permutation)
       (let loop ([acc '()]
                  [idx 0]
                  [permutation permutation]
                  [alt runs]
                  [filled #f])
         (match permutation
           [(list-rest 0 rst)
            (loop acc idx alt rst (not filled))]
           [(list-rest n rst)
            (loop (cons (make-var idx filled) acc)
                  (add1 idx)
                  (cons (sub1 n) rst)
                  alt filled)]
           ['() (if (= idx len)
                    (cb acc)
                    (loop (cons (make-var idx filled) acc)
                          (add1 idx)
                          '() alt filled))]))))))
