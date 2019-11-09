#lang racket

(require pict)

(struct nonogram (rows columns) #:prefab)

(define (spermute nums cb)
  (cb nums)
  (match nums
    ['() (void)]
    [(list-rest 1 _) (void)]
    [(list-rest fst right)
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
     `(,(- whitespace (sub1 run-count))
       ,@(make-list (sub1 run-count) 1) 0)
     (λ (permutation)
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

(define (permute-row->eqn len runs make-var)
  (let ([disjunctions '()])
    (define (push! vars)
      (set! disjunctions (cons `(and ,@vars)
                               disjunctions)))
    (define (make-var-for-eqn idx value)
      (define var (make-var idx))
      (if value
          var
          `(not ,var)))
    (permute-row len runs make-var-for-eqn push!)
    `(or ,@disjunctions)))

(define (atom? obj)
  (not (cons? obj)))

(define (contains-contradictory-values? lst)
  (define true-values '())
  (define false-values (mutable-set))
  (for ([val (in-list lst)])
    (match val
      [`(not ,v) (set-add! false-values v)]
      [v (set! true-values (cons v true-values))]))
  (for/or ([val (in-list true-values)])
    (set-member? false-values val)))

;; remove-duplicates, but use set ordering, on the basis that
;; remove-duplicates keeps order where possible, and using a set
;; will provide us consistent order every time.
(define (remove-duplicates/set lst)
  (set->list (list->set lst)))

(define (reduce expr [assume-true (seteqv)] [assume-false (seteqv)])
  (match expr
    ;; ¬¬A ≡ A
    [`(not (not ,e)) e]

    ;; DeMorgan's Law
    [`(not (and ,@args))
     `(or ,@(map (curry list 'not) args))]
    [`(not (or ,@args))
     `(and ,@(map (curry list 'not) args))]

    ;; Explosion of and/or with single argument
    [`(or ,e) e]
    [`(and ,e) e]

    ;; Explosion of and/or with nested expression of same operator
    [`(and ,@(list-no-order (list-rest 'and inside) outside ...))
     `(and ,@inside ,@outside)]
    [`(or ,@(list-no-order (list-rest 'or inside) outside ...))
     `(or ,@inside ,@outside)]

    ;; Or with a true value inside is a tautology
    [`(or ,@(list-no-order '(and) _ ...)) '(and)]

    ;; And with a false value inside is a paradox (always false)
    [`(and ,@(list-no-order '(or) _ ...)) '(or)]

    ;; (or var (not var)) is a tautology
    [`(or ,@(? contains-contradictory-values?)) '(and)]

    ;; (and var (not var)) is a paradox
    [`(and ,@(? contains-contradictory-values?)) '(or)]

    ;; Values assumed to be true
    [(? (curry set-member? assume-true)) '(and)]

    ;; Values assumed to be false
    [(? (curry set-member? assume-false)) '(or)]

    ;; Make assumptions from an and with literals
    [`(and ,@(list-no-order (or (? atom?)
                                `(not ,(? atom?)))
                            _ ...))
     (=> escape)
     (define (attempt-reductions non-literals assume-true assume-false)
       (define new-non-literals
         (for/list ([eqn (in-list non-literals)])
           (let ([reduced (apply-to-fixpoint
                           reduce eqn assume-true assume-false)])
             (unless (or (eq? escape void)
                         (equal? reduced eqn))
               (set! escape void))
             reduced)))
       (escape)
       `(and ,@(set->list assume-true)
             ,@(for/list ([lit (in-set assume-false)])
                 `(not ,lit))
             ,@new-non-literals))
     (let loop ([vals (cdr expr)]
                [non-literals '()]
                [assume-true assume-true]
                [assume-false assume-false])
       (match vals
         ['() (attempt-reductions non-literals assume-true assume-false)]
         [(list-rest (? atom? lit) vals)
          (loop vals non-literals (set-add assume-true lit) assume-false)]
         [(list-rest `(not ,(? atom? lit)) vals)
          (loop vals non-literals assume-true (set-add assume-false lit))]
         [(list-rest non-lit vals)
          (loop vals (cons non-lit non-literals) assume-true assume-false)]))]

    ;; Delete duplicate values in (and ...) and (or ...) before
    ;; distributing or reducing the arguments.
    [(list-rest sym args)
     (match* (sym (remove-duplicates/set args))

       ;; Distributive Law
       [('or (list-no-order (list-rest 'and and-args) args ...))
        ;; eqn->cnf is called on the leading and below to do our best
        ;; preventing explosion of the equation size
        `(or ,(eqn->cnf `(and ,@(map (curry list 'or (car args))
                                     and-args)))
             ,@(cdr args))]

       ;; Otherwise, reduce each of the arguments
       [(_ args) (cons sym (for/list ([eqn (in-list args)])
                             (reduce eqn assume-true assume-false)))])]

    ;; Return if it's a variable
    [v v]))

(define (apply-to-fixpoint fcn arg . args)
  (let ([result (apply fcn arg args)])
    (if (equal? result arg)
        result
        (apply apply-to-fixpoint fcn result args))))

(define (eqn->cnf expr)
  (apply-to-fixpoint reduce expr))

(define (varsym n)
  (string->symbol (format "var-~A" n)))

(define (reverse-varsym sym)
  (string->number (substring (symbol->string sym) 4)))

(define (dimacs-write expr number-of-vars)
  (let ([expr (eqn->cnf expr)])
    (display "p cnf ")
    (display number-of-vars)
    (display " ")
    (display (sub1 (length expr)))
    (newline)
    (define (display-var var)
      (display (match var
                 [`(not ,var) (sub1 (- var))]
                 [var (add1 var)]))
      (display " "))
    (for ([disjunction (in-list (cdr expr))])
      (match disjunction
        [`(or ,@vars) (map display-var vars)]
        [var (display-var var)])
      (displayln 0))))

(define (smt2-write expr number-of-vars)
  (displayln '(set-logic QF_BV))
  (displayln '(set-info :smt-lib-version 2.0))
  (displayln '(set-info :status sat))
  (for ([i (in-range number-of-vars)])
    (displayln `(declare-fun ,(varsym i)
                             () Bool)))
  (displayln
   `(assert ,(let translate ([expr expr])
               (match expr
                 [(? number?) (varsym expr)]
                 [(list-rest head args) (cons head (map translate args))]))))
  (displayln '(check-sat))
  (displayln `(get-value ,(for/list ([i (in-range number-of-vars)])
                            (varsym i))))
  (displayln '(exit)))

(define (make-output-vector rows columns)
  (build-vector rows
                (λ (_) (make-vector columns 0))))

(define (dimacs-read rows columns)
  (match (read-line)
    ["unsat" #f]
    ["sat"
     (let ([output-vector (make-output-vector rows columns)])
       (for ([n (map string->number (string-split (read-line)))])
         (let-values ([(rownum colnum) (quotient/remainder (sub1 (abs n))
                                                           rows)])
           (vector-set! (vector-ref output-vector rownum)
                        colnum
                        (> n 0))))
       output-vector)]))

(define (smt2-read rows columns)
  (let reader-loop ()
    (match (read)
      ['sat (reader-loop)]
      ['unsat #f]
      [`(error ,@args)
       (apply error args)]
      [pairs
       (let ([output-vector (make-output-vector rows columns)])
         (for ([item (in-list pairs)]
               [n (in-naturals)])
           (match item
             ;;  accepting "2" in front is a workaround for a bug in z3
             [(or (list 2 sym value)
                  (list sym value))
              (let-values ([(rownum colnum) (quotient/remainder n rows)])
                (vector-set! (vector-ref output-vector rownum)
                             colnum
                             (case value
                               ['true #t]
                               ['false #f])))]))
         output-vector)])))

(struct z3-communicator (flag write-fcn read-fcn) #:prefab)

(define dimacs (z3-communicator "-dimacs" dimacs-write dimacs-read))
(define smt2 (z3-communicator "-smt2" smt2-write smt2-read))

(define current-z3-communicator (make-parameter smt2))
(define current-z3-path (make-parameter (find-executable-path "z3")))

(define (solve nono)
  (match* (nono (current-z3-communicator))
    [((struct nonogram (rows columns))
      (struct z3-communicator (z3-flag write-fcn read-fcn)))
     (define column-len (length rows))
     (define row-len (length columns))

     (displayln "Converting to boolean equation...")
     (define row-futures
       (for/list ([runs (in-list rows)]
                  [rownum (in-naturals)])
         (future (λ () (permute-row->eqn
                        row-len runs
                        (λ (colnum)
                          (+ (* rownum column-len)
                             colnum)))))))
     (define column-futures
       (for/list ([runs (in-list columns)]
                  [colnum (in-naturals)])
         (future (λ () (permute-row->eqn
                        column-len runs
                        (λ (rownum)
                          (+ (* rownum column-len)
                             colnum)))))))
     (define equation
       `(and ,@(map touch row-futures)
             ,@(map touch column-futures)))

     (displayln "Running Z3...")
     (define-values (proc proc-output proc-input proc-error)
       (subprocess
        #f
        #f
        (current-error-port)
        (current-z3-path) z3-flag "-in"))
     (parameterize ([current-output-port proc-input])
       (write-fcn equation (* row-len column-len)))
     (close-output-port proc-input)
     (define result
       (parameterize ([current-input-port proc-output])
         (read-fcn column-len row-len)))
     (close-input-port proc-output)
     (subprocess-wait proc)
     result]))

(define (solution->pict solution)
  (apply vl-append
         (for/list ([row (in-vector solution)])
           (apply hc-append
                  (for/list ([cell (in-vector row)])
                    (if cell
                        (filled-rectangle 30 30)
                        (rectangle 30 30)))))))

(define (make-runs-pict runlist append-outer append-inner
                        [output-pict (blank)])
  (let rec ([runlist (map reverse runlist)]
            [output-pict output-pict])
    (if (ormap cons? runlist)
        (rec
         (for/list ([runs (in-list runlist)])
           (if (null? runs)
               '()
               (cdr runs)))
         (append-outer
          (apply append-inner
                 (for/list ([runs (in-list runlist)])
                   (if (null? runs)
                       (blank 30 30)
                       (cc-superimpose
                        (blank 30 30)
                        (text (~a (car runs)))))))
          output-pict))
        output-pict)))

(define (solve/pict nono)
  (define solution (solve nono))
  (match solution
    [#f (text "No solution!")]
    [else
     (match nono
       [(struct nonogram (rows columns))
        (make-runs-pict rows hb-append vc-append
                        (make-runs-pict columns vr-append hc-append
                                        (solution->pict solution)))])]))

(define (read-nonogram port)
  (let loop ([rows '()]
             [columns '()]
             [state #f])
    (match (read-line port)
      [(? eof-object?) (nonogram (reverse rows) (reverse columns))]
      ["rows" (loop rows columns 'rows)]
      ["columns" (loop rows columns 'columns)]
      [(app (λ (text) (map string->number (string-split text))) line)
       (case state
         ['rows (loop (cons line rows) columns state)]
         ['columns (loop rows (cons line columns) state)])])))

(define (run input output)
  (define nonogram (read-nonogram (open-input-file input)))
  (define pict (solve/pict nonogram))
  (match output
    [(list "show" _ _)
     (dynamic-require 'racket/gui/base #f)
     (show-pict pict)]
    [(list _ type filename)
     (send (pict->bitmap pict) save-file filename (string->symbol type))]))

(module+ main
  (void
   (command-line
    #:once-each
    ["--z3" z3-path
            "Path to z3 binary"
            (current-z3-path z3-path)]
    ["--communicator" z3-communicator
                      "How to communicate with z3 (\"smt2\" or \"dimacs\")"
                      (match z3-communicator
                        ["smt2" (current-z3-communicator smt2)]
                        ["dimacs" (current-z3-communicator dimacs)])]
    #:args (input output)
    (unless (current-z3-path)
      (error "z3 is not available"))
    (run input (regexp-match #rx"^(png|jpeg|xbm|xpm|bmp):(.*)|show$"
                             output)))))
