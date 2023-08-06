#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Lif.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(require "priority_queue.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [(Prim '- (list e)) e]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (pe-neg e1) (pe-neg e2)))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [((Int n1) (Prim '+ (list (Int n2) e))) (Prim '+ (list (Int (fx+ n1 n2)) e))]
    [((Prim '+ (list (Int n2) e)) (Int n1)) (Prim '+ (list (Int (fx+ n1 n2)) e))]

    [((Prim '+ (list (Int n1) e1)) (Prim '+ (list (Int n2) e2)))
     (Prim '+ (list (Int (fx+ n1 n2)) (Prim '+ (list e1 e2))))]

    [(e (Int n)) (Prim '+ (list (Int n) e))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-sub r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx- n1 n2))]
    [((Int n1) (Prim '+ (list (Int n2) e)))
     (Prim '+ (list (Int (fx- n1 n2)) (Prim '- (list e))))]
    [((Prim '+ (list (Int n2) e)) (Int n1))
     (Prim '+ (list (Int (fx- n2 n1)) e))]

    [((Prim '+ (list (Int n1) e1)) (Prim '+ (list (Int n2) e2)))
     (Prim '+ (list (Int (fx- n1 n2)) (Prim '+ (list e1 (pe-neg e2)))))]

    [(e (Int n)) (Prim '+ (list (pe-neg (Int n)) e))]
    [(_ _) (Prim '+ (list r1 (pe-neg r2)))]))

(define (pe-not r)
  (match r
    [(Bool #t) (Bool #f)]
    [(Bool #f) (Bool #t)]
    [else (Prim 'not (list r))]))

(define (pe-and r1 r2)
  (match* (r1 r2)
    [((Bool b1) (Bool b2))
     (Bool (and b1 b2))]
    [(_ _) (Prim 'and (list r1 r2))]))

(define (pe-or r1 r2)
  (match* (r1 r2)
    [((Bool b1) (Bool b2))
     (Bool (or b1 b2))]
    [(_ _) (Prim 'or (list r1 r2))]))

(define (pe-< r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2))
     (Bool (< n1 n2))]
    [(_ _) (Prim '< (list r1 r2))]))

(define (pe-<= r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2))
     (Bool (<= n1 n2))]
    [(_ _) (Prim '<= (list r1 r2))]))

(define (pe-> r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2))
     (Bool (> n1 n2))]
    [(_ _) (Prim '> (list r1 r2))]))

(define (pe->= r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2))
     (Bool (>= n1 n2))]
    [(_ _) (Prim '>= (list r1 r2))]))

(define (pe-eq? r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2))
     (Bool (eq? n1 n2))]
    [(_ _) (Prim 'eq? (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Var x) (Var x)]
    [(Bool b) (Bool b)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]
    [(Prim '- (list e1 e2)) (pe-sub (pe-exp e1) (pe-exp e2))]
    [(Prim 'not (list e)) (pe-not (pe-exp e))]
    [(Prim 'and (list e1 e2)) (pe-and (pe-exp e1) (pe-exp e2))]
    [(Prim 'or (list e1 e2)) (pe-or (pe-exp e1) (pe-exp e2))]
    [(Prim '< (list e1 e2)) (pe-< (pe-exp e1) (pe-exp e2))]
    [(Prim '<= (list e1 e2)) (pe-<= (pe-exp e1) (pe-exp e2))]
    [(Prim '> (list e1 e2)) (pe-> (pe-exp e1) (pe-exp e2))]
    [(Prim '>= (list e1 e2)) (pe->= (pe-exp e1) (pe-exp e2))]
    [(Prim 'eq? (list e1 e2)) (pe-eq? (pe-exp e1) (pe-exp e2))]
    [(Prim op le) (Prim op (map pe-exp le))]
    [(If ce te ee) (If (pe-exp ce) (pe-exp te) (pe-exp ee))]
    [(Let rval lval exp) (Let rval (pe-exp lval) (pe-exp exp))]))

(define (pe p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (let ([mapping (dict-ref env x)]) (Var mapping))]
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(Let x e body)
       (let ([xnew (gensym x)])
         (Let xnew
              ((uniquify-exp env) e)
              ((uniquify-exp (cons (cons x xnew) env)) body)))]
      [(If ce te ee)
       (If ((uniquify-exp env) ce)
           ((uniquify-exp env) te)
           ((uniquify-exp env) ee))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : Lvar -> Lvar
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

(define (rco-atom e)
  (match e
    [(Var x) (values (Var x) '())]
    [(Int n) (values (Int n) '())]
    [(Let x e body)
     (define-values (atom env) (rco-atom body))
     (values atom
             (cons (cons x (rco-exp e))
                   env))]
    [(Prim op es)
     (define-values (atoms child-envs)
       (for/lists (l1 l2)
                  ([e es])
         (rco-atom e)))
     (define symb (gensym 'prim-atom))
     (define env (append* child-envs))
     (values (Var symb) (append env
                                (list (cons symb
                                            (Prim op atoms)))))]))

(define (rco-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Let x e body)
     (Let x (rco-exp e) (rco-exp body))]
    [(Prim op es)
     (define-values (atoms child-envs)
       (for/lists (l1 l2)
                  ([e es])
         (rco-atom e)))
     (define env (append* child-envs))
     (for/fold ([acc (Prim op atoms)])
               ([mapping (reverse env)])
       (Let (car mapping)
            (cdr mapping)
            acc))]))

;; remove-complex-opera* : Lvar -> Lvar^mon
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco-exp e))]))

(define (explicate-tail e)
  (match e
    [(Let x rhs body)
     (define-values (body-cont body-vars) (explicate-tail body))
     (define-values (rhs-cont rhs-vars) (explicate-assign rhs x body-cont))
     (values rhs-cont (append body-vars rhs-vars))]
    [else (values (Return e) '())]))

(define (explicate-assign e x cont)
  (match e
    [(Let y rhs body)
     (define-values (body-cont body-vars) (explicate-assign body x cont))
     (define-values (rhs-cont rhs-vars) (explicate-assign rhs y body-cont))
     (values rhs-cont (append body-vars rhs-vars))]
    [else (values (Seq (Assign (Var x) e) cont) (list x))]))

;; explicate-control : Lvar^mon -> Cvar
(define (explicate-control p)
  (match p
    [(Program info e)
     (define-values (cont vars) (explicate-tail e))
     (CProgram `((locals . ,vars))
               `((start . ,cont)))]))

(define (select-atm e)
  (match e
    [(Int n) (Imm n)]
    [(Var x) e]
    [(Reg r) e]
    [else (error "select-atm unhandled case " e)]))

(define (select-stmt-sum se)
  (match se
    [(Assign dest (Prim _
                        (list dest
                              other)))
     (list (Instr 'addq (list (select-atm other) dest)))]

    [(Assign dest (Prim _
                        (list other
                              dest)))
     (list (Instr 'addq (list (select-atm other) dest)))]

    [(Assign dest (Prim _ (list op1 op2)))
     (list (Instr 'movq (list (select-atm op1) dest))
           (Instr 'addq (list (select-atm op2) dest)))]

    [else (error "select-stmt-sum unhandled case " se)]))

(define (select-stmt-dif de)
  (match de
    [(Assign dest (Prim _
                        (list dest
                              other)))
     (list (Instr 'subq (list (select-atm other) dest)))]

    [(Assign dest (Prim _ (list op1 op2)))
     (list (Instr 'movq (list (select-atm op1) dest))
           (Instr 'subq (list (select-atm op2) dest)))]

    [(Assign dest (Prim _ (list op)))
     (list (Instr 'movq (list (select-atm op) dest))
           (Instr 'negq (list dest)))]

    [else (error "select-stmt-dif unhandled case " de)]))

(define (select-stmt-read re)
  (match re
    [(Assign dest _)
     (list (Callq 'read_int 0)
           (Instr 'movq (list (Reg 'rax) dest)))]
    [else (error "select-stmt-read unhandled case " re)]))

(define (select-stmt-atm e)
  (match e
    [(Assign dest atm)
     (list (Instr 'movq (list (select-atm atm) dest)))]
    [else (error "select-stmt-atm unhandled case " e)]))

(define (select-stmt-return re)
  (match re
    [(Reg 'rax)
     (list (Jmp 'conclusion))]
    [else
     (append (select-stmt (Assign (Reg 'rax) re))
             (list (Jmp 'conclusion)))]))

(define (select-stmt e)
  (match e
    [(Assign _ (Prim '+ l)) (select-stmt-sum e)]
    [(Assign _ (Prim '- l)) (select-stmt-dif e)]
    [(Assign _ (Prim 'read '())) (select-stmt-read e)]
    [(Assign _ atm) (select-stmt-atm e)]
    [(Return e) (select-stmt-return e)]
    [else (error "select-stmt unhandled case " e)]))

(define (select-tail e)
  (match e
    [(Return _) (select-stmt e)]
    [(Seq se t) (append (select-stmt se) (select-tail t))]
    [else (error "select-tail unhandled case " e)]))

;; select-instructions : Cvar -> x86var
(define (select-instructions p)
  (match p
    [(CProgram info cblocks)
     (X86Program info
                 (for/list ([label-block cblocks])
                   (cons (car label-block)
                         (Block '() (select-tail (cdr label-block))))))]))

(define (patch-instruction instr)
  (match instr
    [(Instr 'movq (list op op))
     '()]

    [(Instr i (list (Deref reg1 shift1)
                    (Deref reg2 shift2)))
     (list (Instr 'movq (list (Deref reg1 shift1) (Reg 'rax)))
           (Instr i (list (Reg 'rax) (Deref reg2 shift2))))]

    [(Instr i (list (Imm val) (Deref reg shift)))
     #:when (>= val (expt 2 16))
     (list (Instr 'movq (list (Imm val) (Reg 'rax)))
           (Instr i (list (Reg 'rax) (Deref reg shift))))]

    [(Instr i (list (Deref reg shift) (Imm val)))
     #:when (>= val (expt 2 16))
     (list (Instr 'movq (list (Imm val) (Reg 'rax)))
           (Instr i (list (Deref reg shift) (Reg 'rax))))]

    [else (list instr)]))

(define (patch-instructions-list instr-list)
  (define instr-lists (map patch-instruction instr-list))
  (flatten instr-lists))

;; patch-instructions : x86var -> x86int
(define (patch-instructions p)
  (match p
    [(X86Program info blocks)
     (X86Program info
                 (for/list ([block blocks])
                   (match block
                     [(cons label (Block block-info instructions))
                      (cons label (Block block-info
                                         (patch-instructions-list instructions)))]
                     [else (error "patch-instructions unhandled case " block)])))]))

(define (prelude-instrs stack-space used-callee label)
  (define stack-frame
    (list
     (Instr 'pushq (list (Reg 'rbp)))
     (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))))
  (define rem (remainder (+ stack-space (* 8 (length used-callee))) 16))
  (define locals
    (list
     (Instr 'subq (list (Imm (+ rem stack-space)) (Reg 'rsp)))))
  (define callee-saved
    (for/list ([reg used-callee])
      (Instr 'pushq (list (Reg reg)))))
  (define cont
    (list
     (Jmp label)))

  (append stack-frame locals callee-saved cont))

(define (conclusion-instrs stack-space used-callee)
  (define callee-saved
    (for/list ([reg (reverse used-callee)])
      (Instr 'popq (list (Reg reg)))))
  (define rem (remainder (+ stack-space (* 8 (length used-callee))) 16))
  (define locals
    (list
     (Instr 'addq (list (Imm (+ rem stack-space)) (Reg 'rsp)))))
  (define stack-frame
    (list
     (Instr 'popq (list (Reg 'rbp)))))
  (define cont
    (list
     (Retq)))

  (append callee-saved locals stack-frame cont))

;; prelude-and-conclusion : x86int -> x86int
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info blocks)
     (define stack-space (dict-ref info 'stack-space))
     (define used-callee (set->list (dict-ref info 'used_callee)))
     (define main (cons 'main
                         (Block '()
                                 (prelude-instrs stack-space used-callee 'start))))
     (define conclusion (cons 'conclusion
                               (Block '()
                                       (conclusion-instrs stack-space used-callee))))
     (X86Program info
                 (cons main (append blocks (list conclusion))))]))

(define (instr-r-set instr)
  (match instr
    [(Instr 'movq (list (Reg src) _)) (set (Reg src))]
    [(Instr 'movq (list (Var src) _)) (set (Var src))]
    [(Instr 'movq _) (set)]
    [(Instr _ (list (Imm imm) dst)) (set)]
    [(Instr _ (list src dst)) (set src dst)]
    [(Instr 'negq (list op)) (set op)]
    [(Instr 'pushq (list op))
     (define s (set 'rsp))
     (match op
       [(Reg r) (set-add s op)]
       [(Var r) (set-add s op)]
       [else s])]
    [(Instr 'popq _) (set (Reg 'rsp))]
    [(Callq _ arity)
     (define args (list (Reg 'rdi) (Reg 'rsi) (Reg 'rdx) (Reg 'rcx) (Reg 'r8) (Reg 'r9)))
     (list->set (if (< arity 6) (take args arity) args))]
    [(Retq) (set (Reg 'rax))]
    [else (set)]))

(define (instr-w-set instr)
  (match instr
    [(Instr _ (list src dst)) (set dst)]
    [(Instr 'negq (list op)) (set op)]
    [(Instr 'pushq _) (set (Reg 'rsp))]
    [(Instr 'popq (list dst)) (set (Reg 'rsp) dst)]
    [(Callq _ arity)
     (set (Reg 'rax) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'r11))]
    [else (set)]))

(define (block-liveness block label->live)
  (match block
    [(Block info instr-list)
     (define initial
       (match (last instr-list)
         [(Jmp label) (list (dict-ref label->live label))]
         [else (list (set))]))
     (define liveness
       (for/foldr ([sets initial])
                  ([instr instr-list])
         (define Lafter (car sets))
         (define Lbefore (set-union (instr-r-set instr)
                                    (set-subtract Lafter
                                                  (instr-w-set instr))))
         (cons Lbefore sets)))
     (Block (cons (cons 'live liveness) info)
            instr-list)]))

(define (uncover-live-blocks blocks)
  (for/foldr ([label->live (list (cons 'conclusion
                                        (set (Reg 'rax) (Reg 'rsp))))] ;;XXX
              [processed-blocks '()]
              #:result processed-blocks)
             ([label&block blocks])
    (match label&block
      [(cons label block)
       (define new-block-liveness (block-liveness block label->live))
       (define new-label->live
         (match new-block-liveness
           [(Block (cons (cons 'live liveness) _) instr-list)
            (cons (cons label (car liveness)) label->live)]))
       (define new-processed-blocks (cons (cons label new-block-liveness)
                                          processed-blocks))
       (values new-label->live new-processed-blocks)])))

(define (uncover-live p)
  (match p
    [(X86Program info blocks)
     (X86Program info (uncover-live-blocks blocks))]))

(define (interference-rule1 dst Lafter ig)
  (for/set ([i Lafter]) (add-edge! ig dst i)))

(define (interference-rule2 Wk Lafter ig)
  (for/set ([d Wk])
    (for/set ([v Lafter]
              #:when (not (equal? d v)))
      (add-edge! ig d v))))

(define (interference-instr instr Lafter ig)
  (match instr
    [(Instr 'movq (list (Imm _) dst))
     (interference-rule1 dst (set-remove Lafter dst) ig)]
    [(Instr 'movq (list src dst))
     (interference-rule1 dst (set-remove (set-remove Lafter src) dst) ig)]
    [(Instr i _)
     (interference-rule2 (instr-w-set instr) Lafter ig)]
    [(Callq f a)
     (interference-rule2 (instr-w-set instr) Lafter ig)]
    [else (void)]))

(define (build-interference-blocks blocks)
  (define interference-graph (unweighted-graph/undirected '()))

  (for ([block blocks])
    (match block
      [(cons _ (Block block-info instrs))
       (define liveness (cdr (dict-ref block-info 'live)))
       (for ([instr instrs]
             [Lafter liveness])
         (interference-instr instr Lafter interference-graph))]))
  interference-graph)

(define (parse-move-instr instr mg)
  (match instr
    [(Instr 'movq (list (Var v1) (Var v2)))
     (add-edge! mg (Var v1) (Var v2))]
    [else #f]))

(define (build-move-blocks blocks)
  (define move-graph (unweighted-graph/undirected '()))

  (for ([block blocks])
    (match block
      [(cons _ (Block _ instrs))
       (for ([instr instrs])
         (parse-move-instr instr move-graph))]))
  move-graph)

(define (output-interference-graph name ig mapping)
  (define output (open-output-file (symbol->string name)
                                   #:mode 'text
                                   #:exists 'replace))
  (define coloring (make-hash))
  (for ([v (get-vertices ig)])
    (define item (hash-ref mapping v))
    (define color (PqItem-color item))
    (hash-set! coloring
               v
               (+ color 5)))
  (graphviz ig
            #:output output
            #:colors coloring))

(define (build-interference p)
  (match p
    [(X86Program info l&b)
     (define ig (build-interference-blocks l&b))
     (define mg (build-move-blocks l&b))
     ;; DEBUG beg
     ;; (define-values (mapping pq) (init-pq ig mg))
     ;; (pre-saturate-pq ig mapping pq)
     ;; (color-graph-exec ig mg mapping pq)
     ;; (displayln "DEBUG")
     ;; (hash-for-each mapping
     ;;                (lambda (key node) (displayln node)))
     ;; (output-interference-graph 'PROG ig mapping)
     ;; (displayln "END DEBUG")
     ;; end
     (X86Program (cons (cons 'conflicts ig)
                       (cons (cons 'moves mg) info))
                 l&b)]))

(define reg-to-color '((rax . -1) (rsp . -2) (rbp . -3) (r11 . -4) (r15 . -5)
                                  (rcx . 0) (rdx . 1) (rsi . 2) (rdi . 3) (r8 . 4) (r9 . 5)
                                  (r10 . 6) (rbx . 7) (r12 . 8) (r13 . 9) (r14 . 10)))
(define color-to-reg '((0 . rcx ) (1 . rdx) (2 . rsi) (3 . rdi) (4 . r8) (5 . r9) (6 . r10)
                                  (7 . rbx) (8 . r12) (9 . r13) (10 . r14)))
(define calee-saved-regs '(rbp rsp rbx r12 r13 r14))

(struct PqItem (key color saturation node num-assign) #:transparent #:mutable)
(define (cmp-PqItems i1 i2)
  (define i1-saturation (set-count (PqItem-saturation i1)))
  (define i2-saturation (set-count (PqItem-saturation i2)))
  (if (= i1-saturation i2-saturation)
      (>= (PqItem-num-assign i1) (PqItem-num-assign i2))
      (> i1-saturation i2-saturation)))

(define (notify-neighbors ig mapping pq item)
  (define color (PqItem-color item))
  (for ([n (get-neighbors ig (PqItem-key item))])
    (define neigh-item (hash-ref mapping n))
    (set-add! (PqItem-saturation neigh-item) color)

    (define neigh-node (PqItem-node item))
    (when (and neigh-node (not (PqItem-color neigh-item)))
      (pqueue-decrease-key! pq neigh-node))))

(define (init-pq ig mg)
  (define mapping (make-hash))
  (define pq (make-pqueue cmp-PqItems))

  (for ([v (get-vertices ig)])
    (define num-assign (if (has-vertex? mg v) (length (get-neighbors mg v)) 0))
    (define item (PqItem v #f (mutable-set) #f num-assign))
    (hash-set! mapping v item)
    (match v
      [(Reg r)
       #:when (dict-ref reg-to-color r #f)
       (define color (dict-ref reg-to-color r))
       (set-PqItem-color! item color)]
      [(Reg r)
       (error "init-pq unmapped register " r)]
      [else
       (set-PqItem-node! item (pqueue-push! pq item))]))

  (values mapping pq))

(define (pre-saturate-pq ig mapping pq)
  (for ([v (get-vertices ig)])
    (match v
      [(Reg r)
       (define item (hash-ref mapping v))
       (notify-neighbors ig mapping pq item)]
      [else #f])))

(define (chose-item pq)
  (pqueue-pop! pq))

(define (min-available-color item start)
  (if (set-member? (PqItem-saturation item) start)
      (min-available-color item (+ start 1))
      start))

(define (min-assign-color mg mapping item)
  (define key (PqItem-key item))
  (define neighbors (if (has-vertex? mg key) (get-neighbors mg key) '()))
  (define neigh-colors
    (list->set (filter exact-nonnegative-integer?
                       (for/list ([neigh neighbors])
                         (PqItem-color (hash-ref mapping neigh))))))
  (define available-colors (set-subtract neigh-colors (PqItem-saturation item)))
  (if (set-empty? available-colors)
      #f
      (foldl min (set-first available-colors) (set->list available-colors))))

(define (chose-color ig mg mapping pq item)
  (define min-available (min-available-color item 0))
  (define min-assign (min-assign-color mg mapping item))
  (define chosen
    (if (or (not min-assign)
            (= min-available min-assign)
            (and (< min-available (length color-to-reg))
                 (>= min-assign (length color-to-reg))))
        min-available
        min-assign))
  (set-PqItem-color! item chosen)
  (notify-neighbors ig mapping pq item))

(define (color-graph-exec ig mg mapping pq)
  (when (> (pqueue-count pq) 0)
    (begin
      (chose-color ig mg mapping pq (chose-item pq))
      (color-graph-exec ig mg mapping pq))))

(define (assign-var-home color var)
  (if (< color (length color-to-reg))
      (cons var (Reg (dict-ref color-to-reg color)))
      (let* ([n-stack (- color (length color-to-reg))]
             [shift (* -8 (+ 1 n-stack))])
        (cons var (Deref 'rbp shift)))))

(define (assign-var-homes mapping vars)
  (for/list ([var vars])
    (define color (PqItem-color (hash-ref mapping (Var var))))
    (assign-var-home color var)))

(define (color-graph ig mg vars)
  (define-values (mapping pq) (init-pq ig mg))
  (pre-saturate-pq ig mapping pq)
  (color-graph-exec ig mg mapping pq)
  (assign-var-homes mapping vars))

(define (assign-homes-operands operands mapping)
  (for/list ([operand operands])
    (match operand
      [(Var x) (dict-ref mapping x)]
      [else operand])))

(define (assign-homes-from-alist instrs mapping)
  (for/list ([instr instrs])
    (match instr
      [(Instr name operands)
       (Instr name (assign-homes-operands operands mapping))]
      [else instr])))

(define (compute-stack-space mapping)
  (define shifts
    (for/list ([m mapping])
      (match (cdr m)
        [(Deref 'rbp shift) (+ 8 (fx- 0 shift))]
        [else 0])))
  (foldl max 0 shifts))

(define (compute-used-callee mapping)
  (for/fold ([used (set)])
            ([m mapping])
    (match (cdr m)
      [(Reg r)
       #:when (member r calee-saved-regs)
       (set-add used r)]
      [else used])))

(define (allocate-registers p)
  (match p
    [(X86Program info (list (cons 'start (Block bi instructions))))
     (define conflicts (dict-ref info 'conflicts))
     (define moves (dict-ref info 'moves))
     (define vars (dict-ref info 'locals))
     (define block-homes (color-graph conflicts moves vars))
     (define stack-space (compute-stack-space block-homes))
     (define used-callee (compute-used-callee block-homes))
     (X86Program (cons `(stack-space . ,stack-space)
                       (cons `(used_callee . ,used-callee)
                             info))
                 (list (cons 'start (Block bi
                                           (assign-homes-from-alist instructions
                                                                    block-homes)))))]))

(define (shrink-exp e)
  (match e
    [(Prim 'and (list e1 e2)) (If (shrink-exp e1) (shrink-exp e2) (Bool #f))]
    [(Prim 'or (list e1 e2)) (If (shrink-exp e1) (Bool #t) (shrink-exp e2))]
    [(Prim '<= (list e1 e2))
     (define tmp (gensym))
     (Let tmp (shrink-exp e1)
          (Prim 'not (list (Prim '< (list (shrink-exp e2) (Var tmp))))))]
    [(Prim '> (list e1 e2))
     (define tmp1 (gensym))
     (define tmp2 (gensym))
     (Let tmp1 (shrink-exp e1)
          (Let tmp2 (shrink-exp e2)
               (If (Prim 'eq? (list (Var tmp1) (Var tmp2)))
                   (Bool #f)
                   (If (Prim '< (list (Var tmp1) (Var tmp2)))
                       (Bool #f)
                       (Bool #t)))))]
    [(Prim '>= (list e1 e2))
     (Prim 'not (list (Prim '< (list (shrink-exp e1) (shrink-exp e2)))))]
    [(Prim op le) (Prim op (map shrink-exp le))]
    [(Let rval lval exp) (Let rval (shrink-exp lval) (shrink-exp exp))]
    [(If ce te ee) (If (shrink-exp ce) (shrink-exp te) (shrink-exp ee))]
    [else e]))

(define (shrink p)
  (match p
    [(Program info e) (Program info (shrink-exp e))]))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ("partial evaluation" ,pe ,interp-Lif ,type-check-Lif)
    ("shrink" ,shrink ,interp-Lif ,type-check-Lif)
    ("uniquify" ,uniquify ,interp-Lif ,type-check-Lif)
    ;;  ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
    ;;  ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
    ;;  ("instruction selection" ,select-instructions ,interp-x86-0)
    ;;  ("uncover-live" ,uncover-live ,interp-x86-0)
    ;;  ("build-interference" ,build-interference ,interp-x86-0)
    ;;  ("allocate registers" ,allocate-registers ,interp-x86-0)
    ;;  ("patch instructions" ,patch-instructions ,interp-x86-0)
    ;;  ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))
