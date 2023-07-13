#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require srfi/1)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
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
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-sub r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx- n1 n2))]
    [(_ _) (Prim '- (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Var x) (Var x)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]
    [(Prim '- (list e1 e2)) (pe-sub (pe-exp e1) (pe-exp e2))]
    [(Let rval lval exp) (Let rval (pe-exp lval) (pe-exp exp))]))

(define (pe-Lvar p)
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
      [(Let x e body)
       (let ([xnew (gensym x)])
         (Let xnew
              ((uniquify-exp env) e)
              ((uniquify-exp (cons (cons x xnew) env)) body)))]
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

(define (assign-homes-operands operands locals-shifts)
  (for/list ([operand operands])
    (match operand
      [(Var x)
       (define home (dict-ref locals-shifts x))
       (Deref (car home) (cadr home))]
      [else operand])))

(define (assign-homes-stack block locals-shifts)
  (for/list ([instr block])
    (match instr
      [(Instr name operands)
       (Instr name (assign-homes-operands operands locals-shifts))]
      [else instr])))

(define (compute-stack-shifts locals-types)
  (for/list ([lc locals-types]
             [shift (iota (length locals-types) -8 -8)])
    (list (car lc) 'rbp shift)))

(define (compute-stack-space locals-types)
  (define sizes
    (for/list ([lc locals-types])
      (match (cdr lc)
        [Integer 8]
        [else (error "compute-stack-space unhandled case " lc)])))
  (define total (foldl + 0 sizes))
  (+ total (remainder total 16)))

;; assign-homes : x86var -> x86var
(define (assign-homes p)
  (match p
    [(X86Program info blocks)
     (define locals-types (dict-ref info 'locals-types))
     (define locals-shifts (compute-stack-shifts locals-types))
     (define stack-space (compute-stack-space locals-types))
     (X86Program (cons `(stack-space . ,stack-space) info)
                 (for/list ([block blocks])
                   (match block
                     [(cons label (Block i instructions))
                      (cons label (Block i (assign-homes-stack instructions
                                                               locals-shifts)))]
                     [else (error "assign-homes unhandled case " block)])))]))

(define (patch-instruction instr)
  (match instr
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

(define (prelude-instrs stack-space label)
  (list
   (Instr 'pushq (list (Reg 'rbp)))
   (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
   (Instr 'subq (list (Imm stack-space) (Reg 'rsp)))
   (Jmp label)))

(define (conclusion-instrs stack-space)
  (list
   (Instr 'addq (list (Imm stack-space) (Reg 'rsp)))
   (Instr 'popq (list (Reg 'rbp)))
   (Retq)))

;; prelude-and-conclusion : x86int -> x86int
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info blocks)
     (define stack-space (dict-ref info 'stack-space))
     (define main (cons 'main
                         (Block '()
                                 (prelude-instrs stack-space 'start))))
     (define conclusion (cons 'conclusion
                               (Block '()
                                       (conclusion-instrs stack-space))))
     (X86Program info
                 (cons main (append blocks (list conclusion))))]))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ("partial evaluation" ,pe-Lvar ,interp-Lvar ,type-check-Lvar)
     ;; Uncomment the following passes as you finish them.
     ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ("instruction selection" ,select-instructions ,interp-x86-0)
     ("assign homes" ,assign-homes ,interp-x86-0)
     ("patch instructions" ,patch-instructions ,interp-x86-0)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))
