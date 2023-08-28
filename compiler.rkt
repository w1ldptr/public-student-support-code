#lang racket
(require racket/set racket/stream)
(require racket/fixnum racket/promise)
(require graph)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Lif.rkt")
(require "interp-Lwhile.rkt")
(require "interp-Cvar.rkt")
(require "interp-Cif.rkt")
(require "interp.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Lwhile.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Cif.rkt")
(require "utilities.rkt")
(require "priority_queue.rkt")
(require "multigraph.rkt")
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
    [(Let rval lval exp) (Let rval (pe-exp lval) (pe-exp exp))]
    [(SetBang var exp) (SetBang var (pe-exp exp))]
    [(Begin es body) (Begin (for/list ([exp es])
                              (pe-exp exp))
                            (pe-exp body))]
    [(WhileLoop cnd body) (WhileLoop (pe-exp cnd) (pe-exp body))]
    [(Void) (Void)]))

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
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))]
      [(SetBang var exp)
       (SetBang (dict-ref env var) ((uniquify-exp env) exp))]
      [(Begin es lst)
       (Begin (map (uniquify-exp env) es) ((uniquify-exp env) lst))]
      [(WhileLoop cnd body)
       (WhileLoop ((uniquify-exp env) cnd) ((uniquify-exp env) body))]
      [(Void) (Void)])))

;; uniquify : Lvar -> Lvar
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

(define (rco-atom e)
  (match e
    [(Var x) (values (Var x) '())]
    [(Int n) (values (Int n) '())]
    [(Bool b) (values (Bool b) '())]
    [(GetBang var)
     (define symb (gensym 'getbang-atom))
     (values (Var symb)
             (list (cons symb e)))]
    [(SetBang x rhs)
     (define symb (gensym 'setbang-atom))
     (values (Void)
             (list (cons symb (rco-exp e))))]
    [(Let x e body)
     (define-values (atom env) (rco-atom body))
     (values atom
             (cons (cons x (rco-exp e))
                   env))]
    [(If ce te ee)
     (define symb (gensym 'if-atom))
     (values (Var symb)
             (list (cons symb (rco-exp e))))]
    [(Begin le lst)
     (define symb (gensym 'begin-atom))
     (values (Var symb)
             (list (cons symb (rco-exp e))))]
    [(WhileLoop cnd body)
     (define symb (gensym 'while-atom))
     (values (Var symb)
             (list (cons symb (rco-exp e))))]
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
    [(Void) (Void)]
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(GetBang var) (GetBang var)]
    [(SetBang x e) (SetBang x (rco-exp e))]
    [(Let x e body)
     (Let x (rco-exp e) (rco-exp body))]
    [(If ce te ee)
     (If (rco-exp ce) (rco-exp te) (rco-exp ee))]
    [(Begin es lst)
     (Begin (map rco-exp es) (rco-exp lst))]
    [(WhileLoop cnd body)
     (WhileLoop (rco-exp cnd) (rco-exp body))]
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

(define basic-blocks (make-hash))

(define (create-block tail)
  (delay
    (define t  (force tail))
    (match t
      [(Goto _) t]
      [else
       (define label (gensym 'block))
       (hash-set! basic-blocks label t)
       (Goto label)])))

(define (explicate-tail e)
  (match e
    [(If ce te ee)
     (define-values (te-cont te-vars) (explicate-tail te))
     (define-values (ee-cont ee-vars) (explicate-tail ee))
     (define-values (ce-cont ce-vars) (explicate-pred ce te-cont ee-cont))
     (values ce-cont (append te-vars ee-vars ce-vars))]
    [(Let x rhs body)
     (define-values (body-cont body-vars) (explicate-tail body))
     (define-values (rhs-cont rhs-vars) (explicate-assign rhs x body-cont))
     (values rhs-cont (append body-vars rhs-vars))]
    [else (values (delay (Return e)) '())]))

(define (explicate-assign e x cont)
  (match e
    [(If ce te ee)
     (define block-cont (create-block cont))
     (define-values (te-cont te-vars) (explicate-assign te x block-cont))
     (define-values (ee-cont ee-vars) (explicate-assign ee x block-cont))
     (define-values (ce-cont ce-vars) (explicate-pred ce te-cont ee-cont))
     (values ce-cont (append te-vars ee-vars ce-vars))]
    [(Let y rhs body)
     (define-values (body-cont body-vars) (explicate-assign body x cont))
     (define-values (rhs-cont rhs-vars) (explicate-assign rhs y body-cont))
     (values rhs-cont (append body-vars rhs-vars))]
    [else (values (delay (Seq (Assign (Var x) e) (force cont))) (list x))]))

(define (explicate-pred e tc ec)
  (match e
    [(Var _)
     (values (delay (IfStmt (Prim 'eq? (list e (Bool #t)))
                            (force (create-block tc))
                            (force (create-block ec))))
             '())]
    [(Let x rhs body)
     (define-values (body-cont body-vars) (explicate-pred body tc ec))
     (define-values (rhs-cont rhs-vars) (explicate-assign rhs x body-cont))
     (values rhs-cont (append body-vars rhs-vars))]
    [(Prim 'not (list e))
     (values (delay (IfStmt (Prim 'eq? (list e (Bool #f)))
                            (force (create-block tc))
                            (force (create-block ec))))
             '())]
    [(Prim op es)
     #:when (or (eq? op 'eq?) (eq? op '<))
     (values (delay (IfStmt e (force (create-block tc)) (force (create-block ec))))
             '())]
    [(Bool b) (values (if b tc ec) '())]
    [(If ie itc iec)
     (define tcb (create-block tc))
     (define ecb (create-block ec))
     (define-values (itc-cont itc-vars) (explicate-pred itc tcb ecb))
     (define-values (iec-cont iec-vars) (explicate-pred iec tcb ecb))
     (define-values (if-cont if-vars) (explicate-pred ie itc-cont iec-cont))
     (values if-cont (append itc-vars iec-vars if-vars))]
    [else (error "explicate-pred unhandled case" e)]))

;; explicate-control : Lvar^mon -> Cvar
(define (explicate-control p)
  (match p
    [(Program info e)
     (hash-clear! basic-blocks)
     (define-values (promise vars) (explicate-tail e))
     (define cont (force promise))
     (define aux-blocks (hash->list basic-blocks))
     (CProgram `((locals . ,vars))
               (cons (cons 'start cont)
                     aux-blocks))]))

(define (select-atm e)
  (match e
    [(Int n) (Imm n)]
    [(Var x) e]
    [(Reg r) e]
    [(Bool b) (Imm (if b 1 0))]
    [else (error "select-atm unhandled case " e)]))

(define (select-stmt-cmp ce)
  (match ce
    [(Prim cmp (list op1 op2))
     #:when (or (eq? cmp 'eq?) (eq? cmp '<))
     (list (Instr 'cmpq (list (select-atm op2) (select-atm op1))))]
    [else (error "select-stmt-cmp unhandled case " ce)]))

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

(define (select-stmt-not ne)
  (match ne
    [(Assign var (Prim 'not (list var)))
     (list (Instr 'xorq (list (Imm 1) var)))]
    [(Assign dest (Prim 'not (list atm)))
     (list (Instr 'movq (list (select-atm atm) dest))
           (Instr 'xorq (list (Imm 1) dest)))]
    [else (error "select-stmt-not unhandled case " ne)]))

(define (select-stmt-cond ce)
  (match ce
    [(Assign dest (Prim 'eq? l))
     (append (select-stmt-cmp (Prim 'eq? l))
             (list (Instr 'set (list 'e (Reg 'al)))
                   (Instr 'movzbq (list (Reg 'al) dest))))]
    [(Assign dest (Prim '< l))
     (append (select-stmt-cmp (Prim 'eq? l))
             (list (Instr 'set (list 'l (Reg 'al)))
                   (Instr 'movzbq (list (Reg 'al) dest))))]
    [else (error "select-stmt-cond unhandled case " ce)]))

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

(define (select-stmt-if ie)
  (match ie
    [(IfStmt (Prim 'eq? l) (Goto l1) (Goto l2))
     (append (select-stmt-cmp (Prim 'eq? l))
             (list (JmpIf 'e l1)
                   (Jmp l2)))]
    [(IfStmt (Prim '< l) (Goto l1) (Goto l2))
     (append (select-stmt-cmp (Prim 'eq? l))
             (list (JmpIf 'l l1)
                   (Jmp l2)))]
    [else (error "select-stmt-if unhandled case " ie)]))

(define (select-stmt-goto ge)
  (match ge
    [(Goto label)
     (list (Jmp label))]
    [else (error "select-stmt-goto unhandled case " ge)]))

(define (select-stmt e)
  (match e
    [(Assign _ (Prim '+ l)) (select-stmt-sum e)]
    [(Assign _ (Prim '- l)) (select-stmt-dif e)]
    [(Assign _ (Prim 'read '())) (select-stmt-read e)]
    [(Assign _ (Prim 'not l)) (select-stmt-not e)]
    [(Assign _ (Prim cmp l))
     #:when (or (eq? cmp 'eq?) (eq? cmp '<))
     (select-stmt-cond e)]
    [(Assign _ atm) (select-stmt-atm e)]
    [(Return e) (select-stmt-return e)]
    [else (error "select-stmt unhandled case " e)]))

(define (select-tail e)
  (match e
    [(Return _) (select-stmt e)]
    [(IfStmt _ _ _) (select-stmt-if e)]
    [(Goto label) (select-stmt-goto e)]
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

    [(Instr 'cmpq (list op (Imm val)))
     (list (Instr 'movq (list (Imm val) (Reg 'rax)))
           (Instr 'cmpq (list op (Reg 'rax))))]

    [(Instr 'movzbq (list op (Deref reg shift)))
     (list (Instr 'movzbq (list op (Reg 'rax)))
           (Instr 'movq (list (Reg 'rax) (Deref reg shift))))]

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

(define (instr-r-set label->live instr)
  (match instr
    [(Instr 'movq (list (Reg src) _)) (set (Reg src))]
    [(Instr 'movq (list (Var src) _)) (set (Var src))]
    [(Instr 'movq _) (set)]
    [(Instr 'cmpq l)
     (list->set (for/fold ([regs-vars '()])
                          ([op l])
                  (match op
                    [(Reg r) (cons op regs-vars)]
                    [(Var v) (cons op regs-vars)]
                    [else regs-vars])))]
    [(Instr 'movzbq (list (Reg src) _))
     (set (Reg (dict-ref byte-to-reg src)))]
    [(Instr 'set (list _ _)) (set)]
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
    [(JmpIf _ label) (dict-ref label->live label)]
    [else (set)]))

(define (instr-w-set instr)
  (match instr
    [(Instr 'cmpq _) (set)]
    [(Instr 'set (list _ (Reg r)))
     (set (Reg (dict-ref byte-to-reg r)))]
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
         (define rset (instr-r-set label->live instr))
         (define wset (instr-w-set instr))
         (define Lbefore (set-union rset (set-subtract Lafter wset)))
         (cons Lbefore sets)))
     (Block (cons (cons 'live liveness) info)
            instr-list)]))

(define (build-cfg blocks)
  (define cfg (make-multigraph '()))
  (for ([label&block blocks])
    (match label&block
      [(cons label (Block _ instr-list))
       (add-vertex! cfg label)
       (for ([instr instr-list])
         (match instr
           [(Jmp to) (add-directed-edge! cfg label to)]
           [(JmpIf _ to) (add-directed-edge! cfg label to)]
           [else #f]))]))
  cfg)

(define (compute-ordering cfg)
  (tsort (transpose cfg)))

(define (uncover-live-blocks blocks)
  (define cfg (build-cfg blocks))
  (define ordered (compute-ordering cfg))
  (define label->live
    (make-hash (list (cons 'conclusion
                           (set (Reg 'rax) (Reg 'rsp))))))

  (reverse (for/list ([label ordered]
                      #:when (dict-ref blocks label #f))
             (define block (dict-ref blocks label))
             (define new-block-liveness (block-liveness block label->live))
             (match new-block-liveness
               [(Block (cons (cons 'live liveness) _) _)
                (hash-set! label->live label (car liveness))])
             (cons label new-block-liveness))))

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
    [(Instr 'movzbq (list src dst))
     (match src
       [(Imm _)
        (interference-rule1 dst (set-remove Lafter dst) ig)]
       [(Reg r)
        (interference-rule1 dst (set-remove (set-remove Lafter
                                                        (Reg (dict-ref byte-to-reg r)))
                                            dst)
                            ig)])]
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
(define byte-to-reg '((al . rax)))
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
  (for/list ([var vars]
             #:when (hash-ref mapping (Var var) #f))
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

(define (allocate-registers-blocks labels-and-blocks homes)
  (for/list ([label&block labels-and-blocks])
    (match label&block
      [(cons label (Block info instructions))
       (cons label (Block info (assign-homes-from-alist instructions homes)))])))

(define (allocate-registers p)
  (match p
    [(X86Program info labels-and-blocks)
     (define conflicts (dict-ref info 'conflicts))
     (define moves (dict-ref info 'moves))
     (define vars (dict-ref info 'locals))
     (define block-homes (color-graph conflicts moves vars))
     (define stack-space (compute-stack-space block-homes))
     (define used-callee (compute-used-callee block-homes))
     (X86Program (cons `(stack-space . ,stack-space)
                       (cons `(used_callee . ,used-callee)
                             info))
                 (allocate-registers-blocks labels-and-blocks block-homes))]))

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
    [(SetBang var exp) (SetBang var (shrink-exp exp))]
    [(Begin le lst) (Begin (map shrink-exp le) (shrink-exp lst))]
    [(WhileLoop cnd body) (WhileLoop (shrink-exp cnd) (shrink-exp body))]
    [else e]))

(define (shrink p)
  (match p
    [(Program info e) (Program info (shrink-exp e))]))

(define (build-weighted-cfg-with-degrees labels&blocks)
  (define cfg (weighted-graph/directed '()))
  (define-vertex-property cfg degree)

  (for ([label&block labels&blocks])
    (match label&block
      [(cons label (Block _ instr-list))
       (add-vertex! cfg label)
       (for ([instr instr-list])
         (match instr
           [(Jmp to)
            (degree-set! to (+ (degree to #:default 0) 1))
            (add-directed-edge! cfg label to 1)]
           [(JmpIf _ to)
            (degree-set! to (+ (degree to #:default 0) 1))
            (add-directed-edge! cfg label to 0)]
           [else #f]))]))
  (values cfg (degree->hash)))

(define (output-cfg name cfg)
  (define output (open-output-file (symbol->string name)
                                   #:mode 'text
                                   #:exists 'replace))
  (graphviz cfg #:output output))

(define (merge-blocks parent child)
  (match (cons parent child)
    [(cons (Block _ parent-instrs) (Block _ child-instrs))
     (Block '() ;; XXX not merging blocks info
            (append (reverse (cdr (reverse parent-instrs)))
                    child-instrs))]))

(define (remove-jumps-blocks-helper labels&blocks
                                    cfg
                                    processed
                                    degrees
                                    label)
  (define neighbors
    (filter (lambda (neigh)
              (not (set-member? processed neigh)))
            (remove 'conclusion (get-neighbors cfg label))))
  (for ([neigh neighbors])
    (set-add! processed neigh))
  (when (< 2 (length neighbors))
    (error "Too many jmp targets " neighbors))

  ;; (displayln "DEBUG CFG")
  ;; (displayln label)
  ;; (displayln neighbors)
  ;; (displayln (for/list ([neigh neighbors])
  ;;              (dict-ref degrees neigh)))
  ;; (displayln (for/list ([neigh neighbors])
  ;;              (edge-weight cfg label neigh)))
  ;; Can't merge with JumpIf targets marked by 0 weight
  (define non-mergeable-labels&blocks
    (let ([non-mergeable
           (for/first ([neigh neighbors]
                       #:when (eq? 0 (edge-weight cfg label neigh)))
             (remove-jumps-blocks-helper labels&blocks cfg processed degrees neigh))])
      (if non-mergeable non-mergeable '())))
  ;; Can try to merge with Jmp targets marked by 1 weight...
  (define mergeable-labels&blocks
    (let ([mergeable
           (for/first ([neigh neighbors]
                       #:when (eq? 1 (edge-weight cfg label neigh)))
             (remove-jumps-blocks-helper labels&blocks cfg processed degrees neigh))])
      (if mergeable
          (for/list ([l&b mergeable])
            (match l&b
              [(cons neigh block)
               ;; ...and degree of 1
               (if (and (member neigh neighbors)
                        (eq? 1 (edge-weight cfg label neigh))
                        (eq? 1 (dict-ref degrees neigh)))
                   (cons label (merge-blocks (dict-ref labels&blocks label) block))
                   (cons neigh block))]))
          '())))

  (if (dict-ref mergeable-labels&blocks label #f)
      (append mergeable-labels&blocks non-mergeable-labels&blocks)
      (cons (cons label (dict-ref labels&blocks label))
            (append mergeable-labels&blocks non-mergeable-labels&blocks))))

(define (remove-jumps-blocks labels&blocks)
  (define-values (cfg degrees) (build-weighted-cfg-with-degrees labels&blocks))
  ;; (output-cfg 'CFG cfg)
  (remove-jumps-blocks-helper labels&blocks cfg (mutable-set 'start) degrees 'start))

(define (remove-jumps p)
  (match p
    [(X86Program info labels&blocks)
     (X86Program info (remove-jumps-blocks labels&blocks))]))

(define (collect-set! e)
  (match e
    [(SetBang var rhs)
     (set-union (set var) (collect-set! rhs))]
    [(Begin es lst)
     (define set-lst (collect-set! lst))
     (if (empty? es)
         set-lst
         (set-union
          (apply set-union (map collect-set! es))
          set-lst))]
    [(WhileLoop cnd body)
     (set-union (collect-set! cnd) (collect-set! body))]
    [(Let x rhs body)
     (set-union (collect-set! rhs) (collect-set! body))]
    [(If ce te ee)
     (set-union (collect-set! ce) (collect-set! te) (collect-set! ee))]
    [(Prim op es)
     (if (empty? es)
         (set)
         (apply set-union (for/list ([e es]) (collect-set! e))))]
    [else (set)]))

(define (uncover-get!-exp set-vars e)
  (match e
    [(Var x)
     (if (set-member? set-vars x)
         (GetBang x)
         (Var x))]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Let x e body)
     (Let x (uncover-get!-exp set-vars e) (uncover-get!-exp set-vars body))]
    [(If ce te ee)
     (If (uncover-get!-exp set-vars ce)
         (uncover-get!-exp set-vars te)
         (uncover-get!-exp set-vars ee))]
    [(Prim op es)
     (Prim op (for/list ([e es]) (uncover-get!-exp set-vars e)))]
    [(SetBang var exp)
     (SetBang var (uncover-get!-exp set-vars exp))]
    [(Begin es lst)
     (Begin (for/list ([e es])
              (uncover-get!-exp set-vars e))
            (uncover-get!-exp set-vars lst))]
    [(WhileLoop cnd body)
     (WhileLoop (uncover-get!-exp set-vars cnd) (uncover-get!-exp set-vars body))]
    [(Void) (Void)]))

(define (uncover-get!-helper e)
  (define set-vars (collect-set! e))
  (displayln "GET! debug")
  (displayln set-vars)
  (uncover-get!-exp set-vars e))

(define (uncover-get! p)
  (match p
    [(Program info e) (Program info (uncover-get!-helper e))]))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ("partial evaluation" ,pe ,interp-Lwhile ,type-check-Lwhile)
    ("shrink" ,shrink ,interp-Lwhile ,type-check-Lwhile)
    ("uniquify" ,uniquify ,interp-Lwhile ,type-check-Lwhile)
    ("uncover get!" ,uncover-get! ,interp-Lwhile ,type-check-Lwhile)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lwhile ,type-check-Lwhile)
    ;; ("explicate control" ,explicate-control ,interp-Cif ,type-check-Cif)
    ;; ("instruction selection" ,select-instructions ,interp-pseudo-x86-1)
    ;; ("uncover-live" ,uncover-live ,interp-x86-1)
    ;; ("build-interference" ,build-interference ,interp-x86-1)
    ;; ("allocate registers" ,allocate-registers ,interp-x86-1)
    ;; ("remove jumps" ,remove-jumps ,interp-x86-1)
    ;; ("patch instructions" ,patch-instructions ,interp-x86-1)
    ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-1)
     ))
