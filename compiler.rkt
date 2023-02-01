#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body) (let ([env-new (dict-set env x (gensym x))])
                        (Let (dict-ref env-new x)
                             ((uniquify-exp env) e)
                             ((uniquify-exp env-new) body)))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))]
      [_ (error "Unrecognized expression (uniquify_exp)")])))
       
;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program '() e) (Program '() ((uniquify-exp '()) e))]))

(define (rco-atom e)
  (match e
    [(Var x) (values (Var x) '())]
    [(Int n) (values (Int n) '())]
    [(Let x rhs body)
     (define rhs_exp (rco-exp rhs))
     (define-values (body_atm body_env) (rco-atom body))
     (values body_atm (append (list (cons x rhs_exp)) body_env))]
    [(Prim op es)
     (define-values (es_new env_new) (for/lists (ee env) [(e es)] (rco-atom e)))
     (define tmp (gensym "tmp"))
     (values (Var tmp) (append (append* env_new) (list (cons tmp (Prim op es_new)))))]
    [_ (error "Unrecognized expression (rco-atom)")]))


(define (rco-exp e)
  (define (env-to-let env e)
    (match env
      ['() e]
      [(list (cons x rhs) rest ...) (Let x rhs (env-to-let rest e))]))
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Let x e body) (Let x (rco-exp e) (rco-exp body))]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim op es)
     (define-values (es_new env_new) (for/lists (ee env) [(e es)] (rco-atom e)))
     (env-to-let (append* env_new) (Prim op es_new))]
    [_ (error "Unrecognized expression (rco-exp)")]))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco-exp e))]))

(define (explicate-tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Let x rhs body) (explicate-assign rhs x (explicate-tail body))]
    [(Prim op es) (Return (Prim op es))]
    [else (error "Unrecognized expression (explicate-tail)" e)]))


(define (explicate-assign e x cont)
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Let y rhs body) (explicate-assign rhs y (explicate-assign body x cont))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [else (error "Unrecognized expression (explicate-assign)" e)]))


;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p
    [(Program info body) (CProgram info (list (cons 'start (explicate-tail body))))]))

(define (select-instructions-atm atm)
  (match atm
    [(Int n) (Imm n)]
    [(Var x) (Var x)]))

(define (select-assign x e)
  (define (get-op-instruction op)
    (match op
      [(Prim '+ (list e1 e2)) 'addq]
      [(Prim '- (list e1 e2)) 'subq]))
  (match e
    [atm #:when (atm? atm) (list (Instr 'movq (list (select-instructions-atm atm) x)))]
    [(Prim 'read '()) (list (Callq 'read_int 1) (Instr 'movq (list (Reg 'rax) x)))]
    [(Prim '- (list e1)) #:when (equal? e1 x)
                         (list
                          (Instr 'negq (list (select-instructions-atm e1))))]
    [(Prim '- (list e1)) (list
                          (Instr 'movq (list (select-instructions-atm e1) x))
                          (Instr 'negq (list x)))]
    [(Prim op (list e1 e2)) #:when (equal? e1 x) (list
                                                  (Instr (get-op-instruction e) (list (select-instructions-atm e2) x)))]
    [(Prim op (list e1 e2)) #:when (equal? e2 x) (list
                                                  (Instr (get-op-instruction e) (list (select-instructions-atm e1) x)))]
    [(Prim op (list e1 e2)) (list
                             (Instr 'movq            (list (select-instructions-atm e1) x))
                             (Instr (get-op-instruction e) (list (select-instructions-atm e2) x)))]))
    
(define (select-instructions-stmt stmt)
  (match stmt
    [(Return e) (select-assign (Reg 'rax) e)]
    [(Assign lhs rhs) (select-assign lhs rhs)]))

(define (select-instructions-tail e)
  (match e
    [(Seq fst snd) (append (select-instructions-stmt fst) (select-instructions-tail snd))]
    [(Return (Prim 'read '())) (list (Callq 'read_int 1) (Jmp 'conclusion))]
    [(Return x) (append (select-instructions-stmt e) (list (Jmp 'conclusion)))]))

;; select-instructions : C0 -> pseudo-X86
(define (select-instructions p)
  (match p
    [(CProgram info (list (cons 'start t)))
     (X86Program info (list (cons 'start (Block '() (select-instructions-tail t)))))]))

(define (calculate-stack-frame env)
  (cond
    [(eq? (remainder (length env) 16) 0) (* 8 (length env))]
    [else (* 8 (+ (length env) 1))]))

(define (get-location x env)
  (cond
    [(eq? (length env) 0) 0]
    [(eq? x (car (car env))) 1]
    [else (+ 1 (get-location x (cdr env)))]))

(define (assign-homes-imm i env)
  (match i
    [(Imm n) (Imm n)]
    [(Reg r) (Reg r)]
    [(Var x) (Deref 'rbp (* (- 8) (get-location x env)))]))
    
(define (assign-homes-instruction i env)
  (match i
    [(Instr name (list arg))       (Instr name (list (assign-homes-imm arg env)))]
    [(Instr name (list arg1 arg2)) (Instr name (list (assign-homes-imm arg1 env)
                                                     (assign-homes-imm arg2 env)))]
    [else i]
    ))

;; assign-homes : pseudo-X86 -> pseudo-X86
(define (assign-homes p)
  (match p
    [(X86Program info
                 (list (cons 'start (Block blkinfo blkbody))))
     (X86Program (dict-set info 'stack-space (calculate-stack-frame (dict-ref info 'locals-types)))
                 (list (cons 'start (Block blkinfo (for/list ([instr blkbody])
                                                     (assign-homes-instruction instr (dict-ref info 'locals-types)))))))]))

(define (patch-single-instruction i)
  (match i
    [(Instr name (list arg1 arg2)) #:when (and (Deref? arg1) (Deref? arg2))
                                   (list (Instr 'movq (list arg1 (Reg 'rax))) (Instr name (list (Reg 'rax) arg2)))]
    [else (list i)]))

;; assign-homes : pseudo-X86 -> X86
(define (patch-instructions p)
  (match p
    [(X86Program info (list (cons 'start (Block blkinfo blkbody))))
     (X86Program info (list (cons 'start (Block blkinfo (foldr
                                                         (lambda (instr old) (append (patch-single-instruction instr) old)) '() blkbody)))))]))

(define (generate-prelude info)
  (list (cons 'main (Block '()
                           (list
                            (Instr 'pushq (list (Reg 'rbp)))
                            (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
                            (Instr 'subq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp)))
                            (Jmp 'start))))))


(define (generate-conclusion info)
  (list (cons 'conclusion (Block '()
                           (list
                            (Instr 'addq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp)))
                            (Instr 'popq (list (Reg 'rbp)))
                            (Retq))))))

;; prelude-and-conclusion : X86 -> X86
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info block) (X86Program info (append (generate-prelude info) block (generate-conclusion info)))]))
     


;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( 
    ;; Uncomment the following passes as you finish them.
    ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
    ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
    ("instruction selection", select-instructions ,interp-x86-0)
    ("assign homes", assign-homes, interp-x86-0)
    ("patch instructions", patch-instructions, interp-x86-0)
    ("prelude and conclusion", prelude-and-conclusion, interp-x86-0)
    ))