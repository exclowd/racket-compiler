#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require "interp-Lint.rkt")
(require "interp-Lfun.rkt")
(require "interp-Lfun-prime.rkt")
(require "interp-Cfun.rkt")
(require "interp.rkt")
(require "type-check-Lfun.rkt")
(require "type-check-Cfun.rkt")
(require "utilities.rkt")
(require "multigraph.rkt")
(require "graph-printing.rkt")
(require "priority_queue.rkt")
(provide (all-defined-out))


(define (shrink-exp e)
  (match e
    [(Void) (Void)]
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Let var rhs body) (Let var (shrink-exp rhs) (shrink-exp body))]
    [(HasType expr type) (HasType (shrink-exp expr) type)]
    [(Prim 'and (list arg1 arg2)) (let ([e1 (shrink-exp arg1)]
                                        [e2 (shrink-exp arg2)])
                                    (If e1 e2 (Bool #f)))]
    [(Prim 'or (list arg1 arg2))  (let ([e1 (shrink-exp arg1)]
                                        [e2 (shrink-exp arg2)])
                                    (If e1 (Bool #t) e2))]
    [(Prim 'vector-ref  (list vec (Int i)))     (Prim 'vector-ref  (list (shrink-exp vec) (Int i)))]
    [(Prim 'vector-set! (list vec (Int i) val)) (Prim 'vector-set! (list (shrink-exp vec) (Int i) (shrink-exp val)))]
    [(Prim op arg*) (Prim op (map shrink-exp arg*))]
    [(If cnd thn els) (If (shrink-exp cnd) (shrink-exp thn) (shrink-exp els))]
    [(Apply fun arg*) (Apply fun (map shrink-exp arg*))]
    [_ (error "Unrecognized expression (shrink-exp)" e)]))

;; shrink : Lfun -> Lfun
(define (shrink p)
  (match p
    [(ProgramDefsExp info fn-list e)
     (define maindef (list (Def 'main '() 'Integer '() (shrink-exp e))))
     (define fndefs (for/list ([fn fn-list])
                      (match fn
                        [(Def name param* rty info body) (Def name param* rty info (shrink-exp body))])))
     (ProgramDefs info (append fndefs maindef))]))


(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(Let var rhs body) (let ([env-new (dict-set env var (gensym var))])
                            (Let (dict-ref env-new var)
                                 ((uniquify-exp env) rhs)
                                 ((uniquify-exp env-new) body)))]
      [(Prim op arg*) (Prim op (map (uniquify-exp env) arg*))]
      [(HasType expr type) (HasType ((uniquify-exp env) expr) type)]
      [(If cnd thn els) (If ((uniquify-exp env) cnd) ((uniquify-exp env) thn) ((uniquify-exp env) els))]
      [(Apply fun arg*) (Apply ((uniquify-exp env) fun) (map (uniquify-exp env) arg*))]
      [_ (error "Unrecognized expression (uniquify_exp)" e)])))

;; uniquify : Lfun -> Lfun
(define (uniquify p)
  (match p
    [(ProgramDefs info functions)
     (define fn-env (for/list ([fn functions])
                      (match fn
                        [(Def name param* rty '() body)
                         (define uniq-name (if (eq? name 'main) name (gensym name)))
                         (cons name uniq-name)])))
     (ProgramDefs info (for/list ([fn functions])
                         (match fn
                           [(Def name param* rty info body)
                            (define param-env (for/list ([param param*])
                                                (match param [(list name : T) (cons name (gensym name))])))
                            (define new-param* (for/list ([param param*])
                                                 (match param [(list name : T) (list (dict-ref param-env name) : T)])))
                            (Def (dict-ref fn-env name) new-param* rty info ((uniquify-exp (append param-env fn-env)) body))])))]))


(define (reveal-functions-exp fn->arity e)
  (match e
    [(Void) (Void)]
    [(Var x) (if (dict-has-key? fn->arity x) (FunRef x (dict-ref fn->arity x)) (Var x))]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Let var rhs body) (Let var
                             (reveal-functions-exp fn->arity rhs)
                             (reveal-functions-exp fn->arity body))]
    [(Prim op arg*) (Prim op (for/list ([arg arg*]) (reveal-functions-exp fn->arity arg)))]
    [(If cnd thn els) (If
                       (reveal-functions-exp fn->arity cnd)
                       (reveal-functions-exp fn->arity thn)
                       (reveal-functions-exp fn->arity els))]
    [(HasType expr type) (HasType (reveal-functions-exp fn->arity expr) type)]
    [(Apply fun arg*) (Apply (reveal-functions-exp fn->arity fun) (for/list [(arg arg*)] (reveal-functions-exp fn->arity arg)))]
    [_ (error "Unrecognized expression (reveal_functions_exp)" e)]))

;; reveal_functions : LFun -> LFunRef
(define (reveal-functions p)
  (match p
    [(ProgramDefs info functions)
     (define fn->arity (for/list ([fn functions])
                         (match fn
                           [(Def name param* rty '() body)
                            (cons name (length param*))])))
     (ProgramDefs info (for/list ([fn functions])
                         (match fn
                           [(Def name param* rty '() body)
                            (Def name param* rty '() (reveal-functions-exp fn->arity body))])))]))


(define (convert-to-lets assignments body)
  (match assignments
    ['() body]
    [_ (define head (car assignments))
       (define tail (cdr assignments))
       (Let (car head) (cdr head) (convert-to-lets tail body))]))

(define (set-vector-vals name arg* idx)
  (match arg*
    ['() '()]
    [_ (define head (car arg*))
       (define tail (cdr arg*))
       (cons (cons (gensym 'vector-value) (Prim 'vector-set! (list (Var name) (Int idx) (Var (car head)))))
             (set-vector-vals name tail (+ idx 1)))]))

(define (expose-allocation-exp e)
  (match e
    [(Void) (Void)]
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Prim op arg*) (Prim op (map expose-allocation-exp arg*))]
    [(Let var rhs body) (Let var (expose-allocation-exp rhs) (expose-allocation-exp body))]
    [(If cnd thn els) (If (expose-allocation-exp cnd)
                          (expose-allocation-exp thn)
                          (expose-allocation-exp els))]
    [(Apply fun arg*) (Apply (expose-allocation-exp fun) (map expose-allocation-exp arg*))]
    [(FunRef f n) (FunRef f n)]
    [(HasType (Prim 'vector arg*) type)
     (define nargs (length arg*))
     (define vector-arg* (for/list ([arg arg*]) (cons (gensym 'vector-arg) (expose-allocation-exp arg))))
     (define bytes (* 8 nargs))
     (define vector-name (gensym 'vector))
     (define allocation (list (cons (gensym 'ask-for-memory)
                                    (If (Prim '< (list (Prim '+ (list (GlobalValue 'free_ptr)
                                                                      (Int (+ 8 bytes))))
                                                       (GlobalValue 'fromspace_end)))
                                        (Void)
                                        (Collect (+ 8 bytes))))
                              (cons  vector-name (Allocate nargs type))))
     (define vector-set!* (set-vector-vals vector-name vector-arg* 0))
     (define assignments (append vector-arg* allocation vector-set!*))
     (convert-to-lets assignments (Var vector-name))]
    [_ (error "Unrecognized expression (expose_allocation_exp)" e)]))



;; expose-allocation : LFunRef -> LAllocFunRef
(define (expose-allocation p)
  (match p
    [(ProgramDefs info functions)
     (ProgramDefs info (for/list ([fn functions])
                         (match fn
                           [(Def name param* rty '() body)
                            (Def name param* rty '() (expose-allocation-exp body))])))]))


(define (rco-atom e)
  (match e
    [(Void) (values (Void) '())]
    [(Var x) (values (Var x) '())]
    [(Int n) (values (Int n) '())]
    [(Bool b) (values (Bool b) '())]
    [(Let x rhs body)
     (define rhs_exp (rco-exp rhs))
     (define-values (body_atm body_env) (rco-atom body))
     (values body_atm (append (list (cons x rhs_exp)) body_env))]
    [(Prim op arg*)
     (define tmp (gensym "tmp-op"))
     (define-values (es_new env_new) (for/lists (_ __) [(arg arg*)] (rco-atom arg)))
     (values (Var tmp) (append (append* env_new) (list (cons tmp (Prim op es_new)))))]
    [(If cnd thn els)
     (define tmp (gensym "tmp-if"))
     (values (Var tmp) (list (cons tmp (rco-exp (If (rco-exp cnd) (rco-exp thn) (rco-exp els))))))]
    [(FunRef name arity)
     (define tmp (gensym "tmp-funref"))
     (values (Var tmp) (list (cons tmp (rco-exp (FunRef name arity)))))]
    [(Apply fun arg*)
     (define tmp (gensym "tmp-fun"))
     (define-values (f_atm f_env) (rco-atom fun))
     (define-values (args_atm env_new) (for/lists (_ __) [(arg arg*)] (rco-atom arg)))
     (values (Var tmp) (append f_env (append* env_new) (list (cons tmp (Apply f_atm args_atm)))))]
    [(Collect bytes)
     (define tmp (gensym "tmp-collect"))
     (values (Var tmp) (list (cons tmp (Collect bytes))))]
    [(Allocate bytes t)
     (define tmp (gensym "tmp-allocate"))
     (values (Var tmp) (list (cons tmp (Allocate bytes t))))]
    [(GlobalValue x)
     (define tmp (gensym "tmp-globalvalue"))
     (values (Var tmp) (list (cons tmp (GlobalValue x))))]
    [_ (error "Unrecognized expression (rco-atom)" e)]))

(define (rco-exp e)
  (define (env-to-let env body)
    (match env
      ['() body]
      [(list (cons x rhs) rest ...) (Let x rhs (env-to-let rest body))]))
  (match e
    [(Void) (Void)]
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Let x rhs body) (Let x (rco-exp rhs) (rco-exp body))]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim op arg*)
     (define-values (es_new env_new) (for/lists (_ __) [(arg arg*)] (rco-atom arg)))
     (env-to-let (append* env_new) (Prim op es_new))]
    [(If cnd thn els) (If (rco-exp cnd) (rco-exp thn) (rco-exp els))]
    [(FunRef name arity) (FunRef name arity)]
    [(Apply fun arg*)
     (define-values (f_atm f_env) (rco-atom fun))
     (define-values (args_atm env_new) (for/lists (_ __) [(arg arg*)] (rco-atom arg)))
     (env-to-let (append f_env (append* env_new)) (Apply f_atm args_atm))]
    [(Collect bytes) (Collect bytes)]
    [(Allocate bytes t) (Allocate bytes t)]
    [(GlobalValue x) (GlobalValue (rco-atom x))]
    [_ (error "Unrecognized expression (rco-exp)" e)]))

;; remove-complex-opera* : LmonFunRef -> LmonFunRef
(define (remove-complex-opera* p)
  (match p
    [(ProgramDefs info functions)
     (ProgramDefs info (for/list ([fn functions])
                         (match fn
                           [(Def name param* rty '() body)
                            (Def name param* rty '() (rco-exp body))])))]))

(define basic-blocks (make-hash))

(define (create-block tail)
  (match tail
    [(Goto label) (Goto label)]
    [_
     (let ([label (gensym 'block)])
       (dict-set! basic-blocks label tail)
       (Goto label))]))

(define (explicate-tail e)
  (match e
    [(Void) (Return (Void))]
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Bool b) (Return (Bool b))]
    [(Let x rhs body) (explicate-assign rhs x (explicate-tail body))]
    [(If cnd thn els)
     (define thn-block (create-block (explicate-tail thn)))
     (define els-block (create-block (explicate-tail els)))
     (explicate-pred cnd thn-block els-block)]
    [(Apply fun args*) (TailCall fun args*)]
    [(FunRef name arity) (Return (FunRef name arity))]
    [(Prim 'vector-set! es) (Seq (Prim 'vector-set! es) (Return (Void)))]
    [(Prim op es) (Return (Prim op es))]
    [(GlobalValue x) (Return (GlobalValue x))]
    [(Collect bytes) (Seq (Collect bytes) (Return (Void)))]
    [(Allocate bytes t) (Seq (Allocate bytes t) (Return (Void)))]
    [_ (error "Unrecognized expression (explicate-tail)" e)]))

(define (explicate-assign e x cont)
  (match e
    [(Void) (Seq (Assign (Var x) (Void)) cont)]
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Bool b) (Seq (Assign (Var x) (Bool b)) cont)]
    [(Let y rhs body) (explicate-assign rhs y (explicate-assign body x cont))]
    [(Prim 'vector-set! _) (Seq e (explicate-assign (Void) x cont))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [(If cnd thn els)
     (define cont-block (create-block cont))
     (define thn-block (explicate-assign thn x cont-block))
     (define els-block (explicate-assign els x cont-block))
     (explicate-pred cnd thn-block els-block)]
    [(Apply fun args*) (Seq (Assign (Var x) (Call fun args*)) cont)]
    [(FunRef name arity) (Seq (Assign (Var x) (FunRef name arity)) cont)]
    [(GlobalValue _) (Seq (Assign (Var x) e) cont)]
    [(Allocate _ _) (Seq (Assign (Var x) e) cont)]
    [(Collect _) (Seq e cont)]
    [_ (error "Unrecognized expression (explicate-assign)" e)]))

(define (explicate-pred cnd thn els)
  (match cnd
    [(Var x) (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) (create-block thn) (create-block els))]
    [(Let x rhs body) (explicate-assign rhs x (explicate-pred body thn els))]
    [(Bool b) (if b (create-block thn) (create-block els))]
    [(Prim 'not (list e)) (explicate-pred e els thn)]
    [(Prim op es) #:when (or (or (or (or (eq? op 'eq?) (eq? op '<)) (eq? op '<= )) (eq? op '> )) (eq? op '>= ))
                  (IfStmt (Prim op es) (create-block thn) (create-block els))]
    [(Prim op es)
     (define tmpvar (gensym 'tmp))
     (explicate-assign cnd tmpvar (IfStmt (Prim 'eq? (list (Var tmpvar) (Bool #t))) (create-block thn) (create-block els)))]
    [(If cnd^ thn^ els^)
     (define thn-block (create-block thn))
     (define els-block (create-block els))
     (define thn-branch (explicate-pred thn^ thn-block els-block))
     (define els-branch (explicate-pred els^ thn-block els-block))
     (explicate-pred cnd^ thn-branch els-branch)]
    [(Apply fun args*)
     (define tmpvar (gensym 'tmp))
     (explicate-assign cnd tmpvar 
                       (IfStmt (Var tmpvar) (create-block thn) (create-block els)))]
    [(GlobalValue g) (IfStmt (Prim 'eq? `(,(GlobalValue g) ,(Bool #t)))
                             (create-block thn)
                             (create-block els))]
    [_ (error "Unrecognized expression (explicate-pred)" cnd thn els)]))

(define (explicate-control-function p)
  (match p
    [(Def name param* rty '() body)
     (set! basic-blocks (make-hash))
     (define start-label (string->symbol (~a name 'start)))
     (dict-set! basic-blocks start-label (explicate-tail body))
     (Def name param* rty '() (hash->list basic-blocks))]))

;; explicate-control : LmonFunRef -> CFun
(define (explicate-control p)
  (match p
    [(ProgramDefs info fun*) (ProgramDefs info (for/list ([fun fun*]) (explicate-control-function fun)))]))




(define (select-instructions-atm atm)
  (match atm
    [(Int n) (Imm n)]
    [(Var x) (Var x)]
    [(Reg r) (Reg r)]
    [(Void)  (Imm 0)]
    [(Bool b)
     (match b
       [#t (Imm 1)]
       [#f (Imm 0)])]))

(define (select-assign x e)
  (define (get-op-instruction op)
    (match op
      [(Prim '+ (list _ _)) 'addq]
      [(Prim '- (list _ _)) 'subq]))
  (define (type-mask t [mask 0])
    (match t
      [`(Vector) mask]
      [`(Vector (Vector . ,_)) (bitwise-ior mask 1)]
      [`(Vector ,_) mask]
      [`(Vector . ((Vector . ,_) . ,rest)) (type-mask `(Vector . ,rest) (arithmetic-shift (bitwise-ior mask 1) 1))]
      [`(Vector . (,t . ,rest)) (type-mask `(Vector . ,rest) (arithmetic-shift mask 1))]
      [else (error "Type Mask Error" t)]))
  (match e
    [atm #:when (atm? atm) (list (Instr 'movq (list (select-instructions-atm atm) x)))]
    [(FunRef fun _) (list (Instr 'leaq (list (Global fun) x)))]
    [(Call fun arg*)
     (define arg-moves (for/list ([reg (take arguments-list (length arg*))][arg arg*])
                         (Instr 'movq (list (select-instructions-atm arg) reg))))
     (append arg-moves (list (IndirectCallq fun (length arg*)) (Instr 'movq (list (Reg 'rax) x))))]
    [(GlobalValue var)
     (list
      (Instr 'movq (list (Global var) x)))]
    [(Prim 'read '()) (list (Callq 'read_int 1) (Instr 'movq (list (Reg 'rax) x)))]
    [(Prim 'not (list e1)) #:when (equal? e1 x)
                           (list
                            (Instr 'xorq (list (Imm 1) (select-instructions-atm e1))))]
    [(Prim 'not (list e1)) (list
                            (Instr 'movq (list (select-instructions-atm e1) x))
                            (Instr 'xorq (list (Imm 1) x)))]
    [(Prim 'vector-ref (list name (Int idx)))
     (define loc (* 8 (add1 idx)))
     (list
      (Instr 'movq (list (select-instructions-atm name) (Reg 'r11)))
      (Instr 'movq (list (Deref 'r11 loc) (select-instructions-atm x))))]
    [(Prim 'vector-length (list name))
     (list
      (Instr 'movq (list (select-instructions-atm name) (Reg 'r11)))
      (Instr 'movq (list (Deref 'r11 0) (Reg 'rax)))
      (Instr 'andq (list (Imm 63) (Reg 'rax)))
      (Instr 'sarq (list (Imm 1)  (Reg 'rax)))
      (Instr 'movq (list (Reg 'rax) (select-instructions-atm x))))]
    [(Prim '- (list e1)) #:when (equal? e1 x)
                         (list
                          (Instr 'negq (list (select-instructions-atm e1))))]
    [(Prim '- (list e1)) (list
                          (Instr 'movq (list (select-instructions-atm e1) x))
                          (Instr 'negq (list x)))]
    [(Prim 'eq? (list e1 e2)) (list
                               (Instr 'cmpq (list (select-instructions-atm e2) (select-instructions-atm e1)))
                               (Instr 'set (list 'e (Reg 'al)))
                               (Instr 'movzbq (list (Reg 'al) x)))]
    [(Prim '< (list e1 e2)) (list
                             (Instr 'cmpq (list (select-instructions-atm e2) (select-instructions-atm e1)))
                             (Instr 'set (list 'l (Reg 'al)))
                             (Instr 'movzbq (list (Reg 'al) x)))]
    [(Prim '<= (list e1 e2)) (list
                              (Instr 'cmpq (list (select-instructions-atm e2) (select-instructions-atm e1)))
                              (Instr 'set (list 'le (Reg 'al)))
                              (Instr 'movzbq (list (Reg 'al) x)))]
    [(Prim '> (list e1 e2)) (list
                             (Instr 'cmpq (list (select-instructions-atm e2) (select-instructions-atm e1)))
                             (Instr 'set (list 'g (Reg 'al)))
                             (Instr 'movzbq (list (Reg 'al) x)))]
    [(Prim '>= (list e1 e2)) (list
                              (Instr 'cmpq (list (select-instructions-atm e2) (select-instructions-atm e1)))
                              (Instr 'set (list 'ge (Reg 'al)))
                              (Instr 'movzbq (list (Reg 'al) x)))]
    [(Prim _ (list e1 e2)) #:when (equal? e1 x) (list (Instr (get-op-instruction e) (list (select-instructions-atm e2) x)))]
    [(Prim _ (list e1 e2)) #:when (equal? e2 x) (list (Instr (get-op-instruction e) (list (select-instructions-atm e1) x)))]
    [(Prim _ (list e1 e2)) (list
                            (Instr 'movq                  (list (select-instructions-atm e1) x))
                            (Instr (get-op-instruction e) (list (select-instructions-atm e2) x)))]
    [(Allocate len type)
     (define loc (* 8 (add1 len)))
     (define tag (bitwise-ior 1 (arithmetic-shift len 1) (arithmetic-shift (type-mask type) 7)))
     (list
      (Instr 'movq (list (Global 'free_ptr) (Reg 'r11)))
      (Instr 'addq (list (Imm loc) (Global 'free_ptr)))
      (Instr 'movq (list (Imm tag) (Deref 'r11 0)))
      (Instr 'movq (list (Reg 'r11) (select-instructions-atm x))))]
    [_ (error "unrecognized expression (select-assign)" e)]))

(define (select-instructions-stmt stmt)
  (match stmt
    [(Return e) (select-assign (Reg 'rax) e)]
    [(Assign lhs rhs) (select-assign lhs rhs)]
    [(Prim 'read '()) (list (Callq 'read_int 1)) ]
    [(Prim 'vector-set! (list name (Int idx) var))
     (define loc (* 8 (add1 idx)))
     (list
      (Instr 'movq (list (select-instructions-atm name) (Reg 'r11)))
      (Instr 'movq (list (select-instructions-atm var) (Deref 'r11 loc))))]
    [(Collect size)
     (list
      (Instr 'movq (list (Reg 'r15) (Reg 'rdi)))
      (Instr 'movq (list (Imm size) (Reg 'rsi)))
      (Callq 'collect 2))]
    [(Call fun arg*)
     (define arg-moves (for/list ([reg (take arguments-list (length arg*))][arg arg*])
                         (Instr 'movq (list (select-instructions-atm arg) reg))))
     (append arg-moves (list (IndirectCallq fun (length arg*))))]
    [_ (error "unrecognized expression (select-instructions-stmt)" stmt)]))

(define (select-instructions-tail e jmp-label)
  (match e
    [(Seq fst snd) (append (select-instructions-stmt fst) (select-instructions-tail snd jmp-label))]
    [(Return (Prim 'read '())) (list (Callq 'read_int 1) (Jmp jmp-label))]
    [(Return (FunRef fun arity)) (list (Instr 'leaq (list (Global fun) (Reg 'rax))))]
    [(Return _) (append (select-instructions-stmt e) (list (Jmp jmp-label)))]
    [(Goto l) (list (Jmp l))]
    [(IfStmt (Prim 'eq? (list arg1 arg2)) (Goto label1) (Goto label2))
     (define arg1^ (select-instructions-atm arg1))
     (define arg2^ (select-instructions-atm arg2))
     (list
      (Instr 'cmpq (list arg2^ arg1^))
      (JmpIf 'e label1)
      (Jmp label2))]
    [(IfStmt (Prim '< (list arg1 arg2)) (Goto label1) (Goto label2))
     (define arg1^ (select-instructions-atm arg1))
     (define arg2^ (select-instructions-atm arg2))
     (list
      (Instr 'cmpq (list arg2^ arg1^))
      (JmpIf 'l label1)
      (Jmp label2))]
    [(IfStmt (Prim '<= (list arg1 arg2)) (Goto label1) (Goto label2))
     (define arg1^ (select-instructions-atm arg1))
     (define arg2^ (select-instructions-atm arg2))
     (list
      (Instr 'cmpq (list arg2^ arg1^))
      (JmpIf 'le label1)
      (Jmp label2))]
    [(IfStmt (Prim '> (list arg1 arg2)) (Goto label1) (Goto label2))
     (define arg1^ (select-instructions-atm arg1))
     (define arg2^ (select-instructions-atm arg2))
     (list
      (Instr 'cmpq (list arg2^ arg1^))
      (JmpIf 'g label1)
      (Jmp label2))]
    [(IfStmt (Prim '>= (list arg1 arg2)) (Goto label1) (Goto label2))
     (define arg1^ (select-instructions-atm arg1))
     (define arg2^ (select-instructions-atm arg2))
     (list
      (Instr 'cmpq (list arg2^ arg1^))
      (JmpIf 'ge label1)
      (Jmp label2))]
    [(TailCall fun arg*)
     (define arg-moves (for/list ([reg (take arguments-list (length arg*))][arg arg*])
                         (Instr 'movq (list (select-instructions-atm arg) reg))))
     (append arg-moves (list (TailJmp fun (length arg*))))]
    [_ (error "unrecognized expression (select-instructions-tail)" e)]
    ))


(define (select-instructions-function p)
  (match p
    [(Def name param* rty info blocks)
     (define num-params (length param*))
     (define arg-moves (for/list ([reg (take arguments-list num-params)][param param*])
                         (Instr 'movq (list reg (Var (car param))))))
     (define start-label (string->symbol (~a name 'start)))
     (define conc-label  (string->symbol (~a name 'conclusion)))
     (define new-blocks (for/list ([block blocks]) (cons (car block) (Block '() (select-instructions-tail (cdr block) conc-label)))))
     (define new-start-block
       (match (dict-ref new-blocks start-label)
         [(Block '() instr*)
          (Block '() (append arg-moves instr*))]))
     (set! new-blocks (dict-set new-blocks start-label new-start-block))
     (Def name '() rty (dict-set info 'num-params  num-params) new-blocks)]))

;; select-instructions : CFun -> x86(Var,Def)callq*
(define (select-instructions p)
  (match p
    [(ProgramDefs info functions)
     (ProgramDefs info (for/list ([fn functions]) (select-instructions-function fn)))]))


(define caller-saved-list (list (Reg 'rax) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'r11)))

(define callee-saved-list (list (Reg 'rsp) (Reg 'rbp) (Reg 'rbx) (Reg 'r12) (Reg 'r13) (Reg 'r14) (Reg 'r15)))

(define arguments-list    (list (Reg 'rdi) (Reg 'rsi) (Reg 'rdx) (Reg 'rcx) (Reg 'r8) (Reg 'r9)))

(define (uncover-live-arg e)
  (define (get-parent-reg r)
    (match r
      [(Reg 'al) (Reg 'rax)]
      [(Reg 'ah) (Reg 'rax)]
      [(Reg 'bl) (Reg 'rbx)]
      [(Reg 'bh) (Reg 'rbx)]
      [(Reg 'cl) (Reg 'rcx)]
      [(Reg 'ch) (Reg 'rcx)]
      [(Reg 'dl) (Reg 'rdx)]
      [(Reg 'dh) (Reg 'rdx)]
      [_ r]))
  (match e
    [(Var _) (set e)]
    [(Reg _) (set (get-parent-reg e))]
    [_ (set)]))

(define (get-write instr)
  (match instr
    [(Instr 'addq (list _ arg2))    (set-union (uncover-live-arg arg2))]
    [(Instr 'subq (list _ arg2))    (set-union (uncover-live-arg arg2))]
    [(Instr 'movq (list _ arg2))    (set-union (uncover-live-arg arg2))]
    [(Instr 'movzbq (list _ arg2))  (set-union (uncover-live-arg arg2))]
    [(Instr 'negq (list arg1))      (set-union (uncover-live-arg arg1))]
    [(Instr 'xorq (list _ arg2))    (set-union (uncover-live-arg arg2))]
    [(Instr 'set (list _ arg2))     (set-union (uncover-live-arg arg2))]
    [(Instr 'leaq (list arg1 arg2)) (set-union (uncover-live-arg arg2))]
    [(Callq _ _) (list->set caller-saved-list)]
    [(IndirectCallq _ _) (list->set caller-saved-list)]
    [(TailJmp _ _) (list->set caller-saved-list)]
    [_ (set)]))

(define (get-read instr)
  (match instr
    [(Instr 'addq (list arg1 arg2)) (set-union (uncover-live-arg arg1) (uncover-live-arg arg2))]
    [(Instr 'subq (list arg1 arg2)) (set-union (uncover-live-arg arg1) (uncover-live-arg arg2))]
    [(Instr 'movq (list arg1 _))    (set-union (uncover-live-arg arg1))]
    [(Instr 'movzbq (list arg1 _))    (set-union (uncover-live-arg arg1))]
    [(Instr 'negq (list arg))       (set-union (uncover-live-arg arg))]
    [(Instr 'xorq (list arg1 arg2)) (set-union (uncover-live-arg arg1) (uncover-live-arg arg2))]
    [(Instr 'cmpq (list arg1 arg2)) (set-union (uncover-live-arg arg1) (uncover-live-arg arg2))]
    [(Callq _ arity) (list->set (take arguments-list arity))]
    [(IndirectCallq arg arity) (set-union (set arg) (list->set (take arguments-list arity)))]
    [(TailJmp arg arity)      (set-union (set arg) (list->set (take arguments-list arity)))]
    [_ (set)]))

(define (uncover-live-instr newi previ label->live)
  (match newi
    [(Jmp label) (define jmp-after (dict-ref label->live label))
                 (cons (set-union jmp-after (car previ)) previ)]
    [(JmpIf _ label) (define jmp-after (dict-ref label->live label))
                     (cons (set-union jmp-after (car previ)) previ)]
    [_ (define r (get-read newi))
       (define w (get-write newi))
       (cons (set-union (set-subtract (car previ) w) r) previ)]))

(define (uncover-live-block b label->live)
  (match b
    [(Block info blkbody)
     (define live-after-sets (foldr (lambda (v l) (uncover-live-instr v l label->live)) (list (set)) blkbody))
     live-after-sets]))

(define (uncover-live-function p)
  (match p
    [(Def name param* rty info blocks)
     (define conc-label  (string->symbol (~a name 'conclusion)))
     (define label->live (list(cons conc-label (set (Reg 'rax) (Reg 'rsp)))))
     (define labels (dict-keys blocks))
     (define cfg (make-multigraph '()))
     (for/list ([label labels]) (add-vertex! cfg label))
     (define block-graph (foldl (lambda (block graph)
                                  (match block
                                    [(cons label (Block blkinfo blkbody))
                                     (for ([instr blkbody])
                                       (match instr
                                         [(Jmp dest)  #:when (eq? dest conc-label) (void)]
                                         [(JmpIf _ dest) #:when (eq? dest conc-label) (void)]
                                         [(Jmp dest) (add-directed-edge! graph label dest)]
                                         [(JmpIf _ dest) (add-directed-edge! graph label dest)]
                                         [_ (void)]))])
                                  graph)
                                cfg blocks))
     (define order (tsort (transpose block-graph)))
     (define new-blocks (for/list ([label order])
                          (match (dict-ref blocks label)
                            [(Block blkinfo blkbody)
                             (define blk-live-after (uncover-live-block (Block blkinfo blkbody) label->live))
                             (set! label->live (dict-set label->live label (car blk-live-after)))
                             (cons label (Block (dict-set blkinfo 'live-after blk-live-after) blkbody))])))
     (Def name param* rty (dict-set info 'label->live label->live) new-blocks)]))

;; uncover-live : x86(Var,Def)callq* -> x86(Var,Def)callq*
(define (uncover-live p)
  (match p
    [(ProgramDefs info functions) (ProgramDefs info (map uncover-live-function functions))]))


(define (build-interference-graph instr live-after graph locals-types)
  (define (is-vector-type? locals-types var)
    (define label (match var [(Var x) x] [_ ""]))
    (println label)
    (if
    (dict-has-key? locals-types label)
    (match (dict-ref locals-types label)
      [(list 'Vector _ ...) #t]
      [_ #f])
    #f))
  (match instr
    [(Instr 'movq (list s d))
     (when (not (Imm? s)) (add-vertex! graph s))
     (when (not (Imm? d)) (add-vertex! graph d))
     (for ([v (set-subtract live-after (set s d))])
       (add-vertex! graph v) (add-edge! graph d v))]
    [(Instr 'movzbq (list s d))
     (when (not (Imm? s)) (add-vertex! graph s))
     (when (not (Imm? d)) (add-vertex! graph d))
     (for ([v (set-subtract live-after (set s d))])
       (add-vertex! graph v) (add-edge! graph d v))]
    [(Callq 'collect _)
     (for ([x live-after])
       (if (is-vector-type? locals-types x)
           (for ([y (append caller-saved-list callee-saved-list)])
             (add-vertex! graph x)
             (add-edge! graph x y))
           (for ([y caller-save])
             (add-vertex! graph x)
             ;; (add-vertex! graph x)
             (add-edge! graph x y))))]
    [_ (define w (get-write instr))
       (for* ([d w] [v (set-subtract live-after w) ])
         (add-vertex! graph v) (add-edge! graph d v))])
  graph)

(define (build-interference-function p)
  (match p
    [(Def name param* rty info blocks)
     (define graph (undirected-graph '()))
     (define locals-types (dict-ref info 'locals-types))
     (for/list ([block blocks])
       (define interference-graph
         (match block
           [(cons _ (Block blkinfo blkbody))
            (define live-after-sets (dict-ref blkinfo 'live-after))
            (foldl (lambda (instr live-after graph)
                     (build-interference-graph instr live-after graph locals-types))
                   (undirected-graph '())
                   blkbody (cdr live-after-sets))]))
       (graph-union! graph interference-graph))
     (Def name param* rty (dict-set info 'conflicts graph) blocks)]))

;; build-interference : x86(Var,Def)callq* -> x86(Var,Def)callq*
(define (build-interference p)
  (match p
    [(ProgramDefs info functions) (ProgramDefs info (map build-interference-function functions))]))


(define reg->color
  (list (cons (Reg 'r15) -5)
        (cons (Reg 'r11) -4)
        (cons (Reg 'rbp) -3)
        (cons (Reg 'rsp) -2)
        (cons (Reg 'rax) -1)
        (cons (Reg 'rcx)  0)
        (cons (Reg 'rdx)  1)
        (cons (Reg 'rsi)  2)
        (cons (Reg 'rdi)  3)
        (cons (Reg 'r8 )  4)
        (cons (Reg 'r9 )  5)
        (cons (Reg 'r10)  6)
        (cons (Reg 'rbx)  7)
        (cons (Reg 'r12)  8)
        (cons (Reg 'r13)  9)
        (cons (Reg 'r14) 10)))

(define color->reg
  (list (cons  0  (Reg 'rcx))
        (cons  1  (Reg 'rdx))
        (cons  2  (Reg 'rsi))
        (cons  3  (Reg 'rdi))
        (cons  4  (Reg 'r8))
        (cons  5  (Reg 'r9))
        (cons  6  (Reg 'r10))
        (cons  7  (Reg 'rbx))
        (cons  8  (Reg 'r12))
        (cons  9  (Reg 'r13))
        (cons  10 (Reg 'r14))))

(define (get-color s i)
  (if (set-member? s i) (get-color s (+ i 1)) i))

(define (color-graph graph vars)
  ;; vertices are stored in queue as pairs of vertex, priority
  (define variables (map (lambda (v) (Var (car v))) vars))
  (define vertex->saturation (map (lambda (v)
                                    (cons v (list->set
                                             (foldl (lambda (u res)
                                                      (match u
                                                        [(Reg _) (cons (dict-ref reg->color u) res)]
                                                        [_ res]))
                                                    '() (get-neighbors graph v)))))
                                  (get-vertices graph)))
  (define q (make-pqueue (lambda (a b) (> (set-count (cdr a))
                                          (set-count (cdr b))))))
  (define vertex->handle (foldl (lambda (v res)
                                  (dict-set res v (pqueue-push! q (cons v (dict-ref vertex->saturation v)))))
                                '() variables))
  (define (dsatur colors handles saturation)
    (define (update-saturation u h s c)
      (cond
        [(dict-has-key? h u)
         (define old-sat (dict-ref s u))
         (define new-sat (set-union old-sat (set c)))
         (define handle (dict-ref h u))
         (set-node-key! handle (cons u new-sat))
         (pqueue-decrease-key! q (dict-ref h u))
         (dict-set s u new-sat)]
        [else s]))
    (let* ([v (car (pqueue-pop! q))]
           [color (get-color (dict-ref saturation v) 0)]
           [var->color       (dict-set colors v color)]
           [var->handle      (dict-remove handles v)]
           [var->saturation (foldl (lambda (u res)
                                     (update-saturation u var->handle res color))
                                   saturation (get-neighbors graph v))])
      (if (equal? (pqueue-count q) 0)
          var->color (dsatur var->color var->handle var->saturation))))
  (if (equal? (pqueue-count q) 0) '() (dsatur '() vertex->handle vertex->saturation)))


(define (get-var-location var->color)
  (define var (car var->color))
  (define color (cdr var->color))
  (cond
    [(dict-has-key? color->reg color) (cons var (dict-ref color->reg color))]
    [else                             (cons var (Deref 'rbp (* -8 (- color 10))))]
    ))

(define (get-vec-location vec->color)
  (define vec (car vec->color))
  (define color (cdr vec->color))
  (cond
    [(dict-has-key? color->reg color) (cons vec (dict-ref color->reg color))]
    [else                             (cons vec (Deref 'rbp (+ (* -8 (length callee-saved-list)) (* -8 color))))]
    ))

(define (allocate-registers-imm i var->location)
  (match i
    [(Imm n) (Imm n)]
    [(Reg r) (Reg r)]
    [(Deref reg imm) (Deref reg imm)]
    [(Var _) (dict-ref var->location i)]
    [(Global label) (Global label)]))

(define (allocate-registers-instr instr result var->location)
  (match instr
    [(Instr 'set (list cc arg)) (cons (Instr 'set (list cc (allocate-registers-imm arg var->location))) result)]
    [(Instr name (list arg))        (cons (Instr name (list (allocate-registers-imm arg  var->location))) result)]
    [(Instr name (list arg1 arg2))  (cons (Instr name (list (allocate-registers-imm arg1 var->location)
                                                            (allocate-registers-imm arg2 var->location))) result)]
    [(TailJmp target arity) (cons (TailJmp (allocate-registers-imm target var->location) arity) result)]
    [(IndirectCallq target arity) (cons (IndirectCallq (allocate-registers-imm target var->location) arity) result)]
    [_                              (cons instr result)]))

(define (get-used-callee x result)
  (match x
    [(cons (Var _) (Reg r)) (cond [(list? (member (Reg r) callee-saved-list)) (set-add result (Reg r))]
                                  [else result])]
    [_ result]))

(define (allocate-registers-function p)
  (define (Vector? v locals-types)
    (match v
      [(Var x)
       (match (dict-ref locals-types x)
         [`(Vector . ,_) #t]
         [_ #f])]
      [_ #f]))
  (match p
    [(Def name param* rty info blocks)
     (define locals-types (dict-ref info 'locals-types))
     (define graph      (dict-ref info 'conflicts))
     (define variables  (dict-ref info 'locals-types))
     (define all->color (color-graph graph variables))
     (define var->color (filter (lambda (v) (not (Vector? v locals-types))) all->color))
     (define vec->color (filter (lambda (v) (Vector? v locals-types)) all->color))
     (define var->location (map get-var-location var->color))
     (define vec->location (map get-vec-location vec->color))
     (define var/vec->location (append var->location vec->location))
     (define num-var-spilled  (foldl (lambda (x result) (if (Deref? (cdr x)) (+ 1 result) result)) 0 var->location))
     (define num-vecs-spilled (foldl (lambda (x result) (if (Deref? (cdr x)) (+ 1 result) result)) 0 vec->location))
     (define used-callee (foldl get-used-callee (set) var/vec->location))
     (define num-callee  (set-count used-callee))
     (define stack-space (- (align (* 8 (+ num-var-spilled num-callee)) 16) (* 8 num-callee)))
     (define root-stack-space (* 8 num-vecs-spilled))
     (define new-blocks (for/list ([block blocks])
                          (match block
                            [(cons label (Block blkinfo blkbody))
                             (cons label (Block blkinfo (foldr (lambda (instr result)
                                                                 (allocate-registers-instr instr result var/vec->location))
                                                               '() blkbody)))])))
     (Def name param* rty (dict-set* info 'stack-space stack-space 'root-stack-space root-stack-space 'used-callee used-callee) new-blocks)]))

;; allocate-registers : x86(Var,Def)callq* -> x86(Var,Def)callq*
(define (allocate-registers p)
  (match p
    [(ProgramDefs info functions) (ProgramDefs info (map allocate-registers-function functions))]))


(define (patch-single-instruction i)
  (match i
    [(Instr 'movq (list arg1 arg2))    #:when (equal? arg1 arg2) (list)]
    [(Instr 'movzbq (list arg1 arg2))  #:when (equal? arg1 arg2) (list)]
    [(Instr 'movzbq (list arg1 arg2))  #:when (Deref? arg2)
                                       (list (Instr 'movzbq (list arg1 (Reg 'rax)))
                                             (Instr 'movq (list (Reg 'rax) arg2)))]
    [(Instr name (list arg1 arg2))   #:when (and (Deref? arg1) (Deref? arg2))
                                     (list (Instr 'movq (list arg1 (Reg 'rax))) (Instr name (list (Reg 'rax) arg2)))]
    [(Instr 'cmpq (list arg1 (Imm arg2)))
     (list (Instr 'movq  (list (Imm arg2) (Reg 'rax)))
           (Instr 'cmpq (list arg1 (Reg 'rax))))]
    [(Instr 'leaq (list arg1 arg2)) #:when (Deref? arg2)
                                    (list (Instr 'leaq (list arg1 (Reg 'rax)))
                                          (Instr 'movq (list (Reg 'rax) arg2)))]
    [(TailJmp arg arity) (list (Instr 'movq (list  arg (Reg 'rax)))
                               (TailJmp (Reg 'rax) arity))]
    [_ (list i)]))

(define (patch-instructions-function p)
  (match p
    [(Def name param* rty info blocks)
     (define new-blocks (for/list ([block blocks])
                          (match block
                            [(cons label (Block blkinfo blkbody))
                             (cons label (Block blkinfo (foldr
                                                         (lambda (instr old)
                                                           (append (patch-single-instruction instr) old)) '() blkbody)))])))
     (Def name param* rty info new-blocks)]))

;; patch-instructions : x86(Var,Def)callq* -> x86(Def)callq*
(define (patch-instructions p)
  (match p
    [(ProgramDefs info functions) (ProgramDefs info (map patch-instructions-function functions))]))

(define (generate-prelude name info)
  (define start-label (string->symbol (~a name 'start)))
  (define zero-out-list (for/list ([r (range 0 (quotient (dict-ref info 'root-stack-space) 8))])
                          (Instr 'movq (list (Imm 0) (Deref 'r15 (* 8 r))))))
  (match name
    ['main (list (cons name (Block '()
                                   (append
                                    (list
                                     (Instr 'pushq (list (Reg 'rbp)))
                                     (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))))
                                    (foldl (lambda (r res) (cons (Instr 'pushq (list r)) res)) '() (set->list (dict-ref info 'used-callee)) )
                                    (if  (> (dict-ref info 'stack-space) 0)
                                         (list (Instr 'subq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp))))
                                         '())
                                    (list
                                     (Instr 'movq (list (Imm 65536) (Reg 'rdi)))
                                     (Instr 'movq (list (Imm 65536) (Reg 'rsi)))
                                     (Callq 'initialize 2)
                                     (Instr 'movq (list (Global 'rootstack_begin) (Reg 'r15))))
                                    zero-out-list
                                    (list (Instr 'addq (list (Imm (dict-ref info 'root-stack-space)) (Reg 'r15))))
                                    (list (Jmp start-label))))))]
    [_ (list (cons name (Block '()
                               (append
                                (list
                                 (Instr 'pushq (list (Reg 'rbp)))
                                 (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))))
                                (foldl (lambda (r res) (cons (Instr 'pushq (list r)) res)) '() (set->list (dict-ref info 'used-callee)) )
                                (if  (> (dict-ref info 'stack-space) 0)
                                     (list (Instr 'subq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp))))
                                     '())
                                (list
                                 (Jmp start-label))))))]))


(define (generate-conclusion name info)
  (define conc-label  (string->symbol (~a name 'conclusion)))
  (list (cons conc-label (Block '()
                                (append
                                 (if (> (dict-ref info 'stack-space) 0)
                                     (list (Instr 'addq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp))))
                                     '())
                                 (foldr (lambda (r res) (cons (Instr 'popq (list r)) res)) '() (set->list (dict-ref info 'used-callee)) )
                                 (list
                                  (Instr 'popq (list (Reg 'rbp)))
                                  (Retq)))))))

(define (prelude-and-conclusion-function p)
  (match p
    [(Def name param* rty info blocks)
     ;; fix Tail jump
     (define (replace-tailjump instr)
       (match instr
         [(TailJmp target arity) (append
                                  (if (> (dict-ref info 'root-stack-space) 0)
                                      (Instr 'subq (list (Imm (dict-ref info 'root-stack-space)) (Reg 'r15)))
                                      '())
                                  (if (> (dict-ref info 'stack-space) 0)
                                      (list (Instr 'addq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp))))
                                      '())
                                  (foldr (lambda (r res) (cons (Instr 'popq (list r)) res)) '() (set->list (dict-ref info 'used-callee)))
                                  (list
                                   (Instr 'popq (list (Reg 'rbp)))
                                   (IndirectJmp target)))]
         [_ (list instr)]))
     (define new-blocks (for/list ([blk blocks])
                          (match blk
                            [(cons label (Block info instr*))
                             (cons label (Block info (foldr (lambda (instr accum) (append (replace-tailjump instr) accum)) '() instr*)))])))
     (append (generate-prelude name info) new-blocks (generate-conclusion name info))]))


;; prelude-and-conclusion : x86(Def)callq* -> x86callq*
(define (prelude-and-conclusion p)
  (match p
    [(ProgramDefs info functions)
     (define blocks (map prelude-and-conclusion-function functions))
     (X86Program info (append* blocks))]))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ;; Uncomment the following passes as you finish them.
    ("shrink" ,shrink ,interp-Lfun ,type-check-Lfun)
    ("uniquify" ,uniquify ,interp-Lfun ,type-check-Lfun)
    ("reveal functions" ,reveal-functions ,interp-Lfun-prime ,type-check-Lfun)
    ("expose-allocation" ,expose-allocation ,interp-Lfun-prime ,type-check-Lfun)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lfun-prime ,type-check-Lfun)
    ("explicate control" ,explicate-control ,interp-Cfun ,type-check-Cfun)
    ("instruction selection" ,select-instructions ,interp-pseudo-x86-3)
    ("uncover live" ,uncover-live ,interp-pseudo-x86-3)
    ("build interference" ,build-interference ,interp-pseudo-x86-3)
    ("allocate registers" ,allocate-registers ,interp-x86-3)
    ("patch instructions" ,patch-instructions ,interp-x86-3)
    ("prelude and conclusion" ,prelude-and-conclusion ,#f)
    ))
