#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require "interp-Lint.rkt")
(require "interp-Lif.rkt")
(require "interp-Cif.rkt")
(require "interp.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Cif.rkt")
(require "utilities.rkt")
(require "multigraph.rkt")
(require "graph-printing.rkt")
(require "priority_queue.rkt")
(provide (all-defined-out))

(define (shrink-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Let x rhs body) (Let x (shrink-exp rhs) (shrink-exp body))]
    [(Prim 'and `(,e1 ,e2)) (let ([e1 (shrink-exp e1)]
                                  [e2 (shrink-exp e2)])
                              (If e1 e2 (Bool #f)))]
    [(Prim 'or `(,e1 ,e2))  (let ([e1 (shrink-exp e1)]
                                  [e2 (shrink-exp e2)])
                              (If e1 (Bool #t) e2))]
    [(Prim op es) (Prim op (for/list ([ex es]) (shrink-exp ex)))]
    [(If c t e) (If (shrink-exp c) (shrink-exp t) (shrink-exp e))]
    [_ (error "Unrecognized expression (shrink_exp)")])
  )

(define (shrink p)
  (match p
    [(Program info e) (Program info (shrink-exp e))]))


(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(Let x rhs body) (let ([env-new (dict-set env x (gensym x))])
                          (Let (dict-ref env-new x)
                               ((uniquify-exp env) rhs)
                               ((uniquify-exp env-new) body)))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))]
      [(If cnd thn els) (If ((uniquify-exp env) cnd) ((uniquify-exp env) thn) ((uniquify-exp env) els))]
      [_ (error "Unrecognized expression (uniquify_exp)")])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program '() e) (Program '() ((uniquify-exp '()) e))]))


(define (rco-atom e)
  (match e
    [(Var x) (values (Var x) '())]
    [(Int n) (values (Int n) '())]
    [(Bool b) (values (Bool b) '())]
    [(Let x rhs body)
     (define rhs_exp (rco-exp rhs))
     (define-values (body_atm body_env) (rco-atom body))
     (values body_atm (append (list (cons x rhs_exp)) body_env))]
    [(Prim op es)
     (define tmp (gensym "tmp"))
     (define-values (es_new env_new) (for/lists (_ __) [(e es)] (rco-atom e)))
     (values (Var tmp) (append (append* env_new) (list (cons tmp (Prim op es_new)))))]
    [(If cnd thn els)
     (define tmp (gensym "tmp"))
     (values (Var tmp) (list (cons tmp (rco-exp (If (rco-exp cnd) (rco-exp thn) (rco-exp els))))))]
    [_ (error "Unrecognized expression (rco-atom)")]))

(define (rco-exp e)
  (define (env-to-let env e)
    (match env
      ['() e]
      [(list (cons x rhs) rest ...) (Let x rhs (env-to-let rest e))]))
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Let x e body) (Let x (rco-exp e) (rco-exp body))]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim op es)
     (define-values (es_new env_new) (for/lists (_ __) [(e es)] (rco-atom e)))
     (env-to-let (append* env_new) (Prim op es_new))]
    [(If cnd thn els) (If (rco-exp cnd) (rco-exp thn) (rco-exp els))]
    [_ (error "Unrecognized expression (rco-exp)")]))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco-exp e))]))

(define basic-blocks (make-hash))

(define (create-block tail)
  (match tail
    [(Goto label) (Goto label)]
    [else
     (let ([label (gensym 'block)])
       (dict-set! basic-blocks label tail)
       (Goto label))]))

(define (explicate-tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Bool b) (Return (Bool b))]
    [(Let x rhs body) (explicate-assign rhs x (explicate-tail body))]
    [(Prim op es) (Return (Prim op es))]
    [(If cnd thn els)
     (define thn-block (create-block (explicate-tail thn)))
     (define els-block (create-block (explicate-tail els)))
     (explicate-pred cnd thn-block els-block)]
    [_ (error "Unrecognized expression (explicate-tail)" e)]))

(define (explicate-assign e x cont)
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Bool b) (Seq (Assign (Var x) (Bool b)) cont)]
    [(Let y rhs body) (explicate-assign rhs y (explicate-assign body x cont))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [(If cnd thn els)
     (define thn-block (explicate-assign thn x cont))
     (define els-block (explicate-assign els x cont))
     (explicate-pred cnd thn-block els-block)]
    [_ (error "Unrecognized expression (explicate-assign)" e)]))

(define (explicate-pred cnd thn els)
  (match cnd
    [(Var x) (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) (create-block thn) (create-block els))]
    [(Let x rhs body) (explicate-assign rhs x (explicate-pred body thn els))]
    [(Bool b) (if b thn els)]
    [(Prim 'not (list e)) (explicate-pred e els thn)]
    [(Prim op es) #:when (or (or (or (or (eq? op 'eq?) (eq? op '<)) (eq? op '<= )) (eq? op '> )) (eq? op '>= ))
                  (IfStmt (Prim op es) (create-block thn) (create-block els))]
    [(If cnd^ thn^ els^)
     (define thn-block (explicate-pred thn^ thn els))
     (define els-block (explicate-pred els^ thn els))
     (explicate-pred cnd^ thn-block els-block)]
    [else (error "explicate_pred unhandled case" cnd)]))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p
    [(Program info body)
     (set! basic-blocks (make-hash))
     (dict-set! basic-blocks 'start (explicate-tail body))
     (CProgram info (hash->list basic-blocks))]))


(define (select-instructions-atm atm)
  (match atm
    [(Int n) (Imm n)]
    [(Var x) (Var x)]
    [(Reg r) (Reg r)]
    [(Bool b)
     (match b
       [#t (Imm 1)]
       [#f (Imm 0)])]))

(define (select-assign x e)
  (define (get-op-instruction op)
    (match op
      [(Prim '+ (list _ _)) 'addq]
      [(Prim '- (list _ _)) 'subq]))
  (match e
    [atm #:when (atm? atm) (list (Instr 'movq (list (select-instructions-atm atm) x)))]
    [(Prim 'not (list e1)) #:when (equal? e1 x)
                           (list
                            (Instr 'xorq (list (Imm 1) (select-instructions-atm e1))))]
    [(Prim 'not (list e1)) (list
                            (Instr 'movq (list (select-instructions-atm e1) x))
                            (Instr 'xorq (list (Imm 1) x)))]
    [(Prim 'read '()) (list (Callq 'read_int 1) (Instr 'movq (list (Reg 'rax) x)))]
    [(Prim '- (list e1)) #:when (equal? e1 x)
                         (list
                          (Instr 'negq (list (select-instructions-atm e1))))]
    [(Prim '- (list e1)) (list
                          (Instr 'movq (list (select-instructions-atm e1) x))
                          (Instr 'negq (list x)))]
    [(Prim 'eq? (list e1 e2)) (list
                              (Instr 'cmpq (list (select-instructions-atm e2) (select-instructions-atm e1)))
                              (Instr 'sete (list (Reg 'al)))
                              (Instr 'movzbq (list (Reg 'al) x)))]
    [(Prim '< (list e1 e2)) (list
                             (Instr 'cmpq (list (select-instructions-atm e2) (select-instructions-atm e1)))
                             (Instr 'setl (list (Reg 'al)))
                             (Instr 'movzbq (list (Reg 'al) x)))]
    [(Prim '<= (list e1 e2)) (list
                              (Instr 'cmpq (list (select-instructions-atm e2) (select-instructions-atm e1)))
                              (Instr 'setle (list (Reg 'al)))
                              (Instr 'movzbq (list (Reg 'al) x)))]
    [(Prim '> (list e1 e2)) (list
                             (Instr 'cmpq (list (select-instructions-atm e2) (select-instructions-atm e1)))
                             (Instr 'setg (list (Reg 'al)))
                             (Instr 'movzbq (list (Reg 'al) x)))]
    [(Prim '>= (list e1 e2)) (list
                              (Instr 'cmpq (list (select-instructions-atm e2) (select-instructions-atm e1)))
                              (Instr 'setge (list (Reg 'al)))
                              (Instr 'movzbq (list (Reg 'al) x)))]
    [(Prim _ (list e1 e2)) #:when (equal? e1 x) (list (Instr (get-op-instruction e) (list (select-instructions-atm e2) x)))]
    [(Prim _ (list e1 e2)) #:when (equal? e2 x) (list (Instr (get-op-instruction e) (list (select-instructions-atm e1) x)))]
    [(Prim _ (list e1 e2)) (list
                            (Instr 'movq                  (list (select-instructions-atm e1) x))
                            (Instr (get-op-instruction e) (list (select-instructions-atm e2) x)))]))

(define (select-instructions-stmt stmt)
  (match stmt
    [(Return e) (select-assign (Reg 'rax) e)]
    [(Assign lhs rhs) (select-assign lhs rhs)]))

(define (select-instructions-tail e)
  (match e
    [(Seq fst snd) (append (select-instructions-stmt fst) (select-instructions-tail snd))]
    [(Return (Prim 'read '())) (list (Callq 'read_int 1) (Jmp 'conclusion))]
    [(Return _) (append (select-instructions-stmt e) (list (Jmp 'conclusion)))]
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
      (Jmp label2))]))

;; select-instructions : C0 -> pseudo-X86
(define (select-instructions p)
  (match p
    [(CProgram info blocks)
     (println (first blocks))
     (define new-blocks (for/list ([block blocks]) (cons (car block) (Block '() (select-instructions-tail (cdr block))))))
     (X86Program info new-blocks)]))


(define caller-saved-list (list (Reg 'rax) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'r11)))

(define callee-saved-list (list (Reg 'rsp) (Reg 'rbp) (Reg 'rbx) (Reg 'r12) (Reg 'r13) (Reg 'r14) (Reg 'r15)))

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
    [(Instr 'movq (list _ arg2))    (set-union (uncover-live-arg arg2))]
    [(Instr 'movzbq (list _ arg2))  (set-union (uncover-live-arg arg2))]
    [(Instr 'negq (list arg1))      (set-union (uncover-live-arg arg1))]
    [(Instr 'xorq (list _ arg2))    (set-union (uncover-live-arg arg2))]
    [(Instr 'set (list cc arg2))    (set-union (uncover-live-arg arg2))]
    [(Callq _ _) (list->set caller-saved-list)]
    [_ (set)]))

(define (get-read instr)
  (match instr
    [(Instr 'addq (list arg1 arg2)) (set-union (uncover-live-arg arg1) (uncover-live-arg arg2))]
    [(Instr 'movq (list arg1 _))    (set-union (uncover-live-arg arg1))]
    [(Instr 'movzbq (list arg1 _))    (set-union (uncover-live-arg arg1))]
    [(Instr 'negq (list arg))       (set-union (uncover-live-arg arg))]
    [(Instr 'xorq (list arg1 arg2)) (set-union (uncover-live-arg arg1) (uncover-live-arg arg2))]
    [(Instr 'cmpq (list arg1 arg2)) (set-union (uncover-live-arg arg1) (uncover-live-arg arg2))]
    [(Callq _ arity) (list->set (take callee-saved-list arity))]
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

;; uncover-live : pseudo-X86 -> pseudo-X86
(define (uncover-live p)
  (match p
    [(X86Program info blocks)
     (define label->live (list(cons 'conclusion (set (Reg 'rax) (Reg 'rsp)))))
     (define labels (dict-keys blocks))
     (define cfg (make-multigraph '()))
     (for/list ([label labels]) (add-vertex! cfg label))
     (define block-graph (foldl (lambda (block graph)
                                  (match block
                                    [(cons label (Block blkinfo blkbody))
                                     (for ([instr blkbody])
                                       (match instr
                                         [(Jmp 'conclusion) (void)]
                                         [(JmpIf _ 'conclusion) (void)]
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
     (X86Program (dict-set info 'label->live label->live) new-blocks)]))


(define (build-interference-graph instr live-after graph)
  (match instr
    [(Instr 'movq (list s d))
     (when (not (Imm? s)) (add-vertex! graph s))
     (when (not (Imm? d)) (add-vertex! graph d))
     (for ([v (set-subtract live-after (set s d))])
       (add-vertex! graph v) (add-edge! graph d v))]
    [_ (define w (get-write instr))
       (for* ([d w] [v (set-subtract live-after w) ])
         (add-vertex! graph v) (add-edge! graph d v))])
  graph)

;; build-interference : pseudo X86 -> pseudo X86
(define (build-interference p)
  (match p
    [(X86Program info blocks)
     (define graph (undirected-graph '()))
     (for/list ([block blocks])
       (define interference-graph
         (match block
           [(cons _ (Block blkinfo blkbody))
            (define live-after-sets (dict-ref blkinfo 'live-after))
            (foldl build-interference-graph (undirected-graph '()) blkbody (cdr live-after-sets))]))
     (graph-union! graph interference-graph))
     (X86Program (dict-set info 'conflicts graph) blocks)]))


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


(define (get-location var->color)
  (define var (car var->color))
  (define color (cdr var->color))
  (cond
    [(dict-has-key? color->reg color) (cons var (dict-ref color->reg color))]
    [else                             (cons var (Deref 'rbp (* -8 (- color 10))))]
    ))

(define (allocate-registers-imm i var->location)
  (match i
    [(Imm n) (Imm n)]
    [(Reg r) (Reg r)]
    [(Var _) (dict-ref var->location i)]))

(define (allocate-registers-instr instr result var->location)
  (match instr
    [(Instr name (list arg))        (cons (Instr name (list (allocate-registers-imm arg  var->location))) result)]
    [(Instr name (list arg1 arg2))  (cons (Instr name (list (allocate-registers-imm arg1 var->location)
                                                            (allocate-registers-imm arg2 var->location))) result)]
    [_                              (cons instr result)]))

(define (get-used-callee x result)
  (match x
    [(cons (Var _) (Reg r)) (cond [(list? (member (Reg r) callee-saved-list)) (set-add result (Reg r))]
                                  [else result])]
    [_ result]))

;; allocate-registers : pseudoX86 -> X86
(define (allocate-registers p)
  (match p
    [(X86Program info blocks)
     (define graph      (dict-ref info 'conflicts))
     (define variables  (dict-ref info 'locals-types))
     (define var->color (color-graph graph variables))
     (define var->location (map get-location var->color))
     (define num-spilled (foldl (lambda (x result) (if (Deref? (cdr x)) (+ 1 result) result)) 0 var->location))
     (define used-callee (foldl get-used-callee (set) var->location))
     (define num-callee  (set-count used-callee))
     (define stack-space (- (align (* 8 (+ num-spilled num-callee)) 16) (* 8 num-callee)))
     (define new-blocks (for/list ([block blocks])
                          (match block
                            [(cons label (Block blkinfo blkbody))
                             (cons label (Block blkinfo (foldr (lambda (instr result)
                                                                  (allocate-registers-instr instr result var->location))
                                                                '() blkbody)))])))
     (X86Program (dict-set* info 'stack-space stack-space 'used-callee used-callee) new-blocks)]))


(define (patch-single-instruction i)
  (match i
    [(Instr 'movq (list arg1 arg2))  #:when (equal? arg1 arg2) (list)]
    [(Instr 'movzbq (list arg1 arg2))  #:when (equal? arg1 arg2) (list)]
    [(Instr 'movzbq (list arg1 arg2))  #:when (Deref? arg2)
                                       (list (Instr 'movzbq (list arg1 (Reg 'rax)))
                                             (Instr 'movq (list (Reg 'rax) arg2)))]
    [(Instr name (list arg1 arg2))   #:when (and (Deref? arg1) (Deref? arg2))
                                     (list (Instr 'movq (list arg1 (Reg 'rax))) (Instr name (list (Reg 'rax) arg2)))]
    [(Instr 'cmpq (list arg1 (Imm arg2))) 
                                     (list (Instr 'movq  (list (Imm arg2) (Reg 'rax)))
                                           (Instr 'cmpq (list arg1 (Reg 'rax))))]
    [_ (list i)]))

;; assign-homes : pseudo-X86 -> X86
(define (patch-instructions p)
  (match p
    [(X86Program info blocks)
     (define new-blocks (for/list ([block blocks])
                          (match block
                            [(cons label (Block blkinfo blkbody))
                             (cons label (Block blkinfo (foldr
                                                          (lambda (instr old)
                                                            (append (patch-single-instruction instr) old)) '() blkbody)))])))
     (X86Program info new-blocks)]))


(define (generate-prelude info)
  (list (cons 'main (Block '()
                           (append
                            (list
                             (Instr 'pushq (list (Reg 'rbp)))
                             (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))))
                            (foldl (lambda (r res) (cons (Instr 'pushq (list r)) res)) '() (set->list (dict-ref info 'used-callee)) )
                            (list
                             (Instr 'subq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp)))
                             (Jmp 'start)))))))


(define (generate-conclusion info)
  (list (cons 'conclusion (Block '()
                                 (append
                                  (list
                                   (Instr 'addq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp))))
                                  (foldr (lambda (r res) (cons (Instr 'popq (list r)) res)) '() (set->list (dict-ref info 'used-callee)) )
                                  (list
                                   (Instr 'popq (list (Reg 'rbp)))
                                   (Retq)))))))

;; prelude-and-conclusion : X86 -> X86
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info blocks) (X86Program info (append (generate-prelude info) blocks (generate-conclusion info)))]))


;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ;; Uncomment the following passes as you finish them.
    ("shrink" ,shrink ,interp-Lif ,type-check-Lif)
    ("uniquify" ,uniquify ,interp-Lif ,type-check-Lif)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lif ,type-check-Lif)
    ("explicate control" ,explicate-control ,interp-Cif ,type-check-Cif)
    ("instruction selection", select-instructions ,interp-pseudo-x86-1)
    ("uncover live", uncover-live ,interp-pseudo-x86-1)
    ("build interference", build-interference ,interp-pseudo-x86-1)
    ; ("assign homes", assign-homes ,interp-x86-0)
    ("allocate registers", allocate-registers ,interp-x86-1)
    ("patch instructions", patch-instructions ,interp-x86-1)
    ("prelude and conclusion", prelude-and-conclusion ,interp-x86-1)
    ))
