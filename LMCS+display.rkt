#lang racket

(require redex
         "def-scheme-to-expr-scheme.rkt"
         "expr-scheme-to-CPS.rkt"
         "cps-escape-analysis.rkt"
         "utils.rkt"
         racket/trace
         (for-syntax stx/id-table))
(provide (all-defined-out))

(define coloring (make-hasheq))
(define names (make-hasheq))
(define label-ht (make-hasheq))
(define (in-stack? x) (not (eq? heap-ref (dict-ref coloring x stack-ref))))
(define (in-local? x) (eq? stack-ref (dict-ref coloring x stack-ref)))
(define (in-heap? x) (eq? heap-ref (dict-ref coloring x stack-ref)))
(define (has-exn-ref? x) (eq? exn-ref (dict-ref coloring x stack-ref)))
(define-values-for-syntax (stack local heap exn)
  (let ([fail (λ (stx) (raise-syntax-error #f "For use only in case-alloc" stx))])
    (values fail fail fail fail)))
(define-syntax (case-alloc-aux stx)
  (define lut (free-id-table (list (cons #'stack #'stack-ref)
                                   (cons #'heap #'heap-ref)
                                   (cons #'exn #'exn-ref))))
  (syntax-case stx ()
    [(_ id) #'(void)]
    [(_ id [local rhs1 rhs ...] rest ...)
     #'(cond [(not (eq? id heap-ref)) rhs1 rhs ...]
             [else (case-alloc-aux id rest ...)])]
    [(_ id [kind rhs1 rhs ...] rest ...)
     (with-syntax ([ref (free-id-table-ref lut #'kind)])
       (unless ref (raise-syntax-error #f "expected one of (stack heap exn local)" stx))
       #'(cond [(eq? id ref) rhs1 rhs ...]
               [else (case-alloc-aux id rest ...)]))]))
(define-syntax-rule (case-alloc expr [lhs rhs1 rhs ...] ...)
  (let ([x expr])
    (case-alloc-aux x [stack rhs1 rhs ...] ...)))


(define (ψ-is-kind? label v kind)
  (match-define (call-label-info colors depths ulam-depth) (hash-ref label-ht label))
  (eq? (hash-ref colors v) kind))
(define (S?ψ label v) (ψ-is-kind? label v stack-ref))
(define (H?ψ label v) (ψ-is-kind? label v heap-ref))
(define (E?ψ label v) (ψ-is-kind? label v exn-ref))
(define (Ξ?ψ label v) (not (ψ-is-kind? label v heap-ref)))

;; An implementation of Istack from [Clinger 98]
;; - set! + call/cc + display with stack and heap separated.

(define-language CPS-Scheme
  [uexp (if u exp exp) ucall]
  [ucall (uaexp uaexp ... caexp)]
  [ccall (caexp uaexp ...)]
  [call ucall ccall]
  [ulam (λ (u ... k) exp)]
  [clam (κ (u ...) exp)]
  [uaexp u ulam const (void) primop alloc-primop]
  [caexp k clam halt]
  [exp uexp ccall]
  [c integer bool null  ;; simplified
     top abs-int abs-bool] ;; abstract values
  [aint (integer) (abs-int)]
  [abool (bool) (abs-bool)]
  [bool #t #f]
  [const (qwote c)]
  [alloc-primop cons]
  [primop + - * / pair? null? < <= = >= > car cdr]
  [prim primop alloc-primop]
  [(u k x) variable-not-otherwise-mentioned])
(define-extended-language Annotated-CPS-Scheme CPS-Scheme
  [ulam (λ ulab (u ... k) exp)]
  [clam (κ clab (u ...) exp)]
  [lam ulam clam]
  [ccall (cont-call clab (caexp uaexp ...))]
  [uexp (user-exp ulab ucall)
        (user-exp ulab (if u exp exp))]
  [call ucall ccall]
  [(clab ulab lab scope-depth) natural])

(define-extended-language DCPS-machine Annotated-CPS-Scheme
  [ς ς-eval ς-entry ς-capply]
  [ς-eval (exp ρ σ Ξ D)]
  [ς-capply ((Ξ-kont clam ρ) (d ...) σ Ξ D)]
  [ς-colorable ς-capply ς-entry]
  [v prim c (void) (clo ulam ρ) continuation (cons-cell v v)]
  [continuation (σ-kont clam ρ Ξ D) (Ξ-kont clam ρ) halt]
  [tail-continuation k halt]
  [d (v ...)] ;; abstracted via ...
  [ρ ((x ℓ) ...)]
  [σ ((any d) ...)]
  [(D Ξ) (ξ ...)] ;; stacks are lists of stack frames
  [ξ ((x d) ...)] ;; stack frames are referenced positionally
  [ℓ Stack (Heap any)]
  ;; give names to certain configurations for understandable metafunctions
  [conf-kont (Ξ-kont clam ρ) halt]
  [ς-call    ((user-exp ulab (uaexp uaexp ... clam))              ρ σ Ξ D)]
  [ς-exit-tc ((user-exp ulab (uaexp uaexp ... tail-continuation)) ρ σ Ξ D)]
  [ς-final (halt (d ...) σ Ξ D)]
  [ς-entry ((clo ulam ρ) (d ...) conf-kont σ Ξ D)]
  [ς-exit-ret (side-condition ((cont-call (name lab clab) ((name cont tail-continuation) uaexp ...)) ρ σ Ξ D)
                              (S?ψ (term lab) (term cont)))]
  [ς-exit-exn (side-condition ((cont-call (name lab clab) ((name cont tail-continuation) uaexp ...)) ρ σ Ξ D)
                              (E?ψ (term lab) (term cont)))]
  [ς-exit-esc (side-condition ((cont-call (name lab clab) ((name cont tail-continuation) uaexp ...)) ρ σ Ξ D)
                              (H?ψ (term lab) (term cont)))]
  [ς-inner-ueval ((user-exp ulab (if u exp exp)) ρ σ Ξ D)
                 ((user-exp ulab (prim uaexp ... caexp)) clam ρ σ Ξ D)]
  [ς-inner-ceval ((cont-call clab ((λ clab (u ...)) uaexp)) ρ σ Ξ D)]
  [ς-intermediate ς-inner-ceval ς-inner-ueval ς-capply])
(define-extended-language D̂CPS-machine DCPS-machine
  [d (v ...)]
  [c .... top abs-int abs-bool])

(define-syntax-rule (is-state? pattern term)
  (not (not (redex-match DCPS-machine pattern term))))

;; These three meta-functions are the only ones needed to abstract
#;(define-metafunction DCPS-machine ;; concrete heap allocation
  [(alloc ((clo ulam ρ) (d ...) conf-kont σ Ξ D) (any ...))
   ,(add1 (max (max-nat-keys (term σ)) (max-nat-list (term (any ...)))))]
  [(alloc ((user-exp ulab (alloc-primop uaexp ... caexp)) ρ σ Ξ D) (any ...))
   ,(add1 (max (max-nat-keys (term σ)) (max-nat-list (term (any ...)))))]
  [(alloc ((Ξ-kont clam ρ) (d ...) σ Ξ D) (any ...))
   ,(add1 (max (max-nat-keys (term σ)) (max-nat-list (term (any ...)))))])

(define-metafunction DCPS-machine ;; abstract heap allocation (monovariant)
  [(alloc ((clo (λ ulab (x ...) exp) ρ) (d ...) conf-kont σ Ξ D) (any ...))
   ,(list-ref (term (x ...)) (length (term (any ...))))]
  [(alloc ((user-exp ulab (alloc-primop uaexp ... caexp)) ρ σ Ξ D) (any ...))
   ulab]
  [(alloc ((Ξ-kont (κ clab (u ...) exp) ρ) (d ...) σ Ξ D) (any ...))
   ,(list-ref (term (u ...)) (length (term (any ...))))])

(define-metafunction DCPS-machine
  [(combine-stores σ_1 σ_2)
   ,(for/fold ([ret (term σ_1)])
        ([(k vs) (in-dict (term σ_2))])
      (dict-set ret k (join-values vs (dict-ref ret k '()))))])

(define-metafunction DCPS-machine
  [(combine-frames ξ_1 ξ_2)
   ,(for/fold ([ret (term ξ_1)])
        ([(k vs) (in-dict (term ξ_2))])
      (dict-set ret k vs))])

(define-metafunction DCPS-machine
  [(env-lookup ρ x) ,(first (dict-ref (term ρ) (term x)))])
(define-metafunction DCPS-machine
  [(display-lookup D scope-depth) ,(list-ref (term D) (term scope-depth))])

(define-metafunction DCPS-machine
  [(env-extend ρ u ℓ) ,(dict-set (term ρ) (term u) (term (ℓ)))])
(define-metafunction DCPS-machine
  [(env-extend* ρ () ()) ρ]
  [(env-extend* ρ (u u_rest ..._i) (ℓ ℓ_rest ..._i))
   (env-extend* (env-extend ρ u ℓ) (u_rest ...) (ℓ_rest ...))])
(define-metafunction DCPS-machine
  [(update-display D scope-depth ξ) ,(list-update (term D) (term scope-depth) (term ξ))])

;; concrete push/pop
#|
 (define-metafunction DCPS-machine
  [(Ξ-pop (ξ_top ξ ...)) (ξ ...)])
 (define-metafunction DCPS-machine
  [(Ξ-push ξ (ξ_stack ...)) (ξ ξ_stack ...)])
|#
;; local push/pop
(define-metafunction DCPS-machine
  [(Ξ-pop (ξ_top ξ ...)) ()])
(define-metafunction DCPS-machine
  [(Ξ-push ξ (ξ_stack ...)) (ξ)])

(define-metafunction DCPS-machine
  [(Ξ-update x d (ξ_top ξ ...))
   (,(dict-set (term ξ_top) (term x) (term (d))) ξ ...)])

(define-metafunction DCPS-machine
  [(depth-of lab k)
   ,(hash-ref (call-label-info-vdepths (hash-ref label-ht (term lab))) (term k))])

(define-metafunction DCPS-machine
  [(Ξ-lookup x (ξ ξ_rest ...)) ,(first (dict-ref (term ξ) (term x)))])
(define-metafunction DCPS-machine
  [(D-lookup k ρ lab D) (Ξ-lookup k ((display-lookup D (depth-of lab k))))])
(define-metafunction DCPS-machine
  [(σ-lookup (Heap any_h) σ) ,(first (dict-ref (term σ) (term any_h)))])
(define-metafunction DCPS-machine
  [(ℓ-lookup σ ξ #t ρ u) (Ξ-lookup u (ξ))]
  [(ℓ-lookup σ ξ #f ρ u) (σ-lookup (env-lookup ρ u) σ)])

(define-metafunction DCPS-machine
  [(Au ulab u ρ σ D)
   ,(match-let* ([(call-label-info refcolors vdepths ulam-depth) (hash-ref label-ht (term ulab))]
                 [S? (not (eq? heap-ref (hash-ref refcolors (term u))))]
                 [depth (hash-ref vdepths (term u))])
      (cond [depth
             (term (ℓ-lookup σ (display-lookup D ,depth)
                             ,(begin (printf "Escaping ~a ~a~%" (term u) S?) S?)
                             ρ u))]
            [else (unless (set-member? prims (term u))
                    (error 'Au "non-primitive ~a" (term u)))
                  (term (u))]))] ;; primop
  [(Au ulab ulam ρ σ D) ((clo ulam ρ))]
  [(Au ulab (qwote c) ρ σ D) (c)]
  [(Au ulab (void) ρ σ D) ((void))]
  [(Au ulab prim ρ σ D) (prim)])

;; known to be on the stack due to RCPS
(define-metafunction DCPS-machine
  [(Ak clab k ρ D) (D-lookup k ρ clab D)]
  [(Ak clab clam ρ D) ((Ξ-kont clam ρ))]
  [(Ak clab halt ρ D) (halt)])

(define-metafunction DCPS-machine
  [(pop/restore-display lab k Ξ D)
   ((ξ_top ξ_rest ...) (update-display D (depth-of lab k) ξ_top))
   (where (ξ_top ξ_rest ...) (Ξ-pop Ξ))])

;; for concrete semantics
#;(define-metafunction DCPS-machine
  [(pop/rebind-necessarily ulab k    uaexp v ρ Ξ D) (pop/restore-display ulab k Ξ D)]
  [(pop/rebind-necessarily ulab clam ulam  v ρ Ξ D) (Ξ D)]
  [(pop/rebind-necessarily ulab clam prim  v ρ Ξ D) (Ξ D)]
  [(pop/rebind-necessarily ulab halt uaexp v ρ Ξ D) (Ξ D)]
  [(pop/rebind-necessarily ulab clam u     v ρ Ξ D)
   ,(match-let* ([(call-label-info refcolors vdepths ulam-depth) (hash-ref label-ht (term ulab))]
                 [S? (not (eq? heap-ref (hash-ref refcolors (term u))))]
                 [depth (hash-ref vdepths (term u))])
      (cond [S? (term-let ([(ξ_top ξ ...) (term (Ξ-update u (v) Ξ))])
                  (term ((ξ_top ξ ...) (update-display D ,depth ξ_top))))]
            [else (term (Ξ D))]))])
;; for local semantics
(define-metafunction DCPS-machine
  [(pop/rebind-necessarily ulab any_0 any_1 any_2 any_3 Ξ D) (Ξ D)])

(define ((var->loc ς σnew σlocs) i x v)
        (cond [(in-stack? x) (term Stack)]
              [else (define hloc (term (alloc ,ς ,(unbox σlocs))))
                    (set-box! σlocs (cons hloc (unbox σlocs)))
                    (set-box! σnew (term (combine-stores ,(unbox σnew) ((,hloc ,v)))))
                    (term (Heap ,hloc))]))

(define-metafunction DCPS-machine
  [(color-user ς bool_extend natural_depth (u ..._i) (d ..._i) ρ σ (ξ_top ξ ...) D)
   ,(let* ([σnew (box '())]
           [σlocs (box '())]
           [extend? (term bool_extend)]
           [ξ_next (cond [extend? (term (combine-frames ξ_top ((u d) ...)))]
                         [else (term ((u d) ...))])]
           [Ξ_next (cond [extend? (term (,ξ_next ξ ...))]
                         [else (term (,ξ_next ξ_top ξ ...))])])
      (term ((env-extend* ρ (u ...)
                          ,(mapi (var->loc (term ς) σnew σlocs)
                                 (term (u ...)) (term (d ...))))
             ,(unbox σnew) ,Ξ_next
             (update-display D natural_depth ,ξ_next) ,(unbox σlocs))))])

(define-metafunction DCPS-machine
  [(color-cont (name ς ((clo (λ ulab (u ... k) exp) ρ) (d ..._i) conf-kont σ Ξ D))
               natural_depth ρ_1 σ_1 Ξ_1 D_1 any)
   ((env-extend ρ_1 k ℓ)
    (combine-stores σ_1 σ_new)
    (ξ_top ξ_rest ...)
    (update-display D_1 natural_depth ξ_top))
   (where (ξ_top ξ_rest ...) (Ξ-update k (conf-kont) Ξ_1))
   (where (ℓ σ_new)
          ,(cond [(in-stack? (term k)) (term (Stack ()))]
                 [else (define hloc (term (alloc ς any)))
                       (define c
                         (cond [(eq? (term conf-kont) 'halt) 'halt]
                               [else (redex-let DCPS-machine ([(Ξ-kont clam ρ_c) (term conf-kont)])
                                       (term (σ-kont clam ρ_c Ξ D)))]))
                       (term ((Heap ,hloc)
                              ((,hloc (,c)))))]))])

(define-metafunction DCPS-machine
  [(take-branch d exp_1 exp_2)
   ,(append (cond [(term bool_then?) (term (exp_1))]
                  [else '()])
            (cond [(term bool_else?) (term (exp_2))]
                  [else '()]))
   (where bool_then? (possibly-non-false? d))
   (where bool_else? (possibly-false? d))])

;(color-cont ς natural_depth natural_ξloc k ρ_2 σ_comb σlocs)
(define R-DCPS-machine
  (reduction-relation DCPS-machine
    ;; user eval (call)
    [--> ((user-exp ulab (uaexp_0 uaexp ... caexp)) ρ σ Ξ D)
         (v (d ...) conf-kont σ Ξ_1 D_1)
         (where (v_pre ... (name v (clo ulam ρ_1)) v_post ...) (Au ulab uaexp_0 ρ σ D))
         (where (d ...) ((Au ulab uaexp ρ σ D) ...))
         (where (conf-kont) (Ak ulab caexp ρ D))
         (where (Ξ_1 D_1) (pop/rebind-necessarily ulab caexp uaexp_0 v ρ Ξ D))]
    ;; user eval (if)
    [--> ((user-exp ulab (if u exp_1 exp_2)) ρ σ Ξ D)
         (exp_choice ρ σ Ξ D)
         (where (exp_pre ... exp_choice exp_post ...)
                (take-branch (Au ulab u ρ σ D) exp_1 exp_2))]
    ;; user apply (primop)
    [--> ((user-exp ulab (primop uaexp ... caexp)) ρ σ Ξ D)
         (conf-kont ((δ primop d ...)) σ Ξ_1 D_1)
         (where (conf-kont) (Ak ulab caexp ρ D))
         (where (d ...) ((Au ulab uaexp ρ σ D) ...))
         (where (Ξ_1 D_1) (pop/rebind-necessarily ulab caexp primop primop ρ Ξ D))]
    ;; user apply (alloc-primop)
    [--> (name ς ((user-exp ulab (alloc-primop uaexp ... caexp)) ρ σ Ξ D))
         ;; XXX: probably wrong
         (conf-kont (d_res) (combine-stores σ ((any_hloc d_res))) Ξ_1 D_1)
         (where (conf-kont) (Ak ulab caexp ρ D))
         (where any_hloc (alloc ς ()))
         (where (d ...) ((Au ulab uaexp ρ σ D) ...))
         (where d_res (δ alloc-primop d ...))
         (where (Ξ_1 D_1) (pop/rebind-necessarily ulab caexp alloc-primop alloc-primop ρ Ξ D))]
    ;; user apply (entry)
    [--> (name ς ((clo (λ ulab (u ... k) exp) ρ) (d ..._i) conf-kont σ Ξ D))
         (exp ρ_2 (combine-stores σ_comb σ_new2) Ξ_2 D_2)
         (where natural_depth ,(hash-ref label-ht (term ulab)))
         (where (ρ_1 σ_new Ξ_1 D_1 (name σlocs (any ...)))
                (color-user ς #f natural_depth (u ...) (d ...) ρ σ Ξ D))
         (where σ_comb (combine-stores σ σ_new))
         (where (ρ_2 σ_new2 Ξ_2 D_2)
                (color-cont ς natural_depth ρ_1 σ_comb Ξ_1 D_1 σlocs))]
    ;; continuation apply (capply)
    [--> (name ς ((Ξ-kont (κ clab (u ..._i) exp) ρ) (d ..._i) σ Ξ D))
         (exp ρ_1 (combine-stores σ σ_new) Ξ_1 D_1)
         (where (ρ_1 σ_new Ξ_1 D_1 any)
          (color-user ς #t ,(hash-ref label-ht (term clab)) (u ...) (d ...) ρ σ Ξ D))]
    ;; continutation eval (let)
    [--> ((cont-call clab (clam uaexp ...)) ρ σ Ξ D)
         ((Ξ-kont clam ρ) (d ...) σ Ξ D)
         (where (d ...) ((Au clab uaexp ρ σ D) ...))]
    ;; continutation eval (return)
    [--> ς-exit-ret
         (conf-kont (d ...) σ Ξ_1 D_1)
         (where ((cont-call clab (k uaexp ...)) ρ σ Ξ D) ς-exit-ret)
         (where (conf-kont) (D-lookup k ρ clab D))
         (where (d ...) ((Au clab uaexp ρ σ D) ...))
         (where (Ξ_1 D_1) (pop/restore-display clab k Ξ D))]
    ;; continutation eval (escape)
    [--> ς-exit-esc
         ((Ξ-kont clam ρ_1) (d ...) σ Ξ_1 D_1)
         (where ((cont-call clab (k uaexp ...)) ρ σ Ξ D) ς-exit-esc)
         (where (d ...) ((Au clab uaexp ρ σ D) ...))
         (where (σ-kont clam ρ_1 Ξ_1 D_1) (σ-lookup (env-lookup ρ k) σ))]
    ))

(define (ς-over-k? ς kterm)
  (redex-let DCPS-machine
    ([((clo (λ ulab (u ... k) exp) ρ) (d ..._i) conf-kont σ Ξ D) ς])
    (eq? kterm (term k))))
(define (ς-calls-k? ς kterm)
  (redex-let DCPS-machine
    ([((cont-call clab (k uaexp ...)) ρ σ Ξ D) ς])
    (eq? kterm (term k))))

;; Dress up the data manipulation to look more like the math.
(define-syntax-rule (for-callers Callers (ς̃entry ς̃call ς̃callee-entry) body1 body ...)
  (for ([(ς̃entry caller×callee) (in-hash Callers)]
        #:when (equal? ς̃callee-entry (second caller×callee)))
    (let ([ς̃call (first caller×callee)])
      body1 body ...)))
(define-syntax-rule (for-summary Summary (ς̃entry ς̃exit) body1 body ...)
  (for ([ς̃exit (in-set (hash-ref Summary ς̃entry (set)))])
    body1 body ...))
(define-syntax for-escaping-entries
  (syntax-rules (over)
    [(_ EntriesEsc (ςentry over k) body1 body ...)
     (for ([(ςentry _) (in-hash EntriesEsc)]
           #:when (ς-over-k? ςentry (term k)))
       body1 body ...)]))
(define-syntax for-escapes
  (syntax-rules (calls)
    [(_ Escapes (ςexit calls k) body1 body ...)
     (for ([(ςexit _) (in-hash Escapes)]
           #:when (ς-calls-k? ςexit (term k)))
       body1 body ...)]))
#;
(define-syntax for-active-paths
  (syntax-rules (over binds calls)
    [(_ Callers TCallers (ςentry (ςcall over k) ςcallee-entry) body1 body ...)
     (let ([W (make-hash)])
       (let loop ([callee-entry ςcallee-entry])
         (cond [(ς-over-k? ςcall (term k))
                body1 body ...]
               [else
                (for-callers Callers (ςentry ςcall callee-entry)
                  (μ-guard (list ςentry ςcall callee-entry) W (loop ςentry)))
                (for-callers TCallers (ςentry ςcall callee-entry)
                  (μ-guard (list ςentry ςcall callee-entry) W (loop ςentry)))])))]))
(define-syntax-rule (insert-caller! Callers (ς̃entry ς̃call ς̃callee-entry))
  (hash-set! Callers ς̃entry (list ς̃call ς̃callee-entry)))
(define-syntax-rule (add-summary! Summary (ς̃entry ς̃exit))
  (hash-set! Summary ς̃entry (set-add (hash-ref Summary ς̃entry (set)) ς̃exit)))
(define-syntax-rule (μ-guard e W body1 body ...)
  (let ([x e])
    (unless (hash-has-key? W e)
      (insert! e W)
      body1 body ...)))

(define (insert! k . hts) (for ([ht (in-list hts)]) (hash-set! ht k #t)))

(define (GCFA2 e [tr translate])
  (define I (inject e tr))
  (define initial-work (list I I))
  ;; Some notational definitions
  (define (succ ς̃) (apply-reduction-relation R-DCPS-machine ς̃))
  (define (Seen? pair) (hash-has-key? Seen pair))
  (define (in-Summary? ς̃₁ ς̃₂) (set-member? (hash-ref Summary ς̃₁ '()) ς̃₂))
  (define (name-ς ς) (strip-annotation ς names))
  (define (add-summaries! S)
    (for ([(entry exits) (in-hash S)])
      (hash-set! Summary entry (set-union (hash-ref Summary entry (set)) exits))))
  ;; Summary : entry ↦ setof exit
  ;; Seen/Work : (list state state) ↦ #t
  ;; Callers/TCallers : entry ↦ (list caller entry)
  ;; Final : state ↦ #t
  (define-values (Summary ΞSummary Seen Callers TCallers EntriesEsc Escapes)
    (apply values (build-list 7 (λ _ (make-hash)))))
  (define-values (Final Work) (values (make-hasheq) (make-hasheq)))
  (define (Update! ς̃₁ ς̃₂ ς̃₃ ς̃₄)
    (apply printf "Updating ~%〈~a,~% ~a,~% ~a,~% ~a〉~%" (map name-ς (list ς̃₁ ς̃₂ ς̃₃ ς̃₄)))
    (redex-let* DCPS-machine
      ([ς-entry_1 ς̃₁]
       [((user-exp ulab_2 (uaexp_f uaexp_e ... clam)) ρ_2 σ_2 Ξ_2 D_2) ς̃₂]
       [((clo ulam_3 ρ_3) (d_3 ...) conf-kont σ_3 Ξ_3 D_3) ς̃₃]
       [((cont-call clab_4 (k_4 uaexp_4 ...)) ρ_4 σ_4 Ξ_4 D_4) ς̃₄]
       [(d_next ...) (term ((Au clab_4 uaexp_4 ρ_4 σ_4 D_4) ...))]
       [(Ξ_next D_next)
        (cond [(and (symbol? (term uaexp_f))
                    (Ξ?ψ (term ulab_2) (term uaexp_f)))
               (define Ξ_next (term (Ξ-update uaexp_f ((clo ulam_3 ρ_3)) Ξ_2)))
               (term (,Ξ_next (update-display D_2 (depth-of ulab_2 uaexp_f) ,(first Ξ_next))))]
              [else (term (Ξ_2 D_2))])]
       [ς (term ((Ξ-kont clam ρ_2) (d_next ...) σ_4 Ξ_next D_next))])
      (Propagate! ς̃₁ (term ς) #f)))
  (define (Propagate! ς̃₁ ς̃₂ escaping?)
    (define pair (list ς̃₁ ς̃₂))
    (when escaping? (insert! pair Summary))
    (μ-guard pair Seen (insert! pair Work)))
  (define (Intermediate! ς̃₁ ς̃₂)
    (for ([ς̃₃ (in-list (succ ς̃₂))])
      (Propagate! ς̃₁ ς̃₃ #f)))

  (insert! initial-work Seen Work)
  (let analyze ()
    (match (set-grab Work)
      [#f (list Summary Final)] ;; done
      [(list ς̃₁ ς̃₂)
       (apply printf "Processing ~%〈~a,~% ~a〉~%" (map name-ς (list ς̃₁ ς̃₂)))
       ((term-match/single DCPS-machine
          [ς-intermediate (Intermediate! ς̃₁ ς̃₂)]
          ;; entry
          [((clo (λ ulab (u ..._i k) exp) ρ) (d ..._i) conf-kont σ Ξ D)
           (Intermediate! ς̃₁ ς̃₂)
           (case-alloc (dict-ref coloring (term k) stack-ref)
             [heap (insert! ς̃₂ EntriesEsc)
                   (for-escapes Escapes (ς̃₃ calls k) (Propagate! ς̃₂ ς̃₃ #t))])]
          [ς-call
           (for ([ς̃₃ (in-list (succ ς̃₂))])
             (Propagate! ς̃₃ ς̃₃ #f)
             (insert-caller! Callers (ς̃₁ ς̃₂ ς̃₃))
             (for-summary Summary (ς̃₃ ς̃₄) (Update! ς̃₁ ς̃₂ ς̃₃ ς̃₄)))]
          [ς-final (insert! ς̃₂ Final)]
          ;; exit-ret/esc/exn
          [((cont-call clab (k uaexp ...)) ρ σ Ξ D)
           (match-define (call-label-info refcolors vdepths ulam-depth)
                         (hash-ref label-ht (term clab)))
           (define color (dict-ref refcolors (term k) stack-ref))
           (cond [(and (not (eq? color heap-ref)) (equal? ς̃₁ I))
                  (insert! ς̃₂ Final)]
                 [else
                  (case-alloc color
                    [local
                     (add-summary! Summary (ς̃₁ ς̃₂))
                     (for-callers Callers (ς̃₃ ς̃₄ ς̃₁) (Update! ς̃₃ ς̃₄ ς̃₁ ς̃₂))
                     (for-callers TCallers (ς̃₃ ς̃₄ ς̃₁) (Propagate! ς̃₃ ς̃₂ #f))]
                    [exn
                     (cond [(not (in-Summary? ς̃₁ ς̃₂)) ;; not a regular summary edge.
                            (for-active-paths Callers TCallers (ς̃exn-ctx (ς̃exn over k) ς̃₂)
                              (Update! ς̃exn-ctx ς̃exn ς̃₁ ς̃₂))]
                           [(equal? ς̃₁ I) (insert! ς̃₂ Final)]
                           [else])]
                    [heap
                     (cond [(not (in-Summary? ς̃₁ ς̃₂))
                            (insert! ς̃₂ Escapes)
                            (for-escaping-entries EntriesEsc (ς̃₃ over k) (Propagate! ς̃₁ ς̃₃ #t))]
                           [(equal? ς̃₁ I) (insert! ς̃₂ Final)]
                           [else
                            (add-summary! Summary (ς̃₁ ς̃₂))
                            (for-callers Callers (ς̃₃ ς̃₄ ς̃₁) (Update! ς̃₃ ς̃₄ ς̃₁ ς̃₂))
                            (for-callers TCallers (ς̃₃ ς̃₄ ς̃₁) (Propagate! ς̃₃ ς̃₂ #t))])])])]
          ;; tail call
          [ς-exit-tc
           (printf "Tail call~%")
           (for ([ς̃₃ (in-list (succ ς̃₂))])
             (Propagate! ς̃₃ ς̃₃ #f)
             (insert-caller! TCallers (ς̃₁ ς̃₂ ς̃₃))
             (let ([S (make-hash)])
               (for-summary Summary (ς̃₃ ς̃₄)
                 (add-summary! S (ς̃₁ ς̃₄))
                 (Propagate! ς̃₁ ς̃₄ #f))
               (add-summaries! S)))]

          [any (error 'analyze "Uncaught case ~a~%" ς̃₂)])
        ς̃₂)
       (analyze)])))

(define (prepare e [tr translate])
  (set! coloring (make-hasheq))
  (set! label-ht (make-hasheq))
  (set! names (make-hasheq))
  (define cps-e (cps-conv (tr e)))
  (define cps-e* (escape-analysis! cps-e coloring label-ht #:original-name-ht names))
  (pretty-print (redex-match DCPS-machine ulam (second (third cps-e*))))
  (pretty-print (redex-match DCPS-machine clam (third (third cps-e*))))
  (pretty-print cps-e) (newline)
  (pretty-print cps-e*) (newline)
  (pretty-print label-ht) (newline)
  (pretty-print coloring)
  cps-e*)
(define (inject e [tr translate])
  (term (,(prepare e tr) () () (()) (()))))

;; concrete δ dispatcher
#;(define-metafunction DCPS-machine ;; primop implementation
  [(δ primop (v) ...) ((δc primop v ...))]
  [(δ alloc-primop (v) ...) ((δc alloc-primop v ...))])
(define-metafunction DCPS-machine ;; primop implementation
  [(δc + integer ...) ,(apply + (term (integer ...)))]
  [(δc - integer ...) ,(apply - (term (integer ...)))]
  [(δc * integer ...) ,(apply * (term (integer ...)))]
  [(δc / integer ...) ,(apply / (term (integer ...)))]
  [(δc < integer_0 integer_1) ,(< (term integer_0) (term integer_1))]
  [(δc <= integer_0 integer_1) ,(<= (term integer_0) (term integer_1))]
  [(δc = integer_0 integer_1) ,(= (term integer_0) (term integer_1))]
  [(δc >= integer_0 integer_1) ,(>= (term integer_0) (term integer_1))]
  [(δc > integer_0 integer_1) ,(> (term integer_0) (term integer_1))]
  [(δc pair? v) ,(not (not (redex-match DCPS-machine (cons-cell v_0 v_1) (term v))))]
  [(δc null? v) ,(eq? (term v) 'null)]
  [(δc zero? v) ,(zero? (term v))]
  [(δc boolean? v) ,(boolean? (term v))]
  [(δc procedure? v) ,(not (not (or (redex-match DCPS-machine (clo ulam ρ) (term v))
                                   (redex-match DCPS-machine conf-kont (term v)))))]
  [(δc cons v_0 v_1) (cons-cell v_0 v_1)]
  [(δc car (cons-cell v_0 v_1)) v_0]
  [(δc cdr (cons-cell v_0 v_1)) v_1])

;; abstract δ dispatcher
(define-metafunction DCPS-machine ;; primop implementation
  [(δ prim d ...) ((δa prim d ...))])
(define (abstract-value? v) (not (memv v '(top abs-int abs-bool))))
(define (non-clo-pair? x) (and (pair? x) (not (clo? x))))
(define (clo? x) (match x [`(clo ,lam ,ρ) #t] [_ #f]))

(define-metafunction DCPS-machine
  [(possibly-false? top) #t]
  [(possibly-false? abs-int) #f]
  [(possibly-false? integer) #f]
  [(possibly-false? abs-bool) #t]
  [(possibly-false? #t) #f]
  [(possibly-false? #f) #t]
  [(possibly-false? void) #f]
  [(possibly-false? null) #f]
  [(possibly-false? (cons-cell v_1 v_2)) #f])

(define-metafunction DCPS-machine
  [(possibly-non-false? top) #t]
  [(possibly-non-false? abs-int) #t]
  [(possibly-non-false? integer) #t]
  [(possibly-non-false? abs-bool) #t]
  [(possibly-non-false? #t) #t]
  [(possibly-non-false? #f) #f]
  [(possibly-non-false? void) #t]
  [(possibly-non-false? null) #t]
  [(possibly-non-false? (cons-cell v_1 v_2)) #t])

(define-metafunction DCPS-machine ;; abstract primop implementation
  [(δa + aint ...) abs-int]
  [(δa - aint ...) abs-int]
  [(δa * aint ...) abs-int]
  [(δa / aint ...) abs-int]
  [(δa < aint_0 aint_1) ,(cond [(or (abstract-value? (term aint_0))
                                    (abstract-value? (term aint_1)))
                                (term abs-bool)]
                               [else (< (term aint_0) (term aint_1))])]
  [(δa <= aint_0 aint_1) ,(cond [(or (abstract-value? (term aint_0))
                                     (abstract-value? (term aint_1)))
                                 (term abs-bool)]
                                [else (<= (term aint_0) (term aint_1))])]
  [(δa = aint_0 aint_1) ,(cond [(or (abstract-value? (term aint_0))
                                    (abstract-value? (term aint_1)))
                                (term abs-bool)]
                               [else (= (term aint_0) (term aint_1))])]
  [(δa >= aint_0 aint_1) ,(cond [(or (abstract-value? (term aint_0))
                                     (abstract-value? (term aint_1)))
                                 (term abs-bool)]
                                [else (>= (term aint_0) (term aint_1))])]
  [(δa > aint_0 aint_1) ,(cond [(or (abstract-value? (term aint_0))
                                    (abstract-value? (term aint_1)))
                                (term abs-bool)]
                               [else (> (term aint_0) (term aint_1))])]
  [(δa pair? (cons-cell v_0 v_1)) #t]
  [(δa pair? top) abs-bool]
  [(δa pair? v) #f
   (side-condition (and (not (eq? (term v) 'top))
                        (not (redex-match DCPS-machine (cons-cell v_0 v_1) (term v)))))]
  [(δa null? top) abs-bool]
  [(δa null? null) #t]
  [(δa null? v) #f
   (side-condition (not (memv (term v) '(top null))))]
  [(δa zero? 0) #t]
  [(δa zero? abs-int) abs-bool]
  [(δa zero? top) abs-bool]
  [(δa zero? v) #f
   (side-condition (not (memv (term v) '(top abs-int 0))))]
  [(δa boolean? abool) #t]
  [(δa boolean? top) abs-bool]
  [(δa boolean? v) #f
   (side-condition (not (memv (term v) '(top #t #f abs-bool))))]
  [(δa procedure? top) abs-bool]
  [(δa procedure? v) ,(not (not (or (redex-match DCPS-machine (clo lam ρ) (term v))
                                    (redex-match DCPS-machine continuation (term v)))))
   (side-condition (not (eq? (term v) 'top)))]
  [(δa car (cons-cell v_0 v_1)) v_0]
  [(δa car top) top]
  [(δa cdr (cons-cell v_0 v_1)) v_1]
  [(δa cdr top) top])

(define (join-values vs₁ vs₂)
  (cond [(empty? vs₁) vs₂]
        [(empty? vs₂) vs₁]
        [else (match (join-value/values (first vs₁) vs₂)
                [(? non-clo-pair? p) (join-values (rest vs₁) (append-nodups p vs₂))]
                [(? null?) (join-values (rest vs₁) vs₂)]
                [a (join-values (rest vs₁) (nodup-cons a vs₂))])]))

(define (join-value/values v vs)
  (cond [(empty? vs) '()]
        [else (match (join-value/value v (first vs))
                [(? non-clo-pair? p) (append p (rest vs))]
                [a (join-value/values a (rest vs))])]))

(define (join-value/value v₁ v₂)
  (define (join-base pred abs v)
    (match v
      [(or (? (λ (x) (eq? x abs))) (? pred)) abs]
      [else 'top]))
  (cond [(equal? v₁ v₂) v₁]
        [(or (eq? v₁ 'top) (eq? v₂ 'top)) 'top]
        [(or (clo? v₁) (clo? v₂)) (list v₁ v₂)]
        [(or (integer? v₁) (eq? v₁ 'abs-int)) (join-base integer? 'abs-int v₂)]
        [(or (integer? v₂) (eq? v₂ 'abs-int)) (join-base integer? 'abs-int v₂)]
        [(or (boolean? v₁) (eq? v₁ 'abs-bool)) (join-base boolean? 'abs-bool v₂)]
        [(or (boolean? v₂) (eq? v₂ 'abs-bool)) (join-base boolean? 'abs-bool v₂)]
        [else 'top]))

(define t '(let* ([app (λ (f e) (f e))]
                           [id (λ (x) x)]
                           [n1 (app id 1)]
                           [n2 (app id 2)])
                      (+ n1 n2)))

(GCFA2 t)

;(define esop (call-with-input-string (format "(~a)" (call-with-input-file "esop.sch" port->string)) read))
;(define I (inject esop translate-top))
;(define ς (first (apply-reduction-relation* R-DCPS-machine I)))

(initial-font-size 7)

(define (apply-reduction-relation-n R n t)
  (let loop ([n n] [i 0] [t t])
    (unless (zero? n)
      (define ts (apply-reduction-relation R t))
      (unless (empty? ts)
        (define t* (first ts))
        (printf "Step: ~a~%" i)
        (pretty-print t*) (newline)
        (loop (sub1 n) (add1 i) t*)))))
;(traces R-DCPS-machine I)


#;(define I (term (inject ,(escape-analysis! esop* coloring #:annotate-static-depth? #t #:original-name-ht names))))
#;(apply-reduction-relation* R-Istack I)
