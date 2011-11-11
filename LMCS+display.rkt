#lang racket

(require redex
         "def-scheme-to-expr-scheme.rkt"
         "expr-scheme-to-CPS.rkt"
         "cps-escape-analysis.rkt"
         "utils.rkt"
         racket/trace)
(provide (all-defined-out))

(define coloring (make-hasheq))
(define names (make-hasheq))
(define label-ht (make-hasheq))
(define (in-stack? x) (dict-ref coloring x #t))
(define (in-heap? x) (not (in-stack? x)))
(define (S?ψ label v)
  (match-define (call-label-info ht depth) (hash-ref label-ht label))
  (hash-ref ht v))
(define (H?ψ label v) (not (S?ψ label v)))
(trace S?ψ H?ψ)

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
  [c integer bool null] ;; simplified
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
  [d (v)] ;; abstracted later
  [ρ ((x ℓ) ...)]
  [σ ((any d) ...)]
  [(D Ξ) (ξ ...)] ;; stacks are lists of stack frames
  [ξ ((x d) ...)] ;; stack frames are referenced positionally
  [ℓ Stack (Heap any)]
  ;; give names to certain configurations for understandable metafunctions
  [conf-kont (Ξ-kont clam ρ) halt]
  [ς-call (ucall ρ σ Ξ D)]
  [ς-entry ((clo ulam ρ) (d ...) conf-kont σ Ξ D)]
  [ς-exit-ret (side-condition ((cont-call (name lab clab) ((name cont k) uaexp ...)) ρ σ Ξ D)
                              (S?ψ (term lab) (term cont)))]
  [ς-exit-esc (side-condition ((cont-call (name lab clab) ((name cont k) uaexp ...)) ρ σ Ξ D)
                              (H?ψ (term lab) (term cont)))]
  [ς-exit-tc ((user-exp ulab (uaexp uaexp ... k)) ρ σ Ξ D)]
  [ς-inner-ueval ((user-exp ulab (if u exp exp)) ρ σ Ξ D)
                 ((user-exp ulab (prim uaexp ... caexp)) clam ρ σ Ξ D)]
  [ς-inner-ceval ((cont-call clab ((λ clab (u ...)) uaexp)) ρ σ Ξ D)])
(define-extended-language D̂CPS-machine DCPS-machine
  [d (v ...)]
  [c .... top abs-int abs-bool])

(define-syntax-rule (is-state? pattern term)
  (not (not (redex-match DCPS-machine pattern term))))

;; These three meta-functions are the only ones needed to abstract
(define-metafunction DCPS-machine ;; heap allocation
  [(alloc ((clo ulam ρ) (d ...) conf-kont σ Ξ D) (any ...))
   ,(add1 (max (max-nat-keys (term σ)) (max-nat-list (term (any ...)))))]
  [(alloc ((user-exp ulab (alloc-primop uaexp ... caexp)) ρ σ Ξ D) (any ...))
   ,(add1 (max (max-nat-keys (term σ)) (max-nat-list (term (any ...)))))]
  [(alloc ((Ξ-kont clam ρ) (d ...) σ Ξ D) (any ...))
   ,(add1 (max (max-nat-keys (term σ)) (max-nat-list (term (any ...)))))])

(define-metafunction DCPS-machine
  [(combine-stores σ_1 σ_2)
   ,(for/fold ([ret (term σ_1)])
        ([(k vs) (in-dict (term σ_2))])
      (dict-set ret k vs))])

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

(define-metafunction DCPS-machine
  [(Ξ-pop (ξ_top ξ ...)) (ξ ...)])
(define-metafunction DCPS-machine
  [(Ξ-push ξ (ξ_stack ...)) (ξ ξ_stack ...)])

(define-metafunction DCPS-machine
  [(Ξ-update x d (ξ_top ξ ...))
   (,(dict-set (term ξ_top) (term x) (term (d))) ξ ...)])

(define-metafunction DCPS-machine
  [(depth-of lab k)
   ,(hash-ref (call-label-info-depth-ht (hash-ref label-ht (term lab))) (term k))])

(define-metafunction DCPS-machine
  [(Ξ-lookup x (ξ ξ_rest ...)) ,(first (dict-ref (term ξ) (term x)))])
(define-metafunction DCPS-machine
  [(D-lookup k ρ lab D) (Ξ-lookup k ((display-lookup D (depth-of lab k))))])
(define-metafunction DCPS-machine
  [(σ-lookup (Heap natural_h) σ) ,(first (dict-ref (term σ) (term natural_h)))])
(define-metafunction DCPS-machine
  [(ℓ-lookup σ ξ #t ρ u) (Ξ-lookup u (ξ))]
  [(ℓ-lookup σ ξ #f ρ u) (σ-lookup (env-lookup ρ u) σ)])

(define-metafunction DCPS-machine
  [(Au ulab u ρ σ D)
   ,(match-let* ([(call-label-info stack-ht depth-ht) (hash-ref label-ht (term ulab))]
                 [S? (hash-ref stack-ht (term u))]
                 [depth (hash-ref depth-ht (term u))])
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

(define-metafunction DCPS-machine
  [(pop/rebind-necessarily ulab k    uaexp v ρ Ξ D) (pop/restore-display ulab k Ξ D)]
  [(pop/rebind-necessarily ulab clam ulam  v ρ Ξ D) (Ξ D)]
  [(pop/rebind-necessarily ulab clam prim  v ρ Ξ D) (Ξ D)]
  [(pop/rebind-necessarily ulab halt uaexp v ρ Ξ D) (Ξ D)]
  [(pop/rebind-necessarily ulab clam u     v ρ Ξ D)
   ,(match-let* ([(call-label-info stack-ht depth-ht) (hash-ref label-ht (term ulab))]
                 [S? (hash-ref stack-ht (term u))]
                 [depth (hash-ref depth-ht (term u))])
      (cond [S? (term-let ([(ξ_top ξ ...) (term (Ξ-update u (v) Ξ))])
                  (term ((ξ_top ξ ...) (update-display D ,depth ξ_top))))]
            [else (term (Ξ D))]))])

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
  [(take-branch (#f) exp_1 exp_2) (exp_2)]
  [(take-branch (v) exp_1 exp_2) (exp_1) (side-condition (term v))])

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
                (color-cont ς natural_depth ρ_1 σ_comb Ξ_1 D_1 σlocs))
         (side-condition (printf "##Entry##~%"))]
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
         (where (σ-kont clam ρ_1 Ξ_1 D_1) (σ-lookup (env-lookup ρ k) σ))
         (side-condition (printf "Escape!~%"))]
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
(define-syntax-rule (insert-caller! Callers (ς̃entry ς̃call ς̃callee-entry))
  (hash-set! Callers ς̃entry (list ς̃call ς̃callee-entry)))
(define-syntax-rule (add-summary! Summary (ς̃entry ς̃exit))
  (hash-set! Summary ς̃entry (set-add (hash-ref Summary ς̃entry (set)) ς̃exit)))

(define (GCFA2 e)
  (define e′ (escape-analysis! e coloring #:annotate-static-depth? #t #:original-name-ht names))
  (define I (inject e′))
  (define initial-work (list I I))
  ;; Some notational definitions
  (define (succ ς̃) (apply-reduction-relation R-DCPS-machine ς̃))
  (define (insert! k . hts) (for ([ht (in-list hts)]) (hash-set! ht k #t)))
  (define (Seen? pair) (hash-has-key? Seen pair))
  (define (in-Summary? ς̃₁ ς̃₂) (set-member? (hash-ref Summary ς̃₁ '()) ς̃₂))
  (define (name-ς ς) (strip-annotation ς names))
  ;; Summary : entry ↦ setof exit
  ;; Seen/Work : (list state state) ↦ #t
  ;; Callers/TCallers : entry ↦ (list caller entry)
  ;; Final : state ↦ #t
  (define-values (Summary Seen Callers TCallers EntriesEsc Escapes)
    (values (make-hash) (make-hash) (make-hash) (make-hash) (make-hash) (make-hash)))
  (define-values (Final Work) (values (make-hasheq) (make-hasheq)))
  (define (Update! ς̃₁ ς̃₂ ς̃₃ ς̃₄)
    (apply printf "Updating ~%〈~a,~% ~a,~% ~a,~% ~a〉~%" (map name-ς (list ς̃₁ ς̃₂ ς̃₃ ς̃₄)))
    #;(redex-let DCPS-machine (...) (Propagate! ς̃₁ (term (v_4 σ_4 Ξ_2 D_2 κ_2)))))
  (define (Propagate! ς̃₁ ς̃₂ escaping?)
    (define pair (list ς̃₁ ς̃₂))
    (when escaping? (insert! pair Summary))
    (unless (Seen? pair) (insert! pair Seen Work)))

  (insert! initial-work Seen Work)
  (let analyze ()
    (match (set-grab Work)
      [#f (list Summary Final)] ;; done
      [(list ς̃₁ ς̃₂)
       (apply printf "Processing ~%〈~a,~% ~a〉~%" (map name-ς (list ς̃₁ ς̃₂)))
       (define is-entry? (is-state? ς-entry ς̃₂))
       (cond [(or (is-state? ς-inner-ueval ς̃₂)
                  (is-state? ς-inner-ceval ς̃₂)
                  (is-state? ς-capply ς̃₂)
                  is-entry?)
              (for ([ς̃₃ (in-list (succ ς̃₂))])
                (Propagate! ς̃₁ ς̃₃ #f))
              (when is-entry?
                (printf "Entry~%")
                (redex-let DCPS-machine
                ([((clo (λ ulab (u ... k) exp) ρ) (d ..._i) conf-kont σ Ξ D) ς̃₂])
                (unless (in-stack? (term k))
                  (insert! ς̃₂ EntriesEsc)
                  (for-escapes Escapes (ς̃₃ calls k) (Propagate! ς̃₂ ς̃₃ #t)))))]

             [(is-state? ς-call ς̃₂) (printf "Call~%")
              (for ([ς̃₃ (in-list (succ ς̃₂))])
                (Propagate! ς̃₃ ς̃₃)
                (insert-caller! Callers (ς̃₁ ς̃₂ ς̃₃))
                (for-summary Summary (ς̃₃ ς̃₄) (Update! ς̃₁ ς̃₂ ς̃₃ ς̃₄)))]

             [(is-state? ς-exit-ret ς̃₂) (printf "Return (TODO downward continuation summaries)~%")
              (cond [(equal? ς̃₁ I) (insert! ς̃₂ Final)]
                    [else
                     (add-summary! Summary (ς̃₁ ς̃₂))
                     (for-callers Callers (ς̃₃ ς̃₄ ς̃₁) (Update! ς̃₃ ς̃₄ ς̃₁ ς̃₂))
                     (for-callers TCallers (ς̃₃ ς̃₄ ς̃₁) (Propagate! ς̃₃ ς̃₂ #f))])]

             [(is-state? ς-exit-esc ς̃₂) (printf "Call non-downward continuation~%")
              (cond [(not (in-Summary? ς̃₁ ς̃₂))
                     (insert! ς̃₂ Escapes)
                     (redex-let DCPS-machine
                       ([((cont-call clab (k uaexp ...)) ρ σ Ξ D) ς̃₂])
                       (for-escaping-entries EntriesEsc (ς̃₃ over k) (Propagate! ς̃₁ ς̃₃ #t)))]
                    [(equal? ς̃₁ I) (insert! ς̃₂ Final)]
                    [else
                     (add-summary! Summary (ς̃₁ ς̃₂))
                     (for-callers Callers (ς̃₃ ς̃₄ ς̃₁) (Update! ς̃₃ ς̃₄ ς̃₁ ς̃₂))
                     (for-callers TCallers (ς̃₃ ς̃₄ ς̃₁) (Propagate! ς̃₃ ς̃₂ #t))])]

             [(is-state? ς-exit-tc ς̃₂) (printf "Tail call~%")
              (for ([ς̃₃ (in-list (succ ς̃₂))])
                (Propagate! ς̃₃ ς̃₃ #f)
                (insert-caller! TCallers (ς̃₁ ς̃₂ ς̃₃))
                (for-summary Summary (ς̃₃ ς̃₄)
                  (add-summary! Summary (ς̃₁ ς̃₄))
                  (Propagate! ς̃₁ ς̃₄ #f)))]

             [else (error 'analyze "Uncaught case ~a~%" ς̃₂)])
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

(define-metafunction DCPS-machine ;; primop implementation
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
#|
 (define esop (call-with-input-string (format "(~a)" (call-with-input-file "esop.sch" port->string)) read))
 (define esop* (translate-top esop))
 esop*
 (newline)
 (GCFA2 esop*)
|#


(define t '(let* ([app (λ (f e) (f e))]
                           [id (λ (x) x)]
                           [n1 (app id 1)]
                           [n2 (app id 2)])
                      (+ n1 n2)))
(define esop (call-with-input-string (format "(~a)" (call-with-input-file "esop.sch" port->string)) read))
(define I (inject esop translate-top))
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
(apply-reduction-relation* R-DCPS-machine I)
;(traces R-DCPS-machine I)


;(GCFA2 t2)
#;(define I (term (inject ,(escape-analysis! esop* coloring #:annotate-static-depth? #t #:original-name-ht names))))
#;(apply-reduction-relation* R-Istack I)
