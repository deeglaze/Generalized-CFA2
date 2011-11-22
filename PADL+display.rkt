#lang racket

(require redex
         "def-scheme-to-expr-scheme.rkt"
         "expr-scheme-to-CPS.rkt"
         "cps-escape-analysis.rkt"
         "LMCS+display-basics.rkt"
         "utils.rkt"
         racket/trace)
(provide (all-defined-out))

(define (free-vars e)
  (Annotated-CPS-Scheme-free-vars e #f))

;; These meta-functions are the ones needed to abstract.

;; abstract/local heap allocation (monovariant)
(define-metafunction DCPS-machine
  [(alloc ((clo (λ ulab (x ...) exp) ρ) (d ...) conf-kont σ Ξ D) (any ...))
   ,(list-ref (term (x ...)) (length (term (any ...))))]
  [(alloc ((user-exp ulab (alloc-primop uaexp ... caexp)) ρ σ Ξ D) (any ...))
   ulab]
  [(alloc ((Ξ-kont (κ clab (u ...) exp) ρ) (d ...) σ Ξ D) (any ...))
   ,(list-ref (term (u ...)) (length (term (any ...))))])

;; localized metafunctions
(define-metafunction DCPS-machine
  [(Ξ-pop (ξ_top ξ ...)) ()])
(define-metafunction DCPS-machine
  [(Ξ-push ξ (ξ_stack ...)) (ξ)])

;; if pushing values that reference the stack at the same nesting depth, then join!
(define-metafunction DCPS-machine
  [(color-user ς bool_extend natural_depth (u ..._i) (d ..._i) ρ σ (ξ_top ξ ...) D)
   ,(let ()
      (define loss? (box #f))
      (let/ec return
        (let recur ([GCed? #f] [σ (term σ)] [D (term D)])
          (define (combine-stores σ₁ σ₂)
            (for/fold ([ret σ₁]) ([(k vs) (in-dict σ₂)])
              ;; join-values changes for the different abstractions
              (define kvs* (join-values (first vs) (first (dict-ref ret k '(()))) loss?))
              ;; run GC once we know there is a possible loss in precision.
              (cond [(and (not GCed?) (unbox loss?))
                     (define-values (σlocs Ξvars) (ℛ (term ς)))
                     (return (recur #t
                                    (restrict-σ σ σlocs)
                                    (restrict-D D Ξvars)))] ;; GC stack abstraction!
                    [else (dict-set ret k (list kvs*))])))
          (define (combine-frames ξ₁ ξ₂)
            (for/fold ([ret ξ₁]) ([(k vs) (in-dict ξ₂)])
              (dict-set ret k vs)))
          (define-values (σnew σlocs) (values (box '()) (box '())))
          (define extend? (term bool_extend))
          (define ξ_next
            (let ([ξ* (cond [extend? (combine-frames (term ξ_top) (term ((u d) ...)))]
                            [else (term ((u d) ...))])])
              (combine-stores ξ* (term (display-lookup ,D natural_depth)))))
          (define Ξ_next
            (cond [extend? (term (,ξ_next ξ ...))]
                  [else (term (Ξ-push ,ξ_next (ξ_top ξ ...)))]))
          (define (var->loc i x v)
            (cond [(in-stack? x) (term Stack)]
                  [else (define hloc (term (alloc ς ,(unbox σlocs))))
                        (set-box! σlocs (cons hloc (unbox σlocs)))
                        (set-box! σnew (combine-stores (unbox σnew) `((,hloc ,v))))
                        (term (Heap ,hloc))]))
          (define ℓs (mapi var->loc (term (u ...)) (term (d ...))))
          (term ((env-extend* ρ (u ...) ,ℓs)
                 ,(combine-stores σ (unbox σnew))
                 ,Ξ_next
                 (update-display ,D natural_depth ,ξ_next)
                 ,(unbox σlocs))))))])

(define-metafunction DCPS-machine
  [(color-cont (name ς ((clo (λ ulab (u ... k) exp) ρ) (d ..._i) conf-kont σ Ξ D))
               natural_depth ρ_1 σ_1 Ξ_1 D_1 any)
   ;; no references to k will be looked up.
   (ρ_1 σ_1 Ξ_1 D_1)])

(define-metafunction DCPS-machine
  [(pop/rebind-necessarily ulab any_0 any_1 any_2 any_3 Ξ D) (Ξ D)])

(define-metafunction DCPS-machine
  [(Ak clab k ρ D) (truncated)]
  [(Ak clab clam ρ D) ((Ξ-kont clam ρ))]
  [(Ak clab halt ρ D) (halt)])

;;; Metafunctions shared across abstractions.
;; lookups
(define-metafunction DCPS-machine
  [(env-lookup ρ x) ,(first (dict-ref (term ρ) (term x)))])
(define-metafunction DCPS-machine
  [(display-lookup D scope-depth)
   ,(or (for/first ([ξ (in-list (term D))] [i (in-naturals)]
                    #:when (= i (term scope-depth)))
          ξ)
        '())])
(define-metafunction DCPS-machine
  [(Ξ-lookup x (ξ ξ_rest ...)) ,(first (dict-ref (term ξ) (term x)))])
(define-metafunction DCPS-machine
  [(D-lookup k D) (Ξ-lookup k ((display-lookup D ,(get-depth coloring (term k)))))])
(define-metafunction DCPS-machine
  [(σ-lookup (Heap any_h) σ) ,(first (dict-ref (term σ) (term any_h)))])
(define-metafunction DCPS-machine
  [(ℓ-lookup σ ξ #t ρ u) (Ξ-lookup u (ξ))]
  [(ℓ-lookup σ ξ #f ρ u) (σ-lookup (env-lookup ρ u) σ)])

;; updates
(define-metafunction DCPS-machine
  [(env-extend ρ u ℓ) ,(dict-set (term ρ) (term u) (list (term ℓ)))])
(define-metafunction DCPS-machine
  [(env-extend* ρ () ()) ρ]
  [(env-extend* ρ (u u_rest ..._i) (ℓ ℓ_rest ..._i))
   (env-extend* (env-extend ρ u ℓ) (u_rest ...) (ℓ_rest ...))])
(define-metafunction DCPS-machine
  [(update-display D scope-depth ξ) ,(list-update (term D) (term scope-depth) (term ξ))])
(define-metafunction DCPS-machine
  [(Ξ-update x d (ξ_top ξ ...))
   (,(dict-set (term ξ_top) (term x) (list (term d))) ξ ...)])

(define-metafunction DCPS-machine
  [(Au ulab u ρ σ D)
   ,(match-let* ([(call-label-info refcolors ulam-depth) (hash-ref label-ht (term ulab))]
                 [S? (hash-ref refcolors (term u))] ;; #t iff stack ref.
                 [depth (get-depth coloring (term u))])
      (cond [depth
             (term (ℓ-lookup σ (display-lookup D ,depth) ,S? ρ u))]
            [else (unless (set-member? prims (term u))
                    (error 'Au "non-primitive ~a" (term u)))
                  (term (u))]))] ;; primop
  [(Au ulab ulam ρ σ D) ((clo ulam ,(restrict-ρ (term ρ) (free-vars (term ulam)))))]
  [(Au ulab (qwote c) ρ σ D) (c)]
  [(Au ulab (void) ρ σ D) ((void))]
  [(Au ulab prim ρ σ D) (prim)])
;; only used in concrete/abstract semantics.
(define-metafunction DCPS-machine
  [(pop/restore-display lab k Ξ D)
   ((ξ_top ξ_rest ...) (update-display D ,(get-depth coloring (term k)) ξ_top))
   (where (ξ_top ξ_rest ...) (Ξ-pop Ξ))])

(define R-DCPS-machine
  (reduction-relation DCPS-machine
    ;; user eval (call/exit-tc)
    [--> ((user-exp ulab (uaexp_0 uaexp ... caexp)) ρ σ Ξ D)
         (v (d ...) conf-kont σ Ξ_1 D_1)
         (where (v_pre ... (name v (clo ulam ρ_1)) v_post ...) (Au ulab uaexp_0 ρ σ D))
         (where (d ...) ((Au ulab uaexp ρ σ D) ...))
         (where (conf-kont) (Ak ulab caexp ρ D))
         ;; can only pop when we know top of stack isn't reachable!
         ;; Shape of caexp doesn't help.
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
#|
    ;; FIXME: wrong. Add locations to values and bind to location.
    ;; user apply (alloc-primop)
    [--> (name ς ((user-exp ulab (alloc-primop uaexp ... caexp)) ρ σ Ξ D))
         (conf-kont (d_res) (combine-stores ς σ ((any_hloc d_res))) Ξ_1 D_1)
         (where (conf-kont) (Ak ulab caexp ρ D))
         (where any_hloc (alloc ς ()))
         (where (d ...) ((Au ulab uaexp ρ σ D) ...))
         (where d_res (δ alloc-primop d ...))
         (where (Ξ_1 D_1) (pop/rebind-necessarily ulab caexp alloc-primop alloc-primop ρ Ξ D))]
|#
    ;; user apply (entry)
    [--> (name ς ((clo (λ ulab (u ... k) exp) ρ) (d ..._i) conf-kont σ Ξ D))
         (exp ρ_2 σ_new2 Ξ_2 D_2)
         (where natural_depth ,(hash-ref label-ht (term ulab)))
         (where (ρ_1 σ_new Ξ_1 D_1 (name σlocs (any ...)))
                (color-user ς #f natural_depth (u ...) (d ...) ρ σ Ξ D))
         (where (ρ_2 σ_new2 Ξ_2 D_2)
                (color-cont ς natural_depth ρ_1 σ_new Ξ_1 D_1 σlocs))]
    ;; continuation apply (capply)
    [--> (name ς ((Ξ-kont (κ clab (u ..._i) exp) ρ) (d ..._i) σ Ξ D))
         (exp ρ_1 σ_new Ξ_1 D_1)
         (where (ρ_1 σ_new Ξ_1 D_1 any)
          (color-user ς #t ,(hash-ref label-ht (term clab)) (u ...) (d ...) ρ σ Ξ D))]
    ;; continutation eval (let)
    [--> ((cont-call clab (clam uaexp ...)) ρ σ Ξ D)
         ((Ξ-kont clam ,(restrict-ρ (term ρ) (free-vars (term clam))))
          (d ...) σ Ξ D)
         (where (d ...) ((Au clab uaexp ρ σ D) ...))]
    ;; continutation eval (return)
    [--> ς-exit-ret
         (conf-kont (d ...) σ Ξ_1 D_1)
         (where ((cont-call clab (k uaexp ...)) ρ σ Ξ D) ς-exit-ret)
         (where (conf-kont) (D-lookup k D))
         (where (d ...) ((Au clab uaexp ρ σ D) ...))
         (where (Ξ_1 D_1) (pop/restore-display clab k Ξ D))]
    ;; continutation eval (escape)
    [--> ς-exit-esc
         ((Ξ-kont clam ρ_1) (d ...) σ Ξ_1 D_1)
         (where ((cont-call clab (k uaexp ...)) ρ σ Ξ D) ς-exit-esc)
         (where (d ...) ((Au clab uaexp ρ σ D) ...))
         (where (σ-kont clam ρ_1 Ξ_1 D_1) (σ-lookup (env-lookup ρ k) σ))]))

(define (restrict-ρ alist fvs)
  (for/list ([(k single-ℓ) (in-dict alist)]
             #:when (set-member? fvs k))
    (cons k single-ℓ)))
(define (restrict-σ alist σlocs)
  (for/list ([(k v) (in-dict alist)]
             #:when (set-member? σlocs `(Heap ,k)))
    (cons k v)))
(define (restrict-D D Ξvars)
  (map (λ (ξ) (restrict-ρ ξ Ξvars)) D))

(define (closed-vars v)
  (map first
       ((term-match/single DCPS-machine
          [(clo ulam ρ) (term ρ)]
          [(Ξ-kont clam ρ) (term ρ)]
          [(σ-kont clam ρ Ξ D) (term ρ)]
          [any '()]) v)))

;; Touched locations from value, display and machine configuration.
;; returns sets of touched store locations and touched stack locations.
(define (𝒯 v [σlocs (set)] [Ξvars (set)])
  (define (fv-touch fvs ρ σlocs Ξvars)
    (for*/fold ([σlocs σlocs] [Ξvars Ξvars])
               ([fv (in-set fvs)]
                [ρv (in-value (dict-ref ρ fv #f))]
                #:when ρv
                [ℓ (in-value (first ρv))])
      (cond [(eq? ℓ 'Stack) (values σlocs (set-add Ξvars fv))]
            [else (values (set-add σlocs ℓ) Ξvars)])))
  (define (union-2values f v₁ v₂ σlocs Ξvars)
    (define-values (s₁₁ s₁₂) (f v₁ σlocs Ξvars))
    (f v₂ s₁₁ s₁₂))
  (define (𝒯-d d σlocs Ξvars) (map-union-2values 𝒯 d σlocs Ξvars))
  (define (loc v) (𝒯 v σlocs Ξvars))
  ((term-match/single DCPS-machine
       ;; values
       [halt (values σlocs Ξvars)]
       [c    (values σlocs Ξvars)]
       [prim (values σlocs Ξvars)]
       [(clo ulam ρ)        (fv-touch (free-vars (term ulam)) (term ρ) σlocs Ξvars)]
       [(Ξ-kont clam ρ)     (fv-touch (free-vars (term clam)) (term ρ) σlocs Ξvars)]
       [(σ-kont clam ρ Ξ D) (fv-touch (free-vars (term clam)) (term ρ) σlocs Ξvars)]
       [(cons-cell v_0 v_1) (union-2values loc (term v_0) (term v_1) σlocs Ξvars)]
       ;; Display
       [(ξ_top ξ ...)
        (let ()
          (define-values (σlocs′ Ξvars′) (𝒯 (term ξ_top) σlocs Ξvars))
          (𝒯 (term (ξ ...)) σlocs′ Ξvars′))]
       ;; grr, should match (n (1))
       [ξ_top (map-union-2values 𝒯-d (map second (term ξ_top)) σlocs Ξvars)]
       [()   (values σlocs Ξvars)]
       ;; configurations
       [(exp ρ σ Ξ D)
        (let ()
          (define-values (σlocs′ Ξvars′) (fv-touch (free-vars (term exp)) (term ρ) σlocs Ξvars))
          (map-union-2values 𝒯 (take (term D) (exp-depth (term exp))) σlocs′ Ξvars′))]
       [((Ξ-kont clam ρ) (d ...) σ Ξ D)
        (let ()
          (define-values (σlocs′ Ξvars′) (𝒯 (term (Ξ-kont clam ρ)) σlocs Ξvars))
          (define-values (σlocs″ Ξvars″) (map-union-2values 𝒯-d (term (d ...)) σlocs′ Ξvars′))
          (map-union-2values 𝒯-d (take (term D) (hash-ref label-ht (term clam))) σlocs″ Ξvars″))]
       [(halt (d ...) σ Ξ D)
        (map-union-2values 𝒯-d (term (d ...)) σlocs Ξvars)]
       [((clo ulam ρ) (d ...) conf-kont σ Ξ D)
        (let ()
          (define-values (σlocs′ Ξvars′) (𝒯 (term (clo ulam ρ)) σlocs Ξvars))
          (define-values (σlocs″ Ξvars″) (map-union-2values 𝒯-d (term (d ...)) σlocs′ Ξvars′))
          ;; every stack entry above the current lambda is also reachable. Use display
          (map-union-2values 𝒯-d (take (term D) (hash-ref label-ht (term ulam))) σlocs″ Ξvars″))])
     v))

;; Reachable locations (in store and stack) from given machine configuration.
(define (ℛ ς)
  (define σ (σ-of ς))
  (define D (D-of ς))
  (define (↝σ* ℓ ret₁ ret₂)
    (↝²→↝²* (match-lambda [`(Heap ,hloc) (map-union-2values 𝒯 (first (dict-ref σ hloc)) ret₁ ret₂)]
                          [(? symbol? x) (map-union-2values 𝒯 (term (D-lookup ,x ,D)) ret₁ ret₂)])
         ℓ))
  (define-values (root-σlocs root-Ξvars) (𝒯 ς))
  ;; collect the reaching locations of each touched location in the given state
  (set-map-union-2values ↝σ* (set-union root-σlocs root-Ξvars) root-σlocs root-Ξvars))

(define (GCFA2 e #:tr [tr translate] #:inject [inj inject])
  (define I (inj e tr))
  (define initial-work (list I I))
  ;; Some notational definitions
  (define (succ ς̃) (apply-reduction-relation R-DCPS-machine ς̃))
  (define (Seen? pair) (hash-has-key? Seen pair))
  (define (in-Summary? ς̃₁ ς̃₂) (set-member? (hash-ref Summary ς̃₁ '()) ς̃₂))
  (define (name-ς ς) #;(strip-annotation ς names) ς)
  (define (hash-union! S A)
    (for ([(entry exits) (in-hash A)])
      (hash-set-union! S entry exits)))
  ;; Summary : entry ↦ setof exit
  ;; Seen/Work : (list state state) ↦ #t
  ;; Callers/TCallers : entry ↦ (list caller entry)
  ;; Final : state ↦ #t
  (define-values (Summary Seen Callers TCallers EntriesEsc Escapes)
    (apply values (build-list 6 (λ _ (make-hash)))))
  (define-values (Final Work Escaping)
    (apply values (build-list 3 (λ _ (make-hasheq)))))
  (define (Update! ς̃caller-entry ς̃call ς̃callee-entry ς̃callee-return)
    (apply printf "Updating ~%〈~a,~% ~a,~% ~a,~% ~a〉~%" (map name-ς (list ς̃caller-entry ς̃call ς̃callee-entry ς̃callee-return)))
    (redex-let* DCPS-machine
      (;[ς-entry_1 ς̃caller-entry] ;; XXX: Does not match for initial machine state!
       [((user-exp ulab_2 (uaexp_f uaexp_e ... clam)) ρ_2 σ_2 Ξ_2 D_2) ς̃call]
       [((clo (name ulam_3 (λ ulab_3 (x_3 ...) exp_3)) ρ_3) (d_3 ...) conf-kont σ_3 Ξ_3 D_3) ς̃callee-entry]
       [((cont-call clab_4 (k_4 uaexp_4 ...)) ρ_4 σ_4 Ξ_4 D_4) ς̃callee-return]
       [(d_next ...) (term ((Au clab_4 uaexp_4 ρ_4 σ_4 D_4) ...))]
       [(Ξ_next D_next)
        (cond [(and ;; do we know what uaexp_f is because there
                    ;; aren't arbitrarily many calls in between call and exit?
                    (symbol? (term uaexp_f))
                    (Ξ?ψ (term ulab_2) (term uaexp_f)))
               (define Ξ_next (term (Ξ-update uaexp_f ((clo ulam_3 ρ_3)) Ξ_2)))
               (printf "Preventing fake rebinding of ~a~%" (term uaexp_f))
               (term (,Ξ_next
                      (update-display D_2 ,(get-depth coloring (term uaexp_f)) ,(first Ξ_next))))]
              [else (term (Ξ_2 D_2))])]
       [ς (term ((Ξ-kont clam ρ_2) (d_next ...) σ_4 Ξ_next D_next))])
      ;; If d_next close over any of uaexp_f's arguments, then they are escaping.
      ;; We only need to inspect heap-allocated variables, since we trust
      ;; the previous escape analysis.
      (escape-analysis (term (halt (d_next ...) σ_4 Ξ_next D_next)))
      (Propagate! ς̃caller-entry (term ς) #f)))
  (define (escape-analysis final)
    (define σ (σ-of final))
    (define-values (σlocs _) (ℛ final))
    (printf "Reachable locs ~a~%" σlocs)
    ;; FIXME: Depending on monvariance for this part.
    (for* ([ℓ (in-set σlocs)])
      (match-define `(Heap ,fv) ℓ)
      (insert! fv Escaping)))
  (define (Propagate! ς̃₁ ς̃₂ escaping?)
    (define pair (list ς̃₁ ς̃₂))
    (when escaping? (insert! pair Summary))
    (μ-guard pair Seen (insert! pair Work)))
  (define (Intermediate! ς̃₁ ς̃₂)
    (printf "Intermediate~%")
    (for ([ς̃₃ (in-list (succ ς̃₂))])
      (Propagate! ς̃₁ ς̃₃ #f)))

  (insert! initial-work Seen Work)
  (let analyze ()
    (match (set-grab Work)
      [#f (list Summary Final Escaping)] ;; done
      [(list ς̃₁ ς̃₂)
       (apply printf "Processing ~%〈~a,~% ~a〉~%" (map name-ς (list ς̃₁ ς̃₂)))
       ((term-match/single DCPS-machine
          [ς-intermediate (Intermediate! ς̃₁ ς̃₂)]
          ;; entry
          [((clo (λ ulab (u ..._i k) exp) ρ) (d ..._i) conf-kont σ Ξ D)
           (begin (printf "Entry~%") (Intermediate! ς̃₁ ς̃₂)
                  (case-alloc (get-color coloring (term k))
                    [heap (insert! ς̃₂ EntriesEsc)
                          (for-escapes Escapes (ς̃₃ calls (k in ρ)) (Propagate! ς̃₂ ς̃₃ #t))]))]
          [ς-call
           (begin (printf "Call~%")
                  (for ([ς̃₃ (in-list (succ ς̃₂))])
                    (Propagate! ς̃₃ ς̃₃ #f)
                    (insert-caller! Callers (ς̃₁ ς̃₂ ς̃₃))
                    ;; could have arbitrary stack change between ς̃₂ and ς̃₄.
                    ;; It is important that we know the net at ς̃₄
                    (for-summary Summary (ς̃₃ ς̃₄) (Update! ς̃₁ ς̃₂ ς̃₃ ς̃₄))))]
          [ς-final (begin (printf "Final ς̃₂~%")
                          (escape-analysis ς̃₂)
                          (insert! ς̃₂ Final))]
          ;; exit-ret/esc/exn
          [ς-exit-shape
           (let ()
             (define-values (k ρ lab)
               ;; XXX: lack of "or" patterns really sucks.
               (with-handlers ([exn:fail:redex?
                                (λ _
                                   (redex-let DCPS-machine
                                     ([((user-exp ulab (prim uaexp ... tail-continuation)) ρ σ Ξ D)
                                       (term ς-exit-shape)])
                                     (values (term tail-continuation) (term ρ) (term ulab))))])
                 (redex-let DCPS-machine
                   ([((cont-call clab ((name cont tail-continuation) uaexp ...)) ρ σ Ξ D)
                     (term ς-exit-shape)])
                   (values (term tail-continuation) (term ρ) (term clab)))))
             (match-define (call-label-info refcolors ulam-depth)
                           (hash-ref label-ht lab))
             (printf "Exit-")
             (case-alloc (dict-ref refcolors (term k) stack-ref)
               [stack
                (printf "Ret~%")
                (cond [(equal? ς̃₁ I)
                       (printf "Ret Final ς̃₂~%")
                       (escape-analysis ς̃₂)
                       (insert! ς̃₂ Final)]
                      [else
                       (add-summary! Summary (ς̃₁ ς̃₂))
                       (for-callers Callers (ς̃₃ ς̃₄ ς̃₁) (Update! ς̃₃ ς̃₄ ς̃₁ ς̃₂))
                       (for-callers TCallers (ς̃₃ ς̃₄ ς̃₁) (Propagate! ς̃₃ ς̃₂ #f))])]
               [exn
                (printf "Exn~%")
                (cond [(not (in-Summary? ς̃₁ ς̃₂))
                       ;; search call chain for binders of k.
                       (error 'TODO)]
                      [(equal? ς̃₁ I)
                       (printf "Exn Final ς̃₂~%")
                       (escape-analysis ς̃₂)
                       (insert! ς̃₂ Final)]
                      [else
                       (error 'TODO)])]
               [heap
                (printf "Esc~%")
                (cond [(not (in-Summary? ς̃₁ ς̃₂))
                       (insert! ς̃₂ Escapes)
                       ;; don't search call chain. Just find all entries that bind k (monovariant)
                       (for-escaping-entries EntriesEsc (ς̃₃ over (k in ρ)) (Propagate! ς̃₃ ς̃₂ #t))]
                      [(equal? ς̃₁ I)
                       (printf "Esc Final ς̃₂~%")
                       (escape-analysis ς̃₂)
                       (insert! ς̃₂ Final)]
                      [else
                       (add-summary! Summary (ς̃₁ ς̃₂))
                       (for-callers Callers (ς̃₃ ς̃₄ ς̃₁) (Update! ς̃₃ ς̃₄ ς̃₁ ς̃₂))
                       (for-callers TCallers (ς̃₃ ς̃₄ ς̃₁) (Propagate! ς̃₃ ς̃₂ #t))])]))]
          ;; tail call
          [ς-exit-tc
           (begin
             (printf "Tail call~%")
             (for ([ς̃₃ (in-list (succ ς̃₂))])
               (Propagate! ς̃₃ ς̃₃ #f)
               (insert-caller! TCallers (ς̃₁ ς̃₂ ς̃₃))
               (let ([S (make-hash)])
                 (for-summary Summary (ς̃₃ ς̃₄)
                   (add-summary! S (ς̃₁ ς̃₄))
                   (Propagate! ς̃₁ ς̃₄ #f))
                 (hash-union! Summary S))))]

          [any (error 'analyze "Uncaught case ~a~%" ς̃₂)])
        ς̃₂)
       (analyze)])))

#|
 (define-metafunction DCPS-machine ;; concrete heap allocation
  [(alloc ((clo ulam ρ) (d ...) conf-kont σ Ξ D) (any ...))
   ,(add1 (max (max-nat-keys (term σ)) (max-nat-list (term (any ...)))))]
  [(alloc ((user-exp ulab (alloc-primop uaexp ... caexp)) ρ σ Ξ D) (any ...))
   ,(add1 (max (max-nat-keys (term σ)) (max-nat-list (term (any ...)))))]
  [(alloc ((Ξ-kont clam ρ) (d ...) σ Ξ D) (any ...))
   ,(add1 (max (max-nat-keys (term σ)) (max-nat-list (term (any ...)))))])
;; concrete push/pop
 (define-metafunction DCPS-machine
  [(Ξ-pop (ξ_top ξ ...)) (ξ ...)])
 (define-metafunction DCPS-machine
  [(Ξ-push ξ (ξ_stack ...)) (ξ ξ_stack ...)])

; concrete/abstract
 (define-metafunction DCPS-machine
  [(Ak clab k ρ D) (D-lookup k D)]
  [(Ak clab clam ρ D) ((Ξ-kont clam ρ))]
  [(Ak clab halt ρ D) (halt)])

 (define-metafunction DCPS-machine
  [(pop/rebind-necessarily ulab k    uaexp v ρ Ξ D) (pop/restore-display ulab k Ξ D)]
  [(pop/rebind-necessarily ulab clam ulam  v ρ Ξ D) (Ξ D)]
  [(pop/rebind-necessarily ulab clam prim  v ρ Ξ D) (Ξ D)]
  [(pop/rebind-necessarily ulab halt uaexp v ρ Ξ D) (Ξ D)]
  [(pop/rebind-necessarily ulab clam u     v ρ Ξ D)
   ,(match-let* ([(call-label-info refcolors ulam-depth) (hash-ref label-ht (term ulab))]
                 [S? (not (eq? heap-ref (hash-ref refcolors (term u))))]
                 [depth (get-depth coloring (term u))])
      (cond [S? (term-let ([(ξ_top ξ ...) (term (Ξ-update u (v) Ξ))])
                  (term ((ξ_top ξ ...) (update-display D ,depth ξ_top))))]
            [else (term (Ξ D))]))])

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
|#
