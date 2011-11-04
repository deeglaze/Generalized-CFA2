#lang racket

(require redex "pure-scheme-to-LC.rkt"
         "scheme-escape-analysis.rkt"
         "utils.rkt"
         racket/trace)
(provide (all-defined-out))

(define coloring (make-hasheq))
(define (escapes? x) (dict-ref coloring x #t))

;; An implementation of Istack from [Clinger 98]
;; - set! + call/cc + display with stack and heap separated.

(define-language Scheme
  [e (e e ...) ref lam
     (if e e e) (call/cc e) (qwote c)
     #;(set! ref e)]
  [ref x]
  [lam (λ (x ...) e)]
  [c integer void bool null (cons-cell c c)] ;; simplified
  [bool #t #f]
  [x variable-not-otherwise-mentioned])
(define-extended-language Annotated-Scheme Scheme
  [ref (ann-ref x bool scope-depth) primop] ;; bool ⇔ stack reference.
  [lam (λ scope-depth (x ...) e)] ;; scope-depth is static nesting depth of x.
  [scope-depth natural]
  [primop + - * / pair? null? < <= = >= > cons car cdr])

(define-extended-language Istack Annotated-Scheme
  [ς ς-eval ς-apply]
  [d e (tail e)]
  [ς-eval (d ρ σ Ξ D scope-depth κ)]
  [ς-apply (v σ Ξ D κ)]
  [v primop c (clo lam ρ) (kont κ Ξ D)]
  [ρ ((x ℓ) ...)]
  [σ ((natural v v ...) ...)]
  [(D Ξ) (ξ ...)] ;; stacks are lists of stack frames
  [ξ (v ...)] ;; stack frames are referenced positionally
  [ℓ (Stack natural) (Heap/Stack natural natural)]
  [call push goto]
  [capture push-capture goto-capture]
  [κ halt
     truncated ;; for localization
     ;; returning to nesting depth natural. Update display on exit.
     (exit scope-depth κ)
     (call (e ...) (v ...) ρ scope-depth κ)
     (entry (v ...) scope-depth κ)
     (select d d ρ scope-depth κ)
     (capture scope-depth κ)
     #;(assign ℓ natural κ)]
  ;; give names to certain configurations for understandable metafunctions
  [colorable ς-exit-tc ς-entry ς-call/cc]
  [ς-exit-tc ((clo (λ scope-depth () e) ρ) σ Ξ D (goto () () ρ scope-depth κ))
             (v σ Ξ D (goto () ((clo lam ρ) v ...) ρ scope-depth κ))]
  [ς-call (v σ Ξ D (push () ((clo lam ρ) v ...) ρ scope-depth κ))
          ((clo lam ρ) σ Ξ D (push () () ρ scope-depth κ))]
  [ς-entry ((clo lam ρ) σ Ξ D (entry (v ...) scope-depth κ))]
  [ς-exit (v σ Ξ D (exit scope-depth κ))]
  [ς-final (v σ Ξ D halt)]
  [ς-intermediate-apply (v σ Ξ D (call (e_1 e ...) (v ...) ρ scope-depth κ))
                        (v σ Ξ D (select d d scope-depth κ))]
  [ς-call/cc ((clo (λ scope-depth (x) e) ρ) σ Ξ D (capture scope-depth κ))]
  [ς-use/cc (v σ Ξ D (call () ((kont κ Ξ D)) ρ scope-depth κ))]
  [push-kind push push-capture]
  [exit-kind goto goto-capture])
(define-syntax-rule (is-state? pattern term)
  (not (not (redex-match Istack pattern term))))


;; These three meta-functions are the only ones needed to abstract
#;(define-metafunction Istack ;; heap allocation
  [(alloc (v σ Ξ D κ) (natural ...))
   ,(add1 (max (max-nat-keys (term σ)) (max-nat-list (term (natural ...)))))])

(define-metafunction Istack ;; heap allocation
  [(alloc (v σ Ξ D κ) (natural ...)) 0])

#;(define-metafunction Istack ;; we want stack locations to be mutated
  [(combine-stores σ_1 σ_2) ,(for/fold ([ret (term σ_1)]) ([(k vs) (in-dict (term σ_2))]) (dict-set ret k vs))])
(define-metafunction Istack ;; we want stack locations to be mutated
  [(combine-stores σ_1 σ_2)
   ,(for/fold ([ret (term σ_1)])
        ([(k vs) (in-dict (term σ_2))])
      (dict-set ret k (append-nodups vs (dict-ref ret k '()))))])

#;(define-metafunction Istack ;; abstracted when localizing
  [(create-entry (v ...) scope-depth κ) (entry (v ...) scope-depth κ)])
(define-metafunction Istack ;; abstracted when localizing
  [(create-entry (v ...) scope-depth κ) (entry (v ...) scope-depth truncated)])

(define-metafunction Istack ;; primop implementation
  [(δ + integer ...) ,(apply + (term (integer ...)))]
  [(δ - integer ...) ,(apply - (term (integer ...)))]
  [(δ * integer ...) ,(apply * (term (integer ...)))]
  [(δ / integer ...) ,(apply / (term (integer ...)))]
  [(δ < integer_0 integer_1) ,(< (term integer_0) (term integer_1))]
  [(δ <= integer_0 integer_1) ,(<= (term integer_0) (term integer_1))]
  [(δ = integer_0 integer_1) ,(= (term integer_0) (term integer_1))]
  [(δ >= integer_0 integer_1) ,(>= (term integer_0) (term integer_1))]
  [(δ > integer_0 integer_1) ,(> (term integer_0) (term integer_1))]
  [(δ pair? v) ,(not (not (redex-match Istack (cons-cell v_0 v_1) (term v))))]
  [(δ null? v) ,(eq? (term v) 'null)]
  [(δ zero? v) ,(zero? (term v))]
  [(δ boolean? v) ,(boolean? (term v))]
  [(δ procedure? v) ,(not (not (or (redex-match Istack (clo lam ρ) (term v))
                                   (redex-match Istack (kont κ Ξ D) (term v)))))]
  [(δ cons v_0 v_1) (cons-cell v_0 v_1)]
  [(δ car (cons-cell v_0 v_1)) v_0]
  [(δ cdr (cons-cell v_0 v_1)) v_1])

(define-metafunction Istack
  [(untail e) e]
  [(untail (tail e)) e])
(define-metafunction Istack
  [(env-lookup ρ x) ,(first (dict-ref (term ρ) (term x)))])
(define-metafunction Istack
  [(display-lookup D scope-depth) ,(list-ref (term D) (term scope-depth))])
(define-metafunction Istack
  [(ℓ-lookup σ ξ #t (Heap/Stack natural_h natural_s)) (,(list-ref (term ξ) (term natural_s)))]
  [(ℓ-lookup σ ξ #f (Heap/Stack natural_h natural_s)) ,(dict-ref (term σ) (term natural_h))]
  [(ℓ-lookup σ ξ #t (Stack natural)) (,(list-ref (term ξ) (term natural)))])
(define-metafunction Istack
  [(lookup ρ σ D (ann-ref x bool scope-depth))
   (ℓ-lookup σ (display-lookup D scope-depth) bool (env-lookup ρ x))])

(define-metafunction Istack
  [(env-extend ρ x ℓ) ,(dict-set (term ρ) (term x) (term (ℓ)))])
(define-metafunction Istack
  [(env-extend* ρ () ()) ρ]
  [(env-extend* ρ (x x_rest ..._i) (ℓ ℓ_rest ..._i))
   (env-extend* (env-extend ρ x ℓ) (x_rest ...) (ℓ_rest ...))])
(define-metafunction Istack
  [(update-display D scope-depth ξ) ,(list-update (term D) (term scope-depth) (term ξ))])

(define-metafunction Istack
  [(Ξ-pop (ξ_top ξ ...)) (ξ ...)])
(define-metafunction Istack
  [(Ξ-push ξ (ξ_stack ...)) (ξ ξ_stack ...)])
(define-metafunction Istack
  [(pop-necessarily push-kind Ξ) Ξ]
  [(pop-necessarily goto-kind Ξ) (Ξ-pop Ξ)])
(define-metafunction Istack
  [(push-necessarily push-kind scope-depth κ) (exit scope-depth κ)]
  [(push-necessarily goto-kind scope-depth κ) κ])

;; handle binding/allocation for fn-call/cont-capture
(define-metafunction Istack
  ;; exit-tc thunk
  [(color ((clo (λ scope-depth () e) ρ) σ Ξ D (goto () () ρ_unused scope-depth_current κ)))
   ((tail e) ρ σ (Ξ-push () (Ξ-pop Ξ))
    (update-display D scope-depth ()) scope-depth (exit scope-depth_current κ))]
  ;; exit-tc
  [(color (name ς (v_n σ Ξ D (goto () ((clo (λ scope-depth (x ..._ids x_n) e) ρ) v ..._ids) ρ_unused scope-depth_current κ))))
   ((tail e)
    (env-extend* ρ (x ... x_n) (ℓ_all ...))
    (combine-stores σ σ_new)
    (Ξ-push ξ (Ξ-pop Ξ)) (update-display D scope-depth ξ) scope-depth κ)
   (where ξ (v ... v_n))
   (where ((ℓ_all ...) σ_new) (color-alloc ς ((x v) ... (x_n v_n))))]
  ;; entry
  [(color (name ς ((clo (λ scope-depth (x ..._ids) e) ρ) σ Ξ D (entry (v ..._ids) scope-depth_current κ))))
   ((tail e)
    (env-extend* ρ (x ...) (ℓ_all ...))
    (combine-stores σ σ_new)
    (Ξ-push ξ Ξ) (update-display D scope-depth ξ) scope-depth (exit scope-depth_current κ))
   (where ξ (v ...))
   (where ((ℓ_all ...) σ_new) (color-alloc ς ((x v) ...)))]
  ;; call/cc
  [(color (name ς ((clo (λ scope-depth (x) e) ρ) σ Ξ D (capture scope-depth_current κ))))
   ((tail e)
    (env-extend ρ x ℓ)
    (combine-stores σ σ_new)
    (Ξ-push ξ (pop-necessarily capture Ξ))
    (update-display D scope-depth ξ)
    scope-depth
    (push-necessarily call scope-depth_current κ))
   (where ((ℓ) ξ σ_new) (color-alloc ς ((x (kont κ Ξ D)))))])

(define-metafunction Istack
  [(color-alloc ς ((x v) ...))
   ,(let* ([colors (map escapes? (term (x ...)))]
           [heap-locs (box '())]
           [σnew (box '())]
           [escape->loc (λ (i b v) (cond [b (define hloc (term (alloc ς ,(unbox heap-locs))))
                                          (set-box! heap-locs (cons hloc (unbox heap-locs)))
                                          (set-box! σnew (term (combine-stores ,(unbox σnew) ((,hloc ,v)))))
                                          (term (Heap/Stack ,hloc ,i))]
                                       [else (term (Stack ,i))]))]
           [locs (mapi escape->loc colors (term (v ...)))])
      (printf "New heap ~a ~a~%~%" (redex-match Istack σ (unbox σnew)) (unbox σnew))
      (term (,locs ,(unbox σnew))))])

(define-metafunction Istack
  [(inject e) (e () () (()) (()) 0 halt)])

(define R-Istack
  (reduction-relation Istack
    [--> e (inject e)] ;; injection
    ;; terminal eval states
    [--> (primop ρ σ Ξ D scope-depth κ) (primop σ Ξ D κ)]
    [--> (d ρ σ Ξ D scope-depth_current κ) (v σ Ξ D κ)
         (where (v_pre ... v v_post ...) (lookup ρ σ D (untail d)))]
    [--> (d ρ σ Ξ D scope-depth κ) (c σ Ξ D κ)
         (where (qwote c) (untail d))]
    [--> (d ρ σ Ξ D scope-depth κ) ((clo lam ρ) σ Ξ D κ)
         (where lam (untail d))]
  #;[--> (d_set ρ σ Ξ D κ) (e ρ σ Ξ D (assign (env-lookup ρ x) natural κ)) ;; TODO
         (where (set! (ann-ref x natural) e) (untail d_set))]
    ;; intermediate eval states
    [--> ((e_0 e ...) ρ σ Ξ D scope-depth κ)             (e_0 ρ σ Ξ D scope-depth (push (e ...) () ρ scope-depth κ))]
    [--> ((if e_0 e_1 e_2) ρ σ Ξ D scope-depth κ)        (e_0 ρ σ Ξ D scope-depth (select e_1 e_2 ρ scope-depth κ))]
    [--> ((call/cc e_0) ρ σ Ξ D scope-depth κ)           (e_0 ρ σ Ξ D scope-depth (push-capture scope-depth κ))]
    [--> ((tail (e_0 e ...)) ρ σ Ξ D scope-depth κ)      (e_0 ρ σ Ξ D scope-depth (goto (e ...) () ρ scope-depth κ))]
    [--> ((tail (if e_0 e_1 e_2)) ρ σ Ξ D scope-depth κ) (e_0 ρ σ Ξ D scope-depth (select (tail e_1) (tail e_2) ρ scope-depth κ))]
    [--> ((tail (call/cc e_0)) ρ σ Ξ D scope-depth κ)    (e_0 ρ σ Ξ D scope-depth (goto-capture scope-depth κ))]
    ;; apply states
    ;; intermediate evaluation
    [--> (v σ Ξ D (call (e_1 e ...) (v_0 ...) ρ scope-depth κ))
         (e_1 ρ σ Ξ D scope-depth (call (e ...) (v_0 ... v) ρ scope-depth κ))]
    ;; non-tail call entry
    [--> (v_n σ Ξ D (push () ((clo lam ρ) v ...) ρ_unused scope-depth κ))
         ((clo lam ρ) σ Ξ D (create-entry (v ... v_n) scope-depth κ))]
    [--> ((clo (λ scope-depth () e) ρ) σ Ξ D (push () () ρ_unused scope-depth_current κ))
         ((clo (λ scope-depth () e) ρ) σ Ξ D (create-entry () scope-depth κ))]
    ;; call/capture
    [--> colorable (color colorable)]
    ;; call continuation
    [--> (v σ Ξ_unused D_unused (call () ((kont κ Ξ D)) ρ_unused scope-depth_unused κ_unused))
         (v σ Ξ D κ)]
   ;; if branch selection
   [--> (#f σ Ξ D (select d_1 d_2 ρ scope-depth κ)) (d_2 ρ σ Ξ D scope-depth κ)]
   [--> (v σ Ξ D (select d_1 d_2 ρ scope-depth κ)) (d_1 ρ σ Ξ D scope-depth κ)
        (side-condition (term v))]
   ;; deletion strategy
   [--> (v σ (ξ_kill ξ_top ξ ...) D (exit scope-depth κ))
        ;; XXX: this is where stack mutation breaks.
        ;;      set! should only be allowed for heap-allocated variables.
        (v σ (ξ_top ξ ...) (update-display D scope-depth ξ_top) κ)]
   ;; primops
   [--> (v_n σ Ξ D (call () (primop v ...) ρ scope-depth κ))
        ((δ primop v ... v_n) σ Ξ D κ)]
    ;; mutation
  #;[--> (v σ Ξ D (assign ℓ natural κ))
        (void σ_next Ξ D_next κ)
        (where (σ_next Ξ_next D_next) (do-assign ℓ natural σ D))]
   ))

;; Dress up the data manipulation to look more like the math.
(define-syntax-rule (for-callers Callers (ς̃entry ς̃call ς̃callee-entry) body1 body ...)
  (for ([(ς̃entry caller×callee) (in-dict Callers)]
        #:when (equal? ς̃callee-entry (second caller×callee)))
    (let ([ς̃call (first caller×callee)])
      body1 body ...)))
(define-syntax-rule (for-summary Summary (ς̃entry ς̃exit) body1 body ...)
  (for ([ς̃exit (in-set (dict-ref Summary ς̃entry (set)))])
    body1 body ...))
(define-syntax-rule (insert-caller! Callers (ς̃entry ς̃call ς̃callee-entry))
  (hash-set! Callers ς̃entry (list ς̃call ς̃callee-entry)))
(define-syntax-rule (add-summary! Summary (ς̃entry ς̃exit))
  (hash-set! Summary ς̃entry (set-add (hash-ref Summary ς̃entry (set)) ς̃exit)))

(define (GCFA2 e)
  (define e′ (escape-analysis! e coloring))
  (define I (term (inject ,e′)))
  (define initial-work (list I I))
  (define (succ ς̃) (apply-reduction-relation R-Istack ς̃))
  (define (insert! k . hts) (for ([ht (in-list hts)]) (hash-set! ht k #t)))
  (define (Seen? pair) (hash-has-key? Seen pair))
  (define name-ς values)
  ;; Summary : entry ↦ setof exit
  ;; Seen/Work : (list state state) ↦ #t
  ;; Callers/TCallers : entry ↦ (list caller entry)
  ;; Final : state ↦ #t
  (define-values (Summary Seen Callers TCallers) (values (make-hash) (make-hash) (make-hash) (make-hash)))
  (define-values (Final Work) (values (make-hasheq) (make-hasheq)))
  (define (Update! ς̃₁ ς̃₂ ς̃₃ ς̃₄)
    (apply printf "Updating ~%〈~a,~% ~a,~% ~a,~% ~a〉~%" (map name-ς (list ς̃₁ ς̃₂ ς̃₃ ς̃₄)))
    (term-let ([(v_1 σ_1 Ξ_1 D_1 (entry (v_i1 ...) scope-depth_1 truncated)) ς̃₁]
               [(v_n σ_2 Ξ_2 D_2 (push () (v_i2 ...) ρ_2 scope-depth_2 κ_2)) ς̃₂]
               [(v_3 σ_3 Ξ_3 D_3 (entry (v_i3...) scope-depth_3 truncated)) ς̃₃]
               [(v_4 σ_4 Ξ_4 D_4 (exit scope-depth_4 truncated)) ς̃₄])
      (Propagate! ς̃₁ (term (v_4 σ_4 Ξ_2 D_2 κ_2)))))
  (define (Propagate! ς̃₁ ς̃₂)
    (define pair (list ς̃₁ ς̃₂))
    (unless (Seen? pair) (insert! pair Seen Work)))

;  (pretty-print (node-names)) (newline)
  (insert! initial-work Seen Work)
  (let analyze ()
    (match (set-grab Work)
      [#f (list Summary Final)] ;; done
      [(list ς̃₁ ς̃₂)
       (apply printf "Processing ~%〈~a,~% ~a〉~%" (map name-ς (list ς̃₁ ς̃₂)))
       (cond [(or (is-state? ς-eval ς̃₂)
                  (is-state? ς-intermediate-apply ς̃₂)
                  (is-state? ς-entry ς̃₂))
              (printf "Intermediate ~a~%" (cond [(is-state? ς-eval ς̃₂) "Eval"]
                                                [(is-state? ς-intermediate-apply ς̃₂) "Apply"]
                                                [(is-state? ς-entry ς̃₂) "Entry"]))
              (for ([ς̃₃ (in-list (succ ς̃₂))])
                (Propagate! ς̃₁ ς̃₃))]

             [(is-state? ς-call ς̃₂) (printf "Call~%")
              (for ([ς̃₃ (in-list (succ ς̃₂))])
                (Propagate! ς̃₃ ς̃₃)
                (insert-caller! Callers (ς̃₁ ς̃₂ ς̃₃))
                (for-summary Summary (ς̃₃ ς̃₄) (Update! ς̃₁ ς̃₂ ς̃₃ ς̃₄)))]

             [(is-state? ς-final ς̃₂) (printf "Final~%") (insert! ς̃₂ Final)]

             [(is-state? ς-exit ς̃₂) (printf "Return~%")
              (add-summary! Summary (ς̃₁ ς̃₂))
              (for-callers Callers (ς̃₃ ς̃₄ ς̃₁) (Update! ς̃₃ ς̃₄ ς̃₁ ς̃₂))
              (for-callers TCallers (ς̃₃ ς̃₄ ς̃₁) (Propagate! ς̃₃ ς̃₂))]

             [(is-state? ς-exit-tc ς̃₂) (printf "Tail call~%")
              (for ([ς̃₃ (in-list (succ ς̃₂))])
                (Propagate! ς̃₃ ς̃₃)
                (insert-caller! TCallers (ς̃₁ ς̃₂ ς̃₃))
                (for-summary Summary (ς̃₃ ς̃₄) (Propagate! ς̃₁ ς̃₄)))]

             [(is-state? ς-call/cc ς̃₂) (error 'todo-call/cc)]
             [(is-state? ς-use/cc ς̃₂) (error 'todo-use/cc)]

             [else (error 'analyze "Uncaught case ~a~%" ς̃₂)])
       (analyze)])))

(define esop (call-with-input-string (format "(~a)" (call-with-input-file "esop.sch" port->string)) read))
(define esop* (translate-top esop))
esop*
(newline)
;(GCFA2 esop*)