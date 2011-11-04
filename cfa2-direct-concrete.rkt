#lang racket
(require redex
         "pure-scheme-to-LC.rkt"
         "scheme-escape-analysis.rkt"
         "langs.rkt"
         "utils.rkt"
         racket/trace)
(provide (all-defined-out))

;; [abstractables]

;; Concrete semantics
#|
 (define-metafunction CESΞK
   [(combine-stores σ σ*) ,(append (term σ) (term σ*))])
 (define-metafunction CESΞK
   [(alloc (v σ Ξ κ) (natural ...))
    ,(add1 (max (max-nat-keys (term σ)) (max-nat-list (term (natural ...)))))])
 (define-metafunction CESΞK
   [(create-entry (v_n σ Ξ (push () ((clo lam ρ) v ...) ρ_unused κ)))
    ((clo lam ρ) σ Ξ (entry (v ... v_n) κ))])
|#

;; abstract semantics
 (define-metafunction CESΞK
  [(combine-stores σ σ*)
   ,(for/fold ([res (term σ)]) ([(k lst-v) (in-dict (term σ*))])
      (dict-set res k (append-nodups lst-v (dict-ref res k '()))))])

(define monovariance (make-parameter #f))
(define var-count (make-parameter #f))
(define (ref-bump x)
  (dict-ref (monovariance) x (λ _ (define c (var-count)) (var-count (add1 c)) c)))

 (define-metafunction CESΞK
  [(alloc ((clo (λ (x ..._i) e) ρ) σ Ξ (entry (v ..._i) κ)) (natural ...))
   ,(ref-bump (list-ref (term (x ...)) (length (term (natural ...)))))]
  [(alloc (v_n σ Ξ (goto () ((clo (λ (x ..._i x_n) e) ρ) v ..._i) ρ_unused κ)) (natural ...))
   ,(ref-bump (list-ref (term (x ... x_n)) (length (term (natural ...)))))])

;; local semantics (abstract semantics plus next metafunction)
 (define-metafunction CESΞK
  [(create-entry (v_n σ (ξ_top ξ ...) (push () ((clo lam ρ) v ...) ρ_unused κ)))
   ((clo lam ρ) σ (ξ_top) (entry (v ... v_n) truncated))])

;; common metafunctions
(define-metafunction CESΞK
  [(lookup (Heap/Stack natural_h natural_s) #t σ (ξ_top ξ ...)) (,(list-ref (term ξ_top) (term natural_s)))]
  [(lookup (Stack natural_s)                #t σ (ξ_top ξ ...)) (,(list-ref (term ξ_top) (term natural_s)))]
  [(lookup (Heap/Stack natural_h natural_s) #f σ Ξ) ,(dict-ref (term σ) (term natural_h))])
(define-metafunction CESΞK
  [(env-lookup ((x_pre ℓ_pre) ... (x ℓ) (x_post ℓ_post) ...) x) ℓ])
(define-metafunction CESΞK
  [(env-extend ((x ℓ) ...) x_new ℓ_new) ((x_new ℓ_new) (x ℓ) ...)])
(define-metafunction CESΞK
  [(env-extend* ρ () ()) ρ]
  [(env-extend* ρ (y z ..._i) (ℓ_new ℓ_rest ..._i))
   (env-extend* (env-extend ρ y ℓ_new) (z ...) (ℓ_rest ...))])
(define-metafunction CESΞK
  [(Ξ-pop (ξ_top ξ ...)) (ξ ...)])
(define-metafunction CESΞK
  [(Ξ-push ξ (ξ_rest ...)) (ξ ξ_rest ...)])
(define-metafunction CESΞK
  [(Ξ-extend (v ...) ((v_top ...) ξ_rest ...)) ((v ... v_top ...) ξ_rest ...)])
(define-metafunction CESΞK
  [(untail e) e]
  [(untail (tail e)) e])

(define-metafunction CESΞK
  ;; exit-tc thunk
  [(color ((clo (λ () e) ρ) σ Ξ (goto () () ρ_unused κ)))
   ((tail e) ρ σ Ξ (exit κ))]
  ;; exit-tc
  [(color (name ς (v_n σ Ξ (goto () ((clo (λ (x ..._i x_n) e) ρ) v ..._i) ρ_unused κ))))
   ((tail e) (env-extend* ρ (x ... x_n) (ℓ_all ...)) (combine-stores σ σ_new)
    (Ξ-push ξ (Ξ-pop Ξ)) κ)
   (where ξ (v ... v_n))
   (where ((ℓ_all ...) σ_new) (color-alloc ς ((x v) ... (x_n v_n))))]
  ;; entry
  [(color (name ς ((clo (λ (x ..._i) e) ρ) σ Ξ (entry (v ..._i) κ))))
   ((tail e) (env-extend* ρ (x ...) (ℓ_all ...)) (combine-stores σ σ_new)
    (Ξ-push ξ Ξ) (exit κ))
   (where ξ (v ...))
   (where ((ℓ_all ...) σ_new) (color-alloc ς ((x v) ...)))]
  [(color ς) fail] ;; XXX: avoid stuck states
  )

(define-metafunction CESΞK
  [(color-alloc ς ((x v) ...))
   ,(let ()
      (define-values (heap-locs σnew) (values (box '()) (box '())))
      (define (var->loc i x v)
        (cond [(in-stack? x) (term (Stack ,i))]
              [else (define hloc (term (alloc ς ,(unbox heap-locs))))
                    (set-box! heap-locs (cons hloc (unbox heap-locs)))
                    (set-box! σnew (term (combine-stores ,(unbox σnew) ((,hloc ,v)))))
                    (term (Heap/Stack ,hloc ,i))]))
      (define ℓs (mapi var->loc (term (x ...)) (term (v ...))))
      (printf "Coloring: ~a ~a~%" ℓs (prettyfy-ς (unbox σnew)))
      (term (,ℓs ,(unbox σnew))))])

(define R
  (reduction-relation CESΞK
    ;; terminal eval states
    [--> (d ρ σ Ξ κ) (v σ Ξ κ)
         (where (ann-ref x bool) (untail d))
         (where (v_pre ... v v_post ...) (lookup (env-lookup ρ x) bool σ Ξ))]
    [--> (d ρ σ Ξ κ) ((clo lam ρ) σ Ξ κ)
         (where lam (untail d))] ;; closure creation
    [--> (d ρ σ Ξ κ) (c σ Ξ κ) ;; literal values
         (where (qwote c) (untail d))]
    [--> (d ρ σ Ξ κ) (primop σ Ξ κ) ;; primops are values
         (where primop (untail d))]
    ;; non-tail call
    [--> ((e_0 e ...) ρ σ Ξ κ) (e_0 ρ σ Ξ (push (e ...) () ρ κ))]
    ;; tail call
    [--> ((tail (e_0 e ...)) ρ σ Ξ κ) (e_0 ρ σ Ξ (goto (e ...) () ρ κ))]
    ;; argument evaluation
    [--> (v σ Ξ (call (e_1 e ...) (v_0 ...) ρ κ)) (e_1 ρ σ Ξ (call (e ...) (v_0 ... v) ρ κ))]
    ;; non-tail call
    [--> ς-call (create-entry ς-call)]
    [--> ((clo (λ () e) ρ) σ Ξ (push () () ρ_unused κ))
         ((clo (λ () e) ρ) σ Ξ (create-entry () κ))]
    ;; function entry (requires allocation)
    [--> ς-colorable ς_next
         (where ς_next (color ς-colorable))]
    ;; Exit a non-tail call
    [--> (v σ Ξ (exit κ)) (v σ (Ξ-pop Ξ) κ)]
    ;; primop evaluation
    [--> ((if e_0 e_1 e_2) ρ σ Ξ κ) (e_0 ρ σ Ξ (select e_1 e_2 ρ κ))]
    [--> ((tail (if e_0 e_1 e_2)) ρ σ Ξ κ) (e_0 ρ σ Ξ (select (tail e_1) (tail e_2) ρ κ))]
    [--> (#f σ Ξ (select d_1 d_2 ρ κ)) (d_2 ρ σ Ξ κ)]
    [--> (v σ Ξ (select d_1 d_2 ρ κ)) (d_1 ρ σ Ξ κ)
         (side-condition (term v))]
    [--> (v_n σ Ξ (call () (primop v ...) ρ κ))
         ((δ primop v ... v_n) σ Ξ κ)]))

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

(define-syntax-rule (is-state? pattern term)
  (not (not (redex-match CESΞK pattern term))))

(define-syntax-rule (redex-let/fail language fail-value ([pat rhs] ...) body1 body ...)
  (with-handlers ([exn:fail:redex? (λ _ fail-value)])
    (redex-let language ([pat rhs] ...) body1 body ...)))

(define names (make-parameter #f))
(define (prettyfy-ς ς) (strip-annotation ς (names)))
(define (inject e)
  (Stack? (make-hasheq))
  (names (make-hasheq))
  (monovariance (make-hasheq))
  (var-count 0)
  (define annotated-e
    (escape-analysis! e (Stack?)
                      #:annotate-static-depth? #f
                      #:original-name-ht (names)))
  (term (,annotated-e () () (()) halt)))

(define (CFA2 e)
  (define I (inject e))
  (define initial-work (list I I))
  (define (succ ς̃) (apply-reduction-relation R ς̃))
  (define (insert! k . hts) (for ([ht (in-list hts)]) (hash-set! ht k #t)))
  (define (Seen? pair) (hash-has-key? Seen pair))
  (define (prettyfy-ς̃ ς)
    (cond [(equal? ς I) 'I]
          [else (prettyfy-ς ς)]))
  ;; Summary : entry ↦ setof exit
  ;; Seen/Work : (list state state) ↦ #t
  ;; Callers/TCallers : entry ↦ (list caller entry)
  ;; Final : state ↦ #t
  (define-values (Summary Seen Callers TCallers) (values (make-hash) (make-hash) (make-hash) (make-hash)))
  (define-values (Final Work) (values (make-hasheq) (make-hasheq)))
  (define (Update! ς̃₁ ς̃₂ ς̃₃ ς̃₄)
    (apply printf "Updating ~%〈~a,~% ~a,~% ~a,~% ~a〉~%" (map prettyfy-ς̃ (list ς̃₁ ς̃₂ ς̃₃ ς̃₄)))
    (redex-let/fail CESΞK (void)
                   ([ς ς̃₁]
                    [(v_n2 σ_2 Ξ_2 (push () (v_2 ...) ρ_unused κ_2)) ς̃₂]
                    [(v_n3 σ_3 Ξ_3 (entry (v_3 ...) truncated)) ς̃₃]
                    [(v_n4 σ_4 Ξ_4 (exit κ_4)) ς̃₄])
      (Propagate! ς̃₁ (term (v_n4 σ_4 Ξ_2 κ_2)))))
  (define (Propagate! ς̃₁ ς̃₂)
    (define pair (list ς̃₁ ς̃₂))
    (unless (Seen? pair) (insert! pair Seen Work)))
  (define (Intermediate! ς̃₁ ς̃₂)
    (for ([ς̃₃ (in-list (succ ς̃₂))]) (printf "  Next ~a~%" (prettyfy-ς̃ ς̃₃))
      (Propagate! ς̃₁ ς̃₃)))

  (pretty-print (Stack?)) (newline)
  (insert! initial-work Seen Work)
  (let analyze ()
    (match (set-grab Work)
      [#f (list Summary Final)] ;; done
      [(list ς̃₁ ς̃₂)
       (apply printf "~%Processing ~%〈~a,~% ~a〉~%" (map prettyfy-ς̃ (list ς̃₁ ς̃₂)))
       (cond [(is-state? ς-eval ς̃₂) (printf "Eval~%") (Intermediate! ς̃₁ ς̃₂)]
             [(is-state? ς-intermediate-apply ς̃₂)  (printf "Apply~%") (Intermediate! ς̃₁ ς̃₂)]
             [(is-state? ς-entry ς̃₂) (printf "Entry~%") (Intermediate! ς̃₁ ς̃₂)]

             [(is-state? ς-call ς̃₂) (printf "Call~%")
              (for ([ς̃₃ (in-list (succ ς̃₂))]) (printf "  Next ~a~%" (prettyfy-ς̃ ς̃₃))
                (Propagate! ς̃₃ ς̃₃)
                (insert-caller! Callers (ς̃₁ ς̃₂ ς̃₃))
                (for-summary Summary (ς̃₃ ς̃₄) (Update! ς̃₁ ς̃₂ ς̃₃ ς̃₄)))]

             [(is-state? ς-final ς̃₂) (printf "Final~%") (insert! ς̃₂ Final)]

             [(is-state? ς-exit ς̃₂) (printf "Exit~%")
              (cond [(equal? ς̃₁ I) (insert! ς̃₂ Final)]
                    [else (add-summary! Summary (ς̃₁ ς̃₂))
                          (for-callers Callers (ς̃₃ ς̃₄ ς̃₁) (Update! ς̃₃ ς̃₄ ς̃₁ ς̃₂))
                          (for-callers TCallers (ς̃₃ ς̃₄ ς̃₁) (Propagate! ς̃₃ ς̃₂))])]

             [(is-state? ς-exit-tc ς̃₂) (printf "Tail Call~%")
              (for ([ς̃₃ (in-list (succ ς̃₂))]) (printf "  Next ~a~%" (prettyfy-ς̃ ς̃₃))
                (Propagate! ς̃₃ ς̃₃)
                (insert-caller! TCallers (ς̃₁ ς̃₂ ς̃₃))
                (for-summary Summary (ς̃₃ ς̃₄) (Propagate! ς̃₁ ς̃₄)))]

             [else (error 'analyze "Uncaught case ~a~%" ς̃₂)])
       (analyze)])))

(define t (translate '(let fact ([n 4]
                                 [acc 1])
                        (if (zero? n)
                            acc
                            (fact (sub1 n) (* n acc))))))
(define t2 (translate '(let* ([app (λ (f e) (f e))]
                              [id (λ (x) x)]
                              [n1 (app id 1)]
                              [n2 (app id 2)])
                         (+ n1 n2))))
(define t3 (translate '(let* ([n1 1]
                              [n2 2])
                         (+ n1 n2))))
t
(newline)
(CFA2 t)
;(apply-reduction-relation* R (inject t))
; (define ς (inject t))