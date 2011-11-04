#lang racket
(require redex "pure-scheme-to-LC.rkt" "langs.rkt" racket/trace)
(provide (all-defined-out))

(define (CŜK-lookup x σ κ)
  (cond [(in-stack? x) (list (find-first-in-cont κ x))]
        [else (dict-ref σ x)]))
(define (CŜK-combine-stores σ* σ)
  (for/fold ([res σ*]) ([(k lst-v) (in-dict σ)])
    (define v* (dict-ref res k '()))
    (dict-set res k (list-union v* lst-v))))
(define (CŜK-alloc ς σ) 0)
;; α concrete -> abstract
(define-metafunction CSK
  [(CSK->CŜK (d σ κ)) (d (α̂σ σ) κ)]
  [(CSK->CŜK (v σ κ)) ((α̂v v) (α̂σ σ) κ)])
(define-metafunction CSK
  [(α̂v integer) abs-int]
  [(α̂v lam) lam]
  [(α̂v primop) primop])
(define-metafunction CSK
  [(α̂ρ ((x v) ...)) ((x (α̂v v)) ...)])
(define-metafunction CSK ;; XXX: wrong
  [(α̂σ ((natural v) ...)) ((natural (α̂v v)) ...)])

(define (R-CŜK)
;  (define super (R-CSK))
  (lookup CŜK-lookup)
  (combine-stores CŜK-combine-stores)
  (alloc CŜK-alloc)
  (local? #f)
  (abstract? #t)
  (reduction-relation CŜK
    [--> (x σ κ) (v σ κ)
         (where (v_pre ... v v_post ...) ,((lookup) (term x) (term σ) (term κ)))]
    [--> ((tail x) σ κ) (v σ κ)
         (where (v_pre ... v v_post ...) ,((lookup) (term x) (term σ) (term κ)))]
    ;; literals must be abstracted
    [--> (literal σ κ) (abs-int σ κ)]
    [--> ((tail literal) σ κ) (abs-int σ κ)]
    ;; closure creation no longer happens
    [--> ((tail lam) σ κ) (lam σ κ)]
    ;; non-tail call
    [--> ((e_0 e ...) σ κ) (e_0 σ (push (e ...) () κ))]
    ;; tail call
    [--> ((tail (e_0 e ...)) σ κ) (e_0 σ (goto (e ...) () κ))]
    ;; argument evaluation
    [--> ((λ () e) σ (goto () () κ)) (e σ κ)]
    [--> ((λ () e) σ (push () () κ)) (e σ (return () κ))]
    [--> (v σ (fncall (e_1 e ...) (v_0 ...) κ)) (e_1 σ (fncall (e ...) (v_0 ... v) κ))]
    ;; entry/exit tail call
    [--> (name ς (v_n σ (fncall () ((λ (x ..._ids x_n) e) v ..._ids) κ)))
         ((tail e)
          ,((combine-stores) (term σ) (term σ*))
          ,(κ-update (term fncall) (term κ) (term ρ*)))
         (where (σ* ρ*) ,(color (term ς) (term ((x v) ... (x_n v_n)))))]
    ;; Exit-CEval
    [--> (v σ (return ρ κ)) (v σ κ)]
    ;; primop evaluation
    [--> ((if-zero e_0 e_1 e_2) σ κ) (e_0 σ (select e_1 e_2 κ))]
    [--> ((tail (if-zero e_0 e_1 e_2)) σ κ) (e_0 σ (select (tail e_1) (tail e_2) κ))]
    ;; non-deterministic if-zero
    [--> (abs-int σ (select d_1 d_2 κ)) (d_1 σ κ)]
    [--> (abs-int σ (select d_1 d_2 κ)) (d_2 σ κ)]
    [--> (c_n σ (fncall () (primop c ...) κ))
         abs-int
         (side-condition (arity-check (term primop) (length (term (c ... c_n)))))]))
