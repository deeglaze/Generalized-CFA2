#lang racket
(require redex "pure-scheme-to-LC.rkt" "langs.rkt" racket/trace)
(provide (all-defined-out))

(define (CSK-lookup x σ κ)
  (define stack (find-first-in-cont κ x))
  (cond [(in-stack? x) (list stack)]
        [else (dict-ref σ stack)]))
(define (CSK-combine-stores σ* σ) (append σ* σ))
(define (CSK-alloc ς σ)
  (match ς
    [`(,v ,σ* ,κ) (add1 (max (max-nat-keys σ*) (max-nat-keys σ)))]))

(define (partially-close lam κ)
  (define free-heap-vars (filter-not in-stack? (fv lam)))
  (for/list ([x (in-list free-heap-vars)])
    (list x (find-first-in-cont κ x))))

;; concrete semantics

(define (R-CSK)
  (alloc CSK-alloc)
  (lookup CSK-lookup)
  (combine-stores CSK-combine-stores)
  (local? #f)
  (abstract? #f)
  (reduction-relation CSK
    ;; lookup
    [--> (x σ κ) (v σ κ)
         (where (v_pre ... v v_post ...) ,((lookup) (term x) (term σ) (term κ)))]
    [--> ((tail x) σ κ) (v σ κ)
         (where (v_pre ... v v_post ...) ,((lookup) (term x) (term σ) (term κ)))]
    ;; closure creation
    [--> (lam σ κ) (v σ κ)
         (where v (cont lam ,(partially-close (term lam) (term κ))))]
    [--> ((tail lam) σ κ) (v σ κ)
         (where v (cont lam ,(partially-close (term lam) (term κ))))]
    ;; non-tail call
    [--> ((e_0 e ...) σ κ) (e_0 σ (push (e ...) () κ))]
    ;; tail call
    [--> ((tail (e_0 e ...)) σ κ) (e_0 σ (goto (e ...) () κ))]
    ;; argument evaluation
    [--> ((cont (λ () e) β) σ (fncall () () κ)) (e σ ,(κ-update (term fncall) (term κ) (term β)))]
    [--> (v σ (fncall (e_1 e ...) (v_0 ...) κ)) (e_1 σ (fncall (e ...) (v_0 ... v) κ))]
    ;; entry/exit tail call
    [--> (name ς (v_n σ (fncall () ((cont (λ (x ..._ids x_n) e) β) v ..._ids) κ)))
         ((tail e)
          ,((combine-stores) (term σ) (term σ*))
          ,(κ-update (term fncall) (term κ) (env-mutate (term β) (term ρ*))))
         (where (σ* ρ*) ,(color (term ς) (term ((x v) ... (x_n v_n)))))]
    ;; Exit-CEval
    [--> (v σ (return ρ κ)) (v σ κ)]
    ;; primop evaluation
    [--> ((if-zero e_0 e_1 e_2) σ κ) (e_0 σ (select e_1 e_2 κ))]
    [--> ((tail (if-zero e_0 e_1 e_2)) σ κ) (e_0 σ (select (tail e_1) (tail e_2) κ))]
    [--> (0 σ (select d_1 d_2 κ)) (d_1 σ κ)]
    [--> (v σ (select d_1 d_2 κ)) (d_2 σ κ)
         (side-condition (not (equal? (term v) 0)))]
    [--> (c_n σ (fncall () (primop c ...) κ))
         (,(δ (term primop) (term (c ... c_n))) σ κ)
         (side-condition (arity-check (term primop) (length (term (c ... c_n)))))]))
