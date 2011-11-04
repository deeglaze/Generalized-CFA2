#lang racket
(require redex "utils.rkt")
(provide (all-defined-out))

(define prims '(+ - * = sub1 if-zero))
(define-language LC
  [e (e e ...) ref lam non-essential]
  [ref x primop]
  [lam (λ (x ...) e)]
  [(x y z) variable-not-otherwise-mentioned]
  ;; nicety bits
  [non-essential (if e e e) (qwote c)]
  [c integer bool null void]
  [bool #t #f])
(define-extended-language Annotated-LC LC
  [primop + - * < <= = >= > sub1 cons car cdr null? pair? zero?]
  [ref (ann-ref x bool) primop]) ;; bool ⇔ x is stack reference

(define-extended-language CESΞK Annotated-LC
  [(ρ ρ*) ((x ℓ) ...)]
  [(σ σ*) ((natural v v ...) ...)]
  [ℓ (Heap/Stack natural natural) (Stack natural)]
  [v (clo lam ρ) c primop (cons-cell v v)]
  ;; machine states
  [ς ς-eval ς-apply]
  [d e (tail e)]
  [ς-eval (d ρ σ Ξ κ)]
  [ς-apply (v σ Ξ κ)]
  ;; continuations
  [call push goto]
  [Ξ (ξ ...)]
  [ξ (v ...)]
  [κ halt
     truncated
     (call (e ...) (v ...) ρ κ)
     (select d d ρ κ)
     (entry (v ...) κ)
     (exit κ)]
  ;; state kinds
  [ς-call (v σ Ξ (push () ((clo lam ρ) v ...) ρ κ))
          ((clo lam ρ) σ Ξ (push () () ρ κ))]
  [ς-entry (v σ Ξ (entry (v ...) κ))]
  [ς-exit (v σ Ξ (exit κ))]
  [ς-exit-tc (v σ Ξ (goto () ((clo lam ρ) v ...) ρ κ))
             ((clo lam ρ) σ Ξ (goto () () ρ κ))]
  [ς-final (v σ Ξ halt)]
  [ς-intermediate-apply (v σ Ξ (call (e_1 e ...) (v ...) ρ κ))
                        (v σ Ξ (call () (primop v ...) ρ κ))
                        (v σ Ξ (select d d ρ κ))]
  [ς-top-entry ς-entry (d ρ σ Ξ halt)]
  [ς-colorable ς-entry ς-exit-tc])

(define undef (λ _ (error "Not yet defined")))
;; global
(define Stack? (make-parameter #f))
(define (in-stack? x) (dict-ref (Stack?) x #f))

(define-metafunction CESΞK ;; primop implementation
  [(δ + integer ...) ,(apply + (term (integer ...)))]
  [(δ - integer ...) ,(apply - (term (integer ...)))]
  [(δ * integer ...) ,(apply * (term (integer ...)))]
  [(δ / integer ...) ,(apply / (term (integer ...)))]
  [(δ < integer_0 integer_1) ,(< (term integer_0) (term integer_1))]
  [(δ <= integer_0 integer_1) ,(<= (term integer_0) (term integer_1))]
  [(δ = integer_0 integer_1) ,(= (term integer_0) (term integer_1))]
  [(δ >= integer_0 integer_1) ,(>= (term integer_0) (term integer_1))]
  [(δ > integer_0 integer_1) ,(> (term integer_0) (term integer_1))]
  [(δ sub1 integer) ,(sub1 (term integer))]
  [(δ pair? v) ,(not (not (redex-match CESΞK (cons-cell v_0 v_1) (term v))))]
  [(δ null? v) ,(eq? (term v) 'null)]
  [(δ zero? v) ,(zero? (term v))]
  [(δ boolean? v) ,(boolean? (term v))]
  [(δ procedure? v) ,(not (not (redex-match CESΞK (clo lam ρ) (term v))))]
  [(δ cons v_0 v_1) (cons-cell v_0 v_1)]
  [(δ car (cons-cell v_0 v_1)) v_0]
  [(δ cdr (cons-cell v_0 v_1)) v_1])
