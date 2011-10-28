#lang racket
(require redex
         "pure-scheme-to-LC.rkt"
         "cfa2-direct-concrete.rkt"
         "cfa2-direct-abstract.rkt"
         "langs.rkt"
         racket/trace)
(provide (all-defined-out))

;; tests
(define t (translate '(let fact ([n 4]
                                 [acc 1])
                        (if-zero n
                                 acc
                                 (fact (sub1 n) (* n acc))))))
t
(printf "~%")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Localized machine
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; local semantics
(define (R-CŜK̃)
  (lookup CŜK-lookup)
  (combine-stores CŜK-combine-stores)
  (alloc CŜK-alloc)
  (abstract? #t)
  (local? #t)
  (reduction-relation CŜK̃
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
    ;; at least one more tail call argument to evaluate afterwards.
    [--> (v σ (goto (e_1 e_2 e ...) (v_0 ...) κ)) (e_1 σ (goto (e_2 e ...) (v_0 ... v) κ))]
    ;; last argument before exiting with a tail call
    [--> (v σ (goto (e) (v_0 ...) κ)) (e σ (exit-tc (v_0 ... v) κ))]
    [--> (v σ (push (e_1 e ...) (v_0 ...) κ)) (e_1 σ (push (e ...) (v_0 ... v) κ))]
    ;; entry
    [--> (name ς (v_n σ (push () ((λ (x ..._ids x_n) e) v ..._ids) κ)))
         ((tail e)
          ,((combine-stores) (term σ) (term σ*))
          ,(κ-update 'push (term κ) (term ρ*)))
         (where (σ* ρ*) ,(color (term ς) (term ((x v) ... (x_n v_n)))))]
    ;; Exit-CEval
    [--> (v σ (return ρ κ)) (v σ κ)]
    [--> (v_n σ (exit-tc ((λ (x ..._ids x_n) e) v ..._ids) κ))
         ((tail e)
          ,((combine-stores) (term σ) (term σ*))
          ,(κ-update 'goto (term κ) (term ρ*)))
         (where (σ* ρ*) ,(color (term ς) (term ((x v) ... (x_n v_n)))))]
    ;; primop evaluation
    [--> ((if-zero e_0 e_1 e_2) σ κ) (e_0 σ (select e_1 e_2 κ))]
    [--> ((tail (if-zero e_0 e_1 e_2)) σ κ) (e_0 σ (select (tail e_1) (tail e_2) κ))]
    ;; non-deterministic if-zero
    [--> (abs-int σ (select d_1 d_2 κ)) (d_1 σ κ)]
    [--> (abs-int σ (select d_1 d_2 κ)) (d_2 σ κ)]
    [--> (c_n σ (fncall () (primop c ...) κ))
         (abs-int σ κ)
         (side-condition (arity-check (term primop) (length (term (c ... c_n)))))]))

(define-metafunction CŜK
  [(CŜK->CŜK̃ (any σ κ)) (any σ (α̃κ κ))])
(define-metafunction CŜK
  [(α̃κ halt) halt]
  [(α̃κ (return ρ κ)) (return ρ (α̃κ κ))]
  [(α̃κ (tail () (v ...) κ)) (exit-tc (v ...) κ)]
  [(α̃κ (tail (e_1 e ...) (v ...) κ)) (goto (e_1 e ...) (v ...) (α̃κ κ))]
  [(α̃κ (push (e ...) (v ...) κ)) (push (e ...) (v ...) (α̃κ κ))])
(define-metafunction CŜK
  [(top-ρ (fncall (e ...) (v ...) κ)) (top-ρ κ)]
  [(top-ρ (return ρ κ)) ρ])
(define-metafunction CSK
  [(CSK->CŜK̃ ς) (CŜK->CŜK̃ (CSK->CŜK ς))])

;; Workset algorithm to summarize local semantics

(define (localize e)
  (term (CSK->CŜK̃ (,e () (return () halt)))))

(define (CFA2 e)
  (define R (R-CŜK̃))
  (define (succ ς̃) (apply-reduction-relation R ς̃))
  (define I (localize e))
  (define Summary (make-hash)) ;; entry ↦ listof exit
  (define Seen (make-hash)) ;; (list state state) ↦ #t
  (define Callers (make-hash)) ;; entry ↦ (list caller entry)
  (define TCallers (make-hash)) ;; entry ↦ (list caller entry)
  (define Final (make-hasheq)) ;; state ↦ #t
  (define Work (make-hasheq))
  (define initial-work (list I I))
  (hash-set! Work initial-work #t)
  (hash-set! Seen initial-work #t)
#|
  (define Entry? (term-match/single CŜK̃ [(v σ (push () ((λ (x ...) e) v_0 ...) κ)) #t]
                                        [((λ () e) σ (push () () κ)) #t]
                                        [any #f]))
  (define Intermediate? (term-match/single CŜK̃ [(v σ (push (e_1 e ...) (v_0 ...) κ)) #t]
                                               [any #f]))
  (define Exit-TC? (term-match/single CŜK̃ [(v σ (exit-tc (v ...))) #t]
                                          [any #f]))
  (define Return? (term-match/single CŜK̃ [(v σ (return ρ κ)) #t]
                                         [any #f]))
|#
  (define (Update! ς̃₁ ς̃₂ ς̃₃ ς̃₄)
    (printf "Update! ~a~%~a~%~a~%~a~%" ς̃₁ ς̃₂ ς̃₃ ς̃₄))
  (define (Propagate! ς̃₁ ς̃₂)
    (define pair (list ς̃₁ ς̃₂))
;    (printf "Propagate! ~a~%~a~%" ς̃₁ ς̃₂)
    (unless (hash-has-key? Seen pair)
      (hash-set! Seen pair #t)
      (hash-set! Work pair #t)))
  (let analyze ()
    (match (set-grab Work)
      [#f (list Summary Final)] ;; done
      [(list ς̃₁ ς̃₂)
       (printf "Processing ~%〈~a,~% ~a〉~%" ς̃₁ ς̃₂)
       ((term-match/single CŜK̃
          [(d σ κ)
           (for ([ς̃₃ (in-list (succ ς̃₂))])
             (Propagate! ς̃₁ ς̃₃))]
          ;; [apply states]
          [(v σ (push () ((λ (x ...) e) v_0 ...) κ)) ;; call
           ;; insert callers and update via summary
           (for ([ς̃₃ (in-list (succ ς̃₂))])
             (Propagate! ς̃₃ ς̃₃)
             (hash-set! Callers ς̃₁ (list ς̃₂ ς̃₃))
             (for ([ς̃₄ (in-list (dict-ref Summary ς̃₃ '()))])
               (Update! ς̃₁ ς̃₂ ς̃₃ ς̃₄)))]

          [(v σ (fncall (e_0 e ...) (v_0 ...) κ)) ;; inner evaluation
           (for ([ς̃₃ (in-list (succ ς̃₂))])
             (Propagate! ς̃₁ ς̃₃))] ;; propagate successors
          ;; extra stuff
          [(v σ (select d_1 d_2 κ))
           (for ([ς̃₃ (in-list (succ ς̃₂))])
             (Propagate! ς̃₁ ς̃₃))]
          [(c_n σ (fncall () (primop c ...) κ))
           (for ([ς̃₃ (in-list (succ ς̃₂))])
             (Propagate! ς̃₁ ς̃₃))]

          [(v σ (return ρ halt)) ;; final state
           (hash-set! Final ς̃₂ #t)]

          [(v σ (return ρ κ)) ;; exit/inner return
           (begin
             (hash-set! Summary ς̃₁ ς̃₂)
             (for ([(ς̃₃ caller×callee) (in-dict Callers)]
                   #:when (equal? ς̃₁ (second caller×callee)))
               (Update! ς̃₃ (first caller×callee) ς̃₁ ς̃₂))
             (for ([(ς̃₃ caller×callee) (in-dict TCallers)]
                   #:when (equal? ς̃₁ (second caller×callee)))
               (Propagate! ς̃₃ (first caller×callee))))]

          [(v σ (exit-tc (v_0 ...) κ))
           (for ([ς̃₃ (in-list (succ ς̃₂))])
             (Propagate! ς̃₃ ς̃₃)
             (hash-set! TCallers ς̃₁ (list ς̃₂ ς̃₃))
             (printf "Looking for ~a...~%" ς̃₃)
             (for ([ς̃₄ (in-list (dict-ref Summary ς̃₃ '()))])
               (Propagate! ς̃₁ ς̃₄)))])
        ς̃₂)
       (analyze)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define (CSK-traces t)
  (Stack? (create-Stack t))
  (define R (R-CSK))
  (traces R `(,t () (return () halt))))
(define (CSK-apply-reduction-relation t)
  (Stack? (create-Stack t))
  (define R (R-CSK))
  (apply-reduction-relation R `(,t () (return () halt))))
(define (CSK-apply-reduction-relation* t)
  (Stack? (create-Stack t))
  (define R (R-CSK))
  (apply-reduction-relation* R `(,t () (return () halt))))

(define (CŜK-traces t)
  (Stack? (create-Stack t))
  (define R (R-CŜK))
  (traces R `(,t () (return () halt))))
(define (CŜK-apply-reduction-relation* t)
  (Stack? (create-Stack t))
  (define R (R-CŜK))
  (apply-reduction-relation* R (term (CSK->CŜK (,t () (return () halt))))))

(define (CŜK̃-traces t)
  (Stack? (create-Stack t))
  (define R (R-CŜK̃))
  (traces R (localize t)))
(define (CŜK̃-apply-reduction-relation* t)
  (Stack? (create-Stack t))
  (define R (R-CŜK̃))
  (apply-reduction-relation* R (localize t)))

;(define t* (first (CŜK-apply-reduction-relation* t)))
;(trace CŜK-combine-stores)
;(redex-match CŜK (name ς (v_n σ (fncall () ((λ (x ..._ids x_n) e) v ..._ids) κ))) t*)
;(CŜK̃-traces t)
(CFA2 t)
