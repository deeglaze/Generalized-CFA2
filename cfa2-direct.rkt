#lang racket
(require redex
         "pure-scheme-to-LC.rkt"
         "cfa2-direct-concrete.rkt"
         "cfa2-direct-abstract.rkt"
         "langs.rkt"
         racket/trace)
(provide (all-defined-out))

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
    [--> (tailx σ κ) (v σ κ)
         (where (v_pre ... v v_post ...) ,((lookup) (term tailx) (term σ) (term κ)))]
    ;; literals must be abstracted
    [--> (literal σ κ) (abs-int σ κ)]
    [--> ((tail literal) σ κ) (abs-int σ κ)]
    ;; non-tail call
    [--> ((e_0 e ...) σ κ) (e_0 σ (push (e ...) () κ))]
    ;; tail call
    [--> ((tail (e_0 e ...)) σ κ) (e_0 σ (goto (e ...) () κ))]
    ;; thunks
    [--> ((λ () e) σ (push () () κ)) ((λ () e) σ (exit ()))]
    [--> (tailv σ (fncall (e_1 e ...) (v_0 ...) κ))
         (e_1 σ (fncall (e ...) (v_0 ... tailv) κ))]
    ;; call
    [--> (tailv_n σ (push () (v ...) κ)) (tailv_n σ (exit (v ...)))]
    ;; entry
    [--> (tailv_n σ (exit ((λ (x ..._ids x_n) e) v ..._ids)))
         ((tail e)
          ,((combine-stores) (term σ) (term σ*))
          (return ρ*))
         (where (σ* ρ*) ,(color (term ς) (term ((x v) ... (x_n tailv_n)))))]
    ;; tail call exit
    [--> (tailv_n σ (goto () ((λ (x ..._ids x_n) e) v ..._ids) κ))
         ((tail e)
          ,((combine-stores) (term σ) (term σ*))
          ,(κ-update 'goto (term κ) (term ρ*)))
         (where (σ* ρ*) ,(color (term ς) (term ((x v) ... (x_n tailv_n)))))]
    ;; entry thunk
    [--> ((λ () e) σ (exit ())) ((tail e) σ (return ()))]
    [--> ((tail (λ () e)) σ (exit ())) ((tail e) σ (return ()))]
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
  [(α̃κ (return ρ κ)) (return ρ)]
  [(α̃κ (goto (e ...) (v ...) κ)) (goto (e ...) (v ...) (α̃κ κ))]
  [(α̃κ (push () (v ...) κ)) (exit (v ...))]
  [(α̃κ (push (e_1 e ...) (v ...) κ)) (push (e_1 e ...) (v ...) (α̃κ κ))])
(define-metafunction CSK
  [(CSK->CŜK̃ ς) (CŜK->CŜK̃ (CSK->CŜK ς))])

;; Workset algorithm to summarize local semantics

(define (localize e)
  (Stack? (create-Stack e))
  (term (CSK->CŜK̃ (,e () (return () halt)))))

(define-syntax-rule (for-callers Callers (ς̃entry ς̃call ς̃callee-entry) body1 body ...)
  (for ([(ς̃entry caller×callee) (in-dict Callers)]
        #:when (equal? ς̃callee-entry (second caller×callee)))
    (let ([ς̃call (first caller×callee)])
      body1 body ...)))

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
  (define (name-ς ς)
    (list (name-term (first ς)) (name-σ (second ς)) (name-κ (third ς))))
  (define (name-term tm)
    (define t ((term-match/single CŜK̃
      [v (term v)]
      [(tail v) (term v)]
      [literal (term literal)]
      [(name t (e_0 e ...)) (term t)]
      [(name t (tail (e_0 e ...))) (term t)]
      [x (term x)]
      [(tail x) (term x)]
      [any (error 'name-term "WTF ~a" tm)]) tm))
    (hash-ref (node-names) t `(??? ,t)))
  (define (name-σ σ)
    (for/list ([kv (in-list σ)]) (cons (first kv) (map name-term (rest kv)))))
  (define (name-κ κ)
    ((term-match/single CŜK̃
       [halt (term halt)]
       [(exit (tailv ...)) (term (exit ,(map name-term (term (tailv ...)))))]
       [(return ρ) (term (return ,(name-σ (term ρ))))]
       [(fncall (e ...) (tailv ...) κ)
        (term (fncall ,(map name-term (term (e ...)))
                      ,(map name-term (term (tailv ...)))
                      ,(name-κ (term κ))))]
       [(select d_1 d_2 κ)
        (term (select ,(name-term (term d_1)) ,(name-term (term d_2)) ,(name-κ (term κ))))]
       [any (error 'name-κ "WTF ~a" κ)])
     κ))
  (define Entry? (term-match/single CŜK̃ [(tailv σ (exit (lam tailv_1 ...))) #t]
                                        [any #f]))
  (define Call? (term-match/single CŜK̃ [(tailv σ (push () (tailv_0 ...) κ)) #t]
                                       [any #f]))
  (define Exit-TC? (term-match/single CŜK̃ [(tailv σ (goto () (tailv_0 ...) κ)) #t]
                                          [any #f]))
  (define Return? (term-match/single CŜK̃ [(tailv σ (return ρ)) #t]
                                         [any #f]))
  (define Intermediate-Apply?
    (term-match/single CŜK̃
      [(tailv σ (fncall (e_1 e ...) (tailv_0 ...) κ)) #t]
      [(tailv σ (select d_1 d_2 κ)) #t]
      [(c_n σ (fncall () (primop c ...) κ)) #t]
      [any #f]))
  (define Exit? (term-match/single CŜK̃ [(tailv σ (exit (tailv_0 ...))) #t]
                                       [any #f]))
  (define Nonvalue-Eval?
    (term-match/single CŜK̃
      [((e_0 e ...) σ κ) #t]
      [((tail (e_0 e ...)) σ κ) #t]
      [(tailx σ κ) #t]
      [any #f]))
  (define Final? (term-match/single CŜK̃ [(v σ halt) #t]
                                        [any #f]))
  (define (Update! ς̃₁ ς̃₂ ς̃₃ ς̃₄)
    (apply printf "Updating ~%〈~a,~% ~a,~% ~a,~% ~a〉~%" (map name-ς (list ς̃₁ ς̃₂ ς̃₃ ς̃₄)))
    (term-let ([(v_n1 σ_1 (exit (v_1 ...))) ς̃₁]
               [(v_n2 σ_2 (push () (v_2 ...) κ_2)) ς̃₂]
               [(v_n3 σ_3 (exit (v_3 ...))) ς̃₃]
               [(v_n4 σ_4 (return ρ)) ς̃₄])
      (Propagate! ς̃₁ (term (v_n4 σ_4 κ_2)))))
  (define (Propagate! ς̃₁ ς̃₂)
    (define pair (list ς̃₁ ς̃₂))
    (unless (hash-has-key? Seen pair)
      (hash-set! Seen pair #t)
      (hash-set! Work pair #t)))
  (define (Intermediate! ς̃₁ ς̃₂)
    (printf "Intermediate~%")
    (for ([ς̃₃ (in-list (succ ς̃₂))])
      (Propagate! ς̃₁ ς̃₃)))
  (let analyze ()
    (match (set-grab Work)
      [#f (list Summary Final)] ;; done
      [(list ς̃₁ ς̃₂)
       (apply printf "Processing ~%〈~a,~% ~a〉~%" (map name-ς (list ς̃₁ ς̃₂)))
       (cond [(or (Nonvalue-Eval? ς̃₂)
                  (Intermediate-Apply? ς̃₂)
                  (Exit? ς̃₂))
              (Intermediate! ς̃₁ ς̃₂)]

             [(Call? ς̃₂)
              (printf "Call~%")
              ;; insert callers and update via summary
              (for ([ς̃₃ (in-list (succ ς̃₂))])
                (Propagate! ς̃₃ ς̃₃)
                (hash-set! Callers ς̃₁ (list ς̃₂ ς̃₃))
                (for ([ς̃₄ (in-list (dict-ref Summary ς̃₃ '()))])
                  (Update! ς̃₁ ς̃₂ ς̃₃ ς̃₄)))]

             [(Final? ς̃₂)
              (printf "Final~%")
              (hash-set! Final ς̃₂ #t)]

             [(Return? ς̃₂)
              (printf "Return~%")
              (hash-set! Summary ς̃₁ ς̃₂)
              (for-callers Callers (ς̃₃ ς̃₄ ς̃₁) (Update! ς̃₃ ς̃₄ ς̃₁ ς̃₂))
              (for-callers TCallers (ς̃₃ ς̃₄ ς̃₁) (Propagate! ς̃₃ ς̃₂))]

             [(Exit-TC? ς̃₂)
              (printf "Tail call~%")
              (for ([ς̃₃ (in-list (succ ς̃₂))]) ;; tails have no successor in local semantics!
                (Propagate! ς̃₃ ς̃₃)
                (hash-set! TCallers ς̃₁ (list ς̃₂ ς̃₃))
                (printf "Looking for ~a...~%" ς̃₃)
                (for ([ς̃₄ (in-list (dict-ref Summary ς̃₃ '()))])
                  (Propagate! ς̃₁ ς̃₄)))])
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
  (define R (R-CŜK̃))
  (traces R (localize t)))
(define (CŜK̃-apply-reduction-relation* t)
  (define R (R-CŜK̃))
  (apply-reduction-relation* R (localize t)))

(define R (R-CŜK̃))

#;
(redex-match CŜK̃ (v σ any)
             '((λ (g1508) (f1506 (λ (g1504 g1505) ((g1508 g1508) g1504 g1505))))
               ((f1506 (λ (fact) (λ (n acc) (if-zero n acc (fact (- n 1) (* n acc)))))))
               (goto () ((λ (t1507) (t1507 t1507))) (return ()))))

;; tests
(define t (translate '(let fact ([n 4]
                                 [acc 1])
                        (if-zero n
                                 acc
                                 (fact (sub1 n) (* n acc))))))
(localize t)
(printf "~%")
(pretty-print (node-names))
(printf "~%")

;(define t* (first (CŜK-apply-reduction-relation* t)))
;(trace CŜK-combine-stores)
;(redex-match CŜK (name ς (v_n σ (fncall () ((λ (x ..._ids x_n) e) v ..._ids) κ))) t*)
;(CŜK̃-traces t)
(CFA2 t)

