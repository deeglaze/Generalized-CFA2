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
         (where (v_pre ... v v_post ...) ,((lookup) (term (untail tailx)) (term σ) (term κ)))]
    ;; non-tail call
    [--> ((e_0 e ...) σ κ) (e_0 σ (push (e ...) () κ))]
    ;; tail call
    [--> ((tail (e_0 e ...)) σ κ) (e_0 σ (goto (e ...) () κ))]
    ;; thunks
    [--> ((λ () e) σ (push () () κ)) ((λ () e) σ (exit ()))]
    [--> (tailv σ (fncall (e_1 e ...) (v_0 ...) κ))
         (e_1 σ (fncall (e ...) (v_0 ... (untail tailv)) κ))]
    ;; call
    [--> (tailv_n σ (push () (v ...) κ)) ((untail tailv_n) σ (exit (v ...)))]
    ;; entry
    [--> (name ς (tailv_n σ (exit ((λ (x ..._ids x_n) e) v ..._ids))))
         ((tail e)
          ,((combine-stores) (term σ) (term σ*))
          (return ρ*))
         (where (σ* ρ*) ,(color (term ς) (term ((x v) ... (x_n (untail tailv_n))))))]
    ;; tail call exit
    [--> (name ς (tailv_n σ (goto () ((λ (x ..._ids x_n) e) v ..._ids) κ)))
         ((tail e)
          ,((combine-stores) (term σ) (term σ*))
          ,(κ-update 'goto (term κ) (term ρ*)))
         (where (σ* ρ*) ,(color (term ς) (term ((x v) ... (x_n (untail tailv_n))))))]
    ;; entry thunk
    [--> ((λ () e) σ (exit ())) ((tail e) σ (return ()))]
    [--> ((tail (λ () e)) σ (exit ())) ((tail e) σ (return ()))]
    ;; primop evaluation
    [--> ((if-zero e_0 e_1 e_2) σ κ) (e_0 σ (select e_1 e_2 κ))]
    [--> ((tail (if-zero e_0 e_1 e_2)) σ κ) (e_0 σ (select (tail e_1) (tail e_2) κ))]
    ;; non-deterministic if-zero
    [--> (0 σ (select d_1 d_2 κ)) (d_1 σ κ)]
    [--> (tailv σ (select d_1 d_2 κ)) (d_2 σ κ)
         (where v (untail tailv))
         (side-condition (not (zero? (term v))))]
    [--> (c_n σ (fncall () (primop c ...) κ))
         (,(δ (term primop) (term (c ... c_n))) σ κ)
         (side-condition (arity-check (term primop) (length (term (c ... c_n)))))]))
#|
(1 ((f1601 (λ (fact) (λ (n acc) (if-zero n acc (fact (- n 1) (* n acc))))))
    (g1603 (λ (g1603) (f1601 (λ (g1599 g1600) ((g1603 g1603) g1599 g1600)))))
    (fact (λ (g1599 g1600) ((g1603 g1603) g1599 g1600))))
   (exit ((λ (n acc) (if-zero n acc (fact (- n 1) (* n acc))))
          4)))
'#hash(((f1601 (λ (g1599 g1600) ((g1603 g1603) g1599 g1600))) . 9)
       (fact . 25)
       (- . 27)
       ((- n 1) . 26)
       ((fact (- n 1) (* n acc)) . 24)
       ((λ (f1601)
          ((λ (t1602) (t1602 t1602))
           (λ (g1603) (f1601 (λ (g1599 g1600) ((g1603 g1603) g1599 g1600))))))
        .
        2)
       (* . 31)
       ((* n acc) . 30)
       (((λ (f1601)
           ((λ (t1602) (t1602 t1602))
            (λ (g1603) (f1601 (λ (g1599 g1600) ((g1603 g1603) g1599 g1600))))))
         (λ (fact) (λ (n acc) (if-zero n acc (fact (- n 1) (* n acc))))))
        .
        1)
       (n . 32)
       (if-zero . 21)
       (((λ (t1602) (t1602 t1602))
         (λ (g1603) (f1601 (λ (g1599 g1600) ((g1603 g1603) g1599 g1600)))))
        .
        3)
       ((λ (t1602) (t1602 t1602)) . 4)
       ((g1603 g1603) . 13)
       ((λ (n acc) (if-zero n acc (fact (- n 1) (* n acc)))) . 19)
       (4 . 34)
       (acc . 33)
       (((g1603 g1603) g1599 g1600) . 12)
       ((t1602 t1602) . 5)
       (g1599 . 16)
       (t1602 . 7)
       ((if-zero n acc (fact (- n 1) (* n acc))) . 20)
       (g1603 . 15)
       (f1601 . 10)
       ((λ (g1599 g1600) ((g1603 g1603) g1599 g1600)) . 11)
       ((((λ (f1601)
            ((λ (t1602) (t1602 t1602))
             (λ (g1603)
               (f1601 (λ (g1599 g1600) ((g1603 g1603) g1599 g1600))))))
          (λ (fact) (λ (n acc) (if-zero n acc (fact (- n 1) (* n acc))))))
         4
         1)
        .
        0)
       ((λ (g1603) (f1601 (λ (g1599 g1600) ((g1603 g1603) g1599 g1600)))) . 8)
       (1 . 35)
       ((λ (fact) (λ (n acc) (if-zero n acc (fact (- n 1) (* n acc))))) . 18)
       (g1600 . 17))
|#

(define-metafunction CŜK
  [(CŜK->CŜK̃ (any σ κ)) (any σ (α̃κ κ))])
(define-metafunction CŜK
  [(α̃κ (return ρ halt)) (halt ρ)]
  [(α̃κ (return ρ κ))
   (return ρ)
   (side-condition (not (eq? (term κ) 'halt)))]
  [(α̃κ (goto (e ...) (v ...) κ)) (goto (e ...) (v ...) (α̃κ κ))]
  [(α̃κ (push () (v ...) κ)) (exit (v ...))]
  [(α̃κ (push (e_1 e ...) (v ...) κ)) (push (e_1 e ...) (v ...) (α̃κ κ))])
(define-metafunction CSK
  [(CSK->CŜK̃ ς) (CŜK->CŜK̃ (CSK->CŜK ς))])
(define-metafunction CŜK̃
  [(untail v) v]
  [(untail (tail v)) v]
  [(untail x) x]
  [(untail (tail x)) x])

;; Workset algorithm to summarize local semantics

(define (localize e)
  (Stack? (create-Stack e))
  (term (CSK->CŜK̃ (,e () (return () halt)))))

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

(define Entry? (term-match/single CŜK̃ [(tailv σ (exit (v_1 ...))) #t]
                                      [any #f]))
(define Call? (term-match/single CŜK̃ [(tailv σ (push () (v_0 ...) κ)) #t]
                                     [any #f]))
(define Exit-TC? (term-match/single CŜK̃ [(tailv σ (goto () (v_0 ...) κ)) #t]
                                        [any #f]))
(define Return? (term-match/single CŜK̃ [(tailv σ (return ρ)) #t]
                                       [any #f]))
(define Intermediate-Apply?
  (term-match/single CŜK̃
    [(tailv σ (fncall (e_1 e ...) (v_0 ...) κ)) #t]
    [(tailv σ (select d_1 d_2 κ)) #t]
    [(c_n σ (fncall () (primop c ...) κ)) #t]
    [any #f]))
(define Exit? (term-match/single CŜK̃ [(tailv σ (exit (v_0 ...))) #t]
                                     [any #f]))
(define Nonvalue-Eval?
  (term-match/single CŜK̃
    [((e_0 e ...) σ κ) #t]
    [((tail (e_0 e ...)) σ κ) #t]
    [(tailx σ κ) #t]
    ;; non-essential
    [((if-zero e_0 e_1 e_2) σ κ) #t]
    [((tail (if-zero e_0 e_1 e_2)) σ κ) #t]
    [any #f]))
(define Final? (term-match/single CŜK̃ [(tailv σ (halt ρ)) #t]
                                      [any #f]))

(define (CFA2 e)
  (define R (R-CŜK̃))
  (define I (localize e))
  (define initial-work (list I I))
  (define (succ ς̃) (apply-reduction-relation R ς̃))
  (define (insert! k . hts) (for ([ht (in-list hts)]) (hash-set! ht k #t)))
  (define (Seen? pair) (hash-has-key? Seen pair))
  ;; Summary : entry ↦ setof exit
  ;; Seen/Work : (list state state) ↦ #t
  ;; Callers/TCallers : entry ↦ (list caller entry)
  ;; Final : state ↦ #t
  (define-values (Summary Seen Callers TCallers) (values (make-hash) (make-hash) (make-hash) (make-hash)))
  (define-values (Final Work) (values (make-hasheq) (make-hasheq)))
  (define (Update! ς̃₁ ς̃₂ ς̃₃ ς̃₄)
    (apply printf "Updating ~%〈~a,~% ~a,~% ~a,~% ~a〉~%" (map name-ς (list ς̃₁ ς̃₂ ς̃₃ ς̃₄)))
    (term-let ([(tailv_n1 σ_1 (exit (v_1 ...))) ς̃₁]
               [(tailv_n2 σ_2 (push () (v_2 ...) κ_2)) ς̃₂]
               [(tailv_n3 σ_3 (exit (v_3 ...))) ς̃₃]
               [(tailv_n4 σ_4 (return ρ)) ς̃₄])
      (Propagate! ς̃₁ (term ((untail tailv_n4) σ_4 κ_2)))))
  (define (Propagate! ς̃₁ ς̃₂)
    (define pair (list ς̃₁ ς̃₂))
    (unless (Seen? pair) (insert! pair Seen Work)))

  (pretty-print (node-names)) (newline)
  (insert! initial-work Seen Work)
  (let analyze ()
    (match (set-grab Work)
      [#f (list Summary Final)] ;; done
      [(list ς̃₁ ς̃₂)
       (apply printf "Processing ~%〈~a,~% ~a〉~%" (map name-ς (list ς̃₁ ς̃₂)))
       (cond [(or (Nonvalue-Eval? ς̃₂)
                  (Intermediate-Apply? ς̃₂)
                  (Exit? ς̃₂))
              (printf "Intermediate ~a~%" (cond [(Nonvalue-Eval? ς̃₂) "Eval"]
                                                [(Intermediate-Apply? ς̃₂) "Apply"]
                                                [(Exit? ς̃₂) "Exit"]))
              (for ([ς̃₃ (in-list (succ ς̃₂))])
                (Propagate! ς̃₁ ς̃₃))]

             [(Call? ς̃₂) (printf "Call~%")
              (for ([ς̃₃ (in-list (succ ς̃₂))])
                (Propagate! ς̃₃ ς̃₃)
                (insert-caller! Callers (ς̃₁ ς̃₂ ς̃₃))
                (for-summary Summary (ς̃₃ ς̃₄) (Update! ς̃₁ ς̃₂ ς̃₃ ς̃₄)))]

             [(Final? ς̃₂) (printf "Final~%") (insert! ς̃₂ Final)]

             [(Return? ς̃₂) (printf "Return~%")
              (add-summary! Summary (ς̃₁ ς̃₂))
              (for-callers Callers (ς̃₃ ς̃₄ ς̃₁) (Update! ς̃₃ ς̃₄ ς̃₁ ς̃₂))
              (for-callers TCallers (ς̃₃ ς̃₄ ς̃₁) (Propagate! ς̃₃ ς̃₂))]

             [(Exit-TC? ς̃₂) (printf "Tail call~%")
              (for ([ς̃₃ (in-list (succ ς̃₂))])
                (Propagate! ς̃₃ ς̃₃)
                (insert-caller! TCallers (ς̃₁ ς̃₂ ς̃₃))
                (for-summary Summary (ς̃₃ ς̃₄) (Propagate! ς̃₁ ς̃₄)))]

             [else (error 'analyze "Uncaught case ~a~%" ς̃₂)])
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

;; tests
(define t (translate '(let fact ([n 4]
                                 [acc 1])
                        (if-zero n
                                 acc
                                 (fact (sub1 n) (* n acc))))))
(define t2 (translate '(let* ([app (λ (f e) (f e))]
                              [id (λ (x) x)]
                              [n1 (app id 1)]
                              [n2 (app id 2)])
                         (+ n1 n2))))
;(define t* (first (CŜK-apply-reduction-relation* t)))
;(trace CŜK-combine-stores)
;(redex-match CŜK (name ς (v_n σ (fncall () ((λ (x ..._ids x_n) e) v ..._ids) κ))) t*)
;(CŜK̃-traces t)
(CFA2 t)
(printf "~%")
;(CFA2 t2)


