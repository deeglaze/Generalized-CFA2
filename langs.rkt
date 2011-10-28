#lang racket
(require redex)
(provide (all-defined-out))

(define prims '(+ - * = sub1 if-zero))
(define-language LC
  [e (e e ...) x lam non-essential]
  [lam (λ (x ...) e)]
  [(x y z) variable-not-otherwise-mentioned]
  [non-essential (if-zero e e e) literal primop]
  [primop + - * = sub1]
  [literal integer])

;; concrete
(define-extended-language CSK LC
  [(ρ ρ*) ((x v-or-loc) ...)]
  [(σ σ*) ((natural v) ...)]
  [c literal]
  ;; representing closures via binding time (storage location)
  [v (cont lam β) c primop]
  [v-or-loc v natural] ;; to combine β with ρ in κ
  [β ((x natural) ...)]
  ;; machine states
  [ς eval apply]
  [d e (tail e)]
  [eval (d σ κ)]
  [apply (v σ κ)]
  ;; continuations
  [fncall push goto]
  [κ halt
     (fncall (e ...) (v ...) κ)
     (select d d κ)
     (return ρ κ)])
;; abstract
(define-extended-language CŜK CSK
  [σ ((x v v ...) ...)]
  [v lam c primop] ;; closures are all blended in the heap
  [c abs-int])
;; local
(define-extended-language CŜK̃ CŜK
  [κ halt
     (push (e ...) (v ...) κ)
     (goto (e e ...) (v ...) κ)
     (exit-tc (v ...) κ)
     (return ρ κ)
     (select d d κ)])

(define undef (λ _ (error "Not yet defined")))
;; global
(define Stack? (make-parameter #hasheq()))
(define (in-stack? x) (dict-ref (Stack?) x #f))
;; language-specific
(define alloc (make-parameter undef))
(define lookup (make-parameter undef))
(define combine-stores (make-parameter undef))
(define tick (make-parameter undef))
(define abstract? (make-parameter #f))
(define local? (make-parameter #f))

;; syntactic escape analysis
(define (create-Stack t)
  (define maxcount (make-hasheq))
  (define (update! t new) (hash-set! maxcount t (max new (hash-ref maxcount t 0))))
  (define (dict-set-many dict keys v)
    (for/fold ([dict dict]) ([k (in-list keys)]) (dict-set dict k v)))
  (define t*
    (let loop ([t t] [d 0] [count #hasheq()])
      (match t
        [(? integer?) (void)]
        [(? symbol?)
         (unless (member t prims)
           (define deb (dict-ref count t))
           (update! t (- d deb)))]
        [`(λ (,xs ...) ,e) (loop e (add1 d) (dict-set-many count xs (add1 d)))]
        [`(,es ...) (for ([e (in-list es)]) (loop e d count))])))
  (for/hasheq ([(k v) (in-dict maxcount)])
    (values k (zero? v))))

(define (fv t)
  (define frees (make-hasheq))
  (let loop ([e t] [bound (list->set prims)])
    (match e
      [(? integer?) (void)]
      [(? symbol?)
       (unless (set-member? bound e)
         (hash-set! frees e #t))]
      [`(λ (,xs ...) ,e) (loop e (set-union bound (list->set xs)))]
      [`(,es ...) (for ([e (in-list es)]) (loop e bound))]))
  (hash-keys frees))

(define (δ primop cs)
  (case primop
    [(+) (apply + cs)]
    [(-) (apply - cs)]
    [(*) (apply * cs)]
    [(zero?) (zero? (first cs))]
    [(=) (= (first cs) (second cs))]))

(define (arity-check primop n)
  (case primop
    [(+ - *) #t]
    [(zero? =) (= n 2)]
    [(sub1) (= n 1)]))

(define (env-mutate ρ* ρ)
  (for/fold ([ret ρ*]) ([xv (in-list ρ)])
    (dict-set ret (car xv) (cdr xv))))

(define (find-first-in-cont κ x)
  (match κ
    [`(return ,ρ ,κ) (first (dict-ref ρ x))]
    [`(,fncall ,es ,vs ,κ) (find-first-in-cont κ x)]
    [`(exit ,ρ) (first (dict-ref ρ x))]
    [`(exit-tc ,vs ,κ) (find-first-in-cont κ x)]))

;; metafunctions common to all languages:
(define (κ-update kind κ ρ)
  (case kind
    [(push) `(return ,ρ ,κ)]
    [(goto) (mutate-top-return κ ρ)]))

(define (mutate-top-return κ ρ)
  (match κ
    [`(push ,es ,vs ,κ) `(push ,es ,vs ,(mutate-top-return κ ρ))]
    [`(goto ,es ,vs ,κ) `(push ,es ,vs ,(mutate-top-return κ ρ))]
    [`(return ,ρ* ,κ) `(return ,(env-mutate ρ* ρ) ,κ)]
    [`(select ,d1 ,d2 ,κ) `(select ,d1 ,d2 ,(mutate-top-return κ ρ))]
    [`(exit ,ρ*) `(exit ,(env-mutate ρ* ρ))]
    [`(exit-tc ,vs ,κ) `(exit-tc ,vs ,(mutate-top-return κ ρ))]
    [_ κ]))

(define (color ς ρ) (color-aux ς ρ '() '()))
(define (color-aux ς ρ* σ ρ)
  (match ρ*
    ['() `(,σ ,ρ)]
    [`((,x ,v) . ,ρ*)
     (cond [(in-stack? x) (color-aux ς ρ* σ (dict-set ρ x (list v)))]
           [(abstract?)
            (color-aux ς ρ* (dict-set σ x (list v)) ρ)]
           [else
            (define ℓ ((alloc) ς σ)) ;; parameterized allocation
            (color-aux ς ρ* (dict-set σ ℓ (list v)) (dict-set ρ x (list ℓ)))])]))

;; utils
(define (set-grab S)
  (define elm (for/first ([(k v) (in-dict S)]) k))
  (hash-remove! S elm)
  elm)

(define (max-nat-keys dict)
  (for/fold ([kmax 0]) ([(k v) (in-dict dict)])
    (max kmax k)))
(define (list-union lst1 lst2)
  (cond [(empty? lst1) lst2]
        [(member (car lst1) lst2) (list-union (cdr lst1) lst2)]
        [else (cons (car lst1) (list-union (cdr lst1) lst2))]))