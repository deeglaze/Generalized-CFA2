#lang racket

(provide escape-analysis! strip-annotation
         (struct-out call-label-info))

(struct call-label-info (stack-ht depth-ht) #:transparent)

(define (value? c) (or (boolean? c) (integer? c) (eq? c 'null) (eq? c 'void)))
(define (freshen xs ρ original-name-ht)
  (for/fold ([xs* '()] [ρ ρ]) ([x (in-list xs)])
    (define y (gensym x))
    (when original-name-ht
      (dict-set! original-name-ht y x))
    (values (cons y xs*) (dict-set ρ x y))))

;; freshen binders, label lambdas with their static nesting depth, and label
;; references with the static nesting depth of their binding lambda along with
;; the syntactic escaping criterion for whether it counts as a non-escaping reference
(define (α-convert-annotate e color-ht label-ht original-name-ht)
  (define label (box 1))
  (define LV (make-hasheq))
  (define (next-label!) (begin0 (unbox label) (set-box! label (add1 (unbox label)))))
  (let loop ([e e]
             [depth 0]
             [depths #hasheq()]
             [ρ #hasheq()]
             [ulam-depth 0]
             [label-of-discourse 0])
    (define (conv e) (loop e depth depths ρ ulam-depth label-of-discourse))
    (define (set-depths xs v)
      (for/fold ([ret depths]) ([x (in-list xs)]) (hash-set ret x v)))
    (define (populate-label! label kind args)
      (define (var->no-esc?)
        (define depth-ht (make-hasheq))
        (values (for/hasheq ([exp (in-list args)]
                             #:when (symbol? exp))
                  (define exp-depth (dict-ref depths exp #f))
                  (define no-esc? (or (not exp-depth) (= exp-depth ulam-depth)))
                  (unless no-esc? (hash-set! color-ht exp #f))
                  (hash-set! depth-ht exp exp-depth)
                  (values exp no-esc?))
                depth-ht))
      (case kind
        [(λ) (hash-set! label-ht label depth)]
        [(κ) (hash-set! label-ht label ulam-depth)]
        [(call)
         (hash-set! label-ht label (call-with-values var->no-esc? call-label-info))]))
    (match e
      [(? symbol? x) (dict-ref ρ x x)]
      [`(λ ,xs ,e) ;; user lambda
       (define-values (xs* ρ*) (freshen xs ρ original-name-ht))
       (define ℓ (next-label!))
       (define call (loop e (add1 depth) (set-depths xs* depth) ρ* depth ℓ))
       (populate-label! ℓ 'λ call)
       `(λ ,ℓ ,(reverse xs*) ,call)]
      [`(κ ,xs ,e) ;; continuation lambda
       (define-values (xs* ρ*) (freshen xs ρ original-name-ht))
       (define γ (next-label!))
       (define call (loop e depth (set-depths xs* ulam-depth) ρ* ulam-depth γ))
       (populate-label! γ 'κ call)
       `(κ ,γ ,(reverse xs*) ,call)]
      [`(,(and (or 'user-exp 'cont-call) tag) ,call)
       (define ψ (next-label!))
       `(,tag ,ψ ,(loop call depth depths ρ ulam-depth ψ))]
      [`(if ,u ,e₁ ,e₂)
       (define u* (dict-ref ρ u u))
       (populate-label! label-of-discourse 'call (list u*))
       `(if ,u* ,(conv e₁) ,(conv e₂))]
      [`(,es ...)
       (define es* (map conv es))
       (populate-label! label-of-discourse 'call es*)
       es*]
      [_ e])))

;; escape-analysis! : Term Dictionary →! Annotated-Term
;; annotates program text with static binding information and labels
;; all references as stack or heap.
;; !: Populates given dictionary with Variable ↦ Never-has-heap-reference?
(define (escape-analysis! e color-dict label-ht
                          #:original-name-ht [original-name-ht #f])
  (α-convert-annotate e color-dict label-ht original-name-ht))

(define (strip-annotation e [original-name-ht #f])
  (define (name-lookup x)
    (cond [original-name-ht (dict-ref original-name-ht x x)]
          [else x]))
  (let loop ([e e])
    (match e
      [`(qwote ,c) c]
      [`(λ ,scope-depth ,xs ,e) `(λ ,(map name-lookup xs) ,(loop e))]
      [`(κ ,scope-depth ,xs ,e) `(κ ,(map name-lookup xs) ,(loop e))]
      [`(,es ...) (map loop es)]
      [(? symbol? x) (name-lookup x)]
      [_ e])))