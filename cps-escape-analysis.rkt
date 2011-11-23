#lang racket

(provide escape-analysis! strip-annotation
         (struct-out call-label-info)
         (struct-out alloc-depth)
         get-depth get-color recolor!
         stack-ref heap-ref exn-ref)

;; The different colors for references.
(struct *stack-ref ()) (define stack-ref (*stack-ref))
(struct *heap-ref ()) (define heap-ref (*heap-ref))
(struct *exn-ref ()) (define exn-ref (*exn-ref))
(struct alloc-depth ([color #:mutable] depth))
(struct call-label-info (refnonheap ulam-depth) #:transparent)

(define (value? c) (or (boolean? c) (integer? c) (eq? c 'null) (eq? c 'void)))
(define (freshen xs ρ original-name-ht)
  (for/fold ([xs* '()] [ρ ρ]) ([x (in-list xs)])
    (define y (gensym x))
    (when original-name-ht
      (dict-set! original-name-ht y x))
    (values (cons y xs*) (dict-set ρ x y))))

;; change the color entry for a variable, but not the nesting depth.
(define (update-color! color-ht var color)
  (define alloc (hash-ref color-ht var #f))
  (when alloc (set-alloc-depth-color! alloc color)))

(define (get-depth color-ht var)
  (define alloc (hash-ref color-ht var #f))
  (and alloc (alloc-depth-depth alloc)))
(define (get-color color-ht var)
  (define alloc (hash-ref color-ht var #f))
  (cond [alloc (alloc-depth-color alloc)]
        [else stack-ref]))

(define (recolor! color-ht label-ht escaping)
  (define change? (box #f))
  (define (escape-color var col)
    (define var-heap? (hash-has-key? escaping var))
    (cond [var-heap? heap-ref] ;; we know col must be heap
          [(eq? col heap-ref)
           (printf "~a was a heap variable. Proved safe to stack allocate.~%" var)
           (set-box! change? #t)
           exn-ref]
          [else col]))
  (define (non-heap?->color b)
    (cond [b stack-ref]
          [else heap-ref]))
  ;; Turn heap colors that don't escape into exn colors. (Others stay the same).
  (hash-for-each color-ht
                 (λ (var AD)
                    (set-alloc-depth-color! AD (escape-color var (alloc-depth-color AD)))))
  ;; Turn heap refs to exn colored vars into exn refs.
  (hash-for-each label-ht
                 (λ (label alloc-depth+CLI)
                    (when (call-label-info? alloc-depth+CLI)
                      (define refnonheap (call-label-info-refnonheap alloc-depth+CLI))
                      (hash-for-each
                       refnonheap
                       (λ (var non-heap?)
                          (hash-set! refnonheap var
                                     (not (eq? heap-ref
                                               (escape-color var (non-heap?->color non-heap?))))))))))
  ;; report any color promotions.
  (unbox change?))

;; freshen binders, label lambdas with their static nesting depth, and label
;; references with the static nesting depth of their binding lambda along with
;; the syntactic escaping criterion for whether it counts as a non-escaping reference
(define (α-convert-annotate e color-ht label-ht original-name-ht)
  (define label (box 1))
  (define LV (make-hasheq))
  (define (next-label!) (begin0 (unbox label) (set-box! label (add1 (unbox label)))))
  (let loop ([e e]
             [depth 0]
             [ρ #hasheq()]
             [ulam-depth 0]
             [label-of-discourse 0])
    (define (conv e) (loop e depth ρ ulam-depth label-of-discourse))
    (define (initial-alloc! xs v)
      (for ([x (in-list xs)])
        (hash-set! color-ht x (alloc-depth stack-ref v))))
    (define (populate-label! label kind args)
      (define (var->no-esc?)
        (define refnonheap (make-hasheq))
        (for ([exp (in-list args)]
              #:when (symbol? exp))
          (define exp-depth (get-depth color-ht exp))
          (define no-esc? (or (not exp-depth) (= exp-depth ulam-depth)))
          (unless no-esc? (update-color! color-ht exp heap-ref))
          (hash-set! refnonheap exp no-esc?))
        (values refnonheap ulam-depth))
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
       (initial-alloc! xs* depth)
       (define call (loop e (add1 depth) ρ* depth ℓ))
       (populate-label! ℓ 'λ call)
       `(λ ,ℓ ,(reverse xs*) ,call)]
      [`(κ ,xs ,e) ;; continuation lambda
       (define-values (xs* ρ*) (freshen xs ρ original-name-ht))
       (define γ (next-label!))
       (initial-alloc! xs* ulam-depth)
       (define call (loop e depth ρ* ulam-depth γ))
       (populate-label! γ 'κ call)
       `(κ ,γ ,(reverse xs*) ,call)]
      [`(,(and (or 'user-exp 'cont-call) tag) ,call) ;; expr wrapper
       (define ψ (next-label!))
       `(,tag ,ψ ,(loop call depth ρ ulam-depth ψ))]
      [`(if ,u ,e₁ ,e₂) ;; user if
       (define u* (dict-ref ρ u u))
       (populate-label! label-of-discourse 'call (list u*))
       `(if ,u* ,(conv e₁) ,(conv e₂))]
      [`(,es ...) ;; user/continuation call
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