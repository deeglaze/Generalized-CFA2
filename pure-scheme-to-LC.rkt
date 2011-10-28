#lang racket

(provide translate)

(define scheme-arity-table
  '((false . 0)
    (true . 0)
    (nat . 1)
    (cons . 2)
    (null . 0)))
(define scheme-constructors (map car scheme-arity-table))
(define (value? v)
  (or (boolean? v)
      (exact-nonnegative-integer? v)
      (null? v)))
(define (lgensym lst) (for/list ([s (in-list lst)]) (gensym s)))
(define (lvgensym lst) (apply values (lgensym lst)))
(define (ngensym n [tag 'g])
  (build-list n (λ _ (gensym tag))))
(define (nvgensym n [tag 'g])
  (apply values (ngensym n tag)))
(define-syntax-rule (fresh (x ...) body1 body ...)
  (let-values ([(x ...) (lvgensym '(x ...))])
    body1 body ...))
(define (list-index l x)
  (for/first ([y (in-list l)] [i (in-naturals)] #:when (eq? x y)) i))

(define (scott-encode-constructor c)
  (define arity (ngensym (dict-ref scheme-arity-table c) 'x))
  (define cs (lgensym scheme-constructors))
  `(λ ,arity (λ ,cs
                (,(list-ref cs (list-index scheme-constructors c)) ,@arity))))

(define (scott-encode-scheme-value v)
  (cond [(boolean? v)
         (if v
             `(,(scott-encode-constructor 'true))
             `(,(scott-encode-constructor 'false)))]
        [(null? v) `(,(scott-encode-constructor 'null))]
        [(exact-nonnegative-integer? v) `(,(scott-encode-constructor 'nat)
                                          ,(church-encode-nat v))]
        [else (error 'scott-encode-scheme-value "unknown value ~a" v)]))


(define (church-encode-nat n)
  (fresh (f x)
    `(λ (,f) (λ (,x) ,(iterate-app n f x)))))

(define (iterate-app n rator rand)
  (cond [(zero? n) rand]
        [else (iterate-app (sub1 n) rator `(,rator ,rand))]))

;; takes two Church numerals and produces their addition
(define church-encoded-plus
  (fresh (m n f x)
    `(λ (,m ,n) (λ (,f) (λ (,x) ((,m ,f) ((,n ,f) ,x)))))))
(define church-encoded-mult
  (fresh (m n f x)
    `(λ (,m ,n) (λ (,f) (λ (,x) ((,m (,n ,f)) ,x))))))
(define church-encoded-zero?
  (fresh (n x)
    `(λ (,n) ((,n (λ (,x) ,(scott-encode-scheme-value #f)))
              ,(scott-encode-scheme-value #t)))))
(define church-encoded-pred
  (fresh (n f x g h u₁ u₂)
    `(λ (,n)
        (λ (,f)
           (λ (,x)
              (((,n
                 (λ (,g) (λ (,h) (,h (,g ,f)))))
                (λ (,u₁) ,x))
               (λ (,u₂) ,u₂)))))))

(define (y-combinator n)
  (define xs (ngensym n))
  (fresh (f t g)
    `(λ (,f)
        ((λ (,t) (,t ,t))
         (λ (,g) (,f (λ ,xs ((,g ,g) ,@xs))))))))

;; for constructor c, get argument i.
(define (destruct enc c i)
  ;; c takes arity arguments (given as list of symbols)
  (define arity (ngensym (dict-ref scheme-arity-table c) 'x))
  (define ith `(λ ,arity ,(list-ref arity i))) ;; we want to return the ith bit of data.
  (define (constructors-in-order cs c fail?)
    (cond [(empty? cs)
           (if fail?
               (error 'destruct "Unknown constructor ~a" c)
               '())]
          [else
           (define success? (eq? c (car cs)))
           (cons (cond [success? ith]
                       [else (fresh (x₁ x₂)
                               `(λ ,arity ((λ (,x₁) (,x₁ ,x₁))
                                           (λ (,x₂) (,x₂ ,x₂)))))])
                 (constructors-in-order (cdr cs) c (and fail? (not success?))))]))
  `(,enc ,@(constructors-in-order scheme-constructors c #t)))
(define (get-num enc) (destruct enc 'nat 0))

(define (num-op op . encs)
  (define enc-nums (map get-num encs))
  `(,(scott-encode-constructor 'nat) (,op ,@enc-nums)))

(define (translate t)
  (match t
    [`(λ (,xs ...) ,expr) `(λ ,xs ,(translate expr))]
    [(? symbol? x) x]
    [(? integer? x) x]
    [(? value? v) (scott-encode-scheme-value v)]
    [`(if ,e₀ ,e₁ ,e₂)
     (define then (gensym))
     (translate `(let ((,then (λ () ,(translate e₁))))
                   (,(translate e₀)
                    (λ () ,(translate e₂)) ;; false
                    ;; true nat cons null
                    ,then ,then ,then ,then)))]
    [`(let ((,xs ,es) ...) ,body)
     `((λ ,xs ,(translate body)) ,@(map translate es))]
    [`(let ,name ((,xs ,es) ...) ,body)
     (translate `((fixpoint ,(length xs) (λ (,name) (λ ,xs ,body)))
                  ,@es))]
    ;; one level up so we can compare numbers in the CEK machine
    [`(if-zero ,e₀ ,e₁ ,e₂)
     `(if-zero ,(translate e₀) ,(translate e₁) ,(translate e₂))]
    [`(+ ,e₀ ,e₁) `(+ ,(translate e₀) ,(translate e₁))
     ;(num-op church-encoded-plus (translate e₀) (translate e₁))
     ]
    [`(* ,e₀ ,e₁) `(* ,(translate e₀) ,(translate e₁))
     ;(num-op church-encoded-mult (translate e₀) (translate e₁))
     ]
    [`(sub1 ,e) `(- ,(translate e) 1)
     ;(num-op church-encoded-pred (translate e))
     ]
    [`(cons ,e₀ ,e₁)
     `(,(scott-encode-constructor 'cons) ,(translate e₀) ,(translate e₁))]
    [`(car ,e) (destruct (translate e) 'cons 0)]
    [`(cdr ,e) (destruct (translate e) 'cons 1)]
    [`(zero? ,e) `(,church-encoded-zero? ,(get-num (translate e)))]
    [`(fixpoint ,n ,e) `(,(y-combinator n) ,(translate e))]
    [`(,e ,es ...) `(,(translate e) ,@(map translate es))]
    [_ (error 'translate "match-error ~a" t)]))

(struct fn (clo arity))
(define (eval-lcs t ρ)
  (match t
    [(? (λ (t) (memv t '(+ - * if-zero)))) t]
    [(? symbol?) (dict-ref ρ t t)]
    [(? integer?) t]
    [`(λ (,xs ...) ,body)
     (fn (λ (vs)
            (define ρ* (for/fold ([ρ ρ]) ([x xs] [v vs]) (dict-set ρ x v)))
            (eval-lcs body ρ*))
         (length xs))]
    [`(,e₀ ,es ...)
     (define v₀ (eval-lcs e₀ ρ))
     (define vs (map (λ (e) (eval-lcs e ρ)) es))
     (match v₀
       [(fn clo arity) (clo vs)]
       [_ `(,v₀ ,@vs)])]))
(define (eval-lc t) (eval-lcs t #hasheq()))
(define (reify s)
  (match s
    [(fn clo arity)
     (define xs (build-list arity (λ _ (gensym))))
     `(λ ,xs ,(reify (clo xs)))]
    [`(λ ,xs ,body) s]
    [(? symbol?) s]
    [(? integer?) s]
    [`(,n ,ss ...) `(,(reify n) ,@(map reify ss))]))

;; normalize lambda calculus via evaluation
(define (nbe t) (reify (eval-lc t)))

(define (α-equal? t₁ t₂)
  (let loop ([t₁ t₁]
             [t₂ t₂]
             [ρ #hasheq()])
    (define (αeq? t₁ t₂) (loop t₁ t₂ ρ))
    (match* (t₁ t₂)
      [((? symbol?) (? symbol?)) (eq? t₁ (dict-ref ρ t₂ gensym))]
      [((? integer?) (? integer?)) (= t₁ t₂)]
      [(`(λ ,xs₁ ,body₁) `(λ ,xs₂ ,body₂))
       (cond [(= (length xs₁) (length xs₂))
              (define ρ* (for/fold ([ρ ρ]) ([x₁ xs₁] [x₂ xs₂]) (dict-set ρ x₂ x₁)))
              (loop body₁ body₂ ρ*)]
             [else #f])]
      [(`(,ts₁ ...) `(,ts₂ ...))
       (and (= (length ts₁) (length ts₂))
            (andmap αeq? ts₁ ts₂))]
      [(_ _) #f])))

;(α-equal? (nbe (scott-encode-scheme-value 5)) (nbe (translate '(+ 2 3))))
;(α-equal? (nbe (scott-encode-scheme-value #t)) (nbe (translate '(zero? (sub1 (sub1 (sub1 (+ 1 2))))))))