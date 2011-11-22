#lang racket

(provide translate translate-top)

(define scheme-arity-table
  '((false . 0)
    (true . 0)
    (nat . 1)
    (cons . 2)
    (null . 0)))
(define scheme-constructors (map car scheme-arity-table))
(define (value? v)
  (or (boolean? v)
      (integer? v)
      (eq? v 'null)
      (eq? v 'void)))
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

(define (arity-of t)
  (match t
    [`(λ ,xs ,e) (length xs)]
    [_ #f]))

(struct rec-bnd (fn body))
(struct let-bnd (x e))
(define (translate-top p)
  (define-values (revdefs revexprs)
    (for/fold ([defs '()] [exprs '()])
        ([form (in-list p)])
      (match form
        [`(define (,fn ,args ...) ,body)
         (values (cons (rec-bnd fn `(λ ,args ,body))  defs) exprs)]
        [`(define ,x ,e)
         (values (cons (let-bnd x e) defs) exprs)]
        [expr (values defs (cons expr exprs))])))
  (translate
   (for/fold ([form `(list ,@(reverse revexprs))])
       ([bnd (in-list revdefs)])
     (match bnd
       [(rec-bnd fn body)
        `(letrec* ([,fn ,body]) ,form)]
       [(let-bnd x e)
        `(let ([,x ,e]) ,form)]))))

(define (translate t)
  (match t
    [`(λ (,xs ...) ,expr) `(λ ,xs ,(translate expr))]
    [`(lambda (,xs ...) ,expr) `(λ ,xs ,(translate expr))]
    [`qwote (error 'translate-qwote)]
    [(? symbol? x) x]
    [(? null?) `(qwote null)]
    [(? void?) `(qwote void)]
    [(? value? v) `(qwote ,v)]
    [`(let ((,xs ,es) ...) ,body)
     `((λ ,xs ,(translate body)) ,@(map translate es))]
    [`(let* ((,xs ,es) ...) ,body)
     (translate (for/fold ([term body])
                    ([x (in-list (reverse xs))]
                     [e (in-list (reverse es))])
                  `(let ([,x ,e]) ,term)))]
    [`(letrec* ((,xs ,es) ...) ,body)
     (translate (for/fold ([term body])
                    ([x (in-list (reverse xs))]
                     [e (in-list (reverse es))])
                  `(let ([,x (,(y-combinator (arity-of e)) (λ (,x) ,e))]) ,term)))]
    [`(let ,name ((,xs ,es) ...) ,body)
     (translate `((fixpoint ,(length xs) (λ (,name) (λ ,xs ,body)))
                  ,@es))]
    [`(list) `(qwote null)]
    [`(list ,e ,es ...)
     `(cons ,(translate e) ,(translate `(list . ,es)))]
    [`(fixpoint ,n ,e) `(,(y-combinator n) ,(translate e))]
    [`(cadr ,e) `(car (cdr ,(translate e)))]
    [`(caddr ,e) `(car (cdr (cdr ,(translate e))))]
    [`(cadddr ,e) `(car (cdr (cdr (cdr ,(translate e)))))]
    [`(cdar ,e) `(cdr (car ,(translate e)))]
    ;; some macros
    [`(or) `(qwote #f)]
    [`(or ,e ,es ...)
     (define x (gensym))
     (translate `(let ((,x ,e)) (if ,x ,x (or . ,es))))]
    [`(and) `(qwote #t)]
    [`(and ,e ,es ...) (translate `(if ,e (and . ,es) #f))]
    [`(cond) `(qwote void)]
    [`(cond [else ,rhs]) (translate rhs)]
    [`(cond [,lhs ,rhs] ,rest ...)
     (translate `(if ,lhs ,rhs (cond . ,rest)))]
    [`(quote ,c) (translate c)]
    ;; application
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