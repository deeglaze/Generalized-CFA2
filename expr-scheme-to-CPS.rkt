#lang racket
(provide cps-conv prims)
; Common non-terminal:
; <c>    ::= #t | #f | null | <number> | <string>

; Input language:

; <aexpr> ::= (λ (<var>*) <expr>)
;          |  <var>
;          |  (qwote <c>)
;          |  (void)
;          |  call/ec | call/cc
;
; <expr> ::= <aexpr>
;         |  (if <expr> <expr> <expr>)
;         |  (<prim> <expr>*)
;         |  (<expr> <expr>*)
; TODO: UNSUPPORTED
;         |  (begin <expr>*)
;         |  (set! <var> <expr>)
;         |  (letrec ([<var> <aexpr>]*) <expr>)

; <prim> = prims (below)

; Output language:

; <aexp> ::= (λ (<var>*) <cexp>)
;         |  <var>
;         |  (qwote <c>)
;         |  (void)

; <cexp> ::= (if <aexp> <cexp> <cexp>)
;         |  ((cps <prim>) <aexp>*)
;         |  (<aexp> <aexp>*)
; TODO: UNSUPPORTED
;         |  (set-then! <var> <aexp> <cexp>)
;         |  (letrec ([<var> <aexp>]*) <cexp>)

(define prims (apply set '( + - / *  = cons car cdr pair? null? number? string? procedure?)))

(define c? (or/c symbol? number? string? void? null? ))

(define (aexpr? expr)
  (match expr
    [(or `(λ (,_ ...) ,_)
         `(qwote ,(? c?))
         '(void)
         (? symbol?))
     ; =>
     #t]

    [else #f]))

(define (prim? term)
  (set-member? prims term))

(define (T-k expr k)
  (match expr
    [ (? aexpr?)  #;=>  (k (M expr))]

#;[`(begin ,expr)
     (T-k expr k)]

#;[`(begin ,expr ,exprs ...)
     (T-k expr (λ (_)
                  (T-k `(begin ,@exprs) k)))]

    [`(if ,exprc ,exprt ,exprf)
                                        ; We have to reify the cont to avoid
                                        ; a possible code blow-up:
     (define $rv (gensym '$rv))
     (define cont `(κ (,$rv) ,(k $rv)))
     (T-k exprc (λ (aexp)
                   `(user-exp (if ,aexp
                        ,(T-c exprt cont)
                        ,(T-c exprf cont)))))]

#;[`(set! ,var ,expr)
     (T-k expr (λ (aexp)
                  `(set-then! ,var ,aexp
                              ,(k '(void)))))]

#;[`(letrec ([,vs ,as] ...) ,expr)
     `(letrec (,@(map list vs (map M as)))
        ,(T-k expr k))]

    [`(,_ ,_ ...)
                                        ; =>
     (define $rv (gensym '$rv))
     (define cont `(κ (,$rv) ,(k $rv)))
     (T-c expr cont)]

    [_ (error 'T-k "match fail ~a" expr)]))


(define (T-c expr c)
  (match expr
    [ (? aexpr?)  #;=>  `(cont-call (,c ,(M expr)))]

#;[`(begin ,expr)      (T-c expr c)]

#;[`(begin ,expr ,exprs ...)
     (T-k expr (λ (_)
                  (T-c `(begin ,@exprs) c)))]

    [`(if ,exprc ,exprt ,exprf)
                                        ; We have to bind the cont to avoid
                                        ; a possible code blow-up:
     (define $k (gensym '$k))
     `(cont-call
       ((κ (,$k)
          ,(T-k exprc (λ (aexp)
                         `(user-exp (if ,aexp
                                        ,(T-c exprt $k)
                                        ,(T-c exprf $k))))))
       ,c))]

#;[`(set! ,var ,expr)
     (T-k expr (λ (aexp)
                  `(set-then! ,var ,aexp
                              `(,c (void)))))]

#;[`(letrec ([,vs ,as] ...) ,expr)
     `(letrec (,@(map list vs (map M as)))
        ,(T-c expr c))]

    [`(,(and p (? prim?)) ,es ...)
                                        ; =>
     (T*-k es (λ ($es)
                 `(user-exp (,p ,@$es ,c))))]

    [`(,f ,es ...)
                                        ; =>
     (T-k f (λ ($f)
               (T*-k es (λ ($es)
                           `(user-exp (,$f ,@$es ,c))))))]
    [_ (error 'T-c "match fail ~a" expr)]))


(define (T*-k exprs k)
  (cond
    [(null? exprs)   (k '())]
    [(pair? exprs)   (T-k (car exprs) (λ (hd)
                                         (T*-k (cdr exprs) (λ (tl)
                                                              (k (cons hd tl))))))]))

(define (M aexpr)
  (match aexpr
    [`(λ (,vars ...) ,body)
      ; =>
      (define $k (gensym '$k))
     `(λ (,@vars ,$k)
        ,(T-c body $k))]

    [(or 'call/ec 'call/cc)
     '(λ (f cc) (f (λ (x _) (cc x)) cc))]

    [(or (? symbol?)
         `(qwote ,(? c?))
        '(void))
     ; =>
     aexpr]

    [else (error 'M "Not an aexpr! ~a" aexpr)]))


;; Extensions

#;(define (cps f)
  (λ args
     (match args
       [`(,xs ... ,k)
        (k (apply f xs))])))

(define (cps-conv t) (T-c t 'halt))

#;(define-syntax set-then!
  (syntax-rules ()
    [(_ var exp then)
     (begin
       (set! var exp)
       then)]))
