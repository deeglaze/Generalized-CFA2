#lang racket

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

(define c? (or/c symbol? number? string? void? null? ) ( c)
  (or (symbol? c)))

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
                   `(if ,aexp
                        ,(T-c exprt cont)
                        ,(T-c exprf cont))))]

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
     (T-c expr cont)]))


(define (T-c expr c)
  (match expr
    [ (? aexpr?)  #;=>  `(cont-call ,c ,(M expr))]

#;[`(begin ,expr)      (T-c expr c)]

#;[`(begin ,expr ,exprs ...)
     (T-k expr (λ (_)
                  (T-c `(begin ,@exprs) c)))]

    [`(if ,exprc ,exprt ,exprf)
                                        ; We have to bind the cont to avoid
                                        ; a possible code blow-up:
     (define $k (gensym '$k))
     `(cont-call
       (κ (,$k)
          ,(T-k exprc (λ (aexp)
                         `(if ,aexp
                              ,(T-c exprt $k)
                              ,(T-c exprf $k)))))
       ,c)]

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
                 `((cps ,p) ,@$es ,c)))]

    [`(,f ,es ...)
                                        ; =>
     (T-k f (λ ($f)
               (T*-k es (λ ($es)
                           `(user-call ,$f ,@$es ,c)))))]))


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
         (? c?)
        '(void))
     ; =>
     aexpr]

    [else
     (error "Not an aexpr!")]))


;; Extensions

(define (cps f)
  (λ args
     (match args
       [`(,xs ... ,k)
        (k (apply f xs))])))

#;(define-syntax set-then!
  (syntax-rules ()
    [(_ var exp then)
     (begin
       (set! var exp)
       then)]))


;; Examples

(M '(λ (x) x))

(T-c '(g a) 'halt)

(pretty-write
 (T-c '(letrec ([f (λ (n)
                     (if (= n 0)
                         1
                         (* n (f (- n 1)))))])
         (f 5))
      'halt))

(call/ec (λ (halt)
            (letrec ((f
                      (λ (n $k4)
                         ((λ ($k5)
                             ((cps =)
                              n
                              0
                              (λ ($rv6)
                                 (if $rv6 ($k5 1) ((cps -) n 1 (λ ($rv8) (f $rv8 (λ ($rv7) ((cps *) n $rv7 $k5)))))))))
                          $k4))))
              (f 5 halt))))