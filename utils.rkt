#lang racket

(provide (all-defined-out))

(define (max-nat-keys dict)
  (for/fold ([ret 0]) ([(k v) (in-dict dict)]) (max k ret)))

(define (max-nat-list lst)
  (for/fold ([ret 0]) ([k (in-list lst)]) (max k ret)))

(define (list-update lst n v)
  (define (safe-rest lst) (if (empty? lst) lst (rest lst)))
  (cond [(zero? n) (cons v (safe-rest lst))]
        [(empty? lst) (cons '() (list-update lst (sub1 n) v))]
        [else (cons (first lst) (list-update (rest lst) (sub1 n) v))]))

(define (append-nodups lst1 lst2)
  (cond [(empty? lst1) lst2]
        [(member (first lst1) lst2) (append-nodups (rest lst1) lst2)]
        [else (cons (first lst1) (append-nodups (rest lst1) lst2))]))
(define (nodup-cons v lst)
  (cond [(member v lst) lst]
        [else (cons v lst)]))


(define (set-grab S)
  (define elm (for/first ([(k v) (in-dict S)]) k))
  (hash-remove! S elm)
  elm)

(define (remove/fail pred lst)
  (let/ec return
    (cond [(empty? lst) (return #f)]
          [(pred (car lst)) (cdr lst)]
          [else (cons (car lst) (remove/fail pred (cdr lst)))])))

(define (mapi f . lsts)
  (when (empty? lsts) (error 'mapi "Expect at least one list"))
  (unless (procedure-arity-includes? f (add1 (length lsts)))
    (error 'mapi "Expect at function to have arity as number of given lists + 1"))
  (let loop ([i 0] [lsts lsts])
    (cond [(empty? (first lsts)) '()]
          [else (cons (apply f i (map car lsts))
                      (loop (add1 i) (map cdr lsts)))])))

;; Compute the subset of the reflexive transitive closure of a relation that
;; is rooted at element "start".
;; The relation is expressed a function from domain to P(domain)
(define (↝²→↝²* ↝² start [ret₁ (set)] [ret₂ (set)])
  (let recur ([work (set start)]
              [seen (set start)]
              [ret₁ ret₁]
              [ret₂ ret₂])
    (define (work-union . sets)
      (for/fold ([work work]) ([set (in-list sets)])
        (set-union work (set-subtract set seen))))
    (define e (for/first ([a (in-set work)]) a))
    (cond [e (define-values (r₁ r₂) (↝² e))
             (define work′ (work-union r₁ r₂))
             (define seen′ (set-union seen r₁ r₂))
             (recur (set-remove work′ e) seen′ (set-union r₁ ret₁) (set-union r₂ ret₂))]
          [else (values ret₁ ret₂)])))

(define (map-union f lst)
  (for/fold ([result (set)])
      ([v (in-list lst)])
    (set-union result (f v))))
(define (set-map-union f s)
  (for/fold ([result (set)])
      ([v (in-set s)])
    (set-union result (f v))))

(define (map-union-2values f vs σlocs Ξvars)
  (for/fold ([σlocs σlocs] [Ξvars Ξvars])
      ([v (in-list vs)])
    (f v σlocs Ξvars)))
(define (set-map-union-2values f vs σlocs Ξvars)
  (for/fold ([σlocs σlocs] [Ξvars Ξvars])
      ([v (in-set vs)])
    (f v σlocs Ξvars)))