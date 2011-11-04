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

(define (set-grab S)
  (define elm (for/first ([(k v) (in-dict S)]) k))
  (hash-remove! S elm)
  elm)

(define (mapi f . lsts)
  (when (empty? lsts) (error 'mapi "Expect at least one list"))
  (unless (procedure-arity-includes? f (add1 (length lsts)))
    (error 'mapi "Expect at function to have arity as number of given lists + 1"))
  (let loop ([i 0] [lsts lsts])
    (cond [(empty? (first lsts)) '()]
          [else (cons (apply f i (map car lsts))
                      (loop (add1 i) (map cdr lsts)))])))
