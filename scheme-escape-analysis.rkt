#lang racket

(provide escape-analysis!)

(define (value? c) (or (boolean? c) (integer? c) (eq? c 'null) (eq? c 'void)))
(define (freshen xs ρ)
  (for/fold ([xs* '()] [ρ ρ]) ([x (in-list xs)])
    (define y (gensym x))
    (values (cons y xs*) (dict-set ρ x y))))
(define (α-convert-and-annotate e annotate-depth?)
  (define maxcount (make-hasheq))
  (values (α-convert-ρ e 0 #hasheq() #hasheq() maxcount annotate-depth?) maxcount))
;; freshen binders, label lambdas with their static nesting depth, and label
;; references with the static nesting depth of their binding lambda along with
;; the syntactic escaping criterion for whether it counts as a non-escaping reference
(define (α-convert-ρ e depth ρ depths maxcount annotate-depth?)
  (define (update! t new) (hash-set! maxcount t (max new (hash-ref maxcount t 0))))
  (let loop ([e e] [depth depth] [ρ ρ] [depths depths])
    (define (conv e) (loop e depth ρ depths))
    (match e
      [(? symbol? x)
       (cond [(dict-ref depths x #f) =>
              (λ (static-depth)
                 (define new-x (dict-ref ρ x x))
                 (define DeBruijn (- depth static-depth 1))
                 (define suffix (if annotate-depth? (list static-depth) '()))
                 (update! new-x DeBruijn)
                 `(ann-ref ,new-x ,(zero? DeBruijn) ,@suffix))]
             [else e])]
      [`(λ ,xs ,e)
       (define-values (xs* ρ*) (freshen xs ρ))
       (define depths*
         (for/fold ([depths depths]) ([x (in-list xs)])
           (dict-set depths x depth)))
       (define prefix (if annotate-depth? (list depth) '()))
       `(λ ,@prefix ,(reverse xs*) ,(loop e (add1 depth) ρ* depths*))]
      [`(,es ...) (map conv es)]
      [_ e])))

;; escape-analysis! : Term Dictionary →! Annotated-Term
;; annotates program text with static binding information and labels
;; all references as stack or heap.
;; !: Populates given dictionary with Variable ↦ Never-has-heap-reference?
(define (escape-analysis! e color-dict [annotate-depth? #t])
  (define-values (e* maxcount) (α-convert-and-annotate e annotate-depth?))
  (for ([(k count) (in-dict maxcount)])
    (dict-set! color-dict k (zero? count)))
  e*)