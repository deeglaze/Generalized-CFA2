#lang racket

(require "cps-escape-analysis.rkt"
         "LMCS+display-basics.rkt"
         "LMCS+display.rkt")

(define t '(let* ([app (λ (f e) (f e))]
                  [id (λ (x) x)]
                  [n1 (app id 1)]
                  [n2 (app id 2)])
             (+ n1 n2)))

(define t3 '(let* ([app (λ (f e) (f e))]
                   [id (λ (x) x)]
                   [n1 (app id 1)]
                   [n2 (app id 2)])
              (id (λ (y) (+ y n1 n2)))))

(GCFA2 t3)

#|
 (define t2
  '(user-exp 0
             ((λ 1 (f k1)
                 (user-exp 2
                           ((λ 3 (t k2) (user-exp 4 (t t k2)))
                            (λ 5 (g k3)
                               (user-exp 6
                                         (f
                                          (λ 7 (g2 k3)
                                             (user-exp 8
                                                       (g g (κ 9 (rv1) (user-exp 10 (rv1 g2 k3))))))
                                          k3)))
                            k1)))
              (λ 11 (recur k4)
                 (cont-call 12
                            (k4
                             (λ 13 (x k5)
                                (user-exp 14 (recur (λ 15 (z k6) (user-exp 16 (x z k6))) k5))))))
              (κ 17
                 (rv2)
                 (user-exp 18 (rv2 (λ 19 (y k7) (cont-call 20 (k7 y))) halt))))))

 (set-coloring! (make-hasheq `((k1 . ,(alloc-depth stack-ref 0))
                              (k2 . ,(alloc-depth stack-ref 1))
                              (k3 . ,(alloc-depth stack-ref 2))
                              (k4 . ,(alloc-depth stack-ref 1))
                              (k5 . ,(alloc-depth stack-ref 1))
                              (k6 . ,(alloc-depth stack-ref 2))
                              (k7 . ,(alloc-depth stack-ref 0))
                              (rv1 . ,(alloc-depth stack-ref 2))
                              (rv2 . ,(alloc-depth stack-ref 0))
                              (f . ,(alloc-depth heap-ref 0))
                              (t . ,(alloc-depth stack-ref 1))
                              (g . ,(alloc-depth heap-ref 1))
                              (g2 . ,(alloc-depth stack-ref 2))
                              (x . ,(alloc-depth stack-ref 1)) ;; new!
                              (y . ,(alloc-depth stack-ref 0))
                              (z . ,(alloc-depth stack-ref 2))
                              (recur . ,(alloc-depth heap-ref 0))))) ;; new!

 (set-label-ht! (make-hasheq `((0 . ,(call-label-info #hasheq() 0))
                              (1 . 0) ;;λ
                              (2 . ,(call-label-info #hasheq((k1 . #t)) 0))
                              (3 . 1) ;;λ
                              (4 . ,(call-label-info #hasheq((t . #t) (k2 . #t)) 1))
                              (5 . 1) ;;λ
                              (6 . ,(call-label-info #hasheq((f . #f) (k3 . #t)) 1))
                              (7 . 2) ;;λ
                              (8 . ,(call-label-info #hasheq((g . #f)) 2))
                              (9 . 2) ;;κ
                              (10 . ,(call-label-info #hasheq((rv1 . #t) (g2 . #t) (k3 . #t)) 0))
                              (11 . 0) ;;λ
                              (12 . ,(call-label-info #hasheq((k4 . #t)) 0))
                              (13 . 1) ;;λ
                              (14 . ,(call-label-info #hasheq((recur . #f) (k5 . #t)) 1))
                              (15 . 2) ;;λ
                              (16 . ,(call-label-info #hasheq((x . #t) (z . #t) (k6 . #t)) 2))
                              (17 . 0) ;;κ
                              (18 . ,(call-label-info #hasheq((rv2 . #t) (halt . #t)) 0))
                              (19 . 0) ;;λ
                              (20 . ,(call-label-info #hasheq((k7 . #t) (y . #t)) 0)))))
 (GCFA2 t2 #:inject prepared-inject)
|#

;(define esop (call-with-input-string (format "(~a)" (call-with-input-file "esop.sch" port->string)) read))
;(define I (inject esop translate-top))
;(define ς (first (apply-reduction-relation* R-DCPS-machine I)))

;(initial-font-size 7) ;; for traces output