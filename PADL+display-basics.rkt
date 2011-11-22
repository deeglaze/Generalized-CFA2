#lang racket

(require redex
         (only-in srfi/13 string-prefix?)
         "def-scheme-to-expr-scheme.rkt"
         "expr-scheme-to-CPS.rkt"
         "cps-escape-analysis.rkt"
         "utils.rkt"
         (for-syntax syntax/id-table))
(provide (all-defined-out))

;; lookup tables for the intermediate representation. Populated by escape analysis.
(define coloring (make-hasheq))
(define label-ht (make-hasheq))
(define (set-coloring! c) (set! coloring c)) ;; allow mutation outside module.
(define (set-label-ht! l) (set! label-ht l))
;; Cosmetic only: save the original binder names before α-conversion for better printing.
(define names (make-hasheq))
(define (set-names! n) (set! names n))
(define (in-stack? x) (not (eq? heap-ref (get-color coloring x))))
(define (in-local? x) (eq? stack-ref (get-color coloring x)))
(define (in-heap? x) (eq? heap-ref (get-color coloring x)))
(define (has-exn-ref? x) (eq? exn-ref (get-color coloring x)))

;; define some identifiers for use as syntactic keywords.
(define-values-for-syntax (stack local heap exn)
  (let ([fail (λ (stx) (raise-syntax-error #f "For use only in case-alloc" stx))])
    (values fail fail fail fail)))
(define-syntax (case-alloc-aux stx)
  (define lut (make-free-id-table (hasheq #'stack #'stack-ref
                                          #'heap #'heap-ref
                                          #'exn #'exn-ref)))
  (syntax-case stx ()
    [(_ id) #'(void)]
    [(_ id [local rhs1 rhs ...] rest ...)
     #'(cond [(not (eq? id heap-ref)) rhs1 rhs ...]
             [else (case-alloc-aux id rest ...)])]
    [(_ id [kind rhs1 rhs ...] rest ...)
     (let ([ref (free-id-table-ref lut #'kind)])
       (unless ref (raise-syntax-error #f "expected one of (stack heap exn local)" stx))
       #`(cond [(eq? id #,ref) rhs1 rhs ...]
               [else (case-alloc-aux id rest ...)]))]))
(define-syntax-rule (case-alloc expr [lhs rhs1 rhs ...] ...)
  (let ([x expr])
    (case-alloc-aux x [stack rhs1 rhs ...] ...)))
(define-syntax-rule (!! expr) (not (not expr)))

(define (ψ-is-kind? label v kind)
  (match-define (call-label-info colors ulam-depth) (hash-ref label-ht label))
  (eq? (hash-ref colors v) kind))
(define (S?ψ label v) (ψ-is-kind? label v stack-ref))
(define (H?ψ label v) (ψ-is-kind? label v heap-ref))
(define (E?ψ label v) (ψ-is-kind? label v exn-ref))
(define (Ξ?ψ label v) (not (ψ-is-kind? label v heap-ref)))

;; This language isn't used - only extended. Provided f
(define-language CPS-Scheme
  [uexp (if u exp exp) ucall]
  [ucall (uaexp uaexp ... caexp)]
  [ccall (caexp uaexp ...)]
  [call ucall ccall]
  [ulam (λ (u ... k) exp)]
  [clam (κ (u ...) exp)]
  [uaexp u ulam const (void) primop alloc-primop]
  [caexp k clam halt]
  [exp uexp ccall]
  [c integer bool null  ;; simplified
     top abs-int abs-bool] ;; abstract values
  [aint (integer) (abs-int)] ;; unions for the simple abstract domain
  [abool (bool) (abs-bool)]
  [bool #t #f]
  [const (qwote c)]
  [alloc-primop cons] ;; separated so we can abstract it to allocate a bounded number of cells.
  [primop + - * / pair? null? < <= = >= > car cdr]
  [prim primop alloc-primop]
  [(u k x) variable-not-otherwise-mentioned])
;; Intermediate representation of the program used during the analysis.
;; We need labels on all sub-expressions to look up static nesting depth,
;; allocation strategy, and reference classification (informs allocation strategy).
(define-extended-language Annotated-CPS-Scheme CPS-Scheme
  [ulam (λ ulab (u ... k) exp)]
  [clam (κ clab (u ...) exp)]
  [lam ulam clam]
  [ccall (cont-call clab (caexp uaexp ...))]
  [uexp (user-exp ulab ucall)
        (user-exp ulab (if u exp exp))]
  [call ucall ccall]
  [(clab ulab lab scope-depth) natural]
  [n natural])

(define (exp-depth exp)
  (match-define (or `(user-exp ,lab ,_) `(cont-call ,lab ,_)) exp)
  (call-label-info-ulam-depth (hash-ref label-ht lab)))

;; Description of our stack/heap machine's states and environment structure.
;; ρ gives the allocation target for each variable.
;; σ has an unspecified domain for whatever allocation strategy we choose.
;; ℓ describes allocation targets, where "Stack" just means use an env lookup in the display.
(define-extended-language DCPS-machine Annotated-CPS-Scheme
  [ς ς-eval ς-entry ς-capply ς-final]
  [ς-eval (exp ρ σ Ξ D)]
  [ς-capply ((Ξ-kont clam ρ) (d ...) σ Ξ D)]
  [ς-colorable ς-capply ς-entry]
  [v prim c (void) (clo ulam ρ) continuation (cons-cell v v)]
  [continuation (σ-kont clam ρ Ξ D) (Ξ-kont clam ρ) halt truncated]
  [tail-continuation k halt]
  [d (v ...)] ;; abstracted via ...
  [ρ ((x ℓ) ...)]
  [σ ((any d) ...)]
  [(D Ξ) (ξ ...)] ;; stacks are lists of stack frames. A display is a bounded, indexed list of stack frames.
  [ξ ((x d) ...)]
  [ℓ Stack (Heap any)]
  ;; give names to certain configurations for understandable metafunctions
  [conf-kont (Ξ-kont clam ρ) halt truncated]
  [ς-call    (side-condition ((user-exp ulab ((name f uaexp) uaexp ... clam))              ρ σ Ξ D)
                             (not (redex-match DCPS-machine prim (term f))))]
  [ς-exit-tc (side-condition ((user-exp ulab ((name f uaexp) uaexp ... tail-continuation)) ρ σ Ξ D)
                             (not (redex-match DCPS-machine prim (term f))))]
  [ς-final (halt (d ...) σ Ξ D)]
  [ς-entry ((clo ulam ρ) (d ...) conf-kont σ Ξ D)]
  [ς-exit-shape ((cont-call (name lab clab) ((name cont tail-continuation) uaexp ...)) ρ σ Ξ D)
                ((user-exp (name lab ulab) (prim uaexp ... (name cont tail-continuation))) ρ σ Ξ D)]
  [ς-exit-ret (side-condition ((cont-call (name lab clab) ((name cont tail-continuation) uaexp ...)) ρ σ Ξ D)
                              (S?ψ (term lab) (term cont)))
              (side-condition ((user-exp (name lab ulab) (prim uaexp ... (name cont tail-continuation))) ρ σ Ξ D)
                              (S?ψ (term lab) (term cont)))]
  [ς-exit-exn (side-condition ((cont-call (name lab clab) ((name cont tail-continuation) uaexp ...)) ρ σ Ξ D)
                              (E?ψ (term lab) (term cont)))
              (side-condition ((user-exp (name lab ulab) (prim uaexp ... (name cont tail-continuation))) ρ σ Ξ D)
                              (E?ψ (term lab) (term cont)))]
  [ς-exit-esc (side-condition ((cont-call (name lab clab) ((name cont tail-continuation) uaexp ...)) ρ σ Ξ D)
                              (H?ψ (term lab) (term cont)))
              (side-condition ((user-exp (name lab ulab) (prim uaexp ... (name cont tail-continuation))) ρ σ Ξ D)
                              (H?ψ (term lab) (term cont)))]
  [ς-inner-ueval ((user-exp ulab (if u exp exp)) ρ σ Ξ D)
                 ((user-exp ulab (prim uaexp ... clam)) ρ σ Ξ D)]
  [ς-inner-ceval ((cont-call clab ((λ clab (u ...)) uaexp)) ρ σ Ξ D)]
  [ς-intermediate ς-inner-ceval ς-inner-ueval ς-capply])

;; Return the free variables of an annotated expression in the form of
;; (Setof (Var × nesting-depth))
(define (Annotated-CPS-Scheme-free-vars e [include-cont-vars? #t])
  (let loop ([e e]
             [fvs (set)]
             [bnd (set)])
    (define (fv-add x)
      (cond [(set-member? bnd x) fvs]
            ;; FIXME: not robust!
            [(and (string-prefix? "$k" (symbol->string x))
                  include-cont-vars?)
             (set-add fvs x)]
            [else (set-add fvs x)]))
    (match e
      [`(,(or 'λ 'κ) ,_ ,rib ,exp) (loop exp fvs (set-union bnd (list->set rib)))]
      [`(,(or 'cont-call 'user-exp) ,_ (if ,u ,exp₁ ,exp₂))
       (loop exp₂ (loop exp₁ (fv-add u) bnd) bnd)]
      [`(,(or 'cont-call 'user-exp) ,_ (,exps ...))
       (for/fold ([fvs′ fvs])
           ([exp (in-list exps)])
         (loop exp fvs′ bnd))]
      [(or (? (λ (e) (redex-match DCPS-machine prim e)))
           (? (λ (e) (redex-match DCPS-machine (qwote c) e)))
           '(void)
           'halt)
       fvs]
      [(? symbol? x) (fv-add x)])))

;; Direct-style -> annotated CPS
(define (prepare e [tr translate])
  (set! coloring (make-hasheq))
  (set! label-ht (make-hasheq))
  (set! names (make-hasheq))
  (define cps-e (cps-conv (tr e)))
  (define cps-e* (escape-analysis! cps-e coloring label-ht #:original-name-ht names))
  ;; pretty print for debugging
  (pretty-print (redex-match DCPS-machine ulam (second (third cps-e*))))
  (pretty-print (redex-match DCPS-machine clam (third (third cps-e*))))
  (pretty-print cps-e) (newline)
  (pretty-print cps-e*) (newline)
  (pretty-write label-ht) (newline)
  (pretty-write coloring)
  cps-e*)
(define (prepared-inject e [d #f])
  (term (,e () () (()) (()))))
;; Inject program into starting machine state.
(define (inject e [tr translate])
  (term (,(prepare e tr) () () (()) (()))))

;; Some macros/pattern-matching-functions for better readability.
(define-syntax-rule (is-state? pattern term)
  (!! (redex-match DCPS-machine pattern term)))

(define (same-kont? k₁ ρ₁ k₂ ρ₂)
  (and (eq? k₁ k₂)
       (equal? (term (env-lookup ,ρ₁ ,k₁))
               (term (env-lookup ,ρ₂ ,k₂)))))
(define (ςentry-over-k? ς kterm ρterm)
  (redex-let DCPS-machine
    ([((clo (λ ulab (u ... k) exp) ρ) (d ..._i) conf-kont σ Ξ D) ς])
    (same-kont? kterm ρterm (term k) (term ρ))))
(define (ς-calls-k? ς kterm ρterm)
  (redex-let DCPS-machine
    ([((cont-call clab (k uaexp ...)) ρ σ Ξ D) ς])
    (same-kont? kterm ρterm (term k) (term ρ))))
(define (σ-of ς)
  ((term-match/single DCPS-machine
     [(exp ρ σ Ξ D) (term σ)]
     [((Ξ-kont clam ρ) (d ...) σ Ξ D) (term σ)]
     [(halt (d ...) σ Ξ D) (term σ)]
     [((clo ulam ρ) (d ...) conf-kont σ Ξ D) (term σ)])
   ς))
(define (D-of ς)
  ((term-match/single DCPS-machine
     [(exp ρ σ Ξ D) (term D)]
     [((Ξ-kont clam ρ) (d ...) σ Ξ D) (term D)]
     [(halt (d ...) σ Ξ D) (term D)]
     [((clo ulam ρ) (d ...) conf-kont σ Ξ D) (term D)])
   ς))
;; Dress up the data manipulation to look more like the math.
(define-syntax-rule (for-callers Callers (ς̃entry ς̃call ς̃callee-entry) body1 body ...)
  (for* ([(ς̃entry caller×callees) (in-hash Callers)]
         [caller×callee (in-set caller×callees)]
         #:when (equal? ς̃callee-entry (second caller×callee)))
    (let ([ς̃call (first caller×callee)])
      body1 body ...)))
(define-syntax-rule (for-summary Summary (ς̃entry ς̃exit) body1 body ...)
  (for ([ς̃exit (in-set (hash-ref Summary ς̃entry (set)))])
    body1 body ...))
(define-syntax for-escaping-entries
  (syntax-rules (over in)
    [(_ EntriesEsc (ςentry over (k in ρ)) body1 body ...)
     (for ([(ςentry _) (in-hash EntriesEsc)]
           #:when (ςentry-over-k? ςentry k ρ))
       body1 body ...)]))
(define-syntax for-escapes
  (syntax-rules (calls in)
    [(_ Escapes (ςexit calls (k in ρ)) body1 body ...)
     (for ([(ςexit _) (in-hash Escapes)]
           #:when (ς-calls-k? ςexit (term k) (term ρ)))
       body1 body ...)]))
(define-syntax for-active-paths
  (syntax-rules (over in starting-with)
    [(_ Callers (ςentry ςcall (ςmatching over (k in ρ))) starting-with ςcallee-entry body1 body ...)
     (let loop ([top-entry #f]
                [top-call #f]
                [ςmatching ςcallee-entry]
                [callee-entry ςcallee-entry])
       (cond [(and top-entry top-call (ςentry-over-k? ςmatching (term k) (term ρ)))
              (let ([ςentry top-entry]
                    [ςcall top-call])
                body1 body ...)]
             [else
              (for-callers Callers (ςentry ςcall callee-entry)
                (printf "~%###Searching callers for ~a entering ~a~% Found entry ~a~%Call site ~a~%~%" (term k) callee-entry ςentry ςcall)
                ;; if we have to crawl backwards more than once, there is a ΞΔ
                ;; such that we can't prevent fake rebinding.
                (loop ςentry ςcall callee-entry ςentry))]))]))
(define-syntax-rule (insert-caller! Callers (ς̃entry ς̃call ς̃callee-entry))
  (hash-set-add! Callers ς̃entry (list ς̃call ς̃callee-entry)))
(define-syntax-rule (add-summary! Summary (ς̃entry ς̃exit))
  (hash-set-add! Summary ς̃entry ς̃exit))
(define-syntax-rule (μ-guard e W body1 body ...)
  (let ([x e])
    (unless (hash-has-key? W e)
      (insert! e W)
      body1 body ...)))

(define (insert! k . hts) (for ([ht (in-list hts)]) (hash-set! ht k #t)))
(define (hash-set-add! ht k v)
  (hash-set! ht k (set-add (hash-ref ht k (set)) v)))
(define (hash-set-union! ht k v)
  (hash-set! ht k (set-union (hash-ref ht k (set)) v)))

;; Primop implementation (unimportant to the CFA approach)
;; concrete δ dispatcher
#;(define-metafunction DCPS-machine ;; primop implementation
  [(δ primop (v) ...) ((δc primop v ...))]
  [(δ alloc-primop (v) ...) ((δc alloc-primop v ...))])
(define-metafunction DCPS-machine ;; primop implementation
  [(δc + integer ...) ,(apply + (term (integer ...)))]
  [(δc - integer ...) ,(apply - (term (integer ...)))]
  [(δc * integer ...) ,(apply * (term (integer ...)))]
  [(δc / integer ...) ,(apply / (term (integer ...)))]
  [(δc < integer_0 integer_1) ,(< (term integer_0) (term integer_1))]
  [(δc <= integer_0 integer_1) ,(<= (term integer_0) (term integer_1))]
  [(δc = integer_0 integer_1) ,(= (term integer_0) (term integer_1))]
  [(δc >= integer_0 integer_1) ,(>= (term integer_0) (term integer_1))]
  [(δc > integer_0 integer_1) ,(> (term integer_0) (term integer_1))]
  [(δc pair? v) ,(!! (redex-match DCPS-machine (cons-cell v_0 v_1) (term v)))]
  [(δc null? v) ,(eq? (term v) 'null)]
  [(δc zero? v) ,(zero? (term v))]
  [(δc boolean? v) ,(boolean? (term v))]
  [(δc procedure? v) ,(!! (or (redex-match DCPS-machine (clo ulam ρ) (term v))
                              (redex-match DCPS-machine conf-kont (term v))))]
  [(δc cons v_0 v_1) (cons-cell v_0 v_1)]
  [(δc car (cons-cell v_0 v_1)) v_0]
  [(δc cdr (cons-cell v_0 v_1)) v_1])

;; abstract δ dispatcher
(define-metafunction DCPS-machine ;; primop implementation
  [(δ prim d ...) ((δa prim d ...))])
(define (abstract-value? v) (not (memv v '(top abs-int abs-bool))))
(define (non-clo-pair? x) (and (pair? x) (not (clo? x))))
(define (clo? x) (match x [`(clo ,lam ,ρ) #t] [_ #f]))

(define-metafunction DCPS-machine
  [(possibly-false? top) #t]
  [(possibly-false? abs-int) #f]
  [(possibly-false? integer) #f]
  [(possibly-false? abs-bool) #t]
  [(possibly-false? #t) #f]
  [(possibly-false? #f) #t]
  [(possibly-false? void) #f]
  [(possibly-false? null) #f]
  [(possibly-false? (cons-cell v_1 v_2)) #f])

(define-metafunction DCPS-machine
  [(possibly-non-false? top) #t]
  [(possibly-non-false? abs-int) #t]
  [(possibly-non-false? integer) #t]
  [(possibly-non-false? abs-bool) #t]
  [(possibly-non-false? #t) #t]
  [(possibly-non-false? #f) #f]
  [(possibly-non-false? void) #t]
  [(possibly-non-false? null) #t]
  [(possibly-non-false? (cons-cell v_1 v_2)) #t])

(define-metafunction DCPS-machine
  [(take-branch d exp_1 exp_2)
   ,(append (cond [(term bool_then?) (term (exp_1))]
                  [else '()])
            (cond [(term bool_else?) (term (exp_2))]
                  [else '()]))
   (where bool_then? (possibly-non-false? d))
   (where bool_else? (possibly-false? d))])

(define-metafunction DCPS-machine ;; abstract primop implementation
  [(δa + aint ...) abs-int]
  [(δa - aint ...) abs-int]
  [(δa * aint ...) abs-int]
  [(δa / aint ...) abs-int]
  [(δa < aint_0 aint_1) ,(cond [(or (abstract-value? (term aint_0))
                                    (abstract-value? (term aint_1)))
                                (term abs-bool)]
                               [else (< (term aint_0) (term aint_1))])]
  [(δa <= aint_0 aint_1) ,(cond [(or (abstract-value? (term aint_0))
                                     (abstract-value? (term aint_1)))
                                 (term abs-bool)]
                                [else (<= (term aint_0) (term aint_1))])]
  [(δa = aint_0 aint_1) ,(cond [(or (abstract-value? (term aint_0))
                                    (abstract-value? (term aint_1)))
                                (term abs-bool)]
                               [else (= (term aint_0) (term aint_1))])]
  [(δa >= aint_0 aint_1) ,(cond [(or (abstract-value? (term aint_0))
                                     (abstract-value? (term aint_1)))
                                 (term abs-bool)]
                                [else (>= (term aint_0) (term aint_1))])]
  [(δa > aint_0 aint_1) ,(cond [(or (abstract-value? (term aint_0))
                                    (abstract-value? (term aint_1)))
                                (term abs-bool)]
                               [else (> (term aint_0) (term aint_1))])]
  [(δa pair? (cons-cell v_0 v_1)) #t]
  [(δa pair? top) abs-bool]
  [(δa pair? v) #f
   (side-condition (and (not (eq? (term v) 'top))
                        (not (redex-match DCPS-machine (cons-cell v_0 v_1) (term v)))))]
  [(δa null? top) abs-bool]
  [(δa null? null) #t]
  [(δa null? v) #f
   (side-condition (not (memv (term v) '(top null))))]
  [(δa zero? 0) #t]
  [(δa zero? abs-int) abs-bool]
  [(δa zero? top) abs-bool]
  [(δa zero? v) #f
   (side-condition (not (memv (term v) '(top abs-int 0))))]
  [(δa boolean? abool) #t]
  [(δa boolean? top) abs-bool]
  [(δa boolean? v) #f
   (side-condition (not (memv (term v) '(top #t #f abs-bool))))]
  [(δa procedure? top) abs-bool]
  [(δa procedure? v) ,(!! (or (redex-match DCPS-machine (clo lam ρ) (term v))
                              (redex-match DCPS-machine continuation (term v))))
   (side-condition (not (eq? (term v) 'top)))]
  [(δa car (cons-cell v_0 v_1)) v_0]
  [(δa car top) top]
  [(δa cdr (cons-cell v_0 v_1)) v_1]
  [(δa cdr top) top])

(define (join-values vs₁ vs₂ loss-box)
  (let loop ([vs₁ vs₁] [vs₂ vs₂])
  (cond [(empty? vs₁) vs₂]
        [(empty? vs₂) vs₁]
        [else (match (join-value/values (first vs₁) vs₂ loss-box)
                [(? non-clo-pair? p) (loop (rest vs₁) (append-nodups p vs₂))]
                [a (loop (rest vs₁) (nodup-cons a vs₂))])])))

;; Join a single value with several values. Return the new value and a Boolean
;; indicating a loss of precision.
(define (join-value/values v vs loss-box)
  (let loop ([v v] [vs vs])
  (cond [(empty? vs) v]
        [else
         (match-define-values (a loss?) (join-value/value v (first vs)))
         (when loss? (set-box! loss-box #t))
         (match a
           [(? non-clo-pair? p) ;; p is a list of closures
            ;; The rest are guaranteed to be closures
            (append p (rest vs))]
           [a (loop a (rest vs))])])))

;; value * value -> value * Boolean.
;; join two values in abstract value lattice. Return new value and a Boolean
;; indicating a loss of precision.
(define (join-value/value v₁ v₂)
  (define (join-base pred abs v)
    (values (match v
              [(or (? (λ (x) (eq? x abs))) (? pred)) abs]
              [else 'top])
            #t))
  (cond [(equal? v₁ v₂) (values v₁ #f)]
        [(or (eq? v₁ 'top) (eq? v₂ 'top)) (values 'top #t)]
        [(or (clo? v₁) (clo? v₂)) (values (list v₁ v₂) #t)]
        [(or (integer? v₁) (eq? v₁ 'abs-int)) (join-base integer? 'abs-int v₂)]
        [(or (integer? v₂) (eq? v₂ 'abs-int)) (join-base integer? 'abs-int v₂)]
        [(or (boolean? v₁) (eq? v₁ 'abs-bool)) (join-base boolean? 'abs-bool v₂)]
        [(or (boolean? v₂) (eq? v₂ 'abs-bool)) (join-base boolean? 'abs-bool v₂)]
        [else (values 'top #t)]))
