;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; len

(define (len l)
  (if (pair? l)
      (+ 1 (len (cdr l)))
      0))

(len '(4 4 4))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; rev-iter

(define (rev x a)
  (if (pair? x)
      (rev (cdr x) (cons (car x) a))
      a))

(rev '(4 2 4) '())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; len-Y

(define (yc f)
  (let ((foo (lambda (x) (f (lambda (y) ((x x) y))))))
    (foo foo)))

(define (ylen repl)
  (lambda (l)
    (if (null? l)
        0
        (+ 1 (repl (cdr l))))))

((yc ylen) '(1 2 3 4 5))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; tree-count

(define (tree-count t)
  (if (pair? t)
      (+ 1 (tree-count (cadr t)) (tree-count (caddr t)))
      1))

(tree-count '(1 (3 2 4) (5 6 7)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ins-sort

(define (insert elm l)
  (if (pair? l)
      (let ((fst (car l)))
        (if (> elm fst)
            (cons fst (insert elm (cdr l)))
            (cons elm l)))
      (list elm)))

(define (isort l)
  (if (pair? l)
      (insert (car l) (isort (cdr l)))
      '()))

(isort '(2 9 1 34 -5 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; DFS

(define (append l1 l2)
  (if (pair? l1)
      (cons (car l1) (append (cdr l1) l2))
      l2))

(define (reverse l)
  (let loop ((l l)
             (a '()))
    (if (pair? l)
        (loop (cdr l) (cons (car l) a))
        a)))

(define (memv elm l)
  (and (pair? l)
       (or (= elm (car l))
           (memv elm (cdr l)))))

(define (get-children node graph)
  (if (pair? graph)
      (if (= node 0)
          (car graph)
          (get-children (- node 1) (cdr graph)))
      #f))

(define (dfs graph)
  (let loop ((workset '(0))
             (visited '()))
    (if (pair? workset)
        (let ((node (car workset)))
          (if (memv node visited)
              (loop (cdr workset) visited)
              (loop (append (get-children node graph) workset)
                    (cons node visited))))
        (reverse visited))))

;; We represent a directed graph as a list of lists.
;; A graph has n nodes numbered from 0 to n - 1.
;; The i-th position in the list is a list representing target nodes of the 
;; i-th node of the graph.
;; So, in the call below, we have a graph with three nodes that form a cycle.

(dfs '((1) (2) (0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; flatten

(define (app x y)
  (if (pair? x)
      (cons (car x) (app (cdr x) y))
      y))

(define (flatten x)
  (cond
   ((pair? x)
    (app (flatten (car x)) (flatten (cdr x))))
   ((null? x) x)
   (else (list x))))

(flatten '((1 2) (((3 4 5)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; sets

(define (set-member s elm)
  (and (pair? s)
       (or (= elm (car s))
           (set-member (cdr s) elm))))

(define (set-put s elm)
  (if (set-member s elm)
      s
      (cons elm s)))

(define (set-subset s1 s2)
  (if (pair? s1)
      (and (pair? s2)
           (set-member s2 (car s1))
           (set-subset (cdr s1) s2))
      #t))

(define (set-equal s1 s2)
  (and (set-subset s1 s2) (set-subset s2 s1)))

(define (set-union s1 s2)
  (if (pair? s1)
      (set-put (set-union (cdr s1) s2) (car s1))
      s2))

(define (set-intersection s1 s2)
  (if (pair? s1)
      (let ((fst (car s1))
            (ans (set-intersection (cdr s1) s2)))
        (if (set-member s2 fst)
            (cons fst ans)
            ans))
      '()))

;; De Morgan's Law
(set-equal (set-intersection
            '(1 2 3)
            (set-union '(1 3) '(4 5 6)))
           (set-union
            (set-intersection '(1 3) '(1 2 3))
            (set-intersection '(4 5 6) '(1 2 3))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; church-nums

(define (plus n1 n2)
  (lambda (f) (lambda (x) ((n1 f) ((n2 f) x)))))

(define (mult n1 n2)
  (lambda (f) (n2 (n1 f))))

(define (pred n)
  (lambda (f)
    (lambda (x)
      (((n (lambda (g) (lambda (h) (h (g f)))))
        (lambda (ignored) x))
       (lambda (id) id)))))

(define (sub n1 n2)
  ((n2 pred) n1))

(define church0 (lambda (f) (lambda (x) x)))

(define church1 (lambda (f) (lambda (x) (f x))))

(define church2 (lambda (f) (lambda (x) (f (f x)))))

(define church3 (lambda (f) (lambda (x) (f (f (f x))))))

(define (church0? n) ((n (lambda (x) #f)) #t))

(define (church=? n1 n2)
  (cond
   ((church0? n1) (church0? n2))
   ((church0? n2) #f)
   (else (church=? (sub n1 church1) (sub n2 church1)))))

;; multiplication distributes over addition
(church=? (mult church2 (plus church1 church3))
          (plus (mult church2 church1) (mult church2 church3)))
