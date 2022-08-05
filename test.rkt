#lang racket

(struct const (i) #:transparent)
(struct add (e1 e2) #:transparent)
(struct negate (e) #:transparent)
(struct times (e1 e2) #:transparent)

(define (eval-exp e)
  (cond
    [(const? e) e]
    [(add? e)
     (const (+ (const-i (eval-exp (add-e1 e)))
               (const-i (eval-exp (add-e2 e)))))]
    [(negate? e)
     (const (- (const-i (eval-exp (negate-e e)))))]
    [(times? e)
     (const (* (const-i (eval-exp (times-e1 e)))
               (const-i (eval-exp (times-e2 e)))))]
    [#t (error "eval-exp expected an epxression")]))


(define intnode
  (lambda (tree)
    (cond
      [(null? tree) `()]
      [else (if (and (null? (cadr tree)) (null? (caddr tree)) )
                `()
                (append (cons (car tree) (intnode (cadr tree)) ) (intnode (caddr tree)) ))]
      )
    )
  )

(define (istree t)
  (if(null? t) #t
     (if (null? (first t)) #f
         (if (equal? 3 (length t))
         (and (istree (first (rest t))) (istree (first (rest (rest t)))))
         #f
         )
         )
     ))


(define (check-tree tree)
         (cond
           ([null? tree] #t)
           ([null? (car tree)] #f)
           ([equal? (length tree) 3] (and (check-tree (car (cdr tree)))
                                          (check-tree (car (cdr (cdr tree))))))
           [else #f]
           ))