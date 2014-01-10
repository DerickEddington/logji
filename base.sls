#!r6rs
;; Copyright 2014 Derick Eddington.  My MIT-style license is in the file named
;; LICENSE from the original collection this file is distributed with.

(library (logji base)
  (export
    base-env)
  (import
    (rnrs base)
    (rnrs control)
    (rnrs lists)
    (rnrs records syntactic)
    (logji zbepi))


  (define (unimpl who . irts) (apply error who "unimplemented" irts))

  (define (permute l)
    (cond ((null? l)
           '())
          ((null? (cdr l))
           (map list (car l)))
          (else
           (let ((p (permute (cdr l))))
             (apply append (map (lambda (a)
                                  (map (lambda (r) (cons a r))
                                       p))
                                (car l)))))))

  (define $vau         (eval '$vau         standard-env))
  (define $quote       (eval 'quote        standard-env))
  (define $type        (eval '$type        standard-env))
  (define applicative  (eval 'applicative  standard-env))
  (define type-values  (eval 'type-values  standard-env))
  (define logji=       (eval '=            standard-env))


  (define $calculate
    (let ((calculate
           (lambda (expr : method rest env)
             (define (err m i) (error '$calculate m i))
             (if (eq? ': :)
               (let ((val (eval `(,(applicative-underlying (eval method env))
                                  ,expr ,env)
                                empty-env))
                     (p (if (pair? expr)
                          (make-term expr env)
                          expr)))
                 (if (null? rest)
                   env
                   (eval `((,$vau ,p #F
                             (,$calculate . ,rest))
                           . ,val)
                         env)))
               (err "invalid syntax" :)))))

      (eval `(,$vau (expr : method . rest) env
               (,(procedure->applicative calculate)
                expr : method rest env))
            empty-env)))


  (define law
    (procedure->applicative
     (lambda (law-env)
       (procedure->applicative
        (lambda (expr env)
          (define (err m . i) (apply error 'law m i))
          (unless (pair? expr) (err "expression not compound" expr))
          (cond
            ((lookup law-env (make-term expr env))
             => binding-val)
            (else
             (err "not an instance of" expr law-env))))))))


  (define transparency
    (let ((valid (eval '($let ((o1 (var applicative))
                               (o2 (var applicative)))
                          (eval (cons (list $vau '(= (o1 . _) (o2 . _)) #F
                                            (list get-current-environment))
                                      #T)
                                empty-environment))
                       standard-env)))
      (procedure->applicative
       (lambda (idx method)
         (procedure->applicative
          (lambda (expr env)

            (define (err m . i) (apply error 'transparency m i))

            (unless (lookup valid (make-term expr env))
              (err "invalid" expr))

            (let ((e1 (cadr expr))
                  (e2 (caddr expr)))

              (define (examine)
                (let recur ((l1 e1) (l2 e2) (i 0) (got? #F) (s1 #F) (s2 #F))
                  (cond ((and (null? l1) (null? l2))
                         (if got?
                           (values #T s1 s2)
                           (err "index out of bounds" idx)))
                        ((and (pair? l1) (pair? l2))
                         (cond ((= i idx)
                                (recur (cdr l1) (cdr l2) (+ 1 i)
                                       #T (car l1) (car l2)))
                               ((equal? (car l1) (car l2))
                                (recur (cdr l1) (cdr l2) (+ 1 i)
                                       got? s1 s2))
                               (else (values #F s1 s2))))
                        (else (values #F s1 s2)))))

              (let-values (((same? s1 s2) (examine)))
                (unless same? (err "other sub-expressions not equal" expr))
                (let ((val (eval `(,(applicative-underlying method)
                                   (,logji= ,s1 ,s2) ,env)
                                 empty-env)))
                  (if (boolean? val)
                    val
                    (err "method didn't give boolean" method val)))))))))))


  (define consistency
    (procedure->applicative
     (lambda (enclosing-term)

       (define (err m i) (error 'consistency m i))

       (let* ((e-expr (term-expr enclosing-term))
              (e-env (term-env enclosing-term))
              ; TODO: This was taking too long, seemingly exponential!
              (e-val (binding-val
                      (or (lookup e-env enclosing-term)
                          (err "unknown value for enclosing term" e-expr))))
              (e-optr (car e-expr))
              (e-opnd (cdr e-expr)))

         (define (possib-vals expr)
           (define (binding)
             (cond ((pair? expr) (lookup e-env (make-term expr e-env)))
                   ((symbol? expr) (lookup e-env expr))
                   (else (make-binding #F expr))))
           (let ((b (binding)))
             (if b
               (cons (list (binding-val b))
                     #F)
               (cons (eval `(,type-values (,$type ,expr))
                           e-env)
                     (if (symbol? expr)
                       expr
                       (make-term expr e-env))))))

         (let* ((optr-pv/t (possib-vals e-optr))
                (optr-pv (car optr-pv/t))
                (optr-t  (cdr optr-pv/t)))

           (if (for-all applicative? optr-pv)

             (let* ((opnd-pv/t (map possib-vals e-opnd))
                    (opnd-pv (map car opnd-pv/t))
                    (opnd-t  (map cdr opnd-pv/t))
                    (unbound-terms (cons optr-t opnd-t))
                    (vals-possibs (permute (cons optr-pv opnd-pv)))
                    (e-val-possibs
                     (let ((params (do ((n (length e-expr) (- n 1))
                                        (a '() (cons (string->symbol
                                                      (string-append "p"
                                                        (number->string n)))
                                                     a)))
                                       ((= 0 n) a))))
                       (map (lambda (vp)
                              (let* ((t (eval `((,$vau ,params #F
                                                  (,$quote ,params))
                                                . ,vp)
                                              empty-env))
                                     (b (lookup e-env t)))
                                (if b
                                  (cons (binding-val b) vp)
                                  (err "unknown value for possibility" vp))))
                            vals-possibs)))
                    (same-val-possibs
                     (filter (lambda (x)
                               (eval `((,$vau (e-val v) #F
                                         (,logji= e-val v))
                                       ,e-val
                                       ,(car x))
                                     e-env))
                             e-val-possibs))
                    (new-vals-env
                     (if (= 1 (length same-val-possibs))
                       (fold-left (lambda (e t v)
                                    (if t (bind e t v) e))
                                  empty-env
                                  unbound-terms
                                  (cdar same-val-possibs))
                       empty-env)))

               (procedure->applicative
                (lambda (expr env)
                  (cond ((and (pair? expr)
                              (lookup new-vals-env (make-term expr env)))
                         => binding-val)
                        ((and (symbol? expr)
                              (lookup new-vals-env expr))
                         => binding-val)
                        (else (err "unbound" expr))))))

             (err "not applicative" e-optr)))))))


  ; TODO: (define completion )


  (define base-env
    (eval
     `($let (($calculate ,$calculate)
             (law ,law)
             (transparency ,transparency)
             (consistency ,consistency)
           #;(completion ,completion)
             )
        (get-current-environment))
     standard-env))

)
