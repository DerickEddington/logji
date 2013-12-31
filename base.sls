#!r6rs
;; Copyright 2013 Derick Eddington.  My MIT-style license is in the file named
;; LICENSE from the original collection this file is distributed with.

; TODO: Replace includes? with is? predicate-maker.  It supports more flexible
; type determination: it allows used of primitive type predicates like pair?
; while also allowing all the bound-term (no combination computation) uses like
; (includes? integer number) - ((is? number) integer).  The inspiring use case
; is the ability to bind ((is? applicative) (compound expr)) so that the type of
; (compound expr) can be determined without needing to compute the value of
; (compound expr), but also allowing similar expression to be combine-computed
; if no matching term is bound.  Also, (is? applicative) could be bound to
; applicative?, thus allowing combine-computation application without is?
; needing to be applied and know what to return.  However, I need to analyze
; this more to be sure it can do all the transitive stuff bunch inclusion can -
; I think it should be able to do so if (= ((is? b) a) (includes? a b)).

(library (logji base)
  (export
    logji-base-env)
  (import
    (rnrs base)
    (rnrs control)
    (rnrs lists)
    (rnrs records syntactic)
    (logji zbepi))


  (define (permute l)
    (cond ((null? l) '())
          ((null? (cdr l)) (map list (car l)))
          (else (let ((p (permute (cdr l))))
                  (apply append (map (lambda (a) (map (lambda (r) (cons a r)) p))
                                     (car l)))))))

  (define (binding expr env)
    (cond ((pair? expr) (env-binding env (make-term expr env)))
          ((symbol? expr) (env-binding env expr))
          (else (make-binding #F expr))))

  (define (unimpl who . irts) (apply error who "unimplemented" irts))


  (define $vau (eval '$vau standard-env))
  (define $quote (eval 'quote standard-env))


  (define anything
    (let ()
      (define-record-type anything-type)
      (make-anything-type)))

  (define applicative
    (let ()
      (define-record-type applicative-type)
      (make-applicative-type)))

  (define $type
    ; TODO: I imagine this doing more useful things.
    ; TODO: Should this default to returning anything?  That implies the expr
    ; has a value, which might not be true.
    (eval `(,$vau (expr) env
             (,(procedure->applicative (lambda (expr) (unimpl '$type expr)))
              expr))
          empty-env))

  (define type-values
    (procedure->applicative
     (lambda (bunch) (unimpl 'type-values bunch))))


  (define includes?
    (procedure->applicative
     (lambda (test-bunch super-bunch)
       ; TODO: This could call the bunches:includes? procedure
       ;       that's imported from another library.
       (or (eqv? test-bunch super-bunch)
           (unimpl 'includes? test-bunch super-bunch)))))


  (define instance?
    (let ((instance?
           (lambda (test pattern dyn-env)
             (let ((env-t (term-env test))
                   (env-p (term-env pattern)))
               (and
                 (let recur ((et (term-expr test))
                             (ep (term-expr pattern))
                             (vars '()))
                   (cond
                     ((and (pair? et) (pair? ep))
                      (let ((vars (recur (car et) (car ep) vars)))
                        (and vars (recur (cdr et) (cdr ep) vars))))

                     ((symbol? ep)
                      (let ((bp (env-binding env-p ep)))
                        (if bp
                          (let ((bt (binding et env-t)))
                            (and bt
                                 (eqv? (binding-val bt) (binding-val bp))
                                 vars))
                          (cond ((assq ep vars) => (lambda (a)
                                                     (and (equal? et (cdr a))
                                                          vars)))
                                (else
                                 (let ((tt (eval (list $type et) env-t))
                                       (tp (eval (list $type ep) env-p)))
                                   (and (eval `((,$vau (tt tp) #F
                                                  (,includes? tt tp))
                                                ,tt ,tp)
                                              dyn-env)
                                        (cons (cons ep et) vars))))))))

                     ((not ep) vars)

                     (else (and (equal? et ep) vars))))
                 #T)))))

      (make-applicative
       (eval `(,$vau (test pattern) env
                (,(procedure->applicative instance?) test pattern env))
             empty-env))))


  (define logji= (procedure->applicative (lambda (a b) (unimpl '= a b))))


  (define $calculate
    (let ((calculate
           (lambda (expr : method rest env)
             (define (err m i) (error '$calculate m i))
             (if (eq? ': :)
               (let ((val (eval (list (applicative-underlying (eval method env))
                                      expr env)
                                empty-env))
                     (t (make-term expr env)))
                 (if (null? rest)
                   (make-binding t val)
                   (eval (cons (list $vau t #F
                                     (cons $calculate rest))
                               val)
                         env)))
               (err "invalid syntax" :)))))

      (eval `(,$vau (expr : method . rest) env
               (,(procedure->applicative calculate)
                expr : method rest env))
            empty-env)))


  (define law
    (procedure->applicative
     (lambda (b)
       (procedure->applicative
        (lambda (expr env)
          (if (eval `(,instance? ,(make-term expr env) ,(binding-ident b))
                    empty-env)
            (binding-val b)
            (error 'law "not an instance of" expr (binding-ident b))))))))


  (define transparency
    (let ((pat (eval `($let ((= ,logji=)
                             ('(,$type o1) ,applicative)
                             ('(,$type o2) ,applicative))
                        '(= (o1 . #F) (o2 . #F)))
                     standard-env)))
      (procedure->applicative
       (lambda (idx method)
         (procedure->applicative
          (lambda (expr env)

            (define (err m . i) (apply error 'transparency m i))

            (unless (eval (list instance? (make-term expr env) pat)
                          env)
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
                (let ((val (eval (list (applicative-underlying method)
                                       (list logji= s1 s2) env)
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
              ; This is taking too long, seemingly exponential, but the matching
              ; bound term should be at front of env alist, so wtf?!
              (e-val (binding-val (env-binding e-env enclosing-term)))
              (e-optr (car e-expr))
              (e-opnd (cdr e-expr)))

         (define (possib-vals expr)
           (let ((b (binding expr e-env)))
             (if b
               (cons (list (binding-val b))
                     #F)
               (cons (eval (list type-values (list $type expr))
                           e-env)
                     (make-term expr e-env)))))

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
                              (let* ((t (eval (cons (list $vau params #F
                                                          (list $quote params))
                                                    vp)
                                              empty-env))
                                     (b (env-binding e-env t)))
                                (if b
                                  (cons (binding-val b) vp)
                                  (err "unknown value for possibility" vp))))
                            vals-possibs)))
                    (same-val-possibs
                     (filter (lambda (x) (eqv? e-val (car x)))
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
                  (cond ((env-binding new-vals-env (make-term expr env))
                         => binding-val)
                        (else (err "unbound" expr))))))

             (err "not applicative" e-optr)))))))


  (define logji-base-env
    (eval
     `($let ((anything ,anything)
             (applicative ,applicative)
             ($type ,$type)
             (type-values ,type-values)
             (includes? ,includes?)
             (instance? ,instance?)
             (= ,logji=)
             ($calculate ,$calculate)
             (law ,law)
             (transparency ,transparency)
             (consistency ,consistency)
             #;(completion ,completion)
             )
        (get-current-environment))
     standard-env))

)
