#!r6rs
;; Copyright 2013 Derick Eddington.  My MIT-style license is in the file named
;; LICENSE from the original collection this file is distributed with.

(library (logji zbepi)
  (export
    term? make-term term-expr term-env
    applicative? make-applicative applicative-underlying
    procedure->applicative
    bind env-binding make-binding binding-ident binding-val
    term-equal?
    eval
    standard-env primitive-env empty-env)
  (import
    (rnrs base)
    (rnrs control)
    (rnrs lists)
    (rnrs records syntactic))


  (define-record-type environment
    (fields bindings)
    ; This exists to prevent printing the giant contents of environments.
    (opaque #T))


  (define-record-type term
    (fields expr env)
  #;(protocol
     (lambda (m)
       (lambda (expr env)
         (unless (pair? expr) (error 'make-term "not a pair" expr))
         (m expr env)))))


  (define-record-type operative
    (fields params dyn-env-param body static-env)
    (protocol
     (lambda (m)
       (lambda (params dyn-env-param body static-env)
         (define (err msg . irrts)
           (apply error 'operative msg irrts))
         (define (dup p)
           (err "duplicate parameter" p))
         (define (map/check p c)
           (cond ((or (term? p)
                      (and (pair? p) (pair? (cdr p)) (null? (cddr p))
                           (eqv? $quote
                                 (if (symbol? (car p))
                                   (let ((b (env-binding static-env (car p))))
                                     (and b (binding-val b)))
                                   (car p)))))
                  (let ((t (if (term? p) p (make-term (cadr p) static-env))))
                    (when (memp (lambda (x) (and (term? x) (term-equal? t x)))
                                c)
                      (dup p))
                    (values t (cons t c))))
                 ((pair? p)
                  (let*-values (((a c) (map/check (car p) c))
                                ((d c) (map/check (cdr p) c)))
                    (values (cons a d) c)))
                 ((symbol? p)
                  (when (memq p c) (dup p))
                  (values p (cons p c)))
                 ((or (null? p) (not p))
                  (values p c))
                 (else (err "malformed parameter tree" params))))
         (let-values (((params _)
                       (map/check params (if (symbol? dyn-env-param)
                                           (list dyn-env-param)
                                           '()))))
           (m params dyn-env-param body static-env))))))


  (define-record-type applicative
    (fields underlying)
    (protocol
     (lambda (m)
       (lambda (u)
         (assert (combiner? u))
         (m u)))))


  (define-record-type scheme-escape
    (fields proc))


  (define (combiner? x)
    (or (operative? x)
        (applicative? x)
        (scheme-escape? x)))



  (define (eval expr env)

    (define (err msg . irrts) (apply error 'eval msg irrts))

    (cond
      ((pair? expr)
       (cond
         ((env-binding env (make-term expr env)) => binding-val)
         (else
          (let ((combiner (eval (car expr) env))
                (operands (cdr expr)))
            (cond
              ((operative? combiner)
               (let ((params        (operative-params        combiner))
                     (dyn-env-param (operative-dyn-env-param combiner))
                     (body          (operative-body          combiner))
                     (static-env    (operative-static-env    combiner)))
                 (define (incorrect)
                   (err "incorrect operand tree shape" operands params))
                 (eval body
                       (let match ((p params)
                                   (o operands)
                                   (e (if (symbol? dyn-env-param)
                                        (bind static-env dyn-env-param env)
                                        static-env)))
                         (cond ((pair? p)
                                (if (pair? o)
                                  (match (cdr p) (cdr o)
                                         (match (car p) (car o) e))
                                  (incorrect)))
                               ((or (symbol? p)
                                    (term? p))
                                (bind e p o))
                               ((null? p)
                                (if (null? o) e (incorrect)))
                               ((not p)
                                e))))))

              ((applicative? combiner)
               (unless (list? operands)
                 (err "operand tree must be a list" operands))
               (eval (cons (applicative-underlying combiner)
                           (map (lambda (o) (eval o env)) operands))
                     env))

              ((scheme-escape? combiner)
               ((scheme-escape-proc combiner) operands env))

              (else (err "not a combiner" combiner)))))))

      ((symbol? expr)
       (cond ((env-binding env expr) => binding-val)
             (else (err "unbound" expr))))

      (else expr)))



  (define make-binding cons)
  (define binding-ident car)
  (define binding-val cdr)

  (define (bind env sym-or-term val)
    (make-environment
     (cons (make-binding sym-or-term val)
           (environment-bindings env))))

  (define (env-binding env sym-or-term)
    (assp (if (symbol? sym-or-term)
            (lambda (a) (eq? a sym-or-term))
            (lambda (a) (and (term? a) (term-equal? a sym-or-term))))
          (environment-bindings env)))



  (define (term-equal? a b)
    (let ((env-a (term-env a))
          (env-b (term-env b)))

      (define (compare a b bound-eqv unbound)
        (define (binding x e)
          (cond ((pair? x) (env-binding e (make-term x e)))
                ((symbol? x) (env-binding e x))
                (else (make-binding #F x))))
        (let ((ba (binding a env-a))
              (bb (binding b env-b)))
          (if (and ba bb)
            (let ((va (binding-val ba))
                  (vb (binding-val bb)))
              (and (eqv? va vb)
                   (bound-eqv va)))
            (and (not ba) (not bb)
                 (unbound a b)))))

      (let recur ((ea (term-expr a))
                  (eb (term-expr b)))

        (define (operative-operands-equal?)
          (let recur ((oa (cdr ea)) (ob (cdr eb)))
            (cond ((and (pair? oa) (pair? ob))
                   (and (recur (car oa) (car ob))
                        (recur (cdr oa) (cdr ob))))
                  ((and (symbol? oa) (symbol? ob))
                   (and (eq? oa ob)
                        (eq? (env-binding env-a oa)
                             (env-binding env-b ob))))
                  (else (equal? oa ob)))))

        (define (applicative-operands-equal?)
          (let ((oa (cdr ea)) (ob (cdr eb)))
            (and (list? oa) (list? ob)
                 (= (length oa) (length ob))
                 (for-all (lambda (x y)
                            (compare x y
                              (lambda (_) #T)
                              (lambda (x y)
                                (if (and (symbol? x) (symbol? y))
                                  (eq? x y)
                                  (recur x y)))))
                          oa ob))))

        (cond ((and (pair? ea) (pair? eb))
               (compare (car ea) (car eb)
                 (lambda (va)
                   (if (applicative? va)
                     (applicative-operands-equal?)
                     (operative-operands-equal?)))
                 (lambda (aea aeb)
                   (and (if (and (symbol? aea) (symbol? aeb))
                          (eq? aea aeb)
                          (recur aea aeb))
                        (operative-operands-equal?)))))

              ((and (symbol? ea) (symbol? eb))
               (compare ea eb
                 (lambda (_) #T)
                 eq?))

              (else (equal? ea eb))))))



  (define (procedure->applicative proc)
    (make-applicative
     (make-scheme-escape
      (lambda (args _) (apply proc args)))))


  (define empty-env (make-environment '()))

  (define primitive-env
    (fold-left
     (lambda (e x) (bind e (car x) (eval (cdr x) e)))
     empty-env
     `(($vau . ,(make-operative '(params dyn-env-param body)
                                'static-env
                                (cons (procedure->applicative make-operative)
                                      '(params dyn-env-param body static-env))
                                empty-env))

       ($if . ($vau (test consq altn) dyn-env
                (,(procedure->applicative
                   (lambda (t c a de)
                     (case (eval t de)
                       ((#T) (eval c de))
                       ((#F) (eval a de))
                       (else (error '$if "not boolean")))))
                 test consq altn dyn-env)))

       (empty-environment . ,empty-env)

       (quote . ($vau (expr) env
                  (,(procedure->applicative make-term) expr env)))

       (eval   . ,(procedure->applicative eval))
       (wrap   . ,(procedure->applicative make-applicative))
       (unwrap . ,(procedure->applicative applicative-underlying))
       (cons   . ,(procedure->applicative cons))
       (null?  . ,(procedure->applicative null?))
       )))

  (define standard-env
    (fold-left
     (lambda (e x) (bind e (car x) (eval (cdr x) e)))
     primitive-env
     `((get-current-environment . (wrap ($vau () e e)))

       (list . (wrap ($vau args #F args)))

       ($lambda . ($vau (params body) static-env
                    (wrap (eval (list $vau params #F body) static-env))))

       (car . ($lambda ((a . d)) a))
       (cdr . ($lambda ((a . d)) d))
       (cadr . ($lambda ((a b . r)) b))

       (apply . ($lambda (appv arg . opt)
                  (eval (cons (unwrap appv) arg)
                        ($if (null? opt) empty-environment (car opt)))))

       ($let . ($vau (((pt expr)) body) env
                 (eval (list (list $lambda (list pt) body) expr) env)))

       ; TODO: move here everything that can use basic lambda/let

       #;(recur . (wrap ($vau (comb) #F
                          ($vau opnds env
                            (eval (cons comb (cons comb opnds)) env)))))

       ($letrec . ($vau (((id expr)) body) env
                    ($let ((f (eval (list $lambda (list id) expr)
                                    env)))
                      ($let ((r ($lambda (r)
                                  (f ($vau o e (eval (cons (r r) o) e))))))
                        (eval (list $let (list (list id (r r)))
                                    body)
                              env)))))

       (list* . ($letrec ((aux ($lambda ((a . r))
                                 ($if (null? r) a (cons a (aux r))))))
                  ($lambda args (aux args))))

       #;(map . (recur ($lambda (self func list)
                         ($if (null? list)
                           list
                           (cons (func (car list))
                                 (self self (cdr list)))))))

       (map . ($letrec ((map ($lambda (func list)
                               ($if (null? list)
                                 list
                                 (cons (func (car list))
                                       (map func (cdr list)))))))
                map))

       ($let . ($vau (bindings body) env
                 (eval (cons (list $lambda (map car bindings) body)
                             (map cadr bindings))
                       env)))

       (map . ($letrec ((aux ($lambda (func lists)
                               ($if (null? (car lists))
                                 ()
                                 (cons (apply func (map car lists))
                                       (aux func (map cdr lists)))))))
                ($lambda (func list1 . lists)
                  (aux func (cons list1 lists)))))

       (term?     . ,(procedure->applicative term?))
       (make-term . ,(procedure->applicative make-term))
       (term-expr . ,(procedure->applicative term-expr))
       (term-env  . ,(procedure->applicative term-env))
       (term-equal?  . ,(procedure->applicative term-equal?))

       (env-binding   . ,(procedure->applicative env-binding))
       (binding-ident . ,(procedure->applicative binding-ident))
       (binding-val   . ,(procedure->applicative binding-val))
       (make-binding  . ,(procedure->applicative make-binding))
       )))


  (define $quote (eval 'quote primitive-env))

)
