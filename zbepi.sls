#!r6rs
(library (logji zbepi)
  (export
    term? make-term term-expr term-env
    applicative? make-applicative applicative-underlying
    procedure->applicative
    bind lookup make-binding binding-ident binding-val
    eval
    standard-env primitive-env empty-env)
  (import
    (rnrs base)
    (rnrs control)
    (rnrs lists)
    (rnrs records syntactic))


  (define (rappend rl l) (fold-left (lambda (a x) (cons x a)) l rl))

  (define (unimpl who . irts) (apply error who "unimplemented" irts))


  (define-record-type environment
    (fields symbol-bindings term-bindings)
    ; This exists to prevent printing the giant contents of environments.
    (opaque #T))

  (define-record-type binding (fields ident val))

  (define-record-type term
    (fields expr env)
    (protocol
     (lambda (m)
       (lambda (expr env)
         (unless (pair? expr) (error 'make-term "not a pair" expr))
         (m expr env)))))

  (define-record-type value (fields val)) ; private
  (define-record-type variable (fields type))
  (define-record-type ignore)

  (define empty-env (make-environment '() '()))


  (define (bind env sym-or-term val)

    (define (sym-bind sb sym val)
      (cons (make-binding sym val) sb))

    (define (term-bind tb term val)
      (let ((t-env (term-env term)))

        (define (patternify o)
          (cond
            ((pair? o)
             (cons (patternify (car o))
                   (patternify (cdr o))))
            ((and (symbol? o)
                  (lookup t-env o))
             => (lambda (b)
                  (let ((v (binding-val b)))
                    (if (or (variable? v)
                            (ignore? v))
                      v
                      (make-value v)))))
            (else ; o is literal or unbound symbol or null
             o)))

        (cons (make-binding (patternify (term-expr term))
                            val)
              tb)))

    (if (symbol? sym-or-term)
      (make-environment
       (sym-bind (environment-symbol-bindings env) sym-or-term val)
       (environment-term-bindings env))
      (make-environment
       (environment-symbol-bindings env)
       (term-bind (environment-term-bindings env) sym-or-term val))))


  (define-record-type cached (fields obj tried? val? val type? type)) ; private


  (define (lookup env sym-or-term)

    (define (sym-ref sb sym)
      (find (lambda (b) (eq? sym (binding-ident b)))
            sb))

    (define (term-ref tb term)
      (let ((t-expr (term-expr term))
            (t-env (term-env term)))

        (define (match p x cached vars)

          (define (cached-fields c)
            (values (cached-obj    c)
                    (cached-tried? c)
                    (cached-val?   c)
                    (cached-val    c)
                    (cached-type?  c)
                    (cached-type   c)))

          (let-values (((xc tried? val? val type? type)
                        (if (cached? cached)
                          (cached-fields cached)
                          (values x #F #F #F #F #F))))

            (define (yes) (values #T cached vars))
            (define (no) (values #F cached vars))
            (define (yes* cached* vars*) (values #T cached* vars*))
            (define (no* cached* vars*) (values #F cached* vars*))

            (define (cache tried? val? val type? type)
              (make-cached xc tried? val? val type? type))

            (define (do-val tproc bproc eproc)
              (cond (tried?
                     (if (tproc) (yes) (no)))
                    ((lookup t-env (if (pair? x) (make-term x t-env) x))
                     => (lambda (b)
                          (let ((v (binding-val b)))
                            (let ((c* (cache #T #T v type? type)))
                              (if (bproc v)
                                (yes* c* vars)
                                (no* c* vars))))))
                    (else
                     (let ((c* (cache #T #F #F type? type)))
                       (eproc c* vars)))))

            (cond
              ((pair? p)
               (if (pair? x)
                 (let ()
                   (define (cached-part f)
                     (and (cached? cached)
                          (let ((o (f xc)))
                            (and (cached? o)
                                 o))))
                   (define (update-cached ca* cd*)
                     (if (or (cached? ca*) (cached? cd*))
                       (make-cached (cons (if (cached? ca*) ca* (car xc))
                                          (if (cached? cd*) cd* (cdr xc)))
                                    tried? val? val type? type)
                       cached))
                   (let-values (((? ca* vars*) (match (car p)
                                                      (car x)
                                                      (cached-part car)
                                                      vars)))
                     (if ?
                       (let-values (((? cd* vars*) (match (cdr p)
                                                          (cdr x)
                                                          (cached-part cdr)
                                                          vars*)))
                         (if ?
                           (yes* (update-cached ca* cd*) vars*)
                           (no*  (update-cached ca* cd*) vars)))
                       (no* (update-cached ca* #F) vars))))
                 (no)))

              ((value? p)
               (cond ((or (pair? x) (symbol? x))
                      (do-val (lambda () (and val? (equal? (value-val p) val)))
                              (lambda (bv) (equal? (value-val p) bv))
                              no*))
                     ((equal? (value-val p) x)
                      (yes))
                     (else
                      (no))))

              ((variable? p)
               (cond
                 ((assq p vars) => (lambda (a)
                                     (if (equal? x (cdr a))
                                       (yes)
                                       (no))))

                 ((and (symbol? x)
                       (not tried?))
                  (let-values (((? c* _)
                                (do-val (lambda () (assert #F))
                                        (lambda (bv) #T)
                                        no*)))
                    (if ?
                      (match p x c* vars)
                      (no* c* vars))))

                 ((or (not (symbol? x))
                      val?)
                  (let ((pty (variable-type p)))
                    (define (check xty)
                      (eval `((,$vau (pty xty) #F
                                (,is? pty xty))
                              ,pty ,xty)
                            t-env))
                    (define (check* xty)
                      (if (check xty)
                        (yes-v)
                        (no)))
                    (define (yes-c-v c*)
                      (yes* c* (cons (cons p x) vars)))
                    (define (yes-v)
                      (yes-c-v cached))
                    (cond
                      (type?
                       (check* type))
                      ((and (symbol? x)
                            (variable? val))
                       (check* (variable-type val)))
                      ((variable? x)
                       (check* (variable-type x)))
                      ((and val?
                            (check val))
                       (yes-v))
                      (else
                       (let* ((xty (eval `(,$type ,x) t-env))
                              (c* (cache tried? val? val #T xty)))
                         (if (check xty)
                           (yes-c-v c*)
                           (no* c* vars)))))))

                 (else ; x is unbound symbol
                  (no))))

              ((ignore? p)
               (yes))

              (else ; p is literal or unbound symbol or null
               (if (equal? p x)
                 (if (symbol? p)
                   (do-val (lambda () (not val?))
                           (lambda (bv) #F)
                           yes*)
                   (yes))
                 (no))))))

        (let next ((tb tb)
                   (cached #F))
          (and (pair? tb)
               (let-values (((? cached* _)
                             (match (binding-ident (car tb))
                                    t-expr
                                    cached
                                    '())))
                 (if ?
                   (car tb)
                   (next (cdr tb) cached*)))))))

    (if (symbol? sym-or-term)
      (sym-ref (environment-symbol-bindings env) sym-or-term)
      (term-ref (environment-term-bindings env) sym-or-term)))



  (define-record-type operative
    (fields params dyn-env-param body static-env)
    (protocol
     (lambda (m)
       (lambda (params dyn-env-param body static-env)

         (define (err msg . irrts) (apply error 'operative msg irrts))

         (define (check p c)
           (let ((e (bind empty-env p #T)))
             (if (exists (lambda (x)
                           (or (lookup (cdr x) p)
                               (lookup e (car x))))
                         c)
               (err "duplicate parameter" p)
               (cons (cons p e) c))))

         (define (map/check p c)
           (cond ((or (term? p)
                      (and (pair? p) (pair? (cdr p)) (null? (cddr p))
                           (eq? $quote
                                (if (symbol? (car p))
                                  (let ((b (lookup static-env (car p))))
                                    (and b (binding-val b)))
                                  (car p)))))
                  (let ((t (if (term? p) p (make-term (cadr p) static-env))))
                    (values t (check t c))))
                 ((pair? p)
                  (let*-values (((a c) (map/check (car p) c))
                                ((d c) (map/check (cdr p) c)))
                    (values (cons a d) c)))
                 ((symbol? p)
                  (values p (check p c)))
                 ((or (null? p) (not p))
                  (values p c))
                 (else (err "malformed parameter tree" params))))

         (let-values (((params _)
                       (map/check params (if (symbol? dyn-env-param)
                                           (check dyn-env-param '())
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

  (define (procedure->applicative proc)
    (make-applicative
     (make-scheme-escape
      (lambda (args _) (apply proc args)))))


  (define (combiner? x)
    (or (operative? x)
        (applicative? x)
        (scheme-escape? x)))



  (define (eval expr env)

    (define (err msg . irrts) (apply error 'eval msg irrts))

    (cond
      ((pair? expr)
       (cond
         ((lookup env (make-term expr env)) => binding-val)
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
       (cond ((lookup env expr) => binding-val)
             (else (err "unbound" expr))))

      (else expr)))


  (define boolean-ty (procedure->applicative boolean?))


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

       (_ . ,(make-ignore))

       (var . ,(procedure->applicative make-variable))
       ($type . ($vau (expr) env
                  (,(procedure->applicative
                     (lambda (expr)
                       (if (or (pair? expr) (symbol? expr))
                         (unimpl '$type expr)
                         expr)))
                   expr)))
       (is? . ,(procedure->applicative
                (lambda (type obj)
                  (or (equal? type obj)
                      (if (applicative? type)
                        (eval (list (applicative-underlying type)
                                    obj)
                              empty-env)
                        (unimpl 'is? type obj))))))
       (operative   . ,(procedure->applicative operative?))
       (applicative . ,(procedure->applicative applicative?))
       (combiner    . ,(procedure->applicative combiner?))
       (boolean     . ,boolean-ty)
     #;(pair        . ,(procedure->applicative pair?))
     #;(null        . ())
       (type-values . ,(procedure->applicative
                        (lambda (type)
                          (cond ((equal? boolean-ty type) '(#T #F))
                                (else (unimpl 'type-values type))))))

       (eval   . ,(procedure->applicative eval))
       (wrap   . ,(procedure->applicative make-applicative))
       (unwrap . ,(procedure->applicative applicative-underlying))
       (cons   . ,(procedure->applicative cons))
       (null?  . ,(procedure->applicative null?))
       (pair?  . ,(procedure->applicative pair?))

       (= . ,(procedure->applicative equal?))
       )))


  (define $vau   (eval '$vau  primitive-env))
  (define $quote (eval 'quote primitive-env))
  (define $type  (eval '$type primitive-env))
  (define is?    (eval 'is?   primitive-env))


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

       (lookup        . ,(procedure->applicative lookup))
       (binding-ident . ,(procedure->applicative binding-ident))
       (binding-val   . ,(procedure->applicative binding-val))
       )))

)
