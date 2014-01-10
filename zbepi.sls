#!r6rs
;; Copyright 2014 Derick Eddington.  My MIT-style license is in the file named
;; LICENSE from the original collection this file is distributed with.

; TODO: The term-bindings design is seriously flawed because matching commits to
; a path when its part matches, but if the match later fails the entire matching
; fails even if there is another possibility at an outer level that would match
; all the way.  The search must be able to back-track, but this seems at odds
; with the purpose of the data structure (which is to restrict searching to
; selected tree branches).

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


  ; <environment>     : [environment <symbol-bindings> <term-bindings>]
  ; <symbol-bindings> : ([binding <symbol> <anything>] ...)
  ; <term-bindings>   : <possibilities>
  ; <possibilities>   : [possibs (<possibility> ... <possibility*> ? )]
  ; <possibility>     : (<pattern> . <possibilities>)
  ;                   | [end <pattern> [binding <term> <anything>] #F]
  ; <pattern>         : [value <value>]
  ;                   | [variable <type>]
  ;                   | [ignore]
  ;                   | <literal>
  ; <value>           : <anything> except variable or ignore
  ; <type>            : <anything>
  ; <literal>         : <anything> except pair
  ; <possibility*>    | (<possibilities*> . #F)
  ; <possibilities*>  : [possibs ((<pattern> . <possibilities**>) ...
  ;                               <possibility*> ? )]
  ; <possibilities**> : [possibs (<possibility**> ... <possibility*> ? )]
  ; <possibility**>   : (<pattern> . <possibilities**>)
  ;                   | [end <pattern> #F <possibilities**>]
  ;                   | [end <pattern> #F <possibilities>]
  ;
  ; Examples: TODO: Still valid?
  ; Environment with one term (a b):
  ; term-bindings =
  ; [possibs ((a* . [possibs ((b* . [possibs ([end ()
  ;                                                [binding [term (a b) <env>]
  ;                                                         <anything>]
  ;                                                #F])]))]))]
  ; Environment with one term ((a) b):
  ; term-bindings =
  ; [possibs (([possibs ((a*
  ;             . [possibs ([end ()
  ;                              #F
  ;                              [possibs ((b*
  ;                               . [possibs ([end ()
  ;                                                [binding [term ((a) b) <env>]
  ;                                                         <anything>]
  ;                                                #F])]))]])]))]
  ;            . #F))]
  ;
  ; Environment with four terms (a) (a b) ((a) b) ((a b) c):
  ; term-bindings =
  ; [possibs
  ;  ((a* . [possibs
  ;          ([end () [binding [term (a) <env>] <anything>] #F]
  ;           (b* . [possibs
  ;                  ([end () [binding [term (a b) <env>] <anything>] #F])]))])
  ;   ([possibs
  ;     ((a* . [possibs
  ;             ([end () #F [possibs
  ;                          ((b* . [possibs
  ;                                  ([end ()
  ;                                        [binding [term ((a) b) <env>]
  ;                                                 <anything>]
  ;                                        #F])]))]]
  ;              (b* . [possibs
  ;                     ([end () #F [possibs
  ;                                  ((c* . [possibs
  ;                                          ([end ()
  ;                                                [binding [term ((a b) c) <env>]
  ;                                                         <anything>]
  ;                                                #F])]))])]))]))]
  ;    . #F))]

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

  (define-record-type possibs (fields list)) ; private
  (define-record-type end (fields pat binding cont-poss)) ; private
  (define-record-type value (fields val)) ; private
  (define-record-type variable (fields type))
  (define-record-type ignore)

  (define empty-env (make-environment '() (make-possibs '())))


  (define (bind env sym-or-term val)

    (define (sym-bind sb sym val)
      (cons (make-binding sym val) sb))

    (define (term-bind possibilities term val)
      (let ((t-env (term-env term)))

        (define (patternify o)
          ; Initially using patternify on the entire term expression acheives
          ; looking-up all the symbols, as required in all cases handled by
          ; term-bind, only once.
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

        (define (compare p o vars)
          (cond
            ((value? p)
             (and (value? o)
                  (equal? (value-val p) (value-val o))
                  vars))
            ((variable? p)
             (and (variable? o)
                  (cond ((assq p vars) => (lambda (a)
                                            (and (eq? (cdr a) o)
                                                 vars)))
                        (else
                         (and (equal? (variable-type p) (variable-type o))
                              (cons (cons p o) vars))))))
            ((ignore? p)
             (and (ignore? o)
                  vars))
            (else ; p is literal or unbound symbol or null
             (and (equal? p o)
                  vars))))

        (let match ((ps (possibs-list possibilities))
                    (obj (patternify (term-expr term)))
                    (vars '())
                    (ods '())
                    (rps '()))
          (if (pair? ps)
            (let ((p (car ps)))
              (define (update np)
                (make-possibs (rappend rps (cons np (cdr ps)))))
              (cond
                ((and (pair? p)
                      (pair? obj)
                      (not (possibs? (car p)))
                      (not (pair? (car obj)))
                      (compare (car p) (car obj) vars))
                 => (lambda (vars*)
                      (update (cons (car p)
                                    (match (possibs-list (cdr p))
                                           (cdr obj)
                                           vars*
                                           ods
                                           '())))))
                ((and (pair? p)
                      (pair? obj)
                      (possibs? (car p))
                      (pair? (car obj)))
                 (assert (null? (cdr ps)))
                 (update (cons (match (possibs-list (car p))
                                      (car obj)
                                      vars
                                      (cons (cdr obj) ods)
                                      '())
                               #F)))
                ((and (end? p)
                      (not (pair? obj))
                      (compare (end-pat p) obj vars))
                 => (lambda (vars*)
                      (let-values (((b* cps*)
                                    (cond ((end-cont-poss p)
                                           => (lambda (cps)
                                                (values #F
                                                        (match (possibs-list cps)
                                                               (car ods)
                                                               vars*
                                                               (cdr ods)
                                                               '()))))
                                          (else
                                           (values (make-binding term val)
                                                   #F)))))
                        (update (make-end (end-pat p) b* cps*)))))
                (else
                 (match (cdr ps) obj vars ods (cons p rps)))))

            (let make ((obj obj) (ods ods) (rps rps))
              (make-possibs
               (cond ((and (pair? obj)
                           (pair? (car obj)))
                      ; This form of pattern must be after all others at this
                      ; level, to ensure that all patterns which are for pairs
                      ; without pair cars are tried before committing to the
                      ; pattern which is for pairs with pair cars.  Otherwise,
                      ; because of how lookup is implemented, lookup could
                      ; commit to testing a pattern which is for pairs with pair
                      ; cars and if that fails none of the other patterns will
                      ; be tried even though one of them might match.
                      (rappend rps
                               (list
                                (cons (make (car obj) (cons (cdr obj) ods) '())
                                      #F))))
                     ((pair? obj)
                      (cons (cons (car obj)
                                  (make (cdr obj) ods '()))
                            (reverse rps)))
                     (else
                      (cons (if (pair? ods)
                              (make-end obj #F (make (car ods) (cdr ods) '()))
                              (make-end obj (make-binding term val) #F))
                            (reverse rps))))))))))

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

    (define (term-ref possibilities term)
      (let ((t-env (term-env term)))

        (define (compare p o vars cache)

          (define (cached-fields o)
            (values o
                    (cached-obj    o)
                    (cached-tried? o)
                    (cached-val?   o)
                    (cached-val    o)
                    (cached-type?  o)
                    (cached-type   o)))

          (let-values (((o x tried? val? val type? type)
                        (cond ((cached? o)
                               (cached-fields o))
                              ((assoc o cache)
                               => (lambda (a) (cached-fields (cdr a))))
                              (else
                               (values o o #F #F #F #F #F)))))

            (define (yes) (values #T o vars cache))
            (define (no) (values #F o vars cache))
            (define (yes* o* vars* cache*) (values #T o* vars* cache*))
            (define (no* o* vars* cache*) (values #F o* vars* cache*))

            (define (cache-x tried? val? val type? type)
              (let ((o* (make-cached x tried? val? val type? type)))
                (values o* (cons (cons x o*) cache))))

            (define (do-val tproc bproc eproc)
              (cond (tried?
                     (if (tproc) (yes) (no)))
                    ((lookup t-env (if (pair? x) (make-term x t-env) x))
                     => (lambda (b)
                          (let ((v (binding-val b)))
                            (let-values (((o* cache*)
                                          (cache-x #T #T v type? type)))
                              (if (bproc v)
                                (yes* o* vars cache*)
                                (no* o* vars cache*))))))
                    (else
                     (let-values (((o* cache*)
                                   (cache-x #T #F #F type? type)))
                       (eproc o* vars cache*)))))

            (cond
              ((value? p)
               (cond ((or (pair? x) (symbol? x))
                      (do-val (lambda () (and val? (equal? (value-val p) val)))
                              (lambda (bv) (equal? (value-val p) bv))
                              no*))
                     ((equal? (value-val p) x)
                      (yes))
                     (else (no))))

              ((variable? p)
               (cond
                 ((assq p vars) => (lambda (a)
                                     (if (equal? x (cdr a))
                                       (yes)
                                       (no))))

                 ((and (symbol? x)
                       (not tried?))
                  (let-values (((? o* _ cache*)
                                (do-val (lambda () (assert #F))
                                        (lambda (bv) #T)
                                        no*)))
                    (if ?
                      (compare p o* vars cache*)
                      (no* o* vars cache*))))

                 ((or (not (symbol? x))
                      val?)
                  (let-values (((oty o* cache*)
                                (cond
                                  (type?
                                   (values type o cache))
                                  ((and (symbol? x)
                                        (variable? val))
                                   (values (variable-type val) o cache))
                                  ((variable? x)
                                   (values (variable-type x) o cache))
                                  (val?
                                   (values val o cache))
                                  (else
                                   (let ((oty (eval `(,$type ,x) t-env)))
                                     (let-values
                                         (((o* cache*)
                                           (cache-x tried? val? val #T oty)))
                                       (values oty o* cache*)))))))
                    (if (eval `((,$vau (vty oty) #F
                                  (,is? vty oty))
                                ,(variable-type p)
                                ,oty)
                              t-env)
                      (yes* o* (cons (cons p x) vars) cache*)
                      (no* o* vars cache*))))

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

        (let match ((ps (possibs-list possibilities))
                    (o (term-expr term))
                    (vars '())
                    (ods '())
                    (cache '()))
          (define (uncache a) (if (cached? a) (cached-obj a) a))
          (and (pair? ps)
               (let ((p (car ps))
                     (x (uncache o)))
                 (define (next o* cache*)
                   (match (cdr ps) o* vars ods cache*))
                 (cond
                   ((and (pair? p)
                         (pair? x)
                         (not (possibs? (car p))))
                    (let-values (((? oa* vars* cache*)
                                  (compare (car p) (car x) vars cache)))
                      (if ?
                        (match (possibs-list (cdr p))
                               (cdr x)
                               vars*
                               ods
                               cache*)
                        (next (cons oa* (cdr x)) ; This necessitates uncache
                              cache*))))
                   ((and (pair? p)
                         (pair? x)
                         (possibs? (car p))
                         (pair? (uncache (car x))))
                    (match (possibs-list (car p))
                           (car x)
                           vars
                           (cons (cdr x) ods)
                           cache))
                   ((end? p)
                    (let-values (((? o* vars* cache*)
                                  (compare (end-pat p)
                                           (if (and (pair? x)
                                                    (not (cached? o)))
                                             (cons (uncache (car x))
                                                   (cdr x))
                                             o)
                                           vars
                                           cache)))
                      (if ?
                        (cond ((end-cont-poss p)
                               => (lambda (cps)
                                    (match (possibs-list cps)
                                           (car ods)
                                           vars*
                                           (cdr ods)
                                           cache*)))
                              (else (end-binding p)))
                        (next o* cache*))))
                   (else
                    (next o cache))))))))

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

       (= . ,(procedure->applicative
              (lambda (a b)
                (or (equal? a b)
                    (unimpl '= a b)))))
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
       (make-binding  . ,(procedure->applicative make-binding))
       )))

)
