#!r6rs
;; Copyright 2013 Derick Eddington.  My MIT-style license is in the file named
;; LICENSE from the original collection this file is distributed with.

(library (logji zbepi load)
  (export
    load
    $define $define-marker)
  (import
    (rnrs base)
    (rnrs control)
    (rnrs io simple)
    (logji zbepi))


  (define $let (eval '$let standard-env))
  (define get-current-environment (eval 'get-current-environment standard-env))


  (define $define-marker (string-copy "$define-marker"))

  (define $define
    (eval `($vau (params expr) env
             (eval (list $let (list (list params expr))
                         (list ,(procedure->applicative values)
                               ,$define-marker
                               (list get-current-environment)))
                   env))
          standard-env))


  (define load
    (case-lambda
      ((file)
       (load file standard-env))
      ((file env)
       (with-input-from-file file
         (lambda ()
           (let loop ((env (eval `(,$let (($define ,$define))
                                    (,get-current-environment))
                                 env))
                      (vals '()))
             (let ((expr (read)))
               (if (eof-object? expr)
                 (apply values vals)
                 (let-values ((vals (eval expr env)))
                   (cond ((and (= 2 (length vals))
                               (eqv? $define-marker (car vals)))
                          (loop (cadr vals) '()))
                         (else
                          (loop env vals))))))))))))

)
