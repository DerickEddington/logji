#!r6rs
;; Copyright 2013 Derick Eddington.  My MIT-style license is in the file named
;; LICENSE from the original collection this file is distributed with.

(library (logji zbepi repl)
  (export
    repl)
  (import
    (rnrs base)
    (rnrs control)
    (rnrs io simple)
    (rnrs exceptions)
    (logji zbepi)
    (logji zbepi load)
    (only (xitomatl common) pretty-print)
    (only (xitomatl exceptions) print-exception))


  (define $let (eval '$let standard-env))
  (define get-current-environment (eval 'get-current-environment standard-env))


  (define repl
    (case-lambda
      (()
       (repl standard-env))
      ((env)
       (call/cc
         (lambda (exit)
           (let loop ((env (eval `(,$let (($define ,$define))
                                    (,get-current-environment))
                                 env)))
             (display "z> ")
             (loop
              (call/cc
                (lambda (cc)
                  (define-syntax E
                    (syntax-rules ()
                      ((_ expr)
                       (with-exception-handler
                         (lambda (ex)
                           (print-exception ex)
                           (cc env))
                         (lambda () expr)))))

                  (let ((expr (E (read))))
                    (if (eof-object? expr)
                      (exit)
                      (let-values ((vals (E (eval expr env))))
                        (cond
                          ((and (= 2 (length vals))
                                (eqv? $define-marker (car vals)))
                           (cadr vals))
                          (else
                           (for-each pretty-print vals)
                           env))))))))))))))


)
