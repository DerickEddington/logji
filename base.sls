#!r6rs
;; Copyright 2013 Derick Eddington.  My MIT-style license is in the file named
;; LICENSE from the original collection this file is distributed with.

(library (logji base)
  (export
    parameterize-append
    constants
    variable?
    instance?
    instance-of-any?)
  (import
    (rnrs base)
    (rnrs lists)
    (srfi :39 parameters))


(define-syntax parameterize-append
  (syntax-rules ()
    ((_ ((param expr) ...) . body)
     (parameterize ((param (append expr (param))) ...) . body))))


(define constants
  (make-parameter '(⊤ ⊥)))


(define (variable? x)
  (and (symbol? x)
       (not (memq x (constants)))))


(define (instance? test-expr pattern-expr)
  (let match ((e test-expr)
              (p pattern-expr)
              (vars '()))
    (cond ((pair? p)
           (and (pair? e)
                (let ((e-operator (car e))
                      (p-operator (car p)))
                  (and (equal? e-operator p-operator)
                       (let fold ((e-operands (cdr e))
                                  (p-operands (cdr p))
                                  (v vars))
                         (and v
                              (cond ((pair? p-operands)
                                     (and (pair? e-operands)
                                          (fold (cdr e-operands)
                                                (cdr p-operands)
                                                (match (car e-operands)
                                                       (car p-operands)
                                                       v))))
                                    ((null? p-operands)
                                     (and (null? e-operands)
                                          v))
                                    (else
                                     (assert #F)))))))))
          ((variable? p)
           (cond ((assq p vars) => (lambda (a)
                                     (and (equal? e (cdr a))
                                          vars)))
                 (else (cons (cons p e) vars))))
          (else
           (and (equal? e p)
                vars)))))


(define (instance-of-any? expr expr-list)
  (find (lambda (e) (instance? expr e))
        expr-list))

)
