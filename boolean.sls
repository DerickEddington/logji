#!r6rs
;; Copyright 2013 Derick Eddington.  My MIT-style license is in the file named
;; LICENSE from the original collection this file is distributed with.

; TODO: Consistency Rule in someway.

(library (logji boolean)
  (export
    theorems
    anti-theorems
    classify/basic
    prove
    completion
    law
    transparency)
  (import
    (rnrs base)
    (rnrs lists)
    (srfi :39 parameters)
    (logji base))

; TODO: The remaining operators and axioms.

(define (operator? x) (memq x '(¬ ∧ ∨ ⇒ = ≠)))
(define (symmetric-operator? x) (memq x '(∧ ∨ = ≠)))

(define axioms
  '(⊤
    (¬ ⊥)
    (∧ ⊤ ⊤)
    (∨ ⊤ x)
    (∨ x ⊤)
    (⇒ ⊥ x)
    (⇒ x ⊤)
    (= x x)
    (≠ ⊤ ⊥)
    (≠ ⊥ ⊤)))

(define anti-axioms
  '(⊥
    (¬ ⊤)
    (∧ ⊥ x)
    (∧ x ⊥)
    (∨ ⊥ ⊥)
    (⇒ ⊤ ⊥)
    (= ⊤ ⊥)
    (= ⊥ ⊤)
    (≠ x x)))

(define theorems (make-parameter axioms))
(define anti-theorems (make-parameter anti-axioms))


;;;; Classification of Expressions According to Established Theorems

(define (classify/basic expr)
  (cond
    ;;;; Axiom/Proven/Instance Rule
    ((instance-of-any? expr (theorems))
     '⊤)
    ((instance-of-any? expr (anti-theorems))
     '⊥)
    ;;;; Evaluation Rule
    ((and (list? expr) (<= 2 (length expr)))
     (let* ((operator (car expr))
            (operands (cdr expr))
            (operands-classifications (map classify/basic operands)))
       (and (not (equal? operands operands-classifications))
            (for-all (lambda (x) x) operands-classifications)
            (classify/basic `(,operator ,@operands-classifications)))))
    ; Unclassified
    (else #F)))


;;;; Proving

(define-syntax prove
  (syntax-rules (:)
    ((_ expr : rule)
     (prove expr : rule = ⊤))
    ((_ expr1 : rule operator expr2 . rest)
     (prove-aux () expr1 : rule operator expr2 . rest))))

(define-syntax prove-aux
  (syntax-rules (:)
    ((_ (accum ...)
        expr1 : rule
        operator expr2)
     (prove-proc accum ... (cons '(operator expr1 expr2) rule)))
    ((_ (accum ...)
        expr1 : rule1
        operator1 expr2 : rule2
        operator2 expr3
        . rest)
     (prove-aux (accum ... (cons '(operator1 expr1 expr2) rule1))
                expr2 : rule2
                operator2 expr3
                . rest))))

(define (prove-proc . steps)
  (for-all (lambda (s)
             (let ((expr (car s))
                   (rule (cdr s)))
               (eq? '⊤ (rule expr))))
           steps))


;;;; Proof Rules - specialized partial classification

;;;; Completion

(define (completion expr)

  (define vars
    ; Extract the variables of any boolean-operator expressions in the
    ; expression.
    (let f ((a '()) (e expr))
      (cond ((and (pair? e) (operator? (car e)))
             (fold-left f a (cdr e)))
            ((variable? e)
             (if (memq e a) a (cons e a)))
            (else a))))

  (define (subst v)
    (let f ((e expr))
      (cond ((and (pair? e) (operator? (car e)))
             `(,(car e) ,@(map f (cdr e))))
            ((variable? e)
             (cdr (assq e v)))
            (else e))))

  (define (permute l)
    (cond ((null? l) '())
          ((null? (cdr l)) (map list (car l)))
          (else (let ((p (permute (cdr l))))
                  (apply append (map (lambda (a) (map (lambda (r) (cons a r)) p))
                                     (car l)))))))

  (define (all-same-class? l)
    (and (pair? l)  ; No vars, no classifications, results in unclassified.
         (for-all (lambda (x) (and (eqv? (car l) x) x))
                  (cdr l))))

  (all-same-class?
   (map (lambda (v) (classify/basic (subst v)))
        (permute (map (lambda (v) `((,v . ⊤) (,v . ⊥)))
                      vars)))))

;;;; Law

(define (law theorem)
  (lambda (expr)
    ; Law rule only valid for established theorems
    (assert (member theorem (theorems)))
    (and (or (instance? expr theorem)
             ; For expression with a primary symmetric operator, try again with
             ; swapped operands because that's equivalent
             (and (pair? expr)
                  (symmetric-operator? (car expr))
                  (instance? `(,(car expr) ,(caddr expr) ,(cadr expr))
                             theorem)))
         '⊤)))

;;;; Transparency

(define (transparency . laws)
  (lambda (expr)
    ; All the below assertions are done to ensure reasonable usage
    (let recur ((expr expr))
      ; Transparency Rule only valid for classifying if two expressions have
      ; equal value
      (assert (and (pair? expr) (eq? '= (car expr))))
      (let ((e1 (cadr expr))
            (e2 (caddr expr)))
        ; The two must have sub-expressions, so they must be compound
        (assert (and (pair? e1) (pair? e2)))
        (let ((e1-optr (car e1))
              (e1-opnd (cdr e1))
              (e2-optr (car e2))
              (e2-opnd (cdr e2)))
          ; They must have the same operator
          (assert (eq? e1-optr e2-optr))
          (let ((e1ol (length e1-opnd))
                (e2ol (length e2-opnd)))
            ; They must have operands, to have sub-expressions
            (assert (for-all positive? (list e1ol e2ol)))
            ; They must have the same amount of operands
            (assert (= e1ol e2ol)))
          ; The corresponding sub-expressions must differ somewhere
          (assert (not (for-all equal? e1-opnd e2-opnd)))

          ; The corresponding sub-expressions must have equal values
          (and (for-all (lambda (e1s e2s)
                          (or (equal? e1s e2s)
                              (exists (lambda (l) (eq? '⊤ (l `(= ,e1s ,e2s))))
                                      laws)
                              (and (pair? e1s) (pair? e2s)
                                   (recur `(= ,e1s ,e2s)))))
                        e1-opnd
                        e2-opnd)
               '⊤))))))


)
