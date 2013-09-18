#!r6rs
;; Copyright 2013 Derick Eddington.  My MIT-style license is in the file named
;; LICENSE from the original collection this file is distributed with.

; TODO: "if" operator

(library (logji boolean)
  (export
    theorems
    anti-theorems
    prove
    proof
    add-law!
    classify/known
    classify/consistency
    completion
    classify
    law
    transparency)
  (import
    (rnrs base)
    (rnrs lists)
    (srfi :39 parameters)
    (logji base))


(define (operator? x) (memq x '(¬ ∧ ∨ ⇒ ⇐ = ≠)))
(define (symmetric-operator? x) (memq x '(∧ ∨ = ≠)))

(define axioms
  '(⊤
    (¬ ⊥)
    (∧ ⊤ ⊤)
    (∨ ⊤ x)
    (∨ x ⊤)
    (⇒ ⊥ x)
    (⇒ x ⊤)
    (⇐ x ⊥)
    (⇐ ⊤ x)
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
    (⇐ ⊥ ⊤)
    (= ⊤ ⊥)
    (= ⊥ ⊤)
    (≠ x x)))

(define theorems (make-parameter axioms))
(define anti-theorems (make-parameter anti-axioms))


;;;; Classification according to known theorems

(define (classify/known expr)
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
            (operands-classifications (map classify/known operands)))
       (and (not (equal? operands operands-classifications))
            (for-all (lambda (x) x) operands-classifications)
            (classify/known `(,operator ,@operands-classifications)))))
    ; Unclassified
    (else #F)))


;;;; Classification of sub-expressions according to the Consistency Rule

(define (classify/consistency classifier)
  (lambda (expr)
    ; Consistency Rule only valid for expressions with sub-expressions
    (assert (pair? expr))
    (let recur ((e expr))
      (let ((class (classifier e)))
        (and class
             (if (pair? e)
               (let* ((operator (car e))
                      (operands (cdr e))
                      (occ (map recur operands)))
                 (define (candidate? operand class)
                   (and (not class)
                        (or (operator? operator)
                            (and (pair? operand)
                                 (operator? (car operand))))))
                 (let ((ps (permute (map (lambda (o c)
                                           (if (candidate? o c) '(⊤ ⊥) (list o)))
                                         operands occ))))
                   (or (and (< 1 (length ps))
                            (let* ((cs (map (lambda (perm)
                                              (cons perm (classifier
                                                          `(,operator ,@perm))))
                                            ps))
                                   (ecs (filter (lambda (c) (eq? class (cdr c)))
                                                cs)))
                              (and (= 1 (length ecs))
                                   (let ((eperm (caar ecs)))
                                     (fold-left (lambda (a o c ev)
                                                  (if (candidate? o c)
                                                    (cons (cons o ev) a)
                                                    (if c (append c a) a)))
                                                '() operands occ eperm)))))
                       (apply append (filter (lambda (x) x) occ)))))
               '()))))))


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

  (define (all-same-class? l)
    (and (pair? l)  ; No vars, no classifications, results in unclassified.
         (for-all (lambda (x) (and (eqv? (car l) x) x))
                  (cdr l))))

  (all-same-class?
   (map (lambda (v) (classify/known (subst v)))
        (permute (map (lambda (v) `((,v . ⊤) (,v . ⊥)))
                      vars)))))

;;;; Classify

(define (classify rule)
  (lambda (expr)
    ; Only valid for classifying if an expression has same value as ⊤ or ⊥
    (assert (and (pair? expr) (eq? '= (car expr))))
    (let-values (((e1 c) (cond ((memq (cadr expr) '(⊤ ⊥))
                                (values (caddr expr) (cadr expr)))
                               ((memq (caddr expr) '(⊤ ⊥))
                                (values (cadr expr) (caddr expr)))
                               (else (assert #F)))))
      (and (eq? c (rule e1))
           '⊤))))

;;;; Law

(define (law theorem)
  (lambda (expr)
    ; Only valid for known theorems
    (assert (member theorem (theorems)))
    (and (or (instance? expr theorem)
             (and (pair? expr)
                  ; For expression with a primary symmetric operator, try again
                  ; with swapped operands because that's equivalent
                  (or (and (symmetric-operator? (car expr))
                           (instance? `(,(car expr) ,(caddr expr) ,(cadr expr))
                                      theorem))
                      ; For expression with ⇐ operator, try again with
                      ; equivalent ⇒ form
                      (and (eq? '⇐ (car expr))
                           (instance? `(⇒ ,(caddr expr) ,(cadr expr))
                                      theorem)))))
         '⊤)))

;;;; Transparency

; TODO: Remove support for multiple rules in one step

(define (transparency . rules)
  (lambda (expr)
    ; The below assertions are done to ensure reasonable usage
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
          ; The two expressions must have the same operator
          (and (eq? e1-optr e2-optr)
               (let ((e1ol (length e1-opnd))
                     (e2ol (length e2-opnd)))
                 ; They must have operands, to have sub-expressions
                 (and (for-all positive? (list e1ol e2ol))
                      ; They must have the same amount of operands
                      (= e1ol e2ol)))
               ; The corresponding sub-expressions must differ somewhere
               (or (not (for-all equal? e1-opnd e2-opnd))
                   (assert #F))

               ; The corresponding sub-expressions must have equal values
               (for-all (lambda (e1s e2s)
                          (or (equal? e1s e2s)
                              (exists (lambda (r) (eq? '⊤ (r `(= ,e1s ,e2s))))
                                      rules)
                              (and (pair? e1s) (pair? e2s)
                                   (recur `(= ,e1s ,e2s)))))
                        e1-opnd
                        e2-opnd)
               '⊤))))))


;;;; Proving - special form of boolean expression classification

(define-syntax prove
  (syntax-rules (:)
    ((_ expr : rule)
     (prove expr : rule = ⊤))
    ((_ . rest)
     (prove-aux () . rest))))

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

;;;; Proofs in the form of simplication to ⊤ or ⊥

(define-syntax proof
  (syntax-rules ()
    ((_ expr : rule)
     (proof expr : rule = ⊤))
    ((_ . rest)
     (proof-aux () . rest))))

(define-syntax proof-aux
  (syntax-rules (: = ⇒ ⇐ ⊤ ⊥)
    ; When driving towards ⊤, the operators of the steps can be any mixture of =
    ; and ⇐
    ((_ (accum ...) expr : rule = ⊤)
     (prove accum ... expr : rule = ⊤))
    ((_ (accum ...) expr : rule ⇐ ⊤)
     (prove accum ... expr : rule ⇐ ⊤))
    ((_ (accum ...) expr1 : rule = expr2 more ... ⊤)
     (proof-aux (accum ... expr1 : rule =) expr2 more ... ⊤))
    ((_ (accum ...) expr1 : rule ⇐ expr2 more ... ⊤)
     (proof-aux (accum ... expr1 : rule ⇐) expr2 more ... ⊤))
    ; When driving towards ⊥, the operators of the steps can be any mixture of =
    ; and ⇒
    ((_ (accum ...) expr : rule = ⊥)
     (prove accum ... expr : rule = ⊥))
    ((_ (accum ...) expr : rule ⇒ ⊥)
     (prove accum ... expr : rule ⇒ ⊥))
    ((_ (accum ...) expr1 : rule = expr2 more ... ⊥)
     (proof-aux (accum ... expr1 : rule =) expr2 more ... ⊥))
    ((_ (accum ...) expr1 : rule ⇒ expr2 more ... ⊥)
     (proof-aux (accum ... expr1 : rule ⇒) expr2 more ... ⊥))))


;;;; Adding of proven laws

(define-syntax add-law!
  (syntax-rules (⊤ ⊥)
    ((_ law more ... ⊤)
     (add-law!-proc (proof law more ... ⊤) 'law))
    ((_ law more ... ⊥)
     (add-law!-proc (proof law more ... ⊥) '(¬ law)))))

(define (add-law!-proc proven law)
  (if proven
    (theorems (cons law (theorems)))
    (assertion-violation 'add-law! "Invalid proof" 'law)))


)
