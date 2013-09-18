#!r6rs
;; Copyright 2013 Derick Eddington.  My MIT-style license is in the file named
;; LICENSE from the original collection this file is distributed with.

(import
  (rnrs)
  (rnrs eval)
  (logji base)
  (logji boolean)
  (srfi :78 lightweight-testing))

(define-syntax check-AV
  (syntax-rules ()
    ((_ expr)
     (check (guard (ex (else (assertion-violation? ex)))
              expr
              'unexpected-return)
            => #T))))

(define-syntax check-SV
  (syntax-rules ()
    ((_ expr)
     (check (guard (ex (else (syntax-violation? ex)))
              (eval 'expr (environment '(rnrs) '(logji base) '(logji boolean)))
              'unexpected-return)
            => #T))))


;;;; Classification of Expressions According to Known Theorems

(for-each (lambda (axiom) (check (classify/known axiom) => '⊤))
          (theorems))
(for-each (lambda (anti-axiom) (check (classify/known anti-axiom) => '⊥))
          (anti-theorems))

(let-syntax ((true (syntax-rules ()
                     ((_ expr) (check (classify/known 'expr) => '⊤))))
             (false (syntax-rules ()
                      ((_ expr) (check (classify/known 'expr) => '⊥))))
             (un (syntax-rules ()
                   ((_ expr) (check (classify/known 'expr) => #F)))))
  (true ⊤)
  (true (¬ ⊥))
  (true (∧ ⊤ ⊤))
  (true (∨ ⊤ ⊤))
  (true (∨ ⊤ ⊥))
  (true (∨ ⊥ ⊤))
  (false ⊥)
  (false (¬ ⊤))
  (false (∧ ⊤ ⊥))
  (false (∧ ⊥ ⊤))
  (false (∧ ⊥ ⊥))
  (false (∨ ⊥ ⊥))
  ; TODO the remaining axioms

  (un v)
  (un (o))
  (un (o ⊤ ⊤))
  (un (o ⊤ v))
  (un (o (¬ ⊥) (∧ ⊤ ⊥)))
  (un (¬))
  (un (¬ ⊤ ⊤))
  (un (∧))
  (un (∧ ⊤))
  (un (∧ ⊤ ⊤ ⊤))

  (parameterize-append ((theorems '((o x y x))))
    (true (o a b a))
    (un (o a b c))
    (true (o foo bar foo))
    (un (o foo bar zab))
    (true (o (a) (a) (a)))
    (true (o ⊤ ⊥ ⊤))
    (true (∧ (o a b a) (o b a b)))
    (false (¬ (o a b a))))

  (true (¬ (¬ ⊤)))
  (true (¬ (∨ ⊥ ⊥)))
  (false (¬ (¬ (¬ ⊤))))
  (false (¬ (¬ (∨ ⊥ ⊥))))
  (true (∧ (¬ ⊥) (∨ ⊥ ⊤)))
  (false (∧ (¬ ⊥) (∨ ⊥ ⊥)))
  (true (¬ (∨ (∧ (∨ ⊥ ⊥) (¬ (∧ ⊥ ⊥)))
              (∧ (¬ (¬ ⊥)) (∨ ⊥ ⊤)) )))

  (true (∨ ⊤ x))
  (true (∨ x ⊤))
  (true (∨ ⊤ (un x)))
  (false (∧ ⊥ x))
  (false (∧ x ⊥))
  (false (∧ (un x) ⊥))
  (un (¬ x))
  (un (∨ ⊥ x))
  (un (∨ x ⊥))
  (un (∨ x x))
  (un (∧ ⊤ x))
  (un (∧ x ⊤))
  (un (∨ x (¬ x)))  ; Basic classify doesn't do Completion Rule

  (parameterize-append ((theorems '((o a b))))
    (true (o x y)))

  )


;;;; Classification of sub-expressions according to the Consistency Rule

(define (classes-equal? a b)
  (define (sort l)
    (define (to-string x)
      (call-with-string-output-port (lambda (sop) (write x sop))))
    (list-sort
     (lambda ab (apply string<? (map to-string ab)))
     l))
  (equal? (sort a) (sort b)))

(let-syntax ((yes (syntax-rules (: =>)
                    ((_ expr : classifier => sub-expr-classes ...)
                     (check ((classify/consistency classifier) 'expr)
                            (=> classes-equal?)
                            '(sub-expr-classes ...)))))
             (no (syntax-rules (:)
                    ((_ expr : classifier)
                     (check ((classify/consistency classifier) 'expr) => #F))))
             (AV (syntax-rules ()
                    ((_ expr)
                     (check-AV ((classify/consistency #F) 'expr))))))

  (AV a)
  (no (¬ a) : classify/known)
  (no (∧ ⊤ a) : classify/known)

  (parameterize-append ((constants '(a b c d))
                        (theorems '(a (⇒ a b) #;(? c ⊥ b) (o x)))
                        #;(anti-theorems '((? b c d))))
    (AV a)
    (yes (⇒ a b) : classify/known => (b . ⊤))
    (yes (∧ a (⇒ a b)) : classify/known => (b . ⊤))
    (yes (= a a) : classify/known =>)
    (yes (∨ b ⊤) : classify/known =>)
    ; TODO
    #;(yes (? c ⊥ b) : classify/known => (b . ⊤) (c . ⊥))
    #;(yes (? b ⊤ c) : classify/known => (b . ⊤) (c . ⊥))
    #;(yes (? b d c) : classify/known =>)

    (yes (∨ ⊤ a) : classify/known =>)
    (yes (∨ ⊤ (⇒ a b)) : classify/known => (b . ⊤))
    (yes (∨ (⇒ a b) (⇒ a b)) : classify/known => (b . ⊤) (b . ⊤))
    (yes (∨ (∨ ⊤ (⇒ a b)) ⊤) : classify/known => (b . ⊤))

    (yes (o b) : classify/known =>)
    (yes (o (¬ b)) : classify/known =>)
    (yes (o (⇒ a b)) : classify/known => (b . ⊤)))
  )


;;;; Proof Rules

;;;; Completion

(let-syntax ((yes (syntax-rules ()
                    ((_ expr) (check (completion 'expr) => '⊤))))
             (no (syntax-rules ()
                   ((_ expr) (check (completion 'expr) => '⊥))))
             (un (syntax-rules ()
                   ((_ expr) (check (completion 'expr) => #F)))))
  (un x)
  (un (¬ x))
  (un (∧ ⊤ x))
  (un (∨ ⊥ x))
  (un (⇒ ⊤ x))
  (un (= x ⊤))
  (un (∧ ⊤ ⊤))  ; No variables, no possibilities, results in unclassified.

  (yes (∨ ⊤ x))
  (yes (⇒ x ⊤))
  (yes (⇒ x x))
  (yes (= x x))
  (yes (∨ x (¬ x)))
  (yes (¬ (∧ (¬ x) x)))

  (no (∧ (¬ x) x))
  (no (¬ (∨ ⊤ x)))
  (no (¬ (= x x)))

  ; Complex structure (the expression is the Law of Resolution)
  (yes (∧ (∧ (⇒ (∧ a c)
                (∧ (∨ a b)
                   (∨ (¬ b) c)))
             (= (∧ (∨ a b)
                   (∨ (¬ b) c))
                (∨ (∧ a (¬ b))
                   (∧ b c))))
          (⇒ (∨ (∧ a (¬ b))
                (∧ b c))
             (∨ a c))))
  (no (¬ (∧ (∧ (⇒ (∧ a c)
                  (∧ (∨ a b)
                     (∨ (¬ b) c)))
               (= (∧ (∨ a b)
                     (∨ (¬ b) c))
                  (∨ (∧ a (¬ b))
                     (∧ b c))))
            (⇒ (∨ (∧ a (¬ b))
                  (∧ b c))
               (∨ a c)))))

  (parameterize-append ((constants '(c)))
    (un (∨ c (¬ c)))
    ; Mixture of classified and unclassified possibilities
    (un (∨ c x))
    (un (∧ x c))
    (un (∨ (∧ c x) (∧ y c))))
  )

;;;; Classify

(let-syntax ((yes (syntax-rules (:)
                    ((_ expr : rule)
                     (check ((classify rule) 'expr) => '⊤))))
             (no (syntax-rules (:)
                    ((_ expr : rule)
                     (check ((classify rule) 'expr) => #F))))
             (AV (syntax-rules ()
                    ((_ expr)
                     (check-AV ((classify (lambda _ #F)) 'expr))))))
  (AV a)
  (AV (¬ a))
  (AV (∧ a b))
  (AV (= a a))
  (no (= ⊥ ⊤) : classify/known)
  (no (= (¬ ⊤) ⊤) : classify/known)
  (no (= (o z) ⊥) : classify/known)
  (no (= ⊤ ⊥) : classify/known)
  (no (= ⊤ (¬ ⊤)) : classify/known)
  (no (= ⊥ (o z)) : classify/known)
  (yes (= ⊥ ⊥) : classify/known)
  (yes (= (¬ ⊤) ⊥) : classify/known)
  (yes (= (∧ ⊤ ⊤) ⊤) : classify/known)
  (yes (= ⊤ ⊤) : classify/known)
  (yes (= ⊥ (¬ ⊤)) : classify/known)
  (yes (= ⊤ (∧ ⊤ ⊤)) : classify/known)
  )

;;;; Law

(let-syntax ((yes (syntax-rules (:)
                    ((_ expr : theorem) (check ((law `theorem) 'expr) => '⊤))))
             (un (syntax-rules (:)
                   ((_ expr : theorem) (check ((law `theorem) 'expr) => #F))))
             (AV (syntax-rules ()
                   ((_ theorem) (check-AV ((law `theorem) #F))))))
  (AV (= y y))  ; Must use exact law form
  (AV (⇒ y ⊤))
  (AV (¬ (¬ ⊤)))
  (AV x)
  (AV (¬))
  (AV (o a b))
  (yes (= a a) : (= x x))
  (yes (= (o a) (o a)) : (= x x))
  (yes (= (o1 (o2 (o3 a) b) c) (o1 (o2 (o3 a) b) c)) : (= x x))
  (un (= a b) : (= x x))
  (un (= (o a) (o b)) : (= x x))
  (un (= (o1 a) (o2 a)) : (= x x))
  (un (= (o a) (o a b)) : (= x x))
  (un (= (o1 (o2 (o3 d) b) c) (o1 (o2 (o3 a) b) c)) : (= x x))
  (yes (⇒ ⊥ a) : (⇒ ⊥ x))
  (un (⇒ a ⊥) : (⇒ ⊥ x))
  (yes (∨ x ⊤) : (∨ ⊤ x))
  (yes (∨ (o a b) ⊤) : (∨ ⊤ x))
  (yes (⇐ ⊤ ⊤) : (⇒ x ⊤))
  (yes (⇐ a ⊥) : (⇒ ⊥ x))

  (parameterize-append ((theorems '((∨ x (¬ x)))))
    (AV (∨ y (¬ y)))
    (AV (∨ (¬ x) x))
    (yes (∨ c (¬ c)) : (∨ x (¬ x)))
    (yes (∨ (¬ c) c) : (∨ x (¬ x)))
    (yes (∨ (¬ (o (x a b) (y c))) (o (x a b) (y c))) : (∨ x (¬ x))))

  (let ((dist-ma '(= (× a (+ b c)) (+ (× a b) (× a c))))
        (dist-ms '(= (× a (- b c)) (- (× a b) (× a c)))))
    (parameterize-append ((theorems (list dist-ma dist-ms)))
      (yes (= (× x (+ z 1)) (+ (× x z) (× x 1))) : ,dist-ma)
      (yes (= (× y (- z 1)) (- (× y z) (× y 1))) : ,dist-ms)
      (yes (= (× z (- x y)) (- (× z x) (× z y))) : ,dist-ms)
      (yes (= (+ (× x z) (× x 1)) (× x (+ z 1))) : ,dist-ma)
      (yes (= (- (× y z) (× y 1)) (× y (- z 1))) : ,dist-ms)
      (yes (= (- (× z x) (× z y)) (× z (- x y))) : ,dist-ms)
      (un (= (× x (+ z 1)) (+ (× x z) (× x 2))) : ,dist-ma)
      (un (= (× y (- z 1)) (- (× y z) (× z 1))) : ,dist-ms)
      (un (= (× z (- z y)) (- (× z x) (× z y))) : ,dist-ms)))
  )

;;;; Transparency

(let-syntax ((yes (syntax-rules (:)
                    ((_ expr : rules ...)
                     (check ((transparency rules ...) 'expr) => '⊤))))
             (un (syntax-rules (:)
                    ((_ expr : rules ...)
                     (check ((transparency rules ...) 'expr) => #F))))
             (AV (syntax-rules (:)
                   ((_ expr : rules ...)
                    (check-AV ((transparency rules ...) 'expr))))))
  (AV a :)
  (AV (∨ a b) :)
  (AV (¬ a) :)
  (AV (= a b) :)
  (AV (= (a) b) :)
  (AV (= a (b)) :)
  (AV (= (o a) (o a)) :)
  (AV (= (o a (o (o b) c)) (o a (o (o b) c))) :)

  (un (= (o a) (o b)) :)
  (un (= (o) (o)) :)
  (un (= (o1 a) (o2 b)) :)
  (un (= (o a) (o b c)) :)
  (un (= (o1 a (o2 (o3 b) c)) (o1 b (o2 (o3 b) c))) :)
  (un (= (o1 a (o2 (o3 a) c)) (o1 a (o2 (o3 b) c))) :)
  (un (= (o1 a (o2 (o3 b) c)) (o1 a (o2 (o3 b) b))) :)
  (un (= (o1 a (o2 (o3 b) c)) (o1 a (o2 (o4 b) c))) :)

  (parameterize-append ((constants '(a b))
                        (theorems '((= b a))))
    (un (= (o a) (o b)) :)
    (yes (= (o a) (o b)) : (law '(= b a)))
    (yes (= (o b) (o a)) : (law '(= b a)))
    (yes (= (o a (o (o b) c)) (o b (o (o b) c))) : (law '(= b a)))
    (yes (= (o a (o (o a) c)) (o b (o (o b) c))) : (law '(= b a)))
    (yes (= (o b (o (o b) c)) (o a (o (o a) c))) : (law '(= b a)))
    (yes (= (o (z a) (z a)) (o (z a) (z b))) : (law '(= b a)))
    (yes (= (o (z a) (z a)) (o (z b) (z a))) : (law '(= b a)))
    (yes (= (o (z a) (z a)) (o (z b) (z b))) : (law '(= b a)))
    (yes (= (o (z a) (z b)) (o (z b) (z a))) : (law '(= b a))))

  (parameterize-append ((constants '(a))
                        (theorems '((= a (o b)))))
    (AV (= a (o b)) :)
    (un (= (z a) (z (o w))) :)
    (yes (= (z a) (z (o w))) : (law '(= a (o b))))
    (yes (= (z c a b) (z c (o d) b)) : (law '(= a (o b))))
    (yes (= (z c (o e) b) (z c a b)) : (law '(= a (o b))))
    (yes (= (z (o f) a c (o g)) (z a (o h) c a)) : (law '(= a (o b))))
    (un (= (z b) (z (o b))) :)
    (un (= (z (o b)) (z b)) :))

  (parameterize-append ((theorems '((∧ a b))))
    ; Only does Transparency
    (un (= (o (∧ a b)) (o ⊤)) : (law '(∧ a b))))

  ;   x×(z+1) – y×(z–1) – z×(x–y)   distribute
  ; = (x×z + x×1) – (y×z – y×1) – (z×x – z×y)
  (let ((dist-ma '(= (× a (+ b c)) (+ (× a b) (× a c))))
        (dist-ms '(= (× a (- b c)) (- (× a b) (× a c)))))
    (parameterize-append ((theorems (list dist-ma dist-ms)))
      (yes (= (- (- (× x (+ z 1))
                    (× y (- z 1)))
                 (× z (- x y)))
              (- (- (+ (× x z) (× x 1))
                    (- (× y z) (× y 1)))
                 (- (× z x) (× z y))))
           : (law dist-ma)
             (law dist-ms))))

  (yes (= (∧ (= a a) b) (∧ ⊤ b)) : (classify (law '(= x x))))

  )


;;;; Proofs

(let-syntax ((yes (syntax-rules () ((_ . r) (check (prove . r) => #T))))
             (no (syntax-rules () ((_ . r) (check (prove . r) => #F)))))

  (yes (∨ x (¬ x)) : completion)
  (yes   (∨ x y) : completion
       = (∨ y x))
  (yes (⇒ a b) : completion
       = (∨ (¬ a) b))
  (yes (¬ (∧ a b)) : completion
       = (∨ (¬ a) (¬ b)))
  (yes (∨ a (∨ b c)) : completion
       = (∨ (∨ a b) c))
  (no (∨ x x) : completion)

  ; (a ∧ b ⇒ c) = (a ⇒ (b ⇒ c))

  (yes     (⇒ (∧ a b) c)         : completion
         = (∨ (¬ (∧ a b)) c)     : completion
         = (∨ (∨ (¬ a) (¬ b)) c) : completion
         = (∨ (¬ a) (∨ (¬ b) c)) : completion
         = (⇒ a (∨ (¬ b) c))     : completion
         = (⇒ a (⇒ b c)))

  (let ((eq-reflex '(= x x))
        (mat-impl '(= (⇒ a b)
                      (∨ (¬ a) b)))
        (duality '(= (¬ (∧ a b))
                     (∨ (¬ a) (¬ b))))
        (disj-assoc '(= (∨ a (∨ b c))
                        (∨ (∨ a b) c))))
    (parameterize-append ((theorems (list mat-impl duality disj-assoc)))

      (yes     (⇒ (∧ a b) c)         : (law mat-impl)
             = (∨ (¬ (∧ a b)) c)     : (transparency (law duality))
             = (∨ (∨ (¬ a) (¬ b)) c) : (law disj-assoc)
             = (∨ (¬ a) (∨ (¬ b) c)) : (law mat-impl)
             = (⇒ a (∨ (¬ b) c))     : (transparency (law mat-impl))
             = (⇒ a (⇒ b c)))

      (yes   (= (⇒ (∧ a b) c)
                (⇒ a (⇒ b c)))         : (transparency (law mat-impl))
           = (= (∨ (¬ (∧ a b)) c)
                (∨ (¬ a) (⇒ b c)))     : (transparency (law mat-impl))
           = (= (∨ (¬ (∧ a b)) c)
                (∨ (¬ a) (∨ (¬ b) c))) : (transparency (law duality))
           = (= (∨ (∨ (¬ a) (¬ b)) c)
                (∨ (¬ a) (∨ (¬ b) c))) : (transparency (law disj-assoc))
           = (= (∨ (∨ (¬ a) (¬ b)) c)
                (∨ (∨ (¬ a) (¬ b)) c)) : (classify (law eq-reflex))
           = ⊤)

      (no    (= (⇒ (∧ a b) c)
                (⇒ a (⇒ b c)))         : (transparency (law mat-impl))
           = (= (∨ (¬ (∧ a b)) c)
                (∨ (¬ a) (⇒ b c)))     : (transparency (law mat-impl))
           = (= (∨ (¬ (∧ a b)) c)
                (∨ (¬ a) (∨ (¬ b) c))) : (transparency (law duality))
           = (= (∨ (∨ (¬ a) (¬ b)) c)
                (∨ (¬ a) (∨ (¬ b) c))) : (transparency (law disj-assoc))
           = (= (∨ (∨ (¬ a) (¬ b)) c)
                (∨ (∨ (¬ a) (¬ b)) c)) : (classify (law eq-reflex))
           = ⊥)

      (no    (= (⇒ (∧ a b) c)
                (⇒ a (⇒ b c)))         : (transparency (law mat-impl))
           = (= (∨ (¬ (∧ a b)) c)
                (∨ a (⇒ b c)))         : (transparency (law mat-impl))
           = (= (∨ (¬ (∧ a b)) c)
                (∨ (¬ a) (∨ (¬ b) c))) : (transparency (law duality))
           = (= (∨ (∨ (¬ a) (¬ b)) c)
                (∨ (¬ a) (∨ (¬ b) c))) : (transparency (law disj-assoc))
           = (= (∨ (∨ (¬ a) (¬ b)) c)
                (∨ (∨ (¬ a) (¬ b)) c)) : (classify (law eq-reflex))
           = ⊤)

      (no    (= (⇒ (∧ a b) c)
                (⇒ a (⇒ b c)))         : (transparency (law mat-impl))
           = (= (∨ (¬ (∧ a b)) c)
                (∨ (¬ a) (⇒ b c)))     : (transparency (law mat-impl))
           = (= (∨ (¬ (∧ a b)) c)
                (∨ (¬ a) (∨ (¬ b) c))) : (transparency (law duality))
           = (= (∨ (∨ (¬ a) (¬ b)) c)
                (∨ (¬ a) (∨ (¬ b) c))) : (transparency (law disj-assoc))
           = (= (∨ (∨ (¬ a) (¬ b)) c)
                (∨ (∨ (¬ a) (¬ b)) d)) : (classify (law eq-reflex))
           = ⊤)))

  (let ((dist-impl-conj
         '(= (⇒ x (∧ y z))
             (∧ (⇒ x y) (⇒ x z))))
        (antidist-impl-conj
         '(= (⇒ (∧ x y) z)
             (∨ (⇒ x z) (⇒ y z))))
        (dist-conj-disj
         '(= (∧ x (∨ y z))
             (∨ (∧ x y) (∧ x z))))
        (conj-symm
         '(= (∧ x y) (∧ y x)))
        (disj-symm
         '(= (∨ x y) (∨ y x)))
        (generalization
         '(⇒ x (∨ x y))))

    (parameterize-append ((theorems (list dist-impl-conj
                                          antidist-impl-conj
                                          dist-conj-disj
                                          conj-symm
                                          disj-symm
                                          generalization)))

      (yes   (⇒ (∧ a c) (∧ b d))
                                         : (law dist-impl-conj)
           = (∧ (⇒ (∧ a c) b)
                (⇒ (∧ a c) d))
                                         : (transparency (law antidist-impl-conj))
           = (∧ (∨ (⇒ a b) (⇒ c b))
                (∨ (⇒ a d) (⇒ c d)))
                                         : (law dist-conj-disj)
           = (∨ (∧ (∨ (⇒ a b) (⇒ c b))
                   (⇒ a d))
                (∧ (∨ (⇒ a b) (⇒ c b))
                   (⇒ c d)))
                                         : (transparency (law conj-symm))
           = (∨ (∧ (⇒ a d)
                   (∨ (⇒ a b) (⇒ c b)))
                (∧ (⇒ c d)
                   (∨ (⇒ a b) (⇒ c b))))
                                         : (transparency (law dist-conj-disj))
           = (∨ (∨ (∧ (⇒ a d) (⇒ a b))
                   (∧ (⇒ a d) (⇒ c b)))
                (∨ (∧ (⇒ c d) (⇒ a b))
                   (∧ (⇒ c d) (⇒ c b))))
                                         : (law disj-symm)
           = (∨ (∨ (∧ (⇒ c d) (⇒ a b))
                   (∧ (⇒ c d) (⇒ c b)))
                (∨ (∧ (⇒ a d) (⇒ a b))
                   (∧ (⇒ a d) (⇒ c b))))
                                         : (law generalization)
           ⇐ (∨ (∧ (⇒ c d) (⇒ a b))
                (∧ (⇒ c d) (⇒ c b)))
                                         : (law generalization)
           ⇐ (∧ (⇒ c d) (⇒ a b))
                                         : (law conj-symm)
           = (∧ (⇒ a b) (⇒ c d)))))
  )

;;;; Proofs in the form of simplication to ⊤ or ⊥

(let-syntax ((yes (syntax-rules () ((_ . r) (check (proof . r) => #T))))
             (no (syntax-rules () ((_ . r) (check (proof . r) => #F))))
             (SV (syntax-rules () ((_ . r) (check-SV (proof . r))))))

  (SV   (∨ x y) : completion
      = (∨ y x))
  (SV a : completion ⇐ ⊥)
  (SV a : completion ⇒ ⊤)
  (SV   a : completion
      = b : completion
      ⇒ c : completion
      = d : completion
      ⇐ ⊤)
  (SV (= a a) : completion = ⊤ ⊤)
  (SV (= a a) : completion ⇐ ⊤ ⊤)
  (SV (≠ a a) : completion = ⊥ ⊥)
  (SV (≠ a a) : completion ⇒ ⊥ ⊥)

  (yes (∨ x (¬ x)) : completion)
  (yes (= a a) : completion = ⊤)
  (yes (= a a) : completion ⇐ ⊤)
  (yes (≠ a a) : completion = ⊥)
  (yes (≠ a a) : completion ⇒ ⊥)
  (no (∨ x x) : completion)

  (let ((eq-reflex '(= x x))
        (mat-impl '(= (⇒ a b)
                      (∨ (¬ a) b)))
        (duality '(= (¬ (∧ a b))
                     (∨ (¬ a) (¬ b))))
        (disj-assoc '(= (∨ a (∨ b c))
                        (∨ (∨ a b) c))))
    (parameterize-append ((theorems (list mat-impl duality disj-assoc)))
      (yes   (= (⇒ (∧ a b) c)
                (⇒ a (⇒ b c)))         : (transparency (law mat-impl))
           = (= (∨ (¬ (∧ a b)) c)
                (∨ (¬ a) (⇒ b c)))     : (transparency (law mat-impl))
           = (= (∨ (¬ (∧ a b)) c)
                (∨ (¬ a) (∨ (¬ b) c))) : (transparency (law duality))
           = (= (∨ (∨ (¬ a) (¬ b)) c)
                (∨ (¬ a) (∨ (¬ b) c))) : (transparency (law disj-assoc))
           = (= (∨ (∨ (¬ a) (¬ b)) c)
                (∨ (∨ (¬ a) (¬ b)) c)) : (classify (law eq-reflex))
           = ⊤)))

  (let ((identity-impl '(= (⇒ ⊤ x) x))
        (mirror-impl '(= (⇒ x y) (⇐ y x)))
        (non-contradiction '(¬ (∧ x (¬ x))))
        (variation-not '(⇒ (⇒ x y) (⇐ (¬ x) (¬ y))))
        (variation-conj '(⇒ (⇒ x y) (⇒ (∧ x z) (∧ y z))))
        (conj-symm '(= (∧ x y) (∧ y x)))
        (generalization '(⇒ x (∨ x y)))
        (double-neg '(= (¬ (¬ x)) x))
        (duality '(= (¬ (∧ x y)) (∨ (¬ x) (¬ y))))
        (mat-impl '(= (⇒ x y) (∨ (¬ x) y))))

    (parameterize-append ((theorems (list identity-impl
                                          mirror-impl
                                          non-contradiction
                                          variation-not
                                          variation-conj
                                          conj-symm
                                          generalization
                                          double-neg
                                          duality
                                          mat-impl)))

      (yes   (¬ (∧ a (¬ (∨ a b))))     : (law identity-impl)
           = (⇒ ⊤
                (¬ (∧ a (¬ (∨ a b))))) : (law mirror-impl)
           = (⇐ (¬ (∧ a (¬ (∨ a b))))
                ⊤)                     : (transparency
                                          (classify (law non-contradiction)))
           = (⇐ (¬ (∧ a (¬ (∨ a b))))
                (¬ (∧ a (¬ a))))       : (law variation-not)
           ⇐ (⇒ (∧ a (¬ (∨ a b)))
                (∧ a (¬ a)))           : (transparency (law conj-symm))
           = (⇒ (∧ (¬ (∨ a b)) a)
                (∧ (¬ a) a))           : (law variation-conj)
           ⇐ (⇒ (¬ (∨ a b))
                (¬ a))                 : (law mirror-impl)
           = (⇐ (¬ a)
                (¬ (∨ a b)))           : (law variation-not)
           ⇐ (⇒ a (∨ a b))             : (classify (law generalization))
           = ⊤)

      (yes   (∧ a (¬ (∨ a b)))             : (law double-neg)
           = (¬ (¬ (∧ a (¬ (∨ a b)))))     : (transparency (law duality))
           = (¬ (∨ (¬ a) (¬ (¬ (∨ a b))))) : (transparency (law double-neg))
           = (¬ (∨ (¬ a) (∨ a b)))         : (transparency (law mat-impl))
           = (¬ (⇒ a (∨ a b)))             : (transparency
                                              (classify (law generalization)))
           = (¬ ⊤)                         : classify/known
           = ⊥)))

  )


;;;; Adding of proven laws

;;;; TODO: add-law!




(check-report)
