#!r6rs
;; Copyright 2013 Derick Eddington.  My MIT-style license is in the file named
;; LICENSE from the original collection this file is distributed with.

(import
  (rnrs)
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


;;;; Classification of Expressions According to Established Theorems

(for-each (lambda (axiom) (check (classify/basic axiom) => '⊤))
          (theorems))
(for-each (lambda (anti-axiom) (check (classify/basic anti-axiom) => '⊥))
          (anti-theorems))

(let-syntax ((true (syntax-rules ()
                     ((_ expr) (check (classify/basic 'expr) => '⊤))))
             (false (syntax-rules ()
                      ((_ expr) (check (classify/basic 'expr) => '⊥))))
             (un (syntax-rules ()
                   ((_ expr) (check (classify/basic 'expr) => #F)))))
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
  ; TODO?: Some way to test basic classify doesn't do Consistency Rule?

  (parameterize-append ((theorems '((o a b))))
    (true (o x y)))

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

(let-syntax ((yes (syntax-rules ()
                    ((_ expr : laws ...)
                     (check ((transparency laws ...) 'expr) => '⊤))))
             (un (syntax-rules ()
                    ((_ expr : laws ...)
                     (check ((transparency laws ...) 'expr) => #F))))
             (AV (syntax-rules ()
                   ((_ expr : laws ...)
                    (check-AV ((transparency laws ...) 'expr))))))
  (AV a :)
  (AV (∨ a b) :)
  (AV (¬ a) :)
  (AV (= a b) :)
  (AV (= (a) b) :)
  (AV (= a (b)) :)
  (AV (= (o1 a) (o2 b)) :)
  (AV (= (o) (o)) :)
  (AV (= (o a) (o b c)) :)
  (AV (= (o a) (o a)) :)
  (AV (= (o a (o (o b) c)) (o a (o (o b) c))) :)
  (AV (= (o1 a (o2 (o3 b) c)) (o1 a (o2 (o4 b) c))) :)

  (un (= (o a) (o b)) :)
  (un (= (o1 a (o2 (o3 b) c)) (o1 b (o2 (o3 b) c))) :)
  (un (= (o1 a (o2 (o3 a) c)) (o1 a (o2 (o3 b) c))) :)
  (un (= (o1 a (o2 (o3 b) c)) (o1 a (o2 (o3 b) b))) :)

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

  )


;;;; Proofs

(let-syntax ((yes (syntax-rules () ((_ . r) (check (prove . r) => #T)))))

  (yes (∨ x (¬ x)) : completion)
  (yes (⇒ a b) : completion
       = (∨ (¬ a) b))
  (yes (¬ (∧ a b)) : completion
       = (∨ (¬ a) (¬ b)))
  (yes (∨ a (∨ b c)) : completion
       = (∨ (∨ a b) c))

  ; (a ∧ b ⇒ c) = (a ⇒ (b ⇒ c))

  (yes     (⇒ (∧ a b) c)         : completion
         = (∨ (¬ (∧ a b)) c)     : completion
         = (∨ (∨ (¬ a) (¬ b)) c) : completion
         = (∨ (¬ a) (∨ (¬ b) c)) : completion
         = (⇒ a (∨ (¬ b) c))     : completion
         = (⇒ a (⇒ b c)))

  (let ((mat-impl '(= (⇒ a b)
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
             = (⇒ a (⇒ b c)))))
  )



(check-report)
