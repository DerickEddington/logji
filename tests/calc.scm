($define $define-law
  ($vau (name . patterns) env
    (eval (list $define name
                (eval (cons (list $vau (map ($lambda (p) (make-term p env))
                                            patterns)
                                  #F
                                  (list get-current-environment))
                            (map ($lambda #F #T) patterns))
                      empty-environment))
          env)))

($define ⊤ #T)
($define ⊥ #F)

($define x (var boolean))
($define y (var boolean))
($define z (var boolean))

($define ∧ ($lambda (x y) ∧-unimpl))
($define '($type (∧ x y)) boolean)
($define ∨ ($lambda (x y) ∨-unimpl))
($define '($type (∨ x y)) boolean)
($define ¬ ($lambda (x) ¬-unimpl))
($define '($type (¬ x)) boolean)
($define ⇒ ($lambda (x y) ⇒-unimpl))
($define '($type (⇒ x y)) boolean)
($define '($type (= x y)) boolean)

($define '(∧ ⊤ ⊤) #T)
($define '(⇒ ⊤ ⊤) #T)

($define-law mat-impl
  (= (⇒ x y) (∨ (¬ x) y))
  (= (∨ (¬ x) y) (⇒ x y)))
($define-law duality
  (= (¬ (∧ x y)) (∨ (¬ x) (¬ y))))
($define-law disj-assoc
  (= (∨ (∨ x y) z) (∨ x (∨ y z))))
;($define-law eq-symm    (= (= x y) (= y x))
($define-law eq-trans
  (⇒ (∧ (= x y) (= y z)) (= x z)))


; The first law of portation
; (= (⇒ (∧ a b) c)
;    (⇒ a (⇒ b c)))
($let ((a (var boolean))
       (b (var boolean))
       (c (var boolean)))

  ($calculate

   (= (⇒ (∧ a b) c)
      (∨ (¬ (∧ a b)) c))     : (law mat-impl)

   (= (∨ (¬ (∧ a b)) c)
      (∨ (∨ (¬ a) (¬ b)) c)) : (transparency 1 (law duality))

   (= (∨ (∨ (¬ a) (¬ b)) c)
      (∨ (¬ a) (∨ (¬ b) c))) : (law disj-assoc)

   (= (∨ (¬ a) (∨ (¬ b) c))
      (⇒ a (∨ (¬ b) c)))     : (law mat-impl)

   (= (⇒ a (∨ (¬ b) c))
      (⇒ a (⇒ b c)))         : (transparency 2 (law mat-impl))


   (∧ (= (∨ (¬ a) (∨ (¬ b) c))
         (⇒ a (∨ (¬ b) c)))
      (= (⇒ a (∨ (¬ b) c))
         (⇒ a (⇒ b c))))        : eval

   (⇒ (∧ (= (∨ (¬ a) (∨ (¬ b) c))
            (⇒ a (∨ (¬ b) c)))
         (= (⇒ a (∨ (¬ b) c))
            (⇒ a (⇒ b c))))
      (= (∨ (¬ a) (∨ (¬ b) c))
         (⇒ a (⇒ b c))))           : (law eq-trans)


   (= (∨ (¬ a) (∨ (¬ b) c))    ; This is failing because (∧ ⊤ ⊤) is also bound,
                               ; This is a flaw of the environment term-bindings
                               ; design.
      (⇒ a (⇒ b c)))         : (consistency '(⇒ (∧ (= (∨ (¬ a) (∨ (¬ b) c))
                                                      (⇒ a (∨ (¬ b) c)))
                                                   (= (⇒ a (∨ (¬ b) c))
                                                      (⇒ a (⇒ b c))))
                                                (= (∨ (¬ a) (∨ (¬ b) c))
                                                   (⇒ a (⇒ b c)))))

   (∧ (= (∨ (∨ (¬ a) (¬ b)) c)
         (∨ (¬ a) (∨ (¬ b) c)))
      (= (∨ (¬ a) (∨ (¬ b) c))
         (⇒ a (⇒ b c))))         : eval

   (⇒ (∧ (= (∨ (∨ (¬ a) (¬ b)) c)
            (∨ (¬ a) (∨ (¬ b) c)))
         (= (∨ (¬ a) (∨ (¬ b) c))
            (⇒ a (⇒ b c))))
      (= (∨ (∨ (¬ a) (¬ b)) c)
         (⇒ a (⇒ b c))))           : (law eq-trans)

   (= (∨ (∨ (¬ a) (¬ b)) c)
      (⇒ a (⇒ b c)))        : (consistency '(⇒ (∧ (= (∨ (∨ (¬ a) (¬ b)) c)
                                                     (∨ (¬ a) (∨ (¬ b) c)))
                                                  (= (∨ (¬ a) (∨ (¬ b) c))
                                                     (⇒ a (⇒ b c))))
                                               (= (∨ (∨ (¬ a) (¬ b)) c)
                                                  (⇒ a (⇒ b c)))))


   (∧ (= (∨ (¬ (∧ a b)) c)
         (∨ (∨ (¬ a) (¬ b)) c))
      (= (∨ (∨ (¬ a) (¬ b)) c)
         (⇒ a (⇒ b c))))        : eval

   (⇒ (∧ (= (∨ (¬ (∧ a b)) c)
            (∨ (∨ (¬ a) (¬ b)) c))
         (= (∨ (∨ (¬ a) (¬ b)) c)
            (⇒ a (⇒ b c))))
      (= (∨ (¬ (∧ a b)) c)
         (⇒ a (⇒ b c))))           : (law eq-trans)

   (= (∨ (¬ (∧ a b)) c)
      (⇒ a (⇒ b c)))    : (consistency '(⇒ (∧ (= (∨ (¬ (∧ a b)) c)
                                                 (∨ (∨ (¬ a) (¬ b)) c))
                                              (= (∨ (∨ (¬ a) (¬ b)) c)
                                                 (⇒ a (⇒ b c))))
                                           (= (∨ (¬ (∧ a b)) c)
                                              (⇒ a (⇒ b c)))))


   (∧ (= (⇒ (∧ a b) c)
         (∨ (¬ (∧ a b)) c))
      (= (∨ (¬ (∧ a b)) c)
         (⇒ a (⇒ b c))))    : eval

   (⇒ (∧ (= (⇒ (∧ a b) c)
            (∨ (¬ (∧ a b)) c))
         (= (∨ (¬ (∧ a b)) c)
            (⇒ a (⇒ b c))))
      (= (⇒ (∧ a b) c)
         (⇒ a (⇒ b c))))       : (law eq-trans)

   ; TODO: Why is this taking so long?
   (= (⇒ (∧ a b) c)
      (⇒ a (⇒ b c)))  : (consistency '(⇒ (∧ (= (⇒ (∧ a b) c)
                                               (∨ (¬ (∧ a b)) c))
                                            (= (∨ (¬ (∧ a b)) c)
                                               (⇒ a (⇒ b c))))
                                         (= (⇒ (∧ a b) c)
                                            (⇒ a (⇒ b c)))))

  ))
