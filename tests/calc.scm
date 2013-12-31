($define ∧ #;(list "∧") ($lambda (x y) ($if x ($if y #T #F) #F)))
($define ∨ (list "∨") #;($lambda (x y) ($if x #T ($if y #T #F))))
($define ¬ (list "¬") #;($lambda (x) ($if x #F #T)))
($define ⇒ #;(list "⇒") ($lambda (x y) (∨ (¬ x) y)))
($define '(= #T #T) #T)
($define '(= #T #F) #F)
($define '(⇒ #T #T) #T)
($define '(⇒ #T #F) #F)

($define boolean (list "boolean type"))
($define '(type-values boolean) (list #T #F))
($define '($type ∨) applicative)
($define '($type ⇒) applicative)

($define mat-impl
  (make-binding
   ($let (('($type x) boolean)
          ('($type y) boolean))
     '(= (⇒ x y) (∨ (¬ x) y)))
   #T))

($define duality
  (make-binding
   ($let (('($type x) boolean)
          ('($type y) boolean))
     '(= (¬ (∧ x y)) (∨ (¬ x) (¬ y))))
   #T))

($define disj-assoc
  (make-binding
   ($let (('($type x) boolean)
          ('($type y) boolean)
          ('($type z) boolean))
     '(= (∨ (∨ x y) z) (∨ x (∨ y z))))
   #T))

($define eq-symm
  (make-binding
   ($let (('($type x) boolean)
          ('($type y) boolean))
     '(= (= x y) (= y x)))
   #T))

($define eq-trans
  (make-binding
   ($let (('($type x) boolean)
          ('($type y) boolean)
          ('($type z) boolean))
     '(⇒ (∧ (= x y) (= y z))
         (= x z)))
   #T))

; The first law of portation
; (= (⇒ (∧ a b) c)
;    (⇒ a (⇒ b c)))
($let ((∧-use-type (make-binding
                    ($let (('($type x) boolean)
                           ('($type y) boolean))
                      '($type (∧ x y)))
                    boolean))
       (∨-use-type (make-binding
                    ($let (('($type x) boolean)
                           ('($type y) boolean))
                      '($type (∨ x y)))
                    boolean))
       (¬-use-type (make-binding
                    ($let (('($type x) boolean))
                      '($type (¬ x)))
                    boolean))
       (⇒-use-type (make-binding
                    ($let (('($type x) boolean)
                           ('($type y) boolean))
                      '($type (⇒ x y)))
                    boolean))
       (=-use-type (make-binding
                    ($let (('($type x) boolean)
                           ('($type y) boolean))
                      '($type (= x y)))
                    boolean))
       ('($type a) boolean)
       ('($type b) boolean)
       ('($type c) boolean))

  ($calculate

   ($type (∧ a b)) : (law ∧-use-type)

   (= (⇒ (∧ a b) c)
      (∨ (¬ (∧ a b)) c))     : (law mat-impl)

   (= (∨ (¬ (∧ a b)) c)
      (∨ (∨ (¬ a) (¬ b)) c)) : (transparency 1 (law duality))

   ($type (¬ a)) : (law ¬-use-type)
   ($type (¬ b)) : (law ¬-use-type)

   (= (∨ (∨ (¬ a) (¬ b)) c)
      (∨ (¬ a) (∨ (¬ b) c))) : (law disj-assoc)

   ($type (∨ (¬ b) c)) : (law ∨-use-type)

   (= (⇒ a (∨ (¬ b) c))
      (∨ (¬ a) (∨ (¬ b) c))) : (law mat-impl)

   ($type (⇒ a (∨ (¬ b) c))) : (law ⇒-use-type)
   ($type (∨ (¬ a) (∨ (¬ b) c))) : (law ∨-use-type)

   (= (= (⇒ a (∨ (¬ b) c))
         (∨ (¬ a) (∨ (¬ b) c)))
      (= (∨ (¬ a) (∨ (¬ b) c))
         (⇒ a (∨ (¬ b) c))))    : (law eq-symm)

   ($type (= (∨ (¬ a) (∨ (¬ b) c))
             (⇒ a (∨ (¬ b) c))))   : (law =-use-type)

   (= (∨ (¬ a) (∨ (¬ b) c))
      (⇒ a (∨ (¬ b) c)))    : (consistency '(= (= (⇒ a (∨ (¬ b) c))
                                                  (∨ (¬ a) (∨ (¬ b) c)))
                                               (= (∨ (¬ a) (∨ (¬ b) c))
                                                  (⇒ a (∨ (¬ b) c)))))

   (= (⇒ a (⇒ b c))
      (⇒ a (∨ (¬ b) c)))     : (transparency 2 (law mat-impl))

   ($type (⇒ b c)) : (law ⇒-use-type)
   ($type (⇒ a (⇒ b c))) : (law ⇒-use-type)

   (= (= (⇒ a (⇒ b c))
         (⇒ a (∨ (¬ b) c)))
      (= (⇒ a (∨ (¬ b) c))
         (⇒ a (⇒ b c))))    : (law eq-symm)

   ($type (= (⇒ a (∨ (¬ b) c))
             (⇒ a (⇒ b c))))   : (law =-use-type)

   (= (⇒ a (∨ (¬ b) c))
      (⇒ a (⇒ b c)))    : (consistency '(= (= (⇒ a (⇒ b c))
                                              (⇒ a (∨ (¬ b) c)))
                                           (= (⇒ a (∨ (¬ b) c))
                                              (⇒ a (⇒ b c)))))


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

   ($type (= (∨ (¬ a) (∨ (¬ b) c))
             (⇒ a (⇒ b c))))       : (law =-use-type)

   (= (∨ (¬ a) (∨ (¬ b) c))
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

   ($type (∨ (¬ a) (¬ b))) : (law ∨-use-type)
   ($type (∨ (∨ (¬ a) (¬ b)) c)) : (law ∨-use-type)

   (⇒ (∧ (= (∨ (∨ (¬ a) (¬ b)) c)
            (∨ (¬ a) (∨ (¬ b) c)))
         (= (∨ (¬ a) (∨ (¬ b) c))
            (⇒ a (⇒ b c))))
      (= (∨ (∨ (¬ a) (¬ b)) c)
         (⇒ a (⇒ b c))))           : (law eq-trans)

   ($type (= (∨ (∨ (¬ a) (¬ b)) c)
             (⇒ a (⇒ b c))))       : (law =-use-type)

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

   ($type (¬ (∧ a b))) : (law ¬-use-type)
   ($type (∨ (¬ (∧ a b)) c)) : (law ∨-use-type)

   (⇒ (∧ (= (∨ (¬ (∧ a b)) c)
            (∨ (∨ (¬ a) (¬ b)) c))
         (= (∨ (∨ (¬ a) (¬ b)) c)
            (⇒ a (⇒ b c))))
      (= (∨ (¬ (∧ a b)) c)
         (⇒ a (⇒ b c))))           : (law eq-trans)

   ($type (= (∨ (¬ (∧ a b)) c)
             (⇒ a (⇒ b c))))   : (law =-use-type)

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

   ($type (⇒ (∧ a b) c)) : (law ⇒-use-type)

   (⇒ (∧ (= (⇒ (∧ a b) c)
            (∨ (¬ (∧ a b)) c))
         (= (∨ (¬ (∧ a b)) c)
            (⇒ a (⇒ b c))))
      (= (⇒ (∧ a b) c)
         (⇒ a (⇒ b c))))       : (law eq-trans)

   ($type (= (⇒ (∧ a b) c)
             (⇒ a (⇒ b c)))) : (law =-use-type)

   ; TODO: Why is this taking so long?
   (term-equal? '(⇒ (∧ (= (⇒ (∧ a b) c)
                          (∨ (¬ (∧ a b)) c))
                       (= (∨ (¬ (∧ a b)) c)
                          (⇒ a (⇒ b c))))
                    (= (⇒ (∧ a b) c)
                       (⇒ a (⇒ b c))))
                '(⇒ (∧ (= (⇒ (∧ a b) c)
                          (∨ (¬ (∧ a b)) c))
                       (= (∨ (¬ (∧ a b)) c)
                          (⇒ a (⇒ b c))))
                    (= (⇒ (∧ a b) c)
                       (⇒ a (⇒ b c)))))       : eval

   ; TODO: Why is this taking so long?
#;
   ((= (⇒ (∧ a b) c)
       (⇒ a (⇒ b c)))  : (consistency '(⇒ (∧ (= (⇒ (∧ a b) c)
                                                (∨ (¬ (∧ a b)) c))
                                             (= (∨ (¬ (∧ a b)) c)
                                                (⇒ a (⇒ b c))))
                                          (= (⇒ (∧ a b) c)
                                             (⇒ a (⇒ b c)))))

       (here?) : here?)

  ))
