Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module MGS-Unique-Existence where

open import MGS-Subsingleton-Theorems public

β! : {X : π€ Μ } β (X β π₯ Μ ) β π€ β π₯ Μ
β! A = is-singleton (Ξ£ A)

-β! : {π€ π₯ : Universe} (X : π€ Μ ) (Y : X β π₯ Μ ) β π€ β π₯ Μ
-β! X Y = β! Y

syntax -β! A (Ξ» x β b) = β! x κ A , b

β!-is-subsingleton : {X : π€ Μ } (A : X β π₯ Μ )
                   β dfunext (π€ β π₯) (π€ β π₯)
                   β is-subsingleton (β! A)

β!-is-subsingleton A fe = being-singleton-is-subsingleton fe

unique-existence-gives-weak-unique-existence : {X : π€ Μ } (A : X β π₯ Μ )

  β (β! x κ X , A x)
  β (Ξ£ x κ X , A x) Γ ((x y : X) β A x β A y β x β‘ y)

unique-existence-gives-weak-unique-existence A s = center (Ξ£ A) s , u
 where
  u : β x y β A x β A y β x β‘ y
  u x y a b = ap prβ (singletons-are-subsingletons (Ξ£ A) s (x , a) (y , b))

weak-unique-existence-gives-unique-existence-sometimes : {X : π€ Μ } (A : X β π₯ Μ ) β

    ((x : X) β is-subsingleton (A x))

  β ((Ξ£ x κ X , A x) Γ ((x y : X) β A x β A y β x β‘ y))
  β (β! x κ X , A x)

weak-unique-existence-gives-unique-existence-sometimes A i ((x , a) , u) = (x , a) , Ο
 where
  Ο : (Ο : Ξ£ A) β x , a β‘ Ο
  Ο (y , b) = to-subtype-β‘ i (u x y a b)

β-is-nno : hfunext π€β π€
         β (Y : π€ Μ ) (yβ : Y) (g : Y β Y)
         β β! h κ (β β Y), (h 0 β‘ yβ) Γ (h β succ β‘ g β h)

β-is-nno {π€} hfe Y yβ g = Ξ³
 where

  fe : dfunext π€β π€
  fe = hfunext-gives-dfunext hfe

  lemmaβ : (h : β β Y) β ((h 0 β‘ yβ) Γ (h β succ βΌ g β h)) β (h βΌ β-iteration Y yβ g)
  lemmaβ h = r , s , Ξ·
   where
    s : (h 0 β‘ yβ) Γ (h β succ βΌ g β h) β h βΌ β-iteration Y yβ g
    s (p , K) 0 = p
    s (p , K) (succ n) = h (succ n)                  β‘β¨ K n β©
                         g (h n)                     β‘β¨ ap g (s (p , K) n) β©
                         g (β-iteration Y yβ g n)    β‘β¨ refl _ β©
                         β-iteration Y yβ g (succ n) β

    r : codomain s β domain s
    r H = H 0 , (Ξ» n β h (succ n)                  β‘β¨ H (succ n) β©
                       β-iteration Y yβ g (succ n) β‘β¨ refl _ β©
                       g (β-iteration Y yβ g n)    β‘β¨ ap g ((H n)β»ΒΉ) β©
                       g (h n )                    β)

    remark : β n H β prβ (r H) n β‘ H (succ n) β (refl _ β ap g ((H n)β»ΒΉ))
    remark n H = refl _

    Ξ· : (z : (h 0 β‘ yβ) Γ (h β succ βΌ g β h)) β r (s z) β‘ z
    Ξ· (p , K) = q
     where
      v = Ξ» n β
       s (p , K) (succ n) β (refl _ β ap g ((s (p , K) n)β»ΒΉ))                  β‘β¨ refl _ β©
       K n β  ap g (s (p , K) n) β (refl _ β ap g ((s (p , K) n)β»ΒΉ))           β‘β¨ i   n β©
       K n β  ap g (s (p , K) n) β  ap g ((s (p , K) n) β»ΒΉ)                    β‘β¨ ii  n β©
       K n β (ap g (s (p , K) n) β  ap g ((s (p , K) n) β»ΒΉ))                   β‘β¨ iii n β©
       K n β (ap g (s (p , K) n) β (ap g  (s (p , K) n))β»ΒΉ)                    β‘β¨ iv  n β©
       K n β refl _                                                            β‘β¨ refl _ β©
       K n                                                                     β
        where
         i   = Ξ» n β ap (K n β ap g (s (p , K) n) β_)
                        (refl-left {_} {_} {_} {_} {ap g ((s (p , K) n)β»ΒΉ)})
         ii  = Ξ» n β βassoc (K n) (ap g (s (p , K) n)) (ap g ((s (p , K) n)β»ΒΉ))
         iii = Ξ» n β ap (Ξ» - β K n β (ap g (s (p , K) n) β -)) (apβ»ΒΉ g (s (p , K) n) β»ΒΉ)
         iv  = Ξ» n β ap (K n β_) (β»ΒΉ-rightβ (ap g (s (p , K) n)))

      q = r (s (p , K))                                                      β‘β¨ refl _ β©
          p , (Ξ» n β s (p , K) (succ n) β (refl _ β ap g ((s (p , K) n)β»ΒΉ))) β‘β¨ vi β©
          p , K                                                              β
       where
         vi = ap (p ,_) (fe v)

  lemmaβ = Ξ» h β (h 0 β‘ yβ) Γ (h β succ β‘ g β h) ββ¨ i h β©
                 (h 0 β‘ yβ) Γ (h β succ βΌ g β h) ββ¨ lemmaβ h β©
                 (h βΌ β-iteration Y yβ g)        ββ¨ ii h β©
                 (h β‘ β-iteration Y yβ g)        β
   where
    i  = Ξ» h β Ξ£-retract (Ξ» _ β β-gives-β (happly (h β succ) (g β h) , hfe _ _))
    ii = Ξ» h β β-gives-β· (happly h (β-iteration Y yβ g) , hfe _ _)

  lemmaβ : (Ξ£ h κ (β β Y), (h 0 β‘ yβ) Γ (h β succ β‘ g β h))
         β (Ξ£ h κ (β β Y), h β‘ β-iteration Y yβ g)

  lemmaβ = Ξ£-retract lemmaβ

  Ξ³ : is-singleton (Ξ£ h κ (β β Y), (h 0 β‘ yβ) Γ (h β succ β‘ g β h))
  Ξ³ = retract-of-singleton lemmaβ
                           (singleton-types-are-singletons (β β Y) (β-iteration Y yβ g))

module finite-types (hfe : hfunext π€β π€β) where

 fin :  β! Fin κ (β β π€β Μ )
               , (Fin 0 β‘ π)
               Γ (Fin β succ β‘ Ξ» n β Fin n + π)

 fin = β-is-nno hfe (π€β Μ ) π (_+ π)

 Fin : β β π€β Μ
 Fin = prβ (center _ fin)

 Fin-equationβ : Fin 0 β‘ π
 Fin-equationβ = refl _

 Fin-equation-succ : Fin β succ β‘ Ξ» n β Fin n + π
 Fin-equation-succ = refl _

 Fin-equation-succ' : (n : β) β Fin (succ n) β‘ Fin n + π
 Fin-equation-succ' n = refl _

 Fin-equationβ : Fin 1 β‘ π + π
 Fin-equationβ = refl _

 Fin-equationβ : Fin 2 β‘ (π + π) + π
 Fin-equationβ = refl _

 Fin-equationβ : Fin 3 β‘ ((π + π) + π) + π
 Fin-equationβ = refl _

infixr -1 -β!

\end{code}
