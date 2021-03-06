Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module MGS-Function-Graphs where

open import MGS-Yoneda public

module function-graphs
        (ua : Univalence)
        {π€ π₯ : Universe}
        (X : π€ Μ )
        (A : X β π₯ Μ )
       where

 hfe : global-hfunext
 hfe = univalence-gives-global-hfunext ua

 fe : global-dfunext
 fe = univalence-gives-global-dfunext ua

 Function : π€ β π₯ Μ
 Function = (x : X) β A x

 Relation : π€ β (π₯ βΊ) Μ
 Relation = (x : X) β A x β π₯ Μ

 is-functional : Relation β π€ β π₯ Μ
 is-functional R = (x : X) β β! a κ A x , R x a

 being-functional-is-subsingleton : (R : Relation)
                                  β is-subsingleton (is-functional R)

 being-functional-is-subsingleton R = Ξ -is-subsingleton fe
                                       (Ξ» x β β!-is-subsingleton (R x) fe)

 Functional-Relation : π€ β (π₯ βΊ) Μ
 Functional-Relation = Ξ£ R κ Relation , is-functional R

 Ο : Function β Relation
 Ο f = Ξ» x a β f x β‘ a

 Ο-is-embedding : is-embedding Ο
 Ο-is-embedding = NatΞ -is-embedding hfe hfe
                   (Ξ» x β π (A x))
                   (Ξ» x β π¨-is-embedding ua (A x))
  where

   Ο : (x : X) β A x β (A x β π₯ Μ )
   Ο x a b = a β‘ b

   remarkβ : Ο β‘ Ξ» x β π (A x)
   remarkβ = refl _

   remarkβ : Ο β‘ NatΞ  Ο
   remarkβ = refl _

 Ο-is-functional : (f : Function) β is-functional (Ο f)
 Ο-is-functional f = Ο
  where
   Ο : (x : X) β β! a κ A x , f x β‘ a
   Ο x = singleton-types'-are-singletons (A x) (f x)

 Ξ : Function β Functional-Relation
 Ξ f = Ο f , Ο-is-functional f

 Ξ¦ : Functional-Relation β Function
 Ξ¦ (R , Ο) = Ξ» x β prβ (center (Ξ£ a κ A x , R x a) (Ο x))

 Ξ-is-equiv : is-equiv Ξ
 Ξ-is-equiv = invertibles-are-equivs Ξ (Ξ¦ , Ξ· , Ξ΅)
  where
   Ξ· : Ξ¦ β Ξ βΌ id
   Ξ· = refl

   Ξ΅ : Ξ β Ξ¦ βΌ id
   Ξ΅ (R , Ο) = a
    where
     f : Function
     f = Ξ¦ (R , Ο)

     e : (x : X) β R x (f x)
     e x = prβ (center (Ξ£ a κ A x , R x a) (Ο x))

     Ο : (x : X) β Nat (π¨ (f x)) (R x)
     Ο x = π (R x) (f x) (e x)

     Ο-is-fiberwise-equiv : (x : X) β is-fiberwise-equiv (Ο x)
     Ο-is-fiberwise-equiv x = universal-fiberwise-equiv (R x) (Ο x) (f x) (Ο x)

     d : (x : X) (a : A x) β (f x β‘ a) β R x a
     d x a = Ο x a , Ο-is-fiberwise-equiv x a

     c : (x : X) (a : A x) β (f x β‘ a) β‘ R x a
     c x a = EqβId (ua π₯) _ _ (d x a)

     b : Ο f β‘ R
     b = fe (Ξ» x β fe (c x))

     a : (Ο f , Ο-is-functional f) β‘ (R , Ο)
     a = to-subtype-β‘ being-functional-is-subsingleton b

 functions-amount-to-functional-relations : Function β Functional-Relation
 functions-amount-to-functional-relations = Ξ , Ξ-is-equiv

\end{code}
