Tom de Jong 22nd May 2019

The lifting of a set is a set.
We need to assume propositional extensionality for the fixed universe ð£ of
propositions and two instances of function extensionality.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module LiftingSet
  (ð£ : Universe) -- fix a universe for the propositions
  where

open import UF-Subsingletons
open import UF-Base
open import UF-Retracts
open import UF-FunExt
open import UF-Subsingletons-FunExt
open import Lifting ð£

lifting-of-set-is-set : funext ð£ ð¤
                      â funext ð£ ð£
                      â propext ð£
                      â (X : ð¤ Ì )
                      â is-set X
                      â is-set (ð X)
lifting-of-set-is-set fe' fe pe  X i {l} {m} p q  = retract-of-prop r j p q
 where
  r : Î£ has-section
  r = (to-Î£-â¡ , from-Î£-â¡ , tofrom-Î£-â¡)

  j : is-prop (Î£ (Î» pâ â transport (Î» P â (P â X) Ã is-prop P)
               pâ (prâ l) â¡ prâ m))
  j = Î£-is-prop
       (identifications-of-props-are-props pe fe (is-defined m)
        (being-defined-is-prop m) (is-defined l))
       (Î» d â Ã-is-set (Î -is-set fe' Î» _ â i)
                       (props-are-sets (being-prop-is-prop fe)))

\end{code}
