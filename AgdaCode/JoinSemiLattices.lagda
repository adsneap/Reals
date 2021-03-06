Tom de Jong, 24 January 2022
(Refactored from FreeJoinSemiLattice.lagda)

We define join-semilattices using a record. We also introduce convenient helpers
and syntax for reasoning about the order β and we construct finite joins using
the least element and binary joins.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module JoinSemiLattices where

open import SpartanMLTT

open import Fin

open import UF-Subsingletons

record JoinSemiLattice (π₯ π£ : Universe) : π€Ο where
  field
    L : π₯ Μ
    L-is-set : is-set L
    _β_ : L β L β π£ Μ
    β-is-prop-valued : (x y : L) β is-prop (x β y)
    β-is-reflexive : (x : L) β x β x
    β-is-transitive : (x y z : L) β x β y β y β z β x β z
    β-is-antisymmetric : (x y : L) β x β y β y β x β x β‘ y
    β₯ : L
    β₯-is-least : (x : L) β β₯ β x
    _β¨_ : L β L β L
    β¨-is-upperboundβ : (x y : L) β x β (x β¨ y)
    β¨-is-upperboundβ : (x y : L) β y β (x β¨ y)
    β¨-is-lowerbound-of-upperbounds : (x y z : L) β x β z β y β z β (x β¨ y) β z

  transitivity' : (x : L) {y z : L}
                β x β y β y β z β x β z
  transitivity' x {y} {z} = β-is-transitive x y z

  syntax transitivity' x u v = x ββ¨ u β© v
  infixr 0 transitivity'

  reflexivity' : (x : L) β x β x
  reflexivity' x = β-is-reflexive x

  syntax reflexivity' x = x ββ
  infix 1 reflexivity'

  β‘-to-β : {x y : L} β x β‘ y β x β y
  β‘-to-β {x} {x} refl = reflexivity' x

  β¨βΏ : {n : β} β (Fin n β L) β L
  β¨βΏ {zero}   e = β₯
  β¨βΏ {succ m} e = (β¨βΏ (e β suc)) β¨ (e π)

  β¨βΏ-is-upperbound : {n : β} (Ο : Fin n β L)
                   β (k : Fin n) β Ο k β β¨βΏ Ο
  β¨βΏ-is-upperbound {succ n} Ο π       = β¨-is-upperboundβ _ _
  β¨βΏ-is-upperbound {succ n} Ο (suc k) = Ο (suc k)    ββ¨ IH β©
                                        β¨βΏ (Ο β suc) ββ¨ β¨-is-upperboundβ _ _ β©
                                        β¨βΏ Ο         ββ
   where
    IH = β¨βΏ-is-upperbound (Ο β suc) k

  β¨βΏ-is-lowerbound-of-upperbounds : {n : β} (Ο : Fin n β L)
                                    (x : L)
                                  β ((k : Fin n) β Ο k β x)
                                  β β¨βΏ Ο β x
  β¨βΏ-is-lowerbound-of-upperbounds {zero}   Ο x ub = β₯-is-least x
  β¨βΏ-is-lowerbound-of-upperbounds {succ n} Ο x ub =
   β¨-is-lowerbound-of-upperbounds _ _ _ u v
    where
     u : β¨βΏ (Ο β suc) β x
     u = β¨βΏ-is-lowerbound-of-upperbounds {n} (Ο β suc) x (ub β suc)
     v : Ο π β x
     v = ub π

\end{code}
