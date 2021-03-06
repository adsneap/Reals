Our Spartan (intensional) Martin-LΓΆf type theory has the empty type β,
the unit type π, two-point-type π, natural numbers β, product types Ξ ,
sum types Ξ£ (and hence binary product types _Γ_), sum types _+_,
identity types _β‘_, and universes π€, π₯, π¦, ....

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module SpartanMLTT where

open import Empty           public
open import Unit            public
open import Two             public
open import NaturalNumbers  public
open import Plus            public
open import Pi              public
open import Sigma           public
open import Universes       public
open import Id              public

open import GeneralNotation public

\end{code}
