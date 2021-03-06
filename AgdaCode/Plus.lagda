The disjoint sum X + Y of two types X and Y.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Plus where

open import Plus-Type renaming (_+_ to infixr 1 _+_) public

dep-cases : {X : π€ Μ } {Y : π₯ Μ } {A : X + Y β π¦ Μ }
          β ((x : X) β A (inl x))
          β ((y : Y) β A (inr y))
          β ((z : X + Y) β A z)
dep-cases f g (inl x) = f x
dep-cases f g (inr y) = g y

cases : {X : π€ Μ } {Y : π₯ Μ } {A : π¦ Μ } β (X β A) β (Y β A) β X + Y β A
cases = dep-cases

\end{code}

Sometimes it is useful to have the arguments in a different order:

\begin{code}

Cases : {X : π€ Μ } {Y : π₯ Μ } {A : π¦ Μ } β X + Y β (X β A) β (Y β A) β A
Cases z f g = cases f g z

dep-Cases : {X : π€ Μ } {Y : π₯ Μ } (A : X + Y β π¦ Μ )
          β (z : X + Y)
          β ((x : X) β A (inl x))
          β ((y : Y) β A (inr y))
          β A z
dep-Cases {π€} {π₯} {π¦} {X} {Y} A z f g = dep-cases {π€} {π₯} {π¦} {X} {Y} {A} f g z

\end{code}

Added 4 March 2020 by Tom de Jong.

\begin{code}

dep-casesβ : {X : π€ Μ } {Y : π₯ Μ } {Z : π¦ Μ } {A : X + Y + Z β π£ Μ }
           β ((x : X) β A (inl x))
           β ((y : Y) β A (inr (inl y)))
           β ((z : Z) β A (inr (inr z)))
           β ((p : X + Y + Z) β A p)
dep-casesβ f g h (inl x)       = f x
dep-casesβ f g h (inr (inl y)) = g y
dep-casesβ f g h (inr (inr z)) = h z

casesβ : {X : π€ Μ } {Y : π₯ Μ } {Z : π¦ Μ } {A : π£ Μ }
       β (X β A) β (Y β A) β (Z β A) β X + Y + Z β A
casesβ = dep-casesβ

\end{code}
