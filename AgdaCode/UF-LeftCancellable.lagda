Left cancellable maps.

The definition is given in UF-Base. Here we prove things about them.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-LeftCancellable where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Retracts
open import UF-Equiv

left-cancellable-reflects-is-prop : {X : π€ Μ } {Y : π₯ Μ } (f : X β Y)
                                 β left-cancellable f β is-prop Y β is-prop X
left-cancellable-reflects-is-prop f lc i x x' = lc (i (f x) (f x'))

section-lc : {X : π€ Μ } {A : π₯ Μ } (s : X β A) β is-section s β left-cancellable s
section-lc {π€} {π₯} {X} {Y} s (r , rs) {x} {y} p = (rs x)β»ΒΉ β ap r p β rs y

is-equiv-lc : {X : π€ Μ } {Y : π₯ Μ } (f : X β Y) β is-equiv f β left-cancellable f
is-equiv-lc f (_ , hasr) = section-lc f hasr

left-cancellable-closed-under-β : {X : π€ Μ } {Y : π₯ Μ } {Z : π¦ Μ } (f : X β Y) (g : Y β Z)
                                β left-cancellable f β left-cancellable g β left-cancellable (g β f)
left-cancellable-closed-under-β f g lcf lcg = lcf β lcg

NatΞ£-lc : {X : π€ Μ } {A : X β π₯ Μ } {B : X β π¦ Μ } (f : Nat A B)
        β ((x : X) β left-cancellable(f x))
        β left-cancellable (NatΞ£ f)
NatΞ£-lc {π€} {π₯} {π¦} {X} {A} {B} f flc {x , a} {x' , a'} p = to-Ξ£-β‘ (ap prβ p , Ξ³)
 where
  Ξ³ : transport A (ap prβ p) a β‘ a'
  Ξ³ = flc x' (f x' (transport A (ap prβ p) a) β‘β¨ nat-transport f (ap prβ p) β©
              transport B (ap prβ p) (f x a)  β‘β¨ from-Ξ£-β‘' p β©
              f x' a'                         β)

NatΞ -lc : {X : π€ Μ } {A : X β π₯ Μ } {B : X β π¦ Μ } (f : Nat A B)
        β ((x : X) β left-cancellable(f x))
        β {g g' : Ξ  A} β NatΞ  f g β‘ NatΞ  f g' β g βΌ g'
NatΞ -lc f flc {g} {g'} p x = flc x (happly p x)

\end{code}

Sometimes the type of left cancellable maps is useful (but more often
the type of embeddings, defined elsewhere, is useful).

\begin{code}

_β£_ : π€ Μ β π₯ Μ β π€ β π₯ Μ
X β£ Y =  Ξ£ f κ (X β Y) , left-cancellable f

β_β : {X : π€ Μ } {Y : π₯ Μ } β X β£ Y β X β Y
β f , _ β = f

infix 0 _β£_

\end{code}
