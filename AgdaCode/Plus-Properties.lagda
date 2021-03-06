Properties of the disjoint sum _+_ of types.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Plus-Properties where

open import Plus
open import Universes
open import Negation
open import Id
open import Empty
open import Unit
open import Unit-Properties

+-commutative : {A : ๐ค ฬ } {B : ๐ฅ ฬ } โ A + B โ B + A
+-commutative = cases inr inl

+disjoint : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } {x : X} {y : Y} โ ยฌ (inl x โก inr y)
+disjoint {๐ค} {๐ฅ} {X} {Y} p = ๐-is-not-๐ q
 where
  f : X + Y โ ๐คโ ฬ
  f (inl x) = ๐
  f (inr y) = ๐

  q : ๐ โก ๐
  q = ap f p


+disjoint' : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } {x : X} {y : Y} โ ยฌ (inr y โก inl x)
+disjoint' p = +disjoint (p โปยน)

inl-lc : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } {x x' : X} โ inl {๐ค} {๐ฅ} {X} {Y} x โก inl x' โ x โก x'
inl-lc refl = refl

inr-lc : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } {y y' : Y} โ inr {๐ค} {๐ฅ} {X} {Y} y โก inr y' โ y โก y'
inr-lc refl = refl

equality-cases : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } {A : ๐ฆ ฬ } (z : X + Y)
               โ ((x : X) โ z โก inl x โ A) โ ((y : Y) โ z โก inr y โ A) โ A
equality-cases (inl x) f g = f x refl
equality-cases (inr y) f g = g y refl

Cases-equality-l : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } {A : ๐ฆ ฬ } (f : X โ A) (g : Y โ A)
                 โ (z : X + Y) (x : X) โ z โก inl x โ Cases z f g โก f x
Cases-equality-l f g .(inl x) x refl = refl

Cases-equality-r : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } {A : ๐ฆ ฬ } (f : X โ A) (g : Y โ A)
                 โ (z : X + Y) (y : Y) โ z โก inr y โ Cases z f g โก g y
Cases-equality-r f g .(inr y) y refl = refl

Left-fails-gives-right-holds : {P : ๐ค ฬ } {Q : ๐ฅ ฬ } โ P + Q โ ยฌ P โ Q
Left-fails-gives-right-holds (inl p) u = ๐-elim (u p)
Left-fails-gives-right-holds (inr q) u = q

Right-fails-gives-left-holds : {P : ๐ค ฬ } {Q : ๐ฅ ฬ } โ P + Q โ ยฌ Q โ P
Right-fails-gives-left-holds (inl p) u = p
Right-fails-gives-left-holds (inr q) u = ๐-elim (u q)

open import Unit
open import Sigma
open import GeneralNotation

inl-preservation : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } (f : X + ๐ {๐ฆ}  โ Y + ๐ {๐ฃ})
                 โ f (inr โ) โก inr โ
                 โ left-cancellable f
                 โ (x : X) โ ฮฃ y ๊ Y , f (inl x) โก inl y
inl-preservation {๐ค} {๐ฅ} {๐ฆ} {๐ฃ} {X} {Y} f p l x = ฮณ x (f (inl x)) refl
 where
  ฮณ : (x : X) (z : Y + ๐) โ f (inl x) โก z โ ฮฃ y ๊ Y , z โก inl y
  ฮณ x (inl y) q = y , refl
  ฮณ x (inr โ) q = ๐-elim (+disjoint (l r))
   where
    r : f (inl x) โก f (inr โ)
    r = q โ p โปยน

+functor : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } {A : ๐ฆ ฬ } {B : ๐ฃ ฬ }
         โ (X โ A) โ (Y โ B) โ X + Y โ A + B
+functor f g (inl x) = inl (f x)
+functor f g (inr y) = inr (g y)

\end{code}
