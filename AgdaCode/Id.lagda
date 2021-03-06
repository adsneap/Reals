Identity type.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Id where

open import Universes
open import Pi

open import Identity-Type renaming (_โก_ to infix 0 _โก_) public

๐ป๐ฎ๐ป๐ต : {X : ๐ค ฬ } (x : X) โ x โก x
๐ป๐ฎ๐ป๐ต x = refl {_} {_} {x}

by-definition : {X : ๐ค ฬ } {x : X} โ x โก x
by-definition = refl

by-construction : {X : ๐ค ฬ } {x : X} โ x โก x
by-construction = refl

by-assumption : {X : ๐ค ฬ } {x : X} โ x โก x
by-assumption = refl

lhs : {X : ๐ค ฬ } {x y : X} โ x โก y โ X
lhs {๐ค} {X} {x} {y} p = x

rhs : {X : ๐ค ฬ } {x y : X} โ x โก y โ X
rhs {๐ค} {X} {x} {y} p = y

Id : {X : ๐ค ฬ } โ X โ X โ ๐ค ฬ
Id = _โก_

Jbased : {X : ๐ค ฬ } (x : X) (A : (y : X) โ x โก y โ ๐ฅ ฬ )
       โ A x refl โ (y : X) (r : x โก y) โ A y r
Jbased x A b .x refl = b

J : {X : ๐ค ฬ } (A : (x y : X) โ x โก y โ ๐ฅ ฬ )
  โ ((x : X) โ A x x refl) โ {x y : X} (r : x โก y) โ A x y r
J A f {x} {y} = Jbased x (A x) (f x) y


private

 transport' : {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ ) {x y : X}
            โ x โก y โ A x โ A y
 transport' A {x} {y} p a = Jbased x (ฮป y p โ A y) a y p


transport : {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ ) {x y : X}
          โ x โก y โ A x โ A y
transport A refl = id

_โ_ : {X : ๐ค ฬ } {x y z : X} โ x โก y โ y โก z โ x โก z
p โ q = transport (lhs p โก_) q p

_โปยน : {X : ๐ค ฬ } โ {x y : X} โ x โก y โ y โก x
p โปยน = transport (_โก lhs p) p refl

ap : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } (f : X โ Y) {x x' : X} โ x โก x' โ f x โก f x'
ap f p = transport (ฮป - โ f (lhs p) โก f -) p refl

back-transport : {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ ) {x y : X} โ x โก y โ A y โ A x
back-transport B p = transport B (p โปยน)

_โผ_ : {X : ๐ค ฬ } {A : X โ ๐ฅ ฬ } โ ((x : X) โ A x) โ ((x : X) โ A x) โ ๐ค โ ๐ฅ ฬ
f โผ g = โ x โ f x โก g x

\end{code}

Standard syntax for equality chain reasoning:

\begin{code}

_โกโจ_โฉ_ : {X : ๐ค ฬ } (x : X) {y z : X} โ x โก y โ y โก z โ x โก z
_ โกโจ p โฉ q = p โ q

_โ : {X : ๐ค ฬ } (x : X) โ x โก x
_โ _ = refl

\end{code}

Fixities:

\begin{code}

infix  3  _โปยน
infix  1 _โ
infixr 0 _โกโจ_โฉ_
infixl 2 _โ_
infix  4  _โผ_

\end{code}
