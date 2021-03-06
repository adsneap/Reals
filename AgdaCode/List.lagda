Martin Escardo, January 2021.

It is possible to work with lists *defined* from the ingredients of
our Spartan MLTT (see the module Fin.lagda). For the moment we are
Athenian in this respect.

\begin{code}

{-# OPTIONS --without-K --safe --exact-split #-}

module List where

open import SpartanMLTT

data List {๐ค} (X : ๐ค ฬ ) : ๐ค ฬ  where
 [] : List X
 _โท_ : X โ List X โ List X

infixr 3 _โท_

equal-heads : {X : ๐ค ฬ } {x y : X} {s t : List X}
            โ x โท s โก y โท t
            โ x โก y
equal-heads refl = refl

equal-tails : {X : ๐ค ฬ } {x y : X} {s t : List X}
            โ x โท s โก y โท t
            โ s โก t
equal-tails {๐ค} {X} refl = refl

[_] : {X : ๐ค ฬ } โ X โ List X
[ x ] = x โท []

_++_ : {X : ๐ค ฬ } โ List X โ List X โ List X
[]      ++ t = t
(x โท s) ++ t = x โท (s ++ t)

infixr 4 _++_

[]-right-neutral : {X : ๐ค ฬ } (s : List X) โ s โก s ++ []
[]-right-neutral []      = refl
[]-right-neutral (x โท s) = ap (x โท_) ([]-right-neutral s)

++-assoc : {X : ๐ค ฬ } โ associative (_++_ {๐ค} {X})
++-assoc []      t u = refl
++-assoc (x โท s) t u = ap (x โท_) (++-assoc s t u)

foldr : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } โ (X โ Y โ Y) โ Y โ List X โ Y
foldr _ยท_ ฮต []       = ฮต
foldr _ยท_ ฮต (x โท xs) = x ยท foldr _ยท_ ฮต xs

map : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } โ (X โ Y) โ List X โ List Y
map f []       = []
map f (x โท xs) = f x โท map f xs

_<$>_ = map

\end{code}

The above is all we need about lists for the moment, in the module
FreeGroups.lagda.
