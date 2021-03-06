Martin Escardo 7th December 2018.

Characterization of equality in the lifting via the structure of
identity principle.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module LiftingIdentityViaSIP
        (๐ฃ : Universe)
        {๐ค : Universe}
        {X : ๐ค ฬ }
       where

open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-Univalence
open import UF-UA-FunExt
open import UF-StructureIdentityPrinciple

open import Lifting ๐ฃ

_โ_ : ๐ X โ ๐ X โ ๐ฃ โ ๐ค ฬ
l โ m = ฮฃ e ๊ is-defined l โ is-defined m , value l โก value m โ โ e โ

๐-Id : is-univalent ๐ฃ โ (l m : ๐ X) โ (l โก m) โ (l โ m)
๐-Id ua = โก-is-โโ'
 where
  open gsip-with-axioms'
        ๐ฃ (๐ฃ โ ๐ค) (๐ฃ โ ๐ค) ๐ฃ ua
        (ฮป P โ P โ X)
        (ฮป P s โ is-prop P)
        (ฮป P s โ being-prop-is-prop (univalence-gives-funext ua))
        (ฮป {l m (f , e) โ prโ l โก prโ m โ f})
        (ฮป l โ refl)
        (ฮป P ฮต ฮด โ id)
        (ฮป A ฯ ฯ โ refl-left-neutral)

โ-gives-โก : is-univalent ๐ฃ โ {l m : ๐ X} โ (l โ m) โ l โก m
โ-gives-โก ua = โ ๐-Id ua _ _ โโปยน

\end{code}

When dealing with functions it is often more convenient to work with
pointwise equality, and hence we also consider:

\begin{code}

_โยท_ : ๐ X โ ๐ X โ ๐ฃ โ ๐ค ฬ
l โยท m = ฮฃ e ๊ is-defined l โ is-defined m , value l โผ value m โ โ e โ

๐-Idยท : is-univalent ๐ฃ
      โ funext ๐ฃ ๐ค
      โ (l m : ๐ X) โ (l โก m) โ (l โยท m)
๐-Idยท ua fe l m = (๐-Id ua l m) โ (ฮฃ-cong (ฮป e โ โ-funext fe (value l) (value m โ โ e โ)))

\end{code}
