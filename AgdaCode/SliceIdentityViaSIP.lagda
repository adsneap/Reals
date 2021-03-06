Martin Escardo, 6th December 2018

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module SliceIdentityViaSIP
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

open import Slice ๐ฃ

_โ_ : ๐ X โ ๐ X โ ๐ฃ โ ๐ค ฬ
l โ m = ฮฃ e ๊ source l โ source m , family l โก family m โ โ e โ

๐-Id : is-univalent ๐ฃ โ (l m : ๐ X) โ (l โก m) โ (l โ m)
๐-Id ua = โก-is-โโ'
 where
  open gsip
        ๐ฃ (๐ฃ โ ๐ค) ua
        (ฮป P โ P โ X)
        (ฮป {l m (f , e) โ family l โก family m โ f})
        (ฮป l โ refl)
        (ฮป P ฮต ฮด โ id)
        (ฮป A ฯ ฯ โ refl-left-neutral)

โ-gives-โก : is-univalent ๐ฃ โ {l m : ๐ X} โ (l โ m) โ l โก m
โ-gives-โก ua = โ ๐-Id ua _ _ โโปยน

_โยท_ : ๐ X โ ๐ X โ ๐ฃ โ ๐ค ฬ
l โยท m = ฮฃ e ๊ source l โ source m , family l โผ family m โ โ e โ

๐-Idยท : is-univalent ๐ฃ
      โ funext ๐ฃ ๐ค
      โ (l m : ๐ X) โ (l โก m) โ (l โยท m)
๐-Idยท ua fe l m = (๐-Id ua l m) โ (ฮฃ-cong (ฮป e โ โ-funext fe (family l) (family m โ โ e โ)))

\end{code}
