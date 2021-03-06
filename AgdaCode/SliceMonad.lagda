Martin Escardo, 6th December 2018

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module SliceMonad (π£ : Universe) where

open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-Univalence
open import UF-UA-FunExt

open import Slice π£
open import SliceIdentityViaSIP π£

\end{code}

Constructions:

\begin{code}

πΜ : {X : π€ Μ } {Y : π₯ Μ } β (X β Y) β π X β π Y
πΜ f (P , Ο) = P , f β Ο

_β― : {X : π€ Μ } {Y : π₯ Μ } β (X β π Y) β (π X β π Y)
_β― f (P , Ο ) = (Ξ£ p κ P , source (f (Ο p))) ,
                (Ξ» Ο β family (f (Ο (prβ Ο))) (prβ Ο))


ΞΌ : {X : π€ Μ } β π (π X) β π X
ΞΌ = id β―

πΜ-id : {X : π€ Μ }
      β πΜ id β‘ id
πΜ-id {π€} {X} = refl {π€ β (π£ βΊ)} {π X β π X}

πΜ-β : {X : π€ Μ } {Y : π₯ Μ } {Z : π¦ Μ } (f : X β Y) (g : Y β Z)
     β πΜ (g β f) β‘ πΜ g β πΜ f
πΜ-β f g = refl

Ξ·-natural : {X : π€ Μ } {Y : π₯ Μ } (f : X β Y)
          β Ξ· β f β‘ πΜ f β Ξ·
Ξ·-natural f = refl

Ξ·-naturalβΌ : {X : π€ Μ } {Y : π₯ Μ } (f : X β Y)
           β Ξ· β f βΌ πΜ f β Ξ·
Ξ·-naturalβΌ f _ = refl

ΞΌ-naturalβΌ : {X : π€ Μ } {Y : π₯ Μ } (f : X β Y)
           β πΜ f β ΞΌ βΌ ΞΌ β πΜ (πΜ f)
ΞΌ-naturalβΌ f _ = refl

ΞΌ-natural : funext (π£ βΊ β π€) (π£ βΊ β π₯)
          β {X : π€ Μ } {Y : π₯ Μ } (f : X β Y)
          β πΜ f β ΞΌ β‘ ΞΌ β πΜ (πΜ f)
ΞΌ-natural fe f = dfunext fe (ΞΌ-naturalβΌ f)


π-unit-rightβ : {X : π€ Μ } (l : π X)
              β ΞΌ (πΜ Ξ· l) β l
π-unit-rightβ {π€} {X} (P , Ο) = e , refl
 where
  e : P Γ π β P
  e = π-rneutral

π-unit-leftβ : {X : π€ Μ } (l : π X)
             β ΞΌ (Ξ· l) β l
π-unit-leftβ (P , Ο) = e , refl
 where
  e : π Γ P β P
  e = π-lneutral

π-unit-rightβΌ : is-univalent π£ β {X : π€ Μ }
              β ΞΌ β πΜ Ξ· βΌ id
π-unit-rightβΌ {π€} ua {X} l = β-gives-β‘ ua (π-unit-rightβ {π€} {X} l)

π-unit-leftβΌ : is-univalent π£ β {X : π€ Μ }
              β ΞΌ β Ξ· βΌ id
π-unit-leftβΌ {π€} ua {X} l = β-gives-β‘ ua (π-unit-leftβ {π€} {X} l)

π-assocβ : {X : π€ Μ } (l : π (π (π X))) β ΞΌ (ΞΌ l) β ΞΌ (πΜ ΞΌ l)
π-assocβ (P , Ο) = Ξ£-assoc , refl

π-assocβΌ : is-univalent π£ β {X : π€ Μ } β ΞΌ β ΞΌ βΌ ΞΌ β πΜ ΞΌ
π-assocβΌ {π€} ua {X} l = β-gives-β‘ ua (π-assocβ {π€} {X} l)

π-Ο : {X : π€ Μ } {Y : π₯ Μ } β X Γ π Y β π (X Γ Y)
π-Ο (x , m) = πΜ (Ξ» y β (x , y)) m

π-Ο : {X : π€ Μ } {Y : π₯ Μ } β π X Γ Y β π (X Γ Y)
π-Ο (l , y) = πΜ (Ξ» x β (x , y)) l

π-comm : {X : π€ Μ } {Y : π₯ Μ } {l : π X Γ π Y}
       β ΞΌ (πΜ π-Ο (π-Ο l)) βΒ· ΞΌ (πΜ π-Ο (π-Ο l))
π-comm = Γ-comm , (Ξ» z β refl)

π-m : {X : π€ Μ } {Y : π₯ Μ } β π X Γ π Y β π (X Γ Y)
π-m (l , m) = ((Ξ» x β curry π-Ο x m)β―) l

Kleisli-Lawβ : {X : π€ Μ } (l : π X) β (Ξ· β―) l β l
Kleisli-Lawβ (P , Ο) = π-rneutral , refl

Kleisli-Lawβ : {X : π€ Μ } {Y : π₯ Μ } (f : X β π Y) (x : X) β (f β―) (Ξ· x) β f x
Kleisli-Lawβ f x = π-lneutral , refl

Kleisli-Lawβ : {X : π₯ Μ } {Y : π¦ Μ } {Z : π£ Μ } (f : X β π Y) (g : Y β π Z) (l : π X)
             β (g β― β f β―) l β ((g β― β f)β―) l
Kleisli-Lawβ f g l = Ξ£-assoc , refl

πΜ' : {X : π€ Μ } {Y : π₯ Μ } β (X β Y) β π X β π Y
πΜ' f = (Ξ· β f)β―

πΜ-agreement : {X : π€ Μ } {Y : π₯ Μ } (f : X β Y) (l : π X)
             β πΜ' f l βΒ· πΜ f l
πΜ-agreement {π€} {π₯} {X} {Y} f (P , Ο) = π-rneutral , Ξ» _ β refl

\end{code}
