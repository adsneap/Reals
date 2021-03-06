Martin Escardo 8th May 2020.

An old version of this file is at UF-Classifiers-Old.

This version is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes


   * Map classifier
   * Embedding classifier
   * Retraction classifier
   * Surjection classifier

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Classifiers where

open import SpartanMLTT
open import UF-Base
open import UF-Embeddings
open import UF-Equiv
open import UF-Univalence
open import UF-FunExt
open import UF-UA-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Powerset hiding (๐)
open import UF-EquivalenceExamples
open import UF-Retracts

_/_ : (๐ค : Universe) โ ๐ฅ ฬ โ ๐ค โบ โ ๐ฅ ฬ
๐ค / Y = ฮฃ X ๊ ๐ค ฬ , (X โ Y)

ฯ : (Y : ๐ค ฬ ) โ ๐ค / Y  โ (Y โ ๐ค ฬ )
ฯ Y (X , f) = fiber f

is-map-classifier : (๐ค : Universe) โ ๐ค โบ ฬ
is-map-classifier ๐ค = (Y : ๐ค ฬ ) โ is-equiv (ฯ Y)

๐ : (Y : ๐ค ฬ ) โ (Y โ ๐ค ฬ ) โ ๐ค / Y
๐ Y A = ฮฃ A , prโ

ฯฮท : is-univalent ๐ค
   โ (Y : ๐ค ฬ ) (ฯ : ๐ค / Y) โ ๐ Y (ฯ Y ฯ) โก ฯ
ฯฮท ua Y (X , f) = r
 where
  e : ฮฃ (fiber f) โ X
  e = total-fiber-is-domain f

  p : ฮฃ (fiber f) โก X
  p = eqtoid ua (ฮฃ (fiber f)) X e

  observation : โ e โโปยน โก (ฮป x โ f x , x , refl)
  observation = refl

  q = transport (ฮป - โ - โ Y) p prโ โกโจ transport-is-pre-comp' ua e prโ โฉ
      prโ โ โ e โโปยน                 โกโจ refl โฉ
      f                             โ

  r : (ฮฃ (fiber f) , prโ) โก (X , f)
  r = to-ฮฃ-โก (p , q)

ฯฮต : is-univalent ๐ค
   โ funext ๐ค (๐ค โบ)
   โ (Y : ๐ค ฬ ) (A : Y โ ๐ค ฬ ) โ ฯ Y (๐ Y A) โก A
ฯฮต ua fe Y A = dfunext fe ฮณ
 where
  f : โ y โ fiber prโ y โ A y
  f y ((y , a) , refl) = a
  g : โ y โ A y โ fiber prโ y
  g y a = (y , a) , refl
  ฮท : โ y ฯ โ g y (f y ฯ) โก ฯ
  ฮท y ((y , a) , refl) = refl
  ฮต : โ y a โ f y (g y a) โก a
  ฮต y a = refl
  ฮณ : โ y โ fiber prโ y โก A y
  ฮณ y = eqtoid ua _ _ (qinveq (f y) (g y , ฮท y , ฮต y))

universes-are-map-classifiers : is-univalent ๐ค
                              โ funext ๐ค (๐ค โบ)
                              โ is-map-classifier ๐ค
universes-are-map-classifiers ua fe Y = qinvs-are-equivs (ฯ Y)
                                         (๐ Y , ฯฮท ua Y , ฯฮต ua fe Y)

map-classification : is-univalent ๐ค
                   โ funext ๐ค (๐ค โบ)
                   โ (Y : ๐ค ฬ ) โ ๐ค / Y โ (Y โ ๐ค ฬ )
map-classification ua fe Y = ฯ Y , universes-are-map-classifiers ua fe Y

_/[_]_ : (๐ค : Universe) โ (๐ค ฬ โ ๐ฅ ฬ ) โ ๐ค ฬ โ ๐ค โบ โ ๐ฅ ฬ
๐ค /[ P ] Y = ฮฃ X ๊ ๐ค ฬ , ฮฃ f ๊ (X โ Y) , ((y : Y) โ P (fiber f y))

ฯ-special : (P : ๐ค ฬ โ ๐ฅ ฬ ) (Y : ๐ค ฬ ) โ ๐ค /[ P ] Y  โ (Y โ ฮฃ P)
ฯ-special P Y (X , f , ฯ) y = fiber f y , ฯ y

is-special-map-classifier : (๐ค ฬ โ ๐ฅ ฬ ) โ ๐ค โบ โ ๐ฅ ฬ
is-special-map-classifier {๐ค} P = (Y : ๐ค ฬ ) โ is-equiv (ฯ-special P Y)

mc-gives-sc : is-map-classifier ๐ค
            โ (P : ๐ค ฬ โ ๐ฅ ฬ ) โ is-special-map-classifier P
mc-gives-sc {๐ค} s P Y = ฮณ
 where
  e = (๐ค /[ P ] Y)                               โโจ a โฉ
      (ฮฃ ฯ ๊ ๐ค / Y , ((y : Y) โ P ((ฯ Y) ฯ y)))  โโจ b โฉ
      (ฮฃ A ๊ (Y โ ๐ค ฬ ), ((y : Y) โ P (A y)))     โโจ c โฉ
      (Y โ ฮฃ P)                                  โ?
   where
    a = โ-sym ฮฃ-assoc
    b = ฮฃ-change-of-variable (ฮป A โ ฮ? (P โ A)) (ฯ Y) (s Y)
    c = โ-sym ฮ?ฮฃ-distr-โ

  observation : ฯ-special P Y โก โ e โ
  observation = refl

  ฮณ : is-equiv (ฯ-special P Y)
  ฮณ = โโ-is-equiv e

ฯ-special-is-equiv : is-univalent ๐ค
                   โ funext ๐ค (๐ค โบ)
                   โ (P : ๐ค ฬ โ ๐ฅ ฬ ) (Y : ๐ค ฬ )
                   โ is-equiv (ฯ-special P Y)
ฯ-special-is-equiv {๐ค} ua fe P Y = mc-gives-sc (universes-are-map-classifiers ua fe) P Y

special-map-classifier : is-univalent ๐ค
                       โ funext ๐ค (๐ค โบ)
                       โ (P : ๐ค ฬ โ ๐ฅ ฬ ) (Y : ๐ค ฬ )
                       โ ๐ค /[ P ] Y โ (Y โ ฮฃ P)
special-map-classifier {๐ค} ua fe P Y = ฯ-special P Y , ฯ-special-is-equiv ua fe P Y

ฮฉ-is-subtype-classifier : Univalence
                        โ (Y : ๐ค ฬ ) โ Subtypes Y โ (Y โ ฮฉ ๐ค)
ฮฉ-is-subtype-classifier {๐ค} ua = special-map-classifier (ua ๐ค)
                                  (univalence-gives-funext' ๐ค (๐ค โบ) (ua ๐ค) (ua (๐ค โบ)))
                                  is-subsingleton

subtypes-form-set : Univalence โ (Y : ๐ค ฬ ) โ is-set (Subtypes Y)
subtypes-form-set {๐ค} ua Y = equiv-to-set
                              (ฮฉ-is-subtype-classifier ua Y)
                              (powersets-are-sets' ua)

retractions-into : ๐ค ฬ โ ๐ค โบ ฬ
retractions-into {๐ค} Y = ฮฃ X ๊ ๐ค ฬ , Y โ X

pointed-types : (๐ค : Universe) โ ๐ค โบ ฬ
pointed-types ๐ค = ฮฃ X ๊ ๐ค ฬ , X

retraction-classifier : Univalence
                      โ (Y : ๐ค ฬ ) โ retractions-into Y โ (Y โ pointed-types ๐ค)
retraction-classifier {๐ค} ua Y =
 retractions-into Y                                              โโจ i โฉ
 ((๐ค /[ id ] Y))                                                 โโจ ii โฉ
 (Y โ pointed-types ๐ค)                                           โ?
 where
  i  = โ-sym (ฮฃ-cong (ฮป X โ ฮฃ-cong (ฮป f โ ฮ?ฮฃ-distr-โ)))
  ii = special-map-classifier (ua ๐ค)
        (univalence-gives-funext' ๐ค (๐ค โบ) (ua ๐ค) (ua (๐ค โบ)))
        id Y

module surjection-classifier
         (ua : Univalence)
       where

  open import UF-PropTrunc

  module _ (pt : propositional-truncations-exist) where

   open PropositionalTruncation pt public
   open import UF-ImageAndSurjection
   open ImageAndSurjection pt public

   surjections-into : ๐ค ฬ โ ๐ค โบ ฬ
   surjections-into {๐ค} Y = ฮฃ X ๊ ๐ค ฬ , X โ? Y

   inhabited-types : (๐ค : Universe) โ ๐ค โบ ฬ
   inhabited-types ๐ค = ฮฃ X ๊ ๐ค ฬ , โฅ X โฅ

   surjection-classifier : Univalence
                         โ (Y : ๐ค ฬ )
                         โ surjections-into Y โ (Y โ inhabited-types ๐ค)
   surjection-classifier {๐ค} ua = special-map-classifier (ua ๐ค)
                                   (univalence-gives-funext' ๐ค (๐ค โบ) (ua ๐ค) (ua (๐ค โบ)))
                                   โฅ_โฅ

\end{code}
