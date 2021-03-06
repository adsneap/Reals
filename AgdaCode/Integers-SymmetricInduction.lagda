Tom de Jong
Reboot: 22 January 2021
Earlier version: 18 September 2020

We show that the type of integers enjoys the symmetric induction principle, as
used in constructing the circle as the type of โค-torsors. The symmetric
induction principle appears as Theorem 3.13 in "Construction of the circle in
UniMath" by Bezem, Buchholtz, Grayson and Shulman
(doi:10.1016/j.jpaa.2021.106687).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import NaturalNumbers-UniversalProperty

open import Integers
open import Integers-Properties

open import SpartanMLTT
open import UF-Base
open import UF-Embeddings
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-Subsingletons

module Integers-SymmetricInduction where

โค-symmetric-induction : {๐ค : Universe}
                      โ funext ๐คโ ๐ค
                      โ (A : โค โ ๐ค ฬ )
                        (f : (z : โค) โ A z โ A (succ-โค z))
                      โ (ฮฃ h ๊ ฮ  A , ((z : โค) โ h (succ-โค z) โก โ f z โ (h z)))
                      โ A ๐
โค-symmetric-induction {๐ค} fe A f =
 (ฮฃ h ๊ ฮ  A , Qโ h)                                               โโจ I    โฉ
 (ฮฃ h ๊ (ฮ  (A โ โ๐โ) ร ฮ  (A โ inr)) , Qโ (gโ h))                  โโจ II   โฉ
 (ฮฃ hโ ๊ ฮ  (A โ โ๐โ) , ฮฃ hแตฃ ๊ ฮ  (A โ inr) , Qโ (gโ (hโ , hแตฃ)))    โโจ III  โฉ
 (ฮฃ hโ ๊ ฮ  (A โ โ๐โ) , ฮฃ hแตฃ ๊ (ฮ  (A โ pos) ร ฮ  (A โ neg)),
                         Qโ hโ (gโ hแตฃ))                           โโจ IV   โฉ
 (ฮฃ hโ ๊ ฮ  (A โ โ๐โ) , ฮฃ hโ ๊ ฮ  (A โ pos) ,
                       ฮฃ hโ ๊ ฮ  (A โ neg) , Qโ hโ (gโ (hโ , hโ))) โโจ V    โฉ
 (ฮฃ hโ ๊ ฮ  (A โ โ๐โ) , ฮฃ hโ ๊ ฮ  (A โ pos) ,
                       ฮฃ hโ ๊ ฮ  (A โ neg) , Qโ (hโ โ) hโ
                                          ร Qโ' (hโ โ) hโ)        โโจ VI   โฉ
 (ฮฃ hโ ๊ ฮ  (A โ โ๐โ) , ((ฮฃ hโ ๊ ฮ  (A โ pos) , Qโ (hโ โ) hโ)
                     ร  (ฮฃ hโ ๊ ฮ  (A โ neg) , Qโ' (hโ โ) hโ)))    โโจ VII  โฉ
 (ฮฃ hโ ๊ ฮ  (A โ โ๐โ) , ๐ ร (ฮฃ hโ ๊ ฮ  (A โ neg) , Qโ' (hโ โ) hโ))  โโจ VIII โฉ
 (ฮฃ hโ ๊ ฮ  (A โ โ๐โ) , ฮฃ hโ ๊ ฮ  (A โ neg) , Qโ' (hโ โ) hโ)        โโจ IX   โฉ
 (ฮฃ hโ ๊ ฮ  (A โ โ๐โ) , ฮฃ hโ ๊ ฮ  (A โ neg) , Qโ (hโ โ) hโ)         โโจ X    โฉ
 (ฮฃ hโ ๊ ฮ  (A โ โ๐โ) , ๐)                                         โโจ XI   โฉ
 ฮ  (A โ โ๐โ)                                                      โโจ XII  โฉ
 A ๐ โ 
  where
   โ๐โ : ๐ {๐คโ} โ โค
   โ๐โ _ = ๐
   Qโ : ฮ  A โ ๐ค ฬ
   Qโ h = (z : โค) โ h (succ-โค z) โก โ f z โ (h z)
   gโ : ฮ  (A โ โ๐โ) ร ฮ  (A โ inr) โ ฮ  A
   gโ = โ ฮ ร+ fe โ
   Qโ : ฮ  (A โ โ๐โ) โ ฮ  (A โ inr) โ ๐ค ฬ
   Qโ hโ hแตฃ = Qโ (gโ (hโ , hแตฃ))
   gโ : ฮ  (A โ pos) ร ฮ  (A โ neg) โ ฮ  (A โ inr)
   gโ = โ ฮ ร+ fe โ
   Qโ : A ๐ โ ฮ  (A โ pos) โ ๐ค ฬ
   Qโ aโ hโ = (hโ 0 โก โ f ๐ โ aโ)
            ร ((n : โ) โ hโ (succ n) โก โ f (pos n) โ (hโ n))
   Qโ' : A ๐ โ ฮ  (A โ neg) โ ๐ค ฬ
   Qโ' aโ hโ = (aโ โก โ f (neg 0) โ (hโ 0))
             ร ((n : โ) โ hโ n โก โ f (neg (succ n)) โ (hโ (succ n)))
   Qโ : A ๐ โ ฮ  (A โ neg) โ ๐ค ฬ
   Qโ aโ hโ = (hโ 0 โก โ (f (neg 0)) โโปยน aโ)
            ร ((n : โ) โ hโ (succ n) โก โ (f (neg (succ n))) โโปยน (hโ n))
   I    = โ-sym (ฮฃ-change-of-variable Qโ gโ (โโ-is-equiv (ฮ ร+ fe)))
   II   = ฮฃ-assoc
   III  = ฮฃ-cong
          (ฮป hโ โ โ-sym (ฮฃ-change-of-variable (Qโ hโ) gโ (โโ-is-equiv (ฮ ร+ fe))))
   IV   = ฮฃ-cong (ฮป _ โ ฮฃ-assoc)
   V    = ฮฃ-cong ฮป hโ โ ฮฃ-cong (ฮป hโ โ ฮฃ-cong (ฮป hโ โ ฮณ hโ hโ hโ))
    where
     ฮณ : (hโ : ฮ  (A โ โ๐โ))  (hโ : ฮ  (A โ pos)) (hโ : ฮ  (A โ neg))
       โ Qโ hโ (gโ (hโ , hโ)) โ Qโ (hโ โ) hโ ร Qโ' (hโ โ) hโ
     ฮณ hโ hโ hโ = qinveq ฯ (ฯ , ฮท , ฮต)
      where
       ฯ : Qโ hโ (gโ (hโ , hโ)) โ Qโ (hโ โ) hโ ร Qโ' (hโ โ) hโ
       ฯ q = ((q ๐ , q โ pos) , (q (neg 0) , q โ neg โ succ))
       ฯ : (Qโ (hโ โ) hโ ร Qโ' (hโ โ) hโ) โ Qโ hโ (gโ (hโ , hโ))
       ฯ ((qโ , qโ) , (qโ' , qโ')) = c
        where
         c : Qโ hโ (gโ (hโ , hโ))
         c ๐              = qโ
         c (pos n)        = qโ n
         c (neg zero)     = qโ'
         c (neg (succ n)) = qโ' n
       ฮต : ฯ โ ฯ โผ id
       ฮต q = refl
       ฮท : ฯ โ ฯ โผ id
       ฮท q = dfunext fe c
        where
         c : (z : โค) โ (ฯ (ฯ q)) z โก q (z)
         c ๐              = refl
         c (pos n)        = refl
         c (neg zero)     = refl
         c (neg (succ n)) = refl
   VI   = ฮฃ-cong ฮณ
    where
     ฮณ : (hโ : ฮ  (A โ โ๐โ))
       โ (ฮฃ hโ ๊ ฮ  (A โ pos) , ฮฃ hโ ๊ ฮ  (A โ neg) , Qโ (hโ โ) hโ ร Qโ' (hโ โ) hโ)
       โ (  (ฮฃ hโ ๊ ฮ  (A โ pos) , Qโ (hโ โ) hโ)
          ร (ฮฃ hโ ๊ ฮ  (A โ neg) , Qโ' (hโ โ) hโ))
     ฮณ hโ = qinveq ฯ (ฯ , ฮท , ฮต)
      where
       ฯ : _
       ฯ (hโ , hโ , q' , q) = ((hโ , q') , (hโ , q))
       ฯ : _
       ฯ ((hโ , q') , (hโ , q)) = hโ , hโ , q' , q
       ฮท : ฯ โ ฯ โผ id
       ฮท _ = refl
       ฮต : ฯ โ ฯ โผ id
       ฮต _ = refl
   VII  = ฮฃ-cong (ฮป hโ โ ร-cong (singleton-โ-๐ {๐ค} {๐คโ} (ฮณ hโ)) (โ-refl _))
    where
     ฮณ : (hโ : ฮ  (A โ โ๐โ))
       โ is-singleton ((ฮฃ hโ ๊ ฮ  (A โ pos) , Qโ  (hโ โ) hโ))
     ฮณ hโ = (โ-is-nno-dep fe (A โ pos) aโ s)
      where
       aโ : A (pos 0)
       aโ = โ (f ๐) โ (hโ โ)
       s : (n : โ) โ A (pos n) โ A (pos (succ n))
       s n = โ f (pos n) โ
   VIII = ฮฃ-cong (ฮป hโ โ ๐-lneutral)
   IX   = ฮฃ-cong (ฮป hโ โ ฮฃ-cong (ฮป hโ โ ฮณ hโ hโ))
    where
     ฮณ : (hโ : ฮ  (A โ โ๐โ)) (hโ : ฮ  (A โ neg))
       โ Qโ' (hโ โ) hโ โ Qโ (hโ โ) hโ
     ฮณ hโ hโ = ร-cong ฮณโ (ฮ -cong fe fe โ _ _ ฮณโ)
      where
       fโ = โ f (neg 0) โ
       fโโปยน = โ (f (neg 0)) โโปยน
       eโ : is-equiv fโ
       eโ = โโ-is-equiv (f (neg 0))
       ฮณโ : (hโ โ โก fโ (hโ 0))
          โ (hโ 0 โก fโโปยน (hโ โ))
       ฮณโ = (hโ โ โก fโ (hโ 0))             โโจ Iโ   โฉ
            (fโ (hโ 0) โก hโ โ)             โโจ IIโ  โฉ
            (fโ (hโ 0) โก fโ (fโโปยน (hโ โ))) โโจ IIIโ โฉ
            (hโ 0 โก fโโปยน (hโ โ)) โ 
        where
         Iโ   = โก-flip
         IIโ  = โก-cong-r (fโ (hโ 0)) (hโ โ)
                 ((inverses-are-sections fโ eโ (hโ โ)) โปยน)
         IIIโ = embedding-criterion-converse fโ
                 (equivs-are-embeddings fโ eโ)
                 (hโ 0) (fโโปยน (hโ โ))
       fโ : (n : โ) โ A (neg (succ n)) โ A (neg n)
       fโ n = โ f (neg (succ n)) โ
       eโ : (n : โ) โ is-equiv (fโ n)
       eโ n = โโ-is-equiv (f (neg (succ n)))
       fโโปยน : (n : โ) โ A (neg n) โ A (neg (succ n))
       fโโปยน n = โ (f (neg (succ n))) โโปยน
       ฮณโ : (n : โ)
          โ (hโ n โก fโ n (hโ (succ n)))
          โ (hโ (succ n) โก fโโปยน n (hโ n))
       ฮณโ n = (hโ n โก fโ n (hโ (succ n)))                 โโจ Iโ โฉ
              (fโ n (hโ (succ n)) โก hโ n)                 โโจ IIโ โฉ
              (fโ n (hโ (succ n)) โก fโ n (fโโปยน n (hโ n))) โโจ IIIโ โฉ
              (hโ (succ n) โก fโโปยน n (hโ n))               โ 
        where
         Iโ   = โก-flip
         IIโ  = โก-cong-r (fโ n (hโ (succ n))) (hโ n)
                 ((inverses-are-sections (fโ n) (eโ n) (hโ n)) โปยน)
         IIIโ = embedding-criterion-converse (fโ n)
                 (equivs-are-embeddings (fโ n) (eโ n))
                 (hโ (succ n)) (fโโปยน n (hโ n))
   X    = ฮฃ-cong (ฮป hโ โ singleton-โ-๐ {๐ค} {๐คโ} (ฮณ hโ))
    where
     ฮณ : (hโ : ฮ  (A โ โ๐โ))
       โ is-singleton ((ฮฃ hโ ๊ ฮ  (A โ neg) , Qโ  (hโ โ) hโ))
     ฮณ hโ = (โ-is-nno-dep fe (A โ neg) aโ s)
      where
       aโ : A (neg 0)
       aโ = โ (f (neg 0)) โโปยน (hโ โ)
       s : (n : โ) โ A (neg n) โ A (neg (succ n))
       s n = โ (f (neg (succ n))) โโปยน
   XI   = ๐-rneutral
   XII  = โ-sym (๐โ fe)

\end{code}
