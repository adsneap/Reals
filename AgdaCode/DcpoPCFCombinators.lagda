Tom de Jong, 27 May 2019.
Refactored December 2021.

* Continuous K and S functions. These will interpret the K and S combinators of
  PCF in ScottModelOfPCF.lagda.
* Continuous ifZero function specific to the lifting of the natural numbers.
  This will then be used to interpret the ifZero combinator of PCF in
  ScottModelOfPCF.lagda.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-PropTrunc

module DcpoPCFCombinators
        (pt : propositional-truncations-exist)
        (fe : โ {๐ค ๐ฅ} โ funext ๐ค ๐ฅ)
        (๐ฅ : Universe)
       where

open PropositionalTruncation pt

open import UF-Subsingletons
open import UF-Subsingletons-FunExt

open import Poset fe
open import Dcpo pt fe ๐ฅ
open import DcpoMiscelanea pt fe ๐ฅ
open import DcpoExponential pt fe ๐ฅ

\end{code}

We start by defining continuous K and S functions. These will interpret the K
and S combinators of PCF in ScottModelOfPCF.lagda.

This requires a little (straightforward) work, because S must be continuous in
all of its arguments.
Therefore, it is not enough to have S of type
  DCPO[ ๐ , ๐ โนแตแถแตแต ๐ ] โ DCPO[ ๐ , ๐ ] โ DCPO[ ๐ , ๐ ].
Rather we should have S of type
  DCPO[๐ โนแตแถแตแต ๐ โนแตแถแตแต ๐ , (๐ โนแตแถแตแต ๐) โนแตแถแตแต (๐ โนแตแถแตแต ๐) ].

\begin{code}

module _ (๐ : DCPO {๐ค} {๐ฃ})
         (๐ : DCPO {๐ค'} {๐ฃ'})
       where

 Kแตแถแตแต : DCPO[ ๐ , ๐ โนแตแถแตแต ๐ ]
 Kแตแถแตแต = k , c where
  k : โจ ๐ โฉ โ DCPO[ ๐ , ๐ ]
  k x = (ฮป _ โ x) , (constant-functions-are-continuous ๐ ๐ x)
  c : (I : ๐ฅ ฬ ) (ฮฑ : I โ โจ ๐ โฉ) (ฮด : is-Directed ๐ ฮฑ)
    โ is-sup (underlying-order (๐ โนแตแถแตแต ๐)) (k (โ ๐ ฮด)) (ฮป (i : I) โ k (ฮฑ i))
  c I ฮฑ ฮด = u , v where
   u : (i : I) (e : โจ ๐ โฉ) โ ฮฑ i โโจ ๐ โฉ (โ ๐ ฮด)
   u i e = โ-is-upperbound ๐ ฮด i
   v : (f : DCPO[ ๐ , ๐ ])
     โ ((i : I) โ k (ฮฑ i) โโจ ๐ โนแตแถแตแต ๐ โฉ f)
     โ (e : โจ ๐ โฉ) โ โ ๐ ฮด โโจ ๐ โฉ [ ๐ , ๐ ]โจ f โฉ e
   v (f , _) l e = โ-is-lowerbound-of-upperbounds ๐ ฮด (f e)
                   (ฮป (i : I) โ (l i) e)

 module _ (๐ : DCPO {๐ฆ} {๐ฆ'}) where

  Sโแตแถแตแต : DCPO[ ๐ , ๐ โนแตแถแตแต ๐ ]
         โ DCPO[ ๐ , ๐ ]
         โ DCPO[ ๐ , ๐ ]
  Sโแตแถแตแต (f , cf) (g , cg) = (ฮป x โ [ ๐ , ๐ ]โจ f x โฉ (g x)) , c
   where

    c : is-continuous ๐ ๐ (ฮป x โ [ ๐ , ๐ ]โจ f x โฉ (g x))
    c I ฮฑ ฮด = u , v
     where
      u : (i : I) โ [ ๐ , ๐ ]โจ f (ฮฑ i) โฉ   (g (ฮฑ i)) โโจ ๐ โฉ
                    [ ๐ , ๐ ]โจ f (โ ๐ ฮด) โฉ (g (โ ๐ ฮด))
      u i = [ ๐ , ๐ ]โจ f (ฮฑ i)   โฉ (g (ฮฑ i))   โโจ ๐ โฉ[ โฆ1โฆ ]
            [ ๐ , ๐ ]โจ f (โ ๐ ฮด) โฉ (g (ฮฑ i))   โโจ ๐ โฉ[ โฆ2โฆ ]
            [ ๐ , ๐ ]โจ f (โ ๐ ฮด) โฉ (g (โ ๐ ฮด)) โโจ ๐ โฉ
       where
        โฆ1โฆ = monotone-if-continuous ๐ (๐ โนแตแถแตแต ๐) (f , cf) (ฮฑ i)
               (โ ๐ ฮด) (โ-is-upperbound ๐ ฮด i) (g (ฮฑ i))
        โฆ2โฆ = monotone-if-continuous ๐ ๐ (f (โ ๐ ฮด)) (g (ฮฑ i)) (g (โ ๐ ฮด))
               (monotone-if-continuous ๐ ๐ (g , cg) (ฮฑ i) (โ ๐ ฮด)
                 (โ-is-upperbound ๐ ฮด i))
      v : (y : โจ ๐ โฉ)
        โ ((i : I) โ ([ ๐ , ๐ ]โจ f (ฮฑ i) โฉ (g (ฮฑ i))) โโจ ๐ โฉ y)
        โ ([ ๐ , ๐ ]โจ f (โ ๐ ฮด) โฉ (g (โ ๐ ฮด))) โโจ ๐ โฉ y
      v y ineqs = ฮณ
       where
        ฮณ : [ ๐ , ๐ ]โจ f (โ ๐ ฮด) โฉ (g (โ ๐ ฮด)) โโจ ๐ โฉ y
        ฮณ = transport (ฮป - โ [ ๐ , ๐  ]โจ f (โ ๐ ฮด) โฉ - โโจ ๐ โฉ y)
            eโ ฮณโ
         where
          eโ : โ ๐ (image-is-directed' ๐ ๐ (g , cg) ฮด) โก g (โ ๐ ฮด)
          eโ = (continuous-โ-โก ๐ ๐ (g , cg) ฮด) โปยน
          ฮตโ : is-Directed ๐ (g โ ฮฑ)
          ฮตโ = image-is-directed' ๐ ๐ (g , cg) ฮด
          ฮณโ : [ ๐ , ๐ ]โจ f (โ ๐ ฮด) โฉ (โ ๐ ฮตโ) โโจ ๐ โฉ y
          ฮณโ = transport (ฮป - โ - โโจ ๐ โฉ y) eโ ฮณโ
           where
            eโ : โ ๐ (image-is-directed' ๐ ๐ (f (โ ๐ ฮด)) ฮตโ) โก
                 [ ๐ , ๐ ]โจ f (โ ๐ ฮด) โฉ (โ ๐ ฮตโ)
            eโ = (continuous-โ-โก ๐ ๐ (f (โ ๐ ฮด)) ฮตโ) โปยน
            ฮตโ : is-Directed ๐ ([ ๐ , ๐ ]โจ f (โ ๐ ฮด) โฉ โ (g โ ฮฑ))
            ฮตโ = image-is-directed' ๐ ๐ (f (โ ๐ ฮด)) ฮตโ
            ฮณโ : (โ ๐ ฮตโ) โโจ ๐ โฉ y
            ฮณโ = โ-is-lowerbound-of-upperbounds ๐ ฮตโ y ฮณโ
             where
              ฮณโ : (i : I) โ [ ๐ , ๐ ]โจ f (โ ๐ ฮด) โฉ (g (ฮฑ i)) โโจ ๐ โฉ y
              ฮณโ i = transport (ฮป - โ [ ๐ , ๐ ]โจ - โฉ (g (ฮฑ i)) โโจ ๐ โฉ y) eโ ฮณโ
               where
                ฮตโ : is-Directed (๐ โนแตแถแตแต ๐) (f โ ฮฑ)
                ฮตโ = image-is-directed' ๐ (๐ โนแตแถแตแต ๐) (f , cf) ฮด
                eโ : โ (๐ โนแตแถแตแต ๐) {I} {f โ ฮฑ} ฮตโ โก f (โ ๐ ฮด)
                eโ = (continuous-โ-โก ๐ (๐ โนแตแถแตแต ๐) (f , cf) ฮด) โปยน
                ฮณโ : [ ๐ , ๐ ]โจ โ (๐ โนแตแถแตแต ๐) {I} {f โ ฮฑ} ฮตโ โฉ (g (ฮฑ i)) โโจ ๐ โฉ y
                ฮณโ = โ-is-lowerbound-of-upperbounds ๐
                      (pointwise-family-is-directed ๐ ๐ (f โ ฮฑ) ฮตโ (g (ฮฑ i)))
                      y h
                 where
                  h : (j : I) โ [ ๐ , ๐ ]โจ f (ฮฑ j) โฉ (g (ฮฑ i)) โโจ ๐ โฉ y
                  h j = โฅโฅ-rec (prop-valuedness ๐
                         ([ ๐ , ๐ ]โจ f (ฮฑ j) โฉ (g (ฮฑ i))) y)
                         r (semidirected-if-Directed ๐ ฮฑ ฮด i j)
                   where
                    r : (ฮฃ k ๊ I , ฮฑ i โโจ ๐ โฉ ฮฑ k ร ฮฑ j โโจ ๐ โฉ ฮฑ k)
                      โ [ ๐ , ๐ ]โจ f (ฮฑ j) โฉ (g (ฮฑ i)) โโจ ๐ โฉ y
                    r (k , l , m ) = [ ๐ , ๐ ]โจ f (ฮฑ j) โฉ (g (ฮฑ i)) โโจ ๐ โฉ[ โฆ1โฆ ]
                                     [ ๐ , ๐ ]โจ f (ฮฑ k) โฉ (g (ฮฑ i)) โโจ ๐ โฉ[ โฆ2โฆ ]
                                     [ ๐ , ๐ ]โจ f (ฮฑ k) โฉ (g (ฮฑ k)) โโจ ๐ โฉ[ โฆ3โฆ ]
                                     y                              โโจ ๐ โฉ
                     where
                      โฆ1โฆ = monotone-if-continuous ๐ (๐ โนแตแถแตแต ๐) (f , cf)
                             (ฮฑ j) (ฮฑ k) m (g (ฮฑ i))
                      โฆ2โฆ = monotone-if-continuous ๐ ๐ (f (ฮฑ k))
                             (g (ฮฑ i)) (g (ฮฑ k))
                             (monotone-if-continuous ๐ ๐ (g , cg) (ฮฑ i) (ฮฑ k) l)
                      โฆ3โฆ = ineqs k

  Sโแตแถแตแต : DCPO[ ๐ , ๐ โนแตแถแตแต ๐ ]
         โ DCPO[ ๐ โนแตแถแตแต ๐ , ๐ โนแตแถแตแต ๐ ]
  Sโแตแถแตแต (f , cf) = h , c
   where
    h : DCPO[ ๐ , ๐ ] โ DCPO[ ๐ , ๐ ]
    h = (Sโแตแถแตแต (f , cf))
    c : is-continuous (๐ โนแตแถแตแต ๐) (๐ โนแตแถแตแต ๐) h
    c I ฮฑ ฮด = u , v
     where
      u : (i : I) (d : โจ ๐ โฉ)
        โ [ ๐ , ๐ ]โจ h (ฮฑ i) โฉ d โโจ ๐ โฉ
          [ ๐ , ๐ ]โจ h (โ (๐ โนแตแถแตแต ๐) {I} {ฮฑ} ฮด )โฉ d
      u i d = monotone-if-continuous ๐ ๐ (f d)
              ([ ๐ , ๐ ]โจ ฮฑ i โฉ d)
              ([ ๐ , ๐ ]โจ โ (๐ โนแตแถแตแต ๐) {I} {ฮฑ} ฮด โฉ d)
              (โ-is-upperbound ๐ (pointwise-family-is-directed ๐ ๐ ฮฑ ฮด d) i)
      v : (g : DCPO[ ๐ , ๐ ])
        โ ((i : I) โ h (ฮฑ i) โโจ ๐ โนแตแถแตแต ๐ โฉ g)
        โ (d : โจ ๐ โฉ)
        โ [ ๐ , ๐ ]โจ h (โ (๐ โนแตแถแตแต ๐) {I} {ฮฑ} ฮด) โฉ d โโจ ๐ โฉ [ ๐ , ๐ ]โจ g โฉ d
      v g l d = transport (ฮป - โ - โโจ ๐ โฉ [ ๐ , ๐ ]โจ g โฉ d) e s
       where
        ฮต : is-Directed ๐ (pointwise-family ๐ ๐ ฮฑ d)
        ฮต = pointwise-family-is-directed ๐ ๐ ฮฑ ฮด d
        e : โ ๐ (image-is-directed' ๐ ๐ (f d) ฮต)
            โก [ ๐ , ๐ ]โจ h (โ (๐ โนแตแถแตแต ๐) {I} {ฮฑ} ฮด) โฉ d
        e = (continuous-โ-โก ๐ ๐ (f d) ฮต) โปยน
        ฯ : is-Directed ๐
            ([ ๐ , ๐ ]โจ f d โฉ โ (pointwise-family ๐ ๐ ฮฑ d))
        ฯ = image-is-directed' ๐ ๐ (f d) ฮต
        s : โ ๐ ฯ โโจ ๐ โฉ [ ๐ , ๐ ]โจ g โฉ d
        s = โ-is-lowerbound-of-upperbounds ๐ ฯ ([ ๐ , ๐ ]โจ g โฉ d)
            (ฮป (i : I) โ l i d)

  Sแตแถแตแต : DCPO[ ๐ โนแตแถแตแต ๐ โนแตแถแตแต ๐ , (๐ โนแตแถแตแต ๐) โนแตแถแตแต (๐ โนแตแถแตแต ๐) ]
  Sแตแถแตแต = Sโแตแถแตแต , c
   where
    c : is-continuous (๐ โนแตแถแตแต ๐ โนแตแถแตแต ๐)
                      ((๐ โนแตแถแตแต ๐) โนแตแถแตแต (๐ โนแตแถแตแต ๐))
                      Sโแตแถแตแต
    c I ฮฑ ฮด = u , v
     where
      u : (i : I) ((g , _) : DCPO[ ๐ , ๐ ]) (d : โจ ๐ โฉ)
        โ [ ๐ , ๐ ]โจ [ ๐ , ๐ โนแตแถแตแต ๐ ]โจ ฮฑ i โฉ d โฉ (g d) โโจ ๐ โฉ
          [ ๐ , ๐ ]โจ [ ๐ , ๐ โนแตแถแตแต ๐ ]โจ โ (๐ โนแตแถแตแต (๐ โนแตแถแตแต ๐)) {I} {ฮฑ} ฮด โฉ d โฉ
           (g d)
      u i (g , _) d = โ-is-upperbound ๐
                       (pointwise-family-is-directed ๐ ๐ ฮฒ ฮต (g d)) i
       where
        ฮฒ : I โ DCPO[ ๐ , ๐ ]
        ฮฒ = pointwise-family ๐ (๐ โนแตแถแตแต ๐) ฮฑ d
        ฮต : is-Directed (๐ โนแตแถแตแต ๐) ฮฒ
        ฮต = pointwise-family-is-directed ๐ (๐ โนแตแถแตแต ๐) ฮฑ ฮด d
      v : (f : DCPO[ ๐ โนแตแถแตแต ๐ , ๐ โนแตแถแตแต ๐ ])
        โ ((i : I) โ Sโแตแถแตแต (ฮฑ i) โโจ (๐ โนแตแถแตแต ๐) โนแตแถแตแต (๐ โนแตแถแตแต ๐) โฉ f)
        โ (g : DCPO[ ๐ , ๐ ]) (d : โจ ๐ โฉ)
        โ [ ๐ , ๐ ]โจ [ ๐ , ๐ โนแตแถแตแต ๐ ]โจ โ (๐ โนแตแถแตแต (๐ โนแตแถแตแต ๐)) {I} {ฮฑ} ฮด โฉ d โฉ
           ([ ๐ , ๐ ]โจ g โฉ d)
        โโจ ๐ โฉ
          [ ๐ , ๐ ]โจ [ ๐ โนแตแถแตแต ๐ , ๐ โนแตแถแตแต ๐ ]โจ f โฉ g โฉ d
      v (f , _) l g d = โ-is-lowerbound-of-upperbounds ๐ ฮต ([ ๐ , ๐ ]โจ f g โฉ d)
                         (ฮป (i : I) โ l i g d)
       where
        ฮต : is-Directed ๐
             (ฮป i โ [ ๐ , ๐ ]โจ [ ๐ โนแตแถแตแต ๐ , ๐ โนแตแถแตแต ๐ ]โจ Sโแตแถแตแต (ฮฑ i) โฉ g โฉ d)
        ฮต = pointwise-family-is-directed ๐ ๐ ฮฒ ฯ ([ ๐ , ๐ ]โจ g โฉ d)
         where
          ฮฒ : I โ DCPO[ ๐ , ๐ ]
          ฮฒ i = [ ๐ , ๐ โนแตแถแตแต ๐ ]โจ ฮฑ i โฉ d
          ฯ : is-Directed (๐ โนแตแถแตแต ๐) ฮฒ
          ฯ = pointwise-family-is-directed ๐ (๐ โนแตแถแตแต ๐) ฮฑ ฮด d

module _ (๐ : DCPOโฅ {๐ค} {๐ฃ})
         (๐ : DCPOโฅ {๐ค'} {๐ฃ'})
       where

 Kแตแถแตแตโฅ : DCPOโฅ[ ๐ , ๐ โนแตแถแตแตโฅ ๐ ]
 Kแตแถแตแตโฅ = Kแตแถแตแต (๐ โป) (๐ โป)

 Sแตแถแตแตโฅ : (๐ : DCPOโฅ {๐ฆ} {๐ฆ'})
        โ DCPOโฅ[ ๐ โนแตแถแตแตโฅ ๐ โนแตแถแตแตโฅ ๐ , (๐ โนแตแถแตแตโฅ ๐) โนแตแถแตแตโฅ (๐ โนแตแถแตแตโฅ ๐) ]
 Sแตแถแตแตโฅ ๐ = Sแตแถแตแต (๐ โป) (๐ โป) (๐ โป)

\end{code}

TODO: Revise comments

Finally, we construct the continuous ifZero function, specific to the lifting of
โ. This will then be used to interpret the ifZero combinator of PCF in
ScottModelOfPCF.lagda.

\begin{code}

module IfZeroDenotationalSemantics
        (pe : propext ๐ฅ)
       where

 open import Lifting ๐ฅ
 open import LiftingMiscelanea ๐ฅ
 open import LiftingMiscelanea-PropExt-FunExt ๐ฅ pe fe
 open import LiftingMonad ๐ฅ

 open import DcpoLifting pt fe ๐ฅ pe

 open import UF-Miscelanea

 open import NaturalNumbers-Properties

 ๐แตโ : DCPOโฅ {๐ฅ โบ} {๐ฅ โบ}
 ๐แตโ = ๐-DCPOโฅ โ-is-set

 โฆifZeroโฆโ : ๐ โ โ ๐ โ โ โ โ ๐ โ
 โฆifZeroโฆโ a b zero     = a
 โฆifZeroโฆโ a b (succ n) = b

 โฆifZeroโฆโ : ๐ โ โ ๐ โ โ DCPOโฅ[ ๐แตโ , ๐แตโ ]
 โฆifZeroโฆโ a b =
  (โฆifZeroโฆโ a b) โฏ , โฏ-is-continuous โ-is-set โ-is-set (โฆifZeroโฆโ a b)

 โฆifZeroโฆโ : ๐ โ โ DCPOโฅ[ ๐แตโ , ๐แตโ โนแตแถแตแตโฅ ๐แตโ ]
 โฆifZeroโฆโ a = โฆifZeroโฆโ a , c
  where
   c : is-continuous (๐แตโ โป) ((๐แตโ โนแตแถแตแตโฅ ๐แตโ) โป) (โฆifZeroโฆโ a)
   c I ฮฑ ฮด = u , v
    where
     u : (i : I) (l : ๐ โ) (d : is-defined (((โฆifZeroโฆโ a (ฮฑ i)) โฏ) l))
       โ ((โฆifZeroโฆโ a (ฮฑ i)) โฏ) l โก ((โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด)) โฏ) l
     u i l d = ((โฆifZeroโฆโ a (ฮฑ i)) โฏ) l             โกโจ qโ โฉ
               โฆifZeroโฆโ a (ฮฑ i) (value l e)         โกโจ qโ โฉ
               โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด) (value l e) โกโจ qโ โฉ
               ((โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด)) โฏ) l     โ
      where
       e : is-defined l
       e = โฏ-is-defined (โฆifZeroโฆโ a (ฮฑ i)) l d
       qโ = โฏ-on-total-element (โฆifZeroโฆโ a (ฮฑ i)) e
       qโ = (โฏ-on-total-element (โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด)) {l} e) โปยน
       qโ = โ-cases {๐ฅ โบ} {ฮป (n : โ) โ โฆifZeroโฆโ a (ฮฑ i) n
                                     โก โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด) n} (value l e) pโ pโ
        where
         pโ : value l e โก zero
            โ โฆifZeroโฆโ a (ฮฑ i) (value l e) โก โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด) (value l e)
         pโ q = โฆifZeroโฆโ a (ฮฑ i) (value l e)         โกโจ ap (โฆifZeroโฆโ a (ฮฑ i)) q  โฉ
                โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด) zero        โกโจ ap (โฆifZeroโฆโ a _) (q โปยน) โฉ
                โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด) (value l e) โ
         pโ : (n : โ) โ value l e โก succ n
            โ โฆifZeroโฆโ a (ฮฑ i) (value l e) โก โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด) (value l e)
         pโ n q = โฆifZeroโฆโ a (ฮฑ i) (value l e)         โกโจ โฆ1โฆ  โฉ
                  โฆifZeroโฆโ a (ฮฑ i) (succ n)            โกโจ refl โฉ
                  ฮฑ i                                   โกโจ โฆ2โฆ  โฉ
                  โ (๐แตโ โป) ฮด                           โกโจ refl โฉ
                  โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด) (succ n)    โกโจ โฆ3โฆ  โฉ
                  โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด) (value l e) โ
          where
           โฆ1โฆ = ap (โฆifZeroโฆโ a (ฮฑ i)) q
           โฆ3โฆ = ap (โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด)) (q โปยน)
           โฆ2โฆ = family-defined-somewhere-sup-โก โ-is-set ฮด i eแตข
            where
             eแตข : is-defined (ฮฑ i)
             eแตข = โก-to-is-defined (ap (โฆifZeroโฆโ a (ฮฑ i)) q)
                   (โก-to-is-defined
                     (โฏ-on-total-element (โฆifZeroโฆโ a (ฮฑ i)) {l} e) d)

     v : (f : DCPOโฅ[ ๐แตโ , ๐แตโ ])
       โ ((i : I) โ โฆifZeroโฆโ a (ฮฑ i) โโช ๐แตโ โนแตแถแตแตโฅ ๐แตโ โซ f)
       โ (l : ๐ โ) (d : is-defined (((โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด)) โฏ) l))
       โ ((โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด)) โฏ) l โก [ ๐แตโ โป , ๐แตโ โป ]โจ f โฉ l
     v (f , _) ineqs l d = ((โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด)) โฏ) l     โกโจ qโ โฉ
                           โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด) (value l e) โกโจ qโ โฉ
                           f l                                  โ
      where
       e : is-defined l
       e = โฏ-is-defined (โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด)) l d
       qโ = โฏ-on-total-element (โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด)) {l} e
       qโ = โ-cases {๐ฅ โบ} {ฮป (n : โ) โ โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด) n โก f l}
             (value l e) pโ pโ
        where
         pโ : value l e โก zero
            โ โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด) (value l e) โก f l
         pโ q = โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด) (value l e) โกโจ โฆ1โฆ  โฉ
                โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด) zero        โกโจ refl โฉ
                a                                     โกโจ โฆ2โฆ  โฉ
                f l                                   โ
          where
           โฆ1โฆ = ap (โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด)) q
           โฆ2โฆ = โฅโฅ-rec (lifting-of-set-is-set โ-is-set)
                  h (inhabited-if-Directed (๐แตโ โป) ฮฑ ฮด)
            where
             h : (i : I) โ a โก f l
             h i = a                             โกโจ โฆ1'โฆ โฉ
                   โฆifZeroโฆโ a (ฮฑ i) (value l e) โกโจ โฆ2'โฆ โฉ
                   ((โฆifZeroโฆโ a (ฮฑ i)) โฏ) l     โกโจ โฆ3'โฆ โฉ
                   f l                           โ
              where
               โฆ1'โฆ = ap (โฆifZeroโฆโ a (ฮฑ i)) (q โปยน)
               โฆ2'โฆ = (โฏ-on-total-element (โฆifZeroโฆโ a (ฮฑ i)) e) โปยน
               โฆ3'โฆ = ineqs i l (โก-to-is-defined r d)
                where
                 r : ((โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด)) โฏ) l
                   โก ((โฆifZeroโฆโ a (ฮฑ i)) โฏ) l
                 r = qโ โ โฆ1โฆ โ โฆ1'โฆ โ โฆ2'โฆ

         pโ : (m : โ) โ value l e โก succ m
            โ โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด) (value l e) โก f l
         pโ m q = โฅโฅ-rec (lifting-of-set-is-set โ-is-set) h e'
          where
           โฆ1โฆ : (โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด) โฏ) l
               โก โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด) (value l e)
           โฆ1โฆ = โฏ-on-total-element (โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด)) {l} e
           โฆ2โฆ : โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด) (value l e) โก โ (๐แตโ โป) ฮด
           โฆ2โฆ = ap (โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด)) q
           e' : is-defined (โ (๐แตโ โป) ฮด)
           e' = โก-to-is-defined (โฆ1โฆ โ โฆ2โฆ) d
           h : (ฮฃ i ๊ I , is-defined (ฮฑ i))
             โ โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด) (value l e) โก f l
           h (i , dแตข) = โฆifZeroโฆโ a (โ (๐แตโ โป) ฮด) (value l e) โกโจ โฆ1'โฆ โฉ
                        โ (๐แตโ โป) ฮด                           โกโจ โฆ2'โฆ โฉ
                        ฮฑ i                                   โกโจ โฆ3'โฆ โฉ
                        ((โฆifZeroโฆโ a (ฮฑ i)) โฏ) l             โกโจ โฆ4'โฆ โฉ
                        f l                                   โ
            where
             โฆ1'โฆ = โฆ2โฆ
             โฆ2'โฆ = (family-defined-somewhere-sup-โก โ-is-set ฮด i dแตข) โปยน
             โฆ3'โฆ = (โฏ-on-total-element (โฆifZeroโฆโ a (ฮฑ i)) e
                     โ ap (โฆifZeroโฆโ a (ฮฑ i)) q) โปยน
             โฆ4'โฆ = ineqs i l (โก-to-is-defined โฆ3'โฆ dแตข)

\end{code}

We can exploit the fact that ifZero a b 0 โก ifZero b a 1, to reduce the proof
that ifZero is continuous in its first argument to continuity in its second
argument. The "flip"-code below prepares for this.

\begin{code}

 โ-flip : โ โ โ
 โ-flip zero     = succ zero
 โ-flip (succ n) = zero

 ifZero-flip-equation : (a b : ๐ โ) (n : โ)
                      โ โฆifZeroโฆโ a b n โก โฆifZeroโฆโ b a (โ-flip n)
 ifZero-flip-equation a b zero     = refl
 ifZero-flip-equation a b (succ n) = refl

 ๐โ-flip : ๐ โ โ ๐ โ
 ๐โ-flip (P , ฯ , ฯ) = (P , โ-flip โ ฯ , ฯ)

 ifZeroโฏ-flip-equation : (a b : ๐ โ) (l : ๐ โ)
                      โ ((โฆifZeroโฆโ a b) โฏ) l โก ((โฆifZeroโฆโ b a) โฏ) (๐โ-flip l)
 ifZeroโฏ-flip-equation a b l = โ'-is-antisymmetric u v
  where
   l' : ๐ โ
   l' = ๐โ-flip l
   lemma : (p : is-defined l)
         โ (โฆifZeroโฆโ a b โฏ) l โก (โฆifZeroโฆโ b a โฏ) l'
   lemma p = (โฆifZeroโฆโ a b โฏ) l        โกโจ โฆ1โฆ โฉ
             โฆifZeroโฆโ a b (value l  p) โกโจ โฆ2โฆ โฉ
             โฆifZeroโฆโ b a (value l' p) โกโจ โฆ3โฆ โฉ
             (โฆifZeroโฆโ b a โฏ) l'       โ
    where
     โฆ1โฆ = โฏ-on-total-element (โฆifZeroโฆโ a b) p
     โฆ2โฆ = ifZero-flip-equation a b (value l p)
     โฆ3โฆ = (โฏ-on-total-element (โฆifZeroโฆโ b a) p) โปยน
   u : (โฆifZeroโฆโ a b โฏ) l โ' (โฆifZeroโฆโ b a โฏ) l'
   u q = lemma (โฏ-is-defined (โฆifZeroโฆโ a b) l q)
   v : (โฆifZeroโฆโ b a โฏ) l' โ' (โฆifZeroโฆโ a b โฏ) l
   v q = (lemma (โฏ-is-defined (โฆifZeroโฆโ b a) l' q)) โปยน

\end{code}

We are now ready to give the final continuity proof.

\begin{code}

 โฆifZeroโฆ : DCPOโฅ[ ๐แตโ , ๐แตโ โนแตแถแตแตโฅ ๐แตโ โนแตแถแตแตโฅ ๐แตโ  ]
 โฆifZeroโฆ = โฆifZeroโฆโ , c
  where
   c : is-continuous (๐แตโ โป) ((๐แตโ โนแตแถแตแตโฅ ๐แตโ โนแตแถแตแตโฅ ๐แตโ) โป) โฆifZeroโฆโ
   c I ฮฑ ฮด = u , v
    where
     u : (i : I) (b : ๐ โ) (l : ๐ โ)
       โ ((โฆifZeroโฆโ (ฮฑ i) b) โฏ) l โโช ๐แตโ โซ ((โฆifZeroโฆโ (โ (๐แตโ โป) ฮด) b) โฏ) l
     u i b l = ((โฆifZeroโฆโ (ฮฑ i) b) โฏ) l           โโช ๐แตโ โซ[ โฆ1โฆ ]
               ((โฆifZeroโฆโ b (ฮฑ i)) โฏ) l'          โโช ๐แตโ โซ[ โฆ2โฆ ]
               ((โฆifZeroโฆโ b (โ (๐แตโ โป) ฮด)) โฏ) l'  โโช ๐แตโ โซ[ โฆ3โฆ ]
               ((โฆifZeroโฆโ (โ (๐แตโ โป) ฮด) b) โฏ) l   โโช ๐แตโ โซ
      where
       l' : ๐ โ
       l' = ๐โ-flip l
       โฆ1โฆ = โก-to-โ (๐แตโ โป) (ifZeroโฏ-flip-equation (ฮฑ i) b l)
       โฆ2โฆ = (monotone-if-continuous (๐แตโ โป) ((๐แตโ โนแตแถแตแตโฅ ๐แตโ) โป)
              (โฆifZeroโฆโ b) (ฮฑ i) (โ (๐แตโ โป) ฮด)
              (โ-is-upperbound (๐แตโ โป) ฮด i))
             l'
       โฆ3โฆ = โก-to-โ (๐แตโ โป) ((ifZeroโฏ-flip-equation (โ (๐แตโ โป) ฮด) b l) โปยน)

     v : ((f , _) : DCPOโฅ[ ๐แตโ , ๐แตโ โนแตแถแตแตโฅ ๐แตโ ])
       โ ((i : I) (b : ๐ โ) โ โฆifZeroโฆโ (ฮฑ i) b โโช ๐แตโ โนแตแถแตแตโฅ ๐แตโ โซ f b)
       โ (b : ๐ โ) (l : ๐ โ)
       โ ((โฆifZeroโฆโ (โ (๐แตโ โป) ฮด) b) โฏ) l โโช ๐แตโ โซ [ ๐แตโ โป , ๐แตโ โป ]โจ f b โฉ l
     v (f , _) ineqs b l =
      ((โฆifZeroโฆโ (โ (๐แตโ โป) ฮด) b) โฏ) l                 โโช ๐แตโ โซ[ โฆ1โฆ ]
      ((โฆifZeroโฆโ b (โ (๐แตโ โป) ฮด)) โฏ) l'                โโช ๐แตโ โซ[ โฆ2โฆ ]
      [ ๐แตโ โป , ๐แตโ โป ]โจ โฆifZeroโฆโ b (โ (๐แตโ โป) ฮด) โฉ l' โโช ๐แตโ โซ[ โฆ3โฆ ]
      โ (๐แตโ โป) {I} {ฮฑ'} ฮด'                             โโช ๐แตโ โซ[ โฆ4โฆ ]
      โ (๐แตโ โป) {I} {ฮฑ''} ฮด''                           โโช ๐แตโ โซ[ โฆ5โฆ ]
      [ ๐แตโ โป , ๐แตโ โป ]โจ f b โฉ l                        โโช ๐แตโ โซ
       where
        l' : ๐ โ
        l' = ๐โ-flip l
        ฮฑ' : (i : I) โ โช ๐แตโ โซ
        ฮฑ' i = ((โฆifZeroโฆโ b (ฮฑ i)) โฏ) l'
        ฮด' : is-Directed (๐แตโ โป) ฮฑ'
        ฮด' = pointwise-family-is-directed (๐แตโ โป) (๐แตโ โป) (โฆifZeroโฆโ b โ ฮฑ) ฮต l'
         where
          ฮต : is-Directed ((๐แตโ โนแตแถแตแตโฅ ๐แตโ) โป) (โฆifZeroโฆโ b โ ฮฑ)
          ฮต = image-is-directed' (๐แตโ โป) ((๐แตโ โนแตแถแตแตโฅ ๐แตโ) โป) (โฆifZeroโฆโ b) ฮด
        ฮฑ'' : (i : I) โ โช ๐แตโ โซ
        ฮฑ'' i = ((โฆifZeroโฆโ (ฮฑ i) b) โฏ) l
        e : ฮฑ' โก ฮฑ''
        e = dfunext fe (ฮป i โ (ifZeroโฏ-flip-equation (ฮฑ i) b l) โปยน)
        ฮด'' : is-Directed (๐แตโ โป) ฮฑ''
        ฮด'' = transport (is-Directed (๐แตโ โป)) e ฮด'

        โฆ1โฆ = โก-to-โ (๐แตโ โป) (ifZeroโฏ-flip-equation (โ (๐แตโ โป) ฮด) b l)
        โฆ2โฆ = reflexivity (๐แตโ โป) _
        โฆ3โฆ = โก-to-โ (๐แตโ โป)
              (ap (ฮป - โ [ ๐แตโ โป , ๐แตโ โป ]โจ - โฉ l')
                  (continuous-โ-โก (๐แตโ โป) ((๐แตโ โนแตแถแตแตโฅ ๐แตโ) โป)
                    (โฆifZeroโฆโ b) {I} {ฮฑ} ฮด))
        โฆ4โฆ = โก-to-โ (๐แตโ โป) (โ-family-โก (๐แตโ โป) e ฮด')
        โฆ5โฆ = โ-is-lowerbound-of-upperbounds (๐แตโ โป) ฮด''
              ([ ๐แตโ โป , ๐แตโ โป ]โจ f b โฉ l) (ฮป i โ ineqs i b l)

\end{code}
