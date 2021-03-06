Tom de Jong, 12 May 2020 - 9 June 2020.

We construct Scott's famous nontrivial pointed dcpo Dโ for which Dโ is
isomorphic to its own function space.

This formalization is based on Scott's "Continuous lattices"
(doi:10.1007/BFB0073967), specifically pages 126--128.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --experimental-lossy-unification #-}

\end{code}

We use the flag --experimental-lossy-unification to speed up the type-checking.

This flag was kindly implemented by Andrea Vezzosi upon request.

Documentation for the flag (written by Andrea Vezzosi) can be found here:
https://agda.readthedocs.io/en/latest/language/lossy-unification.html

The most important takeaway from the documentation is that the flag is sound:

  "[...] if Agda accepts code with the flag enabled it should also accept it
  without the flag (with enough resources, and possibly needing extra type
  annotations)."

A related issue (originally opened by Wolfram Kahl in 2015) can be found here:
https://github.com/agda/agda/issues/1625

\begin{code}

open import SpartanMLTT
open import UF-FunExt
open import UF-PropTrunc
open import UF-Subsingletons

module DcpoDinfinity
        (pt : propositional-truncations-exist)
        (fe : โ {๐ค ๐ฅ} โ funext ๐ค ๐ฅ)
        (pe : propext ๐คโ)
       where

open PropositionalTruncation pt

open import UF-Base

open import Dcpo pt fe ๐คโ
open import DcpoExponential pt fe ๐คโ
open import DcpoLifting pt fe ๐คโ pe
open import DcpoMiscelanea pt fe ๐คโ

open import DcpoBilimitsSequential pt fe ๐คโ ๐คโ

open import NaturalsOrder
open import NaturalsAddition renaming (_+_ to _+'_)
open import OrderNotation

\end{code}

We start by defining the โ-indexed diagram of iterated exponentials.

\begin{code}

๐โฅ : โ โ DCPOโฅ {๐คโ} {๐คโ}
๐โฅ zero     = ๐-DCPOโฅ {๐คโ} {๐{๐คโ}} (props-are-sets ๐-is-prop)
๐โฅ (succ n) = ๐โฅ n โนแตแถแตแตโฅ ๐โฅ n

๐ : โ โ DCPO {๐คโ} {๐คโ}
๐ n = prโ (๐โฅ n)

๐-diagram : (n : โ)
          โ DCPO[ ๐ n , ๐ (succ n) ]
          ร DCPO[ ๐ (succ n) , ๐ n ]
๐-diagram zero = (eโ , eโ-continuity) , pโ , pโ-continuity
 where
  eโ : โจ ๐ 0 โฉ โ โจ ๐ 1 โฉ
  eโ x = (ฮป y โ x) , (constant-functions-are-continuous (๐ 0) (๐ 0) x)
  eโ-continuity : is-continuous (๐ 0) (๐ 1) eโ
  eโ-continuity I ฮฑ ฮด = ub , lb-of-ubs
   where
    ub : (i : I) โ eโ (ฮฑ i) โโจ (๐ 1) โฉ eโ (โ (๐ 0) ฮด)
    ub i y =  ฮฑ i          โโจ ๐ 0 โฉ[ โ-is-upperbound (๐ 0) ฮด i ]
              โ (๐ 0) ฮด    โโจ ๐ 0 โฉ
    lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (๐ 1))
                  (eโ (โ (๐ 0) ฮด)) (ฮป x โ eโ (ฮฑ x))
    lb-of-ubs (g , c) ub y =
     โ-is-lowerbound-of-upperbounds (๐ 0) ฮด (g y) (ฮป i โ ub i y)
  pโ : โจ ๐ 1 โฉ โ โจ ๐ 0 โฉ
  pโ (f , c) = f (โฅ (๐โฅ 0))
  pโ-continuity : is-continuous (๐ 1) (๐ 0) pโ
  pโ-continuity I ฮฑ ฮด = ub , lb-of-ubs
   where
    ub : (i : I) โ pโ (ฮฑ i) โโจ ๐ 0 โฉ pโ (โ (๐ 1) {I} {ฮฑ} ฮด)
    ub i = โ-is-upperbound (๐ 1) {I} {ฮฑ} ฮด i (โฅ (๐โฅ 0))
    lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (๐ 0))
                  (pโ (โ (๐ 1) {I} {ฮฑ} ฮด)) (ฮป x โ pโ (ฮฑ x))
    lb-of-ubs y ub =
     โ-is-lowerbound-of-upperbounds (๐ 0) ฮต y ub
      where
       ฮต : is-Directed (๐ 0) (pointwise-family (๐ 0) (๐ 0) ฮฑ (โฅ (๐โฅ 0)))
       ฮต = pointwise-family-is-directed (๐ 0) (๐ 0) ฮฑ ฮด (โฅ (๐โฅ 0))
๐-diagram (succ n) = (e , e-continuity) , (p , p-continuity)
 where
  IH : DCPO[ ๐ n , ๐ (succ n) ] ร DCPO[ ๐ (succ n) , ๐ n ]
  IH = ๐-diagram n
  eโ : DCPO[ ๐ n , ๐ (succ n) ]
  eโ = prโ IH
  pโ : DCPO[ ๐ (succ n) , ๐ n ]
  pโ = prโ IH
  e : โจ ๐ (succ n) โฉ โ โจ ๐ (succ (succ n)) โฉ
  e f = DCPO-โโ (๐ (succ n)) (๐ n) (๐ n) (๐ (succ n)) pโ f eโ
  e-continuity : is-continuous (๐ (succ n)) (๐ (succ (succ n))) e
  e-continuity = โ-is-continuous
                  (๐ (succ n))
                  ((๐ n) โนแตแถแตแต (๐ (succ n)))
                  (๐ (succ (succ n)))
                  (ฮป f โ DCPO-โ (๐ n) (๐ n) (๐ (succ n)) f eโ)
                  (DCPO-โ (๐ (succ n)) (๐ n) (๐ (succ n)) pโ)
                  (DCPO-โ-is-continuousโ (๐ n) (๐ n) (๐ (succ n)) eโ)
                  (DCPO-โ-is-continuousโ (๐ (succ n)) (๐ n)
                   (๐ (succ n)) pโ)
  p : โจ ๐ (succ (succ n)) โฉ โ โจ ๐ (succ n) โฉ
  p f = DCPO-โโ (๐ n) (๐ (succ n)) (๐ (succ n)) (๐ n) eโ f pโ
  p-continuity : is-continuous (๐ (succ (succ n))) (๐ (succ n)) p
  p-continuity = โ-is-continuous
                  (๐ (succ (succ n)))
                  ((๐ n) โนแตแถแตแต (๐ (succ n)))
                  (๐ (succ n))
                  (DCPO-โ (๐ n) (๐ (succ n)) (๐ (succ n)) eโ)
                  (ฮป f โ DCPO-โ (๐ n) (๐ (succ n)) (๐ n) f pโ)
                  (DCPO-โ-is-continuousโ (๐ n) (๐ (succ n))
                   (๐ (succ n)) eโ)
                  (DCPO-โ-is-continuousโ (๐ n) (๐ (succ n)) (๐ n) pโ)

ฯ' : (n : โ) โ DCPO[ ๐ (succ n) , ๐ n ]
ฯ' n = prโ (๐-diagram n)

ฯ : (n : โ) โ โจ ๐ (succ n) โฉ โ โจ ๐ n โฉ
ฯ n = underlying-function (๐ (succ n)) (๐ n) (ฯ' n)

ฯ-is-continuous : (n : โ) โ is-continuous (๐ (succ n)) (๐ n) (ฯ n)
ฯ-is-continuous n = prโ (prโ (๐-diagram n))

ฮต' : (n : โ) โ DCPO[ ๐ n , ๐ (succ n) ]
ฮต' n = prโ (๐-diagram n)

ฮต : (n : โ) โ โจ ๐ n โฉ โ โจ ๐ (succ n) โฉ
ฮต n = underlying-function (๐ n) (๐ (succ n)) (ฮต' n)

ฮต-is-continuous : (n : โ) โ is-continuous (๐ n) (๐ (succ n)) (ฮต n)
ฮต-is-continuous n = prโ (prโ (๐-diagram n))

ฯ-on-0 : (f : โจ ๐ 0 โฉ โ โจ ๐ 0 โฉ) (c : is-continuous (๐ 0) (๐ 0) f)
       โ ฯ 0 (f , c) โก f (โฅ (๐โฅ 0))
ฯ-on-0 f c = refl

ฯ-on-succ : (n : โ) (f : โจ ๐ (succ n) โฉ โ โจ ๐ (succ n) โฉ)
            (c : is-continuous (๐ (succ n)) (๐ (succ n)) f)
          โ [ ๐ n , ๐ n ]โจ ฯ (succ n) (f , c) โฉ โก ฯ n โ f โ ฮต n
ฯ-on-succ n f c = refl

ฯ-on-succ' : (n : โ) (f : DCPO[ ๐ (succ n) , ๐ (succ n) ])
           โ [ ๐ n , ๐ n ]โจ ฯ (succ n) f โฉ
           โก ฯ n โ [ ๐ (succ n) , ๐ (succ n) ]โจ f โฉ โ ฮต n
ฯ-on-succ' n f = refl

ฮต-on-0 : (x : โจ ๐ 0 โฉ) โ [ ๐ 0 , ๐ 0 ]โจ ฮต 0 x โฉ โก (ฮป y โ x)
ฮต-on-0 x = refl

ฮต-on-succ : (n : โ) (f : โจ ๐ n โฉ โ โจ ๐ n โฉ) (c : is-continuous (๐ n) (๐ n) f)
          โ [ ๐ (succ n) , ๐ (succ n) ]โจ ฮต (succ n) (f , c) โฉ โก ฮต n โ f โ ฯ n
ฮต-on-succ n f c = refl

ฮต-section-of-ฯ : (n : โ) โ ฯ n โ ฮต n โผ id
ฮต-section-of-ฯ zero x = refl
ฮต-section-of-ฯ (succ n) (f , _) = to-continuous-function-โก (๐ n) (๐ n) ฮณ
 where
  ฮณ : ฯ n โ ฮต n โ f โ ฯ n โ ฮต n โผ f
  ฮณ x = (ฯ n โ ฮต n โ f โ ฯ n โ ฮต n) x โกโจ IH (f (ฯ n (ฮต n x))) โฉ
        (f โ ฯ n โ ฮต n) x             โกโจ ap f (IH x) โฉ
        f x                           โ
   where
    IH : ฯ n โ ฮต n โผ id
    IH = ฮต-section-of-ฯ n

ฮตฯ-deflation : (n : โ) (f : โจ ๐ (succ n) โฉ) โ ฮต n (ฯ n f) โโจ ๐ (succ n) โฉ f
ฮตฯ-deflation zero (f , c) x =
 f (โฅ (๐โฅ 0)) โโจ ๐ 0 โฉ[ m (โฅ (๐โฅ 0)) x (โฅ-is-least (๐โฅ 0) x) ]
 f x          โโจ ๐ 0 โฉ
  where
   m : is-monotone (๐ 0) (๐ 0) f
   m = monotone-if-continuous (๐ 0) (๐ 0) (f , c)
ฮตฯ-deflation (succ n) (f , c) x =
 {- I would use the โโจ ๐ (succ n) โฉ[ ? ] syntax here, but Agda has trouble
    figuring out some implicit arguments. -}
 transitivity (๐ (succ n))
  ((ฮต n โ ฯ n โ f โ ฮต n โ ฯ n) x) (f (ฮต n (ฯ n x))) (f x)
  (IH (f (ฮต n (ฯ n x))))
  (m (ฮต n (ฯ n x)) x (IH x))
{-
 (ฮต n โ ฯ n โ f โ ฮต n โ ฯ n) x โโจ ๐ (succ n) โฉ[ IH (f (ฮต n (ฯ n x)))     ]
 f (ฮต n (ฯ n x))               โโจ ๐ (succ n) โฉ[ m (ฮต n (ฯ n x)) x (IH x) ]
 f x                           โโจ ๐ (succ n) โฉ -}
  where
   IH : (g : โจ ๐ (succ n) โฉ) โ ฮต n (ฯ n g) โโจ ๐ (succ n) โฉ g
   IH = ฮตฯ-deflation n
   m : is-monotone (๐ (succ n)) (๐ (succ n)) f
   m = monotone-if-continuous (๐ (succ n)) (๐ (succ n)) (f , c)

\end{code}

With the diagram defined, we consider its bilimit Dโ.

\begin{code}

open SequentialDiagram
      ๐ ฮต ฯ
      ฮตฯ-deflation
      ฮต-section-of-ฯ
      ฮต-is-continuous
      ฯ-is-continuous

ฯ-exp-to-succ : (n : โ) โ โจ ๐โ โนแตแถแตแต ๐โ โฉ โ โจ ๐ (succ n) โฉ
ฯ-exp-to-succ n f = DCPO-โโ (๐ n) ๐โ ๐โ (๐ n) (ฮตโ' n) f (ฯโ' n)

ฯ-exp-to-succ-is-continuous : (n : โ)
                            โ is-continuous (๐โ โนแตแถแตแต ๐โ) (๐ (succ n))
                               (ฯ-exp-to-succ n)
ฯ-exp-to-succ-is-continuous n =
 DCPO-โโ-is-continuousโ (๐ n) ๐โ ๐โ (๐ n) (ฮตโ' n) (ฯโ' n)

ฯ-exp : (n : โ) โ โจ ๐โ โนแตแถแตแต ๐โ โฉ โ โจ ๐ n โฉ
ฯ-exp zero     = ฯ 0 โ ฯ-exp-to-succ 0
ฯ-exp (succ n) = ฯ-exp-to-succ n

ฯ-exp-is-continuous : (n : โ) โ is-continuous (๐โ โนแตแถแตแต ๐โ) (๐ n) (ฯ-exp n)
ฯ-exp-is-continuous zero = โ-is-continuous (๐โ โนแตแถแตแต ๐โ) (๐ 1) (๐ 0)
                            (ฯ-exp-to-succ 0) (ฯ 0)
                            (ฯ-exp-to-succ-is-continuous 0) (ฯ-is-continuous 0)
ฯ-exp-is-continuous (succ n) = ฯ-exp-to-succ-is-continuous n

ฯ-exp-commutes-with-ฯ : (n : โ) โ ฯ n โ ฯ-exp (succ n) โผ ฯ-exp n
ฯ-exp-commutes-with-ฯ zero f = refl
ฯ-exp-commutes-with-ฯ (succ n) (f , c) =
 to-continuous-function-โก (๐ n) (๐ n) ฮณ
   where
    h : DCPO[ ๐ (succ n) , ๐ (succ n) ]
    h = DCPO-โโ (๐ (succ n)) ๐โ ๐โ (๐ (succ n))
         (ฮตโ' (succ n)) (f , c) (ฯโ' (succ n))
    ฮณ : ([ ๐ n , ๐ n ]โจ ฯ (succ n) h โฉ) โผ ฯโ n โ f โ ฮตโ n
    ฮณ x = [ ๐ n , ๐ n ]โจ (ฯ (succ n) h) โฉ x                       โกโจ eโ   โฉ
          (ฯ n โ [ ๐ (succ n) , ๐ (succ n) ]โจ h โฉ โ ฮต n) x        โกโจ refl โฉ
          (ฯ n โ ฯโ (succ n) โ f') x                              โกโจ eโ   โฉ
          (ฯโบ {n} {succ n} (โค-succ n) โ ฯโ (succ n) โ f') x       โกโจ eโ   โฉ
          (ฯโ n โ f โ ฮตโ (succ n) โ ฮต n) x                        โกโจ eโ   โฉ
          (ฯโ n โ f โ ฮตโ (succ n) โ ฮตโบ {n} {succ n} (โค-succ n)) x โกโจ eโ   โฉ
          (ฯโ n โ f โ ฮตโ n) x                                     โ
           where
            f' : โจ ๐ n โฉ โ โจ ๐โ โฉ
            f' = f โ ฮตโ (succ n) โ ฮต n
            eโ = happly (ฯ-on-succ' n h) x
            eโ = ฯ-in-terms-of-ฯโบ n (ฯโ (succ n) (f' x))
            eโ = ฯโ-commutes-with-ฯs n (succ n) (โค-succ n)
                  (f (ฮตโ (succ n) (ฮต n x)))
            eโ = ap (ฯโ n โ f โ ฮตโ (succ n)) (ฮต-in-terms-of-ฮตโบ n x)
            eโ = ap (ฯโ n โ f) (ฮตโ-commutes-with-ฮตs n (succ n) (โค-succ n) x)

ฯ-exp-commutes-with-ฯโบ : (n m : โ) (l : n โค m) โ ฯโบ {n} {m} l โ ฯ-exp m โผ ฯ-exp n
ฯ-exp-commutes-with-ฯโบ n m l = commute-with-ฯs-lemma (๐โ โนแตแถแตแต ๐โ)
                            ฯ-exp ฯ-exp-commutes-with-ฯ n m l

open DcpoCone (๐โ โนแตแถแตแต ๐โ) ฯ-exp ฯ-exp-is-continuous ฯ-exp-commutes-with-ฯโบ

ฯ-expโ : โจ ๐โ โนแตแถแตแต ๐โ โฉ โ โจ ๐โ โฉ
ฯ-expโ = limit-mediating-arrow

ฯ-expโ-is-continuous : is-continuous (๐โ โนแตแถแตแต ๐โ) ๐โ ฯ-expโ
ฯ-expโ-is-continuous = limit-mediating-arrow-is-continuous

ฯ-expโ' : DCPO[ ๐โ โนแตแถแตแต ๐โ , ๐โ ]
ฯ-expโ' = ฯ-expโ , ฯ-expโ-is-continuous

\end{code}

The point is to prove that the map ฯ-expโ : โจ ๐โ โนแตแถแตแต ๐โ โฉ โ โจ ๐โ โฉ is an
isomorphism.

\begin{code}

ฮต-exp-from-succ : (n : โ) โ โจ ๐ (succ n) โฉ โ โจ ๐โ โนแตแถแตแต ๐โ โฉ
ฮต-exp-from-succ n f = DCPO-โโ ๐โ (๐ n) (๐ n) ๐โ (ฯโ' n) f (ฮตโ' n)

ฮต-exp-from-succ-is-continuous : (n : โ)
                              โ is-continuous (๐ (succ n)) (๐โ โนแตแถแตแต ๐โ)
                                 (ฮต-exp-from-succ n)
ฮต-exp-from-succ-is-continuous n = DCPO-โโ-is-continuousโ ๐โ (๐ n) (๐ n) ๐โ
                                   (ฯโ' n) (ฮตโ' n)

ฮต-exp : (n : โ) โ โจ ๐ n โฉ โ โจ ๐โ โนแตแถแตแต ๐โ โฉ
ฮต-exp zero     = ฮต-exp-from-succ 0 โ ฮต 0
ฮต-exp (succ n) = ฮต-exp-from-succ n

ฮต-exp-is-continuous : (n : โ) โ is-continuous (๐ n) (๐โ โนแตแถแตแต ๐โ) (ฮต-exp n)
ฮต-exp-is-continuous zero = โ-is-continuous (๐ 0) (๐ 1) (๐โ โนแตแถแตแต ๐โ)
                            (ฮต 0) (ฮต-exp-from-succ 0)
                            (ฮต-is-continuous 0) (ฮต-exp-from-succ-is-continuous 0)
ฮต-exp-is-continuous (succ n) = ฮต-exp-from-succ-is-continuous n

ฮต-exp-commutes-with-ฮต : (n : โ) โ ฮต-exp (succ n) โ ฮต n โผ ฮต-exp n
ฮต-exp-commutes-with-ฮต zero x = refl
ฮต-exp-commutes-with-ฮต (succ n) (f , c) =
 to-continuous-function-โก ๐โ ๐โ ฮณ
   where
    ฮต-expโ : โจ ๐โ โฉ โ โจ ๐โ โฉ
    ฮต-expโ = [ ๐โ , ๐โ ]โจ ฮต-exp (succ (succ n)) (ฮต (succ n) (f , c)) โฉ
    ฮต-expโ : โจ ๐โ โฉ โ โจ ๐โ โฉ
    ฮต-expโ = [ ๐โ , ๐โ ]โจ ฮต-exp (succ n) (f , c) โฉ
    ฮณ : ฮต-expโ โผ ฮต-expโ
    ฮณ ฯ = ฮต-expโ ฯ                                                โกโจ refl โฉ
          (ฮตโ (succ n) โ ฮต n โ h) ฯ                               โกโจ eโ   โฉ
          (ฮตโ (succ n) โ ฮตโบ {n} {succ n} (โค-succ n) โ h) ฯ        โกโจ eโ   โฉ
          (ฮตโ n โ h) ฯ                                            โกโจ refl โฉ
          (ฮตโ n โ f โ ฯ n โ ฯโ (succ n)) ฯ                        โกโจ eโ โฉ
          (ฮตโ n โ f โ ฯโบ {n} {succ n} (โค-succ n) โ ฯโ (succ n)) ฯ โกโจ eโ โฉ
          (ฮตโ n โ f โ ฯโ n) ฯ                                     โกโจ refl โฉ
          ฮต-expโ ฯ                                                โ
     where
      h : โจ ๐โ โฉ โ โจ ๐ n โฉ
      h = f โ ฯ n โ ฯโ (succ n)
      eโ = ap (ฮตโ (succ n)) (ฮต-in-terms-of-ฮตโบ n (h ฯ))
      eโ = ฮตโ-commutes-with-ฮตs n (succ n) (โค-succ n) (h ฯ)
      eโ = ap (ฮตโ n โ f) (ฯ-in-terms-of-ฯโบ n (ฯโ (succ n) ฯ))
      eโ = ap (ฮตโ n โ f) (ฯโ-commutes-with-ฯs n (succ n) (โค-succ n) ฯ)

ฮต-exp-commutes-with-ฮตโบ : (n m : โ) (l : n โค m) โ ฮต-exp m โ ฮตโบ {n} {m} l โผ ฮต-exp n
ฮต-exp-commutes-with-ฮตโบ n m l = commute-with-ฮตs-lemma (๐โ โนแตแถแตแต ๐โ) ฮต-exp
                                ฮต-exp-commutes-with-ฮต n m l

open DcpoCocone (๐โ โนแตแถแตแต ๐โ) ฮต-exp ฮต-exp-is-continuous ฮต-exp-commutes-with-ฮตโบ

ฮต-expโ : โจ ๐โ โฉ โ โจ ๐โ โนแตแถแตแต ๐โ โฉ
ฮต-expโ = colimit-mediating-arrow

ฮต-expโ-is-continuous : is-continuous ๐โ (๐โ โนแตแถแตแต ๐โ) ฮต-expโ
ฮต-expโ-is-continuous = colimit-mediating-arrow-is-continuous

ฮต-expโ' : DCPO[ ๐โ , ๐โ โนแตแถแตแต ๐โ ]
ฮต-expโ' = ฮต-expโ , ฮต-expโ-is-continuous

\end{code}

The map ฮต-expโ : โจ ๐โ โฉ โ โจ ๐โ โนแตแถแตแต ๐โ โฉ is going to be the desired inverse of
ฯ-expโ.

\begin{code}

ฮต-exp-family : โจ ๐โ โฉ โ โ โ โจ ๐โ โนแตแถแตแต ๐โ โฉ
ฮต-exp-family ฯ n = ฮต-exp (succ n) (โฆ ฯ โฆ (succ n))

ฮต-exp-family-is-directed : (ฯ : โจ ๐โ โฉ)
                         โ is-Directed (๐โ โนแตแถแตแต ๐โ) (ฮต-exp-family ฯ)
ฮต-exp-family-is-directed ฯ = โฃ 0 โฃ , ฮณ
 where
  ฮณ : is-semidirected (underlying-order (๐โ โนแตแถแตแต ๐โ)) (ฮต-exp-family ฯ)
  ฮณ n m = โฅโฅ-functor g h
   where
    ฮด : is-Directed (๐โ โนแตแถแตแต ๐โ) (colimit-family ฯ)
    ฮด = colimit-family-is-directed ฯ
    h : โ k ๊ โ , colimit-family ฯ (succ n) โโจ ๐โ โนแตแถแตแต ๐โ โฉ colimit-family ฯ k
                ร colimit-family ฯ (succ m) โโจ ๐โ โนแตแถแตแต ๐โ โฉ colimit-family ฯ k
    h = semidirected-if-Directed (๐โ โนแตแถแตแต ๐โ) (colimit-family ฯ) ฮด
         (succ n) (succ m)
    g : (ฮฃ k ๊ โ , colimit-family ฯ (succ n) โโจ ๐โ โนแตแถแตแต ๐โ โฉ colimit-family ฯ k
                 ร colimit-family ฯ (succ m) โโจ ๐โ โนแตแถแตแต ๐โ โฉ colimit-family ฯ k)
      โ ฮฃ k ๊ โ , ฮต-exp-family ฯ n โโจ ๐โ โนแตแถแตแต ๐โ โฉ ฮต-exp-family ฯ k
                ร ฮต-exp-family ฯ m โโจ ๐โ โนแตแถแตแต ๐โ โฉ ฮต-exp-family ฯ k
    g (k , lโ , lโ) = k , lโ' , lโ'
     where
      lโ : colimit-family ฯ k โโจ ๐โ โนแตแถแตแต ๐โ โฉ ฮต-exp-family ฯ k
      lโ = colimit-family-is-monotone ฯ k (succ k) (โค-succ k)
      lโ' : ฮต-exp-family ฯ n โโจ ๐โ โนแตแถแตแต ๐โ โฉ ฮต-exp-family ฯ k
      lโ' = transitivity (๐โ โนแตแถแตแต ๐โ)
             (ฮต-exp-family ฯ n) (colimit-family ฯ k) (ฮต-exp-family ฯ k)
             lโ lโ
      lโ' : ฮต-exp-family ฯ m โโจ ๐โ โนแตแถแตแต ๐โ โฉ ฮต-exp-family ฯ k
      lโ' = transitivity (๐โ โนแตแถแตแต ๐โ)
             (ฮต-exp-family ฯ m) (colimit-family ฯ k) (ฮต-exp-family ฯ k)
             lโ lโ

ฮต-expโ-alt : (ฯ : โจ ๐โ โฉ)
           โ ฮต-expโ ฯ โก โ (๐โ โนแตแถแตแต ๐โ) (ฮต-exp-family-is-directed ฯ)
ฮต-expโ-alt ฯ = antisymmetry (๐โ โนแตแถแตแต ๐โ) (ฮต-expโ ฯ) (โ (๐โ โนแตแถแตแต ๐โ) ฮดโ) a b
 where
  ฮดโ : is-Directed (๐โ โนแตแถแตแต ๐โ) (colimit-family ฯ)
  ฮดโ = colimit-family-is-directed ฯ
  ฮดโ : is-Directed (๐โ โนแตแถแตแต ๐โ) (ฮต-exp-family ฯ)
  ฮดโ = ฮต-exp-family-is-directed ฯ
  a : ฮต-expโ ฯ โโจ ๐โ โนแตแถแตแต ๐โ โฉ โ (๐โ โนแตแถแตแต ๐โ) ฮดโ
  a = โ-is-monotone (๐โ โนแตแถแตแต ๐โ) ฮดโ ฮดโ ฮณ
   where
    ฮณ : (n : โ)
      โ colimit-family ฯ n โโจ ๐โ โนแตแถแตแต ๐โ โฉ ฮต-exp-family ฯ n
    ฮณ n = colimit-family-is-monotone ฯ n (succ n) (โค-succ n)
  b : โ (๐โ โนแตแถแตแต ๐โ) ฮดโ โโจ ๐โ โนแตแถแตแต ๐โ โฉ ฮต-expโ ฯ
  b = โ-is-lowerbound-of-upperbounds (๐โ โนแตแถแตแต ๐โ) ฮดโ (ฮต-expโ ฯ) ฮณ
   where
    ฮณ : is-upperbound (underlying-order (๐โ โนแตแถแตแต ๐โ))
         (ฮต-expโ ฯ) (ฮต-exp-family ฯ)
    ฮณ n = โ-is-upperbound (๐โ โนแตแถแตแต ๐โ) ฮดโ (succ n)

ฯ-exp-family : โจ ๐โ โนแตแถแตแต ๐โ โฉ โ โ โ โจ ๐โ โฉ
ฯ-exp-family ฯ n = ฮตโ (succ n) (ฯ-exp (succ n) ฯ)

\end{code}

In the code below we would like to write things as
 x โโจ ๐โ โฉ[ u ]
 y โโจ ๐โ โฉ[ v ]
 z โโจ ๐โ โฉ

However, Agda has trouble figuring out some implicit arguments. (I believe
because it can't 'see' the additional witnesses (of continuity, etc.) that the
underlying functions of x, y and z are equipped with.)

Not using the _โโจ_โฉ[_] syntax in favour of using transitivity directly and
explicitly naming all its arguments solves the above problem, but it doesn't
read very well.

Instead, we solve the problem by noting that the order on ๐โ is pointwise and
that therefore we are really proving that for every i : โ we have
 โฆ x โฆ i โโจ ๐ i โฉ[ u i ]
 โฆ y โฆ i โโจ ๐ i โฉ[ v i ]
 โฆ z โฆ i โโจ ๐ i โฉ

\begin{code}

ฯ-exp-family-is-directed : (ฯ : โจ ๐โ โนแตแถแตแต ๐โ โฉ)
                         โ is-Directed ๐โ (ฯ-exp-family ฯ)
ฯ-exp-family-is-directed ฯ = โฃ 0 โฃ , ฮณ
 where
  ฮณ : is-semidirected (underlying-order ๐โ) (ฯ-exp-family ฯ)
  ฮณ n m = โฅโฅ-functor g h
   where
    ฯ : โจ ๐โ โฉ
    ฯ = ฯ-expโ ฯ
    ฮด : is-Directed ๐โ (ฮตโ-family ฯ)
    ฮด = ฮตโ-family-is-directed ฯ
    h : โ k ๊ โ , ฮตโ-family ฯ (succ n) โโจ ๐โ โฉ ฮตโ-family ฯ k
                ร ฮตโ-family ฯ (succ m) โโจ ๐โ โฉ ฮตโ-family ฯ k
    h = semidirected-if-Directed ๐โ (ฮตโ-family ฯ) ฮด (succ n) (succ m)
    g : (ฮฃ k ๊ โ , ฮตโ-family ฯ (succ n) โโจ ๐โ โฉ ฮตโ-family ฯ k
                 ร ฮตโ-family ฯ (succ m) โโจ ๐โ โฉ ฮตโ-family ฯ k)
      โ ฮฃ k ๊ โ , ฯ-exp-family ฯ n โโจ ๐โ โฉ ฯ-exp-family ฯ k
                ร ฯ-exp-family ฯ m โโจ ๐โ โฉ ฯ-exp-family ฯ k
    g (k , lโ , lโ) = k , lโ' , lโ'
     where
      lโ : ฮตโ-family ฯ k โโจ ๐โ โฉ ฮตโ-family ฯ (succ k)
      lโ = ฮตโ-family-is-monotone ฯ k (succ k) (โค-succ k)
      lโ' : ฯ-exp-family ฯ n โโจ ๐โ โฉ ฯ-exp-family ฯ k
      lโ' i =
       โฆ ฯ-exp-family ฯ n โฆ     i โโจ ๐ i โฉ[ reflexivity ๐โ (ฯ-exp-family ฯ n) i ]
       โฆ ฮตโ-family ฯ (succ n) โฆ i โโจ ๐ i โฉ[ lโ i ]
       โฆ ฮตโ-family ฯ k        โฆ i โโจ ๐ i โฉ[ lโ i ]
       โฆ ฮตโ-family ฯ (succ k) โฆ i โโจ ๐ i โฉ[ reflexivity ๐โ (ฯ-exp-family ฯ k) i ]
       โฆ ฯ-exp-family ฯ k โฆ     i โโจ ๐ i โฉ
      lโ' : ฯ-exp-family ฯ m โโจ ๐โ โฉ ฯ-exp-family ฯ k
      lโ' i =
       โฆ ฯ-exp-family ฯ m โฆ     i โโจ ๐ i โฉ[ reflexivity ๐โ (ฯ-exp-family ฯ m) i ]
       โฆ ฮตโ-family ฯ (succ m) โฆ i โโจ ๐ i โฉ[ lโ i ]
       โฆ ฮตโ-family ฯ k        โฆ i โโจ ๐ i โฉ[ lโ i ]
       โฆ ฮตโ-family ฯ (succ k) โฆ i โโจ ๐ i โฉ[ reflexivity ๐โ (ฯ-exp-family ฯ k) i ]
       โฆ ฯ-exp-family ฯ k โฆ     i โโจ ๐ i โฉ

ฯ-expโ-alt : (ฯ : โจ ๐โ โนแตแถแตแต ๐โ โฉ)
           โ ฯ-expโ ฯ โก โ ๐โ (ฯ-exp-family-is-directed ฯ)
ฯ-expโ-alt ฯ = ฯ                              โกโจ โ-of-ฮตโs ฯ โฉ
               โ ๐โ (ฮตโ-family-is-directed ฯ) โกโจ ฮณ โฉ
               โ ๐โ (ฯ-exp-family-is-directed ฯ) โ
 where
  ฯ : โจ ๐โ โฉ
  ฯ = ฯ-expโ ฯ
  ฮณ : โ ๐โ (ฮตโ-family-is-directed ฯ) โก โ ๐โ (ฯ-exp-family-is-directed ฯ)
  ฮณ = antisymmetry ๐โ (โ ๐โ ฮดโ) (โ ๐โ ฮดโ) a b
   where
    ฮดโ : is-Directed ๐โ (ฮตโ-family ฯ)
    ฮดโ = ฮตโ-family-is-directed ฯ
    ฮดโ : is-Directed ๐โ (ฯ-exp-family ฯ)
    ฮดโ = ฯ-exp-family-is-directed ฯ
    a : โ ๐โ ฮดโ โโจ ๐โ โฉ โ ๐โ ฮดโ
    a = โ-is-monotone ๐โ ฮดโ ฮดโ h
     where
      h : (n : โ) โ ฮตโ-family ฯ n โโจ ๐โ โฉ ฯ-exp-family ฯ n
      h n i = โฆ ฮตโ-family ฯ n        โฆ i โโจ ๐ i โฉ[ ฮตโ-family-is-monotone ฯ n (succ n) (โค-succ n) i ]
              โฆ ฮตโ-family ฯ (succ n) โฆ i โโจ ๐ i โฉ[ reflexivity ๐โ (ฮตโ-family ฯ (succ n)) i ]
              โฆ ฯ-exp-family ฯ n     โฆ i โโจ ๐ i โฉ
    b : โ ๐โ ฮดโ โโจ ๐โ โฉ โ ๐โ ฮดโ
    b = โ-is-lowerbound-of-upperbounds ๐โ ฮดโ (โ ๐โ ฮดโ) h
     where
      h : is-upperbound (underlying-order ๐โ) (โ ๐โ ฮดโ) (ฯ-exp-family ฯ)
      h n i = โฆ ฯ-exp-family ฯ n     โฆ i โโจ ๐ i โฉ[ reflexivity ๐โ (ฯ-exp-family ฯ n) i ]
              โฆ ฮตโ-family ฯ (succ n) โฆ i โโจ ๐ i โฉ[ โ-is-upperbound ๐โ ฮดโ (succ n) i ]
              โฆ โ ๐โ ฮดโ              โฆ i โโจ ๐ i โฉ

ฯ-exp-family-is-monotone : (ฯ : โจ ๐โ โนแตแถแตแต ๐โ โฉ) {n m : โ} โ n โค m
                         โ ฯ-exp-family ฯ n โโจ ๐โ โฉ ฯ-exp-family ฯ m
ฯ-exp-family-is-monotone ฯ {n} {m} l i =
 โฆ ฯ-exp-family ฯ n              โฆ i โโจ ๐ i โฉ[ reflexivity ๐โ (ฯ-exp-family ฯ n) i ]
 โฆ ฮตโ-family (ฯ-expโ ฯ) (succ n) โฆ i โโจ ๐ i โฉ[ u i ]
 โฆ ฮตโ-family (ฯ-expโ ฯ) (succ m) โฆ i โโจ ๐ i โฉ[ reflexivity ๐โ (ฯ-exp-family ฯ m) i ]
 โฆ ฯ-exp-family ฯ m              โฆ i โโจ ๐ i โฉ
  where
   u = ฮตโ-family-is-monotone (ฯ-expโ ฯ) (succ n) (succ m) l

ฯ-exp-family-is-monotone' : (ฯ ฯ : โจ ๐โ โนแตแถแตแต ๐โ โฉ) {n : โ}
                          โ ฯ โโจ ๐โ โนแตแถแตแต ๐โ โฉ ฯ
                          โ ฯ-exp-family ฯ n โโจ ๐โ โฉ ฯ-exp-family ฯ n
ฯ-exp-family-is-monotone' ฯ ฯ {n} l i =
 โฆ ฯ-exp-family ฯ n               โฆ i โโจ ๐ i โฉ[ uโ i ]
 โฆ ฮตโ (succ n) (ฯ-exp (succ n) ฯ) โฆ i โโจ ๐ i โฉ[ uโ i ]
 โฆ ฮตโ (succ n) (ฯ-exp (succ n) ฯ) โฆ i โโจ ๐ i โฉ[ uโ i ]
 โฆ ฯ-exp-family ฯ n               โฆ i โโจ ๐ i โฉ
  where
   uโ = reflexivity ๐โ (ฮตโ (succ n) (ฯ-exp (succ n) ฯ))
   uโ = monotone-if-continuous (๐โ โนแตแถแตแต ๐โ) ๐โ f ฯ ฯ l
    where
     f : DCPO[ ๐โ โนแตแถแตแต ๐โ , ๐โ ]
     f = DCPO-โ (๐โ โนแตแถแตแต ๐โ) (๐ (succ n)) ๐โ
          (ฯ-exp (succ n) , ฯ-exp-is-continuous (succ n))
          (ฮตโ' (succ n))
   uโ = reflexivity ๐โ (ฮตโ (succ n) (ฯ-exp (succ n) ฯ))

ฮต-exp-family-is-monotone : (ฯ : โจ ๐โ โฉ) {n m : โ} โ n โค m
                         โ ฮต-exp-family ฯ n โโจ ๐โ โนแตแถแตแต ๐โ โฉ ฮต-exp-family ฯ m
ฮต-exp-family-is-monotone ฯ {n} {m} l =
 colimit-family-is-monotone ฯ (succ n) (succ m) l

ฮต-exp-family-is-monotone' : (ฯ ฯ : โจ ๐โ โฉ) {n : โ} โ ฯ โโจ ๐โ โฉ ฯ
                          โ ฮต-exp-family ฯ n โโจ ๐โ โนแตแถแตแต ๐โ โฉ ฮต-exp-family ฯ n
ฮต-exp-family-is-monotone' ฯ ฯ {n} l ฯ i =
 โฆ [ ๐โ , ๐โ ]โจ ฮต-exp-family ฯ n โฉ ฯ                 โฆ i โโจ ๐ i โฉ[ uโ i ]
 โฆ (ฮตโ n โ [ ๐ n , ๐ n ]โจ โฆ ฯ โฆ (succ n) โฉ โ ฯโ n) ฯ โฆ i โโจ ๐ i โฉ[ uโ i ]
 โฆ (ฮตโ n โ [ ๐ n , ๐ n ]โจ โฆ ฯ โฆ (succ n) โฉ โ ฯโ n) ฯ โฆ i โโจ ๐ i โฉ[ uโ i ]
 โฆ [ ๐โ , ๐โ ]โจ ฮต-exp-family ฯ n โฉ ฯ                 โฆ i โโจ ๐ i โฉ
  where
   uโ = reflexivity ๐โ ([ ๐โ , ๐โ ]โจ ฮต-exp-family ฯ n โฉ ฯ)
   uโ = monotone-if-continuous (๐ n) ๐โ (ฮตโ' n)
         ([ ๐ n , ๐ n ]โจ โฆ ฯ โฆ (succ n) โฉ (ฯโ n ฯ))
         ([ ๐ n , ๐ n ]โจ โฆ ฯ โฆ (succ n) โฉ (ฯโ n ฯ))
         (l (succ n) (ฯโ n ฯ))
   uโ = reflexivity ๐โ ([ ๐โ , ๐โ ]โจ ฮต-exp-family ฯ n โฉ ฯ)

\end{code}

Finally, we have established enough material to prove that ฮต-expโ is the inverse
of ฯ-expโ.

\begin{code}

ฮต-expโ-section-of-ฯ-expโ : ฯ-expโ โ ฮต-expโ โผ id
ฮต-expโ-section-of-ฯ-expโ ฯ =
 ฯ-expโ (ฮต-expโ ฯ)                                 โกโจ ap ฯ-expโ (ฮต-expโ-alt ฯ) โฉ
 ฯ-expโ (โ (๐โ โนแตแถแตแต ๐โ) ฮดโ)                       โกโจ eโ โฉ
 โ ๐โ {โ} {ฮป n โ (ฯ-expโ โ ฮต-exp-family ฯ) n} ฮดโ   โกโจ โ-family-โก ๐โ p ฮดโ โฉ
 โ ๐โ {โ} {ฮป n โ โ ๐โ {โ} {ฮป m โ f n m} (ฮดโ n)} ฮดโ โกโจ eโ โฉ
 โ ๐โ {โ} {ฮป n โ ฮตโ n (โฆ ฯ โฆ n)} ฮดโ                โกโจ (โ-of-ฮตโs ฯ) โปยน โฉ
 ฯ                                                 โ
  where
   f : โ โ โ โ โจ ๐โ โฉ
   f n m = ฯ-exp-family (ฮต-exp-family ฯ n) m
   ฮดโ : is-Directed (๐โ โนแตแถแตแต ๐โ) (ฮต-exp-family ฯ)
   ฮดโ = ฮต-exp-family-is-directed ฯ
   ฮดโ : is-Directed ๐โ (ฯ-expโ โ ฮต-exp-family ฯ)
   ฮดโ = image-is-directed' (๐โ โนแตแถแตแต ๐โ) ๐โ ฯ-expโ' ฮดโ
   ฮดโ : (n : โ) โ is-Directed ๐โ (ฯ-exp-family (ฮต-exp-family ฯ n))
   ฮดโ n = ฯ-exp-family-is-directed (ฮต-exp-family ฯ n)
   p : ฯ-expโ โ ฮต-exp-family ฯ โก ฮป n โ โ ๐โ (ฮดโ n)
   p = dfunext fe (ฮป n โ ฯ-expโ-alt (ฮต-exp-family ฯ n))
   ฮดโ : is-Directed ๐โ (ฮป n โ โ ๐โ (ฮดโ n))
   ฮดโ = transport (is-Directed ๐โ) p ฮดโ
   ฮดโ : is-Directed ๐โ (ฮตโ-family ฯ)
   ฮดโ = ฮตโ-family-is-directed ฯ
   eโ = continuous-โ-โก (๐โ โนแตแถแตแต ๐โ) ๐โ ฯ-expโ' ฮดโ
   eโ = antisymmetry ๐โ (โ ๐โ ฮดโ) (โ ๐โ ฮดโ) lโ lโ
    where
     r : (n : โ) โ f n n โก ฮตโ-family ฯ (succ n)
     r n = ap (ฮตโ (succ n)) ฮณ
      where
       ฮณ : ฯ-exp (succ n) (ฮต-exp-family ฯ n) โก โฆ ฯ โฆ (succ n)
       ฮณ = to-continuous-function-โก (๐ n) (๐ n) ฯ
        where
         ฯ' : โจ ๐ n โฉ โ โจ ๐ n โฉ
         ฯ' = [ ๐ n , ๐ n ]โจ โฆ ฯ โฆ (succ n) โฉ
         ฯ : ฯโ n โ ฮตโ n โ ฯ' โ ฯโ n โ ฮตโ n โผ ฯ'
         ฯ x = (ฯโ n โ ฮตโ n โ ฯ' โ ฯโ n โ ฮตโ n) x โกโจ pโ โฉ
               (ฯ' โ ฯโ n โ ฮตโ n) x               โกโจ pโ โฉ
               ฯ' x                               โ
          where
           pโ = ฮตโ-section-of-ฯโ (ฯ' (ฯโ n (ฮตโ n x)))
           pโ = ap ฯ' (ฮตโ-section-of-ฯโ x)
     lโ : โ ๐โ ฮดโ โโจ ๐โ โฉ โ ๐โ ฮดโ
     lโ = โ-is-lowerbound-of-upperbounds ๐โ ฮดโ (โ ๐โ ฮดโ) ฮณ
      where
       ฮณ : is-upperbound (underlying-order ๐โ) (โ ๐โ ฮดโ) (ฮป n โ โ ๐โ (ฮดโ n))
       ฮณ n = โ-is-lowerbound-of-upperbounds ๐โ (ฮดโ n) (โ ๐โ ฮดโ) ฯ
        where
         ฯ : is-upperbound (underlying-order ๐โ) (โ ๐โ ฮดโ) (f n)
         ฯ m i = โฆ f n m                       โฆ i โโจ ๐ i โฉ[ uโ i ]
                 โฆ f (n +' m) m                โฆ i โโจ ๐ i โฉ[ uโ i ]
                 โฆ f (n +' m) (n +' m)         โฆ i โโจ ๐ i โฉ[ uโ i ]
                 โฆ ฮตโ-family ฯ (succ (n +' m)) โฆ i โโจ ๐ i โฉ[ uโ i ]
                 โฆ โ ๐โ ฮดโ                     โฆ i โโจ ๐ i โฉ
          where
           uโ = ฯ-exp-family-is-monotone'
                 (ฮต-exp-family ฯ n) (ฮต-exp-family ฯ (n +' m))
                 (ฮต-exp-family-is-monotone ฯ (โค-+ n m))
           uโ = ฯ-exp-family-is-monotone (ฮต-exp-family ฯ (n +' m)) (โค-+' n m)
           uโ = โก-to-โ ๐โ (r (n +' m))
           uโ = โ-is-upperbound ๐โ ฮดโ (succ (n +' m))
     lโ : โ ๐โ ฮดโ โโจ ๐โ โฉ โ ๐โ ฮดโ
     lโ = โ-is-lowerbound-of-upperbounds ๐โ ฮดโ (โ ๐โ ฮดโ) ฮณ
      where
       ฮณ : is-upperbound (underlying-order ๐โ) (โ ๐โ ฮดโ) (ฮตโ-family ฯ)
       ฮณ n i =
        โฆ ฮตโ-family ฯ n        โฆ i โโจ ๐ i โฉ[ u i                           ]
        โฆ ฮตโ-family ฯ (succ n) โฆ i โโจ ๐ i โฉ[ โก-to-โ ๐โ ((r n) โปยน) i        ]
        โฆ f n n                โฆ i โโจ ๐ i โฉ[ โ-is-upperbound ๐โ (ฮดโ n) n i ]
        โฆ โ ๐โ (ฮดโ n)          โฆ i โโจ ๐ i โฉ[ โ-is-upperbound ๐โ ฮดโ n i     ]
        โฆ โ ๐โ ฮดโ              โฆ i โโจ ๐ i โฉ
         where
          u = ฮตโ-family-is-monotone ฯ n (succ n) (โค-succ n)

ฯ-expโ-section-of-ฮต-expโ : ฮต-expโ โ ฯ-expโ โผ id
ฯ-expโ-section-of-ฮต-expโ ฯ =
 ฮต-expโ (ฯ-expโ ฯ)                                โกโจ eโ โฉ
 ฮต-expโ (โ ๐โ ฮดโ)                                 โกโจ eโ โฉ
 โ ๐ {โ} {ฮป n โ (ฮต-expโ โ ฯ-exp-family ฯ) n} ฮดโ   โกโจ eโ โฉ
 โ ๐ {โ} {ฮป n โ โ ๐ {โ} {ฮป m โ f' n m} (ฮดโ n)} ฮดโ โกโจ eโ โฉ
 โ ๐ {โ} {ฮป n โ f' n n} ฮดโ                        โกโจ eโ โฉ
 โ ๐ {โ} {ฮป n โ g' n n} ฮดโ                        โกโจ eโ โฉ
 DCPO-โโ ๐โ ๐โ ๐โ ๐โ s ฯ s                        โกโจ eโ โฉ
 ฯ                                                โ
  where
   ๐ : DCPO {๐คโ} {๐คโ}
   ๐ = ๐โ โนแตแถแตแต ๐โ
   ฯ : โจ ๐โ โฉ โ โจ ๐โ โฉ
   ฯ = [ ๐โ , ๐โ ]โจ ฯ โฉ
   f' : โ โ โ โ โจ ๐ โฉ
   f' n m = ฮต-exp-family (ฯ-exp-family ฯ n) m
   f : โ โ โ โ โจ ๐โ โฉ โ โจ ๐โ โฉ
   f n m = [ ๐โ , ๐โ ]โจ f' n m โฉ
   f'-mon : (nโ nโ mโ mโ : โ) โ nโ โค nโ โ mโ โค mโ โ f' nโ mโ โโจ ๐ โฉ f' nโ mโ
   f'-mon nโ nโ mโ mโ lโ lโ ฯ i = โฆ f nโ mโ ฯ โฆ i โโจ ๐ i โฉ[ uโ i ]
                                  โฆ f nโ mโ ฯ โฆ i โโจ ๐ i โฉ[ uโ i ]
                                  โฆ f nโ mโ ฯ โฆ i โโจ ๐ i โฉ
    where
     uโ = ฮต-exp-family-is-monotone' (ฯ-exp-family ฯ nโ) (ฯ-exp-family ฯ nโ)
           (ฯ-exp-family-is-monotone ฯ lโ) ฯ
     uโ = ฮต-exp-family-is-monotone (ฯ-exp-family ฯ nโ) lโ ฯ
   g' : โ โ โ โ โจ ๐ โฉ
   g' n m = DCPO-โโ ๐โ ๐โ ๐โ ๐โ (ฮตโฯโ-family m) ฯ (ฮตโฯโ-family n)
   g : โ โ โ โ โจ ๐โ โฉ โ โจ ๐โ โฉ
   g n m = [ ๐โ , ๐โ ]โจ g' n m โฉ
   g'-mon : (nโ nโ mโ mโ : โ) โ nโ โค nโ โ mโ โค mโ โ g' nโ mโ โโจ ๐ โฉ g' nโ mโ
   g'-mon nโ nโ mโ mโ lโ lโ ฯ i = โฆ g nโ mโ ฯ โฆ i โโจ ๐ i โฉ[ uโ i ]
                                  โฆ g nโ mโ ฯ โฆ i โโจ ๐ i โฉ[ uโ i ]
                                  โฆ g nโ mโ ฯ โฆ i โโจ ๐ i โฉ
    where
     uโ = ฮตโฯโ-family-is-monotone lโ ((ฯ โ ฮตโ mโ โ ฯโ mโ) ฯ)
     uโ = monotone-if-continuous ๐โ ๐โ (ฮตโฯโ-family nโ)
           ((ฯ โ ฮตโ mโ โ ฯโ mโ) ฯ) ((ฯ โ ฮตโ mโ โ ฯโ mโ) ฯ)
           (monotone-if-continuous ๐โ ๐โ ฯ
            (ฮตโ mโ (ฯโ mโ ฯ)) (ฮตโ mโ (ฯโ mโ ฯ))
            (ฮตโฯโ-family-is-monotone lโ ฯ))
   q : (ฮป n โ f' n n) โก (ฮป n โ g' n n)
   q = dfunext fe ฮณ
    where
     ฮณ : (ฮป n โ f' n n) โผ (ฮป n โ g' n n)
     ฮณ n = to-continuous-function-โก ๐โ ๐โ ฮณ'
      where
       ฮณ' : f n n โผ g n n
       ฮณ' ฯ =
        f n n ฯ                                                        โกโจ refl โฉ
        (ฮตโ n โ [ ๐ n , ๐ n ]โจ ฯโ (succ n) (ฮตโ (succ n) ฯ) โฉ โ ฯโ n) ฯ โกโจ q'   โฉ
        (ฮตโ n โ [ ๐ n , ๐ n ]โจ ฯ โฉ โ ฯโ n) ฯ                           โกโจ refl โฉ
        (ฮตโ n โ ฯโ n โ ฯ โ ฮตโ n โ ฯโ n) ฯ                              โกโจ refl โฉ
        g n n ฯ โ
         where
          ฯ : DCPO[ ๐ n , ๐ n ]
          ฯ = DCPO-โโ (๐ n) ๐โ ๐โ (๐ n) (ฮตโ' n) ฯ (ฯโ' n)
          q' = ap (ฮป - โ (ฮตโ n โ [ ๐ n , ๐ n ]โจ - โฉ โ ฯโ n) ฯ)
                (ฮตโ-section-of-ฯโ ฯ)
   s : โจ ๐ โฉ
   s = โ ๐ ฮตโฯโ-family-is-directed
   ฮดโ = ฯ-exp-family-is-directed ฯ
   ฮดโ = image-is-directed' ๐โ ๐ ฮต-expโ' ฮดโ
   ฮดโ : (n : โ) โ is-Directed ๐ (ฮต-exp-family (ฯ-exp-family ฯ n))
   ฮดโ n = ฮต-exp-family-is-directed (ฯ-exp-family ฯ n)
   p : ฮต-expโ โ ฯ-exp-family ฯ โก (ฮป n โ โ ๐ (ฮดโ n))
   p = dfunext fe (ฮป n โ ฮต-expโ-alt (ฯ-exp-family ฯ n))
   ฮดโ : is-Directed ๐ (ฮป n โ โ ๐ (ฮดโ n))
   ฮดโ = (transport (is-Directed ๐) p ฮดโ)
   ฮดโ : is-Directed ๐ (ฮป n โ f' n n)
   ฮดโ = โฃ 0 โฃ , ฮดโ'
    where
     ฮดโ' : is-semidirected (underlying-order ๐) (ฮป n โ f' n n)
     ฮดโ' n m = โฃ n +' m , uโ  , uโ โฃ
      where
       uโ : f' n n โโจ ๐ โฉ f' (n +' m) (n +' m)
       uโ = f'-mon n (n +' m) n (n +' m) (โค-+ n m) (โค-+ n m)
       uโ : f' m m โโจ ๐ โฉ f' (n +' m) (n +' m)
       uโ = f'-mon m (n +' m) m (n +' m) (โค-+' n m) (โค-+' n m)
   ฮดโ : is-Directed ๐ (ฮป n โ g' n n)
   ฮดโ = transport (is-Directed ๐) q ฮดโ
   eโ = ap ฮต-expโ (ฯ-expโ-alt ฯ)
   eโ = continuous-โ-โก ๐โ ๐ ฮต-expโ' ฮดโ
   eโ = โ-family-โก ๐ p ฮดโ
   eโ = โ-family-โก ๐ q ฮดโ
   eโ = antisymmetry ๐ (โ ๐ ฮดโ) (โ ๐ ฮดโ) lโ lโ
    where
     lโ : โ ๐ ฮดโ โโจ ๐ โฉ โ ๐ ฮดโ
     lโ = โ-is-lowerbound-of-upperbounds ๐ ฮดโ (โ ๐ ฮดโ) ฮณ
      where
       ฮณ : is-upperbound (underlying-order ๐) (โ ๐ ฮดโ) (ฮป n โ โ ๐ (ฮดโ n))
       ฮณ n = โ-is-lowerbound-of-upperbounds ๐ (ฮดโ n) (โ ๐ ฮดโ) ฮณ'
        where
         ฮณ' : is-upperbound (underlying-order ๐) (โ ๐ ฮดโ) (ฮป m โ f' n m)
         ฮณ' m = transitivity ๐ (f' n m) (f' (n +' m) (n +' m)) (โ ๐ ฮดโ)
                 (f'-mon n (n +' m) m (n +' m) (โค-+ n m) (โค-+' n m))
                 (โ-is-upperbound ๐ ฮดโ (n +' m))
     lโ : โ ๐ ฮดโ โโจ ๐ โฉ โ ๐ ฮดโ
     lโ = โ-is-lowerbound-of-upperbounds ๐ ฮดโ (โ ๐ ฮดโ) ฮณ
      where
       ฮณ : is-upperbound (underlying-order ๐) (โ ๐ ฮดโ) (ฮป n โ f' n n)
       ฮณ n = transitivity ๐ (f' n n) (โ ๐ (ฮดโ n)) (โ ๐ ฮดโ)
              (โ-is-upperbound ๐ (ฮดโ n) n)
              (โ-is-upperbound ๐ ฮดโ n)
   eโ = DCPO-โโ ๐โ ๐โ ๐โ ๐โ s ฯ s โกโจ pโ โฉ
        DCPO-โโ ๐โ ๐โ ๐โ ๐โ ฮน ฯ ฮน โกโจ pโ โฉ
        ฯ                         โ
    where
     ฮน : DCPO[ ๐โ , ๐โ ]
     ฮน = id , id-is-continuous ๐โ
     pโ = apโ (ฮป -โ -โ โ DCPO-โโ ๐โ ๐โ ๐โ ๐โ -โ ฯ -โ) e e
      where
       e : s โก ฮน
       e = โ-of-ฮตโฯโs-is-id
     pโ = to-continuous-function-โก ๐โ ๐โ (ฮป ฯ โ ๐ป๐ฎ๐ป๐ต (ฯ ฯ))
   eโ = antisymmetry ๐ (โ ๐ ฮดโ) (DCPO-โโ ๐โ ๐โ ๐โ ๐โ s ฯ s) lโ lโ
    where
     sโ : โจ ๐โ โฉ โ โจ ๐โ โฉ
     sโ = [ ๐โ , ๐โ ]โจ s โฉ
     lโ : โ ๐ ฮดโ โโจ ๐ โฉ DCPO-โโ ๐โ ๐โ ๐โ ๐โ s ฯ s
     lโ = โ-is-lowerbound-of-upperbounds ๐ ฮดโ (DCPO-โโ ๐โ ๐โ ๐โ ๐โ s ฯ s) ฮณ
      where
       ฮณ : is-upperbound (underlying-order ๐) (DCPO-โโ ๐โ ๐โ ๐โ ๐โ s ฯ s)
            (ฮป n โ g' n n)
       ฮณ n ฯ i = โฆ g n n ฯ                           โฆ i โโจ ๐ i โฉ[ uโ i ]
                 โฆ (ฮตโ n โ ฯโ n โ ฯ โ ฮตโ n โ ฯโ n) ฯ โฆ i โโจ ๐ i โฉ[ uโ i ]
                 โฆ (sโ โ ฯ) (ฮตโ n (ฯโ n ฯ))          โฆ i โโจ ๐ i โฉ[ uโ i ]
                 โฆ (sโ โ ฯ โ sโ) ฯ                   โฆ i โโจ ๐ i โฉ
        where
         ฮด : is-Directed ๐โ (pointwise-family ๐โ ๐โ ฮตโฯโ-family
              ((ฯ โ ฮตโ n โ ฯโ n) ฯ))
         ฮด = pointwise-family-is-directed ๐โ ๐โ ฮตโฯโ-family
              ฮตโฯโ-family-is-directed ((ฯ โ ฮตโ n โ ฯโ n) ฯ)
         ฮด' : is-Directed ๐โ (pointwise-family ๐โ ๐โ ฮตโฯโ-family ฯ)
         ฮด' = pointwise-family-is-directed ๐โ ๐โ ฮตโฯโ-family
               ฮตโฯโ-family-is-directed ฯ
         uโ = reflexivity ๐โ (g n n ฯ)
         uโ = โ-is-upperbound ๐โ ฮด n
         uโ = monotone-if-continuous ๐โ ๐โ (DCPO-โ ๐โ ๐โ ๐โ ฯ s)
               (ฮตโ n (ฯโ n ฯ)) (sโ ฯ) (โ-is-upperbound ๐โ ฮด' n)
     lโ : DCPO-โโ ๐โ ๐โ ๐โ ๐โ s ฯ s โโจ ๐ โฉ โ ๐ ฮดโ
     lโ ฯ = โ-is-lowerbound-of-upperbounds ๐โ ฮด ([ ๐โ , ๐โ ]โจ โ ๐ ฮดโ โฉ ฯ) ฮณ
      where
       ฮด : is-Directed ๐โ (pointwise-family ๐โ ๐โ ฮตโฯโ-family (ฯ (sโ ฯ)))
       ฮด = pointwise-family-is-directed ๐โ ๐โ ฮตโฯโ-family
            ฮตโฯโ-family-is-directed (ฯ (sโ ฯ))
       ฮณ : is-upperbound (underlying-order ๐โ) ([ ๐โ , ๐โ ]โจ โ ๐ ฮดโ โฉ ฯ)
            (pointwise-family ๐โ ๐โ ฮตโฯโ-family (ฯ (sโ ฯ)))
       ฮณ n i =
        โฆ (ฮตโ n โ ฯโ n โ ฯ โ sโ) ฯ โฆ i โโจ ๐ i โฉ[ continuous-โ-โ ๐โ ๐โ h ฮดโ' i ]
        โฆ โ ๐โ ฮดโ'                 โฆ i โโจ ๐ i โฉ[ ฮณโ i ]
        โฆ [ ๐โ , ๐โ ]โจ โ ๐ ฮดโ โฉ ฯ  โฆ i โโจ ๐ i โฉ
         where
          h : DCPO[ ๐โ , ๐โ ]
          h = DCPO-โโ ๐โ ๐โ (๐ n) ๐โ ฯ (ฯโ' n) (ฮตโ' n)
          ฮดโ' : is-Directed ๐โ (pointwise-family ๐โ ๐โ ฮตโฯโ-family ฯ)
          ฮดโ' = pointwise-family-is-directed ๐โ ๐โ ฮตโฯโ-family
                ฮตโฯโ-family-is-directed ฯ
          ฮดโ' : is-Directed ๐โ
                 (ฮป m โ (ฮตโ n โ ฯโ n โ ฯ โ ฮตโ m โ ฯโ m) ฯ)
          ฮดโ' = image-is-directed' ๐โ ๐โ h ฮดโ'
          ฮณโ : โ ๐โ ฮดโ' โโจ ๐โ โฉ [ ๐โ , ๐โ ]โจ โ ๐ ฮดโ โฉ ฯ
          ฮณโ = โ-is-lowerbound-of-upperbounds ๐โ ฮดโ'
                ([ ๐โ , ๐โ ]โจ โ ๐ ฮดโ โฉ ฯ) ฮณโ
           where
            ฮณโ : is-upperbound (underlying-order ๐โ) ([ ๐โ , ๐โ ]โจ โ ๐ ฮดโ โฉ ฯ)
                  (ฮป m โ (ฮตโ n โ ฯโ n โ ฯ โ ฮตโ m โ ฯโ m) ฯ)
            ฮณโ m i = โฆ (ฮตโ n โ ฯโ n โ ฯ โ ฮตโ m โ ฯโ m) ฯ โฆ i โโจ ๐ i โฉ[ uโ i ]
                     โฆ g n m ฯ                           โฆ i โโจ ๐ i โฉ[ uโ i ]
                     โฆ g (n +' m) m ฯ                    โฆ i โโจ ๐ i โฉ[ uโ i ]
                     โฆ g (n +' m) (n +' m) ฯ             โฆ i โโจ ๐ i โฉ[ uโ i ]
                     โฆ [ ๐โ , ๐โ ]โจ โ ๐ ฮดโ โฉ ฯ           โฆ i โโจ ๐ i โฉ
             where
              ฮดโ' : is-Directed ๐โ (pointwise-family ๐โ ๐โ (ฮป k โ g' k k) ฯ)
              ฮดโ' = pointwise-family-is-directed ๐โ ๐โ (ฮป k โ g' k k) ฮดโ ฯ
              uโ = reflexivity ๐โ (g n m ฯ)
              uโ = g'-mon n (n +' m) m m (โค-+ n m) (โค-refl m) ฯ
              uโ = g'-mon (n +' m) (n +' m) m (n +' m)
                    (โค-refl (n +' m)) (โค-+' n m) ฯ
              uโ = โ-is-upperbound ๐โ ฮดโ' (n +' m)

\end{code}

Hence, Dโ is isomorphic (as a dcpo) to its self-exponential (๐โ โนแตแถแตแต ๐โ).

\begin{code}

๐โ-isomorphic-to-its-self-exponential : ๐โ โแตแถแตแต (๐โ โนแตแถแตแต ๐โ)
๐โ-isomorphic-to-its-self-exponential =
 ฮต-expโ , ฯ-expโ , ฮต-expโ-section-of-ฯ-expโ , ฯ-expโ-section-of-ฮต-expโ ,
 ฮต-expโ-is-continuous , ฯ-expโ-is-continuous

\end{code}

But actually we want Dโ to be a pointed dcpo and we want it to be isomorphic to
the pointed exponential (๐โโฅ โนแตแถแตแตโฅ ๐โโฅ), which we prove now.

\begin{code}

ฯ-is-strict : (n : โ) โ is-strict (๐โฅ (succ n)) (๐โฅ n) (ฯ n)
ฯ-is-strict zero = refl
ฯ-is-strict (succ n) = to-continuous-function-โก (๐ n) (๐ n) ฮณ
 where
  f' : โจ ๐ (succ (succ n)) โฉ
  f' = โฅ (๐โฅ (succ (succ n)))
  f : โจ ๐ (succ n) โฉ โ โจ ๐ (succ n) โฉ
  f = [ ๐ (succ n) , ๐ (succ n) ]โจ f' โฉ
  ฮณ : [ ๐ n , ๐ n ]โจ ฯ (succ n) f' โฉ โผ [ ๐ n , ๐ n ]โจ โฅ (๐โฅ (succ n)) โฉ
  ฮณ x = [ ๐ n , ๐ n ]โจ ฯ (succ n) f' โฉ x   โกโจ refl โฉ
        (ฯ n โ f โ ฮต n) x                  โกโจ refl โฉ
        ฯ n (โฅ (๐โฅ (succ n)))              โกโจ IH โฉ
        [ ๐ n , ๐ n ]โจ โฅ (๐โฅ (succ n)) โฉ x โ
   where
    IH : ฯ n (โฅ (๐โฅ (succ n))) โก โฅ (๐โฅ n)
    IH = ฯ-is-strict n

ฯโบ-is-strict-helper : (n m k : โ) (p : n +' k โก m)
                    โ is-strict (๐โฅ m) (๐โฅ n) (ฯโบ-helper n m k p)
ฯโบ-is-strict-helper n n zero refl = refl
ฯโบ-is-strict-helper n m (succ k) refl =
 ฯโบ-helper n m (succ k) refl (โฅ (๐โฅ m))              โกโจ refl โฉ
 ฯโบ-helper n (n +' k) k refl (ฯ (n +' k) (โฅ (๐โฅ m))) โกโจ q    โฉ
 ฯโบ-helper n (n +' k) k refl (โฅ (๐โฅ (n +' k)))       โกโจ IH   โฉ
 โฅ (๐โฅ n)                                            โ
  where
   q = ap (ฯโบ-helper n (n +' k) k refl) (ฯ-is-strict (n +' k))
   IH = ฯโบ-is-strict-helper n (n +' k) k refl

ฯโบ-is-strict : (n m : โ) (l : n โค m) โ is-strict (๐โฅ m) (๐โฅ n) (ฯโบ l)
ฯโบ-is-strict n m l = ฯโบ-is-strict-helper n m k p
 where
  k : โ
  k = prโ (subtraction' n m l)
  p : n +' k โก m
  p = prโ (subtraction' n m l)

๐โ-has-least : has-least (underlying-order ๐โ)
๐โ-has-least = (ฯโฅ , p) , q
 where
  ฯโฅ : (n : โ) โ โจ ๐ n โฉ
  ฯโฅ n = โฅ (๐โฅ n)
  p : (n m : โ) (l : n โค m) โ ฯโบ l (ฯโฅ m) โก ฯโฅ n
  p = ฯโบ-is-strict
  q : is-least (underlying-order ๐โ) (ฯโฅ , p)
  q ฯ n = โฅ-is-least (๐โฅ n) (โฆ ฯ โฆ n)

๐โโฅ : DCPOโฅ {๐คโ} {๐คโ}
๐โโฅ = ๐โ , ๐โ-has-least

๐โโฅ-strict-isomorphic-to-its-self-exponential : ๐โโฅ โแตแถแตแตโฅ (๐โโฅ โนแตแถแตแตโฅ ๐โโฅ)
๐โโฅ-strict-isomorphic-to-its-self-exponential =
 โแตแถแตแต-to-โแตแถแตแตโฅ ๐โโฅ (๐โโฅ โนแตแถแตแตโฅ ๐โโฅ) ๐โ-isomorphic-to-its-self-exponential

\end{code}

Finally, we show that ๐โ is nontrivial, i.e. it has an element ฯโ such that ฯโ
is not the least element.

\begin{code}

ฯโ : โจ ๐โ โฉ
ฯโ = ฯ , p
 where
  xโ : โจ ๐ 0 โฉ
  xโ = ๐ , id , ๐-is-prop
  ฯ : (n : โ) โ โจ ๐ n โฉ
  ฯ n = ฮตโบ {0} {n} โ xโ
  p : (n m : โ) (l : n โค m) โ ฯโบ l (ฯ m) โก ฯ n
  p n m l = ฯโบ {n} {m} l (ฮตโบ {0} {m} โ xโ)                  โกโจ eโ โฉ
            (ฯโบ {n} {m} l โ ฮตโบ {n} {m} l โ ฮตโบ {0} {n} โ) xโ โกโจ eโ โฉ
            ฮตโบ {0} {n} โ xโ                                 โ
   where
    eโ = ap (ฯโบ {n} {m} l) ((ฮตโบ-comp โ l xโ) โปยน)
    eโ = ฮตโบ-section-of-ฯโบ l (ฮตโบ {0} {n} โ xโ)

๐โโฅ-is-nontrivial : ฯโ โข โฅ ๐โโฅ
๐โโฅ-is-nontrivial e = ๐-is-not-๐ (ฮณ โปยน)
 where
  eโ : โฆ ฯโ โฆ 0 โก โฅ (๐โฅ 0)
  eโ = ap (ฮป - โ โฆ - โฆ 0) e
  ฮณ : ๐ โก ๐
  ฮณ = ap prโ eโ

\end{code}
