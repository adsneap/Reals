Tom de Jong, May 2019.
Major additions January 2020.

We construct the exponential (pointed) dcpos (๐ โนแตแถแตแต ๐) and (๐ โนแตแถแตแตโฅ ๐) for
(pointed) dcpos ๐ and ๐.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (J)
open import UF-FunExt
open import UF-PropTrunc

module DcpoExponential
        (pt : propositional-truncations-exist)
        (fe : โ {๐ค ๐ฅ} โ funext ๐ค ๐ฅ)
        (๐ฅ : Universe)
       where

open PropositionalTruncation pt

open import UF-Subsingletons
open import UF-Subsingletons-FunExt

open import Dcpo pt fe ๐ฅ
open import DcpoMiscelanea pt fe ๐ฅ

open import Poset fe

module _ (๐ : DCPO {๐ค} {๐ฃ})
         (๐ : DCPO {๐ค'} {๐ฃ'})
       where

 _hom-โ_ : DCPO[ ๐ , ๐ ] โ DCPO[ ๐ , ๐ ] โ ๐ค โ ๐ฃ' ฬ
 (f , _) hom-โ (g , _) = โ d โ f d โโจ ๐ โฉ g d

 pointwise-family : {I : ๐ฅ ฬ} (ฮฑ : I โ DCPO[ ๐ , ๐ ]) โ โจ ๐ โฉ โ I โ โจ ๐ โฉ
 pointwise-family ฮฑ d i = underlying-function ๐ ๐ (ฮฑ i) d

 pointwise-family-is-directed : {I : ๐ฅ ฬ} (ฮฑ : I โ DCPO[ ๐ , ๐ ])
                                (ฮด : is-directed _hom-โ_ ฮฑ)
                                (d : โจ ๐ โฉ)
                              โ is-directed (underlying-order ๐)
                                 (pointwise-family ฮฑ d)
 pointwise-family-is-directed {I} ฮฑ ฮด d = a , b
  where
   a : โฅ I โฅ
   a = inhabited-if-directed _hom-โ_ ฮฑ ฮด
   b : is-semidirected (underlying-order ๐) (pointwise-family ฮฑ d)
   b i j = do
    (k , l , m) โ semidirected-if-directed _hom-โ_ ฮฑ ฮด i j
    โฃ k , l d , m d โฃ

 continuous-functions-sup : {I : ๐ฅ ฬ} (ฮฑ : I โ DCPO[ ๐ , ๐ ])
                          โ is-directed _hom-โ_ ฮฑ โ DCPO[ ๐ , ๐ ]
 continuous-functions-sup {I} ฮฑ ฮด = f , c
  where
   ฮต : (d : โจ ๐ โฉ) โ is-directed (underlying-order ๐) (pointwise-family ฮฑ d)
   ฮต = pointwise-family-is-directed ฮฑ ฮด
   f : โจ ๐ โฉ โ โจ ๐ โฉ
   f d = โ ๐ (ฮต d)
   c : is-continuous ๐ ๐ f
   c J ฮฒ ฯ = ub , lb-of-ubs
    where
     ub : (j : J) โ f (ฮฒ j) โโจ ๐ โฉ f (โ ๐ ฯ)
     ub j = f (ฮฒ j)         โโจ ๐ โฉ[ reflexivity ๐ (f (ฮฒ j)) ]
            โ ๐ (ฮต (ฮฒ j))   โโจ ๐ โฉ[ โ-is-monotone ๐ (ฮต (ฮฒ j)) (ฮต (โ ๐ ฯ)) h ]
            โ ๐ (ฮต (โ ๐ ฯ)) โโจ ๐ โฉ[ reflexivity ๐ (f (โ ๐ ฯ)) ]
            f (โ ๐ ฯ)       โโจ ๐ โฉ
      where
       h : (i : I) โ [ ๐ , ๐ ]โจ ฮฑ i โฉ (ฮฒ j) โโจ ๐ โฉ [ ๐ , ๐ ]โจ ฮฑ i โฉ (โ ๐ ฯ)
       h i = monotone-if-continuous ๐ ๐ (ฮฑ i) (ฮฒ j) (โ ๐ ฯ)
              (โ-is-upperbound ๐ ฯ j)
     lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order ๐) (f (โ ๐ ฯ))
                  (f โ ฮฒ)
     lb-of-ubs e l = f (โ ๐ ฯ)       โโจ ๐ โฉ[ reflexivity ๐ (f (โ ๐ ฯ)) ]
                     โ ๐ (ฮต (โ ๐ ฯ)) โโจ ๐ โฉ[ u ]
                     e               โโจ ๐ โฉ
      where
       u = โ-is-lowerbound-of-upperbounds ๐ (ฮต (โ ๐ ฯ)) e v
        where
         v : (i : I) โ [ ๐ , ๐ ]โจ ฮฑ i โฉ (โ ๐ ฯ) โโจ ๐ โฉ e
         v i = [ ๐ , ๐ ]โจ ฮฑ i โฉ (โ ๐ ฯ)             โโจ ๐ โฉ[ lโ ]
               โ ๐ (image-is-directed' ๐ ๐ (ฮฑ i) ฯ) โโจ ๐ โฉ[ lโ ]
               e                                    โโจ ๐ โฉ
          where
           lโ = continuous-โ-โ ๐ ๐ (ฮฑ i) ฯ
           lโ = โ-is-lowerbound-of-upperbounds ๐
                 (image-is-directed' ๐ ๐ (ฮฑ i) ฯ) e w
            where
             w : (j : J) โ [ ๐ , ๐ ]โจ ฮฑ i โฉ (ฮฒ j) โโจ ๐ โฉ e
             w j = [ ๐ , ๐ ]โจ ฮฑ i โฉ (ฮฒ j) โโจ ๐ โฉ[ โ-is-upperbound ๐ (ฮต (ฮฒ j)) i ]
                   โ ๐ (ฮต (ฮฒ j))          โโจ ๐ โฉ[ reflexivity ๐ (f (ฮฒ j)) ]
                   f (ฮฒ j)                โโจ ๐ โฉ[ l j ]
                   e                      โโจ ๐ โฉ

infixr 20 _โนแตแถแตแต_

_โนแตแถแตแต_ : DCPO {๐ค} {๐ฃ} โ DCPO {๐ค'} {๐ฃ'}
        โ DCPO {(๐ฅ โบ) โ ๐ค โ ๐ฃ โ ๐ค' โ ๐ฃ'} {๐ค โ ๐ฃ'}
๐ โนแตแถแตแต ๐ = DCPO[ ๐ , ๐ ] , _โ_ , pa , dc
 where
  _โ_ = ๐ hom-โ ๐
  pa : PosetAxioms.poset-axioms _โ_
  pa = s , p , r , t , a
   where
    open PosetAxioms _โ_
    s : is-set DCPO[ ๐ , ๐ ]
    s = subsets-of-sets-are-sets (โจ ๐ โฉ โ โจ ๐ โฉ) (is-continuous ๐ ๐)
         (ฮ?-is-set fe (ฮป x โ sethood ๐))
         (ฮป {f} โ being-continuous-is-prop ๐ ๐ f)
    p : (f g : DCPO[ ๐ , ๐ ]) โ is-prop (f โ g)
    p (f , _) (g , _) = ฮ?-is-prop fe (ฮป x โ prop-valuedness ๐ (f x) (g x))
    r : (f : DCPO[ ๐ , ๐ ]) โ f โ f
    r (f , _) x = reflexivity ๐ (f x)
    t : (f g h : DCPO[ ๐ , ๐ ]) โ f โ g โ g โ h โ f โ h
    t (f , _) (g , _) (h , _) l m x = transitivity ๐ (f x) (g x) (h x)
                                      (l x) (m x)
    a : (f g : DCPO[ ๐ , ๐ ]) โ f โ g โ g โ f โ f โก g
    a f g l m = to-continuous-function-โก ๐ ๐
                 (ฮป x โ antisymmetry ๐ ([ ๐ , ๐ ]โจ f โฉ x) ([ ๐ , ๐ ]โจ g โฉ x)
                  (l x) (m x))
  dc : is-directed-complete _โ_
  dc I ฮฑ ฮด = (continuous-functions-sup ๐ ๐ ฮฑ ฮด) , u , v
   where
    u : (i : I) โ ฮฑ i โ continuous-functions-sup ๐ ๐ ฮฑ ฮด
    u i d = โ-is-upperbound ๐ (pointwise-family-is-directed ๐ ๐ ฮฑ ฮด d) i
    v : (g : DCPO[ ๐ , ๐ ])
      โ ((i : I) โ ฮฑ i โ g)
      โ continuous-functions-sup ๐ ๐ ฮฑ ฮด โ g
    v (g , _) l d = โ-is-lowerbound-of-upperbounds ๐
                     (pointwise-family-is-directed ๐ ๐ ฮฑ ฮด d)
                     (g d) (ฮป (i : I) โ l i d)

infixr 20 _โนแตแถแตแตโฅ_

_โนแตแถแตแตโฅ_ : DCPOโฅ {๐ค} {๐ฃ} โ DCPOโฅ {๐ค'} {๐ฃ'}
         โ DCPOโฅ {(๐ฅ โบ) โ ๐ค โ ๐ฃ โ ๐ค' โ ๐ฃ'} {๐ค โ ๐ฃ'}
๐ โนแตแถแตแตโฅ ๐ = (๐ โป) โนแตแถแตแต (๐ โป) , h
 where
  h : has-least (underlying-order ((๐ โป) โนแตแถแตแต (๐ โป)))
  h = ((ฮป _ โ โฅ ๐) ,
      constant-functions-are-continuous (๐ โป) (๐ โป) (โฅ ๐)) ,
      (ฮป g d โ โฅ-is-least ๐ (underlying-function (๐ โป) (๐ โป) g d))

\end{code}

Now that we have constructed exponentials, we can state and prove additional
continuity results regarding composition of continuous functions.

(These results are used in constructing Scott's Dโ in DcpoDinfinity.lagda.)

\begin{code}

DCPO-โ-is-monotoneโ : (๐ : DCPO {๐ค} {๐ฃ})
                      (๐ : DCPO {๐ค'} {๐ฃ'})
                      (๐' : DCPO {๐ฆ} {๐ฆ'})
                      (f : DCPO[ ๐ , ๐ ])
                    โ is-monotone (๐ โนแตแถแตแต ๐') (๐ โนแตแถแตแต ๐') (DCPO-โ ๐ ๐ ๐' f)
DCPO-โ-is-monotoneโ ๐ ๐ ๐' (f , cf) g h l x = l (f x)

DCPO-โ-is-monotoneโ : (๐ : DCPO {๐ค} {๐ฃ})
                      (๐ : DCPO {๐ค'} {๐ฃ'})
                      (๐' : DCPO {๐ฆ} {๐ฆ'})
                      (g : DCPO[ ๐ , ๐' ])
                    โ is-monotone (๐ โนแตแถแตแต ๐) (๐ โนแตแถแตแต ๐')
                       (ฮป f โ DCPO-โ ๐ ๐ ๐' f g)
DCPO-โ-is-monotoneโ ๐ ๐ ๐' g (f , cf) (h , ch) l x =
 monotone-if-continuous ๐ ๐' g (f x) (h x) (l x)

DCPO-โ-is-continuousโ : (๐ : DCPO {๐ค} {๐ฃ})
                        (๐ : DCPO {๐ค'} {๐ฃ'})
                        (๐' : DCPO {๐ฆ} {๐ฆ'})
                        (f : DCPO[ ๐ , ๐ ])
                      โ is-continuous (๐ โนแตแถแตแต ๐') (๐ โนแตแถแตแต ๐') (DCPO-โ ๐ ๐ ๐' f)
DCPO-โ-is-continuousโ ๐ ๐ ๐' f I ฮฑ ฮด =
 transport (ฮป - โ is-sup (underlying-order (๐ โนแตแถแตแต ๐')) - (DCPO-โ ๐ ๐ ๐' f โ ฮฑ))
  (ฮณ โปยน) (โ-is-sup (๐ โนแตแถแตแต ๐') {I} {ฮฒ} ฮต)
  where
     ฮฒ : I โ โจ ๐ โนแตแถแตแต ๐' โฉ
     ฮฒ i = DCPO-โ ๐ ๐ ๐' f (ฮฑ i)
     ฮต : is-Directed (๐ โนแตแถแตแต ๐') ฮฒ
     ฮต = image-is-directed (๐ โนแตแถแตแต ๐') (๐ โนแตแถแตแต ๐') {DCPO-โ ๐ ๐ ๐' f}
          (DCPO-โ-is-monotoneโ ๐ ๐ ๐' f) {I} {ฮฑ} ฮด
     ฮณ : DCPO-โ ๐ ๐ ๐' f (โ (๐ โนแตแถแตแต ๐') {I} {ฮฑ} ฮด) โก โ (๐ โนแตแถแตแต ๐') {I} {ฮฒ} ฮต
     ฮณ = to-continuous-function-โก ๐ ๐' ฯ
      where
       ฯ : (x : โจ ๐ โฉ)
         โ [ ๐ , ๐' ]โจ (โ (๐ โนแตแถแตแต ๐') {I} {ฮฑ} ฮด) โฉ ([ ๐ , ๐ ]โจ f โฉ x)
         โก โ ๐' (pointwise-family-is-directed ๐ ๐' ฮฒ ฮต x)
       ฯ x = [ ๐ , ๐' ]โจ (โ (๐ โนแตแถแตแต ๐') {I} {ฮฑ} ฮด) โฉ ([ ๐ , ๐ ]โจ f โฉ x) โกโจ eโ โฉ
             โ ๐' ฮต'                                                     โกโจ eโ โฉ
             โ ๐' (pointwise-family-is-directed ๐ ๐' ฮฒ ฮต x) โ
        where
         ฮต' : is-Directed ๐' (pointwise-family ๐ ๐' ฮฑ ([ ๐ , ๐ ]โจ f โฉ x))
         ฮต' = pointwise-family-is-directed ๐ ๐' ฮฑ ฮด ([ ๐ , ๐ ]โจ f โฉ x)
         eโ = refl
         eโ = โ-independent-of-directedness-witness ๐' ฮต'
               (pointwise-family-is-directed ๐ ๐' ฮฒ ฮต x)

DCPO-โ-is-continuousโ : (๐ : DCPO {๐ค} {๐ฃ})
                        (๐ : DCPO {๐ค'} {๐ฃ'})
                        (๐' : DCPO {๐ฆ} {๐ฆ'})
                        (g : DCPO[ ๐ , ๐' ])
                      โ is-continuous (๐ โนแตแถแตแต ๐) (๐ โนแตแถแตแต ๐')
                         (ฮป f โ DCPO-โ ๐ ๐ ๐' f g)
DCPO-โ-is-continuousโ ๐ ๐ ๐' g I ฮฑ ฮด =
 transport
  (ฮป - โ is-sup (underlying-order (๐ โนแตแถแตแต ๐')) - ((ฮป f โ DCPO-โ ๐ ๐ ๐' f g) โ ฮฑ))
  (ฮณ โปยน) (โ-is-sup (๐ โนแตแถแตแต ๐') {I} {ฮฒ} ฮต)
   where
    ฮฒ : I โ โจ ๐ โนแตแถแตแต ๐' โฉ
    ฮฒ i = DCPO-โ ๐ ๐ ๐' (ฮฑ i) g
    ฮต : is-Directed (๐ โนแตแถแตแต ๐') ฮฒ
    ฮต = image-is-directed (๐ โนแตแถแตแต ๐) (๐ โนแตแถแตแต ๐') {ฮป f โ DCPO-โ ๐ ๐ ๐' f g}
         (DCPO-โ-is-monotoneโ ๐ ๐ ๐' g) {I} {ฮฑ} ฮด
    ฮณ : DCPO-โ ๐ ๐ ๐' (โ (๐ โนแตแถแตแต ๐) {I} {ฮฑ} ฮด) g โก โ (๐ โนแตแถแตแต ๐') {I} {ฮฒ} ฮต
    ฮณ = to-continuous-function-โก ๐ ๐' ฯ
     where
      ฯ : (x : โจ ๐ โฉ)
        โ [ ๐ , ๐' ]โจ g โฉ ([ ๐ , ๐ ]โจ โ (๐ โนแตแถแตแต ๐) {I} {ฮฑ} ฮด โฉ x)
        โก โ ๐' (pointwise-family-is-directed ๐ ๐' ฮฒ ฮต x)
      ฯ x = [ ๐ , ๐' ]โจ g โฉ ([ ๐ , ๐ ]โจ โ (๐ โนแตแถแตแต ๐) {I} {ฮฑ} ฮด โฉ x) โกโจ refl โฉ
            [ ๐ , ๐' ]โจ g โฉ (โ ๐ ฮต')                                 โกโจ eโ โฉ
            โ ๐' ฮต''                                                 โกโจ eโ โฉ
            โ ๐' (pointwise-family-is-directed ๐ ๐' ฮฒ ฮต x)           โ
       where
        ฮต' : is-Directed ๐ (pointwise-family ๐ ๐ ฮฑ x)
        ฮต' = pointwise-family-is-directed ๐ ๐ ฮฑ ฮด x
        ฮต'' : is-Directed ๐' ([ ๐ , ๐' ]โจ g โฉ โ pointwise-family ๐ ๐ ฮฑ x)
        ฮต'' = image-is-directed' ๐ ๐' g ฮต'
        eโ = continuous-โ-โก ๐ ๐' g ฮต'
        eโ = โ-independent-of-directedness-witness ๐' ฮต''
              (pointwise-family-is-directed ๐ ๐' ฮฒ ฮต x)

DCPO-โโ-is-continuousโ : {๐ฆโ ๐ฃโ ๐ฆโ ๐ฃโ ๐ฆโ ๐ฃโ ๐ฆโ ๐ฃโ : Universe}
                         (๐โ : DCPO {๐ฆโ} {๐ฃโ}) (๐โ : DCPO {๐ฆโ} {๐ฃโ})
                         (๐โ : DCPO {๐ฆโ} {๐ฃโ}) (๐โ : DCPO {๐ฆโ} {๐ฃโ})
                         (f : DCPO[ ๐โ , ๐โ ]) (h : DCPO[ ๐โ , ๐โ ])
                       โ is-continuous (๐โ โนแตแถแตแต ๐โ) (๐โ โนแตแถแตแต ๐โ)
                          (ฮป g โ DCPO-โโ ๐โ ๐โ ๐โ ๐โ f g h)
DCPO-โโ-is-continuousโ ๐โ ๐โ ๐โ ๐โ f h =
 โ-is-continuous (๐โ โนแตแถแตแต ๐โ) (๐โ โนแตแถแตแต ๐โ) (๐โ โนแตแถแตแต ๐โ)
  (ฮป g โ DCPO-โ ๐โ ๐โ ๐โ g h) (DCPO-โ ๐โ ๐โ ๐โ f)
  (DCPO-โ-is-continuousโ ๐โ ๐โ ๐โ h) (DCPO-โ-is-continuousโ ๐โ ๐โ ๐โ f)

\end{code}
