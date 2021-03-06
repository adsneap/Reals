Tom de Jong, May 2019.
Refactored Dec 2021.

Least fixed points of Scott continuous maps.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-PropTrunc

module DcpoLeastFixedPoint
        (pt : propositional-truncations-exist)
        (fe : โ {๐ค ๐ฅ} โ funext ๐ค ๐ฅ)
       where

open PropositionalTruncation pt

open import UF-Miscelanea
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

open import NaturalsAddition renaming (_+_ to _+'_)
open import NaturalsOrder
open import NaturalNumbers-Properties
open import OrderNotation

module _ {๐ฅ : Universe} where

 open import Dcpo pt fe ๐ฅ
 open import DcpoMiscelanea pt fe ๐ฅ
 open import DcpoExponential pt fe ๐ฅ

 module _ (๐ : DCPOโฅ {๐ค} {๐ฃ}) where

  iter : (n : โ) โ โช ๐ โนแตแถแตแตโฅ ๐ โซ โ โช ๐ โซ
  iter zero     f = โฅ ๐
  iter (succ n) f = [ ๐ โป , ๐ โป ]โจ f โฉ (iter n f)

  iter-is-monotone : (n : โ) โ is-monotone ((๐ โนแตแถแตแตโฅ ๐) โป) (๐ โป) (iter n)
  iter-is-monotone zero     f g l = โฅ-is-least ๐ (iter zero g)
  iter-is-monotone (succ n) f g l = iter (succ n) f               โโช ๐ โซ[ โฆ1โฆ ]
                                    [ ๐ โป , ๐ โป ]โจ g โฉ (iter n f) โโช ๐ โซ[ โฆ2โฆ ]
                                    iter (succ n) g               โโช ๐ โซ
   where
    โฆ1โฆ = l (iter n f)
    โฆ2โฆ = monotone-if-continuous (๐ โป) (๐ โป) g (iter n f) (iter n g)
          (iter-is-monotone n f g l)

  n-family : {I : ๐ฅ ฬ } (ฮฑ : I โ โช ๐ โนแตแถแตแตโฅ ๐ โซ) (n : โ) โ I โ โช ๐ โซ
  n-family ฮฑ n i = iter n (ฮฑ i)

  n-family-is-directed : {I : ๐ฅ ฬ } (ฮฑ : I โ โช ๐ โนแตแถแตแตโฅ ๐ โซ)
                         (ฮด : is-Directed ((๐ โนแตแถแตแตโฅ ๐) โป) ฮฑ)
                         (n : โ) โ is-Directed (๐ โป) (n-family ฮฑ n)
  n-family-is-directed {I} ฮฑ ฮด n =
    inhabited-if-Directed ((๐ โนแตแถแตแตโฅ ๐ ) โป) ฮฑ ฮด , ฮต
   where
    ฮต : is-Semidirected (๐ โป) (n-family ฮฑ n)
    ฮต i j = โฅโฅ-functor h (semidirected-if-Directed ((๐ โนแตแถแตแตโฅ ๐) โป) ฮฑ ฮด i j)
     where
      h : (ฮฃ k ๊ I , (ฮฑ i) โโช ๐ โนแตแถแตแตโฅ ๐ โซ (ฮฑ k) ร
                     (ฮฑ j) โโช ๐ โนแตแถแตแตโฅ ๐ โซ (ฮฑ k))
        โ ฮฃ k ๊ I , (n-family ฮฑ n i) โโช ๐ โซ (n-family ฮฑ n k) ร
                    (n-family ฮฑ n j) โโช ๐ โซ (n-family ฮฑ n k)
      h (k , l , m) = k , (iter-is-monotone n (ฮฑ i) (ฮฑ k) l) ,
                          (iter-is-monotone n (ฮฑ j) (ฮฑ k) m)

  double-โ-lemma : {I : ๐ฅ ฬ } (ฮฑ : I โ โช ๐ โนแตแถแตแตโฅ ๐ โซ)
                   (ฮด : is-Directed ((๐ โนแตแถแตแตโฅ ๐) โป) ฮฑ)
                   (n : โ)
                 โ โ (๐ โป) (pointwise-family-is-directed (๐ โป) (๐ โป) ฮฑ ฮด
                           (โ (๐ โป) (n-family-is-directed ฮฑ ฮด n)))
                   โก โ (๐ โป) (n-family-is-directed ฮฑ ฮด (succ n))
  double-โ-lemma {I} ฮฑ ฮด n = antisymmetry (๐ โป) x y a b
   where
    ฮต : is-Directed (๐ โป) (pointwise-family (๐ โป) (๐ โป) ฮฑ
         (โ (๐ โป) (n-family-is-directed ฮฑ ฮด n)))
    ฮต = (pointwise-family-is-directed (๐ โป) (๐ โป) ฮฑ ฮด
         (โ (๐ โป) (n-family-is-directed ฮฑ ฮด n)))
    ฯ : (n : โ) โ is-Directed (๐ โป) (n-family ฮฑ n)
    ฯ n = n-family-is-directed ฮฑ ฮด n

    x : โช ๐ โซ
    x = โ (๐ โป) ฮต
    y : โช ๐ โซ
    y = โ (๐ โป) (n-family-is-directed ฮฑ ฮด (succ n))

    a : x โโช ๐ โซ y
    a = โ-is-lowerbound-of-upperbounds (๐ โป) ฮต y g
     where
      g : (i : I)
        โ (pointwise-family (๐ โป) (๐ โป) ฮฑ (โ (๐ โป) (ฯ n)) i) โโช ๐ โซ y
      g i = sup-is-lowerbound-of-upperbounds
             (underlying-order (๐ โป)) s y u
       where
        ฮฒ : I โ โช ๐ โซ
        ฮฒ = [ ๐ โป , ๐ โป ]โจ ฮฑ i โฉ โ (n-family ฮฑ n)
        s : is-sup (underlying-order (๐ โป))
             (pointwise-family (๐ โป) (๐ โป) ฮฑ (โ (๐ โป) (ฯ n)) i) ฮฒ
        s = continuity-of-function (๐ โป) (๐ โป) (ฮฑ i) I (n-family ฮฑ n) (ฯ n)
        u : (j : I) โ ฮฒ j โโจ ๐ โป โฉ y
        u j = โฅโฅ-rec (prop-valuedness (๐ โป) (ฮฒ j) y) v
               (semidirected-if-Directed ((๐ โนแตแถแตแตโฅ ๐) โป) ฮฑ ฮด i j)
                where
          v : (ฮฃ  k ๊ I , ฮฑ i โโช ๐ โนแตแถแตแตโฅ ๐ โซ ฮฑ k ร ฮฑ j โโช ๐ โนแตแถแตแตโฅ ๐ โซ ฮฑ k)
            โ ฮฒ j โโช ๐ โซ y
          v (k , l , m) = ฮฒ j                                 โโช ๐ โซ[ โฆ1โฆ ]
                          [ ๐ โป , ๐ โป ]โจ ฮฑ k โฉ (iter n (ฮฑ j)) โโช ๐ โซ[ โฆ2โฆ ]
                          iter (succ n) (ฮฑ k)                 โโช ๐ โซ[ โฆ3โฆ ]
                          y                                   โโช ๐ โซ
           where
            โฆ1โฆ = l (iter n (ฮฑ j))
            โฆ2โฆ = monotone-if-continuous (๐ โป) (๐ โป) (ฮฑ k)
                   (iter n (ฮฑ j))
                   (iter n (ฮฑ k))
                   (iter-is-monotone n (ฮฑ j) (ฮฑ k) m)
            โฆ3โฆ = โ-is-upperbound (๐ โป) (ฯ (succ n)) k

    b : y โโช ๐ โซ x
    b = โ-is-lowerbound-of-upperbounds (๐ โป) (ฯ (succ n)) x h
     where
      h : (i : I) โ (n-family ฮฑ (succ n) i) โโช ๐ โซ x
      h i = n-family ฮฑ (succ n) i                โโช ๐ โซ[ โฆ1โฆ ]
            [ ๐ โป , ๐ โป ]โจ ฮฑ i โฉ (โ (๐ โป) (ฯ n)) โโช ๐ โซ[ โฆ2โฆ ]
            x                                    โโช ๐ โซ
       where
        โฆ1โฆ = monotone-if-continuous (๐ โป) (๐ โป) (ฮฑ i)
               (iter n (ฮฑ i))
               (โ (๐ โป) (n-family-is-directed ฮฑ ฮด n))
               (โ-is-upperbound (๐ โป) (ฯ n) i)
        โฆ2โฆ = โ-is-upperbound (๐ โป) ฮต i

  iter-is-continuous : (n : โ) โ is-continuous ((๐ โนแตแถแตแตโฅ ๐) โป) (๐ โป) (iter n)
  iter-is-continuous zero     I ฮฑ ฮด = a , b
   where
    a : (i : I) โ iter zero (ฮฑ i) โโช ๐ โซ
                  iter zero (โ ((๐ โนแตแถแตแตโฅ ๐) โป) {I} {ฮฑ} ฮด)
    a i = โฅ-is-least ๐ (iter zero (โ ((๐ โนแตแถแตแตโฅ ๐) โป) {I} {ฮฑ} ฮด))
    b : (u : โช ๐ โซ)
      โ ((i : I) โ iter zero (ฮฑ i) โโช ๐ โซ u)
      โ iter zero (โ ((๐ โนแตแถแตแตโฅ ๐) โป) {I} {ฮฑ} ฮด) โโช ๐ โซ u
    b u l = โฅ-is-least ๐ u
  iter-is-continuous (succ n) I ฮฑ ฮด = ฮณ
   where
    ฮณ : is-sup (underlying-order (๐ โป))
        (iter (succ n) (โ ((๐ โนแตแถแตแตโฅ ๐) โป) ฮด)) (iter (succ n) โ ฮฑ)
    ฮณ = transport
        (ฮป - โ is-sup (underlying-order (๐ โป)) - (iter (succ n) โ ฮฑ)) (h โปยน) k
     where
      k : is-sup (underlying-order (๐ โป))
          (โ (๐ โป) (n-family-is-directed ฮฑ ฮด (succ n)))
          (iter (succ n) โ ฮฑ)
      k = โ-is-sup (๐ โป) (n-family-is-directed ฮฑ ฮด (succ n))
      h = iter (succ n) s                                           โกโจ refl โฉ
          [ ๐ โป , ๐ โป ]โจ s โฉ (iter n s)                             โกโจ โฆ1โฆ  โฉ
          [ ๐ โป , ๐ โป ]โจ s โฉ (โ (๐ โป) (n-family-is-directed ฮฑ ฮด n)) โกโจ refl โฉ
          โ (๐ โป) (pointwise-family-is-directed (๐ โป) (๐ โป) ฮฑ ฮด
            (โ (๐ โป) (n-family-is-directed ฮฑ ฮด n)))                 โกโจ โฆ2โฆ  โฉ
          โ (๐ โป) (n-family-is-directed ฮฑ ฮด (succ n))               โ
       where
        s = (โ ((๐ โนแตแถแตแตโฅ ๐) โป) {I} {ฮฑ} ฮด)
        โฆ2โฆ = double-โ-lemma ฮฑ ฮด n
        โฆ1โฆ = ap ([ ๐ โป , ๐ โป ]โจ s โฉ) e
         where
          e : iter n s โก โ (๐ โป) (n-family-is-directed ฮฑ ฮด n)
          e = antisymmetry (๐ โป) (iter n s) (โ (๐ โป)
               (n-family-is-directed ฮฑ ฮด n)) l m
           where
            IH : is-sup (underlying-order (๐ โป)) (iter n (โ ((๐ โนแตแถแตแตโฅ ๐) โป) ฮด))
                 (iter n โ ฮฑ)
            IH = iter-is-continuous n I ฮฑ ฮด
            l : iter n s โโช ๐ โซ โ (๐ โป) (n-family-is-directed ฮฑ ฮด n)
            l = sup-is-lowerbound-of-upperbounds
                 (underlying-order (๐ โป)) IH
                 (โ (๐ โป) (n-family-is-directed ฮฑ ฮด n))
                 (โ-is-upperbound (๐ โป) (n-family-is-directed ฮฑ ฮด n))
            m : โ (๐ โป) (n-family-is-directed ฮฑ ฮด n) โโช ๐ โซ iter n s
            m = โ-is-lowerbound-of-upperbounds (๐ โป) (n-family-is-directed ฮฑ ฮด n)
                 (iter n s)
                 (sup-is-upperbound (underlying-order (๐ โป)) IH)

  iter-c : โ โ DCPO[ (๐ โนแตแถแตแตโฅ ๐) โป , ๐ โป ]
  iter-c n = iter n , iter-is-continuous n

  iter-is-ฯ-chain : (n : โ) โ (iter-c n) โโจ ((๐ โนแตแถแตแตโฅ ๐) โป) โนแตแถแตแต (๐ โป) โฉ
                              (iter-c (succ n))
  iter-is-ฯ-chain zero     f = โฅ-is-least ๐ (iter (succ zero) f)
  iter-is-ฯ-chain (succ n) f = monotone-if-continuous (๐ โป) (๐ โป) f
                                (iter n f)
                                (iter (succ n) f)
                                (iter-is-ฯ-chain n f)

  iter-increases : (n m : โ) โ (n โค m)
                 โ (iter-c n) โโจ ((๐ โนแตแถแตแตโฅ ๐) โป) โนแตแถแตแต (๐ โป) โฉ (iter-c m)
  iter-increases n zero l     f = transport
                                   (ฮป - โ iter - f โโช ๐ โซ iter zero f)
                                   (unique-minimal n l โปยน)
                                   (reflexivity (๐ โป) (iter zero f))
  iter-increases n (succ m) l f = h (โค-split n m l)
   where
    h : (n โค m) + (n โก succ m) โ (iter n f) โโช ๐ โซ iter (succ m) f
    h (inl l') = iter n f        โโช ๐ โซ[ iter-increases n m l' f ]
                 iter m f        โโช ๐ โซ[ iter-is-ฯ-chain m f     ]
                 iter (succ m) f โโช ๐ โซ
    h (inr e)  = transport (ฮป - โ iter - f โโช ๐ โซ iter (succ m) f) (e โปยน)
                  (reflexivity (๐ โป) (iter (succ m) f))

\end{code}

For convenience, we now specialize to ๐คโ-dcpos (directed completeness for the
lowest universe), because โ lives in ๐คโ.

Of course, we can easily construct โ' : ๐ฅ in any ๐ฅ with โ โ โ' and work with
this equivalent type when dealing with ๐ฅ-dcpos. But this would require going
back-and-forth along the equivalence which would be somewhat cumbersome and we
don't have a practical use for it anyway (at the time of writing).

\begin{code}

module _ where

 open import Dcpo pt fe ๐คโ
 open import DcpoMiscelanea pt fe ๐คโ
 open import DcpoExponential pt fe ๐คโ

 module _ (๐ : DCPOโฅ {๐ค} {๐ฃ}) where

  iter-is-directed : is-directed (ฮป F G โ โ f โ F f โโช ๐ โซ G f) (iter ๐)
  iter-is-directed = โฃ zero โฃ , ฮด
   where
    ฮด : (i j : โ)
      โ โ k ๊ โ , ((f : DCPO[ (๐ โป) , (๐ โป) ]) โ iter ๐ i f โโช ๐ โซ iter ๐ k f)
                ร ((f : DCPO[ (๐ โป) , (๐ โป) ]) โ iter ๐ j f โโช ๐ โซ iter ๐ k f)
    ฮด i j = โฃ i +' j , l , m โฃ
     where
      l : (f : DCPO[ (๐ โป) , (๐ โป) ]) โ iter ๐ i f โโช ๐ โซ iter ๐ (i +' j) f
      l = iter-increases ๐ i (i +' j)
           (cosubtraction i (i +' j) (j , (addition-commutativity j i)))
      m : (f : DCPO[ (๐ โป) , (๐ โป) ]) โ iter ๐ j f โโช ๐ โซ iter ๐ (i +' j) f
      m = iter-increases ๐ j (i +' j) (cosubtraction j (i +' j) (i , refl))

  ฮผ : DCPO[ ((๐ โนแตแถแตแตโฅ ๐) โป) , (๐ โป) ]
  ฮผ = continuous-functions-sup ((๐ โนแตแถแตแตโฅ ๐) โป) (๐ โป) (iter-c ๐) iter-is-directed

  ฮผ-gives-a-fixed-point : (f : DCPO[ (๐ โป) , (๐ โป) ])
                        โ [ (๐ โนแตแถแตแตโฅ ๐) โป , ๐ โป ]โจ ฮผ โฉ f
                          โก [ ๐ โป , ๐ โป ]โจ f โฉ
                             ([ (๐ โนแตแถแตแตโฅ ๐) โป , ๐ โป ]โจ ฮผ โฉ f)
  ฮผ-gives-a-fixed-point fc = antisymmetry (๐ โป) (ฮฝ fc) (f (ฮฝ fc)) l m
   where
    ฮฝ : DCPO[ (๐ โป) , (๐ โป) ] โ โช ๐ โซ
    ฮฝ = [ (๐ โนแตแถแตแตโฅ ๐) โป , ๐ โป ]โจ ฮผ โฉ
    f : โช ๐ โซ โ โช ๐ โซ
    f = [ ๐ โป , ๐ โป ]โจ fc โฉ
    ฮด : is-directed (underlying-order (๐ โป))
         (pointwise-family ((๐ โนแตแถแตแตโฅ ๐) โป) (๐ โป) (iter-c ๐) fc)
    ฮด = pointwise-family-is-directed ((๐ โนแตแถแตแตโฅ ๐) โป) (๐ โป) (iter-c ๐)
        iter-is-directed fc

    l : ฮฝ fc โโช ๐ โซ f (ฮฝ fc)
    l = โ-is-lowerbound-of-upperbounds (๐ โป) ฮด (f (ฮฝ fc)) h
     where
      h : (n : โ) โ iter ๐ n fc โโช ๐ โซ f (ฮฝ fc)
      h zero     = โฅ-is-least ๐ (f (ฮฝ fc))
      h (succ n) = monotone-if-continuous (๐ โป) (๐ โป) fc
                   (iter ๐ n fc)
                   (ฮฝ fc)
                   (โ-is-upperbound (๐ โป) ฮด n)

    m : f (ฮฝ fc) โโช ๐ โซ ฮฝ fc
    m = sup-is-lowerbound-of-upperbounds (underlying-order (๐ โป))
         (continuity-of-function (๐ โป) (๐ โป) fc โ ฮฑ ฮด) (ฮฝ fc) k
     where
      ฮฑ : โ โ โช ๐ โซ
      ฮฑ = pointwise-family ((๐ โนแตแถแตแตโฅ ๐) โป) (๐ โป) (iter-c ๐) fc
      k : (n : โ) โ [ ๐ โป , ๐ โป ]โจ fc โฉ (ฮฑ n) โโช ๐ โซ ฮฝ fc
      k n = f (ฮฑ n)    โโช ๐ โซ[ reflexivity (๐ โป) (f (ฮฑ n))      ]
            ฮฑ (succ n) โโช ๐ โซ[ โ-is-upperbound (๐ โป) ฮด (succ n) ]
            ฮฝ fc       โโช ๐ โซ

  ฮผ-gives-lowerbound-of-fixed-points :
      (f : DCPO[ (๐ โป) , (๐ โป) ])
      (d : โช ๐ โซ)
    โ [ ๐ โป , ๐ โป ]โจ f โฉ d  โโช ๐ โซ d
    โ [ (๐ โนแตแถแตแตโฅ ๐) โป , ๐ โป ]โจ ฮผ โฉ f โโช ๐ โซ d
  ฮผ-gives-lowerbound-of-fixed-points f d l =
   โ-is-lowerbound-of-upperbounds (๐ โป)
    (pointwise-family-is-directed ((๐ โนแตแถแตแตโฅ ๐) โป) (๐ โป) (iter-c ๐)
      iter-is-directed f)
    d g
    where
     g : (n : โ) โ iter ๐ n f โโช ๐ โซ d
     g zero     = โฅ-is-least ๐ d
     g (succ n) = iter ๐ (succ n) f    โโช ๐ โซ[ k ]
                  [ ๐ โป , ๐ โป ]โจ f โฉ d โโช ๐ โซ[ l ]
                  d                    โโช ๐ โซ
      where
       k = monotone-if-continuous (๐ โป) (๐ โป) f (iter ๐ n f) d (g n)

\end{code}
