Martin Escardo 28 July 2018

Adapted from the module PropTychnoff to take order into account. The
file PropTychonoff has many comments, but this one doesn't.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt

module PropInfTychonoff (fe : FunExt) where

open import Two-Properties
open import CompactTypes
open import InfCompact
open import UF-Base
open import UF-Subsingletons
open import UF-PropIndexedPiSigma
open import UF-Equiv
open import UF-EquivalenceExamples

prop-inf-tychonoff : {X : ð¤ Ì } {Y : X â ð¥ Ì }
                   â is-prop X
                   â (_âº_ : {x : X} â Y x â Y x â ð¦ Ì )
                   â ((x : X) â inf-compact (Î» (y y' : Y x) â Â¬ (y' âº y)))
                   â inf-compact (Î» (Ï Î³ : Î  Y) â Â¬ (Î£ x ê X , Î³ x âº Ï x))
prop-inf-tychonoff {ð¤} {ð¥} {ð¦} {X} {Y} hp _âº_ Îµ p =
 Ïâ , Ïâ-is-conditional-root , a , b
 where
  _â¼_ : {x : X} â Y x â Y x â ð¦ Ì
  y â¼ y' = Â¬ (y' âº y)

  _â¤_ : Î  Y â Î  Y â ð¤ â ð¦ Ì
  Ï â¤ Î³ = Â¬ (Î£ x ê X , Î³ x âº Ï x)

  hip : (x : X) â Î  Y â Y x
  hip = prop-indexed-product (fe ð¤ ð¥) hp

  h : (x : X) â Y x â Î  Y
  h x = prâ(prâ(prâ(hip x)))

  hf : (x : X) (Ï : Î  Y) â h x (Ï x) â¡ Ï
  hf x = prâ(prâ(prâ(hip x)))

  q : (x : X) â Y x â ð
  q x y = p (h x y)

  Ïâ : Î  Y
  Ïâ x = prâ(Îµ x (q x))

  cr : (x : X) â (Î£ y ê Y x , p (h x y) â¡ â) â p (h x (Ïâ x)) â¡ â
  cr x = prâ(prâ(Îµ x (q x)))

  cr-particular-case : (x : X) â (Î£ Ï ê Î  Y , p (h x (Ï x)) â¡ â) â p (h x (Ïâ x)) â¡ â
  cr-particular-case x (Ï , r) = cr x (Ï x , r)

  Ïâ-is-conditional-root-assuming-X : X â (Î£ Ï ê Î  Y , p Ï â¡ â) â p Ïâ â¡ â
  Ïâ-is-conditional-root-assuming-X x (Ï , r) = s â t
   where
    s : p Ïâ â¡ p (h x (Ïâ x))
    s = ap p ((hf x Ïâ)â»Â¹)
    t : p (h x (Ïâ x)) â¡ â
    t = cr-particular-case x (Ï , (ap p (hf x Ï) â r))

  Ïâ-is-conditional-root-assuming-X-empty : Â¬ X â (Î£ Ï ê Î  Y , p Ï â¡ â) â p Ïâ â¡ â
  Ïâ-is-conditional-root-assuming-X-empty u (Ï , r) = ap p c â r
   where
    c : Ïâ â¡ Ï
    c = dfunext (fe ð¤ ð¥) (Î» x â unique-from-ð(u x))

  câ : (Î£ Ï ê Î  Y , p Ï â¡ â) â X â p Ïâ â¡ â
  câ Ï x = Ïâ-is-conditional-root-assuming-X x Ï

  Câ : (Î£ Ï ê Î  Y , p Ï â¡ â) â p Ïâ â¡ â â Â¬ X
  Câ Ï = contrapositive(câ Ï) â equal-â-different-from-â

  Câ : (Î£ Ï ê Î  Y , p Ï â¡ â) â Â¬ X â p Ïâ â¡ â
  Câ Ï u = Ïâ-is-conditional-root-assuming-X-empty u Ï

  Câ : (Î£ Ï ê Î  Y , p Ï â¡ â) â p Ïâ â¡ â â p Ïâ â¡ â
  Câ Ï = Câ Ï â Câ Ï

  Ïâ-is-conditional-root : (Î£ Ï ê Î  Y , p Ï â¡ â) â p Ïâ â¡ â
  Ïâ-is-conditional-root Ï = ð-equality-cases id (Câ Ï)

  Î± : (x : X) â (y : Y x) â q x y â¡ â â Ïâ x â¼ y
  Î± x = prâ(prâ(prâ(Îµ x (q x))))

  Î² : (x : X) â (l : Y x) â root-lower-bound _â¼_ (q x) l â l â¼ Ïâ x
  Î² x = prâ(prâ(prâ(Îµ x (q x))))

  a : (Ï : Î  Y) â p Ï â¡ â â Ïâ â¤ Ï
  a Ï r (x , l) = Î± x (Ï x) Î³ l
   where
    Î³ : p (h x (Ï x)) â¡ â
    Î³ = ap p (hf x Ï) â r

  b : (l : Î  Y) â root-lower-bound _â¤_ p l â l â¤ Ïâ
  b l u (x , m) = Î² x (l x) Î³ m
   where
    Î³ : (y : Y x) â p (h x y) â¡ â â l x â¼ y
    Î³ y r n = u Ïâ g (x , m)
     where
      g : p Ïâ â¡ â
      g = Ïâ-is-conditional-root (h x y , r)

\end{code}
