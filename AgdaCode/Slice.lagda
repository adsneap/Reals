Martin Escardo, 6th December 2018.

Cf. The lifting monad.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module Slice (ð£ : Universe) where

open import UF-Base
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-Subsingletons

ð : ð¤ Ì â ð¤ â ð£ âº Ì
ð X = Î£ I ê ð£ Ì , (I â X)

source : {X : ð¤ Ì } â ð X â ð£ Ì
source (I , Ï) = I

family : {X : ð¤ Ì } (l : ð X) â source l â X
family (I , Ï) = Ï

Î· : {X : ð¤ Ì } â X â ð X
Î· x = ð , (Î» _ â x)

SIGMA : {X : ð¤ Ì } â ð  X â ð£ Ì
SIGMA (I , Ï) = I

PI : {X : ð¤ Ì } â ð  X â ð£ â ð¤ Ì
PI {ð¤} {X} (I , Ï) = Î£ s ê (X â I) , Ï â s â¡ id

pullback : {A : ð¤ Ì } {B : ð¥ Ì } {C : ð¦ Ì }
         â (A â C) â (B â C) â ð¤ â ð¥ â ð¦ Ì
pullback f g = Î£ x ê domain f , Î£ y ê domain g , f x â¡ g y

pprâ : {A : ð¤ Ì } {B : ð¥ Ì } {C : ð¦ Ì }
       {f : A â C} {g : B â C}
     â pullback f g â A
pprâ (x , y , p) = x

pprâ : {A : ð¤ Ì } {B : ð¥ Ì } {C : ð¦ Ì }
       {f : A â C} {g : B â C}
     â pullback f g â B
pprâ (x , y , p) = y

pprâ : {A : ð¤ Ì } {B : ð¥ Ì } {C : ð¦ Ì }
       {f : A â C} {g : B â C}
     â (z : pullback f g) â f (pprâ z) â¡ g (pprâ z)
pprâ (x , y , p) = p

to-span : {A : ð¤ Ì } {B : ð¥ Ì } {C : ð¦ Ì }
          (f : A â C) (g : B â C)
          (X : ð¤' Ì )
        â ð¤ â ð¥ â ð¦ â ð¤' Ì
to-span {ð¤} {ð¥} {ð¦} {ð¤'} {A} {B} {C} f g X =
 Î£ k ê (X â A) , Î£ l ê (X â B) , (f â k â¼ g â l)

â-pullback-â : {A : ð¤ Ì } {B : ð¥ Ì } {C : ð¦ Ì }
               (f : A â C) (g : B â C)
               (X : ð¤' Ì )
             â funext ð¤' (ð¤ â ð¥ â ð¦)
             â (X â pullback f g) â to-span f g X
â-pullback-â {ð¤} {ð¥} {ð¦} {ð¤Ì } {A} {B} {C} f g X fe =
 (X â pullback f g)                              ââ¨ i â©
 (X â Î£ p ê A Ã B , f (prâ p) â¡ g (prâ p))       ââ¨ ii â©
 (Î£ j ê (X â A Ã B) , f â prâ â j â¼ g â prâ â j) ââ¨ iii â©
 to-span f g X                                   â 
  where
   i   = Î -cong fe fe X
          (Î» _ â pullback f g)
          (Î» _ â Î£ p ê A Ã B , f (prâ p) â¡ g (prâ p))
          (Î» x â â-sym Î£-assoc)
   ii  = Î Î£-distr-â
   iii = qinveq Ï (Ï , (Î» x â refl) , (Î» x â refl))
    where
     Ï : (Î£ j ê (X â A Ã B) , f â prâ â j â¼ g â prâ â j)
       â to-span f g X
     Ï (j , H) = (prâ â j , prâ â j , H)

     Ï : to-span f g X
       â (Î£ j ê (X â A Ã B) , f â prâ â j â¼ g â prâ â j)
     Ï (k , l , H) = ((Î» x â (k x , l x)) , H)

pbf : {X : ð£ Ì } {Y : ð£ Ì } â (X â Y) â (ð Y â ð X)
pbf f (Y , Î³) = pullback f Î³ , pprâ

â : {X : ð¤ Ì } {Y : ð¥ Ì } â (X â Y) â (ð X â ð Y)
â f (A , Ï) = A , f â Ï

-- Using Proposition 2.3 of
-- https://ncatlab.org/nlab/show/locally+cartesian+closed+category
â : {X : ð£ Ì } {Y : ð£ Ì } â (X â Y) â (ð X â ð Y)
â {X} {Y} f (E , Ï) = pullback k l , pprâ
 where
  A : ð£ Ì
  A = Y

  B : ð£ Ì
  B = Î£ Ï ê (X â E) , f â¼ f â Ï â Ï

  C : ð£ Ì
  C = Î£ Ï ê (X â X) , f â¼ f â Ï

  k : Y â C
  k y = (id , Î» x â refl)

  l : B â C
  l (Ï , H) = (Ï â Ï , H)

open import UF-Classifiers
open import UF-Equiv
open import UF-FunExt
open import UF-Univalence

ð-equiv-particular : is-univalent ð£
                   â funext ð£ (ð£ âº)
                   â (X : ð£ Ì ) â ð X â (X â ð£ Ì )
ð-equiv-particular = map-classification

open import UF-Size
open import UF-Base
open import UF-Equiv-FunExt
open import UF-UA-FunExt
open import UF-UniverseEmbedding
open import UF-EquivalenceExamples

ð-equiv : Univalence â  (X : ð¤ Ì ) â ð X â (Î£ A ê (X â ð£ â ð¤ Ì ), (Î£ A) has-size ð£)
ð-equiv {ð¤} ua X = qinveq Ï (Ï , ÏÏ , ÏÏ)
 where
  fe : FunExt
  fe = Univalence-gives-FunExt ua

  Ï : ð X â Î£ A ê (X â ð£ â ð¤ Ì ), (Î£ A) has-size ð£
  Ï (I , Ï) = fiber Ï , I , â-sym (total-fiber-is-domain Ï)

  Ï : (Î£ A ê (X â ð£ â ð¤ Ì ), (Î£ A) has-size ð£) â ð X
  Ï (A , I , (f , e)) = I , prâ â f

  ÏÏ : (Ï : Î£ A ê (X â ð£ â ð¤ Ì ), (Î£ A) has-size ð£) â Ï (Ï Ï) â¡ Ï
  ÏÏ (A , I , (f , e)) = p
   where
    h : (x : X) â fiber (prâ â f) x â A x
    h x = (Î£ i ê I , prâ (f i) â¡ x) ââ¨ Î£-change-of-variable (Î» (Ï : Î£ A) â prâ Ï â¡ x) f e â©
          (Î£ Ï ê Î£ A , prâ Ï â¡ x)   ââ¨ prâ-fiber-equiv x â©
          A x                       â 

    p : fiber (prâ â f) , I , â-sym (total-fiber-is-domain (prâ â f)) â¡ A , I , f , e
    p = to-Î£-â¡ (dfunext (fe ð¤ ((ð£ â ð¤) âº)) (Î» x â eqtoid (ua (ð£ â ð¤)) (fiber (prâ â f) x) (A x) (h x)) ,
                has-size-is-prop ua (Î£ A) ð£ _ (I , f , e))
  ÏÏ : (l : ð X) â Ï (Ï l) â¡ l
  ÏÏ (I , Ï) = ap (Î» - â I , -) (dfunext (fe ð£ ð¤) (Î» i â refl))

\end{code}
