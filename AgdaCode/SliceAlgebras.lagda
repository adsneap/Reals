Martin Escardo 31 Jan 2019

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module SliceAlgebras
        (π£ : Universe)
       where

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
open import SliceMonad π£

double-π-charac : (X : π€ Μ )
                β π (π X) β (Ξ£ I κ π£ Μ , (Ξ£ J κ (I β π£ Μ ), ((i : I) β J i β X)))
double-π-charac X = Ξ£-cong (Ξ³ X)
 where
  Ξ³ : (X : π€ Μ ) (I : π£ Μ ) β (I β π X) β (Ξ£ J κ (I β π£ Μ ), ((i : I) β J i β X))
  Ξ³ X I = (I β Ξ£ J κ π£ Μ , (J β X))               ββ¨ Ξ Ξ£-distr-β β©
          (Ξ£ J κ (I β π£ Μ ), ((i : I) β J i β X)) β 

π-algebra : π€ Μ β π£ βΊ β π€ Μ
π-algebra X = Ξ£ s κ (π X β X), (s β Ξ· βΌ id) Γ (s β ΞΌ βΌ s β πΜ s)

free-π-algebra : is-univalent π£ β (X : π€ Μ ) β π-algebra (π X)
free-π-algebra ua X = ΞΌ , π-unit-leftβΌ ua , π-assocβΌ ua

joinop : π€ Μ β π£ βΊ β π€ Μ
joinop X = {I : π£ Μ } β (I β X) β X

π-alg-Lawβ : {X : π€ Μ } β joinop X β π€ Μ
π-alg-Lawβ {π€} {X} β = (x : X) β β (Ξ» (i : π) β x) β‘ x

π-alg-Lawβ : {X : π€ Μ } β joinop X β π£ βΊ β π€ Μ
π-alg-Lawβ {π€} {X} β = (I : π£ Μ ) (J : I β π£ Μ ) (f : Ξ£ J β X)
                     β β f β‘ β (Ξ» i β β (Ξ» j β f (i , j)))


π-alg : π€ Μ β π£ βΊ β π€ Μ
π-alg X = Ξ£ β κ joinop X , π-alg-Lawβ β Γ π-alg-Lawβ β

β : {X : π€ Μ } β (π X β X) β joinop X
β s {I} f = s (I , f)

βΜ : {X : π€ Μ } β π-algebra X β joinop X
βΜ (s , _) = β s

β : {X : π€ Μ } β π-alg X β joinop X
β (β , ΞΊ , ΞΉ) = β

lawβ : {X : π€ Μ } (a : π-alg X) β π-alg-Lawβ (β a)
lawβ (β , ΞΊ , ΞΉ) = ΞΊ

lawβ : {X : π€ Μ } (a : π-alg X) β π-alg-Lawβ (β a)
lawβ (β , ΞΊ , ΞΉ) = ΞΉ

π-morphism-charac : {X : π€ Μ } {Y : π₯ Μ }
                    (s : π X β X) (t : π Y β Y)
                    (h : X β Y)

                  β (h β s βΌ t β πΜ h)
                  β ({I : π£ Μ } (f : I β X) β h (β s f) β‘ β t (h β f))
π-morphism-charac s t h = qinveq (Ξ» H {I} f β H (I , f))
                                 ((Ξ» {Ο (I , f) β Ο {I} f}) ,
                                  (Ξ» _ β refl) ,
                                  (Ξ» _ β refl))


π-algebra-gives-alg : {X : π€ Μ } β π-algebra X β π-alg X
π-algebra-gives-alg (s , unit , assoc) =
                    β s ,
                    unit ,
                    (Ξ» I J f β assoc (I , (Ξ» i β J i , (Ξ» j β f (i , j)))))

π-alg-gives-algebra : {X : π€ Μ } β π-alg X β π-algebra X
π-alg-gives-algebra {π€} {X} (β , unit , ΞΉ) = s , unit , assoc
 where
  s : π X β X
  s (I , f) = β f
  assoc : s β ΞΌ βΌ s β πΜ s
  assoc (I , g) = ΞΉ I (prβ β g) Ξ» { (i , j) β prβ (g i) j }

π-alg-charac : {X : π€ Μ } β π-algebra X β π-alg X
π-alg-charac = qinveq π-algebra-gives-alg (π-alg-gives-algebra , ((Ξ» _ β refl) , (Ξ» _ β refl)))

Ξ -is-alg : funext π€ π₯
         β {X : π€ Μ } (A : X β π₯ Μ )
         β ((x : X) β π-alg (A x)) β π-alg (Ξ  A)
Ξ -is-alg {π€} {π₯} fe {X} A Ξ± = βΒ· , lβ , lβ
 where
  βΒ· : {I : π£ Μ } β (I β Ξ  A) β Ξ  A
  βΒ· f x = β (Ξ± x) (Ξ» i β f i x)
  lβ : (Ο : Ξ  A) β βΒ· (Ξ» i β Ο) β‘ Ο
  lβ Ο = dfunext fe (Ξ» x β lawβ (Ξ± x) (Ο x))
  lβ : (I : π£ Μ ) (J : I β π£ Μ ) (f : Ξ£ J β Ξ  A)
    β βΒ· f β‘ βΒ· (Ξ» i β βΒ· (Ξ» j β f (i , j)))
  lβ I J f = dfunext fe (Ξ» x β lawβ (Ξ± x) I J (Ξ» Ο β f Ο x))

universe-is-algebra-Ξ£ : is-univalent π£ β π-alg (π£ Μ )
universe-is-algebra-Ξ£ ua = sum , k , ΞΉ
 where
  sum : {I : π£ Μ } β (I β π£ Μ ) β π£ Μ
  sum = Ξ£
  k : (X : π£ Μ ) β Ξ£ (Ξ» i β X) β‘ X
  k X = eqtoid ua (π Γ X) X π-lneutral
  ΞΉ : (I : π£ Μ ) (J : I β π£ Μ ) (f : Ξ£ J β π£ Μ )
    β Ξ£ f β‘ Ξ£ (Ξ» i β Ξ£ (Ξ» j β f (i , j)))
  ΞΉ I J f = eqtoid ua _ _ Ξ£-assoc

universe-is-algebra-Ξ  : is-univalent π£ β π-alg (π£ Μ )
universe-is-algebra-Ξ  ua = prod , k , ΞΉ
 where
  fe : funext π£ π£
  fe = univalence-gives-funext ua
  prod : {I : π£ Μ } β (I β π£ Μ ) β π£ Μ
  prod = Ξ 
  k : (X : π£ Μ ) β Ξ  (Ξ» i β X) β‘ X
  k X = eqtoid ua (π β X) X (β-sym (πβ (univalence-gives-funext ua)))
  ΞΉ : (I : π£ Μ ) (J : I β π£ Μ ) (f : Ξ£ J β π£ Μ )
    β Ξ  f β‘ Ξ  (Ξ» i β Ξ  (Ξ» j β f (i , j)))
  ΞΉ I J f = eqtoid ua _ _ (curry-uncurry' fe fe)

\end{code}
