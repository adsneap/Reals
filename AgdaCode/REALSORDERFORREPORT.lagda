Andrew Sneap

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) -- TypeTopology

open import OrderNotation
open import RationalsOrder

open import UF-FunExt -- TypeTopology
open import UF-PropTrunc -- TypeTopology
open import UF-Powerset -- TypeTopology
open import UF-Subsingletons --TypeTopology
open import UF-Subsingletons-FunExt --TypeTopology

open import Rationals

module DedekindRealsOrder
         (pe : Prop-Ext) 
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
       where

open import DedekindReals pe pt fe
open PropositionalTruncation pt -- TypeTopology

_<ℝ_ : ℝ → ℝ → 𝓤₀ ̇
((Lx , Rx) , isCutx) <ℝ ((Ly , Ry) , isCuty) = ∃ q ꞉ ℚ , q ∈ Rx × q ∈ Ly

instance
 Strict-Order-ℝ-ℝ : Strict-Order ℝ ℝ
 _<_ {{Strict-Order-ℝ-ℝ}} = _<ℝ_

<-is-prop : (x y : ℝ) → is-prop (x < y)
<-is-prop x y = ∃-is-prop

ℝ<-trans : (x y z : ℝ) → x < y → y < z → x < z
ℝ<-trans ((Lx , Rx) , _) ((Ly , Ry) , _ , _ , _ , _ , disjoint-y , _) ((Lz , Rz) , _ , _ , rounded-left-z , _ , _ , _) l r = ∥∥-functor I (binary-choice l r)
 where
  I : (Σ q ꞉ ℚ , q ∈ Rx × q ∈ Ly) × (Σ p ꞉ ℚ , p ∈ Ry × p ∈ Lz ) → Σ s ꞉ ℚ , s ∈ Rx × s ∈ Lz
  I ((q , (qRx , qLy)) , (p , (pRy , pLz)))
   = q , (qRx , rounded-left-a Lz rounded-left-z q p (ℚ<-coarser-than-≤ q p (disjoint-y q p (qLy , pRy))) pLz)

_≤ℝ_ : ℝ → ℝ → 𝓤₀ ̇
((Lx , Rx) , isCutx) ≤ℝ ((Ly , Ry) , isCuty) = (q : ℚ) → q ∈ Lx → q ∈ Ly

instance
 Order-ℝ-ℝ : Order ℝ ℝ
 _≤_ {{Order-ℝ-ℝ}} = _≤ℝ_

≤-is-prop : (x y : ℝ) → is-prop (x ≤ y)
≤-is-prop ((Lx , Rx) , isCutx) ((Ly , Ry) , isCuty) = Π₂-is-prop fe (λ q _ → ∈-is-prop Ly q)

ℝ≤-trans : (x y z : ℝ) → x ≤ y → y ≤ z → x ≤ z
ℝ≤-trans ((Lx , Rx) , _) ((Ly , Ry) , _) ((Lz , Rz) , _) f g = λ q qLx → g q (f q qLx)

ℝ-archimedean : (x y : ℝ)
              → x < y
              → ∃ q ꞉ ℚ , q > x
                        × q < y
ℝ-archimedean x y l = l

weak-linearity : (x y z : ℝ) → x < y → x < z ∨ z < y
weak-linearity x y z l = ∥∥-rec ∨-is-prop I l
 where
  I : Σ q ꞉ ℚ , q > x × q < y → x < z ∨ z < y
  I (q , qRx , qLy) = ∥∥-rec ∨-is-prop II (binary-choice exists-r exists-s)
   where
    exists-r : ∃ r ꞉ ℚ , r < q × r > x
    exists-r = rounded-right-b (upper-cut-of x) (rounded-from-real-R x) q qRx
    exists-s : ∃ s ꞉ ℚ , q < s × s < y
    exists-s = rounded-left-b (lower-cut-of y) (rounded-from-real-L y) q qLy
    II : (Σ r ꞉ ℚ , r < q × r > x) × (Σ s ꞉ ℚ , q < s × s < y) → x < z ∨ z < y
    II ((r , r<q , rRx) , s , q<s , sLy) = ∥∥-rec ∨-is-prop IV III
     where
      III : r < z ∨ s > z
      III = located-from-real z r s (ℚ<-trans r q s r<q q<s)
      IV : r < z ∔ s > z → x < z ∨ z < y
      IV (inl rLz) = ∣ inl ∣ r , rRx , rLz ∣ ∣
      IV (inr sRz) = ∣ inr ∣ s , sRz , sLy ∣ ∣

_♯_ : (x y : ℝ) → 𝓤₀ ̇
x ♯ y = x < y ∨ y < x

apartness-gives-inequality : (x y : ℝ) → x ♯ y → ¬ (x ≡ y)
apartness-gives-inequality x y apart e = ∥∥-rec 𝟘-is-prop I apart
 where
  I : x < y ∔ y < x → 𝟘
  I (inl l) = ∥∥-rec 𝟘-is-prop III II
   where
    II : x < x
    II = transport (x <_) (e ⁻¹) l
    III : Σ q ꞉ ℚ , q > x × q < x → 𝟘
    III (q , qRx , qLx) = ℚ<-not-itself q (disjoint-from-real x q q (qLx , qRx))
  I (inr r) = ∥∥-rec 𝟘-is-prop III II
   where
    II : y < y
    II = transport (y <_) e r
    III : Σ p ꞉ ℚ , p > y × p < y → 𝟘
    III (p , pRy , pLy) = ℚ<-not-itself p (disjoint-from-real y p p (pLy , pRy))

ℝ<-≤-trans : (x y z : ℝ) → x < y → y ≤ z → x < z
ℝ<-≤-trans x y z x<y y≤z = ∥∥-functor I x<y
 where
  I : Σ q ꞉ ℚ , q > x × q < y → Σ q' ꞉ ℚ , q' > x × q' < z
  I (q , qRx , qLy) = q , qRx , y≤z q qLy

ℝ-less-than-or-equal-not-greater : (x y : ℝ) → x ≤ y → ¬ (y < x)
ℝ-less-than-or-equal-not-greater x y x≤y y<x = ∥∥-rec 𝟘-is-prop I y<x
 where
  I : Σ q ꞉ ℚ , q > y × q < x → 𝟘
  I (q , qRy , qLx) = ℚ<-not-itself q (disjoint-from-real y q q ((x≤y q qLx) , qRy))

ℝ-less-than-not-greater-or-equal : (x y : ℝ) → x < y → ¬ (y ≤ x)
ℝ-less-than-not-greater-or-equal x y l₁ l₂ = ℝ-less-than-or-equal-not-greater y x l₂ l₁

ℝ-not-less-is-greater-or-equal : (x y : ℝ) → ¬ (x < y) → y ≤ x
ℝ-not-less-is-greater-or-equal x y nl p pLy = ∥∥-rec (∈-is-prop (lower-cut-of x) p) I (rounded-left-b (lower-cut-of y) (rounded-from-real-L y) p pLy)
 where
  I : Σ q ꞉ ℚ , p < q × q < y → p < x
  I (q , l , q<y) = ∥∥-rec (∈-is-prop (lower-cut-of x) p) II (located-from-real x p q l)
   where
    II : p < x ∔ q > x → p < x
    II (inl p<x) = p<x
    II (inr x<q) = 𝟘-elim (nl ∣ q , (x<q , q<y) ∣)

ℝ≤-<-trans : (x y z : ℝ) → x ≤ y → y < z → x < z
ℝ≤-<-trans x y z x≤y y<z = ∥∥-functor I y<z
 where
  I : Σ q ꞉ ℚ , q > y × q < z
    → Σ q' ꞉ ℚ , q' > x × q' < z
  I (q , qRy , qLz) = q , ∥∥-rec (∈-is-prop (upper-cut-of x) q) III II , qLz
   where
    II : ∃ k ꞉ ℚ , k < q × k > y
    II = rounded-right-b (upper-cut-of y) (rounded-from-real-R y) q qRy 

    III : Σ k ꞉ ℚ , k < q × k > y → q > x
    III (k , k<q , kRy) = ∥∥-rec (∈-is-prop (upper-cut-of x) q) IV (located-from-real x k q k<q)
     where
      IV : k < x ∔ q > x → q > x
      IV (inl kLx) = 𝟘-elim (ℚ<-not-itself k (disjoint-from-real y k k (x≤y k kLx , kRy)))
      IV (inr qRx) = qRx

ℝ-less-than-not-itself : (x : ℝ) → x ≮ x
ℝ-less-than-not-itself x l = ∥∥-rec 𝟘-is-prop I l
 where
  I : (Σ k ꞉ ℚ , k > x × k < x) → 𝟘
  I (k , x<k , k<x) = ℚ<-not-itself k (disjoint-from-real x k k (k<x , x<k))

ℝ-zero-less-than-one : 0ℝ < 1ℝ
ℝ-zero-less-than-one = ∣ 1/2 , 0<1/2 , 1/2<1 ∣

ℝ-zero-apart-from-one : 0ℝ ♯ 1ℝ
ℝ-zero-apart-from-one = ∣ inl ℝ-zero-less-than-one ∣



