Andrew Sneap


\begin{code}
{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆)  -- TypeTopology

open import UF-FunExt
open import Plus-Properties

open import Rationals
open import RationalsOrder

module RationalsMinMax (fe : Fun-Ext) where

max' : (x y : ℚ) → (x < y) ∔ (x ≡ y) ∔ (y < x) → ℚ
max' x y (inl z) = y
max' x y (inr z) = x

max : ℚ → ℚ → ℚ
max p q = max' p q (ℚ-trichotomous fe p q)

max'-to-max : (x y : ℚ) → (t : (x < y) ∔ (x ≡ y) ∔ (y < x)) → max' x y t ≡ max x y
max'-to-max x y t = equality-cases t I II
 where
  I : (l : x < y) → t ≡ inl l → max' x y t ≡ max x y
  I l e = max' x y t                         ≡⟨ ap (max' x y) e ⟩
          max' x y (inl l)                   ≡⟨ ap (max' x y) (ℚ-trich-a fe x y l ⁻¹) ⟩
          max' x y (ℚ-trichotomous fe x y)   ≡⟨ by-definition ⟩
          max x y              ∎
  II : (l : (x ≡ y) ∔ (y < x)) → t ≡ inr l → max' x y t ≡ max x y
  II r e = max' x y t                       ≡⟨ ap (max' x y) e ⟩
           max' x y (inr r)                 ≡⟨ ap (max' x y) (ℚ-trich-b fe x y r ⁻¹) ⟩
           max' x y (ℚ-trichotomous fe x y) ≡⟨ by-definition ⟩
           max x y ∎

max'-refl : (q : ℚ) → (t : (q < q) ∔ (q ≡ q) ∔ (q < q)) → max' q q t ≡ q
max'-refl q (inl l) = 𝟘-elim (ℚ<-not-itself q l)
max'-refl q (inr (inl l)) = l
max'-refl q (inr (inr l)) = 𝟘-elim (ℚ<-not-itself q l)

max-refl : (q : ℚ) → max q q ≡ q
max-refl q = I (ℚ-trichotomous fe q q)
 where
  I : (q < q) ∔ (q ≡ q) ∔ (q < q) → max q q ≡ q
  I t = max q q    ≡⟨ max'-to-max q q t ⁻¹ ⟩
        max' q q t ≡⟨ max'-refl q t ⟩
        q          ∎

max'-comm : (x y : ℚ)
            → (s : (x < y) ∔ (x ≡ y) ∔ (y < x))
            → (t : (y < x) ∔ (y ≡ x) ∔ (x < y))
            → max' x y s ≡ max' y x t
max'-comm x y (inl s) (inl t) = 𝟘-elim (ℚ<-not-itself x (ℚ<-trans x y x s t))
max'-comm x y (inl s) (inr (inl t)) = 𝟘-elim (ℚ<-not-itself y (transport (_< y) (t ⁻¹) s))
max'-comm x y (inl s) (inr (inr t)) = refl
max'-comm x y (inr (inl s)) (inl t) = refl
max'-comm x y (inr (inr s)) (inl t) = refl
max'-comm x y (inr (inl s)) (inr (inl t)) = s
max'-comm x y (inr (inl s)) (inr (inr t)) = s
max'-comm x y (inr (inr s)) (inr (inl t)) = t ⁻¹
max'-comm x y (inr (inr s)) (inr (inr t)) = 𝟘-elim (ℚ<-not-itself x (ℚ<-trans x y x t s))

max-comm : (p q : ℚ) → max p q ≡ max q p
max-comm x y =
 max x y                           ≡⟨ max'-to-max x y (ℚ-trichotomous fe x y) ⟩
 max' x y (ℚ-trichotomous fe x y)  ≡⟨ max'-comm x y (ℚ-trichotomous fe x y) (ℚ-trichotomous fe y x) ⟩
 max' y x (ℚ-trichotomous fe y x)  ≡⟨ max'-to-max y x (ℚ-trichotomous fe y x) ⟩
 max y x ∎

max'-to-≤ : (p q : ℚ) → (t : (p < q) ∔ (p ≡ q) ∔ (q < p))
                     → (p ≤ q) × (max' p q t ≡ q)
                     ∔ (q ≤ p) × (max' p q t ≡ p)
max'-to-≤ p q (inl t) = Cases (ℚ-trichotomous fe p q) I II
 where
  I : p < q → (p ≤ q) × (max' p q (inl t) ≡ q) ∔ (q ≤ p) × (max' p q (inl t) ≡ p)
  I l = inl ((ℚ<-coarser-than-≤ p q l) , refl)
  II : (p ≡ q) ∔ (q < p) → (p ≤ q) × (max' p q (inl t) ≡ q) ∔ (q ≤ p) × (max' p q (inl t) ≡ p)
  II (inl e) = 𝟘-elim (ℚ<-not-itself p (transport (p <_) (e ⁻¹) t))
  II (inr l) = 𝟘-elim (ℚ<-not-itself p (ℚ<-trans p q p t l))
max'-to-≤ p q (inr t) = inr (I t , refl)
 where
  I : (p ≡ q) ∔ (q < p) → q ≤ p
  I (inl l) = transport (q ≤_) (l ⁻¹) (ℚ≤-refl q)
  I (inr l) = ℚ<-coarser-than-≤ q p l

max-to-≤ : (p q : ℚ) → (p ≤ q) × (max p q ≡ q) ∔ q ≤ p × (max p q ≡ p)
max-to-≤ p q = I (max'-to-≤ p q (ℚ-trichotomous fe p q))
 where
  I : (p ≤ q) × (max' p q (ℚ-trichotomous fe p q) ≡ q)
    ∔ (q ≤ p) × (max' p q (ℚ-trichotomous fe p q) ≡ p)
    → (p ≤ q) × (max p q ≡ q) ∔ (q ≤ p) × (max p q ≡ p)
  I (inl t) = inl t
  I (inr t) = inr t

min' : (x y : ℚ) → (x < y) ∔ (x ≡ y) ∔ (y < x) → ℚ
min' x y (inl _) = x
min' x y (inr _) = y

min : ℚ → ℚ → ℚ
min p q = min' p q (ℚ-trichotomous fe p q)
 where
  I : (p < q) ∔ (p ≡ q) ∔ (q < p) → ℚ
  I (inl z) = p
  I (inr z) = q

min'-to-min : (x y : ℚ) → (t : (x < y) ∔ (x ≡ y) ∔ (y < x)) → min' x y t ≡ min x y 
min'-to-min x y t = equality-cases t I II
 where
  I : (k : x < y) → t ≡ inl k → min' x y t ≡ min x y
  I k e = min' x y t       ≡⟨ ap (min' x y) e ⟩
          min' x y (inl k) ≡⟨ ap (min' x y) (ℚ-trich-a fe x y k ⁻¹) ⟩
          min' x y (ℚ-trichotomous fe x y) ≡⟨ by-definition ⟩
          min x y ∎
  II : (k : (x ≡ y) ∔ (y < x)) → t ≡ inr k → min' x y t ≡ min x y
  II k e = min' x y t                      ≡⟨ ap (min' x y) e ⟩
          min' x y (inr k)                 ≡⟨ ap (min' x y) (ℚ-trich-b fe x y k ⁻¹) ⟩
          min' x y (ℚ-trichotomous fe x y) ≡⟨ by-definition ⟩
          min x y ∎

min'-refl : (q : ℚ) → (t : (q < q) ∔ (q ≡ q) ∔ (q < q)) → min' q q t ≡ q
min'-refl q (inl l) = 𝟘-elim (ℚ<-not-itself q l)
min'-refl q (inr (inl l)) = l
min'-refl q (inr (inr l)) = 𝟘-elim (ℚ<-not-itself q l)

min-refl : (q : ℚ) → min q q ≡ q
min-refl q = I (ℚ-trichotomous fe q q)
 where
  I : (q < q) ∔ (q ≡ q) ∔ (q < q) → min q q ≡ q
  I t = min q q    ≡⟨ min'-to-min q q t ⁻¹ ⟩
        min' q q t ≡⟨ min'-refl q t ⟩
        q          ∎

min'-comm : (x y : ℚ)
            → (s : (x < y) ∔ (x ≡ y) ∔ (y < x))
            → (t : (y < x) ∔ (y ≡ x) ∔ (x < y))
            → min' x y s ≡ min' y x t
min'-comm x y (inl s) (inl t) = 𝟘-elim (ℚ<-not-itself x (ℚ<-trans x y x s t))
min'-comm x y (inl s) (inr (inl t)) = 𝟘-elim (ℚ<-not-itself y (transport (_< y) (t ⁻¹) s))
min'-comm x y (inl s) (inr (inr t)) = refl
min'-comm x y (inr (inl s)) (inl t) = refl
min'-comm x y (inr (inr s)) (inl t) = refl
min'-comm x y (inr (inl s)) (inr (inl t)) = t
min'-comm x y (inr (inl s)) (inr (inr t)) = s ⁻¹
min'-comm x y (inr (inr s)) (inr (inl t)) = t
min'-comm x y (inr (inr s)) (inr (inr t)) = 𝟘-elim (ℚ<-not-itself x (ℚ<-trans x y x t s))

min-comm : (p q : ℚ) → min p q ≡ min q p
min-comm x y =
 min x y                           ≡⟨ min'-to-min x y (ℚ-trichotomous fe x y) ⟩
 min' x y (ℚ-trichotomous fe x y)  ≡⟨ min'-comm x y (ℚ-trichotomous fe x y) (ℚ-trichotomous fe y x) ⟩
 min' y x (ℚ-trichotomous fe y x)  ≡⟨ min'-to-min y x (ℚ-trichotomous fe y x) ⟩
 min y x ∎

min'-to-≤ : (p q : ℚ) → (t : (p < q) ∔ (p ≡ q) ∔ (q < p))
                     → (p ≤ q) × (min' p q t ≡ p)
                     ∔ (q ≤ p) × (min' p q t ≡ q)
min'-to-≤ p q (inl t) = Cases (ℚ-trichotomous fe p q) I II
 where
  I : p < q → (p ≤ q) × (min' p q (inl t) ≡ p) ∔ (q ≤ p) × (min' p q (inl t) ≡ q)
  I l = inl ((ℚ<-coarser-than-≤ p q l) , refl)
  II : (p ≡ q) ∔ (q < p) → (p ≤ q) × (min' p q (inl t) ≡ p) ∔ (q ≤ p) × (min' p q (inl t) ≡ q)
  II (inl e) = 𝟘-elim (ℚ<-not-itself p (transport (p <_) (e ⁻¹) t))
  II (inr l) = 𝟘-elim (ℚ<-not-itself p (ℚ<-trans p q p t l))
min'-to-≤ p q (inr t) = inr (I t , refl)
 where
  I : (p ≡ q) ∔ (q < p) → q ≤ p
  I (inl l) = transport (q ≤_) (l ⁻¹) (ℚ≤-refl q)
  I (inr l) = ℚ<-coarser-than-≤ q p l

min-to-≤ : (p q : ℚ) → (p ≤ q) × (min p q ≡ p) ∔ q ≤ p × (min p q ≡ q)
min-to-≤ p q = I (min'-to-≤ p q (ℚ-trichotomous fe p q))
 where
  I : (p ≤ q) × (min' p q (ℚ-trichotomous fe p q) ≡ p)
    ∔ (q ≤ p) × (min' p q (ℚ-trichotomous fe p q) ≡ q)
    → (p ≤ q) × (min p q ≡ p) ∔ (q ≤ p) × (min p q ≡ q)
  I (inl t) = inl t
  I (inr t) = inr t

≤-to-min' : (x y : ℚ) → x ≤ y → (t : (x < y) ∔ (x ≡ y) ∔ (y < x)) → x ≡ min' x y t
≤-to-min' x y l (inl t) = refl
≤-to-min' x y l (inr (inl t)) = t
≤-to-min' x y l (inr (inr t)) = I (ℚ≤-split fe x y l)
 where
  I : (x < y) ∔ (x ≡ y) → x ≡ min' x y (inr (inr t))
  I (inl s) = 𝟘-elim (ℚ<-not-itself x (ℚ<-trans x y x s t))
  I (inr s) = s

≤-to-min : (x y : ℚ) → x ≤ y → x ≡ min x y
≤-to-min x y l = I (≤-to-min' x y l (ℚ-trichotomous fe x y))
 where
  I : x ≡ min' x y (ℚ-trichotomous fe x y) → x ≡ min x y
  I e = e







