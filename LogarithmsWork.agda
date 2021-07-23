open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆)  -- TypeTopology

module LogarithmsWork where

open import BinaryNaturals --TypeTopology
open import NaturalsOrder renaming (_<_ to _ℕ<_ ; _≤_ to _ℕ≤_) --TypeTopology

height-preserves-≤-lemma₀ : (m : ℕ) → height (succ m) ℕ≤ succ (height m)
height-preserves-≤-lemma₀ zero     = ⋆
height-preserves-≤-lemma₀ (succ m) = I
 where
  I : size (Succ (Succ (binary m))) ℕ≤ succ (size (Succ (binary m)))
  I = {!!}

height-preserves-≤-lemma9 : (m : ℕ) → height (succ m) ℕ≤ succ (height m)
height-preserves-≤-lemma9 m = {!!}

-- succ (height n) = height (right n)

height-preserves-≤-lemma : (m : ℕ) → height m ℕ≤ height (succ m)
height-preserves-≤-lemma zero     = zero-minimal 0
height-preserves-≤-lemma (succ m) = {!!}
 where
  IH : height m ℕ≤ height (succ m)
  IH = height-preserves-≤-lemma m

--This result is needed. Clearly true. Unsure how to go about completion.
height-preserves-≤-lemma2 : (m : ℕ) → height m ℕ≤ height (succ m)
height-preserves-≤-lemma2 = induction base step
 where
  base : 𝟙
  base = ⋆

  step : (k : ℕ)
       → height k ℕ≤ height (succ k)
       → height (succ k) ℕ≤ height (succ (succ k))
  step k IH = {!!}

-- height is floor of log 2
height-preserves-≤ : (m n : ℕ) → m ℕ≤ n → height m ℕ≤ height n
height-preserves-≤ m = induction base step
 where
  base : m ℕ≤ 0 → height m ℕ≤ height 0
  base l = ≤-trans (height m) 0 (height 0) (transport (_ℕ≤ 0) (II ⁻¹) (≤-refl 0)) ⋆
   where
    I : m ≡ 0
    I = unique-minimal m l 
    II : height m ≡ 0
    II = height m ≡⟨ ap height I ⟩ height 0 ≡⟨ height-equation₀ ⟩ 0 ∎
  step : (k : ℕ)
       → (m ℕ≤ k → height m ℕ≤ height k)
       → m ℕ≤ succ k
       → height m ℕ≤ height (succ k)
  step k IH l = I (≤-split m k l)
   where
    I : (m ℕ≤ k) ∔ (m ≡ succ k) → height m ℕ≤ height (succ k)
    I (inl x) = ≤-trans (height m) (height k) (height (succ k)) II (height-preserves-≤-lemma k)
     where
      II : height m ℕ≤ height k
      II = IH x
    I (inr x) = transport (height m ℕ≤_) II III
     where
      II : height m ≡ height (succ k)
      II = ap height x

      III : height m ℕ≤ height m
      III = ≤-refl (height m)

-- The following code is not productive. Need to be very careful about less than since I am working with floors. Going to be a lot more difficult than first anticipated.
{-
need-this : (m : ℕ) → height m ℕ< height (succ m)
need-this zero     = ⋆
need-this (succ zero) = {!!}
need-this (succ (succ m)) = {!!}

height-preserves-< : (m n : ℕ) → m ℕ< n → height m ℕ< height n
height-preserves-< m = induction base step
 where
  base : m ℕ< 0 → height m ℕ< height 0
  base l = 𝟘-elim l

  step : (k : ℕ)
       → (m ℕ< k → height m ℕ< height k)
       →  m ℕ< succ k
       → height m ℕ< height (succ k)
  step k IH l = I (<-split m k l)
   where
    I : (m ℕ< k) ∔ (m ≡ k) → height m ℕ< height (succ k)
    I (inl x) = <-trans (height m) (height k) (height (succ k)) II {!!}
     where
      II : height m ℕ< height k
      II = IH x
    I (inr x) = {!!}
    
-}

open import Integers
open import Rationals renaming (_<_ to _ℚ<_) 

embedding-ℕ-in-ℚ : ℕ → ℚ
embedding-ℕ-in-ℚ n = toℚ (pos n , 0)

embedding-preserves-order : (m n : ℕ) → m ℕ< n → embedding-ℕ-in-ℚ m ℚ< embedding-ℕ-in-ℚ n
embedding-preserves-order m n l = {!!}
