open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆)  -- TypeTopology

module LogarithmsWork where

open import BinaryNaturals --TypeTopology
open import NaturalsOrder --TypeTopology

--This result is needed. Clearly true. Unsure how to go about completion.
height-preserves-≤-lemma : (m : ℕ) → height m ≤ height (succ m)
height-preserves-≤-lemma = induction base step
 where
  base : 𝟙
  base = ⋆

  step : (k : ℕ)
       → height k ≤ height (succ k)
       → height (succ k) ≤ height (succ (succ k))
  step k IH = {!!}

-- height is floor of log 2
height-preserves-≤ : (m n : ℕ) → m ≤ n → height m ≤ height n
height-preserves-≤ m = induction base step
 where
  base : m ≤ 0 → height m ≤ height 0
  base l = ≤-trans (height m) 0 (height 0) (transport (_≤ 0) (II ⁻¹) (≤-refl 0)) ⋆
   where
    I : m ≡ 0
    I = unique-minimal m l 
    II : height m ≡ 0
    II = height m ≡⟨ ap height I ⟩ height 0 ≡⟨ height-equation₀ ⟩ 0 ∎
  step : (k : ℕ)
       → (m ≤ k → height m ≤ height k)
       → m ≤ succ k
       → height m ≤ height (succ k)
  step k IH l = I (≤-split m k l)
   where
    I : (m ≤ k) ∔ (m ≡ succ k) → height m ≤ height (succ k)
    I (inl x) = ≤-trans (height m) (height k) (height (succ k)) II (height-preserves-≤-lemma k)
     where
      II : height m ≤ height k
      II = IH x
    I (inr x) = transport (height m ≤_) II III
     where
      II : height m ≡ height (succ k)
      II = ap height x

      III : height m ≤ height m
      III = ≤-refl (height m)
