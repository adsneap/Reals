open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆)  -- TypeTopology

module LogarithmsWork where

open import BinaryNaturals --TypeTopology
open import NaturalsOrder renaming (_<_ to _ℕ<_ ; _≤_ to _ℕ≤_) --TypeTopology
{-
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
   where
    I : height k ℕ< succ (height k)
    I = <-succ (height k)

    II : height (succ k) ℕ< succ (height (succ k))
    II = <-succ (height (succ k))
    
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
-}
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
open import ncRationals renaming (_<_ to _ℚₙ<)
open import Rationals renaming (_<_ to _ℚ<_ ; _*_ to _ℚ*_ ; _≤_ to _ℚ≤_)
open import IntegersOrder renaming (_<_ to _ℤ<_)

embedding-ℕ-in-ℚ : ℕ → ℚ
embedding-ℕ-in-ℚ n = toℚ (pos n , 0)

embedding-preserves-order : (m n : ℕ) → m ℕ< n → embedding-ℕ-in-ℚ m ℚ< embedding-ℕ-in-ℚ n
embedding-preserves-order m n l = I
 where
  I : toℚ (pos m , 0) ℚ< toℚ (pos n , 0)
  I = <-lemma (pos m , 0) (pos n , 0) II
   where
    II : pos m ℤ< pos n 
    II = ℕ-order-respects-ℤ-order m n l

embedding-ℤ-in-ℚ : ℤ → ℚ
embedding-ℤ-in-ℚ z = toℚ (z , 0)

{-
ℚ-floor : (q : ℚ) → Σ z ꞉ ℤ , ((embedding-ℤ-in-ℚ z) ℚ< q) × {!!}
ℚ-floor q = {!!}
-}

-- Work with positive bases

_ℚ^_ : ℚ → ℕ → ℚ
q ℚ^ zero   = toℚ (pos 1 , 0)
q ℚ^ succ n = rec q (_ℚ* q) n

⟨2/3⟩^_ : ℕ → ℚ
⟨2/3⟩^ 0  = toℚ (pos 1 , 0)
⟨2/3⟩^ (succ n)  = rec (toℚ (pos 2 , 2)) (λ k → k ℚ* toℚ (pos 2 , 2)) n

_ℚ<_ℚ<_ : (q1 q2 q3 : ℚ) → 𝓤₀ ̇
q1 ℚ< q2 ℚ< q3 = (q1 ℚ< q2) × (q2 ℚ< q3)

log_base_ : (q : ℚ) → (b : ℕ) → Σ n ꞉ ℕ , ((toℚ (pos b , 0) ℚ^ n) ℚ≤ q) × (q ℚ< (toℚ (pos b , 0) ℚ^ n))
log q base zero   = {!!}
log q base succ b = {!!}

exists-2/3-n : (x p : ℚ) → zero-ℚ ℚ< x → zero-ℚ ℚ< p → Σ n ꞉ ℕ , (((⟨2/3⟩^ n) ℚ* x) ℚ< p)
exists-2/3-n x p l₁ l₂ = {!!} , {!!}

lim : (f : ℕ → ℚ) → 𝓤₀ ̇ 
lim f = ∀ (ε : ℕ) → (n : ℕ) →  Σ N ꞉ ℕ , ((N ℕ< n) → f n ℚ< toℚ (pos ε , zero))

conv : (f : ℕ → ℚ) → 𝓤₀ ̇
conv f = ∀ (ε : ℚ) → zero-ℚ ℚ< ε → (n : ℕ) → Σ N ꞉ ℕ , ((N ℕ< n) → f n ℚ< ε)

sandwich' : (f g : ℕ → ℚ) → (Σ M ꞉ ℕ , ((m : ℕ) → (M ℕ< m) → (f m ℚ< g m))) → conv g → conv f
sandwich' f g (n' , h) conv-g = I
 where
  I : conv f
  I ε l n = II (conv-g ε l n) 
   where
    II : (Σ N ꞉ ℕ , (N ℕ< n → g n ℚ< ε)) → Σ N ꞉ ℕ , (N ℕ< n → f n ℚ< ε)
    II (N , α) = N , III
     where
      III : _ ℕ< n → f n ℚ< ε
      III l₂ = ℚ<-trans (f n) (g n) ε (h n {!!}) (α l₂)

sandwich : (f g : ℕ → ℚ) → ((n : ℕ) → f n ℚ< g n) → lim g → lim f 
sandwich f g h g-holds = I
 where
  I : ∀ (ε : ℕ) → (n : ℕ) →  Σ N ꞉ ℕ , ((N ℕ< n) → f n ℚ< toℚ (pos ε , zero))
  I ε n = II (g-holds ε n)
   where
    II : Σ N ꞉ ℕ , (N ℕ< n → g n ℚ< toℚ (pos ε , zero)) → Σ N ꞉ ℕ , ((N ℕ< n) → f n ℚ< toℚ (pos ε , zero))
    II (N , l₂) = N , III
     where
      III : N ℕ< n → f n ℚ< toℚ (pos ε , zero)
      III l = ℚ<-trans (f n) (g n) (toℚ (pos ε , zero)) (h n) (l₂ l)

1/n : ℕ → ℚ
1/n zero = toℚ (pos 2 , 0)
1/n (succ n) = toℚ (pos 1 , n)

two-thirds-goes-down : lim ⟨2/3⟩^_
two-thirds-goes-down = sandwich (⟨2/3⟩^_) 1/n I II
 where
  I : (n : ℕ) → (⟨2/3⟩^ n) ℚ< 1/n n
  I = induction base step
   where
    base : (⟨2/3⟩^ 0) ℚ< 1/n 0
    base = (pos 1) , (⋆ , refl)

    step : (k : ℕ) → (⟨2/3⟩^ k) ℚ< 1/n k → (⟨2/3⟩^ succ k) ℚ< 1/n (succ k)
    step zero IH     = (pos 1) , (⋆ , refl)
    step (succ k) IH = {!!}
  II : lim 1/n
  II = λ ε n → {!!} , {!!}
