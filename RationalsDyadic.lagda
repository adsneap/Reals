

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) -- TypeTopology

open import CanonicalMapNotation
open import NaturalsMultiplication
open import NaturalNumbers
open import NaturalsAddition
open import ncRationals
open import Rationals
open import IntegersB

_ℕ^_ : ℕ → ℕ → ℕ
a ℕ^ b = ((a *_) ^ b) 1

zero-base : (a : ℕ) → a ℕ^ 0 ≡ 1
zero-base a = refl

infixl 33 _ℕ^_ 

2^ : ℕ → ℕ
2^ = 2 ℕ^_

prod-of-powers : (n a b : ℕ) → n ℕ^ a * n ℕ^ b ≡ n ℕ^ (a + b)
prod-of-powers n a zero     = refl
prod-of-powers n a (succ b) = I
 where
  I : n ℕ^ a * n ℕ^ succ b ≡ n ℕ^ (a + succ b)
  I = n ℕ^ a * n ℕ^ succ b  ≡⟨ refl ⟩
      n ℕ^ a * (n * n ℕ^ b) ≡⟨ mult-associativity (n ℕ^ a) n (n ℕ^ b) ⁻¹ ⟩
      n ℕ^ a * n * n ℕ^ b   ≡⟨ ap (_* n ℕ^ b) (mult-commutativity (n ℕ^ a) n) ⟩
      n * n ℕ^ a * n ℕ^ b   ≡⟨ mult-associativity n (n ℕ^ a) (n ℕ^ b) ⟩
      n * (n ℕ^ a * n ℕ^ b) ≡⟨ ap (n *_) (prod-of-powers n a b) ⟩
      n * n ℕ^ (a + b)      ≡⟨ refl ⟩
      n ℕ^ succ (a + b)     ≡⟨ refl ⟩
      n ℕ^ (a + succ b) ∎

raise-again : (n a b : ℕ) → (n ℕ^ a) ℕ^ b ≡ n ℕ^ (a * b)
raise-again n a zero     = refl
raise-again n a (succ b) = I
 where
  IH : n ℕ^ a ℕ^ b ≡ n ℕ^ (a * b)
  IH = raise-again n a b
  
  I : n ℕ^ a ℕ^ succ b ≡ n ℕ^ (a * succ b)
  I = n ℕ^ a ℕ^ succ b       ≡⟨ refl ⟩
      n ℕ^ a * (n ℕ^ a) ℕ^ b ≡⟨ ap (n ℕ^ a *_) IH ⟩
      n ℕ^ a * n ℕ^ (a * b)  ≡⟨ prod-of-powers n a (a * b) ⟩
      n ℕ^ (a + a * b)       ≡⟨ refl ⟩
      n ℕ^ (a * succ b)      ∎

--Candidate One

ℤ[1/2] : 𝓤₀ ̇
ℤ[1/2] = Σ (z , n) ꞉ ℤ × ℕ , is-in-lowest-terms (z , 2^ n)

ℤ[1/2]-to-ℚ : ℤ[1/2] → ℚ
ℤ[1/2]-to-ℚ ((z , n) , lt) = (z , (2^ n)) , lt

instance
 canonical-map-ℤ[1/2]-to-ℚ : Canonical-Map ℤ[1/2] ℚ
 ι {{canonical-map-ℤ[1/2]-to-ℚ}} = ℤ[1/2]-to-ℚ

-- Alternatively, we could have an intermediary type, similar to my ℚₙ

ℤ[1/2]ₙ : 𝓤₀ ̇
ℤ[1/2]ₙ = ℤ × ℕ

-- Then write operators/relations for intermediary and elevate to ℤ[1/2]ₙ by adding lowest terms condition

-- We also have a second option.

--Candidate Two

is-power-of-2 : (n : ℕ) → 𝓤₀ ̇
is-power-of-2 n = Σ k ꞉ ℕ , n ≡ 2 ℕ^ k

ℤ[1/2]' : 𝓤₀ ̇
ℤ[1/2]' = Σ ((z , n) , _) ꞉ ℚ , is-power-of-2 n

--This option is probably preferable. Would still need to do work to write operators.

\end{code}


