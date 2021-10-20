
\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆) --TypeTopology

import NaturalsAddition --TypeTopology

import NaturalsMultiplication

module NumberTheory where

-- Attempts to write parts of the number theory module within Agda.

-- open import Integers
-- open import IntegersHCF
-- open import IntegersDivision

open import NaturalsDivision

isPrime : (a : ℕ) → 𝓤₀ ̇
isPrime a = ((d : ℕ) → ¬ (d ∣ a))

open import NaturalsMultiplication
open import HCF

prime-lemma : (p : ℕ) → (a b : ℕ) → isPrime p → p ∣ (a * b) → (p ∣ a) ∔ (p ∣ b)
prime-lemma p a b f (x , e) = {!!}
 where
  hcf-p-a : Σ h ꞉ ℕ , is-hcf h p a
  hcf-p-a = HCF p a
  
  h = pr₁ hcf-p-a
  
  I : is-hcf h p a
  I = pr₂ hcf-p-a
  



{-
isPrime : (a : ℤ) → 𝓤₀ ̇
isPrime a = ((d : ℕ) → ¬ {!!})

prime-lemma : (p : ℕ) → (a b : ℤ) → ℤ-is-common-divisor (pos p) a b → ((pos p) ∣ a) ∔ ((pos p) ∣ b)
prime-lemma p a b (α , β) = {!!}
-}


\end{code}
