Andrew Sneap - 8th January 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆) --TypeTopology
open import UF-Base

open import Rationals
open import RationalsOrder

module RationalsExtension where

\end{code}

The proof is simple, and doesn't require condition (1) from the jamboard.

\begin{code}

order-preserving-and-bijection : (f : ℚ → ℚ)
                               → (g : ℚ → ℚ) 
                               → ((p q : ℚ) → p < q ⇔ f p < f q)
                               → ((r : ℚ) → (g (f r) ≡ r) × (f (g r) ≡ r))
                               → ((p q : ℚ) → p < q ⇔ g p < g q)
order-preserving-and-bijection f g f-preserves-order f-g-bijection = γ
 where
  γ : (p q : ℚ) → (p < q) ⇔ (g p < g q)
  γ p q = I , II
   where
    α : (g p < g q) ⇔ (f (g p) < f (g q))
    α = f-preserves-order (g p) (g q)
    
    I : p < q → g p < g q
    I l = (rl-implication α) i
     where
      i : f (g p) < f (g q)
      i = transport₂ _<_ (pr₂ (f-g-bijection p) ⁻¹) (pr₂ (f-g-bijection q) ⁻¹) l


    II : g p < g q → p < q
    II l = transport₂ _<_ (pr₂ (f-g-bijection p)) (pr₂ (f-g-bijection q)) i
     where
      i : f (g p) < f (g q)
      i = (lr-implication α) l

\end{code}
The code without the unneeded assumption.
\begin{code}

order-preserving-and-bijection' : (f : ℚ → ℚ)
                               → (g : ℚ → ℚ) 
                               → ((p q : ℚ) → p < q ⇔ f p < f q)
                               → ((r : ℚ) → (f (g r) ≡ r))
                               → ((p q : ℚ) → p < q ⇔ g p < g q)
order-preserving-and-bijection' f g f-preserves-order f-g-bijection = γ
 where
  γ : (p q : ℚ) → (p < q) ⇔ (g p < g q)
  γ p q = I , II
   where
    α : (g p < g q) ⇔ (f (g p) < f (g q))
    α = f-preserves-order (g p) (g q)

    f-preserves-order-forward : f (g p) < f (g q) → g p < g q
    f-preserves-order-forward = rl-implication α

    f-preserves-order-backward : g p < g q → f (g p) < f (g q)
    f-preserves-order-backward = lr-implication α
    
    I : p < q → g p < g q
    I l = f-preserves-order-forward i
     where
      i : f (g p) < f (g q)
      i = transport₂ _<_ ((f-g-bijection p) ⁻¹) ((f-g-bijection q) ⁻¹) l

    II : g p < g q → p < q
    II l = transport₂ _<_ (f-g-bijection p) (f-g-bijection q) i
     where
      i : f (g p) < f (g q)
      i = f-preserves-order-backward l 


