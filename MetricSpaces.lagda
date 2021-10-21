
\begin{code}
{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆)  -- TypeTopology
open import Rationals

open import UF-PropTrunc
open import UF-FunExt

module MetricSpaces
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
       where 
open import NewDedekindReals pt fe
--X should have a zero-element
--X should be ordered
--X should have equality

metric : {𝓤 : Universe} → {X : 𝓤 ̇} → {!!}
metric = {!!}

-- Ultrametric:
-- m : X × X → ℝ
-- m (x , y) ≡ 0 ⇔ x ≡ y
-- m (x , y) ≡ m (y , x)
-- m (x , z) ≤ max (m (x , y) , m (y , z))

-- ≤-max : R × R × R → 𝓤
-- ≤-max (x , y , z) = 

-- max : R × R → R
-- [    ]     x
-- [        ] y
-- [        ] max

-- A function f is uniformly continuous
-- ∀ ε , ∃ δ , m (x , y) ≤ δ → m (f x , f y) ≤ ε  
-- mod : ℝ (ε) → ℝ (δ)
-- mod := pr₁ ε

-- (ℚ → ℚ) → (ℝ → ℝ)
--single variable 
final-goal : (ℚ → ℝ) → (ℝ → ℝ)
final-goal f ((L , R) , conditions)  = {!!}

--           <--->δ
-- L[             ]x[            ]R
-- L[        ]fx[                ]R
---<---------->ε

-- L[ 1  2 ] x  [ 3 4 ]R
-- L[ 4  1 ] fx [ 2 3 ]R

embed : (ℚ → ℚ) → (ℝ → ℝ)
embed = final-goal ∘ (embedding-ℚ-to-ℝ ∘_)

\end{code}
