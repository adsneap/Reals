
\begin{code}
{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆)  -- TypeTopology
open import Rationals
open import NewDedekindReals
open import UF-PropTrunc
open import UF-FunExt

module MetricSpaces
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
       where 

--X should have a zero-element
--X should be ordered
--X should have equality

metric : {𝓤 : Universe} → {X : 𝓤 ̇} → {!!}
metric = {!!}


--single variable 
final-goal : (ℚ → ℝ pt fe) → (ℝ pt fe → ℝ pt {!fe!})
final-goal = {!!}

\end{code}
