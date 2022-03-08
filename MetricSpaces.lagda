Andrew Sneap

\begin{code}
{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT renaming (_+_ to _∔_)  -- TypeTopology
open import CanonicalMapNotation --TypeTopology
open import OrderNotation --TypeTopology
open import UF-FunExt -- TypeTopology
open import UF-PropTrunc -- TypeTopology
open import UF-Subsingletons --TypeTopology

module MetricSpaces
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
         (pe : Prop-Ext)
       where 

open import DedekindReals pe pt fe
open import DedekindRealsOrder pe pt fe
open PropositionalTruncation pt

M1 : {𝓤 : Universe} → (X : 𝓤 ̇) → (d : X → X → ℝ) → 𝓤₁ ⊔ 𝓤 ̇
M1 X d = (x y : X) → d x y ≡ 0ℝ ⇔ x ≡ y

M2 : {𝓤 : Universe} → (X : 𝓤 ̇) → (d : X → X → ℝ) → 𝓤₁ ⊔ 𝓤 ̇
M2 X d = (x y : X) → d x y ≡ d y x

open import DedekindRealsAddition pe pt fe
open import DedekindRealsOrder pe pt fe

M3 : {𝓤 : Universe} → (X : 𝓤 ̇) → (d : X → X → ℝ) → 𝓤 ̇
M3 X d = (x y z : X) → (d x y) + (d y z) ≤ d x z

MetricSpace : {𝓤 : Universe} → (X : 𝓤 ̇) → 𝓤₁ ⊔ 𝓤 ̇
MetricSpace X = Σ d ꞉ (X → X → ℝ) , M1 X d × M2 X d × M3 X d

open import MetricSpaceAltDef pt fe pe
open import Rationals
open import RationalsOrder
{-
metric-space→MetricSpace : {𝓤 : Universe}
                         → (X : 𝓤 ̇)
--                         → (B : X → X → (ε : ℚ) → 0ℚ < ε → 𝓤₀ ̇)
--                         → (d : (X → X → ℝ))
--                         → ((x y : X) → ((ε , l) : ℚ₊) → d x y ≤ ι ε ⇔ B x y ε l)
                         → metric-space X
                         → MetricSpace X
metric-space→MetricSpace X (B , m1' , m2' , m3' , m4') = d , {!!}
 where
  d : X → X → ℝ
  d x y = {!!}
-}

