Andrew Sneap


\begin{code}
{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆)  -- TypeTopology

open import Rationals
open import RationalsAddition
open import RationalsOrder


module MetricSpaceAltDef where

m1a : {𝓤 : Universe} → (X : 𝓤 ̇) → (B : X → X → (ε : ℚ) → 0ℚ < ε → 𝓤₀ ̇) → 𝓤 ̇
m1a X B = (x y : X) → ((ε : ℚ) → (l : 0ℚ < ε) → B x y ε l) → x ≡ y

m1b : {𝓤 : Universe} → (X : 𝓤 ̇) → (B : X → X → (ε : ℚ) → 0ℚ < ε → 𝓤₀ ̇) → 𝓤 ̇
m1b X B = (x : X) → ((ε : ℚ) → (l : 0ℚ < ε) → B x x ε l)

m2 : {𝓤 : Universe} → (X : 𝓤 ̇) → (B : X → X → (ε : ℚ) → 0ℚ < ε → 𝓤₀ ̇) → 𝓤 ̇
m2 X B = (x y : X) → (ε : ℚ) → (l : 0ℚ < ε) → B x y ε l → B y x ε l

m3 : {𝓤 : Universe} → (X : 𝓤 ̇) → (B : X → X → (ε : ℚ) → 0ℚ < ε → 𝓤₀ ̇) → 𝓤 ̇
m3 X B = (x y : X) → (ε₁ ε₂ : ℚ) → (l₁ : 0ℚ < ε₁) → (l₂ : 0ℚ < ε₂) → ε₁ < ε₂ → B x y ε₁ l₁ → B x y ε₂ l₂

m4 : {𝓤 : Universe} → (X : 𝓤 ̇) → (B : X → X → (ε : ℚ) → 0ℚ < ε → 𝓤₀ ̇) → 𝓤 ̇
m4 X B = (x y z : X) → (ε₁ ε₂ : ℚ) → (l₁ : (0ℚ < ε₁)) → (l₂ : (0ℚ < ε₂)) → B x y ε₁ l₁ → B y z ε₂ l₂ → B x z (ε₁ + ε₂) (ℚ<-adding-zero ε₁ ε₂ l₁ l₂)

metric-space : {𝓤 : Universe} → (X : 𝓤 ̇) → 𝓤₁ ⊔ 𝓤 ̇
metric-space X =
 Σ B ꞉ (X → X → (ε : ℚ) → 0ℚ < ε → 𝓤₀ ̇) , m1a X B × m1b X B × m2 X B × m3 X B × m4 X B

\end{code}
