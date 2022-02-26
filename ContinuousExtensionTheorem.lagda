\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) --TypeTopology

open import UF-Subsingletons
open import UF-FunExt
open import UF-PropTrunc
open import OrderNotation

open import Rationals
open import RationalsOrder
open import MetricSpaceRationals

module ContinuousExtensionTheorem
 (fe : Fun-Ext)
 (pe : Prop-Ext)
 (pt : propositional-truncations-exist)
  where

open PropositionalTruncation pt

open import DedekindReals pe pt fe
open import MetricSpaceAltDef pt fe pe
-- open import MetricSpaceDedekindReals pt fe pe

\end{code}

The goal is to solve the following proof from Simmons Introduction to Topology and Modern Analysis:

Let X be a metric space, let Y be a complete metric space, and A be a dense subspace of X.
If f is a uniformly continuous mapping of A into Y, then f can be extended uniquely to a uniformly continuous mapping g of X into Y.

In order to prove this, it is first necessary to introduce the definitions in the proof.

\begin{code}
{-
continuous : {M₁ : 𝓤 ̇} {M₂ : 𝓥 ̇} → (m₁ : metric-space M₁) → (m₂ : metric-space M₂) → (f : M₁ → M₂) → 𝓤 ̇ 
continuous {𝓤} {𝓥} {M₁} {M₂} (B₁ , conditions) (B₂ , conditions') f = (c : M₁) → (ε : ℚ) → (l : 0ℚ < ε) → Σ δ ꞉ ℚ , ((l₂ : 0ℚ < δ) → (x : M₁) → B₁ c x δ l₂ → B₂ (f c) (f x) ε l)

continuous-extension-theorem : {M₁ : 𝓤 ̇} → {M₂ : 𝓥 ̇} → (m₁ : metric-space M₁) → (m₂ : complete-metric-space M₂) → {!!}
continuous-extension-theorem = {!!}
-}

open import RationalsAddition

ℚ-succ : ℚ → ℚ
ℚ-succ q = q + 1ℚ

rationals-extension : (ℚ → ℚ) → ℝ → ℝ
rationals-extension f = {!!}

ℝ-succ : ℝ → ℝ
ℝ-succ = rationals-extension ℚ-succ
 where
  this : {!!}
  this = {!!}


\end{code}
