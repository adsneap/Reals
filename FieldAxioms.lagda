Andrew Sneap - 27th April 2021

I link to this module within the Dedekind Reals and Discussion sections of my report.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


open import SpartanMLTT renaming (_+_ to _∔_  ; _⁻¹ to sym ) -- TypeTopology

import UF-Subsingletons

module FieldAxioms where

distributive : {X : 𝓤 ̇ } → (X → X → X) → (X → X → X) → 𝓤 ̇
distributive _⊕_ _⊙_ = ∀ x y z → x ⊙ (y ⊕ z) ≡ ((x ⊙ y) ⊕ (x ⊙ z))

field-structure : 𝓤 ̇ → 𝓤 ̇
field-structure F = (F → F → F) × (F → F → F)

open UF-Subsingletons

field-axioms : (F : 𝓤 ̇) → field-structure F → 𝓤 ̇
field-axioms F (_⊕_ , _⊙_) = is-set F × associative _⊕_
                                       × associative _⊙_
                                       × commutative _⊕_
                                       × commutative _⊙_
                                       × distributive _⊕_ _⊙_
                                       × (Σ (e , e') ꞉ F × F , (¬ (e ≡ e') × left-neutral e _⊕_
                                                                           × ((x : F) → Σ x' ꞉ F , x ⊕ x' ≡ e) 
                                                                           × left-neutral e' _⊙_
                                                                           × ((x : F) → ¬ (x ≡ e) → Σ x' ꞉ F , x ⊙ x' ≡ e' )))

Field-structure : 𝓤 ̇ → 𝓤 ̇
Field-structure F = Σ fs ꞉ field-structure F , field-axioms F fs

ordered-field-structure : {𝓤 𝓥 : Universe} → (F : 𝓤 ̇) → (fs : field-structure F) → (fa : field-axioms F fs) → 𝓤 ⊔ (𝓥 ⁺) ̇
ordered-field-structure {𝓤} {𝓥} F fs fa = (F → F → 𝓥 ̇)


ordered-field-axioms : {𝓤 𝓥 : Universe} → (F : 𝓤 ̇) → (fs : field-structure F) → (fa : field-axioms F fs) →  ordered-field-structure { 𝓤 } { 𝓥 } F fs fa → 𝓤 ⊔ 𝓥 ̇
ordered-field-axioms {𝓤} {𝓥} F (_⊕_ , _⊙_) (s , a , a' , c , c' , d , (e , e') , i) _<_ = ((x y z : F) → x < y → (x ⊕ z) < (y ⊕ z))
                                                                                      × ((x y : F) → e < x → e < y → e < (x ⊙ y))

Ordered-field-structure : {𝓤 𝓥 : Universe} → (F : 𝓤 ̇) → Field-structure F → 𝓤 ⊔ (𝓥 ⁺) ̇
Ordered-field-structure {𝓤} {𝓥} F (fs , fa) = Σ ofa ꞉ (ordered-field-structure {𝓤} {𝓥} F fs fa) , ordered-field-axioms {𝓤} {𝓥} F fs fa ofa



\end{code}
