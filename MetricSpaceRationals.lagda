\begin{code}

{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆)  -- TypeTopology

open import UF-FunExt

open import MetricSpaceAltDef
open import Rationals
open import RationalsAbs
open import RationalsAddition
open import RationalsNegation
open import RationalsOrder

module MetricSpaceRationals
         (fe : Fun-Ext)
 where

ℚ-metric : ℚ → ℚ → ℚ
ℚ-metric p q = abs (p - q)

ℚ-self-dist : Fun-Ext → (q : ℚ) → ℚ-metric q q ≡ 0ℚ
ℚ-self-dist fe q = ℚ-metric q q ≡⟨ by-definition ⟩
                   abs (q - q)   ≡⟨ ap abs (ℚ-inverse-sum-to-zero fe q) ⟩
                   abs 0ℚ        ≡⟨ by-definition ⟩
                   0ℚ ∎

ℚ-metric-commutes : (p q : ℚ) → ℚ-metric p q ≡ ℚ-metric q p
ℚ-metric-commutes p q = conclusion
 where
  conclusion : ℚ-metric p q ≡ ℚ-metric q p -- Ridiculous proof :(
  conclusion = ℚ-metric p q                   ≡⟨ by-definition ⟩
               abs (p - q)                    ≡⟨ ℚ-abs-neg-equals-pos fe (p - q) ⟩
               abs (- (p - q))                ≡⟨ by-definition ⟩
               abs (- (p + (- q)))            ≡⟨ ap (λ z → abs (- z)) (ℚ+-comm p (- q)) ⟩
               abs (- ((- q) + p))            ≡⟨ ap abs (ℚ-minus-dist fe (- q) p ⁻¹) ⟩
               abs ((- (- q)) + (- p))        ≡⟨ ap (λ z → abs (z + (- p))) (ℚ-minus-minus fe q ⁻¹) ⟩
               abs (q + (- p))                ≡⟨ by-definition ⟩
               abs (q - p)                    ≡⟨ by-definition ⟩
               ℚ-metric q p                   ∎

B-ℚ : (x y ε : ℚ) → 0ℚ < ε → 𝓤₀ ̇
B-ℚ x y ε l = ℚ-metric x y < ε

ℚ-m1a : m1a ℚ B-ℚ
ℚ-m1a x y f = I (ℚ≤-split fe 0ℚ (abs (x - y)) (ℚ-abs-is-positive (x - y)))
 where
  α : ℚ
  α = ℚ-metric x y
  I : (0ℚ < abs (x - y)) ∔ (0ℚ ≡ abs (x - y)) → x ≡ y
  I (inl z) = 𝟘-elim (ℚ<-not-itself α ζ)
   where
    ζ : α < α
    ζ = f α z
  I (inr z) = ii
   where
    i : (x - y) ≡ 0ℚ
    i = ℚ-abs-zero-is-zero fe (x - y) (z ⁻¹)
    ii : x ≡ y
    ii = x                      ≡⟨ ℚ-zero-right-neutral fe x ⁻¹ ⟩
         x + 0ℚ                 ≡⟨ ap (x +_) (ℚ-inverse-sum-to-zero fe y ⁻¹) ⟩
         x + (y - y)            ≡⟨ ap (x +_) (ℚ+-comm y (- y)) ⟩
         x + ((- y) + y)        ≡⟨ ℚ+-assoc fe x (- y) y ⁻¹ ⟩
         x + (- y) + y          ≡⟨ ap (_+ y) i ⟩
         0ℚ + y                 ≡⟨ ℚ-zero-left-neutral fe y ⟩ 
         y                      ∎
  
ℚ-m1b : m1b ℚ B-ℚ
ℚ-m1b x y l = transport (λ v → v < y) (ℚ-self-dist fe x ⁻¹) l

ℚ-m2 : m2 ℚ B-ℚ
ℚ-m2 x y ε l₁ B = transport (λ z → z < ε) (ℚ-metric-commutes x y) B

ℚ-m3 : m3 ℚ B-ℚ
ℚ-m3 x y ε₁ ε₂ l₁ l₂ l₃ B = ℚ<-trans (ℚ-metric x y) ε₁ ε₂ B l₃

ℚ-m4 : m4 ℚ B-ℚ
ℚ-m4 x y z ε₁ ε₂ l₁ l₂ B₁ B₂ = conclusion α
 where
  α : abs ((x - y) + (y - z)) ≤ (abs (x - y) + abs (y - z))
  α = ℚ-triangle-inequality fe (x - y) (y - z)

  β : (abs (x - y) + abs (y - z)) < (ε₁ + ε₂)
  β = ℚ<-adding (abs (x - y)) ε₁ (abs(y - z)) ε₂ B₁ B₂

  δ : abs ((x - y) + (y + (- z))) ≡ abs (x - z)
  δ = ap abs (ℚ-add-zero fe x (- z) y ⁻¹)

  conclusion : abs ((x - y) + (y - z)) ≤ (abs (x - y) + abs (y - z)) → abs (x - z) < (ε₁ + ε₂)
  conclusion l = I (ℚ≤-split fe (abs ((x - y) + (y - z))) ((abs (x - y) + abs (y - z))) l) 
   where
    I : (abs ((x - y) + (y - z)) < (abs (x - y) + abs (y - z))) ∔ (abs ((x - y) + (y - z)) ≡ abs (x - y) + abs (y - z)) → abs (x - z) < (ε₁ + ε₂)
    I (inl l) =  ℚ<-trans (abs (x - z)) ((abs (x - y) + abs (y - z))) (ε₁ + ε₂) γ β
     where
      γ : abs (x - z) < (abs (x - y) + abs (y - z))
      γ = transport (λ k → k < (abs (x - y) + abs (y - z))) δ l
    I (inr e) = transport (_< (ε₁ + ε₂)) (e ⁻¹ ∙ δ) β

ℚ-metric-space : metric-space ℚ
ℚ-metric-space = B-ℚ , ℚ-m1a , ℚ-m1b , ℚ-m2 , ℚ-m3 , ℚ-m4


\end{code}
