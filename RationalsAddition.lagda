Andrew Sneap

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆) --TypeTopology

open import UF-Base hiding (_≈_) --TypeTopology
open import UF-FunExt -- TypeTopology

open import IntegersB
open import ncRationals
open import ncRationalsOperations renaming (_+_ to _ℚₙ+_)
open import Rationals

module RationalsAddition where

_+_ : ℚ → ℚ → ℚ
(p , _) + (q , _) = toℚ (p ℚₙ+ q)

infixl 32 _+_ 

ℚ+-comm : (p q : ℚ) → p + q ≡ q + p
ℚ+-comm (p , _) (q , _) = ap toℚ I
 where
  I : p ℚₙ+ q ≡ q ℚₙ+ p
  I = ℚₙ+-comm p q

toℚ-+ : Fun-Ext → (p q : ℚₙ) → toℚ (p ℚₙ+ q) ≡ (toℚ p + toℚ q)
toℚ-+ fe p q = equiv→equality fe (p ℚₙ+ q) (p' ℚₙ+ q') conclusion
 where
  p-ℚ = toℚ p
  q-ℚ = toℚ q
  p' = toℚₙ p-ℚ -- ncRational p
  q' = toℚₙ q-ℚ -- ncRational q

  I : p ≈ p'
  I = ≈-toℚ p
  
  II : q ≈ q'
  II = ≈-toℚ q

  III : (p ℚₙ+ q) ≈ (p' ℚₙ+ q)
  III = ≈-addition p p' q I

  IV : (q ℚₙ+ p') ≈ (q' ℚₙ+ p')
  IV = ≈-addition  q q' p' II

  V : (p' ℚₙ+ q) ≈ (p' ℚₙ+ q')
  V = transport₂ _≈_ (ℚₙ+-comm q p') (ℚₙ+-comm q' p') IV
  
  conclusion : (p ℚₙ+ q) ≈ (p' ℚₙ+ q')
  conclusion = ≈-trans (p ℚₙ+ q) (p' ℚₙ+ q) (p' ℚₙ+ q') III V
  
ℚ+-assoc : Fun-Ext → (p q r : ℚ) → (p + q) + r ≡ p + (q + r)
ℚ+-assoc fe (x , p) (y , q) (z , r) = V
 where
  α β : ℚ
  α = toℚ (x ℚₙ+ y)
  β = toℚ (y ℚₙ+ z) 

  III : Σ r' ꞉ ℚₙ , (z , r ≡ toℚ r')
  III = q-has-qn fe ((z , r))
  r' = pr₁ III
  rp = pr₂ III

  IV : Σ p' ꞉ ℚₙ , (x , p ≡ toℚ p')
  IV = q-has-qn fe ((x , p))
  p' = pr₁ IV
  pp = pr₂ IV

  V : (toℚ (x ℚₙ+ y) + (z , r)) ≡ ((x , p) + ((y , q) + (z , r)))
  V =  α + (z , r)          ≡⟨ ap (α +_) rp ⟩
       α + toℚ r'           ≡⟨ toℚ-+ fe (x ℚₙ+ y) r' ⁻¹ ⟩
       toℚ (x ℚₙ+ y ℚₙ+ z)   ≡⟨ ap toℚ (ℚₙ+-assoc x y z) ⟩
       toℚ (x ℚₙ+ (y ℚₙ+ z)) ≡⟨ toℚ-+ fe p' (y ℚₙ+ z) ⟩
       toℚ p' + β           ≡⟨ ap (_+ β) (pp ⁻¹) ⟩
       (x , p) + β ∎

ℚ-zero-left-neutral : Fun-Ext → (q : ℚ) → 0ℚ + q ≡ q
ℚ-zero-left-neutral fe q = II
 where
  I : Σ q' ꞉ ℚₙ , q ≡ toℚ q'
  I = q-has-qn fe q

  q' : ℚₙ
  q' = pr₁ I

  II : (0ℚ + q) ≡ q
  II = 0ℚ + q               ≡⟨ refl ⟩
       toℚ ((pos 0 , 0) ℚₙ+ q') ≡⟨ ap toℚ (ℚₙ+-comm (pos 0 , 0) q') ⟩
       toℚ (q' ℚₙ+ (pos 0 , 0)) ≡⟨ ap toℚ (ℚₙ-zero-right-neutral q') ⟩
       toℚ q'                   ≡⟨ pr₂ I ⁻¹ ⟩
       q                        ∎

ℚ-zero-right-neutral : Fun-Ext → (q : ℚ) → q + 0ℚ ≡ q
ℚ-zero-right-neutral fe q = ℚ+-comm q 0ℚ ∙ (ℚ-zero-left-neutral fe q)

1/3+1/3 : Fun-Ext → 1/3 + 1/3 ≡ 2/3
1/3+1/3 fe = equiv→equality fe ((pos 1 , 2) ℚₙ+ (pos 1 , 2)) (pos 2 , 2) 1/3+1/3≈2/3

1/3+2/3 : Fun-Ext → 1/3 + 2/3 ≡ 1ℚ
1/3+2/3 fe = equiv→equality fe ((pos 1 , 2) ℚₙ+ (pos 2 , 2)) (pos 1 , 0) 1/3+2/3≈1
  




