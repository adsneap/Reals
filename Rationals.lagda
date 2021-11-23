
\Andrew Sneap - 27th April 2021

I link to this module within the Rationals section of my report.

\begin{code}

{-# OPTIONS --without-K --exact-split --no-eta-equality #-}

-- Need to correct options to be consistent with type topology once field is ready
open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆) --TypeTopology

import DiscreteAndSeparated --TypeTopology
import Groups --TypeTopology
import NaturalsAddition --TypeTopology
import NaturalNumbers-Properties -- TypeTopology
import UF-Base -- TypeTopology
import UF-FunExt -- Typetopology
import UF-Miscelanea --TypeTopology
import UF-Subsingletons --Typetopology

import FieldAxioms
import HCF
import Integers

import IntegersOrder renaming (_≤_ to _ℤ≤_)
import IntegersProperties
import NaturalsMultiplication
import NaturalsDivision
import MoreNaturalProperties
import ncRationals

module Rationals where

open ncRationals renaming (_+_ to _ℚₙ+_ ; _<_ to _ℚₙ<_ ; _>_ to _ℚₙ>_ ; _*_ to _ℚₙ*_)

ℚ : 𝓤₀ ̇
ℚ = Σ q ꞉ ℚₙ , is-in-lowest-terms q

open DiscreteAndSeparated --TypeTopology
open UF-FunExt --TypeTopology
open UF-Miscelanea --TypeTopology
open UF-Subsingletons --TypeTopology

ℚ-is-discrete : Fun-Ext → is-discrete ℚ
ℚ-is-discrete fe = Σ-is-discrete ℚₙ-is-discrete λ q x y → inl (is-in-lowest-terms-is-prop fe q x y)

ℚ-is-set : Fun-Ext → is-set ℚ
ℚ-is-set fe = discrete-types-are-sets (ℚ-is-discrete fe)

toℚₙ : ℚ → ℚₙ
toℚₙ (q , ψ) = q

open HCF
open NaturalsMultiplication renaming (_*_ to _ℕ*_)
open NaturalNumbers-Properties --TypeTopology
open Integers renaming (_*_ to _ℤ*_ ; _+_ to _ℤ+_ ; -_ to ℤ-_)
open IntegersProperties

-- 

toℚlemma : ((x , a) : ℚₙ) → Σ ((x' , a') , p) ꞉ ℚ , (Σ h ꞉ ℕ , (x ≡ (pos (succ h)) ℤ* x') × (succ a ≡ (succ h) ℕ* succ a'))
toℚlemma (pos a , b) = f (divbyhcf a (succ b))
 where
  f : Σ h ꞉ ℕ , Σ x ꞉ ℕ , Σ y ꞉ ℕ , ((h ℕ* x ≡ a) × (h ℕ* y ≡ succ b)) × coprime x y → _
  f (h      , x , zero   , (γ₁ , γ₂) , r) = 𝟘-elim (positive-not-zero b (γ₂ ⁻¹))
  f (0      , x , succ y , (γ₁ , γ₂) , r) = 𝟘-elim (positive-not-zero b (γ₂ ⁻¹ ∙ zero-left-is-zero (succ y)))
  f (succ h , x , succ y , (γ₁ , γ₂) , r) = (((pos x) , y) , r) , h , I , (γ₂ ⁻¹)
   where
    I : pos a ≡ pos (succ h) ℤ* pos x
    I = pos a                 ≡⟨ ap pos γ₁ ⁻¹                                 ⟩                               
        pos (succ h ℕ* x)     ≡⟨ pos-multiplication-equiv-to-ℕ (succ h) x ⁻¹ ⟩
        pos (succ h) ℤ* pos x ∎
toℚlemma (negsucc a , b) = f (divbyhcf (succ a) (succ b))
 where
  f : ((Σ h ꞉ ℕ , Σ x ꞉ ℕ , Σ y ꞉ ℕ , ((h ℕ* x ≡ (succ a)) × (h ℕ* y ≡ succ b)) × coprime x y)) → _
  f (h      , x      , 0      , (γ₁ , γ₂) , r) = 𝟘-elim (positive-not-zero b (γ₂ ⁻¹))
  f (h      , 0      , succ y , (γ₁ , γ₂) , r) = 𝟘-elim (positive-not-zero a (γ₁ ⁻¹))
  f (0      , succ x , succ y , (γ₁ , γ₂) , r) = 𝟘-elim (positive-not-zero b (γ₂ ⁻¹ ∙ zero-left-is-zero (succ y)))
  f (succ h , succ x , succ y , (γ₁ , γ₂) , r) = (((negsucc x) , y) , r) , (h , (I , (γ₂ ⁻¹)))
   where
    i : pos (succ a) ≡ (pos (succ h) ℤ* pos (succ x))
    i = pos (succ a)                 ≡⟨ ap pos γ₁ ⁻¹                                        ⟩
        pos (succ h ℕ* succ x)       ≡⟨ pos-multiplication-equiv-to-ℕ (succ h) (succ x) ⁻¹ ⟩
        pos (succ h) ℤ* pos (succ x) ∎

    I : negsucc a ≡ pos (succ h) ℤ* negsucc x
    I = negsucc a                        ≡⟨ ap ℤ-_ i                                                     ⟩
        ℤ- pos (succ h) ℤ* pos (succ x)   ≡⟨ subtraction-dist-over-mult (pos (succ h)) (pos (succ x)) ⁻¹ ⟩
        pos (succ h) ℤ* (ℤ- pos (succ x)) ∎

--feed in ℚₙ
toℚ : ℚₙ → ℚ
toℚ q = pr₁ (toℚlemma q)

zero-ℚ : ℚ
zero-ℚ = toℚ ((pos zero) , zero)

1ℚ : ℚ
1ℚ = toℚ ((pos 1) , 0)

-1ℚ : ℚ
-1ℚ = toℚ ((negsucc 0) , 0)

_+_ : ℚ → ℚ → ℚ
(p , α) + (q , β) = toℚ (p ℚₙ+ q)

open UF-Base --TypeTopology

ℚ≡-to-ℚₙ≡ : ((p , α) (q , β) : ℚ) → (p , α) ≡ (q , β) → p ≡ q
ℚ≡-to-ℚₙ≡ (p , α) (q , β) e = pr₁ (from-Σ-≡ e)

open IntegersOrder renaming (_<_ to _ℤ<_ ; _>_ to _ℤ>_)

equiv-equality : Fun-Ext → (p q : ℚₙ) → p ℚₙ≈ q ⇔ toℚ p ≡ toℚ q
equiv-equality fe (x , a) (y , b) = I , II
 where
  α : Σ ((x' , a') , p) ꞉ ℚ , Σ h ꞉ ℕ , (x ≡ (pos (succ h) ℤ* x')) × (succ a ≡ succ h ℕ* succ a')
  α = toℚlemma (x , a)

  β : Σ ((y' , b') , p') ꞉ ℚ , Σ h' ꞉ ℕ , (y ≡ (pos (succ h') ℤ* y')) × (succ b ≡ succ h' ℕ* succ b')
  β = toℚlemma (y , b)

  h h' : ℕ
  h = pr₁ (pr₂ α)
  h' = pr₁ (pr₂ β)

  a' b' : ℕ
  a' = pr₂ (pr₁ (pr₁ α))
  b' = pr₂ (pr₁ (pr₁ β))

  x' y' : ℤ
  x' = pr₁ (pr₁ (pr₁ α))
  y' = pr₁ (pr₁ (pr₁ β))

  p : is-in-lowest-terms (x' , a')
  p = pr₂ (pr₁ α)

  p' : is-in-lowest-terms (y' , b')
  p' = pr₂ (pr₁ β)

  αₚ₁ : x ≡ pos (succ h) ℤ* x'
  αₚ₁ = pr₁ (pr₂ (pr₂ α))

  αₚ₂ : succ a ≡ succ h ℕ* succ a'
  αₚ₂ = pr₂ (pr₂ (pr₂ α))

  αₚ₂' : pos (succ a) ≡ pos (succ h) ℤ* pos (succ a')
  αₚ₂' = pos (succ a)                  ≡⟨ ap pos αₚ₂ ⟩
        pos (succ h ℕ* succ a')       ≡⟨ pos-multiplication-equiv-to-ℕ (succ h) (succ a') ⁻¹ ⟩
        pos (succ h) ℤ* pos (succ a') ∎

  βₚ₁ : y ≡ (pos (succ h') ℤ* y')
  βₚ₁ = pr₁ (pr₂ (pr₂ β))

  βₚ₂ : succ b ≡ succ h' ℕ* succ b'
  βₚ₂ = pr₂ (pr₂ (pr₂ β))

  βₚ₂' : pos (succ b) ≡ pos (succ h') ℤ* (pos (succ b'))
  βₚ₂' = pos (succ b)              ≡⟨ ap pos βₚ₂ ⟩
         pos (succ h' ℕ* succ b') ≡⟨ pos-multiplication-equiv-to-ℕ (succ h') (succ b') ⁻¹ ⟩
         pos (succ h') ℤ* pos (succ b') ∎

  I : (x , a) ℚₙ≈ (y , b) → ((x' , a') , p) ≡ ((y' , b') , p')
  I e = to-subtype-≡ (λ z → is-in-lowest-terms-is-prop fe z) (equiv-with-lowest-terms-is-equal (x' , a') (y' , b') f p p')
   where
    f : x' ℤ* (pos (succ b')) ≡ y' ℤ* (pos (succ a'))
    f = ℤ-mult-left-cancellable (x' ℤ* pos (succ b')) (y' ℤ* pos (succ a')) (pos (succ h)) (pos-succ-not-zero h) g
     where
      g : pos (succ h) ℤ* (x' ℤ* (pos (succ b'))) ≡ pos (succ h) ℤ* (y' ℤ* (pos (succ a')))
      g = ℤ-mult-left-cancellable (pos (succ h) ℤ* ((x' ℤ* pos (succ b')))) (pos (succ h) ℤ* (y' ℤ* pos (succ a'))) (pos (succ h')) (pos-succ-not-zero h') k
       where
        k : pos (succ h') ℤ* (pos (succ h) ℤ* (x' ℤ* (pos (succ b')))) ≡ pos (succ h') ℤ* (pos (succ h) ℤ* (y' ℤ* (pos (succ a'))))
        k = pos (succ h') ℤ* (pos (succ h) ℤ* (x' ℤ* pos (succ b')))       ≡⟨ ap (pos (succ h') ℤ*_) (ℤ*-assoc (pos (succ h)) x' (pos (succ b'))) ⟩
            pos (succ h') ℤ* ((pos (succ h) ℤ* x') ℤ* pos (succ b'))       ≡⟨ ap (λ z → pos (succ h') ℤ* (z ℤ* pos (succ b'))) (αₚ₁ ⁻¹) ⟩
            pos (succ h') ℤ* (x ℤ* pos (succ b'))                          ≡⟨ ℤ-mult-rearrangement''' (pos (succ h')) x (pos (succ b')) ⟩
            x ℤ* (pos (succ h') ℤ* pos (succ b'))                          ≡⟨ ap (x ℤ*_) (βₚ₂' ⁻¹) ⟩
            x ℤ* pos (succ b)                                              ≡⟨ e ⟩
            y ℤ* pos (succ a)                                              ≡⟨ ap₂ (λ z z' → z ℤ* z') βₚ₁ αₚ₂' ⟩
            pos (succ h') ℤ* y' ℤ* (pos (succ h) ℤ* pos (succ a'))         ≡⟨ ℤ*-assoc (pos (succ h')) y' (pos (succ h) ℤ* pos (succ a')) ⁻¹ ⟩
            pos (succ h') ℤ* (y' ℤ* (pos (succ h) ℤ* pos (succ a')))       ≡⟨ ap (pos (succ h') ℤ*_) (ℤ-mult-rearrangement''' y' (pos (succ h)) (pos (succ a'))) ⟩
            pos (succ h') ℤ* (pos (succ h) ℤ* (y' ℤ* pos (succ a')))       ∎

  II : toℚ (x , a) ≡ toℚ (y , b) → (x , a) ℚₙ≈ (y , b)
  II e = x ℤ* pos (succ b)                                              ≡⟨ ap₂ (λ z z' → z ℤ* z') αₚ₁ (ap pos βₚ₂) ⟩
         ((pos (succ h) ℤ* x') ℤ* pos (succ h' ℕ* succ b'))             ≡⟨ ap₂ (λ z z' → ((pos (succ h) ℤ* z) ℤ* pos (succ h' ℕ* succ z'))) (pr₁ iii) ((pr₂ iii) ⁻¹) ⟩
         ((pos (succ h) ℤ* y') ℤ* pos (succ h' ℕ* succ a'))             ≡⟨ ap (((pos (succ h) ℤ* y')) ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h') (succ a')) ⁻¹ ⟩
         ((pos (succ h) ℤ* y') ℤ* (pos (succ h') ℤ* pos (succ a')))     ≡⟨ ℤ-mult-rearrangement'' (pos (succ h')) (pos (succ h)) y' (pos (succ a')) ⟩
         (((pos (succ h') ℤ* y')) ℤ* (pos (succ h) ℤ* pos (succ a')))   ≡⟨ ap (((pos (succ h') ℤ* y')) ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h) (succ a')) ⟩ 
         ((pos (succ h') ℤ* y')) ℤ* pos (succ h ℕ* succ a')             ≡⟨ ap₂ (λ z z' → z ℤ* z') (pr₁ (pr₂ (pr₂ β)) ⁻¹) (ap pos (pr₂ (pr₂ (pr₂ α)) ⁻¹)) ⟩
         y ℤ* pos (succ a) ∎
    where
     i : Σ δ ꞉ (x' , a') ≡ (y' , b') , transport is-in-lowest-terms δ (pr₂ (toℚ (x , a))) ≡ pr₂ (toℚ (y , b))
     i = from-Σ-≡ e

     ii : x' , a' ≡ y' , b'
     ii = pr₁ i

     iii : (x' ≡ y') × (a' ≡ b')
     iii = from-×-≡' ii

≈-toℚ : (p : ℚₙ) → p ℚₙ≈ toℚₙ (toℚ p)
≈-toℚ (x , a) = conclusion
 where
  right-l : Σ ((x' , a') , p) ꞉ ℚ , (Σ h ꞉ ℕ , (x ≡ (pos (succ h)) ℤ* x') × (succ a ≡ (succ h) ℕ* succ a'))
  right-l = toℚlemma (x , a)

  right : ℚ
  right = toℚ (x , a)

  x' : ℤ
  x' = pr₁ (pr₁ right)
  a' : ℕ
  a' = pr₂ (pr₁ right)

  h : ℕ
  h = pr₁ (pr₂ right-l) 
    
  conclusion : x ℤ* pos (succ a') ≡ x' ℤ* pos (succ a)
  conclusion = x ℤ* pos (succ a')                    ≡⟨ ap (_ℤ* pos (succ a')) (pr₁ (pr₂ (pr₂ right-l))) ⟩
               (pos (succ h)) ℤ* x' ℤ* pos (succ a') ≡⟨ ap (_ℤ* pos (succ a')) (ℤ*-comm (pos (succ h)) x') ⟩
               x' ℤ* pos (succ h) ℤ* pos (succ a')   ≡⟨ ℤ*-assoc x' (pos (succ h)) (pos (succ a')) ⁻¹ ⟩
               x' ℤ* (pos (succ h) ℤ* pos (succ a')) ≡⟨ ap (x' ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h) (succ a')) ⟩
               x' ℤ* pos ((succ h) ℕ* succ a')       ≡⟨ ap (x' ℤ*_) (ap pos (pr₂ (pr₂ (pr₂ right-l))) ⁻¹ ) ⟩
               x' ℤ* pos (succ a) ∎

ℚ+-comm : (a b : ℚ) → a + b ≡ b + a
ℚ+-comm ((x , a) , p) ((y , b) , q) = ap toℚ I
 where
  I : ((x , a) ℚₙ+ (y , b)) ≡ ((y , b) ℚₙ+ (x , a))
  I = ℚₙ+-comm (x , a) (y , b)

toℚ-over-addition : Fun-Ext → (p q : ℚₙ) → toℚ (p ℚₙ+ q) ≡ toℚ p + toℚ q
toℚ-over-addition fe (x , a) (y , b) = helper I
 where
  p' = toℚ (x , a)
  q' = toℚ (y , b)

  x' y' : ℤ
  x' = pr₁ (pr₁ p')
  y' = pr₁ (pr₁ q')
  
  a' b' : ℕ
  a' = pr₂ (pr₁ p')
  b' = pr₂ (pr₁ q')

  helper : ((x , a) ℚₙ+ (y , b)) ℚₙ≈ ((x' , a') ℚₙ+ (y' , b')) → toℚ ((x , a) ℚₙ+ (y , b)) ≡ (toℚ (x , a) + toℚ (y , b))
  helper = pr₁ (equiv-equality fe ((x , a) ℚₙ+ (y , b)) ((x' , a') ℚₙ+ (y' , b')))

  aux₁ : (x , a) ℚₙ≈ (x' , a')
  aux₁ = ≈-toℚ (x , a)

  aux₂ : (y , b) ℚₙ≈ (y' , b')
  aux₂ = ≈-toℚ (y , b)

  aux₃ : ((x , a) ℚₙ+ (y , b)) ℚₙ≈ ((x' , a') ℚₙ+ (y , b))
  aux₃ = ≈-addition (x , a) (x' , a') (y , b) aux₁

  aux₄ : ((y' , b') ℚₙ+ (x' , a')) ℚₙ≈ ((y , b) ℚₙ+ (x' , a'))
  aux₄ = ≈-addition (y' , b') (y , b) (x' , a') (≈-sym (y , b) (y' , b') aux₂)

  aux₅ : ((y , b) ℚₙ+ (x' , a')) ℚₙ≈ ((y' , b') ℚₙ+ (x' , a'))
  aux₅ = ≈-sym ((y' , b') ℚₙ+ (x' , a')) ((y , b) ℚₙ+ (x' , a')) aux₄

  aux₆ : ((x' , a') ℚₙ+ (y , b)) ℚₙ≈ ((x' , a') ℚₙ+ (y' , b'))
  aux₆ = transport₂ _ℚₙ≈_ (ℚₙ+-comm (y , b) (x' , a')) (ℚₙ+-comm (y' , b') (x' , a')) aux₅
  
  I : ((x , a) ℚₙ+ (y , b)) ℚₙ≈ ((x' , a') ℚₙ+ (y' , b'))
  I = ≈-trans ((x , a) ℚₙ+ (y , b)) ((x' , a') ℚₙ+ (y , b)) ((x' , a') ℚₙ+ (y' , b')) aux₃ aux₆

q-has-qn : Fun-Ext → (q : ℚ) → Σ q' ꞉ ℚₙ , q ≡ toℚ q'
q-has-qn fe (q , p) = q , (to-subtype-≡ (is-in-lowest-terms-is-prop fe) (equiv-with-lowest-terms-is-equal q q' (≈-toℚ q) p (pr₂ right)))
 where
  right : ℚ
  right = toℚ q

  q' : ℚₙ
  q' = pr₁ right
  
ℚ+-assoc : Fun-Ext → (p q r : ℚ) → (p + q) + r ≡ p + (q + r)
ℚ+-assoc fe (x , p) (y , q) (z , r) = V
 where
  I II : ℚ
  I = toℚ (x ℚₙ+ y)
  II = toℚ (y ℚₙ+ z) 

  III : Σ r' ꞉ ℚₙ , (z , r ≡ toℚ r')
  III = q-has-qn fe ((z , r))

  IV : Σ p' ꞉ ℚₙ , (x , p ≡ toℚ p')
  IV = q-has-qn fe ((x , p))

  V : (toℚ (x ℚₙ+ y) + (z , r)) ≡ ((x , p) + ((y , q) + (z , r)))
  V = (I + (z , r))                     ≡⟨ ap (I +_) (pr₂ III) ⟩
        (I + toℚ (pr₁ III))                ≡⟨ toℚ-over-addition fe (x ℚₙ+ y) (pr₁ III) ⁻¹  ⟩
        toℚ ((x ℚₙ+ y) ℚₙ+ z)             ≡⟨ ap toℚ (ℚₙ+-assoc x y z) ⟩
        toℚ (x ℚₙ+ (y ℚₙ+ z))             ≡⟨ toℚ-over-addition fe (pr₁ IV) (y ℚₙ+ z) ⟩
        (toℚ (pr₁ IV) + II)                ≡⟨ ap (_+ II) (pr₂ IV ⁻¹) ⟩
        ((x , p) + II) ∎

_*_ : ℚ → ℚ → ℚ
(p , _) * (q , _) = toℚ (p ℚₙ* q)

toℚ-over-mult : Fun-Ext → (p q : ℚₙ) → toℚ (p ℚₙ* q) ≡ toℚ p * toℚ q
toℚ-over-mult fe (x , a) (y , b) = helper I
 where
  p' = toℚ (x , a)
  q' = toℚ (y , b)

  x' y' : ℤ
  x' = pr₁ (pr₁ p')
  y' = pr₁ (pr₁ q')
  
  a' b' : ℕ
  a' = pr₂ (pr₁ p')
  b' = pr₂ (pr₁ q') 
   
  helper : ((x , a) ℚₙ* (y , b)) ℚₙ≈ ((x' , a') ℚₙ* (y' , b')) → toℚ ((x , a) ℚₙ* (y , b)) ≡ toℚ ((x' , a') ℚₙ* (y' , b'))
  helper = pr₁ (equiv-equality fe ((x , a) ℚₙ* (y , b)) ((x' , a') ℚₙ* (y' , b')))

  aux₁ : (x , a) ℚₙ≈ (x' , a')
  aux₁ = ≈-toℚ (x , a)

  aux₂ : (y , b) ℚₙ≈ (y' , b')
  aux₂ = ≈-toℚ (y , b)

  aux₃ : ((x , a) ℚₙ* (y , b)) ℚₙ≈ ((x' , a') ℚₙ* (y , b))
  aux₃ = ≈-over-* (x , a) (x' , a') (y , b) aux₁

  aux₄ : ((y' , b') ℚₙ* (x' , a')) ℚₙ≈ ((y , b) ℚₙ* (x' , a'))
  aux₄ = ≈-over-* (y' , b') (y , b) (x' , a') (≈-sym (y , b ) (y' , b') aux₂)

  aux₅ : ((y , b) ℚₙ* (x' , a')) ℚₙ≈ ((y' , b') ℚₙ* (x' , a'))
  aux₅ = ≈-sym ((y' , b') ℚₙ* (x' , a')) ((y , b) ℚₙ* (x' , a')) aux₄

  aux₆ : ((x' , a') ℚₙ* (y , b)) ℚₙ≈ ((x' , a') ℚₙ* (y' , b'))
  aux₆ = transport₂ _ℚₙ≈_ (ℚₙ*-comm (y , b) (x' , a')) (ℚₙ*-comm (y' , b') (x' , a')) aux₅

  I : ((x , a) ℚₙ* (y , b)) ℚₙ≈ ((x' , a') ℚₙ* (y' , b'))
  I = ≈-trans ((x , a) ℚₙ* (y , b)) ((x' , a') ℚₙ* (y , b)) ((x' , a') ℚₙ* (y' , b')) aux₃ aux₆

ℚ*-comm : (p q : ℚ) → p * q ≡ q * p
ℚ*-comm (p , _) (q , _) = ap toℚ (ℚₙ*-comm p q)

ℚ*-assoc : Fun-Ext → (p q r : ℚ) → (p * q) * r ≡ p * (q * r)
ℚ*-assoc fe (x , p) (y , q) (z , r) = III
 where
  left : ℚ
  left = (x , p) * (y , q)

  right : ℚ
  right = (y , q) * (z , r)

  I : Σ l ꞉ ℚₙ , (z , r ≡ toℚ l)
  I = q-has-qn fe (z , r)

  II : Σ t ꞉ ℚₙ , (x , p ≡ toℚ t)
  II = q-has-qn fe (x , p)

  l t : ℚₙ
  l = pr₁ I
  t = pr₁ II

  III : toℚ (x ℚₙ* y) * (z , r) ≡ ((x , p) * toℚ (y ℚₙ* z))
  III = (left * (z , r))      ≡⟨ ap (left *_) (pr₂ I) ⟩
        left * toℚ z          ≡⟨ toℚ-over-mult fe (x ℚₙ* y) z ⁻¹ ⟩
        toℚ ((x ℚₙ* y) ℚₙ* z) ≡⟨ ap toℚ (ℚₙ*-assoc x y z) ⟩
        toℚ (x ℚₙ* (y ℚₙ* z)) ≡⟨ toℚ-over-mult fe x (y ℚₙ* z) ⟩
        (toℚ x * right)       ≡⟨ ap (_* right) (pr₂ II ⁻¹) ⟩
        ((x , p) * right) ∎

_<_ : ℚ → ℚ → 𝓤₀ ̇
(p , ψ) < (q , ζ) = p ℚₙ< q

ℚ<-is-prop : (p q : ℚ) → is-prop (p < q)
ℚ<-is-prop (p , α) (q , β) = ℚₙ<-is-prop p q

ℚ<-trans : (p q r : ℚ) → p < q → q < r → p < r
ℚ<-trans (p , α) (q , β) (c , γ) x y = ℚₙ-trans p q c x y

_≤_ : ℚ → ℚ → 𝓤₀ ̇
p ≤ q = (p < q) ∔ (p ≡ q)
{-
ℚ≤-is-prop : (p q : ℚ) → is-prop (p ≤ q)
ℚ≤-is-prop (p , ψ) (q , η) = -- ℚₙ≤-is-prop p q
-}
<-lemma : (p q : ℚₙ) → p ℚₙ< q → toℚ p < toℚ q 
<-lemma (x , a) (y , b) l = ordering-right-cancellable (x' ℤ* pos (succ b')) (y' ℤ* (pos (succ a'))) (pos (succ h ℕ* succ h')) IV V
 where
  I : Σ ((x' , a') , p) ꞉ ℚ , (Σ h ꞉ ℕ , (x ≡ (pos (succ h)) ℤ* x') × (succ a ≡ (succ h) ℕ* succ a'))
  I = toℚlemma (x , a)

  II : Σ ((y' , b') , p) ꞉ ℚ , (Σ h' ꞉ ℕ , (y ≡ (pos (succ h')) ℤ* y') × (succ b ≡ (succ h') ℕ* succ b'))
  II = toℚlemma (y , b)

  x' y' : ℤ
  x' = pr₁ (pr₁ (pr₁ I))
  y' = pr₁ (pr₁ (pr₁ II))

  a' b' : ℕ
  a' = pr₂ (pr₁ (pr₁ I))
  b' = pr₂ (pr₁ (pr₁ II))

  h h' : ℕ
  h = pr₁ (pr₂ I)
  h' = pr₁ (pr₂ II)

  α : x ≡ (pos (succ h)) ℤ* x'
  α = pr₁ (pr₂ (pr₂ I))

  β : succ a ≡ (succ h) ℕ* succ a'
  β = pr₂ (pr₂ (pr₂ I))

  α' : y ≡ (pos (succ h')) ℤ* y'
  α' = pr₁ (pr₂ (pr₂ II))

  β' : succ b ≡ (succ h') ℕ* succ b'
  β' = pr₂ (pr₂ (pr₂ II))

  III : greater-than-zero (pos (succ h) ℤ* pos (succ h'))
  III = greater-than-zero-mult-trans (pos (succ h)) (pos (succ h')) (pos-succ-greater-than-zero h) (pos-succ-greater-than-zero h')

  IV : greater-than-zero (pos (succ h ℕ* succ h'))
  IV = transport (λ z → greater-than-zero z) (pos-multiplication-equiv-to-ℕ (succ h) (succ h')) III

  V : ((x' ℤ* pos (succ b')) ℤ* pos (succ h ℕ* succ h')) ℤ< ((y' ℤ* pos (succ a')) ℤ* pos (succ h ℕ* succ h'))
  V = transport₂ (λ z z' → z ℤ< z') VI VII l
   where
    VI : x ℤ* pos (succ b) ≡ x' ℤ* pos (succ b') ℤ* pos (succ h ℕ* succ h')
    VI = x ℤ* pos (succ b)                                         ≡⟨ ap₂ (λ z z' → z ℤ* z') α (ap pos β') ⟩
          pos (succ h) ℤ* x' ℤ* pos (succ h' ℕ* succ b')            ≡⟨ ap (pos (succ h) ℤ* x' ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h') (succ b') ⁻¹) ⟩
          pos (succ h) ℤ* x' ℤ* (pos (succ h') ℤ* (pos (succ b')))  ≡⟨ ap₂ (λ z z' → z ℤ* z') (ℤ*-comm (pos (succ h)) x') (ℤ*-comm (pos (succ h')) (pos (succ b'))) ⟩
          x' ℤ* pos (succ h) ℤ* (pos (succ b') ℤ* pos (succ h'))    ≡⟨ ℤ*-assoc x' (pos (succ h)) (pos (succ b') ℤ* pos (succ h')) ⁻¹ ⟩
          x' ℤ* (pos (succ h) ℤ* (pos (succ b') ℤ* pos (succ h')))  ≡⟨ ap (x' ℤ*_) (ℤ-mult-rearrangement''' (pos (succ h)) (pos (succ b')) (pos (succ h'))) ⟩
          x' ℤ* (pos (succ b') ℤ* (pos (succ h) ℤ* pos (succ h')))  ≡⟨ ℤ*-assoc x' (pos (succ b')) (pos (succ h) ℤ* pos (succ h')) ⟩
          x' ℤ* pos (succ b') ℤ* (pos (succ h) ℤ* pos (succ h'))    ≡⟨ ap ( x' ℤ* pos (succ b') ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h) (succ h')) ⟩
          x' ℤ* pos (succ b') ℤ* pos (succ h ℕ* succ h') ∎

    VII : y ℤ* pos (succ a) ≡ y' ℤ* pos (succ a') ℤ* pos (succ h ℕ* succ h')
    VII = y ℤ* pos (succ a)                                         ≡⟨ ap₂ (λ z z' → z ℤ* z') α' (ap pos β) ⟩
           pos (succ h') ℤ* y' ℤ* pos (succ h ℕ* succ a')            ≡⟨ ap (pos (succ h') ℤ* y' ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h) (succ a') ⁻¹) ⟩
           pos (succ h') ℤ* y' ℤ* (pos (succ h) ℤ* pos (succ a'))    ≡⟨ ap₂ (λ z z' → z ℤ* z') (ℤ*-comm (pos (succ h')) y') (ℤ*-comm (pos (succ h)) (pos (succ a'))) ⟩
           y' ℤ* pos (succ h') ℤ* (pos (succ a') ℤ* pos (succ h))    ≡⟨ ℤ*-assoc y' (pos (succ h')) (pos (succ a') ℤ* pos (succ h)) ⁻¹ ⟩
           y' ℤ* (pos (succ h') ℤ* (pos (succ a') ℤ* pos (succ h)))  ≡⟨ ap (y' ℤ*_) (ℤ-mult-rearrangement''' (pos (succ h')) (pos (succ a')) (pos (succ h))) ⟩
           y' ℤ* (pos (succ a') ℤ* (pos (succ h') ℤ* pos (succ h)))  ≡⟨ ℤ*-assoc y' (pos (succ a')) (pos (succ h') ℤ* pos (succ h)) ⟩
           y' ℤ* pos (succ a') ℤ* (pos (succ h') ℤ* pos (succ h))    ≡⟨ ap (y' ℤ* pos (succ a') ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h') (succ h)) ⟩
           y' ℤ* pos (succ a') ℤ* pos (succ h' ℕ* succ h)            ≡⟨ ap (λ z → y' ℤ* pos (succ a') ℤ* pos z) (mult-commutativity (succ h') (succ h)) ⟩
           y' ℤ* pos (succ a') ℤ* pos (succ h ℕ* succ h') ∎

ℚ-no-max-element : (p : ℚ) → Σ q ꞉ ℚ , (p < q)
ℚ-no-max-element ((x , a) , α) = q , III
 where
  q : ℚ 
  q = toℚ ((succℤ x) , a)

  x' : ℤ
  x' = pr₁ (pr₁ q)
  a' : ℕ
  a' = pr₂ (pr₁ q)

  I : succℤ x ℤ* pos (succ a') ≡ x' ℤ* pos (succ a)
  I = ≈-toℚ ((succℤ x) , a)

  II : (x ℤ* pos (succ a')) ℤ< (succℤ x ℤ* pos (succ a'))
  II = positive-multiplication-preserves-order x (succℤ x) (pos (succ a')) (pos-succ-greater-than-zero a') (<-incrℤ x)

  III : x ℤ* pos (succ a') ℤ< (x' ℤ* pos (succ a))
  III = transport (x ℤ* pos (succ a') ℤ<_) I II

ℚ-no-least-element : (q : ℚ) → Σ p ꞉ ℚ , p < q
ℚ-no-least-element ((x , a) , α) = p , III
 where
  p : ℚ
  p = toℚ ((predℤ x) , a)

  x' : ℤ
  x' = pr₁ (pr₁ p)
  a' : ℕ
  a' = pr₂ (pr₁ p)

  I : predℤ x ℤ* pos (succ a') ≡ x' ℤ* pos (succ a)
  I = ≈-toℚ ((predℤ x) , a)

  II : (predℤ x ℤ* pos (succ a')) ℤ< (x ℤ* pos (succ a'))
  II = positive-multiplication-preserves-order (predℤ x) x (pos (succ a')) (pos-succ-greater-than-zero a') (<-predℤ x)

  III : x' ℤ* pos (succ a) ℤ< (x ℤ* pos (succ a'))
  III = transport (_ℤ< x ℤ* pos (succ a')) I II

ℚ-trichotomous-lemma : Fun-Ext → ((p , α) (q , β) : ℚ) → p ℚₙ≈ q → p , α ≡ q , β
ℚ-trichotomous-lemma fe (p , α) (q , β) e = to-subtype-≡ (λ - → is-in-lowest-terms-is-prop fe -) (equiv-with-lowest-terms-is-equal p q e α β)

ℚ-trichotomous : Fun-Ext → (p q : ℚ) → (p < q) ∔ (p ≡ q) ∔ (q < p)
ℚ-trichotomous fe ((x , a) , α) ((y , b) , β) = f (ℤ-trichotomous (x ℤ* pos (succ b)) (y ℤ* pos (succ a)))
 where
  f : (x ℤ* pos (succ b)) ℤ< (y ℤ* pos (succ a))
     ∔ (x ℤ* pos (succ b) ≡ y ℤ* pos (succ a))
     ∔ (y ℤ* pos (succ a)) ℤ< (x ℤ* pos (succ b))
    →  ((x , a) , α) < ((y , b) , β)
     ∔ ((x , a) , α ≡ (y , b) , β)
     ∔ ((y , b) , β) < ((x , a) , α)
  f (inl z)       = inl z
  f (inr (inl z)) = inr (inl (ℚ-trichotomous-lemma fe ((x , a) , α) ((y , b) , β) z))
  f (inr (inr z)) = inr (inr z)
{-
ℚ-dichotomous : Fun-Ext → (p q : ℚ) → (p ≤ q) ∔ (q < p)
ℚ-dichotomous fe p q = I (ℚ-trichotomous fe p q)
 where
  I : (p < q) ∔ (p ≡ q) ∔ (q < p) → (p ≤ q) ∔ (q < p)
  I (inl x)       = inl (inl x)
  I (inr (inl x)) = inl (inr (ℚ≡-to-ℚₙ≡ p q x))
  I (inr (inr x)) = inr x
-}
located-property : Fun-Ext → (p q x : ℚ) → p < q → (p < x) ∔ (x < q) 
located-property fe p q x l = f (ℚ-trichotomous fe x q)
 where
  f : (x < q) ∔ (x ≡ q) ∔ (q < x) → (p < x) ∔ (x < q) 
  f (inl z)       = inr z
  f (inr (inl z)) = inl (transport (p <_) (z ⁻¹) l)
  f (inr (inr z)) = inl (ℚ<-trans p q x l z)


open MoreNaturalProperties
open NaturalsAddition renaming (_+_ to _ℕ+_) --Type Topology

rounded-lemma₀ : (a : ℕ) → succ (2 ℕ* pred (succ a)) ≡ pred (2 ℕ* (succ a))
rounded-lemma₀ zero = refl
rounded-lemma₀ (succ a) = succ (2 ℕ* pred (succ (succ a))) ≡⟨ ap (λ - → succ (2 ℕ* -)) (pred-succ a) ⟩
                   succ (2 ℕ* succ a)                ≡⟨ pred-succ (2 ℕ* succ a) ⁻¹ ⟩
                   pred (succ (succ (2 ℕ* succ a)))  ≡⟨ refl ⟩
                   pred (2 ℕ* succ a ℕ+ 2)           ≡⟨ refl ⟩
                   pred (2 ℕ* (succ a) ℕ+ 2 ℕ* 1)    ≡⟨ ap pred (distributivity-mult-over-nat 2 (succ a) 1 ⁻¹) ⟩
                   pred (2 ℕ+ (2 ℕ* (succ a)))       ≡⟨ refl ⟩
                   pred (2 ℕ* succ (succ a)) ∎

rounded-lemma : (p q : ℚ) → p < q → Σ x ꞉ ℚ , (p < x) × (x < q)
rounded-lemma ((x , a) , α) ((y , b) , β) l = midpoint , firstly , secondly
 where
  midpoint : ℚ
  midpoint = toℚ (half-ℚₙ ((x , a) ℚₙ+ (y , b)))

  z : ℤ
  z = pr₁ (pr₁ midpoint)
  c : ℕ
  c = pr₂ (pr₁ midpoint)

  z' : ℤ
  z' = pr₁ (half-ℚₙ ((x , a) ℚₙ+ (y , b)))

  z'' : z' ≡ x ℤ* pos (succ b) ℤ+ y ℤ* pos (succ a)
  z'' = refl

  c' : ℕ
  c' = pr₂ (half-ℚₙ ((x , a) ℚₙ+ (y , b)))

  c'' : c' ≡ succ (2 ℕ* pred (succ a ℕ* succ b))
  c'' = refl

  I : (z' , c') ℚₙ≈ (z , c)
  I = ≈-toℚ (half-ℚₙ ((x , a) ℚₙ+ (y , b)))

  II : z' ℤ* pos (succ c) ≡ z ℤ* pos (succ c')
  II = I

  III : Σ k ꞉ ℕ , succ k ≡ succ a ℕ* succ b
  III = pos-mult-is-succ a b

  k : ℕ
  k = pr₁ III

  a' b' k' c''' : ℤ
  a' = pos (succ a)
  b' = pos (succ b)
  k' = pos (succ k)
  c''' = pos (succ c')
  
  IV : (x : ℤ) →  x ℤ* pos (succ (succ (2 ℕ* pred (succ a ℕ* succ b)))) ≡ x ℤ* a' ℤ* b' ℤ+ x ℤ* (a') ℤ* b'
  IV x = x ℤ* pos (succ (succ (2 ℕ* pred (succ a ℕ* succ b))))    ≡⟨ ap (λ - → x ℤ* pos (succ (succ (2 ℕ* pred -)))) ((pr₂ III) ⁻¹) ⟩
       x ℤ* pos (succ (succ (2 ℕ* pred (succ k))))                ≡⟨ ap (λ - → x ℤ* pos (succ -)) (rounded-lemma₀ k) ⟩
       x ℤ* pos (succ (pred (2 ℕ* succ k)))                       ≡⟨ ap (λ - → x ℤ* pos -) (succ-pred' (2 ℕ* succ k) λ w → ℕ-positive-multiplication-not-zero 1 k w) ⟩
       x ℤ* pos (2 ℕ* succ k)                                     ≡⟨ ap (λ - → x ℤ* pos -) (mult-commutativity 2 (succ k)) ⟩
       x ℤ* pos (succ k ℕ+ succ k)                                ≡⟨ ap (λ - → x ℤ* -) (pos-addition-equiv-to-ℕ (succ k) (succ k)  ⁻¹) ⟩
       x ℤ* (k' ℤ+ k')                                            ≡⟨ distributivity-mult-over-ℤ' (k') (k') x ⟩
       x ℤ* k' ℤ+ x ℤ* k'                                         ≡⟨ ap (λ - → x ℤ* pos - ℤ+ x ℤ* pos -) (pr₂ III) ⟩
       x ℤ* pos (succ a ℕ* succ b) ℤ+ x ℤ* pos (succ a ℕ* succ b) ≡⟨ ap (λ - → (x ℤ* -) ℤ+ (x ℤ* -)) (pos-multiplication-equiv-to-ℕ (succ a) (succ b) ⁻¹) ⟩
       x ℤ* (a' ℤ* b') ℤ+ x ℤ* (a' ℤ* b')                          ≡⟨ ap (λ - → - ℤ+ -) (ℤ*-assoc x (a') (b')) ⟩
       x ℤ* a' ℤ* b' ℤ+ x ℤ* a' ℤ* b' ∎

  V : (x ℤ* b' ℤ+ y ℤ* a') ℤ* a' ≡ x ℤ* a' ℤ* b' ℤ+ y ℤ* (a') ℤ* a'
  V = (x ℤ* b' ℤ+ y ℤ* a') ℤ* a' ≡⟨ distributivity-mult-over-ℤ (x ℤ* b') ( y ℤ* a') (a') ⟩
         x ℤ* b' ℤ* a' ℤ+ y ℤ* a' ℤ* a' ≡⟨ ap (λ - → - ℤ+ y ℤ* a' ℤ* a') (ℤ-mult-rearrangement x (b') (a'))  ⟩
         x ℤ* a' ℤ* b' ℤ+ y ℤ* a' ℤ* a' ∎

  VI : (x ℤ* a' ℤ* b' ℤ+ x ℤ* a' ℤ* b') ℤ< (x ℤ* a' ℤ* b' ℤ+ y ℤ* a' ℤ* a')
  VI = ℤ<-adding'' (x ℤ* a' ℤ* b') (y ℤ* a' ℤ* a') (x ℤ* a' ℤ* b') ii
   where
    i : (x ℤ* b' ℤ* a') ℤ< (y ℤ* a' ℤ* a')
    i = positive-multiplication-preserves-order (x ℤ* b') (y ℤ* a') (a') (pos-succ-greater-than-zero a) l

    ii : (x ℤ* a' ℤ* b') ℤ< (y ℤ* a' ℤ* a')
    ii = transport (_ℤ< y ℤ* a' ℤ* a') (ℤ-mult-rearrangement x (b') (a')) i

  VII : (x ℤ* pos (succ (succ (2 ℕ* pred (succ a ℕ* succ b))))) ℤ< ((x ℤ* b' ℤ+ y ℤ* a') ℤ* a')
  VII = transport₂ _ℤ<_ (IV x ⁻¹) (V ⁻¹) VI

  VIII : x ℤ* c''' ℤ< z' ℤ* a'
  VIII = VII

  IX : (x ℤ* c''' ℤ* pos (succ c)) ℤ< (z' ℤ* a' ℤ* pos (succ c)) 
  IX = positive-multiplication-preserves-order (x ℤ* c''') (z' ℤ* a') (pos (succ c)) (pos-succ-greater-than-zero c) VIII

  X : (x ℤ* pos (succ c) ℤ* c''') ℤ< (z ℤ* a' ℤ* c''')
  X = transport₂ _ℤ<_ i ii IX
   where
    i : x ℤ* c''' ℤ* pos (succ c) ≡ x ℤ* pos (succ c) ℤ* c'''
    i = ℤ-mult-rearrangement x (c''') (pos (succ c)) 

    ii : z' ℤ* a' ℤ* pos (succ c) ≡ z ℤ* a' ℤ* c'''
    ii = z' ℤ* a' ℤ* pos (succ c) ≡⟨ ℤ-mult-rearrangement z' (a') (pos (succ c)) ⟩
         z' ℤ* pos (succ c) ℤ* a' ≡⟨ ap (_ℤ* a') II ⟩
         z ℤ* c''' ℤ* a' ≡⟨ ℤ-mult-rearrangement z (c''') (a') ⟩
         z ℤ* a' ℤ* c''' ∎

  firstly : (x ℤ* pos (succ c)) ℤ< (z ℤ* a')
  firstly = ordering-right-cancellable (x ℤ* pos (succ c)) (z ℤ* a') (c''') (pos-succ-greater-than-zero c') X

  XI : x ℤ* b' ℤ* b' ℤ+ y ℤ* a' ℤ* b' ≡ (x ℤ* (b') ℤ+ y ℤ* a') ℤ* b'
  XI = x ℤ* b' ℤ* b' ℤ+ y ℤ* a' ℤ* b' ≡⟨ distributivity-mult-over-ℤ (x ℤ* b') ( y ℤ* a') (b') ⁻¹ ⟩
         (x ℤ* b' ℤ+ y ℤ* a') ℤ* b' ∎

  XII : y ℤ* a' ℤ* b' ℤ+ y ℤ* (a') ℤ* b' ≡ y ℤ* pos (succ (succ (2 ℕ* pred (succ a ℕ* (succ b)))))
  XII = IV y ⁻¹

  XIII : x ℤ* b' ℤ* b' ℤ+ y ℤ* a' ℤ* b' ℤ< y ℤ* a' ℤ* b' ℤ+ y ℤ* a' ℤ* b'
  XIII = ℤ<-adding' (x ℤ* b' ℤ* b') (y ℤ* a' ℤ* b') (y ℤ* a' ℤ* b') i
   where
    i : (x ℤ* b' ℤ* b') ℤ< (y ℤ* a' ℤ* b')
    i = positive-multiplication-preserves-order (x ℤ* b') (y ℤ* a') (b') (pos-succ-greater-than-zero b) l

  XIV : (z' ℤ* b') ℤ< (y ℤ* c''')
  XIV = transport₂ _ℤ<_ XI XII XIII

  XV : (z' ℤ* b' ℤ* pos (succ c)) ℤ< (y ℤ* c''' ℤ* pos (succ c))
  XV = positive-multiplication-preserves-order (z' ℤ* b') (y ℤ* c''') (pos (succ c)) (pos-succ-greater-than-zero c') XIV

  XVI : (z ℤ* b') ℤ* c''' ℤ< (y ℤ* pos (succ c)) ℤ* c'''
  XVI = transport₂ _ℤ<_ i ii XV
   where
    i : z' ℤ* b' ℤ* pos (succ c) ≡ z ℤ* b' ℤ* c'''
    i = z' ℤ* b' ℤ* pos (succ c) ≡⟨ ℤ-mult-rearrangement z' (b') (pos (succ c)) ⟩
        z' ℤ* pos (succ c) ℤ* b' ≡⟨ ap (_ℤ* b') II ⟩
        z ℤ* c''' ℤ* b' ≡⟨ ℤ-mult-rearrangement z (c''') (b') ⟩
        z ℤ* b' ℤ* c''' ∎

    ii : y ℤ* c''' ℤ* pos (succ c) ≡ y ℤ* pos (succ c) ℤ* c'''
    ii = ℤ-mult-rearrangement y (c''') (pos (succ c))

  secondly : (z ℤ* b') ℤ< (y ℤ* pos (succ c))
  secondly = ordering-right-cancellable (z ℤ* b') (y ℤ* pos (succ c)) (c''') (pos-succ-greater-than-zero c') XVI

ℚ-zero-not-one : Fun-Ext → ¬ (zero-ℚ ≡ 1ℚ)
ℚ-zero-not-one fe e = positive-not-zero 0 (pos-lc V ⁻¹)
 where
  I : ((pos 0 , 0) ℚₙ≈ (pos 1 , 0)) ⇔ toℚ (pos 0 , 0) ≡ toℚ (pos 1 , 0) 
  I = equiv-equality fe ((pos 0) , 0) ((pos 1) , 0)

  II : toℚ (pos 0 , 0) ≡ toℚ (pos 1 , 0) → (pos 0 , 0) ℚₙ≈ (pos 1 , 0)
  II = pr₂ I

  III : (pos 0 , 0) ℚₙ≈ (pos 1 , 0)
  III = II e

  IV : pos 0 ℤ* pos 1 ≡ pos 1 ℤ* pos 1
  IV = III

  V : pos 0 ≡ pos 1
  V = pos 0          ≡⟨ refl ⟩
      pos 0 ℤ* pos 1 ≡⟨ IV   ⟩
      pos 1 ℤ* pos 1 ≡⟨ refl ⟩
      pos 1          ∎

ℚ-zero-left-neutral : Fun-Ext → (q : ℚ) → zero-ℚ + q ≡ q
ℚ-zero-left-neutral fe q = II
 where
  I : Σ q' ꞉ ℚₙ , q ≡ toℚ q'
  I = q-has-qn fe q

  q' : ℚₙ
  q' = pr₁ I

  II : (zero-ℚ + q) ≡ q
  II = zero-ℚ + q               ≡⟨ refl ⟩
       toℚ ((pos 0 , 0) ℚₙ+ q') ≡⟨ ap toℚ (ℚₙ+-comm (pos 0 , 0) q') ⟩
       toℚ (q' ℚₙ+ (pos 0 , 0)) ≡⟨ ap toℚ (ℚₙ-zero-right-neutral q') ⟩
       toℚ q'                   ≡⟨ pr₂ I ⁻¹ ⟩
       q                        ∎

ℚ-zero-right-neutral : Fun-Ext → (q : ℚ) → q + zero-ℚ ≡ q
ℚ-zero-right-neutral fe q = ℚ+-comm q zero-ℚ ∙ (ℚ-zero-left-neutral fe q)

ℚ-mult-left-id : Fun-Ext → (q : ℚ) → 1ℚ * q ≡ q
ℚ-mult-left-id fe q = II
 where
  I : Σ q' ꞉ ℚₙ , q ≡ toℚ q'
  I = q-has-qn fe q 
  
  q' : ℚₙ
  q' = pr₁ I

  II : (1ℚ * q) ≡ q
  II = (1ℚ * q)                    ≡⟨ refl ⟩
        toℚ ((pos 1 , 0) ℚₙ* q')   ≡⟨ ap toℚ (ℚₙ-mult-left-id q') ⟩
        toℚ q'                     ≡⟨ pr₂ I ⁻¹ ⟩
        q ∎

ℚ-mult-right-id : Fun-Ext → (q : ℚ) → q * 1ℚ ≡ q
ℚ-mult-right-id fe q = ℚ*-comm q 1ℚ ∙ ℚ-mult-left-id fe q 

ℚ-distributivity : Fun-Ext → (p q r : ℚ) → p * (q + r) ≡ (p * q) + (p * r) 
ℚ-distributivity fe p q r = II
 where
  pnc : Σ p' ꞉ ℚₙ , p ≡ toℚ p'
  pnc = q-has-qn fe p

  qnc : Σ q' ꞉ ℚₙ , q ≡ toℚ q'
  qnc = q-has-qn fe q

  rnc : Σ r' ꞉ ℚₙ , r ≡ toℚ r'
  rnc = q-has-qn fe r

  p' q' r' : ℚₙ
  p' = pr₁ pnc
  q' = pr₁ qnc
  r' = pr₁ rnc

  I : (p' ℚₙ* (q' ℚₙ+ r')) ℚₙ≈ ((p' ℚₙ* q') ℚₙ+ (p' ℚₙ* r')) → toℚ (p' ℚₙ* (q' ℚₙ+ r')) ≡ toℚ ((p' ℚₙ* q') ℚₙ+ (p' ℚₙ* r')) 
  I = lr-implication (equiv-equality fe (p' ℚₙ* (q' ℚₙ+ r')) ((p' ℚₙ* q') ℚₙ+ (p' ℚₙ* r')))

  II : p * (q + r) ≡ (p * q) + (p * r)
  II = p * (q + r)                             ≡⟨ refl ⟩
       p * toℚ (q' ℚₙ+ r')                     ≡⟨ ap (λ - → - * toℚ (q' ℚₙ+ r')) (pr₂ pnc) ⟩
       toℚ p' * toℚ (q' ℚₙ+ r')                ≡⟨ toℚ-over-mult fe p' (q' ℚₙ+ r') ⁻¹ ⟩
       toℚ (p' ℚₙ* (q' ℚₙ+ r'))                ≡⟨ I (ℚ-dist-lemma p' q' r') ⟩
       toℚ ((p' ℚₙ* q') ℚₙ+ (p' ℚₙ* r'))       ≡⟨ toℚ-over-addition fe (p' ℚₙ* q') (p' ℚₙ* r') ⟩
       toℚ (p' ℚₙ* q') + toℚ (p' ℚₙ* r')       ≡⟨ refl ⟩
       (p * q) + (p * r)  ∎

ℚₙ- : ℚₙ → ℚₙ
ℚₙ- (x , a) = ℤ- x , a

-_ : ℚ → ℚ
- ((x , a) , p) = toℚ (ℚₙ- (x , a))

toℚ-over-minus : Fun-Ext → ((x , a) : ℚₙ) → (- toℚ (x , a)) ≡ toℚ (ℤ- x , a) 
toℚ-over-minus fe (x , a) = IV
 where
  p : ℚ
  p = toℚ (x , a)

  x' : ℤ
  x' = pr₁ (pr₁ p)
  a' : ℕ
  a' = pr₂ (pr₁ p)

  helper : (ℤ- x' , a') ℚₙ≈ (ℤ- x , a) → toℚ (ℤ- x' , a') ≡ toℚ (ℤ- x , a)
  helper = pr₁ (equiv-equality fe (ℤ- x' , a') (ℤ- x , a))

  I : (x , a) ℚₙ≈ (x' , a')
  I = ≈-toℚ (x , a)

  II : (x' , a') ℚₙ≈ (x , a)
  II = ≈-sym (x , a) (x' , a') I

  III : x' ℤ* pos (succ a) ≡ x ℤ* pos (succ a') → (ℤ- x' , a') ℚₙ≈ (ℤ- x , a)
  III e = (ℤ- x') ℤ* pos (succ a)   ≡⟨ subtraction-dist-over-mult' x' (pos (succ a)) ⟩
          ℤ- (x' ℤ* pos (succ a))   ≡⟨ ap ℤ-_ e ⟩
          ℤ- (x ℤ* pos (succ a'))   ≡⟨ subtraction-dist-over-mult' x (pos (succ a')) ⁻¹ ⟩
          (ℤ- x) ℤ* pos (succ a') ∎

  IV : (- toℚ (x , a)) ≡ toℚ (ℤ- x , a) 
  IV = (- toℚ (x , a))       ≡⟨ refl ⟩
        (- p)                ≡⟨ refl ⟩
        toℚ (ℤ- x' , a')     ≡⟨ helper (III II) ⟩
        toℚ (ℤ- x , a)  ∎ 

ℚ-minus-dist : Fun-Ext → (p q : ℚ) → (- p) + (- q) ≡ - (p + q)
ℚ-minus-dist fe ((x , a) , p) ((y , b) , q) = II
 where
  pnc : Σ p' ꞉ ℚₙ , ((x , a) , p) ≡ toℚ p'
  pnc = q-has-qn fe ((x , a) , p)

  qnc : Σ q' ꞉ ℚₙ , ((y , b) , q) ≡ toℚ q'
  qnc = q-has-qn fe ((y , b) , q)

  p' q' : ℚₙ
  p' = pr₁ pnc
  q' = pr₁ qnc

  x' y' : ℤ
  x' = pr₁ p'
  y' = pr₁ q'

  a' b' : ℕ
  a' = pr₂ p'
  b' = pr₂ q'

  pqnc : Σ pq ꞉ ℚₙ , (toℚ (p' ℚₙ+ q')) ≡ toℚ pq
  pqnc = q-has-qn fe (toℚ (p' ℚₙ+ q'))

  pq : ℚₙ
  pq = pr₁ pqnc

  z : ℤ
  z = pr₁ pq

  c : ℕ
  c = pr₂ pq

  I : ((ℤ- x , a) ℚₙ+ (ℤ- y , b)) ℚₙ≈ (((ℤ- x') , a') ℚₙ+ ((ℤ- y') , b')) → toℚ ((ℤ- x , a) ℚₙ+ (ℤ- y , b)) ≡ toℚ (((ℤ- x') , a') ℚₙ+ ((ℤ- y') , b')) 
  I = lr-implication (equiv-equality fe ((ℤ- x , a) ℚₙ+ (ℤ- y , b)) (((ℤ- x') , a') ℚₙ+ ((ℤ- y') , b')))

  II : (- ((x , a) , p)) + (- ((y , b) , q)) ≡ - (((x , a) , p) + ((y , b) , q))
  II = ((- ((x , a) , p)) + (- ((y , b) , q)))                                                      ≡⟨ refl ⟩
       (toℚ ((ℤ- x) , a) + toℚ ((ℤ- y) , b))                                                        ≡⟨ toℚ-over-addition fe (ℤ- x , a) (ℤ- y , b) ⁻¹  ⟩
       toℚ ((ℤ- x , a) ℚₙ+ (ℤ- y , b))                                                              ≡⟨ I refl ⟩
       toℚ (((ℤ- x') , a') ℚₙ+ ((ℤ- y') , b'))                                                      ≡⟨ ap₂ (λ α β → toℚ (α ℤ+ β ,  pred (succ a' ℕ* succ b'))) (subtraction-dist-over-mult' x' (pos (succ b'))) (subtraction-dist-over-mult' y' (pos (succ a'))) ⟩
       toℚ (((ℤ- x' ℤ* pos (succ b')) ℤ+ (ℤ- y' ℤ* pos (succ a'))) , ( pred (succ a' ℕ* succ b'))) ≡⟨ ap (λ - → toℚ (- , pred (succ a' ℕ* succ b'))) (subtraction-dist (x' ℤ* pos (succ b')) (y' ℤ* pos (succ a'))) ⟩
       toℚ ((ℤ- x' ℤ* pos (succ b') ℤ+ y' ℤ* pos (succ a')) , ( pred (succ a' ℕ* succ b')))        ≡⟨ toℚ-over-minus fe ((x' ℤ* pos (succ b') ℤ+ y' ℤ* pos (succ a') , pred (succ a' ℕ* succ b'))) ⁻¹ ⟩
       (- toℚ (x' ℤ* pos (succ b') ℤ+ y' ℤ* pos (succ a') , pred (succ a' ℕ* succ b')))            ≡⟨ refl ⟩
       (- toℚ (p' ℚₙ+ q'))                                                                          ≡⟨ refl ⟩
       (- (((x , a) , p) + ((y , b) , q))) ∎

ℚ-minus-zero-is-zero : zero-ℚ ≡ - zero-ℚ 
ℚ-minus-zero-is-zero = refl

ℚ+-inverse-lemma : ((x , a) : ℚₙ) → ((ℤ- x , a) ℚₙ+ (x , a)) ℚₙ≈ (pos zero , zero)
ℚ+-inverse-lemma (x , a) = I
 where
  I : ((ℤ- x , a) ℚₙ+ (x , a)) ℚₙ≈ (pos zero , zero)
  I = ((ℤ- x) ℤ* pos (succ a) ℤ+ (x ℤ* pos (succ a))) ℤ* pos 1 ≡⟨ ℤ-mult-right-id ((ℤ- x) ℤ* pos (succ a) ℤ+ (x ℤ* pos (succ a))) ⟩
      ((ℤ- x) ℤ* pos (succ a) ℤ+ (x ℤ* pos (succ a)))          ≡⟨ distributivity-mult-over-ℤ (ℤ- x) x (pos (succ a)) ⁻¹ ⟩
      ((ℤ- x) ℤ+ x) ℤ* pos (succ a)                            ≡⟨ ap (λ - → - ℤ* pos (succ a)) (ℤ+-comm (ℤ- x) x)  ⟩
      (x ℤ+ (ℤ- x)) ℤ* pos (succ a)                            ≡⟨ ap (λ - → - ℤ* pos (succ a)) (ℤ-sum-of-inverse-is-zero x) ⟩
      pos 0 ℤ* pos (succ a)                                    ≡⟨ ℤ-zero-left-is-zero (pos (succ a)) ⟩
      pos 0                                                    ≡⟨ ℤ-zero-left-is-zero (pos (succ (pred (succ a ℕ* succ a)))) ⁻¹  ⟩
      pos zero ℤ* pos (succ (pred (succ a ℕ* succ a)))     ∎

ℚ-inverse-sum-to-zero : Fun-Ext → (q : ℚ) → q + (- q) ≡ zero-ℚ
ℚ-inverse-sum-to-zero fe ((x , a) , p) = γ
 where
  -qnc : Σ (x' , y') ꞉ ℚₙ , toℚ (ℤ- x , a) ≡ toℚ (x' , y') 
  -qnc = q-has-qn fe (toℚ (ℤ- x , a))

  x' : ℤ
  x' = pr₁ (pr₁ -qnc)

  y' : ℕ
  y' = pr₂ (pr₁ -qnc)

  I : ((x , a) ℚₙ+ (x' , y')) ℚₙ≈ (pos zero , zero) → toℚ ((x , a) ℚₙ+ (x' , y')) ≡ toℚ ((pos zero , zero))
  I = lr-implication (equiv-equality fe ((x , a) ℚₙ+ (x' , y')) (pos zero , zero))

  II : (x , a) ℚₙ+ (x' , y') ℚₙ≈ ((x' , y') ℚₙ+ (x , a))
  II = ≈-addition-comm (x , a) (x' , y')

  IIIᵢ : (x' , y') ℚₙ≈ (ℤ- x , a)
  IIIᵢ = ≈-sym (ℤ- x , a) (x' , y') (rl-implication (equiv-equality fe (ℤ- x , a) (x' , y')) (pr₂ -qnc))

  III : ((x' , y') ℚₙ+ (x , a)) ℚₙ≈ ((ℤ- x , a) ℚₙ+ (x , a))
  III = ≈-addition (x' , y') (ℤ- x , a) (x , a) IIIᵢ

  IVᵢ : (x , a) ℚₙ+ (x' , y') ℚₙ≈ ((ℤ- x , a) ℚₙ+ (x , a))
  IVᵢ = ≈-trans ((x , a) ℚₙ+ (x' , y')) ((x' , y') ℚₙ+ (x , a)) ((ℤ- x , a) ℚₙ+ (x , a)) II III

  IV : ((ℤ- x , a) ℚₙ+ (x , a)) ℚₙ≈ (pos zero , zero)
  IV = ℚ+-inverse-lemma (x , a)

  V : ((x , a) ℚₙ+ (x' , y')) ℚₙ≈ (pos zero , zero)
  V = ≈-trans ((x , a) ℚₙ+ (x' , y')) ((ℤ- x , a) ℚₙ+ (x , a)) ((pos zero , zero)) IVᵢ IV

  γ : (((x , a) , p) + (- ((x , a) , p))) ≡ zero-ℚ
  γ = (((x , a) , p) + (- ((x , a) , p)))     ≡⟨ refl ⟩
      (((x , a) , p) + toℚ (ℤ- x , a))        ≡⟨ refl ⟩
      toℚ ((x , a) ℚₙ+ (x' , y'))             ≡⟨ I V ⟩
      toℚ (pos zero , zero)                   ≡⟨ refl ⟩
      zero-ℚ ∎

ℚ-inverse-sum-to-zero' : Fun-Ext → (q : ℚ) → (- q) + q ≡ zero-ℚ
ℚ-inverse-sum-to-zero' fe q = ℚ+-comm (- q) q ∙ ℚ-inverse-sum-to-zero fe q

ℚ+-inverse : Fun-Ext → (q : ℚ) → Σ q' ꞉ ℚ , q + q' ≡ zero-ℚ
ℚ+-inverse fe q = (- q) , (ℚ-inverse-sum-to-zero fe q)

ℚ+-inverse' : Fun-Ext → (q : ℚ) → Σ q' ꞉ ℚ , q' + q ≡ zero-ℚ
ℚ+-inverse' fe q = f (ℚ+-inverse fe q)
  where
   f : Σ q' ꞉ ℚ , q + q' ≡ zero-ℚ → Σ q' ꞉ ℚ , q' + q ≡ zero-ℚ
   f (q' , e) = q' , (ℚ+-comm q' q ∙ e)

open NaturalsDivision

numerator-zero-is-zero : Fun-Ext → (((x , a) , p) : ℚ) → x ≡ pos zero → ((x , a) , p) ≡ zero-ℚ
numerator-zero-is-zero fe ((negsucc x    , a) , p) e = 𝟘-elim (neg-not-positive e)
numerator-zero-is-zero fe ((pos zero , a) , icd , f) e = to-subtype-≡ (is-in-lowest-terms-is-prop fe) I
 where
  I : pos zero , a ≡ pos zero , 0
  I = ap₂ _,_ refl (succ-lc II)
   where    
    II : succ a ≡ 1
    II = ∣-anti (succ a) 1 (f (succ a) ((0 , refl) , 1 , refl)) (pr₂ icd)
numerator-zero-is-zero fe ((pos (succ x) , a) , p) e = 𝟘-elim (positive-not-zero x (pos-lc e))

--Maybe consider implementation of division and it's properties
multiplicative-inverse : Fun-Ext → (q : ℚ) → ¬ (q ≡ zero-ℚ) → ℚ 
multiplicative-inverse fe ((pos zero     , a) , p) nz = 𝟘-elim (nz (numerator-zero-is-zero fe (((pos zero , a) , p)) refl))
multiplicative-inverse fe ((pos (succ x) , a) , p) nz = toℚ ((pos (succ a)) , x)
multiplicative-inverse fe ((negsucc x    , a) , p) nz = toℚ ((negsucc  a) , x)

ℚ*-inverse-lemma₀ : Fun-Ext → ((x , a) : ℚₙ) → x ≡ pos (succ a) → toℚ (x , a) ≡ 1ℚ
ℚ*-inverse-lemma₀ fe (negsucc x    , a) e = 𝟘-elim (neg-not-positive e)
ℚ*-inverse-lemma₀ fe (pos 0        , a) e = 𝟘-elim (zero-not-positive a (pos-lc e))
ℚ*-inverse-lemma₀ fe (pos (succ x) , a) e = I II
 where
  I : (pos (succ x) , a) ℚₙ≈ (pos 1 , 0) → toℚ (pos (succ x) , a) ≡ toℚ (pos 1 , 0)
  I = lr-implication (equiv-equality fe (pos (succ x) , a) (pos (succ 0) , 0))

  II : (pos (succ x) , a) ℚₙ≈ (pos 1 , 0)
  II = pos (succ x) ≡⟨ e ⟩
       pos (succ a) ≡⟨ ℤ-mult-left-id (pos (succ a)) ⁻¹ ⟩
       pos 1 ℤ* pos (succ a) ∎

ℚ*-inverse-lemma₁ : Fun-Ext → (((x , a) , p) : ℚ) → ((x , a) , p) ≡ toℚ (x , a)
ℚ*-inverse-lemma₁ fe ((x , a) , p) = II
 where
  I : (x , a) ℚₙ≈ toℚₙ (toℚ (x , a))
  I = ≈-toℚ (x , a)

  II : ((x , a) , p) ≡ toℚ (x , a)
  II = to-subtype-≡ (is-in-lowest-terms-is-prop fe) (equiv-with-lowest-terms-is-equal (x , a) (pr₁ (toℚ (x , a))) I p (pr₂ (toℚ (x , a))))

ℚ*-inverse-product-is-one : (fe : Fun-Ext) → (q : ℚ) → (nz : ¬ (q ≡ zero-ℚ)) → q * multiplicative-inverse fe q nz ≡ 1ℚ
ℚ*-inverse-product-is-one fe ((pos zero     , a) , p) nz = 𝟘-elim (nz (numerator-zero-is-zero fe ((pos zero , a) , p) refl))
ℚ*-inverse-product-is-one fe ((pos (succ x) , a) , p) nz = γ
 where
  ψ : pos (succ x) ℤ* pos (succ a) ≡ pos (succ (pred (succ a ℕ* succ x)))
  ψ = pos (succ x) ℤ* pos (succ a) ≡⟨ ℤ*-comm (pos (succ x)) (pos (succ a)) ⟩
      pos (succ a) ℤ* pos (succ x) ≡⟨ denom-setup a x ⁻¹ ⟩
      pos (succ (pred (succ a ℕ* succ x))) ∎

  γ : ((pos (succ x) , a) , p) * toℚ ((pos (succ a)) , x) ≡ 1ℚ
  γ = ((pos (succ x) , a) , p) * toℚ ((pos (succ a)) , x)    ≡⟨ ap (_* toℚ (pos (succ a) , x)) (ℚ*-inverse-lemma₁ fe ((pos (succ x) , a) , p)) ⟩
      toℚ (pos (succ x) , a) * toℚ (pos (succ a) , x)        ≡⟨ toℚ-over-mult fe (pos (succ x) , a) (pos (succ a) , x) ⁻¹ ⟩
      toℚ ((pos (succ x) , a) ℚₙ* (pos (succ a) , x))        ≡⟨ refl ⟩
      toℚ ((pos (succ x) ℤ* pos (succ a)) , (pred (succ a ℕ* succ x))) ≡⟨ ℚ*-inverse-lemma₀ fe ((pos (succ x) ℤ* pos (succ a)) , (pred (succ a ℕ* succ x))) ψ ⟩
      toℚ (pos 1 , 0)                                        ≡⟨ refl ⟩
      1ℚ                                                     ∎
ℚ*-inverse-product-is-one fe ((negsucc x    , a) , p) nz = γ
 where
  ψ : negsucc x ℤ* negsucc a ≡ pos (succ (pred (succ a ℕ* succ x)))
  ψ = negsucc x ℤ* negsucc a       ≡⟨ minus-times-minus-is-positive (pos (succ x)) (pos (succ a)) ⟩
      pos (succ x) ℤ* pos (succ a) ≡⟨ ℤ*-comm (pos (succ x)) (pos (succ a)) ⟩
      pos (succ a) ℤ* pos (succ x) ≡⟨ denom-setup a x ⁻¹ ⟩
      pos (succ (pred (succ a ℕ* succ x))) ∎
 
  γ : (((negsucc x , a) , p) * toℚ ((negsucc  a) , x)) ≡ 1ℚ
  γ = ((negsucc x , a) , p) * toℚ (negsucc a , x) ≡⟨  ap (_* toℚ (negsucc a , x)) (ℚ*-inverse-lemma₁ fe ((negsucc x , a) , p)) ⟩
      (toℚ (negsucc x , a) * toℚ (negsucc a , x)) ≡⟨ toℚ-over-mult fe (negsucc x , a) (negsucc a , x) ⁻¹ ⟩
      toℚ ((negsucc x , a) ℚₙ* (negsucc a , x))   ≡⟨ ℚ*-inverse-lemma₀ fe (negsucc x ℤ* negsucc a , pred (succ a ℕ* succ x)) ψ ⟩
      1ℚ ∎

ℚ*-inverse : Fun-Ext → (q : ℚ) → ¬ (q ≡ zero-ℚ) → Σ q' ꞉ ℚ , q * q' ≡ 1ℚ
ℚ*-inverse fe q nz = (multiplicative-inverse fe q nz) , ℚ*-inverse-product-is-one fe q nz

open Groups --TypeTopology

ℚ+-is-group : Fun-Ext → Group-structure ℚ
ℚ+-is-group fe = _+_ , (ℚ-is-set fe , (ℚ+-assoc fe) , (zero-ℚ , ℚ-zero-left-neutral fe , ℚ-zero-right-neutral fe , λ x → - x , ((ℚ+-comm (- x) x ∙ ℚ-inverse-sum-to-zero fe x) , ℚ-inverse-sum-to-zero fe x)))

ℚ*-is-group : Fun-Ext → ((q : ℚ) → ¬ (q ≡ zero-ℚ)) → Group-structure ℚ
ℚ*-is-group fe nz = _*_ , (ℚ-is-set fe) , (ℚ*-assoc fe) , (1ℚ , ℚ-mult-left-id fe , ℚ-mult-right-id fe , λ x → (multiplicative-inverse fe x (nz x)) , ((ℚ*-comm (multiplicative-inverse fe x (nz x)) x ∙  ℚ*-inverse-product-is-one fe x (nz x)) , ℚ*-inverse-product-is-one fe x (nz x)))

open FieldAxioms

ℚ-is-field : Fun-Ext → Field-structure ℚ
ℚ-is-field fe = (_+_ , _*_) , ℚ-is-set fe
                            , ℚ+-assoc fe
                            , ℚ*-assoc fe
                            , ℚ+-comm
                            , ℚ*-comm
                            , ℚ-distributivity fe
                            , (zero-ℚ , 1ℚ) , ℚ-zero-not-one fe
                                            , ℚ-zero-left-neutral fe
                                            , ℚ+-inverse fe
                                            , ℚ-mult-left-id fe
                                            , ℚ*-inverse fe

ℚ-addition-preserves-order : (p q r : ℚ) → p < q → (p + r) < (q + r)
ℚ-addition-preserves-order ((x , a) , p) ((y , b) , q) ((z , c) , r) (n , g , e) = <-lemma ((x , a) ℚₙ+ (z , c)) ((y , b) ℚₙ+ (z , c)) (ℚₙ-addition-preserves-order (x , a) (y , b) (z , c) (n , g , e))

ℚ-pos-multiplication-preserves-order : (p q : ℚ) → zero-ℚ < p → zero-ℚ < q → zero-ℚ < (p * q)
ℚ-pos-multiplication-preserves-order ((x , a) , p) ((y , b) , q) (n₁ , g₁ , l₁) (n₂ , g₂ , l₂) = <-lemma (pos 0 , 0) ((x , a) ℚₙ* (y , b)) (ℚₙ-pos-multiplication-preserves-order (x , a) (y , b) ((n₁ , g₁ , l₁)) ((n₂ , g₂ , l₂)))

ℚ-is-ordered-field : (fe : Fun-Ext) → Ordered-field-structure ℚ (ℚ-is-field fe)
ℚ-is-ordered-field fe = _<_ , ℚ-addition-preserves-order , ℚ-pos-multiplication-preserves-order

ℚ<-adding : (p q r s : ℚ) → p < q → r < s → (p + r) < (q + s)
ℚ<-adding p q r s l₁ l₂ = ℚ<-trans (p + r) (q + r) (q + s) I III
 where
  I : (p + r) < (q + r)
  I = ℚ-addition-preserves-order p q r l₁ 

  II : (r + q) < (s + q)
  II = ℚ-addition-preserves-order r s q l₂

  III : (q + r) < (q + s)
  III = transport₂ _<_ (ℚ+-comm r q) (ℚ+-comm s q) II

ℚ<-adding-zero : (p q : ℚ) → zero-ℚ < p → zero-ℚ < q → zero-ℚ < (p + q)
ℚ<-adding-zero p q l₁ l₂ = ℚ<-adding zero-ℚ p zero-ℚ q l₁ l₂

ℚ<-not-itself : (p : ℚ) → ¬ (p < p)
ℚ<-not-itself ((x , a) , p) (negsucc k , gtz , e) = 𝟘-elim gtz
ℚ<-not-itself ((x , a) , p) (pos 0 , gtz , e) = 𝟘-elim gtz
ℚ<-not-itself ((x , a) , p) (pos (succ k) , gtz , e) = 𝟘-elim (zero-not-positive k (pos-lc II ⁻¹))
 where
  I : x ℤ* pos (succ a) ℤ+ pos (succ k) ≡ x ℤ* pos (succ a) ℤ+ pos 0
  I = e
  II : pos (succ k) ≡ pos 0
  II = ℤ+-lc (pos (succ k)) (pos 0) (x ℤ* pos (succ a)) e

ℚ<-subtraction : Fun-Ext → (r p q : ℚ) → p < q → (r + (p + (- q))) < r
ℚ<-subtraction fe r p q l = transport ((r + (p + (- q))) <_) (ℚ-zero-right-neutral fe r) IV
 where
  I : (r + p) < (r + q)
  I = transport₂ _<_ (ℚ+-comm p r) (ℚ+-comm q r) (ℚ-addition-preserves-order p q r l)

  II : ((r + p) + (- q)) < ((r + q) + (- q))
  II = ℚ-addition-preserves-order (r + p) (r + q) (- q) I

  III : (r + (p + (- q))) < (r + (q + (- q)))
  III = transport₂ _<_ (ℚ+-assoc fe r p (- q)) (ℚ+-assoc fe r q (- q)) II

  IV : (r + (p + (- q))) < (r + zero-ℚ)
  IV = transport (λ α → (r + (p + (- q))) < (r + α)) (ℚ-inverse-sum-to-zero fe q) III

ℚ<-subtraction' : Fun-Ext → (r p q : ℚ) → p < q → r < (r + (q + (- p)))
ℚ<-subtraction' fe r p q l = transport (_< (r + (q + (- p)))) (ℚ-zero-right-neutral fe r) IV
 where
  I : (r + p) < (r + q)
  I = transport₂ _<_ (ℚ+-comm p r) (ℚ+-comm q r) (ℚ-addition-preserves-order p q r l)

  II : ((r + p) + (- p)) < ((r + q) + (- p))
  II = ℚ-addition-preserves-order (r + p) (r + q) (- p) I

  III : (r + (p + (- p))) < (r + (q + (- p)))
  III = transport₂ _<_ (ℚ+-assoc fe r p (- p)) (ℚ+-assoc fe r q (- p)) II

  IV : (r + zero-ℚ) < (r + (q + (- p)))
  IV = transport (λ α → (r + α) < (r + (q + (- p)))) (ℚ-inverse-sum-to-zero fe p) III

ℚ<-subtraction'' : Fun-Ext → (p q : ℚ) → (p < q) → Σ k ꞉ ℚ , (zero-ℚ < k) × (k ≡ (q + (- p)))
ℚ<-subtraction'' fe p q l = k , I
 where
  k : ℚ
  k = q + (- p)

  I : zero-ℚ < k × (k ≡ q + (- p))
  I = II , refl
   where
    II : zero-ℚ < k
    II = transport (zero-ℚ <_) III (ℚ<-subtraction' fe zero-ℚ p q l)
     where
      III : (zero-ℚ + (q + (- p))) ≡ (q + (- p))
      III = (zero-ℚ + (q + (- p))) ≡⟨ ℚ-zero-left-neutral fe (q + (- p)) ⟩
            (q + (- p))            ≡⟨ refl ⟩
            k                      ∎

ℚ<-subtraction''' : Fun-Ext → (p q : ℚ) → (p < q) → zero-ℚ < (q + (- p))
ℚ<-subtraction''' fe p q l = transport (zero-ℚ <_) ii i
 where
  I : Σ k ꞉ ℚ , (zero-ℚ < k) × (k ≡ (q + (- p)))
  I = ℚ<-subtraction'' fe p q l
  k : ℚ
  k = pr₁ I
  i : zero-ℚ < k
  i = pr₁ (pr₂ I)
  ii : k ≡ (q + (- p))
  ii = pr₂ (pr₂ I)
  
ℚ-minus-minus : Fun-Ext → (p : ℚ) → p ≡ (- (- p))
ℚ-minus-minus fe p = IV
 where
  p-constructed : Σ (x , a) ꞉ ℚₙ , p ≡ toℚ (x , a)
  p-constructed = q-has-qn fe p

  x = pr₁ (pr₁ p-constructed)
  a = pr₂ (pr₁ p-constructed)

  I : (- toℚ (x , a)) ≡ toℚ (ℤ- x , a)
  I = toℚ-over-minus fe (x , a)

  II : - toℚ (ℤ- x , a) ≡ toℚ ((ℤ- (ℤ- x)) , a)
  II = toℚ-over-minus fe (ℤ- x , a)

  III : toℚ ((ℤ- (ℤ- x)) , a) ≡ toℚ (x , a)
  III = ap (λ k → toℚ (k , a)) (minus-minus-is-plus x)

  IV : p ≡ (- (- p))
  IV = p                     ≡⟨ pr₂ p-constructed ⟩
       toℚ (x , a)           ≡⟨ III ⁻¹ ⟩
       toℚ (ℤ- (ℤ- x) , a)   ≡⟨ II ⁻¹ ⟩
       (- toℚ (ℤ- x , a))    ≡⟨ ap -_ (I ⁻¹) ⟩
       (- (- toℚ (x , a)))   ≡⟨ ap (λ k → - (- k)) (pr₂ p-constructed ⁻¹) ⟩
       (- (- p)) ∎

ℚ-zero-less-than-positive : (x y : ℕ) → zero-ℚ < toℚ ((pos (succ x)) , y)
ℚ-zero-less-than-positive x y = <-lemma (pos 0 , 0) (pos (succ x) , y) ((pos (succ x)) , (⋆ , I))
 where
  I : pos 0 ℤ* pos (succ y) ℤ+ pos (succ x) ≡ pos (succ x) ℤ* pos 1
  I = pos 0 ℤ* pos (succ y) ℤ+ pos (succ x) ≡⟨ ap (_ℤ+ (pos (succ x))) (ℤ-zero-left-is-zero (pos (succ y))) ⟩
      pos 0 ℤ+ pos (succ x)                 ≡⟨ ℤ-zero-left-neutral (pos (succ x)) ⟩
      pos (succ x)                          ≡⟨ ℤ-mult-right-id (pos (succ x)) ⟩
      pos (succ x) ℤ* pos 1 ∎



{- 
lim : (f : ℕ → ℚ) → 𝓤₀ ̇ 
lim f = ∀ (ε : ℕ) → (n : ℕ) →  Σ N ꞉ ℕ , ((N ℕ< n) → f n ℚ< toℚ (pos ε , zero))

conv : (f : ℕ → ℚ) → 𝓤₀ ̇
conv f = ∀ (ε : ℚ) → zero-ℚ ℚ< ε → (n : ℕ) → Σ N ꞉ ℕ , ((N ℕ< n) → f n ℚ< ε)

sandwich' : (f g : ℕ → ℚ) → (Σ M ꞉ ℕ , ((m : ℕ) → (M ℕ< m) → (f m ℚ< g m))) → conv g → conv f
sandwich' f g (n' , h) conv-g = I
 where
  I : conv f
  I ε l n = II (conv-g ε l n) 
   where
    II : (Σ N ꞉ ℕ , (N ℕ< n → g n ℚ< ε)) → Σ N ꞉ ℕ , (N ℕ< n → f n ℚ< ε)
    II (N , α) = N , III
     where
      III : _ ℕ< n → f n ℚ< ε
      III l₂ = ℚ<-trans (f n) (g n) ε (h n {!!}) (α l₂)

sandwich : (f g : ℕ → ℚ) → ((n : ℕ) → f n ℚ< g n) → lim g → lim f 
sandwich f g h g-holds = I
 where
  I : ∀ (ε : ℕ) → (n : ℕ) →  Σ N ꞉ ℕ , ((N ℕ< n) → f n ℚ< toℚ (pos ε , zero))
  I ε n = II (g-holds ε n)
   where
    II : Σ N ꞉ ℕ , (N ℕ< n → g n ℚ< toℚ (pos ε , zero)) → Σ N ꞉ ℕ , ((N ℕ< n) → f n ℚ< toℚ (pos ε , zero))
    II (N , l₂) = N , III
     where
      III : N ℕ< n → f n ℚ< toℚ (pos ε , zero)
      III l = ℚ<-trans (f n) (g n) (toℚ (pos ε , zero)) (h n) (l₂ l)

1/n : ℕ → ℚ
1/n zero = toℚ (pos 2 , 0)
1/n (succ n) = toℚ (pos 1 , n)

two-thirds-goes-down : lim ⟨2/3⟩^_
two-thirds-goes-down = sandwich (⟨2/3⟩^_) 1/n I II
 where
  I : (n : ℕ) → (⟨2/3⟩^ n) ℚ< 1/n n
  I = induction base step
   where
    base : (⟨2/3⟩^ 0) ℚ< 1/n 0
    base = (pos 1) , (⋆ , refl)

    step : (k : ℕ) → (⟨2/3⟩^ k) ℚ< 1/n k → (⟨2/3⟩^ succ k) ℚ< 1/n (succ k)
    step zero IH     = (pos 1) , (⋆ , refl)
    step (succ k) IH = {!!}
  II : lim 1/n
  II = λ ε n → {!!} , {!!}
-}




{-
ℚ-lim : (a : (ℕ → ℚ)) → {!!}
ℚ-lim = {!!}
-}

-- approximate-half : Σ h ꞉ ℚ , (zero-ℚ < (h + h)) × ((h + h) < 1ℚ)
-- approximate-half = {!!}

{-
ℚ<-to-+ : (p q r : ℚ) → (p + q) < r → Σ (p' , q') ꞉ ℚ × ℚ , p' + q' ≡ r
ℚ<-to-+ p q r = {!!}
-}
{-

ℚ-half : Fun-Ext → (p : ℚ) → Σ p' ꞉ ℚ , ((p' < p) × (p' + p' ≡ p))
ℚ-half fe ((x , a) , p) = (toℚ (x , (pred (2 ℕ* succ a)))) , (I , II)
 where
  I : toℚ (x , pred (2 ℕ* succ a)) < ((x , a) , p)
  I = {!!}

  II : (toℚ (x , pred (2 ℕ* succ a)) + toℚ (x , pred (2 ℕ* succ a))) ≡ (x , a) , p
  II = (toℚ (x , pred (2 ℕ* succ a)) + toℚ (x , pred (2 ℕ* succ a))) ≡⟨ toℚ-over-addition fe (x , pred (2 ℕ* succ a)) (x , pred (2 ℕ* succ a)) ⁻¹ ⟩
       toℚ ((x , pred (2 ℕ* succ a)) ℚₙ+ (x , pred (2 ℕ* succ a)))   ≡⟨ {!!} ⟩
       {!!}                                                              ≡⟨ {!!} ⟩
       (x , a) , p ∎
-}

\end{code}
