Andrew Sneap

\begin{code}
{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆)  -- TypeTopology

open import UF-FunExt -- TypeTopology
open import UF-Base hiding (_≈_) -- TypeTopology
open import UF-Subsingletons -- TypeTopology

open import IntegersAbs hiding (abs)
open import IntegersAddition renaming (_+_ to _ℤ+_)
open import IntegersB
open import IntegersMultiplication renaming (_*_ to _ℤ*_)
open import IntegersOrder renaming (_≤_ to _ℤ≤_) hiding (_<_)
open import NaturalsMultiplication renaming (_*_ to _ℕ*_)
open import ncRationals
open import ncRationalsOperations renaming (abs to ℚₙ-abs) renaming (-_ to ℚₙ-_) hiding (_+_)
open import Rationals
open import RationalsAddition
open import RationalsNegation
open import RationalsOrder

module RationalsAbs where

abs : ℚ → ℚ
abs (q , _) = toℚ (ℚₙ-abs q)

ℚ-abs-zero : 0ℚ ≡ abs 0ℚ
ℚ-abs-zero = by-definition

toℚ-abs : Fun-Ext → (q : ℚₙ) → abs (toℚ q) ≡ toℚ (ℚₙ-abs q) 
toℚ-abs fe (x , a) = conclusion
 where
  rational-q : Σ ((x' , a') , lxp) ꞉ ℚ , Σ h ꞉ ℕ , (x ≡ pos (succ h) ℤ* x') × (succ a ≡ succ h ℕ* succ a')
  rational-q = toℚlemma (x , a)
  lx : ℚ
  lx = pr₁ rational-q
  x' : ℤ
  x' = pr₁ (pr₁ lx)
  a' : ℕ
  a' = pr₂ (pr₁ lx)
  lxp = pr₂ lx
  h = pr₁ (pr₂ (rational-q))
  e₁ : succ a ≡ succ h ℕ* succ a'
  e₁ = pr₂ (pr₂ (pr₂ rational-q))
  e₂ : x ≡ pos (succ h) ℤ* x'
  e₂ = pr₁ (pr₂ (pr₂ rational-q))

  sa = succ a
  psa = pos (succ a)
  sh = succ h
  psh = pos (succ h)
  sa' = succ a'
  psa' = pos (succ a')
    
  helper : ℚₙ-abs (x' , a') ≈ ℚₙ-abs (x , a) → toℚ (ℚₙ-abs (x' , a')) ≡ toℚ (ℚₙ-abs (x , a))
  helper = equiv→equality fe (ℚₙ-abs (x' , a')) (ℚₙ-abs (x , a))

  I : ℚₙ-abs (x' , a') ≈ ℚₙ-abs (x , a)
  I = ℤ-mult-left-cancellable (absℤ x' ℤ* psa) (absℤ x ℤ* psa') psh id II
   where
    II : psh ℤ* (absℤ x' ℤ* psa) ≡ psh ℤ* (absℤ x ℤ* psa')
    II = psh ℤ* (absℤ x' ℤ* psa)       ≡⟨ ℤ*-assoc psh (absℤ x') psa ⁻¹ ⟩
         psh ℤ* absℤ x' ℤ* psa         ≡⟨ by-definition ⟩
         absℤ psh ℤ* absℤ x' ℤ* psa    ≡⟨ ap (_ℤ* psa) (abs-over-mult' psh x' ⁻¹) ⟩
         absℤ (psh ℤ* x') ℤ* psa       ≡⟨ ap (λ z → absℤ z ℤ* psa) (e₂ ⁻¹) ⟩
         absℤ x ℤ* psa                 ≡⟨ ap (λ z → absℤ x ℤ* pos z) e₁ ⟩
         absℤ x ℤ* pos (sh ℕ* sa')     ≡⟨ ap (λ z → absℤ x ℤ* z) (pos-multiplication-equiv-to-ℕ sh sa' ⁻¹) ⟩
         absℤ x ℤ* (psh ℤ* psa')       ≡⟨ ℤ-mult-rearrangement''' (absℤ x) psh psa' ⟩
         psh ℤ* (absℤ x ℤ* psa')       ∎
  
  conclusion : abs (toℚ (x , a)) ≡ toℚ (ℚₙ-abs (x , a))
  conclusion = helper I

abs-of-pos-is-pos : Fun-Ext → (p : ℚ) → 0ℚ ≤ p → abs p ≡ p
abs-of-pos-is-pos fe ((pos x , a) , α) l = I
 where
  I : abs ((pos x , a) , α) ≡ (pos x , a) , α
  I = abs ((pos x , a) , α)    ≡⟨ by-definition ⟩
      toℚ (ℚₙ-abs (pos x , a)) ≡⟨ by-definition ⟩
      toℚ (pos x , a)          ≡⟨ toℚ-toℚₙ fe ((pos x , a) , α) ⁻¹ ⟩
      ((pos x , a) , α) ∎
abs-of-pos-is-pos fe ((negsucc x , a) , α) l = 𝟘-elim (III II)
 where
  I : (pos 0 ℤ* pos (succ a)) ℤ≤ (negsucc x ℤ* pos 1)
  I = l
  II : pos 0 ℤ≤ negsucc x
  II = transport₂ _ℤ≤_ (ℤ-zero-left-is-zero (pos (succ a))) (ℤ-zero-right-neutral (negsucc x)) I
  III : ¬ (pos 0 ℤ≤ negsucc x) 
  III (k , e) = pos-not-negative (ℤ-zero-left-neutral (pos k) ⁻¹ ∙ e)
  

ℚ-abs-neg-equals-pos : Fun-Ext → (q : ℚ) → abs q ≡ abs (- q)
ℚ-abs-neg-equals-pos fe (q , p) = conclusion
 where
  helper : ℚₙ-abs q ≈ ℚₙ-abs (ℚₙ- q) → toℚ (ℚₙ-abs q) ≡ toℚ (ℚₙ-abs (ℚₙ- q))
  helper = equiv→equality fe (ℚₙ-abs q) (ℚₙ-abs (ℚₙ- q))

  I : ℚₙ-abs q ≈ ℚₙ-abs (ℚₙ- q)
  I = ℚₙ-abs-neg-equals-pos q
  
  conclusion : abs (q , p) ≡ abs (- (q , p))
  conclusion = abs (q , p)          ≡⟨ by-definition ⟩
               toℚ (ℚₙ-abs q)        ≡⟨ helper I ⟩
               toℚ (ℚₙ-abs (ℚₙ- q))  ≡⟨ toℚ-abs fe (ℚₙ- q) ⁻¹ ⟩
               abs (toℚ (ℚₙ- q))     ≡⟨ by-definition ⟩
               abs (- (q , p)) ∎

ℚ-abs-inverse : Fun-Ext → (q : ℚ) → (abs q ≡ q) ∔ (abs q ≡ - q)
ℚ-abs-inverse fe ((pos x , a) , q) = inl conclusion
 where
  I : (pos x , a) ≈ toℚₙ (toℚ (pos x , a))
  I = ≈-toℚ (pos x , a)
  II : Σ (x' , a') ꞉ ℚₙ , ((pos x , a) , q ≡ (toℚ (x' , a'))) 
  II = q-has-qn fe ((pos x , a) , q)
  x' = pr₁ (pr₁ II)
  a' = pr₂ (pr₁ II)

  helper : (pos x , a) ≈ (x' , a') → toℚ (pos x , a) ≡ toℚ (x' , a')
  helper = equiv→equality fe (pos x , a) (x' , a')

  III : (pos x , a) ≈ (x' , a')
  III = refl

  conclusion : abs ((pos x , a) , q) ≡ (pos x , a) , q
  conclusion = abs ((pos x , a) , q)   ≡⟨ by-definition ⟩
               toℚ (pos x , a)         ≡⟨ helper III ⟩
               toℚ (x' , a')           ≡⟨ pr₂ II ⁻¹ ⟩
               (pos x , a) , q         ∎
ℚ-abs-inverse fe ((negsucc x , a) , q) = inr conclusion
 where
  conclusion : abs ((negsucc x , a) , q) ≡ (- ((negsucc x , a) , q))
  conclusion = abs ((negsucc x , a) , q)    ≡⟨ by-definition ⟩
               toℚ ((absℤ (negsucc x)) , a)  ≡⟨ by-definition ⟩
               toℚ (pos (succ x) , a)        ≡⟨ by-definition ⟩
               toℚ (ℚₙ- (negsucc x , a))     ≡⟨ by-definition ⟩
               (- ((negsucc x , a) , q))     ∎

ℚ-positive-not-zero : Fun-Ext → (x a : ℕ) → ¬ (toℚ (pos (succ x) , a) ≡ 0ℚ)
ℚ-positive-not-zero fe x a e = pos-int-not-zero x III
 where
  I : (pos (succ x) , a) ≈ (pos 0 , 0)
  I = equality→equiv fe (pos (succ x) , a) (pos 0 , 0) e

  II : pos (succ x) ℤ* pos 1 ≡ pos 0 ℤ* pos (succ a)
  II = I

  III : pos (succ x) ≡ pos 0
  III = pos (succ x)            ≡⟨ by-definition ⟩
        pos (succ x) ℤ* (pos 1) ≡⟨ II ⟩
        pos 0 ℤ* pos (succ a)   ≡⟨ ℤ-zero-left-is-zero (pos (succ a))  ⟩
        pos 0 ∎

ℚ-abs-is-positive : (q : ℚ) → 0ℚ ≤ abs q
ℚ-abs-is-positive ((pos zero , a) , _)     = 0 , I
 where
  I : pos 0 ℤ* pos 0 ℤ+ pos 0 ≡ pos 0 ℤ* pos (succ 0)
  I = pos 0 ℤ* pos 0 ℤ+ pos 0 ≡⟨ by-definition ⟩
      pos 0 ℤ* pos 0          ≡⟨ by-definition ⟩
      pos 0                   ≡⟨ by-definition ⟩
      pos 0 ℤ* pos 1          ∎
ℚ-abs-is-positive ((pos (succ x) , a) , q) = ℚ<-coarser-than-≤ 0ℚ (abs ((pos (succ x) , a) , q)) (ℚ-zero-less-than-positive x a)
ℚ-abs-is-positive ((negsucc x , a) , q)    = ℚ<-coarser-than-≤ 0ℚ (abs (((negsucc x , a) , q))) (ℚ-zero-less-than-positive x a)

ℚ-abs-zero-is-zero : Fun-Ext → (q : ℚ) → abs q ≡ 0ℚ → q ≡ 0ℚ
ℚ-abs-zero-is-zero fe ((pos 0 , a) , p) e = numerator-zero-is-zero fe ((pos 0 , a) , p) refl
ℚ-abs-zero-is-zero fe ((pos (succ x) , a) , p) e = 𝟘-elim (ℚ-positive-not-zero fe x a e)
ℚ-abs-zero-is-zero fe ((negsucc x , a) , p) e = 𝟘-elim (ℚ-positive-not-zero fe x a e)

ℚ-abs-≤ : Fun-Ext → (q : ℚ) → (- (abs q)) ≤ q × q ≤ abs q
ℚ-abs-≤ fe q = locate-q (ℚ-abs-inverse fe q)
 where
  i : 0ℚ ≤ abs q
  i = ℚ-abs-is-positive q
  ii : (0ℚ + (- abs q)) ≤ (abs q + (- abs q))
  ii = ℚ≤-addition-preserves-order fe 0ℚ (abs q) (- abs q) i
  iii : (- abs q) ≤ 0ℚ
  iii = transport₂ _≤_ (ℚ-zero-left-neutral fe (- abs q)) (ℚ-inverse-sum-to-zero fe (abs q)) ii
  iv : (- abs q) ≤ abs q
  iv = ℚ≤-trans fe (- abs q) 0ℚ (abs q) iii i
  
  locate-q : (abs q ≡ q) ∔ (abs q ≡ (- q)) → ((- abs q) ≤ q) × (q ≤ abs q)
  locate-q (inl e) = I , II
   where
    I : (- abs q) ≤ q
    I = transport ((- abs q) ≤_) e iv

    II : q ≤ abs q
    II = transport (q ≤_) (e ⁻¹) (ℚ≤-refl q)
  locate-q (inr r) = I , II
   where
    α : q ≡ (- abs q)
    α = q         ≡⟨ ℚ-minus-minus fe q ⟩
        (- (- q)) ≡⟨ ap -_ (r ⁻¹) ⟩
        - (abs q) ∎
        
    I : (- abs q) ≤ q
    I = transport (_≤ q) α (ℚ≤-refl q)

    II : q ≤ abs q 
    II = transport (_≤ (abs q)) (α ⁻¹) iv

ℚ-abs-≤-unpack : Fun-Ext → (q ε : ℚ) → abs q ≤ ε → - ε ≤ q × q ≤ ε
ℚ-abs-≤-unpack fe q ε l = locate-q (ℚ-abs-inverse fe q)
 where
  abs-q-positive : 0ℚ ≤ abs q
  abs-q-positive = ℚ-abs-is-positive q

  ε-positive : 0ℚ ≤ ε
  ε-positive = ℚ≤-trans fe 0ℚ (abs q) ε abs-q-positive l

  neg-epsilon-negative : (- ε) ≤ 0ℚ
  neg-epsilon-negative = ℚ≤-swap fe 0ℚ ε ε-positive
  
  locate-q : (abs q ≡ q) ∔ (abs q ≡ - q) → ((- ε) ≤ q) × (q ≤ ε)
  locate-q (inl i) = ℚ≤-trans fe (- ε) 0ℚ q neg-epsilon-negative (transport (0ℚ ≤_) i abs-q-positive) , (transport (_≤ ε) i l)
  locate-q (inr i) = transport (- ε ≤_) (ℚ-minus-minus fe q ⁻¹) β , ℚ≤-trans fe q 0ℚ ε δ ε-positive
   where
    α : (- q) ≤ ε
    α = transport (_≤ ε) i l
    β : (- ε) ≤ (- (- q))
    β = ℚ≤-swap fe (- q) ε α
    γ : (- (- q)) ≤ 0ℚ
    γ = transport (λ z → - z ≤ 0ℚ) i (ℚ≤-swap fe 0ℚ (abs q) abs-q-positive)
    δ : q ≤ 0ℚ
    δ = transport (_≤ 0ℚ) (ℚ-minus-minus fe q ⁻¹) γ
  
ℚ≤-to-abs : Fun-Ext → (x y : ℚ) → (- y) ≤ x × x ≤ y → abs x ≤ y
ℚ≤-to-abs fe x y (l₁ , l₂) = I (ℚ-abs-inverse fe x)
 where
  α : (- x) ≤ (- (- y))
  α = ℚ≤-swap fe (- y) x l₁
  I : (abs x ≡ x) ∔ (abs x ≡ (- x)) → abs x ≤ y
  I (inl l) = transport (_≤ y) (l ⁻¹) l₂
  I (inr r) = transport₂ _≤_ (r ⁻¹) (ℚ-minus-minus fe y ⁻¹) α

ℚ<-to-abs : Fun-Ext → (x y : ℚ) → (- y) < x × x < y → abs x < y
ℚ<-to-abs fe x y (l₁ , l₂) = II (ℚ≤-split fe (abs x) y I) 
 where
  I : abs x ≤ y
  I = ℚ≤-to-abs fe x y (ℚ<-coarser-than-≤ (- y) x l₁ , ℚ<-coarser-than-≤ x y l₂)
  II : (abs x < y) ∔ (abs x ≡ y) → abs x < y
  II (inl l) = l
  II (inr r) = III (ℚ-abs-inverse fe x)
   where
    
    III : (abs x ≡ x) ∔ (abs x ≡ - x) → abs x < y
    III (inl s) = 𝟘-elim (ℚ<-not-itself x (transport (x <_) (r ⁻¹ ∙ s) l₂))
    III (inr s) = 𝟘-elim (ℚ<-not-itself x (transport (_< x) IV l₁))
     where
      IV : - y ≡ x
      IV = - y     ≡⟨ ap -_ (r ⁻¹ ∙ s) ⟩
           - (- x) ≡⟨ ℚ-minus-minus fe x ⁻¹ ⟩
           x ∎

ℚ-abs-<-unpack :  Fun-Ext → (q ε : ℚ) → abs q < ε → - ε < q × q < ε
ℚ-abs-<-unpack fe q ε l = locate-q (ℚ-abs-inverse fe q)
 where
  abs-q-positive : 0ℚ ≤ abs q
  abs-q-positive = ℚ-abs-is-positive q
  
  ε-positive : 0ℚ < ε
  ε-positive = ℚ≤-<-trans fe 0ℚ (abs q) ε abs-q-positive l

  neg-epsilon-negative : - ε < 0ℚ
  neg-epsilon-negative = ℚ<-swap fe 0ℚ ε ε-positive

  locate-q : (abs q ≡ q) ∔ (abs q ≡ - q) → ((- ε) < q) × (q < ε)
  locate-q (inl i) = ℚ<-≤-trans fe (- ε) 0ℚ q neg-epsilon-negative (transport (0ℚ ≤_) i abs-q-positive) , (transport (_< ε) i l)
  locate-q (inr i) = transport (- ε <_) (ℚ-minus-minus fe q ⁻¹) β , ℚ≤-<-trans fe q 0ℚ ε δ ε-positive
   where
    α : - q < ε
    α = transport (_< ε) i l
    β : - ε < - (- q)
    β = ℚ<-swap fe (- q) ε α
    γ : - (- q) ≤ 0ℚ
    γ = transport (λ z → - z ≤ 0ℚ) i (ℚ≤-swap fe 0ℚ (abs q) abs-q-positive)
    δ : q ≤ 0ℚ
    δ = transport (_≤ 0ℚ) (ℚ-minus-minus fe q ⁻¹) γ
  

ℚ-triangle-inequality : Fun-Ext → (x y : ℚ) → abs (x + y) ≤ (abs x + abs y)
ℚ-triangle-inequality fe x y = ℚ≤-to-abs fe (x + y) (abs x + abs y) (I (ℚ-abs-≤ fe x) (ℚ-abs-≤ fe y))
 where
  I : (- (abs x)) ≤ x × x ≤ abs x → (- abs y) ≤ y × y ≤ abs y → (- (abs x + abs y)) ≤ (x + y) × (x + y) ≤ (abs x + abs y) -- (input ℚ-abs-order' x and ℚ-abs-order' y)
  I (l₁ , l₂) (l₃ , l₄) = transport (_≤ (x + y)) γ α , β
   where
    α : ((- abs x) + (- abs y)) ≤ (x + y)
    α = ℚ≤-adding fe (- abs x) x (- abs y) y l₁ l₃
    γ : ((- abs x) + (- abs y)) ≡ (- (abs x + abs y))
    γ = ℚ-minus-dist fe (abs x) (abs y)
    β : (x + y) ≤ (abs x + abs y)
    β = ℚ≤-adding fe x (abs x) y (abs y) l₂ l₄



\end{code}
