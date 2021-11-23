\begin{code}
{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆)  -- TypeTopology
open import Rationals renaming (_≤_ to _ℚ≤_ ; _<_ to _ℚ<_ ; -_ to ℚ-_ ; _+_ to _ℚ+_)

open import UF-PropTrunc --TypeTopology
open import UF-FunExt --TypeTopology

module MetricSpace3
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
       where 
open import NewDedekindReals pt fe

open import NaturalsOrder renaming (_<_ to _ℕ<_ ; _≤_ to _ℕ≤_ ; max to ℕmax)
open import UF-PropTrunc
open PropositionalTruncation pt

open import NaturalsMultiplication renaming (_*_ to _ℕ*_)
open import Integers renaming (_*_ to _ℤ*_ ; _+_ to _ℤ+_)
open import IntegersOrder
open import IntegersProperties
open import ncRationals renaming (_<_ to _ℚₙ<_)

ℚ-abs : ℚ → ℚ
ℚ-abs ((x , a) , p) = toℚ (absℤ x , a)

ℚ-abs-zero : zero-ℚ ≡ ℚ-abs zero-ℚ
ℚ-abs-zero = by-definition

toℚ-over-abs : ((x , a) : ℚₙ) → ℚ-abs (toℚ (x , a)) ≡ toℚ (absℤ x , a)
toℚ-over-abs (x , a) = conclusion
 where
  lxl : Σ ((x' , a') , lxp) ꞉ ℚ , Σ h ꞉ ℕ , (x ≡ pos (succ h) ℤ* x') × (succ a ≡ succ h ℕ* succ a')
  lxl = toℚlemma (x , a)
  lx : ℚ
  lx = pr₁ lxl
  x' : ℤ
  x' = pr₁ (pr₁ lx)
  a' : ℕ
  a' = pr₂ (pr₁ lx)
  lxp = pr₂ lx
  h = pr₁ (pr₂ (lxl))
  e₁ : succ a ≡ succ h ℕ* succ a'
  e₁ = pr₂ (pr₂ (pr₂ lxl))
  e₂ : x ≡ pos (succ h) ℤ* x'
  e₂ = pr₁ (pr₂ (pr₂ lxl))
  
  helper : (absℤ x' , a') ℚₙ≈ (absℤ x , a) → toℚ (absℤ x' , a') ≡ toℚ (absℤ x , a)
  helper = pr₁ (equiv-equality fe (absℤ x' , a') (absℤ x , a))

  I : (absℤ x' , a') ℚₙ≈ (absℤ x , a)
  I = ℤ-mult-left-cancellable (absℤ x' ℤ* pos (succ a)) (absℤ x ℤ* pos (succ a')) (pos (succ h)) (pos-succ-not-zero h) II
   where
    II : pos (succ h) ℤ* (absℤ x' ℤ* pos (succ a)) ≡ pos (succ h) ℤ* (absℤ x ℤ* pos (succ a'))
    II = pos (succ h) ℤ* (absℤ x' ℤ* pos (succ a))      ≡⟨ ℤ*-assoc (pos (succ h)) (absℤ x') (pos (succ a)) ⟩
         pos (succ h) ℤ* absℤ x' ℤ* pos (succ a)        ≡⟨ by-definition ⟩
         absℤ (pos (succ h)) ℤ* absℤ x' ℤ* pos (succ a) ≡⟨ ap (_ℤ* (pos (succ a))) (abs-over-mult' (pos (succ h)) x' ⁻¹) ⟩
         absℤ (pos (succ h) ℤ* x') ℤ* pos (succ a)      ≡⟨ ap (λ z → absℤ z ℤ* pos (succ a)) (e₂ ⁻¹) ⟩
         absℤ x ℤ* pos (succ a)                         ≡⟨ ap (λ z → absℤ x ℤ* pos z) e₁ ⟩
         absℤ x ℤ* pos (succ h ℕ* succ a')              ≡⟨ ap (λ z → absℤ x ℤ* z) (pos-multiplication-equiv-to-ℕ (succ h) (succ a') ⁻¹) ⟩
         absℤ x ℤ* (pos (succ h) ℤ* pos (succ a'))      ≡⟨ ℤ-mult-rearrangement''' (absℤ x) (pos (succ h)) (pos (succ a')) ⟩
         pos (succ h) ℤ* (absℤ x ℤ* pos (succ a')) ∎

  conclusion : ℚ-abs (toℚ (x , a)) ≡ toℚ (absℤ x , a)
  conclusion = ℚ-abs (toℚ (x , a))             ≡⟨ by-definition ⟩
               ℚ-abs ((x' , a') , lxp)         ≡⟨ by-definition ⟩
               toℚ (absℤ x' , a')              ≡⟨ helper I ⟩
               toℚ (absℤ x , a) ∎

ℚ-abs-neg-equals-pos : (q : ℚ) → ℚ-abs q ≡ ℚ-abs (ℚ- q)
ℚ-abs-neg-equals-pos ((x , a) , lt) = conclusion
 where
  helper : (absℤ x , a) ℚₙ≈ (absℤ (- x) , a) → toℚ (absℤ x , a) ≡ toℚ (absℤ (- x) , a)
  helper = pr₁ (equiv-equality fe (absℤ x , a) (absℤ (- x) , a))

  I : (absℤ x , a) ℚₙ≈ (absℤ (- x) , a)
  I = absℤ x ℤ* pos (succ a)     ≡⟨ ap (_ℤ* pos (succ a)) (absℤ-removes-neg-sign x) ⟩
      absℤ (- x) ℤ* pos (succ a) ∎

  conclusion : ℚ-abs ((x , a) , lt) ≡ ℚ-abs (ℚ- ((x , a) , lt))
  conclusion = ℚ-abs ((x , a) , lt)       ≡⟨ by-definition ⟩
                toℚ (absℤ x , a)          ≡⟨ helper I ⟩
                toℚ (absℤ (- x) , a)      ≡⟨ toℚ-over-abs (- x , a) ⁻¹ ⟩
                ℚ-abs (toℚ (- x , a))     ≡⟨ by-definition ⟩
                ℚ-abs (ℚ- ((x , a) , lt)) ∎

ℚ-abs-inverse : (q : ℚ) → (ℚ-abs q ≡ q) ∔ (ℚ-abs q ≡ (ℚ- q))
ℚ-abs-inverse ((pos x , a) , q) = inl conclusion
 where
  I : (pos x , a) ℚₙ≈ toℚₙ (toℚ (pos x , a))
  I = ≈-toℚ (pos x , a)
  II : Σ (x' , a') ꞉ ℚₙ , ((pos x , a) , q ≡ (toℚ (x' , a'))) 
  II = q-has-qn fe ((pos x , a) , q)
  x' = pr₁ (pr₁ II)
  a' = pr₂ (pr₁ II)

  helper : (pos x , a) ℚₙ≈ (x' , a') → toℚ (pos x , a) ≡ toℚ (x' , a')
  helper = lr-implication (equiv-equality fe (pos x , a) (x' , a'))

  III : (pos x , a) ℚₙ≈ (x' , a')
  III = refl

  conclusion : ℚ-abs ((pos x , a) , q) ≡ (pos x , a) , q
  conclusion = ℚ-abs ((pos x , a) , q) ≡⟨ by-definition ⟩
               toℚ (pos x , a)         ≡⟨ helper III ⟩
               toℚ (x' , a')           ≡⟨ pr₂ II ⁻¹ ⟩
               (pos x , a) , q ∎
ℚ-abs-inverse ((negsucc x , a) , q) = inr conclusion
 where
  conclusion : ℚ-abs ((negsucc x , a) , q) ≡ (ℚ- ((negsucc x , a) , q))
  conclusion = ℚ-abs ((negsucc x , a) , q)  ≡⟨ by-definition ⟩
               toℚ ((absℤ (negsucc x)) , a) ≡⟨ by-definition ⟩
               toℚ (pos (succ x) , a)       ≡⟨ by-definition ⟩
               toℚ (- (negsucc x) , a)      ≡⟨ by-definition ⟩
               (ℚ- ((negsucc x , a) , q))   ∎

open import UF-Subsingletons
open import UF-Base

ℚ-positive-not-zero : (x a : ℕ) → ¬ (toℚ (pos (succ x) , a) ≡ zero-ℚ)
ℚ-positive-not-zero x a e = pos-int-not-zero x III
 where
  I : (pos (succ x) , a) ℚₙ≈ (pos 0 , 0)
  I = rl-implication (equiv-equality fe (pos (succ x) , a) (pos 0 , 0)) e

  II : pos (succ x) ℤ* pos 1 ≡ pos 0 ℤ* pos (succ a)
  II = I

  III : pos (succ x) ≡ pos 0
  III = pos (succ x)            ≡⟨ by-definition ⟩
        pos (succ x) ℤ* (pos 1) ≡⟨ II ⟩
        pos 0 ℤ* pos (succ a)   ≡⟨ ℤ-zero-left-is-zero (pos (succ a))  ⟩
        pos 0 ∎

ℚ-abs-is-positive : (q : ℚ) → zero-ℚ ℚ≤ ℚ-abs q
ℚ-abs-is-positive ((pos zero , a) , lt)     = inr (numerator-zero-is-zero fe zero-ℚ refl)
ℚ-abs-is-positive ((pos (succ x) , a) , lt) = inl (ℚ-zero-less-than-positive x a)
ℚ-abs-is-positive ((negsucc x , a) , lt)    = inl (ℚ-zero-less-than-positive x a)

ℚ-abs-order : (q : ℚ) → q ℚ≤ ℚ-abs q
ℚ-abs-order q = cases I II (ℚ-abs-inverse q)
 where
  I : ℚ-abs q ≡ q → q ℚ≤ ℚ-abs q
  I e = inr (e ⁻¹)
  II : ℚ-abs q ≡ (ℚ- q) → q ℚ≤ ℚ-abs q
  II e = conclusion ii
   where
    i : zero-ℚ ℚ≤ ℚ-abs q
    i = ℚ-abs-is-positive q
    ii : zero-ℚ ℚ≤ (ℚ- q)
    ii = transport (zero-ℚ ℚ≤_) e i
    
    conclusion : (zero-ℚ ℚ< (ℚ- q)) ∔ (zero-ℚ ≡ (ℚ- q)) → q ℚ≤ ℚ-abs q
    conclusion (inl l) = inl (ℚ<-trans q zero-ℚ (ℚ-abs q) α β)
     where
      γ : (zero-ℚ ℚ+ q) ℚ< ((ℚ- q) ℚ+ q)
      γ = ℚ-addition-preserves-order zero-ℚ (ℚ- q) q l
      α : q ℚ< zero-ℚ
      α = transport₂ _ℚ<_ ψ υ γ
       where
        ψ : zero-ℚ ℚ+ q ≡ q
        ψ = ℚ-zero-left-neutral fe q
        υ : (ℚ- q) ℚ+ q ≡ zero-ℚ
        υ = ℚ-inverse-sum-to-zero' fe q
      β : zero-ℚ ℚ< ℚ-abs q
      β = transport (zero-ℚ ℚ<_) (e ⁻¹) l
    conclusion (inr t) = inr β
     where
      α : q ≡ zero-ℚ
      α = q              ≡⟨ ℚ-zero-right-neutral fe q ⁻¹ ⟩
          (q ℚ+ zero-ℚ)  ≡⟨ ap (q ℚ+_) t ⟩
          (q ℚ-- q)      ≡⟨ ℚ-inverse-sum-to-zero fe q ⟩
          zero-ℚ ∎
      β : q ≡ ℚ-abs q
      β = transport (λ z → z ≡ ℚ-abs z) (α ⁻¹) ℚ-abs-zero

_ℚ≤_ℚ≤_ : (p q r : ℚ) → 𝓤₀ ̇
p ℚ≤ q ℚ≤ r = (p ℚ≤ q) × (q ℚ≤ r)

ℚ-abs-order' : (q : ℚ) → (ℚ- (ℚ-abs q)) ℚ≤ q ℚ≤ ℚ-abs q
ℚ-abs-order' q = I , II
 where
  I : (ℚ- ℚ-abs q) ℚ≤ q
  I = cases III IV (ℚ-abs-inverse  q)
   where
    III : ℚ-abs q ≡ q → (ℚ- ℚ-abs q) ℚ≤ q
    III e = cases i ii α
     where
      α : zero-ℚ ℚ≤ ℚ-abs q
      α = ℚ-abs-is-positive q
      β : zero-ℚ ℚ≤ q
      β = transport (zero-ℚ ℚ≤_) e α
      i : zero-ℚ ℚ< ℚ-abs q → (ℚ- ℚ-abs q) ℚ≤ q
      i l = inl conclusion
       where
        γ : (zero-ℚ ℚ+ (ℚ- ℚ-abs q)) ℚ< (ℚ-abs q ℚ+ (ℚ- ℚ-abs q))
        γ = ℚ-addition-preserves-order zero-ℚ (ℚ-abs q) (ℚ- (ℚ-abs q)) l
        ψ : zero-ℚ ℚ+ (ℚ- ℚ-abs q) ≡ (ℚ- ℚ-abs q)
        ψ = ℚ-zero-left-neutral fe (ℚ- (ℚ-abs q)) 
        ϕ : (ℚ-abs q ℚ+ (ℚ- ℚ-abs q)) ≡ zero-ℚ
        ϕ = ℚ-inverse-sum-to-zero fe (ℚ-abs q)
        ζ : (ℚ- ℚ-abs q) ℚ< zero-ℚ
        ζ = transport₂ _ℚ<_ ψ ϕ γ
        conclusion : (ℚ- ℚ-abs q) ℚ< q
        conclusion = ℚ<-trans (ℚ- (ℚ-abs q)) zero-ℚ q ζ (transport (zero-ℚ ℚ<_) e l)
      ii : zero-ℚ ≡ ℚ-abs q → (ℚ- ℚ-abs q) ℚ≤ q
      ii e₂ = inr iv
       where
        iii : zero-ℚ ≡ q
        iii = e₂ ∙ e
        iv : (ℚ- ℚ-abs q) ≡ q
        iv = (ℚ- ℚ-abs q) ≡⟨ ap ℚ-_ (e₂ ⁻¹) ⟩
             (ℚ- zero-ℚ)  ≡⟨ by-definition ⟩ 
             zero-ℚ       ≡⟨ e₂ ⟩
             ℚ-abs q      ≡⟨ e ⟩
             q ∎
      
    IV : ℚ-abs q ≡ (ℚ- q) → (ℚ- ℚ-abs q) ℚ≤ q
    IV e = inr α
     where
      α : (ℚ- ℚ-abs q) ≡ q
      α = (ℚ- ℚ-abs q) ≡⟨ ap ℚ-_ e ⟩
          (ℚ- (ℚ- q))  ≡⟨ ℚ-minus-minus fe q ⁻¹ ⟩
          q ∎
  II : q ℚ≤ ℚ-abs q
  II = ℚ-abs-order q
 
numerator-zero-is-zero' : (a : ℕ) → toℚ (pos 0 , a) ≡ zero-ℚ
numerator-zero-is-zero' a = I II
 where
  I : ((pos 0 , a) ℚₙ≈ (pos 0 , 0)) → toℚ (pos 0 , a) ≡ zero-ℚ
  I = lr-implication (equiv-equality fe (pos 0 , a) (pos 0 , 0))
  II : (pos 0 , a) ℚₙ≈ (pos 0 , 0)
  II = pos 0 ℤ* pos 1 ≡⟨ by-definition ⟩
       pos 0          ≡⟨ ℤ-zero-left-is-zero (pos (succ a)) ⁻¹ ⟩
       pos 0 ℤ* pos (succ a) ∎

ℚ-abs-zero-is-zero : (q : ℚ) → ℚ-abs q ≡ zero-ℚ → q ≡ zero-ℚ
ℚ-abs-zero-is-zero ((pos 0 , a) , p) e = numerator-zero-is-zero fe ((pos 0 , a) , p) refl
ℚ-abs-zero-is-zero ((pos (succ x) , a) , p) e = 𝟘-elim (ℚ-positive-not-zero x a e)
ℚ-abs-zero-is-zero ((negsucc x , a) , p) e = 𝟘-elim (ℚ-positive-not-zero x a e)

ℚ-te-lemma : (x a : ℚ) → ℚ-abs x ℚ≤ a → x ℚ≤ a
ℚ-te-lemma x a (inl l) = cases I II (ℚ-abs-order x)
 where
  I : x ℚ< ℚ-abs x → x ℚ≤ a
  I s = inl (ℚ<-trans x (ℚ-abs x) a s l)
  II : x ≡ ℚ-abs x → x ℚ≤ a
  II e = inl (transport (_ℚ< a) (e ⁻¹) l)
ℚ-te-lemma x a (inr e) = cases I II (ℚ-abs-order x)
 where
  I : x ℚ< ℚ-abs x → x ℚ≤ a
  I l = inl (transport (x ℚ<_) e l)
  II : x ≡ ℚ-abs x → x ℚ≤ a
  II e₂ = inr (e₂ ∙ e)

ℚ≤-addition-preserves-order : (x y z : ℚ) → x ℚ≤ y → (x ℚ+ z) ℚ≤ (y ℚ+ z)
ℚ≤-addition-preserves-order x y z (inl l) = inl (ℚ-addition-preserves-order x y z l)
ℚ≤-addition-preserves-order x y z (inr e) = inr (ap (_ℚ+ z) e)

ℚ≤-adding : (x y u v : ℚ) → x ℚ≤ y → u ℚ≤ v → (x ℚ+ u) ℚ≤ (y ℚ+ v) 
ℚ≤-adding x y u v (inl l₁) (inl l₂) = inl (ℚ<-adding x y u v l₁ l₂)
ℚ≤-adding x y u v (inl l₁) (inr l₂) = inl (transport ((x ℚ+ u) ℚ<_) (ap (y ℚ+_) l₂) I)
 where
  I : (x ℚ+ u) ℚ< (y ℚ+ u)
  I = ℚ-addition-preserves-order x y u l₁
ℚ≤-adding x y u v (inr l₁) (inl l₂) = inl (transport (_ℚ< (y ℚ+ v)) (ap (_ℚ+ u) (l₁ ⁻¹)) II)
 where
  I : (u ℚ+ y) ℚ< (v ℚ+ y)
  I = ℚ-addition-preserves-order u v y l₂
  II : (y ℚ+ u) ℚ< (y ℚ+ v)
  II = transport₂ _ℚ<_ (ℚ+-comm u y) (ℚ+-comm v y) I
ℚ≤-adding x y u v (inr l₁) (inr l₂) = inr (ap₂ _ℚ+_ l₁ l₂)

ℚ≤-swap : (x y : ℚ) → x ℚ≤ y → (ℚ- y) ℚ≤ (ℚ- x)
ℚ≤-swap x y l = transport id III II
 where
  I : (x ℚ+ (ℚ- x)) ℚ≤ (y ℚ+ (ℚ- x))
  I = ℚ≤-addition-preserves-order x y (ℚ- x) l
  
  II : ((x ℚ+ (ℚ- x)) ℚ+ (ℚ- y)) ℚ≤ ((y ℚ+ (ℚ- x)) ℚ+ (ℚ- y))
  II = ℚ≤-addition-preserves-order (x ℚ+ (ℚ- x)) (y ℚ+ (ℚ- x)) (ℚ- y) I

  III : (((x ℚ+ (ℚ- x)) ℚ+ (ℚ- y)) ℚ≤ ((y ℚ+ (ℚ- x)) ℚ+ (ℚ- y))) ≡ ((ℚ- y) ℚ≤ (ℚ- x))
  III = ap₂ _ℚ≤_ α β
   where
    α : (((x ℚ+ (ℚ- x)) ℚ+ (ℚ- y))) ≡ (ℚ- y)
    α = ((x ℚ+ (ℚ- x)) ℚ+ (ℚ- y)) ≡⟨ ap (_ℚ+ (ℚ- y)) (ℚ-inverse-sum-to-zero fe x) ⟩
        zero-ℚ ℚ+ (ℚ- y)          ≡⟨ ℚ-zero-left-neutral fe (ℚ- y) ⟩ 
        (ℚ- y)                    ∎
    β : ((y ℚ+ (ℚ- x)) ℚ+ (ℚ- y)) ≡ (ℚ- x)
    β = ((y ℚ+ (ℚ- x)) ℚ+ (ℚ- y)) ≡⟨ ap (_ℚ+ (ℚ- y)) (ℚ+-comm y (ℚ- x)) ⟩
        (((ℚ- x) ℚ+ y) ℚ+ (ℚ- y)) ≡⟨ ℚ+-assoc fe (ℚ- x) y (ℚ- y) ⟩
        ((ℚ- x) ℚ+ (y ℚ+ (ℚ- y))) ≡⟨ ap ((ℚ- x) ℚ+_) (ℚ-inverse-sum-to-zero fe y) ⟩
        ((ℚ- x) ℚ+ zero-ℚ)        ≡⟨ ℚ-zero-right-neutral fe (ℚ- x) ⟩
        (ℚ- x) ∎

ℚ-te-lemma-b : (x y : ℚ) → (ℚ- y) ℚ≤ x ℚ≤ y → ℚ-abs x ℚ≤ y
ℚ-te-lemma-b x y (l₁ , l₂) = I (ℚ-abs-inverse x)
 where
  I : (ℚ-abs x ≡ x) ∔ (ℚ-abs x ≡ (ℚ- x)) → ℚ-abs x ℚ≤ y
  I (inl e) = transport (_ℚ≤ y) (e ⁻¹) l₂
  I (inr e) = transport₂ _ℚ≤_ (e ⁻¹) (ℚ-minus-minus fe y ⁻¹) II
   where
    II : (ℚ- x) ℚ≤ (ℚ- (ℚ- y))
    II = ℚ≤-swap (ℚ- y) x l₁

ℚ-triangle-inequality : (x y : ℚ) → ℚ-abs (x ℚ+ y) ℚ≤ (ℚ-abs x ℚ+ ℚ-abs y)
ℚ-triangle-inequality x y = ℚ-te-lemma-b (x ℚ+ y) (ℚ-abs x ℚ+ ℚ-abs y) (I (ℚ-abs-order' x) (ℚ-abs-order' y))
 where
  I : (ℚ- ℚ-abs x) ℚ≤ x ℚ≤ ℚ-abs x → (ℚ- ℚ-abs y) ℚ≤ y ℚ≤ ℚ-abs y → (ℚ- (ℚ-abs x ℚ+ ℚ-abs y)) ℚ≤ (x ℚ+ y) ℚ≤ (ℚ-abs x ℚ+ ℚ-abs y) -- (input ℚ-abs-order' x and ℚ-abs-order' y)
  I (l₁ , l₂) (l₃ , l₄) = transport (_ℚ≤ (x ℚ+ y)) γ α , β
   where
    α : ((ℚ- ℚ-abs x) ℚ+ (ℚ- ℚ-abs y)) ℚ≤ (x ℚ+ y)
    α = ℚ≤-adding (ℚ- ℚ-abs x) x (ℚ- ℚ-abs y) y l₁ l₃
    γ : ((ℚ- ℚ-abs x) ℚ+ (ℚ- ℚ-abs y)) ≡ (ℚ- (ℚ-abs x ℚ+ ℚ-abs y))
    γ = ℚ-minus-dist fe (ℚ-abs x) (ℚ-abs y)
    β : (x ℚ+ y) ℚ≤ (ℚ-abs x ℚ+ ℚ-abs y)
    β = ℚ≤-adding x (ℚ-abs x) y (ℚ-abs y) l₂ l₄
  
ℚ-metric : ℚ → ℚ → ℚ
ℚ-metric p q = ℚ-abs (p ℚ-- q)

ℚ-self-dist : (q : ℚ) → ℚ-metric q q ≡ zero-ℚ
ℚ-self-dist q = ℚ-metric q q    ≡⟨ by-definition ⟩
                ℚ-abs (q ℚ-- q) ≡⟨ ap ℚ-abs (ℚ-inverse-sum-to-zero fe q) ⟩
                ℚ-abs zero-ℚ    ≡⟨ by-definition ⟩
                zero-ℚ ∎

ℚ-metric-commutes : (p q : ℚ) → ℚ-metric p q ≡ ℚ-metric q p
ℚ-metric-commutes p q = conclusion
 where
  conclusion : ℚ-metric p q ≡ ℚ-metric q p -- Ridiculous proof :(
  conclusion = ℚ-metric p q                   ≡⟨ by-definition ⟩
               ℚ-abs (p ℚ-- q)                ≡⟨ ℚ-abs-neg-equals-pos (p ℚ-- q) ⟩
               ℚ-abs (ℚ- (p ℚ-- q))           ≡⟨ by-definition ⟩
               ℚ-abs (ℚ- (p ℚ+ (ℚ- q)))       ≡⟨ ap (λ z → ℚ-abs (ℚ- z)) (ℚ+-comm p (ℚ- q)) ⟩
               ℚ-abs (ℚ- ((ℚ- q) ℚ+ p))       ≡⟨ ap ℚ-abs (ℚ-minus-dist fe (ℚ- q) p ⁻¹) ⟩
               ℚ-abs ((ℚ- (ℚ- q)) ℚ+ (ℚ- p))  ≡⟨ ap (λ z → ℚ-abs (z ℚ+ (ℚ- p))) (ℚ-minus-minus fe q ⁻¹) ⟩
               ℚ-abs (q ℚ+ (ℚ- p))            ≡⟨ by-definition ⟩
               ℚ-abs (q ℚ-- p)                ≡⟨ by-definition ⟩
               ℚ-metric q p                   ∎

ℚ-max : ℚ → ℚ → ℚ
ℚ-max p q = I (ℚ-trichotomous fe p q)
 where
  I : (p ℚ< q) ∔ (p ≡ q) ∔ (q ℚ< p) → ℚ
  I (inl z) = q
  I (inr z) = p

ℚ-min : ℚ → ℚ → ℚ
ℚ-min p q = I (ℚ-trichotomous fe p q)
 where
  I : (p ℚ< q) ∔ (p ≡ q) ∔ (q ℚ< p) → ℚ
  I (inl z) = p
  I (inr z) = q

B-ℚ : (x y ε : ℚ) → zero-ℚ ℚ< ε → 𝓤₀ ̇
B-ℚ x y ε l = ℚ-metric x y ℚ< ε

open import UF-Powerset

B-ℝ : (x y : ℝ) → (ε : ℚ) → zero-ℚ ℚ< ε → 𝓤₀ ̇
B-ℝ ((Lx , Rx) , _) ((Ly , Ry) , _) ε l =
  ∃ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , p ∈ Lx × u ∈ Ly × q ∈ Rx × v ∈ Ry × B-ℚ (ℚ-min p u) (ℚ-max q v) ε l

m1a : {𝓤 : Universe} → (X : 𝓤 ̇) → (B : X → X → (ε : ℚ) → zero-ℚ ℚ< ε → 𝓤₀ ̇) → 𝓤 ̇
m1a X B = (x y : X) → ((ε : ℚ) → (l : zero-ℚ ℚ< ε) → B x y ε l) → x ≡ y

m1b : {𝓤 : Universe} → (X : 𝓤 ̇) → (B : X → X → (ε : ℚ) → zero-ℚ ℚ< ε → 𝓤₀ ̇) → 𝓤 ̇
m1b X B = (x : X) → ((ε : ℚ) → (l : zero-ℚ ℚ< ε) → B x x ε l)

m2 : {𝓤 : Universe} → (X : 𝓤 ̇) → (B : X → X → (ε : ℚ) → zero-ℚ ℚ< ε → 𝓤₀ ̇) → 𝓤 ̇
m2 X B = (x y : X) → (ε : ℚ) → (l : zero-ℚ ℚ< ε) → B x y ε l → B y x ε l

m3 : {𝓤 : Universe} → (X : 𝓤 ̇) → (B : X → X → (ε : ℚ) → zero-ℚ ℚ< ε → 𝓤₀ ̇) → 𝓤 ̇
m3 X B = (x y : X) → (ε₁ ε₂ : ℚ) → (l₁ : zero-ℚ ℚ< ε₁) → (l₂ : zero-ℚ ℚ< ε₂) → ε₁ ℚ< ε₂ → B x y ε₁ l₁ → B x y ε₂ l₂

m4 : {𝓤 : Universe} → (X : 𝓤 ̇) → (B : X → X → (ε : ℚ) → zero-ℚ ℚ< ε → 𝓤₀ ̇) → 𝓤 ̇
m4 X B = (x y z : X) → (ε₁ ε₂ : ℚ) → (l₁ : (zero-ℚ ℚ< ε₁)) → (l₂ : (zero-ℚ ℚ< ε₂)) → B x y ε₁ l₁ → B y z ε₂ l₂ → B x z (ε₁ ℚ+ ε₂) (ℚ<-adding-zero ε₁ ε₂ l₁ l₂)

metric-space : {𝓤 : Universe} → (X : 𝓤 ̇) → 𝓤₁ ⊔ 𝓤 ̇
metric-space X = Σ B ꞉ (X → X → (ε : ℚ) → zero-ℚ ℚ< ε → 𝓤₀ ̇) , m1a X B × m1b X B × m2 X B × m3 X B × m4 X B

ℚₙ≡-to-ℚ≡ : (p q : ℚₙ) → p ≡ q → toℚ p ≡ toℚ q
ℚₙ≡-to-ℚ≡ p q e = ap toℚ e

ℚ-add-zero : (x y z : ℚ) → (x ℚ+ y) ≡ ((x ℚ-- z) ℚ+ (z ℚ+ y))
ℚ-add-zero x y z = I
 where
  I : (x ℚ+ y) ≡ ((x ℚ-- z) ℚ+ (z ℚ+ y))
  I = (x ℚ+ y)                    ≡⟨ ap (_ℚ+ y) (ℚ-zero-right-neutral fe x ⁻¹) ⟩
      ((x ℚ+ zero-ℚ) ℚ+ y)        ≡⟨ ap (λ k → (x ℚ+ k) ℚ+ y) (ℚ-inverse-sum-to-zero' fe z ⁻¹) ⟩
      ((x ℚ+ ((ℚ- z) ℚ+ z)) ℚ+ y) ≡⟨ ap (_ℚ+ y) (ℚ+-assoc fe x (ℚ- z) z ⁻¹) ⟩
      (((x ℚ+ (ℚ- z)) ℚ+ z) ℚ+ y) ≡⟨ ℚ+-assoc fe (x ℚ-- z) z y ⟩
      ((x ℚ-- z) ℚ+ (z ℚ+ y)) ∎

ℚ-metric-space : metric-space ℚ
ℚ-metric-space = B-ℚ , I , II , III , IV , V
 where
  I : m1a ℚ B-ℚ
  I x y f = γ β
   where
    α : ℚ
    α = ℚ-metric x y
    β : zero-ℚ ℚ≤ α
    β = ℚ-abs-is-positive (x ℚ-- y)
    γ : zero-ℚ ℚ≤ ℚ-metric x y → x ≡ y
    γ (inl z) = 𝟘-elim (ℚ<-not-itself α ζ)
     where
      ζ : α ℚ< α
      ζ = f α z
    γ (inr z) = ii
     where
      i : (x ℚ-- y) ≡ zero-ℚ
      i = ℚ-abs-zero-is-zero (x ℚ-- y) (z ⁻¹)
      ii : x ≡ y
      ii = x                      ≡⟨ ℚ-zero-right-neutral fe x ⁻¹ ⟩
           x ℚ+ zero-ℚ            ≡⟨ ap (x ℚ+_) (ℚ-inverse-sum-to-zero fe y ⁻¹) ⟩
           (x ℚ+ (y ℚ+ (ℚ- y)))   ≡⟨ ap (x ℚ+_) (ℚ+-comm y (ℚ- y)) ⟩
           (x ℚ+ ((ℚ- y) ℚ+ y))   ≡⟨ ℚ+-assoc fe x (ℚ- y) y ⁻¹ ⟩
           ((x ℚ+ (ℚ- y)) ℚ+ y)   ≡⟨ ap (_ℚ+ y) i ⟩
           (zero-ℚ ℚ+ y)          ≡⟨ ℚ-zero-left-neutral fe y ⟩ 
           y                      ∎
    
  II : m1b ℚ B-ℚ
  II x y l = transport (λ v → v ℚ< y) (ℚ-self-dist x ⁻¹) l
  
  III : m2 ℚ B-ℚ
  III x y ε l₁ B = transport (λ z → z ℚ< ε) (ℚ-metric-commutes x y) B
  
  IV : m3 ℚ B-ℚ
  IV x y ε₁ ε₂ l₁ l₂ l₃ B = ℚ<-trans (ℚ-metric x y) ε₁ ε₂ B l₃
  
  V : m4 ℚ B-ℚ
  V x y z ε₁ ε₂ l₁ l₂ B₁ B₂ = conclusion α
   where
    α : ℚ-abs ((x ℚ-- y) ℚ+ (y ℚ-- z)) ℚ≤ (ℚ-abs (x ℚ-- y) ℚ+ ℚ-abs (y ℚ-- z))
    α = ℚ-triangle-inequality (x ℚ-- y) (y ℚ-- z)
    
    β : (ℚ-abs (x ℚ-- y) ℚ+ ℚ-abs (y ℚ-- z)) ℚ< (ε₁ ℚ+ ε₂)
    β = ℚ<-adding (ℚ-abs (x ℚ-- y)) ε₁ (ℚ-abs(y ℚ-- z)) ε₂ B₁ B₂

    δ : ℚ-abs ((x ℚ-- y) ℚ+ (y ℚ+ (ℚ- z))) ≡ ℚ-abs (x ℚ-- z)
    δ = ap ℚ-abs (ℚ-add-zero x (ℚ- z) y ⁻¹)
    
    conclusion : ℚ-abs ((x ℚ-- y) ℚ+ (y ℚ-- z)) ℚ≤ (ℚ-abs (x ℚ-- y) ℚ+ ℚ-abs (y ℚ-- z)) → ℚ-abs (x ℚ-- z) ℚ< (ε₁ ℚ+ ε₂)
    conclusion (inl l) = ℚ<-trans (ℚ-abs (x ℚ-- z)) ((ℚ-abs (x ℚ-- y) ℚ+ ℚ-abs (y ℚ-- z))) (ε₁ ℚ+ ε₂) γ β
     where
      γ : ℚ-abs (x ℚ-- z) ℚ< (ℚ-abs (x ℚ-- y) ℚ+ ℚ-abs (y ℚ-- z))
      γ = transport (λ k → k ℚ< (ℚ-abs (x ℚ-- y) ℚ+ ℚ-abs (y ℚ-- z))) δ l
    conclusion (inr e) = transport (_ℚ< (ε₁ ℚ+ ε₂)) (e ⁻¹ ∙ δ) β

open import NaturalsOrder renaming (_<_ to _ℕ<_)

ℚ-lim : (L : ℚ) → (f : ℕ → ℚ) → 𝓤₀ ̇
ℚ-lim L f = ∀ (ε : ℚ) → zero-ℚ ℚ< ε → Σ N ꞉ ℕ , ((n : ℕ) → N ℕ< n → ℚ-metric (f n) L ℚ< ε)

ℚ-squeeze : (L : ℚ)
          → (f g h : ℕ → ℚ)
          → ℚ-lim L f
          → ℚ-lim L h
          → Σ N ꞉ ℕ , ((n : ℕ) → (N ℕ< n) → f n ℚ≤ g n ℚ≤ h n)
          → ℚ-lim L g
ℚ-squeeze L f g h f-conv h-conv (N₁ , n-large) ε l₁ = I (f-conv ε l₁) (h-conv ε l₁)
 where
  I : (Σ N₂ ꞉ ℕ , ((n : ℕ) → N₂ ℕ< n → ℚ-metric (f n) L ℚ< ε))
    → (Σ N₃ ꞉ ℕ , ((n : ℕ) → N₃ ℕ< n → ℚ-metric (h n) L ℚ< ε))
    → Σ N ꞉ ℕ , ((n : ℕ) → N ℕ< n → ℚ-metric (g n) L ℚ< ε)
  I = {!!}

ℝ-metric-space : metric-space ℝ
ℝ-metric-space = B-ℝ , I , II , III , IV , V
 where
  I : m1a ℝ B-ℝ
  I x y f = {!!}
   where
    δ : {!!}
    δ = {!!}
    α : {!!}
    α = ℚ-metric {!!} {!!}
  II : m1b ℝ B-ℝ
  II x ε l = {!!}
  III : m2 ℝ B-ℝ
  III = {!!}
  IV : m3 ℝ B-ℝ
  IV = {!!}
  V : m4 ℝ B-ℝ
  V = {!!}


   -- ?ℚ<-trans (ℚ-abs (x ℚ-- z)) (ℚ-abs (x ℚ-- y) ℚ+ ℚ-abs (y ℚ-- z)) (ε₁ ℚ+ ε₂) γ β
   -- where
    {-
    α : ℚ-abs ((x ℚ-- y) ℚ+ (y ℚ-- z)) ℚ< (ℚ-abs (x ℚ-- y) ℚ+ ℚ-abs (y ℚ-- z))
    α = ℚ-triangle-inequality (x ℚ-- y) (y ℚ-- z)
    β : (ℚ-abs (x ℚ-- y) ℚ+ ℚ-abs (y ℚ-- z)) ℚ< (ε₁ ℚ+ ε₂)
    β = ℚ<-adding (ℚ-abs (x ℚ-- y)) ε₁ (ℚ-abs(y ℚ-- z)) ε₂ B₁ B₂
    γ : ℚ-abs (x ℚ-- z) ℚ< (ℚ-abs (x ℚ-- y) ℚ+ ℚ-abs (y ℚ-- z))
    γ = transport (λ k → k ℚ< (ℚ-abs (x ℚ-- y) ℚ+ ℚ-abs (y ℚ-- z))) ζ (ℚ-triangle-inequality (x ℚ-- y) (y ℚ-- z))
     where
      ζ : ℚ-abs ((x ℚ-- y) ℚ+ (y ℚ-- z)) ≡ ℚ-abs (x ℚ-- z)
      ζ = ap ℚ-abs δ
       where
        δ : ((x ℚ-- y) ℚ+ (y ℚ-- z)) ≡ (x ℚ-- z)
        δ = ((x ℚ-- y) ℚ+ (y ℚ-- z))          ≡⟨ ℚ+-assoc fe x (ℚ- y) (y ℚ-- z) ⟩
             (x ℚ+ ((ℚ- y) ℚ+ (y ℚ-- z)))     ≡⟨ ap (x ℚ+_) (ℚ+-assoc fe (ℚ- y) y (ℚ- z)) ⁻¹ ⟩
             (x ℚ+ (((ℚ- y) ℚ+ y) ℚ+ (ℚ- z))) ≡⟨ ap (λ k → x ℚ+ (k ℚ+ (ℚ- z))) (ℚ-inverse-sum-to-zero' fe y) ⟩
             (x ℚ+ (zero-ℚ ℚ+ (ℚ- z)))        ≡⟨ ap (λ k → x ℚ+ k) (ℚ-zero-left-neutral fe (ℚ- z)) ⟩
             (x ℚ+ (ℚ- z))                    ≡⟨ by-definition ⟩
             (x ℚ-- z)                        ∎
     -}
  -- | x - y | < ε₁
  -- | y - z | < ε₂
  -- -> | x - z | < ε₁ + ε₂
  -- since | x - z | = | x - y + y - z | < |x - y| + |y - z| < ε₁ + ε₂

{-
ℚ-abs-of-pos-is-pos : (x a : ℕ) → toℚ (pos (succ x) , a) ≡ ℚ-abs (toℚ (pos (succ x) , a))
ℚ-abs-of-pos-is-pos = {!!}
-}

{-
ℚ-abs-pos : (q : ℚ) → zero-ℚ ℚ≤ ℚ-abs q
ℚ-abs-pos ((pos 0 , a) , p)     = inr (equiv-with-lowest-terms-is-equal (pos 0 , 0) (pos 0 , a) I (pr₂ zero-ℚ) p)
 where
  I : (pos 0 , 0) ℚₙ≈ (pos 0 , a)
  I = pos 0 ℤ* pos (succ a) ≡⟨ ℤ-zero-left-is-zero (pos (succ a)) ⟩
         pos 0              ≡⟨ (ℤ-mult-right-id (pos 0)) ⁻¹ ⟩
         pos 0 ℤ* pos 1 ∎
ℚ-abs-pos ((pos (succ x) , a) , p) = inl I
 where
  I : (pos 0 , 0) ℚₙ< (pos (succ x) , a)
  I = (pos (succ x)) , ⋆ , II
   where
    II : (pos 0) ℤ* pos (succ a) ℤ+ pos (succ x) ≡ pos (succ x) ℤ* pos 1
    II = pos 0 ℤ* pos (succ a) ℤ+ pos (succ x) ≡⟨ ap (_ℤ+ pos (succ x)) (ℤ-zero-left-is-zero (pos (succ a))) ⟩
         pos 0 ℤ+ pos (succ x)                 ≡⟨ ℤ-zero-left-neutral (pos (succ x)) ⟩
         pos (succ x)                             ≡⟨ ℤ-mult-right-id (pos (succ x)) ⟩
         pos (succ x) ℤ* pos 1                    ∎
ℚ-abs-pos ((negsucc x , a) , p) = inl (ℚ-zero-less-than-positive x a)
-}

{-
ℚ-abs-pos : (q : ℚ) → zero-ℚ ℚ≤ ℚ-abs q
ℚ-abs-pos ((pos zero , a) , lt)     = inr (pr₁ II)
 where
  I : zero-ℚ ≡ zero-ℚ
  I = numerator-zero-is-zero fe ((pos zero , 0) , pr₂ zero-ℚ) refl

  II : Σ pr ꞉ pr₁ zero-ℚ ≡ (pos zero , 0) , _
  II = from-Σ-≡ I
  
ℚ-abs-pos ((pos (succ x) , a) , lt) = inl ((pos (succ x)) , ⋆ , I)
 where
  I : pos 0 ℤ* pos (succ (pr₂ (pr₁ (ℚ-abs ((pos (succ x) , a) , lt))))) ℤ+ pos (succ x) ≡ pr₁ (pr₁ (ℚ-abs ((pos (succ x) , a) , lt))) ℤ* pos 1
  I = {!!}
ℚ-abs-pos ((negsucc x , a) , lt) = {!!}

ℚ-abs-pos' : (q : ℚ) → zero-ℚ ℚ≤ ℚ-abs q
ℚ-abs-pos' ((x , a) , lt) = {!!}
-}

\end{code}
