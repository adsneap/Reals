Andrew Sneap - 27th April 2021

I link to this module within the Rationals section of my report.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆) --TypeTopology

import DiscreteAndSeparated --TypeTopology
import NaturalsAddition --TypeTopology
import NaturalNumbers-Properties -- TypeTopology
import UF-Base --TypeTopology
import UF-FunExt --TypeTopology
import UF-Miscelanea --TypeTopology
import UF-Subsingletons --TypeTopology

import Integers
import IntegersHCF
import IntegersOrder
import IntegersProperties
import HCF
import MoreNaturalProperties
import NaturalsDivision
import NaturalsMultiplication 

module ncRationals where

open Integers renaming (_*_ to _ℤ*_ ; _+_ to _ℤ+_)

ℚₙ : 𝓤₀ ̇
ℚₙ = ℤ × ℕ

open HCF

is-in-lowest-terms : ℚₙ → 𝓤₀ ̇
is-in-lowest-terms (x , y) = coprime (abs x) (succ y)

open UF-FunExt -- TypeTopology
open UF-Subsingletons --TypeTopology

is-in-lowest-terms-is-prop : Fun-Ext → (q : ℚₙ) → is-prop (is-in-lowest-terms q)
is-in-lowest-terms-is-prop fe (x , y) = coprime-is-prop fe (abs x) (succ y)

open DiscreteAndSeparated --TypeTopology
open IntegersProperties
open UF-Miscelanea --TypeTopology

ℚₙ-is-discrete : is-discrete ℚₙ
ℚₙ-is-discrete = Σ-is-discrete ℤ-is-discrete λ _ → ℕ-is-discrete

ℚₙ-is-set : is-set ℚₙ
ℚₙ-is-set = discrete-types-are-sets ℚₙ-is-discrete

open NaturalsMultiplication renaming (_*_ to _ℕ*_)

_ℚₙ'+_ : ℚₙ → ℚₙ → ℚₙ
(x , a) ℚₙ'+ (y , b) = (x ℤ* pos b) ℤ+ (y ℤ* pos a) , a ℕ* b 

open UF-Base --TypeTopology

ℚₙ'+-comm : (a b : ℚₙ) → a ℚₙ'+ b ≡ b ℚₙ'+ a
ℚₙ'+-comm (x , a) (y , b) = ap₂ (λ z z' → z , z') (ℤ+-comm (x ℤ* pos b) (y ℤ* pos a)) (mult-commutativity a b)

ℚₙ'+-assoc : (a b c : ℚₙ) → (a ℚₙ'+ b) ℚₙ'+ c ≡ a ℚₙ'+ (b ℚₙ'+ c)
ℚₙ'+-assoc (x , y) (x' , y') (x'' , y'') = ap₂ (λ z z' → z , z') I II
 where
  I : (((x ℤ* (pos y')) ℤ+ (x' ℤ* (pos y))) ℤ* pos y'') ℤ+ (x'' ℤ* pos (y ℕ* y')) ≡ (x ℤ* pos (y' ℕ* y'')) ℤ+ (((x' ℤ* pos y'') ℤ+ (x'' ℤ* pos y')) ℤ* pos y)
  I = (x ℤ* pos y' ℤ+ x' ℤ* pos y) ℤ* pos y'' ℤ+ x'' ℤ* pos (y ℕ* y')                  ≡⟨ ap₂ (λ z z' → z ℤ+ z') (distributivity-mult-over-ℤ (x ℤ* pos y') (x' ℤ* pos y) (pos y'')) (ap (x'' ℤ*_) (pos-multiplication-equiv-to-ℕ y y') ⁻¹)                            ⟩
      x ℤ* pos y' ℤ* pos y'' ℤ+ x' ℤ* pos y ℤ* pos y'' ℤ+ x'' ℤ* (pos y ℤ* pos y')     ≡⟨ ℤ+-assoc ((x ℤ* pos y') ℤ* pos y'') ((x' ℤ* pos y) ℤ* pos y'') ((x'' ℤ* (pos y ℤ* pos y')))                                                                                 ⟩ 
      x ℤ* pos y' ℤ* pos y'' ℤ+ (x' ℤ* pos y ℤ* pos y'' ℤ+ x'' ℤ* (pos y ℤ* pos y'))   ≡⟨ ap₂ (λ z z' → z ℤ+ z') (ℤ*-assoc x (pos y') (pos y'') ⁻¹) (ap₂ (λ z z' → z ℤ+ z') (ap (_ℤ* pos y'') (ℤ*-comm x' (pos y))) (ap (x'' ℤ*_) (ℤ*-comm (pos y) (pos y'))))         ⟩
      x ℤ* (pos y' ℤ* pos y'') ℤ+ (pos y ℤ* x' ℤ* pos y'' ℤ+ x'' ℤ* (pos y' ℤ* pos y)) ≡⟨ ap₂ (λ z z' → z ℤ+ z') (ap (x ℤ*_) (pos-multiplication-equiv-to-ℕ y' y'')) (ap₂ (λ z z' → z ℤ+ z') (ap (_ℤ* pos y'') (ℤ*-comm (pos y) x')) (ℤ*-assoc x'' (pos y') (pos y)))  ⟩
      x ℤ* pos (y' ℕ* y'') ℤ+ (x' ℤ* pos y ℤ* pos y'' ℤ+ x'' ℤ* pos y' ℤ* pos y)       ≡⟨ ap ((x ℤ* pos (y' ℕ* y'')) ℤ+_) (ap₂ (λ z z' → z ℤ+ z') (ap (_ℤ* pos y'') (ℤ*-comm x' (pos y))) (ℤ*-comm (x'' ℤ* pos y') (pos y)))                                          ⟩
      x ℤ* pos (y' ℕ* y'') ℤ+ (pos y ℤ* x' ℤ* pos y'' ℤ+ pos y ℤ* (x'' ℤ* pos y'))     ≡⟨ ap (λ z →  ((x ℤ* pos (y' ℕ* y'')) ℤ+ (z ℤ+ (pos y ℤ* (x'' ℤ* pos y'))))) (ℤ*-assoc (pos y) x' (pos y'') ⁻¹)                                                                ⟩
      x ℤ* pos (y' ℕ* y'') ℤ+ (pos y ℤ* (x' ℤ* pos y'') ℤ+ pos y ℤ* (x'' ℤ* pos y'))   ≡⟨ ap ((x ℤ* pos (y' ℕ* y'')) ℤ+_) (distributivity-mult-over-ℤ' (x' ℤ* pos y'') (x'' ℤ* pos y') (pos y) ⁻¹)                                                                    ⟩
      x ℤ* pos (y' ℕ* y'') ℤ+ pos y ℤ* (x' ℤ* pos y'' ℤ+ x'' ℤ* pos y')                ≡⟨ ap ((x ℤ* pos (y' ℕ* y'')) ℤ+_) (ℤ*-comm (pos y) ((x' ℤ* pos y'') ℤ+ (x'' ℤ* pos y')))                                                                                      ⟩
      x ℤ* pos (y' ℕ* y'') ℤ+ (x' ℤ* pos y'' ℤ+ x'' ℤ* pos y') ℤ* pos y                ∎ 

  II : y ℕ* y' ℕ* y'' ≡ y ℕ* (y' ℕ* y'')
  II = mult-associativity y y' y''

open NaturalNumbers-Properties  --TypeTopology

_+_ : ℚₙ → ℚₙ → ℚₙ
(x , y) + (x' , y') = f ((x , succ y) ℚₙ'+ (x' , succ y')) --(x ℤ* pos (succ y')) ℤ+ (x' ℤ* pos (succ y)) , pred (succ y ℕ* succ y')
 where
  f : ℚₙ → ℚₙ
  f (a , b) = a , (pred b)

open NaturalsAddition renaming (_+_ to _ℕ+_) --TypeTopology
open MoreNaturalProperties 

ℚₙ+-comm : (p q : ℚₙ) → p + q ≡ q + p
ℚₙ+-comm (x , a) (y , b) = ap₂ _,_ (ap pr₁ e) (ap pred (ap pr₂ e))
 where
  e : ((x , succ a) ℚₙ'+ (y , succ b)) ≡ ((y , succ b) ℚₙ'+ (x , succ a))
  e = ℚₙ'+-comm (x , (succ a)) (y , (succ b))
    
ℚₙ+-assoc-lemma : (x y : ℕ) → Σ z ꞉ ℕ , succ z ≡ (succ x) ℕ* (succ y) 
ℚₙ+-assoc-lemma x = induction base step
 where
  base : Σ z ꞉ ℕ , succ z ≡ succ x ℕ* 1
  base = x , refl

  step : (k : ℕ)
       → Σ z ꞉ ℕ , succ z ≡ succ x ℕ* succ k
       → Σ z ꞉ ℕ , succ z ≡ succ x ℕ* succ (succ k)
  step k (z , p) = (x ℕ+ 1) ℕ+ z , I
   where
    I : succ (x ℕ+ 1 ℕ+ z) ≡ succ x ℕ* succ (succ k)
    I = succ (x ℕ+ 1 ℕ+ z) ≡⟨ addition-right-succ (succ x) z ⁻¹ ⟩
        succ x ℕ+ succ z                     ≡⟨ ap (succ x ℕ+_) p ⟩
        succ x ℕ+ (succ x ℕ+ succ x ℕ* k)    ≡⟨ refl              ⟩
        succ x ℕ* succ (succ k)              ∎

denom-setup : (a b : ℕ) →  pos (succ (pred (succ a ℕ* succ b))) ≡ pos (succ a) ℤ* pos (succ b)
denom-setup a b = pos (succ (pred (succ a ℕ* succ b))) ≡⟨ ap pos (succ-pred-multiplication a b ⁻¹) ⟩
                  pos (succ a ℕ* succ b)               ≡⟨ pos-multiplication-equiv-to-ℕ (succ a) (succ b) ⁻¹ ⟩
                  pos (succ a) ℤ* pos (succ b) ∎

ℚₙ+-assoc : (a b c : ℚₙ) → (a + b) + c ≡ a + (b + c)
ℚₙ+-assoc (x , a) (y , b) (z , c) = ap₂ _,_ I II
 where
  left : ℚₙ
  left = (x , a) + (y , b)
  
  right : ℚₙ
  right = (y , b) + (z , c)

  α δ : ℤ
  α = pr₁ left
  δ = pr₁ right

  β γ : ℕ
  β = pr₂ left
  γ = pr₂ right

  e : (((x , succ a) ℚₙ'+ (y , succ b)) ℚₙ'+ (z , succ c)) ≡ ((x , succ a) ℚₙ'+ ((y , succ b) ℚₙ'+ (z , succ c)))
  e = (ℚₙ'+-assoc (x , (succ a)) (y , succ b) (z , succ c))
  
  I : α ℤ* pos (succ c) ℤ+ z ℤ* pos (succ (pred (succ a ℕ* succ b))) ≡ x ℤ* pos (succ (pred (succ b ℕ* succ c))) ℤ+ δ ℤ* pos (succ a)
  I = α ℤ* pos (succ c) ℤ+ z ℤ* pos (succ (pred (succ a ℕ* succ b))) ≡⟨ ap (λ - → α ℤ* pos (succ c) ℤ+ z ℤ* pos -) ((succ-pred-multiplication a b ⁻¹)) ⟩
      α ℤ* pos (succ c) ℤ+ z ℤ* pos (succ a ℕ* succ b)                 ≡⟨ ap pr₁ e ⟩
      x ℤ* pos (succ b ℕ* succ c) ℤ+ δ ℤ* pos (succ a)                 ≡⟨ ap (λ - →  x ℤ* pos - ℤ+ δ ℤ* pos (succ a)) (succ-pred-multiplication b c) ⟩
      x ℤ* pos (succ (pred (succ b ℕ* succ c))) ℤ+ δ ℤ* pos (succ a) ∎

  II : pred (succ (pred (succ a ℕ* (succ b))) ℕ* succ c) ≡ pred (succ a ℕ* succ (pred (succ b ℕ+ succ b ℕ* c)))
  II = pred (succ (pred (succ a ℕ* succ b)) ℕ* succ c) ≡⟨ ap (λ - → pred (- ℕ* succ c)) (succ-pred-multiplication a b ⁻¹) ⟩
       pred ((succ a ℕ* succ b) ℕ* succ c) ≡⟨ ap pred (ap pr₂ e) ⟩
       pred (succ a ℕ* (succ b ℕ* succ c)) ≡⟨ ap (λ - → pred (succ a ℕ* -)) (succ-pred-multiplication b c) ⟩
       pred (succ a ℕ* succ (pred (succ b ℕ* succ c))) ∎

open IntegersOrder renaming (_<_ to _ℤ<_ ; _>_ to _ℤ>_) 

_<_ _>_ : ℚₙ → ℚₙ → 𝓤₀ ̇
(x , a) < (y , b) = (x ℤ* pos (succ b)) ℤ< (y ℤ* pos (succ a))
p > q = q < p

ℚₙ<-is-prop : (p q : ℚₙ) → is-prop (p < q)
ℚₙ<-is-prop (x , a) (y , b) = ℤ<-is-prop (x ℤ* pos (succ b)) (y ℤ* pos (succ a))

ℚₙ-trans : (p q r : ℚₙ) → p < q → q < r → p < r
ℚₙ-trans (x , a) (y , b) (z , c) α β = ordering-right-cancellable (x ℤ* pos (succ c)) (z ℤ* pos (succ a)) (pos (succ b)) ⋆ I
 where
  I : ((x ℤ* pos (succ c)) ℤ* pos (succ b)) ℤ< ((z ℤ* pos (succ a)) ℤ* pos (succ b))
  I = ℤ<-trans ((x ℤ* pos (succ c)) ℤ* pos (succ b)) ((y ℤ* pos (succ a)) ℤ* pos (succ c)) ((z ℤ* pos (succ a)) ℤ* pos (succ b)) i ii
   where
    i : ((x ℤ* pos (succ c)) ℤ* pos (succ b)) ℤ< ((y ℤ* pos (succ a)) ℤ+ ((y ℤ* pos (succ a)) ℤ* pos c))
    i = transport (λ z → z ℤ< ((y ℤ* pos (succ a)) ℤ+ ((y ℤ* pos (succ a)) ℤ* pos c))) ϕ θ
     where
      ϕ : ((x ℤ* pos (succ b)) ℤ* pos (succ c)) ≡ ((x ℤ* pos (succ c)) ℤ* pos (succ b))
      ϕ = ℤ-mult-rearrangement x (pos (succ b)) (pos (succ c))

      θ : ((x ℤ* pos (succ b)) ℤ* pos (succ c)) ℤ< ((y ℤ* pos (succ a)) ℤ* pos (succ c))
      θ = positive-multiplication-preserves-order (x ℤ* pos (succ b)) (y ℤ* pos (succ a)) (pos (succ c)) ⋆ α
    ii : ((y ℤ* pos (succ a)) ℤ* pos (succ c)) ℤ< ((z ℤ* pos (succ a)) ℤ* pos (succ b))
    ii = transport₂ (λ s s' → s ℤ< s') γ₁ γ₂ γ₃
     where
      γ₁ : ((y ℤ* pos (succ c)) ℤ* pos (succ a)) ≡ ((y ℤ* pos (succ a)) ℤ* pos (succ c))
      γ₁ = ℤ-mult-rearrangement y (pos (succ c)) (pos (succ a))

      γ₂ : ((z ℤ* pos (succ b)) ℤ* pos (succ a)) ≡ ((z ℤ* pos (succ a)) ℤ* pos (succ b))
      γ₂ = ℤ-mult-rearrangement z (pos (succ b)) (pos (succ a))

      γ₃ : ((y ℤ* pos (succ c)) ℤ* pos (succ a)) ℤ< ((z ℤ* pos (succ b)) ℤ* pos (succ a))
      γ₃ = positive-multiplication-preserves-order (y ℤ* pos (succ c)) (z ℤ* pos (succ b)) (pos (succ a)) ⋆ β

ℚₙ-less-than-pos-addition : (p (y , b) : ℚₙ) → greater-than-zero y → p < (p + (y , b))
ℚₙ-less-than-pos-addition (x , a) (y , b) p = f (III) 
 where
  a' b' : ℤ
  a' = pos (succ a)
  b' = pos (succ b)

  III : Σ c ꞉ ℤ , greater-than-zero c × (x ℤ* (a' ℤ* b') ℤ+ c ≡ x ℤ* (a' ℤ* b') ℤ+ (y ℤ* a') ℤ* a')
  III = ℤ<-less-than-pos-addition (x ℤ* (a' ℤ* b')) ((y ℤ* a') ℤ* a') (greater-than-zero-mult-trans (y ℤ* a') (a') (greater-than-zero-mult-trans y (a') p (pos-succ-greater-than-zero a)) (pos-succ-greater-than-zero a))

  f : Σ c ꞉ ℤ , greater-than-zero c × (x ℤ* (a' ℤ* b') ℤ+ c ≡ x ℤ* (a' ℤ* b') ℤ+ (y ℤ* a') ℤ* a')
    → Σ c ꞉ ℤ , greater-than-zero c × (x ℤ* pos (succ (pred (succ a ℕ* succ b))) ℤ+ c ≡ (x ℤ* b' ℤ+ (y ℤ* a')) ℤ* a')
  f (c , (g , p)) = c , g , transport₂ (λ z z' → z ≡ z') IV V p
   where
    VI : succ (pred (succ a ℕ* succ b)) ≡ succ a ℕ* succ b
    VI = succ-pred-multiplication a b ⁻¹

    IV : x ℤ* (a' ℤ* b') ℤ+ c ≡ x ℤ* pos (succ (pred (succ a ℕ* succ b))) ℤ+ c
    IV = x ℤ* (a' ℤ* b') ℤ+ c        ≡⟨ ap (λ z → x ℤ* z ℤ+ c) (pos-multiplication-equiv-to-ℕ (succ a) (succ b)) ⟩
         x ℤ* pos (succ a ℕ* succ b) ℤ+ c                ≡⟨ ap (λ z → (x ℤ* z) ℤ+ c) (ap pos (VI ⁻¹)) ⟩
         x ℤ* pos (succ (pred (succ a ℕ* succ b))) ℤ+ c ∎

    V : x ℤ* (a' ℤ* b') ℤ+ y ℤ* a' ℤ* a' ≡ (x ℤ* b' ℤ+ y ℤ* a') ℤ* a'
    V = x ℤ* (a' ℤ* b') ℤ+ y ℤ* a' ℤ* a' ≡⟨ ap (λ z → x ℤ* z ℤ+ y ℤ* a' ℤ* a') (ℤ*-comm (a') (b')) ⟩
        x ℤ* (b' ℤ* a') ℤ+ y ℤ* a' ℤ* a' ≡⟨  ap (_ℤ+ y ℤ* a' ℤ* a') (ℤ*-assoc x (b') (a')) ⟩
        (x ℤ* b') ℤ* a' ℤ+ y ℤ* a' ℤ* a' ≡⟨ distributivity-mult-over-ℤ (x ℤ+ x ℤ* pos b) (y ℤ+ y ℤ* pos a) (a') ⁻¹ ⟩
        (x ℤ* b' ℤ+ y ℤ* a') ℤ* a'                 ∎

_*_ : ℚₙ → ℚₙ → ℚₙ
(x , a) * (y , b) = (x ℤ* y) , (pred (succ a ℕ* succ b))

infixl 33 _+_
infixl 34 _*_

ℚₙ*-comm : (p q : ℚₙ) → p * q ≡ q * p
ℚₙ*-comm (x , a) (y , b) = ap₂ _,_ I II
 where
  I : x ℤ* y ≡ y ℤ* x
  I = ℤ*-comm x y

  II : pred (succ a ℕ* succ b) ≡ pred (succ b ℕ* succ a)
  II = ap pred (mult-commutativity (succ a) (succ b))

ℚₙ*-assoc : (p q r : ℚₙ) → (p * q) * r ≡ p * (q * r)
ℚₙ*-assoc (x , a) (y , b) (z , c) = ap₂ _,_ I II
 where
  I : x ℤ* y ℤ* z ≡ x ℤ* (y ℤ* z)
  I = ℤ*-assoc x y z ⁻¹

  a' b' c' : ℕ
  a' = succ a
  b' = succ b
  c' = succ c

  II : pred (succ (pred (a' ℕ* b')) ℕ* c') ≡ pred (a' ℕ* succ (pred (b' ℕ* c')))
  II = pred (succ (pred (a' ℕ* b')) ℕ* c') ≡⟨ ap (λ - → pred (- ℕ* c')) (succ-pred-multiplication a b ⁻¹) ⟩
       pred ((a' ℕ* b') ℕ* c') ≡⟨ ap pred (mult-associativity a' b' c') ⟩
       pred (a' ℕ* (b' ℕ* c')) ≡⟨ ap (λ - → pred (a' ℕ* -)) (succ-pred-multiplication b c) ⟩
       pred (a' ℕ* succ (pred (b' ℕ* c'))) ∎

ℚₙ-zero-right-neutral : (q : ℚₙ) → q + (pos 0 , 0) ≡ q
ℚₙ-zero-right-neutral (x , a) = (x , a) + (pos 0 , 0)                ≡⟨ refl ⟩
                                 x ℤ+ (pos 0 ℤ* pos (succ a)) , a    ≡⟨ ap (λ - → x ℤ+ - , a) (ℤ*-comm (pos 0) (pos (succ a))) ⟩
                                 x ℤ+ pos 0 , a                      ≡⟨ ap (λ - → - , a) refl ⟩
                                 x , a ∎

ℚₙ-mult-left-id : (q : ℚₙ) → (pos 1 , 0) * q ≡ q
ℚₙ-mult-left-id (x , a) = (pos 1 , 0) * (x , a)             ≡⟨ refl ⟩
                          pos 1 ℤ* x , pred (1 ℕ* succ a) ≡⟨ ap₂ (λ l r → l , pred r) (ℤ-mult-left-id x) (mult-left-id (succ a)) ⟩
                          x , pred (succ a)                ≡⟨ ap (λ - → x , -) refl ⟩
                          x , a                             ∎

_ℚₙℕ*_ : (p : ℚₙ) → (x : ℕ) → ℚₙ
p ℚₙℕ* x = p * ((pos (succ x)) , x)

_ℚₙ≈_ : (p q : ℚₙ) → 𝓤₀ ̇
(x , a) ℚₙ≈ (y , b) = x ℤ* pos (succ b) ≡ (y ℤ* pos (succ a))

open NaturalsDivision
open IntegersHCF

equiv-with-lowest-terms-is-equal : (a b : ℚₙ) -> a ℚₙ≈ b → is-in-lowest-terms a → is-in-lowest-terms b → a ≡ b
equiv-with-lowest-terms-is-equal (x , a) (y , b) e ((m₁ , m₂) , n) ((m₁' , m₂') , n') = to-×-≡ xyequal abequal
 where
  e' : (x ℤ* pos (succ b)) ≡ (y ℤ* pos (succ a))
  e' = e

  γ : abs (x ℤ* pos (succ b)) ≡ abs (y ℤ* pos (succ a))
  γ = ap abs e'

  δ : abs x ℕ* succ b ≡ abs y ℕ* succ a
  δ = abs x ℕ* abs (pos (succ b)) ≡⟨ abs-over-mult x (pos (succ b))  ⁻¹ ⟩
      abs (x ℤ* pos (succ b))     ≡⟨ γ ⟩
      abs (y ℤ* pos (succ a))     ≡⟨ abs-over-mult y (pos (succ a)) ⟩
      abs y ℕ* abs (pos (succ a)) ∎
 
  s : (succ a) ∣ ((abs x) ℕ* (succ b))
  s = (abs y) , I
   where
    I : succ a ℕ* abs y ≡ abs x ℕ* succ b
    I = succ a ℕ* abs y ≡⟨ mult-commutativity (succ a) (abs y) ⟩
        abs y ℕ* succ a ≡⟨ δ ⁻¹ ⟩
        abs x ℕ* succ b ∎

  s' : (succ b) ∣ (abs y) ℕ* (succ a)
  s' = (abs x) , I
   where
    I : succ b ℕ* abs x ≡ abs y ℕ* succ a
    I = succ b ℕ* abs x ≡⟨ mult-commutativity (succ b) (abs x) ⟩
        abs x ℕ* succ b ≡⟨ δ ⟩
        abs y ℕ* succ a ∎

  a-divides-b : (succ a) ∣ (succ b)
  a-divides-b = coprime-with-division (succ a) (abs x) (succ b) ((m₂ , m₁) , λ f' (h₁ , h₂) → n f' (h₂ , h₁)) s

  b-divides-a : (succ b) ∣ (succ a)
  b-divides-a = coprime-with-division (succ b) (abs y) (succ a) ((m₂' , m₁') , λ f (h₁ , h₂) → n' f (h₂ , h₁)) s'

  abequal : a ≡ b
  abequal = succ-lc (∣-anti (succ a) (succ b) a-divides-b b-divides-a)

  e'' : x ℤ* pos (succ a) ≡ y ℤ* pos (succ a)
  e'' = ap (x ℤ*_) (ap pos (ap succ abequal)) ∙ e

  xyequal : x ≡ y
  xyequal = ℤ-mult-right-cancellable x y (pos (succ a)) (λ z → z) e''

≈-refl : (q : ℚₙ) → q ℚₙ≈ q
≈-refl q = refl

≈-sym : (p q : ℚₙ) → p ℚₙ≈ q → q ℚₙ≈ p
≈-sym p q e = e ⁻¹

≈-trans : (p q r : ℚₙ) → p ℚₙ≈ q → q ℚₙ≈ r → p ℚₙ≈ r
≈-trans (x , a) (y , b) (z , c) e₁ e₂ = ℤ-mult-left-cancellable (x ℤ* pos (succ c)) (z ℤ* pos (succ a)) (pos (succ b)) (pos-succ-not-zero b) III
 where
  I : x ℤ* pos (succ b) ℤ* pos (succ c) ≡ y ℤ* pos (succ a) ℤ* pos (succ c)
  I = ap (_ℤ* pos (succ c)) e₁

  II : pos (succ a) ℤ* (y ℤ* pos (succ c)) ≡ pos (succ a) ℤ* (z ℤ* pos (succ b))
  II = ap (pos (succ a) ℤ*_) e₂

  III : pos (succ b) ℤ* (x ℤ* pos (succ c)) ≡ pos (succ b) ℤ* (z ℤ* pos (succ a))
  III = pos (succ b) ℤ* (x ℤ* pos (succ c)) ≡⟨ ℤ*-assoc (pos (succ b)) x (pos (succ c)) ⟩
        pos (succ b) ℤ* x ℤ* pos (succ c) ≡⟨ ap (_ℤ* pos (succ c)) (ℤ*-comm (pos (succ b)) x) ⟩
        x ℤ* pos (succ b) ℤ* pos (succ c) ≡⟨ I ⟩
        y ℤ* pos (succ a) ℤ* pos (succ c) ≡⟨ ap (_ℤ* pos (succ c)) (ℤ*-comm y (pos (succ a))) ⟩
        pos (succ a) ℤ* y ℤ* pos (succ c) ≡⟨ ℤ*-assoc (pos (succ a)) y (pos (succ c))  ⁻¹ ⟩
        pos (succ a) ℤ* (y ℤ* pos (succ c)) ≡⟨ II ⟩
        pos (succ a) ℤ* (z ℤ* pos (succ b)) ≡⟨ ℤ-mult-rearrangement' z (pos (succ b)) (pos (succ a)) ⟩
        pos (succ b) ℤ* (z ℤ* pos (succ a)) ∎

≈-addition : (p q r : ℚₙ) → p ℚₙ≈ q → (p + r) ℚₙ≈ (q + r)
≈-addition (x , a) (y , b) (z , c) e₁ = III
 where
  I :  pos (succ (pred (succ b ℕ* succ c))) ≡ pos (succ b) ℤ* pos (succ c)
  I = denom-setup b c

  II : pos (succ a) ℤ* pos (succ c) ≡ pos (succ (pred (succ a ℕ* succ c)))
  II = denom-setup a c ⁻¹

  a' b' c' : ℤ
  a' = pos (succ a)
  b' = pos (succ b)
  c' = pos (succ c)

  III : ((x , a) + (z , c)) ℚₙ≈ ((y , b) + (z , c))
  III = (x ℤ* c' ℤ+ (z ℤ* a')) ℤ* pos (succ (pred (succ b ℕ* succ c))) ≡⟨ ap (λ - → (x ℤ* c' ℤ+ (z ℤ* a')) ℤ* -) I ⟩
        (x ℤ* c' ℤ+ z ℤ* a') ℤ* (b' ℤ* c')                             ≡⟨ distributivity-mult-over-ℤ (x ℤ* c') (z ℤ* a') (b' ℤ* c') ⟩
         x ℤ* c' ℤ* (b' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                ≡⟨ ap₂ _ℤ+_ (ℤ-mult-rearrangement x (c') (b' ℤ* c')) (ℤ-mult-rearrangement z (a') (b' ℤ* c'))  ⟩
         x ℤ* (b' ℤ* c') ℤ* c' ℤ+ z ℤ* (b' ℤ* c') ℤ* a'                ≡⟨ ap₂ _ℤ+_ (ap (_ℤ* c') (ℤ*-assoc x b' c')) (ap (_ℤ* a') (ℤ*-assoc z b' c')) ⟩
         x ℤ* b' ℤ* c' ℤ* c' ℤ+ z ℤ* b' ℤ* c' ℤ* a'                    ≡⟨ ap₂ _ℤ+_ (ap (λ - → -  ℤ* c' ℤ* c') e₁) (ℤ*-assoc (z ℤ* b') c' a' ⁻¹) ⟩
         y ℤ* a' ℤ* c' ℤ* c' ℤ+ z ℤ* b' ℤ* (c' ℤ* a')                  ≡⟨ ap₂ _ℤ+_ (ap (_ℤ* c') (ℤ-mult-rearrangement y a' c')) (ap (λ - → z ℤ* b' ℤ* -) (ℤ*-comm c' a')) ⟩
         y ℤ* c' ℤ* a' ℤ* c' ℤ+ z ℤ* b' ℤ* (a' ℤ* c')                  ≡⟨ ap (_ℤ+ z ℤ* b' ℤ* (a' ℤ* c')) (ℤ*-assoc (y ℤ* c') a' c' ⁻¹) ⟩
         y ℤ* c' ℤ* (a' ℤ* c') ℤ+ z ℤ* b' ℤ* (a' ℤ* c')                ≡⟨ distributivity-mult-over-ℤ (y ℤ* c') (z ℤ* b') (a' ℤ* c') ⁻¹ ⟩
        (y ℤ* c' ℤ+ z ℤ* b') ℤ* (a' ℤ* c')                             ≡⟨ ap (λ - → (y ℤ* c' ℤ+ (z ℤ* b')) ℤ* -) II ⟩
        (y ℤ* c' ℤ+ (z ℤ* b')) ℤ* pos (succ (pred (succ a ℕ* succ c))) ∎

≈-addition-comm : (p q : ℚₙ) → (p + q) ℚₙ≈ (q + p)
≈-addition-comm (x , a) (y , b) = I
 where
  I : ((x , a) + (y , b)) ℚₙ≈ ((y , b) + (x , a))
  I = (x ℤ* pos (succ b) ℤ+ y ℤ* pos (succ a)) ℤ* pos (succ (pred (succ b ℕ* succ a))) ≡⟨ ap₂ _ℤ*_ (ℤ+-comm (x ℤ* pos (succ b)) (y ℤ* pos (succ a))) (ap (λ - → pos (succ (pred -))) (mult-commutativity (succ b) (succ a))) ⟩
      (y ℤ* pos (succ a) ℤ+ x ℤ* pos (succ b)) ℤ* pos (succ (pred (succ a ℕ* succ b))) ∎

≈-over-* : (p q r : ℚₙ) → p ℚₙ≈ q → (p * r) ℚₙ≈ (q * r)
≈-over-* (x , a) (y , b) (z , c) e = I
 where
  a' b' c' : ℤ
  a' = pos (succ a)
  b' = pos (succ b)
  c' = pos (succ c)

  I : x ℤ* z ℤ* pos (succ (pred (succ b ℕ* succ c))) ≡ y ℤ* z ℤ* pos (succ (pred (succ a ℕ* succ c)))
  I = x ℤ* z ℤ* pos (succ (pred (succ b ℕ* succ c))) ≡⟨ ap (λ - → x ℤ* z ℤ* -) (denom-setup b c) ⟩
      x ℤ* z ℤ* (b' ℤ* c')                           ≡⟨ ℤ*-assoc (x ℤ* z) b' c' ⟩
      x ℤ* z ℤ* b' ℤ* c'                             ≡⟨ ap (_ℤ* c') (ℤ-mult-rearrangement x z b') ⟩
      x ℤ* b' ℤ* z ℤ* c'                             ≡⟨ ap (λ - → - ℤ* z ℤ* c') e ⟩
      y ℤ* a' ℤ* z ℤ* c'                             ≡⟨ ap (_ℤ* c') (ℤ*-assoc y a' z ⁻¹ ) ⟩
      y ℤ* (a' ℤ* z) ℤ* c'                           ≡⟨ ap (λ - → y ℤ* - ℤ* c') (ℤ*-comm a' z) ⟩
      y ℤ* (z ℤ* a') ℤ* c'                           ≡⟨ ap (_ℤ* c') (ℤ*-assoc y z a') ⟩
      y ℤ* z ℤ* a' ℤ* c'                             ≡⟨ ℤ*-assoc (y ℤ* z) a' c' ⁻¹ ⟩ 
      y ℤ* z ℤ* (a' ℤ* c')                           ≡⟨ ap (λ - → (y ℤ* z ℤ* -)) (denom-setup a c ⁻¹) ⟩
      y ℤ* z ℤ* pos (succ (pred (succ a ℕ* succ c))) ∎

half-ℚₙ : ℚₙ → ℚₙ
half-ℚₙ (x , a) = x , (succ (2 ℕ* a))

ℚ-dist-lemma : (p q r : ℚₙ) → p * (q + r) ℚₙ≈ (p * q + p * r)
ℚ-dist-lemma (x , a) (y , b) (z , c) = I
 where
  a' b' c' : ℕ
  a' = succ a
  b' = succ b
  c' = succ c

  a'' b'' c'' : ℤ
  a'' = pos a'
  b'' = pos b'
  c'' = pos c'

  I-lemma : (x y p q : ℤ) → x ℤ* y ℤ* (p ℤ* q) ≡ x ℤ* p ℤ* (y ℤ* q)
  I-lemma x y p q = x ℤ* y ℤ* (p ℤ* q) ≡⟨ ℤ*-assoc (x ℤ* y) p q ⟩
                    x ℤ* y ℤ* p ℤ* q   ≡⟨ ap (_ℤ* q) (ℤ*-assoc x y p ⁻¹) ⟩
                    x ℤ* (y ℤ* p) ℤ* q ≡⟨ ap (λ - → x ℤ* - ℤ* q) (ℤ*-comm y p) ⟩
                    x ℤ* (p ℤ* y) ℤ* q ≡⟨ ap (_ℤ* q) (ℤ*-assoc x p y) ⟩
                    x ℤ* p ℤ* y ℤ* q   ≡⟨ ℤ*-assoc (x ℤ* p) y q ⁻¹ ⟩
                    x ℤ* p ℤ* (y ℤ* q) ∎

  I : _ ≡ _
  I = 
      x ℤ* (  y ℤ* c'' ℤ+ (z ℤ* b'')  )                                                        ℤ*      pos (succ (pred    (succ (pred (a' ℕ* b'))   ℕ*   (succ (pred (a' ℕ* c'))))))            ≡⟨ i ⟩
      x ℤ* (  y ℤ* c'' ℤ+ (z ℤ* b'')  )                                                        ℤ*  (   pos (succ (pred    (a' ℕ* b')))              ℤ*    pos (succ (pred (a' ℕ* c')))   )      ≡⟨ ii ⟩
      x ℤ* (  y ℤ* c'' ℤ+ (z ℤ* b'')  )                                                        ℤ*  (   pos (a' ℕ* b')                               ℤ*    pos (a' ℕ* c')                 )      ≡⟨ iii ⟩
      x ℤ* (  y ℤ* c'' ℤ+ (z ℤ* b'')  )                                                        ℤ*  (   (    a'' ℤ* b'' )  ℤ*   (a'' ℤ* c'') )                                                   ≡⟨ iv ⟩
      x ℤ* (  y ℤ* c'' ℤ+ (z ℤ* b'')  )                                                        ℤ*  (   a''  ℤ*                      ( b'' ℤ*   (a'' ℤ* c'')  )       )                           ≡⟨ v ⟩
      x ℤ* (  y ℤ* c'' ℤ+ (z ℤ* b'') ) ℤ* a''                                                  ℤ*  (                                         ( b'' ℤ*   (a'' ℤ* c'')  )       )        ≡⟨ vi ⟩
      x ℤ* a'' ℤ* (  y ℤ* c'' ℤ+ (z ℤ* b'') )                                                  ℤ*  (                                         ( a'' ℤ*   (b'' ℤ* c'')  )       )        ≡⟨ vii ⟩
     (x ℤ* a'' ℤ* (y ℤ* c'')    ℤ+    x ℤ* a'' ℤ* (z ℤ* b''))                                  ℤ*  (               ( a'' ℤ*   (pos (b' ℕ* c'))        )       )                              ≡⟨ viii ⟩
     (x ℤ* y ℤ* (a'' ℤ* c'')       ℤ+  x ℤ* z ℤ* (a'' ℤ* b''))                                 ℤ*  (               ( a'' ℤ*   (pos (b' ℕ* c'))        )       )                              ≡⟨ ix ⟩
     (x ℤ* y ℤ* pos (succ (pred (a' ℕ* c'))) ℤ+ (x ℤ* z ℤ* pos (succ (pred (a' ℕ* b')))))      ℤ*      (       ( a'' ℤ*   (pos (b' ℕ* c'))        )    )                                     ≡⟨ xi ⟩
     (x ℤ* y ℤ* pos (succ (pred (a' ℕ* c'))) ℤ+ (x ℤ* z ℤ* pos (succ (pred (a' ℕ* b')))))      ℤ*      pos (a' ℕ* (b' ℕ* c'))                                                                   ≡⟨ xii ⟩
     (x ℤ* y ℤ* pos (succ (pred (a' ℕ* c'))) ℤ+ (x ℤ* z ℤ* pos (succ (pred (a' ℕ* b')))))      ℤ*      pos (a' ℕ* succ (pred (b' ℕ* c')))                                                       ≡⟨ xiii ⟩
     (x ℤ* y ℤ* pos (succ (pred (a' ℕ* c'))) ℤ+ (x ℤ* z ℤ* pos (succ (pred (a' ℕ* b')))))      ℤ*      (pos (succ (pred (a' ℕ* succ (pred (b' ℕ* c')))))) ∎
   where
    i  = ap (λ β → x ℤ* (y ℤ* c'' ℤ+ (z ℤ* b'')) ℤ* β ) (denom-setup (pred (a' ℕ* b')) (pred (a' ℕ* c')))
    ii = ap₂ (λ α β → x ℤ* (y ℤ* c'' ℤ+ (z ℤ* b'')) ℤ* (pos α ℤ* pos β)) (succ-pred-multiplication a b ⁻¹) (succ-pred-multiplication a c ⁻¹)
    iii = ap₂ (λ α β → x ℤ* (y ℤ* c'' ℤ+ (z ℤ* b'')) ℤ* (α ℤ* β) ) (pos-multiplication-equiv-to-ℕ a' b' ⁻¹) (pos-multiplication-equiv-to-ℕ a' c' ⁻¹)
    iv = ap (λ α → x ℤ* (y ℤ* c'' ℤ+ (z ℤ* b'')) ℤ* α ) (ℤ*-assoc a'' b'' ( a'' ℤ* c'') ⁻¹)
    v = ℤ*-assoc (x ℤ* (  y ℤ* c'' ℤ+ (z ℤ* b'')  )) a'' ( b'' ℤ*   (a'' ℤ* c''))
    vi = ap₂ (λ α β → α ℤ* β) (ℤ-mult-rearrangement x ( y ℤ* c'' ℤ+ (z ℤ* b'')) a'') (ℤ-mult-rearrangement''' b'' a'' c'')
    vii = ap₂ (λ α β → α ℤ* (a'' ℤ* β)) (distributivity-mult-over-ℤ' (y ℤ* c'') (z ℤ* b'') (x ℤ* a'')) (pos-multiplication-equiv-to-ℕ b' c')
    viii = ap₂ (λ α β → (α ℤ+ β) ℤ* ((a'' ℤ* (pos (b' ℕ* c'))))) (I-lemma x a'' y c'') (I-lemma x a'' z b'')
    ix = ap₂ (λ α β → (x ℤ* y ℤ* α ℤ+ x ℤ* z ℤ* β) ℤ* ((a'' ℤ* (pos (b' ℕ* c'))))) (denom-setup a c ⁻¹) (denom-setup a b ⁻¹)
    xi = ap (λ α → (x ℤ* y ℤ* pos (succ (pred (a' ℕ* c'))) ℤ+ (x ℤ* z ℤ* pos (succ (pred (a' ℕ* b'))))) ℤ* α) (pos-multiplication-equiv-to-ℕ a' (b' ℕ* c'))
    xii = ap  (λ α → (x ℤ* y ℤ* pos (succ (pred (a' ℕ* c'))) ℤ+ (x ℤ* z ℤ* pos (succ (pred (a' ℕ* b'))))) ℤ* (pos (a' ℕ* α))) (succ-pred-multiplication b c)
    xiii = ap (λ α → (x ℤ* y ℤ* pos (succ (pred (a' ℕ* c'))) ℤ+ (x ℤ* z ℤ* pos (succ (pred (a' ℕ* b'))))) ℤ* pos α) (succ-pred-multiplication a (pred (b' ℕ* c')))

ℚₙ-addition-preserves-order : (p q r : ℚₙ) → p < q → (p + r) < (q + r)
ℚₙ-addition-preserves-order (x , a) (y , b) (z , c) (n , g , l) = (c' ℤ* c' ℤ* n) , δ , γ
 where
  a' b' c' : ℤ
  a' = pos (succ a)
  b' = pos (succ b)
  c' = pos (succ c)
  
  δ : greater-than-zero (c' ℤ* c' ℤ* n)
  δ = greater-than-zero-mult-trans (c' ℤ* c') n ε g
   where
    ε : greater-than-zero (c' ℤ* c')
    ε = greater-than-zero-mult-trans (c') (c') (pos-succ-greater-than-zero c) (pos-succ-greater-than-zero c)
  
  γ : (x ℤ* c' ℤ+ z ℤ* a') ℤ* pos (succ (pred (succ b ℕ* succ c))) ℤ+ c' ℤ* c' ℤ* n ≡ (y ℤ* c' ℤ+ z ℤ* b') ℤ* pos (succ (pred (succ a ℕ* succ c)))
  γ = (x ℤ* c' ℤ+ z ℤ* a') ℤ* pos (succ (pred (succ b ℕ* succ c))) ℤ+ c' ℤ* c' ℤ* n ≡⟨ ap (λ - → ((x ℤ* c' ℤ+ z ℤ* a') ℤ* -) ℤ+  c' ℤ* c' ℤ* n) (denom-setup b c ) ⟩
      (x ℤ* c' ℤ+ z ℤ* a') ℤ* (b' ℤ* c') ℤ+ c' ℤ* c' ℤ* n                           ≡⟨ ap (λ - → - ℤ+ c' ℤ* c' ℤ* n) (distributivity-mult-over-ℤ (x ℤ* c') (z ℤ* a') (b' ℤ* c'))  ⟩
      x ℤ* c' ℤ* (b' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c') ℤ+ c' ℤ* c' ℤ* n               ≡⟨ ℤ+-assoc ( x ℤ* c' ℤ* (b' ℤ* c')) (z ℤ* a' ℤ* (b' ℤ* c')) (c' ℤ* c' ℤ* n ) ⟩
      x ℤ* c' ℤ* (b' ℤ* c') ℤ+ (z ℤ* a' ℤ* (b' ℤ* c') ℤ+ c' ℤ* c' ℤ* n)             ≡⟨ ap (x ℤ* c' ℤ* (b' ℤ* c') ℤ+_) (ℤ+-comm (z ℤ* a' ℤ* (b' ℤ* c')) ( c' ℤ* c' ℤ* n)) ⟩
      x ℤ* c' ℤ* (b' ℤ* c') ℤ+ (c' ℤ* c' ℤ* n ℤ+ z ℤ* a' ℤ* (b' ℤ* c'))             ≡⟨ ℤ+-assoc ( x ℤ* c' ℤ* (b' ℤ* c')) (c' ℤ* c' ℤ* n) (z ℤ* a' ℤ* (b' ℤ* c')) ⁻¹ ⟩
      x ℤ* c' ℤ* (b' ℤ* c') ℤ+ c' ℤ* c' ℤ* n ℤ+ z ℤ* a' ℤ* (b' ℤ* c')               ≡⟨ ap₂ (λ α β → α ℤ+ β ℤ+ z ℤ* a' ℤ* (b' ℤ* c')) (ℤ-mult-rearrangement x c' (b' ℤ* c')) (ℤ*-comm (c' ℤ* c') n) ⟩
      x ℤ* (b' ℤ* c') ℤ* c' ℤ+ n ℤ* (c' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c')             ≡⟨ ap (λ - → - ℤ* c'  ℤ+ n ℤ* (c' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c')) (ℤ*-assoc x b' c') ⟩
      x ℤ* b' ℤ* c' ℤ* c' ℤ+ n ℤ* (c' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c')               ≡⟨ ap (λ - → - ℤ+ n ℤ* (c' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c')) (ℤ*-assoc (x ℤ* b') c' c' ⁻¹) ⟩
      x ℤ* b' ℤ* (c' ℤ* c') ℤ+ n ℤ* (c' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c')             ≡⟨ ap (λ - → - ℤ+ z ℤ* a' ℤ* (b' ℤ* c')) (distributivity-mult-over-ℤ ( x ℤ* b') n (c' ℤ* c') ⁻¹) ⟩
      (x ℤ* b' ℤ+ n) ℤ* (c' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                         ≡⟨ ap (λ - → - ℤ+ z ℤ* a' ℤ* (b' ℤ* c') ) (ℤ*-assoc ((x ℤ* b' ℤ+ n)) c' c') ⟩
      (x ℤ* b' ℤ+ n) ℤ* c' ℤ* c' ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                           ≡⟨ ap (λ - → - ℤ* c' ℤ* c' ℤ+ z ℤ* a' ℤ* (b' ℤ* c')) l ⟩
      y ℤ* a' ℤ* c' ℤ* c' ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                                  ≡⟨ ap₂ (λ α β → α ℤ* c' ℤ+ β) (ℤ-mult-rearrangement y a' c') (ℤ*-assoc z a' (b' ℤ* c') ⁻¹) ⟩
      y ℤ* c' ℤ* a' ℤ* c' ℤ+ z ℤ* (a' ℤ* (b' ℤ* c'))                                ≡⟨ ap₂ (λ α β → α ℤ+ z ℤ* β) (ℤ*-assoc (y ℤ* c') a' c' ⁻¹) (ℤ-mult-rearrangement''' a' b' c') ⟩
      y ℤ* c' ℤ* (a' ℤ* c') ℤ+ z ℤ* (b' ℤ* (a' ℤ* c'))                              ≡⟨ ap (λ - → y ℤ* c' ℤ* (a' ℤ* c') ℤ+ -) (ℤ*-assoc z b' (a' ℤ* c')) ⟩
      y ℤ* c' ℤ* (a' ℤ* c') ℤ+ z ℤ* b' ℤ* (a' ℤ* c')                                ≡⟨ distributivity-mult-over-ℤ (y ℤ* c') (z ℤ* b') (a' ℤ* c') ⁻¹ ⟩
      (y ℤ* c' ℤ+ z ℤ* b') ℤ* (a' ℤ* c')                                            ≡⟨ ap (λ - → (y ℤ* c' ℤ+ z ℤ* b') ℤ* -) (denom-setup a c ⁻¹) ⟩
      (y ℤ* c' ℤ+ z ℤ* b') ℤ* pos (succ (pred (succ a ℕ* succ c))) ∎

ℚₙ-pos-multiplication-preserves-order : (p q : ℚₙ) → (pos 0 , 0) < p → (pos 0 , 0) < q → (pos 0 , 0) < (p * q)
ℚₙ-pos-multiplication-preserves-order (x , a) (y , b) (n₁ , g₁ , l₁) (n₂ , g₂ , l₂) = n₁ ℤ* n₂ , δ' , γ
 where
  δ' : greater-than-zero (n₁ ℤ* n₂)
  δ' = greater-than-zero-mult-trans n₁ n₂ g₁ g₂

  α : n₁ ≡ x
  α = n₁                            ≡⟨ ℤ-zero-left-neutral n₁ ⁻¹ ⟩
      pos 0 ℤ+ n₁                   ≡⟨ ap (λ - → - ℤ+ n₁) (ℤ-zero-left-is-zero (pos (succ a)) ⁻¹) ⟩
      pos 0 ℤ* pos (succ a) ℤ+ n₁   ≡⟨ l₁ ⟩
      x                             ∎ 

  β : n₂ ≡ y
  β = n₂                            ≡⟨ ℤ-zero-left-neutral n₂ ⁻¹ ⟩
      pos 0 ℤ+ n₂                   ≡⟨ ap (λ - → - ℤ+ n₂) (ℤ-zero-left-is-zero (pos (succ b)) ⁻¹) ⟩
      pos 0 ℤ* pos (succ b) ℤ+ n₂   ≡⟨ l₂ ⟩
      y                             ∎

  γ : (pos 0 ℤ* pos (succ (pred (succ a ℕ* succ b)))) ℤ+ n₁ ℤ* n₂ ≡ x ℤ* y ℤ* pos 1
  γ = pos 0 ℤ* pos (succ (pred (succ a ℕ* succ b))) ℤ+ n₁ ℤ* n₂ ≡⟨ ap (λ - → - ℤ+ n₁ ℤ* n₂) (ℤ-zero-left-is-zero (pos (succ (pred (succ a ℕ* succ b))))) ⟩
      pos 0 ℤ+ n₁ ℤ* n₂ ≡⟨ ℤ-zero-left-neutral (n₁ ℤ* n₂) ⟩
      n₁ ℤ* n₂          ≡⟨ ap₂ _ℤ*_ α β ⟩
      x ℤ* y            ≡⟨ ℤ-mult-right-id (x ℤ* y) ⟩ 
      x ℤ* y ℤ* pos 1   ∎

_ℚₙ≤_ _ℚₙ≥_ : ℚₙ → ℚₙ → 𝓤₀ ̇
p ℚₙ≤ q = (p < q) ∔ (p ≡ q)
p ℚₙ≥ q = q ℚₙ≤ p

ℚₙ≤-is-prop : (p q : ℚₙ) → is-prop (p ℚₙ≤ q)
ℚₙ≤-is-prop (x , a) (y , b) = +-is-prop (ℚₙ<-is-prop (x , a) (y , b)) ℚₙ-is-set I
 where
  I : (x , a) < (y , b) → ¬ ((x , a) ≡ (y , b))
  I (k , g , α) e = zero-not-greater-than-zero (transport (λ - → greater-than-zero -) IV g)
   where
    II : (x ≡ y) × (a ≡ b)
    II = from-×-≡' e
    i = pr₁ II
    ii = pr₂ II
  
    III : (x ℤ* pos (succ b) ℤ+ k ≡ x ℤ* pos (succ b))
    III = x ℤ* pos (succ b) ℤ+ k ≡⟨ α ⟩
          y ℤ* pos (succ a)      ≡⟨ ap₂ _ℤ*_ (i ⁻¹) (ap pos (ap succ ii)) ⟩
          x ℤ* pos (succ b)      ∎

    IV : k ≡ pos 0
    IV = ℤ≤-anti-lemma (x ℤ* pos (succ b)) k III

ℚₙ≤-trans : (p q r : ℚₙ) → p ℚₙ≤ q → q ℚₙ≤ r → p ℚₙ≤ r
ℚₙ≤-trans p q r (inl a) (inl b) = inl (ℚₙ-trans p q r a b)
ℚₙ≤-trans p q r (inl a) (inr b) = inl (transport (p <_) b a)
ℚₙ≤-trans p q r (inr a) (inl b) = inl (transport (_< r) (a ⁻¹) b)
ℚₙ≤-trans p q r (inr a) (inr b) = inr (a ∙ b)

{-
third-addition : (pos 1 , 2) + (pos 1 , 2) ≡ pos 2 , 2
third-addition = {!refl!}
-}

{-

ℚₙ-half-addition : ((x , a) : ℚₙ) → (x , pred (2 ℕ* succ a)) + (x , pred (2 ℕ* succ a)) ℚₙ≈ (x , a)
ℚₙ-half-addition (x , a) = I
 where
  I : ((x , pred (2 ℕ* succ a)) + (x , pred (2 ℕ* succ a))) ℚₙ≈ (x , a)
  I = pr₁ ((x , pred (2 ℕ* succ a)) + (x , pred (2 ℕ* succ a))) ℤ*  pos (succ a) ≡⟨ {!!} ⟩
      {!!}                                                                       ≡⟨ {!!} ⟩
      {!!}                                                                       ∎

-}

\end{code}


