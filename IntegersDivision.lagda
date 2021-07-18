Andrew Sneap - 27th April 2021

I link to this module within the Integers section of my report.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆) --TypeTopology

import NaturalsAddition --TypeTopology
import NaturalNumbers-Properties --TypeTopology
import NaturalsOrder --TypeTopology
import UF-Base --TypeTopology
import UF-Subsingletons --TypeTopology

import Integers
import IntegersOrder
import IntegersProperties
import MoreNaturalProperties
import NaturalsDivision
import NaturalsMultiplication 
import NaturalsOrderExtended

open Integers

_∣_ : ℤ → ℤ → 𝓤₀ ̇
a ∣ b = Σ x ꞉ ℤ , a * x ≡ b

open IntegersOrder
open IntegersProperties
open UF-Subsingletons --TypeTopology

_ℤ∣_-is-prop : (a b : ℤ) → not-zero a → is-prop (a ∣ b)
_ℤ∣_-is-prop a b nz (x , p) (x' , p') = to-subtype-≡ (λ _ → ℤ-is-set) (ℤ-mult-right-cancellable x x' a nz (ℤ*-comm x a ∙ (p ∙ p' ⁻¹ ∙ ℤ*-comm a x')))

open NaturalsDivision renaming (_∣_ to _ℕ∣_)

div-equiv-to-pos-div : (a b : ℕ) → a ℕ∣ b → pos a ∣ pos b
div-equiv-to-pos-div a b (x , p) = (pos x) , (pos-multiplication-equiv-to-ℕ a x ∙ ap pos p)

sign-split : (x : ℤ) → positive x ∔ negative x
sign-split (pos x)     = inl ⋆
sign-split (negsucc x) = inr ⋆

open NaturalNumbers-Properties --TypeTopology

pos-div-to-nat-div : (a b : ℕ) → pos a ∣ pos b → a ℕ∣ b
pos-div-to-nat-div a b (pos x , p) = x , (pos-lc (pos-multiplication-equiv-to-ℕ a x ⁻¹ ∙ p))
pos-div-to-nat-div a zero (negsucc x , p) = zero , refl
pos-div-to-nat-div zero (succ b) (negsucc x , p) = 𝟘-elim (positive-not-zero b (pos-lc (ℤ-zero-left-is-zero (negsucc x) ⁻¹ ∙ p) ⁻¹))
pos-div-to-nat-div (succ a) (succ b) (negsucc x , p) = 𝟘-elim (product-positive-negative-not-positive (succ a) x b p)

open MoreNaturalProperties
open NaturalsOrder renaming (_<_ to _ℕ<_ ; _≤_ to _ℕ≤_) --TypeTopology
open NaturalsOrderExtended
open NaturalsAddition renaming (_+_ to _ℕ+_)--TypeTopology
open NaturalsMultiplication renaming (_*_ to _ℕ*_)
open UF-Base --TypeTopology

ℤ-division : (a : ℤ) → (d : ℕ) → Σ q ꞉ ℤ , Σ r ꞉ ℕ , (a ≡ (q * (pos (succ d))) + (pos r)) × (r ℕ< (succ d))
ℤ-division (pos a) d = f (division a d)
 where
  f : Σ q ꞉ ℕ , Σ r ꞉ ℕ , (a ≡ q ℕ* succ d ℕ+ r) × (r ℕ< succ d)
    → Σ q ꞉ ℤ , Σ r ꞉ ℕ , (pos a ≡ q * pos (succ d) + pos r) × (r ℕ< succ d)
  f (q , r , e , l) = (pos q) , r , (ap pos e ∙ I) , l
   where
    I : pos (q ℕ* succ d ℕ+ r) ≡ pos q * pos (succ d) + pos r
    I = pos (q ℕ* succ d ℕ+ r)    ≡⟨ pos-addition-equiv-to-ℕ (q ℕ* (succ d)) r ⁻¹               ⟩
        pos (q ℕ* succ d) + pos r ≡⟨ ap (_+ pos r) (pos-multiplication-equiv-to-ℕ q (succ d) ⁻¹) ⟩
        pos q * pos (succ d) + pos r ∎
ℤ-division (negsucc a) d = f (division (succ a) d)
 where
  f : Σ q ꞉ ℕ , Σ r ꞉ ℕ , (succ a ≡ q ℕ* succ d ℕ+ r) × (r ℕ< succ d) → Σ q ꞉ ℤ , Σ r ꞉ ℕ , (negsucc a ≡ q * pos (succ d) + pos r) × (r ℕ< succ d)
  f (zero , zero , e , l) = 𝟘-elim (positive-not-zero a I)
   where
    I : succ a ≡ zero
    I = succ a                 ≡⟨ e ⟩
        zero ℕ* succ d ℕ+ zero ≡⟨ zero-left-is-zero (succ d) ⟩
        0                       ∎
  f (succ q , zero , e , l) = negsucc q , 0 , I , l
   where
    I : negsucc a ≡ negsucc q * pos (succ d)
    I = negsucc a                       ≡⟨ refl ⟩
        - pos (succ a)                  ≡⟨ ap -_ (ap pos e) ⟩
        - (pos (succ q ℕ* succ d))      ≡⟨ ap -_ (pos-multiplication-equiv-to-ℕ (succ q) (succ d) ⁻¹) ⟩
        - (pos (succ q) * pos (succ d)) ≡⟨ subtraction-dist-over-mult' (pos (succ q)) (pos (succ d)) ⁻¹ ⟩
        (- pos (succ q)) * pos (succ d) ≡⟨ refl ⟩
        negsucc q * pos (succ d)        ∎
    
  f (zero , succ r , e , l) = (negsucc 0) , k , II , cosubtraction k d (r , succ-lc I)
   where
    r-lemma : Σ k ꞉ ℕ , k ℕ+ succ r ≡ succ d
    r-lemma = subtraction' (succ r) (succ d) l

    k : ℕ
    k = pr₁ r-lemma

    I : succ (r ℕ+ k) ≡ succ d
    I = succ (r ℕ+ k) ≡⟨ succ-left r k ⁻¹ ⟩ succ r ℕ+ k ≡⟨ addition-commutativity (succ r) k ⟩ k ℕ+ succ r ≡⟨ pr₂ r-lemma ⟩ succ d ∎

    III : a ≡ r
    III = succ-lc (e ∙ ap succ (ap (_ℕ+ r) (zero-left-is-zero (succ d))) ∙ ap succ (zero-left-neutral r) )

    V : negsucc 0 * pos (succ r) ≡ negsucc r
    V = mult-inverse (pos (succ r)) ⁻¹ ∙ refl

    VI : pos k + pos (succ r) ≡ pos (succ d)
    VI = pos-addition-equiv-to-ℕ k (succ r) ∙ ap pos (pr₂ r-lemma)
 
    II : negsucc a ≡ negsucc 0 * pos (succ d) + pos k
    II = negsucc a ≡⟨ ap negsucc III ⟩
         negsucc r                        ≡⟨ ℤ-zero-left-neutral (negsucc r) ⁻¹ ⟩
         pos 0 + negsucc r                ≡⟨ ap (_+ (negsucc r)) (ℤ-sum-of-inverse-is-zero (pos k) ⁻¹ ) ⟩
         pos k + (- pos k) + negsucc r    ≡⟨ ℤ+-assoc (pos k) (- pos k) (negsucc r) ⟩
         pos k + ((- pos k) + negsucc r)  ≡⟨ ℤ+-comm (pos k) ((- pos k) + negsucc r) ⟩
         ((- pos k) + negsucc r) + pos k  ≡⟨ ap (λ z → (z + negsucc r) + pos k) (mult-inverse (pos k)) ⟩
         negsucc 0 * pos k + negsucc r + pos k ≡⟨ ap (λ z →  (negsucc 0 * pos k + z) + pos k) (mult-inverse (pos (succ r))) ⟩
         negsucc 0 * pos k + (negsucc 0 * pos (succ r)) + pos k ≡⟨ ap (_+ pos k) (distributivity-mult-over-ℤ' (pos k) (pos (succ r)) (negsucc 0) ⁻¹) ⟩
         negsucc 0 * (pos k + pos (succ r)) + pos k             ≡⟨ ap (λ z → negsucc 0 * z + pos k) VI ⟩
         negsucc 0 * pos (succ d) + pos k                            ∎
         
  f (succ q , succ r , e , l) = (negsucc (succ q)) , k , I , cosubtraction k d (r , succ-lc V)
   where
    r-lemma' : Σ k ꞉ ℕ , k ℕ+ (succ r) ≡ succ d
    r-lemma' = subtraction (succ r) (succ d) (<-trans r d (succ d) l (<-succ d)) 

    k : ℕ
    k = pr₁ r-lemma'

    V : succ (r ℕ+ k) ≡ succ d
    V = succ (r ℕ+ k) ≡⟨ succ-left r k ⁻¹ ⟩ succ r ℕ+ k ≡⟨ addition-commutativity (succ r) k ⟩ k ℕ+ succ r ≡⟨ pr₂ r-lemma' ⟩ succ d ∎

    II : (- pos k) + (- pos (succ r)) ≡ - pos (succ d)
    II = (- pos k) + (- pos (succ r)) ≡⟨ subtraction-dist (pos k) (pos (succ r))    ⟩
         -(pos k + pos (succ r))      ≡⟨ ap -_ (pos-addition-equiv-to-ℕ k (succ r)) ⟩
         - pos (k ℕ+ succ r)          ≡⟨ ap -_ (ap pos (pr₂ r-lemma'))               ⟩
         - pos (succ d)               ∎
         
    III : - pos (succ r) ≡ pos k + (- pos (succ d))
    III = - pos (succ r) ≡⟨ refl ⟩
          negsucc r                              ≡⟨ ℤ-zero-left-neutral (negsucc r) ⁻¹                             ⟩
          pos 0 + (- pos (succ r))               ≡⟨ ap (_+ (- pos (succ r))) (ℤ-sum-of-inverse-is-zero (pos k) ⁻¹) ⟩
          pos k + (- pos k) + (- pos (succ r))   ≡⟨ ℤ+-assoc (pos k) (- pos k) (- pos (succ r))                    ⟩
          pos k + ((- pos k) + (- pos (succ r))) ≡⟨ ap (pos k +_) II                                               ⟩
          pos k + (- pos (succ d)) ∎

    IV : pos (succ q) + pos 1 ≡ pos (succ (succ q))
    IV = refl
   
    I : negsucc a ≡ negsucc (succ q) * pos (succ d) + pos k
    I = negsucc a                                            ≡⟨ refl                                                                                   ⟩
        - pos (succ a)                                       ≡⟨ ap -_ (ap pos e)                                                                       ⟩ 
        - (pos (succ q ℕ* succ d ℕ+ succ r))                 ≡⟨ ap -_ (pos-addition-equiv-to-ℕ (succ q ℕ* (succ d)) (succ r) ⁻¹)                      ⟩
        - (pos (succ q ℕ* succ d) + pos (succ r))            ≡⟨ subtraction-dist (pos (succ q ℕ* succ d)) (pos (succ r)) ⁻¹                            ⟩
        (- pos (succ q ℕ* succ d)) + (- pos (succ r))        ≡⟨ ap₂ (λ z z' → z + z') (ap -_ (pos-multiplication-equiv-to-ℕ (succ q) (succ d) ⁻¹)) III ⟩
        (- pos (succ q) * pos (succ d)) + (pos k + (- pos (succ d))) ≡⟨ ℤ+-rearrangement (- (pos (succ q) * pos (succ d))) (pos k) (- pos (succ d)) ⁻¹ ⟩
        (- pos (succ q) * pos (succ d)) + (- pos (succ d)) + pos k  ≡⟨ ap (λ z → (z + (- pos (succ d))) + pos k) (ap -_ (ℤ*-comm (pos (succ q)) (pos (succ d)))) ⟩ 
        (- (pos (succ d) * pos (succ q))) + (- pos (succ d)) + pos k    ≡⟨ ap (λ z → (z + (- pos (succ d))) + pos k) (subtraction-dist-over-mult' (pos (succ d)) (pos (succ q)) ⁻¹) ⟩
        (- pos (succ d)) * pos (succ q) + (- (pos (succ d))) + pos k    ≡⟨ ap (λ z → ((- pos (succ d)) * pos (succ q) + z) + pos k) (ℤ-mult-right-id (- pos (succ d))) ⁻¹ ⟩
        (- pos (succ d)) * pos (succ q) + (- pos (succ d)) * pos 1 + pos k ≡⟨ ap (_+ pos k) (distributivity-mult-over-ℤ' (pos (succ q)) (pos 1) (- pos (succ d)) ⁻¹)  ⟩
        (- pos (succ d)) * (pos (succ q) + pos 1) + pos k  ≡⟨ ap (λ z → (((- pos (succ d))) * z) + pos k) IV ⟩
        (- pos (succ d)) * pos (succ (succ q)) + pos k     ≡⟨ ap (_+ pos k) (subtraction-dist-over-mult' (pos (succ d)) (pos (succ (succ q)))) ⟩
        (- pos (succ d) * pos (succ (succ q))) + pos k     ≡⟨ ap (λ z → (- z) + pos k) (ℤ*-comm (pos (succ d)) (pos (succ (succ q))))  ⟩
        (- pos (succ (succ q)) * pos (succ d)) + pos k     ≡⟨ ap (_+ pos k) (subtraction-dist-over-mult' (pos (succ (succ q))) (pos (succ d)) ⁻¹) ⟩
        negsucc (succ q) * pos (succ d) + pos k ∎

ℤ-∣-respects-addition : (x y z : ℤ) → x ∣ y → x ∣ z → x ∣ y + z
ℤ-∣-respects-addition x y z (α , αₚ) (β , βₚ) = α + β , I
 where
  I : x * (α + β) ≡ y + z
  I = x * (α + β)   ≡⟨ distributivity-mult-over-ℤ' α β x ⟩
      x * α + x * β ≡⟨ ap₂ _+_ αₚ βₚ ⟩
      y + z         ∎

ℤ-∣-respects-addition-of-multiples : (x y z k l : ℤ) → x ∣ y → x ∣ z → x ∣ (y * k + z * l)
ℤ-∣-respects-addition-of-multiples x y z k l (α , αₚ) (β , βₚ) = α * k + β * l , I
 where
  I : x * (α * k + β * l) ≡ y * k + z * l
  I = x * (α * k + β * l)       ≡⟨ distributivity-mult-over-ℤ' (α * k) (β * l) x ⟩
      x * (α * k) + x * (β * l) ≡⟨ ap₂ _+_ (ℤ*-assoc x α k) (ℤ*-assoc x β l) ⟩
      x * α * k + x * β * l     ≡⟨ ap₂ _+_ (ap (_* k) αₚ) (ap (_* l) βₚ) ⟩
      y * k + z * l             ∎



\end{code}
