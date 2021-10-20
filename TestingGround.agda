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

module TestingGround where

open import Rationals
open ncRationals renaming (_+_ to _ℚₙ+_ ; _<_ to _ℚₙ<_ ; _>_ to _ℚₙ>_ ; _*_ to _ℚₙ*_)
open UF-FunExt
open HCF
open NaturalsMultiplication renaming (_*_ to _ℕ*_)
open NaturalNumbers-Properties --TypeTopology
open Integers renaming (_*_ to _ℤ*_ ; _+_ to _ℤ+_ ; -_ to ℤ-_)
open IntegersProperties

tf1 : Fun-Ext → toℚ (pos 2 , 2) ≡ toℚ (pos 6 , 8)
tf1 fe = pr₁ (equiv-equality fe (pos 2 , 2) (pos 6 , 8)) I
 where
  I : (pos 2 , 2) ℚₙ≈ (pos 6 , 8)
  I = pos 2 ℤ* pos 9 ≡⟨ refl ⟩
      pos 6 ℤ* pos 3 ∎

tf2 : toℚ ((pos 1 , 2) ℚₙ+ (pos 1 , 2)) ≡ toℚ (pos 6 , 8)
tf2 = ap toℚ I
 where
  I : (pos 1 , 2) ℚₙ+ (pos 1 , 2) ≡ pos 6 , 8
  I = refl


trisect-lemma : Fun-Ext → toℚ (pos 1 , 2) + toℚ (pos 1 , 2) ≡ toℚ (pos 2 , 2)
trisect-lemma fe = III
 where
  I : toℚ ((pos 1 , 2) ℚₙ+ (pos 1 , 2)) ≡ (toℚ (pos 1 , 2) + toℚ (pos 1 , 2))
  I = toℚ-over-addition fe (pos 1 , 2) (pos 1 , 2)

  II : (toℚ (pos 1 , 2) + toℚ (pos 1 , 2)) ≡ toℚ ((pos 1 , 2) ℚₙ+ (pos 1 , 2))
  II = I ⁻¹

  III : (toℚ (pos 1 , 2) + toℚ (pos 1 , 2)) ≡ toℚ (pos 2 , 2)
  III = (toℚ (pos 1 , 2) + toℚ (pos 1 , 2)) ≡⟨ II ⟩
        toℚ ((pos 1 , 2) ℚₙ+ (pos 1 , 2))   ≡⟨ tf2 ⟩
        toℚ (pos 6 , 8)                     ≡⟨ (tf1 fe) ⁻¹ ⟩
        toℚ (pos 2 , 2)                     ∎

open UF-Base

trisect-lemma₃ : Fun-Ext → toℚ (pos 1 , 2) + toℚ (pos 2 , 2) ≡ 1ℚ
trisect-lemma₃ fe = ii
 where
  i : toℚ (pos 9 , 8) ≡ toℚ (pos 1 , 0)
  i = pr₁ (equiv-equality fe (pos 9 , 8) (pos 1 , 0)) refl
  ii : toℚ (pos 1 , 2) + toℚ (pos 2 , 2) ≡ 1ℚ
  ii = (toℚ (pos 1 , 2) + toℚ (pos 2 , 2)) ≡⟨ (toℚ-over-addition fe (pos 1 , 2) (pos 2 , 2)) ⁻¹ ⟩
                 toℚ ((pos 1 , 2) ℚₙ+ (pos 2 , 2))      ≡⟨ refl ⟩
                 toℚ (pos 9 , 8)                        ≡⟨ i ⟩
                 1ℚ ∎

trisect-lemma₂ : Fun-Ext → (p : ℚ) → zero-ℚ < p → (p * toℚ (pos 2 , 2)) < p
trisect-lemma₂ fe p l = transport₂ _<_ iii iv ii
 where
  i : zero-ℚ < (p * toℚ (pos 1 , 2))
  i = ℚ-pos-multiplication-preserves-order p (toℚ (pos 1 , 2)) l (ℚ-zero-less-than-positive 0 2)

  ii : (zero-ℚ + (p * toℚ (pos 2 , 2))) < ((p * toℚ (pos 1 , 2)) + (p * toℚ (pos 2 , 2)))
  ii = ℚ-addition-preserves-order zero-ℚ (p * toℚ (pos 1 , 2)) (p * toℚ (pos 2 , 2)) i

  iii : zero-ℚ + (p * toℚ (pos 2 , 2)) ≡ p * toℚ (pos 2 , 2)
  iii = ℚ-zero-left-neutral fe (p * toℚ (pos 2 , 2))

  iv : (p * toℚ (pos 1 , 2)) + (p * toℚ (pos 2 , 2)) ≡ p
  iv = ((p * toℚ (pos 1 , 2)) + (p * toℚ (pos 2 , 2))) ≡⟨ ℚ-distributivity fe p (toℚ (pos 1 , 2)) (toℚ (pos 2 , 2)) ⁻¹ ⟩
       (p * (toℚ (pos 1 , 2) + toℚ (pos 2 , 2)))       ≡⟨ ap (p *_) (trisect-lemma₃ fe) ⟩
       p * 1ℚ                                          ≡⟨ ℚ-mult-right-id fe p ⟩ 
       p ∎

trisect : Fun-Ext → (x y : ℚ) → x < y → Σ (x' , y') ꞉ ℚ × ℚ , (x < x') × (x' < y') × (y' < y) × ((y + (- x')) ≡ (toℚ ((pos 2) , 2) * (y + (- x)))) × (y' + (- x) ≡ toℚ ((pos 2) , 2) * (y + (- x)))
trisect fe x y l = ((x + ((y + (- x)) * 1/3)) , (x + ((y + (- x)) * 2/3))) , I , II , III , IV , V
 where
  p : ℚ
  p = y + (- x)

  1/3 : ℚ
  1/3 = toℚ (pos 1 , 2)

  2/3 : ℚ
  2/3 = toℚ (pos 2 , 2)

  α : zero-ℚ < p
  α = ℚ<-subtraction''' fe x y l

  β : zero-ℚ < 1/3
  β = ℚ-zero-less-than-positive 0 2

  I : x < (x + (p * 1/3))
  I = transport₂ _<_ (ℚ-zero-left-neutral fe x) (ℚ+-comm (p * 1/3) x) ii
   where
    i : zero-ℚ < (p * 1/3)
    i = ℚ-pos-multiplication-preserves-order p (1/3) α β

    ii : (zero-ℚ + x) < ((p * 1/3) + x)
    ii = ℚ-addition-preserves-order zero-ℚ (p * 1/3) x i

  II : (x + (p * 1/3)) < (x + (p * 2/3))
  II = transport ((x + (p * 1/3)) <_) ii i
   where
    i : (x + (p * 1/3)) < ((x + (p * 1/3)) + (p * 1/3))
    i = ℚ-addition-preserves-order x (x + (p * 1/3)) (p * 1/3) I

    ii : (((x + (p * 1/3)) + (p * 1/3))) ≡ (x + (p * 2/3))
    ii = ((x + (p * 1/3)) + (p * 1/3)) ≡⟨ ℚ+-assoc fe x (p * 1/3) (p * 1/3) ⟩
         x + ((p * 1/3) + (p * 1/3))   ≡⟨ ap (x +_) (ℚ-distributivity fe p (1/3) (1/3) ⁻¹) ⟩
         (x + (p * (1/3 + 1/3))) ≡⟨ ap (λ z → x + (p * z)) (trisect-lemma fe) ⟩
         (x + (p * 2/3)) ∎
    
  III : (x + (p * 2/3)) < y
  III = transport₂ _<_ (ℚ+-comm (p * 2/3) x) iv iii
   where
    i : (p * 2/3) < p
    i = trisect-lemma₂ fe p α

    ii : (p * 2/3) < p
    ii = i

    iii : ((p * 2/3) + x) < (p + x)
    iii = ℚ-addition-preserves-order (p * 2/3) p x ii

    iv : p + x ≡ y
    iv = (p + x) ≡⟨ ℚ+-assoc fe y (- x) x ⟩
         (y + ((- x) + x)) ≡⟨ ap (y +_) (ℚ-inverse-sum-to-zero' fe x) ⟩
         (y + zero-ℚ)      ≡⟨ ℚ-zero-right-neutral fe y ⟩
         y ∎

  IV : (y + (- (x + (p * 1/3)))) ≡ (2/3 * p)
  IV = i
   where
    i : (y + (- (x + (p * 1/3)))) ≡ (2/3 * p)
    i = (y + (- (x + (p * 1/3))))          ≡⟨ ap (y +_) (ℚ-minus-dist fe x (p * 1/3) ⁻¹) ⟩
          y + ((- x) + (- (p * 1/3)))        ≡⟨ ℚ+-assoc fe y (- x) (- (p * 1/3)) ⁻¹ ⟩
          ((y + (- x)) + (- (p * 1/3)))      ≡⟨ refl ⟩
          p + (- (p * 1/3))                  ≡⟨ ap (_+ (- (p * 1/3))) (ℚ-mult-left-id fe p ⁻¹) ⟩
          ((1ℚ * p) + (- (p * 1/3)))         ≡⟨ ap (λ z → (z * p) + (- (p * 1/3))) (trisect-lemma₃ fe ⁻¹) ⟩
          ((1/3 + 2/3) * p) + (- (p * 1/3))  ≡⟨ ap (_+ (- (p * 1/3))) (ℚ*-comm (1/3 + 2/3) p) ⟩
          (p * (1/3 + 2/3)) + (- (p * 1/3))  ≡⟨ ap (λ z → (p * z) + (- (p * 1/3))) (ℚ+-comm 1/3 2/3) ⟩
          (p * (2/3 + 1/3)) + (- (p * 1/3))  ≡⟨ ap (_+ - (p * 1/3)) (ℚ-distributivity fe p 2/3 1/3) ⟩
          ((p * 2/3) + (p * 1/3)) + (- (p * 1/3))    ≡⟨ ℚ+-assoc fe (p * 2/3) (p * 1/3) (- (p * 1/3)) ⟩
          (p * 2/3) + ((p * 1/3) + (- (p * 1/3)))    ≡⟨ ap₂ _+_ (ℚ*-comm p 2/3) (ℚ-inverse-sum-to-zero fe (p * 1/3)) ⟩
          (2/3 * p) + zero-ℚ                         ≡⟨ ℚ-zero-right-neutral fe (2/3 * p) ⟩
          (2/3 * p)                                  ∎

  V : ((x + (p * 2/3)) + (- x)) ≡ (2/3 * p)
  V = ((x + (p * 2/3)) + (- x)) ≡⟨ ap (_+ (- x)) (ℚ+-comm x (p * 2/3)) ⟩
      ((p * 2/3) + x) + (- x)   ≡⟨ ℚ+-assoc fe (p * 2/3) x (- x) ⟩
      ((p * 2/3) + (x + (- x))) ≡⟨  ap₂ _+_ (ℚ*-comm p 2/3) (ℚ-inverse-sum-to-zero fe x) ⟩
      (2/3 * p) + zero-ℚ        ≡⟨ ℚ-zero-right-neutral fe (2/3 * p) ⟩
      (2/3 * p)                 ∎

1/3 2/3 : ℚ
1/3 = toℚ (pos 1 , 2)
2/3 = toℚ (pos 2 , 2)

⟨2/3⟩^_ : ℕ → ℚ
⟨2/3⟩^ 0  = toℚ (pos 1 , 0)
⟨2/3⟩^ (succ n)  = rec (2/3) (λ k → k * 2/3) n








{-
log-result : (q : ℚ) → (m : ℕ) → Σ n ꞉ ℕ , (((⟨2/3⟩^ n) * q) < toℚ (pos m , 0))
log-result q = {!!}
-}
{-
exists-n : Fun-Ext → (p x y : ℚ) → zero-ℚ < p → x < y → Σ n ꞉ ℕ , (((⟨2/3⟩^ n) * (y + (- x))) < p) -- Try complete ded section with these above types. Still need to do logs
exists-n fe p x y l₁ l₂ = ii (ℚ-dichotomous fe p (y + (- x)))
 where
  i : zero-ℚ < (y + (- x))
  i = ℚ<-subtraction''' fe x y l₂

  ii : (p ≤ (y + (- x))) ∔ ((y + (- x)) < p) → Σ n ꞉ ℕ , (((⟨2/3⟩^ n) * (y + (- x))) < p)
  ii (inl z) = {!!}
  ii (inr z) = 0 , (transport (_< p) (ℚ-mult-left-id fe (y + (- x)) ⁻¹) z)
-}

--Don't need logs? p/(y-x)
