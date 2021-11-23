Andrew Sneap - 27th April 2021

I link to this module within the Integers section of my report.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆) -- TypeTopology

import DiscreteAndSeparated -- TypeTopology
import Groups -- TypeTopology
import NaturalsAddition -- TypeTopology
import NaturalNumbers-Properties -- TypeTopology
import UF-Base -- TypeTopology
import UF-Miscelanea -- TypeTopology
import UF-Subsingletons -- TypeTopology
import Unit-Properties -- TypeTopology

import Integers
import NaturalsMultiplication 

module IntegersProperties where

open Integers

pos-lc : {x y : ℕ} → pos x ≡ pos y → x ≡ y
pos-lc = ap abs

open NaturalNumbers-Properties renaming (pred to ℕpred) -- TypeTopology

negsuc-lc : {x y : ℕ} → negsucc x ≡ negsucc y → x ≡ y
negsuc-lc {x} {y} p = succ-lc (ap abs p)

ℤ-left-succ-pos : (x : ℤ) → (y : ℕ) → succℤ x +pos y ≡ succℤ (x +pos y)  --cubical
ℤ-left-succ-pos x 0        = refl
ℤ-left-succ-pos x (succ y) = ap succℤ (ℤ-left-succ-pos x y)

ℤ-left-pred-pos : (x : ℤ) → (y : ℕ) → predℤ x +pos y ≡ predℤ (x +pos y) --cubical
ℤ-left-pred-pos x 0        = refl
ℤ-left-pred-pos x (succ y) = succℤ (predℤ x +pos y)       ≡⟨ ℤ-left-succ-pos (predℤ x) y ⁻¹ ⟩
                              (succℤ (predℤ x) +pos y)    ≡⟨ ap (_+pos y) (succpredℤ x)     ⟩
                              x +pos y                    ≡⟨ predsuccℤ (x +pos y) ⁻¹        ⟩
                              predℤ (succℤ (x +pos y))    ∎

ℤ-left-pred-negsucc : (x : ℤ) → (y : ℕ) → predℤ x +negsucc y ≡ predℤ (x +negsucc y) 
ℤ-left-pred-negsucc x 0        = refl
ℤ-left-pred-negsucc x (succ y) = ap predℤ (ℤ-left-pred-negsucc x y)

ℤ-left-succ-negsucc : (x : ℤ) → (y : ℕ) → succℤ x +negsucc y ≡ succℤ (x +negsucc y) --cubical agda
ℤ-left-succ-negsucc x 0        = predsuccℤ x ∙ succpredℤ x ⁻¹
ℤ-left-succ-negsucc x (succ y) = (succℤ x +negsucc succ y)             ≡⟨ ℤ-left-pred-negsucc (succℤ x) y ⁻¹  ⟩
                                 (predℤ (succℤ x) +negsucc y)          ≡⟨ ap (_+ (negsucc y)) (predsuccℤ x)   ⟩
                                 (x + negsucc y)                       ≡⟨ succpredℤ (x +negsucc y) ⁻¹         ⟩
                                 succℤ (x +negsucc succ y)             ∎

ℤ-right-succ : (x y : ℤ) → x + succℤ y ≡ succℤ (x + y)
ℤ-right-succ x (pos y)            = refl
ℤ-right-succ x (negsucc 0)        = succpredℤ x ⁻¹
ℤ-right-succ x (negsucc (succ y)) = succpredℤ (x +negsucc y) ⁻¹

ℤ-left-succ : (x y : ℤ) → succℤ x + y ≡ succℤ (x + y)
ℤ-left-succ x (pos y)     = ℤ-left-succ-pos x y
ℤ-left-succ x (negsucc y) = ℤ-left-succ-negsucc x y

ℤ-left-pred : (x y : ℤ) → predℤ x + y ≡ predℤ (x + y)
ℤ-left-pred x (pos y)     = ℤ-left-pred-pos x y
ℤ-left-pred x (negsucc y) = ℤ-left-pred-negsucc x y

ℤ-right-pred : (x y : ℤ) → x + predℤ y ≡ predℤ (x + y)
ℤ-right-pred x (pos 0)        = refl
ℤ-right-pred x (pos (succ y)) = predsuccℤ (x +pos y) ⁻¹
ℤ-right-pred x (negsucc y)    = refl

ℤ-zero-right-neutral : (x : ℤ) → x + pos 0 ≡ x
ℤ-zero-right-neutral x = refl

ℤ-zero-left-neutral : (x : ℤ) → pos 0 + x ≡ x
ℤ-zero-left-neutral (pos 0)            = refl
ℤ-zero-left-neutral (pos (succ x))     = ap succℤ (ℤ-zero-left-neutral (pos x))
ℤ-zero-left-neutral (negsucc 0)        = refl
ℤ-zero-left-neutral (negsucc (succ x)) = ap predℤ (ℤ-zero-left-neutral (negsucc x))

ℤ-pred-is-minus-one : (x : ℤ) → predℤ x ≡ negsucc 0 + x
ℤ-pred-is-minus-one (pos 0)            = refl
ℤ-pred-is-minus-one (pos (succ x))     = predℤ (pos (succ x))      ≡⟨ succpredℤ (pos x) ⁻¹                   ⟩
                                         succℤ (predℤ (pos x))     ≡⟨ ap succℤ (ℤ-pred-is-minus-one (pos x)) ⟩
                                         negsucc 0 + pos (succ x)  ∎
ℤ-pred-is-minus-one (negsucc 0)        = refl
ℤ-pred-is-minus-one (negsucc (succ x)) = predℤ (negsucc (succ x))      ≡⟨ ap predℤ (ℤ-pred-is-minus-one (negsucc x)) ⟩
                                         predℤ (negsucc 0 + negsucc x) ∎

succℤ-lc : {x y : ℤ} → succℤ x ≡ succℤ y → x ≡ y
succℤ-lc {x} {y} p = x               ≡⟨ predsuccℤ x ⁻¹ ⟩
                     predℤ (succℤ x) ≡⟨ ap predℤ p     ⟩
                     predℤ (succℤ y) ≡⟨ predsuccℤ y    ⟩
                     y               ∎

predℤ-lc : {x y : ℤ} →  predℤ x ≡ predℤ y → x ≡ y
predℤ-lc {x} {y} p = x               ≡⟨ succpredℤ x ⁻¹ ⟩
                     succℤ (predℤ x) ≡⟨ ap succℤ p     ⟩
                     succℤ (predℤ y) ≡⟨ succpredℤ y    ⟩
                     y               ∎

ℤ+-comm : (x y : ℤ) → x + y ≡ y + x
ℤ+-comm x = ℤ-induction base step₁ step₂
 where
  base : x ≡ (pos 0 + x)
  base = ℤ-zero-left-neutral x ⁻¹

  step₁ : (k : ℤ)
        → x + k         ≡ k + x
        → x + succℤ k   ≡ succℤ k + x
  step₁ k IH = x + succℤ k   ≡⟨ ℤ-right-succ x k   ⟩
               succℤ (x + k) ≡⟨ ap succℤ IH        ⟩
               succℤ (k + x) ≡⟨ ℤ-left-succ k x ⁻¹ ⟩
               succℤ k + x   ∎ 
    
  step₂ : (k : ℤ)
        → x + succℤ k ≡ succℤ k + x
        → x + k       ≡ k + x
  step₂ k IH = succℤ-lc I
   where
    I : succℤ (x + k) ≡ succℤ (k + x)
    I = succℤ (x + k) ≡⟨ ℤ-right-succ x k ⁻¹ ⟩
        x + succℤ k   ≡⟨ IH                  ⟩
        succℤ k + x   ≡⟨ ℤ-left-succ k x     ⟩
        succℤ (k + x) ∎

ℤ+-assoc : (a b c : ℤ) → (a + b) + c ≡ a + (b + c)
ℤ+-assoc a b = ℤ-induction base step₁ step₂
 where
  base : (a + b) + pos 0 ≡ a + (b + pos 0)
  base = refl

  step₁ : (k : ℤ)
        → (a + b) + k       ≡ a + (b + k)
        → (a + b) + succℤ k ≡ a + (b + succℤ k)
  step₁ k IH = (a + b) + succℤ k   ≡⟨ ℤ-right-succ (a + b) k           ⟩
               succℤ ((a + b) + k) ≡⟨ ap succℤ IH                     ⟩
               succℤ (a + (b + k)) ≡⟨ ℤ-right-succ a (b + k) ⁻¹       ⟩
               a + succℤ (b + k)   ≡⟨ ap (a +_) (ℤ-right-succ b k ⁻¹) ⟩
               a + (b + succℤ k)   ∎

  step₂ : (k : ℤ)
        → (a + b) + succℤ k ≡ a + (b + succℤ k)
        → (a + b) + k       ≡ a + (b + k)
  step₂ k IH = succℤ-lc I
   where
    I : succℤ (a + b + k) ≡ succℤ (a + (b + k))
    I = succℤ ((a + b) + k)        ≡⟨ ℤ-right-succ (a + b) k ⁻¹    ⟩
        (a + b) + succℤ k          ≡⟨ IH                           ⟩ 
        a + (b + succℤ k)          ≡⟨ ap (a +_) (ℤ-right-succ b k) ⟩
        a + succℤ (b + k)          ≡⟨ ℤ-right-succ a (b + k)       ⟩
        succℤ (a + (b + k))        ∎

ℤ+-rearrangement : (a b c : ℤ) → a + c + b ≡ a + (b + c)
ℤ+-rearrangement a b c = a + c + b   ≡⟨ ℤ+-assoc a c b          ⟩ 
                         a + (c + b) ≡⟨ ap (a +_) (ℤ+-comm c b) ⟩
                         a + (b + c) ∎

ℤ+-lc : (x y z : ℤ) → z + x ≡ z + y → x ≡ y
ℤ+-lc x y = ℤ-induction base step₁ step₂
 where
  base : pos 0 + x ≡ pos 0 + y → x ≡ y
  base l = x           ≡⟨ ℤ-zero-left-neutral x ⁻¹ ⟩
           pos 0 + x   ≡⟨ l                        ⟩
           pos 0 + y   ≡⟨ ℤ-zero-left-neutral y    ⟩
           y           ∎

  step₁ : (k : ℤ)
        → (k + x ≡ k + y → x ≡ y)
        → succℤ k + x ≡ succℤ k + y
        → x ≡ y
  step₁ k IH l = IH (succℤ-lc I)
   where
    I : succℤ (k + x) ≡ succℤ (k + y)
    I = succℤ (k + x)  ≡⟨ ℤ-left-succ k x ⁻¹ ⟩
        succℤ k + x    ≡⟨ l                  ⟩
        succℤ k + y    ≡⟨ ℤ-left-succ k y    ⟩
        succℤ (k + y)  ∎

  step₂ : (k : ℤ)
        → (succℤ k + x ≡ succℤ k + y → x ≡ y)
        → k + x ≡ k + y
        → x ≡ y
  step₂ k IH l = IH I
   where
    I : succℤ k + x ≡ succℤ k + y
    I = succℤ k + x    ≡⟨ ℤ-left-succ k x    ⟩ 
        succℤ (k + x)  ≡⟨ ap succℤ l         ⟩
        succℤ (k + y)  ≡⟨ ℤ-left-succ k y ⁻¹ ⟩
        succℤ k + y    ∎

ℤ-zero-right-is-zero : (x : ℤ) → x * pos 0 ≡ pos 0
ℤ-zero-right-is-zero x = refl

ℤ-zero-left-is-zero : (x : ℤ) → pos 0 * x ≡ pos 0
ℤ-zero-left-is-zero = ℤ-induction base step₁ step₂
 where
  base : pos 0 * pos 0 ≡ pos 0
  base = refl

  step₁ : (k : ℤ)
        → pos 0 * k       ≡ pos 0
        → pos 0 * succℤ k ≡ pos 0
  step₁ (pos x)            IH = I
   where
    I : pos 0 * succℤ (pos x) ≡ pos 0
    I = pos 0 * succℤ (pos x) ≡⟨ refl             ⟩
        pos 0 + pos 0 * pos x ≡⟨ ap (pos 0 +_) IH ⟩
        pos 0 + pos 0         ≡⟨ refl             ⟩
        pos 0                 ∎
  step₁ (negsucc 0)        IH = refl
  step₁ (negsucc (succ x)) IH = I
   where
    I : pos 0 * negsucc x ≡ pos 0
    I = pos 0 * negsucc x            ≡⟨ ℤ-zero-left-neutral (pos 0 * negsucc x) ⁻¹ ⟩
        pos 0 + pos 0 * negsucc x    ≡⟨ refl                                       ⟩
        pos 0 * negsucc (succ x)     ≡⟨ IH                                         ⟩
        pos 0                        ∎

  step₂ : (k : ℤ)
        → pos 0 * succℤ k ≡ pos 0
        → pos 0 * k       ≡ pos 0
  step₂ (pos x)            IH = I
   where
    I : pos 0 * pos x ≡ pos 0
    I = pos 0 * pos x         ≡⟨ ℤ-zero-left-neutral (pos 0 * pos x) ⁻¹ ⟩
        pos 0 + pos 0 * pos x ≡⟨ IH                                     ⟩
        pos 0                 ∎
  step₂ (negsucc 0)        IH = refl
  step₂ (negsucc (succ x)) IH = I
   where
    I : pos 0 + pos 0 * negsucc x ≡ pos 0
    I = pos 0 + pos 0 * negsucc x ≡⟨ ℤ-zero-left-neutral (pos 0 * negsucc x) ⟩
        pos 0 * negsucc x         ≡⟨ IH                                      ⟩
        pos 0                     ∎

ℤ-mult-right-id : (x : ℤ) → x * pos 1 ≡ x
ℤ-mult-right-id x = refl

ℤ-mult-left-id : (x : ℤ) → pos 1 * x ≡ x
ℤ-mult-left-id = ℤ-induction base step₁ step₂
 where
  base : pos 1 * pos 0 ≡ pos 0
  base = refl

  step₁ : (k : ℤ)
        → pos 1 * k       ≡ k
        → pos 1 * succℤ k ≡ succℤ k
  step₁ (pos x) IH = I
   where
    I : pos 1 * succℤ (pos x) ≡ succℤ (pos x)
    I = pos 1 * succℤ (pos x) ≡⟨ ap (pos 1 +_) IH        ⟩
        pos 1 + pos x         ≡⟨ ℤ+-comm (pos 1) (pos x) ⟩
        succℤ (pos x)         ∎
  step₁ (negsucc 0)        IH = refl
  step₁ (negsucc (succ x)) IH = I
   where
    I : pos 1 * negsucc x ≡ negsucc x
    I = ℤ+-lc (pos 1 * negsucc x) (negsucc x) (negsucc 0) II
     where
      II : negsucc 0 + pos 1 * negsucc x ≡ negsucc 0 + negsucc x
      II = negsucc 0 + pos 1 * negsucc x ≡⟨ IH                                 ⟩
           negsucc (succ x)              ≡⟨ ℤ+-comm (negsucc x) (negsucc 0)    ⟩
           negsucc 0 + negsucc x         ∎

  step₂ : (k : ℤ)
        → pos 1 * succℤ k ≡ succℤ k
        → pos 1 * k       ≡ k
  step₂ (pos x)            IH = ℤ+-lc (pos 1 * pos x) (pos x) (pos 1) I
   where
    I : pos 1 + pos 1 * pos x ≡ pos 1 + pos x
    I = pos 1 + pos 1 * pos x ≡⟨ IH                      ⟩
        succℤ (pos x)         ≡⟨ ℤ+-comm (pos x) (pos 1) ⟩
        pos 1 + pos x         ∎
  step₂ (negsucc 0)        IH = refl
  step₂ (negsucc (succ x)) IH = I
   where
    I : pos 1 * negsucc (succ x) ≡ negsucc (succ x)
    I = pos 1 * negsucc (succ x) ≡⟨ ap (negsucc 0 +_) IH            ⟩
        negsucc 0 + negsucc x    ≡⟨ ℤ+-comm (negsucc 0) (negsucc x) ⟩
        negsucc (succ x)         ∎
    
negsucctopredℤ : (k : ℕ) → negsucc k ≡ predℤ (- pos k)
negsucctopredℤ 0        = refl
negsucctopredℤ (succ k) = refl

predℤtominussuccℤ : (x : ℤ) → (k : ℕ) → predℤ (- (x + pos k)) ≡ - succℤ (x + pos k)
predℤtominussuccℤ x k = predminus (x + pos k)

succℤtominuspredℤ : (x : ℤ) → succℤ (- x) ≡ (- predℤ x)
succℤtominuspredℤ (pos 0)               = refl
succℤtominuspredℤ (pos (succ 0))        = refl
succℤtominuspredℤ (pos (succ (succ x))) = refl
succℤtominuspredℤ (negsucc x)           = refl

subtraction-dist₀ : (x : ℤ) (y : ℕ) → (- x) + (- pos y) ≡ - (x + pos y)
subtraction-dist₀ x = induction base step
 where
  base : (- x) + (- pos 0) ≡ - (x + pos 0)
  base = refl

  step : (k : ℕ)
       → (- x) + (- pos k)        ≡ - (x + pos k)
       → (- x) + (- pos (succ k)) ≡ - (x + pos (succ k))
  step k IH = (- x) + negsucc k            ≡⟨ ap ((- x) +_) (negsucctopredℤ k) ⟩
              (- x) + predℤ (- pos k)      ≡⟨ ℤ-right-pred (- x) (- pos k)     ⟩
              predℤ ((- x) + (- pos k))    ≡⟨ ap predℤ IH                      ⟩
              predℤ (- (x + pos k))        ≡⟨ predℤtominussuccℤ x k            ⟩
              - (x + pos (succ k))         ∎

subtraction-dist₁ : (x : ℤ) → (y : ℕ) → (- x) + (- (negsucc y)) ≡ - (x + negsucc y)
subtraction-dist₁ x = induction base step
 where
  base : ((- x) + (- negsucc 0)) ≡ (- (x + negsucc 0))
  base = succℤtominuspredℤ x

  step : (k : ℕ)
       → (- x) + pos (succ k)         ≡ - (x + negsucc k)
       → (- x) + (- negsucc (succ k)) ≡ - (x + negsucc (succ k))
  step k IH = (- x) + succℤ (pos (succ k))   ≡⟨ ℤ-right-succ (- x) (pos (succ k)) ⟩
              succℤ ((- x) + pos (succ k))   ≡⟨ ap succℤ IH                       ⟩
              succℤ (- (x +negsucc k))       ≡⟨ succℤtominuspredℤ (x +negsucc k) ⟩
              - (x + negsucc (succ k))       ∎

subtraction-dist : (x y : ℤ) → (- x) + (- y) ≡ - (x + y)
subtraction-dist x (pos y)     = subtraction-dist₀ x y
subtraction-dist x (negsucc y) = subtraction-dist₁ x y


distributivity-mult-over-ℤ₀ : (x y : ℤ) → (z : ℕ) → (x + y) * (pos z) ≡ (x * pos z) + (y * pos z)
distributivity-mult-over-ℤ₀ x y = induction base step
 where
  base : (x + y) * pos 0 ≡ (x * pos 0) + (y * pos 0)
  base = refl

  step : (k : ℕ)
       → (x + y) * pos k        ≡ x * pos k + y * pos k
       → (x + y) * pos (succ k) ≡ x * pos (succ k) + y * pos (succ k)
  step k IH = (x + y) * pos (succ k)             ≡⟨ ap ((x + y) +_) IH ⟩
              (x + y) + (u + v)                  ≡⟨ ℤ+-assoc (x + y) u v ⁻¹ ⟩
              ((x + y) + u) + v                  ≡⟨ ap (_+ v) (ℤ+-assoc x y u) ⟩
              (x + (y + u)) + v                  ≡⟨ ap (λ z → (x + z) + v) (ℤ+-comm y u) ⟩
              (x + (u + y)) + v                  ≡⟨ ap (_+ v) (ℤ+-assoc x u y ⁻¹) ⟩
              ((x + u) + y) + v                  ≡⟨ ℤ+-assoc (x + u) y v ⟩
              (x + u) + (y + v) ∎
     where
       u v : ℤ
       u = x * pos k
       v = y * pos k

distributivity-mult-over-ℤ₁ : (x y : ℤ) → (z : ℕ) → (x + y) * (negsucc z) ≡ (x * negsucc z) + (y * negsucc z)
distributivity-mult-over-ℤ₁ x y = induction base step
 where
  base : (x + y) * negsucc 0 ≡ x * negsucc 0 + y * negsucc 0
  base = (x + y) * negsucc 0           ≡⟨ refl                    ⟩
         - (x + y)                     ≡⟨ subtraction-dist x y ⁻¹ ⟩
         (- x) + (- y)                 ≡⟨ refl                    ⟩
         x * negsucc 0 + y * negsucc 0 ∎

  step : (k : ℕ)
       → (x + y) * negsucc k               ≡ x * negsucc k + y * negsucc k
       → (- (x + y)) + (x + y) * negsucc k ≡ (- x) + x * negsucc k + ((- y) + y * negsucc k)
  step k IH = (- x + y) + (x + y) * negsucc k                   ≡⟨ ap ((- (x + y)) +_) IH                                                   ⟩
              (- x + y) + (x * negsucc k + y * negsucc k)       ≡⟨ ap (_+ (((x * negsucc k) + (y * negsucc k)))) (subtraction-dist x y ⁻¹) ⟩
              (- x) + (- y) + (x * negsucc k + y * negsucc k)   ≡⟨ ℤ+-assoc (- x) (- y) (u + v)                                            ⟩
              (- x) + ((- y) + (x * negsucc k + y * negsucc k)) ≡⟨ ap ((- x) +_) (ℤ+-assoc (- y) u v ⁻¹)                                   ⟩
              (- x) + ((- y) + x * negsucc k + y * negsucc k)   ≡⟨ ap (λ z → (- x) + (z + v)) (ℤ+-comm (- y) u)                            ⟩
              (- x) + (x * negsucc k + (- y) + y * negsucc k)   ≡⟨ ap ((- x) +_) (ℤ+-assoc u (- y) v)                                      ⟩
              (- x) + (x * negsucc k + ((- y) + y * negsucc k)) ≡⟨ ℤ+-assoc (- x) u ((- y) + v) ⁻¹                                         ⟩
              (- x) + x * negsucc k + ((- y) + y * negsucc k) ∎
    where
      u v : ℤ
      u = x * negsucc k
      v = y * negsucc k
    
distributivity-mult-over-ℤ : (x y z : ℤ) → (x + y) * z ≡ (x * z) + (y * z)
distributivity-mult-over-ℤ x y (pos z)     = distributivity-mult-over-ℤ₀ x y z
distributivity-mult-over-ℤ x y (negsucc z) = distributivity-mult-over-ℤ₁ x y z
    
ℤ*-comm₀ : (x : ℤ) → (y : ℕ) → x * pos y ≡ pos y * x
ℤ*-comm₀ x = induction base step
 where
  base : (x * pos 0) ≡ (pos 0 * x)
  base = x * pos 0 ≡⟨ ℤ-zero-left-is-zero x ⁻¹ ⟩
         pos 0 * x ∎

  step : (k : ℕ)
       → x * pos k     ≡ pos k * x
       → x + x * pos k ≡ (pos k + pos 1) * x
  step k IH = x + x * pos k         ≡⟨ ap (x +_) IH                                    ⟩
              x + pos k * x         ≡⟨ ap (_+ (pos k * x)) (ℤ-mult-left-id x ⁻¹)       ⟩
              pos 1 * x + pos k * x ≡⟨ distributivity-mult-over-ℤ (pos 1) (pos k) x ⁻¹ ⟩
              (pos 1 + pos k) * x   ≡⟨ ap (_* x) (ℤ+-comm (pos 1) (pos k))             ⟩
              (pos k + pos 1) * x   ∎

mult-inverse : (x : ℤ) → (- x) ≡ (negsucc 0 * x)
mult-inverse = ℤ-induction base step₁ step₂
 where
  base : (- pos 0) ≡ (negsucc 0 * pos 0)
  base = refl

  step₁ : (k : ℤ)
        → (- k)     ≡ negsucc 0 * k
        → - succℤ k ≡ negsucc 0 * succℤ k
  step₁ (pos 0)            IH = refl 
  step₁ (pos (succ x))     IH = predℤ (negsucc x)                ≡⟨ ap predℤ IH                                           ⟩
                                predℤ (negsucc 0 * pos (succ x)) ≡⟨ ℤ-pred-is-minus-one (negsucc 0 + (negsucc 0 * pos x)) ⟩
                                negsucc 0 * succℤ (pos (succ x)) ∎ 
  step₁ (negsucc 0)        IH = refl
  step₁ (negsucc (succ x)) IH = ℤ+-lc (- succℤ (negsucc (succ x))) (negsucc 0 * succℤ (negsucc (succ x))) (pos 1) I
   where
    I : pos 1 + (- succℤ (negsucc (succ x))) ≡ pos 1 + negsucc 0 * succℤ (negsucc (succ x))
    I = pos 1 + (- succℤ (negsucc (succ x))) ≡⟨ ap succℤ (ℤ+-comm (pos 1) (pos x)) ⟩
        succℤ (pos x + pos 1)                ≡⟨ IH ⟩
        negsucc 0 * negsucc (succ x)         ∎

  step₂ : (k : ℤ)
        → - succℤ k ≡ negsucc 0 * succℤ k
        → - k       ≡ negsucc 0 * k
  step₂ (pos 0)        IH = refl
  step₂ (pos (succ x)) IH = ℤ+-lc (- pos (succ x)) (negsucc 0 * pos (succ x)) (negsucc 0) I
   where
    I : negsucc 0 + (- pos (succ x)) ≡ negsucc 0 + negsucc 0 * pos (succ x)
    I = negsucc 0 + (- pos (succ x))     ≡⟨ ℤ+-comm (negsucc 0) (negsucc x) ⟩
        negsucc x + negsucc 0            ≡⟨ IH ⟩
        negsucc 0 * succℤ (pos (succ x)) ∎
  step₂ (negsucc 0)        IH = refl
  step₂ (negsucc (succ x)) IH = I
   where
    I : pos (succ x) + pos 1 ≡ pos 1 + negsucc 0 * succℤ (negsucc (succ x))
    I = pos (succ x) + pos 1                         ≡⟨ ℤ+-comm (pos (succ x)) (pos 1) ⟩
        pos 1 + pos (succ x)                         ≡⟨  ap (pos (succ 0) +_) IH    ⟩
        pos 1 + negsucc 0 * succℤ (negsucc (succ x)) ∎

ℤ*-comm₁ : (x : ℤ) → (y : ℕ) → x * (negsucc y) ≡ (negsucc y) * x
ℤ*-comm₁ x = induction base step
 where
  base : (x * negsucc 0) ≡ (negsucc 0 * x)
  base = mult-inverse x

  step : (k : ℕ)
       → x * negsucc k        ≡ negsucc k * x
       → x * negsucc (succ k) ≡ negsucc (succ k) * x
  step k IH = x * negsucc (succ k)              ≡⟨ refl                                                       ⟩
              (- x) + x * negsucc k             ≡⟨ ap ((- x) +_) IH                                           ⟩
              (- x) + negsucc k * x             ≡⟨ ap (_+ (negsucc k * x)) (mult-inverse x)                   ⟩
              (negsucc 0) * x + negsucc k * x   ≡⟨ distributivity-mult-over-ℤ (negsucc 0) (negsucc k) x ⁻¹ ⟩
              (negsucc 0 + negsucc k) * x       ≡⟨ ap (_* x) (ℤ+-comm (negsucc 0) (negsucc k))             ⟩ 
              negsucc (succ k) * x              ∎

ℤ*-comm : (x y : ℤ) → x * y ≡ y * x
ℤ*-comm x (pos y)     = ℤ*-comm₀ x y
ℤ*-comm x (negsucc y) = ℤ*-comm₁ x y

open UF-Base -- TypeTopology

distributivity-mult-over-ℤ' : (x y z : ℤ) → z * (x + y) ≡ (z * x) + (z * y)
distributivity-mult-over-ℤ' x y z = z * (x + y)      ≡⟨ ℤ*-comm z (x + y)                                 ⟩
                                    (x + y) * z      ≡⟨ distributivity-mult-over-ℤ x y z                  ⟩
                                    x * z + y * z    ≡⟨ ap₂ (λ z z' → z + z') (ℤ*-comm x z) (ℤ*-comm y z) ⟩
                                    z * x + z * y    ∎

ℤ*-assoc₀ : (x y : ℤ) → (z : ℕ ) → x * (y * pos z) ≡ (x * y) * pos z
ℤ*-assoc₀ x y = induction base step
  where
    base : x * (y * pos 0) ≡ (x * y) * pos 0
    base = refl

    step : (k : ℕ)
         → x * (y * pos k)         ≡ (x * y) * pos k
         → x * (y * pos (succ k))  ≡ (x * y) * pos (succ k)
    step k IH = x * (y * pos (succ k))        ≡⟨ distributivity-mult-over-ℤ' y (y * pos k) x ⟩
                x * y + x * (y * pos k)       ≡⟨ ap ((x * y) +_) IH                          ⟩
                x * y + (x * y) * pos k       ∎


subtraction-dist-over-mult₀ : (x : ℤ) → (y : ℕ) → x * (- pos y) ≡ - x * pos y
subtraction-dist-over-mult₀ x = induction base step
  where
    base : x * (- pos 0) ≡ - (x * pos 0)
    base = refl

    step : (k : ℕ)
         → x * (- pos k)        ≡ - (x * pos k)
         → x * (- pos (succ k)) ≡ - (x * pos (succ k))
    step 0        IH = refl
    step (succ k) IH = x * (- pos (succ (succ k)))  ≡⟨ ap ((- x) +_) IH                     ⟩
                       (- x) + (- x * pos (succ k)) ≡⟨ subtraction-dist x (x + (x * pos k)) ⟩
                       - x + (x + x * pos k)        ∎

minus-minus-is-plus : (x : ℤ) → - (- x) ≡ x
minus-minus-is-plus (pos 0)        = refl
minus-minus-is-plus (pos (succ x)) = refl
minus-minus-is-plus (negsucc x)    = refl

subtraction-dist-over-mult₁ : (x : ℤ) → (y : ℕ) → x * (- negsucc y) ≡ - x * negsucc y
subtraction-dist-over-mult₁ x = induction base step
 where
  base : x * (- negsucc 0) ≡ - x * negsucc 0
  base = minus-minus-is-plus x ⁻¹

  step : (k : ℕ)
       → x * (- negsucc k) ≡ - x * negsucc k
       → x + x * (- negsucc k) ≡ - (- x) + x * negsucc k
  step k IH = x + x * (- negsucc k)         ≡⟨ ap (x +_) IH                                            ⟩
              x + (- x * negsucc k)         ≡⟨ ap (_+ (- (x * negsucc k)) ) (minus-minus-is-plus x ⁻¹) ⟩
              (- (- x)) + (- x * negsucc k) ≡⟨ subtraction-dist (- x) (x * negsucc k)                  ⟩
              - (- x) + x * negsucc k       ∎

subtraction-dist-over-mult : (x y : ℤ) → x * (- y) ≡ - (x * y)
subtraction-dist-over-mult x (pos y)     = subtraction-dist-over-mult₀ x y 
subtraction-dist-over-mult x (negsucc y) = subtraction-dist-over-mult₁ x y

subtraction-dist-over-mult' : (x y : ℤ) → (- x) * y ≡ - (x * y)
subtraction-dist-over-mult' x y = II
 where
  I : y * (- x) ≡ - (y * x)
  I = subtraction-dist-over-mult y x

  II : (- x) * y ≡ - x * y
  II = (- x) * y ≡⟨ ℤ*-comm (- x) y     ⟩
       y * (- x) ≡⟨ I                   ⟩
       - (y * x) ≡⟨ ap -_ (ℤ*-comm y x) ⟩
       - (x * y)   ∎

minus-times-minus-is-positive : (x y : ℤ) → (- x) * (- y) ≡ x * y
minus-times-minus-is-positive x y = (- x) * (- y) ≡⟨ subtraction-dist-over-mult' x (- y) ⟩
                                    - (x * (- y)) ≡⟨ ap -_ (subtraction-dist-over-mult x y) ⟩
                                    - (- (x * y)) ≡⟨ minus-minus-is-plus (x * y) ⟩
                                    x * y ∎
       
ℤ*-assoc₁ : (x y : ℤ) → (z : ℕ) → x * (y * negsucc z) ≡ (x * y) * negsucc z

ℤ*-assoc₁ x y = induction base step
 where
  base : x * (y * negsucc 0) ≡ (x * y) * negsucc 0
  base = subtraction-dist-over-mult x y

  step : (k : ℕ)
       → x * (y * negsucc k) ≡ (x * y) * negsucc k
       → x * (y * negsucc (succ k)) ≡ (x * y) * negsucc (succ k)
  step k IH = x * (y * negsucc (succ k))        ≡⟨ distributivity-mult-over-ℤ' (- y) (y * negsucc k) x            ⟩
              x * (- y) + x * (y * negsucc k)   ≡⟨ ap ((x * (- y)) +_) IH                                         ⟩
              x * (- y) + x * y * negsucc k     ≡⟨ ap (_+ ((x * y) * negsucc k)) (subtraction-dist-over-mult x y) ⟩ 
              (- x * y) + x * y * negsucc k     ∎

ℤ*-assoc : (x y z : ℤ) → x * (y * z) ≡ (x * y) * z
ℤ*-assoc x y (pos z)     = ℤ*-assoc₀ x y z
ℤ*-assoc x y (negsucc z) = ℤ*-assoc₁ x y z

open UF-Subsingletons -- TypeTopology

positive-is-prop : (x : ℤ) → is-prop (positive x)
positive-is-prop (pos x)     = 𝟙-is-prop
positive-is-prop (negsucc x) = 𝟘-is-prop

negative-is-prop : (x : ℤ) → is-prop (negative x)
negative-is-prop (pos x) = 𝟘-is-prop
negative-is-prop (negsucc x) = 𝟙-is-prop

greater-than-zero-is-positive : (z : ℤ) → greater-than-zero z → positive z
greater-than-zero-is-positive (negsucc x) g = g
greater-than-zero-is-positive (pos x)     g = unique-to-𝟙 g

greater-than-zero-is-prop : (z : ℤ) → is-prop (greater-than-zero z)
greater-than-zero-is-prop (pos 0)        = 𝟘-is-prop
greater-than-zero-is-prop (pos (succ x)) = 𝟙-is-prop
greater-than-zero-is-prop (negsucc x)    = 𝟘-is-prop

greater-than-zero-succℤ : (x : ℤ) → greater-than-zero x → greater-than-zero (succℤ x)
greater-than-zero-succℤ (pos 0)        g = 𝟘-elim g
greater-than-zero-succℤ (pos (succ x)) g = g
greater-than-zero-succℤ (negsucc x)    g = 𝟘-elim g

gtz₀ : (x : ℤ) → (y : ℕ) → greater-than-zero x → greater-than-zero (pos y) → greater-than-zero (x + (pos y))
gtz₀ x = induction base step
 where
  base : greater-than-zero x
       → greater-than-zero (pos 0)
       → greater-than-zero (x + pos 0)
  base l r = 𝟘-elim r

  step : (k : ℕ)
       → (greater-than-zero x → greater-than-zero (pos k) → greater-than-zero (x + pos k))
       → greater-than-zero x
       → greater-than-zero (pos (succ k))
       → greater-than-zero (x + pos (succ k))
  step 0        IH l r = greater-than-zero-succℤ x l
  step (succ k) IH l r = greater-than-zero-succℤ (x + pos (succ k)) (IH l r)

greater-than-zero-trans : (x y : ℤ) → greater-than-zero x → greater-than-zero y → greater-than-zero (x + y)
greater-than-zero-trans x (pos y)         = gtz₀ x y
greater-than-zero-trans x (negsucc y) l r = 𝟘-elim r

gtzmt₀ : (x : ℤ) → (y : ℕ) → greater-than-zero x → greater-than-zero (pos y) → greater-than-zero (x * pos y)
gtzmt₀ x = induction base step
 where
  base : greater-than-zero x → greater-than-zero (pos 0) → greater-than-zero (x * pos 0)
  base l r = 𝟘-elim r

  step : (k : ℕ)
       → (greater-than-zero x → greater-than-zero (pos k) → greater-than-zero (x * pos k))
       → greater-than-zero x
       → greater-than-zero (pos (succ k))
       → greater-than-zero (x * pos (succ k))
  step zero IH l r = l
  step (succ k) IH l r = greater-than-zero-trans x (x * pos (succ k)) l (IH l r)

greater-than-zero-mult-trans : (x y : ℤ) → greater-than-zero x → greater-than-zero y → greater-than-zero (x * y)
greater-than-zero-mult-trans x (negsucc y) l r = 𝟘-elim r
greater-than-zero-mult-trans x (pos y)     l r = gtzmt₀ x y l r

greater-than-zero-trans' : (x y : ℤ) → greater-than-zero x → positive y → greater-than-zero (x + y)
greater-than-zero-trans' (pos 0)        y              g p = 𝟘-elim g
greater-than-zero-trans' (pos (succ x)) (negsucc y)    g p = 𝟘-elim p
greater-than-zero-trans' (pos (succ x)) (pos 0)        g p = g
greater-than-zero-trans' (pos (succ x)) (pos (succ y)) g p = greater-than-zero-trans (pos (succ x)) (pos (succ y)) g p
greater-than-zero-trans' (negsucc x)    y              g p = 𝟘-elim g

negsucc-lc : {x y : ℕ} → negsucc x ≡ negsucc y → x ≡ y
negsucc-lc p = succ-lc (ap abs p)

open Unit-Properties -- TypeTopology

pos-not-negative : {x y : ℕ} → pos x ≢ negsucc y
pos-not-negative p = 𝟙-is-not-𝟘 (ap positive p)

neg-not-positive : {x y : ℕ} → negsucc x ≢ pos y
neg-not-positive p = pos-not-negative (p ⁻¹)

pos-int-not-zero : (x : ℕ) → pos (succ x) ≢ pos 0
pos-int-not-zero x p = positive-not-zero x (pos-lc p)

neg-int-not-zero : (x : ℕ) → negsucc x ≢ pos 0
neg-int-not-zero x p = positive-not-zero x (ap abs p)

open DiscreteAndSeparated -- TypeTopology

ℤ-is-discrete : is-discrete ℤ
ℤ-is-discrete (pos x) (pos y) = f (ℕ-is-discrete x y)
  where
    f : (x ≡ y) ∔ ¬ (x ≡ y) → (pos x ≡ pos y) ∔ ¬ (pos x ≡ pos y)
    f (inl z) = inl (ap pos z)
    f (inr z) = inr (λ k → z (pos-lc k))
ℤ-is-discrete (pos x)     (negsucc y) = inr pos-not-negative
ℤ-is-discrete (negsucc x) (pos y)     = inr neg-not-positive
ℤ-is-discrete (negsucc x) (negsucc y) = f (ℕ-is-discrete x y)
  where
    f : (x ≡ y) ∔ ¬ (x ≡ y) → decidable (negsucc x ≡ negsucc y)
    f (inl z) = inl (ap negsucc z)
    f (inr z) = inr (λ k → z (negsucc-lc k) )

open UF-Miscelanea -- TypeTopology

ℤ-is-set : is-set ℤ
ℤ-is-set = discrete-types-are-sets ℤ-is-discrete

positive-succℤ : (x : ℤ) → positive x → positive (succℤ x)
positive-succℤ (negsucc x) z = 𝟘-elim z
positive-succℤ (pos x)     z = unique-to-𝟙 z

positive-trans₀ : (x : ℤ) → (y : ℕ) → positive x → positive (x + pos y) 
positive-trans₀ x = induction base step
 where
  base : positive x → positive (x + pos 0)
  base p = p

  step : (k : ℕ)
       → (positive x → positive (x + pos k))
       → positive x
       → positive (x + pos (succ k))
  step k IH z = positive-succℤ (x + (pos k)) (IH z)

positive-trans : (x y : ℤ) → positive x →  positive y → positive (x + y) --NEED TO ADD THE REST OF THE CASES IN
positive-trans (negsucc x) (negsucc y) p q = 𝟘-elim p
positive-trans (negsucc x) (pos y)     p q = 𝟘-elim p
positive-trans (pos x)     (negsucc y) p q = 𝟘-elim q
positive-trans (pos x)     (pos y)     p q = positive-trans₀ (pos x) y (unique-to-𝟙 (positive (pos x + pos y)))

pos-succ-greater-than-zero : (x : ℕ) → greater-than-zero (pos (succ x))
pos-succ-greater-than-zero x = unique-to-𝟙 (greater-than-zero (pos (succ x)))

pos-succ-not-zero : (x : ℕ) → not-zero (pos (succ x))
pos-succ-not-zero x = λ z → z

open NaturalsAddition renaming (_+_ to _ℕ+_) -- TypeTopology

pos-addition-equiv-to-ℕ : (x y : ℕ) → pos x + pos y ≡ pos (x ℕ+ y)
pos-addition-equiv-to-ℕ x = induction base step
 where
  base : (pos x + pos 0) ≡ pos (x ℕ+ 0)
  base = refl

  step : (k : ℕ)
       → pos x + pos k        ≡ pos (x ℕ+ k)
       → pos x + pos (succ k) ≡ pos (x ℕ+ succ k)
  step k IH = pos x + pos (succ k)  ≡⟨ ap succℤ IH ⟩
              succℤ (pos (x ℕ+ k))  ∎

open NaturalsMultiplication renaming (_*_ to _ℕ*_)

pos-multiplication-equiv-to-ℕ : (x y : ℕ) → pos x * pos y ≡ pos (x ℕ* y)
pos-multiplication-equiv-to-ℕ x = induction base step
  where
    base : (pos x * pos 0) ≡ pos (x ℕ* 0)
    base = refl

    step : (k : ℕ) →
             (pos x * pos k) ≡ pos (x ℕ* k) →
             (pos x * pos (succ k)) ≡ pos (x ℕ* succ k)
    step k IH = (pos x * pos (succ k))   ≡⟨ ap (pos x +_) IH                    ⟩
                (pos x + pos (x ℕ* k))   ≡⟨ pos-addition-equiv-to-ℕ x (x ℕ* k) ⟩
                pos (x ℕ* succ k) ∎

ppnnp-lemma : (a b : ℕ) → Σ c ꞉ ℕ , negsucc a + negsucc b ≡ negsucc c
ppnnp-lemma a = induction base step
 where
  base : Sigma ℕ (λ c → negsucc a + negsucc 0 ≡ negsucc c)
  base = succ a , refl

  step : (k : ℕ) →
           Sigma ℕ (λ c → negsucc a + negsucc k ≡ negsucc c) →
           Sigma ℕ (λ c → negsucc a + negsucc (succ k) ≡ negsucc c)
  step k (c , IH) = succ c , ap predℤ IH


product-positive-negative-not-positive : (a b c : ℕ) → ¬ ((pos a * negsucc b) ≡ pos (succ c))
product-positive-negative-not-positive zero zero c e = 𝟘-elim (positive-not-zero c (pos-lc e ⁻¹))
product-positive-negative-not-positive zero (succ b) c e = 𝟘-elim (positive-not-zero c (I ⁻¹))
 where
  I : 0 ≡ succ c
  I = pos-lc (pos 0                    ≡⟨ ℤ-zero-left-is-zero (negsucc (succ b)) ⁻¹ ⟩
              pos 0 * negsucc (succ b) ≡⟨ e ⟩
              pos (succ c)             ∎)
product-positive-negative-not-positive (succ a) (succ b) c e = neg-not-positive (III ⁻¹ ∙ e)
  where
   II : Σ z ꞉ ℕ , succ z ≡ succ a ℕ* succ b
   II = pos-mult-is-succ a b

   z : ℕ
   z = pr₁ II

   IV : Σ c ꞉ ℕ , negsucc a + negsucc z ≡ negsucc c
   IV = ppnnp-lemma a z

   I : pos (succ a) * negsucc b ≡ negsucc z
   I = pos (succ a) * negsucc b        ≡⟨ refl ⟩
       pos (succ a) * (- pos (succ b)) ≡⟨ subtraction-dist-over-mult (pos (succ a)) (pos (succ b)) ⟩
       - (pos (succ a) * pos (succ b)) ≡⟨ ap -_ (pos-multiplication-equiv-to-ℕ (succ a) (succ b)) ⟩
       - pos (succ a ℕ* succ b)        ≡⟨ ap (λ - → -_ (pos -)) ((pr₂ II) ⁻¹) ⟩
       - pos (succ z)                  ≡⟨ refl ⟩
       negsucc z                       ∎

   III : negsucc a + pos (succ a) * negsucc b ≡ negsucc (pr₁ IV)
   III = ap ((negsucc a) +_) I ∙ pr₂ IV

ℤ-sum-of-inverse-is-zero₀ : (x : ℕ) → pos x + (- pos x) ≡ pos 0
ℤ-sum-of-inverse-is-zero₀ = induction base step
 where
  base : pos 0 + (- pos 0) ≡ pos 0
  base = refl

  step : (k : ℕ)
       → pos k + (- pos k)               ≡ pos 0
       → pos (succ k) + (- pos (succ k)) ≡ pos 0
  step 0        IH = refl
  step (succ k) IH = predℤ (pos (succ (succ k)) + negsucc k) ≡⟨ ℤ-left-pred (pos (succ (succ k))) (negsucc k) ⁻¹ ⟩
                     (pos (succ k) + (- pos (succ k)))       ≡⟨ IH                                               ⟩
                     pos 0                                   ∎

ℤ-sum-of-inverse-is-zero₁ : (x : ℕ) → negsucc x + (- (negsucc x)) ≡ pos 0
ℤ-sum-of-inverse-is-zero₁ = induction base step
 where
  base : (negsucc 0 + (- negsucc 0)) ≡ pos 0
  base = refl

  step : (k : ℕ)
       → negsucc k + (- negsucc k)               ≡ pos 0
       → negsucc (succ k) + (- negsucc (succ k)) ≡ pos 0
  step k IH = negsucc (succ k) + (- negsucc (succ k))  ≡⟨ ap succℤ (ℤ-left-succ (negsucc (succ k)) (pos k) ⁻¹) ⟩
              succℤ (succℤ (negsucc (succ k)) + pos k) ≡⟨ IH                                                   ⟩
              pos 0                                    ∎

ℤ-sum-of-inverse-is-zero : (x : ℤ) → x + (- x) ≡ pos 0
ℤ-sum-of-inverse-is-zero (pos x)     = ℤ-sum-of-inverse-is-zero₀ x
ℤ-sum-of-inverse-is-zero (negsucc x) = ℤ-sum-of-inverse-is-zero₁ x 

ℤ-mult-rearrangement : (x y z : ℤ) → (x * y) * z ≡ (x * z) * y
ℤ-mult-rearrangement x y z = x * y * z   ≡⟨ ℤ*-assoc x y z ⁻¹       ⟩
                             x * (y * z) ≡⟨ ap (x *_) (ℤ*-comm y z) ⟩
                             x * (z * y) ≡⟨ ℤ*-assoc x z y          ⟩
                             x * z * y   ∎

ℤ-mult-rearrangement' : (x y z : ℤ) → z * (x * y) ≡ y * (x * z)
ℤ-mult-rearrangement' x y z = z * (x * y) ≡⟨ ℤ*-comm z (x * y)          ⟩
                              x * y * z   ≡⟨ ℤ-mult-rearrangement x y z ⟩
                              x * z * y   ≡⟨ ℤ*-comm (x * z) y          ⟩
                              y * (x * z) ∎

ℤ-mult-rearrangement'' : (w x y z : ℤ) → (x * y) * (w * z) ≡ (w * y) * (x * z)
ℤ-mult-rearrangement'' w x y z = (x * y) * (w * z)     ≡⟨ ℤ-mult-rearrangement x y (w * z)     ⟩
                                (x * (w * z)) * y      ≡⟨ ap (_* y) (ℤ*-assoc x w z)           ⟩
                                ((x * w) * z) * y      ≡⟨ ap (λ a → (a * z) * y) (ℤ*-comm x w) ⟩
                                ((w * x) * z) * y      ≡⟨ ℤ*-assoc (w * x) z y ⁻¹              ⟩
                                (w * x) * (z * y)      ≡⟨ ap ((w * x) *_) (ℤ*-comm z y)        ⟩
                                (w * x) * (y * z)      ≡⟨ ℤ*-assoc (w * x) y z                 ⟩
                                ((w * x) * y) * z      ≡⟨ ap (_* z) (ℤ*-assoc w x y ⁻¹)        ⟩
                                (w * (x * y)) * z      ≡⟨ ap (λ a → (w * a) * z) (ℤ*-comm x y) ⟩
                                (w * (y * x)) * z      ≡⟨ ap (_* z) (ℤ*-assoc w y x)           ⟩
                                ((w * y) * x) * z      ≡⟨ ℤ*-assoc (w * y) x z ⁻¹              ⟩
                                (w * y) * (x * z) ∎

ℤ-mult-rearrangement''' : (x y z : ℤ) → x * (y * z) ≡ y * (x * z)
ℤ-mult-rearrangement''' x y z = x * (y * z) ≡⟨ ℤ*-assoc x y z ⟩
                                x * y * z   ≡⟨ ap (_* z) (ℤ*-comm x y) ⟩
                                y * x * z   ≡⟨ ℤ*-assoc y x z ⁻¹ ⟩
                                y * (x * z) ∎

abs-removes-neg-sign : (x : ℤ) → abs x ≡ abs (- x)
abs-removes-neg-sign (pos zero)     = refl
abs-removes-neg-sign (pos (succ x)) = refl
abs-removes-neg-sign (negsucc x)    = refl

absℤ-removes-neg-sign : (x : ℤ) → absℤ x ≡ absℤ (- x)
absℤ-removes-neg-sign (pos zero)     = refl
absℤ-removes-neg-sign (pos (succ x)) = refl
absℤ-removes-neg-sign (negsucc x)    = refl

abs-over-mult : (a b : ℤ) → abs (a * b) ≡ abs a ℕ* abs b
abs-over-mult (pos x) (pos b) = I
 where
  I : abs (pos x * pos b) ≡ abs (pos x) ℕ* abs (pos b)
  I = abs (pos x * pos b)        ≡⟨ ap abs (pos-multiplication-equiv-to-ℕ x b) ⟩
      abs (pos (x ℕ* b))         ≡⟨ refl ⟩
      abs (pos x) ℕ* abs (pos b) ∎
abs-over-mult (pos zero) (negsucc b) = I
 where
  I : abs (pos zero * negsucc b) ≡ abs (pos zero) ℕ* abs (negsucc b)
  I = abs (pos zero * negsucc b) ≡⟨ ap abs (ℤ-zero-left-is-zero (negsucc b)) ⟩
      abs (pos 0)                ≡⟨ zero-left-is-zero (abs (negsucc b)) ⁻¹ ⟩
      abs (pos zero) ℕ* abs (negsucc b) ∎
abs-over-mult (pos (succ x)) (negsucc b) = I
 where
  I : abs (pos (succ x) * negsucc b) ≡ abs (pos (succ x)) ℕ* abs (negsucc b)
  I = abs (pos (succ x) * negsucc b)           ≡⟨ ap abs (subtraction-dist-over-mult (pos (succ x)) (pos (succ b))) ⟩
      abs (- ((pos (succ x) * pos (succ b))))  ≡⟨ ap (λ z → (abs (- z))) (pos-multiplication-equiv-to-ℕ (succ x) (succ b)) ⟩
      abs (- pos (succ x ℕ* succ b))           ≡⟨ abs-removes-neg-sign ( pos (succ x ℕ* succ b)) ⁻¹ ⟩
      abs (pos (succ x ℕ* succ b))             ≡⟨ refl ⟩
      succ x ℕ* succ b                         ≡⟨ refl ⟩
      abs (pos (succ x)) ℕ* abs (negsucc b)    ∎
abs-over-mult (negsucc x) (pos b) = I
 where
  I : abs (negsucc x * pos b) ≡ abs (negsucc x) ℕ* abs (pos b)
  I = abs (negsucc x * pos b)        ≡⟨ ap abs (subtraction-dist-over-mult' (pos (succ x)) (pos b)) ⟩
      abs (- pos (succ x) * pos b)   ≡⟨ ap (λ z → abs (- z)) (pos-multiplication-equiv-to-ℕ (succ x) b) ⟩
      abs (- pos (succ x ℕ* b))      ≡⟨ abs-removes-neg-sign (pos (succ x ℕ* b)) ⁻¹ ⟩
      (succ x) ℕ* b                  ≡⟨ refl ⟩
      abs (negsucc x) ℕ* abs (pos b) ∎
abs-over-mult (negsucc x) (negsucc b) = I
 where
  I : abs (negsucc x * negsucc b) ≡ abs (negsucc x) ℕ* abs (negsucc b)
  I = abs (negsucc x * negsucc b)               ≡⟨ ap abs (subtraction-dist-over-mult (negsucc x) (pos (succ b))) ⟩
      abs (- negsucc x * pos (succ b) )         ≡⟨ ap (λ z → abs (- z)) (subtraction-dist-over-mult' (pos (succ x)) (pos (succ b))) ⟩
      abs (- (- pos (succ x) * pos (succ b)))   ≡⟨ ap abs (minus-minus-is-plus (pos (succ x) * pos (succ b))) ⟩
      abs (pos (succ x) * pos (succ b))         ≡⟨ ap abs (pos-multiplication-equiv-to-ℕ (succ x) (succ b)) ⟩
      (succ x) ℕ* (succ b)                      ≡⟨ refl ⟩
      abs (negsucc x) ℕ* abs (negsucc b)       ∎

pos-abs-is-equal : (x : ℕ) → absℤ (pos x) ≡ pos x
pos-abs-is-equal x = refl

abs-over-mult' : (x y : ℤ) → absℤ (x * y) ≡ absℤ x * absℤ y
abs-over-mult' (pos x) (pos y) = I
 where
  I : absℤ (pos x * pos y) ≡ absℤ (pos x) * absℤ (pos y)
  I = absℤ (pos x * pos y) ≡⟨ ap absℤ (pos-multiplication-equiv-to-ℕ x y) ⟩
      absℤ (pos (x ℕ* y))  ≡⟨ by-definition ⟩
      pos (x ℕ* y)         ≡⟨ pos-multiplication-equiv-to-ℕ x y ⁻¹ ⟩
      pos x * pos y        ≡⟨ by-definition ⟩
      absℤ (pos x) * absℤ (pos y) ∎
abs-over-mult' (pos x) (negsucc y) = I
 where
  I : absℤ (pos x * negsucc y) ≡ absℤ (pos x) * absℤ (negsucc y)
  I = absℤ (pos x * negsucc y)        ≡⟨ ap absℤ (subtraction-dist-over-mult (pos x) (pos (succ y))) ⟩
      absℤ (- pos x * pos (succ y))   ≡⟨ ap (λ z → absℤ (- z)) (pos-multiplication-equiv-to-ℕ x (succ y)) ⟩
      absℤ (- pos (x ℕ* succ y))      ≡⟨ absℤ-removes-neg-sign (pos (x ℕ* succ y)) ⁻¹ ⟩
      absℤ (pos (x ℕ* succ y))        ≡⟨ by-definition ⟩
      pos (x ℕ* succ y)               ≡⟨ pos-multiplication-equiv-to-ℕ x (succ y) ⁻¹ ⟩
      pos x * pos (succ y)            ≡⟨ by-definition ⟩
      absℤ (pos x) * absℤ (negsucc y) ∎
abs-over-mult' (negsucc x) (pos y) = I
 where
  I : absℤ (negsucc x * pos y) ≡ absℤ (negsucc x) * absℤ (pos y)
  I = absℤ (negsucc x * pos y)      ≡⟨ ap absℤ (ℤ*-comm (negsucc x) (pos y)) ⟩
      absℤ (pos y * negsucc x)      ≡⟨ ap absℤ (subtraction-dist-over-mult (pos y) (pos (succ x))) ⟩
      absℤ (- pos y * pos (succ x)) ≡⟨ ap (λ z → absℤ (- z)) (pos-multiplication-equiv-to-ℕ y (succ x)) ⟩
      absℤ (- pos (y ℕ* succ x))    ≡⟨ absℤ-removes-neg-sign (pos (y ℕ* succ x)) ⁻¹ ⟩
      absℤ (pos (y ℕ* succ x))      ≡⟨ by-definition ⟩
      pos (y ℕ* succ x)             ≡⟨ pos-multiplication-equiv-to-ℕ y (succ x) ⁻¹ ⟩
      pos y * pos (succ x)          ≡⟨ ℤ*-comm (pos y) (pos (succ x)) ⟩
      pos (succ x) * pos y          ≡⟨ by-definition ⟩ 
      absℤ (negsucc x) * absℤ (pos y) ∎
abs-over-mult' (negsucc x) (negsucc y) = I
 where
  I : absℤ (negsucc x * negsucc y) ≡ absℤ (negsucc x) * absℤ (negsucc y)
  I = absℤ (negsucc x * negsucc y)        ≡⟨ ap absℤ (minus-times-minus-is-positive (pos (succ x)) (pos (succ y))) ⟩
      absℤ (pos (succ x) * pos (succ y))  ≡⟨ ap absℤ (pos-multiplication-equiv-to-ℕ (succ x) (succ y)) ⟩
      absℤ (pos (succ x ℕ* succ y))       ≡⟨ by-definition ⟩
      pos (succ x ℕ* succ y)              ≡⟨ pos-multiplication-equiv-to-ℕ (succ x) (succ y) ⁻¹ ⟩
      pos (succ x) * pos (succ y)         ≡⟨ by-definition ⟩
      absℤ (negsucc x) * absℤ (negsucc y) ∎

open Groups -- TypeTopology

integers-+-group : Group-structure ℤ
integers-+-group = _+_ , ℤ-is-set , ℤ+-assoc , (pos 0) , (ℤ-zero-left-neutral , ℤ-zero-right-neutral , (λ x → (- x) , ((ℤ+-comm (- x) x ∙ ℤ-sum-of-inverse-is-zero x) , (ℤ-sum-of-inverse-is-zero x))))

\end{code}
