Andrew Sneap - 27th April 2021

I link to this module within the Integers section of my report.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆) --TypeTopology

import NaturalsAddition --TypeTopology

import NaturalsMultiplication

module Integers where

data ℤ : 𝓤₀ ̇ where 
 pos     : ℕ → ℤ
 negsucc : ℕ → ℤ

predℤ : ℤ → ℤ
predℤ (pos 0)        = negsucc 0
predℤ (pos (succ x)) = pos x
predℤ (negsucc x)    = negsucc (succ x)

succℤ : ℤ → ℤ
succℤ (pos x)            = pos (succ x)
succℤ (negsucc 0)        = pos 0
succℤ (negsucc (succ x)) = negsucc x

ℤ-induction : {A : ℤ → 𝓤 ̇} → A (pos 0)
                             → ((k : ℤ) → A k → A (succℤ k))
                             → ((k : ℤ) → A (succℤ k) → A k)
                             → (x : ℤ)
                             → A x 
ℤ-induction base step₀ step₁ (pos 0)            = base
ℤ-induction base step₀ step₁ (pos (succ x))     = step₀ (pos x) (ℤ-induction base step₀ step₁ (pos x))
ℤ-induction base step₀ step₁ (negsucc 0)        = step₁ (negsucc 0) base
ℤ-induction base step₀ step₁ (negsucc (succ x)) = step₁ (negsucc (succ x)) (ℤ-induction base step₀ step₁ (negsucc x))

succpredℤ : (x : ℤ) → succℤ (predℤ x) ≡ x 
succpredℤ (pos 0)        = refl
succpredℤ (pos (succ x)) = refl
succpredℤ (negsucc x)    = refl

predsuccℤ : (x : ℤ) → predℤ (succℤ x) ≡ x 
predsuccℤ (pos x)            = refl
predsuccℤ (negsucc 0)        = refl
predsuccℤ (negsucc (succ x)) = refl

-_ : ℤ → ℤ
-_ (pos 0)        = pos 0
-_ (pos (succ x)) = negsucc x
-_ (negsucc x)    = pos (succ x)

infix 30 -_

predminus : (x : ℤ) → predℤ (- x) ≡ (- succℤ x)
predminus (pos 0)            = refl
predminus (pos (succ x))     = refl
predminus (negsucc 0)        = refl
predminus (negsucc (succ x)) = refl

abs : ℤ → ℕ
abs (pos x)     = x
abs (negsucc x) = succ x

absℤ : ℤ → ℤ
absℤ (pos x)     = pos x
absℤ (negsucc x) = pos (succ x)

_+pos_ : ℤ → ℕ → ℤ 
x +pos 0      = x
x +pos succ y = succℤ (x +pos y)

_+negsucc_ : ℤ → ℕ → ℤ 
x +negsucc 0      = predℤ x
x +negsucc succ y = predℤ (x +negsucc y)

open NaturalsAddition renaming (_+_ to _ℕ+_) --TypeTopology

_+_ : ℤ → ℤ → ℤ 
x + pos y     = x +pos y
x + negsucc y = x +negsucc y

infixl 31 _+_

_*_ : ℤ → ℤ → ℤ
x * pos 0            = pos 0
x * pos (succ y)     = x + (x * pos y)
x * negsucc 0        = - x
x * negsucc (succ y) = (- x) + (x * negsucc y)

open NaturalsMultiplication renaming (_*_ to _ℕ*_)

infixl 32 _*_

_-_ : ℤ → ℤ → ℤ 
x - y = x + (- y)

positive : ℤ → 𝓤₀ ̇
positive (pos x)     = 𝟙
positive (negsucc x) = 𝟘

negative : ℤ → 𝓤₀ ̇
negative (pos x)     = 𝟘
negative (negsucc x) = 𝟙

is-zero : ℤ → 𝓤₀ ̇
is-zero (pos 0)        = 𝟙
is-zero (pos (succ x)) = 𝟘
is-zero (negsucc x)    = 𝟘

not-zero : ℤ → 𝓤₀ ̇
not-zero z = ¬ (is-zero z)

greater-than-zero : ℤ → 𝓤₀ ̇
greater-than-zero (pos 0)        = 𝟘
greater-than-zero (pos (succ z)) = 𝟙
greater-than-zero (negsucc z)    = 𝟘


\end{code}
