{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _⊹_ ; * to ⋆) --TypeTopology
open import Integers
open import DecidableAndDetachable
open import DiscreteAndSeparated
open import NaturalNumbers-Properties
open import NaturalsOrder renaming (_<_ to _<ℕ_ ; _≤_ to _≤ℕ_)
open import UF-Base
open import UF-Subsingletons
open import UF-Miscelanea
open import UF-FunExt
open import IntegersProperties
open import UF-Subsingletons-FunExt
-- open import IntegersOrder

{-# BUILTIN INTEGER       ℤ       #-}
{-# BUILTIN INTEGERPOS    pos     #-}
{-# BUILTIN INTEGERNEGSUC negsucc #-}

module Reals2 (fe : FunExt) where

to-zero : ℤ → ℤ
to-zero (pos n) = pos (pred n)
to-zero (negsucc n) = negsucc (pred n)

Interval : 𝓤₀ ̇
Interval = ℤ × ℤ
-- ⟦ (k , p) ⟧ = [k/2ᵖ⁺¹ , (k+2)/2ᵖ⁺¹]

codeOf precOf : Interval → ℤ
codeOf = pr₁
precOf = pr₂

_/2 : ℕ → ℕ
0 /2 = 0
1 /2 = 0
succ (succ n) /2 = succ (n /2)

−_ : Interval → Interval
− (k , p) = (negsucc 1 - k , p)

downLeft downMid downRight upRight : ℤ → ℤ
downLeft  k           = k + k          
downMid   k           = k + k + pos 1  
downRight k           = k + k + pos 2  
upRight   (pos x)     = pos     (x /2) 
upRight   (negsucc x) = negsucc (x /2)

_≤ℤ_ : (a b : ℤ) → 𝓤₀ ̇
a ≤ℤ b = Σ c ꞉ ℕ , a + pos c ≡ b

_<ℤ_ : (a b : ℤ) → 𝓤₀ ̇
a <ℤ b = succℤ a ≤ℤ b

_≤ℤ_≤ℤ_ : (a b c : ℤ) → 𝓤₀ ̇
a ≤ℤ b ≤ℤ c = (a ≤ℤ b) × (b ≤ℤ c)

pos-< : (a b : ℕ) → a <ℕ b → pos a <ℤ pos b
pos-< = {!!}

ℤ-trich : (a b : ℤ) → (a <ℤ b) ⊹ (a ≡ b) ⊹ (b <ℤ a)
ℤ-trich = {!!}

data 𝟛 : 𝓤₀ ̇ where
  −1 O +1 : 𝟛

match𝟛 : {X : 𝓤 ̇ } → (a : 𝟛) → X → X → X → X
match𝟛 −1 x y z = x
match𝟛  O x y z = y
match𝟛 +1 x y z = z

_∶∶_ : {X : 𝓤 ̇ } → X → (ℕ → X) → (ℕ → X)
(a ∶∶ α) 0 = a
(a ∶∶ α) (succ n) = α n

down : 𝟛 → (ℤ → ℤ)
down −1 = downLeft
down  O = downMid
down +1 = downRight

[-1,1] : Interval
[-1,1] = (negsucc 0 , negsucc 0)

conv→ conv→' : (ℕ → 𝟛) → (ℕ → ℤ)
conv→' α 0 = negsucc 0
conv→' α (succ n) = conv→ α n
conv→ α n = down (α n) (conv→' α n)

_-immediatelyDownFrom-_ : ℤ → ℤ → 𝓤₀ ̇
i -immediatelyDownFrom- j
 = (i ≡ downLeft j) ⊹ (i ≡ downMid j) ⊹ (i ≡ downRight j)

Real : 𝓤₀ ̇
Real = Σ x ꞉ (ℤ → ℤ)
     , Π n ꞉ ℤ , (x n) -immediatelyDownFrom- (x (predℤ n))

CompactInterval : Interval → 𝓤₀ ̇
CompactInterval _ = ℕ → ℤ

CompactToReal : (i : Interval) → CompactInterval i → Real
CompactToReal (k , p) α = β , γ where
  β : ℤ → ℤ
  β n = Cases (ℤ-trich n p) (λ (a , _) → {!!}) (cases (λ _ → k) λ (a , _) → {!!})
  γ : (n : ℤ) → β n -immediatelyDownFrom- β (predℤ n)
  γ n = {!!}
  
 -- if n ≡ p then k
 -- if n > p then calculate from α
 -- if n < p then upRightⁿ (n - p) k
