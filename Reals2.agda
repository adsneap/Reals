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

_+ℕ_ : ℕ → ℕ → ℕ
a +ℕ 0 = a
a +ℕ succ b = succ (a +ℕ b)

1+ℕ : (a : ℕ) → 1 +ℕ a ≡ succ a
1+ℕ zero = refl
1+ℕ (succ a) = ap succ (1+ℕ a)

+-pos : (a b : ℕ) → pos (a +ℕ b) ≡ pos a + pos b
+-pos a 0 = refl
+-pos a (succ b) = ap succℤ (+-pos a b)

+-negsucc : (a b : ℕ) → negsucc (a +ℕ b) ≡ succℤ (negsucc a + negsucc b)
+-negsucc a 0 = refl
+-negsucc a (succ b)
 = ap predℤ  (+-negsucc a b)
 ∙ predsuccℤ (negsucc a +negsucc b)
 ∙ succpredℤ (negsucc a +negsucc b) ⁻¹

+-pred-negsucc : (a b : ℕ)
               → predℤ (negsucc a) +pos b ≡ predℤ (negsucc a +pos b)
+-pred-negsucc a zero = refl
+-pred-negsucc a (succ b) = ap succℤ (+-pred-negsucc a b)
                          ∙ succpredℤ _
                          ∙ predsuccℤ _ ⁻¹

+-negsucc-pos : (a b : ℕ) → negsucc (a +ℕ b) +pos b ≡ negsucc a
+-negsucc-pos a zero = refl
+-negsucc-pos a (succ b)
 = ap (λ ─ → succℤ ─) (+-pred-negsucc (a +ℕ b) b)
 ∙ succpredℤ (negsucc (a +ℕ b) +pos b)
 ∙ +-negsucc-pos a b
 
succ+ℕ : (a b : ℕ) → succ (a +ℕ b) ≡ succ a +ℕ b
succ+ℕ a zero = refl
succ+ℕ a (succ b) = ap succ (succ+ℕ a b)

succ+ℤ : (a b : ℤ) → succℤ (a + b) ≡ succℤ a + b
succ+ℤ a (pos zero) = refl
succ+ℤ a (pos (succ x))
 = ap succℤ (succ+ℤ a (pos x))
succ+ℤ a (negsucc zero)
 = succpredℤ _ ∙ predsuccℤ _ ⁻¹
succ+ℤ a (negsucc (succ x))
 = succpredℤ _ ∙ predsuccℤ _ ⁻¹ ∙ ap predℤ (succ+ℤ a (negsucc x))

to-zero : ℤ → ℤ
to-zero (pos n) = pos (pred n)
to-zero (negsucc n) = negsucc (pred n)

from-zero : ℤ → ℤ
from-zero (pos n) = pos (succ n)
from-zero (negsucc n) = negsucc (succ n)

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

upRightⁿ : ℤ → ℕ → ℤ
upRightⁿ k 0 = k
upRightⁿ k (succ n) = upRight (upRightⁿ k n)

_≤ℤ_ : (a b : ℤ) → 𝓤₀ ̇
a ≤ℤ b = Σ c ꞉ ℕ , a + pos c ≡ b

_<ℤ_ : (a b : ℤ) → 𝓤₀ ̇
a <ℤ b = succℤ a ≤ℤ b

_≤ℤ_≤ℤ_ : (a b c : ℤ) → 𝓤₀ ̇
a ≤ℤ b ≤ℤ c = (a ≤ℤ b) × (b ≤ℤ c)

_<ℕ2_ : ℕ → ℕ → 𝓤₀ ̇
a <ℕ2 b = Σ c ꞉ ℕ , succ a +ℕ c ≡ b

<ℕ-succ : (a b : ℕ) → a <ℕ2 b → succ a <ℕ2 succ b
<ℕ-succ a b (d , e) = d , (succ+ℕ (succ a) d ⁻¹ ∙ ap succ e)

pos-< : (a b : ℕ) → a <ℕ2 b → pos a <ℤ pos b
pos-< a b (d , e) = d , (+-pos (succ a) d ⁻¹ ∙ ap pos e)

ℕ-trich : (a b : ℕ) → (a <ℕ2 b) ⊹ (a ≡ b) ⊹ (b <ℕ2 a)
ℕ-trich zero zero = inr (inl refl)
ℕ-trich zero (succ b) = inl (b , 1+ℕ b)
ℕ-trich (succ a) zero = (inr ∘ inr) (a , 1+ℕ a)
ℕ-trich (succ a) (succ b)
 = Cases (ℕ-trich a b)
   (inl ∘ <ℕ-succ a b)
   (cases
   (inr ∘ inl ∘ ap succ)
   (inr ∘ inr ∘ <ℕ-succ b a))

+ℕℤ-assoc : ∀ a b c → a +pos (b +ℕ c) ≡ (a +pos b) +pos c
+ℕℤ-assoc a b zero = refl
+ℕℤ-assoc a b (succ c) = ap succℤ (+ℕℤ-assoc a b c)

<ℤ-trans : {a b c : ℤ} → a <ℤ b → b <ℤ c → a <ℤ c
<ℤ-trans {a} {b} {c} (d₁ , e₁) (d₂ , e₂)
 = (d₁ +ℕ (succ d₂))
 , (+ℕℤ-assoc (succℤ a) d₁ (succ d₂)
 ∙ (ap succℤ (ap (_+pos d₂) e₁) ∙ succ+ℤ b (pos d₂))
 ∙ e₂)

negsucc<−1 : (a : ℕ) → negsucc (succ a) <ℤ negsucc 0
negsucc<−1 zero = 0 , refl
negsucc<−1 (succ a) = <ℤ-trans (0 , refl) (negsucc<−1 a)

−1<pos : (a : ℕ) → negsucc 0 <ℤ pos a
−1<pos zero = zero , refl
−1<pos (succ a) = <ℤ-trans {negsucc 0} (−1<pos a) (0 , refl)

negsucc<pos : (a b : ℕ) → negsucc a <ℤ pos b
negsucc<pos 0 b = −1<pos b
negsucc<pos (succ a) b = <ℤ-trans (negsucc<−1 a) (−1<pos b)

a<b-negsucc : (a b : ℕ)
            → negsucc a <ℤ negsucc b
            → negsucc (succ a) <ℤ negsucc (succ b)
a<b-negsucc a b (d , e)
 = d , (predsuccℤ _ ⁻¹
     ∙ ap predℤ (succ+ℤ (negsucc a) (pos d) ∙ e))

a<b-negsucc⁻¹ : (a b : ℕ)
              → negsucc (succ a) <ℤ negsucc (succ b)
              → negsucc a <ℤ negsucc b
a<b-negsucc⁻¹ a b (d , e)
 = d , (succ+ℤ (negsucc a) (pos d) ⁻¹
     ∙ ap succℤ e)

casta<b : ∀ a b → a <ℕ2 b →
      (negsucc a <ℤ negsucc b) ⊹
      (negsucc a ≡ negsucc b) ⊹ (negsucc b <ℤ negsucc a)
casta<b zero zero (zero , ())
casta<b zero zero (succ d , ())
casta<b zero (succ b) (d , e) = (inr ∘ inr) (negsucc<−1 b)
casta<b (succ a) zero (d , e) = inl (negsucc<−1 a)
casta<b (succ a) (succ b) (d , e)
 = Cases (casta<b a b (d , ap pred (succ+ℕ (succ a) d ∙ e)))
     (inl ∘ a<b-negsucc a b)
     (cases
     (inr ∘ inl ∘ ap from-zero)
     (inr ∘ inr ∘ a<b-negsucc b a))

ℤ-trich : (a b : ℤ) → (a <ℤ b) ⊹ (a ≡ b) ⊹ (b <ℤ a)
ℤ-trich (pos a) (pos b)
 = Cases (ℕ-trich a b)
   (inl ∘ pos-< a b)
   (cases
   (inr ∘ inl ∘ ap pos)
   (inr ∘ inr ∘ pos-< b a))
ℤ-trich (pos a) (negsucc b)
 = (inr ∘ inr) (negsucc<pos b a)
ℤ-trich (negsucc a) (pos b)
 = inl (negsucc<pos a b)
ℤ-trich (negsucc a) (negsucc b)
 = Cases (ℕ-trich a b)
   (casta<b a b)
   (cases
   (inr ∘ inl ∘ ap negsucc)
   (λ f → Cases (casta<b b a f) (inr ∘ inr)
     (cases
     (inr ∘ inl ∘ _⁻¹)
     inl)))

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
CompactInterval (k , p)
 = Σ α ꞉ (ℕ → ℤ)  , (α 0 -immediatelyDownFrom- k)
 × (Π n ꞉ ℕ , α (succ n) -immediatelyDownFrom- α n)

halfEq : (n : ℕ) → (n ≡ (n /2) +ℕ (n /2)) ⊹ (n ≡ succ ((n /2) +ℕ (n /2)))
halfEq 0 = inl refl
halfEq 1 = inr refl
halfEq (succ (succ n))
 = Cases (halfEq n)
    (λ f → inl (ap (succ ∘ succ) f ∙ ap succ (succ+ℕ (n /2) (n /2))))
    (λ g → inr (ap (succ ∘ succ) g ∙ ap succ (succ+ℕ (n /2) (succ (n /2)))))

ap-× : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x₁ x₂ : X} {y₁ y₂ : Y}
     → x₁ ≡ x₂ → y₁ ≡ y₂ → (x₁ , y₁) ≡ (x₂ , y₂)
ap-× {𝓤} {𝓥} {X} {Y} {x₁} {.x₁} {y₁} {.y₁} refl refl = refl

upRightEq : (i : ℤ) → (i ≡ downLeft (upRight i)) ⊹ (i ≡ downMid (upRight i))
upRightEq (pos k)
  = Cases (halfEq k)
      (λ f → inl (ap pos f ∙ +-pos (k /2) (k /2)))
      (λ g → inr (ap pos g ∙ ap succℤ (+-pos (k /2) (k /2))))
upRightEq (negsucc k)
  = Cases (halfEq k)
      (λ f → inr (ap negsucc f ∙ +-negsucc (k /2) (k /2)))
      (λ g → inl (ap negsucc g ∙ ap predℤ (+-negsucc (k /2) (k /2))
                       ∙ predsuccℤ (negsucc (k /2) +negsucc (k /2))))

downLeftIsDown : (i : ℤ) → downLeft i -immediatelyDownFrom- i
downLeftIsDown i = inl refl

downMidIsDown : (i : ℤ) → downMid i -immediatelyDownFrom- i
downMidIsDown i = (inr ∘ inl) refl

downRightIsDown : (i : ℤ) → downRight i -immediatelyDownFrom- i
downRightIsDown i = (inr ∘ inr) refl

downFromUpRight : (i : ℤ) → i -immediatelyDownFrom- upRight i
downFromUpRight i
 = Cases (upRightEq i)
     (λ e → transport (_-immediatelyDownFrom- upRight i)
              (e ⁻¹) (downLeftIsDown (upRight i)))
     (λ e → transport (_-immediatelyDownFrom- upRight i)
              (e ⁻¹) (downMidIsDown (upRight i)))

Cases-property : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {P : A → 𝓣 ̇ }
               → (xy : X ⊹ Y) {f : X → A} {g : Y → A}
               → Π (P ∘ f)
               → Π (P ∘ g)
               → P (Cases xy f g)
Cases-property (inl x) F G = F x
Cases-property (inr y) F G = G y

back : {n p : ℤ} (e : (n <ℤ p) ⊹ (n ≡ p) ⊹ (p <ℤ n))
     → (predℤ n <ℤ p) ⊹ (predℤ n ≡ p) ⊹ (p <ℤ predℤ n)
back {n} {p} (inl (d , e))
 = inl (succ d , (ap (λ ─ → succℤ (─ +pos d)) (succpredℤ n) ∙ succ+ℤ n (pos d) ∙ e))
back {n} {.n} (inr (inl refl))
 = inl (0 , succpredℤ n)
back {n} {p} (inr (inr (0 , e)))
 = inr (inl (ap predℤ (e ⁻¹) ∙ predsuccℤ p))
back {n} {p} (inr (inr (succ d , e)))
 = inr (inr (d , succℤ-lc (e ∙ succpredℤ n ⁻¹)))

succℤ≢ : {n : ℤ} → succℤ n ≢ n
succℤ≢ {negsucc 0} ()
succℤ≢ {negsucc (succ x)} ()

succℤ≢2 : (n : ℤ) (d : ℕ) → n +pos (succ d) ≢ n
succℤ≢2 n 0 = succℤ≢ 
succℤ≢2 n (succ d) e = {!!}
    
ℤ-trich-is-prop : (n p : ℤ) → is-prop ((n <ℤ p) ⊹ (n ≡ p) ⊹ (p <ℤ n))
ℤ-trich-is-prop n p = +-is-prop {!!} (+-is-prop {!!} {!!} {!!}) {!!}
 where
   δ : (n p : ℤ) → n <ℤ p → ¬ (n ≡ p)
   δ n .n (d , e₁) refl = succℤ≢2 n d (succ+ℤ n (pos d) ∙ e₁)
   ζ : (n p : ℤ) → n <ℤ p → ¬ (p <ℤ n)
   ζ n p (d₁ , e₁) (d₂ , e₂) = {!!}
   γ : (n p : ℤ) → n ≡ p → ¬ (p <ℤ n)
   γ n .n refl (zero , e) = {!!}
   γ n .n refl (succ d , e) = {!d !}

CompactToReal : (i : Interval) → CompactInterval i → Real
CompactToReal (k , p) (α , f , g)
 = (λ n → β n (ℤ-trich n p)) , (λ n → γ n (ℤ-trich n p))  where
  β : (n : ℤ) → (n <ℤ p) ⊹ (n ≡ p) ⊹ (p <ℤ n) → ℤ
  β n (inl (d , _))       = upRightⁿ k (succ d)
  β n (inr (inl _))       = k
  β n (inr (inr (d , _))) = α d
  δ : (n : ℤ) → (e : (n <ℤ p) ⊹ (n ≡ p) ⊹ (p <ℤ n))
    → β n e -immediatelyDownFrom-
      β (predℤ n) (back e)
  δ n (inl (d , e))            = downFromUpRight (β n (inl (d , e)))
  δ n (inr (inl refl))         = downFromUpRight (β n (inr (inl refl)))
  δ n (inr (inr (0 , e)))      = f
  δ n (inr (inr (succ d , e))) = g d
  γ : (n : ℤ) → (n <ℤ p) ⊹ (n ≡ p) ⊹ (p <ℤ n)
    → β n (ℤ-trich n p) -immediatelyDownFrom-
      β (predℤ n) (ℤ-trich (predℤ n) p)
  γ n e
   = transport
       (λ ─ → β n ─ -immediatelyDownFrom- β (predℤ n) (ℤ-trich (predℤ n) p))
       (ℤ-trich-is-prop n p e (ℤ-trich n p))
       (transport
       (λ ─ → β n e -immediatelyDownFrom- β (predℤ n) ─)
       (ℤ-trich-is-prop (predℤ n) p (back e) (ℤ-trich (predℤ n) p))
       (δ n e))

 -- if n < p then upRightⁿ (n - p) k
 -- if n ≡ p then k
 -- if n > p then calculate from α
