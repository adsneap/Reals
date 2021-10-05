{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _⊹_ ; * to ⋆) --TypeTopology
open import Integers
open import DecidableAndDetachable
open import DiscreteAndSeparated
open import NaturalNumbers-Properties
open import UF-Base
open import UF-Subsingletons
open import UF-Miscelanea
open import UF-FunExt
open import IntegersProperties
open import UF-Subsingletons-FunExt
open import UF-Equiv
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

from-zero : ℤ → ℤ
from-zero (pos n) = pos (succ n)
from-zero (negsucc n) = negsucc (succ n)

Interval : 𝓤₀ ̇
Interval = ℤ × ℤ
-- ⟦ (k , p) ⟧ = [k/2ᵖ⁺¹ , (k+2)/2ᵖ⁺¹]

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

_<ℕ_ : ℕ → ℕ → 𝓤₀ ̇
a <ℕ b = Σ c ꞉ ℕ , succ a +ℕ c ≡ b

<ℕ-succ : (a b : ℕ) → a <ℕ b → succ a <ℕ succ b
<ℕ-succ a b (d , e) = d , (succ+ℕ (succ a) d ⁻¹ ∙ ap succ e)

pos-< : (a b : ℕ) → a <ℕ b → pos a <ℤ pos b
pos-< a b (d , e) = d , (+-pos (succ a) d ⁻¹ ∙ ap pos e)

ℕ-trich : (a b : ℕ) → (a <ℕ b) ⊹ (a ≡ b) ⊹ (b <ℕ a)
ℕ-trich zero zero = inr (inl refl)
ℕ-trich zero (succ b) = inl (b , 1+ℕ b)
ℕ-trich (succ a) zero = (inr ∘ inr) (a , 1+ℕ a)
ℕ-trich (succ a) (succ b)
 = Cases (ℕ-trich a b)
   (inl ∘ <ℕ-succ a b)
   (cases
   (inr ∘ inl ∘ ap succ)
   (inr ∘ inr ∘ <ℕ-succ b a))

assoc+ℤℕ : ∀ a b c → a +pos (b +ℕ c) ≡ (a +pos b) +pos c
assoc+ℤℕ a b zero = refl
assoc+ℤℕ a b (succ c) = ap succℤ (assoc+ℤℕ a b c)

<ℤ-trans : {a b c : ℤ} → a <ℤ b → b <ℤ c → a <ℤ c
<ℤ-trans {a} {b} {c} (d₁ , e₁) (d₂ , e₂)
 = (d₁ +ℕ (succ d₂))
 , (assoc+ℤℕ (succℤ a) d₁ (succ d₂)
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

casta<b : ∀ a b → a <ℕ b →
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

trichotomous∙ : {X : 𝓤 ̇ } (_<_ : X → X → 𝓥 ̇ ) → X → X → 𝓤 ⊔ 𝓥 ̇
trichotomous∙ _<_ a b = (a < b) ⊹ (a ≡ b) ⊹ (b < a)

trichotomous : {X : 𝓤 ̇ } (_<_ : X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇ 
trichotomous _<_ = ∀ a b → trichotomous∙ _<_ a b

ℤ-trich : trichotomous _<ℤ_
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

𝟛ᴺ = ℕ → 𝟛

down : 𝟛 → (ℤ → ℤ)
down −1 = downLeft
down  O = downMid
down +1 = downRight

[-1,1] : Interval
[-1,1] = (negsucc 0 , negsucc 0)

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

downLeftIsDown : (i : ℤ) → downLeft i -immediatelyDownFrom- i
downLeftIsDown i = inl refl

downMidIsDown : (i : ℤ) → downMid i -immediatelyDownFrom- i
downMidIsDown i = (inr ∘ inl) refl

downRightIsDown : (i : ℤ) → downRight i -immediatelyDownFrom- i
downRightIsDown i = (inr ∘ inr) refl

downIsDown : (i : ℤ) (b : 𝟛) → down b i -immediatelyDownFrom- i
downIsDown i −1 = downLeftIsDown  i
downIsDown i  O = downMidIsDown   i
downIsDown i +1 = downRightIsDown i

downFromUpRight : (i : ℤ) → i -immediatelyDownFrom- upRight i
downFromUpRight i
 = Cases (upRightEq i)
     (λ e → transport (_-immediatelyDownFrom- upRight i)
              (e ⁻¹) (downLeftIsDown (upRight i)))
     (λ e → transport (_-immediatelyDownFrom- upRight i)
              (e ⁻¹) (downMidIsDown (upRight i)))
  where
    halfEq : (n : ℕ) → (n ≡ (n /2) +ℕ (n /2)) ⊹ (n ≡ succ ((n /2) +ℕ (n /2)))
    halfEq 0 = inl refl
    halfEq 1 = inr refl
    halfEq (succ (succ n))
      = Cases (halfEq n)
          (λ f → inl (ap (succ ∘ succ) f ∙ ap succ (succ+ℕ (n /2) (n /2))))
          (λ g → inr (ap (succ ∘ succ) g ∙ ap succ (succ+ℕ (n /2) (succ (n /2)))))
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

ℤ-trich-prec : {n p : ℤ} → trichotomous∙ _<ℤ_ n p → trichotomous∙ _<ℤ_ (predℤ n) p 
ℤ-trich-prec {n} {p} (inl (d , e))
 = inl (succ d , (ap (λ ─ → succℤ (─ +pos d)) (succpredℤ n) ∙ succ+ℤ n (pos d) ∙ e))
ℤ-trich-prec {n} {.n} (inr (inl refl))
 = inl (0 , succpredℤ n)
ℤ-trich-prec {n} {p} (inr (inr (0 , e)))
 = inr (inl (ap predℤ (e ⁻¹) ∙ predsuccℤ p))
ℤ-trich-prec {n} {p} (inr (inr (succ d , e)))
 = inr (inr (d , succℤ-lc (e ∙ succpredℤ n ⁻¹)))

succn≢n : {n : ℤ} → succℤ n ≢ n
succn≢n {negsucc 0} ()
succn≢n {negsucc (succ x)} ()

add-unique-0 : (n d : ℤ) → n + d ≡ n → d ≡ pos 0
add-unique-0 n d e = ℤ+-lc d (pos 0) (n +pos 0) e

succ≢0 : {n : ℕ} → succ n ≢ 0
succ≢0 {n} ()

add-nonzero-not-equal : (n : ℤ) (d : ℕ) → n +pos (succ d) ≢ n
add-nonzero-not-equal n 0 = succn≢n
add-nonzero-not-equal n (succ d) e
 = succ≢0 (pos-lc (add-unique-0 n (pos (succ (succ d))) e))

downLeft≢downMid : (k : ℤ) → downLeft k ≢ downMid k
downLeft≢downMid k e = 𝟘-elim (add-nonzero-not-equal (k + k) 0 (e ⁻¹))

downMid≢downRight : (k : ℤ) → downMid k ≢ downRight k
downMid≢downRight k e = 𝟘-elim (add-nonzero-not-equal (succℤ (k + k)) 0 (e ⁻¹))

downLeft≢downRight : (k : ℤ) → downLeft k ≢ downRight k
downLeft≢downRight k e = 𝟘-elim (add-nonzero-not-equal (k + k) 1 (e ⁻¹))

immediatelyDown-isProp : (i j : ℤ) → is-prop (i -immediatelyDownFrom- j)
immediatelyDown-isProp i j = +-is-prop ℤ-is-set
                               (+-is-prop ℤ-is-set ℤ-is-set
                                 (λ x y → downMid≢downRight j (x ⁻¹ ∙ y)))
                                (λ x → cases
                                  (λ y → downLeft≢downMid j (x ⁻¹ ∙ y))
                                  (λ y → downLeft≢downRight j (x ⁻¹ ∙ y))) 

+pos-lc : ∀ a b c → a +pos b ≡ a +pos c → b ≡ c
+pos-lc a zero zero e = refl
+pos-lc a zero (succ c) e = 𝟘-elim (add-nonzero-not-equal a c (e ⁻¹))
+pos-lc a (succ b) zero e = 𝟘-elim (add-nonzero-not-equal a b e)
+pos-lc a (succ b) (succ c) e
 = ap succ (+pos-lc (succℤ a) _ _ (succ+ℤ a (pos b) ⁻¹ ∙ e ∙ succ+ℤ a (pos c)))

<ℤ-is-prop : (n p : ℤ) → is-prop (n <ℤ p)
<ℤ-is-prop n p (d₁ , e₁) (d₂ , e₂) = to-Σ-≡ (γ₁ , (ℤ-is-set _ _)) where
  γ₁ : d₁ ≡ d₂
  γ₁ = +pos-lc (succℤ n) d₁ d₂ (e₁ ∙ e₂ ⁻¹)

ℤ-trich-is-prop : (n p : ℤ) → is-prop (trichotomous∙ _<ℤ_ n p)
ℤ-trich-is-prop n p
 = +-is-prop (<ℤ-is-prop n p)
    (+-is-prop ℤ-is-set (<ℤ-is-prop p n) γ)
    (λ n<p → cases (δ n<p) (ζ n<p))
 where
   δ : {n p : ℤ} → n <ℤ p → ¬ (n ≡ p)
   δ {n} {.n} (d , e₁) refl = add-nonzero-not-equal n d (succ+ℤ n (pos d) ∙ e₁)
   ζ : {n p : ℤ} → n <ℤ p → ¬ (p <ℤ n)
   ζ {n} {p} (d₁ , e₁) (d₂ , e₂) = add-nonzero-not-equal n (succ (d₁ +ℕ d₂)) (y ∙ x) where
     x : succℤ (succℤ n +pos d₁) +pos d₂ ≡ n
     x = ap (λ ─ → succℤ ─ +pos d₂) e₁ ∙ e₂
     y : (n +pos succ (succ (d₁ +ℕ d₂))) ≡ succℤ (succℤ n +pos d₁) +pos d₂
     y = ap succℤ
         (ap (λ ─ → n +pos ─) (succ+ℕ d₁ d₂)
         ∙ assoc+ℤℕ n (succ d₁) d₂
         ∙ ap (_+pos d₂) (succ+ℤ n (pos d₁)))
       ∙ succ+ℤ (succℤ n +pos d₁) (pos d₂)
   γ : {n p : ℤ} → n ≡ p → ¬ (p <ℤ n)
   γ {n} {.n} refl (d , e) = add-nonzero-not-equal n d (succ+ℤ n (pos d) ∙ e)

CompactToReal : (i : Interval) → CompactInterval i → Real
CompactToReal (k , p) (α , f , g)
 = (λ n → β n (ℤ-trich n p)) , (λ n → γ n (ℤ-trich n p))  where
  β : (n : ℤ) → (n <ℤ p) ⊹ (n ≡ p) ⊹ (p <ℤ n) → ℤ
  β n (inl (d , _))       = upRightⁿ k (succ d)
  β n (inr (inl _))       = k
  β n (inr (inr (d , _))) = α d
  δ : (n : ℤ) → (e : (n <ℤ p) ⊹ (n ≡ p) ⊹ (p <ℤ n))
    → β n e -immediatelyDownFrom-
      β (predℤ n) (ℤ-trich-prec e)
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
       (ℤ-trich-is-prop (predℤ n) p (ℤ-trich-prec e) (ℤ-trich (predℤ n) p))
       (δ n e))
       
-- θ = k , down (α 0) k , down (α 1) (down (α 0) k) ...
-- β =     down (α 0) k , down (α 1) (down (α 0) k) ...
θ : ℤ → 𝟛ᴺ → (ℕ → ℤ)
θ k α 0 = k
θ k α (succ n) = down (α n) (θ k α n)
β : ℤ → 𝟛ᴺ → (ℕ → ℤ)
β k α = θ k α ∘ succ
γ* : (k : ℤ) (α : ℕ → 𝟛) (n : ℕ) → β k α n -immediatelyDownFrom- θ k α n
γ* k α n = downIsDown (θ k α n) (α n)

SignedToCompact : (i : Interval) → 𝟛ᴺ → CompactInterval i
SignedToCompact (k , _) α = β k α , γ* k α 0 , γ* k α ∘ succ

down-to-𝟛 : (i j : ℤ) → i -immediatelyDownFrom- j → 𝟛
down-to-𝟛 i j (inl _)       = −1
down-to-𝟛 i j (inr (inl _)) =  O
down-to-𝟛 i j (inr (inr _)) = +1

CompactToSigned : (i : Interval) → CompactInterval i → 𝟛ᴺ
CompactToSigned (k , _) (α , δ , γ) 0        = down-to-𝟛 (α 0) k δ
CompactToSigned (k , _) (α , δ , γ) (succ n) = down-to-𝟛 (α (succ n)) (α n) (γ n)

down-eq₁ : (k : ℤ) (b : 𝟛) (f : down b k -immediatelyDownFrom- k)
         → down-to-𝟛 (down b k) k f ≡ b
down-eq₁ k −1 (inl _)       = refl
down-eq₁ k −1 (inr (inl e)) = 𝟘-elim (add-nonzero-not-equal (k + k) 0 (e ⁻¹))
down-eq₁ k −1 (inr (inr e)) = 𝟘-elim (add-nonzero-not-equal (k + k) 1 (e ⁻¹))
down-eq₁ k  O (inl e)       = 𝟘-elim (add-nonzero-not-equal (k + k) 0 e)
down-eq₁ k  O (inr (inl _)) = refl
down-eq₁ k  O (inr (inr e)) = 𝟘-elim (add-nonzero-not-equal (succℤ (k + k)) 0 (e ⁻¹))
down-eq₁ k +1 (inl e)       = 𝟘-elim (add-nonzero-not-equal (k + k) 1 e)
down-eq₁ k +1 (inr (inl e)) = 𝟘-elim (add-nonzero-not-equal (succℤ (k + k)) 0 e)
down-eq₁ k +1 (inr (inr _)) = refl

Compact-id : (i : Interval) → CompactToSigned i ∘ SignedToCompact i ∼ id
Compact-id (k , p) α = dfunext (fe _ _) γ where
  γ : (CompactToSigned (k , p) ∘ SignedToCompact (k , p)) α ∼ α
  γ zero = down-eq₁ k (α zero) (downIsDown k (α zero))
  γ (succ n) = down-eq₁ (down (α n) _) (α (succ n)) (downIsDown (down (α n) _) (α (succ n)))

down-eq₂ : (k : ℤ) (n : ℤ) (f : n -immediatelyDownFrom- k)
        → down (down-to-𝟛 n k f) k ≡ n
down-eq₂ k n (inl x)       = x ⁻¹
down-eq₂ k n (inr (inl x)) = x ⁻¹
down-eq₂ k n (inr (inr x)) = x ⁻¹

Signed-id : (i : Interval) → SignedToCompact i ∘ CompactToSigned i ∼ id
Signed-id (k , p) (α , δ₀ , δₛ)
 = to-Σ-≡ ((dfunext (fe _ _) γ)
 , (to-×-≡ (immediatelyDown-isProp (α 0) k _ _)
     (Π-is-prop (fe _ _) (λ n → immediatelyDown-isProp (α (succ n)) (α n)) _ _)))
 where
  γ : pr₁ ((SignedToCompact (k , p) ∘ CompactToSigned (k , p)) (α , δ₀ , δₛ)) ∼ α
  γ zero = down-eq₂ k (α 0) δ₀
  γ (succ n) = ap (down (down-to-𝟛 (α (succ n)) (α n) (δₛ n))) (γ n)
             ∙ down-eq₂ (α n) (α (succ n)) (δₛ n)

equiv : Interval × 𝟛ᴺ ≃ Σ CompactInterval
equiv = qinveq (λ (i , α) → i , SignedToCompact i α)
               ((λ (i , c) → i , CompactToSigned i c)
               , ((λ (i , α) → to-×-≡ refl (Compact-id i α))
               , (λ (i , c) → to-Σ-≡ (refl , (Signed-id i c)))))

open import GenericConvergentSequence
open import Codistance fe

+-to-𝟚 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ⊹ Y → 𝟚
+-to-𝟚 (inl _) = ₁
+-to-𝟚 (inr _) = ₀

C : (i : Interval) → CompactInterval i × CompactInterval i → ℕ∞
C i ((β , _) , (δ , _))
 = force-decreasing α , force-decreasing-is-decreasing α where
  α : ℕ → 𝟚
  α n = +-to-𝟚 (ℤ-is-discrete (β n) (δ n))

CauchySequence : (i : Interval) → 𝓤₀ ̇ 
CauchySequence i = Σ s ꞉ (ℕ → CompactInterval i) , Π ε ꞉ ℕ , Σ N ꞉ ℕ
                 , ∀ m n → (N <ℕ m) × (N <ℕ n) → under ε ≺ C i (s m , s n)

has-limit : {X : 𝓤 ̇ } → (ℕ → X) → 𝓤 ̇
has-limit {X} s = Σ i ꞉ ℕ , Π n ꞉ ℕ , (i <ℕ succ n → s n ≡ s i)

complete : (i : Interval) → ((s , _) : CauchySequence i) → has-limit s
complete = {!!}


{-
CUT-CauchySequence : CoUltrametricType → 𝓤 ̇
CUT-CauchySequence (X , c , _) = Σ s ꞉ (ℕ → X) , Π ε ꞉ ℕ , Σ N ꞉ ℕ
                                 , ∀ m n → (N < m) × (N < n) → under ε ≺ c (s m) (s n)

has-limit : {X : 𝓤 ̇ } → (ℕ → X) → 𝓤 ̇
has-limit {X} s = Σ i ꞉ ℕ , Π n ꞉ ℕ , (i ≤ n → s n ≡ s i)

CUT-Complete : CoUltrametricType → 𝓤 ̇
CUT-Complete C = Π (s , _) ꞉ CUT-CauchySequence C , has-limit s
-}
