Andrew Sneap - 27th April 2021

I link to this module within the Integers section of my report.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆) --TypeTopology

import NaturalsAddition -- TypeTopology
import UF-Base --TypeTopology
import UF-Subsingletons --TypeTopology

import MoreNaturalProperties
import Integers
import IntegersProperties

module IntegersOrder where

open Integers

_≤_ _≥_ _<_ _>_ : (x y : ℤ) → 𝓤₀ ̇
x ≤ y = Σ c ꞉ ℤ , positive c × (x + c ≡ y)
x ≥ y = y ≤ x
x < y = Σ c ꞉ ℤ , greater-than-zero c × (x + c ≡ y) --Σ c ꞉ ℤ , positive c × (x + (succℤ c) ≡ y) -- succℤ x ≤ y
x > y = y < x

open IntegersProperties
open UF-Subsingletons --TypeTopology


ℤ≤-is-prop : (x y : ℤ) → is-prop (x ≤ y)
ℤ≤-is-prop x y (p , q , r) (p' , q' , r') = to-subtype-≡ (λ a → ×-is-prop (positive-is-prop a) ℤ-is-set) (ℤ+-lc p p' x (r ∙ (r' ⁻¹)))

ℤ<-is-prop : (x y : ℤ) → is-prop (x < y)
ℤ<-is-prop x y (p , q , r) (p' , q' , r') = to-subtype-≡ (λ a → ×-is-prop (greater-than-zero-is-prop a) ℤ-is-set) (ℤ+-lc p p' x (r ∙ r' ⁻¹))

≤-incrℤ : (x : ℤ) → x ≤ succℤ x
≤-incrℤ x = pos 1 , ⋆ , refl

<-incrℤ : (x : ℤ) → x < succℤ x
<-incrℤ x = pos 1 , ⋆ , refl

<-predℤ : (x : ℤ) → predℤ x < x
<-predℤ x = pos 1 , ⋆ , (succpredℤ x)

ℤ≤-trans : (x y z : ℤ) → x ≤ y → y ≤ z → x ≤ z
ℤ≤-trans x y z (c , p , q) (c' , p' , q') = (c + c') , (positive-trans c c' p p' , I)
 where
  I : x + (c + c') ≡ z
  I = x + (c + c') ≡⟨ ℤ+-assoc x c c' ⁻¹ ⟩
      (x + c) + c' ≡⟨ ap (_+ c') q       ⟩
      y + c'       ≡⟨ q'                 ⟩
      z            ∎

ℤ<-trans : (x y z : ℤ) → x < y → y < z → x < z
ℤ<-trans x y z (c , p , q) (c' , p' , q') = c + c' , (greater-than-zero-trans c c' p p') , I
 where
  I : x + (c + c') ≡ z
  I = x + (c + c') ≡⟨ ℤ+-assoc x c c' ⁻¹ ⟩
      x + c + c'   ≡⟨  ap (_+ c') q      ⟩
      y + c'       ≡⟨ q'                 ⟩
      z            ∎

ℤ≤-refl : (x : ℤ) → x ≤ x
ℤ≤-refl x = pos 0 , ⋆ , refl

ℤ≤-anti-lemma : (x y : ℤ) → x + y ≡ x → y ≡ pos 0
ℤ≤-anti-lemma x y l = ℤ+-lc y (pos 0) x l

ℤ≤-succℤ-ap : (x y : ℤ) → x ≤ y → succℤ x ≤ succℤ y
ℤ≤-succℤ-ap x y (p , q , r) = p , q , I
 where
  I : succℤ x + p ≡ succℤ y
  I = succℤ x + p   ≡⟨ ℤ-left-succ x p ⟩
      succℤ (x + p) ≡⟨ ap succℤ r      ⟩
      succℤ y       ∎

ℤ<-adding : (a b c d : ℤ) → a < b → c < d → (a + c) < (b + d)
ℤ<-adding a b c d (p , α , β) (q , α' , β') = (p + q) , (greater-than-zero-trans p q α α') , I
 where
   I : (a + c) + (p + q) ≡ (b + d)
   I = (a + c) + (p + q)      ≡⟨ ℤ+-assoc (a + c) p q ⁻¹              ⟩
       ((a + c) + p) + q      ≡⟨ ap (λ z → (z + p) + q) (ℤ+-comm a c) ⟩
       ((c + a) + p) + q      ≡⟨ ap (_+ q) (ℤ+-assoc c a p)           ⟩
       (c + (a + p)) + q      ≡⟨ ap (λ z → (c + z) + q) β             ⟩
       (c + b) + q            ≡⟨ ap (_+ q) (ℤ+-comm c b)              ⟩
       (b + c) + q            ≡⟨ ℤ+-assoc b c q                       ⟩
       b + (c + q)            ≡⟨ ap (b +_) β'                         ⟩
       b + d                  ∎

ℤ≤-adding : (a b c d : ℤ) → a ≤ b → c ≤ d → (a + c) ≤ (b + d)
ℤ≤-adding a b c d (p , α , β) (q , α' , β') = (p + q) , (positive-trans p q α α') , I
 where
  I : (a + c) + (p + q) ≡ (b + d)
  I = (a + c) + (p + q)      ≡⟨ ℤ+-assoc (a + c) p q ⁻¹              ⟩
      ((a + c) + p) + q      ≡⟨ ap (λ z → (z + p) + q) (ℤ+-comm a c) ⟩
      ((c + a) + p) + q      ≡⟨ ap (_+ q) (ℤ+-assoc c a p)           ⟩
      (c + (a + p)) + q      ≡⟨ ap (λ z → (c + z) + q) β             ⟩
      (c + b) + q            ≡⟨ ap (_+ q) (ℤ+-comm c b)              ⟩
      (b + c) + q            ≡⟨ ℤ+-assoc b c q                       ⟩
      b + (c + q)            ≡⟨ ap (b +_) β'                         ⟩
      b + d                  ∎

ℤ<-adding' : (a b c : ℤ) → a < b → a + c < b + c
ℤ<-adding' a b c (k , α , β) = k , (α , I)
 where
  I : a + c + k ≡ b + c
  I = a + c + k       ≡⟨ ℤ+-assoc a c k ⟩
      a + (c + k)     ≡⟨ ap (a +_) (ℤ+-comm c k) ⟩
      a + (k + c)     ≡⟨ ℤ+-assoc a k c ⁻¹ ⟩
      a + k + c       ≡⟨ ap (_+ c) β ⟩
      b + c ∎

open UF-Base --TypeTopology

ℤ<-adding'' : (a b c : ℤ) → a < b → c + a < c + b
ℤ<-adding'' a b c l = transport₂ _<_ (ℤ+-comm a c) (ℤ+-comm b c) I
 where
  I : (a + c) < (b + c)
  I = ℤ<-adding' a b c l

ℤ<-less-than-pos-addition' : (a b c : ℤ) → greater-than-zero c → a < b → a < b + c
ℤ<-less-than-pos-addition' a b (negsucc x) g l       = 𝟘-elim g
ℤ<-less-than-pos-addition' a b (pos x) g (k , g' , p) = (k + pos x) , ((greater-than-zero-trans k (pos x) g' g) , I)
 where
  I : a + (k + pos x) ≡ b + pos x
  I = a + (k + pos x) ≡⟨ ℤ+-assoc a k (pos x) ⁻¹ ⟩
      a + k + pos x   ≡⟨ ap (_+ pos x) p         ⟩
      b + pos x ∎

ℤ<-less-than-pos-addition : (a b : ℤ) → greater-than-zero b → a < a + b
ℤ<-less-than-pos-addition a (negsucc x) g = 𝟘-elim g
ℤ<-less-than-pos-addition a (pos x)     g = (pos x) , (g , refl)

negative-less-than-positive : (x y : ℤ) → negative x → positive y → x < y
negative-less-than-positive (pos x)     (pos y)     n p = 𝟘-elim n
negative-less-than-positive (pos x)     (negsucc y) n p = 𝟘-elim p
negative-less-than-positive (negsucc x) (pos y)     n p = (pos (succ x) + (pos y)) , (greater-than-zero-trans' (pos (succ x)) (pos y) ⋆ ⋆ , I)
 where
  I : negsucc x + (pos (succ x) + pos y) ≡ pos y
  I = negsucc x + (pos (succ x) + pos y)  ≡⟨ ℤ+-assoc (negsucc x) (pos (succ x)) (pos y) ⁻¹       ⟩
      (negsucc x + pos (succ x)) + pos y  ≡⟨ ap (_+ pos y) (ℤ-sum-of-inverse-is-zero (negsucc x)) ⟩
      pos 0 + pos y                       ≡⟨ ℤ+-comm  (pos 0) (pos y)                             ⟩                 
      pos y                               ∎
negative-less-than-positive (negsucc x) (negsucc y) n p = 𝟘-elim p

ℤ<-succℤ-ap : (x y : ℤ) → x < y → succℤ x < succℤ y
ℤ<-succℤ-ap x y (c , p , e) = c , p , I
 where
  I : succℤ x + c ≡ succℤ y
  I = succℤ x + c   ≡⟨ ℤ-left-succ x c ⟩
      succℤ (x + c) ≡⟨ ap succℤ e      ⟩
      succℤ y       ∎

open MoreNaturalProperties
open NaturalsAddition renaming (_+_ to _ℕ+_) --TypeTopology

greater-than-zero-not-less-than-zero : (k : ℕ) → ¬ (pos (succ k) < pos zero)
greater-than-zero-not-less-than-zero k (negsucc x    , p , q) = 𝟘-elim p
greater-than-zero-not-less-than-zero k (pos 0        , p , q) = 𝟘-elim p
greater-than-zero-not-less-than-zero k (pos (succ x) , p , q) = 𝟘-elim (pos-int-not-zero (k ℕ+ succ x) I)
 where
  I : pos (succ (k ℕ+ succ x)) ≡ pos 0
  I = pos (succ (k ℕ+ succ x))    ≡⟨ ap pos (succ-left k (succ x) ⁻¹)    ⟩
      pos (succ k ℕ+ succ x)      ≡⟨ pos-addition-equiv-to-ℕ (succ k) (succ x) ⁻¹ ⟩
      pos (succ k) + pos (succ x) ≡⟨ q                                            ⟩
      pos 0                       ∎

zero-not-greater-than-zero : ¬ greater-than-zero (pos zero)
zero-not-greater-than-zero z = z

ℤ-equal-not-less-than : (a b : ℤ) → a ≡ b → ¬ (a < b)
ℤ-equal-not-less-than a b e (negsucc x    , g , p) = 𝟘-elim g
ℤ-equal-not-less-than a b e (pos 0        , g , p) = 𝟘-elim g
ℤ-equal-not-less-than a b e (pos (succ x) , g , p) = pos-int-not-zero x (ℤ+-lc (pos (succ x)) (pos 0) a p')
 where
  p' : a + pos (succ x) ≡ a + (pos zero)
  p' = a + pos (succ x) ≡⟨ p    ⟩
       b                ≡⟨ e ⁻¹ ⟩
       a                ∎

ℤ-trichotomous-lemma : (x : ℕ) → (negsucc x) + (pos x) ≡ negsucc zero
ℤ-trichotomous-lemma = induction base step
 where
  base : (negsucc 0 + pos 0) ≡ negsucc zero
  base = refl

  step : (k : ℕ)
       → (negsucc k + pos k)               ≡ negsucc 0
       → (negsucc (succ k) + pos (succ k)) ≡ negsucc 0
  step k IH = negsucc (succ k) + pos (succ k)  ≡⟨ ℤ-left-pred (negsucc k) (pos (succ k)) ⟩
              predℤ (negsucc k + pos (succ k)) ≡⟨ predsuccℤ (negsucc k + pos k)          ⟩
              negsucc k + pos k                ≡⟨ IH                                     ⟩
              negsucc 0                        ∎

ℤ-trichotomous : (x y : ℤ) → (x < y) ∔ (x ≡ y) ∔ (y < x)
ℤ-trichotomous (pos 0)        (pos 0)            = inr (inl refl)
ℤ-trichotomous (pos 0)        (pos (succ y))     = inl ((pos (succ y)) , ⋆ , ap succℤ (ℤ+-comm (pos 0) (pos y)))
ℤ-trichotomous (pos 0)        (negsucc 0)        = inr (inr (pos 1 , ⋆ , refl))
ℤ-trichotomous (pos 0)        (negsucc (succ y)) = inr (inr ((pos (succ (succ y))) , (⋆ , (ℤ-sum-of-inverse-is-zero (negsucc (succ y))))))
ℤ-trichotomous (pos (succ x)) (pos 0)            = inr (inr ((pos (succ x)) , (⋆ , (ap succℤ (ℤ+-comm (pos 0) (pos x))))))
ℤ-trichotomous (pos (succ x)) (pos (succ y))     = helper (ℤ-trichotomous (pos x) (pos y))
 where
  helper : (pos x < pos y) ∔ (pos x ≡ pos y) ∔ (pos y < pos x) →
           (pos (succ x) < pos (succ y)) ∔ (pos (succ x) ≡ pos (succ y)) ∔ (pos (succ y) < pos (succ x))
  helper (inl (c , (g , p)))       = inl (c , (g  , (ℤ-left-succ (pos x) c ∙ ap succℤ p)))
  helper (inr (inl z))             = inr (inl (ap succℤ z))
  helper (inr (inr (c , (g , p)))) = inr (inr (c , (g , (ℤ-left-succ (pos y) c ∙ ap succℤ p))))
ℤ-trichotomous (pos (succ x))     (negsucc 0)        = inr (inr ((pos (succ (succ x))) , ⋆ , (ℤ+-comm (negsucc 0) (pos (succ (succ x))))))
ℤ-trichotomous (pos (succ x))     (negsucc (succ y)) = inr (inr (negative-less-than-positive (negsucc (succ y)) (pos (succ x)) ⋆ ⋆))
ℤ-trichotomous (negsucc 0)        (pos 0)            = inl (pos 1 , ⋆ , refl)
ℤ-trichotomous (negsucc 0)        (pos (succ y))     = inl ((pos (succ (succ y))) , ⋆ , (ℤ+-comm (negsucc 0) (pos (succ (succ y)))))
ℤ-trichotomous (negsucc (succ x)) (pos 0)            = inl (negative-less-than-positive (negsucc (succ x)) (pos 0) ⋆ ⋆)
ℤ-trichotomous (negsucc (succ x)) (pos (succ y))     = inl (negative-less-than-positive (negsucc (succ x)) (pos (succ y)) ⋆ ⋆)
ℤ-trichotomous (negsucc 0)        (negsucc 0)        = inr (inl refl)
ℤ-trichotomous (negsucc 0)        (negsucc (succ y)) = inr (inr ((pos (succ y)) , ⋆ , ℤ-trichotomous-lemma (succ y)))
ℤ-trichotomous (negsucc (succ x)) (negsucc 0)        = inl ((pos (succ x)) , (⋆ , ℤ-trichotomous-lemma (succ x)))
ℤ-trichotomous (negsucc (succ x)) (negsucc (succ y)) = tri-split (ℤ-trichotomous (negsucc x) (negsucc y))
 where
  tri-split : (negsucc x < negsucc y) ∔ (negsucc x ≡ negsucc y) ∔ (negsucc y < negsucc x)
            → (negsucc (succ x) < negsucc (succ y)) ∔ (negsucc (succ x) ≡ negsucc (succ y)) ∔ (negsucc (succ y) < negsucc (succ x))
  tri-split (inl (c , (g , p)))       = inl (c , (g , (ℤ-left-pred (negsucc x) c ∙ ap predℤ p)))
  tri-split (inr (inl z))             = inr (inl (ap predℤ z))
  tri-split (inr (inr (c , (g , p)))) = inr (inr (c , (g , (ℤ-left-pred (negsucc y) c ∙ ap predℤ p))))

ℤ<-coarser-than-≤ : (m n : ℤ) → (m < n) → m ≤ n
ℤ<-coarser-than-≤ m n (k , g , p) = k , greater-than-zero-is-positive k g , p

ℤ≤-split : (x y : ℤ) → x ≤ y → (x < y) ∔ (x ≡ y)
ℤ≤-split x y (negsucc a    , p) = 𝟘-elim (pr₁ p)
ℤ≤-split x y (pos 0        , p) = inr (pr₂ p)
ℤ≤-split x y (pos (succ a) , p) = inl (pos (succ a) , ⋆ , pr₂ p)

ℤ≡-to-≤ : (x y : ℤ) → x ≡ y → x ≤ y
ℤ≡-to-≤ x y e = (pos 0) , (⋆ , e)

pmpo-lemma : (a b : ℤ) → (n : ℕ) → a < b →  a * pos (succ n) < b * pos (succ n)
pmpo-lemma a b = induction base step
 where
  base : a < b
       → a * pos 1 < b * pos 1
  base z = z

  step : (k : ℕ)
       → (a < b → a * pos (succ k) < b * pos (succ k))
       → a < b
       → a * pos (succ (succ k)) < b * pos (succ (succ k))
  step k IH l = ℤ<-adding a b (a + (a * pos k)) (b + (b * pos k)) l (IH l)

positive-multiplication-preserves-order : (a b c : ℤ) → greater-than-zero c → a < b → (a * c) < (b * c)
positive-multiplication-preserves-order a b (negsucc x)    p l = 𝟘-elim p
positive-multiplication-preserves-order a b (pos 0)        p l = 𝟘-elim p
positive-multiplication-preserves-order a b (pos (succ x)) p l = pmpo-lemma a b x l

positive-multiplication-preserves-order' : (a b c : ℤ) → greater-than-zero c → a < b → (c * a) < (c * b)
positive-multiplication-preserves-order' a b c g l = transport₂ (λ z z' → z < z') (ℤ*-comm a c) (ℤ*-comm b c) (positive-multiplication-preserves-order a b c g l)

nmco-lemma : (a b : ℤ) → (c : ℕ) → a < b → (b * (negsucc c)) < (a * (negsucc c))
nmco-lemma a b = induction base step
 where
  base : a < b → (b * negsucc 0) < (a * negsucc 0)
  base (α , β , γ) = α , β , I
   where
    I : b * negsucc 0 + α ≡ a * negsucc 0
    I = (- b) + α  ≡⟨ ap (λ z → ((- z) + α)) (γ ⁻¹)       ⟩
        (- (a + α)) + α         ≡⟨ ap (_+ α) (subtraction-dist a α ⁻¹)        ⟩
        ((- a) + (- α)) + α     ≡⟨ ℤ+-assoc (- a) (- α) α                     ⟩
        (- a) + ((- α) + α)     ≡⟨ ap ((- a) +_) (ℤ+-comm (- α) α)            ⟩
        (- a) + (α + (- α))     ≡⟨ ap ((- a) +_) (ℤ-sum-of-inverse-is-zero α) ⟩
        (- a)                   ∎

  step : (k : ℕ)
       → (a < b → (b * negsucc k) < (a * negsucc k))
       →  a < b → (b * negsucc (succ k)) < (a * negsucc (succ k))
  step k IH l = ℤ<-adding (- b) (- a) (b * negsucc k) (a * negsucc k) (base l) (IH l)

negative-multiplication-changes-order : (a b c : ℤ) → negative c → a < b → (b * c) < (a * c)
negative-multiplication-changes-order a b (pos c)     g l = 𝟘-elim g
negative-multiplication-changes-order a b (negsucc c) g l = nmco-lemma a b c l

negative-multiplication-changes-order' : (a b c : ℤ) → negative c → a ≤ b → (b * c) ≤ (a * c)
negative-multiplication-changes-order' a b (pos c)     g l = 𝟘-elim g
negative-multiplication-changes-order' a b (negsucc c) g l = I (ℤ≤-split a b l)
 where
  I : (a < b) ∔ (a ≡ b) → (b * negsucc c) ≤ (a * negsucc c)
  I (inr z) = ℤ≡-to-≤ (b * negsucc c) (a * negsucc c) (II ⁻¹)
   where
    II : a * negsucc c ≡ b * negsucc c
    II = ap (_* negsucc c) z
  I (inl z) = ℤ<-coarser-than-≤ (b * negsucc c) (a * negsucc c) II
   where
    II : (b * negsucc c) < (a * negsucc c)
    II = negative-multiplication-changes-order a b (negsucc c) ⋆ z

ordering-right-cancellable-lemma : (a b : ℤ) → (n : ℕ) → (a * (pos (succ n))) < (b * (pos (succ n))) → a < b
ordering-right-cancellable-lemma a b = induction base step
 where
  base : (a * pos 1) < (b * pos 1) → a < b
  base z = z

  step : (k : ℕ)
       → (a * pos (succ k) < b * pos (succ k) → a < b)
       → a * pos (succ (succ k)) < b * pos (succ (succ k))
       → a < b
  step k IH (α , β , γ) = I (ℤ-trichotomous a b)
   where
    I : (a < b) ∔ (a ≡ b) ∔ (b < a) → a < b
    I (inl l)       = l
    I (inr (inl l)) = 𝟘-elim (zero-not-greater-than-zero (transport greater-than-zero (ℤ+-lc α (pos 0) (a + (a + (a * pos k))) i) β))
     where
      i : a + (a + a * pos k) + α ≡ a * pos (succ (succ k)) + pos 0 
      i = a + (a + a * pos k) + α        ≡⟨ γ                                                   ⟩
          b * pos (succ (succ k))        ≡⟨ ap (λ z → (z * pos (succ (succ k))) + pos 0) (l ⁻¹) ⟩
          a * pos (succ (succ k)) + pos 0 ∎
    I (inr (inr (p , q , r))) = IH (((a + α) + (- b)) , (II , III))
     where
      II : greater-than-zero ((a + α) + (- b))
      II = tri-split (ℤ-trichotomous (a + (- b)) (pos 0))
       where
        i : (a + α) + (- b) ≡ α + (a + (- b))
        i = a + α + (- b)   ≡⟨ ℤ+-assoc a α (- b)          ⟩
            a + (α + (- b)) ≡⟨ ap (a +_) (ℤ+-comm α (- b)) ⟩
            a + ((- b) + α) ≡⟨ ℤ+-assoc a (- b) α ⁻¹       ⟩
            a + (- b) + α   ≡⟨ ℤ+-comm (a + (- b)) α       ⟩
            α + (a + (- b)) ∎

        tri-split : ((a + (- b)) < pos 0) ∔ ((a + (- b)) ≡ pos 0) ∔ (pos 0 < (a + (- b))) → greater-than-zero ((a + α) + (- b))
        tri-split (inl (p' , q' , r')) = 𝟘-elim (zero-not-greater-than-zero (transport greater-than-zero δ (greater-than-zero-trans p p' q q')))
         where
          δ : p + p' ≡ pos 0
          δ = p + p'               ≡⟨ ap (λ z → (p + z) + p') (ℤ-sum-of-inverse-is-zero b ⁻¹) ⟩
              p + (b + (- b)) + p' ≡⟨ ap (_+ p') (ℤ+-assoc p b (- b) ⁻¹)                      ⟩
              p + b + (- b) + p'   ≡⟨ ap (λ z → (z + (- b)) + p') (ℤ+-comm p b)               ⟩
              b + p + (- b) + p'   ≡⟨ ap (λ z → (z + (- b)) + p') r                           ⟩
              a + (- b) + p'       ≡⟨ r'                                                      ⟩
              pos 0                ∎              
        tri-split (inr (inl c)) = transport greater-than-zero ψ β
         where
          ψ : α ≡ a + α + (- b)
          ψ = α + pos 0       ≡⟨ ap (α +_) (c ⁻¹) ⟩
              α + (a + (- b)) ≡⟨ i ⁻¹             ⟩
              a + α + (- b)   ∎  
        tri-split (inr (inr (p , q , r))) = transport greater-than-zero δ (greater-than-zero-trans α p β q)
         where
          δ : α + p ≡ a + α + (- b)
          δ = α + p           ≡⟨ ap (α +_) (ℤ+-comm p (pos 0) ∙ r) ⟩
              α + (a + (- b)) ≡⟨ i ⁻¹                              ⟩
              a + α + (- b)   ∎
        
      III : a * pos (succ k) + (a + α + (- b)) ≡ b * pos (succ k)
      III = a * pos (succ k) + (a + α + (- b)) ≡⟨ ℤ+-assoc (a + (a * pos k)) (a + α) (- b) ⁻¹              ⟩
            a + a * pos k + (a + α) + (- b)    ≡⟨ ap (_+ (- b)) (ℤ+-assoc (a + (a * pos k)) a α ⁻¹)        ⟩
            a + a * pos k + a + α + (- b)      ≡⟨ ap (λ z → (z + α) + (- b)) (ℤ+-comm (a + (a * pos k)) a) ⟩
            a + (a + a * pos k) + α + (- b)    ≡⟨ ap (_+ (- b)) γ                                          ⟩
            b * pos (succ (succ k)) + (- b)    ≡⟨ ap (_+ (- b)) (ℤ+-comm b (b + (b * pos k)))              ⟩
            b + b * pos k + b + (- b)          ≡⟨ ℤ+-assoc (b + (b * pos k)) b (- b)                       ⟩
            b + b * pos k + (b + (- b))        ≡⟨ ap ((b * pos (succ k)) +_) (ℤ-sum-of-inverse-is-zero b)  ⟩
            b * pos (succ k) + pos 0           ∎

ordering-right-cancellable : (a b c : ℤ) → greater-than-zero c → (a * c) < (b * c) → a < b
ordering-right-cancellable a b (negsucc x)    p l = 𝟘-elim p
ordering-right-cancellable a b (pos 0)        p l = 𝟘-elim p
ordering-right-cancellable a b (pos (succ x)) p l = ordering-right-cancellable-lemma a b x l

ℤ-ordering-cancellable : (a b c : ℤ) → greater-than-zero c → c * a < c * b
                                                           ∔ c * a < b * c
                                                           ∔ a * c < c * b
                                                           ∔ a * c < b * c
                                                           → a < b
ℤ-ordering-cancellable a b c p (inl l)             = ordering-right-cancellable a b c p (transport₂ (λ z z' → z < z') (ℤ*-comm c a) (ℤ*-comm c b) l)
ℤ-ordering-cancellable a b c p (inr (inl l))       = ordering-right-cancellable a b c p (transport (_< b * c) (ℤ*-comm c a) l)
ℤ-ordering-cancellable a b c p (inr (inr (inl l))) = ordering-right-cancellable a b c p (transport ((a * c) <_) (ℤ*-comm c b) l)
ℤ-ordering-cancellable a b c p (inr (inr (inr l))) = ordering-right-cancellable a b c p l

ordering-multiplication-transitive : (a b c d : ℤ) → greater-than-zero b → greater-than-zero c → a < b → c < d → (a * c) < (b * d)
ordering-multiplication-transitive a b              (negsucc c)    d g₁ g₂     = 𝟘-elim g₂
ordering-multiplication-transitive a (negsucc b)    (pos c)        d g₁ g₂     = 𝟘-elim g₁
ordering-multiplication-transitive a (pos 0)        (pos c)        d g₁ g₂     = 𝟘-elim g₁
ordering-multiplication-transitive a (pos (succ b)) (pos 0)        d g₁ g₂     = 𝟘-elim g₂
ordering-multiplication-transitive a (pos (succ b)) (pos (succ c)) d g₁ g₂ α β = ℤ<-trans (a * pos (succ c)) (pos (succ b) * pos (succ c)) (pos (succ b) * d) I II
 where
  I : a * pos (succ c) < pos (succ b) * pos (succ c)
  I = positive-multiplication-preserves-order a (pos (succ b)) (pos (succ c)) ⋆ α

  II : pos (succ b) * pos (succ c) < pos (succ b) * d
  II = positive-multiplication-preserves-order' (pos (succ c)) d (pos (succ b)) ⋆ β

ℤ-mult-right-cancellable : (x y z : ℤ) → not-zero z → (x * z) ≡ (y * z) → x ≡ y
ℤ-mult-right-cancellable x y (pos 0)        notzero e = 𝟘-elim (notzero ⋆)
ℤ-mult-right-cancellable x y (pos (succ z)) notzero e = tri-split (ℤ-trichotomous x y)
 where
  tri-split : (x < y) ∔ (x ≡ y) ∔ (y < x) → x ≡ y
  tri-split (inl α)        = 𝟘-elim (ℤ-equal-not-less-than (x * pos (succ z)) (y * (pos (succ z))) e (positive-multiplication-preserves-order x y (pos (succ z)) ⋆ α))
  tri-split (inr (inl α)) = α
  tri-split (inr (inr α)) = 𝟘-elim (ℤ-equal-not-less-than (y * pos (succ z)) (x * (pos (succ z))) (e ⁻¹) (positive-multiplication-preserves-order y x (pos (succ z)) ⋆ α))
ℤ-mult-right-cancellable x y (negsucc z) notzero e = tri-split (ℤ-trichotomous x y)
 where
  tri-split : (x < y) ∔ (x ≡ y) ∔ (y < x) → x ≡ y
  tri-split (inl α)       = 𝟘-elim (ℤ-equal-not-less-than (y * negsucc z) (x * negsucc z) (e ⁻¹) (negative-multiplication-changes-order x y (negsucc z) ⋆ α))
  tri-split (inr (inl α)) = α
  tri-split (inr (inr α)) = 𝟘-elim (ℤ-equal-not-less-than (x * negsucc z) (y * negsucc z) e (negative-multiplication-changes-order y x (negsucc z) ⋆ α)) 

ℤ-mult-left-cancellable : (x y z : ℤ) → not-zero z → (z * x) ≡ (z * y) → x ≡ y
ℤ-mult-left-cancellable x y z nz e = ℤ-mult-right-cancellable x y z nz I
 where
  I : x * z ≡ y * z
  I = x * z   ≡⟨ ℤ*-comm x z ⟩
      z * x   ≡⟨ e ⟩
      z * y   ≡⟨ ℤ*-comm z y ⟩
      y * z ∎

ℤ-set-least-element : {A : ℤ → 𝓤 ̇} → (Σ a ꞉ ℤ , ((A a) × ((m : ℤ) → (A m) → a < m))) → Σ m ꞉ ℤ , A m × ((n : ℤ) → A n → m ≤ n)
ℤ-set-least-element (x , p , q) = x , p , λ n y → ℤ<-coarser-than-≤ x n (q n y)

ℤ-mod-gives-positive : (z : ℤ) → positive (absℤ z)
ℤ-mod-gives-positive (pos z) = ⋆
ℤ-mod-gives-positive (negsucc z) = ⋆

ℤ-between-mod : (z : ℤ) → - absℤ z ≤ z × z ≤ absℤ z
ℤ-between-mod (pos 0)        = ℤ≤-refl (pos 0) , ℤ≤-refl (pos 0)
ℤ-between-mod (pos (succ z)) = I , II
 where
  I : (- absℤ (pos (succ z))) ≤ pos (succ z)
  I = ℤ<-coarser-than-≤ (- absℤ (pos (succ z))) (pos (succ z)) (negative-less-than-positive (- absℤ (pos (succ z))) (pos (succ z)) (unique-to-𝟙 (negative (- absℤ (pos (succ z))))) (unique-to-𝟙 (positive (pos (succ z)))) )

  II : pos (succ z) ≤ absℤ (pos (succ z))
  II = ℤ≤-refl (pos (succ z))
ℤ-between-mod (negsucc z) = I , II
 where
  I : (- absℤ (negsucc z)) ≤ negsucc z
  I = ℤ≤-refl (- absℤ (negsucc z))

  II : negsucc z ≤ absℤ (negsucc z)
  II = ℤ<-coarser-than-≤ (negsucc z) (absℤ (negsucc z)) (negative-less-than-positive (negsucc z) (absℤ (negsucc z)) (unique-to-𝟙 (negsucc z)) (unique-to-𝟙 (absℤ (negsucc z))))

ℤ-between-mod-converse : (a c : ℤ) → positive c → (- c ≤ a) × (a ≤ c) → absℤ a ≤ c
ℤ-between-mod-converse a           (negsucc c) g (α                   , β) = 𝟘-elim g
ℤ-between-mod-converse (pos a)     (pos 0)     g (α                   , β) = β
ℤ-between-mod-converse (negsucc a) (pos 0)     g ((negsucc c , δ , γ) , β) = 𝟘-elim δ
ℤ-between-mod-converse (negsucc a) (pos 0)     g ((pos c     , δ , γ) , β) = 𝟘-elim (neg-not-positive (I ⁻¹))
 where
  I : pos c ≡ negsucc a
  I = pos c         ≡⟨ ℤ-zero-left-neutral (pos c) ⁻¹ ⟩
      pos 0 + pos c ≡⟨ γ ⟩
      negsucc a     ∎
  
ℤ-between-mod-converse (pos a)     (pos (succ c)) g (α , β) = β
ℤ-between-mod-converse (negsucc a) (pos (succ c)) g (α , β) = negative-multiplication-changes-order' (- pos (succ c)) (negsucc a) (negsucc 0) g α

ℤ-triangle-inequality : (a b : ℤ) → absℤ (a + b) ≤ absℤ a + absℤ b
ℤ-triangle-inequality a b = ℤ-between-mod-converse (a + b) (absℤ a + absℤ b) (positive-trans (absℤ a) (absℤ b) (ℤ-mod-gives-positive a) (ℤ-mod-gives-positive b)) ((IV III) , V)
 where
  I : ((- absℤ a) ≤ a) × (a ≤ absℤ a)
  I = ℤ-between-mod a

  i : (- absℤ a) ≤ a
  i = pr₁ I

  ii : a ≤ absℤ a
  ii = pr₂ I
    
  II : ((- absℤ b) ≤ b) × (b ≤ absℤ b) 
  II = ℤ-between-mod b

  iii : (- absℤ b) ≤ b
  iii = pr₁ II

  iv : b ≤ absℤ b
  iv = pr₂ II

  III : (- absℤ a) + (- absℤ b) ≤ a + b
  III = ℤ≤-adding (- absℤ a) a (- absℤ b) b i iii

  IV : (- absℤ a) + (- absℤ b) ≤ (a + b) → - (absℤ a + absℤ b) ≤ (a + b)
  IV = transport (λ - → - ≤ a + b) (subtraction-dist (absℤ a) (absℤ b))

  V : (a + b) ≤ (absℤ a + absℤ b)
  V = ℤ≤-adding a (absℤ a) b (absℤ b) ii iv

\end{code}
