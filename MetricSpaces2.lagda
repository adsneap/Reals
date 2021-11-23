
\begin{code}
{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆)  -- TypeTopology
open import Rationals renaming (_≤_ to _ℚ≤_ ; _<_ to _ℚ<_ ; -_ to ℚ-_)

open import UF-PropTrunc --TypeTopology
open import UF-FunExt --TypeTopology

module MetricSpaces2
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
       where 
open import NewDedekindReals pt fe

open import NaturalsOrder renaming (_<_ to _ℕ<_ ; _≤_ to _ℕ≤_ ; max to ℕmax)
open import UF-PropTrunc
open PropositionalTruncation pt

\end{code}

In this file I am strictly considering Q and R

\begin{code}

ℚ₊ : 𝓤₀  ̇
ℚ₊ = Σ q ꞉ ℚ , (zero-ℚ ℚ≤ q)

zero-ℚ₊ : ℚ₊
zero-ℚ₊ = zero-ℚ , inr refl

open import Integers renaming (_*_ to _ℤ*_ ; _+_ to _ℤ+_)
open import ncRationals renaming (_+_ to _ℚₙ₊_ ; _<_ to _ℚₙ<_) 

ℚ≤-adding-lemma : (p q : ℚ) → zero-ℚ ℚ≤ p → zero-ℚ ℚ≤ q → zero-ℚ ℚ≤ (p + q)
ℚ≤-adding-lemma p q (inl l) (inl h) = inl {!!}
 where
  I : {!!}
  I = transport {!!} {!!} (ℚ-addition-preserves-order {!!} {!!} zero-ℚ {!!})
ℚ≤-adding-lemma p q (inl l) (inr h) = {!!}
ℚ≤-adding-lemma p q (inr l) (inl h) = {!!}
ℚ≤-adding-lemma p q (inr l) (inr h) = inr I
 where
  I : (pos 0 , 0) ≡ pr₁ (p + q)
  I = (pos 0 , 0) ≡⟨ {!!} ⟩
      {!!}        ≡⟨ {!!} ⟩
      {!!}        ≡⟨ {!!} ⟩
      pr₁ (p + q) ∎

_ℚ₊+_ : ℚ₊ → ℚ₊ → ℚ₊
(p , l) ℚ₊+ (q , h) = (p + q) , ℚ≤-adding-lemma p q l h

relation : {𝓤 : Universe} → (X : 𝓤 ̇) → (d : X → X → ℚ) → 𝓤 ̇
relation X d = (x y : X) → ((ε , _) : ℚ₊) → (d x y) ℚ≤ ε

open import IntegersOrder
open import IntegersProperties
open import ncRationals renaming (_<_ to _ℚₙ<_)

--maybe abstract
ℚ-abs : ℚ → ℚ₊
ℚ-abs ((pos x , a) , p)     = ((pos x , a) , p) , I x a p
 where
  I : (n a : ℕ) → (p : is-in-lowest-terms (pos n , a)) → zero-ℚ ℚ≤ ((pos n , a) , p)
  I zero a p     = inr (equiv-with-lowest-terms-is-equal (pos zero , zero) (pos zero , a) II (pr₂ zero-ℚ) p)
   where
    II : (pos zero , zero) ℚₙ≈ (pos zero , a)
    II = pos zero ℤ* pos (succ a) ≡⟨ ℤ-zero-left-is-zero (pos (succ a)) ⟩
         pos zero                 ≡⟨ (ℤ-mult-right-id (pos zero)) ⁻¹ ⟩
         pos zero ℤ* pos 1 ∎
  I (succ n) a p = inl II
   where
    II : (pos zero , zero) ℚₙ< (pos (succ n) , a)
    II = pos (succ n) , ⋆ , III
     where
      III : (pos zero) ℤ* pos (succ a) ℤ+ pos (succ n) ≡ pos (succ n) ℤ* pos 1
      III = pos zero ℤ* pos (succ a) ℤ+ pos (succ n) ≡⟨ ap (_ℤ+ pos (succ n)) (ℤ-zero-left-is-zero (pos (succ a))) ⟩
            pos zero ℤ+ pos (succ n)                 ≡⟨ ℤ-zero-left-neutral (pos (succ n)) ⟩
            pos (succ n)                             ≡⟨ ℤ-mult-right-id (pos (succ n)) ⟩
            pos (succ n) ℤ* pos 1 ∎
ℚ-abs ((negsucc x , a) , _) = toℚ (pos (succ x) , a) , inl (ℚ-zero-less-than-positive x a)

ℚ-metric : ℚ → ℚ → ℚ₊
ℚ-metric x y = ℚ-abs (y ℚ-- x)

open import UF-Subsingletons

ℚ-metric-corr : (x : ℚ) → ℚ-metric x x ≡ zero-ℚ₊
ℚ-metric-corr x = ℚ-metric x x     ≡⟨ refl ⟩
                  ℚ-abs (x ℚ-- x)  ≡⟨ ap ℚ-abs (ℚ-inverse-sum-to-zero fe x) ⟩
                  ℚ-abs zero-ℚ     ≡⟨ refl ⟩
                  zero-ℚ₊          ∎

open import NaturalNumbers-Properties
open import UF-Base

ℚ-zero-not-positive : (x a : ℕ) → ¬ (toℚ (pos (succ x) , a) ≡ zero-ℚ)
ℚ-zero-not-positive x a e = pos-int-not-zero x IV
 where
  I : toℚ (pos (succ x) , a) ≡ toℚ (pos 0 , 0) → (pos (succ x) , a) ℚₙ≈ (pos 0 , 0)
  I = pr₂ (equiv-equality fe (pos (succ x) , a) (pos 0 , 0))

  II : (pos (succ x) , a) ℚₙ≈ (pos 0 , 0)
  II = I e

  III : pos (succ x) ℤ* pos 1 ≡ pos 0 ℤ* pos (succ a)
  III = II

  IV : pos (succ x) ≡ pos 0
  IV = pos (succ x)                 ≡⟨ ℤ-mult-right-id (pos (succ x)) ⟩
       pos (succ x) ℤ* pos 1        ≡⟨ III ⟩
       pos 0 ℤ* pos (succ a)        ≡⟨ ℤ-zero-left-is-zero (pos (succ a)) ⟩
       pos 0 ∎

ℚ≤-zero-not-negative : (x a : ℕ) → ¬ (zero-ℚ ℚ≤ toℚ (negsucc x , a))
ℚ≤-zero-not-negative = {!!}

abs-zero-lemma : ℚ-abs zero-ℚ ≡ zero-ℚ₊
abs-zero-lemma = refl

abs-zero : (x : ℚ) → ℚ-abs x ≡ zero-ℚ₊ ⇔ x ≡ zero-ℚ
abs-zero x = I x , II
 where
  I : (x : ℚ) → ℚ-abs x ≡ zero-ℚ₊ → x ≡ zero-ℚ
  I ((pos x , a) , p) e = pr₁ (from-Σ-≡ e)
  I ((negsucc x , a) , p) e = 𝟘-elim (ℚ-zero-not-positive x a (pr₁ (from-Σ-≡ e)))
  
  II : x ≡ zero-ℚ → ℚ-abs x ≡ zero-ℚ₊
  II e = to-subtype-≡ (ℚ≤-is-prop zero-ℚ) III
   where
    III : pr₁ (ℚ-abs x) ≡ zero-ℚ
    III = pr₁ (ℚ-abs x)      ≡⟨ ap (λ - → pr₁ (ℚ-abs -)) e ⟩
          pr₁ (ℚ-abs zero-ℚ) ≡⟨ ap pr₁ abs-zero-lemma ⟩
          pr₁ zero-ℚ₊        ≡⟨ refl ⟩
          zero-ℚ ∎

ℚ-abs-gtz : ((q , l) : ℚ₊) → ℚ-abs q ≡ q , l
ℚ-abs-gtz (((pos x , a) , p) , l) = to-subtype-≡ (ℚ≤-is-prop zero-ℚ) refl
ℚ-abs-gtz (((negsucc x , a) , p) , l) = 𝟘-elim (ℚ≤-zero-not-negative x a II)
 where
  I : ((negsucc x , a) , p) ≡ toℚ (negsucc x , a)
  I = {!!}
  II : zero-ℚ ℚ≤ toℚ (negsucc x , a)
  II = transport (zero-ℚ ℚ≤_) I l


ℚ-abs-ltz : ((q , l) : ℚ₊) → ℚ-abs (ℚ- q) ≡ q , l
ℚ-abs-ltz = {!!}

hh : (q : ℚ) → ℚ-abs q ≡ ℚ-abs (ℚ- q)
hh ((pos x , a) , p) = to-subtype-≡ (ℚ≤-is-prop zero-ℚ) {!!}
hh ((negsucc x , a) , p) = {!!}

ℚ-metric-sym-gen : (x y : ℚ) → x ℚ< y → ℚ-metric x y ≡ ℚ-metric y x
ℚ-metric-sym-gen x y l = ℚ-metric x y          ≡⟨ by-definition ⟩
                         ℚ-abs (y ℚ-- x)       ≡⟨ hh (y ℚ-- x) ⟩
                         ℚ-abs (ℚ- (y ℚ-- x))  ≡⟨ ap ℚ-abs {!!} ⟩
                         ℚ-abs (x ℚ-- y)       ≡⟨ by-definition ⟩ 
                         ℚ-metric y x ∎
 
-- abs (x - y) ≡ abs (y - x)
-- abs (x - y) ≡ abs (- (y - x)) ≡⟨ ap ℚ-abs
-- x - y ≡ - (y - x)

ℚ-metric-sym : (x y : ℚ) → ℚ-metric x y ≡ ℚ-metric y x
ℚ-metric-sym x y = I (ℚ-trichotomous fe x y)
 where
  I : (x ℚ< y) ∔ (x ≡ y) ∔ (y ℚ< x) → ℚ-metric x y ≡ ℚ-metric y x
  I (inl l) = ℚ-metric-sym-gen x y l
  I (inr (inl e)) = ap (λ z → ℚ-metric z y) e ∙ ap (λ z → ℚ-metric y z) (e ⁻¹)
  I (inr (inr l)) = ℚ-metric-sym-gen y x l ⁻¹
                   
{-
abs-zero : (x y : ℚ) → ℚ-metric x y ≡ zero-ℚ₊ ⇔ x ≡ y
abs-zero x y = I , II
 where
  I : ℚ-metric x y ≡ zero-ℚ₊ → x ≡ y
  I e = {!!}
   where
    i : ℚ-abs (y ℚ-- x) ≡ zero-ℚ₊
    i = e
    ii : y ℚ-- x ≡ zero-ℚ
    ii = {!!}
  
  II : x ≡ y → ℚ-metric x y ≡ zero-ℚ₊
  II e = transport (λ v → ℚ-metric x v ≡ zero-ℚ₊) e (ℚ-metric-corr x)
-}

B : (x y : ℚ) → (ε : ℚ₊) → 𝓤₀ ̇
B x y (ε , _) = pr₁ (ℚ-metric x y) ℚ≤ ε

--B' : (x y : ℚ) → (ε : ℚ₊) → 𝓤₀ ̇
--B' x y ε = B x y ε → Σ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , (p ℚ< x) × (x ℚ< q) × (u ℚ< y) × (y ℚ< v) × ((pr₁ (d (ℚmin p u) (ℚmax q v))) ℚ< (pr₁ ε))

m1 : {𝓤 : Universe} → (X : 𝓤 ̇) → (B : X → X → ℚ₊ → 𝓤₀ ̇) → 𝓤 ̇
m1 X B = (x y : X) → ((q : ℚ₊) → B x y q) ⇔ x ≡ y

m2 : {𝓤 : Universe} → (X : 𝓤 ̇) → (B : X → X → ℚ₊ → 𝓤₀ ̇) → 𝓤 ̇
m2 X B = (x y : X) → (r : ℚ₊) → B x y r ⇔ B y x r

m3 : {𝓤 : Universe} → (X : 𝓤 ̇) → (B : X → X → ℚ₊ → 𝓤₀ ̇) → 𝓤 ̇
m3 X B = (x y : X) → ((r , rₚ) (s , sₚ) : ℚ₊) → r ℚ≤ s → B x y (r , rₚ) → B x y (s , sₚ)

--triple check
m4 : {𝓤 : Universe} → (X : 𝓤 ̇) → (B : X → X → ℚ₊ → 𝓤₀ ̇) → 𝓤 ̇
m4 X B = (x y z : X) → (e s : ℚ₊) → B x y e → B y z s → B x z (e ℚ₊+ s)

metric-space : {𝓤 : Universe} → (X : 𝓤 ̇) → 𝓤₁ ⊔ 𝓤 ̇
metric-space X = Σ B ꞉ (X → X → ℚ₊ → 𝓤₀ ̇) , m1 X B × m2 X B × m3 X B × m4 X B

ms-lemma : (x y : ℚ) → ¬ (((q : ℚ₊) → B x y q) × ¬ (x ≡ y))
ms-lemma x y (f , g) = I (f z)
 where
  z : ℚ₊
  z = ℚ-metric x y
  a = pr₁ (ℚ-metric x y)
  I : a ℚ≤ a → 𝟘
  I (inl lt) = {!!}
  I (inr e) = {!!}
  
open import ncRationals renaming (_<_ to _ℚₙ<_)

ℚ-metric-space : metric-space ℚ
ℚ-metric-space = B , M1 , M2 , M3 , M4
 where
  M1 : m1 ℚ B
  M1 x y = I x y , II x y 
   where
    I : (x y : ℚ) → ((q : ℚ₊) → B x y q) → x ≡ y
    I x y f = Cases (ℚ-is-discrete fe x y) id λ g → 𝟘-elim (ms-lemma x y (f , g))
    II : (x y : ℚ) → x ≡ y → (q : ℚ₊) → B x y q
    II (x , a) (.x , .a) refl (q , inl e) = inl {!!}
    II (x , a) (.x , .a) refl (q , inr l) = inl {!!}
  
  M2 : (x y : ℚ) → (r : ℚ₊) → B x y r ⇔ B y x r
  M2 x y (r , rₚ) = I , II
   where
    I : B x y (r , rₚ) → B y x (r , rₚ)
    I (inl g) = inl (transport (λ - → pr₁ (pr₁ -) ℚₙ< pr₁ r) (ℚ-metric-sym x y) g)
    I (inr g) = inr (transport (λ - → pr₁ (pr₁ -) ≡ pr₁ r) (ℚ-metric-sym x y) g)
    II : B y x (r , rₚ) → B x y (r , rₚ)
    II (inl g) = inl (transport (λ - → pr₁ (pr₁ -) ℚₙ< pr₁ r) (ℚ-metric-sym y x) g)
    II (inr g) = inr (transport (λ - → pr₁ (pr₁ -) ≡ pr₁ r) (ℚ-metric-sym y x) g)
  
  M3 : m3 ℚ B
  M3 p q ε₁ ε₂ (inl l) (inl h) = inl (ℚₙ-trans (pr₁ (pr₁ (ℚ-metric p q))) (pr₁ (pr₁ ε₁)) (pr₁ (pr₁ ε₂)) h l)
  M3 p q ε₁ ε₂ (inr l) (inl h) = inl (transport (λ - → pr₁ (pr₁ (ℚ-metric p q)) ℚₙ< -) l h)
  M3 p q ε₁ ε₂ (inl l) (inr h) = inl (transport (λ - → - ℚₙ< pr₁ (pr₁ ε₂)) (h ⁻¹) l)
  M3 p q ε₁ ε₂ (inr l) (inr h) = inr (h ∙ l)
  
  M4 : m4 ℚ B
  M4 x y z e s (inl l) (inl h) = inl {!!}
  M4 x y z e s (inr l) (inl h) = {!!}
  M4 x y z e s (inl l) (inr h) = {!!}
  M4 x y z e s (inr l) (inr h) = inr {!!}

ℝ-metric-space : metric-space ℝ
ℝ-metric-space = {!!}

continuous-function : {!!}
continuous-function = {!!}

single-variable-proof-statement : {!!}
single-variable-proof-statement = {!!}

single-variable-proof : (ℚ → ℝ) → (ℝ → ℝ)
single-variable-proof = {!!}

extend-ℚ-to-ℝ : (ℚ → ℚ) → (ℝ → ℝ)
extend-ℚ-to-ℝ f = single-variable-proof g
 where
  g : ℚ → ℝ
  g q = embedding-ℚ-to-ℝ (f q)

extend-ℚ-to-ℝ' : (ℚ → ℚ) → (ℝ → ℝ)
extend-ℚ-to-ℝ' = single-variable-proof ∘ (embedding-ℚ-to-ℝ ∘_)

extend-ℚ²-to-ℝ² : (ℚ → ℚ → ℚ) → (ℝ → ℝ → ℝ)
extend-ℚ²-to-ℝ² = {!!}
