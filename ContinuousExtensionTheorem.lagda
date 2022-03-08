\begin{code}

{-# OPTIONS --without-K --exact-split --safe --experimental-lossy-unification #-}

open import SpartanMLTT renaming (_+_ to _∔_) --TypeTopology

open import CanonicalMapNotation
open import UF-Base
open import UF-Subsingletons
open import UF-FunExt
open import UF-PropTrunc
open import OrderNotation

open import Rationals
open import RationalsOrder
open import RationalsMultiplication 


module ContinuousExtensionTheorem
 (fe : Fun-Ext)
 (pe : Prop-Ext)
 (pt : propositional-truncations-exist)
  where

open PropositionalTruncation pt

open import DedekindReals pe pt fe
open import MetricSpaceAltDef pt fe pe
open import MetricSpaceDedekindReals pt fe pe
open import MetricSpaceRationals fe pt pe
open import RationalsLimits fe pt pe
open import DedekindRealsProperties fe pt pe

\end{code}

The goal is to solve the following proof from Simmons Introduction to Topology and Modern Analysis:

Let X be a metric space, let Y be a complete metric space, and A be a dense subspace of X.
If f is a uniformly continuous mapping of A into Y, then f can be extended uniquely to a uniformly continuous mapping g of X into Y.

In order to prove this, it is first necessary to introduce the definitions in the proof.

First, we would like to know that every point in ℝ is a limit point for some cauchy sequence.

\begin{code}

open import OrderNotation
open import NaturalsOrder
{-
ℚ-converges-to-point-in-ℝ : (x : ℝ) → Σ S ꞉ (ℕ → ℚ) , (c : ?) → (embedding-ℚ-to-ℝ {!!} ≡ x)
ℚ-converges-to-point-in-ℝ S = {!!}
-}

{-
    S' : ℕ → ℝ
    S' _ = ι x

    ι-sequence-cauchy' : cauchy-sequence ℝ ℝ-metric-space S'
    ι-sequence-cauchy' (ε , l) = 0 , sequence-is-cauchy'
     where
      sequence-is-cauchy' : (m n : ℕ) → 0 ≤ m → 0 ≤ n → B-ℝ (S' m) (S' n) ε l
      sequence-is-cauchy' m n l₁ l₂ = ℝ-m1b (ι x) ε l

    sequence-converges' : convergent-sequence ℝ ℝ-metric-space S'
    sequence-converges' = ℝ-cauchy-sequences-are-convergent S' ι-sequence-cauchy'
 -}
 
continuous : {M₁ : 𝓤 ̇} {M₂ : 𝓥 ̇} → (m₁ : metric-space M₁) → (m₂ : metric-space M₂) → (f : M₁ → M₂) → 𝓤 ̇ 
continuous {𝓤} {𝓥} {M₁} {M₂} (B₁ , _) (B₂ , _) f = (c : M₁) → ((ε , l) : ℚ₊) → Σ (δ , l₂) ꞉ ℚ₊ , ((x : M₁) → B₁ c x δ l₂ → B₂ (f c) (f x) ε l)

open import RationalsNegation
open import RationalsMinMax fe renaming (max to ℚ-max ; min to ℚ-min)
open import RationalsAbs
open import RationalsAddition

ι-continuous : continuous ℚ-metric-space ℝ-metric-space ι
ι-continuous c (ε , 0<ε) = (ε' , 0<ε') , I 
 where
  ε' : ℚ
  ε' = 1/2 * ε
  0<ε' : 0ℚ < ε'
  0<ε' = halving-preserves-order' ε 0<ε
  I : (x : ℚ)
    → B-ℚ c x ε' 0<ε'
    → B-ℝ (ι c) (ι x) ε 0<ε
  I x B = ∣ (c - 1/4 * ε , c + 1/4 * ε , x - 1/4 * ε , x + 1/4 * ε) , (l₁ , l₂ , l₃ , l₄ , II (min-to-≤ (c - 1/4 * ε) (x - 1/4 * ε)) (max-to-≤ (c + 1/4 * ε) (x + 1/4 * ε))) ∣
   where
     general-rearrange : {a b c d : ℚ} → a + b - (c + d) ≡ a - c + (b - d)
     general-rearrange {a} {b} {c} {d} = a + b - (c + d)         ≡⟨ ℚ+-assoc fe a b (- (c + d)) ⟩
                                         a + (b + (- (c + d)))   ≡⟨ ap (λ α → a + (b + α)) (ℚ-minus-dist fe c d ⁻¹) ⟩
                                         a + (b + ((- c) - d))   ≡⟨ ap (a +_) (ℚ+-assoc fe b (- c) (- d) ⁻¹) ⟩
                                         a + (b - c - d)         ≡⟨ ap (λ α → a + (α - d)) (ℚ+-comm b (- c)) ⟩
                                         a + ((- c) + b - d)     ≡⟨ ap (a +_) (ℚ+-assoc fe (- c) b (- d)) ⟩
                                         a + ((- c) + (b - d))   ≡⟨ ℚ+-assoc fe a (- c) (b - d) ⁻¹ ⟩
                                         a - c + (b - d) ∎

     II : c - 1/4 * ε ≤ x - 1/4 * ε × (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε) ≡ c - 1/4 * ε ) ∔ x - 1/4 * ε ≤ c - 1/4 * ε × (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε) ≡ x - 1/4 * ε)
        → c + 1/4 * ε ≤ x + 1/4 * ε × (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε) ≡ x + 1/4 * ε ) ∔ x + 1/4 * ε ≤ c + 1/4 * ε × (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε) ≡ c + 1/4 * ε)
        → B-ℚ (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε)) (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε)) ε 0<ε
     II (inl (l₁ , e₁)) (inl (l₂ , e₂)) = transport (_< ε) (ℚ-metric-commutes (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε)) (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε))) i
      where     
       i : B-ℚ (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε)) (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε)) ε 0<ε
       i = transport₂ (λ α β → B-ℚ α β ε 0<ε) (e₂ ⁻¹) (e₁ ⁻¹) (ℚ≤-<-trans fe (ℚ-metric (x + 1/4 * ε) (c - 1/4 * ε)) (abs (x - c) + 1/2 * ε) ε v vi)
        where
         ii : ℚ-metric (x + 1/4 * ε) (c - 1/4 * ε) ≡ ℚ-metric (x - c) (- 1/2 * ε)
         ii = ap abs (x + 1/4 * ε - (c - 1/4 * ε)    ≡⟨ general-rearrange ⟩
                     x - c + (1/4 * ε - (- 1/4 * ε)) ≡⟨ ap (λ α → x - c + (1/4 * ε + α)) (ℚ-minus-minus fe (1/4 * ε) ⁻¹) ⟩ 
                     x - c + (1/4 * ε + 1/4 * ε)     ≡⟨ ap (x - c +_) (ℚ-distributivity' fe ε 1/4 1/4 ⁻¹) ⟩ 
                     x - c + (1/4 + 1/4) * ε         ≡⟨ ap (λ α → x - c + α * ε ) (1/4+1/4 fe) ⟩
                     x - c + 1/2 * ε                 ≡⟨ ap (x - c +_) (ℚ-minus-minus fe (1/2 * ε)) ⟩         
                     x - c - (- 1/2 * ε)  ∎)
         iii : ℚ-metric (x - c) (- 1/2 * ε) ≤ abs (x - c) + abs (- (- 1/2 * ε))
         iii = ℚ-triangle-inequality fe (x - c) (- (- 1/2 * ε))
         iv : abs (- (- 1/2 * ε)) ≡ 1/2 * ε
         iv = ap abs (ℚ-minus-minus fe (1/2 * ε) ⁻¹) ∙ abs-of-pos-is-pos' fe (1/2 * ε) 0<ε'
         v : ℚ-metric (x + 1/4 * ε) (c - 1/4 * ε) ≤ abs (x - c) + 1/2 * ε
         v = transport₂ (λ α β → β ≤ abs (x - c) + α) iv (ii ⁻¹) iii
         vi : abs (x - c) + 1/2 * ε < ε
         vi = transport (abs (x - c) + 1/2 * ε <_) vii (ℚ<-addition-preserves-order (abs (x - c)) (1/2 * ε) (1/2 * ε) (transport (_< 1/2 * ε) (ℚ-metric-commutes c x) B))
          where
           vii : 1/2 * ε + 1/2 * ε ≡ ε
           vii = ap₂ _+_ (ℚ*-comm 1/2 ε) (ℚ*-comm 1/2 ε) ∙ ℚ-into-half fe ε ⁻¹
       
     II (inl (l₁ , e₁)) (inr (l₂ , e₂)) = transport (_< ε) (ℚ-metric-commutes (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε)) (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε))) i
      where
       i : B-ℚ (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε)) (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε)) ε 0<ε
       i = transport₂ (λ α β → B-ℚ α β ε 0<ε) (e₂ ⁻¹) (e₁ ⁻¹) (transport (_< ε) (ii ⁻¹) (half-of-pos-is-less fe ε 0<ε))
        where
         ii : ℚ-metric (c + 1/4 * ε) (c - 1/4 * ε) ≡ 1/2 * ε
         ii = ap abs (c + 1/4 * ε - (c - 1/4 * ε)       ≡⟨ general-rearrange ⟩
                      (c - c) + (1/4 * ε - (- 1/4 * ε)) ≡⟨ ap₂ _+_ (ℚ-inverse-sum-to-zero fe c) (ap (1/4 * ε +_) (ℚ-minus-minus fe (1/4 * ε) ⁻¹)) ⟩
                      0ℚ + (1/4 * ε + 1/4 * ε)          ≡⟨ ℚ-zero-left-neutral fe (1/4 * ε + 1/4 * ε) ⟩
                      1/4 * ε + 1/4 * ε                 ≡⟨ ℚ-distributivity' fe ε 1/4 1/4 ⁻¹ ⟩
                      (1/4 + 1/4) * ε                   ≡⟨ ap (_* ε) (1/4+1/4 fe) ⟩
                      1/2 * ε ∎) ∙ abs-of-pos-is-pos' fe (1/2 * ε) 0<ε'
     II (inr (l₁ , e₁)) (inl (l₂ , e₂)) = transport (_< ε) (ℚ-metric-commutes (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε)) (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε))) i
      where
       i :  B-ℚ (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε)) (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε)) ε 0<ε
       i = transport₂ (λ α β → B-ℚ α β ε 0<ε) (e₂ ⁻¹) (e₁ ⁻¹) (transport (_< ε) (ii ⁻¹) (half-of-pos-is-less fe ε 0<ε))
        where
         ii : ℚ-metric (x + 1/4 * ε) (x - 1/4 * ε) ≡ 1/2 * ε
         ii = ap abs (x + 1/4 * ε - (x - 1/4 * ε)       ≡⟨ general-rearrange ⟩
                      (x - x) + (1/4 * ε - (- 1/4 * ε)) ≡⟨ ap₂ _+_ (ℚ-inverse-sum-to-zero fe x) (ap (1/4 * ε +_) (ℚ-minus-minus fe (1/4 * ε) ⁻¹)) ⟩
                      0ℚ + (1/4 * ε + 1/4 * ε)          ≡⟨ ℚ-zero-left-neutral fe (1/4 * ε + 1/4 * ε) ⟩
                      1/4 * ε + 1/4 * ε                 ≡⟨ ℚ-distributivity' fe ε 1/4 1/4 ⁻¹ ⟩
                      (1/4 + 1/4) * ε                   ≡⟨ ap (_* ε) (1/4+1/4 fe) ⟩
                      1/2 * ε ∎) ∙ abs-of-pos-is-pos' fe (1/2 * ε) 0<ε'
     II (inr (l₁ , e₁)) (inr (l₂ , e₂)) = transport (_< ε) (ℚ-metric-commutes (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε)) (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε))) i
      where
       i : B-ℚ (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε)) (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε)) ε 0<ε
       i = transport₂ (λ α β → B-ℚ α β ε 0<ε) (e₂ ⁻¹) (e₁ ⁻¹) (ℚ≤-<-trans fe (ℚ-metric (c + 1/4 * ε) (x - 1/4 * ε)) (abs (c - x) + 1/2 * ε) ε v vi)
        where
         ii : ℚ-metric (c + 1/4 * ε) (x - 1/4 * ε) ≡ ℚ-metric (c - x) (- 1/2 * ε)
         ii = ap abs (c + 1/4 * ε - (x - 1/4 * ε)    ≡⟨ general-rearrange ⟩
                     c - x + (1/4 * ε - (- 1/4 * ε)) ≡⟨ ap (λ α → c - x + (1/4 * ε + α)) (ℚ-minus-minus fe (1/4 * ε) ⁻¹) ⟩ 
                     c - x + (1/4 * ε + 1/4 * ε)     ≡⟨ ap (c - x +_) (ℚ-distributivity' fe ε 1/4 1/4 ⁻¹) ⟩ 
                     c - x + (1/4 + 1/4) * ε         ≡⟨ ap (λ α → c - x + α * ε ) (1/4+1/4 fe) ⟩
                     c - x + 1/2 * ε                 ≡⟨ ap (c - x +_) (ℚ-minus-minus fe (1/2 * ε)) ⟩         
                     c - x - (- 1/2 * ε)  ∎)
         iii : ℚ-metric (c - x) (- 1/2 * ε) ≤ abs (c - x) + abs (- (- 1/2 * ε))
         iii = ℚ-triangle-inequality fe (c - x) (- (- 1/2 * ε))
         iv : abs (- (- 1/2 * ε)) ≡ 1/2 * ε
         iv = ap abs (ℚ-minus-minus fe (1/2 * ε) ⁻¹) ∙ abs-of-pos-is-pos' fe (1/2 * ε) 0<ε'
         v : ℚ-metric (c + 1/4 * ε) (x - 1/4 * ε) ≤ abs (c - x) + 1/2 * ε
         v = transport₂ (λ α β → β ≤ abs (c - x) + α) iv (ii ⁻¹) iii
         vi : abs (c - x) + 1/2 * ε < ε
         vi = transport (abs (c - x) + 1/2 * ε <_) vii (ℚ<-addition-preserves-order (abs (c - x)) (1/2 * ε) (1/2 * ε) B)
          where
           vii : 1/2 * ε + 1/2 * ε ≡ ε
           vii = ap₂ _+_ (ℚ*-comm 1/2 ε) (ℚ*-comm 1/2 ε) ∙ ℚ-into-half fe ε ⁻¹
           
     abstract       
     
      0<ε'' : 0ℚ <ℚ 1/4 * ε
      0<ε'' = quarter-preserves-order' ε 0<ε
      l₁ : c - 1/4 * ε <ℚ c
      l₁ = ℚ<-subtraction-preserves-order fe c (1/4 * ε) 0<ε''
      l₂ : x - 1/4 * ε <ℚ x
      l₂ = ℚ<-subtraction-preserves-order fe x (1/4 * ε) 0<ε''
      l₃ : c <ℚ c + 1/4 * ε
      l₃ = ℚ<-addition-preserves-order'' fe c (1/4 * ε) 0<ε''
      l₄ : x <ℚ x + 1/4 * ε
      l₄ = ℚ<-addition-preserves-order'' fe x (1/4 * ε) 0<ε''

{-
I
 where
  S : ℕ → ℝ
  S _ = ι c

  ι-sequence-cauchy : cauchy-sequence ℝ ℝ-metric-space S
  ι-sequence-cauchy (ε , l) = 0 , sequence-is-cauchy
   where
    sequence-is-cauchy : (m n : ℕ) → 0 ≤ m → 0 ≤ n → B-ℝ (S m) (S n) ε l
    sequence-is-cauchy m n l₁ l₂ = ℝ-m1b (ι c) ε l
    
  sequence-converges : convergent-sequence ℝ ℝ-metric-space S
  sequence-converges = ℝ-cauchy-sequences-are-convergent S ι-sequence-cauchy
  
  I : (x : ℚ) → B-ℚ c x ε 0<ε → B-ℝ (ι c) (ι x) ε 0<ε
  I x B = ∥∥-rec ∃-is-prop II sequence-converges
   where
    II : Σ y ꞉ ℝ , ((((ε , l) : ℚ₊) → Σ _ ꞉ ℕ , ((n : ℕ) → _ → B-ℝ y (ι c) ε l)))
       → B-ℝ (ι c) (ι x) ε 0<ε
    II (y , f) = {!!}
     where
      c-ε/2-close : Σ N ꞉ ℕ , ((n : ℕ) → N < n → B-ℝ y (ι c) (1/2 * ε) {!!})
      c-ε/2-close = f (1/2 * ε , {!!})  
-}

\end{code}

I am first going to try and show that certain functions are continuous, and attempt to extend them directly, as a proof of concept.

\begin{code}

ℚ-id : ℚ → ℚ
ℚ-id = id

ℚ-id-continuous : continuous ℚ-metric-space ℚ-metric-space ℚ-id
ℚ-id-continuous c (ε , 0<ε) = (ε , 0<ε) , I
 where
  I : (x : ℚ) → B-ℚ c x ε 0<ε → B-ℚ (id c) (id x) ε 0<ε
  I x B = B

ℚ-ℝ-id : ℚ → ℝ
ℚ-ℝ-id = ι ∘ id
{-
ℚ-ℝ-id-continuous : continuous ℚ-metric-space ℝ-metric-space ℚ-ℝ-id
ℚ-ℝ-id-continuous c (ε , 0<ε) = (ε , 0<ε) , I
 where
  I : (x : ℚ) → B-ℚ c x ε 0<ε → B-ℝ (ℚ-ℝ-id c) (ℚ-ℝ-id x) ε 0<ε
  I x B = {!!}

every-point-in-ℝ-limit-point : (x : ℝ) → {!Σ !}
every-point-in-ℝ-limit-point = {!!}
-}
open import RationalsMultiplication
open import RationalsNegation
open import UF-Powerset
{-
continuous-extension-theorem : (f : ℚ → ℝ)
                             → continuous ℚ-metric-space ℝ-metric-space f
                             → ∃! g ꞉ (ℝ → ℝ) , (continuous ℝ-metric-space ℝ-metric-space g)
continuous-extension-theorem f f-continuous = (g , g-continuous) , g-unique
 where
  g : ℝ → ℝ
  g x = {!!}
   where
    Sl : ℕ → ℝ
    Sl n = embedding-ℚ-to-ℝ {!!}
     where
      I : {!!} 
      I = ℝ-arithmetically-located x (⟨1/sn⟩ n) {!!}
    res1 : (S : ℕ → ℝ) → cauchy→convergent ℝ ℝ-metric-space S
    res1 = ℝ-cauchy-sequences-are-convergent
  
  g-continuous : continuous ℝ-metric-space ℝ-metric-space g
  g-continuous = {!!}
  
  g-unique : is-central (Σ (continuous ℝ-metric-space ℝ-metric-space)) (g , g-continuous)
  g-unique (g' , g'-continuous) = {!!}
-}
open import RationalsAddition

ℚ-addition-to-ℝ : ℚ → ℚ → ℝ
ℚ-addition-to-ℝ p q = embedding-ℚ-to-ℝ (p + q)

ℚ-succ : ℚ → ℚ
ℚ-succ q = q + 1ℚ

ℚ-succ-to-ℝ : ℚ → ℝ
ℚ-succ-to-ℝ q = embedding-ℚ-to-ℝ (ℚ-succ q)
{-
ℚ-succ-to-ℝ-continuous : continuous ℚ-metric-space ℝ-metric-space ℚ-succ-to-ℝ
ℚ-succ-to-ℝ-continuous c ε = {!!}

rationals-extension : (ℚ → ℚ) → ℝ → ℝ
rationals-extension f = {!!}

ℝ-succ : ℝ → ℝ
ℝ-succ = rationals-extension ℚ-succ
 where
  this : {!!}
  this = {!!}
-}

\end{code}


{-
continuous-extension-theorem : {M₁ : 𝓤 ̇} → {M₂ : 𝓥 ̇}
                             → (m₁ : metric-space M₁) → (m₂ : complete-metric-space M₂) → {!!}
continuous-extension-theorem = {!!}
-}
