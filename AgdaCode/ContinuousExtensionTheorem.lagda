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

First, we would like to know that every point in ℝ is a limit point for some cauchy sequence. <- This is impossible constructively, so search for another solution.

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


 -- This needs to be cleaned up, abstract two proofs to chop proof in half
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


composition-preserves-continuity : {M₁ : 𝓤 ̇} {M₂ : 𝓥 ̇} {M₃ : 𝓦 ̇}
                                 → (m₁ : metric-space M₁)
                                 → (m₂ : metric-space M₂)
                                 → (m₃ : metric-space M₃)
                                 → (f : M₁ → M₂)
                                 → (g : M₂ → M₃)
                                 → continuous m₁ m₂ f
                                 → continuous m₂ m₃ g
                                 → continuous m₁ m₃ (g ∘ f) 
composition-preserves-continuity  {𝓤} {𝓥} {𝓦} {M₁} {M₂} {M₃} (B₁ , m₁) (B₂ , m₂) (B₃ , m₃) f g c₁ c₂ c (ε , l) = I (c₂ (f c) (ε , l))
 where
  I : Σ (δ , 0<δ) ꞉ ℚ₊ , ((y : M₂) → B₂ (f c) y δ 0<δ → B₃ (g (f c)) (g y) ε l)
    → Σ (κ , 0<κ) ꞉ ℚ₊ , ((x : M₁) → B₁ c x κ 0<κ → B₃ (g (f c)) (g (f x)) ε l)
  I ((δ , 0<δ) , τ) = II (c₁ c (δ , 0<δ))
   where
    II : (Σ (δ₁ , 0<δ₁) ꞉ ℚ₊ , ((z : M₁) → B₁ c z δ₁ 0<δ₁ → B₂ (f c) (f z) δ 0<δ))
        → Σ (κ , 0<κ) ꞉ ℚ₊ , ((x : M₁) → B₁ c x κ 0<κ → B₃ (g (f c)) (g (f x)) ε l)
    II ((δ₁ , 0<δ₁) , τ₁) = (δ₁ , 0<δ₁) , λ x B → τ (f x) (τ₁ x B)

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
ℚ-ℝ-id = ι ∘ ℚ-id

ℚ-ℝ-id-continuous : continuous ℚ-metric-space ℝ-metric-space ℚ-ℝ-id
ℚ-ℝ-id-continuous = composition-preserves-continuity ℚ-metric-space ℚ-metric-space ℝ-metric-space ℚ-id ι ℚ-id-continuous ι-continuous

\end{code}

Now we have that the function from ℚ-ℝ-id is continuous. We want to extend this function from the rationals to the reals.

\begin{code}

open import DedekindRealsOrder pe pt fe
open import DedekindRealsAddition pe pt fe renaming (_+_ to _ℝ+_)
{-
ℝ-no-maximum : (x : ℝ) → Σ y ꞉ ℝ , y < x ∔ x < y
ℝ-no-maximum x = {!weak-linearity ? ? ? ?!}

ℝ-id : ℝ → ℝ
ℝ-id r = ℚ-ℝ-id (I by-ℚ-ℝ-id-continuity)
 where
  S : ℕ → ℚ
  S = ⟨1/sn⟩
  
  by-ℚ-ℝ-id-continuity : (c : ℚ) → ((ε , l) : ℚ₊) → Σ (δ , l₂) ꞉ ℚ₊ , ((x : ℚ) → B-ℚ c x δ l₂ → B-ℝ (ℚ-ℝ-id c) (ℚ-ℝ-id x) ε l)
  by-ℚ-ℝ-id-continuity = ℚ-ℝ-id-continuous
  
  I : ((c : ℚ) → ((ε , l) : ℚ₊) → Σ (δ , l₂) ꞉ ℚ₊ , ((x : ℚ) → B-ℚ c x δ l₂ → B-ℝ (ℚ-ℝ-id c) (ℚ-ℝ-id x) ε l)) → ℚ
  I f = {!!}
   where
    II : {!!}
    II = {!f 0 1!}


ℝ-id' : ℝ → ℝ
ℝ-id' r = I (by-ℚ-ℝ-id-continuity)
 where
  
  by-ℚ-ℝ-id-continuity : (c : ℚ) → ((ε , l) : ℚ₊) → Σ (δ , l₂) ꞉ ℚ₊ , ((x : ℚ) → B-ℚ c x δ l₂ → B-ℝ (ℚ-ℝ-id c) (ℚ-ℝ-id x) ε l)
  by-ℚ-ℝ-id-continuity = ℚ-ℝ-id-continuous
  
  I : ((c : ℚ) → ((ε , l) : ℚ₊) → Σ (δ , l₂) ꞉ ℚ₊ , ((x : ℚ) → B-ℚ c x δ l₂ → B-ℝ (ℚ-ℝ-id c) (ℚ-ℝ-id x) ε l)) → ℝ
  I f = (left , right) , {!!}
   where
    left : ℚ-subset-of-propositions
    left p = B-ℝ {!!} {!!} {!!} {!!} , {!!}
    right : ℚ-subset-of-propositions
    right = {!!}
-}
\end{code}

The problem goes even further. There is no way to find a q in relation to r without q being truncated, and we cannot escape truncations since neither Q or R are subsingletons.
That is, not only can I not find a q close to r (without truncation), I cannot find a q any distance from r without truncation.

So how do we find to find a q close to r? We cannot.

The only way I see to get access to values is by defining the "fbar" function. 

\begin{code}

open import RationalsMultiplication
open import RationalsNegation
open import UF-Powerset

{-
ℚ-continuous-has-inverse :  (f : ℚ → ℚ) → continuous ℚ-metric-space ℚ-metric-space f
                         → Σ g ꞉ (ℚ → ℚ) , continuous ℚ-metric-space ℚ-metric-space g × (g ∘ f ≡ id)
ℚ-continuous-has-inverse f cont = I , II
 where
  I : ℚ → ℚ
  I q = i {!by-f-continuity q!}
   where
    i : {!!}
    i = {!!}
  II : continuous ℚ-metric-space ℚ-metric-space I × (I ∘ f ≡ id)
  II = {!!}
  by-f-continuity : (c : ℚ) → ((ε , 0<ε) : ℚ₊) → Σ (δ , 0<δ) ꞉ ℚ₊ , ((x : ℚ) → B-ℚ c x δ 0<δ → B-ℚ (f c) (f x) ε 0<ε)
  by-f-continuity = cont 
-}

f^ : (f g : ℚ → ℚ)
   → continuous ℚ-metric-space ℚ-metric-space f
   → continuous ℚ-metric-space ℚ-metric-space g
   → ((k : ℚ) → (f ∘ g) k ≡ k)
   → ((k : ℚ) → (g ∘ f) k ≡ k)
   → ℝ → ℝ
f^ f g f-cont g-cont e₁ e₂ r = z
 where
  z : ℝ
  z =  (L , R) , inhabited-left-z , inhabited-right-z , rounded-left-z , rounded-right-z , disjoint-z , located-z
   where

\end{code}

So we adopt the same strategy as we used to show that monotonic functions can be extended. Now we have access to some p and q.

My initial thought is to use the same condition as we used before. The idea is the since we have continuity, this property allows us to extract the reals conditions.
Working in reverse, we impose conditions base on (g p) < r, (since we can obtain p' < r → g p' ≡ g (f p') ≡ p').

However, I actually think this is not a strong enough condition. We don't know how f p behaves, so some of the conditions are now not automatic.
The monotinicity result is extremely strong, since it gives us order on g.

I believe we need to design a condition L and R, which is related to continuity.

We have that ∀ ε , δ > 0 , ∀ x c →  | x - c | < δ  → | f x - f c | < ε
                                    | x - c | < δ →  | g x - g c | < ε

We have some r , mapping to r' , but we are defining r'.

                         p < r' → condition    with     condition ⇔ ?
                         
                         We require that if a < r then f a < r' . But I see here that a = g b for some b. b = f a.
                         So we want b < r' ⇔ g b < r. This is fine by bijectivity of f , g.

So then, the question is, is continuity strong enough to be able to construct this real?

\begin{code}

    L : ℚ-subset-of-propositions
    L p = (g p < r) , ∈-is-prop (lower-cut-of r) (g p)
    R : ℚ-subset-of-propositions
    R q = (r < g q) , ∈-is-prop (upper-cut-of r) (g q)
    inhabited-left-z : inhabited-left L
    inhabited-left-z = ∥∥-functor I (inhabited-from-real-L r)
     where
      I : Σ p ꞉ ℚ , p < r → Σ p' ꞉ ℚ , g p' < r
      I (p , p<r) = (f p) ,  transport (_< r) (e₂ p ⁻¹) p<r
      
    inhabited-right-z : inhabited-right R
    inhabited-right-z = ∥∥-functor I (inhabited-from-real-R r)
     where
      I : Σ q ꞉ ℚ , r < q → Σ q' ꞉ ℚ , r < g q'
      I (q , r<q) = f q ,  transport (r <_) (e₂ q ⁻¹) r<q 

\end{code}

Inhabitedness is trivial and is lifted from the monotonicity proof. It doesn't make use of monotonicity/continuity properties.

Roundedness is where the problem begins. Following the same proof pattern, this reduces to proving:

 Given that

 g p < p' < r

 is p < f p'?

 The only thing we have is continuity of f and g. I don't think this is possible.

 But we have not considered the standard theorem, which perhaps we could introduce at this point now that we have access to p and p'.

 Cauchy sequences on rationals?
 Different condition for z (I believe the current condition would have to be extended rather than replaced)?
 Or perhaps the above is easilu provable and I'm not seeing it.

\begin{code}

    rounded-left-z : rounded-left L
    rounded-left-z p = ltr , rtl
     where
      ltr : g p < r → ∃ p' ꞉ ℚ , p < p' × g p' < r
      ltr gp<r = ∥∥-functor I (rounded-left-b (lower-cut-of r) (rounded-from-real-L r) (g p) gp<r)
       where
        I : Σ p' ꞉ ℚ , (g p) < p' × p' < r → Σ p' ꞉ ℚ , p < p' × (g p' < r)
        I (p' , gp<p' , p'<r) = (f p') , {!not-true!} , (transport (_< r) (e₂ p' ⁻¹) p'<r)
         where
          by-continuity : {!!}
          by-continuity = {!!}
      
      rtl : {!!}
      rtl = {!!}
     
    
    rounded-right-z : rounded-right R
    rounded-right-z = {!!}
    
    disjoint-z : disjoint L R
    disjoint-z = {!!}
    
    located-z : located L R
    located-z = {!!}

  


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

{-
ℚ-addition-to-ℝ : ℚ → ℚ → ℝ
ℚ-addition-to-ℝ p q = embedding-ℚ-to-ℝ (p + q)

ℚ-succ : ℚ → ℚ
ℚ-succ q = q + 1ℚ

ℚ-succ-to-ℝ : ℚ → ℝ
ℚ-succ-to-ℝ q = embedding-ℚ-to-ℝ (ℚ-succ q)
-}
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

f^' : (f g : ℚ → ℚ)
    → continuous ℚ-metric-space ℚ-metric-space g
    → ℝ → ℝ
f^' f f-cont e r = z
 where
  z : ℝ
  z =  (L , R) , inhabited-left-z , inhabited-right-z , rounded-left-z , rounded-right-z , disjoint-z , located-z
   where

    L : ℚ-subset-of-propositions
    L p = (∃ u ꞉ ℚ , u < f u) , {!!}
    
    R : ℚ-subset-of-propositions
    R q = {!f q !} , {!!} 
    
    inhabited-left-z : inhabited-left L
    inhabited-left-z = {!!}
      
    inhabited-right-z : inhabited-right R
    inhabited-right-z = {!!}


    rounded-left-z : rounded-left L
    rounded-left-z p = ltr , rtl
     where
      ltr : {!!}
      ltr = {!!}
      rtl : {!!}
      rtl = {!!}
     
    
    rounded-right-z : rounded-right R
    rounded-right-z = {!!}
    
    disjoint-z : disjoint L R
    disjoint-z = {!!}
    
    located-z : located L R
    located-z = {!!}



\end{code}
