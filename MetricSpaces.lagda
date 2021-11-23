
\begin{code}
{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆)  -- TypeTopology
open import Rationals renaming (_≤_ to _ℚ≤_ ; _<_ to _ℚ<_)

open import UF-PropTrunc --TypeTopology
open import UF-FunExt --TypeTopology

module MetricSpaces
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
       where 
open import NewDedekindReals pt fe

open import NaturalsOrder renaming (_<_ to _ℕ<_ ; _≤_ to _ℕ≤_ ; max to ℕmax)
open import UF-PropTrunc
open PropositionalTruncation pt

\end{code}

The following are the three conditions that define a metric function

\begin{code}

m1 : {𝓤 : Universe} → (X : 𝓤 ̇) → (d : X → X → ℝ) → 𝓤₁ ⊔ 𝓤 ̇
m1 X d = (x y : X) → (zero-ℝ ≤ d x y) × (d x y ≡ zero-ℝ ⇔ x ≡ y)

m2 : {𝓤 : Universe} → (X : 𝓤 ̇) → (d : X → X → ℝ) → 𝓤₁ ⊔ 𝓤 ̇
m2 X d = (x y : X) → d x y ≡ d y x

--Ultrametric definition vs standard, since I standard edition uses addition for triangle inequality
m3 : {𝓤 : Universe} → (X : 𝓤 ̇) → (d : X → X → ℝ) → 𝓤 ̇ 
m3 X d = (x y z : X) → d x y ≤ max (d x z) (d y z)

\end{code}

Now I define metric and complete metric spaces.

A space is a metric space if it satisfies the above three conditions.

A space is a complete metric space if every cauchy sequence in a metric space is also a convergent sequence.

Convergent and Cauchy Sequences are also defined below. In a metric space, all convergent sequences are cauchy sequences.

A definition is also given for what it means for a function to be continous, and what it means for a subspace of a space to be dense.

\begin{code}

metric-space : {𝓤 : Universe} → (X : 𝓤 ̇) → 𝓤₁ ⊔ 𝓤 ̇
metric-space X  = Σ d ꞉ (X → X → ℝ) , m1 X d × m2 X d × m3 X d

convergent-sequence : {𝓤 : Universe} → (X : 𝓤 ̇) → metric-space X → (S : ℕ → X) → 𝓤₁ ⊔ 𝓤 ̇
convergent-sequence X (d , _) S = ∃ x ꞉ X , ((ε : ℝ) → zero-ℝ < ε → Σ N ꞉ ℕ , ((n : ℕ) → N ℕ< n → d (S n) x < ε))

cauchy-sequence : {𝓤 : Universe} → (X : 𝓤 ̇) → metric-space X → (S : ℕ → X) → 𝓤₁ ̇
cauchy-sequence X (d , _) S = (ε : ℝ) → zero-ℝ < ε → ∃ N ꞉ ℕ , ((m n : ℕ) → N ℕ< m → N ℕ< n → d (S m) (S n) < ε)

convergent→cauchy : {𝓤 : Universe} → (X : 𝓤 ̇) → (m : metric-space X) → (S : ℕ → X) → 𝓤₁ ⊔ 𝓤 ̇
convergent→cauchy X m S = convergent-sequence X m S → cauchy-sequence X m S

cauchy→convergent : {𝓤 : Universe} → (X : 𝓤 ̇) → metric-space X → (S : ℕ → X) → 𝓤₁ ⊔ 𝓤 ̇
cauchy→convergent X m S = cauchy-sequence X m S → convergent-sequence X m S

complete-metric-space : {𝓤 : Universe} → (X : 𝓤 ̇) → 𝓤₁ ⊔ 𝓤 ̇
complete-metric-space X = Σ m ꞉ (metric-space X) , ((S : ℕ → X) → cauchy→convergent X m S)

uniformly-continuous : {𝓤 𝓥 : Universe} → (X : 𝓤 ̇) → (Y : 𝓥 ̇) → metric-space X → metric-space Y → (f : X → Y) → 𝓤₁ ⊔ 𝓤 ̇
uniformly-continuous X Y (d₁ , _) (d₂ , _) f = (ε : ℝ) → zero-ℝ < ε → ∃ δ ꞉ ℝ , ((x y : X) → d₁ x y < δ → d₂ (f x) (f y) < δ)

open import UF-Retracts --TypeTopology
open import UF-Powerset --TypeTopology

subspace-of-metric-space-is-metric-space : {𝓤 𝓥 : Universe} → (A : 𝓤 ̇) → (X : 𝓥 ̇) → A ◁ X → metric-space X → metric-space A
subspace-of-metric-space-is-metric-space A X (f , g , r) (d , m1 , m2 , m3) = d' , m1' , m2' , m3'
 where
  d' : A → A → ℝ
  d' a₁ a₂ = d (g a₁) (g a₂)
  m1' : _
  m1' a₁ a₂ = I , II , III
   where
    from-X : (zero-ℝ ≤ d (g a₁) (g a₂)) × (d (g a₁) (g a₂) ≡ zero-ℝ ⇔ g a₁ ≡ g a₂)
    from-X = m1 (g a₁) (g a₂)
    
    I : zero-ℝ ≤ d (g a₁) (g a₂)
    I = pr₁ from-X
    
    II : d' a₁ a₂ ≡ zero-ℝ → a₁ ≡ a₂
    II e = a₁         ≡⟨ refl ⟩
           id a₁      ≡⟨ r a₁ ⁻¹ ⟩
           (f ∘ g) a₁ ≡⟨ ap f ii ⟩
           (f ∘ g) a₂ ≡⟨ r a₂ ⟩
           id a₂      ≡⟨ refl ⟩
           a₂ ∎
     where
      i : d (g a₁) (g a₂) ≡ zero-ℝ → g a₁ ≡ g a₂
      i = lr-implication (pr₂ from-X)
      ii : g a₁ ≡ g a₂
      ii = i e
    
    III : a₁ ≡ a₂ → d' a₁ a₂ ≡ zero-ℝ
    III e = i (ap g e)
     where
      i : g a₁ ≡ g a₂ → d (g a₁) (g a₂) ≡ zero-ℝ
      i = rl-implication (pr₂ from-X)
      
  m2' : _
  m2' a₁ a₂ = m2 (g a₁) (g a₂)

  m3' : _
  m3' a₁ a₂ a₃ = m3 (g a₁) (g a₂) (g a₃)

--Need to clarify this definition for general proof
--Subspaces of metric spaces are automatic as above

--Subspace is retract of

dense-in : {𝓤 𝓥 : Universe} → (A : 𝓤 ̇) → (X : 𝓥 ̇) → metric-space X → 𝓤₁ ⊔ 𝓤 ⊔ 𝓥 ̇
dense-in A X (d , _) = (r : A ◁ X) → (ε : ℝ) → zero-ℝ < ε → (x : X) → ∃ a ꞉ A , (d x (section r a) < ε)

\end{code}

With all of the above conditions, then the following theorem can be applied:

\begin{code}

open import UF-Subsingletons

ccp-lemma1 : (ε p r : ℝ) → p < ε → r < ε → max p r < ε
ccp-lemma1 ((L , R) , _) ((Lₚ , Rₚ) , _) ((Lᵣ , Rᵣ) , _) l₁ l₂ = ∥∥-functor I (binary-choice l₁ l₂)
 where
  I : (Σ a ꞉ ℚ , a ∈ Rₚ × a ∈ L) × (Σ b ꞉ ℚ , b ∈ Rᵣ × b ∈ L) → Σ c ꞉ ℚ , c ∈ pr₂ (pr₁ (max ((Lₚ , Rₚ) , _) ((Lᵣ , Rᵣ) , _))) × c ∈ L
  I = {!!}

ccp-lemma2 : (x y z : ℝ) → x ≤ y → y < z → x < z
ccp-lemma2 ((L₁ , R₁) , _) ((L₂ , R₂) , _) ((L₃ , R₃) , _) l₁ l₂ = ∥∥-functor I l₂
 where
  I : Σ p ꞉ ℚ , p ∈ R₂ × p ∈ L₃ → Σ q ꞉ ℚ , q ∈ R₁ × q ∈ L₃
  I (p , p-R₂ , p-L₃) = p , ({!!} , p-L₃)
   where
    i : {!!}
    i = l₁ p {!!}

convergent→cauchy-proof : {𝓤 : Universe} → (X : 𝓤 ̇) → (m : metric-space X) → (S : ℕ → X) → convergent→cauchy X m S
convergent→cauchy-proof X (d , m1 , m2 , m3) S convergent ε l = ∥∥-functor I convergent
 where
  I : (Σ x ꞉ X , ((ε₁ : ℝ) → zero-ℝ < ε₁ → Σ N₀ ꞉ ℕ , ((n : ℕ) → N₀ ℕ< n → d (S n) x < ε₁)))
      →  Σ N ꞉ ℕ , ((m n : ℕ) → N ℕ< m → N ℕ< n → d (S m) (S n) < ε)
  I (x , f) = i (f ε l)
   where
    i : (Σ N₀ ꞉ ℕ , ((n : ℕ) → N₀ ℕ< n → d (S n) x < ε))
      → Σ N ꞉ ℕ , ((m n : ℕ) → N ℕ< m → N ℕ< n → d (S m) (S n) < ε)
    i (N₀ , g) = N₀ , ii 
     where
      ii : (m n : ℕ) → N₀ ℕ< m → N₀ ℕ< n → d (S m) (S n) < ε
      ii m n l₂ l₃ = ccp-lemma2 (d (S m) (S n)) (max (d (S m) x) (d (S n) x)) ε α (ccp-lemma1 ε (d (S m) x) (d (S n) x) β γ)
       where
        α : d (S m) (S n) ≤ max (d (S m) x) (d (S n) x)
        α = m3 (S m) (S n) x
        β : d (S m) x < ε
        β = g m l₂
        γ : d (S n) x < ε
        γ = g n l₃


general-theorem-sketch : {𝓤 𝓥 𝓦 : Universe}
                       → (A : 𝓤 ̇)
                       → (X : 𝓥 ̇)
                       → (Y : 𝓦 ̇)
                       → (m₁ : metric-space A)
                       → (m₂ : metric-space X)
                       → ((m₃ , _) : complete-metric-space Y)
                       → dense-in A X m₂
                       → (f : A → Y)
                       → uniformly-continuous A Y m₁ m₃ f
                       → ∃! g ꞉ (X → Y) , uniformly-continuous X Y m₂ m₃ g
general-theorem-sketch A X Y = {!!}

open import Integers

mod : ℚ → ℚ
mod ((pos x , a) , p)     = (pos x , a) , p
mod ((negsucc x , a) , _) = toℚ {!!}

--May not need ℚ-metric, since ℚ ◃ ℝ and ℝ is a metric space
ℚ-metric : ℚ → ℚ → ℝ
ℚ-metric = {!!}

ℚ-m1 : m1 ℚ ℚ-metric
ℚ-m1 = {!!}

ℚ-m2 : m2 ℚ ℚ-metric
ℚ-m2 = {!!}

ℚ-m3 : m3 ℚ ℚ-metric
ℚ-m3 = {!!}

ℚ-metric-space : metric-space ℚ
ℚ-metric-space = ℚ-metric , ℚ-m1 , ℚ-m2 , ℚ-m3

ℝ-metric : ℝ → ℝ → ℝ
ℝ-metric x y = {!!}

ℝ-m1 : m1 ℝ ℝ-metric
ℝ-m1 = {!!}

ℝ-m2 : m2 ℝ ℝ-metric
ℝ-m2 = {!!}

ℝ-m3 : m3 ℝ ℝ-metric
ℝ-m3 = {!!}

ℝ-metric-space : metric-space ℝ
ℝ-metric-space = ℝ-metric , ℝ-m1 , ℝ-m2 , ℝ-m3

ℝ-complete-metric-space : complete-metric-space ℝ 
ℝ-complete-metric-space = ℝ-metric-space , {!!}

--Not sure how to write density
--I have an easy proof of this one.
-- ℚ-dense-in-ℝ : (x y : ℝ) → (x < y) → Σ q ꞉ ℚ , (x < embedding-ℚ-to-ℝ q) × (embedding-ℚ-to-ℝ q < y)
-- ℚ-dense-in-ℝ = {!!}

ℚ-dense-in-ℝ : 𝓤₁  ̇
ℚ-dense-in-ℝ = (x : ℝ) → (ε : ℝ) → zero-ℝ < ε → ∃ q ꞉ ℚ , (ℝ-metric x (embedding-ℚ-to-ℝ q) < ε)

ℚ-dense-in-ℝ-proof : ℚ-dense-in-ℝ
ℚ-dense-in-ℝ-proof x ε l = {!!}

theorem-sketch : (m₁ : metric-space ℚ)
               → (m₂ : metric-space ℝ)
               → ((m₃ , _) : complete-metric-space ℝ)
               → ℚ-dense-in-ℝ
               → (f : ℚ → ℝ)
               → uniformly-continuous ℚ ℝ m₁ m₃ f
               → ∃ g ꞉ (ℝ → ℝ) , uniformly-continuous ℝ ℝ m₂ m₃ g
theorem-sketch m1 m2 (m3 , complete) dense f unif = {!!}
 where
  


\end{code}

Step 1 : Since ℚ is dense, x is the limit of a convergent sequence aₙ in ℝ. I need to show that ℚ dense → existence of convergent sequence for each x in ℝ
           i.e ∀ (x : ℝ) , ∃ S ꞉ (ℕ → ℝ) , (ε : ℝ) → zero-ℝ < ε → Σ N ꞉ ℕ , ((n : ℕ) → N ℕ< n → d (S n) x < ε)

Step 2 : Since S is convergent, it is cauchy. Since f is uniformly continuous, {f(aₙ)} is also a Cauchy sequence (requires proof)

Step 3 : Since ℝ is complete,  ∃ g(x) ∈ ℝ such that f(aₙ) → g(x)

Step 4 : Prove that this function is unique. (By theorem-sketch-is-prop?)


--X should have a zero-element
--X should be ordered
--X should have equality

--metric : {𝓤 : Universe} → {X : 𝓤 ̇} → {!!}
--metric = {!!}

-- Ultrametric:
-- m : X × X → ℝ
-- m (x , y) ≡ 0 ⇔ x ≡ y
-- m (x , y) ≡ m (y , x)
-- m (x , z) ≤ max (m (x , y) , m (y , z))

-- ≤-max : R × R × R → 𝓤
-- ≤-max (x , y , z) = 

-- max : R × R → R
-- [    ]     x
-- [        ] y
-- [        ] max

-- A function f is uniformly continuous
-- ∀ ε , ∃ δ , m (x , y) ≤ δ → m (f x , f y) ≤ ε  
-- mod : ℝ (ε) → ℝ (δ)
-- mod := pr₁ ε

-- (ℚ → ℚ) → (ℝ → ℝ)
--single variable 
final-goal : (ℚ → ℝ) → (ℝ → ℝ)
final-goal f ((L , R) , conditions)  = {!!}

--           <--->δ
-- L[             ]x[            ]R
-- L[        ]fx[                ]R
---<---------->ε

-- L[ 1  2 ] x  [ 3 4 ]R
-- L[ 4  1 ] fx [ 2 3 ]R

embed : (ℚ → ℚ) → (ℝ → ℝ)
embed = final-goal ∘ (embedding-ℚ-to-ℝ ∘_)
