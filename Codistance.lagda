Martin Escardo, 11th September 2018
Completed by Todd Waugh Ambridge, 15th May 2020

We begin by defining a "codistance" or "closeness" function

  c : X → X → ℕ∞

such that

  c x y ≡ ∞ ⇔ x ≡ y

for some examples of types X, including Baire, Cantor and ℕ∞.

That is, two points are equal iff they are infinitely close.  If we
have c x y ≡ under n for n : ℕ, the intuition is that x and y can be
distinguished by a finite amount of information of size n.

(An application is to show that WLPO holds iff ℕ∞ is discrete.)

We then discuss further codistance axioms.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt

module Codistance (fe : FunExt) where

open import Sequence fe
open import CoNaturals fe
open import CoNaturalsArithmetic fe
open import GenericConvergentSequence renaming (min to min')
open import DiscreteAndSeparated
open import UF-Miscelanea
open import Two-Properties

module sequences
        {𝓤 : Universe}
        (D : 𝓤 ̇ )
        (δ : is-discrete D)
       where

\end{code}

We denote the type of sequences over D by $, and define a codistance
function $ → $ → ℕ∞ using the fact that ℕ∞ is the final coalgebra of
the functor 𝟙 + (-), which we refer to as corecursion.

\begin{code}

 private
  𝓢 : 𝓤 ̇
  𝓢 = ℕ → D
  X : 𝓤 ̇
  X = 𝓢 × 𝓢
  f : (α β : 𝓢) → head α ≡ head β → 𝟙 {𝓤₀} + X
  f α β q = inr (tail α , tail β)
  g : (α β : 𝓢) → head α ≢ head β → 𝟙 {𝓤₀} + X
  g α β n = inl *
  p : X → 𝟙 {𝓤₀} + X
  p (α , β) = cases (f α β) (g α β) (δ (head α) (head β))
  c : 𝓢 → 𝓢 → ℕ∞
  c = curry (ℕ∞-corec p)
 
\end{code}

We use the private name "c" in this submodule, which is exported as
"codistance":

\begin{code}

 codistance : 𝓢 → 𝓢 → ℕ∞
 codistance = c

\end{code}

The two defining properties of the function c are the following:

\begin{code}

 codistance-eq₀ : (α β : 𝓢) → head α ≢ head β
                → c α β ≡ Zero
 codistance-eq₁ : (α β : 𝓢) → head α ≡ head β
                → c α β ≡ Succ (c (tail α) (tail β))
                
 codistance-eq₀ α β n = γ r
  where
   t : δ (head α) (head β) ≡ inr n
   t = discrete-inr (fe 𝓤 𝓤₀) δ (head α) (head β) n
   r : p (α , β) ≡ inl *
   r = ap (cases (f α β) (g α β)) t
   γ : p (α , β) ≡ inl * → c α β ≡ Zero
   γ = Coalg-morphism-Zero p (α , β) *

 codistance-eq₁ α β q = γ r
  where
   t : δ (head α) (head β) ≡ inl q
   t = discrete-inl δ (head α) (head β) q
   r : p (α , β) ≡ inr (tail α , tail β)
   r = ap (cases (f α β) (g α β)) t
   γ : p (α , β) ≡ inr (tail α , tail β)
     → c α β ≡ Succ (c (tail α) (tail β))
   γ = Coalg-morphism-Succ p (α , β) (tail α , tail β)

\end{code}

That any sequence is infinitely close to itself is proved by
coinduction on ℕ∞ using codistance-eq₁:

\begin{code}

 infinitely-close-to-itself : (α : 𝓢) → c α α ≡ ∞
 infinitely-close-to-itself α = ℕ∞-coinduction R b (c α α) ∞ γ
  where
   l : ∀ α → c α α ≡ Succ (c (tail α) (tail α))
   l α = codistance-eq₁ α α refl
   R : ℕ∞ → ℕ∞ → 𝓤 ̇
   R u v = (Σ α ꞉ 𝓢 , u ≡ c α α) × (v ≡ ∞)
   b : ℕ∞-bisimulation R
   b .(c α α) .∞ ((α , refl) , refl) = s , t , Pred-∞-is-∞
    where
     s : positivity (c α α) ≡ positivity ∞
     s = successors-same-positivity (l α) ((Succ-∞-is-∞ (fe 𝓤₀ 𝓤₀))⁻¹)
     t : Σ α' ꞉ 𝓢 , Pred (c α α) ≡ c α' α'
     t = tail α , (ap Pred (l α) ∙ Pred-Succ)
   γ : R (c α α) ∞
   γ = (α , refl) , refl

\end{code}

That any two infinitely close sequences are equal is proved by
coinduction on sequences, using both codistance-eq₀ (to rule out an
impossible case) and codistance-eq₁ (to establish the result):

\begin{code}

 infinitely-close-are-equal : (α β : 𝓢) → c α β ≡ ∞ → α ≡ β
 infinitely-close-are-equal = seq-coinduction (λ α β → c α β ≡ ∞) b
  where
   b : (α β : 𝓢) → c α β ≡ ∞
                 → (head α ≡ head β) × (c (tail α) (tail β) ≡ ∞)
   b α β q = d , e
    where
     l : head α ≢ head β → c α β ≡ Zero
     l = codistance-eq₀ α β
     d : head α ≡ head β
     d = Cases (δ (head α) (head β))
          (λ (p : head α ≡ head β)
            → p)
          (λ (n : head α ≢ head β)
            → 𝟘-elim (Zero-not-Succ (Zero    ≡⟨ (l n)⁻¹ ⟩
                                     c α β   ≡⟨ q ⟩
                                     ∞       ≡⟨ (Succ-∞-is-∞ (fe 𝓤₀ 𝓤₀))⁻¹ ⟩
                                     Succ ∞  ∎)))
     e : c (tail α) (tail β) ≡ ∞
     e = ap Pred (Succ (c (tail α) (tail β)) ≡⟨ (codistance-eq₁ α β d)⁻¹ ⟩
                  c α β                      ≡⟨ q ⟩
                  ∞                          ∎)

\end{code}

Symmetric property:

\begin{code}

 symmetric-property : (α β : 𝓢) → c α β ≡ c β α
 symmetric-property α β = ℕ∞-coinduction R b (c α β) (c β α) γ
  where
   R : ℕ∞ → ℕ∞ → 𝓤 ̇
   R u v = Σ \α → Σ \β → (u ≡ c α β) × (v ≡ c β α)
   b : ℕ∞-bisimulation R
   b .(c α β) .(c β α) (α , β , refl , refl)
     = s , t (δ (head α) (head β))
    where
     s : positivity (c α β) ≡ positivity (c β α)
     s = Cases (δ (head α) (head β)) sₕ sₜ
      where
       sₕ : head α ≡ head β → positivity (c α β) ≡ positivity (c β α)
       sₕ h≡ = successors-same-positivity
               (codistance-eq₁ α β h≡) (codistance-eq₁ β α (h≡ ⁻¹))
       sₜ : head α ≢ head β → positivity (c α β) ≡ positivity (c β α)
       sₜ h≢ = equal-same-positivity (c α β) (c β α)
               (codistance-eq₀ α β h≢
               ∙ codistance-eq₀ β α (λ h≡ → h≢ (h≡ ⁻¹)) ⁻¹)
     t : (head α ≡ head β) + (head α ≢ head β)
       → R (Pred (c α β)) (Pred (c β α))
     t (inl h≡) = tail α , tail β
                , ap Pred (codistance-eq₁ α β h≡ ∙ Pred-Succ)
                , ap Pred (codistance-eq₁ β α (h≡ ⁻¹) ∙ Pred-Succ)
     t (inr h≢) = α , β
                , Pred-Zero-is-Zero' (c α β) (codistance-eq₀ α β h≢)
                , Pred-Zero-is-Zero' (c β α) (codistance-eq₀ β α (λ h≡ → h≢ (h≡ ⁻¹)))
   γ : R (c α β) (c β α)
   γ = α , β , refl , refl

\end{code}

Ultra property:

\begin{code}

 codistance-eq₁' : (α β : 𝓢) → is-positive (c α β)
                 → head α ≡ head β
 codistance-eq₁' α β p = Cases (δ (head α) (head β)) id
   (λ h≢ → 𝟘-elim (zero-is-not-one
    (is-Zero-Zero ⁻¹ ∙ ap (λ - → incl - 0) (codistance-eq₀ α β h≢ ⁻¹) ∙ p)))

 open import NaturalsOrder

 codistance-conceptually₁ : (α β : 𝓢) (n : ℕ)
                          → ((k : ℕ) → k ≤ n → α k ≡ β k)
                          → n ⊏ c α β
 codistance-conceptually₁ α β zero α≈ₙβ
  = transport (0 ⊏_) (codistance-eq₁ α β (α≈ₙβ 0 *) ⁻¹)
    (is-positive-Succ (c (tail α) (tail β)))
 codistance-conceptually₁ α β (succ n) α≈ₙβ
  = transport (succ n ⊏_) (codistance-eq₁ α β (α≈ₙβ 0 *) ⁻¹)
    (codistance-conceptually₁ (tail α) (tail β) n (λ m → α≈ₙβ (succ m)))
 
 codistance-conceptually₂ : (α β : 𝓢) (n : ℕ)
                          → n ⊏ c α β
                          → ((k : ℕ) → k ≤ n → α k ≡ β k)
 codistance-conceptually₂ α β n ⊏ₙcαβ zero k≤n
  = codistance-eq₁' α β (⊏-trans'' (c α β) n 0 k≤n ⊏ₙcαβ)
 codistance-conceptually₂ α β n ⊏ₙcαβ (succ k) k≤n
  = codistance-conceptually₂ (tail α) (tail β) k (transport (succ k ⊏_)
      (codistance-eq₁ α β (codistance-eq₁' α β (⊏-trans'' (c α β) n 0 * ⊏ₙcαβ)))
      (⊏-trans'' (c α β) n (succ k) k≤n ⊏ₙcαβ))
    k (≤-refl k)

 min-split : (α β : ℕ∞) (n : ℕ) → n ⊏ uncurry min' (α , β) → n ⊏ α × n ⊏ β
 pr₁ (min-split α β n min≼) = different-from-₀-equal-₁
                              (λ x → zero-is-not-one (Lemma[min𝟚ab≡₀] (inl x) ⁻¹ ∙ min≼))
 pr₂ (min-split α β n min≼) = different-from-₀-equal-₁
                              (λ x → zero-is-not-one (Lemma[min𝟚ab≡₀] (inr x) ⁻¹ ∙ min≼))

 ultra-property : (α β ε : 𝓢) → min (c α β , c β ε) ≼ c α ε
 ultra-property α β ε n min≼  = codistance-conceptually₁ α ε n
                     (λ k k≤n → codistance-conceptually₂ α β n (pr₁ min-split') k k≤n
                              ∙ codistance-conceptually₂ β ε n (pr₂ min-split') k k≤n)
  where
   min-split' : n ⊏ c α β × n ⊏ c β ε
   min-split' = min-split (c α β) (c β ε) n
                (transport (λ - → n ⊏ - (c α β , c β ε)) min≡ min≼)

\end{code}

We now consider the following two special cases for the Baire and
Cantor types:

\begin{code}

open sequences ℕ ℕ-is-discrete
 renaming
  (codistance                 to Baire-codistance ;
   infinitely-close-to-itself to Baire-infinitely-close-to-itself ;
   infinitely-close-are-equal to Baire-infinitely-close-are-equal ;
   symmetric-property         to Baire-symmetric-property ;
   ultra-property             to Baire-ultra-property )

open sequences 𝟚 𝟚-is-discrete
 renaming
  (codistance                 to Cantor-codistance ;
   infinitely-close-to-itself to Cantor-infinitely-close-to-itself ;
   infinitely-close-are-equal to Cantor-infinitely-close-are-equal ;
   symmetric-property         to Cantor-symmetric-property ;
   ultra-property             to Cantor-ultra-property )

\end{code}

And now we reduce the codistance of the Cantor type to the generic
convergent sequence:

\begin{code}

ℕ∞-codistance : ℕ∞ → ℕ∞ → ℕ∞
ℕ∞-codistance u v = Cantor-codistance (incl u) (incl v)

ℕ∞-infinitely-close-to-itself : (u : ℕ∞) → ℕ∞-codistance u u ≡ ∞
ℕ∞-infinitely-close-to-itself u = Cantor-infinitely-close-to-itself (incl u)

ℕ∞-equal-are-infinitely-close : (u v : ℕ∞) → u ≡ v → ℕ∞-codistance u v ≡ ∞
ℕ∞-equal-are-infinitely-close u .u refl = ℕ∞-infinitely-close-to-itself u

ℕ∞-infinitely-close-are-equal : (u v : ℕ∞) → ℕ∞-codistance u v ≡ ∞ → u ≡ v
ℕ∞-infinitely-close-are-equal u v r = incl-lc (fe 𝓤₀ 𝓤₀) γ
 where
  γ : incl u ≡ incl v
  γ = Cantor-infinitely-close-are-equal (incl u) (incl v) r

ℕ∞-symmetric-property : (u v : ℕ∞) → ℕ∞-codistance u v ≡ ℕ∞-codistance v u
ℕ∞-symmetric-property u v = Cantor-symmetric-property (incl u) (incl v)

ℕ∞-ultra-property : (u v w : ℕ∞) → min (ℕ∞-codistance u v , ℕ∞-codistance v w)
                                 ≼ ℕ∞-codistance u w
ℕ∞-ultra-property u v w = Cantor-ultra-property (incl u) (incl v) (incl w)

\end{code}

Axioms for codistance:

\begin{code}

is-codistance
 indistinguishable-are-equal
 self-indistinguishable
 is-symmetric
 is-ultra
  : {X : 𝓤 ̇ } → (X → X → ℕ∞) → 𝓤 ̇

indistinguishable-are-equal c = ∀ x y → c x y ≡ ∞ → x ≡ y
self-indistinguishable      c = ∀ x → c x x ≡ ∞
is-symmetric                c = ∀ x y → c x y ≡ c y x
is-ultra                    c = ∀ x y z → min (c x y , c y z) ≼ c x z
is-codistance               c = indistinguishable-are-equal c
                              × self-indistinguishable c
                              × is-symmetric c
                              × is-ultra c

\end{code}

The above codistances are indeed codistances according
to this definition

\begin{code}

open sequences

ℕ→D-has-codistance : (X : 𝓤 ̇ ) (δ : is-discrete X)
                   → is-codistance (codistance X δ)
ℕ→D-has-codistance X δ
 = infinitely-close-are-equal X δ
 , infinitely-close-to-itself X δ
 , symmetric-property X δ
 , ultra-property X δ

ℕ→ℕ-has-codistance : is-codistance (Baire-codistance)
ℕ→ℕ-has-codistance = ℕ→D-has-codistance ℕ ℕ-is-discrete

ℕ→𝟚-has-codistance : is-codistance (Cantor-codistance)
ℕ→𝟚-has-codistance = ℕ→D-has-codistance 𝟚 𝟚-is-discrete

ℕ→ℕ∞-has-codistance : is-codistance (ℕ∞-codistance)
ℕ→ℕ∞-has-codistance = ℕ∞-infinitely-close-are-equal
                    , ℕ∞-infinitely-close-to-itself
                    , ℕ∞-symmetric-property
                    , ℕ∞-ultra-property
