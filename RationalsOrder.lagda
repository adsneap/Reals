Andrew Sneap - 11th November 2021

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆) --TypeTopology

open import NaturalNumbers-Properties
open import MoreNaturalProperties
open import NaturalsAddition renaming (_+_ to _ℕ+_)
open import Plus-Properties
open import UF-Base hiding (_≈_) --TypeTopology
open import UF-FunExt --TypeTopology
open import UF-Subsingletons --TypeTopology

open import IntegersAbs
open import IntegersAddition renaming (_+_ to _ℤ+_)
open import IntegersB
open import IntegersMultiplication renaming (_*_ to _ℤ*_)
open import IntegersOrder renaming (_<_ to _ℤ<_ ; _≤_ to _ℤ≤_)
open import NaturalsMultiplication renaming (_*_ to _ℕ*_)
open import ncRationals
open import ncRationalsOperations renaming (_+_ to _ℚₙ+_ ; _*_ to _ℚₙ*_) hiding (-_)
open import ncRationalsOrder 
open import Rationals
open import RationalsAddition
open import RationalsMultiplication
open import RationalsNegation

_≤_ : (p q : ℚ) → 𝓤₀ ̇
(p , _) ≤ (q , _) = p ℚₙ≤ q

ℚ≤-is-prop : (p q : ℚ) → is-prop (p ≤ q)
ℚ≤-is-prop (p , _) (q , _) = ℚₙ≤-is-prop p q

_<_ : (p q : ℚ) → 𝓤₀ ̇
(p , _) < (q , _) = p ℚₙ< q

ℚ<-is-prop : (p q : ℚ) → is-prop (p < q)
ℚ<-is-prop (p , _) (q , _) = ℚₙ<-is-prop p q

ℚ<-trans : (p q r : ℚ) → p < q → q < r → p < r
ℚ<-trans (p , _) (q , _) (r , _) α β = ℚₙ<-trans p q r α β

ℚ≤-refl : (q : ℚ) → q ≤ q
ℚ≤-refl q = 0 , by-definition

ℚ<-coarser-than-≤ : (p q : ℚ) → p < q → p ≤ q
ℚ<-coarser-than-≤ (p , _) (q , _) l = ℚₙ<-coarser-than-≤ p q l

toℚ-< : (p q : ℚₙ) → p ℚₙ< q → toℚ p < toℚ q
toℚ-< (x , a) (y , b) l = ordering-right-cancellable (x' ℤ* pos (succ b')) (y' ℤ* (pos (succ a'))) (pos (succ h ℕ* succ h')) IV V
 where
  I : Σ ((x' , a') , p) ꞉ ℚ , (Σ h ꞉ ℕ , (x ≡ (pos (succ h)) ℤ* x') × (succ a ≡ (succ h) ℕ* succ a'))
  I = toℚlemma (x , a)

  II : Σ ((y' , b') , p) ꞉ ℚ , (Σ h' ꞉ ℕ , (y ≡ (pos (succ h')) ℤ* y') × (succ b ≡ (succ h') ℕ* succ b'))
  II = toℚlemma (y , b)

  x' y' : ℤ
  x' = pr₁ (pr₁ (pr₁ I))
  y' = pr₁ (pr₁ (pr₁ II))

  a' b' : ℕ
  a' = pr₂ (pr₁ (pr₁ I))
  b' = pr₂ (pr₁ (pr₁ II))

  h h' : ℕ
  h = pr₁ (pr₂ I)
  h' = pr₁ (pr₂ II)

  α : x ≡ (pos (succ h)) ℤ* x'
  α = pr₁ (pr₂ (pr₂ I))

  β : succ a ≡ (succ h) ℕ* succ a'
  β = pr₂ (pr₂ (pr₂ I))

  α' : y ≡ (pos (succ h')) ℤ* y'
  α' = pr₁ (pr₂ (pr₂ II))

  β' : succ b ≡ (succ h') ℕ* succ b'
  β' = pr₂ (pr₂ (pr₂ II))

  III : greater-than-zero (pos (succ h) ℤ* pos (succ h'))
  III = greater-than-zero-mult-trans (pos (succ h)) (pos (succ h')) ⋆ ⋆

  IV : greater-than-zero (pos (succ h ℕ* succ h'))
  IV = transport (λ z → greater-than-zero z) (pos-multiplication-equiv-to-ℕ (succ h) (succ h')) III

  V : ((x' ℤ* pos (succ b')) ℤ* pos (succ h ℕ* succ h')) ℤ< ((y' ℤ* pos (succ a')) ℤ* pos (succ h ℕ* succ h'))
  V = transport₂ (λ z z' → z ℤ< z') VI VII l
   where
    VI : x ℤ* pos (succ b) ≡ x' ℤ* pos (succ b') ℤ* pos (succ h ℕ* succ h')
    VI = x ℤ* pos (succ b)                                         ≡⟨ ap₂ (λ z z' → z ℤ* z') α (ap pos β') ⟩
          pos (succ h) ℤ* x' ℤ* pos (succ h' ℕ* succ b')            ≡⟨ ap (pos (succ h) ℤ* x' ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h') (succ b') ⁻¹) ⟩
          pos (succ h) ℤ* x' ℤ* (pos (succ h') ℤ* (pos (succ b')))  ≡⟨ ap₂ (λ z z' → z ℤ* z') (ℤ*-comm (pos (succ h)) x') (ℤ*-comm (pos (succ h')) (pos (succ b'))) ⟩
          x' ℤ* pos (succ h) ℤ* (pos (succ b') ℤ* pos (succ h'))    ≡⟨ ℤ*-assoc x' (pos (succ h)) (pos (succ b') ℤ* pos (succ h')) ⟩
          x' ℤ* (pos (succ h) ℤ* (pos (succ b') ℤ* pos (succ h')))  ≡⟨ ap (x' ℤ*_) (ℤ-mult-rearrangement''' (pos (succ h)) (pos (succ b')) (pos (succ h'))) ⟩
          x' ℤ* (pos (succ b') ℤ* (pos (succ h) ℤ* pos (succ h')))  ≡⟨ ℤ*-assoc x' (pos (succ b')) (pos (succ h) ℤ* pos (succ h')) ⁻¹ ⟩
          x' ℤ* pos (succ b') ℤ* (pos (succ h) ℤ* pos (succ h'))    ≡⟨ ap ( x' ℤ* pos (succ b') ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h) (succ h')) ⟩
          x' ℤ* pos (succ b') ℤ* pos (succ h ℕ* succ h') ∎

    VII : y ℤ* pos (succ a) ≡ y' ℤ* pos (succ a') ℤ* pos (succ h ℕ* succ h')
    VII = y ℤ* pos (succ a)                                         ≡⟨ ap₂ (λ z z' → z ℤ* z') α' (ap pos β) ⟩
           pos (succ h') ℤ* y' ℤ* pos (succ h ℕ* succ a')            ≡⟨ ap (pos (succ h') ℤ* y' ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h) (succ a') ⁻¹) ⟩
           pos (succ h') ℤ* y' ℤ* (pos (succ h) ℤ* pos (succ a'))    ≡⟨ ap₂ (λ z z' → z ℤ* z') (ℤ*-comm (pos (succ h')) y') (ℤ*-comm (pos (succ h)) (pos (succ a'))) ⟩
           y' ℤ* pos (succ h') ℤ* (pos (succ a') ℤ* pos (succ h))    ≡⟨ ℤ*-assoc y' (pos (succ h')) (pos (succ a') ℤ* pos (succ h)) ⟩
           y' ℤ* (pos (succ h') ℤ* (pos (succ a') ℤ* pos (succ h)))  ≡⟨ ap (y' ℤ*_) (ℤ-mult-rearrangement''' (pos (succ h')) (pos (succ a')) (pos (succ h))) ⟩
           y' ℤ* (pos (succ a') ℤ* (pos (succ h') ℤ* pos (succ h)))  ≡⟨ ℤ*-assoc y' (pos (succ a')) (pos (succ h') ℤ* pos (succ h)) ⁻¹ ⟩
           y' ℤ* pos (succ a') ℤ* (pos (succ h') ℤ* pos (succ h))    ≡⟨ ap (y' ℤ* pos (succ a') ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h') (succ h)) ⟩
           y' ℤ* pos (succ a') ℤ* pos (succ h' ℕ* succ h)            ≡⟨ ap (λ z → y' ℤ* pos (succ a') ℤ* pos z) (mult-commutativity (succ h') (succ h)) ⟩
           y' ℤ* pos (succ a') ℤ* pos (succ h ℕ* succ h') ∎

toℚ-≤ : (p q : ℚₙ) → p ℚₙ≤ q → toℚ p ≤ toℚ q
toℚ-≤ (x , a) (y , b) l = ℤ≤-ordering-right-cancellable (x' ℤ* pos (succ b')) (y' ℤ* (pos (succ a'))) (pos (succ h ℕ* succ h')) III IV
 where
  I : Σ ((x' , a') , p) ꞉ ℚ , (Σ h ꞉ ℕ , (x ≡ (pos (succ h)) ℤ* x') × (succ a ≡ (succ h) ℕ* succ a'))
  I = toℚlemma (x , a)

  II : Σ ((y' , b') , p) ꞉ ℚ , (Σ h' ꞉ ℕ , (y ≡ (pos (succ h')) ℤ* y') × (succ b ≡ (succ h') ℕ* succ b'))
  II = toℚlemma (y , b)

  x' y' : ℤ
  x' = pr₁ (pr₁ (pr₁ I))
  y' = pr₁ (pr₁ (pr₁ II))

  a' b' : ℕ
  a' = pr₂ (pr₁ (pr₁ I))
  b' = pr₂ (pr₁ (pr₁ II))

  h h' : ℕ
  h = pr₁ (pr₂ I)
  h' = pr₁ (pr₂ II)

  α : x ≡ (pos (succ h)) ℤ* x'
  α = pr₁ (pr₂ (pr₂ I))

  β : succ a ≡ (succ h) ℕ* succ a'
  β = pr₂ (pr₂ (pr₂ I))

  α' : y ≡ (pos (succ h')) ℤ* y'
  α' = pr₁ (pr₂ (pr₂ II))

  β' : succ b ≡ (succ h') ℕ* succ b'
  β' = pr₂ (pr₂ (pr₂ II))

  III : greater-than-zero (pos (succ h ℕ* succ h'))
  III = transport (λ - → greater-than-zero -) (pos-multiplication-equiv-to-ℕ (succ h) (succ h')) (greater-than-zero-mult-trans (pos (succ h)) (pos (succ h')) ⋆ ⋆)

  IV : (x' ℤ* pos (succ b') ℤ* pos (succ h ℕ* succ h')) ℤ≤ (y' ℤ* pos (succ a') ℤ* pos (succ h ℕ* succ h'))
  IV = transport₂ (λ z z' → z ℤ≤ z') VI VII l
   where
    VI : x ℤ* pos (succ b) ≡ x' ℤ* pos (succ b') ℤ* pos (succ h ℕ* succ h')
    VI = x ℤ* pos (succ b)                                         ≡⟨ ap₂ (λ z z' → z ℤ* z') α (ap pos β') ⟩
          pos (succ h) ℤ* x' ℤ* pos (succ h' ℕ* succ b')            ≡⟨ ap (pos (succ h) ℤ* x' ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h') (succ b') ⁻¹) ⟩
          pos (succ h) ℤ* x' ℤ* (pos (succ h') ℤ* (pos (succ b')))  ≡⟨ ap₂ (λ z z' → z ℤ* z') (ℤ*-comm (pos (succ h)) x') (ℤ*-comm (pos (succ h')) (pos (succ b'))) ⟩
          x' ℤ* pos (succ h) ℤ* (pos (succ b') ℤ* pos (succ h'))    ≡⟨ ℤ*-assoc x' (pos (succ h)) (pos (succ b') ℤ* pos (succ h')) ⟩
          x' ℤ* (pos (succ h) ℤ* (pos (succ b') ℤ* pos (succ h')))  ≡⟨ ap (x' ℤ*_) (ℤ-mult-rearrangement''' (pos (succ h)) (pos (succ b')) (pos (succ h'))) ⟩
          x' ℤ* (pos (succ b') ℤ* (pos (succ h) ℤ* pos (succ h')))  ≡⟨ ℤ*-assoc x' (pos (succ b')) (pos (succ h) ℤ* pos (succ h')) ⁻¹ ⟩
          x' ℤ* pos (succ b') ℤ* (pos (succ h) ℤ* pos (succ h'))    ≡⟨ ap ( x' ℤ* pos (succ b') ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h) (succ h')) ⟩
          x' ℤ* pos (succ b') ℤ* pos (succ h ℕ* succ h') ∎

    VII : y ℤ* pos (succ a) ≡ y' ℤ* pos (succ a') ℤ* pos (succ h ℕ* succ h')
    VII = y ℤ* pos (succ a)                                         ≡⟨ ap₂ (λ z z' → z ℤ* z') α' (ap pos β) ⟩
           pos (succ h') ℤ* y' ℤ* pos (succ h ℕ* succ a')            ≡⟨ ap (pos (succ h') ℤ* y' ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h) (succ a') ⁻¹) ⟩
           pos (succ h') ℤ* y' ℤ* (pos (succ h) ℤ* pos (succ a'))    ≡⟨ ap₂ (λ z z' → z ℤ* z') (ℤ*-comm (pos (succ h')) y') (ℤ*-comm (pos (succ h)) (pos (succ a'))) ⟩
           y' ℤ* pos (succ h') ℤ* (pos (succ a') ℤ* pos (succ h))    ≡⟨ ℤ*-assoc y' (pos (succ h')) (pos (succ a') ℤ* pos (succ h)) ⟩
           y' ℤ* (pos (succ h') ℤ* (pos (succ a') ℤ* pos (succ h)))  ≡⟨ ap (y' ℤ*_) (ℤ-mult-rearrangement''' (pos (succ h')) (pos (succ a')) (pos (succ h))) ⟩
           y' ℤ* (pos (succ a') ℤ* (pos (succ h') ℤ* pos (succ h)))  ≡⟨ ℤ*-assoc y' (pos (succ a')) (pos (succ h') ℤ* pos (succ h)) ⁻¹ ⟩
           y' ℤ* pos (succ a') ℤ* (pos (succ h') ℤ* pos (succ h))    ≡⟨ ap (y' ℤ* pos (succ a') ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h') (succ h)) ⟩
           y' ℤ* pos (succ a') ℤ* pos (succ h' ℕ* succ h)            ≡⟨ ap (λ z → y' ℤ* pos (succ a') ℤ* pos z) (mult-commutativity (succ h') (succ h)) ⟩
           y' ℤ* pos (succ a') ℤ* pos (succ h ℕ* succ h') ∎


ℚ-no-max-element : (p : ℚ) → Σ q ꞉ ℚ , (p < q)
ℚ-no-max-element ((x , a) , α) = q , III
 where
  q : ℚ 
  q = toℚ ((succℤ x) , a)

  x' : ℤ
  x' = pr₁ (pr₁ q)
  a' : ℕ
  a' = pr₂ (pr₁ q)

  I : succℤ x ℤ* pos (succ a') ≡ x' ℤ* pos (succ a)
  I = ≈-toℚ ((succℤ x) , a)

  II : (x ℤ* pos (succ a')) ℤ< (succℤ x ℤ* pos (succ a'))
  II = positive-multiplication-preserves-order x (succℤ x) (pos (succ a')) ⋆ (<-incrℤ x)

  III : x ℤ* pos (succ a') ℤ< (x' ℤ* pos (succ a))
  III = transport (x ℤ* pos (succ a') ℤ<_) I II

ℚ-no-least-element : (q : ℚ) → Σ p ꞉ ℚ , p < q
ℚ-no-least-element ((x , a) , α) = p , III
 where
  p : ℚ
  p = toℚ ((predℤ x) , a)

  x' : ℤ
  x' = pr₁ (pr₁ p)
  a' : ℕ
  a' = pr₂ (pr₁ p)

  I : predℤ x ℤ* pos (succ a') ≡ x' ℤ* pos (succ a)
  I = ≈-toℚ ((predℤ x) , a)

  II : (predℤ x ℤ* pos (succ a')) ℤ< (x ℤ* pos (succ a'))
  II = positive-multiplication-preserves-order (predℤ x) x (pos (succ a')) ⋆ (<-predℤ x)

  III : x' ℤ* pos (succ a) ℤ< (x ℤ* pos (succ a'))
  III = transport (_ℤ< x ℤ* pos (succ a')) I II

ℚ-trichotomous-lemma : Fun-Ext → ((p , α) (q , β) : ℚ) → p ≈ q → p , α ≡ q , β
ℚ-trichotomous-lemma fe (p , α) (q , β) e = to-subtype-≡ (λ - → is-in-lowest-terms-is-prop fe -) (equiv-with-lowest-terms-is-equal p q e α β)

ℚ-trichotomous : Fun-Ext → (p q : ℚ) → (p < q) ∔ (p ≡ q) ∔ (q < p)
ℚ-trichotomous fe ((x , a) , α) ((y , b) , β) = f (ℤ-trichotomous (x ℤ* pos (succ b)) (y ℤ* pos (succ a)))
 where
  f : (x ℤ* pos (succ b)) ℤ< (y ℤ* pos (succ a))
     ∔ (x ℤ* pos (succ b) ≡ y ℤ* pos (succ a))
     ∔ (y ℤ* pos (succ a)) ℤ< (x ℤ* pos (succ b))
    →  ((x , a) , α) < ((y , b) , β)
     ∔ ((x , a) , α ≡ (y , b) , β)
     ∔ ((y , b) , β) < ((x , a) , α)
  f (inl z)       = inl z
  f (inr (inl z)) = inr (inl (ℚ-trichotomous-lemma fe ((x , a) , α) ((y , b) , β) z))
  f (inr (inr z)) = inr (inr z)

ℚ-dichotomous : (p q : ℚ) → p ≤ q ∔ q ≤ p
ℚ-dichotomous ((x , a) , α) ((y , b) , β) = ℤ-dichotomous (x ℤ* pos (succ b)) (y ℤ* pos (succ a))

located-property : Fun-Ext → (p q x : ℚ) → p < q → (p < x) ∔ (x < q) 
located-property fe p q x l = f (ℚ-trichotomous fe x q)
 where
  f : (x < q) ∔ (x ≡ q) ∔ (q < x) → (p < x) ∔ (x < q) 
  f (inl z)       = inr z
  f (inr (inl z)) = inl (transport (p <_) (z ⁻¹) l)
  f (inr (inr z)) = inl (ℚ<-trans p q x l z)

half-ℚₙ : ℚₙ → ℚₙ
half-ℚₙ (x , a) = x , (succ (2 ℕ* a))

rounded-lemma₀ : (a : ℕ) → succ (2 ℕ* pred (succ a)) ≡ pred (2 ℕ* (succ a))
rounded-lemma₀ zero = refl
rounded-lemma₀ (succ a) = succ (2 ℕ* pred (succ (succ a))) ≡⟨ ap (λ - → succ (2 ℕ* -)) (pred-succ a) ⟩
                   succ (2 ℕ* succ a)                ≡⟨ pred-succ (2 ℕ* succ a) ⁻¹ ⟩
                   pred (succ (succ (2 ℕ* succ a)))  ≡⟨ refl ⟩
                   pred (2 ℕ* succ a ℕ+ 2)           ≡⟨ refl ⟩
                   pred (2 ℕ* (succ a) ℕ+ 2 ℕ* 1)    ≡⟨ ap pred (distributivity-mult-over-nat 2 (succ a) 1 ⁻¹) ⟩
                   pred (2 ℕ+ (2 ℕ* (succ a)))       ≡⟨ refl ⟩
                   pred (2 ℕ* succ (succ a)) ∎

--This proof definitely needs improving
ℚ-dense : (p q : ℚ) → p < q → Σ x ꞉ ℚ , (p < x) × (x < q)
ℚ-dense ((x , a) , α) ((y , b) , β) l = midpoint , firstly , secondly
 where
  midpoint : ℚ
  midpoint = toℚ (half-ℚₙ ((x , a) ℚₙ+ (y , b)))

  z : ℤ
  z = pr₁ (pr₁ midpoint)
  c : ℕ
  c = pr₂ (pr₁ midpoint)

  z' : ℤ
  z' = pr₁ (half-ℚₙ ((x , a) ℚₙ+ (y , b)))

  z'' : z' ≡ x ℤ* pos (succ b) ℤ+ y ℤ* pos (succ a)
  z'' = refl

  c' : ℕ
  c' = pr₂ (half-ℚₙ ((x , a) ℚₙ+ (y , b)))

  c'' : c' ≡ succ (2 ℕ* pred (succ a ℕ* succ b))
  c'' = refl

  I : (z' , c') ≈ (z , c)
  I = ≈-toℚ (half-ℚₙ ((x , a) ℚₙ+ (y , b)))

  II : z' ℤ* pos (succ c) ≡ z ℤ* pos (succ c')
  II = I

  III : Σ k ꞉ ℕ , succ k ≡ succ a ℕ* succ b
  III = pos-mult-is-succ a b

  k : ℕ
  k = pr₁ III

  a' b' k' c''' : ℤ
  a' = pos (succ a)
  b' = pos (succ b)
  k' = pos (succ k)
  c''' = pos (succ c')
  
  IV : (x : ℤ) →  x ℤ* pos (succ (succ (2 ℕ* pred (succ a ℕ* succ b)))) ≡ x ℤ* a' ℤ* b' ℤ+ x ℤ* (a') ℤ* b'
  IV x = x ℤ* pos (succ (succ (2 ℕ* pred (succ a ℕ* succ b))))    ≡⟨ ap (λ - → x ℤ* pos (succ (succ (2 ℕ* pred -)))) ((pr₂ III) ⁻¹) ⟩
       x ℤ* pos (succ (succ (2 ℕ* pred (succ k))))                ≡⟨ ap (λ - → x ℤ* pos (succ -)) (rounded-lemma₀ k) ⟩
       x ℤ* pos (succ (pred (2 ℕ* succ k)))                       ≡⟨ ap (λ - → x ℤ* pos -) (succ-pred' (2 ℕ* succ k) λ w → ℕ-positive-multiplication-not-zero 1 k w) ⟩
       x ℤ* pos (2 ℕ* succ k)                                     ≡⟨ ap (λ - → x ℤ* pos -) (mult-commutativity 2 (succ k)) ⟩
       x ℤ* pos (succ k ℕ+ succ k)                                ≡⟨ ap (λ - → x ℤ* -) (pos-addition-equiv-to-ℕ (succ k) (succ k)  ⁻¹) ⟩
       x ℤ* (k' ℤ+ k')                                            ≡⟨ distributivity-mult-over-ℤ' (k') (k') x ⟩
       x ℤ* k' ℤ+ x ℤ* k'                                         ≡⟨ ap (λ - → x ℤ* pos - ℤ+ x ℤ* pos -) (pr₂ III) ⟩
       x ℤ* pos (succ a ℕ* succ b) ℤ+ x ℤ* pos (succ a ℕ* succ b) ≡⟨ ap (λ - → (x ℤ* -) ℤ+ (x ℤ* -)) (pos-multiplication-equiv-to-ℕ (succ a) (succ b) ⁻¹) ⟩
       x ℤ* (a' ℤ* b') ℤ+ x ℤ* (a' ℤ* b')                          ≡⟨ ap (λ - → - ℤ+ -) (ℤ*-assoc x a' b' ⁻¹) ⟩
       x ℤ* a' ℤ* b' ℤ+ x ℤ* a' ℤ* b' ∎

  V : (x ℤ* b' ℤ+ y ℤ* a') ℤ* a' ≡ x ℤ* a' ℤ* b' ℤ+ y ℤ* (a') ℤ* a'
  V = (x ℤ* b' ℤ+ y ℤ* a') ℤ* a' ≡⟨ distributivity-mult-over-ℤ (x ℤ* b') ( y ℤ* a') (a') ⟩
         x ℤ* b' ℤ* a' ℤ+ y ℤ* a' ℤ* a' ≡⟨ ap (λ - → - ℤ+ y ℤ* a' ℤ* a') (ℤ-mult-rearrangement x (b') (a'))  ⟩
         x ℤ* a' ℤ* b' ℤ+ y ℤ* a' ℤ* a' ∎

  VI : (x ℤ* a' ℤ* b' ℤ+ x ℤ* a' ℤ* b') ℤ< (x ℤ* a' ℤ* b' ℤ+ y ℤ* a' ℤ* a')
  VI = ℤ<-adding'' (x ℤ* a' ℤ* b') (y ℤ* a' ℤ* a') (x ℤ* a' ℤ* b') ii
   where
    i : (x ℤ* b' ℤ* a') ℤ< (y ℤ* a' ℤ* a')
    i = positive-multiplication-preserves-order (x ℤ* b') (y ℤ* a') (a') ⋆ l

    ii : (x ℤ* a' ℤ* b') ℤ< (y ℤ* a' ℤ* a')
    ii = transport (_ℤ< y ℤ* a' ℤ* a') (ℤ-mult-rearrangement x (b') (a')) i

  VII : (x ℤ* pos (succ (succ (2 ℕ* pred (succ a ℕ* succ b))))) ℤ< ((x ℤ* b' ℤ+ y ℤ* a') ℤ* a')
  VII = transport₂ _ℤ<_ (IV x ⁻¹) (V ⁻¹) VI

  VIII : x ℤ* c''' ℤ< z' ℤ* a'
  VIII = VII

  IX : (x ℤ* c''' ℤ* pos (succ c)) ℤ< (z' ℤ* a' ℤ* pos (succ c)) 
  IX = positive-multiplication-preserves-order (x ℤ* c''') (z' ℤ* a') (pos (succ c)) ⋆ VIII

  X : (x ℤ* pos (succ c) ℤ* c''') ℤ< (z ℤ* a' ℤ* c''')
  X = transport₂ _ℤ<_ i ii IX
   where
    i : x ℤ* c''' ℤ* pos (succ c) ≡ x ℤ* pos (succ c) ℤ* c'''
    i = ℤ-mult-rearrangement x (c''') (pos (succ c)) 

    ii : z' ℤ* a' ℤ* pos (succ c) ≡ z ℤ* a' ℤ* c'''
    ii = z' ℤ* a' ℤ* pos (succ c) ≡⟨ ℤ-mult-rearrangement z' (a') (pos (succ c)) ⟩
         z' ℤ* pos (succ c) ℤ* a' ≡⟨ ap (_ℤ* a') II ⟩
         z ℤ* c''' ℤ* a' ≡⟨ ℤ-mult-rearrangement z (c''') (a') ⟩
         z ℤ* a' ℤ* c''' ∎

  firstly : (x ℤ* pos (succ c)) ℤ< (z ℤ* a')
  firstly = ordering-right-cancellable (x ℤ* pos (succ c)) (z ℤ* a') (c''') ⋆ X

  XI : x ℤ* b' ℤ* b' ℤ+ y ℤ* a' ℤ* b' ≡ (x ℤ* (b') ℤ+ y ℤ* a') ℤ* b'
  XI = x ℤ* b' ℤ* b' ℤ+ y ℤ* a' ℤ* b' ≡⟨ distributivity-mult-over-ℤ (x ℤ* b') ( y ℤ* a') (b') ⁻¹ ⟩
         (x ℤ* b' ℤ+ y ℤ* a') ℤ* b' ∎

  XII : y ℤ* a' ℤ* b' ℤ+ y ℤ* (a') ℤ* b' ≡ y ℤ* pos (succ (succ (2 ℕ* pred (succ a ℕ* (succ b)))))
  XII = IV y ⁻¹

  XIII : x ℤ* b' ℤ* b' ℤ+ y ℤ* a' ℤ* b' ℤ< y ℤ* a' ℤ* b' ℤ+ y ℤ* a' ℤ* b'
  XIII = ℤ<-adding' (x ℤ* b' ℤ* b') (y ℤ* a' ℤ* b') (y ℤ* a' ℤ* b') i
   where
    i : (x ℤ* b' ℤ* b') ℤ< (y ℤ* a' ℤ* b')
    i = positive-multiplication-preserves-order (x ℤ* b') (y ℤ* a') (b') ⋆ l

  XIV : (z' ℤ* b') ℤ< (y ℤ* c''')
  XIV = transport₂ _ℤ<_ XI XII XIII

  XV : (z' ℤ* b' ℤ* pos (succ c)) ℤ< (y ℤ* c''' ℤ* pos (succ c))
  XV = positive-multiplication-preserves-order (z' ℤ* b') (y ℤ* c''') (pos (succ c)) ⋆ XIV

  XVI : (z ℤ* b') ℤ* c''' ℤ< (y ℤ* pos (succ c)) ℤ* c'''
  XVI = transport₂ _ℤ<_ i ii XV
   where
    i : z' ℤ* b' ℤ* pos (succ c) ≡ z ℤ* b' ℤ* c'''
    i = z' ℤ* b' ℤ* pos (succ c) ≡⟨ ℤ-mult-rearrangement z' (b') (pos (succ c)) ⟩
        z' ℤ* pos (succ c) ℤ* b' ≡⟨ ap (_ℤ* b') II ⟩
        z ℤ* c''' ℤ* b' ≡⟨ ℤ-mult-rearrangement z (c''') (b') ⟩
        z ℤ* b' ℤ* c''' ∎

    ii : y ℤ* c''' ℤ* pos (succ c) ≡ y ℤ* pos (succ c) ℤ* c'''
    ii = ℤ-mult-rearrangement y (c''') (pos (succ c))

  secondly : (z ℤ* b') ℤ< (y ℤ* pos (succ c))
  secondly = ordering-right-cancellable (z ℤ* b') (y ℤ* pos (succ c)) (c''') ⋆ XVI

ℚ-zero-less-than-positive : (x y : ℕ) → 0ℚ < toℚ ((pos (succ x)) , y)
ℚ-zero-less-than-positive x y = toℚ-< (pos 0 , 0) (pos (succ x) , y) (x , I)
 where
  I : succℤ (pos 0 ℤ* pos (succ y)) ℤ+ pos x ≡ pos (succ x) ℤ* pos 1
  I = succℤ (pos 0 ℤ* pos (succ y)) ℤ+ pos x ≡⟨ ap (λ α → succℤ α ℤ+ pos x) (ℤ-zero-left-is-zero (pos (succ y))) ⟩
      succℤ (pos 0) ℤ+ pos x                 ≡⟨ ℤ-left-succ (pos 0) (pos x) ⟩
      succℤ (pos 0 ℤ+ pos x)                 ≡⟨ ap succℤ (ℤ+-comm (pos 0) (pos x)) ⟩
      succℤ (pos x)                          ≡⟨ by-definition ⟩
      pos (succ x)                           ≡⟨ by-definition ⟩
      pos (succ x) ℤ* pos 1                  ∎

ℚ<-addition-preserves-order : (p q r : ℚ) → p < q → (p + r) < (q + r)
ℚ<-addition-preserves-order (p , _) (q , _) (r , _) l =
 toℚ-< (p ℚₙ+ r) (q ℚₙ+ r) (ℚₙ<-addition-preserves-order p q r l)

ℚ<-adding : (p q r s : ℚ) → p < q → r < s → p + r < q + s
ℚ<-adding (p , _) (q , _) (r , _) (s , _) l₁ l₂ = toℚ-< (p ℚₙ+ r) (q ℚₙ+ s) I
 where
  I : p ℚₙ+ r ℚₙ< q ℚₙ+ s
  I = ℚₙ<-adding p q r s l₁ l₂

ℚ<-addition-preserves-order' : Fun-Ext → (p q r : ℚ) → p < q → 0ℚ < r → p < q + r
ℚ<-addition-preserves-order' fe p q r l m = transport (_< q + r) (ℚ-zero-right-neutral fe p) (ℚ<-adding p q 0ℚ r l m)

ℚ<-pos-multiplication-preserves-order : (p q : ℚ) → 0ℚ < p → 0ℚ < q → 0ℚ < p * q
ℚ<-pos-multiplication-preserves-order (p , _) (q , _) l₁ l₂ = toℚ-< (pos 0 , 0) (p ℚₙ* q) (ℚₙ-pos-multiplication-preserves-order p q l₁ l₂)

ℚ≤-pos-multiplication-preserves-order : (p q : ℚ) → 0ℚ ≤ p → 0ℚ ≤ q → 0ℚ ≤ (p * q)
ℚ≤-pos-multiplication-preserves-order (p , _) (q , _) l₁ l₂ = toℚ-≤ (pos 0 , 0) (p ℚₙ* q) (ℚₙ≤-pos-multiplication-preserves-order p q l₁ l₂)

ℚ<-addition-preserves-order'' : Fun-Ext → (p q : ℚ) → 0ℚ < q → p < p + q
ℚ<-addition-preserves-order'' fe p q l = transport₂ _<_ (ℚ-zero-left-neutral fe p) (ℚ+-comm q p) (ℚ<-addition-preserves-order 0ℚ q p l)

ℚ<-adding-zero : (p q : ℚ) → 0ℚ < p → 0ℚ < q → 0ℚ < p + q
ℚ<-adding-zero p q l₁ l₂ = ℚ<-adding 0ℚ p 0ℚ q l₁ l₂

ℚ<-not-itself : (p : ℚ) → ¬ (p < p)
ℚ<-not-itself ((x , a) , _) (n , e) = positive-not-zero n (pos-lc (ℤ+-lc (pos (succ n)) (pos 0) (x ℤ* pos (succ a)) I))
 where
  I : x ℤ* pos (succ a) ℤ+ pos (succ n) ≡ x ℤ* pos (succ a) ℤ+ pos 0
  I = x ℤ* pos (succ a) ℤ+ pos (succ n)  ≡⟨ by-definition ⟩
      x ℤ* pos (succ a) ℤ+ succℤ (pos n) ≡⟨ ℤ-right-succ (x ℤ* pos (succ a)) (pos n) ⟩
      succℤ (x ℤ* pos (succ a) ℤ+ pos n) ≡⟨ ℤ-left-succ (x ℤ* pos (succ a)) (pos n) ⁻¹ ⟩
      succℤ (x ℤ* pos (succ a)) ℤ+ pos n ≡⟨ e ⟩
      x ℤ* pos (succ a)                  ≡⟨ by-definition ⟩
      x ℤ* pos (succ a) ℤ+ pos 0 ∎

ℚ≤-split : Fun-Ext → (p q : ℚ) → p ≤ q → (p < q) ∔ (p ≡ q)
ℚ≤-split fe (p , α) (q , β) (0 , e) = inr (to-subtype-≡ (is-in-lowest-terms-is-prop fe) I)
 where
  I : p ≡ q
  I = equiv-with-lowest-terms-is-equal p q e α β
ℚ≤-split fe ((x , a) , _) ((y , b) , _) (succ n , e) = inl (n , (ℤ-left-succ (x ℤ* pos (succ b)) (pos n) ∙ e))

ℚ≤-addition-preserves-order : Fun-Ext → (p q r : ℚ) → p ≤ q → (p + r) ≤ (q + r)
ℚ≤-addition-preserves-order fe p q r l = I (ℚ≤-split fe p q l)
 where
  I : (p < q) ∔ (p ≡ q) → (p + r) ≤ (q + r)
  I (inl l) = ℚ<-coarser-than-≤ (p + r) (q + r) (ℚ<-addition-preserves-order p q r l)
  I (inr e) = transport (p + r ≤_) II (ℚ≤-refl (p + r))
   where
    II : p + r ≡ q + r
    II = ap (_+ r) e

ℚ≤-difference-positive : (fe : Fun-Ext) → (p q : ℚ) → p ≤ q → 0ℚ ≤ q - p
ℚ≤-difference-positive fe p q l = transport (_≤ q - p) (ℚ-inverse-sum-to-zero fe p) I
 where
  I : p - p ≤ q - p
  I = ℚ≤-addition-preserves-order fe p q (- p) l

ℚ≤-pos-multiplication-preserves-order' : Fun-Ext → (p q r : ℚ) → (p ≤ q) → 0ℚ ≤ r → p * r ≤ q * r
ℚ≤-pos-multiplication-preserves-order' fe p q r l₁ l₂ = transport₂ _≤_ III IV II
 where
  I : 0ℚ ≤ ((q - p) * r)
  I = ℚ≤-pos-multiplication-preserves-order (q - p) r (ℚ≤-difference-positive fe p q l₁) l₂
  
  II : (0ℚ + p * r) ≤ ((q - p) * r + p * r)
  II = ℚ≤-addition-preserves-order fe 0ℚ ((q - p) * r) (p * r) I

  III : 0ℚ + p * r ≡ p * r
  III = ℚ-zero-left-neutral fe (p * r)

  IV : ((q - p) * r) + p * r ≡ q * r
  IV = (q - p) * r + p * r         ≡⟨ ap (_+ p * r) (ℚ-distributivity' fe r q (- p)) ⟩
       q * r + (- p) * r + p * r   ≡⟨ ℚ+-assoc fe (q * r) ((- p) * r) (p * r) ⟩
       q * r + ((- p) * r + p * r) ≡⟨ ap (λ z → (q * r) + (z + p * r)) (ℚ-subtraction-dist-over-mult fe p r) ⟩
       q * r + ((- p * r) + p * r) ≡⟨ ap (q * r +_) (ℚ-inverse-sum-to-zero' fe (p * r)) ⟩
       q * r + 0ℚ                  ≡⟨ ℚ-zero-right-neutral fe (q * r) ⟩
       q * r ∎
 
ℚ≤-trans : Fun-Ext → (p q r : ℚ) → p ≤ q → q ≤ r → p ≤ r
ℚ≤-trans fe p q r l₁ l₂ = I (ℚ≤-split fe p q l₁) (ℚ≤-split fe q r l₂)
 where
  I : (p < q) ∔ (p ≡ q) → (q < r) ∔ (q ≡ r) → p ≤ r
  I (inl k) (inl e) = ℚ<-coarser-than-≤ p r (ℚ<-trans p q r k e)
  I (inl k) (inr e) = ℚ<-coarser-than-≤ p r (transport (p <_) e k)
  I (inr k) (inl e) = ℚ<-coarser-than-≤ p r (transport (_< r) (k ⁻¹) e)
  I (inr k) (inr e) = transport (p ≤_) e l₁

ℚ<-≤-trans : Fun-Ext → (p q r : ℚ) → p < q → q ≤ r → p < r
ℚ<-≤-trans fe p q r l₁ l₂ = I (ℚ≤-split fe q r l₂) 
 where
  I : (q < r) ∔ (q ≡ r) → p < r
  I (inl l) = ℚ<-trans p q r l₁ l
  I (inr l) = transport (p <_) l l₁

ℚ≤-<-trans : Fun-Ext → (p q r : ℚ) → p ≤ q → q < r → p < r
ℚ≤-<-trans fe p q r l₁ l₂ = I (ℚ≤-split fe p q l₁)
 where
  I : (p < q) ∔ (p ≡ q) → p < r
  I (inl l) = ℚ<-trans p q r l l₂
  I (inr l) = transport (_< r) (l ⁻¹) l₂

ℚ≤-adding : Fun-Ext → (x y u v : ℚ) → x ≤ y → u ≤ v → (x + u) ≤ (y + v)
ℚ≤-adding fe x y u v l₁ l₂ = ℚ≤-trans fe (x + u) (y + u) (y + v) I III
 where
  I : (x + u) ≤ (y + u)
  I = ℚ≤-addition-preserves-order fe x y u l₁

  II : (u + y) ≤ (v + y)
  II = ℚ≤-addition-preserves-order fe u v y l₂

  III : (y + u) ≤ (y + v)
  III = transport₂ _≤_ (ℚ+-comm u y) (ℚ+-comm v y) II

ℚ≤-swap : Fun-Ext → (x y : ℚ) → x ≤ y → (- y) ≤ (- x)
ℚ≤-swap fe x y l = transport id III II
 where
  I : (x - x) ≤ (y + (- x))
  I = ℚ≤-addition-preserves-order fe x y (- x) l
  
  II : ((x - x) + (- y)) ≤ ((y + (- x)) + (- y))
  II = ℚ≤-addition-preserves-order fe (x - x) (y + (- x)) (- y) I

  III : (((x - x) + (- y)) ≤ ((y + (- x)) + (- y))) ≡ ((- y) ≤ (- x))
  III = ap₂ _≤_ α β
   where
    α : (((x - x) + (- y))) ≡ (- y)
    α = (x - x) + (- y)       ≡⟨ ap (_+ (- y)) (ℚ-inverse-sum-to-zero fe x) ⟩
        0ℚ + (- y)            ≡⟨ ℚ-zero-left-neutral fe (- y) ⟩ 
        (- y)                 ∎
    β : (y - x) + (- y) ≡ (- x)
    β = (y - x) + (- y)       ≡⟨ ap (_+ (- y)) (ℚ+-comm y (- x)) ⟩
        (- x) + y + (- y)     ≡⟨ ℚ+-assoc fe (- x) y (- y) ⟩
        (- x) + (y - y)       ≡⟨ ap ((- x) +_) (ℚ-inverse-sum-to-zero fe y) ⟩
        (- x) + 0ℚ            ≡⟨ ℚ-zero-right-neutral fe (- x) ⟩
        (- x) ∎

ℚ<-swap : Fun-Ext → (x y : ℚ) → x < y → (- y) < (- x)
ℚ<-swap fe x y l = split (ℚ≤-split fe (- y) (- x) I)
 where
  I : (- y) ≤ (- x)
  I = ℚ≤-swap fe x y (ℚ<-coarser-than-≤ x y l)
  split : ((- y) < (- x)) ∔ (- y ≡ - x) → (- y) < (- x)
  split (inl il) = il
  split (inr ir) = 𝟘-elim (ℚ<-not-itself x (transport (x <_) III l))
   where
    II : - (- y) ≡ - (- x)
    II = ap -_ ir
    III : y ≡ x
    III = y ≡⟨ ℚ-minus-minus fe y ⟩
          - (- y) ≡⟨ II ⟩
          - (- x) ≡⟨ ℚ-minus-minus fe x ⁻¹ ⟩
          x ∎
  
ℚ-equal-or-less-than-is-prop : Fun-Ext → (x y : ℚ) → is-prop ((x ≡ y) ∔ (y < x))
ℚ-equal-or-less-than-is-prop fe x y (inl l) (inl r) = ap inl (ℚ-is-set fe l r)
ℚ-equal-or-less-than-is-prop fe x y (inl l) (inr r) = 𝟘-elim (ℚ<-not-itself y ((transport (y <_) l r)))
ℚ-equal-or-less-than-is-prop fe x y (inr l) (inl r) = 𝟘-elim ((ℚ<-not-itself x (transport (_< x) (r ⁻¹) l)))
ℚ-equal-or-less-than-is-prop fe x y (inr l) (inr r) = ap inr (ℚ<-is-prop y x l r)

ℚ-trich-a : (fe : Fun-Ext) → (x y : ℚ) → (l : x < y) → ℚ-trichotomous fe x y ≡ inl l
ℚ-trich-a fe x y l = equality-cases (ℚ-trichotomous fe x y) I II
 where
  I : (l₂ : x < y) → ℚ-trichotomous fe x y ≡ inl l₂ → ℚ-trichotomous fe x y ≡ inl l
  I l₂ e = e ∙ ap inl (ℚ<-is-prop x y l₂ l)
  II : (y₁ : (x ≡ y) ∔ (y < x)) → ℚ-trichotomous fe x y ≡ inr y₁ → ℚ-trichotomous fe x y ≡ inl l
  II (inl e) _ = 𝟘-elim (ℚ<-not-itself y (transport (_< y) e l))
  II (inr lt) _ = 𝟘-elim (ℚ<-not-itself x (ℚ<-trans x y x l lt))

ℚ-trich-b : (fe : Fun-Ext) → (x y : ℚ) → (r : (x ≡ y) ∔ (y < x)) → ℚ-trichotomous fe x y ≡ inr r
ℚ-trich-b fe x y r = equality-cases (ℚ-trichotomous fe x y) I II
 where
  I : (l : x < y) → ℚ-trichotomous fe x y ≡ inl l → ℚ-trichotomous fe x y ≡ inr r
  I l _ = Cases r (λ e → 𝟘-elim (ℚ<-not-itself y (transport (_< y) e l)))
                   λ e → 𝟘-elim (ℚ<-not-itself x (ℚ<-trans x y x l e)) 
  II : (s : (x ≡ y) ∔ (y < x)) → ℚ-trichotomous fe x y ≡ inr s → ℚ-trichotomous fe x y ≡ inr r
  II s e = e ∙ (ap inr III)
   where
    III : s ≡ r
    III = ℚ-equal-or-less-than-is-prop fe x y s r

ℚ-trich-c : (fe : Fun-Ext) → (x : ℚ) → (e : (x ≡ x) ∔ x < x) → ℚ-trichotomous fe x x ≡ inr e
ℚ-trich-c fe x e = equality-cases (ℚ-trichotomous fe x x) I II
 where
  I : (k : x < x) → ℚ-trichotomous fe x x ≡ inl k → ℚ-trichotomous fe x x ≡ inr e
  I k f = 𝟘-elim (ℚ<-not-itself x k)

  II : (k : (x ≡ x) ∔ (x < x)) → ℚ-trichotomous fe x x ≡ inr k → ℚ-trichotomous fe x x ≡ inr e
  II k l = Cases k III
                   (λ - → 𝟘-elim (ℚ<-not-itself x -) )
   where
    III : x ≡ x → ℚ-trichotomous fe x x ≡ inr e
    III z = l ∙ ap inr (ℚ-equal-or-less-than-is-prop fe x x k e)

ℚ<-difference-positive : (fe : Fun-Ext) → (p q : ℚ) → p < q → 0ℚ < q - p
ℚ<-difference-positive fe p q l = transport (_< q - p) (ℚ-inverse-sum-to-zero fe p) I
 where
  I : p - p < q - p
  I = ℚ<-addition-preserves-order p q (- p) l

trisect : Fun-Ext → (x y : ℚ) → x < y → Σ (x' , y') ꞉ ℚ × ℚ , (x < x') × (x' < y') × (y' < y) × (y - x' ≡ 2/3 * (y - x)) × (y' - x ≡ 2/3 * (y - x))
trisect fe x y l = (x + d * 1/3 , x + d * 2/3) , I , II , III , IV , V
 where
  d : ℚ
  d = y - x
  α : 0ℚ < d
  α = ℚ<-difference-positive fe x y l

  β : 0ℚ < 1/3
  β = ℚ-zero-less-than-positive 0 2

  γ : 0ℚ < d * 1/3
  γ = ℚ<-pos-multiplication-preserves-order d 1/3 α β

  ψ : (x + d * 1/3) < (x + d * 1/3 + d * 1/3)
  ψ = ℚ<-addition-preserves-order'' fe (x + d * 1/3) (d * 1/3) γ

  η : d * 2/3 < d
  η = transport₂ _<_ ii iii i
   where
    i : (0ℚ + d * 2/3) < (d * 1/3 + d * 2/3)
    i = ℚ<-addition-preserves-order 0ℚ (d * 1/3) (d * 2/3) γ
    ii : 0ℚ + d * 2/3 ≡ d * 2/3
    ii = ℚ-zero-left-neutral fe (d * 2/3)
    iii : d * 1/3 + d * 2/3 ≡ d
    iii = d * 1/3 + d * 2/3 ≡⟨ ℚ-distributivity fe d 1/3 2/3 ⁻¹ ⟩
          d * (1/3 + 2/3)   ≡⟨ ap (d *_) (1/3+2/3 fe) ⟩
          d * 1ℚ            ≡⟨ ℚ-mult-right-id fe d ⟩
          d                 ∎
 
  I : x < (x + d * 1/3)
  I = ℚ<-addition-preserves-order'' fe x (d * 1/3) γ

  II : (x + d * 1/3) < (x + d * 2/3)
  II = transport (x + d * 1/3 <_) i ψ
   where
    i : x + d * 1/3 + d * 1/3 ≡ x + d * 2/3
    i = x + d * 1/3 + d * 1/3   ≡⟨ ℚ+-assoc fe x (d * 1/3) (d * 1/3) ⟩
        x + (d * 1/3 + d * 1/3) ≡⟨ ap (x +_) (ℚ-distributivity fe d 1/3 1/3 ⁻¹) ⟩
        x + d * (1/3 + 1/3)     ≡⟨ ap (λ z → x + (d * z)) (1/3+1/3 fe) ⟩
        x + d * 2/3             ∎
 

  III : x + d * 2/3 < y
  III = transport₂ _<_ ii iii i
   where
    i : d * 2/3 + x < d + x
    i = ℚ<-addition-preserves-order (d * 2/3) d x η
    ii : d * 2/3 + x ≡ x + d * 2/3
    ii = ℚ+-comm (d * 2/3) x
    iii : d + x ≡ y
    iii = d + x            ≡⟨ ℚ+-assoc fe y (- x) x ⟩
          y + ((- x) + x)  ≡⟨ ap (y +_) (ℚ-inverse-sum-to-zero' fe x) ⟩
          y + 0ℚ           ≡⟨ ℚ-zero-right-neutral fe y ⟩
          y                ∎

  IV : y - (x + d * 1/3) ≡ 2/3 * d
  IV = y - (x + d * 1/3)                 ≡⟨ ap (y +_) (ℚ-minus-dist fe x (d * 1/3)) ⁻¹ ⟩
       y + ((- x) + (- d * 1/3))         ≡⟨ ℚ+-assoc fe y (- x) (- d * 1/3) ⁻¹ ⟩
       d + (- d * 1/3)                   ≡⟨ ap (_+ (- (d * 1/3))) (ℚ-mult-left-id fe d ⁻¹) ⟩
       1ℚ * d + (- d * 1/3)              ≡⟨ ap (λ z → (z * d) + (- (d * 1/3))) (1/3+2/3 fe) ⟩
       1ℚ * d + (- d * 1/3)              ≡⟨ ap (_+ (- (d * 1/3))) (ℚ*-comm (1/3 + 2/3) d)  ⟩
       d * (1/3 + 2/3) + (- d * 1/3)     ≡⟨ ap (λ z → (d * z) + (- (d * 1/3))) (ℚ+-comm 1/3 2/3) ⟩
       d * (2/3 + 1/3) + (- d * 1/3)     ≡⟨ ap (_+ - (d * 1/3)) (ℚ-distributivity fe d 2/3 1/3) ⟩
       d * 2/3 + d * 1/3 + (- d * 1/3)   ≡⟨ ℚ+-assoc fe (d * 2/3) (d * 1/3) (- (d * 1/3)) ⟩
       d * 2/3 + (d * 1/3 + (- d * 1/3)) ≡⟨ ap₂ _+_ (ℚ*-comm d 2/3) (ℚ-inverse-sum-to-zero fe (d * 1/3)) ⟩
       2/3 * d + 0ℚ                      ≡⟨ ℚ-zero-right-neutral fe (2/3 * d) ⟩
       2/3 * d ∎

  V : x + d * 2/3 - x ≡ 2/3 * d
  V = x + d * 2/3 - x       ≡⟨ ap (_+ (- x)) (ℚ+-comm x (d * 2/3)) ⟩
      d * 2/3 + x + (- x)   ≡⟨ ℚ+-assoc fe (d * 2/3) x (- x) ⟩
      d * 2/3 + (x - x)     ≡⟨ ap₂ _+_ (ℚ*-comm d 2/3) (ℚ-inverse-sum-to-zero fe x) ⟩
      2/3 * d + 0ℚ          ≡⟨ ℚ-zero-right-neutral fe (2/3 * d) ⟩
      2/3 * d ∎

\end{code}
