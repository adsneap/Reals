Andrew Sneap

\begin{code}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆)  -- TypeTopology
open import UF-PropTrunc -- TypeTopology
open import UF-FunExt -- TypeTopology
open import UF-Powerset -- TypeTopology

open import Rationals
open import RationalsMultiplication
open import RationalsNegation
open import RationalsOrder

module DedekindRealsProperties
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
      where
open import DedekindReals pt fe
open PropositionalTruncation pt

exists-2/3-n : (x y p : ℚ) → x < y → 0ℚ < p → Σ n ꞉ ℕ , (((⟨2/3⟩^ n) * (y - x)) < p)
exists-2/3-n x y p l₁ l₂ = {!!} , {!!}

ral-lemma : (α β : ℚ) → (n : ℕ) → β ≡ 2/3 * α → ((rec 2/3 (λ k → k * 2/3) n * 2/3) * α) ≡ (rec 2/3 (λ k → k * 2/3) n * β)
ral-lemma α β n e = ((rec 2/3 (λ k → k * 2/3) n * 2/3) * α) ≡⟨ refl ⟩
               (((⟨2/3⟩^ (succ (succ n))) * α) )            ≡⟨ ap (_* α) (I (succ n)) ⟩
               (((⟨2/3⟩^ succ n) * 2/3) * α)                ≡⟨ ℚ*-assoc fe (⟨2/3⟩^ (succ n)) 2/3 α ⟩
               ((⟨2/3⟩^ succ n) * (2/3 * α))                ≡⟨ ap ((⟨2/3⟩^ (succ n)) *_) (e ⁻¹) ⟩
               (rec 2/3 (λ k → k * 2/3) n * β)              ∎
 where
  I : (n : ℕ) → ⟨2/3⟩^ (succ n) ≡ ((⟨2/3⟩^ n) * 2/3)
  I zero = f
   where
    abstract
     f : ⟨2/3⟩^ (succ 0) ≡ ((⟨2/3⟩^ 0) * 2/3)
     f = (ℚ-mult-left-id fe 2/3) ⁻¹
  I (succ n) = refl


ℝ-arithmetically-located : (((L , R) , _) : ℝ)
                          → (p : ℚ)
                          → 0ℚ < p
                          → ∃ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × 0ℚ < (y - x) × (y - x) < p
ℝ-arithmetically-located ((L , R) , inhabited-left , inhabited-right , rounded-left , rounded-right , disjoint , located) p l = ∥∥-rec ∃-is-prop I (binary-choice inhabited-left inhabited-right)
 where
  I : (Σ x ꞉ ℚ , x ∈ L) × (Σ y ꞉ ℚ , y ∈ R) → ∃ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × (0ℚ < (y - x) × (y - x) < p)
  I ((x , x-L) , (y , y-R)) = II x y x-L y-R (pr₁ γ) (trisect fe x y (disjoint x y (x-L , y-R))) (pr₂ γ) 
   where
    γ : Sigma ℕ (λ n → ((⟨2/3⟩^ n) * (y - x)) < p)
    γ = exists-2/3-n x y p (disjoint x y (x-L , y-R)) l
    
    II : (x y : ℚ) → x ∈ L → y ∈ R → (n : ℕ) → (Σ (x' , y') ꞉ ℚ × ℚ , x < x' × x' < y' × y' < y × ((y - x') ≡ (2/3 * (y - x))) × (y' - x ≡ 2/3 * (y - x)))
       → ((⟨2/3⟩^ n) * (y - x)) < p
       → ∃ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × (0ℚ < (y - x)) × ((y - x) < p)
    II x y x-L y-R zero ((x' , y') , l₁ , l₂ , l₃ , e₁ , e₂) l₄            = ∣ (x , y) , x-L , y-R , α , β ∣
     where
      abstract
       α : 0ℚ < (y - x)
       α = ℚ<-difference-positive fe x y (disjoint x y (x-L , y-R))
       β : y - x < p
       β = transport (_< p) (ℚ-mult-left-id fe (y - x)) l₄
      
    II x y x-L y-R (succ zero) ((x' , y') , l₁ , l₂ , l₃ , e₁ , e₂) l₄     = ∥∥-rec ∃-is-prop III (located x' y' l₂)
     where
      III : (x' ∈ L) ∔ (y' ∈ R) → ∃ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × (0ℚ < y - x × y - x < p)
      III (inl x'-L) = ∣ (x' , y) , x'-L , y-R , α , β ∣
       where
        abstract
         α : 0ℚ < y - x'
         α = ℚ<-difference-positive fe x' y (disjoint x' y (x'-L , y-R))
         β : y - x' < p
         β = transport (_< p) (e₁ ⁻¹) l₄
      III (inr y'-R) = ∣ (x , y') , x-L , y'-R , α , β ∣
       where
        abstract
         α : 0ℚ < y' - x
         α = ℚ<-difference-positive fe x y' (disjoint x y' (x-L , y'-R))
         β : y' - x < p
         β = transport (_< p) (e₂ ⁻¹) l₄
    II x y x-L y-R (succ (succ n)) ((x' , y') , l₁ , l₂ , l₃ , e₁ , e₂) l₄ =
      ∥∥-induction (λ _ → ∃-is-prop)
        (cases (λ x'-L → II x' y  x'-L y-R  (succ n) (trisect fe x' y (ℚ<-trans x' y' y l₂ l₃)) III)
               (λ y'-R → II x  y' x-L  y'-R (succ n) (trisect fe x y' (ℚ<-trans x x' y' l₁ l₂)) IV))
        (located x' y' l₂)
     where
      III : ((⟨2/3⟩^ succ n) * (y - x')) < p
      III = transport (_< p) (ral-lemma (y - x) (y - x') n e₁) l₄
      IV : ((⟨2/3⟩^ succ n) * (y' - x)) < p
      IV = transport (_< p) (ral-lemma (y - x) (y' - x) n e₂) l₄

\end{code}
