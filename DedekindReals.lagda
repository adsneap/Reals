Andrew Sneap


\begin{code}

{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆)  -- TypeTopology

open import UF-Base --TypeTopology
open import UF-FunExt -- TypeTopology
open import UF-PropTrunc -- TypeTopology
open import UF-Powerset -- TypeTopology
open import UF-Retracts --TypeTopology
open import UF-Subsingletons --TypeTopology
open import UF-Subsingletons-FunExt --TypeTopology
open import UF-Univalence --TypeTopology

open import Rationals
open import RationalsOrder renaming (_<_ to _ℚ<_)

module DedekindReals
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
       where

open PropositionalTruncation pt

ℚ-subset-of-propositions : 𝓤₁ ̇
ℚ-subset-of-propositions = 𝓟 ℚ


--Powersets are sets
ℚ-subset-of-propositions-is-set : Univalence → is-set ℚ-subset-of-propositions
ℚ-subset-of-propositions-is-set univ = powersets-are-sets' univ

inhabited-left : (L : ℚ-subset-of-propositions) → 𝓤₀ ̇
inhabited-left L = (∃ p ꞉ ℚ , p ∈ L) 

inhabited-right : (R : ℚ-subset-of-propositions) → 𝓤₀ ̇
inhabited-right R = (∃ q ꞉ ℚ , q ∈ R)

inhabited-left-is-prop : (L : ℚ-subset-of-propositions) → is-prop (inhabited-left L)
inhabited-left-is-prop L = ∃-is-prop

inhabited-right-is-prop : (R : ℚ-subset-of-propositions) → is-prop (inhabited-right R)
inhabited-right-is-prop R = ∃-is-prop

rounded-left : (L : ℚ-subset-of-propositions) → 𝓤₀ ̇
rounded-left L = (x : ℚ) → (x ∈ L ⇔ (∃ p ꞉ ℚ , (x ℚ< p) × p ∈ L))

rounded-left-a : (L : ℚ-subset-of-propositions) → rounded-left L → (x y : ℚ) → x ≤ y → y ∈ L → x ∈ L
rounded-left-a L r x y l y-L = II (ℚ≤-split fe x y l)
 where
  I : (∃ p ꞉ ℚ , (x ℚ< p) × p ∈ L) → x ∈ L
  I = pr₂ (r x)
  II : (x ℚ< y) ∔ (x ≡ y) → x ∈ L
  II (inl l) = I ∣ y , (l , y-L) ∣
  II (inr r) = transport (_∈ L) (r ⁻¹) y-L

-- rounded-left-b : {!!}
-- rounded-left-b = {!!}

rounded-right : (R : ℚ-subset-of-propositions) → 𝓤₀ ̇
rounded-right R = (x : ℚ) → x ∈ R ⇔ (∃ q ꞉ ℚ , (q ℚ< x) × q ∈ R)

rounded-right-a : (R : ℚ-subset-of-propositions) → rounded-right R → (x y : ℚ) → x ≤ y → x ∈ R → y ∈ R
rounded-right-a R r x y l x-R = II (ℚ≤-split fe x y l)
 where
  I : (∃ p ꞉ ℚ , (p ℚ< y) × p ∈ R) → y ∈ R 
  I = pr₂ (r y)
  II : (x ℚ< y) ∔ (x ≡ y) → y ∈ R
  II (inl r) = I ∣ x , (r , x-R) ∣
  II (inr r) = transport (_∈ R) r x-R

rounded-left-is-prop : (L : ℚ-subset-of-propositions) → is-prop (rounded-left L)
rounded-left-is-prop L = Π-is-prop fe δ
 where
  δ : (x : ℚ) → is-prop (x ∈ L ⇔ (∃ p ꞉ ℚ , (x ℚ< p) × p ∈ L))
  δ x = ×-is-prop (Π-is-prop fe (λ _ → ∃-is-prop)) (Π-is-prop fe (λ _ → ∈-is-prop L x))

rounded-right-is-prop : (R : ℚ-subset-of-propositions) → is-prop (rounded-right R)
rounded-right-is-prop R = Π-is-prop fe δ
 where
  δ : (x : ℚ) → is-prop (x ∈ R ⇔ (∃ q ꞉ ℚ , (q ℚ< x) × q ∈ R))
  δ x = ×-is-prop (Π-is-prop fe (λ _ → ∃-is-prop)) (Π-is-prop fe (λ _ → ∈-is-prop R x))

disjoint : (L R : ℚ-subset-of-propositions) → 𝓤₀ ̇
disjoint L R = (p q : ℚ) → p ∈ L × q ∈ R → p ℚ< q

disjoint-is-prop : (L R : ℚ-subset-of-propositions) → is-prop (disjoint L R)
disjoint-is-prop L R = Π₃-is-prop fe (λ x y _ → ℚ<-is-prop x y)

located : (L R : ℚ-subset-of-propositions) → 𝓤₀ ̇
located L R = (p q : ℚ) → p ℚ< q → p ∈ L ∨ q ∈ R

located-is-prop : (L R : ℚ-subset-of-propositions) → is-prop (located L R)
located-is-prop L R = Π₃-is-prop fe (λ _ _ _ → ∨-is-prop)

isCut : (L R : ℚ-subset-of-propositions) → 𝓤₀ ̇
isCut L R = inhabited-left L
          × inhabited-right R
          × rounded-left L
          × rounded-right R
          × disjoint L R
          × located L R

isCut-is-prop : (L R : ℚ-subset-of-propositions) → is-prop (isCut L R)
isCut-is-prop L R = ×-is-prop (inhabited-left-is-prop L)
                   (×-is-prop (inhabited-right-is-prop R)
                   (×-is-prop (rounded-left-is-prop L)
                   (×-is-prop (rounded-right-is-prop R)
                   (×-is-prop (disjoint-is-prop L R)
                              (located-is-prop L R)))))

ℝ : 𝓤₁ ̇
ℝ = Σ (L , R) ꞉ ℚ-subset-of-propositions × ℚ-subset-of-propositions , isCut L R

ℝ-is-set : Univalence → is-set ℝ
ℝ-is-set univ = Σ-is-set (×-is-set (ℚ-subset-of-propositions-is-set univ) (ℚ-subset-of-propositions-is-set univ)) δ
 where
  δ : ((L , R) : ℚ-subset-of-propositions × ℚ-subset-of-propositions) → is-set (isCut L R)
  δ (L , R)= props-are-sets (isCut-is-prop L R)

embedding-ℚ-to-ℝ : ℚ → ℝ
embedding-ℚ-to-ℝ x = (L , R) , inhabited-left'
                              , inhabited-right'
                              , rounded-left'
                              , rounded-right'
                              , disjoint'
                              , located' 
 where
  L R : 𝓟 ℚ
  L p = p ℚ< x , ℚ<-is-prop p x
  R q = x ℚ< q , ℚ<-is-prop x q

  inhabited-left' : ∃ p ꞉ ℚ , p ∈ L
  inhabited-left' = ∣ ℚ-no-least-element x ∣ 

  inhabited-right' : ∃ q ꞉ ℚ , q ∈ R
  inhabited-right' = ∣ ℚ-no-max-element x ∣

  rounded-left' :  (p : ℚ) → (p ∈ L ⇔ (∃ p' ꞉ ℚ , (p ℚ< p') × p' ∈ L))
  rounded-left' p = α , β
   where
    α : p ∈ L →  (∃ p' ꞉ ℚ , (p ℚ< p') × p' ∈ L)
    α l = ∣ ℚ-dense p x l ∣

    β :  (∃ p' ꞉ ℚ , (p ℚ< p') × p' ∈ L) → p ∈ L
    β l = ∥∥-rec (ℚ<-is-prop p x) δ l
     where
      δ : Σ p' ꞉ ℚ , (p ℚ< p') × p' ∈ L → p ℚ< x
      δ (p' , a , b) = ℚ<-trans p p' x a b

  rounded-right' : (q : ℚ) → q ∈ R ⇔ (∃ q' ꞉ ℚ , (q' ℚ< q) × q' ∈ R)
  rounded-right' q = α , β
   where
    α : q ∈ R → ∃ q' ꞉ ℚ , (q' ℚ< q) × q' ∈ R
    α r = ∣ δ (ℚ-dense x q r) ∣
     where
      δ : (Σ q' ꞉ ℚ , (x ℚ< q') × (q' ℚ< q)) → Σ q' ꞉ ℚ , (q' ℚ< q) × q' ∈ R
      δ (q' , a , b) = q' , b , a

    β : ∃ q' ꞉ ℚ , (q' ℚ< q) × q' ∈ R → q ∈ R
    β r = ∥∥-rec (ℚ<-is-prop x q) δ r
     where
      δ : Σ q' ꞉ ℚ , (q' ℚ< q) × q' ∈ R → x ℚ< q
      δ (q' , a , b) = ℚ<-trans x q' q b a

  disjoint' : (p q : ℚ) → p ∈ L × q ∈ R → p ℚ< q
  disjoint' p q (l , r) = ℚ<-trans p x q l r

  located' : (p q : ℚ) → p ℚ< q → p ∈ L ∨ q ∈ R
  located' p q l = ∣ located-property fe p q x l ∣

0ℝ : ℝ
0ℝ = embedding-ℚ-to-ℝ 0ℚ

1ℝ : ℝ
1ℝ = embedding-ℚ-to-ℝ 1ℚ

ℝ-equality : (((Lx , Rx) , isCutx) ((Ly , Ry) , isCuty) : ℝ)
           → (Lx ≡ Ly)
           → (Rx ≡ Ry)
           → ((Lx , Rx) , isCutx) ≡ ((Ly , Ry) , isCuty)
ℝ-equality ((Lx , Rx) , isCutx) ((Ly , Ry) , isCuty) e₁  e₂ = to-subtype-≡ (λ (L , R) → isCut-is-prop L R) (to-×-≡' (e₁ , e₂))

\end{code}
