{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆)  -- TypeTopology
open import UF-FunExt -- TypeTopology
open import UF-PropTrunc -- TypeTopology
open import UF-Univalence

import NaturalsOrder
import UF-Powerset
import UF-Retracts
import UF-Subsingletons
import UF-Subsingletons-FunExt

import Rationals

module NewDedekindReals
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
       where

open PropositionalTruncation pt -- TypeTopology
open Rationals renaming (_<_ to _ℚ<_ ; _+_ to _ℚ+_ ; _*_ to _ℚ*_ ; -_ to ℚ-_ ; _≤_ to _ℚ≤_)
open UF-Powerset -- TypeTopology
open UF-Subsingletons --Type Topology
open UF-Subsingletons-FunExt -- TypeTopology

ℚ-subset-of-propositions : 𝓤₁ ̇
ℚ-subset-of-propositions = 𝓟 ℚ

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

rounded-right : (R : ℚ-subset-of-propositions) → 𝓤₀ ̇
rounded-right R = (x : ℚ) → x ∈ R ⇔ (∃ q ꞉ ℚ , (q ℚ< x) × q ∈ R)

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

open UF-Retracts -- TypeTopology

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
    α l = ∣ rounded-lemma p x l ∣

    β :  (∃ p' ꞉ ℚ , (p ℚ< p') × p' ∈ L) → p ∈ L
    β l = ∥∥-rec (ℚ<-is-prop p x) δ l
     where
      δ : Σ p' ꞉ ℚ , (p ℚ< p') × p' ∈ L → p ℚ< x
      δ (p' , a , b) = ℚ<-trans p p' x a b

  rounded-right' : (q : ℚ) → q ∈ R ⇔ (∃ q' ꞉ ℚ , (q' ℚ< q) × q' ∈ R)
  rounded-right' q = α , β
   where
    α : q ∈ R → ∃ q' ꞉ ℚ , (q' ℚ< q) × q' ∈ R
    α r = ∣ δ (rounded-lemma x q r) ∣
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

zero-ℝ : ℝ
zero-ℝ = embedding-ℚ-to-ℝ zero-ℚ

one-ℝ : ℝ
one-ℝ = embedding-ℚ-to-ℝ 1ℚ

_<_ : ℝ → ℝ → 𝓤₀ ̇
((Lx , Rx) , isCutx) < ((Ly , Ry) , isCuty) = ∃ q ꞉ ℚ , q ∈ Rx × q ∈ Ly

_≤_ : ℝ → ℝ → 𝓤₀ ̇
((Lx , Rx) , isCutx) ≤ ((Ly , Ry) , isCuty) = (q : ℚ) → q ∈ Lx → q ∈ Ly

<-is-prop : (x y : ℝ) → is-prop (x < y)
<-is-prop x y = ∃-is-prop

≤-is-prop : (x y : ℝ) → is-prop (x ≤ y)
≤-is-prop ((Lx , Rx) , isCutx) ((Ly , Ry) , isCuty) = Π₂-is-prop fe (λ q _ → ∈-is-prop Ly q)

_#_ : (x y : ℝ) → 𝓤₀ ̇
x # y = (x < y) ∨ (y < x)

#-is-prop : (x y : ℝ) → is-prop (x # y)
#-is-prop _ _ = ∨-is-prop

open import UF-Base --TypeTopology













{-
open NaturalsOrder renaming (_<_ to _ℕ<_ ; _≤_ to _ℕ≤_)
open import Integers renaming (_+_ to ℤ+_)
{-
⟨2/3⟩^_ : ℕ → ℚ
⟨2/3⟩^ 0  = toℚ (pos 1 , 0)
⟨2/3⟩^ (succ n)  = rec (toℚ (pos 2 , 2)) (λ k → k ℚ* toℚ (pos 2 , 2)) n
-}
_ℚ--_ : ℚ → ℚ → ℚ
p ℚ-- q = p ℚ+ (ℚ- q)

ℝ-order-lemma : (((L , R) , inhabited-left , inhabited-right , rounded-left , rounded-right , disjoint , located) : ℝ) → (x y : ℚ) → x ∈ L → y ∈ R → zero-ℚ ℚ< (y ℚ+ (ℚ- x))
ℝ-order-lemma ((L , R) , inhabited-left , inhabited-right , rounded-left , rounded-right , disjoint , located) x y x-L y-R = ℚ<-subtraction''' fe x y I
 where
  I : x ℚ< y
  I = disjoint x y (x-L , y-R)

open import TestingGround

_ℚ<_ℚ<_ : ℚ → ℚ → ℚ → 𝓤₀ ̇
a ℚ< b ℚ< c = (a ℚ< b) × (b ℚ< c)

foo : ⟨2/3⟩^ 1 ≡ ((⟨2/3⟩^ 0) ℚ* 2/3)
foo = blah
 where
  abstract
   blah : ⟨2/3⟩^ 1 ≡ ((⟨2/3⟩^ 0) ℚ* 2/3)
   blah = ℚ-mult-left-id fe 2/3 ⁻¹

ral-lemma : (n : ℕ) → ⟨2/3⟩^ succ n ≡ ((⟨2/3⟩^ n) ℚ* 2/3)
ral-lemma zero = foo -- (ℚ-mult-left-id fe 2/3) ⁻¹
ral-lemma (succ n) = refl

ral-lemma₂ : Fun-Ext → (q : ℚ) → (n : ℕ) → ((⟨2/3⟩^ n) ℚ* 2/3) ℚ* q ≡ ((⟨2/3⟩^ n) ℚ* (2/3 ℚ* q))  
ral-lemma₂ fe q n = ℚ*-assoc fe (⟨2/3⟩^ n) 2/3 q

ral-lemma₃ : Fun-Ext → (q : ℚ) → (n : ℕ) → (⟨2/3⟩^ succ n) ℚ* q ≡ ((⟨2/3⟩^ n) ℚ* (2/3 ℚ* q))
ral-lemma₃ fe q n = ap (_ℚ* q) (ral-lemma n) ∙ ral-lemma₂ fe q n

{-
Want to show Σ x y , 0 < (y - x) < p ,x ∈ L, y ∈ R
x ∈ L
y ∈ R

x < x' < y' < y

y' - x = 2/3 (y - x)

locatedness x' y' - x' ∈ L, y' ∈ R

Σ n , (2/3)^n * (y - x) < p

Σ x' y' , x' ∈ L , y' ∈ R , 0 < (y' - x') < p

Suggestion : Define y' = (2/3)^n * y' , (2/3)^n x'
 Maybe a stronger n 

-}

ℝ-arithmetically-located' : (((L , R) , _) : ℝ)
              → (p : ℚ)
              → zero-ℚ ℚ< p
              → ∃ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × (zero-ℚ ℚ< (y ℚ-- x) ℚ< p)
ℝ-arithmetically-located' ((L , R) , inhabited-left , inhabited-right , rounded-left , rounded-right , disjoint , located) p l = ∥∥-rec ∃-is-prop I (binary-choice inhabited-left inhabited-right)
 where
  I : (Σ x ꞉ ℚ , x ∈ L) × (Σ y ꞉ ℚ , y ∈ R) → ∃ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × (zero-ℚ ℚ< (y ℚ-- x) ℚ< p)
  I ((x , x-L) , (y , y-R)) = II {!!} {!!}
   where
    II : (n : ℕ) → ((⟨2/3⟩^ n) ℚ* (y ℚ-- x)) ℚ< p → ∃ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × (zero-ℚ ℚ< (y ℚ-- x) ℚ< p)
    II zero l₂            = ∣ (x , y) , x-L , y-R , α , β ∣
     where
      abstract
       α : zero-ℚ ℚ< (y ℚ-- x)
       α =  ℚ<-subtraction''' fe x y (disjoint x y (x-L , y-R))
       β : (y ℚ-- x) ℚ< p
       β = (transport (_ℚ< p) (ℚ-mult-left-id fe (y ℚ-- x))) l₂
     
    II (succ zero) l₂     = {!!}
    II (succ (succ n)) l₂ = II (succ n) {!!}
     where
      III : (Σ (x' , y') ꞉ ℚ × ℚ , (x ℚ< x') × (x' ℚ< y') × (y' ℚ< y) × ((y ℚ-- x') ≡ (2/3 ℚ* (y ℚ-- x))) × (y' ℚ-- x ≡ 2/3 ℚ* (y ℚ-- x))) → ((⟨2/3⟩^ succ n) ℚ* (y ℚ-- x)) ℚ< p
      III ((x' , y') , l₁ , l₂ , l₃ , e₁ , e₂) = {!!}

-- This function allows succ n. I can't fill these holes, since I need to know if x' ∈ L or y' ∈ R
-- The next function shows that once I know the above, I can complete the induction. Unfortunately, it results in termination problems. I'm not sure how to tackle this.
last-attempt : (((L , R) , inhabited-left , inhabited-right , rounded-left , rounded-right , disjoint , located) : ℝ)
                          → (p : ℚ)
                          → zero-ℚ ℚ< p
                          → ∃ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × (zero-ℚ ℚ< (y ℚ-- x)) × ((y ℚ-- x) ℚ< p)
last-attempt ((L , R) , inhabited-left , inhabited-right , rounded-left , rounded-right , disjoint , located) p l = ∥∥-rec ∃-is-prop I (binary-choice inhabited-left inhabited-right)
 where
  I : (Σ x ꞉ ℚ , x ∈ L) × (Σ y ꞉ ℚ , y ∈ R) → ∃ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × (zero-ℚ ℚ< (y ℚ-- x) ℚ< p)
  I ((x , x-L) , (y , y-R)) = II x y x-L y-R {!!} (trisect fe x y (disjoint x y (x-L , y-R))) {!!} 
   where
    II : (x y : ℚ) → x ∈ L → y ∈ R → (n : ℕ) → (Σ (x' , y') ꞉ ℚ × ℚ , (x ℚ< x') × (x' ℚ< y') × (y' ℚ< y) × ((y ℚ-- x') ≡ (2/3 ℚ* (y ℚ-- x))) × (y' ℚ-- x ≡ 2/3 ℚ* (y ℚ-- x)))
       → ((⟨2/3⟩^ n) ℚ* (y ℚ-- x)) ℚ< p
       → ∃ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × (zero-ℚ ℚ< (y ℚ-- x)) × ((y ℚ-- x) ℚ< p)
    II x y x-L y-R zero ((x' , y') , l₁ , l₂ , l₃ , e₁ , e₂) l₄            = ∣ (x , y) , x-L , y-R , {!!} , {!!} ∣
    II x y x-L y-R (succ zero) ((x' , y') , l₁ , l₂ , l₃ , e₁ , e₂) l₄     = {!!}
    II x y x-L y-R (succ (succ n)) ((x' , y') , l₁ , l₂ , l₃ , e₁ , e₂) l₄ = II {!!} {!!} {!!} {!!} (succ n) {!!} {!!} -- ∥∥-rec ∃-is-prop IH (located x' y' l₂)
     where
      split : x' ∈ L ∔ y' ∈ R → ∃ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × (zero-ℚ ℚ< (y ℚ-- x)) × ((y ℚ-- x) ℚ< p)
      split (inl x'-L) = II {!!} {!!} {!!} {!!} n {!!} {!!}
      split (inr y'-R) = {!!}


ℝ-arithmetically-located : (((L , R) , _) : ℝ)
              → (p : ℚ)
              → zero-ℚ ℚ< p
              → ∃ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × (zero-ℚ ℚ< (y ℚ-- x) ℚ< p)
ℝ-arithmetically-located ((L , R) , inhabited-left , inhabited-right , rounded-left , rounded-right , disjoint , located) p l = ∥∥-rec ∃-is-prop I (binary-choice inhabited-left inhabited-right)
 where
  I : (Σ x ꞉ ℚ , x ∈ L) × (Σ y ꞉ ℚ , y ∈ R) → ∃ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × (zero-ℚ ℚ< (y ℚ-- x) ℚ< p)
  I ((x , x-L) , (y , y-R)) = II x y x-L y-R (trisect fe x y (disjoint x y (x-L , y-R))) {!!} {!!} -- II (trisect fe x y (disjoint x y (x-L , y-R)))
   where
    II : (x y : ℚ) → x ∈ L → y ∈ R
       → Σ (x' , y') ꞉ ℚ × ℚ , (x ℚ< x') × (x' ℚ< y') × (y' ℚ< y) × ((y ℚ-- x') ≡ (2/3 ℚ* (y ℚ-- x))) × (y' ℚ-- x ≡ 2/3 ℚ* (y ℚ-- x))
       → (n : ℕ) → ((⟨2/3⟩^ n) ℚ* (y ℚ-- x)) ℚ< p
       → ∃ (x' , y') ꞉ ℚ × ℚ , x' ∈ L × y' ∈ R × (zero-ℚ ℚ< (y' ℚ-- x') ℚ< p)
    II x y x-L y-R ((x' , y') , l₁ , l₂ , l₃ , e₁ , e₂) zero l₅ = {!!} -- ∣ (x , y) , (x-L , (y-R , ((ℚ<-subtraction''' fe x y (disjoint x y (x-L , y-R))) , (transport (_ℚ< p) (ℚ-mult-left-id fe (y ℚ-- x)) l₅)))) ∣
    II x y x-L y-R ((x' , y') , l₁ , l₂ , l₃ , e₁ , e₂) (succ zero) l₅ = {!!}
     where
      III : x' ∈ L ∔ y' ∈ R → ∃ (x' , y') ꞉ ℚ × ℚ , x' ∈ L × y' ∈ R × (zero-ℚ ℚ< (y' ℚ-- x') ℚ< p)
      III (inl x'-L) = {!!} -- ∣ (x' , y) , (x'-L , (y-R , ((ℚ<-subtraction''' fe x' y (ℚ<-trans x' y' y l₂ l₃)) , (transport (_ℚ< p) (e₁ ⁻¹) l₅)))) ∣
      III (inr y'-R) = {!!}
    II x y x-L y-R ((x' , y') , l₁ , l₂ , l₃ , e₁ , e₂) (succ (succ n)) l₅ = ∥∥-rec ∃-is-prop III (located x' y' l₂)
     where
      III : x' ∈ L ∔ y' ∈ R → ∃ (x' , y') ꞉ ℚ × ℚ , x' ∈ L × y' ∈ R × (zero-ℚ ℚ< (y' ℚ-- x') ℚ< p)
      III (inl x'-L) = {!!} -- II x' y x'-L y-R (trisect fe x' y (ℚ<-trans x' y' y l₂ l₃)) (succ n) (transport (_ℚ< p) v l₅)
       where
        i : ((⟨2/3⟩^ succ n) ℚ* (y ℚ-- x)) ≡ ((⟨2/3⟩^ n) ℚ* (2/3 ℚ* (y ℚ-- x)))
        i = ral-lemma₃ fe (y ℚ-- x) n
        ii :  ((⟨2/3⟩^ n) ℚ* (2/3 ℚ* (y ℚ-- x))) ≡  ( (⟨2/3⟩^ n) ℚ* (y ℚ-- x'))
        ii = ap ((⟨2/3⟩^ n) ℚ*_) (e₁ ⁻¹)
        iii : ((⟨2/3⟩^ succ n) ℚ* (y ℚ-- x)) ≡ ((⟨2/3⟩^ n) ℚ* (y ℚ-- x'))
        iii = i ∙ ii
        iv : ((rec 2/3 (λ k → k ℚ* 2/3) n ℚ* 2/3) ℚ* (y ℚ-- x)) ≡ ((⟨2/3⟩^ (succ (succ n))) ℚ* (y ℚ-- x)) 
        iv = refl
        v : ((rec 2/3 (λ k → k ℚ* 2/3) n ℚ* 2/3) ℚ* (y ℚ-- x)) ≡ (rec 2/3 (λ k → k ℚ* 2/3) n ℚ* (y ℚ-- x'))
        v = ((rec 2/3 (λ k → k ℚ* 2/3) n ℚ* 2/3) ℚ* (y ℚ-- x)) ≡⟨ iv ⁻¹ ⟩
             ( ((⟨2/3⟩^ (succ (succ n))) ℚ* (y ℚ-- x)))        ≡⟨ ral-lemma₃ fe (y ℚ-- x) (succ  n) ⟩
             ((⟨2/3⟩^ succ n) ℚ* (2/3 ℚ* (y ℚ-- x)))           ≡⟨ ap (((⟨2/3⟩^ succ n)) ℚ*_) (e₁ ⁻¹) ⟩
             ((⟨2/3⟩^ succ n) ℚ* (y ℚ-- x'))                   ≡⟨ refl ⟩
             (rec 2/3 (λ k → k ℚ* 2/3) n ℚ* (y ℚ-- x')) ∎
      III (inr y'-R) = II {!!} {!!} {!!} {!!} {!!} n {!!}


ℝ-addition-lemma : (((L-x , R-x) , _)
                    ((L-y , R-y) , _) : ℝ)
                 → (p q : ℚ)
                 → (∃ (r , s) ꞉ ℚ × ℚ , r ∈ L-x × s ∈ L-y × p ℚ< (r ℚ+ s) → ∃ (r , s) ꞉ ℚ × ℚ , r ∈ L-x × s ∈ L-y × (p ≡ r ℚ+ s))
                 ×  ((∃ (r , s) ꞉ ℚ × ℚ , r ∈ R-x × s ∈ R-y × ((r ℚ+ s)) ℚ< q) → (∃ (r , s) ꞉ ℚ × ℚ , r ∈ R-x × s ∈ R-y × (q ≡ r ℚ+ s)))
ℝ-addition-lemma ((L-x , R-x) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x)
                    ((L-y , R-y) , inhabited-left-y , inhabited-right-y , rounded-left-y , rounded-right-y , disjoint-y , located-y) p q = α , β
 where
  α : ∃ (r , s) ꞉ ℚ × ℚ , r ∈ L-x × s ∈ L-y × p ℚ< (r ℚ+ s) → ∃ (r , s) ꞉ ℚ × ℚ , r ∈ L-x × s ∈ L-y × (p ≡ r ℚ+ s)
  α = ∥∥-functor I
   where
    I : Σ (r , s) ꞉ ℚ × ℚ , r ∈ L-x × s ∈ L-y × p ℚ< (r ℚ+ s) → Σ (r , s) ꞉ ℚ × ℚ , r ∈ L-x × s ∈ L-y × (p ≡ r ℚ+ s)
    I ((r , s) , l-x , l-y , l) = ((r ℚ+ (ℚ- k)) , s) , ii , l-y , iii
     where
      i : Σ k ꞉ ℚ , (zero-ℚ ℚ< k) × (k ≡ (r ℚ+ s) ℚ+ (ℚ- p))
      i = ℚ<-subtraction'' fe p (r ℚ+ s) l
      k : ℚ
      k = pr₁ i
      ii : (r ℚ+ (ℚ- k)) ∈ L-x
      ii = δ ∣ r , (γ , l-x) ∣
       where
        δ : ∃ p' ꞉ ℚ , ((r ℚ+ (ℚ- k)) ℚ< p') × p' ∈ L-x → (r ℚ+ (ℚ- k)) ∈ L-x
        δ = pr₂ (rounded-left-x (r ℚ+ (ℚ- k)))
        ψ : (p ℚ+ (ℚ- s)) ℚ< ((r ℚ+ s) ℚ+ (ℚ- s))
        ψ = ℚ-addition-preserves-order p (r ℚ+ s) (ℚ- s) l
        ζ : (p ℚ+ (ℚ- s)) ℚ< (r ℚ+ (s ℚ+ (ℚ- s)))
        ζ = transport ((p ℚ+ (ℚ- s)) ℚ<_) (ℚ+-assoc fe r s (ℚ- s)) ψ
        ϕ : (p ℚ+ (ℚ- s)) ℚ< (r ℚ+ zero-ℚ)
        ϕ = transport ((p ℚ+ (ℚ- s)) ℚ<_) (ap (r ℚ+_) (ℚ-inverse-sum-to-zero fe s)) ζ
        τ : (p ℚ+ (ℚ- s)) ℚ< r
        τ = transport ((p ℚ+ (ℚ- s)) ℚ<_) (ℚ-zero-right-neutral fe r) ϕ
        γ : (r ℚ+ (ℚ- k)) ℚ< r
        γ = transport (_ℚ< r) μ τ
         where
          μ : p ℚ+ (ℚ- s) ≡ (r ℚ+ (ℚ- k))
          μ = p ℚ+ (ℚ- s)                               ≡⟨ ap (p ℚ+_) (ℚ-zero-left-neutral fe (ℚ- s) ⁻¹) ⟩
              p ℚ+ (zero-ℚ ℚ+ (ℚ- s))                   ≡⟨ ap (λ - → p ℚ+ (- ℚ+ (ℚ- s))) (ℚ-inverse-sum-to-zero fe r ⁻¹) ⟩
              p ℚ+ ((r ℚ+ (ℚ- r)) ℚ+ (ℚ- s))            ≡⟨ ap (p ℚ+_) (ℚ+-assoc fe r (ℚ- r) (ℚ- s)) ⟩
              p ℚ+ (r ℚ+ ((ℚ- r) ℚ+ (ℚ- s)))            ≡⟨ ap (λ - → p ℚ+ (r ℚ+ -)) (ℚ-minus-dist fe r s) ⟩
              p ℚ+ (r ℚ+ (ℚ- (r ℚ+ s)))                 ≡⟨ ℚ+-comm p (r ℚ+ (ℚ- (r ℚ+ s))) ⟩
              (r ℚ+ (ℚ- (r ℚ+ s))) ℚ+ p                 ≡⟨ ℚ+-assoc fe r (ℚ- (r ℚ+ s)) p ⟩
              r ℚ+ ((ℚ- (r ℚ+ s)) ℚ+ p)                 ≡⟨ ap (λ - → r ℚ+ ((ℚ- (r ℚ+ s)) ℚ+ -)) (ℚ-minus-minus fe p) ⟩
              r ℚ+ ((ℚ- (r ℚ+ s)) ℚ+ (ℚ- (ℚ- p)))       ≡⟨ ap (r ℚ+_) (ℚ-minus-dist fe (r ℚ+ s) (ℚ- p)) ⟩
              r ℚ+ (ℚ- ((r ℚ+ s) ℚ+ (ℚ- p)))            ≡⟨ ap (λ z → (r ℚ+ (ℚ- z))) ((pr₂ (pr₂ i))⁻¹) ⟩
              r ℚ+ (ℚ- k) ∎
      iii : p ≡ ((r ℚ+ (ℚ- k)) ℚ+ s)
      iii = p                                            ≡⟨ ℚ-zero-right-neutral fe p ⁻¹ ⟩
            (p ℚ+ zero-ℚ)                                ≡⟨ ap (p ℚ+_) (ℚ-inverse-sum-to-zero' fe s ⁻¹ ) ⟩
            p ℚ+ ((ℚ- s) ℚ+ s)                           ≡⟨ ℚ+-assoc fe p (ℚ- s) s ⁻¹ ⟩
            (p ℚ+ (ℚ- s)) ℚ+ s                           ≡⟨ ap (_ℚ+ s) (ℚ+-comm p (ℚ- s)) ⟩
            ((ℚ- s) ℚ+ p) ℚ+ s                           ≡⟨ ap (λ - → (- ℚ+ p) ℚ+ s) (ℚ-zero-left-neutral fe (ℚ- s) ⁻¹) ⟩
            ((zero-ℚ ℚ+ (ℚ- s)) ℚ+ p) ℚ+ s               ≡⟨ ap (λ - → ((- ℚ+ (ℚ- s)) ℚ+ p) ℚ+ s) (ℚ-inverse-sum-to-zero fe r ⁻¹) ⟩
            (((r ℚ+ (ℚ- r)) ℚ+ (ℚ- s)) ℚ+ p) ℚ+ s        ≡⟨ ap (λ - → (- ℚ+ p) ℚ+ s) (ℚ+-assoc fe r (ℚ- r) (ℚ- s)) ⟩
            ((r ℚ+ ((ℚ- r) ℚ+ (ℚ- s))) ℚ+ p) ℚ+ s        ≡⟨ ap (_ℚ+ s) (ℚ+-assoc fe r ((ℚ- r) ℚ+ (ℚ- s)) p) ⟩
            (r ℚ+ (((ℚ- r) ℚ+ (ℚ- s)) ℚ+ p)) ℚ+ s        ≡⟨ ap₂ (λ ζ₁ ζ₂ → (r ℚ+ (ζ₁ ℚ+ ζ₂)) ℚ+ s) (ℚ-minus-dist fe r s) (ℚ-minus-minus fe p) ⟩
            (r ℚ+ ((ℚ- (r ℚ+ s)) ℚ+ (ℚ- (ℚ- p)))) ℚ+ s   ≡⟨ ap (λ - → (r ℚ+ -) ℚ+ s) (ℚ-minus-dist fe (r ℚ+ s) (ℚ- p)) ⟩
            (r ℚ+ (ℚ- ((r ℚ+ s) ℚ+ (ℚ- p)))) ℚ+ s        ≡⟨ ap (λ - → (r ℚ+ (ℚ- -)) ℚ+ s ) (pr₂ (pr₂ i) ⁻¹) ⟩
            (r ℚ+ (ℚ- k)) ℚ+ s ∎
  β : ∃ (r , s) ꞉ ℚ × ℚ , r ∈ R-x × s ∈ R-y × (r ℚ+ s) ℚ< q → ∃ (r , s) ꞉ ℚ × ℚ , r ∈ R-x × s ∈ R-y × (q ≡ r ℚ+ s)
  β = ∥∥-functor I
   where
    I : Σ (r , s) ꞉ ℚ × ℚ , r ∈ R-x × s ∈ R-y × (r ℚ+ s) ℚ< q
      → Σ (r , s) ꞉ ℚ × ℚ , r ∈ R-x × s ∈ R-y × (q ≡ r ℚ+ s)
    I ((r , s) , r-x , r-y , l) = ((r ℚ+ k) , s) , ii δ , r-y , iii
     where
      i : Σ k ꞉ ℚ , (zero-ℚ ℚ< k) × (k ≡ (q ℚ+ (ℚ- (r ℚ+ s))))
      i = ℚ<-subtraction'' fe (r ℚ+ s) q l
      k = pr₁ i

      ii : ∃ q' ꞉ ℚ , ((q' ℚ< (r ℚ+ k)) × (q' ∈ R-x)) → (r ℚ+ k) ∈ R-x 
      ii = pr₂ (rounded-right-x (r ℚ+ k))

      δ : ∃ q' ꞉ ℚ , ((q' ℚ< (r ℚ+ k)) × (q' ∈ R-x))
      δ = ∣ r , (γ , r-x) ∣
       where
        ψ : (zero-ℚ ℚ+ r) ℚ< (k ℚ+ r)
        ψ = ℚ-addition-preserves-order zero-ℚ k r (pr₁ (pr₂ i))
        γ : r ℚ< (r ℚ+ k)
        γ = transport₂ _ℚ<_ (ℚ-zero-left-neutral fe r) (ℚ+-comm k r) ψ

      iii : q ≡ ((r ℚ+ k) ℚ+ s)
      iii = q                                         ≡⟨ ℚ-zero-right-neutral fe q ⁻¹ ⟩
            q ℚ+ zero-ℚ                               ≡⟨ ap (q ℚ+_) (ℚ-inverse-sum-to-zero' fe s ⁻¹) ⟩
            q ℚ+ ((ℚ- s) ℚ+ s)                        ≡⟨ ℚ+-assoc fe q (ℚ- s) s ⁻¹ ⟩
            (q ℚ+ (ℚ- s)) ℚ+ s                        ≡⟨ ap (λ - → (- ℚ+ (ℚ- s)) ℚ+ s) (ℚ-zero-left-neutral fe q ⁻¹) ⟩
            ((zero-ℚ ℚ+ q) ℚ+ (ℚ- s)) ℚ+ s            ≡⟨ ap (λ - → ((- ℚ+ q) ℚ+ (ℚ- s)) ℚ+ s) (ℚ-inverse-sum-to-zero fe r ⁻¹ ) ⟩
            (((r ℚ+ (ℚ- r)) ℚ+ q) ℚ+ (ℚ- s)) ℚ+ s     ≡⟨ ap (λ - → (- ℚ+ (ℚ- s)) ℚ+ s) (ℚ+-assoc fe r (ℚ- r) q) ⟩
            ((r ℚ+ ((ℚ- r) ℚ+ q)) ℚ+ (ℚ- s)) ℚ+ s     ≡⟨ ap  (_ℚ+ s) (ℚ+-assoc fe r ((ℚ- r) ℚ+ q) (ℚ- s)) ⟩
            (r ℚ+ (((ℚ- r) ℚ+ q) ℚ+ (ℚ- s))) ℚ+ s     ≡⟨ ap (λ - → (r ℚ+ (- ℚ+ (ℚ- s))) ℚ+ s) (ℚ+-comm (ℚ- r) q) ⟩
            (r ℚ+ ((q ℚ+ (ℚ- r)) ℚ+ (ℚ- s))) ℚ+ s     ≡⟨ ap (λ - → (r ℚ+ -) ℚ+ s) (ℚ+-assoc fe q (ℚ- r) (ℚ- s)) ⟩
            (r ℚ+ (q ℚ+ ((ℚ- r) ℚ+ (ℚ- s)))) ℚ+ s     ≡⟨ ap (λ - → (r ℚ+ (q ℚ+ -)) ℚ+ s) (ℚ-minus-dist fe r s) ⟩
            (r ℚ+ (q ℚ+ (ℚ- (r ℚ+ s)))) ℚ+ s          ≡⟨ ap (λ - → (r ℚ+ -) ℚ+ s) (pr₂ (pr₂ i) ⁻¹) ⟩
            (r ℚ+ k) ℚ+ s ∎

--Binary Naturals file needs to be worked on. Also embedding to the rational numbers

_+_ : ℝ → ℝ → ℝ
((L-x , R-x) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x) + ((L-y , R-y) , inhabited-left-y , inhabited-right-y , rounded-left-y , rounded-right-y , disjoint-y , located-y) =
 (L-z , R-z) , inhabited-left-z , inhabited-right-z , rounded-left-z , rounded-right-z , disjoint-z , located-z
 where
  L-z R-z : ℚ-subset-of-propositions
  L-z p = (∃ (r , s) ꞉ ℚ × ℚ , r ∈ L-x × s ∈ L-y × (p ≡ r ℚ+ s)) , ∃-is-prop
  R-z q = (∃ (r , s) ꞉ ℚ × ℚ , r ∈ R-x × s ∈ R-y × (q ≡ r ℚ+ s)) , ∃-is-prop

  inhabited-left-z : ∃ q ꞉ ℚ , q ∈ L-z
  inhabited-left-z = ∥∥-rec ∃-is-prop δ (binary-choice inhabited-left-x inhabited-left-y)
   where
    δ : (Σ p ꞉ ℚ , p ∈ L-x) × (Σ q ꞉ ℚ , q ∈ L-y) → ∃ z ꞉ ℚ , z ∈ L-z
    δ ((p , l-x) , q , l-y) = ∣ (p ℚ+ q) , (∣ (p , q) , l-x , l-y , refl ∣) ∣

  inhabited-right-z : ∃ q ꞉ ℚ , q ∈ R-z
  inhabited-right-z = ∥∥-rec ∃-is-prop δ (binary-choice inhabited-right-x inhabited-right-y)
   where
    δ : (Σ p ꞉ ℚ , p ∈ R-x) × (Σ q ꞉ ℚ , q ∈ R-y) → ∃ z ꞉ ℚ , z ∈ R-z
    δ ((p , r-x) , q , r-y) = ∣ (p ℚ+ q) , (∣ (p , q) , (r-x , r-y , refl) ∣) ∣

  ψ : (z r t s : ℚ) → t ≡ r ℚ+ s → z ≡ ((r ℚ+ (z ℚ+ (ℚ- t))) ℚ+ s)
  ψ z r t s e = z                                                ≡⟨ ℚ-zero-left-neutral fe z ⁻¹ ⟩
                (zero-ℚ ℚ+ z)                                    ≡⟨ ap (_ℚ+ z) (ℚ-inverse-sum-to-zero fe r ⁻¹) ⟩
                ((r ℚ+ (ℚ- r)) ℚ+ z)                             ≡⟨ (ℚ+-assoc fe r (ℚ- r) z) ⟩
                (r ℚ+ ((ℚ- r) ℚ+ z))                             ≡⟨ ℚ-zero-right-neutral fe (r ℚ+ ((ℚ- r) ℚ+ z)) ⁻¹ ⟩
                (r ℚ+ ((ℚ- r) ℚ+ z)) ℚ+ zero-ℚ                  ≡⟨ ap₂ _ℚ+_ (ap (r ℚ+_) (ℚ+-comm (ℚ- r) z)) (ℚ-inverse-sum-to-zero' fe s ⁻¹) ⟩
                (r ℚ+ (z ℚ+ (ℚ- r))) ℚ+ ((ℚ- s) ℚ+ s)           ≡⟨ ℚ+-assoc fe (r ℚ+ (z ℚ+ (ℚ- r))) (ℚ- s) s ⁻¹ ⟩
                ((r ℚ+ (z ℚ+ (ℚ- r))) ℚ+ (ℚ- s)) ℚ+ s           ≡⟨ ap (_ℚ+ s) (ℚ+-assoc fe r (z ℚ+ (ℚ- r)) (ℚ- s)) ⟩
                (r ℚ+ ((z ℚ+ (ℚ- r)) ℚ+ (ℚ- s))) ℚ+ s           ≡⟨ ap (λ - → (r ℚ+ -) ℚ+ s) (ℚ+-assoc fe z (ℚ- r) (ℚ- s)) ⟩
                (r ℚ+ (z ℚ+ ((ℚ- r) ℚ+ (ℚ- s)))) ℚ+ s           ≡⟨ ap (λ - → (r ℚ+ (z ℚ+ -)) ℚ+ s) (ℚ-minus-dist fe r s) ⟩
                (r ℚ+ (z ℚ+ (ℚ- (r ℚ+ s)))) ℚ+ s                ≡⟨ ap ((λ - → (r ℚ+ (z ℚ+ (ℚ- -))) ℚ+ s)) (e ⁻¹) ⟩
                (r ℚ+ (z ℚ+ (ℚ- t))) ℚ+ s                       ∎
    
  rounded-left-z : (z : ℚ) → (z ∈ L-z ⇔ (∃ t ꞉ ℚ , (z ℚ< t) × t ∈ L-z))
  rounded-left-z z = α , β
   where
    α : z ∈ L-z → (∃ t ꞉ ℚ , (z ℚ< t) × t ∈ L-z)
    α l-z = ∥∥-rec ∃-is-prop δ l-z
     where
      δ : Σ (r , s) ꞉ ℚ × ℚ , r ∈ L-x × s ∈ L-y × (z ≡ r ℚ+ s) → ∃ t ꞉ ℚ , (z ℚ< t) × t ∈ L-z
      δ ((r , s) , l-x , l-y , e) = γ (pr₁ (rounded-left-x r)) (pr₁ (rounded-left-y s))
       where
        γ : (r ∈ L-x → ∃ p ꞉ ℚ , (r ℚ< p) × (p ∈ L-x)) → (s ∈ L-y → ∃ p ꞉ ℚ , (s ℚ< p) × (p ∈ L-y)) → ∃ t ꞉ ℚ , (z ℚ< t) × t ∈ L-z
        γ f g = ζ (binary-choice (f l-x) (g l-y))
         where
          ζ : ∥ (Σ p ꞉ ℚ , (r ℚ< p) × p ∈ L-x) × (Σ q ꞉ ℚ , (s ℚ< q) × (q ∈ L-y)) ∥ → ∃ t ꞉ ℚ , (z ℚ< t) × t ∈ L-z
          ζ bc = ∥∥-functor η bc
           where
            η : (Σ p ꞉ ℚ , (r ℚ< p) × p ∈ L-x)
              × (Σ q ꞉ ℚ , (s ℚ< q) × q ∈ L-y)
              →  Σ t ꞉ ℚ , (z ℚ< t) × t ∈ L-z 
            η ((p , l₁ , sub₁) , q , l₂ , sub₂) = (p ℚ+ q) , (transport (_ℚ< (p ℚ+ q)) (e ⁻¹) (ℚ<-adding r p s q l₁ l₂)) , ∣ (p , q) , (sub₁ , (sub₂ , refl)) ∣
            
    β : ∃ t ꞉ ℚ , (z ℚ< t) × t ∈ L-z → z ∈ L-z
    β exists-t = ∥∥-rec (∈-is-prop L-z z) δ exists-t
     where
      δ : Σ t ꞉ ℚ , (z ℚ< t) × t ∈ L-z → z ∈ L-z
      δ (t , l , l-z) = ∥∥-rec (∈-is-prop L-z z) γ l-z
       where
        γ : (Σ (r , s) ꞉ ℚ × ℚ ,  r ∈ L-x × s ∈ L-y × (t ≡ r ℚ+ s)) → z ∈ L-z
        γ ((r , s) , l-x , l-y , e) = ∣ ((r ℚ+ (z ℚ+ (ℚ- t))) , s) , (pr₂ (rounded-left-x (r ℚ+ (z ℚ+ (ℚ- t))))) I , (l-y , ψ z r t s e) ∣
         where
          I : ∃ r' ꞉ ℚ , (((r ℚ+ (z ℚ+ (ℚ- t))) ℚ< r') × r' ∈ L-x)
          I = ∣ r , (ℚ<-subtraction fe r z t l , l-x) ∣
               
  rounded-right-z : (z : ℚ) → (z ∈ R-z) ⇔ (∃ q ꞉ ℚ , ((q ℚ< z) × (q ∈ R-z)))
  rounded-right-z z = α , β
   where
    α : (z ∈ R-z) → (∃ q ꞉ ℚ , ((q ℚ< z) × (q ∈ R-z)))
    α r-z = ∥∥-rec ∃-is-prop δ r-z
     where
      δ : (Σ (r , s) ꞉ ℚ × ℚ , (r ∈ R-x) × (s ∈ R-y) × (z ≡ (r ℚ+ s))) → (∃ q ꞉ ℚ , (q ℚ< z) × q ∈ R-z)
      δ ((r , s) , r-x , r-y , e) = γ (pr₁ (rounded-right-x r)) (pr₁ (rounded-right-y s))
       where
        γ : (r ∈ R-x → (∃ q ꞉ ℚ , (q ℚ< r) × (q ∈ R-x))) → (s ∈ R-y → (∃ q ꞉ ℚ , (q ℚ< s) × (q ∈ R-y))) → (∃ q ꞉ ℚ , (q ℚ< z) × q ∈ R-z)
        γ f g = ζ (binary-choice (f r-x) (g r-y))
         where
          ζ : ∥ Σ (λ q → (q ℚ< r) × q ∈ R-x) × Σ (λ q → (q ℚ< s) × q ∈ R-y) ∥ → Exists ℚ (λ q → (q ℚ< z) × q ∈ R-z)
          ζ bc = ∥∥-functor η bc
           where
            η : (Σ p ꞉ ℚ , (p ℚ< r) × p ∈ R-x)
              × (Σ q ꞉ ℚ , (q ℚ< s) × q ∈ R-y)
              → Σ t ꞉ ℚ , (t ℚ< z) × t ∈ R-z
            η ((p , l₁ , sub₁) , q , l₂ , sub₂) = (p ℚ+ q) , (transport ((p ℚ+ q) ℚ<_) (e ⁻¹) (ℚ<-adding p r q s l₁ l₂) , ∣ (p , q) , (sub₁ , (sub₂ , refl)) ∣)

    β : ∃ t ꞉ ℚ , (t ℚ< z) × t ∈ R-z → z ∈ R-z
    β exists-t = ∥∥-rec (∈-is-prop R-z z) δ exists-t
     where
      δ : Σ t ꞉ ℚ , (t ℚ< z) × t ∈ R-z → z ∈ R-z
      δ (t , l , r-z) = ∥∥-rec (∈-is-prop R-z z) γ r-z
       where
        γ : (Σ (r , s) ꞉ ℚ × ℚ , (r ∈ R-x) × s ∈ R-y × (t ≡ r ℚ+ s)) → z ∈ R-z
        γ ((r , s) , r-x , r-y , e) = ∣ ((r ℚ+ (z ℚ+ (ℚ- t))) , s) , ((pr₂ (rounded-right-x (r ℚ+ (z ℚ+ (ℚ- t))))) I , (r-y , ψ z r t s e)) ∣
         where
          I : ∃ r' ꞉ ℚ , (r' ℚ< (r ℚ+ (z ℚ+ (ℚ- t)))) × (r' ∈ R-x)
          I = ∣ r , (ℚ<-subtraction' fe r t z l , r-x) ∣
          
  disjoint-z : (p q : ℚ) → (p ∈ L-z) × (q ∈ R-z) → p ℚ< q
  disjoint-z p q (α , β) = ∥∥-rec (ℚ<-is-prop p q) δ (binary-choice α β)
   where
    δ : (Σ (r , s) ꞉ ℚ × ℚ , r ∈ L-x × s ∈ L-y × (p ≡ r ℚ+ s))
      × (Σ (r' , s') ꞉ ℚ × ℚ , r' ∈ R-x × s' ∈ R-y × (q ≡ r' ℚ+ s'))
      → p ℚ< q
    δ (((r , s) , l-x , l-y , e₁) , ((r' , s') , r-x , r-y , e₂)) = transport₂ _ℚ<_ (e₁ ⁻¹) (e₂ ⁻¹) (ℚ<-adding r r' s s' I II)
     where
      I : r ℚ< r'
      I = disjoint-x r r' (l-x , r-x) 

      II : s ℚ< s'
      II = disjoint-y s s' (l-y , r-y)

  located-z : (p q : ℚ) → p ℚ< q → (p ∈ L-z) ∨ (q ∈ R-z)
  located-z p q l = I (ℚ<-subtraction'' fe p q l)
   where
    I : (Σ k ꞉ ℚ , (zero-ℚ ℚ< k) × (k ≡ (q ℚ+ (ℚ- p)))) → (p ∈ L-z) ∨ (q ∈ R-z)
    I (k , l' , e') = II (ℝ-arithmetically-located (((L-x , R-x) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x)) k l') -- arithmetically located functoion goes here
     where
      II : (∃ (e , t) ꞉ ℚ × ℚ , e ∈ L-x × t ∈ R-x × (zero-ℚ ℚ< (t ℚ+ (ℚ- e)) ) × ((t ℚ+ (ℚ- e)) ℚ< k)) → (p ∈ L-z) ∨ (q ∈ R-z)
      II = ∥∥-rec ∨-is-prop δ
       where
        δ : (Σ (e , t) ꞉ ℚ × ℚ , e ∈ L-x × t ∈ R-x × (zero-ℚ ℚ< (t ℚ+ (ℚ- e)) ) × ((t ℚ+ (ℚ- e)) ℚ< k)) → (p ∈ L-z) ∨ (q ∈ R-z)
        δ ((e , t) , l-x , r-x , l₁ , l₂) = ∥∥-functor η (located-y x y l₅)
         where
          α : (p ℚ+ (ℚ- e)) ℚ< (q ℚ+ (ℚ- t))
          α = transport₂ _ℚ<_ iii iv ii
           where
            i : (t ℚ+ (ℚ- e)) ℚ< (q ℚ+ (ℚ- p))
            i = transport ((t ℚ+ (ℚ- e)) ℚ<_) e' l₂
            ii : ((t ℚ+ (ℚ- e)) ℚ+ (p ℚ+ (ℚ- t))) ℚ< ((q ℚ+ (ℚ- p)) ℚ+ (p ℚ+ (ℚ- t)))
            ii = ℚ-addition-preserves-order (t ℚ+ (ℚ- e)) (q ℚ+ (ℚ- p)) (p ℚ+ (ℚ- t)) i  
            iii : ((t ℚ+ (ℚ- e)) ℚ+ (p ℚ+ (ℚ- t))) ≡ (p ℚ+ (ℚ- e))
            iii = ((t ℚ+ (ℚ- e)) ℚ+ (p ℚ+ (ℚ- t))) ≡⟨ ap₂ _ℚ+_ (ℚ+-comm t (ℚ- e)) (ℚ+-comm p (ℚ- t)) ⟩
                  ((ℚ- e) ℚ+ t) ℚ+ ((ℚ- t) ℚ+ p)    ≡⟨ ℚ+-assoc fe ((ℚ- e) ℚ+ t) (ℚ- t) p ⁻¹ ⟩
                  ((((ℚ- e) ℚ+ t) ℚ+ (ℚ- t)) ℚ+ p)  ≡⟨ ap (_ℚ+ p) (ℚ+-assoc fe (ℚ- e) t (ℚ- t)) ⟩
                  (((ℚ- e) ℚ+ (t ℚ+ (ℚ- t))) ℚ+ p)  ≡⟨ ap (λ - → ((ℚ- e) ℚ+ -) ℚ+ p) (ℚ-inverse-sum-to-zero fe t) ⟩
                  (((ℚ- e) ℚ+ zero-ℚ) ℚ+ p)         ≡⟨ ap (_ℚ+ p) (ℚ-zero-right-neutral fe (ℚ- e)) ⟩
                  (ℚ- e) ℚ+ p                       ≡⟨ ℚ+-comm (ℚ- e) p ⟩
                  p ℚ+ (ℚ- e) ∎
            iv :  ((q ℚ+ (ℚ- p)) ℚ+ (p ℚ+ (ℚ- t))) ≡ (q ℚ+ (ℚ- t))
            iv = (((q ℚ+ (ℚ- p)) ℚ+ (p ℚ+ (ℚ- t)))) ≡⟨ ℚ+-assoc fe (q ℚ+ (ℚ- p)) p (ℚ- t) ⁻¹ ⟩
                 (((q ℚ+ (ℚ- p)) ℚ+ p) ℚ+ (ℚ- t))   ≡⟨ ap (_ℚ+ (ℚ- t)) (ℚ+-assoc fe q (ℚ- p) p ) ⟩
                 ((q ℚ+ ((ℚ- p) ℚ+ p)) ℚ+ (ℚ- t))   ≡⟨ ap (λ - → (q ℚ+ -) ℚ+ (ℚ- t)) (ℚ-inverse-sum-to-zero' fe p ) ⟩
                 ((q ℚ+ zero-ℚ) ℚ+ (ℚ- t))          ≡⟨ ap (_ℚ+ (ℚ- t)) (ℚ-zero-right-neutral fe q ) ⟩
                 q ℚ+ (ℚ- t) ∎

          β : Σ y ꞉ ℚ , ((p ℚ+ (ℚ- e)) ℚ< y) × (y ℚ< (q ℚ+ (ℚ- t))) 
          β = rounded-lemma (p ℚ+ (ℚ- e)) (q ℚ+ (ℚ- t)) α
          y = pr₁ β
          l₄ = pr₁ (pr₂ β)
          γ : Σ x ꞉ ℚ , (p ℚ+ (ℚ- e)) ℚ< x × (x ℚ< y) 
          γ = rounded-lemma (p ℚ+ (ℚ- e)) y l₄
          x = pr₁ γ
          l₅ = pr₂ (pr₂ γ)
  
          helper : (∃ (r , s) ꞉ ℚ × ℚ , r ∈ L-x × s ∈ L-y × p ℚ< (r ℚ+ s) → ∃ (r , s) ꞉ ℚ × ℚ , r ∈ L-x × s ∈ L-y × (p ≡ r ℚ+ s))
                 × ((∃ (r , s) ꞉ ℚ × ℚ , r ∈ R-x × s ∈ R-y × ((r ℚ+ s)) ℚ< q) → (∃ (r , s) ꞉ ℚ × ℚ , r ∈ R-x × s ∈ R-y × (q ≡ r ℚ+ s)))
          helper = ℝ-addition-lemma ((L-x , R-x) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x) ((L-y , R-y) , inhabited-left-y , inhabited-right-y , rounded-left-y , rounded-right-y , disjoint-y , located-y) p q

          helper₁ = pr₁ helper
          helper₂ = pr₂ helper
   
          η : (x ∈ L-y) ∔ (y ∈ R-y) → p ∈ L-z ∔ q ∈ R-z 
          η (inl x-l) = inl (helper₁ ∣ (e , x) , (l-x , x-l , i) ∣)
           where
            i : p ℚ< (e ℚ+ x)
            i = transport₂ _ℚ<_ ii iii (ℚ-addition-preserves-order (p ℚ+ (ℚ- e)) x e (pr₁ (pr₂ γ)))
             where
              ii : (p ℚ+ (ℚ- e)) ℚ+ e ≡ p
              ii = (p ℚ+ (ℚ- e)) ℚ+ e    ≡⟨ ℚ+-assoc fe p (ℚ- e) e ⟩
                    p ℚ+ ((ℚ- e) ℚ+ e)   ≡⟨ ap (p ℚ+_) (ℚ-inverse-sum-to-zero' fe e) ⟩
                    p ℚ+ zero-ℚ          ≡⟨ ℚ-zero-right-neutral fe p ⟩
                    p                    ∎
              iii : x ℚ+ e ≡ (e ℚ+ x)
              iii = ℚ+-comm x e
          η (inr y-r) = inr (helper₂ ∣ (t , y) , (r-x , y-r , i) ∣)
           where
            i : (t ℚ+ y) ℚ< q
            i = transport₂ _ℚ<_ ii iii (ℚ-addition-preserves-order y (q ℚ+ (ℚ- t)) t (pr₂ (pr₂ β)))
             where
              ii : y ℚ+ t ≡ t ℚ+ y
              ii = ℚ+-comm y t
              iii : (q ℚ+ (ℚ- t)) ℚ+ t ≡ q
              iii = (q ℚ+ (ℚ- t)) ℚ+ t  ≡⟨ ℚ+-assoc fe q (ℚ- t) t ⟩
                     q ℚ+ ((ℚ- t) ℚ+ t) ≡⟨ ap (q ℚ+_) (ℚ-inverse-sum-to-zero' fe t) ⟩
                     q ℚ+ zero-ℚ        ≡⟨ ℚ-zero-right-neutral fe q ⟩
                     q                  ∎
          
-}


