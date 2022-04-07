Andrew Sneap

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) -- TypeTopology

open import OrderNotation
open import UF-Base -- TypeTopology
open import UF-PropTrunc -- TypeTopology
open import UF-Subsingletons --TypeTopology
open import UF-FunExt -- TypeTopology
open import UF-Powerset -- TypeTopology

open import Rationals
open import RationalsOrder
open import RationalsMultiplication

module DedekindRealsMultiplication
         (pe : Prop-Ext) 
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
       where

open import DedekindReals pe pt fe
open PropositionalTruncation pt

open import RationalsMinMax fe

transport₄ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {U : 𝓤' ̇} → (A : X → Y → Z → U → 𝓣 ̇ )
             {x x' : X} {y y' : Y} {z z' : Z} {u u' : U}
           → x ≡ x' → y ≡ y' → z ≡ z' → u ≡ u' → A x y z u → A x' y' z' u'
transport₄ A refl refl refl refl = id

_*ℝ_ : ℝ → ℝ → ℝ
x *ℝ y  = (L , R) , {!!}
 where
  L : ℚ-subset-of-propositions
  L p = (∃ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a < x × x < b × c < y × y < d × p < min₄ (a * c) (a * d) (b * c) (b * d)) , ∃-is-prop
  R : ℚ-subset-of-propositions
  R q = (∃ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a < x × x < b × c < y × y < d × max₄ (a * c) (a * d) (b * c) (b * d) < q) , ∃-is-prop


infixl 31 _*ℝ_

ℝ*-comm : (x y : ℝ) → x *ℝ y ≡ y *ℝ x
ℝ*-comm x y = ℝ-equality-from-left-cut' (x *ℝ y) (y *ℝ x) left right
 where
  generalised : (x y : ℝ) (p : ℚ) → Σ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a < x × x < b × c < y × y < d × p < min₄ (a * c) (a * d) (b * c) (b * d)
                                  → Σ (c , d , a , b) ꞉ ℚ × ℚ × ℚ × ℚ , c < y × y < d × a < x × x < b × p < min₄ (c * a) (c * b) (d * a) (d * b)
  generalised x y p ((a , b , c , d) , a<x , x<b , c<y , y<d , p<m) = (c , d , a , b) , c<y , y<d , a<x , x<b , I
   where
    I : p < min₄ (c * a) (c * b) (d * a) (d * b)
    I = transport (p <_) III p<m
     where
      III : min₄ (a * c) (a * d) (b * c) (b * d) ≡ min₄ (c * a) (c * b) (d * a) (d * b) 
      III = min₄ (a * c) (a * d) (b * c) (b * d)            ≡⟨ ap (min₄ (a * c) (a * d) (b * c)) (ℚ*-comm b d)                   ⟩
            min₄ (a * c) (a * d) (b * c) (d * b)            ≡⟨ ap (λ α → min α (d * b)) (min-assoc (a * c) (a * d) (b * c))      ⟩
            min (min (a * c) (min (a * d) (b * c))) (d * b) ≡⟨ ap (λ α → min (min (a * c) α) (d * b)) (min-comm (a * d) (b * c)) ⟩
            min (min (a * c) (min (b * c) (a * d))) (d * b) ≡⟨ ap (λ α → min α (d * b)) (min-assoc (a * c) (b * c) (a * d) ⁻¹)   ⟩
            min₄ (a * c) (b * c) (a * d) (d * b)            ≡⟨ ap (λ α → min₄ α (b * c) (a * d) (d * b)) (ℚ*-comm a c)           ⟩
            min₄ (c * a) (b * c) (a * d) (d * b)            ≡⟨ ap (λ α → min₄ (c * a) α (a * d) (d * b)) (ℚ*-comm b c)           ⟩
            min₄ (c * a) (c * b) (a * d) (d * b)            ≡⟨ ap (λ α → min₄ (c * a) (c * b) α (d * b)) (ℚ*-comm a d)           ⟩   
            min₄ (c * a) (c * b) (d * a) (d * b)            ∎
            
  left : (p : ℚ) → p < x *ℝ y → p < y *ℝ x
  left p = ∥∥-functor (generalised x y p)
              
  right : (p : ℚ) → p < y *ℝ x → p < x *ℝ y
  right p = ∥∥-functor (generalised y x p)

ℝ*-assoc : (x y z : ℝ) → x *ℝ y *ℝ z ≡ x *ℝ (y *ℝ z)
ℝ*-assoc x y z = ℝ-equality-from-left-cut' (x *ℝ y *ℝ z) (x *ℝ (y *ℝ z)) left right
 where
  left : (p : ℚ) → p < x *ℝ y *ℝ z → p < x *ℝ (y *ℝ z)
  left p = ∥∥-functor I
   where
    I : {!!}
    I = {!!}
  right : {!!}
  right = {!!}
