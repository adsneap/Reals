\begin{code}
{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆)  -- TypeTopology

open import UF-Base
open import UF-FunExt -- TypeTopology
open import UF-Powerset -- TypeTopology
open import UF-PropTrunc -- TypeTopology
open import UF-Subsingletons -- TypeTopology

open import MetricSpaceAltDef
open import RationalsAddition
open import Rationals
open import RationalsAbs
open import RationalsNegation
open import RationalsOrder

module MetricSpaceDedekindReals
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
 where

open PropositionalTruncation pt

open import DedekindReals pt fe
open import MetricSpaceRationals fe
open import RationalsMinMax fe

B-ℝ : (x y : ℝ) → (ε : ℚ) → 0ℚ < ε → 𝓤₀ ̇
B-ℝ ((Lx , Rx) , _) ((Ly , Ry) , _) ε l =
 ∃ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , p ∈ Lx × u ∈ Ly × q ∈ Rx × v ∈ Ry × B-ℚ (min p u) (max q v) ε l
{-
ℝ-m1a : m1a ℝ B-ℝ
ℝ-m1a ((Lx , Rx) , isCutx) ((Ly , Ry) , isCuty) f = 𝟘-elim { 𝓤₁ } { 𝓤₀ } (∥∥-rec 𝟘-is-prop I (f 1ℚ {!!}))
 where
  I : (Σ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , p ∈ Lx × u ∈ Ly × q ∈ Rx × v ∈ Ry × B-ℚ (min p u) (max q v) 1ℚ {!!}) → 𝟘
  I ((p , q , u , v) , pLx , uLy , qRx , vRy , B) = third second
   where
    first : 0ℚ ≤ abs (ℚ-metric (min p u) (max q v))
    first = ℚ-abs-is-positive (ℚ-metric (min p u) (max q v))
    second : (0ℚ < abs (ℚ-metric (min p u) (max q v))) ∔ (0ℚ ≡ abs (ℚ-metric (min p u) (max q v)))
    second = ℚ≤-split fe 0ℚ (abs (ℚ-metric (min p u) (max q v))) first
    third : (0ℚ < abs (ℚ-metric (min p u) (max q v))) ∔ (0ℚ ≡ abs (ℚ-metric (min p u) (max q v))) → 𝟘
    third (inl l) = {!!}
     where
      II :  (∃ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , p ∈ Lx × u ∈ Ly × q ∈ Rx × v ∈ Ry × B-ℚ (min p u) (max q v) {!abs (ℚ-metric (min p u) (max q v))!} {!!})
      II = f (abs (ℚ-metric (min p u) (max q v))) l
    third (inr r) = {!!}
  conclusion : ((Lx , Rx) , isCutx) ≡ ((Ly , Ry) , isCuty)
  conclusion = ℝ-equality (((Lx , Rx) , isCutx)) (((Ly , Ry) , isCuty)) α β
   where
    α : Lx ≡ Ly
    α = subset-extensionality pe fe γ δ
     where
      γ : Lx ⊆ Ly
      γ k k-Lx = {!!}
      δ : Ly ⊆ Lx
      δ = {!!}
    β : {!!}
    β = {!!}
-}
{-

m1b-lemma : (q ε : ℚ) → 0ℚ < q × q < ε → abs q < ε
m1b-lemma q ε (l₁ , l₂) = {!!}
 where
  I : 0ℚ < ε 
  I = ℚ<-trans 0ℚ q ε l₁ l₂
  II : ((- ε) < 0ℚ)
  II = {!!}
  III : (- ε) < q
  III = ℚ<-trans (- ε) 0ℚ q II l₁
  IV : abs q ≤ ε
  IV = ℚ≤-to-abs fe q ε ((ℚ<-coarser-than-≤ (- ε) q III) , ℚ<-coarser-than-≤ q ε l₂) 
-- Since (- ε ℚ< zero-ℚ) and then by a function above



ℝ-m1b : m1b ℝ B-ℝ
ℝ-m1b ((L , R) , iscut) ε l = ∥∥-functor I (ℝ-arithmetically-located ((L , R) , iscut) ε l)
 where
  I : (Σ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × (0ℚ < (y - x)) × ((y - x) < ε)) → Σ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , p ∈ L × u ∈ L × q ∈ R × v ∈ R × B-ℚ (min p u) (max q v) ε l
  I ((x , y) , Lx , Ry , (l₁ , l₂)) = (x , y , x , y) , Lx , Lx , Ry , Ry , transport₂ (λ α β → B-ℚ α β ε l) (min-refl x ⁻¹) (max-refl y ⁻¹) iii
   where
    i : ℚ-metric y x < ε 
    i = ? -- m1b-lemma (y - x) ε (l₁ , l₂)
    ii : ℚ-metric y x ≡ ℚ-metric x y
    ii = ℚ-metric-commutes y x
    iii : ℚ-metric x y < ε
    iii = transport (_< ε) ii i

-}

ℝ-m2 : m2 ℝ B-ℝ
ℝ-m2 ((Lx , Rx) , _) ((Ly , Ry) , _) ε l B = ∥∥-functor α B
 where
  α : Σ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , p ∈ Lx × u ∈ Ly × q ∈ Rx × v ∈ Ry × B-ℚ (min p u) (max q v) ε l
    → Σ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , p ∈ Ly × u ∈ Lx × q ∈ Ry × v ∈ Rx × B-ℚ (min p u) (max q v) ε l
  α ((p , q , u , v) , pLx , uLy , qRx , vRy , B) = (u , v , p , q) , uLy , pLx , vRy , qRx , transport₂ (λ α β → B-ℚ α β ε l) (min-comm p u) (max-comm q v) B

ℝ-m3 : m3 ℝ B-ℝ
ℝ-m3 ((Lx , Rx) , iscutx) ((Ly , Ry) , iscuty) ε₁ ε₂ l₁ l₂ l₃ B = ∥∥-functor I B
 where
  I : Σ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , p ∈ Lx × u ∈ Ly × q ∈ Rx × v ∈ Ry × B-ℚ (min p u) (max q v) ε₁ l₁
    → Σ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , p ∈ Lx × u ∈ Ly × q ∈ Rx × v ∈ Ry × B-ℚ (min p u) (max q v) ε₂ l₂
  I ((p , q , u , v) , pLx , uLy , qRx , vRy , B) = (p , q , u , v) , pLx , uLy , qRx , vRy , ℚ<-trans (ℚ-metric (min p u) (max q v)) ε₁ ε₂ B l₃
  
ℝ-m4 : m4 ℝ B-ℝ
ℝ-m4 ((Lx , Rx) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x)
     ((Ly , Ry) , inhabited-left-y , inhabited-right-y , rounded-left-y , rounded-right-y , disjoint-y , located-y)
     ((Lz , Rz) , inhabited-left-z , inhabited-right-z , rounded-left-z , rounded-right-z , disjoint-z , located-z) ε₁ ε₂ l₁ l₂ B₁ B₂ = ∥∥-functor I (binary-choice B₁ B₂)
 where
  I : (Σ (p₁ , q₁ , u₁ , v₁) ꞉ ℚ × ℚ × ℚ × ℚ , p₁ ∈ Lx × u₁ ∈ Ly × q₁ ∈ Rx × v₁ ∈ Ry × B-ℚ (min p₁ u₁) (max q₁ v₁) ε₁ l₁)
    × (Σ (p₂ , q₂ , u₂ , v₂) ꞉ ℚ × ℚ × ℚ × ℚ , p₂ ∈ Ly × u₂ ∈ Lz × q₂ ∈ Ry × v₂ ∈ Rz × B-ℚ (min p₂ u₂) (max q₂ v₂) ε₂ l₂)
    → Σ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , p ∈ Lx × u ∈ Lz × q ∈ Rx × v ∈ Rz × B-ℚ (min p u) (max q v) (ε₁ + ε₂) (ℚ<-adding-zero ε₁ ε₂ l₁ l₂)
  I (((p₁ , q₁ , u₁ , v₁) , p₁Lx , u₁Ly , q₁Rx , v₁Ry , B₃) , ((p₂ , q₂ , u₂ , v₂) , p₂Ly , u₂Lz , q₂Ry , v₂Rz , B₄))
   = (min p₁ p₂ , max q₁ q₂ , min u₁ u₂ , max v₁ v₂) , II (min-to-≤ p₁ p₂) (min-to-≤ u₁ u₂) (max-to-≤ q₁ q₂) (max-to-≤ v₁ v₂)
    where

     III : (ℚ-metric (min p₁ u₁) (max q₁ v₁) + ℚ-metric (min p₂ u₂) (max q₂ v₂)) < (ε₁ + ε₂)
     III = ℚ<-adding (ℚ-metric (min p₁ u₁) (max q₁ v₁)) ε₁ (ℚ-metric (min p₂ u₂) (max q₂ v₂)) ε₂ B₃ B₄

     IV : ℚ-metric (min p₁ u₁ - max q₁ v₁) (max q₂ v₂ - min p₂ u₂) ≤ (ℚ-metric (min p₁ u₁) (max q₁ v₁) + ℚ-metric (min p₂ u₂) (max q₂ v₂))
     IV = {!!}
     {-
     δ : min (min p₁ u₁) (min p₂ u₂) ≡ min (min p₁ p₂) (min u₁ u₂)
     δ = {!!}
     -}
     ψ : max (max q₁ v₁) (max q₂ v₂) ≡ max (max q₁ q₂) (max v₁ v₂)
     ψ = {!!}
     {-
     IV : ℚ-metric (min (min p₁ u₁) (min p₂ u₂)) (max (max q₁ v₁) (max q₂ v₂)) ≤ ℚ-metric (min p₁ u₁) (max q₁ v₁) + ℚ-metric (min p₂ u₂) (max q₂ v₂)
     IV = {!!}
      where
       i : ℚ-metric (min (min p₁ u₁) (min p₂ u₂)) (max (max q₁ v₁) (max q₂ v₂)) ≡ ℚ-metric (min (min p₁ p₂) (min u₁ u₂)) (max (max q₁ q₂) (max v₁ v₂))
       i = ap₂ ℚ-metric δ ψ 
     
     V : ℚ-metric (min (min p₁ u₁) (min p₂ u₂)) (max (max q₁ v₁) (max q₂ v₂)) ≤ ℚ-metric (min p₁ u₁) (max q₁ v₁) + ℚ-metric (min p₂ u₂) (max q₂ v₂)
       → B-ℚ (min (min p₁ p₂) (min u₁ u₂)) (max (max q₁ q₂) (max v₁ v₂)) (ε₁ + ε₂) (ℚ<-adding-zero ε₁ ε₂ l₁ l₂)
     V = {!!}
     -}
     

     {-
     γ : Σ a ꞉ ℚ , a ≡ min (min p₁ p₂) (min u₁ u₂)
       → Σ b ꞉ ℚ , b ≡ max (max q₁ q₂) (max v₁ v₂)
       → B-ℚ (min (min p₁ p₂) (min u₁ u₂)) (max (max q₁ q₂) (max v₁ v₂)) (ε₁ + ε₂) (ℚ<-adding-zero ε₁ ε₂ l₁ l₂)
     γ = {!!}
     -}
     α : B-ℚ (min (min p₁ p₂) (min u₁ u₂)) (max (max q₁ q₂) (max v₁ v₂)) (ε₁ + ε₂) (ℚ<-adding-zero ε₁ ε₂ l₁ l₂)
     α = {!!}
      where 
       {-
       β : (min p₁ p₂ ≤ min u₁ u₂) × (min (min p₁ p₂) (min u₁ u₂) ≡ min p₁ p₂)
         ∔ (min u₁ u₂ ≤ min p₁ p₂) × (min (min p₁ p₂) (min u₁ u₂) ≡ min u₁ u₂)
         → (max q₁ q₂ ≤ max v₁ v₂) × (max (max q₁ q₂) (max v₁ v₂) ≡ max v₁ v₂)
         ∔ (max v₁ v₂ ≤ max q₁ q₂) × (max (max q₁ q₂) (max v₁ v₂) ≡ max q₁ q₂)
         → B-ℚ (min (min p₁ p₂) (min u₁ u₂)) (max (max q₁ q₂) (max v₁ v₂)) (ε₁ + ε₂) (ℚ<-adding-zero ε₁ ε₂ l₁ l₂)
       β (inl (a , a')) (inl (b , b')) = {!!} -- γ (min-to-≤ p₁ p₂) (max-to-≤ v₁ v₂)
        where
       
         
         δ : {!!} → {!!}
         δ i = transport (_< (ε₁ + ε₂)) i (ℚ<-adding (ℚ-metric (min p₁ u₁) (max q₁ v₁)) ε₁ (ℚ-metric (min p₂ u₂) (max q₂ v₂)) ε₂ B₃ B₄)
         γ : (p₁ ≤ p₂) × (min p₁ p₂ ≡ p₁) ∔ (p₂ ≤ p₁) × (min p₁ p₂ ≡ p₂)
           → (v₁ ≤ v₂) × (max v₁ v₂ ≡ v₂) ∔ (v₂ ≤ v₁) × (max v₁ v₂ ≡ v₁)
           → B-ℚ (min (min p₁ p₂) (min u₁ u₂)) (max (max q₁ q₂) (max v₁ v₂)) (ε₁ + ε₂) (ℚ<-adding-zero ε₁ ε₂ l₁ l₂)
         γ (inl (c , c')) (inl (d , d')) = δ {!!} -- transport (_< (ε₁ + ε₂)) {!!} (ℚ<-adding (ℚ-metric (min p₁ u₁) (max q₁ v₁)) ε₁ (ℚ-metric (min p₂ u₂) (max q₂ v₂)) ε₂ B₃ B₄)
         γ (inl (c , c')) (inr (d , d')) = {!!} -- transport (_< (ε₁ + ε₂)) {!!} (ℚ<-adding (ℚ-metric (min p₁ u₁) (max q₁ v₁)) ε₁ (ℚ-metric (min p₂ u₂) (max q₂ v₂)) ε₂ B₃ B₄)
         γ (inr (c , c')) (inl (d , d')) = {!!}
         γ (inr (c , c')) (inr (d , d')) = {!!}
       β (inl (a , a')) (inr (b , b')) = {!!}
       β (inr (a , a')) (inl (b , b')) = {!!}
       β (inr (a , a')) (inr (b , b')) = {!!}
     -}
     help : {!!}
     help = {!!}
     
     II : (p₁ ≤ p₂) × (min p₁ p₂ ≡ p₁) ∔ (p₂ ≤ p₁) × (min p₁ p₂ ≡ p₂)
        → (u₁ ≤ u₂) × (min u₁ u₂ ≡ u₁) ∔ (u₂ ≤ u₁) × (min u₁ u₂ ≡ u₂)
        → (q₁ ≤ q₂) × (max q₁ q₂ ≡ q₂) ∔ (q₂ ≤ q₁) × (max q₁ q₂ ≡ q₁)
        → (v₁ ≤ v₂) × (max v₁ v₂ ≡ v₂) ∔ (v₂ ≤ v₁) × (max v₁ v₂ ≡ v₁)
        → min p₁ p₂ ∈ Lx ×  min u₁ u₂ ∈ Lz × max q₁ q₂ ∈ Rx ×  max v₁ v₂ ∈ Rz
        × B-ℚ (min (min p₁ p₂) (min u₁ u₂)) (max (max q₁ q₂) (max v₁ v₂)) (ε₁ + ε₂) (ℚ<-adding-zero ε₁ ε₂ l₁ l₂)
     II (inl (a , a')) (inl (b , b')) (inl (c , c')) (inl (d , d')) = transport (_∈ Lx) (a' ⁻¹) p₁Lx
                                                                    , transport (_∈ Lz) (b' ⁻¹) (rounded-left-a Lz rounded-left-z u₁ u₂ b u₂Lz)
                                                                    , transport (_∈ Rx) (c' ⁻¹) (rounded-right-a Rx rounded-right-x q₁ q₂ c q₁Rx)
                                                                    , transport (_∈ Rz) (d' ⁻¹) v₂Rz
                                                                    , X (min-to-≤ (min p₁ p₂) (min u₁ u₂)) (max-to-≤ (max q₁ q₂) (max v₁ v₂))
      where
       X : (min p₁ p₂ ≤ min u₁ u₂) × (min (min p₁ p₂) (min u₁ u₂) ≡ min p₁ p₂)
         ∔ (min u₁ u₂ ≤ min p₁ p₂) × (min (min p₁ p₂) (min u₁ u₂) ≡ min u₁ u₂)
         → (max q₁ q₂ ≤ max v₁ v₂) × (max (max q₁ q₂) (max v₁ v₂) ≡ max v₁ v₂)
         ∔ (max v₁ v₂ ≤ max q₁ q₂) × (max (max q₁ q₂) (max v₁ v₂) ≡ max q₁ q₂)
         → B-ℚ (min (min p₁ p₂) (min u₁ u₂)) (max (max q₁ q₂) (max v₁ v₂)) (ε₁ + ε₂) (ℚ<-adding-zero ε₁ ε₂ l₁ l₂)
       X (inl (e , e')) (inl (f , f')) = {!!}
       X (inl x) (inr x₁) = {!!}
       X (inr x) (inl x₁) = {!!}
       X (inr x) (inr x₁) = {!!}
     II (inl (a , a')) (inl (b , b')) (inl (c , c')) (inr (d , d')) = transport (_∈ Lx) (a' ⁻¹) p₁Lx
                                                                    , transport (_∈ Lz) (b' ⁻¹) (rounded-left-a Lz rounded-left-z u₁ u₂ b u₂Lz)
                                                                    , transport (_∈ Rx) (c' ⁻¹) (rounded-right-a Rx rounded-right-x q₁ q₂ c q₁Rx)
                                                                    , transport (_∈ Rz) (d' ⁻¹) (rounded-right-a Rz rounded-right-z v₂ v₁ d v₂Rz)
                                                                    , α
     II (inl (a , a')) (inl (b , b')) (inr (c , c')) (inl (d , d')) = transport (_∈ Lx) (a' ⁻¹) p₁Lx
                                                                    , transport (_∈ Lz) (b' ⁻¹) (rounded-left-a Lz rounded-left-z u₁ u₂ b u₂Lz)
                                                                    , transport (_∈ Rx) (c' ⁻¹) q₁Rx
                                                                    , transport (_∈ Rz) (d' ⁻¹) v₂Rz
                                                                    , α
     II (inl (a , a')) (inl (b , b')) (inr (c , c')) (inr (d , d')) = transport (_∈ Lx) (a' ⁻¹) p₁Lx
                                                                    , transport (_∈ Lz) (b' ⁻¹) (rounded-left-a Lz rounded-left-z u₁ u₂ b u₂Lz)
                                                                    , transport (_∈ Rx) (c' ⁻¹) q₁Rx
                                                                    , transport (_∈ Rz) (d' ⁻¹) ((rounded-right-a Rz rounded-right-z v₂ v₁ d v₂Rz))
                                                                    , α
     II (inl (a , a')) (inr (b , b')) (inl (c , c')) (inl (d , d')) = transport (_∈ Lx) (a' ⁻¹) p₁Lx
                                                                    , transport (_∈ Lz) (b' ⁻¹) u₂Lz
                                                                    , transport (_∈ Rx) (c' ⁻¹) (rounded-right-a Rx rounded-right-x q₁ q₂ c q₁Rx)
                                                                    , transport (_∈ Rz) (d' ⁻¹) v₂Rz
                                                                    , α
     II (inl (a , a')) (inr (b , b')) (inl (c , c')) (inr (d , d')) = transport (_∈ Lx) (a' ⁻¹) p₁Lx
                                                                    , transport (_∈ Lz) (b' ⁻¹) u₂Lz
                                                                    , transport (_∈ Rx) (c' ⁻¹) (rounded-right-a Rx rounded-right-x q₁ q₂ c q₁Rx)
                                                                    , transport (_∈ Rz) (d' ⁻¹) ((rounded-right-a Rz rounded-right-z v₂ v₁ d v₂Rz))
                                                                    , α
     II (inl (a , a')) (inr (b , b')) (inr (c , c')) (inl (d , d')) = transport (_∈ Lx) (a' ⁻¹) p₁Lx
                                                                    , transport (_∈ Lz) (b' ⁻¹) u₂Lz
                                                                    , transport (_∈ Rx) (c' ⁻¹) q₁Rx
                                                                    , transport (_∈ Rz) (d' ⁻¹) v₂Rz
                                                                    , α
     II (inl (a , a')) (inr (b , b')) (inr (c , c')) (inr (d , d')) = transport (_∈ Lx) (a' ⁻¹) p₁Lx
                                                                    , transport (_∈ Lz) (b' ⁻¹) u₂Lz
                                                                    , transport (_∈ Rx) (c' ⁻¹) q₁Rx
                                                                    , transport (_∈ Rz) (d' ⁻¹) ((rounded-right-a Rz rounded-right-z v₂ v₁ d v₂Rz))
                                                                    , α
     II (inr (a , a')) (inl (b , b')) (inl (c , c')) (inl (d , d')) = transport (_∈ Lx) (a' ⁻¹) (rounded-left-a Lx rounded-left-x p₂ p₁ a p₁Lx)
                                                                    , transport (_∈ Lz) (b' ⁻¹) (rounded-left-a Lz rounded-left-z u₁ u₂ b u₂Lz)
                                                                    , transport (_∈ Rx) (c' ⁻¹) (rounded-right-a Rx rounded-right-x q₁ q₂ c q₁Rx)
                                                                    , transport (_∈ Rz) (d' ⁻¹) v₂Rz
                                                                    , α
     II (inr (a , a')) (inl (b , b')) (inl (c , c')) (inr (d , d')) = transport (_∈ Lx) (a' ⁻¹) (rounded-left-a Lx rounded-left-x p₂ p₁ a p₁Lx)
                                                                    , transport (_∈ Lz) (b' ⁻¹) (rounded-left-a Lz rounded-left-z u₁ u₂ b u₂Lz)
                                                                    , transport (_∈ Rx) (c' ⁻¹) (rounded-right-a Rx rounded-right-x q₁ q₂ c q₁Rx)
                                                                    , transport (_∈ Rz) (d' ⁻¹) ((rounded-right-a Rz rounded-right-z v₂ v₁ d v₂Rz))
                                                                    , α
     II (inr (a , a')) (inl (b , b')) (inr (c , c')) (inl (d , d')) = transport (_∈ Lx) (a' ⁻¹) (rounded-left-a Lx rounded-left-x p₂ p₁ a p₁Lx)
                                                                    , transport (_∈ Lz) (b' ⁻¹) (rounded-left-a Lz rounded-left-z u₁ u₂ b u₂Lz)
                                                                    , transport (_∈ Rx) (c' ⁻¹) q₁Rx
                                                                    , transport (_∈ Rz) (d' ⁻¹) v₂Rz
                                                                    , α
     II (inr (a , a')) (inl (b , b')) (inr (c , c')) (inr (d , d')) = transport (_∈ Lx) (a' ⁻¹) (rounded-left-a Lx rounded-left-x p₂ p₁ a p₁Lx)
                                                                    , transport (_∈ Lz) (b' ⁻¹) (rounded-left-a Lz rounded-left-z u₁ u₂ b u₂Lz)
                                                                    , transport (_∈ Rx) (c' ⁻¹) q₁Rx
                                                                    , transport (_∈ Rz) (d' ⁻¹) ((rounded-right-a Rz rounded-right-z v₂ v₁ d v₂Rz))
                                                                    , α
     II (inr (a , a')) (inr (b , b')) (inl (c , c')) (inl (d , d')) = transport (_∈ Lx) (a' ⁻¹) (rounded-left-a Lx rounded-left-x p₂ p₁ a p₁Lx)
                                                                    , transport (_∈ Lz) (b' ⁻¹) u₂Lz
                                                                    , transport (_∈ Rx) (c' ⁻¹) (rounded-right-a Rx rounded-right-x q₁ q₂ c q₁Rx)
                                                                    , transport (_∈ Rz) (d' ⁻¹) v₂Rz
                                                                    , α
     II (inr (a , a')) (inr (b , b')) (inl (c , c')) (inr (d , d')) = transport (_∈ Lx) (a' ⁻¹) (rounded-left-a Lx rounded-left-x p₂ p₁ a p₁Lx)
                                                                    , transport (_∈ Lz) (b' ⁻¹) u₂Lz
                                                                    , transport (_∈ Rx) (c' ⁻¹) (rounded-right-a Rx rounded-right-x q₁ q₂ c q₁Rx)
                                                                    , transport (_∈ Rz) (d' ⁻¹) ((rounded-right-a Rz rounded-right-z v₂ v₁ d v₂Rz))
                                                                    , α
     II (inr (a , a')) (inr (b , b')) (inr (c , c')) (inl (d , d')) = transport (_∈ Lx) (a' ⁻¹) (rounded-left-a Lx rounded-left-x p₂ p₁ a p₁Lx)
                                                                    , transport (_∈ Lz) (b' ⁻¹) u₂Lz
                                                                    , transport (_∈ Rx) (c' ⁻¹) q₁Rx
                                                                    , transport (_∈ Rz) (d' ⁻¹) v₂Rz
                                                                    , α
     II (inr (a , a')) (inr (b , b')) (inr (c , c')) (inr (d , d')) = transport (_∈ Lx) (a' ⁻¹) (rounded-left-a Lx rounded-left-x p₂ p₁ a p₁Lx)
                                                                    , transport (_∈ Lz) (b' ⁻¹) u₂Lz
                                                                    , transport (_∈ Rx) (c' ⁻¹) q₁Rx
                                                                    , transport (_∈ Rz) (d' ⁻¹) ((rounded-right-a Rz rounded-right-z v₂ v₁ d v₂Rz))
                                                                    , α
     

ℝ-metric-space : metric-space ℝ
ℝ-metric-space = B-ℝ , {!!} , {!!} , ℝ-m2 , ℝ-m3 , ℝ-m4



