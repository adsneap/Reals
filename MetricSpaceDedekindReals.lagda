\begin{code}
{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆)  -- TypeTopology

open import UF-Base
open import UF-FunExt -- TypeTopology
open import UF-Powerset -- TypeTopology
open import UF-PropTrunc -- TypeTopology
open import UF-Subsingletons -- TypeTopology

open import DedekindRealsProperties
open import MetricSpaceAltDef
open import RationalsAddition
open import Rationals
open import RationalsAbs
open import RationalsNegation
open import RationalsOrder

module MetricSpaceDedekindReals
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
 where

open PropositionalTruncation pt

open import DedekindReals pe pt fe
open import MetricSpaceRationals fe
open import RationalsMinMax fe

B-ℝ : (x y : ℝ) → (ε : ℚ) → 0ℚ < ε → 𝓤₀ ̇
B-ℝ ((Lx , Rx) , _) ((Ly , Ry) , _) ε l =
 ∃ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , p ∈ Lx × u ∈ Ly × q ∈ Rx × v ∈ Ry × B-ℚ (min p u) (max q v) ε l

ℝ-m1a-lemma : (((Lx , Rx) , _) ((Ly , Ry) , _) : ℝ) → ((ε : ℚ) → (ε>0 : 0ℚ < ε) → ∃ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , p ∈ Lx × u ∈ Ly × q ∈ Rx × v ∈ Ry × B-ℚ (min p u) (max q v) ε ε>0) → Lx ⊆ Ly
ℝ-m1a-lemma ((Lx , Rx) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x) ((Ly , Ry) , inhabited-left-y , inhabited-right-y , rounded-left-y , rounded-right-y , disjoint-y , located-y) f k kLx = ∥∥-rec Ly-is-prop α obtain-k'
 where
  Ly-is-prop : is-prop (k ∈ Ly)
  Ly-is-prop = (∈-is-prop Ly k)

  obtain-k' : ∃ k' ꞉ ℚ , (k < k') × k' ∈ Lx
  obtain-k' = (pr₁ (rounded-left-x k)) kLx

  α : Σ k' ꞉ ℚ , (k < k') × k' ∈ Lx → k ∈ Ly
  α (k' , (k<k' , k'-Lx)) = ∥∥-rec Ly-is-prop i obtain-info
   where
    ε : ℚ
    ε = k' - k
    ε>0 : 0ℚ < ε
    ε>0 = ℚ<-difference-positive fe k k' k<k'

    obtain-info : ∃ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , p ∈ Lx × u ∈ Ly × q ∈ Rx × v ∈ Ry × B-ℚ (min p u) (max q v) ε ε>0
    obtain-info = f ε ε>0

    i : Σ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , p ∈ Lx
                                           × u ∈ Ly
                                           × q ∈ Rx
                                           × v ∈ Ry
                                           × B-ℚ (min p u) (max q v) ε ε>0
                                           → k ∈ Ly
    i ((p , q , u , v) , p-Lx , u-Ly , q-Rx , v-Ry , metric)  = if-smaller-than-u ∣ u , (k<u , u-Ly) ∣
     where
      from-abs : ((- ε) < (min p u - max q v)) × ((min p u - max q v) < ε)
      from-abs = ℚ-abs-<-unpack fe (min p u - max q v) ε metric
      add-max : ((- ε) + max q v) < (min p u - max q v + max q v)
      add-max = ℚ<-addition-preserves-order (- ε) (min p u - max q v) (max q v) (pr₁ from-abs)
      simplify-left : (- ε) + max q v ≡ k + (max q v - k')
      simplify-left = (- ε) + max q v                ≡⟨ by-definition ⟩
                      (- (k' - k)) + max q v         ≡⟨ ap (_+ max q v) (ℚ-minus-dist fe k' (- k) ⁻¹) ⟩
                      (- k') + (- (- k)) + max q v   ≡⟨ ap (_+ max q v) (ℚ+-comm (- k') (- (- k))) ⟩
                      (- (- k)) + (- k') + max q v   ≡⟨ ℚ+-assoc fe (- (- k)) (- k') (max q v) ⟩
                      (- (- k)) + ((- k') + max q v) ≡⟨ ap₂ _+_ (ℚ-minus-minus fe k ⁻¹) (ℚ+-comm (- k') (max q v)) ⟩
                      k + (max q v - k')             ∎
      simplify-right : min p u - max q v + max q v ≡ min p u
      simplify-right = min p u - max q v + max q v       ≡⟨ ℚ+-assoc fe (min p u) (- max q v) (max q v) ⟩
                       min p u + ((- max q v) + max q v) ≡⟨ ap (min p u +_) (ℚ+-comm (- max q v) (max q v)) ⟩
                       min p u + (max q v + (- max q v)) ≡⟨ ap (min p u +_) (ℚ-inverse-sum-to-zero fe (max q v)) ⟩
                       min p u + 0ℚ ≡⟨ ℚ-zero-right-neutral fe (min p u) ⟩
                       min p u ∎
      simplify : (k + (max q v - k')) < min p u
      simplify = transport₂ _<_ simplify-left simplify-right add-max
      left-adds-positive : 0ℚ < max q v - k'
      left-adds-positive = which-is-max (max-to-≤ q v)
       where
        k<q : k' < q
        k<q = disjoint-x k' q (k'-Lx , q-Rx)
        0<q-k' : 0ℚ < (q - k')
        0<q-k' = ℚ<-difference-positive fe k' q k<q
        which-is-max : (q ≤ v) × (max q v ≡ v)
                     ∔ (v ≤ q) × (max q v ≡ q)
                     → 0ℚ < (max q v - k')
        which-is-max (inl (q≤v , e)) = ℚ<-difference-positive fe k' (max q v) (transport (k' <_) (e ⁻¹) k<v)
         where    
          k<v : k' < v
          k<v = ℚ<-≤-trans fe k' q v k<q q≤v
        which-is-max (inr (v≤q , e)) = ℚ<-difference-positive fe k' (max q v) (transport (k' <_) (e ⁻¹) k<q)
      k-small : k < k + (max q v - k')
      k-small = ℚ<-addition-preserves-order'' fe k (max q v - k') left-adds-positive
      right-small : min p u ≤ u
      right-small = min-split (min-to-≤ p u)
       where
        min-split : (p ≤ u) × (min p u ≡ p)
                  ∔ (u ≤ p) × (min p u ≡ u)
                  → min p u ≤ u
        min-split (inl (p≤u , e)) = transport (_≤ u) (e ⁻¹) p≤u
        min-split (inr (u≤p , e)) = transport (_≤ u) (e ⁻¹) (ℚ≤-refl u)
      k<minpu : k < min p u
      k<minpu = ℚ<-trans k (k + (max q v - k')) (min p u) k-small simplify
      k<u : k < u
      k<u = ℚ<-≤-trans fe k (min p u) u k<minpu right-small
      if-smaller-than-u : ∃ u ꞉ ℚ , (k < u) × u ∈ Ly → k ∈ Ly
      if-smaller-than-u = pr₂ (rounded-left-y k)

\end{code}
It's useful to have the second condition before the first in order to abstract a proof in the first condition.
\begin{code}

ℝ-m2 : m2 ℝ B-ℝ
ℝ-m2 ((Lx , Rx) , _) ((Ly , Ry) , _) ε l B = ∥∥-functor α B
 where
  α : Σ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , p ∈ Lx × u ∈ Ly × q ∈ Rx × v ∈ Ry × B-ℚ (min p u) (max q v) ε l
    → Σ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , p ∈ Ly × u ∈ Lx × q ∈ Ry × v ∈ Rx × B-ℚ (min p u) (max q v) ε l
  α ((p , q , u , v) , pLx , uLy , qRx , vRy , B) = (u , v , p , q) , uLy , pLx , vRy , qRx , transport₂ (λ α β → B-ℚ α β ε l) (min-comm p u) (max-comm q v) B
  
ℝ-m1a : m1a ℝ B-ℝ
ℝ-m1a ((Lx , Rx) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x) ((Ly , Ry) , inhabited-left-y , inhabited-right-y , rounded-left-y , rounded-right-y , disjoint-y , located-y) f = ℝ-equality-from-left-cut' x y I II
 where
  x = ((Lx , Rx) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x)
  y = ((Ly , Ry) , inhabited-left-y , inhabited-right-y , rounded-left-y , rounded-right-y , disjoint-y , located-y)

  I : Lx ⊆ Ly
  I = ℝ-m1a-lemma x y f

  II : Ly ⊆ Lx
  II = ℝ-m1a-lemma y x (λ ε ε>0 → ℝ-m2 x y ε ε>0 (f ε ε>0))

m1b-lemma : (q ε : ℚ) → 0ℚ < q × q < ε → abs q < ε
m1b-lemma q ε (l₁ , l₂) = IV
 where
  I : 0ℚ < ε 
  I = ℚ<-trans 0ℚ q ε l₁ l₂
  II : ((- ε) < 0ℚ)
  II = transport (- ε <_) ℚ-minus-zero-is-zero i
   where
    i : (- ε) < (- 0ℚ)
    i = ℚ<-swap fe 0ℚ ε I
  III : (- ε) < q
  III = ℚ<-trans (- ε) 0ℚ q II l₁
  IV : abs q < ε
  IV = ℚ<-to-abs fe q ε (III , l₂) 

ℝ-m1b : m1b ℝ B-ℝ
ℝ-m1b ((L , R) , iscut) ε l = ∥∥-functor I (ℝ-arithmetically-located fe pt pe ((L , R) , iscut) ε l)
 where
  I : (Σ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × (0ℚ < (y - x)) × ((y - x) < ε)) → Σ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , p ∈ L × u ∈ L × q ∈ R × v ∈ R × B-ℚ (min p u) (max q v) ε l
  I ((x , y) , Lx , Ry , (l₁ , l₂)) = (x , y , x , y) , Lx , Lx , Ry , Ry , transport₂ (λ α β → B-ℚ α β ε l) (min-refl x ⁻¹) (max-refl y ⁻¹) iii
   where
    i : ℚ-metric y x < ε 
    i = m1b-lemma (y - x) ε (l₁ , l₂)
    ii : ℚ-metric y x ≡ ℚ-metric x y
    ii = ℚ-metric-commutes y x
    iii : ℚ-metric x y < ε
    iii = transport (_< ε) ii i


ℝ-m3 : m3 ℝ B-ℝ
ℝ-m3 ((Lx , Rx) , iscutx) ((Ly , Ry) , iscuty) ε₁ ε₂ l₁ l₂ l₃ B = ∥∥-functor I B
 where
  I : Σ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , p ∈ Lx × u ∈ Ly × q ∈ Rx × v ∈ Ry × B-ℚ (min p u) (max q v) ε₁ l₁
    → Σ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , p ∈ Lx × u ∈ Ly × q ∈ Rx × v ∈ Ry × B-ℚ (min p u) (max q v) ε₂ l₂
  I ((p , q , u , v) , pLx , uLy , qRx , vRy , B) = (p , q , u , v) , pLx , uLy , qRx , vRy , ℚ<-trans (ℚ-metric (min p u) (max q v)) ε₁ ε₂ B l₃

{-
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
-}                                                                   
     

ℝ-metric-space : metric-space ℝ
ℝ-metric-space = B-ℝ , ℝ-m1a , ℝ-m1b , ℝ-m2 , ℝ-m3 , {!!} -- ℝ-m4



