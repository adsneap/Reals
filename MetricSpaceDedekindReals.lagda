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
ℝ-m4 : m4 ℝ B-ℝ
ℝ-m4 ((Lx , Rx) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x)
     ((Ly , Ry) , inhabited-left-y , inhabited-right-y , rounded-left-y , rounded-right-y , disjoint-y , located-y)
     ((Lz , Rz) , inhabited-left-z , inhabited-right-z , rounded-left-z , rounded-right-z , disjoint-z , located-z) ε₁ ε₂ l₁ l₂ B₁ B₂ = ∥∥-functor I (binary-choice B₁ B₂)
 where
  ε : ℚ
  ε = ε₁ + ε₂
  ε>0 : 0ℚ < ε     
  ε>0 = ℚ<-adding-zero ε₁ ε₂ l₁ l₂
  
  ε>ε₁ : ε₁ < ε
  ε>ε₁ = ℚ<-addition-preserves-order'' fe ε₁ ε₂ l₂
  ε>ε₂ : ε₂ < ε
  ε>ε₂ = transport (ε₂ <_) (ℚ+-comm ε₂ ε₁) (ℚ<-addition-preserves-order'' fe ε₂ ε₁ l₁)

  I : (Σ (p₁ , q₁ , u₁ , v₁) ꞉ ℚ × ℚ × ℚ × ℚ , p₁ ∈ Lx × u₁ ∈ Ly × q₁ ∈ Rx × v₁ ∈ Ry × B-ℚ (min p₁ u₁) (max q₁ v₁) ε₁ l₁)
    × (Σ (p₂ , q₂ , u₂ , v₂) ꞉ ℚ × ℚ × ℚ × ℚ , p₂ ∈ Ly × u₂ ∈ Lz × q₂ ∈ Ry × v₂ ∈ Rz × B-ℚ (min p₂ u₂) (max q₂ v₂) ε₂ l₂)
    → Σ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , p ∈ Lx × u ∈ Lz × q ∈ Rx × v ∈ Rz × B-ℚ (min p u) (max q v) ε ε>0
  I (((p₁ , q₁ , u₁ , v₁) , p₁Lx , u₁Ly , q₁Rx , v₁Ry , B₃) , ((p₂ , q₂ , u₂ , v₂) , p₂Ly , u₂Lz , q₂Ry , v₂Rz , B₄))
   = (min p₁ p₂ , max q₁ q₂ , min u₁ u₂ , max v₁ v₂) , II , III , IV , V , VI
    where
     xyl = min p₁ u₁
     xyr = max q₁ v₁
     yzl = min p₂ u₂
     yzr = max q₂ v₂
     II : min p₁ p₂ ∈ Lx
     II = i (min-to-≤ p₁ p₂)
      where
       i : (p₁ ≤ p₂) × (min p₁ p₂ ≡ p₁) ∔ (p₂ ≤ p₁) × (min p₁ p₂ ≡ p₂) → min p₁ p₂ ∈ Lx
       i (inl (l , e)) = transport (_∈ Lx) (e ⁻¹) p₁Lx
       i (inr (l , e)) = rounded-left-a Lx rounded-left-x (min p₁ p₂) p₁ (transport (_≤ p₁) (e ⁻¹) l) p₁Lx
     III : min u₁ u₂ ∈ Lz
     III = i (min-to-≤ u₁ u₂)
      where
       i : (u₁ ≤ u₂) × (min u₁ u₂ ≡ u₁) ∔ (u₂ ≤ u₁) × (min u₁ u₂ ≡ u₂) → min u₁ u₂ ∈ Lz
       i (inl (l , e)) = rounded-left-a Lz rounded-left-z (min u₁ u₂) u₂ (transport (_≤ u₂) (e ⁻¹) l) u₂Lz
       i (inr (l , e)) = transport (_∈ Lz) (e ⁻¹) u₂Lz
     IV : max q₁ q₂ ∈ Rx
     IV = i (max-to-≤ q₁ q₂)
      where
       i : (q₁ ≤ q₂) × (max q₁ q₂ ≡ q₂) ∔ (q₂ ≤ q₁) × (max q₁ q₂ ≡ q₁) → max q₁ q₂ ∈ Rx
       i (inl (l , e)) = rounded-right-a Rx rounded-right-x q₁ (max q₁ q₂) (transport (q₁ ≤_ ) (e ⁻¹) l) q₁Rx
       i (inr (l , e)) = transport (_∈ Rx) (e ⁻¹) q₁Rx
     V : max v₁ v₂ ∈ Rz
     V = i (max-to-≤ v₁ v₂)
      where
       i : (v₁ ≤ v₂) × (max v₁ v₂ ≡ v₂) ∔ (v₂ ≤ v₁) × (max v₁ v₂ ≡ v₁) → max v₁ v₂ ∈ Rz
       i (inl (l , e)) = transport (_∈ Rz) (e ⁻¹) v₂Rz
       i (inr (l , e)) = rounded-right-a Rz rounded-right-z v₂ (max v₁ v₂) (transport (v₂ ≤_) (e ⁻¹) l) v₂Rz
     VI : B-ℚ (min (min p₁ p₂) (min u₁ u₂)) (max (max q₁ q₂) (max v₁ v₂)) ε ε>0
     VI = transport₂ (λ α β → B-ℚ α β ε ε>0) (i ⁻¹) (ii ⁻¹) iii
      where
       i : min (min p₁ p₂) (min u₁ u₂) ≡ min xyl yzl
       i = min (min p₁ p₂) (min u₁ u₂) ≡⟨ min-assoc p₁ p₂ (min u₁ u₂) ⟩
           min p₁ (min p₂ (min u₁ u₂)) ≡⟨ ap (λ - → min p₁ -) (min-comm p₂ (min u₁ u₂)) ⟩
           min p₁ (min (min u₁ u₂) p₂) ≡⟨ min-assoc p₁ (min u₁ u₂) p₂ ⁻¹ ⟩
           min (min p₁ (min u₁ u₂)) p₂ ≡⟨ ap (λ z → min z p₂) (min-assoc p₁ u₁ u₂ ⁻¹) ⟩
           min (min xyl u₂) p₂ ≡⟨ min-assoc xyl u₂ p₂  ⟩
           min xyl (min u₂ p₂) ≡⟨ ap (λ - → min xyl -) (min-comm u₂ p₂) ⟩
           min xyl yzl ∎
       ii : max (max q₁ q₂) (max v₁ v₂) ≡ max xyr yzr
       ii = max (max q₁ q₂) (max v₁ v₂) ≡⟨ max-assoc q₁ q₂ (max v₁ v₂) ⟩
            max q₁ (max q₂ (max v₁ v₂)) ≡⟨ ap (λ - → max q₁ -) (max-comm q₂ (max v₁ v₂)) ⟩
            max q₁ (max (max v₁ v₂) q₂) ≡⟨ max-assoc q₁ (max v₁ v₂) q₂ ⁻¹ ⟩
            max (max q₁ (max v₁ v₂)) q₂ ≡⟨ ap (λ z → max z q₂) (max-assoc q₁ v₁ v₂ ⁻¹) ⟩
            max (max xyr v₂) q₂ ≡⟨ max-assoc xyr v₂ q₂ ⟩
            max xyr (max v₂ q₂) ≡⟨ ap (λ - → max xyr -) (max-comm v₂ q₂) ⟩
            max xyr yzr ∎
       iii : B-ℚ (min xyl yzl) (max xyr yzr) ε ε>0
       iii = iv (min-to-≤ xyl yzl) (max-to-≤ xyr yzr)
        where
         iv : (xyl ≤ yzl) × (min xyl yzl ≡ xyl)
            ∔ (yzl ≤ xyl) × (min xyl yzl ≡ yzl)
            → (xyr ≤ yzr) × (max xyr yzr ≡ yzr)
            ∔ (yzr ≤ xyr) × (max xyr yzr ≡ xyr)
            → B-ℚ (min xyl yzl) (max xyr yzr) ε ε>0
         iv (inl (k₁ , e₁)) (inl (k₂ , e₂)) = transport₂ (λ α β → ℚ-metric α β < ε₁ + ε₂) (e₁ ⁻¹) (e₂ ⁻¹) from-inequalities
          where
           from-inequalities : ℚ-metric xyl yzr < (ε₁ + ε₂)
           from-inequalities = inequality-chain-with-metric xyl xyr yzl yzr ε₁ ε₂ (v (min-to-≤ p₂ u₂) (max-to-≤ q₁ v₁)) k₂ B₃ B₄
            where
             v : (p₂ ≤ u₂) × (min p₂ u₂ ≡ p₂) ∔ (u₂ ≤ p₂) × (min p₂ u₂ ≡ u₂)
               → (q₁ ≤ v₁) × (max q₁ v₁ ≡ v₁) ∔ (v₁ ≤ q₁) × (max q₁ v₁ ≡ q₁)
               → min p₂ u₂ ≤ max q₁ v₁
             v (inl (γ₁ , δ₁)) (inl (γ₂ , δ₂)) = transport₂ _≤_ (δ₁ ⁻¹) (δ₂ ⁻¹) (ℚ<-coarser-than-≤ p₂ v₁ (disjoint-y p₂ v₁ (p₂Ly , v₁Ry)))
             v (inl (γ₁ , δ₁)) (inr (γ₂ , δ₂)) = transport₂ _≤_ (δ₁ ⁻¹) (δ₂ ⁻¹) (ℚ<-coarser-than-≤ p₂ q₁ (disjoint-y p₂ q₁ (p₂Ly , (rounded-right-a Ry rounded-right-y v₁ q₁ γ₂ v₁Ry))))
             v (inr (γ₁ , δ₁)) (inl (γ₂ , δ₂)) = transport₂ _≤_ (δ₁ ⁻¹) (δ₂ ⁻¹) (ℚ<-coarser-than-≤ u₂ v₁ (disjoint-y u₂ v₁ ((rounded-left-a Ly rounded-left-y u₂ p₂ γ₁ p₂Ly) , v₁Ry)))
             v (inr (γ₁ , δ₁)) (inr (γ₂ , δ₂)) = transport₂ _≤_ (δ₁ ⁻¹) (δ₂ ⁻¹) (ℚ<-coarser-than-≤ u₂ q₁ (disjoint-y u₂ q₁ ((rounded-left-a Ly rounded-left-y u₂ p₂ γ₁ p₂Ly) , (rounded-right-a Ry rounded-right-y v₁ q₁ γ₂ v₁Ry))))
           
         iv (inl (k₁ , e₁)) (inr (k₂ , e₂)) = ℚ<-trans (abs (min xyl yzl - (max xyr yzr))) ε₁ ε (transport (_< ε₁) (v ⁻¹) B₃) ε>ε₁
          where
          v : abs (min xyl yzl - max xyr yzr) ≡ abs (xyl - xyr)
          v = ap₂ (λ α β → abs (α - β)) e₁ e₂
         iv (inr (k₁ , e₁)) (inl (k₂ , e₂)) = ℚ<-trans (abs (min xyl yzl - (max xyr yzr))) ε₂ ε (transport (_< ε₂) (v ⁻¹) B₄) ε>ε₂
          where
           v : abs (min xyl yzl - max xyr yzr) ≡ abs (yzl - yzr)
           v = ap₂ (λ α β → abs (α - β)) e₁ e₂
         iv (inr (k₁ , e₁)) (inr (k₂ , e₂)) = transport (ℚ-metric (min xyl yzl) (max xyr yzr) <_) (ℚ+-comm ε₂ ε₁) v
          where
           from-inequalities : ℚ-metric yzl xyr < (ε₂ + ε₁)
           from-inequalities = inequality-chain-with-metric yzl yzr xyl xyr ε₂ ε₁ (vi (min-to-≤ p₁ u₁) (max-to-≤ q₂ v₂)) k₂ B₄ B₃
            where
             vi : (p₁ ≤ u₁) × (min p₁ u₁ ≡ p₁) ∔ (u₁ ≤ p₁) × (min p₁ u₁ ≡ u₁)
                → (q₂ ≤ v₂) × (max q₂ v₂ ≡ v₂) ∔ (v₂ ≤ q₂) × (max q₂ v₂ ≡ q₂)
                → min p₁ u₁ ≤ max q₂ v₂
             vi (inl (γ₁ , δ₁)) (inl (γ₂ , δ₂)) = transport₂ _≤_ (δ₁ ⁻¹) (δ₂ ⁻¹) (ℚ<-coarser-than-≤ p₁ v₂ (disjoint-y p₁ v₂ ((rounded-left-a Ly rounded-left-y p₁ u₁ γ₁ u₁Ly) , (rounded-right-a Ry rounded-right-y q₂ v₂ γ₂ q₂Ry))))
             vi (inl (γ₁ , δ₁)) (inr (γ₂ , δ₂)) = transport₂ _≤_ (δ₁ ⁻¹) (δ₂ ⁻¹) (ℚ<-coarser-than-≤ p₁ q₂ (disjoint-y p₁ q₂ ((rounded-left-a Ly rounded-left-y p₁ u₁ γ₁ u₁Ly) , q₂Ry)))
             vi (inr (γ₁ , δ₁)) (inl (γ₂ , δ₂)) = transport₂ _≤_ (δ₁ ⁻¹) (δ₂ ⁻¹) (ℚ<-coarser-than-≤ u₁ v₂ (disjoint-y u₁ v₂ (u₁Ly , (rounded-right-a Ry rounded-right-y q₂ v₂ γ₂ q₂Ry))))
             vi (inr (γ₁ , δ₁)) (inr (γ₂ , δ₂)) = transport₂ _≤_ (δ₁ ⁻¹) (δ₂ ⁻¹) (ℚ<-coarser-than-≤ u₁ q₂ (disjoint-y u₁ q₂ (u₁Ly , q₂Ry)))
           v : ℚ-metric (min xyl yzl) (max xyr yzr) < (ε₂ + ε₁)
           v = transport₂ (λ α β → ℚ-metric α β < ε₂ + ε₁) (e₁ ⁻¹) (e₂ ⁻¹) from-inequalities

ℝ-metric-space : metric-space ℝ
ℝ-metric-space = B-ℝ , ℝ-m1a , ℝ-m1b , ℝ-m2 , ℝ-m3 , ℝ-m4 



