Andrew Sneap

\begin{code}
{-# OPTIONS --without-K --exact-split --safe --experimental-lossy-unification #-}

open import SpartanMLTT renaming (_+_ to _∔_) -- TypeTopology
open import UF-Base -- TypeTopology
open import UF-FunExt -- TypeTopology
open import UF-Subsingletons -- TypeTopology
open import UF-PropTrunc -- TypeTopology
open import OrderNotation -- TypeTopology


open import UF-Powerset
open import DedekindRealsProperties
open import Rationals
open import RationalsAddition renaming (_+_ to _ℚ+_)
open import RationalsNegation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import RationalsOrder 

module DedekindRealsAddition
         (pe : Prop-Ext)
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
       where 

open import DedekindReals pe pt fe
open import DedekindRealsOrder pe pt fe
open PropositionalTruncation pt

_+_ : ℝ → ℝ → ℝ
((L-x , R-x) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x) + ((L-y , R-y) , inhabited-left-y , inhabited-right-y , rounded-left-y , rounded-right-y , disjoint-y , located-y) =
 (L-z , R-z) , inhabited-left-z , inhabited-right-z , rounded-left-z , rounded-right-z , disjoint-z , located-z
 where
  x : ℝ
  x = ((L-x , R-x) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x)
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

  ψ : (z r t s : ℚ) → t ≡ r ℚ+ s → z ≡ ((r ℚ+ (z ℚ- t)) ℚ+ s)
  ψ z r t s e = z                                               ≡⟨ ℚ-zero-left-neutral fe z ⁻¹ ⟩
                (0ℚ ℚ+ z)                                       ≡⟨ ap (_ℚ+ z) (ℚ-inverse-sum-to-zero fe r ⁻¹) ⟩
                ((r ℚ- r)) ℚ+ z                                 ≡⟨ (ℚ+-assoc fe r (ℚ- r) z) ⟩
                (r ℚ+ ((ℚ- r) ℚ+ z))                            ≡⟨ ℚ-zero-right-neutral fe (r ℚ+ ((ℚ- r) ℚ+ z)) ⁻¹ ⟩
                (r ℚ+ ((ℚ- r) ℚ+ z)) ℚ+ 0ℚ                      ≡⟨ ap₂ _ℚ+_ (ap (r ℚ+_) (ℚ+-comm (ℚ- r) z)) (ℚ-inverse-sum-to-zero' fe s ⁻¹) ⟩
                (r ℚ+ (z ℚ- r)) ℚ+ ((ℚ- s) ℚ+ s)                ≡⟨ ℚ+-assoc fe (r ℚ+ (z ℚ+ (ℚ- r))) (ℚ- s) s ⁻¹ ⟩
                ((r ℚ+ (z ℚ+ (ℚ- r))) ℚ+ (ℚ- s)) ℚ+ s           ≡⟨ ap (_ℚ+ s) (ℚ+-assoc fe r (z ℚ+ (ℚ- r)) (ℚ- s)) ⟩
                (r ℚ+ ((z ℚ+ (ℚ- r)) ℚ+ (ℚ- s))) ℚ+ s           ≡⟨ ap (λ - → (r ℚ+ -) ℚ+ s) (ℚ+-assoc fe z (ℚ- r) (ℚ- s)) ⟩
                (r ℚ+ (z ℚ+ ((ℚ- r) ℚ+ (ℚ- s)))) ℚ+ s           ≡⟨ ap (λ - → (r ℚ+ (z ℚ+ -)) ℚ+ s) (ℚ-minus-dist fe r s) ⟩
                (r ℚ+ (z ℚ+ (ℚ- (r ℚ+ s)))) ℚ+ s                ≡⟨ ap ((λ - → (r ℚ+ (z ℚ+ (ℚ- -))) ℚ+ s)) (e ⁻¹) ⟩
                (r ℚ+ (z ℚ+ (ℚ- t))) ℚ+ s                       ∎

  rounded-left-z : (z : ℚ) → (z ∈ L-z ⇔ (∃ t ꞉ ℚ , (z < t) × t ∈ L-z))
  rounded-left-z z = I , II
   where
    I : z ∈ L-z → ∃ t ꞉ ℚ , (z < t) × t ∈ L-z
    I zLz = ∥∥-rec ∃-is-prop δ zLz
     where
      δ : Σ (r , s) ꞉ ℚ × ℚ , r ∈ L-x × s ∈ L-y × (z ≡ r ℚ+ s) → ∃ t ꞉ ℚ , (z < t) × t ∈ L-z
      δ ((r , s) , rLx , sLy , e) = γ (rounded-left-b L-x rounded-left-x r rLx) (rounded-left-b L-y rounded-left-y s sLy)
       where
        γ : (∃ p ꞉ ℚ , r < p × p ∈ L-x) → (∃ q ꞉ ℚ , s < q × q ∈ L-y) → ∃ t ꞉ ℚ , z < t × t ∈ L-z 
        γ f g = ζ (binary-choice f g)
         where
          ζ : ∥ (Σ p ꞉ ℚ , r < p × p ∈ L-x) × (Σ q ꞉ ℚ , s < q × q ∈ L-y) ∥ → ∃ t ꞉ ℚ , z < t × t ∈ L-z
          ζ bc = ∥∥-functor η bc
           where
            η : (Σ p ꞉ ℚ , r < p × p ∈ L-x) × (Σ q ꞉ ℚ , s < q × q ∈ L-y) → Σ t ꞉ ℚ , z < t × t ∈ L-z
            η ((p , l₁ , pLx) , q , l₂ , qLy) = (p ℚ+ q) , (II , III)
             where
              II : z <  p ℚ+ q
              II = transport (_< p ℚ+ q) (e ⁻¹) (ℚ<-adding r p s q l₁ l₂)
              III : (p ℚ+ q) ∈ L-z
              III = ∣ (p , q) , (pLx , qLy , refl) ∣
      
    II : ∃ t ꞉ ℚ , (z < t) × t ∈ L-z → z ∈ L-z
    II et = ∥∥-rec (∈-is-prop L-z z) δ et
     where
      δ : Σ t ꞉ ℚ , (z < t) × t ∈ L-z → z ∈ L-z
      δ (t , l , tLz) = ∥∥-functor γ tLz
       where
        γ : Σ (r , s) ꞉ ℚ × ℚ , r ∈ L-x × s ∈ L-y × (t ≡ r ℚ+ s)
          → Σ (r' , s') ꞉ ℚ × ℚ , r' ∈ L-x × s' ∈ L-y × (z ≡ r' ℚ+ s')
        γ ((r , s) , rLx , sLy , e) = ((r ℚ+ (z ℚ- t)) , s) , III , sLy , IV
         where
          III : (r ℚ+ (z ℚ- t)) ∈ L-x
          III = rounded-left-c L-x rounded-left-x (r ℚ+ (z ℚ- t)) r (ℚ<-subtraction-preserves-order' fe r (z ℚ- t) (ℚ<-difference-positive' fe z t l) ) rLx
          IV : z ≡ r ℚ+ (z ℚ- t) ℚ+ s
          IV = ψ z r t s e
      
  rounded-right-z : (z : ℚ) → (z ∈ R-z) ⇔ (∃ q ꞉ ℚ , ((q < z) × (q ∈ R-z)))
  rounded-right-z z = I , II
   where
    I : z ∈ R-z → ∃ q ꞉ ℚ , q < z × q ∈ R-z
    I zRz = ∥∥-rec ∃-is-prop δ zRz
     where
      δ : (Σ (r , s) ꞉ ℚ × ℚ , (r ∈ R-x) × (s ∈ R-y) × (z ≡ (r ℚ+ s))) → (∃ q ꞉ ℚ , (q < z) × q ∈ R-z)
      δ ((r , s) , rRx , sRy , e) = γ (rounded-right-b R-x rounded-right-x r rRx) (rounded-right-b R-y rounded-right-y s sRy)
       where
        γ : (∃ p ꞉ ℚ , p < r × p ∈ R-x) → (∃ q ꞉ ℚ , q < s × q ∈ R-y) → ∃ t ꞉ ℚ , t < z × t ∈ R-z 
        γ f g = ζ (binary-choice f g)
         where
          ζ : ∥ (Σ p ꞉ ℚ , p < r × p ∈ R-x) × (Σ q ꞉ ℚ , q < s × q ∈ R-y) ∥ → ∃ t ꞉ ℚ , t < z × t ∈ R-z
          ζ = ∥∥-functor η 
           where
            η : (Σ p ꞉ ℚ , p < r × p ∈ R-x) × (Σ q ꞉ ℚ , q < s × q ∈ R-y) → Σ t ꞉ ℚ , t < z × t ∈ R-z
            η ((p , l₁ , pRx) , q , l₂ , qRy) = p ℚ+ q , II , III
             where
              II : p ℚ+ q < z
              II = transport (p ℚ+ q <_) (e ⁻¹) (ℚ<-adding p r q s l₁ l₂)
              III : (p ℚ+ q) ∈ R-z
              III = ∣ (p , q) , pRx , qRy , refl ∣
    II : ∃ t ꞉ ℚ , (t < z) × t ∈ R-z → z ∈ R-z
    II et = ∥∥-rec (∈-is-prop R-z z) δ et
     where
      δ : Σ t ꞉ ℚ , (t < z) × t ∈ R-z → z ∈ R-z
      δ (t , l , tRz) = ∥∥-functor γ tRz
       where
        γ : Σ (r , s) ꞉ ℚ × ℚ , r ∈ R-x × s ∈ R-y × (t ≡ r ℚ+ s)
          → Σ (r' , s') ꞉ ℚ × ℚ , r' ∈ R-x × s' ∈ R-y × (z ≡ r' ℚ+ s')
        γ ((r , s) , rRx , sRy , e) = ((r ℚ+ (z ℚ- t)) , s) , III , sRy , IV
         where
          III : (r ℚ+ (z ℚ- t)) ∈ R-x
          III = rounded-right-c R-x rounded-right-x r (r ℚ+ (z ℚ- t)) (ℚ<-addition-preserves-order'' fe r (z ℚ- t) (ℚ<-difference-positive fe t z l)) rRx
          IV : z ≡ r ℚ+ (z ℚ- t) ℚ+ s
          IV = ψ z r t s e 
          
  disjoint-z : disjoint L-z R-z
  disjoint-z p q (α , β) = ∥∥-rec (ℚ<-is-prop p q) δ (binary-choice α β)
   where
    δ : (Σ (r , s) ꞉ ℚ × ℚ , r ∈ L-x × s ∈ L-y × (p ≡ r ℚ+ s))
      × (Σ (r' , s') ꞉ ℚ × ℚ , r' ∈ R-x × s' ∈ R-y × (q ≡ r' ℚ+ s'))
      → p < q
    δ (((r , s) , l-x , l-y , e₁) , ((r' , s') , r-x , r-y , e₂)) = transport₂ _<_ (e₁ ⁻¹) (e₂ ⁻¹) (ℚ<-adding r r' s s' I II)
     where
      I : r < r'
      I = disjoint-x r r' (l-x , r-x) 

      II : s < s'
      II = disjoint-y s s' (l-y , r-y)
      
  located-z : located L-z R-z
  located-z p q l = I (ℝ-arithmetically-located fe pt pe x (q ℚ- p) (ℚ<-difference-positive fe p q l))
   where
    I : ∃ (e , t) ꞉ ℚ × ℚ , e ∈ L-x × t ∈ R-x × 0ℚ < t ℚ- e × t ℚ- e < q ℚ- p → p ∈ L-z ∨ q ∈ R-z
    I = ∥∥-rec ∨-is-prop δ
     where
      δ : Σ (e , t) ꞉ ℚ × ℚ , e ∈ L-x × t ∈ R-x × 0ℚ < t ℚ- e × t ℚ- e < q ℚ- p → p ∈ L-z ∨ q ∈ R-z
      δ ((e , t) , eLx , tRx , l₁ , l₂) = IV II III
       where
        l₃ : p ℚ- e < q ℚ- t
        l₃ = transport₂ _<_ i ii (ℚ<-addition-preserves-order (t ℚ- e) (q ℚ- p) (p ℚ- t) l₂)
         where
          i : t ℚ- e ℚ+ (p ℚ- t) ≡ p ℚ- e
          i = t ℚ- e ℚ+ (p ℚ- t)           ≡⟨ ℚ+-comm (t ℚ- e) (p ℚ- t) ⟩
              p ℚ- t ℚ+ (t ℚ- e)           ≡⟨ ℚ+-assoc fe p (ℚ- t) (t ℚ- e) ⟩
              p ℚ+ ((ℚ- t) ℚ+ (t ℚ- e))    ≡⟨ ap (p ℚ+_) (ℚ+-assoc fe (ℚ- t) t (ℚ- e) ⁻¹) ⟩
              p ℚ+ ((ℚ- t) ℚ+ t ℚ- e)      ≡⟨ ap (λ α → p ℚ+ (α ℚ- e)) (ℚ-inverse-sum-to-zero' fe t) ⟩
              p ℚ+ (0ℚ ℚ- e)               ≡⟨ ap (p ℚ+_) (ℚ-zero-left-neutral fe (ℚ- e)) ⟩
              p ℚ- e ∎
          ii : q ℚ- p ℚ+ (p ℚ- t) ≡ q ℚ- t
          ii = q ℚ- p ℚ+ (p ℚ- t)           ≡⟨ ℚ+-assoc fe q (ℚ- p) (p ℚ- t) ⟩
               q ℚ+ ((ℚ- p) ℚ+ (p ℚ- t))    ≡⟨ ap (q ℚ+_) (ℚ+-assoc fe (ℚ- p) p (ℚ- t) ⁻¹) ⟩
               q ℚ+ ((ℚ- p) ℚ+ p ℚ- t)      ≡⟨ ap (λ α → q ℚ+ (α ℚ- t)) (ℚ-inverse-sum-to-zero' fe p) ⟩
               q ℚ+ (0ℚ ℚ- t)               ≡⟨ ap (q ℚ+_) (ℚ-zero-left-neutral fe (ℚ- t)) ⟩
               q ℚ- t ∎
               
        II : Σ z ꞉ ℚ , (p ℚ- e < z) × (z < q ℚ- t)
        II = ℚ-dense fe (p ℚ- e) (q ℚ- t) l₃
       
        III : Σ y ꞉ ℚ , p ℚ- e < y × y < (pr₁ II)
        III = ℚ-dense fe (p ℚ- e) (pr₁ II) (pr₁ (pr₂ II))
        IV : ((y , _) : Σ y ꞉ ℚ , (p ℚ- e < y) × (y < q ℚ- t)) → Σ z ꞉ ℚ , p ℚ- e < z × z < y → ∥ p ∈ L-z ∔ q ∈ R-z ∥
        IV (y , l₄ , l₅) (z , l₆ , l₇) = ∥∥-functor η (located-y z y l₇)
         where
          η : z ∈ L-y ∔ y ∈ R-y → p ∈ L-z ∔ q ∈ R-z
          η (inl zLy) = inl ∣ (p ℚ- z , z) , V , zLy , VI ∣
           where
            V : (p ℚ- z) ∈ L-x
            V = rounded-left-c L-x rounded-left-x (p ℚ- z) e (ℚ<-swap' fe p e z l₆) eLx

            VI : p ≡ p ℚ- z ℚ+ z
            VI = p                  ≡⟨ ℚ-zero-right-neutral fe p ⁻¹ ⟩
                 p ℚ+ 0ℚ            ≡⟨ ap (p ℚ+_) (ℚ-inverse-sum-to-zero' fe z ⁻¹) ⟩
                 p ℚ+ ((ℚ- z) ℚ+ z) ≡⟨ ℚ+-assoc fe p (ℚ- z) z ⁻¹ ⟩
                 p ℚ- z ℚ+ z        ∎

          η (inr yRy) = inr ∣ (t , q ℚ- t) , tRx , V , VI ∣
           where
            V : (q ℚ- t) ∈ R-y
            V = rounded-right-c R-y rounded-right-y y (q ℚ- t) l₅ yRy

            VI : q ≡ t ℚ+ (q ℚ- t)
            VI = q                  ≡⟨ ℚ-zero-left-neutral fe q ⁻¹ ⟩
                 0ℚ ℚ+ q            ≡⟨ ap (_ℚ+ q) (ℚ-inverse-sum-to-zero fe t ⁻¹) ⟩
                 t ℚ+ (ℚ- t) ℚ+ q   ≡⟨ ℚ+-assoc fe t (ℚ- t) q ⟩
                 t ℚ+ ((ℚ- t) ℚ+ q) ≡⟨ ap (t ℚ+_) (ℚ+-comm (ℚ- t) q) ⟩
                 t ℚ+ (q ℚ- t)      ∎

infixl 30 _+_

ℝ+-comm : ∀ x y → x + y ≡ y + x
ℝ+-comm x y = ℝ-equality-from-left-cut' (x + y) (y + x) I II
 where
  I : lower-cut-of (x + y) ⊆ lower-cut-of (y + x)
  I p p<x+y = ∥∥-functor i p<x+y
   where
    i : Σ (r , s) ꞉ ℚ × ℚ , r ∈ lower-cut-of x × s ∈ lower-cut-of y × (p ≡ r ℚ+ s)
      → Σ (r , s) ꞉ ℚ × ℚ , r ∈ lower-cut-of y × s ∈ lower-cut-of x × (p ≡ r ℚ+ s)
    i ((r , s) , rLx , sLy , e) = (s , r) , (sLy , rLx , (e ∙ ℚ+-comm r s))
  II : lower-cut-of (y + x) ⊆ lower-cut-of (x + y)
  II q x+y<q = ∥∥-functor i x+y<q
   where
    i : Σ (r , s) ꞉ ℚ × ℚ , r ∈ lower-cut-of y × s ∈ lower-cut-of x × (q ≡ r ℚ+ s)
      → Σ (r , s) ꞉ ℚ × ℚ , r ∈ lower-cut-of x × s ∈ lower-cut-of y × (q ≡ r ℚ+ s)
    i ((r , s) , rLy , sLx , e) = (s , r) , (sLx , rLy , (e ∙ ℚ+-comm r s))

ℝ-zero-left-neutral : (x : ℝ) → 0ℝ + x ≡ x
ℝ-zero-left-neutral x = ℝ-equality-from-left-cut' (0ℝ + x) x I II
 where
  I : lower-cut-of (0ℝ + x) ⊆ lower-cut-of x
  I p 0+x<x = ∥∥-rec (∈-is-prop (lower-cut-of x) p) i 0+x<x
   where
    i : Σ (r , s) ꞉ ℚ × ℚ , r ∈ lower-cut-of 0ℝ × s ∈ lower-cut-of x × (p ≡ r ℚ+ s) → p ∈ lower-cut-of x
    i ((r , s) , r<0 , s<x , e) = rounded-left-c (lower-cut-of x) (rounded-from-real-L x) p s iv s<x
     where
      ii : p ℚ+ r < p
      ii = ℚ<-subtraction-preserves-order' fe p r r<0
      iii : p ℚ+ r < r ℚ+ s
      iii = transport (p ℚ+ r <_) e ii
      iv : p < s
      iv = transport₂ _<_ v vi (ℚ<-addition-preserves-order (p ℚ+ r) (r ℚ+ s) (ℚ- r) iii )
       where
        v : p ℚ+ r ℚ- r ≡ p
        v = ℚ+-assoc fe p r (ℚ- r) ∙ ℚ-inverse-intro fe p r ⁻¹ 
        vi : r ℚ+ s ℚ- r ≡ s
        vi = r ℚ+ s ℚ- r   ≡⟨ ap (_ℚ- r) (ℚ+-comm r s) ⟩
             s ℚ+ r ℚ- r   ≡⟨ ℚ+-assoc fe s r (ℚ- r) ⟩
             s ℚ+ (r ℚ- r) ≡⟨ ℚ-inverse-intro fe s r ⁻¹ ⟩
             s ∎
  II : lower-cut-of x ⊆ lower-cut-of (0ℝ + x)
  II q q<x = ∥∥-functor i by-rounded-x
   where
    by-rounded-x : ∃ q' ꞉ ℚ , q < q' × q' ∈ lower-cut-of x
    by-rounded-x = rounded-left-b (lower-cut-of x) (rounded-from-real-L x) q q<x
    i : Σ q' ꞉ ℚ , q < q' × q' ∈ lower-cut-of x → Σ (r , s) ꞉ ℚ × ℚ , r ∈ lower-cut-of 0ℝ × s ∈ lower-cut-of x × (q ≡ r ℚ+ s)
    i (q' , l , q'Lx) = (q ℚ- q' , q') , iii , q'Lx , ii
     where
      ii : q ≡ q ℚ- q' ℚ+ q'
      ii = q                    ≡⟨ ℚ-inverse-intro fe q q' ⟩
           q ℚ+ (q' ℚ- q')      ≡⟨ ap (q ℚ+_) (ℚ+-comm q' (ℚ- q')) ⟩
           q ℚ+ ((ℚ- q') ℚ+ q') ≡⟨ ℚ+-assoc fe q (ℚ- q') q' ⁻¹ ⟩
           q ℚ- q' ℚ+ q' ∎
      
      iii : q ℚ- q' < 0ℚ
      iii = transport (q ℚ- q' <_) iv (ℚ<-addition-preserves-order q q' (ℚ- q') l)
       where
        iv : q' ℚ- q' ≡ 0ℚ
        iv = ℚ-inverse-sum-to-zero fe q'

ℝ-zero-right-neutral : (x : ℝ) → x + 0ℝ ≡ x
ℝ-zero-right-neutral x = ℝ+-comm x 0ℝ ∙ ℝ-zero-left-neutral x
{-
ℝ+-assoc : {!∀ x y z → x + y + z ≡ ?!}
ℝ+-assoc = {!!}
-}
