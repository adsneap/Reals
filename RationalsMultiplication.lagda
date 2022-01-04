Andrew Sneap - 11th November 2021

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆) --TypeTopology

open import UF-Base hiding (_≈_) --TypeTopology
open import UF-FunExt --TypeTopology

open import IntegersB
open import ncRationals
open import ncRationalsOperations renaming (_*_ to _ℚₙ*_ ; _+_ to _ℚₙ+_)
open import Rationals
open import RationalsAddition

_*_ : ℚ → ℚ → ℚ
(p , _) * (q , _) = toℚ (p ℚₙ* q)

infixl 33 _*_

toℚ-* : Fun-Ext → (p q : ℚₙ) → toℚ (p ℚₙ* q) ≡ toℚ p * toℚ q
toℚ-* fe p q = equiv→equality fe (p ℚₙ* q) (p' ℚₙ* q') conclusion
 where
  p' = toℚₙ (toℚ p)
  q' = toℚₙ (toℚ q)

  I : p ≈ p'
  I = ≈-toℚ p

  II : q ≈ q'
  II = ≈-toℚ q

  III : (p ℚₙ* q) ≈ (p' ℚₙ* q)
  III = ≈-over-* p p' q I

  IV : (q ℚₙ* p') ≈ (q' ℚₙ* p')
  IV = ≈-over-* q q' p' II

  V : (p' ℚₙ* q) ≈ (p' ℚₙ* q')
  V = transport₂ _≈_ (ℚₙ*-comm q p') (ℚₙ*-comm q' p') IV
  
  conclusion : (p ℚₙ* q) ≈ (p' ℚₙ* q')
  conclusion = ≈-trans (p ℚₙ* q) (p' ℚₙ* q) (p' ℚₙ* q') III V

ℚ*-comm : (p q : ℚ) → p * q ≡ q * p
ℚ*-comm (p , _) (q , _) = ap toℚ (ℚₙ*-comm p q)

ℚ*-assoc : Fun-Ext → (p q r : ℚ) → (p * q) * r ≡ p * (q * r)
ℚ*-assoc fe (x , p) (y , q) (z , r) = III
 where
  left : ℚ
  left = (x , p) * (y , q)

  right : ℚ
  right = (y , q) * (z , r)

  I : Σ l ꞉ ℚₙ , (z , r ≡ toℚ l)
  I = q-has-qn fe (z , r)

  II : Σ t ꞉ ℚₙ , (x , p ≡ toℚ t)
  II = q-has-qn fe (x , p)

  l t : ℚₙ
  l = pr₁ I
  t = pr₁ II

  III : toℚ (x ℚₙ* y) * (z , r) ≡ ((x , p) * toℚ (y ℚₙ* z))
  III = (left * (z , r))      ≡⟨ ap (left *_) (pr₂ I) ⟩
        left * toℚ z          ≡⟨ toℚ-* fe (x ℚₙ* y) z ⁻¹ ⟩
        toℚ ((x ℚₙ* y) ℚₙ* z) ≡⟨ ap toℚ (ℚₙ*-assoc x y z) ⟩
        toℚ (x ℚₙ* (y ℚₙ* z)) ≡⟨ toℚ-* fe x (y ℚₙ* z) ⟩
        (toℚ x * right)       ≡⟨ ap (_* right) (pr₂ II ⁻¹) ⟩
        ((x , p) * right) ∎

ℚ-zero-left-is-zero : Fun-Ext → (q : ℚ) → 0ℚ * q ≡ 0ℚ
ℚ-zero-left-is-zero fe ((x , a) , q) = III
 where
  qn : Σ (x' , a') ꞉ ℚₙ , ((x , a) , q ≡ toℚ (x' , a'))
  qn = q-has-qn fe ((x , a) , q)
  x' = pr₁ (pr₁ qn)
  a' = pr₂ (pr₁ qn)

  II : toℚ ((pos 0 , 0) ℚₙ* (x' , a'))  ≡ toℚ (pos 0 , 0)
  II = equiv→equality fe ((pos 0 , 0) ℚₙ* (x' , a')) (pos 0 , 0) (ℚₙ-zero-left-neutral (x' , a'))
  
  III : 0ℚ * ((x , a) , q) ≡ 0ℚ
  III = 0ℚ * ((x , a) , q)             ≡⟨ ap (0ℚ *_) (pr₂ qn) ⟩
       0ℚ * toℚ (x' , a')              ≡⟨ toℚ-* fe (pos 0 , 0) (x' , a') ⁻¹ ⟩
       toℚ ((pos 0 , 0) ℚₙ* (x' , a')) ≡⟨ II ⟩
       0ℚ ∎

ℚ-zero-right-is-zero : Fun-Ext → (q : ℚ) → q * 0ℚ ≡ 0ℚ
ℚ-zero-right-is-zero fe q = ℚ*-comm q 0ℚ ∙ ℚ-zero-left-is-zero fe q

ℚ-mult-left-id : Fun-Ext → (q : ℚ) → 1ℚ * q ≡ q
ℚ-mult-left-id fe q = II
 where
  I : Σ q' ꞉ ℚₙ , q ≡ toℚ q'
  I = q-has-qn fe q 
  
  q' : ℚₙ
  q' = pr₁ I

  II : (1ℚ * q) ≡ q
  II = (1ℚ * q)                    ≡⟨ refl ⟩
        toℚ ((pos 1 , 0) ℚₙ* q')   ≡⟨ ap toℚ (ℚₙ-mult-left-id q') ⟩
        toℚ q'                     ≡⟨ pr₂ I ⁻¹ ⟩
        q ∎

ℚ-mult-right-id : Fun-Ext → (q : ℚ) → q * 1ℚ ≡ q
ℚ-mult-right-id fe q = ℚ*-comm q 1ℚ ∙ ℚ-mult-left-id fe q 

ℚ-distributivity : Fun-Ext → (p q r : ℚ) → p * (q + r) ≡ (p * q) + (p * r) 
ℚ-distributivity fe p q r = II
 where
  pnc : Σ p' ꞉ ℚₙ , p ≡ toℚ p'
  pnc = q-has-qn fe p

  qnc : Σ q' ꞉ ℚₙ , q ≡ toℚ q'
  qnc = q-has-qn fe q

  rnc : Σ r' ꞉ ℚₙ , r ≡ toℚ r'
  rnc = q-has-qn fe r

  p' q' r' : ℚₙ
  p' = pr₁ pnc
  q' = pr₁ qnc
  r' = pr₁ rnc

  I : (p' ℚₙ* (q' ℚₙ+ r')) ≈ ((p' ℚₙ* q') ℚₙ+ (p' ℚₙ* r')) → toℚ (p' ℚₙ* (q' ℚₙ+ r')) ≡ toℚ ((p' ℚₙ* q') ℚₙ+ (p' ℚₙ* r')) 
  I = equiv→equality fe (p' ℚₙ* (q' ℚₙ+ r')) ((p' ℚₙ* q') ℚₙ+ (p' ℚₙ* r'))

  II : p * (q + r) ≡ (p * q) + (p * r)
  II = p * (q + r)                             ≡⟨ refl ⟩
       p * toℚ (q' ℚₙ+ r')                     ≡⟨ ap (λ - → - * toℚ (q' ℚₙ+ r')) (pr₂ pnc) ⟩
       toℚ p' * toℚ (q' ℚₙ+ r')                ≡⟨ toℚ-* fe p' (q' ℚₙ+ r') ⁻¹ ⟩
       toℚ (p' ℚₙ* (q' ℚₙ+ r'))                ≡⟨ I (ℚₙ-dist p' q' r') ⟩
       toℚ ((p' ℚₙ* q') ℚₙ+ (p' ℚₙ* r'))       ≡⟨ toℚ-+ fe (p' ℚₙ* q') (p' ℚₙ* r') ⟩
       toℚ (p' ℚₙ* q') + toℚ (p' ℚₙ* r')       ≡⟨ refl ⟩
       (p * q) + (p * r)  ∎

ℚ-distributivity' : Fun-Ext → (p q r : ℚ) → (q + r) * p ≡ (q * p) + (r * p) 
ℚ-distributivity' fe p q r = II
 where
  I : p * (q + r) ≡ p * q + p * r
  I = ℚ-distributivity fe p q r

  II : (q + r) * p ≡ q * p + r * p
  II = (q + r) * p ≡⟨ ℚ*-comm (q + r) p ⟩
       p * (q + r) ≡⟨ I ⟩
       p * q + p * r ≡⟨ ap₂ _+_ (ℚ*-comm p q) (ℚ*-comm p r) ⟩
       q * p + r * p ∎

⟨2/3⟩^_ : ℕ → ℚ
⟨2/3⟩^ 0         = toℚ (pos 1 , 0)
⟨2/3⟩^ (succ n)  = rec 2/3 (_* 2/3) n

⟨2/3⟩-to-mult : Fun-Ext → (n : ℕ) → ⟨2/3⟩^ (succ n) ≡ (⟨2/3⟩^ n) * 2/3
⟨2/3⟩-to-mult fe zero = f
 where
  abstract
   f : ⟨2/3⟩^ (succ 0) ≡ ((⟨2/3⟩^ 0) * 2/3)
   f = (ℚ-mult-left-id fe 2/3) ⁻¹
⟨2/3⟩-to-mult fe (succ n) = refl

⟨1/n⟩ : ℕ → ℚ
⟨1/n⟩ n = toℚ (pos 1 , n)

⟨1/sn⟩ : ℕ → ℚ
⟨1/sn⟩ 0 = 1ℚ
⟨1/sn⟩ (succ n) = ⟨1/n⟩ n

⟨1/n⟩-1 : Fun-Ext → ⟨1/n⟩ 0 ≡ 1ℚ
⟨1/n⟩-1 fe = equiv→equality fe (pos 1 , 0) (pos 1 , 0) refl

1/2 : ℚ
1/2 = toℚ (pos 1 , 1)

⟨1/n⟩-1/2 : Fun-Ext → ⟨1/n⟩ 1 ≡ 1/2
⟨1/n⟩-1/2 fe = equiv→equality fe (pos 1 , 1) (pos 1 , 1) by-definition

⟨1/2⟩^_ : ℕ → ℚ
⟨1/2⟩^ 0         = toℚ (pos 1 , 0)
⟨1/2⟩^ (succ n)  = rec (1/2) (_* 1/2) n

