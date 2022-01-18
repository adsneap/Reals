Andrew Sneap

\begin{code}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆)  -- TypeTopology

open import UF-Base --TypeTopology
open import UF-FunExt --TypeTopology

open import NaturalsOrderExtended
open import Rationals
open import RationalsAddition
open import RationalsAbs
open import RationalsMinMax
open import RationalsMultiplication
open import RationalsNegation
open import RationalsOrder
open import MetricSpaceRationals
open import NaturalsOrder renaming (_<_ to _ℕ<_ ; _≤_ to _ℕ≤_ ; max to ℕ-max ; max-comm to ℕ-max-comm)

module RationalsLimits
        (fe : Fun-Ext)
 where

_limit-of_ : (L : ℚ) → (f : ℕ → ℚ) → 𝓤₀ ̇
L limit-of f = ∀ (ε : ℚ) → 0ℚ < ε → Σ N ꞉ ℕ , ((n : ℕ) → N ℕ≤ n → ℚ-metric fe (f n) L < ε)

sandwich-theorem : (L : ℚ) → (f g h : ℕ → ℚ) → (Σ k ꞉ ℕ , ((k' : ℕ) → k ℕ≤ k' → f k' ≤ g k' × g k' ≤ h k')) →  L limit-of f → L limit-of h → L limit-of g
sandwich-theorem L f g h (k , k-greater) lim-f lim-h = lim-g
 where
  lim-g : L limit-of g
  lim-g ε l = getN's (lim-f ε l) (lim-h ε l)
   where
    getN's : Σ N₁ ꞉ ℕ , ((n : ℕ) → N₁ ℕ≤ n → ℚ-metric fe (f n) L < ε)
           → Σ N₂ ꞉ ℕ , ((n : ℕ) → N₂ ℕ≤ n → ℚ-metric fe (h n) L < ε)
           → Σ N ꞉ ℕ  , ((n : ℕ) → N  ℕ≤ n → ℚ-metric fe (g n) L < ε)
    getN's (N₁ , f-close) (N₂ , h-close) = N , g-close
     where
      N : ℕ
      N = ℕ-max (ℕ-max N₁ N₂) k
      
      N₁-small : N₁ ℕ≤ ℕ-max N₁ N₂
      N₁-small = max-≤-upper-bound N₁ N₂
      
      N₂-small : N₂ ℕ≤ ℕ-max N₁ N₂
      N₂-small = transport (N₂ ℕ≤_) (ℕ-max-comm N₂ N₁) (max-≤-upper-bound N₂ N₁)
      
      N₁N₂-small : ℕ-max N₁ N₂ ℕ≤ ℕ-max (ℕ-max N₁ N₂) k
      N₁N₂-small = max-≤-upper-bound (ℕ-max N₁ N₂) k
      
      k-small : k ℕ≤ ℕ-max (ℕ-max N₁ N₂) k
      k-small = transport (k ℕ≤_) (ℕ-max-comm k (ℕ-max N₁ N₂)) (max-≤-upper-bound k (ℕ-max N₁ N₂))

      α : (f N ≤ g N) × (g N ≤ h N)
      α = k-greater N k-small
     
      g-close : (n : ℕ) → ℕ-max (ℕ-max N₁ N₂) k ℕ≤ n → ℚ-metric fe (g n) L < ε
      g-close n less = obtain-inequalities (ℚ-abs-<-unpack fe (f n - L) ε f-close') (ℚ-abs-<-unpack fe (h n - L) ε h-close')
       where
        f-close' : ℚ-metric fe (f n) L < ε
        f-close' = f-close n (≤-trans N₁ N n (≤-trans N₁ (ℕ-max N₁ N₂) N N₁-small N₁N₂-small) less)
        h-close' : ℚ-metric fe (h n) L < ε
        h-close' = h-close n (≤-trans N₂ N n (≤-trans N₂ (ℕ-max N₁ N₂) N N₂-small N₁N₂-small) less)

        obtain-inequalities : ((- ε) < (f n - L)) × ((f n - L) < ε)
                            → ((- ε) < (h n - L)) × ((h n - L) < ε)
                            → ℚ-metric fe (g n) L < ε
        obtain-inequalities (l₁ , l₂) (l₃ , l₄) = ℚ<-to-abs fe (g n - L) ε (I , II)
         where
          k-greater' : (f n ≤ g n) × (g n ≤ h n)
          k-greater' = k-greater n (≤-trans k N n k-small less)
          
          I : (- ε) < (g n - L)
          I = ℚ<-≤-trans fe (-  ε) (f n - L) (g n - L) l₁ (ℚ≤-addition-preserves-order fe (f n) (g n) (- L) (pr₁ k-greater'))
          II : (g n - L) < ε
          II = ℚ≤-<-trans fe (g n - L) (h n - L) ε (ℚ≤-addition-preserves-order fe (g n) (h n) (- L) (pr₂ k-greater')) l₄

0f : ℕ → ℚ
0f _ = 0ℚ

0f-converges : 0ℚ limit-of 0f
0f-converges ε l = 0 , f-conv
 where
  f-conv : (n : ℕ) → 0 ℕ≤ n → ℚ-metric fe (0f n) 0ℚ < ε
  f-conv n less = transport (_< ε) I l
   where
    I : ℚ-metric fe (0f n) 0ℚ ≡ 0ℚ
    I = ℚ-metric fe (0f n) 0ℚ ≡⟨ by-definition ⟩
        abs (0ℚ - 0ℚ)         ≡⟨ by-definition ⟩
        abs 0ℚ                ≡⟨ by-definition ⟩
        0ℚ ∎

open import IntegersB
open import IntegersAddition
open import ncRationalsOrder
open import ncRationalsOperations renaming (_*_ to _ℚₙ*_)

embedding-ℕ-to-ℚ : ℕ → ℚ
embedding-ℕ-to-ℚ n = toℚ (pos n , 0)

embedding-1/ℕ-to-ℚ : ℕ → ℚ
embedding-1/ℕ-to-ℚ n = toℚ (pos 1 , n)

-- always-a-smaller-ε : (ε : ℚ) → 0ℚ < ε → Σ n ꞉ ℕ , (embedding-ℕ-to-ℚ n < ε)
-- always-a-smaller-ε = {!!}

open import NaturalsDivision
open import NaturalsAddition renaming (_+_ to _ℕ+_)
open import NaturalsMultiplication renaming (_*_ to _ℕ*_)
open import NaturalNumbers-Properties -- TypeTopology
open import IntegersMultiplication renaming (_*_ to _ℤ*_)
open import IntegersAddition renaming (_+_ to _ℤ+_)

⟨1/sn⟩-converges : 0ℚ limit-of ⟨1/sn⟩
⟨1/sn⟩-converges ((pos 0 , a) , ε)        l = 𝟘-elim (ℚ<-not-itself 0ℚ (transport (0ℚ <_) (numerator-zero-is-zero fe ((pos 0 , a) , ε) refl) l))
⟨1/sn⟩-converges ((negsucc x , a) , ε)    l = 𝟘-elim {!!}
⟨1/sn⟩-converges ((pos (succ x) , a) , ε) l = q ℕ+ 1 , conclusion 
 where
  rough-N : Σ q ꞉ ℕ , Σ r ꞉ ℕ , (a ≡ q ℕ* succ x ℕ+ r) × (r ℕ< succ x)
  rough-N = division a x
  q = pr₁ rough-N
  r = pr₁ (pr₂ rough-N)
  
  I : a ℕ< (succ x ℕ* (q ℕ+ 1))
  I = transport₂ _ℕ<_ ii iii i
   where
    i : (q ℕ* succ x ℕ+ r) ℕ< (q ℕ* succ x ℕ+ succ x)
    i = <-n-monotone-left r (succ x) (q ℕ* succ x) (pr₂ (pr₂ (pr₂ rough-N)))

    ii : q ℕ* succ x ℕ+ r ≡ a 
    ii = pr₁ (pr₂ (pr₂ rough-N)) ⁻¹

    iii : q ℕ* succ x ℕ+ succ x ≡ succ x ℕ* (q ℕ+ 1)
    iii = q ℕ* succ x ℕ+ succ x      ≡⟨ ap₂ _ℕ+_ (mult-commutativity q (succ x)) (mult-right-id (succ x) ⁻¹) ⟩
          succ x ℕ* q ℕ+ succ x ℕ* 1 ≡⟨ distributivity-mult-over-nat (succ x) q 1 ⁻¹ ⟩
          succ x ℕ* (q ℕ+ 1) ∎


  
  conclusion : (n : ℕ) → (q ℕ+ 1) ℕ≤ n → ℚ-metric fe (⟨1/sn⟩ n) 0ℚ < ((pos (succ x) , a) , ε)
  conclusion 0 l' = 𝟘-elim l'
  conclusion (succ n) l' = {!!}
   where
     II : toℚ ((pos (succ a)) , x) < toℚ (pos (succ n) , 0)
     II = toℚ-< (pos (succ a) , x) {!pos (succ n) , 0!} {!!}
    
limits-lemma : (k : ℕ) → ((pos 1 , succ k) ℚₙ* (pos 2 , 2)) ℚₙ≤ (pos 1 , succ (succ k))
limits-lemma k = k , I
 where
  I : pos 2 ℤ* pos (succ (succ (succ k))) ℤ+ pos k ≡ pos 1 ℤ* pos (succ (pred (succ (succ k) ℕ* 3)))
  I = pos 2 ℤ* pos (succ (succ (succ k))) ℤ+ pos k ≡⟨ by-definition ⟩
      pos 2 ℤ* pos (k ℕ+ 3) ℤ+ pos k               ≡⟨ ℤ+-comm (pos 2 ℤ* pos (k ℕ+ 3)) (pos k) ⟩
      pos k ℤ+ pos 2 ℤ* pos (k ℕ+ 3)               ≡⟨ ap (λ z → pos k ℤ+ pos 2 ℤ* z) (pos-addition-equiv-to-ℕ k 3 ⁻¹) ⟩
      pos k ℤ+ pos 2 ℤ* (pos k ℤ+ pos 3)           ≡⟨ ap (pos k ℤ+_) (distributivity-mult-over-ℤ' (pos k) (pos 3) (pos 2) ) ⟩
      pos k ℤ+ (pos 2 ℤ* pos k ℤ+ pos 6)           ≡⟨ ℤ+-assoc (pos k) (pos 2 ℤ* pos k) (pos 6) ⁻¹ ⟩
      pos k ℤ+ pos 2 ℤ* pos k ℤ+ pos 6             ≡⟨ ap (λ z → z ℤ+ pos 2 ℤ* pos k ℤ+ pos 6) (ℤ-mult-left-id (pos k) ⁻¹) ⟩
      pos 1 ℤ* pos k ℤ+ pos 2 ℤ* pos k ℤ+ pos 6    ≡⟨ ap (_ℤ+ pos 6) (distributivity-mult-over-ℤ (pos 1) (pos 2) (pos k) ⁻¹) ⟩
      (pos 3) ℤ* pos k ℤ+ pos 6                    ≡⟨ ap (_ℤ+ pos 6) (ℤ*-comm (pos 3) (pos k)) ⟩
      pos k ℤ* pos 3 ℤ+ pos 6                      ≡⟨ distributivity-mult-over-ℤ (pos k) (pos 2) (pos 3) ⁻¹ ⟩
      (pos k ℤ+ pos 2) ℤ* pos 3                    ≡⟨ ap (_ℤ* pos 3) (pos-addition-equiv-to-ℕ k 2) ⟩
      pos (k ℕ+ 2) ℤ* pos 3                        ≡⟨ by-definition ⟩
      pos (succ (succ k)) ℤ* pos 3                 ≡⟨ denom-setup (succ k) 2 ⁻¹ ⟩
      pos (succ (pred (succ (succ k) ℕ* 3)))       ≡⟨ ℤ-mult-left-id (pos (succ (pred (succ (succ k) ℕ* 3)))) ⁻¹ ⟩
      pos 1 ℤ* pos (succ (pred (succ (succ k) ℕ* 3))) ∎


⟨2/3⟩^n-squeezed : Σ N ꞉ ℕ  , ((n : ℕ) → N ℕ≤ n → (0f n ≤ (⟨2/3⟩^ n)) × ((⟨2/3⟩^ n) ≤ ⟨1/sn⟩ n))
⟨2/3⟩^n-squeezed = 1 , I
 where
  γ : 0ℚ ≤ 2/3
  γ = toℚ-≤ (pos 0 , 0) (pos 2 , 2) (2 , by-definition)
  I : (n : ℕ) → 1 ℕ≤ n → (0f n ≤ (⟨2/3⟩^ n)) × ((⟨2/3⟩^ n) ≤ ⟨1/sn⟩ n)
  I 0 l = 𝟘-elim l
  I (succ n) l = II , III
   where
    II : 0ℚ ≤ (⟨2/3⟩^ succ n)
    II = induction base step n
     where
      base : 0ℚ ≤ (⟨2/3⟩^ succ 0)
      base = toℚ-≤ (pos 0 , 0) (pos 2 , 2) (2 , refl)
      step : (k : ℕ) → 0ℚ ≤ (⟨2/3⟩^ succ k) → 0ℚ ≤ (⟨2/3⟩^ succ (succ k))
      step k IH = i
       where
        i : (0ℚ * 2/3) ≤ ((⟨2/3⟩^ succ k) * 2/3)
        i = ℚ≤-pos-multiplication-preserves-order' fe 0ℚ (⟨2/3⟩^ (succ k)) 2/3 IH γ

    III : (⟨2/3⟩^ succ n) ≤ ⟨1/sn⟩ (succ n)
    III = induction base step n
     where
      base : (⟨2/3⟩^ succ 0) ≤ ⟨1/sn⟩ (succ 0)
      base = toℚ-≤ (pos 2 , 2) (pos 1 , 0) (1 , refl)
      step : (k : ℕ)
           → (⟨2/3⟩^ succ k) ≤ ⟨1/sn⟩ (succ k)
           → (⟨2/3⟩^ succ (succ k)) ≤ ⟨1/sn⟩ (succ (succ k))
      step 0 IH = ii
       where
        abstract
         i : toℚ (pos 4 , 8) ≤ toℚ (pos 1 , 1)
         i = toℚ-≤ (pos 4 , 8) (pos 1 , 1) (1 , refl)
         ii : (⟨2/3⟩^ succ (succ 0)) ≤ ⟨1/sn⟩ (succ (succ 0))
         ii = transport (_≤ toℚ (pos 1 , 1)) (toℚ-* fe (pos 2 , 2) (pos 2 , 2)) i
      step (succ k) IH = ℚ≤-trans fe (((⟨2/3⟩^ succ (succ k)) * 2/3)) ((⟨1/n⟩ (succ k) * 2/3)) (⟨1/n⟩ (succ (succ k))) i ii
       where
        i : ((⟨2/3⟩^ succ (succ k)) * 2/3) ≤ (⟨1/n⟩ (succ k) * 2/3)
        i = ℚ≤-pos-multiplication-preserves-order' fe (⟨2/3⟩^ (succ (succ k))) (⟨1/n⟩ (succ k)) 2/3 IH γ
        ii : (⟨1/n⟩ (succ k) * 2/3) ≤ ⟨1/n⟩ (succ (succ k))
        ii = transport (_≤ ⟨1/n⟩ (succ (succ k))) (iii ⁻¹) iv
         where
          abstract
           iii : (⟨1/n⟩ (succ k)) * 2/3 ≡ toℚ ((pos 1 , succ k) ℚₙ* (pos 2 , 2))
           iii = toℚ-* fe (pos 1 , succ k) (pos 2 , 2) ⁻¹
           iv : toℚ ((pos 1 , succ k) ℚₙ* (pos 2 , 2)) ≤ ⟨1/n⟩ (succ (succ k))
           iv = toℚ-≤ ((pos 1 , succ k) ℚₙ* (pos 2 , 2)) (pos 1 , succ (succ k)) (limits-lemma k)

⟨2/3⟩^n-converges : 0ℚ limit-of ⟨2/3⟩^_
⟨2/3⟩^n-converges = sandwich-theorem 0ℚ 0f ⟨2/3⟩^_ ⟨1/sn⟩ ⟨2/3⟩^n-squeezed 0f-converges ⟨1/sn⟩-converges

\end{code}
