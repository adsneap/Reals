

\begin{code}

open import SpartanMLTT renaming (_+_ to _∔_)

open import IntegersB
  
ℤ[i] : 𝓤₀ ̇
ℤ[i] = ℤ × ℤ

open import IntegersAddition renaming (_+_ to _ℤ+_)

_+_ : ℤ[i] → ℤ[i] → ℤ[i] 
(a , b) + (c , d) = a ℤ+ c , b ℤ+ d

infixl 40 _+_

open import IntegersMultiplication renaming (_*_ to _ℤ*_)

𝓲 : ℤ[i]
𝓲 = (pos 0 , pos 1)

-𝓲 : ℤ[i]
-𝓲 = pos 0 , negsucc 0

open import IntegersNegation renaming (-_ to ℤ-_)

_ℤ-_ : ℤ → ℤ → ℤ
a ℤ- b  = a ℤ+ (ℤ- b)

_*_ : ℤ[i] → ℤ[i] → ℤ[i]
(a , b) * (c , d) = ((a ℤ* c) ℤ- (b ℤ* d)) , a ℤ* d ℤ+ b ℤ* c

open import UF-Base

i-squared : 𝓲 * 𝓲 ≡ ℤ- pos 1 , pos 0
i-squared = to-×-≡ refl refl

ℤ[i]+-comm : (x y : ℤ[i]) → x + y ≡ y + x
ℤ[i]+-comm (a , b) (c , d) = to-×-≡ (ℤ+-comm a c) (ℤ+-comm b d)

ℤ[i]+-assoc : (x y z : ℤ[i]) → x + y + z ≡ x + (y + z)
ℤ[i]+-assoc (a , b) (c , d) (u , v) = to-×-≡ I II
 where
  I : a ℤ+ c ℤ+ u ≡ a ℤ+ (c ℤ+ u)
  I = ℤ+-assoc a c u
  II : b ℤ+ d ℤ+ v ≡ b ℤ+ (d ℤ+ v)
  II = ℤ+-assoc b d v




\end{code}


