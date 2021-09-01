{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _⊹_ ; * to ⋆) --TypeTopology
open import Integers
open import DecidableAndDetachable
open import DiscreteAndSeparated
open import NaturalNumbers-Properties
open import NaturalsOrder renaming (_<_ to _<ℕ_ ; _≤_ to _≤ℕ_)
open import UF-Base
open import UF-Subsingletons
open import UF-Miscelanea
open import UF-FunExt
open import IntegersProperties
open import UF-Subsingletons-FunExt
-- open import IntegersOrder

{-# BUILTIN INTEGER       ℤ       #-}
{-# BUILTIN INTEGERPOS    pos     #-}
{-# BUILTIN INTEGERNEGSUC negsucc #-}

module Reals (fe : FunExt) where

to-zero : ℤ → ℤ
to-zero (pos n) = pos (pred n)
to-zero (negsucc n) = negsucc (pred n)

Interval : 𝓤₀ ̇
Interval = ℤ × ℤ
-- ⟦ (k , p) ⟧ = [k/2ᵖ⁺¹ , (k+2)/2ᵖ⁺¹]

codeOf precOf : Interval → ℤ
codeOf = pr₁
precOf = pr₂

_/2 : ℕ → ℕ
0 /2 = 0
1 /2 = 0
succ (succ n) /2 = succ (n /2)

−_ : Interval → Interval
− (k , p) = (negsucc 1 - k , p)

downLeft downMid downRight upRight : Interval → Interval
downLeft  (k         , p) = (k + k          , succℤ p)
downMid   (k         , p) = (k + k + pos 1  , succℤ p)
downRight (k         , p) = (k + k + pos 2  , succℤ p)
upRight   (pos x     , p) = (pos     (x /2) , predℤ p)
upRight   (negsucc x , p) = (negsucc (x /2) , predℤ p)

downLeftₙ downRightₙ upRightₙ : Interval → ℕ → Interval
downLeftₙ  (k , p) = rec (k , p) downLeft
downRightₙ (k , p) = rec (k , p) downRight
upRightₙ   (k , p) = rec (k , p) upRight

{-
endpoints-at-lower-level : Interval → ℕ → Interval × Interval
endpoints-at-lower-level (k , p) n = (downLeftₙ (k , p) n) , (downRightₙ (k , p) n)

endpoints-at-lower-level' : Interval → ℕ → ℤ × ℤ × ℤ
endpoints-at-lower-level' (k , p) n = pr₁ (pr₁ γ) , pr₁ (pr₂ γ) , pr₂ (pr₂ γ)
 where γ = endpoints-at-lower-level (k , p) n

next : Interval → Interval
next (k , p) = (k + pos 2 , p)
-}

_≤ℤ_ : (a b : ℤ) → 𝓤₀ ̇
a ≤ℤ b = Σ c ꞉ ℕ , a + pos c ≡ b

_≤ℤ_≤ℤ_ : (a b c : ℤ) → 𝓤₀ ̇
a ≤ℤ b ≤ℤ c = (a ≤ℤ b) × (b ≤ℤ c)

{-
_⊆_ : Interval → Interval → 𝓤₀ ̇
(k , p) ⊆ (c , q)
 = Σ (a , _) ꞉ (q ≤ℤ p)
 , codeOf (downLeftₙ (c , q) a) ≤ℤ k ≤ℤ codeOf (downRightₙ (c , q) a)

≤ℤ-refl : {a : ℤ} → a ≤ℤ a
≤ℤ-refl = 0 , refl

⊆-refl : {i : Interval} → i ⊆ i
⊆-refl = ≤ℤ-refl , ≤ℤ-refl , ≤ℤ-refl
-}
+-trans : (a b c d : ℤ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
+-trans a b c d = ℤ+-assoc a b (c + d)
                ∙ ap (a +_) (ℤ+-assoc b c d ⁻¹)
                ∙ ap (λ ■ → a + (■ + d)) (ℤ+-comm b c)
                ∙ ap (a +_) (ℤ+-assoc c b d)
                ∙ ℤ+-assoc a c (b + d) ⁻¹

_+ℕ_ : ℕ → ℕ → ℕ
a +ℕ 0 = a
a +ℕ succ b = succ (a +ℕ b)

+-pos : (a b : ℕ) → pos (a +ℕ b) ≡ pos a + pos b
+-pos a 0 = refl
+-pos a (succ b) = ap succℤ (+-pos a b)

+-negsucc : (a b : ℕ) → negsucc (a +ℕ b) ≡ succℤ (negsucc a + negsucc b)
+-negsucc a 0 = refl
+-negsucc a (succ b)
 = ap predℤ  (+-negsucc a b)
 ∙ predsuccℤ (negsucc a +negsucc b)
 ∙ succpredℤ (negsucc a +negsucc b) ⁻¹

succ+ℕ : (a b : ℕ) → succ (a +ℕ b) ≡ succ a +ℕ b
succ+ℕ a zero = refl
succ+ℕ a (succ b) = ap succ (succ+ℕ a b)

{-
succ+ℤ : (a b : ℤ) → succℤ (a + b) ≡ succℤ a + b
succ+ℤ a (pos zero) = refl
succ+ℤ a (pos (succ x)) = ap succℤ (succ+ℤ a (pos x))
succ+ℤ a (negsucc zero) = succpredℤ a
                        ∙ predsuccℤ a ⁻¹
succ+ℤ a (negsucc (succ x)) = succpredℤ (a + negsucc x)
                            ∙ predsuccℤ (a + negsucc x) ⁻¹
                            ∙ ap predℤ (succ+ℤ a (negsucc x))

fact'' : (m n : ℕ) (a b : ℤ) → a ≤ℤ b → m ≤ℕ n
       → (succℤ ^ m) (a + a) ≤ℤ (succℤ ^ n) (b + b)
fact'' zero zero a b (c , f) ⋆
 = c +ℕ c
 , (ap (a + a +_) (+-pos c c)
 ∙ +-trans a a (pos c) (pos c)
 ∙ ap (_+ (a + pos c)) f
 ∙ ap (b +_) f)
fact'' zero (succ n) a b a≤b ⋆
 = succ (pr₁ IH)
 , ap succℤ (pr₂ IH)  
 where IH = fact'' 0 n a b a≤b ⋆
fact'' (succ m) (succ n) a b a≤b g
 = pr₁ IH
 , (succ+ℤ ((succℤ ^ m) (a + a)) (pos (pr₁ IH)) ⁻¹
 ∙ ap succℤ (pr₂ IH))
 where IH = fact'' m n a b a≤b g

⊆-downLeft : (i j : Interval) → i ⊆ j → downLeft i ⊆ j
⊆-downLeft i j ((a , f) , (b , g) , (c , h))
  = (succ a , ap succℤ f)
  , fact'' 0 0 m₁ (codeOf i) (b , g) ⋆
  , fact'' 0 2 (codeOf i) m₂ (c , h) ⋆
  where
    m₁ = codeOf (downLeftₙ j a)
    m₂ = codeOf (downRightₙ j a)

⊆-downMid : (i j : Interval) → i ⊆ j → downMid i ⊆ j
⊆-downMid i j ((a , f) , (b , g) , (c , h))
  = (succ a , ap succℤ f)
  , fact'' 0 1 m₁ (codeOf i) (b , g) ⋆
  , fact'' 1 2 (codeOf i) m₂ (c , h) ⋆
  where
    m₁ = codeOf (downLeftₙ  j a)
    m₂ = codeOf (downRightₙ j a)

⊆-downRight : (i j : Interval) → i ⊆ j → downRight i ⊆ j
⊆-downRight i j ((a , f) , (b , g) , (c , h))
  = (succ a , ap succℤ f)
  , fact'' 0 2 m₁ (codeOf i) (b , g) ⋆
  , fact'' 2 2 (codeOf i) m₂ (c , h) ⋆
  where
    m₁ = codeOf (downLeftₙ  j a)
    m₂ = codeOf (downRightₙ j a)

𝓟 : Interval → 𝓤₀ ̇
𝓟 i = Σ (_⊆ i)

downLeft⋆ downMid⋆ downRight⋆ : {j : Interval} → 𝓟 j → 𝓟 j
downLeft⋆  {j} (i , f) = downLeft  i , ⊆-downLeft  i j f
downMid⋆   {j} (i , f) = downMid   i , ⊆-downMid   i j f
downRight⋆ {j} (i , f) = downRight i , ⊆-downRight i j f

⦅−1,1⦆ : 𝓟 [-1,1]
⦅−1,1⦆ = [-1,1] , ⊆-refl
-}

data 𝟛 : 𝓤₀ ̇ where
  −1 O +1 : 𝟛

match𝟛 : {X : 𝓤 ̇ } → (a : 𝟛) → X → X → X → X
match𝟛 −1 x y z = x
match𝟛  O x y z = y
match𝟛 +1 x y z = z

_∶∶_ : {X : 𝓤 ̇ } → X → (ℕ → X) → (ℕ → X)
(a ∶∶ α) 0 = a
(a ∶∶ α) (succ n) = α n

down : 𝟛 → (Interval → Interval)
down −1 = downLeft
down  O = downMid
down +1 = downRight

{-
⊆-down : (a : 𝟛) (i j : Interval) → i ⊆ j → down a i ⊆ j
⊆-down −1 = ⊆-downLeft
⊆-down  O = ⊆-downMid
⊆-down +1 = ⊆-downRight

down⋆ : 𝟛 → {j : Interval} → 𝓟 j → 𝓟 j
down⋆ a (i , e) = down a i , ⊆-down a i _ e
-}

[-1,1] : Interval
[-1,1] = (negsucc 0 , negsucc 0)

conv→ conv→' : (ℕ → 𝟛) → (ℕ → Interval)
conv→' α 0 = [-1,1]
conv→' α (succ n) = conv→ α n
conv→ α n = down (α n) (conv→' α n)

_-immediatelyDownFrom-_ : Interval → Interval → 𝓤₀ ̇
i -immediatelyDownFrom- j
 = (i ≡ downLeft j) ⊹ (i ≡ downMid j) ⊹ (i ≡ downRight j)

halfEq : (n : ℕ) → (n ≡ (n /2) +ℕ (n /2)) ⊹ (n ≡ succ ((n /2) +ℕ (n /2)))
halfEq 0 = inl refl
halfEq 1 = inr refl
halfEq (succ (succ n))
 = Cases (halfEq n)
    (λ f → inl (ap (succ ∘ succ) f ∙ ap succ (succ+ℕ (n /2) (n /2))))
    (λ g → inr (ap (succ ∘ succ) g ∙ ap succ (succ+ℕ (n /2) (succ (n /2)))))

ap-× : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x₁ x₂ : X} {y₁ y₂ : Y}
     → x₁ ≡ x₂ → y₁ ≡ y₂ → (x₁ , y₁) ≡ (x₂ , y₂)
ap-× {𝓤} {𝓥} {X} {Y} {x₁} {.x₁} {y₁} {.y₁} refl refl = refl

upRightEq : (i : Interval)
          → (i ≡ downLeft (upRight i)) ⊹ (i ≡ downMid (upRight i))
upRightEq (pos k , p)
  = Cases (halfEq k)
      (λ f → inl (ap-× (ap pos f ∙ +-pos (k /2) (k /2))
                       (succpredℤ p ⁻¹)))
      (λ g → inr (ap-× (ap pos g ∙ ap succℤ (+-pos (k /2) (k /2)))
                       (succpredℤ p ⁻¹)))
upRightEq (negsucc k , p)
  = Cases (halfEq k)
      (λ f → inr (ap-× (ap negsucc f ∙ +-negsucc (k /2) (k /2))
                       (succpredℤ p ⁻¹)))
      (λ g → inl (ap-× (ap negsucc g ∙ ap predℤ (+-negsucc (k /2) (k /2))
                       ∙ predsuccℤ (negsucc (k /2) +negsucc (k /2)))
                       (succpredℤ p ⁻¹)))

downLeftIsDown : (i : Interval) → downLeft i -immediatelyDownFrom- i
downLeftIsDown i = inl refl

downMidIsDown : (i : Interval) → downMid i -immediatelyDownFrom- i
downMidIsDown i = (inr ∘ inl) refl

downRightIsDown : (i : Interval) → downRight i -immediatelyDownFrom- i
downRightIsDown i = (inr ∘ inr) refl

downFromUpRight : (i : Interval) → i -immediatelyDownFrom- upRight i
downFromUpRight i
 = Cases (upRightEq i)
     (λ e → transport (_-immediatelyDownFrom- upRight i)
              (e ⁻¹) (downLeftIsDown (upRight i)))
     (λ e → transport (_-immediatelyDownFrom- upRight i)
              (e ⁻¹) (downMidIsDown (upRight i)))

downIsDown : (a : 𝟛) (i : Interval) → down a i -immediatelyDownFrom- i
downIsDown −1 = downLeftIsDown
downIsDown  O = downMidIsDown
downIsDown +1 = downRightIsDown

Real : 𝓤₀ ̇
Real = Σ x ꞉ (ℤ → Interval)
     , Π n ꞉ ℤ , (x n) -immediatelyDownFrom- (x (predℤ n))

upRightOrDownLeft : Interval → ℤ → Interval
upRightOrDownLeft i (negsucc n) = upRightₙ  i (succ n)
upRightOrDownLeft i (pos n)     = downLeftₙ i n

awayFromZero : ℤ → ℤ
awayFromZero (pos n) = succℤ (pos n)
awayFromZero (negsucc n) = predℤ (pos n)

upRightOrDownLeftIsDown : (i : Interval) (n m : ℤ) → m ≡ predℤ n
                        → upRightOrDownLeft i n
                         -immediatelyDownFrom-
                          upRightOrDownLeft i m
upRightOrDownLeftIsDown i (negsucc n) _ refl = downFromUpRight (upRightₙ i (succ n))
upRightOrDownLeftIsDown i (pos 0) _ refl = downFromUpRight i
upRightOrDownLeftIsDown i (pos (succ n)) _ refl = downLeftIsDown (downLeftₙ i n)

fromInterval : Interval → Real
fromInterval (k , p)
 = (λ n → upRightOrDownLeft (k , p) (n - p))
 , (λ n → upRightOrDownLeftIsDown (k , p) (n - p) (predℤ n - p) (ℤ-left-pred n (- p)))

CompactInterval : Interval → 𝓤₀ ̇
CompactInterval (k , p) = Σ (x , f) ꞉ Real , x p ≡ (k , p)

x' : (α : ℕ → 𝟛) → ℤ → Interval
x' α (negsucc n) = upRightₙ [-1,1] n
x' α (pos n)     = conv→ α n

f' : (α : ℕ → 𝟛) (n : ℤ) → x' α n -immediatelyDownFrom- x' α (predℤ n)
f' α (negsucc n)    = downFromUpRight (x' α (negsucc n))
f' α (pos 0)        = downIsDown (α 0) [-1,1]
f' α (pos (succ n)) = downIsDown (α (succ n)) (x' α (pos n))

conv-real : (ℕ → 𝟛) → CompactInterval [-1,1]
conv-real α = (x' α , f' α) , refl 

Interval-is-set : is-set Interval
Interval-is-set = ×-is-set ℤ-is-set ℤ-is-set

suc≢ : (n : ℕ) → n ≢ succ n
suc≢ zero = λ ()
suc≢ (succ n) = suc≢ n ∘ ap pred

sucsuc≢ : (n : ℕ) → n ≢ succ (succ n)
sucsuc≢ zero = λ ()
sucsuc≢ (succ n) = sucsuc≢ n ∘ ap pred

succ≢ : (n : ℤ) → n ≢ succℤ n
succ≢ (pos n) = suc≢ n ∘ pos-lc
succ≢ (negsucc 0) = λ ()
succ≢ (negsucc (succ n)) = suc≢ n ∘ negsucc-lc ∘ _⁻¹

succsucc≢ : (n : ℤ) → n ≢ succℤ (succℤ n)
succsucc≢ (pos n) = sucsuc≢ n ∘ pos-lc
succsucc≢ (negsucc 0) = λ ()
succsucc≢ (negsucc 1) = λ ()
succsucc≢ (negsucc (succ (succ n))) = sucsuc≢ n ∘ negsucc-lc ∘ _⁻¹

downLeft≢downMid : (i : Interval) → downMid i ≢ downLeft i
downLeft≢downMid (k , p) x = succ≢ (k + k) (ap pr₁ x ⁻¹) 

downMid≢downRight : (i : Interval) → downMid i ≢ downRight i
downMid≢downRight (k , p) x = succ≢ (succℤ (k + k)) (ap pr₁ x)

downLeft≢downRight : (i : Interval) → downLeft i ≢ downRight i
downLeft≢downRight (k , p) x = succsucc≢ (k + k) (ap pr₁ x)

immediatelyDown-isProp : (i j : Interval) → is-prop (i -immediatelyDownFrom- j)
immediatelyDown-isProp i j = +-is-prop Interval-is-set
                            (+-is-prop Interval-is-set Interval-is-set
                              (λ x y → downMid≢downRight j (x ⁻¹ ∙ y)))
                              (λ x → cases
                                (λ y → downLeft≢downMid j (y ⁻¹ ∙ x))
                                (λ y → downLeft≢downRight j (x ⁻¹ ∙ y)))

conv-real-∼ : (α : ℕ → 𝟛) (((x , f) , e) : CompactInterval [-1,1])
            → x' α ∼ x
            → conv-real α ≡ (x , f) , e
conv-real-∼ α ((x , f) , e) x∼x = to-Σ-≡ ((to-Σ-≡ (γ₀ , γ₁)) , γ₂) where
  γ₀ : x' α ≡ x
  γ₀ = dfunext (fe 𝓤₀ 𝓤₀) x∼x
  γ₁ = Π-is-prop (fe 𝓤₀ 𝓤₀) (λ z → immediatelyDown-isProp (x z) (x (predℤ z))) _ _
  γ₂ = Interval-is-set _ _

imeq : (i j : Interval) → i -immediatelyDownFrom- j
      → Σ b ꞉ 𝟛 , i ≡ down b j
imeq i j (inl      x ) = −1 , x
imeq i j (inr (inl y)) =  O , y
imeq i j (inr (inr z)) = +1 , z

imeq₁ = λ i j f → pr₁ (imeq i j f)
imeq₂ = λ i j f → pr₂ (imeq i j f)

real-conv' : CompactInterval [-1,1] → (ℕ → 𝟛)
real-conv' ((x , f) , _) n = imeq₁ (x (pos n)) (x (predℤ (pos n))) (f (pos n))

-- conv-real-∼ (real-conv' ((x , f) , e)) ((x , f) , e) x-eq where

_≣_ : Real → Real → 𝓤₀ ̇
(x , _) ≣ (y , _) = Σ k ꞉ ℤ , Π n ꞉ ℤ , (k ≤ℤ n → x n ≡ y n)

_≣'_ : CompactInterval [-1,1] → CompactInterval [-1,1] → 𝓤₀ ̇
(xf , _) ≣' (yg , _) = xf ≣ yg

eqx : (n : ℤ) → negsucc 0 ≤ℤ n
    → (x : CompactInterval [-1,1])
    → (pr₁ ∘ pr₁) ((conv-real ∘ real-conv') x) n ≡ ((pr₁ ∘ pr₁) x) n
eqx (pos n)     -1≤n ((x , f) , e)
 = ap (down (imeq₁ (x (pos n)) (x (predℤ (pos n))) (f (pos n)))) (γ n)
 ∙ imeq₂ (x (pos n)) (x (predℤ (pos n))) (f (pos n)) ⁻¹
 where
   γ : (n : ℕ) → conv→' (real-conv' ((x , f) , e)) n ≡ x (predℤ (pos n))
   γ zero = e ⁻¹
   γ (succ n)
    = eqx (pos n)
          (succ n , (ap succℤ (ℤ-pred-is-minus-one (pos n) ⁻¹) ∙ succpredℤ (pos n)))
          ((x , f) , e)
eqx (negsucc 0) _ ((x , f) , e) = e ⁻¹
eqx (negsucc (succ n)) -1≤n _   = 𝟘-elim {!!}

eqx* : ∀ x → (conv-real ∘ real-conv') x ≣' x
eqx* x = negsucc 0 , λ n o → eqx n o x

eqy : real-conv' ∘ conv-real ∼ id
eqy y = {!!}

{-
intInterval : ℤ → Interval
intInterval n = (n + n , pos 0)

natInterval : ℕ → Interval
natInterval n = intInterval (pos n)

intervalReal : Interval → Real
intervalReal (k , p) = ? {- λ n → match₃ (ℤ-trich n p)
                               (upRightₙ  (k , p) (abs (n - p)))
                                          (k , p)
                               (downLeftₙ (k , p) (abs (n - p))) -}

intReal : ℤ → Real
intReal = intervalReal ∘ intInterval

natReal : ℕ → Real
natReal = intervalReal ∘ natInterval

add : Real → Real → Real
add x y n = upRight ((((pr₁ ∘ x) (succℤ n)) + ((pr₁ ∘ y) (succℤ n))) , succℤ n)
-}
