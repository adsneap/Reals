\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Retracts where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import AlternativePlus

has-section : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } โ (X โ Y) โ ๐ค โ ๐ฅ ฬ
has-section r = ฮฃ s ๊ (codomain r โ domain r), r โ s โผ id

is-section : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } โ (X โ Y) โ ๐ค โ ๐ฅ ฬ
is-section s = ฮฃ r ๊ (codomain s โ domain s), r โ s โผ id

sections-are-lc : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } (s : X โ Y)
                โ is-section s โ left-cancellable s
sections-are-lc s (r , rs) {x} {x'} p = (rs x)โปยน โ ap r p โ rs x'

retract_of_ : ๐ค ฬ โ ๐ฅ ฬ โ ๐ค โ ๐ฅ ฬ
retract Y of X = ฮฃ r ๊ (X โ Y) , has-section r

retraction : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } โ retract X of Y โ (Y โ X)
retraction (r , s , rs) = r

section : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } โ retract X of Y โ (X โ Y)
section (r , s , rs) = s

retract-condition : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } (ฯ : retract X of Y)
                  โ retraction ฯ โ section ฯ โผ id
retract-condition (r , s , rs) = rs

retraction-has-section : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } (ฯ : retract X of Y)
                       โ has-section (retraction ฯ)
retraction-has-section (r , h) = h

retract-of-singleton : {X : ๐ค ฬ } {Y : ๐ฅ ฬ }
                     โ retract Y of X
                     โ is-singleton X
                     โ is-singleton Y
retract-of-singleton (r , s , rs) (c , ฯ) = r c , (ฮป y โ ap r (ฯ (s y)) โ rs y)

retract-of-prop : {X : ๐ค ฬ } {Y : ๐ฅ ฬ }
                โ retract Y of X
                โ is-prop X
                โ is-prop Y
retract-of-prop (r , s , rs) = subtype-of-prop-is-prop s (sections-are-lc s (r , rs))

ฮฃ-is-set : {X : ๐ค ฬ } {A : X โ ๐ฅ ฬ }
         โ is-set X
         โ ((x : X) โ is-set (A x))
         โ is-set (ฮฃ A)
ฮฃ-is-set {๐ค} {๐ฅ} {X} {A} i j {ฯ} {ฯ} = ฮณ
 where
  S = ฮฃ p ๊ prโ ฯ โก prโ ฯ , transport A p (prโ ฯ) โก prโ ฯ

  a : is-prop S
  a = ฮฃ-is-prop i (ฮป p โ j (prโ ฯ))

  b : retract (ฯ โก ฯ) of S
  b = to-ฮฃ-โก , from-ฮฃ-โก , tofrom-ฮฃ-โก

  ฮณ : is-prop (ฯ โก ฯ)
  ฮณ = retract-of-prop b a

identity-retraction : {X : ๐ค ฬ } โ retract X of X
identity-retraction = id , id , ฮป x โ refl

has-section-closed-under-โผ : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } (f g : X โ Y)
                           โ has-section f
                           โ g โผ f
                           โ has-section g
has-section-closed-under-โผ {๐ค} {๐ฅ} {X} {Y} f g (s , fs) h =
 (s , ฮป y โ g (s y) โกโจ h (s y) โฉ f (s y) โกโจ fs y โฉ y โ)

has-section-closed-under-โผ' : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } {f g : X โ Y}
                            โ has-section f
                            โ f โผ g
                            โ has-section g
has-section-closed-under-โผ' ise h = has-section-closed-under-โผ _ _ ise (ฮป x โ (h x)โปยน)

is-section-closed-under-โผ : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } (f g : X โ Y)
                          โ is-section f
                          โ  g โผ f
                          โ is-section g
is-section-closed-under-โผ {๐ค} {๐ฅ} {X} {Y} f g (r , rf) h =
  (r , ฮป x โ r (g x) โกโจ ap r (h x) โฉ
             r (f x) โกโจ rf x โฉ
             x       โ)

is-section-closed-under-โผ' : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } {f g : X โ Y}
                           โ is-section f
                           โ f โผ g
                           โ is-section g
is-section-closed-under-โผ' ise h = is-section-closed-under-โผ _ _ ise (ฮป x โ (h x)โปยน)

\end{code}

Surjection expressed in Curry-Howard logic amounts to retraction.

\begin{code}

has-section' : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } (f : X โ Y) โ ๐ค โ ๐ฅ ฬ
has-section' f = (y : codomain f) โ ฮฃ x ๊ domain f , f x โก y

retract_Of_ : ๐ค ฬ โ ๐ฅ ฬ โ ๐ค โ ๐ฅ ฬ
retract Y Of X = ฮฃ f ๊ (X โ Y) , has-section' f

retract-of-retract-Of : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } โ retract Y of X โ retract Y Of X
retract-of-retract-Of {๐ค} {๐ฅ} {X} {Y} ฯ = (retraction ฯ , hass)
 where
  hass : (y : Y) โ ฮฃ x ๊ X , retraction ฯ x โก y
  hass y = section ฯ y , retract-condition ฯ y

retract-Of-retract-of : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } โ retract Y Of X โ retract Y of X
retract-Of-retract-of {๐ค} {๐ฅ} {X} {Y} (f , hass) = (f , ฯ)
 where
  ฯ : ฮฃ s ๊ (Y โ X) , f โ s โผ id
  ฯ = (ฮป y โ prโ (hass y)) , (ฮป y โ prโ (hass y))

retracts-compose : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } {Z : ๐ฆ ฬ }
                 โ retract Y of X
                 โ retract Z of Y
                 โ retract Z of X
retracts-compose (r , s , rs) (r' , s' , rs') =
  r' โ r , s โ s' , ฮป z โ r' (r (s (s' z))) โกโจ ap r' (rs (s' z)) โฉ
                          r' (s' z)         โกโจ rs' z โฉ
                          z                 โ

ร-retract : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } {A : ๐ฆ ฬ } {B : ๐ฃ ฬ }
          โ retract X of A
          โ retract Y of B
          โ retract (X ร Y) of (A ร B)
ร-retract {๐ค} {๐ฅ} {๐ฆ} {๐ฃ} {X} {Y} {A} {B} (r , s , rs) (t , u , tu) = f , g , fg
 where
  f : A ร B โ X ร Y
  f (a , b) = (r a , t b)

  g : X ร Y โ A ร B
  g (x , y) = s x , u y

  fg : (z : X ร Y) โ f (g z) โก z
  fg (x , y) = to-ร-โก (rs x) (tu y)

+-retract : {X : ๐ค ฬ } {Y : ๐ฆ ฬ } {A : ๐ฅ ฬ } {B : ๐ฃ ฬ }
          โ retract X of A
          โ retract Y of B
          โ retract (X + Y) of (A + B)
+-retract {๐ค} {๐ฅ} {๐ฆ} {๐ฃ} {X} {Y} {A} {B} (r , s , rs) (t , u , tu) = f , g , fg
 where
  f : A + B โ X + Y
  f (inl a) = inl (r a)
  f (inr b) = inr (t b)

  g : X + Y โ A + B
  g (inl x) = inl (s x)
  g (inr y) = inr (u y)

  fg : (p : X + Y) โ f (g p) โก p
  fg (inl x) = ap inl (rs x)
  fg (inr y) = ap inr (tu y)

+'-retract-of-+ : {X Y : ๐ค ฬ }
                โ retract (X +' Y) of (X + Y)
+'-retract-of-+ {๐ค} {X} {Y} = f , g , fg
 where
  f : X + Y โ X +' Y
  f (inl x) = โ , x
  f (inr y) = โ , y

  g : X +' Y โ X + Y
  g (โ , x) = inl x
  g (โ , y) = inr y

  fg : (z : X +' Y) โ f (g z) โก z
  fg (โ , x) = refl
  fg (โ , y) = refl

+'-retract : {X Y : ๐ค ฬ } {A B : ๐ฅ ฬ }
           โ retract X of A
           โ retract Y of B
           โ retract (X +' Y) of (A +' B)
+'-retract {๐ค} {๐ฅ} {X} {Y} {A} {B} (r , s , rs) (t , u , tu) = f , g , fg
 where
  f : A +' B โ X +' Y
  f (โ , a) = โ , r a
  f (โ , b) = โ , t b

  g : X +' Y โ A +' B
  g (โ , x) = โ , s x
  g (โ , y) = โ , u y

  fg : (p : X +' Y) โ f (g p) โก p
  fg (โ , x) = ap (ฮป - โ (โ , -)) (rs x)
  fg (โ , y) = ap (ฮป - โ (โ , -)) (tu y)

ฮฃ-reindex-retract : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } {A : X โ ๐ฆ ฬ } (r : Y โ X)
                  โ has-section r โ retract (ฮฃ A) of (ฮฃ (A โ r))
ฮฃ-reindex-retract {๐ค} {๐ฅ} {๐ฆ} {X} {Y} {A} r (s , rs) = ฮณ , ฯ , ฮณฯ
 where
  ฮณ : (ฮฃ y ๊ Y , A (r y)) โ ฮฃ A
  ฮณ (y , a) = (r y , a)

  ฯ : ฮฃ A โ ฮฃ y ๊ Y , A (r y)
  ฯ (x , a) = (s x , back-transport A (rs x) a)

  ฮณฯ : (ฯ : ฮฃ A) โ ฮณ (ฯ ฯ) โก ฯ
  ฮณฯ (x , a) = to-ฮฃ-โก (rs x , p)
   where
    p : transport A (rs x) (back-transport A (rs x) a) โก a
    p = back-and-forth-transport (rs x)

ฮฃ-retract : {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ ) (B : X โ ๐ฆ ฬ )
          โ ((x : X) โ retract (A x) of (B x))
          โ retract (ฮฃ A) of (ฮฃ B)
ฮฃ-retract {๐ค} {๐ฅ} {๐ฆ} {X} A B ฯ = Natฮฃ R , Natฮฃ S , rs
 where
  R : (x : X) โ B x โ A x
  R x = retraction (ฯ x)

  S : (x : X) โ A x โ B x
  S x = section (ฯ x)

  RS : (x : X) (a : A x) โ R x (S x a) โก a
  RS x = retract-condition (ฯ x)

  rs : (ฯ : ฮฃ A) โ Natฮฃ R (Natฮฃ S ฯ) โก ฯ
  rs (x , a) = to-ฮฃ-โก' (RS x a)

retract-๐+๐-of-๐ : retract ๐ + ๐ of ๐
retract-๐+๐-of-๐ = f , (g , fg)
 where
  f : ๐ โ ๐ {๐คโ} + ๐ {๐คโ}
  f = ๐-cases (inl โ) (inr โ)

  g : ๐ + ๐ โ ๐
  g = cases (ฮป x โ โ) (ฮป x โ โ)

  fg : (x : ๐ + ๐) โ f (g x) โก x
  fg (inl โ) = refl
  fg (inr โ) = refl

\end{code}

TODO. Several retractions here are actually equivalences. So some code
should be generalized and moved to an equivalences module. Similarly,
some retracts proved here are also shown as equivalences in other
modules, and hence there is some amount of repetition that should be
removed. This is the result of (1) merging initially independent
developments, and (2) work over many years with uncontrolled growth.

\begin{code}

ฮฃ-retractโ : {X : ๐ค ฬ } {Y : X โ ๐ฅ ฬ } {A : ๐ฆ ฬ } {B : ๐ฃ ฬ }
           โ retract X of A
           โ ((x : X) โ retract  (Y x) of B)
           โ retract (ฮฃ Y) of (A ร B)
ฮฃ-retractโ {๐ค} {๐ฅ} {๐ฆ} {๐ฃ} {X} {Y} {A} {B} (r , s , rs) R = f , g , gf
 where
  ฯ : (x : X) โ B โ Y x
  ฯ x = retraction (R x)

  ฮณ : (x : X) โ Y x โ B
  ฮณ x = section (R x)

  ฯฮณ : (x : X) โ (y : Y x) โ ฯ x (ฮณ x y) โก y
  ฯฮณ x = retract-condition (R x)

  f : A ร B โ ฮฃ Y
  f (a , b) = r a , ฯ (r a) b

  g : ฮฃ Y โ A ร B
  g (x , y) = s x , ฮณ x y

  gf : (z : ฮฃ Y) โ f (g z) โก z
  gf (x , y) = to-ฮฃ-โก (rs x , l (rs x))
   where
    l : {x' : X} (p : x' โก x) โ transport Y p (ฯ x' (ฮณ x y)) โก y
    l refl = ฯฮณ x y

retract-๐+๐-of-โ : retract ๐ + ๐ of โ
retract-๐+๐-of-โ = r , s , rs
 where
  r : โ โ ๐ + ๐
  r zero = inl โ
  r (succ _) = inr โ

  s : ๐ + ๐ โ โ
  s (inl โ) = zero
  s (inr โ) = succ zero

  rs : (z : ๐ {๐คโ} + ๐ {๐คโ}) โ r (s z) โก z
  rs (inl โ) = refl
  rs (inr โ) = refl

\end{code}

Added 5th March 2019. Notation for composing retracts. I should have
added this ages ago to make the above proofs more readable.

\begin{code}

_โ_ : ๐ค ฬ โ ๐ฅ ฬ โ ๐ค โ ๐ฅ ฬ
Y โ X = retract Y of X

_โโจ_โฉ_ : (X : ๐ค ฬ ) {Y : ๐ฅ ฬ } {Z : ๐ฆ ฬ } โ X โ Y โ Y โ Z โ X โ Z
_ โโจ d โฉ e = retracts-compose e d

โ-refl : (X : ๐ค ฬ ) โ X โ X
โ-refl X = identity-retraction {universe-of X} {X}


_โ : (X : ๐ค ฬ ) โ X โ X
_โ = โ-refl

\end{code}

Fixities:

\begin{code}

infix  0 _โ_
infix  1 _โ
infixr 0 _โโจ_โฉ_

\end{code}

Added 20 February 2020 by Tom de Jong.

\begin{code}

ap-of-section-is-section : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } (s : X โ Y)
                         โ is-section s
                         โ (x x' : X) โ is-section (ap s {x} {x'})
ap-of-section-is-section {๐ค} {๐ฅ} {X} {Y} s (r , rs) x x' = ฯ , ฯap
 where
  ฯ : s x โก s x' โ x โก x'
  ฯ q = x        โกโจ (rs x) โปยน โฉ
        r (s x)  โกโจ ap r q โฉ
        r (s x') โกโจ rs x' โฉ
        x'       โ

  ฯap : (p : x โก x') โ ฯ (ap s p) โก p
  ฯap p = ฯ (ap s p)                          โกโจ by-definition โฉ
          (rs x) โปยน โ (ap r (ap s p) โ rs x') โกโจ i โฉ
          (rs x) โปยน โ ap r (ap s p) โ rs x'   โกโจ ii โฉ
          (rs x) โปยน โ ap (r โ s) p โ  rs x'   โกโจ iii โฉ
          ap id p                             โกโจ (ap-id-is-id' p)โปยน โฉ
          p                                   โ
   where
    i   = โassoc ((rs x) โปยน) (ap r (ap s p)) (rs x') โปยน
    ii  = ap (ฮป - โ (rs x) โปยน โ - โ rs x') (ap-ap s r p)
    iii = homotopies-are-natural'' (r โ s) id rs {x} {x'} {p}

\end{code}

I would phrase this in terms of fibers, but fiber is defined in UF-Equiv which
imports this file.

\begin{code}

ฮฃ-section-retract : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } {Z : ๐ฆ ฬ } (ฯ : Y โ Z) (g : X โ Y)
                  โ (y : Y)
                  โ (ฮฃ x ๊ X , g x โก y)
                  โ (ฮฃ x ๊ X , section ฯ (g x) โก section ฯ y)
ฮฃ-section-retract {๐ค} {๐ฅ} {๐ฆ} {X} {Y} {Z} (r , s , rs) g y =
 ฮฃ-retract (ฮป x โ g x โก y) (ฮป x โ s (g x) โก s y) ฮณ
  where
   ฮณ : (x : X) โ (g x โก y) โ (s (g x) โก s y)
   ฮณ x = ฯ , (ฯ , ฯฯ)
    where
     ฯ : g x โก y โ s (g x) โก s y
     ฯ = ap s

     ฯ : s (g x) โก s y โ g x โก y
     ฯ = prโ (ap-of-section-is-section s (r , rs) (g x) y)

     ฯฯ : (p : g x โก y) โ ฯ (ฯ p) โก p
     ฯฯ = prโ (ap-of-section-is-section s ((r , rs)) (g x) y)

\end{code}
