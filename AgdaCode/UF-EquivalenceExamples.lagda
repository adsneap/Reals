Martin Escardo, 2012-

Expanded on demand whenever a general equivalence is needed.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import Two-Properties
open import Plus-Properties
open import UF-Base
open import UF-Equiv
open import UF-FunExt
open import UF-Lower-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-PropIndexedPiSigma

module UF-EquivalenceExamples where

curry-uncurry' : funext ð¤ (ð¥ â ð¦)
               â funext (ð¤ â ð¥) ð¦
               â {X : ð¤ Ì } {Y : X â ð¥ Ì } {Z : (Î£ x ê X , Y x) â ð¦ Ì }
               â Î  Z â (Î  x ê X , Î  y ê Y x , Z (x , y))
curry-uncurry' {ð¤} {ð¥} {ð¦} fe fe' {X} {Y} {Z} = qinveq c (u , uc , cu)
 where
  c : (w : Î  Z) â ((x : X) (y : Y x) â Z (x , y))
  c f x y = f (x , y)

  u : ((x : X) (y : Y x) â Z (x , y)) â Î  Z
  u g (x , y) = g x y

  cu : â g â c (u g) â¡ g
  cu g = dfunext fe (Î» x â dfunext (lower-funext ð¤ ð¦ fe') (Î» y â refl))
  uc : â f â u (c f) â¡ f
  uc f = dfunext fe' (Î» w â refl)

curry-uncurry : (fe : FunExt)
              â {X : ð¤ Ì } {Y : X â ð¥ Ì } {Z : (Î£ x ê X , Y x) â ð¦ Ì }
              â Î  Z â (Î  x ê X , Î  y ê Y x , Z (x , y))
curry-uncurry {ð¤} {ð¥} {ð¦} fe = curry-uncurry' (fe ð¤ (ð¥ â ð¦)) (fe (ð¤ â ð¥) ð¦)

Î£-â¡-â : {X : ð¤ Ì } {A : X â ð¥ Ì } {Ï Ï : Î£ A}
      â (Ï â¡ Ï) â (Î£ p ê prâ Ï â¡ prâ Ï , transport A p (prâ Ï) â¡ prâ Ï)
Î£-â¡-â {ð¤} {ð¥} {X} {A} {x , a} {y , b} = qinveq from-Î£-â¡ (to-Î£-â¡ , Îµ , Î·)
 where
  Î· : (Ï : Î£ p ê x â¡ y , transport A p a â¡ b) â from-Î£-â¡ (to-Î£-â¡ Ï) â¡ Ï
  Î· (refl , refl) = refl
  Îµ : (q : x , a â¡ y , b) â to-Î£-â¡ (from-Î£-â¡ q) â¡ q
  Îµ refl = refl

Ã-â¡-â : {X : ð¤ Ì } {A : ð¥ Ì } {Ï Ï : X Ã A}
      â (Ï â¡ Ï) â (prâ Ï â¡ prâ Ï) Ã (prâ Ï â¡ prâ Ï)
Ã-â¡-â {ð¤} {ð¥} {X} {A} {x , a} {y , b} = qinveq from-Ã-â¡' (to-Ã-â¡' , (Îµ , Î·))
 where
  Î· : (t : (x â¡ y) Ã (a â¡ b)) â from-Ã-â¡' (to-Ã-â¡' t) â¡ t
  Î· (refl , refl) = refl

  Îµ : (u : x , a â¡ y , b) â to-Ã-â¡' (from-Ã-â¡' u) â¡ u
  Îµ refl = refl

Î£-assoc : {X : ð¤ Ì } {Y : X â ð¥ Ì } {Z : Î£ Y â ð¦ Ì }
        â Î£ Z â (Î£ x ê X , Î£ y ê Y x , Z (x , y))
Î£-assoc {ð¤} {ð¥} {ð¦} {X} {Y} {Z} = qinveq c (u , (Î» Ï â refl) , (Î» Ï â refl))
 where
  c : Î£ Z â Î£ x ê X , Î£ y ê Y x , Z (x , y)
  c ((x , y) , z) = (x , (y , z))

  u : (Î£ x ê X , Î£ y ê Y x , Z (x , y)) â Î£ Z
  u (x , (y , z)) = ((x , y) , z)

Î£-flip : {X : ð¤ Ì } {Y : ð¥ Ì } {A : X â Y â ð¦ Ì }
       â (Î£ x ê X , Î£ y ê Y , A x y) â (Î£ y ê Y , Î£ x ê X , A x y)
Î£-flip {ð¤} {ð¥} {ð¦} {X} {Y} {A} = qinveq f (g , Îµ , Î·)
 where
  f : (Î£ x ê X , Î£ y ê Y , A x y) â (Î£ y ê Y , Î£ x ê X , A x y)
  f (x , y , p) = y , x , p

  g : (Î£ y ê Y , Î£ x ê X , A x y) â (Î£ x ê X , Î£ y ê Y , A x y)
  g (y , x , p) = x , y , p

  Îµ : â Ï â g (f Ï) â¡ Ï
  Îµ (x , y , p) = refl

  Î· : â Ï â f (g Ï) â¡ Ï
  Î· (y , x , p) = refl

Î£-cong : {X : ð¤ Ì } {Y : X â ð¥ Ì } {Y' : X â ð¦ Ì }
       â ((x : X) â Y x â Y' x) â Î£ Y â Î£ Y'
Î£-cong {ð¤} {ð¥} {ð¦} {X} {Y} {Y'} Ï = (F , (G , FG) , (H , HF))
 where
  f : (x : X) â Y x â Y' x
  f x = prâ (Ï x)

  g : (x : X) â Y' x â Y x
  g x = prâ (prâ (prâ (Ï x)))

  fg : (x : X) (y' : Y' x) â f x (g x y') â¡ y'
  fg x = prâ (prâ (prâ (Ï x)))

  h : (x : X) â Y' x â Y x
  h x = prâ (prâ (prâ (Ï x)))

  hf : (x : X) (y : Y x) â h x (f x y) â¡ y
  hf x = prâ (prâ (prâ (Ï x)))

  F : Î£ Y â Î£ Y'
  F (x , y) = x , f x y

  G : Î£ Y' â Î£ Y
  G (x , y') = x , g x y'

  H : Î£ Y' â Î£ Y
  H (x , y') = x , h x y'

  FG : (w' : Î£ Y') â F (G w') â¡ w'
  FG (x , y') = to-Î£-â¡' (fg x y')

  HF : (w : Î£ Y) â H (F w) â¡ w
  HF (x , y) = to-Î£-â¡' (hf x y)

Î Î£-distr-â : {X : ð¤ Ì } {A : X â ð¥ Ì } {P : (x : X) â A x â ð¦ Ì }
           â (Î  x ê X , Î£ a ê A x , P x a) â (Î£ f ê Î  A , Î  x ê X , P x (f x))
Î Î£-distr-â {ð¤} {ð¥} {ð¦} {X} {A} {P} = qinveq Î Î£-distr (Î Î£-distr-back , Îµ , Î·)
 where
  Î· :  Î Î£-distr {ð¤} {ð¥} {ð¦} {X} {A} {P} â Î Î£-distr-back â¼ id
  Î· _ = refl

  Îµ : Î Î£-distr-back â Î Î£-distr â¼ id
  Îµ _ = refl

Î£+ : (X : ð¤ Ì ) (A : X â ð¥ Ì ) (B : X â ð¦ Ì )
   â (Î£ x ê X , A x + B x)
   â ((Î£ x ê X , A x) + (Î£ x ê X , B x))
Î£+ X A B = qinveq f (g , Î· , Îµ)
 where
  f : (Î£ x ê X , A x + B x) â (Î£ x ê X , A x) + (Î£ x ê X , B x)
  f (x , inl a) = inl (x , a)
  f (x , inr b) = inr (x , b)

  g : ((Î£ x ê X , A x) + (Î£ x ê X , B x)) â (Î£ x ê X , A x + B x)
  g (inl (x , a)) = x , inl a
  g (inr (x , b)) = x , inr b

  Î· : g â f â¼ id
  Î· (x , inl a) = refl
  Î· (x , inr b) = refl

  Îµ : f â g â¼ id
  Îµ (inl (x , a)) = refl
  Îµ (inr (x , b)) = refl

\end{code}

The following name is badly chosen, and probably should have been used
for the above:

\begin{code}

Î£+distr : (X : ð¤ Ì ) (Y : ð¥ Ì ) (A : X + Y â ð¦ Ì )
        â (Î£ x ê X , A (inl x)) + (Î£ y ê Y , A (inr y))
        â (Î£ z ê X + Y , A z)
Î£+distr X Y A = qinveq f (g , Î· , Îµ)
 where
  f : (Î£ x ê X , A (inl x)) + (Î£ y ê Y , A (inr y)) â (Î£ z ê X + Y , A z)
  f (inl (x , a)) = inl x , a
  f (inr (y , a)) = inr y , a

  g : (Î£ z ê X + Y , A z) â (Î£ x ê X , A (inl x)) + (Î£ y ê Y , A (inr y))
  g (inl x , a) = inl (x , a)
  g (inr y , a) = inr (y , a)

  Î· : g â f â¼ id
  Î· (inl _) = refl
  Î· (inr _) = refl

  Îµ : f â g â¼ id
  Îµ (inl _ , _) = refl
  Îµ (inr _ , _) = refl

Î -cong : funext ð¤ ð¥
       â funext ð¤ ð¦
       â (X : ð¤ Ì ) (Y : X â ð¥ Ì ) (Y' : X â ð¦ Ì )
       â ((x : X) â Y x â Y' x) â Î  Y â Î  Y'
Î -cong fe fe' X Y Y' Ï = (F , (G , FG) , (H , HF))
 where
  f : (x : X) â Y x â Y' x
  f x = prâ (Ï x)

  g : (x : X) â Y' x â Y x
  g x =  prâ (prâ (prâ (Ï x)))

  fg : (x : X) (y' : Y' x) â f x (g x y') â¡ y'
  fg x = prâ (prâ (prâ (Ï x)))

  h : (x : X) â Y' x â Y x
  h x = prâ (prâ (prâ (Ï x)))

  hf : (x : X) (y : Y x) â h x (f x y) â¡ y
  hf x = prâ (prâ (prâ (Ï x)))

  F : ((x : X) â Y x) â ((x : X) â Y' x)
  F = Î» z x â prâ (Ï x) (z x)

  G : ((x : X) â Y' x) â (x : X) â Y x
  G u x = g x (u x)

  H : ((x : X) â Y' x) â (x : X) â Y x
  H u' x = h x (u' x)

  FG :  (w' : ((x : X) â Y' x)) â F (G w') â¡ w'
  FG w' = dfunext fe' FG'
   where
    FG' : (x : X) â F (G w') x â¡ w' x
    FG' x = fg x (w' x)

  HF : (w : ((x : X) â Y x)) â H (F w) â¡ w
  HF w = dfunext fe GF'
   where
    GF' : (x : X) â H (F w) x â¡ w x
    GF' x = hf x (w x)

\end{code}

An application of Î -cong is the following:

\begin{code}

â-funextâ : funext ð¤ (ð¥ â ð¦)
          â funext ð¥ ð¦
          â {X : ð¤ Ì } {Y : X â ð¥ Ì } {A : (x : X) â Y x â ð¦ Ì }
            (f g : (x : X) (y : Y x) â A x y) â (f â¡ g) â (â x y â f x y â¡ g x y)
â-funextâ fe fe' {X} f g =
 (f â¡ g)            ââ¨ â-funext fe f g â©
 (f â¼ g)            ââ¨ Î -cong fe fe X
                        (Î» x â f x â¡ g x)
                        (Î» x â f x â¼ g x)
                        (Î» x â â-funext fe' (f x) (g x))â©
 (â x â f x â¼ g x)  â 

ð-lneutral : {Y : ð¤ Ì } â ð {ð¥} Ã Y â Y
ð-lneutral {ð¤} {ð¥} {Y} = qinveq f (g , Îµ , Î·)
 where
   f : ð Ã Y â Y
   f (o , y) = y

   g : Y â ð Ã Y
   g y = (â , y)

   Î· : â x â f (g x) â¡ x
   Î· y = refl

   Îµ : â z â g (f z) â¡ z
   Îµ (o , y) = ap (_, y) (ð-is-prop â o)

Ã-comm : {X : ð¤ Ì } {Y : ð¥ Ì } â X Ã Y â Y Ã X
Ã-comm {ð¤} {ð¥} {X} {Y} = qinveq f (g , Îµ , Î·)
 where
  f : X Ã Y â Y Ã X
  f (x , y) = (y , x)

  g : Y Ã X â X Ã Y
  g (y , x) = (x , y)

  Î· : â z â f (g z) â¡ z
  Î· z = refl

  Îµ : â t â g (f t) â¡ t
  Îµ t = refl

ð-rneutral : {Y : ð¤ Ì } â Y Ã ð {ð¥} â Y
ð-rneutral {ð¤} {ð¥} {Y} = Y Ã ð ââ¨ Ã-comm â©
                          ð Ã Y ââ¨ ð-lneutral {ð¤} {ð¥} â©
                          Y     â 

+comm : {X : ð¤ Ì } {Y : ð¥ Ì } â X + Y â Y + X
+comm {ð¤} {ð¥} {X} {Y} = qinveq f (g , Î· , Îµ)
 where
   f : X + Y â Y + X
   f (inl x) = inr x
   f (inr y) = inl y

   g : Y + X â X + Y
   g (inl y) = inr y
   g (inr x) = inl x

   Îµ : (t : Y + X) â (f â g) t â¡ t
   Îµ (inl y) = refl
   Îµ (inr x) = refl

   Î· : (u : X + Y) â (g â f) u â¡ u
   Î· (inl x) = refl
   Î· (inr y) = refl

ð-rneutral : {X : ð¤ Ì } â X â X + ð {ð¥}
ð-rneutral {ð¤} {ð¥} {X} = qinveq f (g , Î· , Îµ)
 where
   f : X â X + ð
   f = inl

   g : X + ð â X
   g (inl x) = x
   g (inr y) = ð-elim y

   Îµ : (y : X + ð) â (f â g) y â¡ y
   Îµ (inl x) = refl
   Îµ (inr y) = ð-elim y

   Î· : (x : X) â (g â f) x â¡ x
   Î· x = refl

ð-rneutral' : {X : ð¤ Ì } â X + ð {ð¥} â X
ð-rneutral' {ð¤} {ð¥} = â-sym (ð-rneutral {ð¤} {ð¥})

ð-lneutral : {X : ð¤ Ì } â ð {ð¥} + X â X
ð-lneutral {ð¤} {ð¥} {X} = (ð + X) ââ¨ +comm â©
                         (X + ð) ââ¨ ð-rneutral' {ð¤} {ð¥} â©
                         X       â 

one-ð-only : ð {ð¤} â ð {ð¥}
one-ð-only = qinveq ð-elim (ð-elim , ð-induction , ð-induction)

one-ð-only : (ð¤ ð¥ : Universe) â ð {ð¤} â ð {ð¥}
one-ð-only _ _ = unique-to-ð , (unique-to-ð , (Î» {â â refl})) , (unique-to-ð , (Î» {â â refl}))

+assoc : {X : ð¤ Ì } {Y : ð¥ Ì } {Z : ð¦ Ì } â (X + Y) + Z â X + (Y + Z)
+assoc {ð¤} {ð¥} {ð¦} {X} {Y} {Z} = qinveq f (g , Î· , Îµ)
 where
   f : (X + Y) + Z â X + (Y + Z)
   f (inl (inl x)) = inl x
   f (inl (inr y)) = inr (inl y)
   f (inr z)       = inr (inr z)

   g : X + (Y + Z) â (X + Y) + Z
   g (inl x)       = inl (inl x)
   g (inr (inl y)) = inl (inr y)
   g (inr (inr z)) = inr z

   Îµ : (t : X + (Y + Z)) â (f â g) t â¡ t
   Îµ (inl x)       = refl
   Îµ (inr (inl y)) = refl
   Îµ (inr (inr z)) = refl

   Î· : (u : (X + Y) + Z) â (g â f) u â¡ u
   Î· (inl (inl x)) = refl
   Î· (inl (inr x)) = refl
   Î· (inr x)       = refl

+cong : {X : ð¤ Ì } {Y : ð¥ Ì } {A : ð¦ Ì } {B : ð£ Ì }
      â X â A â Y â B â X + Y â A + B
+cong {ð¤} {ð¥} {ð¦} {ð£} {X} {Y} {A} {B} (f , (g , e) , (g' , d)) (Ï , (Î³ , Îµ) , (Î³' , Î´)) =
 +functor f Ï , (+functor g Î³ , E) , (+functor g' Î³' , D)
 where
  E : (c : A + B) â +functor f Ï (+functor g Î³ c) â¡ c
  E (inl a) = ap inl (e a)
  E (inr b) = ap inr (Îµ b)

  D : (z : X + Y) â +functor g' Î³' (+functor f Ï z) â¡ z
  D (inl x) = ap inl (d x)
  D (inr y) = ap inr (Î´ y)

Ãð : {X : ð¤ Ì } â ð {ð¥} â X Ã ð {ð¦}
Ãð {ð¤} {ð¥} {ð¦} {X} = qinveq f (g , Î· , Îµ)
 where
   f : ð â X Ã ð
   f = unique-from-ð

   g : X Ã ð â ð
   g (x , y) = ð-elim y

   Îµ : (t : X Ã ð) â (f â g) t â¡ t
   Îµ (x , y) = ð-elim y

   Î· : (u : ð) â (g â f) u â¡ u
   Î· = ð-induction

ðdistr : {X : ð¤ Ì } {Y : ð¥ Ì } â X Ã Y + X â X Ã (Y + ð {ð¦})
ðdistr {ð¤} {ð¥} {ð¦} {X} {Y} = f , (g , Îµ) , (g , Î·)
 where
   f : X Ã Y + X â X Ã (Y + ð)
   f (inl (x , y)) = x , inl y
   f (inr x)       = x , inr â

   g : X Ã (Y + ð) â X Ã Y + X
   g (x , inl y) = inl (x , y)
   g (x , inr O) = inr x

   Îµ : (t : X Ã (Y + ð)) â (f â g) t â¡ t
   Îµ (x , inl y) = refl
   Îµ (x , inr â) = refl

   Î· : (u : X Ã Y + X) â (g â f) u â¡ u
   Î· (inl (x , y)) = refl
   Î· (inr x)       = refl

Ap+ : {X : ð¤ Ì } {Y : ð¥ Ì } (Z : ð¦ Ì ) â X â Y â X + Z â Y + Z
Ap+ {ð¤} {ð¥} {ð¦} {X} {Y} Z (f , (g , Îµ) , (h , Î·)) = f' , (g' , Îµ') , (h' , Î·')
 where
   f' : X + Z â Y + Z
   f' (inl x) = inl (f x)
   f' (inr z) = inr z

   g' : Y + Z â X + Z
   g' (inl y) = inl (g y)
   g' (inr z) = inr z

   h' : Y + Z â X + Z
   h' (inl y) = inl (h y)
   h' (inr z) = inr z

   Îµ' : (t : Y + Z) â (f' â g') t â¡ t
   Îµ' (inl y) = ap inl (Îµ y)
   Îµ' (inr z) = refl

   Î·' : (u : X + Z) â (h' â f') u â¡ u
   Î·' (inl x) = ap inl (Î· x)
   Î·' (inr z) = refl

Ãcomm : {X : ð¤ Ì } {Y : ð¥ Ì } â X Ã Y â Y Ã X
Ãcomm {ð¤} {ð¥} {X} {Y} = f , (g , Îµ) , (g , Î·)
 where
   f : X Ã Y â Y Ã X
   f (x , y) = (y , x)

   g : Y Ã X â X Ã Y
   g (y , x) = (x , y)

   Îµ : (t : Y Ã X) â (f â g) t â¡ t
   Îµ (y , x) = refl

   Î· : (u : X Ã Y) â (g â f) u â¡ u
   Î· (x , y) = refl

Ãfunctor : {X : ð¤ Ì } {Y : ð¥ Ì } {A : ð¦ Ì } {B : ð£ Ì }
         â (X â A) â (Y â B) â X Ã Y â A Ã B
Ãfunctor f g (x , y) = f x , g y

Ã-cong : {X : ð¤ Ì } {Y : ð¥ Ì } {A : ð¦ Ì } {B : ð£ Ì }
      â X â A â Y â B â X Ã Y â A Ã B
Ã-cong {ð¤} {ð¥} {ð¦} {ð£} {X} {Y} {A} {B} (f , (g , e) , (g' , d)) (Ï , (Î³ , Îµ) , (Î³' , Î´)) =
 Ãfunctor f Ï , (Ãfunctor g Î³ , E) , (Ãfunctor g' Î³' , D)
 where
  E : (c : A Ã B) â Ãfunctor f Ï (Ãfunctor g Î³ c) â¡ c
  E (a , b) = to-Ã-â¡ (e a) (Îµ b)

  D : (z : X Ã Y) â Ãfunctor g' Î³' (Ãfunctor f Ï z) â¡ z
  D (x , y) = to-Ã-â¡ (d x) (Î´ y)

ðâ : {X : ð¤ Ì }
   â funext ð¦ ð¤
   â ð {ð¥} â (ð {ð¦} â X)
ðâ {ð¤} {ð¥} {ð¦} {X} fe = qinveq f (g , Îµ , Î·)
 where
  f : ð â ð â X
  f â y = ð-elim y

  g : (ð â X) â ð
  g h = â

  Î· : (h : ð â X) â f (g h) â¡ h
  Î· h = dfunext fe (Î» z â ð-elim z)

  Îµ : (y : ð) â g (f y) â¡ y
  Îµ â = refl

ðâ : {X : ð¤ Ì }
   â funext ð¥ ð¤
   â X â (ð {ð¥} â X)
ðâ {ð¤} {ð¥} {X} fe = qinveq f (g , Îµ , Î·)
 where
  f : X â ð â X
  f x â = x

  g : (ð â X) â X
  g h = h â

  Î· : (h : ð â X) â f (g h) â¡ h
  Î· h = dfunext fe Î³
   where
    Î³ : (t : ð) â f (g h) t â¡ h t
    Î³ â = refl

  Îµ : (x : X) â g (f x) â¡ x
  Îµ x = refl

âð : {X : ð¤ Ì } â funext ð¤ ð¥
   â (X â ð {ð¥}) â ð {ð¥}
âð {ð¤} {ð¥} {X} fe = qinveq f (g , Îµ , Î·)
 where
  f : (X â ð) â ð
  f = unique-to-ð

  g : (t : ð) â X â ð
  g t = unique-to-ð

  Îµ : (Î± : X â ð) â g â â¡ Î±
  Îµ Î± = dfunext fe Î» (x : X) â ð-is-prop (g â x) (Î± x)

  Î· : (t : ð) â â â¡ t
  Î· = ð-is-prop â


Î Ã+ : {X : ð¤ Ì } {Y : ð¥ Ì } {A : X + Y â ð¦ Ì } â funext (ð¤ â ð¥) ð¦
    â (Î  x ê X , A (inl x)) Ã (Î  y ê Y , A (inr y))
    â (Î  z ê X + Y , A z)

Î Ã+ {ð¤} {ð¥} {ð¦} {X} {Y} {A} fe = qinveq f (g , Îµ , Î·)
 where
  f : (Î  x ê X , A (inl x)) Ã (Î  y ê Y , A (inr y)) â (Î  z ê X + Y , A z)
  f (l , r) (inl x) = l x
  f (l , r) (inr y) = r y

  g : (Î  z ê X + Y , A z) â (Î  x ê X , A (inl x)) Ã (Î  y ê Y , A (inr y))
  g h = h â inl , h â inr

  Î· : f â g â¼ id
  Î· h = dfunext fe Î³
   where
    Î³ : (z : X + Y) â (f â g) h z â¡ h z
    Î³ (inl x) = refl
    Î³ (inr y) = refl

  Îµ : g â f â¼ id
  Îµ (l , r) = refl


+â : {X : ð¤ Ì } {Y : ð¥ Ì } {Z : ð¦ Ì }
   â funext (ð¤ â ð¥) ð¦
   â ((X + Y) â Z) â (X â Z) Ã (Y â Z)
+â fe = â-sym (Î Ã+ fe)

âÃ : {A : ð¤ Ì } {X : A â ð¥ Ì } {Y : A â ð¦ Ì }
   â ((a : A) â X a Ã Y a)  â Î  X Ã Î  Y
âÃ {ð¤} {ð¥} {ð¦} {A} {X} {Y} = qinveq f (g , Îµ , Î·)
 where
  f : ((a : A) â X a Ã Y a) â Î  X Ã Î  Y
  f Ï = (Î» a â prâ (Ï a)) , (Î» a â prâ (Ï a))

  g : Î  X Ã Î  Y â (a : A) â X a Ã Y a
  g (Î³ , Î´) a = Î³ a , Î´ a

  Îµ : (Ï : (a : A) â X a Ã Y a) â g (f Ï) â¡ Ï
  Îµ Ï = refl

  Î· : (Î± : Î  X Ã Î  Y) â f (g Î±) â¡ Î±
  Î· (Î³ , Î´) = refl

âcong : {X : ð¤ Ì } {Y : ð¥ Ì } {A : ð¦ Ì } {B : ð£ Ì }
      â funext ð¦ ð£
      â funext ð¤ ð¥
      â X â A â Y â B â (X â Y) â (A â B)
âcong {ð¤} {ð¥} {ð¦} {ð£} {X} {Y} {A} {B} fe fe' (f , i) (Ï , j) =
 H (equivs-are-qinvs f i) (equivs-are-qinvs Ï j)
 where
  H : qinv f â qinv Ï â (X â Y) â (A â B)
  H (g , e , d) (Î³ , Îµ , Î´) =  F , (G , E) , (G , D)
   where
    F : (X â Y) â (A â B)
    F h = Ï â h â g

    G : (A â B) â (X â Y)
    G k = Î³ â k â f

    E : (k : A â B) â F (G k) â¡ k
    E k = dfunext fe (Î» a â Î´ (k (f (g a))) â ap k (d a))

    D : (h : X â Y) â G (F h) â¡ h
    D h = dfunext fe' (Î» x â Îµ (h (g (f x))) â ap h (e x))

âcong' : {X : ð¤ Ì } {Y : ð¥ Ì } {B : ð£ Ì }
       â funext ð¤ ð£
       â funext ð¤ ð¥
       â Y â B â (X â Y) â (X â B)
âcong' {ð¤} {ð¥} {ð£} {X} {Y} {B} fe fe' = âcong fe fe' (â-refl X)

âcong'' : {X : ð¤ Ì } {Y : ð¥ Ì } {A : ð¦ Ì }
        â funext ð¦ ð¥
        â funext ð¤ ð¥
        â X â A â (X â Y) â (A â Y)
âcong'' {ð¤} {ð¥} {ð£} {X} {Y} {B} fe fe' e = âcong fe fe' e (â-refl Y)

prâ-equivalence : (X : ð¤ Ì ) (A : X â ð¥ Ì )
                â ((x : X) â is-singleton (A x))
                â is-equiv (prâ {ð¤} {ð¥} {X} {A})
prâ-equivalence {ð¤} {ð¥} X A iss = qinvs-are-equivs prâ (g , Îµ , Î·)
 where
  g : X â Î£ A
  g x = x , prâ (iss x)

  Î· : (x : X) â prâ (g x) â¡ x
  Î· x = refl

  Îµ : (Ï : Î£ A) â g (prâ Ï) â¡ Ï
  Îµ (x , a) = to-Î£-â¡ (Î· x , singletons-are-props (iss x) _ _)

NatÎ£-fiber-equiv : {X : ð¤ Ì } (A : X â ð¥ Ì ) (B : X â ð¦ Ì ) (Î¶ : Nat A B)
                 â (x : X) (b : B x) â fiber (Î¶ x) b â fiber (NatÎ£ Î¶) (x , b)
NatÎ£-fiber-equiv A B Î¶ x b = qinveq (f b) (g b , Îµ b , Î· b)
 where
  f : (b : B x) â fiber (Î¶ x) b â fiber (NatÎ£ Î¶) (x , b)
  f . (Î¶ x a) (a , refl) = (x , a) , refl

  g : (b : B x) â fiber (NatÎ£ Î¶) (x , b) â fiber (Î¶ x) b
  g . (Î¶ x a) ((.x , a) , refl) = a , refl

  Îµ : (b : B x) (w : fiber (Î¶ x) b) â g b (f b w) â¡ w
  Îµ . (Î¶ x a) (a , refl) = refl

  Î· : (b : B x) (t : fiber (NatÎ£ Î¶) (x , b)) â f b (g b t) â¡ t
  Î· b (a , refl) = refl

NatÎ£-vv-equiv : {X : ð¤ Ì } (A : X â ð¥ Ì ) (B : X â ð¦ Ì ) (Î¶ : Nat A B)
              â ((x : X) â is-vv-equiv (Î¶ x))
              â is-vv-equiv (NatÎ£ Î¶)
NatÎ£-vv-equiv A B Î¶ i (x , b) = equiv-to-singleton
                                   (â-sym (NatÎ£-fiber-equiv A B Î¶ x b))
                                   (i x b)

NatÎ£-vv-equiv-converse : {X : ð¤ Ì } (A : X â ð¥ Ì ) (B : X â ð¦ Ì ) (Î¶ : Nat A B)
                       â is-vv-equiv (NatÎ£ Î¶)
                       â ((x : X) â is-vv-equiv (Î¶ x))
NatÎ£-vv-equiv-converse A B Î¶ e x b = equiv-to-singleton
                                      (NatÎ£-fiber-equiv A B Î¶ x b)
                                      (e (x , b))

NatÎ£-equiv : {X : ð¤ Ì } (A : X â ð¥ Ì ) (B : X â ð¦ Ì ) (Î¶ : Nat A B)
           â ((x : X) â is-equiv (Î¶ x))
           â is-equiv (NatÎ£ Î¶)
NatÎ£-equiv A B Î¶ i = vv-equivs-are-equivs
                         (NatÎ£ Î¶)
                         (NatÎ£-vv-equiv A B Î¶
                           (Î» x â equivs-are-vv-equivs (Î¶ x) (i x)))

NatÎ£-equiv-converse : {X : ð¤ Ì } (A : X â ð¥ Ì ) (B : X â ð¦ Ì ) (Î¶ : Nat A B)
                    â is-equiv (NatÎ£ Î¶)
                    â ((x : X) â is-equiv (Î¶ x))
NatÎ£-equiv-converse A B Î¶ e x = vv-equivs-are-equivs (Î¶ x)
                                 (NatÎ£-vv-equiv-converse A B Î¶
                                   (equivs-are-vv-equivs (NatÎ£ Î¶) e) x)

NatÎ£-equiv-gives-fiberwise-equiv : {X : ð¤ Ì } {A : X â ð¥ Ì } {B : X â ð¦ Ì }
                                   (Ï : Nat A B)
                                 â is-equiv (NatÎ£ Ï)
                                 â is-fiberwise-equiv Ï
NatÎ£-equiv-gives-fiberwise-equiv = NatÎ£-equiv-converse _ _

Î£-cong' : {X : ð¤ Ì } (A : X â ð¥ Ì ) (B : X â ð¦ Ì )
        â ((x : X) â A x â B x) â Î£ A â Î£ B
Î£-cong' A B e = NatÎ£ (Î» x â prâ (e x)) , NatÎ£-equiv A B (Î» x â prâ (e x)) (Î» x â prâ (e x))

NatÎ£-equiv' : {X : ð¤ Ì } (A : X â ð¥ Ì ) (B : X â ð¦ Ì ) (Î¶ : Nat A B)
            â ((x : X) â is-equiv (Î¶ x))
            â is-equiv (NatÎ£ Î¶)
NatÎ£-equiv' A B Î¶ i = ((s , Î¶s), (r , rÎ¶))
 where
  s : Î£ B â Î£ A
  s (x , b) = x , prâ (prâ (i x)) b

  Î¶s : (Î² : Î£ B) â (NatÎ£ Î¶ â s) Î² â¡ Î²
  Î¶s (x , b) = ap (Î» - â (x , -)) (prâ (prâ (i x)) b)

  r : Î£ B â Î£ A
  r (x , b) = x , (prâ (prâ (i x)) b)

  rÎ¶ : (Î± : Î£ A) â (r â NatÎ£ Î¶) Î± â¡ Î±
  rÎ¶ (x , a) = ap (Î» - â (x , -)) (prâ (prâ (i x)) a)

Î£-change-of-variable' : {X : ð¤ Ì } {Y : ð¥ Ì } (A : X â ð¦ Ì ) (g : Y â X)
                       â is-hae g
                       â Î£ Î³ ê ((Î£ y ê Y , A (g y)) â Î£ A) , qinv Î³
Î£-change-of-variable' {ð¤} {ð¥} {ð¦} {X} {Y} A g (f , Î· , Îµ , Î±) = Î³ , Ï , ÏÎ³ , Î³Ï
 where
  Î³ : (Î£ y ê Y , A (g y)) â Î£ A
  Î³ (y , a) = (g y , a)

  Ï : Î£ A â Î£ y ê Y , A (g y)
  Ï (x , a) = (f x , back-transport A (Îµ x) a)

  Î³Ï : (Ï : Î£ A) â Î³ (Ï Ï) â¡ Ï
  Î³Ï (x , a) = to-Î£-â¡ (Îµ x , p)
   where
    p : transport A (Îµ x) (back-transport A (Îµ x) a) â¡ a
    p = back-and-forth-transport (Îµ x)

  ÏÎ³ : (Ï : (Î£ y ê Y , A (g y))) â Ï (Î³ Ï) â¡ Ï
  ÏÎ³ (y , a) = to-Î£-â¡ (Î· y , q)
   where
    q = transport (Î» - â A (g -)) (Î· y) (back-transport A (Îµ (g y)) a) â¡â¨ i â©
        transport A (ap g (Î· y)) (back-transport A (Îµ (g y)) a)        â¡â¨ ii â©
        transport A (Îµ (g y)) (back-transport A (Îµ (g y)) a)           â¡â¨ iii â©
        a                                                              â
     where
      i   = transport-ap A g (Î· y)
      ii  = ap (Î» - â transport A - (back-transport A (Îµ (g y)) a)) (Î± y)
      iii = back-and-forth-transport (Îµ (g y))

Î£-change-of-variable : {X : ð¤ Ì } {Y : ð¥ Ì } (A : X â ð¦ Ì ) (g : Y â X)
                     â is-equiv g â (Î£ y ê Y , A (g y)) â Î£ A
Î£-change-of-variable {ð¤} {ð¥} {ð¦} {X} {Y} A g e = Î³ , qinvs-are-equivs Î³ q
 where
  Î³ :  (Î£ y ê Y , A (g y)) â Î£ A
  Î³ = prâ (Î£-change-of-variable' A g (equivs-are-haes g e))

  q :  qinv Î³
  q = prâ (Î£-change-of-variable' A g (equivs-are-haes g e))

NatÎ -fiber-equiv : {X : ð¤ Ì } (A : X â ð¥ Ì ) (B : X â ð¦ Ì ) (Î¶ : Nat A B)
                 â funext ð¤ ð¦
                 â (g : Î  B) â (Î  x ê X , fiber (Î¶ x) (g x)) â fiber (NatÎ  Î¶) g
NatÎ -fiber-equiv {ð¤} {ð¥} {ð¦} {X} A B Î¶ fe g =
  (Î  x ê X , fiber (Î¶ x) (g x))           ââ¨ i â©
  (Î  x ê X , Î£ a ê A x , Î¶ x a â¡ g x)     ââ¨ ii â©
  (Î£ f ê Î  A , Î  x ê X , Î¶ x (f x) â¡ g x) ââ¨ iii â©
  (Î£ f ê Î  A , (Î» x â Î¶ x (f x)) â¡ g)     ââ¨ iv â©
  fiber (NatÎ  Î¶) g                        â 
   where
    i   = â-refl _
    ii  = Î Î£-distr-â
    iii = Î£-cong (Î» f â â-sym (â-funext fe (Î» x â Î¶ x (f x)) g))
    iv  =  â-refl _

NatÎ -vv-equiv : {X : ð¤ Ì } (A : X â ð¥ Ì ) (B : X â ð¦ Ì ) (Î¶ : Nat A B)
              â funext ð¤ (ð¥ â ð¦)
              â ((x : X) â is-vv-equiv (Î¶ x))
              â is-vv-equiv (NatÎ  Î¶)
NatÎ -vv-equiv {ð¤} {ð¥} {ð¦} A B Î¶ fe i g = equiv-to-singleton
                                           (â-sym (NatÎ -fiber-equiv A B Î¶
                                                    (lower-funext ð¤ ð¥ fe) g))
                                           (Î -is-singleton fe (Î» x â i x (g x)))

NatÎ -equiv : {X : ð¤ Ì } (A : X â ð¥ Ì ) (B : X â ð¦ Ì ) (Î¶ : Nat A B)
           â funext ð¤ (ð¥ â ð¦)
           â ((x : X) â is-equiv (Î¶ x))
           â is-equiv (NatÎ  Î¶)
NatÎ -equiv A B Î¶ fe i = vv-equivs-are-equivs
                             (NatÎ  Î¶)
                             (NatÎ -vv-equiv A B Î¶ fe
                               (Î» x â equivs-are-vv-equivs (Î¶ x) (i x)))

Î -cong' : {X : ð¤ Ì } (A : X â ð¥ Ì ) (B : X â ð¦ Ì )
        â funext ð¤ (ð¥ â ð¦)
        â ((x : X) â A x â B x)
        â Î  A â Î  B
Î -cong' A B fe e = NatÎ  (Î» x â prâ (e x)) ,
                   NatÎ -equiv A B (Î» x â prâ (e x)) fe (Î» x â prâ (e x))

â¡-cong : {X : ð¤ Ì } (x y : X) {x' y' : X} â x â¡ x' â y â¡ y' â (x â¡ y) â (x' â¡ y')
â¡-cong x y refl refl = â-refl (x â¡ y)

â¡-cong-l : {X : ð¤ Ì } (x y : X) {x' : X} â x â¡ x' â (x â¡ y) â (x' â¡ y)
â¡-cong-l x y refl = â-refl (x â¡ y)

â¡-cong-r : {X : ð¤ Ì } (x y : X) {y' : X} â y â¡ y' â (x â¡ y) â (x â¡ y')
â¡-cong-r x y refl = â-refl (x â¡ y)

â¡-flip : {X : ð¤ Ì } {x y : X} â (x â¡ y) â (y â¡ x)
â¡-flip = _â»Â¹ , (_â»Â¹ , â»Â¹-involutive) , (_â»Â¹ , â»Â¹-involutive)

singleton-â : {X : ð¤ Ì } {Y : ð¥ Ì } â is-singleton X â is-singleton Y â X â Y
singleton-â {ð¤} {ð¥} (c , Ï) (d , Î³) = (Î» _ â d) , ((Î» _ â c) , Î³) , ((Î» _ â c) , Ï)

singleton-â-ð : {X : ð¤ Ì } â is-singleton X â X â ð {ð¥}
singleton-â-ð i = singleton-â i ð-is-singleton

singleton-â-ð' : {X : ð¤ Ì } â is-singleton X â ð {ð¥} â X
singleton-â-ð' = singleton-â ð-is-singleton

ð-â¡-â : (P : ð¤ Ì )
      â funext ð¤ ð¤
      â propext ð¤
      â is-prop P
      â (ð â¡ P) â P
ð-â¡-â P fe pe i = qinveq (Î» q â Idtofun q â) (f , Îµ , Î·)
 where
  f : P â ð â¡ P
  f p = pe ð-is-prop i (Î» _ â p) unique-to-ð

  Î· : (p : P) â Idtofun (f p) â â¡ p
  Î· p = i (Idtofun (f p) â) p

  Îµ : (q : ð â¡ P) â f (Idtofun q â) â¡ q
  Îµ q = identifications-of-props-are-props pe fe P i ð (f (Idtofun q â)) q

empty-â-ð : {X : ð¤ Ì } â (X â ð {ð¥}) â X â ð {ð¦}
empty-â-ð i = qinveq (ð-elim â i) (ð-elim , (Î» x â ð-elim (i x)) , (Î» x â ð-elim x))

complement-is-equiv : is-equiv complement
complement-is-equiv = qinvs-are-equivs complement
                       (complement , complement-involutive , complement-involutive)

complement-â : ð â ð
complement-â = (complement , complement-is-equiv)

domain-is-total-fiber : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y) â X â Î£ (fiber f)
domain-is-total-fiber {ð¤} {ð¥} {X} {Y} f =
  X                             ââ¨ â-sym (ð-rneutral {ð¤} {ð¤}) â©
  X Ã ð                         ââ¨ Î£-cong (Î» x â singleton-â ð-is-singleton
                                          (singleton-types-are-singletons (f x))) â©
  (Î£ x ê X , Î£ y ê Y , f x â¡ y) ââ¨ Î£-flip â©
  (Î£ y ê Y , Î£ x ê X , f x â¡ y) â 

total-fiber-is-domain : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                      â (Î£ y ê Y , Î£ x ê X , f x â¡ y) â X
total-fiber-is-domain {ð¤} {ð¥} {X} {Y} f = â-sym (domain-is-total-fiber f)

left-Id-equiv : {X : ð¤ Ì } {Y : X â ð¥ Ì } (x : X)
              â (Î£ x' ê X , (x' â¡ x) Ã Y x') â Y x
left-Id-equiv {ð¤} {ð¥} {X} {Y} x =
   (Î£ x' ê X , (x' â¡ x) Ã Y x')            ââ¨ â-sym Î£-assoc â©
   (Î£ (x' , _) ê singleton-type' x , Y x') ââ¨ a â©
   Y x                                     â 
  where
   a = prop-indexed-sum (singleton-types'-are-props x) (singleton'-center x)

right-Id-equiv : {X : ð¤ Ì } {Y : X â ð¥ Ì } (x : X)
               â (Î£ x' ê X , Y x' Ã (x' â¡ x)) â Y x
right-Id-equiv {ð¤} {ð¥} {X} {Y} x =
   (Î£ x' ê X , Y x' Ã (x' â¡ x))  ââ¨ Î£-cong (Î» x' â Ã-comm) â©
   (Î£ x' ê X , (x' â¡ x) Ã Y x')  ââ¨ left-Id-equiv x â©
   Y x                           â 


prâ-fiber-equiv : {X : ð¤ Ì } {Y : X â ð¥ Ì } (x : X)
                â fiber (prâ {ð¤} {ð¥} {X} {Y}) x â Y x
prâ-fiber-equiv {ð¤} {ð¥} {X} {Y} x =
  fiber prâ x                   ââ¨ Î£-assoc â©
  (Î£ x' ê X , Y x' Ã (x' â¡ x))  ââ¨ right-Id-equiv x â©
  Y x                           â 

\end{code}

Tom de Jong, September 2019 (two lemmas used in UF-Classifiers-Old)

A nice application of Î£-change-of-variable is that the fiber of a map doesn't
change (up to equivalence, at least) when precomposing with an equivalence.

These two lemmas are used in UF-Classifiers-Old, but are sufficiently general to
warrant their place here.

\begin{code}

precomposition-with-equiv-does-not-change-fibers : {X : ð¤ Ì } {Y : ð¥ Ì } {Z : ð¦ Ì }
                                                   (e : Z â X) (f : X â Y) (y : Y)
                                                 â fiber (f â â e â) y â fiber f y
precomposition-with-equiv-does-not-change-fibers (g , i) f y =
 Î£-change-of-variable (Î» x â f x â¡ y) g i

retract-pointed-fibers : {X : ð¤ Ì } {Y : ð¥ Ì } {r : Y â X}
                       â (Î£ s ê (X â Y) , r â s â¼ id) â (Î  x ê X , fiber r x)
retract-pointed-fibers {ð¤} {ð¥} {X} {Y} {r} = qinveq f (g , (p , q))
 where
  f : (Î£ s ê (X â Y) , r â s â¼ id) â Î  (fiber r)
  f (s , rs) x = (s x) , (rs x)

  g : ((x : X) â fiber r x) â Î£ s ê (X â Y) , r â s â¼ id
  g Î± = (Î» (x : X) â prâ (Î± x)) , (Î» (x : X) â prâ (Î± x))

  p : (srs : Î£ s ê (X â Y) , r â s â¼ id) â g (f srs) â¡ srs
  p (s , rs) = refl

  q : (Î± : Î  x ê X , fiber r x) â f (g Î±) â¡ Î±
  q Î± = refl

\end{code}

Added 10 February 2020 by Tom de Jong.

\begin{code}

fiber-of-composite : {X : ð¤ Ì } {Y : ð¥ Ì } {Z : ð¦ Ì } (f : X â Y) (g : Y â Z)
                   â (z : Z)
                   â fiber (g â f) z
                   â (Î£ (y , _) ê fiber g z , fiber f y)
fiber-of-composite {ð¤} {ð¥} {ð¦} {X} {Y} {Z} f g z =
 qinveq Ï (Ï , (ÏÏ , ÏÏ))
  where
   Ï : fiber (g â f) z
     â (Î£ w ê (fiber g z) , fiber f (fiber-point w))
   Ï (x , p) = ((f x) , p) , (x , refl)

   Ï : (Î£ w ê (fiber g z) , fiber f (fiber-point w))
     â fiber (g â f) z
   Ï ((y , q) , (x , p)) = x , ((ap g p) â q)

   ÏÏ : (w : fiber (g â f) z) â Ï (Ï w) â¡ w
   ÏÏ (x , refl) = refl

   ÏÏ : (w : Î£ w ê (fiber g z) , fiber f (fiber-point w))
      â Ï (Ï w) â¡ w
   ÏÏ ((.(f x) , refl) , (x , refl)) = refl

fiber-of-unique-to-ð : {ð¥ : Universe} {X : ð¤ Ì }
                     â (u : ð) â fiber (unique-to-ð {_} {ð¥} {X}) u â X
fiber-of-unique-to-ð {ð¤} {ð¥} {X} â =
 (Î£ x ê X , unique-to-ð x â¡ â) ââ¨ Î£-cong Ï â©
 X Ã ð{ð¥}                      ââ¨ ð-rneutral â©
 X                             â 
  where
   Ï : (x : X) â (â â¡ â) â ð
   Ï x = singleton-â-ð
         (pointed-props-are-singletons refl (props-are-sets ð-is-prop))

â¼-fiber-identifications-â : {X : ð¤ Ì } {Y : ð¥ Ì } {f : X â Y} {g : X â Y}
                          â f â¼ g
                          â (y : Y) (x : X) â (f x â¡ y) â (g x â¡ y)
â¼-fiber-identifications-â {ð¤} {ð¥} {X} {Y} {f} {g} H y x = qinveq Î± (Î² , (Î²Î± , Î±Î²))
 where
  Î± : f x â¡ y â g x â¡ y
  Î± p = (H x) â»Â¹ â p

  Î² : g x â¡ y â f x â¡ y
  Î² q = (H x) â q

  Î²Î± : (p : f x â¡ y) â Î² (Î± p) â¡ p
  Î²Î± p = Î² (Î± p)                â¡â¨ refl â©
         (H x) â ((H x) â»Â¹ â p) â¡â¨ (âassoc (H x) ((H x) â»Â¹) p) â»Â¹ â©
         (H x) â (H x) â»Â¹ â p   â¡â¨ ap (Î» - â - â p) ((right-inverse (H x)) â»Â¹) â©
         refl â p               â¡â¨ refl-left-neutral â©
         p                      â

  Î±Î² : (q : g x â¡ y) â Î± (Î² q) â¡ q
  Î±Î² q = Î± (Î² q)                â¡â¨ refl â©
         (H x) â»Â¹ â ((H x) â q) â¡â¨ (âassoc ((H x) â»Â¹) (H x) q) â»Â¹ â©
         (H x) â»Â¹ â (H x) â q   â¡â¨ ap (Î» - â - â q) (left-inverse (H x)) â©
         refl â q               â¡â¨ refl-left-neutral â©
         q                      â

â¼-fiber-â : {X : ð¤ Ì } {Y : ð¥ Ì } {f : X â Y} {g : X â Y}
          â f â¼ g
          â (y : Y) â fiber f y â fiber g y
â¼-fiber-â H y = Î£-cong (â¼-fiber-identifications-â H y)

â-is-equiv-left : {X : ð¤ Ì } {x y z : X} (p : z â¡ x)
                â is-equiv (Î» (q : x â¡ y) â p â q)
â-is-equiv-left {ð¤} {X} {x} {y} refl =
 equiv-closed-under-â¼ id (refl â_) (id-is-equiv (x â¡ y))
  (Î» _ â refl-left-neutral)

â-is-equiv-right : {X : ð¤ Ì } {x y z : X} (q : x â¡ y)
                 â is-equiv (Î» (p : z â¡ x) â p â q)
â-is-equiv-right {ð¤} {X} {x} {y} {z} refl = id-is-equiv (z â¡ y)

\end{code}

Added by Tom de Jong, November 2021.

\begin{code}

â-2-out-of-3-right : {X : ð¤ Ì } {Y : ð¥ Ì } {Z : ð¦ Ì }
                   â {f : X â Y} {g : Y â Z}
                   â is-equiv f â is-equiv (g â f) â is-equiv g
â-2-out-of-3-right {ð¤} {ð¥} {ð¦} {X} {Y} {Z} {f} {g} i j =
 equiv-closed-under-â¼ (g â f â fâ»Â¹) g k h
  where
   ð : X â Y
   ð = (f , i)
   fâ»Â¹ : Y â X
   fâ»Â¹ = â ð ââ»Â¹
   k : is-equiv (g â f â fâ»Â¹)
   k = â-is-equiv (âââ»Â¹-is-equiv ð) j
   h : g â¼ g â f â fâ»Â¹
   h y = ap g ((â-sym-is-rinv ð y) â»Â¹)

â-2-out-of-3-left : {X : ð¤ Ì } {Y : ð¥ Ì } {Z : ð¦ Ì }
                  â {f : X â Y} {g : Y â Z}
                  â is-equiv g â is-equiv (g â f) â is-equiv f
â-2-out-of-3-left {ð¤} {ð¥} {ð¦} {X} {Y} {Z} {f} {g} i j =
 equiv-closed-under-â¼ (gâ»Â¹ â g â f) f k h
  where
   ð : Y â Z
   ð = (g , i)
   gâ»Â¹ : Z â Y
   gâ»Â¹ = â ð ââ»Â¹
   k : is-equiv (gâ»Â¹ â g â f)
   k = â-is-equiv j (âââ»Â¹-is-equiv ð)
   h : f â¼ gâ»Â¹ â g â f
   h x = (â-sym-is-linv ð (f x)) â»Â¹

\end{code}

Completely unrelated to the above, but still useful.

\begin{code}

open import UF-PropTrunc

module _
        (pt : propositional-truncations-exist)
       where

 open PropositionalTruncation pt

 â¥â¥-cong : {X : ð¤ Ì  } {Y : ð¥ Ì  } â X â Y â â¥ X â¥ â â¥ Y â¥
 â¥â¥-cong f = logically-equivalent-props-are-equivalent â¥â¥-is-prop â¥â¥-is-prop
              (â¥â¥-functor â f â) (â¥â¥-functor â f ââ»Â¹)

 â-cong : {X : ð¤ Ì  } {Y : X â ð¥ Ì  } {Y' : X â ð¦ Ì  }
        â ((x : X) â Y x â Y' x)
        â â Y â â Y'
 â-cong e = â¥â¥-cong (Î£-cong e)

 outer-â-inner-Î£ : {X : ð¤ Ì  } {Y : X â ð¥ Ì  } {A : (x : X) â Y x â ð¦ Ì  }
                 â (â x ê X , â y ê Y x , A x y)
                 â (â x ê X , Î£ y ê Y x , A x y)
 outer-â-inner-Î£ {ð¤} {ð¥} {ð¦} {X} {Y} {A} =
  logically-equivalent-props-are-equivalent â¥â¥-is-prop â¥â¥-is-prop f g
   where
    g : (â x ê X , Î£ y ê Y x , A x y)
      â (â x ê X , â y ê Y x , A x y)
    g = â¥â¥-functor (Î» (x , y , a) â x , â£ y , a â£)
    f : (â x ê X , â y ê Y x , A x y)
      â (â x ê X , Î£ y ê Y x , A x y)
    f = â¥â¥-rec â¥â¥-is-prop Ï
     where
      Ï : (Î£ x ê X , â y ê Y x , A x y)
        â (â x ê X , Î£ y ê Y x , A x y)
      Ï (x , p) = â¥â¥-functor (Î» (y , a) â x , y , a) p

\end{code}
