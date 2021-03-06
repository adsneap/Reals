Martin Escardo, 21 March 2018, 1st December 2019.

We prove the known (constructive) fact that

  X + π β Y + π β X β Y.

The new proof from 1st December 2019 is extracted from the module
UF-Factorial and doesn't use function extensionality. The old proof
from 21 March 2018 is included at the end.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module PlusOneLC where

open import SpartanMLTT
open import UF-Equiv
open import Plus-Properties
open import UF-Retracts
open import Swap
open import DiscreteAndSeparated

+π-cancellable : {X : π€ Μ } {Y : π₯ Μ}
               β (X + π {π¦} β Y + π {π£})
               β X β Y
+π-cancellable {π€} {π₯} {π¦} {π£} {X} {Y} (Ο , i) = qinveq f' (g' , Ξ·' , Ξ΅')
 where
  zβ : X + π
  zβ = inr β

  tβ : Y + π
  tβ = inr β

  j : is-isolated zβ
  j = new-point-is-isolated

  k : is-isolated (Ο zβ)
  k = equivs-preserve-isolatedness Ο i zβ j

  l : is-isolated tβ
  l = new-point-is-isolated

  s : Y + π β Y + π
  s = swap (Ο zβ) tβ k l

  f : X + π β Y + π
  f = s β Ο

  p : f zβ β‘ tβ
  p = swap-equationβ (Ο zβ) tβ k l

  g : Y + π β X + π
  g = inverse Ο i β s

  h : s β s βΌ id
  h = swap-involutive (Ο zβ) tβ k l

  Ξ· : g β f βΌ id
  Ξ· z = inverse Ο i (s (s (Ο z))) β‘β¨ ap (inverse Ο i) (h (Ο z)) β©
        inverse Ο i (Ο z)         β‘β¨ inverses-are-retractions Ο i z β©
        z                         β

  Ξ΅ : f β g βΌ id
  Ξ΅ t = s (Ο (inverse Ο i (s t))) β‘β¨ ap s (inverses-are-sections Ο i (s t)) β©
        s (s t)                   β‘β¨ h t β©
        t                         β

  f' : X β Y
  f' x = prβ (inl-preservation f p (sections-are-lc f (g , Ξ·)) x)

  a : (x : X) β f (inl x) β‘ inl (f' x)
  a x = prβ (inl-preservation f p (sections-are-lc f (g , Ξ·)) x)

  q = g tβ     β‘β¨ ap g (p β»ΒΉ) β©
      g (f zβ) β‘β¨ Ξ· zβ β©
      inr β    β

  g' : Y β X
  g' y = prβ (inl-preservation g q (sections-are-lc g (f , Ξ΅)) y)

  b : (y : Y) β g (inl y) β‘ inl (g' y)
  b y = prβ (inl-preservation g q (sections-are-lc g (f , Ξ΅)) y)

  Ξ·' : (x : X) β g' (f' x) β‘ x
  Ξ·' x = inl-lc (inl (g' (f' x)) β‘β¨ (b (f' x))β»ΒΉ β©
                 g (inl (f' x))  β‘β¨ (ap g (a x))β»ΒΉ β©
                 g (f (inl x))   β‘β¨ Ξ· (inl x) β©
                 inl x           β)

  Ξ΅' : (y : Y) β f' (g' y) β‘ y
  Ξ΅' y = inl-lc (inl (f' (g' y)) β‘β¨ (a (g' y))β»ΒΉ β©
                 f (inl (g' y))  β‘β¨ (ap f (b y))β»ΒΉ β©
                 f (g (inl y))   β‘β¨ Ξ΅ (inl y) β©
                 inl y           β)

\end{code}

The old version from 21 March 2018, which uses function
extensionality:

\begin{code}

_β_ : (X : π€ Μ ) (a : X) β π€ Μ
X β a = Ξ£ x κ X , x β’ a

open import UF-FunExt

module old (fe : FunExt) where

 open import UF-Base
 open import UF-Subsingletons-FunExt

 add-and-remove-point : {X : π€ Μ } β  X β (X + π) β (inr β)
 add-and-remove-point {π€} {X} = qinveq f (g , Ξ΅ , Ξ·)
  where
   f : X β (X + π {π€}) β inr β
   f x = (inl x , +disjoint)

   g : (X + π) β inr β β X
   g (inl x , u) = x
   g (inr β , u) = π-elim (u refl)

   Ξ· : f β g βΌ id
   Ξ· (inl x , u) = to-Ξ£-β‘' (negations-are-props (fe π€ π€β) _ _)
   Ξ· (inr β , u) = π-elim (u refl)

   Ξ΅ : g β f βΌ id
   Ξ΅ x = refl

 remove-points : {X : π€ Μ } {Y : π₯ Μ } (f : X β Y) β qinv f β (a : X) β X β a β Y β (f a)
 remove-points {π€} {π₯} {X} {Y} f (g , Ξ΅ , Ξ·) a = qinveq f' (g' , Ξ΅' , Ξ·')
  where
   f' : X β a β Y β (f a)
   f' (x , u) = (f x , Ξ» (p : f x β‘ f a) β u ((Ξ΅ x)β»ΒΉ β ap g p β Ξ΅ a))

   g' : Y β (f a) β X β a
   g' (y , v) = (g y , Ξ» (p : g y β‘ a) β v ((Ξ· y) β»ΒΉ β ap f p))

   Ξ΅' : g' β f' βΌ id
   Ξ΅' (x , _) = to-Ξ£-β‘ (Ξ΅ x , negations-are-props (fe π€ π€β) _ _)

   Ξ·' : f' β g' βΌ id
   Ξ·' (y , _) = to-Ξ£-β‘ (Ξ· y , negations-are-props (fe π₯ π€β) _ _)

 add-one-and-remove-isolated-point : {Y : π₯ Μ } (z : Y + π) β is-isolated z β ((Y + π) β z) β Y
 add-one-and-remove-isolated-point {π₯} {Y} (inl b) i = qinveq f (g , Ξ΅ , Ξ·)
  where
   f : (Y + π) β (inl b) β Y
   f (inl y , u) = y
   f (inr β , u) = b

   g' : (y : Y) β decidable (inl b β‘ inl y) β (Y + π) β (inl b)
   g' y (inl p) = (inr β , +disjoint')
   g' y (inr u) = (inl y , contrapositive (_β»ΒΉ) u)

   g : Y β (Y + π) β (inl b)
   g y = g' y (i (inl y))

   Ξ΅ : g β f βΌ id
   Ξ΅ (inl y , u) = to-Ξ£-β‘ (p , negations-are-props (fe π₯ π€β) _ _)
    where
     Ο : (p : inl b β‘ inl y) (q : i (inl y) β‘ inl p) β i (inl y) β‘ inr (β’-sym u)
     Ο p q = π-elim (u (p β»ΒΉ))
     Ο : (v : inl b β’ inl y) (q : i (inl y) β‘ inr v) β i (inl y) β‘ inr (β’-sym u)
     Ο v q = q β ap inr (negations-are-props (fe π₯ π€β) _ _)
     h : i (inl y) β‘ inr (β’-sym u)
     h = equality-cases (i (inl y)) Ο Ο
     p : prβ (g' y (i (inl y))) β‘ inl y
     p = ap (prβ β (g' y)) h
   Ξ΅ (inr β , u) = equality-cases (i (inl b)) Ο Ο
    where
     Ο : (p : inl b β‘ inl b) β i (inl b) β‘ inl p β g (f (inr β , u)) β‘ (inr β , u)
     Ο p q = r β to-Ξ£-β‘ (refl , negations-are-props (fe π₯ π€β) _ _)
      where
       r : g b β‘ (inr β , +disjoint')
       r = ap (g' b) q
     Ο : (v : inl b β’ inl b) β i (inl b) β‘ inr v β g (f (inr β , u)) β‘ (inr β , u)
     Ο v q = π-elim (v refl)

   Ξ· : f β g βΌ id
   Ξ· y = equality-cases (i (inl y)) Ο Ο
    where
     Ο : (p : inl b β‘ inl y) β i (inl y) β‘ inl p β f (g' y (i (inl y))) β‘ y
     Ο p q = ap (Ξ» - β f (g' y -)) q β inl-lc p
     Ο : (u : inl b β’ inl y) β i (inl y) β‘ inr u β f (g' y (i (inl y))) β‘ y
     Ο _ = ap ((Ξ» d β f (g' y d)))

 add-one-and-remove-isolated-point {π₯} {Y} (inr β) _ = β-sym add-and-remove-point

 +π-cancellable' : {X : π€ Μ } {Y : π₯ Μ } β (X + π) β (Y + π) β X β Y
 +π-cancellable' {π€} {π₯} {X} {Y} (Ο , e) =
    X                  ββ¨ add-and-remove-point β©
   (X + π) β inr β     ββ¨ remove-points Ο (equivs-are-qinvs Ο e) (inr β) β©
   (Y + π) β Ο (inr β) ββ¨ add-one-and-remove-isolated-point
                           (Ο (inr β))
                           (equivs-preserve-isolatedness Ο e (inr β)
                             new-point-is-isolated) β©
    Y                  β 

\end{code}

Added 16th April 2021.

\begin{code}

open import UF-Subsingletons-FunExt

remove-and-add-isolated-point : funext π€ π€β
                              β {X : π€ Μ } (xβ : X)
                              β is-isolated xβ
                              β X β (X β xβ + π {π₯})
remove-and-add-isolated-point fe {X} xβ ΞΉ = qinveq f (g , Ξ΅ , Ξ·)
 where
  Ο : (x : X) β decidable (xβ β‘ x) β X β xβ + π
  Ο x (inl p) = inr β
  Ο x (inr Ξ½) = inl (x , (Ξ» (p : x β‘ xβ) β Ξ½ (p β»ΒΉ)))

  f : X β X β xβ + π
  f x = Ο x (ΞΉ x)

  g : X β xβ + π β X
  g (inl (x , _)) = x
  g (inr β) = xβ

  Ξ·' : (y : X β xβ + π) (d : decidable (xβ β‘ g y)) β Ο (g y) d β‘ y
  Ξ·' (inl (x , Ξ½)) (inl q) = π-elim (Ξ½ (q β»ΒΉ))
  Ξ·' (inl (x , Ξ½)) (inr _) = ap (Ξ» - β inl (x , -)) (negations-are-props fe _ _)
  Ξ·' (inr β) (inl p)       = refl
  Ξ·' (inr β) (inr Ξ½)       = π-elim (Ξ½ refl)

  Ξ· : f β g βΌ id
  Ξ· y = Ξ·' y (ΞΉ (g y))

  Ξ΅' : (x : X) (d : decidable (xβ β‘ x)) β g (Ο x d) β‘ x
  Ξ΅' x (inl p) = p
  Ξ΅' x (inr Ξ½) = refl

  Ξ΅ : g β f βΌ id
  Ξ΅ x = Ξ΅' x (ΞΉ x)

\end{code}
