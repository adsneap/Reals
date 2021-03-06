Tom de Jong 22nd May 2019

Various lemmas for working with partial elements of a type.
Includes an alternative partial order on the lifting of a type without relying
on full univalence.

Moreover, there are some lemmas on the Kleisli extension for the lifting monad.
In particular, (Î· â f) â¯ is pointwise equal to ðÌ f.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-Subsingletons

module LiftingMiscelanea-PropExt-FunExt
        (ð£ : Universe)
        (pe : propext ð£)
        (fe : Fun-Ext)
       where

open import UF-Base
open import UF-Equiv
open import UF-Retracts
open import UF-Subsingletons-FunExt

open import Lifting ð£
open import LiftingIdentityViaSIP ð£
open import LiftingMiscelanea ð£
open import LiftingMonad ð£

\end{code}

Assuming propositional extensionality for ð£ and function extensionality, we can
prove that the lifting of a set is again a set.

\begin{code}

module _ {ð¤ : Universe}
         {X : ð¤ Ì }
       where

 open import LiftingUnivalentPrecategory ð£ X

 lifting-of-set-is-set : is-set X â is-set (ð X)
 lifting-of-set-is-set i {l} {m} p q  = retract-of-prop r j p q
  where
   r : Î£ has-section
   r = (to-Î£-â¡ , from-Î£-â¡ , tofrom-Î£-â¡)
   j : is-prop (Î£ (Î» pâ â transport (Î» P â (P â X) Ã is-prop P)
                pâ (prâ l) â¡ prâ m))
   j = Î£-is-prop
        (identifications-of-props-are-props pe fe (is-defined m)
         (being-defined-is-prop m) (is-defined l))
        (Î» d â Ã-is-set (Î -is-set fe Î» _ â i)
                        (props-are-sets (being-prop-is-prop fe)))

 \end{code}

 We prefer to work with â' as it yields identifications, which can be transported
 and allow for equational reasoning with â¡â¨ â©.
 Moreover, it has the right universe level for use in the Scott model of PCF.

 This duplicates some material from LiftingUnivalentPrecategory. However, we only
 assume propositional extensionality and function extensionality here. We do not
 rely on full univalence.

 \begin{code}

 _â'_ : (l m : ð X) â ð¤ â ð£ âº Ì
 l â' m = is-defined l â l â¡ m

 â-to-â' : {l m : ð X} â l â m â l â' m
 â-to-â' {l} {m} a d = â-anti pe fe fe (a , b) where
  b : m â l
  b = c , v where
   c : is-defined m â is-defined l
   c = Î» _ â d
   v : (e : is-defined m) â value m e â¡ value l d
   v e = value m e         â¡â¨ ap (value m)
                             (being-defined-is-prop m e (prâ a d)) â©
         value m (prâ a d) â¡â¨ g â»Â¹ â©
         value l d         â where
    h : is-defined l â is-defined m
    h = prâ a
    g : value l d â¡ value m (prâ a d)
    g = prâ a d

 â'-to-â : {l m : ð X} â l â' m â l â m
 â'-to-â {l} {m} a = â e ââ»Â¹ g where
  e : (l â m) â (is-defined l â l â m)
  e = â-open fe fe l m
  g : is-defined l â l â m
  g d = transport (_â_ l) (a d) (ð-id l)

 â'-is-reflexive : {l : ð X} â l â' l
 â'-is-reflexive {l} d = refl

 â'-is-transitive : {l m n : ð X} â l â' m â m â' n â l â' n
 â'-is-transitive {l} {m} {n} a b d = l â¡â¨ a d â©
                                      m â¡â¨ b (â¡-to-is-defined (a d) d) â©
                                      n â

 â'-is-antisymmetric : {l m : ð X} â l â' m â m â' l â l â¡ m
 â'-is-antisymmetric a b = â-anti pe fe fe (â'-to-â a , â'-to-â b)

 â'-prop-valued : is-set X â {l m : ð X} â is-prop (l â' m)
 â'-prop-valued s {l} {m} =
  Î -is-prop fe Î» (d : is-defined l) â lifting-of-set-is-set s

 is-defined-Î·-â¡ : {l : ð X} (d : is-defined l) â l â¡ Î· (value l d)
 is-defined-Î·-â¡ {l} d =
  â-to-â' ((Î» _ â â) , Î» (e : is-defined l) â value-is-constant l e d) d

 â-to-â¡ : {l m : ð X} â l â m â l â¡ m
 â-to-â¡ {l} {m} (deq , veq) = â-anti pe fe fe (a , b)
  where
   a : l â m
   a = â deq â , happly veq
   b : m â l
   b = (â deq ââ»Â¹ , h)
    where
     h : (d : is-defined m) â value m d â¡ value l (â deq ââ»Â¹ d)
     h d = value m d  â¡â¨ value-is-constant m d d' â©
           value m d' â¡â¨ (happly veq e)â»Â¹ â©
           value l e  â
      where
       e : is-defined l
       e = â deq ââ»Â¹ d
       d' : is-defined m
       d' = â deq â e

module _ {ð¤ : Universe}
         {X : ð¤ Ì }
         {ð¥ : Universe}
         {Y : ð¥ Ì }
       where

 â¯-is-defined : (f : X â ð Y) (l : ð X) â is-defined ((f â¯) l) â is-defined l
 â¯-is-defined f l = prâ

 â¯-on-total-element : (f : X â ð Y) {l : ð X} (d : is-defined l)
                    â (f â¯) l â¡ f (value l d)
 â¯-on-total-element f {l} d =
  (f â¯) l               â¡â¨ ap (f â¯) (is-defined-Î·-â¡ d) â©
  (f â¯) (Î· (value l d)) â¡â¨ â-to-â¡ (Kleisli-Lawâ f (value l d)) â©
  f (value l d)         â

 open import LiftingUnivalentPrecategory ð£ Y

 ðÌ-â¯-â¼ : (f : X â Y) â (Î· â f) â¯ â¼ ðÌ f
 ðÌ-â¯-â¼ f l = â-anti pe fe fe (a , b)
  where
   a : ((Î· â f) â¯) l â (ðÌ f) l
   a = p , q
    where
     p : is-defined (((Î· â f) â¯) l) â is-defined (ðÌ f l)
     p = â¯-is-defined (Î· â f) l
     q : (d : is-defined (((Î· â f) â¯) l))
       â value (((Î· â f) â¯) l) d â¡ value (ðÌ f l) (â¯-is-defined (Î· â f) l d)
     q d = refl
   b : (ðÌ f) l â ((Î· â f) â¯) l
   b = r , s
    where
     r : is-defined (ðÌ f l) â is-defined (((Î· â f) â¯) l)
     r d = d , â
     s : (d : is-defined (ðÌ f l))
       â value (ðÌ f l) d â¡ value (((Î· â f) â¯) l) (r d)
     s d = refl

\end{code}
