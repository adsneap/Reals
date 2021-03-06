Martin Escardo, January 2019.

Minimal development of hlevels. For simplicity, for the moment we
assume univalence globally, although it is not necessary. Our
convention here is that propositions are at level zero (apologies).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Univalence

module UF-hlevels (ua : Univalence) where

open import UF-FunExt
open import UF-UA-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-EquivalenceExamples

private fe : FunExt
fe = Univalence-gives-FunExt ua

_is-of-hlevel_ : ð¤ Ì â â â ð¤ Ì
X is-of-hlevel zero     = is-prop X
X is-of-hlevel (succ n) = (x x' : X) â (x â¡ x') is-of-hlevel n

hlevel-relation-is-prop : (n : â) (X : ð¤ Ì ) â is-prop  (X is-of-hlevel n)
hlevel-relation-is-prop {ð¤} zero     X = being-prop-is-prop (fe ð¤ ð¤)
hlevel-relation-is-prop {ð¤} (succ n) X = Î -is-prop (fe ð¤ ð¤)
                                             (Î» x â Î -is-prop (fe ð¤ ð¤)
                                                      (Î» x' â hlevel-relation-is-prop {ð¤} n (x â¡ x')))

props-have-all-hlevels : (n : â) (P : ð¤ Ì ) â is-prop P â P is-of-hlevel n
props-have-all-hlevels zero     P i = i
props-have-all-hlevels (succ n) P i = Î» x x' â props-have-all-hlevels n (x â¡ x') (props-are-sets i)

hlevels-closed-under-Î£ : (n : â)
                        â (X : ð¤ Ì ) (Y : X â ð¤ Ì )
                        â X is-of-hlevel n
                        â ((x : X) â (Y x) is-of-hlevel n)
                        â (Î£ Y) is-of-hlevel n
hlevels-closed-under-Î£ {ð¤} zero X Y l m = Î£-is-prop l m
hlevels-closed-under-Î£ {ð¤} (succ n) X Y l m = Î³
 where
  Î³ : (Ï Ï : Î£ Y) â (Ï â¡ Ï) is-of-hlevel n
  Î³ Ï Ï = back-transport (_is-of-hlevel n) a IH
   where
    a : (Ï â¡ Ï) â¡ (Î£ p ê prâ Ï â¡ prâ Ï , transport Y p (prâ Ï) â¡ prâ Ï)
    a = eqtoid (ua ð¤) _ _ Î£-â¡-â
    IH : (Î£ p ê prâ Ï â¡ prâ Ï , transport Y p (prâ Ï) â¡ prâ Ï) is-of-hlevel n
    IH = hlevels-closed-under-Î£ n
           (prâ Ï â¡ prâ Ï)
           (Î» p â transport Y p (prâ Ï) â¡ prâ Ï)
           (l (prâ Ï) (prâ Ï))
           (Î» p â m (prâ Ï) (transport Y p (prâ Ï)) (prâ Ï))

hlevels-closed-under-Î  : (n : â)
                       â (X : ð¤ Ì ) (Y : X â ð¤ Ì )
                       â ((x : X) â (Y x) is-of-hlevel n)
                       â (Î  Y) is-of-hlevel n
hlevels-closed-under-Î  {ð¤} zero X Y m = Î -is-prop (fe ð¤ ð¤) m
hlevels-closed-under-Î  {ð¤} (succ n) X Y m = Î³
 where
  Î³ : (f g : Î  Y) â (f â¡ g) is-of-hlevel n
  Î³ f g = back-transport (_is-of-hlevel n) a IH
   where
    a : (f â¡ g) â¡ (f â¼ g)
    a = eqtoid (ua ð¤) (f â¡ g) (f â¼ g) (â-funext (fe ð¤ ð¤) f g)
    IH : (f â¼ g) is-of-hlevel n
    IH = hlevels-closed-under-Î  {ð¤} n X (Î» x â f x â¡ g x) (Î» x â m x (f x) (g x))

\end{code}

The subuniverse of types of hlevel n:

\begin{code}

â : â â (ð¤ : Universe) â ð¤ âº Ì
â n ð¤ = Î£ X ê ð¤ Ì , X is-of-hlevel n

\end{code}
