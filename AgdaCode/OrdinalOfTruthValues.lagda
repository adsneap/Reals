Martin Escardo, 4th October 2018

The ordinal of truth values in a universe ð¤.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-Subsingletons renaming (â¤Î© to â¤ ; â¥Î© to â¥)

module OrdinalOfTruthValues
       (fe : FunExt)
       (ð¤  : Universe)
       (pe : propext ð¤)
       where

open import OrdinalsType
open import OrdinalNotions
open import OrdinalsType

open import UF-Subsingletons-FunExt

Î©â : Ordinal (ð¤ âº)
Î©â = Î© ð¤ , _âº_ , pv , w , e , t
 where
  _âº_ : Î© ð¤ â Î© ð¤ â ð¤ âº Ì
  p âº q = (p â¡ â¥) Ã (q â¡ â¤)

  pv : is-prop-valued _âº_
  pv p q = Ã-is-prop (Î©-is-set (fe ð¤ ð¤) pe) (Î©-is-set (fe ð¤ ð¤) pe)

  w : is-well-founded _âº_
  w p = next p s
   where
    t : (q : Î© ð¤) â  q âº â¥ â is-accessible _âº_ q
    t â¥ (refl , b) = ð-elim (â¥-is-not-â¤ b)

    â¥-accessible : is-accessible _âº_ â¥
    â¥-accessible = next â¥ t

    s : (q : Î© ð¤) â q âº p â is-accessible _âº_ q
    s â¥ (refl , b) = â¥-accessible

  e : is-extensional _âº_
  e p q f g = Î©-ext pe (fe ð¤ ð¤) Ï Ï
   where
    Ï : p â¡ â¤ â q â¡ â¤
    Ï a = prâ (f â¥ (refl , a))

    Ï : q â¡ â¤ â p â¡ â¤
    Ï b = prâ (g â¥ (refl , b))

  t : is-transitive _âº_
  t p q r (a , _) (_ , b) = a , b

\end{code}
