Martin Escardo, 1st April 2013

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module NonCollapsibleFamily where

open import SpartanMLTT

open import UF-Base
open import UF-Subsingletons
open import UF-KrausLemma
open import DiscreteAndSeparated

decidable-equality-criterion : (X : ๐ค ฬ )
                               (a : ๐ โ X) โ ((x : X) โ collapsible(ฮฃ i ๊ ๐ , a i โก x))
                             โ decidable(a โ โก a โ)
decidable-equality-criterion {๐ค} X a c = equal-or-different
 where
  ฮบ : (x : X) โ (ฮฃ i ๊ ๐ , a i โก x) โ ฮฃ i ๊ ๐ , a i โก x
  ฮบ x = prโ(c x)

  ฮบ-constant : (x : X) โ wconstant(ฮบ x)
  ฮบ-constant x = prโ(c x)

  prop-fix : (x : X) โ is-prop (fix(ฮบ x))
  prop-fix x = fix-is-prop (ฮบ x) (ฮบ-constant x)

  choice : (x : X) โ fix(ฮบ x) โ ฮฃ i ๊ ๐ , a i โก x
  choice x = prโ

  ฮท : (x : X) โ (ฮฃ i ๊ ๐ , a i โก x) โ fix(ฮบ x)
  ฮท x ฯ = ฮบ x ฯ , ฮบ-constant x ฯ (ฮบ x ฯ)

  E : ๐ค ฬ
  E = ฮฃ x ๊ X , fix(ฮบ x)

  r : ๐ โ E
  r i = a i , ฮท (a i) (i , refl)

  r-splits : (e : E) โ ฮฃ i ๊ ๐ , r i โก e
  r-splits (x , p) = prโ p' , to-ฮฃ-โก (prโ p' , prop-fix x _ p)
   where
    p' : ฮฃ i ๊ ๐ , a i โก x
    p' = choice x p

  s : E โ ๐
  s e = prโ(r-splits e)

  r-retract : (e : E) โ r(s e) โก e
  r-retract e = prโ(r-splits e)

  s-injective : (e e' : E) โ s e โก s e' โ e โก e'
  s-injective e e' p = (r-retract e)โปยน โ ap r p โ r-retract e'

  a-r : (i j : ๐) โ a i โก a j โ r i โก r j
  a-r i j p = to-ฮฃ-โก (p , prop-fix (a j) _ (ฮท (a j) (j , refl)))

  r-a : (i j : ๐) โ r i โก r j โ a i โก a j
  r-a i j = ap prโ

  a-s : (i j : ๐) โ a i โก a j โ s(r i) โก s(r j)
  a-s i j p = ap s (a-r i j p)

  s-a : (i j : ๐) โ s(r i) โก s(r j) โ a i โก a j
  s-a i j p = r-a i j (s-injective (r i) (r j) p)

  equal-or-different : (a โ โก a โ) + (a โ โก a โ โ ๐)
  equal-or-different = claim(๐-is-discrete (s(r โ)) (s(r โ)))
   where
    claim : (s(r โ) โก s(r โ)) + (s(r โ) โก s(r โ) โ ๐) โ (a โ โก a โ) + (a โ โก a โ โ ๐)
    claim (inl p) = inl (s-a โ โ p)
    claim (inr u) = inr (ฮป p โ u (a-s โ โ p))

\end{code}
