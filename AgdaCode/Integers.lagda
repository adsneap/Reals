Tom de Jong
Reboot: 22 January 2021
Earlier version: 18 September 2020

We construct the type of integers with the aim of using them in constructing the
circle as the type of ā¤-torsors, as described in "Construction of the circle in
UniMath" by Bezem, Buchholtz, Grayson and Shulman
(doi:10.1016/j.jpaa.2021.106687).

See Integers-Properties and Integers-SymmetricInduction for (more) properties of
the type of integers.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base

module Integers where

ā¤ : š¤ā Ģ
ā¤ = š + ā + ā

pattern š     = inl ā
pattern pos i = inr (inl i)
pattern neg i = inr (inr i)

ā-to-ā¤ā : ā ā ā¤
ā-to-ā¤ā 0        = š
ā-to-ā¤ā (succ n) = pos n

ā-to-ā¤ā : ā ā ā¤
ā-to-ā¤ā 0        = š
ā-to-ā¤ā (succ n) = neg n

ā¤-induction : {š¤ : Universe} (P : ā¤ ā š¤ Ģ )
            ā P š
            ā ((n : ā) ā P (ā-to-ā¤ā n) ā P (ā-to-ā¤ā (succ n)))
            ā ((n : ā) ā P (ā-to-ā¤ā n) ā P (ā-to-ā¤ā (succ n)))
            ā (z : ā¤) ā P z
ā¤-induction {š¤} P pā pā pā š       = pā
ā¤-induction {š¤} P pā pā pā (pos i) = h (succ i)
 where
  Pā : ā ā š¤ Ģ
  Pā = P ā ā-to-ā¤ā
  h : (n : ā) ā Pā n
  h = induction pā pā
ā¤-induction {š¤} P pā pā pā (neg i) = h (succ i)
 where
  Pā : ā ā š¤ Ģ
  Pā = P ā ā-to-ā¤ā
  h : (n : ā) ā Pā n
  h = induction pā pā

\end{code}
