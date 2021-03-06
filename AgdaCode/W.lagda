W-types.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module W where

open import SpartanMLTT

data W {๐ค ๐ฅ : Universe} (X : ๐ค ฬ ) (A : X โ ๐ฅ ฬ ) : ๐ค โ ๐ฅ ฬ where
 sup : (x : X) โ (A x โ W X A) โ W X A

\end{code}

The record version of W in case we need it:

\begin{code}

record W' {๐ค ๐ฅ : Universe} (X : ๐ค ฬ ) (A : X โ ๐ฅ ฬ ) : ๐ค โ ๐ฅ ฬ where
 inductive
 constructor
  sup
 field
  prโ : X
  prโ : A prโ โ W' X A

\end{code}

Indexed version of W:

\begin{code}

data Wแตข {๐ค ๐ฅ ๐ฆ : Universe}
        (I : ๐ฆ ฬ )
        (A : ๐ค ฬ )
        (t : A โ I)
        (B : A โ ๐ฅ ฬ )
        (s : (a : A) โ B a โ I)
      : I โ ๐ค โ ๐ฅ โ ๐ฆ ฬ
 where
 sup : (a : A) โ ((b : B a) โ Wแตข I A t B s (s a b)) โ Wแตข I A t B s (t a)

\end{code}

E.g. for typed terms:

  I    type of "types"
  A    type of operations
  t    type of the result
  B    arity assignment
  s    type of arguments
