Martin Escardo 7th December 2022

Type-class for notation for _+_.

Unfortunately, _+_ for types has a different precedence than _+_ for
naturals, integers, rationals, reals, etc., and so we use temporarily
_โ_ (\dotplus) here. An alternative is โงพ ("C-x 8 RET TINY").

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module PlusNotation where

open import Universes

record Plus {๐ค} {๐ฅ} {๐ฆ} (X : ๐ค ฬ ) (Y : ๐ฅ ฬ ) : (๐ค โ ๐ฅ โ ๐ฆ)โบ ฬ  where
 field
   _โ_ : X โ Y โ ๐ฆ  ฬ

 infixl 31 _โ_

open Plus {{...}} public


\end{code}
