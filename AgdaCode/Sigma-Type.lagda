\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Sigma-Type where

open import Universes

record Î£ {ð¤ ð¥} {X : ð¤ Ì } (Y : X â ð¥ Ì ) : ð¤ â ð¥ Ì  where
  constructor
   _,_
  field
   prâ : X
   prâ : Y prâ

infixr 50 _,_

\end{code}
