\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Universes where

open import Agda.Primitive public
  using (_â_)
  renaming (lzero to ð¤â
          ; lsuc to _âº
          ; Level to Universe
          ; SetÏ to ð¤Ï
          )

variable
 ð¤ ð¥ ð¦ ð£ ð¤' ð¥' ð¦' ð£' : Universe

\end{code}

The following should be the only use of the Agda keyword 'Set' in this
development:

\begin{code}

_Ì : (ð¤ : Universe) â _
ð¤ Ì = Set ð¤

ð¤â = ð¤â âº
ð¤â = ð¤â âº

_âºâº : Universe â Universe
ð¤ âºâº = ð¤ âº âº

\end{code}

This is mainly to avoid naming implicit arguments:

\begin{code}

universe-of : (X : ð¤ Ì ) â Universe
universe-of {ð¤} X = ð¤

\end{code}

precedences:

\begin{code}

infix  1 _Ì

\end{code}
