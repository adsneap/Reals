Martin Escardo 2011.

The Cantor space is the type (β β π). We show it is compact, under
the assumptions discussed in CountableTychonoff.

This module is a set of corollaries of the module CountableTychonoff
and other modules.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT
open import Two-Properties
open import UF-FunExt

module CantorCompact (fe : FunExt) where

open import CompactTypes
open import CountableTychonoff fe
open import CompactTypes
open import WeaklyCompactTypes

cantor-compactβ : compactβ (β β π)
cantor-compactβ = countable-Tychonoff (Ξ» i β π-compactβ)

cantor-compact : compact (β β π)
cantor-compact = compactβ-gives-compact cantor-compactβ

cantor-wcompact : wcompact (β β π)
cantor-wcompact = compact-gives-wcompact cantor-compactβ

\end{code}

The characteristic function of the universal quantifier
of the Cantor space:

\begin{code}

A : ((β β π) β π) β π
A = prβ (wcompact-implies-wcompact' cantor-wcompact)

\end{code}

Discreteness of ((β β π) β β):

\begin{code}

open import DiscreteAndSeparated

Cantorββ-is-discrete : is-discrete ((β β π) β β)
Cantorββ-is-discrete = compact-discrete-discrete' (fe π€β π€β) cantor-compact β-is-discrete

\end{code}

The characteristic function of equality on ((β β π) β β):

\begin{code}

open import DecidableAndDetachable

equal : ((β β π) β β) β ((β β π) β β) β π

equal f  = prβ (characteristic-function (Cantorββ-is-discrete f))

\end{code}

Experiments: Evaluate the following to normal form (give β, β, β, β quickly):

\begin{code}

number : π β β
number β = 0
number β = 1

test0 : π
test0 = A (Ξ» Ξ± β minπ (Ξ± 17) (Ξ± 180))

test1 : π
test1 = A (Ξ» Ξ± β β)

test2 : π
test2 = equal (Ξ» Ξ± β number (Ξ± 17)) (Ξ» Ξ± β number (Ξ± 100))

test3 : π
test3 = equal (Ξ» Ξ± β number (Ξ± 100)) (Ξ» Ξ± β number (Ξ± 100))

test4 : π
test4 = equal (Ξ» Ξ± β number (Ξ± 1000)) (Ξ» Ξ± β number (Ξ± 1000))

test5 : π
test5 = equal (Ξ» Ξ± β number (Ξ± 1001)) (Ξ» Ξ± β number (Ξ± 1000))

\end{code}
