Andrew Sneap


\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _ā_)

open import NaturalNumbers
open import Fin
open import Fin-Properties
open import UF-Subsingletons

open import FieldAxioms


module Matrices
  (Field : Ordered-Field š¤ { š„ } { š¦ })
  where

F : š¤ Ģ
F = āØ Field ā©

eā : F
eā = additive-identity Field

eā : F
eā = multiplicative-identity Field

_+_ : F ā F ā F
_+_ = addition Field 

+-comm : (x y : F) ā x + y ā” y + x
+-comm = addition-commutative Field

_*_ : F ā F ā F
_*_ = multiplication Field

F-is-set : is-set F
F-is-set = underlying-type-is-set Field

F-zero-left-neutral : (x : F) ā eā + x ā” x
F-zero-left-neutral = zero-left-neutral Field

matrix : (n m : ā) ā š¤ Ģ
matrix n m = Fin n ā Fin m ā F

0ā : {n m : ā} ā matrix n m
0ā i j = eā

row : {n m : ā} ā Fin n ā matrix n m ā matrix 1 m
row fn A i j = A fn j

column : {n m : ā} ā Fin m ā matrix n m ā matrix n 1
column fm A i j = A i fm

inner-product : {n : ā} ā matrix 1 n ā matrix n 1 ā matrix 1 1 -- With help from "An Agda proof of Valiant's aglorithm for context free parsing"
inner-product {zero} A B i j = eā
inner-product {succ n} A B i j = (A fzero fzero * B fzero fzero) + inner-product {n} (Ī» i j ā A fzero (suc j)) (Ī» i j ā B (suc i) j) i j

outer-product : {n : ā} ā matrix n 1 ā matrix 1 n ā matrix n n
outer-product A B i j = A i fzero * B fzero j

_*M_ : {n m q : ā} ā matrix n m ā matrix m q ā matrix n q
_*M_ A B i j = inner-product (row i A) (column j B) fzero fzero

_ā_ : {n m : ā} ā (A B : matrix n m) ā š¤ Ģ
_ā_ {n} {m} A B = (i : Fin n) ā (j : Fin m) ā A i j ā” B i j

infix 19 _ā_

_+M_ : {n m : ā} ā matrix n m ā matrix n m ā matrix n m
_+M_ A B i j = A i j + B i j

+M-comm : {n m : ā} ā (A B : matrix n m) ā (A +M B) ā (B +M A)
+M-comm A B i j = +-comm (A i j) (B i j)

_*sM_ : {n m : ā} ā (s : F) ā matrix n m ā matrix n m
_*sM_ s M i j = s * M i j

įµ : {n m : ā} ā matrix n m ā matrix m n
įµ A i j = A j i

transpose-involutive : {n m : ā} ā (M : matrix n m) ā įµ (įµ M) ā” M
transpose-involutive M = refl

transpose-involutive' : {n m : ā} ā (M : matrix n m) ā įµ (įµ M) ā M
transpose-involutive' M i j = įµ (įµ M) i j ā”āØ by-definition ā©
                              įµ M j i     ā”āØ by-definition ā©
                              M i j ā

+M-zero-left-neutral : {n m : ā} ā (A : matrix n m) ā 0ā +M A ā A
+M-zero-left-neutral A i j = (0ā +M A) i j    ā”āØ by-definition ā©
                             (0ā i j + A i j) ā”āØ by-definition ā©
                             (eā + A i j)     ā”āØ F-zero-left-neutral (A i j) ā©
                             A i j ā


open import UF-FunExt
open import UF-Subsingletons-FunExt

matrix-equivāequality : Fun-Ext ā {n m : ā} ā (A B : matrix n m) ā A ā B ā A ā” B
matrix-equivāequality fe {n} {m} A B equiv = dfunext fe (Ī» i ā dfunext fe (Ī» j ā equiv i j))











