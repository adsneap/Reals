Martin Escardo 2011.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module Sequence (fe : FunExt) where

open import SpartanMLTT hiding (_+_)
open import UF-Base
open import UF-Retracts
open import NaturalsAddition

_βΆβΆ_ : {X : β β π€ Μ } β X 0 β ((n : β) β X (succ n)) β ((n : β) β X n)
(x βΆβΆ Ξ±) 0 = x
(x βΆβΆ Ξ±) (succ n) = Ξ± n

head : {X : β β π€ Μ } β ((n : β) β X n) β X 0
head Ξ± = Ξ± 0

tail : {X : β β π€ Μ } β ((n : β) β X n) β ((n : β) β X (succ n))
tail Ξ± n = Ξ± (succ n)

head-tail-eta : {X : β β π€ Μ } {Ξ± : (n : β) β X n} β (head Ξ± βΆβΆ tail Ξ±) β‘ Ξ±
head-tail-eta {π€} {X} = dfunext (fe π€β π€) lemma
 where
  lemma : {Ξ± : (n : β) β X n} β (i : β) β (head Ξ± βΆβΆ tail Ξ±) i β‘ Ξ± i
  lemma 0 = refl
  lemma (succ i) = refl

private cons : {X : β β π€ Μ } β X 0 Γ ((n : β) β X (succ n)) β ((n : β) β X n)
cons (x , Ξ±) = x βΆβΆ Ξ±

cons-has-section' : {X : β β π€ Μ } β has-section' (cons {π€} {X})
cons-has-section' Ξ± = (head Ξ± , tail Ξ±) , head-tail-eta

\end{code}

(In fact it is an equivalence, but I won't bother, until this is
needed.)

\begin{code}

itail : {X : β β π€ Μ } β (n : β) β ((i : β) β X i) β ((i : β) β X (i + n))
itail n Ξ± i = Ξ± (i + n)

\end{code}

Added 16th July 2018. Corecursion on sequences β β A.

                    p = (h,t)
             X ------------------> A Γ X
             |                       |
             |                       |
          f  |                       | A Γ f
             |                       |
             |                       |
             v                       v
         (β β A) ---------------> A Γ (β β A)
                  P = (head, tail)


  head (f x) = h x
  tail (f x) = f (t x)

Or equivalentaily

  f x = cons (h x) (f (t x))

\begin{code}

module _ {π€ π₯ : Universe}
         {A : π€ Μ }
         {X : π₯ Μ }
         (h : X β A)
         (t : X β X)
       where

 private
  f : X β (β β A)
  f x zero = h x
  f x (succ n) = f (t x) n

 seq-corec = f

 seq-corec-head : head β f βΌ h
 seq-corec-head x = refl

 seq-corec-tail : tail β f βΌ f β t
 seq-corec-tail x = dfunext (fe π€β π€) (Ξ» n β refl)

 seq-final : Ξ£! f κ (X β (β β A)), (head β f βΌ h) Γ (tail β f βΌ f β t)
 seq-final = (seq-corec , seq-corec-head , seq-corec-tail) , c
  where
   c : (f f' : X β β β A) β
         (head β f βΌ h) Γ (tail β f βΌ f β t) β
         (head β f' βΌ h) Γ (tail β f' βΌ f' β t) β f β‘ f'
   c f f' (a , b) (c , d) = dfunext (fe π₯ π€) (Ξ» x β dfunext (fe π€β π€) (r x))
    where
     r : (x : X) (n : β) β f x n β‘ f' x n
     r x zero = a x β (c x)β»ΒΉ
     r x (succ n) = f x (succ n) β‘β¨ ap (Ξ» - β - n) (b x) β©
                    f (t x) n    β‘β¨ r (t x) n β©
                    f' (t x) n   β‘β¨ ( ap (Ξ» - β - n) (d x)) β»ΒΉ β©
                    f' x (succ n) β

 \end{code}

Added 11th September 2018.

\begin{code}

seq-bisimulation : {A : π€ Μ } β ((β β A) β (β β A) β π₯ Μ ) β π€ β π₯ Μ
seq-bisimulation {π€} {π₯} {A} R = (Ξ± Ξ² : β β A) β R Ξ± Ξ²
                                                 β (head Ξ± β‘ head Ξ²)
                                                 Γ R (tail Ξ±) (tail Ξ²)

seq-coinduction : {A : π€ Μ } (R : (β β A) β (β β A) β π₯ Μ )
                β seq-bisimulation R β (Ξ± Ξ² : β β A) β R Ξ± Ξ² β Ξ± β‘ Ξ²
seq-coinduction {π€} {π₯} {A} R b Ξ± Ξ² r = dfunext (fe π€β π€) (h Ξ± Ξ² r)
 where
  h : (Ξ± Ξ² : β β A) β R Ξ± Ξ² β Ξ± βΌ Ξ²
  h Ξ± Ξ² r zero = prβ (b Ξ± Ξ² r)
  h Ξ± Ξ² r (succ n) = h (tail Ξ±) (tail Ξ²) (prβ (b Ξ± Ξ² r)) n

\end{code}
