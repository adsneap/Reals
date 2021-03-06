Cory Knapp, 6th June 2018.

This is an alternative version of naive-funext-gives-funext from
UF-FunExt-Properties.lagda (by Martin Escardo, 19th May 2018);

here we split the proof that naive function extensionality into two parts:

1. If post-composition with an equivalence is again an equivalence, then
   function extensionality holds;

2. If naive-function extensionality holds, then the antecedent of the
   above holds.

Point 2. is already proved in UF-Equiv-Funext.lagda

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-FunExt-from-Naive-FunExt where

open import SpartanMLTT
open import UF-Base
open import UF-FunExt
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-Equiv-FunExt
open import UF-Yoneda
open import UF-Subsingletons
open import UF-Retracts

equiv-post-comp-closure : â ð¤ ð¦ ð¥ â (ð¤ â ð¥ â ð¦) âº Ì
equiv-post-comp-closure ð¤ ð¥ ð¦ = {X : ð¤ Ì } {Y : ð¥ Ì } {A : ð¦ Ì } (f : X â Y)
                                â is-equiv f â is-equiv (Î» (h : A â X) â f â h)

equiv-post-gives-funext' : equiv-post-comp-closure (ð¤ â ð¥) ð¤ ð¤ â funext ð¤ ð¥
equiv-post-gives-funext' {ð¤} {ð¥} eqc = funext-via-singletons Î³
  where
  Î³ : (X : ð¤ Ì ) (A : X â ð¥ Ì ) â ((x : X) â is-singleton (A x)) â is-singleton (Î  A)
  Î³ X A Ï = retract-of-singleton (r , s , rs) iss
   where
   f : Î£ A â X
   f = prâ
   eqf : is-equiv f
   eqf = prâ-equivalence X A Ï
   g : (X â Î£ A) â (X â X)
   g h = f â h
   eqg : is-equiv g
   eqg = eqc f eqf
   iss : â! h ê (X â Î£ A), f â h â¡ id
   iss = equivs-are-vv-equivs g eqg id
   r : (Î£ h ê (X â Î£ A), f â h â¡ id) â Î  A
   r (h , p) x = transport A (happly p x) (prâ (h x))
   s : Î  A â (Î£ h ê (X â Î£ A), f â h â¡ id)
   s Ï = (Î» x â x , Ï x) , refl
   rs : â Ï â r (s Ï) â¡ Ï
   rs Ï = refl

naive-funext-gives-funext' : naive-funext ð¤ (ð¤ â ð¥) â naive-funext ð¤ ð¤ â funext ð¤ ð¥
naive-funext-gives-funext' nfe nfe' = equiv-post-gives-funext' (equiv-post nfe nfe')

naive-funext-gives-funext : naive-funext ð¤ ð¤ â funext ð¤ ð¤
naive-funext-gives-funext fe = naive-funext-gives-funext' fe fe

\end{code}
