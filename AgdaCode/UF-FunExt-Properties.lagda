Martin Escardo, 19th May 2018.

Properties of function extensionality.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-FunExt-Properties where

open import SpartanMLTT
open import UF-Base
open import UF-FunExt
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-Yoneda
open import UF-Subsingletons
open import UF-Retracts
open import UF-EquivalenceExamples

\end{code}

Vladimir Voevodsky proved in Coq that naive function extensionality
(any two pointwise equal non-dependent functions are equal) implies
function extensionality (happly is an equivalence, for dependent
functions):

  https://github.com/vladimirias/Foundations/blob/master/Generalities/uu0.v

Here is an Agda version, with explicit indication of the universe levels.

\begin{code}

naive-funext-gives-funext' : naive-funext π€ (π€ β π₯) β naive-funext π€ π€ β funext π€ π₯
naive-funext-gives-funext' {π€} {π₯} nfe nfe' = funext-via-singletons Ξ³
 where
  Ξ³ : (X : π€ Μ ) (A : X β π₯ Μ )
    β ((x : X) β is-singleton (A x))
    β is-singleton (Ξ  A)
  Ξ³ X A Ο = Ξ΄
   where
    f : Ξ£ A β X
    f = prβ

    f-is-equiv : is-equiv f
    f-is-equiv = prβ-equivalence X A Ο

    g : (X β Ξ£ A) β (X β X)
    g h = f β h

    g-is-equiv : is-equiv g
    g-is-equiv = equiv-post nfe nfe' f f-is-equiv

    e : β! h κ (X β Ξ£ A) , f β h β‘ id
    e = equivs-are-vv-equivs g g-is-equiv id

    r : (Ξ£ h κ (X β Ξ£ A) , f β h β‘ id) β Ξ  A
    r (h , p) x = transport A (happly p x) (prβ (h x))

    s : Ξ  A β (Ξ£ h κ (X β Ξ£ A) , f β h β‘ id)
    s Ο = (Ξ» x β x , Ο x) , refl

    rs : β Ο β r (s Ο) β‘ Ο
    rs Ο = refl

    Ξ΄ : is-singleton (Ξ  A)
    Ξ΄ = retract-of-singleton (r , s , rs) e

naive-funext-gives-funext : naive-funext π€ π€ β funext π€ π€
naive-funext-gives-funext fe = naive-funext-gives-funext' fe fe

naive-funext-gives-funextβ : naive-funext π€ π€ β funext π€ π€β
naive-funext-gives-funextβ fe = naive-funext-gives-funext' fe fe

\end{code}
