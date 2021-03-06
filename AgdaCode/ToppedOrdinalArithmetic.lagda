Martin Escardo, 29 June 2018

To get closure under sums constructively, we need to restrict to
particular kinds of ordinals. Having a top element is a simple
sufficient condition, which holds in the applications we have in mind
(for compact ordinals).  Classically, ordinals with a top element are
precisely the successor ordinals. Constructively, ββ is an example of
an ordinal with a top element, which "is not" a successor ordinal, as
its top element is not isolated.

TODO. Generalize this from π€β to an arbitrary universe. The
(practical) problem is that the type of natural numbers is defined at
π€β. We could (1) either using universe lifting, or (2) define the type
in any universe (like we did for the the types π and π). But (1) is
cumbersome and (2) requires much work in other modules.


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module ToppedOrdinalArithmetic
        (fe : FunExt)
       where

open import SpartanMLTT
open import OrdinalsType
open import OrdinalArithmetic fe
open import OrdinalsWellOrderArithmetic
open import ToppedOrdinalsType fe
open import GenericConvergentSequence
open import NaturalsOrder
open import InjectiveTypes fe
open import SquashedSum fe
open import CanonicalMapNotation

open import UF-Subsingletons
open import UF-Embeddings

Ordα΅ = Ordinalα΅ π€β

succβ : Ord β Ordα΅
succβ Ξ± = Ξ± +β πβ  ,
          plus.top-preservation
           (underlying-order Ξ±)
           (underlying-order πβ)
           (prop.topped π π-is-prop β)

πα΅ πα΅ ββα΅ : Ordα΅
πα΅  = πβ , prop.topped π π-is-prop β
πα΅  = succβ πβ
ββα΅ = (βββ , β , β-top)

\end{code}

Sum of an ordinal-indexed family of ordinals:

\begin{code}

β : (Ο : Ordα΅) β (βͺ Ο β« β Ordα΅) β Ordα΅
β ((X , _<_ , o) , t) Ο = ((Ξ£ x κ X , βͺ Ο x β«) ,
                              Sum.order ,
                              Sum.well-order o (Ξ» x β tis-well-ordered (Ο x))) ,
                          Sum.top-preservation t
 where
  _βΊ_ : {x : X} β βͺ Ο x β« β βͺ Ο x β« β π€β Μ
  y βΊ z = y βΊβͺ Ο _ β« z

  module Sum = sum-top fe _<_ _βΊ_ (Ξ» x β top (Ο x)) (Ξ» x β top-is-top (Ο x))

\end{code}

Addition and multiplication can be reduced to β, given the ordinal πα΅
defined above:

\begin{code}

_+α΅_ : Ordα΅ β Ordα΅ β Ordα΅
Ο +α΅ Ο = β πα΅ (cases (Ξ» _ β Ο) (Ξ» _ β Ο))

_Γα΅_ : Ordα΅ β Ordα΅ β Ordα΅
Ο Γα΅ Ο = β Ο  (Ξ» (_ : βͺ Ο β«) β Ο)

\end{code}

Extension of a family X β Ordα΅ along an embedding j : X β A to get a
family A β Ordα΅. (This can also be done for Ord-valued families.)
This uses the module π€βF-InjectiveTypes to calculate Y / j.

\begin{code}

_β_ : {X A : π€β Μ } β (X β Ordα΅) β (Ξ£ j κ (X β A), is-embedding j) β (A β Ordα΅)
Ο β (j , e) = Ξ» a β ((Y / j) a ,
                     Extension.order a ,
                     Extension.well-order a (Ξ» x β tis-well-ordered (Ο x))) ,
                     Extension.top-preservation a (Ξ» x β topped (Ο x))
 where
  Y : domain Ο β π€β Μ
  Y x = βͺ Ο x β«
  module Extension = extension fe Y j e (Ξ» {x} β tunderlying-order (Ο x))

\end{code}

Sum of a countable family with an added non-isolated top element. We
first extend the family to ββ and then take the ordinal-indexed sum of
ordinals defined above.

\begin{code}

βΒΉ : (β β Ordα΅) β Ordα΅
βΒΉ Ο = β ββα΅ (Ο β (ΞΉ , ΞΉ-embedding feβ))

\end{code}

And now with an isolated top element:

\begin{code}

ββ : (β β Ordα΅) β Ordα΅
ββ Ο = β (succβ ββ) (Ο β (over , over-embedding))

\end{code}
