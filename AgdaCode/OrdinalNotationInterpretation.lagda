Martin Escardo, 2012, 2018.

Compact ordinals, discrete ordinals and their relationships.

A 4-page abstract of a talk at Types'2019:
https://www.cs.bham.ac.uk/~mhe/papers/compact-ordinals-Types-2019-abstract.pdf

Begun December 2012, based on earlier work, circa 2010.

Most of the work has been done later, and coded in July 2018 after a
long pause to understand univalent foundations, which is what we use
in this development, and to develop the mathematical basis for this in
other modules.

Here an ordinal is a type equipped with a well order, namely
relation < which is

  * prop valued,
  * well founded,
  * transitive, and
  * extensional (any two elements with the same lower set are equal).

The extensionality axiom implies that the underlying type of an
ordinal is a set (or satisfies the K axiom), which is proved in the
module OrdinalNotions. This seems to be a new observation about the
univalent notion of ordinal (as introduced in the HoTT Book).

A dependency graph of this module is available at
https://www.cs.bham.ac.uk/~mhe/TypeTopology/OrdinalNotationInterpretation.pdf

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt

module OrdinalNotationInterpretation (fe : FunExt) where

\end{code}

We work with ordinal encodings, or ordinal expressions, that are
slightly different from the traditional Brouwer ordinal trees, which
we also consider towards the end of this article.

\begin{code}

data OE : π€β Μ where
 One  : OE
 Add  : OE β OE β OE
 Mul  : OE β OE β OE
 Sum1 : (β β OE) β OE

\end{code}

We consider two mappings from these ordinal expressions to actual
ordinals as discussed above:

  * Ξ : OE β Ordα΅
  * Ξ : OE β Ordα΅

Here Ordα΅ is the type of ordinals that have a top element (which, in
constructive mathematics, are not in general successor
ordinals). Technically, the top element allows us to prove the closure
of ordinals under ordinal-indexed sums, playing a crucial role in the
proof of extensionality of the sum. But the top element is equally
crucial for compactness purposes, as dicussed below.

  * The ordinals in the image of Ξ are discrete (have decidable
    equality) and have countable underlying sets, which are in fact
    retracts of β.

  * Those in the image of Ξ are compact, or "exhaustibly searchable".

    Moreover, they are retracts of the Cantor type (β β π) of binary
    sequences, and hence are totally separated, which means that the
    functions into π separate the points.

    And not only the Ξ ordinals are searchable, they are also
    inf-compact, which means that any detachable subset has an
    infimum, which belongs to the subset iff and only if the subset is
    non-empty (with non-emptiness expressed by a double negation).

    The discrete ordinals, being retracts of β, cannot be retracts of
    the Cantor space. This is because the Cantor space is potentially
    compact, in the presence of Brouwerian axioms (which we are not
    assuming but are consistent), and compactness is inherited by
    retracts, and the compactnesss of the infinite discrete ordinals
    is equivalent to Bishop's LPO (limited principle of omnscient),
    which is not provable in any variety of constructive mathematics.

The Ξ and Ξ interpretation of One, Add and Mul are as expected. They
differ only in the interpretation of Sum1.

   * In the discrete case, Sum1 is interpreted as simply the countable
     sum plus the ordinal π (written ββ).

   * In the compact case, Sum1 is interpreted as the sum with an added
     non-isolated top point (written βΒΉ). It is this that makes the
     searchability of the compact ordinals possible. The searchability
     of the discrete ordinals is a contructive taboo.

Additionally, we kave a map ΞΉ from the Ξ-ordinals to the Ξ-ordinals,
which is

  * an embedding (has subsingleton fibers),
  * dense (the complement of its image is empty),
  * order preserving and reflecting.

Lastly, we have a mapping from our ordinal trees to Brouwer trees that
allows us to use other people's constructions to get very "large"
compact ordinals. As a trivial example, we show how to map a Brouwer
code of Ξ΅β to a compact ordinal that dominates Ξ΅β.

The bulk of the work to perform these constructions and prove their
properties is developed in the imported modules.

After a brief pause for importing the necessary definitions, we state
the theorems and constructions to be performed here:

\begin{code}

open import OrdinalsType
open import ToppedOrdinalsType fe
open import OrdinalArithmetic fe
open import ToppedOrdinalArithmetic fe
open import OrdinalsClosure fe
open import OrdinalCodes
open import CompactTypes
open import InfCompact
open import TotallySeparated
open import SquashedSum fe
open import SquashedCantor fe hiding (Ξ)
open import DiscreteAndSeparated

open import UF-Subsingletons
open import UF-Retracts
open import UF-Embeddings
open import UF-Miscelanea

\end{code}

In the following, βͺ Ο β« denotes the underlying set of an ordinal Ο, and
_βΊβͺ Ο β«_ denotes its underlying order.

\begin{code}

Ξ                      : OE β Ordα΅
Ξ-compactβ             : (Ξ½ : OE) β compactβ βͺ Ξ Ξ½ β«
Ξ-Cantor-retract       : (Ξ½ : OE) β retract βͺ Ξ Ξ½ β« of (β β π)
Ξ-is-totally-separated : (Ξ½ : OE) β is-totally-separated βͺ Ξ Ξ½ β«

Ξ                      : OE β Ordα΅
Ξ-retract-of-β         : (Ξ½ : OE) β retract βͺ Ξ Ξ½ β« of β
Ξ-is-discrete          : (Ξ½ : OE) β is-discrete βͺ Ξ Ξ½ β«

ΞΉ                      : {Ξ½ : OE} β βͺ Ξ Ξ½ β« β βͺ Ξ Ξ½ β«
ΞΉ-dense                : (Ξ½ : OE) β is-dense (ΞΉ {Ξ½})
ΞΉ-embedding            : (Ξ½ : OE) β is-embedding (ΞΉ {Ξ½})

ΞΉ-order-preserving     : (Ξ½ : OE) (x y : βͺ Ξ Ξ½ β«)
                            β   x βΊβͺ Ξ Ξ½ β«   y
                            β ΞΉ x βΊβͺ Ξ Ξ½ β« ΞΉ y

ΞΉ-order-reflecting     : (Ξ½ : OE) (x y : βͺ Ξ Ξ½ β«)
                            β ΞΉ x βΊβͺ Ξ Ξ½ β« ΞΉ y
                            β   x βΊβͺ Ξ Ξ½ β«   y

Ξ-inf-compact          : propext π€β
                       β (Ξ½ : OE) β inf-compact (Ξ» x y β x βΌβͺ Ξ Ξ½ β« y)

brouwer-to-oe          : B β OE
Ξ΅β-upper-bound         : Ordα΅
compactβ-Ξ΅β-ub         : compactβ βͺ Ξ΅β-upper-bound β«

\end{code}

The interpretation function is the following, with values on topped
ordinals, where an ordinal is a type equipped with a
prop-valued, well-founded, transitive and extensional relation
(and such a type is automatically a set). "Topped" means that there is
a top element in the order

This version of the function is from 1st July 2018 (the original
version considered only the underlying set of the ordinal and didn't
construct the order as this was work in progress):

\begin{code}

Ξ One  = πα΅
Ξ (Add Ξ½ ΞΌ) = Ξ Ξ½ +α΅ Ξ ΞΌ
Ξ (Mul Ξ½ ΞΌ) = Ξ Ξ½ Γα΅  Ξ ΞΌ
Ξ (Sum1 Ξ½) = βΒΉ Ξ»(i : β) β Ξ(Ξ½ i)

\end{code}

The underlying sets β―of such ordinals are compactβ:

\begin{code}

Ξ-compactβ One       = π-compactβ
Ξ-compactβ (Add Ξ½ ΞΌ) = Ξ£-compactβ
                        π+π-compactβ
                        (dep-cases (Ξ» _ β Ξ-compactβ Ξ½) (Ξ» _ β Ξ-compactβ ΞΌ))
Ξ-compactβ (Mul Ξ½ ΞΌ) = Ξ£-compactβ (Ξ-compactβ Ξ½) (Ξ» _ β Ξ-compactβ ΞΌ)
Ξ-compactβ (Sum1 Ξ½)  = Ξ£ΒΉ-compactβ (Ξ» n β βͺ Ξ (Ξ½ n) β«) (Ξ» i β Ξ-compactβ (Ξ½ i))

\end{code}

Completed 20th July 2018:

The compactβ ordinals are retracts of the Cantor type (β β π).

\begin{code}

Ξ-Cantor-retract One       = (Ξ» _ β β) , (Ξ» _ β Ξ» n β β) , π-is-prop β
Ξ-Cantor-retract (Add Ξ½ ΞΌ) = +-retract-of-Cantor (Ξ Ξ½) (Ξ ΞΌ)
                              (Ξ-Cantor-retract Ξ½) (Ξ-Cantor-retract ΞΌ)
Ξ-Cantor-retract (Mul Ξ½ ΞΌ) = Γ-retract-of-Cantor (Ξ Ξ½) (Ξ ΞΌ)
                              (Ξ-Cantor-retract Ξ½) (Ξ-Cantor-retract ΞΌ)
Ξ-Cantor-retract (Sum1 Ξ½)  = Ξ£ΒΉ-Cantor-retract
                               (Ξ» n β βͺ Ξ (Ξ½ n) β«) (Ξ» i β Ξ-Cantor-retract (Ξ½ i))
\end{code}

And hence they are totally separated:

\begin{code}

Ξ-is-totally-separated Ξ½ = retract-of-totally-separated
                             (Ξ-Cantor-retract Ξ½)
                             (Cantor-is-totally-separated feβ)
\end{code}

Without total separatedness (enough functions into the type π of
booleans), compactness wouldn't be an interesting property. It is
not possible to prove total separatedness directly, because this
property is not closed under Ξ£, which is used to define +α΅, Γα΅ and Ξ£β,
as shown in the module FailureOfTotalSeparatedness.

Classically, the squashed sum is the ordinal sum plus 1, and now we
give an alternative semantics of ordinal codes with this
interpretation, which produces ordinals with discrete underlying
sets. Moreover, there is a function that maps the underlying set of
the discrete version to the underlying set of the above version, with
many interesting properties, formulated above and proved below.

\begin{code}

Ξ One       = πα΅
Ξ (Add Ξ½ ΞΌ) = Ξ Ξ½ +α΅ Ξ ΞΌ
Ξ (Mul Ξ½ ΞΌ) = Ξ Ξ½ Γα΅  Ξ ΞΌ
Ξ (Sum1 Ξ½)  = ββ Ξ»(i : β) β Ξ(Ξ½ i)

Ξ-is-discrete One       = π-is-discrete
Ξ-is-discrete (Add Ξ½ ΞΌ) = Ξ£-is-discrete
                           (+-is-discrete π-is-discrete π-is-discrete)
                          (dep-cases (Ξ» _ β Ξ-is-discrete Ξ½)
                          (Ξ» _ β Ξ-is-discrete ΞΌ))
Ξ-is-discrete (Mul Ξ½ ΞΌ) = Ξ£-is-discrete (Ξ-is-discrete Ξ½) (Ξ» _ β Ξ-is-discrete ΞΌ)
Ξ-is-discrete (Sum1 Ξ½)  = Ξ£β-is-discrete
                            (Ξ» n β βͺ Ξ (Ξ½ n) β«)
                            (Ξ» i β Ξ-is-discrete (Ξ½ i))
\end{code}

Completed 27 July 2018. There is a dense embedding ΞΉ of the discrete
ordinals into the compactβ ordinals, where density means that the
complement of the image of the embedding is empty. Moreover, it is
order preserving and reflecting (28 July 2018).

\begin{code}

ΞΉ {One}     = id
ΞΉ {Add Ξ½ ΞΌ} = pair-fun id (dep-cases (Ξ» _ β ΞΉ {Ξ½}) (Ξ» _ β ΞΉ {ΞΌ}))
ΞΉ {Mul Ξ½ ΞΌ} = pair-fun (ΞΉ {Ξ½}) (Ξ» _ β ΞΉ {ΞΌ})
ΞΉ {Sum1 Ξ½}  = ββ (Ξ» n β Ξ (Ξ½ n)) (Ξ» n β Ξ (Ξ½ n)) (Ξ» n β ΞΉ {Ξ½ n})

ΞΉ-dense One       = id-is-dense
ΞΉ-dense (Add Ξ½ ΞΌ) = pair-fun-dense
                     id
                    (dep-cases (Ξ» _ β ΞΉ {Ξ½}) (Ξ» _ β ΞΉ {ΞΌ}))
                    id-is-dense
                    (dep-cases (Ξ» _ β ΞΉ-dense Ξ½) (Ξ» _ β ΞΉ-dense ΞΌ))
ΞΉ-dense (Mul Ξ½ ΞΌ) = pair-fun-dense _ _
                    (ΞΉ-dense Ξ½)
                    (Ξ» _ β ΞΉ-dense ΞΌ)
ΞΉ-dense (Sum1 Ξ½) =  Ξ£β-dense
                     (Ξ» n β βͺ Ξ (Ξ½ n) β«)
                     (Ξ» n β βͺ Ξ (Ξ½ n) β«)
                     (Ξ» n β ΞΉ {Ξ½ n})
                     (Ξ» i β ΞΉ-dense (Ξ½ i))

ΞΉ-embedding One       = id-is-embedding
ΞΉ-embedding (Add Ξ½ ΞΌ) = pair-fun-is-embedding
                         id
                         (dep-cases (Ξ» _ β ΞΉ {Ξ½}) (Ξ» _ β ΞΉ {ΞΌ}))
                         id-is-embedding
                         (dep-cases (Ξ» _ β ΞΉ-embedding Ξ½) (Ξ» _ β ΞΉ-embedding ΞΌ))
ΞΉ-embedding (Mul Ξ½ ΞΌ) = pair-fun-is-embedding _ _
                         (ΞΉ-embedding Ξ½)
                         (Ξ» _ β ΞΉ-embedding ΞΌ)
ΞΉ-embedding (Sum1 Ξ½)  = Ξ£β-embedding
                         (Ξ» n β βͺ Ξ (Ξ½ n) β«)
                         (Ξ» n β βͺ Ξ (Ξ½ n) β«)
                         (Ξ» n β ΞΉ {Ξ½ n})
                         (Ξ» i β ΞΉ-embedding (Ξ½ i))

ΞΉ-order-preserving One       = Ξ» x y l β l
ΞΉ-order-preserving (Add Ξ½ ΞΌ) = pair-fun-is-order-preserving
                                πα΅
                                πα΅
                                (cases (Ξ» _ β Ξ Ξ½) (Ξ» _ β Ξ ΞΌ))
                                (cases (Ξ» _ β Ξ Ξ½) (Ξ» _ β Ξ ΞΌ))
                                id
                                (dep-cases (Ξ» _ β ΞΉ {Ξ½}) (Ξ» _ β ΞΉ {ΞΌ}))
                                (Ξ» x y l β l)
                                (dep-cases (Ξ» _ β ΞΉ-order-preserving Ξ½)
                                           (Ξ» _ β ΞΉ-order-preserving ΞΌ))
ΞΉ-order-preserving (Mul Ξ½ ΞΌ) = pair-fun-is-order-preserving
                                (Ξ Ξ½)
                                (Ξ Ξ½)
                                (Ξ» _ β Ξ ΞΌ)
                                (Ξ» _ β Ξ ΞΌ)
                                (ΞΉ {Ξ½})
                                (Ξ» _ β ΞΉ {ΞΌ})
                                (ΞΉ-order-preserving Ξ½)
                                (Ξ» _ β ΞΉ-order-preserving ΞΌ)
ΞΉ-order-preserving (Sum1 Ξ½) = ββ-is-order-preserving
                                (Ξ β Ξ½)
                                (Ξ β Ξ½)
                                (Ξ» n β ΞΉ {Ξ½ n})
                                (Ξ» i β ΞΉ-order-preserving (Ξ½ i))

ΞΉ-order-reflecting One       = Ξ» x y l β l
ΞΉ-order-reflecting (Add Ξ½ ΞΌ) = pair-fun-is-order-reflecting
                                πα΅
                                πα΅
                                (cases (Ξ» _ β Ξ Ξ½) (Ξ» _ β Ξ ΞΌ))
                                (cases (Ξ» _ β Ξ Ξ½) (Ξ» _ β Ξ ΞΌ))
                                id
                                (dep-cases (Ξ» _ β ΞΉ {Ξ½}) (Ξ» _ β ΞΉ {ΞΌ}))
                                (Ξ» x y l β l)
                                id-is-embedding
                                (dep-cases (Ξ» _ β ΞΉ-order-reflecting Ξ½)
                                           (Ξ» _ β ΞΉ-order-reflecting ΞΌ))
ΞΉ-order-reflecting (Mul Ξ½ ΞΌ) = pair-fun-is-order-reflecting
                                (Ξ Ξ½)
                                (Ξ Ξ½)
                                (Ξ» _ β Ξ ΞΌ)
                                (Ξ» _ β Ξ ΞΌ)
                                (ΞΉ {Ξ½})
                                (Ξ» _ β ΞΉ {ΞΌ})
                                (ΞΉ-order-reflecting Ξ½)
                                (ΞΉ-embedding Ξ½)
                                (Ξ» _ β ΞΉ-order-reflecting ΞΌ)
ΞΉ-order-reflecting (Sum1 Ξ½)  = ββ-is-order-reflecting
                                (Ξ β Ξ½)
                                (Ξ β Ξ½)
                                (Ξ» n β ΞΉ {Ξ½ n})
                                (Ξ» i β ΞΉ-order-reflecting (Ξ½ i))
\end{code}

As discussed in the module Ordinals, propositional extensionality in
the following construction is not strictly needed but makes our life
much easier (given the mathematics we have already developed).

\begin{code}

Ξ-inf-compact pe One       = πα΅-inf-compact
Ξ-inf-compact pe (Add Ξ½ ΞΌ) = β-inf-compact pe
                               πα΅
                               (cases (Ξ» _ β Ξ Ξ½) (Ξ» _ β Ξ ΞΌ))
                               πα΅-inf-compact
                               (dep-cases (Ξ» _ β Ξ-inf-compact pe Ξ½)
                                          (Ξ» _ β Ξ-inf-compact pe ΞΌ))
Ξ-inf-compact pe (Mul Ξ½ ΞΌ) = β-inf-compact pe
                               (Ξ Ξ½)
                               (Ξ» _ β Ξ ΞΌ)
                               (Ξ-inf-compact pe Ξ½)
                               (Ξ» _ β Ξ-inf-compact pe ΞΌ)
Ξ-inf-compact pe (Sum1 Ξ½) = ββ-inf-compact
                               pe
                               (Ξ β Ξ½)
                               (Ξ» i β Ξ-inf-compact pe (Ξ½ i))
\end{code}

Added 31 July 2018:

\begin{code}

Ξ-retract-of-β One       = (Ξ» _ β β) , (Ξ» _ β 0) , π-is-prop β
Ξ-retract-of-β (Add Ξ½ ΞΌ) = Ξ£-retract-of-β
                             retract-π+π-of-β
                             (dep-cases (Ξ» _ β Ξ-retract-of-β Ξ½)
                                        (Ξ» _ β Ξ-retract-of-β ΞΌ))
Ξ-retract-of-β (Mul Ξ½ ΞΌ) = Ξ£-retract-of-β
                             (Ξ-retract-of-β Ξ½)
                             (Ξ» _ β Ξ-retract-of-β ΞΌ)
Ξ-retract-of-β (Sum1 Ξ½) = Ξ£β-β-retract (Ξ» i β Ξ-retract-of-β (Ξ½ i))

\end{code}

NB. We could have proved that the Ξ-ordinals are discrete using the
above, as discrete types are closed under retracts.

Hence the compactness of any infinite discrete ordinal is a
constructive taboo, logically equivalent to Bishop's LPO.

Brouwer ordinal codes can be mapped to compactβ ordinal codes, so
that the meaning is not necessarily preserved, but so that it is
bigger or equal, because sums dominate suprema.

\begin{code}

brouwer-to-oe    Z  = One
brouwer-to-oe (S Ξ½) = Add One (brouwer-to-oe Ξ½)
brouwer-to-oe (L Ξ½) = Sum1 (Ξ» i β brouwer-to-oe (Ξ½ i))

\end{code}

The following is a relatively "small" example: an upper bound of the
ordinal Ξ΅β (because sums dominate suprema):

\begin{code}

Ξ΅β-upper-bound = Ξ (brouwer-to-oe B-Ξ΅β)

compactβ-Ξ΅β-ub = Ξ-compactβ (brouwer-to-oe B-Ξ΅β)

\end{code}

We can go much higher using the work of and Setzer, Hancock and
others.
