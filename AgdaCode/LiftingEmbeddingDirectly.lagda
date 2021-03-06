Martin Escardo 25th October 2018.

We show that the natural map into the lifting is an embedding.  See
the module LiftingEmbeddingViaSIP for an alternative approach via the
structure identity principle.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module LiftingEmbeddingDirectly (π£ : Universe) where

open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Embeddings
open import UF-Equiv
open import UF-FunExt

open import Lifting π£

\end{code}

Our strategy here to show that Ξ· is an embedding (has subsingleton
fibers) is to exhibit it as the composite of two embeddings (the first
of which is actually an equivalence).

\begin{code}

π : π€ Μ β π€ β π£ βΊ Μ
π X = Ξ£ P κ π£ Μ , (P β X) Γ is-singleton P

ΞΊ : {X : π€ Μ } β X β π X
ΞΊ x = π , (Ξ» _ β x) , π-is-singleton

ΞΆ : (X : π€ Μ ) (P : π£ Μ ) β (P β X) Γ is-singleton P β (P β X) Γ is-prop P
ΞΆ X P (Ο , i) = Ο , singletons-are-props i

πβπ : (X : π€ Μ ) β π X β π X
πβπ X = NatΞ£ (ΞΆ X)

Ξ·-composite : funext π£ π£
            β funext π€ (π£ βΊ β π€)
            β {X : π€ Μ } β Ξ· β‘ πβπ X β ΞΊ
Ξ·-composite fe fe' {X} = dfunext fe' h
 where
  h : (x : X) β (π , (Ξ» _ β x) , π-is-prop)
              β‘ (π , (Ξ» _ β x) , singletons-are-props (π-is-singleton))
  h x = to-Ξ£-β‘ (refl , to-Γ-β‘ refl (being-prop-is-prop fe _ _))

\end{code}

The fact that πβπ is an embedding can be proved by obtaining it as
a combination of maps that we already know to be embeddings, using
Γ-embedding, maps-of-props-are-embeddings, id-is-embedding, and
NatΞ£-embedding.:

\begin{code}

ΞΆ-is-embedding : funext π£ π£ β (X : π€ Μ ) (P : π£ Μ ) β is-embedding (ΞΆ X P)
ΞΆ-is-embedding fe X P = Γ-embedding
                          id
                          singletons-are-props
                          id-is-embedding
                          (maps-of-props-are-embeddings
                            singletons-are-props
                            (being-singleton-is-prop fe)
                            (being-prop-is-prop fe))

πβπ-is-embedding : funext π£ π£ β (X : π€ Μ ) β is-embedding (πβπ X)
πβπ-is-embedding fe X = NatΞ£-is-embedding
                          (Ξ» P β (P β X) Γ is-singleton P)
                          (Ξ» P β (P β X) Γ is-prop P)
                          (ΞΆ X)
                          (ΞΆ-is-embedding fe X)

\end{code}

That ΞΊ is an equivalence corresponds to the fact that the lifting of a
type X with respect to the dominance "is-singleton" is equivalent to X
itself.

\begin{code}

ΞΊ-is-equiv : propext π£
           β funext π£ π£
           β funext π£ π€
           β {X : π€ Μ } β is-equiv (ΞΊ {π€} {X})
ΞΊ-is-equiv {π€} pe fe fe' {X} = qinvs-are-equivs ΞΊ (Ο , (ΟΞΊ , ΞΊΟ))
 where
  Ο : {X : π€ Μ } β π X β X
  Ο (P , Ο , i) = Ο (center i)
  ΟΞΊ : {X : π€ Μ } (x : X) β Ο (ΞΊ x) β‘ x
  ΟΞΊ x = refl
  ΞΊΟ : (m : π X) β ΞΊ (Ο m) β‘ m
  ΞΊΟ (P , Ο , i) = u
   where
    t : π β‘ P
    t = pe π-is-prop (singletons-are-props i)
                     (Ξ» _ β center i)
                     unique-to-π
    s : (t : π β‘ P)
      β transport (Ξ» - β (- β X) Γ is-singleton -)
                  t ((Ξ» _ β Ο (center i)),
        π-is-singleton)
      β‘ Ο , i
    s refl = to-Γ-β‘ a b
     where
      a : (Ξ» x β Ο (center i)) β‘ Ο
      a = dfunext fe' (Ξ» x β ap Ο (π-is-prop (center i) x))
      b : π-is-singleton β‘ i
      b = (singletons-are-props (pointed-props-are-singletons
                                   π-is-singleton (being-singleton-is-prop fe))
                                 π-is-singleton i)
    u : π , (Ξ» _ β Ο (center i)) , π-is-singleton β‘ P , Ο , i
    u = to-Ξ£-β‘ (t , s t)

ΞΊ-is-embedding : propext π£ β funext π£ π£ β funext π£ π€
               β {X : π€ Μ } β is-embedding (ΞΊ {π€} {X})
ΞΊ-is-embedding pe fe fe' = equivs-are-embeddings ΞΊ (ΞΊ-is-equiv pe fe fe')

\end{code}

Finally, Ξ· is an embedding because it is equal to the composition of
two embeddings:

\begin{code}

Ξ·-is-embedding : propext π£
               β funext π£ π£
               β funext π£ π€
               β funext π€ (π£ βΊ β π€)
               β {X : π€ Μ } β is-embedding (Ξ· {π€} {X})
Ξ·-is-embedding pe fe fe' fe'' {X} =
  back-transport
   is-embedding
   (Ξ·-composite fe fe'')
   (β-is-embedding (ΞΊ-is-embedding pe fe fe') (πβπ-is-embedding fe X))
\end{code}
