Martin Escardo, 20th June 2019 and 28th May 2021.

Search over uniformly continuous decidable predicates on the Cantor type.

This is loosely based on my LICS'2007 paper "Infinite sets that admit
fast exhaustive search" and my LMCS'2008 paper "Exhaustible sets in
higher-type computation".

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import Two-Properties
open import DiscreteAndSeparated
open import NaturalsOrder
open import OrderNotation

open import UF-FunExt
open import UF-Base

module CantorSearch (fe : funext π€β π€β) where

\end{code}

We first consider search over the type π of binary digits β and β.

To check that for all n : π we have p n β‘ β, it is enough to check
that p (p β) β‘ β.

\begin{code}

private
 motivating-fact : (p : π β π) β  p (p β) β‘ β β (n : π) β p n β‘ β
 motivating-fact p r = f (p β) refl r
  where
   f : (nβ : π) β p β β‘ nβ β p nβ β‘ β β (n : π) β p n β‘ β
   f β s r β = r
   f β s r β = π-elim (zero-is-not-one (s β»ΒΉ β r))
   f β s r β = s
   f β s r β = r

Ξ΅π : (π β π) β π
Ξ΅π p = p β

Aπ : (π β π) β π
Aπ p = p (Ξ΅π p)

\end{code}

The function Aπ is the characteristic function of universal
quantification:

\begin{code}

Aπ-propertyβ : (p : π β π) β Aπ p β‘ β β (n : π) β p n β‘ β
Aπ-propertyβ = motivating-fact

Aπ-propertyβ : (p : π β π) β ((n : π) β p n β‘ β) β Aπ p β‘ β
Aπ-propertyβ p Ο = Ο (Ξ΅π p)

π-searchable : (p : π β π) β Ξ£ nβ κ π , (p nβ β‘ β β (n : π) β p n β‘ β)
π-searchable p = Ξ΅π p , Aπ-propertyβ p

\end{code}

The function p has a root (that is, there is n with p n β‘ β) if and
only if Ξ΅π p is a root. This follows from Aπ-propertyβ. So Ξ΅π chooses
a root if there is some root, and otherwise chooses garbage. But we
can check whether there is a root by checking whether or not
p (Ξ΅π p) β‘ β. This is what Aπ does.

\begin{code}

Ξ΅π-propertyβ : (p : π β π) β (Ξ£ n κ π , p n β‘ β) β p (Ξ΅π p) β‘ β
Ξ΅π-propertyβ p = IV
 where
  I : (Ξ£ n κ π , p n β‘ β) β Β¬ ((n : π) β p n β‘ β)
  I (n , e) Ο = equal-β-different-from-β e (Ο n)

  II : Β¬ ((n : π) β p n β‘ β) β Β¬ (Aπ p β‘ β)
  II = contrapositive (Aπ-propertyβ p)

  III : Β¬ (Aπ p β‘ β) β p (Ξ΅π p) β‘ β
  III = different-from-β-equal-β

  IV : (Ξ£ n κ π , p n β‘ β) β p (Ξ΅π p) β‘ β
  IV = III β II β I

Ξ΅π-propertyβ : (p : π β π) β p (Ξ΅π p) β‘ β β (Ξ£ n κ π , p n β‘ β)
Ξ΅π-propertyβ p e = Ξ΅π p , e

\end{code}

We use this to search over the Cantor type. We first need some
preliminary definitions and facts.

\begin{code}

Cantor = β β π

head : Cantor β π
head Ξ± = Ξ± 0

tail : Cantor β Cantor
tail Ξ± = Ξ± β succ

cons : π β Cantor β Cantor
cons n Ξ± 0        = n
cons n Ξ± (succ i) = Ξ± i

head-cons : (n : π) (Ξ± : Cantor) β head (cons n Ξ±) β‘ n
head-cons n Ξ± = refl

tail-cons : (n : π) (Ξ± : Cantor) β tail (cons n Ξ±) β‘ Ξ±
tail-cons n Ξ± = refl

cons-head-tail : (Ξ± : Cantor) β cons (head Ξ±) (tail Ξ±) β‘ Ξ±
cons-head-tail Ξ± = dfunext fe h
 where
  h : cons (head Ξ±) (tail Ξ±) βΌ Ξ±
  h zero     = refl
  h (succ i) = refl

\end{code}

Uniform continuity as defined below is data rather than property. This
is because any number bigger than a modulus of uniform continuity is
also a modulus.

We first define when two binary sequences Ξ± and Ξ² agree at the first n
positions, written Ξ± β‘β¦ n β§ Ξ².

\begin{code}

_β‘β¦_β§_ : Cantor β β β Cantor β π€β Μ
Ξ± β‘β¦ 0      β§ Ξ² = π
Ξ± β‘β¦ succ n β§ Ξ² = (head Ξ± β‘ head Ξ²) Γ (tail Ξ± β‘β¦ n β§ tail Ξ²)

\end{code}

We have that (Ξ± β‘β¦ n β§ Ξ²) iff Ξ± k β‘ Ξ² k for all k < n:

\begin{code}

agreementβ : (Ξ± Ξ² : Cantor)
             (n : β)
           β (Ξ± β‘β¦ n β§ Ξ²)
           β ((k : β) β k < n β Ξ± k β‘ Ξ² k)
agreementβ Ξ± Ξ² 0        *       k        l = π-elim l
agreementβ Ξ± Ξ² (succ n) (p , e) 0        l = p
agreementβ Ξ± Ξ² (succ n) (p , e) (succ k) l = IH k l
 where
  IH : (k : β) β k < n β Ξ± (succ k) β‘ Ξ² (succ k)
  IH = agreementβ (tail Ξ±) (tail Ξ²) n e

agreementβ : (Ξ± Ξ² : Cantor)
             (n : β)
           β ((k : β) β k < n β Ξ± k β‘ Ξ² k)
           β (Ξ± β‘β¦ n β§ Ξ²)
agreementβ Ξ± Ξ² 0        Ο = β
agreementβ Ξ± Ξ² (succ n) Ο = Ο 0 β , agreementβ (tail Ξ±) (tail Ξ²) n (Ξ» k β Ο (succ k))

\end{code}

A function is Cantor β π is uniformly continuous if it has a modulus
of continuity:

\begin{code}

_is-a-modulus-of-uniform-continuity-of_ : β β (Cantor β π) β π€β Μ
n is-a-modulus-of-uniform-continuity-of p = (Ξ± Ξ² : Cantor) β Ξ± β‘β¦ n β§ Ξ² β p Ξ± β‘ p Ξ²

uniformly-continuous : (Cantor β π) β π€β Μ
uniformly-continuous p = Ξ£ n κ β , n is-a-modulus-of-uniform-continuity-of p

\end{code}

TODO. Show that

 (Ξ£ p κ (Cantor  β π) , uniformly-continuous p) β (Ξ£ n κ β , Fin n β π)

If we define uniform continuity with β rather than Ξ£, this is no longer the case.

Notice that a function has modulus of continuity zero if and only it
is constant.

\begin{code}

modulus-zero-iff-constant  : (p : Cantor β π)
                           β 0 is-a-modulus-of-uniform-continuity-of p
                           β ((Ξ± Ξ² : Cantor) β p Ξ± β‘ p Ξ²)
modulus-zero-iff-constant p = I , II
 where
  I :  0 is-a-modulus-of-uniform-continuity-of p β ((Ξ± Ξ² : Cantor) β p Ξ± β‘ p Ξ²)
  I u Ξ± Ξ² = u Ξ± Ξ² β

  II :  ((Ξ± Ξ² : Cantor) β p Ξ± β‘ p Ξ²) β 0 is-a-modulus-of-uniform-continuity-of p
  II ΞΊ Ξ± Ξ² β = ΞΊ Ξ± Ξ²

\end{code}

The crucial lemma for Cantor search is this:

\begin{code}

cons-decreases-modulus : (p : Cantor β π)
                         (n : β)
                         (b : π)
                       β (succ n) is-a-modulus-of-uniform-continuity-of p
                       β n is-a-modulus-of-uniform-continuity-of (p β cons b)
cons-decreases-modulus p n b u Ξ± Ξ² = III
 where
  I : Ξ± β‘β¦ n β§ Ξ² β cons b Ξ± β‘β¦ succ n β§ cons b Ξ²
  I e = refl , e

  II : cons b Ξ± β‘β¦ succ n β§ cons b Ξ² β p (cons b Ξ±) β‘ p (cons b Ξ²)
  II = u (cons b Ξ±) (cons b Ξ²)

  III : Ξ± β‘β¦ n β§ Ξ² β p (cons b Ξ±) β‘ p (cons b Ξ²)
  III = II β I

\end{code}

We now define search over the Cantor space. The functions A and Ξ΅ are
mutually recursively defined. But of course we can consider only Ξ΅
expanding the definition of A in that of Ξ΅, because the definition of
A doesn't use induction.

The following point cβ of the Cantor type is arbitrary, and what we do
works with any choice of cβ. So we make it abstract.

\begin{code}

abstract
 cβ : Cantor
 cβ = Ξ» i β β

A  : β β (Cantor β π) β π
Ξ΅  : β β (Cantor β π) β Cantor

A n p = p (Ξ΅ n p)

Ξ΅ 0 p        = cβ
Ξ΅ (succ n) p = case Ξ΅π (Ξ» b β A n (p β cons b)) of
                (Ξ» (bβ : π) β cons bβ (Ξ΅ n (p β cons bβ)))
\end{code}

The function A is designed to satisfy the specification

  A n p β‘ β β ((Ξ± : Cantor) β p Ξ± β‘ β)

for any decidable predicate p with modulus of uniform continuity n.

So A is the characteristic function of universal quantification over
uniformly continuous decidable predicates.

One direction is trivial and doesn't require uniform continuity, but
we still need to supply a number:

\begin{code}

A-propertyβ : (p : Cantor β π)
              (n : β)
            β ((Ξ± : Cantor) β p Ξ± β‘ β)
            β A n p β‘ β
A-propertyβ p n Ο = Ο (Ξ΅ n p)

\end{code}

The other direction is proved by induction on β.

\begin{code}

A-propertyβ : (p : Cantor β π)
              (n : β)
            β n is-a-modulus-of-uniform-continuity-of p
            β A n p β‘ β
            β (Ξ± : Cantor) β p Ξ± β‘ β
A-propertyβ p 0        u r Ξ± = p Ξ±  β‘β¨ u Ξ± cβ β β©
                               p cβ β‘β¨ r β©
                               β    β
A-propertyβ p (succ n) u r Ξ± = IV
 where
  IH : (b : π) β A n (p β cons b) β‘ β β (Ξ² : Cantor) β p (cons b Ξ²) β‘ β
  IH b = A-propertyβ (p β cons b) n (cons-decreases-modulus p n b u)

  bβ : π
  bβ = Ξ΅π (Ξ» b β A n (p β cons b))

  I : A n (p β cons bβ) β‘ β β (b : π) β A n (p β cons b) β‘ β
  I = Aπ-propertyβ (Ξ» b β A n (p β cons b))

  observationβ : A (succ n) p β‘ β
  observationβ = r

  observationβ : A (succ n) p β‘ A n (p β cons bβ)
  observationβ = refl

  II : (b : π) (Ξ² : Cantor) β p (cons b Ξ²) β‘ β
  II b = IH b (I r b)

  III : p (cons (head Ξ±) (tail Ξ±)) β‘ β
  III = II (head Ξ±) (tail Ξ±)

  IV : p Ξ± β‘ β
  IV = transport (Ξ» - β p - β‘ β) (cons-head-tail Ξ±) III

\end{code}

The desired construction is the following:

\begin{code}

Cantor-uniformly-searchable : (p : Cantor β π)
                            β uniformly-continuous p
                            β Ξ£ Ξ±β κ Cantor , (p Ξ±β β‘ β β (Ξ± : Cantor) β p Ξ± β‘ β)
Cantor-uniformly-searchable p (n , u) = Ξ΅ n p , A-propertyβ p n u

Ξ : (p : Cantor β π)
  β uniformly-continuous p
  β decidable (Ξ£ Ξ± κ Cantor , p Ξ± β‘ β)
Ξ p (n , u) = Ξ³ (p Ξ±) refl
 where
  Ξ± : Cantor
  Ξ± = Ξ΅ n p

  Ξ³ : (k : π) β p Ξ± β‘ k β decidable (Ξ£ Ξ± κ Cantor , p Ξ± β‘ β)
  Ξ³ β r = inl (Ξ±  , r)
  Ξ³ β r = inr (Ξ» (Ξ² , s) β zero-is-not-one (s β»ΒΉ β A-propertyβ p n u r Ξ²))

Ξ' : (p : Cantor β π)
   β uniformly-continuous p
   β decidable ((Ξ± : Cantor) β p Ξ± β‘ β)
Ξ' p u = Ξ³ (Ξ p u)
 where
  Ξ³ : decidable (Ξ£ Ξ± κ Cantor , p Ξ± β‘ β) β decidable ((Ξ± : Cantor) β p Ξ± β‘ β)
  Ξ³ (inl (Ξ± , r)) = inr (Ξ» Ο β zero-is-not-one (r β»ΒΉ β Ο Ξ±))
  Ξ³ (inr Ξ½)       = inl (Ξ» Ξ± β different-from-β-equal-β (Ξ» r β Ξ½ (Ξ± , r)))

\end{code}

Examples that show that A can be fast (in this case linear time) even
if the supplied modulus of uniform continuity is large:

\begin{code}

module examples where

 prc : β β Cantor β π
 prc n Ξ± = Ξ± n

 sprc-lemma : (n : β) β (succ n) is-a-modulus-of-uniform-continuity-of (prc n)
 sprc-lemma 0        Ξ± Ξ² (r , _) = r
 sprc-lemma (succ n) Ξ± Ξ² (_ , s) = sprc-lemma n (tail Ξ±) (tail Ξ²) s

 sprc : (n : β) β uniformly-continuous (prc n)
 sprc n = succ n , sprc-lemma n

 prc-example : β β π
 prc-example n = A (succ n) (prc n)
{-
 large-prc-example : prc-example 10000 β‘ β
 large-prc-example = refl
-}
\end{code}

In the worst case, however, A n p runs in time 2βΏ.

\begin{code}

 xor : β β Cantor β π
 xor 0        Ξ± = β
 xor (succ n) Ξ± = head Ξ± β xor n (tail Ξ±)

 xor-uc : (n : β) β n is-a-modulus-of-uniform-continuity-of (xor n)
 xor-uc 0        Ξ± Ξ² β       = refl
 xor-uc (succ n) Ξ± Ξ² (p , q) = Ξ³
  where
   IH : xor n (tail Ξ±) β‘ xor n (tail Ξ²)
   IH = xor-uc n (tail Ξ±) (tail Ξ²) q

   Ξ³ : head Ξ± β xor n (tail Ξ±) β‘ head Ξ² β xor n (tail Ξ²)
   Ξ³ = apβ _β_ p IH

 xor-example : β β π
 xor-example n = A n (xor n)
{-
 large-xor-example : xor-example 17 β‘ β
 large-xor-example = refl
-}
\end{code}

The xor example works with n=17 in about 25s in a core-i7 machine.
The time 2^n for this example.

Another fast example (linear):

\begin{code}

 ΞΊβ : β β Cantor β π
 ΞΊβ n Ξ± = complement (Ξ± n β Ξ± n)

 sΞΊβ-lemma : (n : β) β (succ n) is-a-modulus-of-uniform-continuity-of (ΞΊβ n)
 sΞΊβ-lemma 0        Ξ± Ξ² (r , _) = ap (Ξ» - β complement (- β -)) r
 sΞΊβ-lemma (succ n) Ξ± Ξ² (_ , s) = sΞΊβ-lemma n (tail Ξ±) (tail Ξ²) s

 sΞΊβ : (n : β) β uniformly-continuous (ΞΊβ n)
 sΞΊβ n = succ n , sΞΊβ-lemma n

 ΞΊβ-example : β β π
 ΞΊβ-example n = A (succ n) (ΞΊβ n)
{-
 large-ΞΊβ-example : ΞΊβ-example 100000 β‘ β
 large-ΞΊβ-example = refl
-}
\end{code}
