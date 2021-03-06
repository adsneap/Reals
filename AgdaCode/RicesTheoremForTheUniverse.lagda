

  R i c e ' s   T h e o r e m   f o r   t h e

  M a r t i n - L o f   u n i v e r s e


    Martin Escardo, University of Birmingham, UK.
    February 2012, update 06 April 2012.

    This is a proof in intensional Martin-Lof type theory,
    extended with the propositional axiom of extensionality as a
    postulate, written in Agda notation. The K-rule or UIP axiom
    are not used, except in instances where they can be
    proved. The proof type-checks in Agda 2.3.2

    An addendum included 21 August 2014.

A b s t r a c t. We show that a Martin-Lof universe `a la Russell
satisfies the conclusion of Rice's Theorem: it has no non-trivial,
decidable, extensional properties. We derive this as a corollary
of more general topological facts in type theory, which don't rely
on Brouwerian continuity axioms.


I n t r o d u c t i o n

We don't manipulate syntax or Turing machines to prove this
claim. We show, within type theory, that the hypothetical
existence of a non-trivial, decidable extensional property of the
universe leads to a construction that is known to be impossible,
namely WLPO, defined and discussed below.

Hence this version of Rice's Theorem for the universe remains true
when type theory is extended with any kind of postulated axiom
(e.g. univalence, Church's thesis, Brouwerian continuity axioms,
Markov principle, to name a few of the contentious axioms that one
may wish to consider in constructive mathematics). One possible
reaction to our result is that this is to be expected: after all,
there are no elimination rules for the universe. But our arguments
show that, even if there were, Rice's Theorem for the universe
would still hold, which justifies the lack of elimination rules.

Of course, if we postulate classical logic, for example in its
extreme version given by the principle of excluded middle, then
there are decidable properties of the universe. Our theorem is
compatible with that. In fact, what our construction does is to
produce a classical conclusion from the hypothetical premise.

Our assumption of the axiom of extensionality may seem dubious. In
any case, we do get a meta-theorem that does not rely on
extensionality: For all closed terms p: U ??? ???? with p extensional
and X,Y: U, there is no closed term of type p (X) ??? ??? ??? P (Y) ??? ???,
where U is the universe of types and where ???? is a type with two
distinct elements ??? and ???, and with decidable equality.

We derive this claim as a corollary or more general topological
constructions developed in the module TheTopologyOfTheUniverse,
which is the interesting and non-trivial technical aspect of this
work. We emphasize that we don't postulate any continuity axiom in
that module (or in fact any axiom other than extensionality).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module RicesTheoremForTheUniverse (fe : FunExt) where

open import SpartanMLTT

open import UF-Equiv
open import UF-EquivalenceExamples
open import TheTopologyOfTheUniverse fe
open import GenericConvergentSequence
open import WLPO
open import BasicDiscontinuityTaboo fe
open import CanonicalMapNotation

\end{code}

Our promised corollary of the universe indiscreteness theorem is that
the hypothetical existence of an extensional P : U ??? ???? with two
different values is a taboo.

\begin{code}

extensional : (???? ?? ??? ????) ??? ???? ??? ??
extensional P = ??? X Y ??? X ??? Y ??? P X ??? P Y

Rice's-Theorem-for-U :

    (P : ???? ?? ??? ????) ??? extensional P ??? (X Y : ???? ?? ) ??? P X ??? ??? ??? P Y ??? ??? ??? WLPO

Rice's-Theorem-for-U {????} P e X Y r s = basic-discontinuity-taboo p (p-lemma , p-lemma???)
 where
  Q : ?????? ??? ???? ??
  Q = pr??? (Universe-Indiscreteness-Theorem (?? i ??? X) Y)

  Q-lemma : (i : ???) ??? Q (?? i) ??? X
  Q-lemma = pr??? (pr??? (Universe-Indiscreteness-Theorem (?? i ??? X) Y))

  Q-lemma??? : Q ??? ??? Y
  Q-lemma??? = pr??? (pr??? (Universe-Indiscreteness-Theorem (?? i ??? X) Y))

  p : ?????? ??? ????
  p u = P (Q u)

  p-lemma : (i : ???) ??? p (?? i) ??? ???
  p-lemma i = e (Q (?? i)) X (Q-lemma i) ??? r

  p-lemma??? : p ??? ??? ???
  p-lemma??? = e (Q ???) Y Q-lemma??? ??? s

\end{code}

Notice that although the proof uses topological techniques, the
formulation of the theorem doesn't mention topology.

One can get more milleage exploiting the fact that ?????? is compact, in
the sense that it satisfies Bishop's principle of omniscience, as
proved in the module GenericConvergentSequence. As a simple example,
one can conclude LPO rather than WLPO.

The type-inhabitedness predicate is clearly extensional. By the
above theorem, this means that there is no algorithm within type
theory that decides whether any given type is inhabited, that is,
whether a proposition has a proof. Of course we already know this
since the time of Godel, Turing and Church, in stronger forms
(such as adding general recursion to type theory). But we
emphasize again that our development is syntax-free (or
Godel-number free), and hence make senses in any model of type
theory.

We have the following meta-theorem as a corollary, *without*
assuming the propositional axiom of extensionality:

  For all closed terms P: ???? ?? ??? ???? and X,Y: ???? ?? with a given proof of
  extensionality of P, there is no closed term of type P(X) ??? P(Y).

Proof. Assuming the axiom of extensionality, there can't be such
closed terms, as there is a realizability interpretation, e.g.
Hyland's effective topos, where WLPO solves the Halting
Problem. Without postulating the axiom, fewer terms are definable
in the language, and hence the omission of extensionality gives
the same result. Q.E.D.


Added 21 August 2014:

WLPO amounts to saying that we can solve the halting problem. If we
cannot, then all ????-valued functions on ???? ?? must be constant:

\begin{code}

Rice's-contrapositive : ??? {????}

 ??? ?? WLPO ??? (P : ???? ?? ??? ????) ??? extensional P ??? (X Y : ???? ?? ) ??? P X ??? P Y

Rice's-contrapositive {????} nwlpo P e = f
 where
  a : (X Y : ???? ?? ) ??? P X ??? ??? ??? P Y ??? ??? ??? WLPO
  a X Y = Rice's-Theorem-for-U P e X Y

  b : (X Y : ???? ?? ) (m n : ????) ??? P X ??? m ??? P Y ??? n ??? m ??? n
  b X Y ??? ??? p q = refl
  b X Y ??? ??? p q = ????-elim (nwlpo (a X Y p q))
  b X Y ??? ??? p q = ????-elim (nwlpo (a Y X q p))
  b X Y ??? ??? p q = refl

  f : (X Y : ???? ?? ) ??? P X ??? P Y
  f X Y = b X Y (P X) (P Y) refl refl

\end{code}
