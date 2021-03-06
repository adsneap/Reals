Martin Escardo 29 April 2014.

A proposition-indexed product of pointed compact sets is itself
compact. But the assumption that a proposition-indexed product of
compact sets is compact gives weak excluded middle (negative
propositions are decidable).

The definition of compactness (or exhaustive searchability) is

    compactâ A = (p : A â ð) â Î£ aâ ê A , p aâ â¡ â â (a : A) â p a â¡ â

With excluded middle for propositions, the above claim is not
surprising, because

    (ð â Y) = Y^ð â ð (which is always compact),
    (ð â Y) = Y^ð â Y (which is compact if Y is),

and excluded middle for a proposition X amounts to X=ð or X=ð, so
that

    Y^X is compact if Y is compact and X is a proposition.

The point is that

    (1) We can reach this conclusion without excluded middle.

    (2) This also holds for dependent products:

        Î  x : X , Y x is compact if X is a proposition and Y x is
        compact for every x : X.

        (This product is also written (x : X) â Y x or Î  Y in Agda.)

Our Agda proof below can be written rather concisely by expanding the
definitions. We deliberately don't do that, so that we have a rigorous
informal proof side-by-side with the formal proof. We proceed in a
series of trivial steps, hopefully in the most natural way (although
we had a convoluted path to this supposedly natural way).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

open import UF-FunExt

module PropTychonoff (fe : FunExt) where

open import CompactTypes
open import Two-Properties
open import UF-Base
open import UF-Subsingletons
open import UF-PropIndexedPiSigma
open import UF-Equiv
open import UF-EquivalenceExamples

\end{code}

A crucial lemma is

    prop-indexed-product : is-prop X â (a : X) â Î  Y â Y a

This is proved in the module Prop-indexed-product. Although it has a
subtle proof, it should be intuitively clear, as X has at most one
element by hypothesis, and if the element is a:X then the product Î  Y
should be isomorphic to its only factor Y a.

With this observation, the following proof should be self-contained,
if we recall again the definition of compact set from the module
CompacTypes:

    compactâ A = (p : A â ð) â Î£ aâ ê A , p aâ â¡ â â (a : A) â p a â¡ â

Recall also that such an aâ is called a universal witness for the predicate p.

\begin{code}

prop-tychonoff : {X : ð¤ Ì } {Y : X â ð¥ Ì }
               â is-prop X
               â ((x : X) â compactâ (Y x))
               â compactâ (Î  Y)
prop-tychonoff {ð¤} {ð¥} {X} {Y} X-is-prop Îµ p = Î³
 where
  have : (type-of Îµ â¡ ((x : X) â compactâ(Y x)))
       Ã (type-of p â¡ (Î  Y â ð))
  have = refl , refl

  hip : (x : X) â Î  Y â Y x
  hip = prop-indexed-product (fe ð¤ ð¥) X-is-prop

\end{code}

The essence of the first part of the proof is this:

\begin{code}

  crude : X â compactâ (Î  Y)
  crude x = equiv-compactâ (â-sym(hip x)) (Îµ x)

\end{code}

But this is very crude for our purposes (or so it seems).  So we
instead proceed as follows.

The following is what we get from prop-indexed-product, abstractly:

\begin{code}

  f : (x : X) â Î  Y â Y x
  f x = prâ (hip x)

  hrf : (x : X) â Î£ r ê (Y x â Î  Y), r â f x â¼ id
  hrf x = prâ (prâ (hip x))

  h : (x : X) â Y x â Î  Y
  h x = prâ (hrf x)

  hf : (x : X) (Ï : Î  Y) â h x (f x Ï) â¡ Ï
  hf x = prâ (hrf x)

\end{code}

We define a predicate q x : Y x â ð, for each x : X, from the
predicate p : Î  Y â ð via (part of) the above isomorphism:

\begin{code}

  q : (x : X) â Y x â ð
  q x y = p (h x y)

\end{code}

We argue that the following is a universal witness for the
searchability of the type Î  Y wrt the predicate p:

\begin{code}

  Ïâ : Î  Y
  Ïâ x = prâ (Îµ x (q x))

\end{code}

By hypothesis, it satisfies:

\begin{code}

  Ïâ-spec : (x : X) â q x (Ïâ x) â¡ â â (y : Y x) â q x y â¡ â
  Ïâ-spec x = prâ (Îµ x (q x))

\end{code}

By expanding the definitions, this amounts to:

\begin{code}

  Ïâ-specâ : (x : X) â p (h x (Ïâ x)) â¡ â â (y : Y x) â p (h x y) â¡ â
  Ïâ-specâ = Ïâ-spec

\end{code}

By the definition of f in prop-indexed-product (namely f x Ï = Ï x):

\begin{code}

  Ïâ-specâ : (x : X) â p (h x (f x Ïâ)) â¡ â â (y : Y x) â p (h x y) â¡ â
  Ïâ-specâ = Ïâ-specâ

\end{code}

(So we can't abstract away the definition/proof of
prop-indexed-product.)

In particular, with y = f x Ï, we get:

\begin{code}

  Ïâ-specâ-particular-case : (x : X)
                           â p (h x (f x Ïâ)) â¡ â
                           â (Ï : Î  Y) â p (h x (f x Ï)) â¡ â
  Ïâ-specâ-particular-case x r Ï = Ïâ-specâ x r (f x Ï)

\end{code}

Using the fact that g x (f x Ï) = Ï for any x:X, we get:

\begin{code}

  Ïâ-is-universal-witness-assuming-X : X â p Ïâ â¡ â â (Ï : Î  Y) â p Ï â¡ â
  Ïâ-is-universal-witness-assuming-X x r Ï =
     p Ï             â¡â¨ ap p ((hf x Ï)â»Â¹) â©
     p (h x (f x Ï)) â¡â¨ Ïâ-specâ-particular-case x s Ï â©
     â               â
   where
    s = p (h x (f x Ïâ)) â¡â¨ ap p (hf x Ïâ) â©
        p Ïâ             â¡â¨ r â©
        â                â

\end{code}

Notice that the point x : X vanishes from the conclusion, and so we
are able to omit it from the hypothesis, which is crucial for what
follows.

We get the same conclusion if X is empty:

\begin{code}

  Ïâ-is-universal-witness-assuming-Xâð : (X â ð) â p Ïâ â¡ â â (Ï : Î  Y) â p Ï â¡ â
  Ïâ-is-universal-witness-assuming-Xâð u r Ï = p Ï  â¡â¨ ap p claim â©
                                               p Ïâ â¡â¨ r â©
                                               â    â

   where
    claim : Ï â¡ Ïâ
    claim = dfunext (fe ð¤ ð¥) (Î» x â unique-from-ð (u x))
\end{code}

So we would get what we want if we had excluded middle, because X is a
proposition and the above shows that both X and X â ð give the desired
conclusion that Ïâ is a universal witness. But excluded middle is not
needed.

We shuffle the arguments of Ïâ-is-universal-witness-assuming-X:

\begin{code}
  claimâ : p Ïâ â¡ â â (Ï : Î  Y) â X â p Ï â¡ â
  claimâ r Ï x = Ïâ-is-universal-witness-assuming-X x r Ï

\end{code}

We then take the contrapositive of the conclusion X â p Ï â¡ â, and
use the fact that if a point of the two-point type ð is â, then it is
not â:

\begin{code}

  Claimâ : p Ïâ â¡ â â (Ï : Î  Y) â p Ï â¡ â â (X â ð)
  Claimâ r Ï = contrapositive(claimâ r Ï) â equal-â-different-from-â

\end{code}

This concludes the first part of the argument.

We now shuffle the arguments of Ïâ-is-universal-witness-assuming-Xâð:

\begin{code}

  Claimâ : p Ïâ â¡ â â (Ï : Î  Y) â (X â ð) â p Ï â¡ â
  Claimâ r Ï u = Ïâ-is-universal-witness-assuming-Xâð u r Ï

\end{code}

Combining the two last claims, we get:

\begin{code}

  Claimâ : p Ïâ â¡ â â (Ï : Î  Y) â p Ï â¡ â â p Ï â¡ â
  Claimâ r Ï = Claimâ r Ï â Claimâ r Ï

\end{code}

Finally, we do case analysis on the value of p Ï:

\begin{code}

  Ïâ-is-universal-witness : p Ïâ â¡ â â (Ï : Î  Y) â p Ï â¡ â
  Ïâ-is-universal-witness r Ï = ð-equality-cases (Claimâ r Ï) id

  Î³ : Î£ Ïâ ê Î  Y , (p Ïâ â¡ â â (Ï : Î  Y) â p Ï â¡ â)
  Î³ = Ïâ , Ïâ-is-universal-witness

\end{code}

And we are done.

TODO. 9 Sep 2015. We can generalize from X being a subsingleton (or
proposition) to X being subfinite (embedded into a finite type).

A particular case is the following:

\begin{code}

prop-tychonoff-corollary : {X : ð¤ Ì } {Y : ð¥ Ì }
                         â is-prop X
                         â compactâ Y
                         â compactâ (X â Y)
prop-tychonoff-corollary X-is-prop Îµ = prop-tychonoff X-is-prop (Î» x â Îµ)

\end{code}

This holds even for undecided X (such as X = LPO), or when we have no
idea whether X or (X â ð), and hence whether (X â Y) is ð or Y (or
none, if this is undecided)!

Better (9 Sep 2015):

\begin{code}

prop-tychonoff-corollary' : {X : ð¤ Ì } {Y : ð¥ Ì }
                          â is-prop X
                          â (X â compactâ Y)
                          â compactâ (X â Y)
prop-tychonoff-corollary' = prop-tychonoff

\end{code}

So the function type (LPO â â) is compact! (See the module LPO for a
proof.)

The Tychonoff theorem for prop-indexed products of compact types
doesn't hold. To see this, first notice that a proposition is
compact iff it is decidable. Now, the empty type ð is compact
(but not compactââ), and if ð^P, that is, Â¬P, where compact for a
proposition P, this would imply that Â¬P is decidable for every
proposition P, which is weak excluded middle, which is not provable.

\begin{code}

open import UF-ExcludedMiddle

compact-prop-tychonoff-gives-WEM : ((X : ð¤ Ì ) (Y : X â ð¥ Ì )
                                       â is-prop X
                                       â ((x : X) â compact (Y x))
                                       â compact (Î  Y))
                                 â WEM ð¤
compact-prop-tychonoff-gives-WEM {ð¤} {ð¥} Ï X X-is-prop = Î´ Î³
 where
  Y : X â ð¥ Ì
  Y x = ð

  negation-compact : compact (X â ð {ð¥})
  negation-compact = Ï X Y X-is-prop (Î» p â ð-compact)

  Î³ : decidable (X â ð {ð¥})
  Î³ = compact-decidable (X â ð) negation-compact

  Î´ : decidable (X â ð {ð¥}) â decidable (Â¬ X)
  Î´ (inl f) = inl (ð-elim â f)
  Î´ (inr Ï) = inr (contrapositive (Î» f â ð-elim â f) Ï)

\end{code}
