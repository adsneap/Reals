Martin Escardo, August 2018. A structure identity principle.

There is a much better treatment of this here and so this file is
obsolete:

https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/

This is also ported in the module UF-SIP.

A structure identity principle (sip) for types, rather than categories
as in the HoTT Book.

This tries to make previous work by Coquand and Danielsson [1] more
general.

[1] https://www.sciencedirect.com/science/article/pii/S0019357713000694 , 2013

Contents:

 * The submodule gsip has a very abstract version of sip.

 * This is followed by various submodules that consider more concrete
   examples such as â-magmas and much more.

 * The submodule gsip-with-axioms considers structures subject to
   axioms, to easily account for mathematical structures such as
   monoids, groups, spaces, etc. This module performs a reduction to
   the module gsip.

 * This is followed by monoids as an example.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base
open import UF-Equiv
open import UF-Univalence
open import UF-Yoneda
open import UF-EquivalenceExamples

module UF-StructureIdentityPrinciple where

\end{code}

We consider the type Î£ S of types X : ð¤ Ì equipped with structure s : S X,
where the universe U is univalent and S : ð¤ Ì â ð¥ Ì is a parameter.

The underlying set and structure are given by the first and second
projections:

\begin{code}

â¨_â© : {ð¤ ð¥ : Universe} {S : ð¤ Ì â ð¥ Ì } â Î£ S â ð¤ Ì
â¨_â© = prâ

structure : {ð¤ ð¥ : Universe} {S : ð¤ Ì â ð¥ Ì } (A : Î£ S) â S â¨ A â©
structure = prâ

\end{code}

 If S comes with suitable data, including S-equiv discussed
 below, we can characterize identity of elements of Î£ S as equivalence
 of underlying sets subject to a suitable condition involving the
 data:

   (A â¡ B) â Î£ f ê â¨ A â© â â¨ B â© , Î£ e ê is-equiv f , S-equiv A B (f , e)

 It is important that such a condition is not necessarily property but
 actually data in general.

 Thus

  (1) For an equivalence f : â¨ A â© â â¨ B â© we want data that
      establishes that it is an equivalence in the sense of
      S-structure, in some abstract sense, specified by S-equiv.

 One possible list of data for S and S-equiv is the following:

  (2) We want data showing that the identity equivalence â-refl â¨ A â©
      is an S-equivalence, given by S-refl.

  (3) Moreover, when f : â¨ X , s â© â â¨ X , t â© is the identity
      function, we want the data for (1) to give data for the identity
      s â¡ t of structures. This is specified by the function
      S-id-structure.

  (4) We need a technical transport condition (which is not
      surprising, as identity in Î£-types is given by transport of the
      second component), specified by the function S-transport below,
      relating the data specified by the functions S-id-structure and
      S-refl.

 These assumptions (1)-(4) are given as module parameters for gsip:

\begin{code}

module gsip

  (ð¤ ð¥ : Universe)

  (ua : is-univalent ð¤)

  (S : ð¤ Ì â ð¥ Ì )

  (S-equiv : (A B : Î£ S) â â¨ A â© â â¨ B â© â ð¤ â ð¥ Ì )

  (S-refl : (A : Î£ S) â S-equiv A A (â-refl â¨ A â©))

  (S-id-structure : (X : ð¤ Ì ) (s t : S X)
                  â S-equiv (X , s) (X , t) (â-refl X) â s â¡ t)

  (S-transport : (A : Î£ S)
                 (s : S â¨ A â©)
                 (Ï : S-equiv A (â¨ A â© , s) (â-refl â¨ A â©))
               â transport
                    (Î» - â S-equiv A (â¨ A â© , -) (â-refl â¨ A â©))
                    (S-id-structure â¨ A â© (structure A) s Ï)
                    (S-refl A)
               â¡ Ï)
  where

\end{code}

  Under these assumptions, we show that identity in Î£ S is equivalent
  to _ââ_ defined as follows:

\begin{code}

  _ââ_ : Î£ S â Î£ S â ð¤ â ð¥ Ì
  A ââ B = Î£ f ê (â¨ A â© â â¨ B â©) , Î£ e ê is-equiv f , S-equiv A B (f , e)

\end{code}

  This defines a Î£ S - equivalence to be an equivalence of underlying
  sets that is an S-structure equivalence in the sense abstractly
  specified by the function S-equiv. Then the assumption S-refl
  allows us to have an equivalence of any element of Î£ S with itself:

\begin{code}

  ââ-refl : (A : Î£ S) â A ââ A
  ââ-refl A = prâ(â-refl â¨ A â©) , prâ(â-refl â¨ A â©) , S-refl A

\end{code}

  And hence an identity gives a Î£ S - equivalence by induction in the
  usual way:

\begin{code}

  idtoeqâ : (A B : Î£ S) â A â¡ B â A ââ B
  idtoeqâ A .A refl = ââ-refl A

\end{code}

  We use the following auxiliary constructions to define an inverse of
  idtoeqâ by equivalence induction (the function JEq):

\begin{code}

  private
    Î¨ : (A : Î£ S) (Y : ð¤ Ì ) â â¨ A â© â Y â ð¤ âº â ð¥ Ì
    Î¨ A Y e = (s : S Y) â S-equiv A (Y , s) e â A â¡ (Y , s)
    Ï : (A : Î£ S) â Î¨ A â¨ A â© (â-refl â¨ A â©)
    Ï A s Ï = to-Î£-â¡' (S-id-structure â¨ A â© (structure A) s Ï)

  eqtoidâ : (A B : Î£ S) â A ââ B â A â¡ B
  eqtoidâ A B (f , e , Ï) = JEq ua â¨ A â© (Î¨ A) (Ï A) â¨ B â© (f , e) (structure B) Ï

\end{code}

  So far we have used the hypotheses

     * S-equiv (to define _â¡â_),
     * S-refl (to define idtoeqâ), and
     * S-id-structure (to define eqtoidâ).

  Next we use the remaining hypothesis S-transport to show that
  eqtoidâ is a section of idtoeqâ:

\begin{code}

  idtoeq-eqtoidâ : (A B : Î£ S) (Îµ : A ââ B) â idtoeqâ A B (eqtoidâ A B Îµ) â¡ Îµ
  idtoeq-eqtoidâ A B (f , e , Ï) = JEq ua â¨ A â© Î¦ Ï â¨ B â© (f , e) (structure B) Ï
   where
    Î¦ : (Y : ð¤ Ì ) â â¨ A â© â Y â ð¤ â ð¥ Ì
    Î¦ Y (f , e) = (s : S Y)
                  (Ï : S-equiv A (Y , s) (f , e))
                 â idtoeqâ A (Y , s) (eqtoidâ A (Y , s) (f , e , Ï)) â¡ f , e , Ï
    Ï : Î¦ â¨ A â© (â-refl â¨ A â©)
    Ï s Ï =
      idtoeqâ A A' (eqtoidâ A A' refl')
            â¡â¨ ap (Î» h â idtoeqâ A A' (h s Ï)) (JEq-comp ua â¨ A â© (Î¨ A) (Ï A)) â©
      idtoeqâ A A' (to-Î£-â¡' p)
            â¡â¨ h p â©
      prâ(â-refl â¨ A â©) , prâ(â-refl â¨ A â©) , g p
            â¡â¨ to-Î£-â¡' (to-Î£-â¡' (S-transport A s Ï)) â©
      refl' â
     where
      A' : Î£ S
      A' = â¨ A â© , s
      refl' : A ââ A'
      refl' = prâ(â-refl â¨ A â©) , prâ(â-refl â¨ A â©) , Ï
      g : structure A â¡ s â S-equiv A A' (â-refl â¨ A â©)
      g p = transport (Î» - â S-equiv A (â¨ A â© , -) (â-refl â¨ A â©)) p (S-refl A)
      h : (p : structure A â¡ s) â idtoeqâ A A' (to-Î£-â¡' p)
                                â¡ prâ(â-refl â¨ A â©) , prâ(â-refl â¨ A â©) , g p
      h refl = refl
      p : structure A â¡ s
      p = S-id-structure â¨ A â© (structure A) s Ï

\end{code}

  Being a natural section of idtoeqâ, the function eqtoidâ is also a
  retraction, by a general property of the identity type (namely the
  one called nat-retraction-is-equiv in our development (in the module
  UF-Yoneda)):

\begin{code}

  uaâ : (A B : Î£ S) â is-equiv (idtoeqâ A B)
  uaâ A = nats-with-sections-are-equivs A
            (idtoeqâ A)
            (Î» B â eqtoidâ A B , idtoeq-eqtoidâ A B)

  eqtoid-idtoeqâ : (A B : Î£ S) (p : A â¡ B) â eqtoidâ A B (idtoeqâ A B p) â¡ p
  eqtoid-idtoeqâ A B = prâ(prâ (equivs-are-qinvs (idtoeqâ A B) (uaâ A B)))

  â¡-is-ââ : (A B : Î£ S) â (A â¡ B) â (A ââ B)
  â¡-is-ââ A B = idtoeqâ A B , uaâ A B

  _ââ'_ : Î£ S â Î£ S â ð¤ â ð¥ Ì
  A ââ' B = Î£ p ê â¨ A â© â â¨ B â© , S-equiv A B (prâ p , prâ p)

  ââ-is-ââ' : (A B : Î£ S) â (A ââ B) â (A ââ' B)
  ââ-is-ââ' A B = â-sym Î£-assoc

  â¡-is-ââ' : (A B : Î£ S) â (A â¡ B) â (A ââ' B)
  â¡-is-ââ' A B = (â¡-is-ââ A B) â (ââ-is-ââ' A B)

\end{code}

  This completes the proof of the abstract SIP considered here.


We now consider some concrete examples to illustrate how this works in
practice.

An â-magma is a type, not assumed to be a set, equipped with a binary
operation. The above gives a characterization of identity of â-magmas:

\begin{code}

module â-magma (ð¤ : Universe) (ua : is-univalent ð¤) where

 S : ð¤ Ì â ð¤ Ì
 S X = X â X â X

 S-equiv : (A B : Î£ S) â â¨ A â© â â¨ B â© â ð¤ Ì
 S-equiv A B (f , e) = (Î» x x' â f (structure A x x')) â¡ (Î» x x' â structure B (f x) (f x'))

 S-refl : (A : Î£ S) â S-equiv A A (â-refl â¨ A â©)
 S-refl A = refl

 S-id-structure : (X : ð¤ Ì ) (s t : S X) â S-equiv (X , s) (X , t) (â-refl X) â s â¡ t
 S-id-structure X m n = id

 S-transport : (A : Î£ S)
                 (s : S â¨ A â©)
                 (Ï : S-equiv A (â¨ A â© , s) (â-refl â¨ A â©))
               â transport
                    (Î» - â S-equiv A (â¨ A â© , -) (â-refl â¨ A â©))
                    (S-id-structure â¨ A â© (structure A) s Ï)
                    (S-refl A)
               â¡ Ï
 S-transport A m Ï = refl-left-neutral

 open gsip ð¤ ð¤ ua S S-equiv S-refl S-id-structure S-transport

 â-Magma : ð¤ âº Ì
 â-Magma = Î£ S

 fact : (A B : â-Magma)
      â (A â¡ B) â (Î£ f ê (â¨ A â© â â¨ B â©)
                       , is-equiv f
                       Ã ((Î» x x' â f (structure A x x')) â¡ (Î» x x' â structure B (f x) (f x'))))
 fact = â¡-is-ââ

\end{code}

 Perhaps the following reformulation is more appealing, where Agda
 infers that (X , _Â·_) and (Y , _*_) are â-Magmas from the *proof*
 "fact" of "fact'":

\begin{code}

 fact' : (X Y : ð¤ Ì ) (_Â·_ : X â X â X) (_*_ : Y â Y â Y)
       â ((X , _Â·_) â¡ (Y , _*_))
       â (Î£ f ê (X â Y) , is-equiv f Ã ((Î» x x' â f (x Â· x')) â¡ (Î» x x' â f x * f x')))
 fact' X Y _Â·_ _*_ = fact (X , _Â·_) (Y , _*_)

\end{code}

 Of course, the condition (Î» x x' â f (x Â· x')) â¡ (Î» x x' â f x â f x')
 is equivalent to (x x' : X) â f (x Â· x') â¡ f x â f x' by function
 extensionality. Hence the congruence of the type-theoretic operations
 gives that the identifications of â-Magmas are (equivalent to) a
 homomorphic equivalences:

\begin{code}

 open import UF-FunExt
 open import UF-UA-FunExt
 open import UF-EquivalenceExamples

 fe : funext ð¤ ð¤
 fe = univalence-gives-funext ua

 fact'' : (X Y : ð¤ Ì ) (_Â·_ : X â X â X) (_*_ : Y â Y â Y)
        â ((X , _Â·_) â¡ (Y , _*_))
        â (Î£ f ê (X â Y) , is-equiv f Ã ((x x' : X) â f (x Â· x') â¡ f x * f x'))
 fact'' X Y _Â·_ _*_ =
   ((X , _Â·_) â¡ (Y , _*_))
       ââ¨ fact' X Y _Â·_ _*_ â©
   (Î£ f ê (X â Y) , is-equiv f Ã ((Î» x x' â f (x Â· x')) â¡ (Î» x x' â f x * f x')))
       ââ¨ Î£-cong (Î» f â Ã-cong (â-refl (is-equiv f)) (â-funextâ fe fe _ _)) â©
   (Î£ f ê (X â Y) , is-equiv f Ã ((x x' : X) â f (x Â· x') â¡ f x * f x')) â 

\end{code}

 It is automatic that the inverse of f is also a magma homomorphism
 (exercise, perhaps worth adding). However, it is not the case, in the
 absence of the underlying types being sets, that equivalences of
 â-magmas are pairs of mutually inverse homomorphisms, for the same
 reason that equivalences of types are not in general equivalent to
 pairs of mutually inverse functions (quasi-equivalences, in the
 terminology of the HoTT book).

As a second example, a topology on a set X is a set of subsets of X
satisfying suitable axioms. A set of subsets amounts to a map
(X â Î©) â Î©. Dropping the assumption that the type X is a set and the
axioms for topologies, and generalizing Î© to an arbitrary type R, we
get â-proto-topological spaces.

\begin{code}

module â-proto-topological-spaces (ð¤ ð¥ : Universe) (ua : is-univalent ð¤) (R : ð¥ Ì ) where

 S : ð¤ Ì â ð¤ â ð¥ Ì
 S X = (X â R) â R

 open gsip
       ð¤ (ð¤ â ð¥) ua S
       (Î» {A B (f , e) â (Î» V â structure A (V â f)) â¡ structure B})
       (Î» A â refl)
       (Î» X Ï Ï â id)
       (Î» A Ï Ï â refl-left-neutral)

 fact : (A B : Î£ S)
      â (A â¡ B) â (Î£ f ê (â¨ A â© â â¨ B â©)
                       , is-equiv f Ã ((Î» V â structure A (Î» x â V (f x))) â¡ structure B))
 fact = â¡-is-ââ

\end{code}

 Or in perhaps more appealing terms:

\begin{code}

 fact' : (X Y : ð¤ Ì ) (Ï : (X â R) â R) (Ï : (Y â R) â R)
       â ((X , Ï) â¡ (Y , Ï)) â (Î£ f ê (X â Y) , is-equiv f Ã ((Î» V â Ï (V â f)) â¡ Ï))
 fact' X Y Ï Ï = fact (X , Ï) (Y , Ï)

\end{code}

 Again by function extensionality, structure preservation is equivalent
 to (V : Y â R) â Ï(V â f) â¡ Ï V. We can read this, at least when R is
 the type Î© of truth-values, as saying that a set V : Y â R is Ï-open
 precisely when its inverse image V â f is Ï-open.

 Thus, if we say that an equivalence f : X â Y is an â-homeomorphism
 when an "R-set" V : Y â R is Ï-open precisely when its f-inverse image
 V â f : X â R is Ï-open, then the above says that two
 â-proto-topological spaces are equal iff they are â-homeomorphic.

Another example generalizes metric spaces (when R is a type of reals)
and ordered sets (when R is Î© and d=_âº_, reflexive or not):

\begin{code}

module â-proto-metric-spaces (ð¤ ð¥ : Universe) (ua : is-univalent ð¤) (R : ð¥ Ì ) where

 S : ð¤ Ì â ð¤ â ð¥ Ì
 S X = X â X â R

 open gsip
       ð¤ (ð¤ â ð¥) ua S
       (Î» {A B (f , e) â structure A â¡ (Î» x x' â structure B (f x) (f x'))})
       (Î» A â refl)
       (Î» X d e â id)
       (Î» A s Ï â refl-left-neutral)

 fact : (A B : Î£ S)
      â (A â¡ B) â (Î£ f ê (â¨ A â© â â¨ B â©)
                       , is-equiv f Ã (structure A â¡ (Î» x x' â structure B (f x) (f x'))))
 fact = â¡-is-ââ

 fact' : (X Y : ð¤ Ì ) (d : X â X â R) (e : Y â Y â R)
       â ((X , d) â¡ (Y , e)) â (Î£ f ê (X â Y) , is-equiv f Ã (d â¡ (Î» x x' â e (f x) (f x'))))
 fact' X Y Ï Ï = fact (X , Ï) (Y , Ï)

\end{code}

 Notice that here the S-equivalences are the isometries (metric-space case)
 or order preserving-reflecting maps (ordered-set case).

The following example is related to compact types (in the sense of the
module CompactTypes):

\begin{code}

module selection-spaces (ð¤ ð¥ : Universe) (ua : is-univalent ð¤) (R : ð¥ Ì ) where

 S : ð¤ Ì â ð¤ â ð¥ Ì
 S X = (X â R) â X

 open gsip
       ð¤ (ð¤ â ð¥) ua S
       (Î» {A B (f , e) â (Î» V â f (structure A (V â f))) â¡ structure B})
       (Î» A â refl)
       (Î» X Îµ Î´ â id)
       (Î» A Ï Ï â refl-left-neutral)

 fact : (A B : Î£ S)
      â (A â¡ B) â (Î£ f ê (â¨ A â© â â¨ B â©)
                       , is-equiv f Ã ((Î» V â f(structure A (Î» x â V (f x)))) â¡ structure B))
 fact = â¡-is-ââ

 fact' : (X Y : ð¤ Ì ) (Îµ : (X â R) â X) (Î´ : (Y â R) â Y)
       â ((X , Îµ) â¡ (Y , Î´)) â (Î£ f ê (X â Y) , is-equiv f Ã ((Î» V â f (Îµ (V â f))) â¡ Î´))
 fact' X Y Ï Ï = fact (X , Ï) (Y , Ï)

\end{code}

We now continue our abstract development, to account for things such
as monoids and groups and topological spaces. We consider given axioms
on X and its structure.

\begin{code}

open import UF-Subsingletons

module gsip-with-axioms

 (ð¤ ð¥ : Universe)

 (ua : is-univalent ð¤)

 (S : ð¤ Ì â ð¥ Ì )

 (Axioms : (X : ð¤ Ì ) â S X â ð¥ Ì )

 (Axioms-is-prop : (X : ð¤ Ì ) (s : S X) â is-prop (Axioms X s))

 (S-equiv : (A B : Î£ S) â â¨ A â© â â¨ B â© â ð¤ â ð¥ Ì )

 (S-refl : (A : Î£ S) â S-equiv A A (â-refl â¨ A â©))

 (S-id-structure : (X : ð¤ Ì ) (s t : S X)
                 â S-equiv (X , s) (X , t) (â-refl X) â s â¡ t)

 (S-transport : (A : Î£ S)
                (s : S â¨ A â©)
                (Ï : S-equiv A (â¨ A â© , s) (â-refl â¨ A â©))
              â transport
                   (Î» - â S-equiv A (â¨ A â© , -) (â-refl â¨ A â©))
                   (S-id-structure â¨ A â© (structure A) s Ï)
                   (S-refl A)
              â¡ Ï)
 where

\end{code}

   Our reduction of gsip-with-axioms to gsip is as follows:

\begin{code}

   S' : ð¤ Ì â ð¥ Ì
   S' X = Î£ s ê S X , Axioms X s

   S'-preserving : (A' B' : Î£ S') â â¨ A' â© â â¨ B' â© â ð¤ â ð¥ Ì
   S'-preserving (X , s , Î±) (Y , t , Î²) = S-equiv (X , s) (Y , t)

   S'-refl : (A' : Î£ S') â S'-preserving A' A' (â-refl â¨ A' â©)
   S'-refl (X , s , Î±) = S-refl (X , s)

   S'-id-structure : (X : ð¤ Ì ) (s' t' : S' X)
                   â S'-preserving (X , s') (X , t') (â-refl X) â s' â¡ t'
   S'-id-structure X (s , Î±) (t , Î²) Ï' = to-Î£-â¡ (S-id-structure X s t Ï' ,
                                                   Axioms-is-prop X t _ _)

   S'-transport : (A' : Î£ S')
                  (s' : S' â¨ A' â©)
                  (Ï' : S'-preserving A' (â¨ A' â© , s') (â-refl â¨ A' â©))
                â transport
                     (Î» - â S'-preserving A' (â¨ A' â© , -) (â-refl â¨ A' â©))
                     (S'-id-structure â¨ A' â© (structure A') s' Ï')
                     (S'-refl A')
                â¡ Ï'
   S'-transport (X , s , Î±) (t , Î²) Ï' =
    f (S'-id-structure X (s , Î±) (t , Î²) Ï')
        â¡â¨ transport-ap F prâ (S'-id-structure X (s , Î±) (t , Î²) Ï') â©
    g (ap prâ (S'-id-structure X (s , Î±) (t , Î²) Ï'))
        â¡â¨ ap g r â©
    g (S-id-structure X s t Ï')
        â¡â¨ S-transport (X , s) t Ï' â©
    Ï'  â
    where
     F : S X â ð¤ â ð¥ Ì
     F t = S-equiv (X , s) (X  , t) (â-refl X)
     f : (s , Î±) â¡ (t , Î²) â F t
     f q = transport (F â prâ) q (S-refl (X , s))
     g : s â¡ t â F t
     g p = transport F p (S-refl (X , s))
     r : ap prâ (S'-id-structure X (s , Î±) (t , Î²) Ï') â¡ S-id-structure X s t Ï'
     r = ap-prâ-to-Î£-â¡ _

\end{code}

   We export gsip with the above data:

\begin{code}

   open gsip ð¤ ð¥ ua S' S'-preserving S'-refl S'-id-structure S'-transport public

\end{code}

   And this completes the reduction to gsip.

We now consider monoids to illustrate how this can be applied.

\begin{code}

module monoids (ð¤ : Universe) (ua : is-univalent ð¤) where

 open import UF-FunExt
 open import UF-Subsingletons-FunExt
 open import UF-UA-FunExt

 fe : funext ð¤ ð¤
 fe = univalence-gives-funext ua

\end{code}

The structure of a monoid with underlying type X consists of a binary
"multiplication" operation X â X â X and a distinguished point of X,
the "unit":

\begin{code}

 S : ð¤ Ì â ð¤ Ì
 S X = (X â X â X) Ã X

\end{code}

The axioms say that not only multiplication must be associative and
the unit must be neutral for this operation, but also the underlying
type X must a set:

\begin{code}

 Axioms : (X : ð¤ Ì ) â S X â ð¤ Ì
 Axioms X (_Â·_ , e) = is-set X
                    Ã ((x y z : X) â (x Â· y) Â· z â¡ x Â· (y Â· z))
                    Ã ((x : X) â (e Â· x â¡ x) Ã (x Â· e â¡ x))

\end{code}

The fact that the underlying type is a set gives that the axioms form
a proposition:

\begin{code}

 Axioms-is-prop : (X : ð¤ Ì ) (s : S X) â is-prop (Axioms X s)
 Axioms-is-prop X (_Â·_ , e) (i , Î± , Î½) = Ã-is-prop
                                           (being-set-is-prop fe)
                                           (Ã-is-prop
                                              (Î -is-prop fe
                                                 Î» x â Î -is-prop fe
                                                         Î» y â Î -is-prop fe
                                                                 Î» z â i)
                                              (Î -is-prop fe Î» x â Ã-is-prop i i))
                                          (i , Î± , Î½)
\end{code}

We use primed capital letters for types equipped with axiomless
structure. The following to functions extract the multiplication and
unit:

\begin{code}

 mul : (A' : Î£ S) â â¨ A' â© â â¨ A' â© â â¨ A' â©
 mul (X , _Â·_ , e) = _Â·_

 unit : (A' : Î£ S) â â¨ A' â©
 unit (X , _Â·_ , e) = e

\end{code}

A monoid is a type equipped with such structure and witnesses for the
axioms:

\begin{code}

 Monoid : ð¤ âº Ì
 Monoid = Î£ X ê ð¤ Ì , Î£ s ê S X , Axioms X s

\end{code}

We again have multiplication and unit extraction functions:

\begin{code}

 Î¼ : (A : Monoid) â â¨ A â© â â¨ A â© â â¨ A â©
 Î¼ (X , s , Î±) = mul (X , s)

 Î· : (A : Monoid) â â¨ A â©
 Î· (X , s , Î±) = unit (X , s)

\end{code}

And now we are ready to apply gsip-with-axioms to our situation:

\begin{code}

 open gsip-with-axioms
       ð¤ ð¤ ua S
       Axioms
       Axioms-is-prop
       (Î» {A' B' (f , e) â ((Î» x x' â f (mul A' x x')) â¡ (Î» x x' â mul B' (f x) (f x')))
                         Ã (f (unit A') â¡ unit B')})
       (Î» A' â refl , refl)
       (Î» X m n Ï â to-Ã-â¡ (prâ Ï) (prâ Ï))
       (Î» { A' m (refl , refl) â refl })

 fact : (A B : Monoid)
      â (A â¡ B)
      â (Î£ f ê (â¨ A â© â â¨ B â©)
             , is-equiv f
             Ã ((Î» x x' â f (Î¼ A x x')) â¡ (Î» x x' â Î¼ B (f x) (f x')))
             Ã (f (Î· A) â¡ Î· B))
 fact = â¡-is-ââ

 fact' : (X : ð¤ Ì ) (_Â·_ : X â X â X) (d : X) (Î± : Axioms X (_Â·_ , d))
         (Y : ð¤ Ì ) (_*_ : Y â Y â Y) (e : Y) (Î² : Axioms Y (_*_ , e))
       â ((X , (_Â·_ , d) , Î±) â¡ (Y , (_*_ , e) , Î²))
       â (Î£ f ê (X â Y)
              , is-equiv f
              Ã ((Î» x x' â f (x Â· x')) â¡ (Î» x x' â f x * f x'))
              Ã (f d â¡ e))
 fact' X _Â·_ d Î± Y _*_ e Î² = fact (X , ((_Â·_ , d) , Î±)) (Y , ((_*_ , e) , Î²))

\end{code}

Perhaps it is possible to derive the SIP for 1-categories from the
above SIP for types equipped with structure. But this is not the point
we are trying to make. The point is to give a criterion for natural
characterizations of identity of types equipped with structure, and
possibly axioms for them, before we know they form (â-)categories, and
even if they don't.

Another example that should be accounted for by the methods developed
here is identity of ordinals (in the module ), which
is what prompted us to think about the subject of this module.

Added 8th December 2018. I came across a situation where the universe
levels don't work if the axioms apply only to the underlying set (and
not to the structure). Here is a version that addresses that:

\begin{code}

module gsip'

  (ð¤ ð¥ ð¦ : Universe)

  (ua : is-univalent ð¤)

  (S : ð¤ Ì â ð¥ Ì )

  (S-equiv : (A B : Î£ S) â â¨ A â© â â¨ B â© â ð¦ Ì )

  (S-refl : (A : Î£ S) â S-equiv A A (â-refl â¨ A â©))

  (S-id-structure : (X : ð¤ Ì ) (s t : S X)
                  â S-equiv (X , s) (X , t) (â-refl X) â s â¡ t)

  (S-transport : (A : Î£ S)
                 (s : S â¨ A â©)
                 (Ï : S-equiv A (â¨ A â© , s) (â-refl â¨ A â©))
               â transport
                    (Î» - â S-equiv A (â¨ A â© , -) (â-refl â¨ A â©))
                    (S-id-structure â¨ A â© (structure A) s Ï)
                    (S-refl A)
               â¡ Ï)
  where

  _ââ_ : Î£ S â Î£ S â ð¤ â ð¦ Ì
  A ââ B = Î£ f ê (â¨ A â© â â¨ B â©) , Î£ e ê is-equiv f , S-equiv A B (f , e)

  ââ-refl : (A : Î£ S) â A ââ A
  ââ-refl A = prâ(â-refl â¨ A â©) , prâ(â-refl â¨ A â©) , S-refl A

  idtoeqâ : (A B : Î£ S) â A â¡ B â A ââ B
  idtoeqâ A .A refl = ââ-refl A

  private
    Î¨ : (A : Î£ S) (Y : ð¤ Ì ) â â¨ A â© â Y â ð¤ âº â ð¥ â ð¦ Ì
    Î¨ A Y e = (s : S Y) â S-equiv A (Y , s) e â A â¡ (Y , s)
    Ï : (A : Î£ S) â Î¨ A â¨ A â© (â-refl â¨ A â©)
    Ï A s Ï = to-Î£-â¡' (S-id-structure â¨ A â© (structure A) s Ï)

  eqtoidâ : (A B : Î£ S) â A ââ B â A â¡ B
  eqtoidâ A B (f , e , Ï) = JEq ua â¨ A â© (Î¨ A) (Ï A) â¨ B â© (f , e) (structure B) Ï

  idtoeq-eqtoidâ : (A B : Î£ S) (Îµ : A ââ B) â idtoeqâ A B (eqtoidâ A B Îµ) â¡ Îµ
  idtoeq-eqtoidâ A B (f , e , Ï) = JEq ua â¨ A â© Î¦ Ï â¨ B â© (f , e) (structure B) Ï
   where
    Î¦ : (Y : ð¤ Ì ) â â¨ A â© â Y â ð¤ â ð¥ â ð¦ Ì
    Î¦ Y (f , e) = (s : S Y)
                  (Ï : S-equiv A (Y , s) (f , e))
                 â idtoeqâ A (Y , s) (eqtoidâ A (Y , s) (f , e , Ï)) â¡ f , e , Ï
    Ï : Î¦ â¨ A â© (â-refl â¨ A â©)
    Ï s Ï =
      idtoeqâ A A' (eqtoidâ A A' refl')
            â¡â¨ ap (Î» h â idtoeqâ A A' (h s Ï)) (JEq-comp ua â¨ A â© (Î¨ A) (Ï A)) â©
      idtoeqâ A A' (to-Î£-â¡' p)
            â¡â¨ h p â©
      prâ(â-refl â¨ A â©) , prâ(â-refl â¨ A â©) , g p
            â¡â¨ to-Î£-â¡' (to-Î£-â¡' (S-transport A s Ï)) â©
      refl' â
     where
      A' : Î£ S
      A' = â¨ A â© , s
      refl' : A ââ A'
      refl' = prâ(â-refl â¨ A â©) , prâ(â-refl â¨ A â©) , Ï
      g : structure A â¡ s â S-equiv A A' (â-refl â¨ A â©)
      g p = transport (Î» - â S-equiv A (â¨ A â© , -) (â-refl â¨ A â©)) p (S-refl A)
      h : (p : structure A â¡ s) â idtoeqâ A A' (to-Î£-â¡' p)
                                â¡ prâ(â-refl â¨ A â©) , prâ(â-refl â¨ A â©) , g p
      h refl = refl
      p : structure A â¡ s
      p = S-id-structure â¨ A â© (structure A) s Ï

  uaâ : (A B : Î£ S) â is-equiv (idtoeqâ A B)
  uaâ A = nats-with-sections-are-equivs A
            (idtoeqâ A)
            (Î» B â eqtoidâ A B , idtoeq-eqtoidâ A B)

  eqtoid-idtoeqâ : (A B : Î£ S) (p : A â¡ B) â eqtoidâ A B (idtoeqâ A B p) â¡ p
  eqtoid-idtoeqâ A B = prâ(prâ (equivs-are-qinvs (idtoeqâ A B) (uaâ A B)))

  â¡-is-ââ : (A B : Î£ S) â (A â¡ B) â (A ââ B)
  â¡-is-ââ A B = idtoeqâ A B , uaâ A B

  _ââ'_ : Î£ S â Î£ S â ð¤ â ð¦ Ì
  A ââ' B = Î£ p ê â¨ A â© â â¨ B â© , S-equiv A B (prâ p , prâ p)

  ââ-is-ââ' : (A B : Î£ S) â (A ââ B) â (A ââ' B)
  ââ-is-ââ' A B = â-sym Î£-assoc

  â¡-is-ââ' : (A B : Î£ S) â (A â¡ B) â (A ââ' B)
  â¡-is-ââ' A B = (â¡-is-ââ A B) â (ââ-is-ââ' A B)

module gsip-with-axioms'

 (ð¤ ð¥ ð¦ ð£ : Universe)

 (ua : is-univalent ð¤)

 (S : ð¤ Ì â ð¥ Ì )

 (Axioms : (X : ð¤ Ì ) â S X â ð£ Ì )

 (Axioms-is-prop : (X : ð¤ Ì ) (s : S X) â is-prop (Axioms X s))

 (S-equiv : (A B : Î£ S) â â¨ A â© â â¨ B â© â ð¦ Ì )

 (S-refl : (A : Î£ S) â S-equiv A A (â-refl â¨ A â©))

 (S-id-structure : (X : ð¤ Ì ) (s t : S X)
                 â S-equiv (X , s) (X , t) (â-refl X) â s â¡ t)

 (S-transport : (A : Î£ S)
                (s : S â¨ A â©)
                (Ï : S-equiv A (â¨ A â© , s) (â-refl â¨ A â©))
              â transport
                   (Î» - â S-equiv A (â¨ A â© , -) (â-refl â¨ A â©))
                   (S-id-structure â¨ A â© (structure A) s Ï)
                   (S-refl A)
              â¡ Ï)
 where

   S' : ð¤ Ì â ð¥ â ð£ Ì
   S' X = Î£ s ê S X , Axioms X s

   S'-preserving : (A' B' : Î£ S') â â¨ A' â© â â¨ B' â© â ð¦ Ì
   S'-preserving (X , s , Î±) (Y , t , Î²) = S-equiv (X , s) (Y , t)

   S'-refl : (A' : Î£ S') â S'-preserving A' A' (â-refl â¨ A' â©)
   S'-refl (X , s , Î±) = S-refl (X , s)

   S'-id-structure : (X : ð¤ Ì ) (s' t' : S' X)
                   â S'-preserving (X , s') (X , t') (â-refl X) â s' â¡ t'
   S'-id-structure X (s , Î±) (t , Î²) Ï' = to-Î£-â¡ (S-id-structure X s t Ï' ,
                                                   Axioms-is-prop X t _ _)

   S'-transport : (A' : Î£ S')
                  (s' : S' â¨ A' â©)
                  (Ï' : S'-preserving A' (â¨ A' â© , s') (â-refl â¨ A' â©))
                â transport
                     (Î» - â S'-preserving A' (â¨ A' â© , -) (â-refl â¨ A' â©))
                     (S'-id-structure â¨ A' â© (structure A') s' Ï')
                     (S'-refl A')
                â¡ Ï'
   S'-transport (X , s , Î±) (t , Î²) Ï' =
    f (S'-id-structure X (s , Î±) (t , Î²) Ï')
        â¡â¨ transport-ap F prâ (S'-id-structure X (s , Î±) (t , Î²) Ï') â©
    g (ap prâ (S'-id-structure X (s , Î±) (t , Î²) Ï'))
        â¡â¨ ap g r â©
    g (S-id-structure X s t Ï')
        â¡â¨ S-transport (X , s) t Ï' â©
    Ï'  â
    where
     F : S X â ð¦ Ì
     F t = S-equiv (X , s) (X  , t) (â-refl X)
     f : (s , Î±) â¡ (t , Î²) â F t
     f q = transport (F â prâ) q (S-refl (X , s))
     g : s â¡ t â F t
     g p = transport F p (S-refl (X , s))
     r : ap prâ (S'-id-structure X (s , Î±) (t , Î²) Ï') â¡ S-id-structure X s t Ï'
     r = ap-prâ-to-Î£-â¡ _

   open gsip' ð¤ (ð¥ â ð£) ð¦ ua S' S'-preserving S'-refl S'-id-structure S'-transport public

\end{code}

TODO. Maybe replace the original versions by this last version. This
requires changing the existing code that uses the original, less
general, version. Or redefining the original version as an instance of
the new version.
