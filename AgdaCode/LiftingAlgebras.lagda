Martin Escardo 17th December 2018. (This has a connection with injectivity.)

We have a look at the algebras of the lifting monad.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module LiftingAlgebras
        (π£ : Universe)
       where

open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-Univalence
open import UF-UA-FunExt

open import Lifting π£
open import LiftingIdentityViaSIP π£
open import LiftingMonad π£

\end{code}

An element of π (π X) amounts to a family of partial elements of X
indexed by a proposition:

\begin{code}

double-π-charac : (X : π€ Μ )
                β π (π X) β (Ξ£ P κ π£ Μ
                                 , (Ξ£ Q κ (P β π£ Μ ), ((p : P) β (Q p β X)) Γ ((p : P) β is-prop (Q p)))
                                 Γ is-prop P)
double-π-charac X = Ξ£-cong (Ξ» P β Γ-cong (Ξ³ X P) (β-refl (is-prop P)))
 where
  Ξ³ : (X : π€ Μ ) (P : π£ Μ ) β (P β π X) β (Ξ£ Q κ (P β π£ Μ ), ((p : P) β (Q p β X)) Γ ((p : P) β is-prop (Q p)))
  Ξ³ X P = (P β Ξ£ Q κ π£ Μ , (Q β X) Γ is-prop Q)                                 ββ¨ Ξ Ξ£-distr-β β©
          (Ξ£ Q κ (P β π£ Μ ), ((p : P) β ((Q p β X) Γ is-prop (Q p))))           ββ¨ Ξ£-cong (Ξ» Q β βΓ) β©
          (Ξ£ Q κ (P β π£ Μ ), ((p : P) β (Q p β X)) Γ ((p : P) β is-prop (Q p))) β 

\end{code}

The usual definition of algebra of a monad and construction of free
algebras:

\begin{code}

π-algebra : π€ Μ β π£ βΊ β π€ Μ
π-algebra X = Ξ£ s κ (π X β X) , (s β Ξ· βΌ id) Γ (s β ΞΌ βΌ s β πΜ s)

free-π-algebra : is-univalent π£ β (X : π€ Μ ) β π-algebra (π X)
free-π-algebra ua X = ΞΌ , π-unit-leftβΌ ua , π-assocβΌ ua

\end{code}

We can describe algebras in terms of "join" operations subject to two
laws:

\begin{code}

joinop : π€ Μ β π£ βΊ β π€ Μ
joinop X = {P : π£ Μ } β is-prop P β (P β X) β X

\end{code}

The intuitive idea is that a "join" operation on X consists of, for
each proposition P, a map (P β X) β X that "puts together" the
elements of a family f : P β X to get an element β f of X.

Unfortunately, we won't be able to write simply β f in Agda notation,
as the witness that P is a proposition can almost never be
automatically inferred and hence has to be written explicitly.

To characterize algebras, the join operations have two satisfy the
following two laws:

\begin{code}

π-alg-Lawβ : {X : π€ Μ } β joinop X β π€ Μ
π-alg-Lawβ {π€} {X} β = (x : X) β β π-is-prop (Ξ» (p : π) β x) β‘ x

π-alg-Lawβ : {X : π€ Μ } β joinop X β π£ βΊ β π€ Μ
π-alg-Lawβ {π€} {X} β = (P : π£ Μ ) (Q : P β π£ Μ ) (i : is-prop P) (j : (p : P) β is-prop (Q p)) (f : Ξ£ Q β X)
                          β β (Ξ£-is-prop i j) f β‘ β i (Ξ» p β β (j p) (Ξ» q β f (p , q)))

\end{code}

Omitting the witnesses of proposition-hood, the above two laws can be
written in more standard mathematical notation as follows:

    β  x = x
   p:π

    β          f r  =  β   β     f (p , q)
  r : Ξ£ {P} Q         p:P q:Q(p)


\begin{code}

π-alg : π€ Μ β π£ βΊ β π€ Μ
π-alg X = Ξ£ β κ joinop X , π-alg-Lawβ β Γ π-alg-Lawβ β

\end{code}

Before proving that we have an equivalence

  π-algebra X β π-alg X,

we characterize the algebra morphisms in terms of joins (unfortunately
overloading is not available):

\begin{code}

β : {X : π€ Μ } β (π X β X) β joinop X
β s {P} i f = s (P , f , i)

βΜ : {X : π€ Μ } β π-algebra X β joinop X
βΜ (s , _) = β s

β : {X : π€ Μ } β π-alg X β joinop X
β (β , ΞΊ , ΞΉ) = β

lawβ : {X : π€ Μ } (a : π-alg X) β π-alg-Lawβ (β a)
lawβ (β , ΞΊ , ΞΉ) = ΞΊ

lawβ : {X : π€ Μ } (a : π-alg X) β π-alg-Lawβ (β a)
lawβ (β , ΞΊ , ΞΉ) = ΞΉ


\end{code}

The algebra morphisms are the maps that preserve joins. Omitting the
first argument of β, the following says that the morphisms are the
maps h : X β Y with

  h (β f) β‘ β h (f p)
            p:P

for all f:PβX.

\begin{code}

π-morphism-charac : {X : π€ Μ } {Y : π₯ Μ }
                    (s : π X β X) (t : π Y β Y)
                    (h : X β Y)

                  β (h β s βΌ t β πΜ h)
                  β ({P : π£ Μ } (i : is-prop P) (f : P β X) β h (β s i f) β‘ β t i (Ξ» p β h (f p)))
π-morphism-charac s t h = qinveq (Ξ» H {P} i f β H (P , f , i))
                                 ((Ξ» {Ο (P , f , i) β Ο {P} i f}) ,
                                 (Ξ» _ β refl) ,
                                 (Ξ» _ β refl))

\end{code}

We name the other two projections of π-alg:

\begin{code}

π-alg-const : {X : π€ Μ } (A : π-alg X) β (x : X) β β A π-is-prop (Ξ» (p : π) β x) β‘ x
π-alg-const (β , ΞΊ , ΞΉ) = ΞΊ

π-alg-iterated : {X : π€ Μ } (A : π-alg X)
                 (P : π£ Μ ) (Q : P β π£ Μ ) (i : is-prop P) (j : (p : P) β is-prop (Q p))
                 (f : Ξ£ Q β X)
               β β A (Ξ£-is-prop i j) f β‘ β A i (Ξ» p β β A (j p) (Ξ» q β f (p , q)))
π-alg-iterated (β , ΞΊ , ΞΉ) = ΞΉ

\end{code}

We could write a proof of the following characterization of the
π-algebras by composing equivalences as above, but it seems more
direct, and just as clear, to write a direct proof, by construction of
the equivalence and its inverse. This also emphasizes that the
equivalence is definitional, in the sense that the two required
equations hold definitionally.

\begin{code}

π-algebra-gives-alg : {X : π€ Μ } β π-algebra X β π-alg X
π-algebra-gives-alg (s , unit , assoc) =
                    β s ,
                    unit ,
                    (Ξ» P Q i j f β assoc (P , (Ξ» p β Q p , (Ξ» q β f (p , q)) , j p) , i))

π-alg-gives-algebra : {X : π€ Μ } β π-alg X β π-algebra X
π-alg-gives-algebra {π€} {X} (β , unit , ΞΉ) = s , unit , assoc
 where
  s : π X β X
  s (P , f , i) = β i f
  assoc : s β ΞΌ βΌ s β πΜ s
  assoc (P , g , i) = ΞΉ P (prβ β g) i (Ξ» p β prβ (prβ (g p))) (Ξ» r β prβ (prβ (g (prβ r))) (prβ r))

π-alg-charac : {X : π€ Μ } β π-algebra X β π-alg X
π-alg-charac = qinveq π-algebra-gives-alg (π-alg-gives-algebra , ((Ξ» _ β refl) , (Ξ» _ β refl)))

\end{code}

We now consider an equivalent of π-alg-Lawβ (which is useful e.g. for
type injectivity purposes).

\begin{code}

π-alg-Lawβ' : {X : π€ Μ } β joinop X β π£ βΊ β π€ Μ
π-alg-Lawβ' {π€} {X} β = (P : π£ Μ ) (i : is-prop P) (f : P β X) (p : P) β β i f β‘ f p


π-alg-Lawβ-givesβ' : propext π£
                   β funext π£ π£
                     β funext π£ π€
                   β {X : π€ Μ } (β : joinop X)
                   β π-alg-Lawβ β β π-alg-Lawβ' β
π-alg-Lawβ-givesβ' pe fe fe' {X} β ΞΊ P i f p = Ξ³
 where
  r : f β‘ Ξ» (_ : P) β f p
  r = dfunext fe' (Ξ» p' β ap f (i p' p))
  s : P β‘ π β β {P} i f β‘ β {π} π-is-prop (Ξ» (_ : π) β f p)
  s refl = apβ β (being-prop-is-prop fe i π-is-prop) r
  t : P β‘ π
  t = pe i π-is-prop unique-to-π (Ξ» _ β p)
  Ξ³ : β i f β‘ f p
  Ξ³ = β {P} i f                   β‘β¨ s t β©
      β π-is-prop (f β (Ξ» _ β p)) β‘β¨ ΞΊ (f p) β©
      f p                         β

π-alg-Lawβ'-givesβ : {X : π€ Μ } (β : joinop X)
                    β π-alg-Lawβ' β β π-alg-Lawβ β
π-alg-Lawβ'-givesβ {π€} {X} β Ο x = Ο π π-is-prop (Ξ» _ β x) β

\end{code}

We now consider a non-dependent version of π-alg-Lawβ, and show that it is
equivalent to π-alg-Lawβ:

\begin{code}

π-alg-Lawβ' : {X : π€ Μ } β joinop X β π£ βΊ β π€ Μ
π-alg-Lawβ' {π€} {X} β = (P Q : π£ Μ ) (i : is-prop P) (j : is-prop Q) (f : P Γ Q β X)
                             β β (Γ-is-prop i j) f β‘ β i (Ξ» p β β j (Ξ» q β f (p , q)))

\end{code}

The difference with π-alg-Lawβ is that the family f has type P Γ Q β X
rather than Ξ£ {P} Q β X, and so the modified, logically equivalent law
amounts to

    β   β   f (p , q) =   β        f r
   p:P q:Q              r : P Γ Q

One direction of the logical equivalence is trivial:

\begin{code}

π-alg-Lawβ-givesβ' : {X : π€ Μ } (β : joinop X)
                   β π-alg-Lawβ β β π-alg-Lawβ' β
π-alg-Lawβ-givesβ' {π€} {X} β a P Q i j = a P (Ξ» _ β Q) i (Ξ» p β j)

\end{code}

To establish the converse we need the following lemma for joins, which
is interesting on its own right,

  β  f p β‘ β  f (k q),
 p:P      q:Q

and also gives self-distributivity of joins:

  β   β  f (p , q) =   β   β  f (p , q)
 p:P q:Q              q:Q p:P


\begin{code}

change-of-variables-in-join : {X : π€ Μ } (β : joinop X)
                              (P : π£ Μ ) (i : is-prop P)
                              (Q : π£ Μ ) (j : is-prop Q)
                              (h : P β Q) (k : Q β P) (f : P β X)
                            β is-univalent π£
                            β β i f β‘ β j (f β k)

change-of-variables-in-join β P i Q j h k f ua = cd (eqtoid ua Q P e) β ap (Ξ» - β β j (f β -)) a
 where
  cd : (r : Q β‘ P) β β i f β‘ β j (f β Idtofun r)
  cd refl = ap (Ξ» - β β - f) (being-prop-is-prop (univalence-gives-funext ua) i j)
  e : Q β P
  e = qinveq k (h , ((Ξ» q β j (h (k q)) q) , Ξ» p β i (k (h p)) p))
  a : Idtofun (eqtoid ua Q P e) β‘ k
  a = ap β_β (idtoeq'-eqtoid ua Q P e)

π-alg-self-distr : {X : π€ Μ } (β : joinop X)
                   (P : π£ Μ ) (i : is-prop P)
                   (Q : π£ Μ ) (j : is-prop Q)
                 β is-univalent π£
                 β π-alg-Lawβ' β
                 β (f : P Γ Q β X) β β i (Ξ» p β β j (Ξ» q β f (p , q)))
                                   β‘ β j (Ξ» q β β i (Ξ» p β f (p , q)))

π-alg-self-distr β P i Q j ua lβ' f = β i (Ξ» p β β j (Ξ» q β f (p , q)))                     β‘β¨ a β©
                                      β (Ξ£-is-prop i (Ξ» p β j)) f                           β‘β¨ b β©
                                      β (Ξ£-is-prop j (Ξ» p β i)) (f β (Ξ» t β prβ t , prβ t)) β‘β¨ c β©
                                      β j (Ξ» q β β i (Ξ» p β f (p , q)))                     β
 where
  a = (lβ' P Q i j f)β»ΒΉ
  b = change-of-variables-in-join β (P Γ Q) (Ξ£-is-prop i (Ξ» p β j)) (Q Γ P) (Ξ£-is-prop j (Ξ» p β i))
                                  (Ξ» t β prβ t , prβ t) (Ξ» t β prβ t , prβ t) f ua
  c = lβ' Q P j i (Ξ» t β f (prβ t , prβ t))

\end{code}

Using this we can prove the other direction of the logical equivalence claimed above:

\begin{code}

π-alg-Lawβ'-givesβ : {X : π€ Μ } (β : joinop X)
                    β is-univalent π£
                    β funext π£ π€
                    β π-alg-Lawβ' β β π-alg-Lawβ β
π-alg-Lawβ'-givesβ {π€} {X} β ua fe a P Q i j f =
 β {Ξ£ Q} (Ξ£-is-prop i j) f                                         β‘β¨ b β©
 β {Ξ£ Q} (Ξ£-is-prop i j) (f' β k')                                 β‘β¨ c β©
 β {P Γ Ξ£ Q} (Γ-is-prop i (Ξ£-is-prop i j)) f'                      β‘β¨ d β©
 β {P} i (Ξ» p β β {Ξ£ Q} (Ξ£-is-prop i j) ((Ξ» Ο β f (p , Ο)) β k p)) β‘β¨ e β©
 β {P} i (Ξ» p β β {Q p} (j p) (Ξ» q β f (p , q)))                   β

 where
  h : (p : P) β Q p β Ξ£ Q
  h p q = (p , q)
  k : (p : P) β Ξ£ Q β Q p
  k p (p' , q) = transport Q (i p' p) q
  f' : P Γ Ξ£ Q β X
  f' (p , p' , q) = f (p , k p (p' , q))
  k' : Ξ£ Q β P Γ Ξ£ Q
  k' (p , q) = p , p , q
  H : f' β k' βΌ f
  H (p , q) = ap (Ξ» - β f (p , -)) (j p _ _)
  b = (ap (β {Ξ£ Q} (Ξ£-is-prop i j)) (dfunext fe H))β»ΒΉ
  c = (change-of-variables-in-join β (P Γ Ξ£ Q) (Γ-is-prop i (Ξ£-is-prop i j)) (Ξ£ Q) (Ξ£-is-prop i j) prβ k' f' ua)β»ΒΉ
  d = a P (Ξ£ Q) i (Ξ£-is-prop i j) (Ξ» z β f (prβ z , k (prβ z) (prβ z)))
  e = (ap (β {P} i) (dfunext fe (Ξ» p β change-of-variables-in-join β (Q p) (j p) (Ξ£ Q) (Ξ£-is-prop i j)
                                                                  (h p) (k p) (Ξ» Ο β f (p , Ο)) ua)))β»ΒΉ

\end{code}

The algebras form an exponential ideal with the pointwise
operations. More generally:

\begin{code}

Ξ -is-alg : funext π€ π₯
         β {X : π€ Μ } (A : X β π₯ Μ )
         β ((x : X) β π-alg (A x)) β π-alg (Ξ  A)
Ξ -is-alg {π€} {π₯} fe {X} A Ξ± = βΒ· , lβ , lβ
 where
  βΒ· : {P : π£ Μ } β is-prop P β (P β Ξ  A) β Ξ  A
  βΒ· i f x = β (Ξ± x) i (Ξ» p β f p x)
  lβ : (Ο : Ξ  A) β βΒ· π-is-prop (Ξ» p β Ο) β‘ Ο
  lβ Ο = dfunext fe (Ξ» x β lawβ (Ξ± x) (Ο x))
  lβ : (P : π£ Μ ) (Q : P β π£ Μ )
       (i : is-prop P) (j : (p : P) β is-prop (Q p))
       (f : Ξ£ Q β Ξ  A)
      β
        βΒ· (Ξ£-is-prop i j) f
      β‘ βΒ· i (Ξ» p β βΒ· (j p) (Ξ» q β f (p , q)))
  lβ P Q i j f = dfunext fe (Ξ» x β lawβ (Ξ± x) P Q i j (Ξ» Ο β f Ο x))

\end{code}

This is the case for any monad of a certain kind, but the way we
proved this above with using our characterizations of the algebras
applies only to our monad.

The following examples are crucial for injectivity. They say that the
universe is an algebra in at least two ways, with β = Ξ£ and β = Ξ 
respectively.

\begin{code}

universe-is-algebra-Ξ£ : is-univalent π£ β π-alg (π£ Μ )
universe-is-algebra-Ξ£ ua = sum , k , ΞΉ
 where
  sum : {P : π£ Μ } β is-prop P β (P β π£ Μ ) β π£ Μ
  sum {P} i = Ξ£
  k : (X : π£ Μ ) β Ξ£ (Ξ» p β X) β‘ X
  k X = eqtoid ua (π Γ X) X π-lneutral
  ΞΉ : (P : π£ Μ ) (Q : P β π£ Μ ) (i : is-prop P)
      (j : (p : P) β is-prop (Q p)) (f : Ξ£ Q β π£ Μ )
    β Ξ£ f β‘ Ξ£ (Ξ» p β Ξ£ (Ξ» q β f (p , q)))
  ΞΉ P Q i j f = eqtoid ua _ _ Ξ£-assoc

universe-is-algebra-Ξ  : is-univalent π£ β π-alg (π£ Μ )
universe-is-algebra-Ξ  ua = prod , k , ΞΉ
 where
  fe : funext π£ π£
  fe = univalence-gives-funext ua
  prod : {P : π£ Μ } β is-prop P β (P β π£ Μ ) β π£ Μ
  prod {P} i = Ξ 
  k : (X : π£ Μ ) β Ξ  (Ξ» p β X) β‘ X
  k X = eqtoid ua (π β X) X (β-sym (πβ (univalence-gives-funext ua)))
  ΞΉ : (P : π£ Μ ) (Q : P β π£ Μ ) (i : is-prop P)
      (j : (p : P) β is-prop (Q p)) (f : Ξ£ Q β π£ Μ )
    β Ξ  f β‘ Ξ  (Ξ» p β Ξ  (Ξ» q β f (p , q)))
  ΞΉ P Q i j f = eqtoid ua _ _ (curry-uncurry' fe fe)

\end{code}
