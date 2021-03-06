Martin Escardo.

Formulation of univalence. Notice that this file doesn't postulate
univalence. It only defines the notion of univalent
universe. Univalence, when used, is taken as an explicit hypothesis.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Univalence where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Equiv
open import UF-LeftCancellable

is-univalent : โ ๐ค โ ๐ค โบ ฬ
is-univalent ๐ค = (X Y : ๐ค ฬ ) โ is-equiv(idtoeq X Y)

Univalence : ๐คฯ
Univalence = (๐ค : Universe) โ is-univalent ๐ค

idtoeq' : (X Y : ๐ค ฬ ) โ X โก Y โ X โ Y
idtoeq' X Y p = (Idtofun p , transports-are-equivs p)

idtoEqs-agree : (X Y : ๐ค ฬ ) โ idtoeq' X Y โผ idtoeq X Y
idtoEqs-agree X _ refl = refl

Idtofun-is-equiv : (X Y : ๐ค ฬ ) (p : X โก Y) โ is-equiv(idtofun X Y p)
Idtofun-is-equiv X Y p = prโ(idtoeq X Y p)

module _
        (ua : is-univalent ๐ค)
       where

 eqtoid : (X Y : ๐ค ฬ ) โ X โ Y โ X โก Y
 eqtoid X Y = prโ(prโ(ua X Y))

 idtoeq-eqtoid : (X Y : ๐ค ฬ ) (e : X โ Y) โ idtoeq X Y (eqtoid X Y e) โก e
 idtoeq-eqtoid X Y = prโ(prโ(ua X Y))

 eqtoid-idtoeq : (X Y : ๐ค ฬ ) (p : X โก Y) โ  eqtoid X Y (idtoeq X Y p) โก p
 eqtoid-idtoeq X Y = prโ(prโ (equivs-are-qinvs (idtoeq X Y) (ua X Y)))

 eqtoid-refl : (X : ๐ค ฬ ) โ eqtoid X X (โ-refl X) โก refl
 eqtoid-refl X = eqtoid-idtoeq X X refl

 idtoeq'-eqtoid : (X Y : ๐ค ฬ ) โ idtoeq' X Y โ eqtoid X Y โผ id
 idtoeq'-eqtoid X Y e = idtoEqs-agree X Y (eqtoid X Y e) โ idtoeq-eqtoid X Y e

 idtofun-eqtoid : {X Y : ๐ค ฬ } (e : X โ Y)
                โ idtofun X Y (eqtoid X Y e) โก โ e โ
 idtofun-eqtoid {X} {Y} e = ap prโ (idtoeq-eqtoid X Y e)

 Idtofun-eqtoid : {X Y : ๐ค ฬ } (e : X โ Y)
                โ Idtofun (eqtoid X Y e) โก โ e โ
 Idtofun-eqtoid {X} {Y} e =
  (idtofun-agreement X Y (eqtoid X Y e)) โปยน โ idtofun-eqtoid e

 Idtofun-โ : {X Y Z : ๐ค ฬ } (p : X โก Y) (q : Y โก Z)
           โ Idtofun (p โ q) โก Idtofun q โ Idtofun p
 Idtofun-โ refl refl = refl

 univalence-โ : (X Y : ๐ค ฬ ) โ (X โก Y) โ (X โ Y)
 univalence-โ X Y = idtoeq X Y , ua X Y

 back-transport-is-pre-comp' : {X X' Y : ๐ค ฬ } (e : X โ X') (g : X' โ Y)
                             โ back-transport (ฮป - โ - โ Y) (eqtoid X X' e) g โก g โ โ e โ
 back-transport-is-pre-comp' {X} {X'} e g = back-transport-is-pre-comp (eqtoid X X' e) g โ q
  where
   q : g โ Idtofun (eqtoid X X' e) โก g โ โ e โ
   q = ap (g โ_) (ap โ_โ (idtoeq'-eqtoid X X' e))

 pre-comp-is-equiv : {X Y Z : ๐ค ฬ } (f : X โ Y)
                   โ is-equiv f โ is-equiv (ฮป (g : Y โ Z) โ g โ f)
 pre-comp-is-equiv {X} {Y} f ise =
  equiv-closed-under-โผ' (back-transports-are-equivs (eqtoid X Y (f , ise)))
                        (back-transport-is-pre-comp' (f , ise))

\end{code}

Induction on equivalences is available in univalent universes: to
prove that all equivalences satisfy some property, it is enough to
show that the identity equivalences satisfy it.

\begin{code}

โ-induction : (๐ค ๐ฅ : Universe) โ (๐ค โ ๐ฅ)โบ ฬ
โ-induction ๐ค ๐ฅ = (X : ๐ค ฬ ) (A : (Y : ๐ค ฬ ) โ X โ Y โ ๐ฅ ฬ )
                 โ A X (โ-refl X) โ (Y : ๐ค ฬ ) (e : X โ Y) โ A Y e

private
 JEq' : is-univalent ๐ค โ โ {๐ฅ} โ โ-induction ๐ค ๐ฅ
 JEq' {๐ค} ua {๐ฅ} X A b Y e = transport (A Y) (idtoeq-eqtoid ua X Y e) g
  where
   A' : (Y : ๐ค ฬ ) โ X โก Y โ ๐ฅ ฬ
   A' Y p = A Y (idtoeq X Y p)
   b' : A' X refl
   b' = b
   f' : (Y : ๐ค ฬ ) (p : X โก Y) โ A' Y p
   f' = Jbased X A' b'
   g : A Y (idtoeq X Y (eqtoid ua X Y e))
   g = f' Y (eqtoid ua X Y e)

eqtoid-inverse : (ua : is-univalent ๐ค) {X X' : ๐ค ฬ } (e : X โ X')
               โ (eqtoid ua X X' e)โปยน โก eqtoid ua X' X (โ-sym e)
eqtoid-inverse ua {X} {X'} = JEq' ua X (ฮป X' e โ (eqtoid ua X X' e)โปยน โก eqtoid ua X' X (โ-sym e)) p X'
 where
  p : (eqtoid ua X X (โ-refl X))โปยน โก eqtoid ua X X (โ-sym (โ-refl X))
  p = ap _โปยน (eqtoid-refl ua X) โ (eqtoid-refl ua X)โปยน

idtofun-eqtoid-โปยน : (ua : is-univalent ๐ค) {X Y : ๐ค ฬ } (e : X โ Y)
                  โ idtofun Y X ((eqtoid ua X Y e) โปยน) โก โ e โโปยน
idtofun-eqtoid-โปยน ua {X} {Y} e =
 idtofun Y X ((eqtoid ua X Y e) โปยน)    โกโจ I  โฉ
 idtofun Y X (eqtoid ua Y X (โ-sym e)) โกโจ II โฉ
 โ e โโปยน                               โ
  where
   I  = ap (idtofun Y X) (eqtoid-inverse ua e)
   II = idtofun-eqtoid ua (โ-sym e)

Idtofun-eqtoid-โปยน : (ua : is-univalent ๐ค) {X Y : ๐ค ฬ } (e : X โ Y)
                  โ Idtofun ((eqtoid ua X Y e) โปยน) โก โ e โโปยน
Idtofun-eqtoid-โปยน ua {X} {Y} e =
 (idtofun-agreement Y X ((eqtoid ua X Y e) โปยน)) โปยน โ idtofun-eqtoid-โปยน ua e

transport-is-pre-comp' : (ua : is-univalent ๐ค)
                       โ {X X' Y : ๐ค ฬ } (e : X โ X') (g : X โ Y)
                       โ transport (ฮป - โ - โ Y) (eqtoid ua X X' e) g โก g โ โ e โโปยน
transport-is-pre-comp' ua {X} {X'} e g = transport-is-pre-comp (eqtoid ua X X' e) g โ q
 where
  b : Idtofun ((eqtoid ua X X' e)โปยน) โก Idtofun (eqtoid ua X' X (โ-sym e))
  b = ap Idtofun (eqtoid-inverse ua e)
  c : Idtofun (eqtoid ua X' X (โ-sym e)) โก prโ (โ-sym e)
  c = ap prโ (idtoeq'-eqtoid ua X' X (โ-sym e))
  q : g โ Idtofun ((eqtoid ua X X' e)โปยน) โก g โ prโ (โ-sym e)
  q = ap (g โ_) (b โ c)

\end{code}

A public, improved version JEq of JEq' is provided below.

Conversely, if the induction principle for equivalences holds, then
univalence follows. In this construction, the parametric universe V is
instantiated to the universe U and its successor ๐ค โบ only. This was
produced 18th May 2018 while visiting the Hausdorff Research Institute
for Mathematics in Bonn.

The following is an adaptation of an 'improvement method' I learned
from Peter Lumsdaine, 7 July 2017, when we were both visiting the
Newton Institute. His original version translated to Agda is here:
http://www.cs.bham.ac.uk/~mhe/TypeTopology/Lumsdaine.html

Unfortunately, we couldn't use his result off-the-shelf. The main
difference is that Peter works with a global identity system on all
types (of a universe), whereas we work with an identity system on a
single type, namely a universe. As a result, we can't define the
type of left-cancellable maps using the notion of equality given by
the identity system, as Peter does. Instead, we define it using the
native (Martin-Loef) identity type, and with this little
modification, Peter's argument goes through for the situation
considered here.

\begin{code}

JEq-improve : โ {๐ค ๐ฅ}
            โ (jeq' : โ-induction ๐ค ๐ฅ)
            โ ฮฃ jeq ๊ โ-induction ๐ค ๐ฅ , ((X : ๐ค ฬ ) (A : (Y : ๐ค ฬ ) โ X โ Y โ ๐ฅ ฬ ) (b : A X (โ-refl X))
                                      โ jeq X A b X (โ-refl X) โก b)
JEq-improve {๐ค} {๐ฅ} jeq' = jeq , jeq-comp
 where
  module _ (X : ๐ค ฬ ) (A : (Y : ๐ค ฬ ) โ X โ Y โ ๐ฅ ฬ ) where
   g : {Y Z : ๐ค ฬ } (p : X โ Y) (q : X โ Z) โ ฮฃ f ๊ (A Y p โ A Z q) , left-cancellable f
   g {Y} {Z} p q = jeq' X B b Z q
    where
     B : (T : ๐ค ฬ ) โ X โ T โ ๐ฅ ฬ
     B T q = ฮฃ f ๊ (A Y p โ A T q) , left-cancellable f
     C : (T : ๐ค ฬ ) โ X โ T โ ๐ฅ ฬ
     C T p = ฮฃ f ๊ (A T p โ A X (โ-refl X)), left-cancellable f
     b : B X (โ-refl X)
     b = jeq' X C ((ฮป a โ a) , ฮป p โ p) _ p

   h : (b : A X (โ-refl X)) {Y : ๐ค ฬ } (p : X โ Y)
     โ ฮฃ a ๊ A Y p , prโ (g p p) a โก prโ (g (โ-refl X) p) b
   h b p = jeq' X B (b , refl) _ p
    where
     B : (Y : ๐ค ฬ ) (p : X โ Y) โ ๐ฅ ฬ
     B Y p = ฮฃ a ๊ A Y p , prโ (g p p) a โก prโ (g (โ-refl X) p) b

   jeq : A X (โ-refl X) โ (Y : ๐ค ฬ ) (p : X โ Y) โ A Y p
   jeq b Y p = prโ (h b p)

   jeq-comp : (b : A X (โ-refl X)) โ jeq b X (โ-refl X) โก b
   jeq-comp b = prโ (g (โ-refl X) (โ-refl X)) (prโ (h b (โ-refl X)))

\end{code}

This is the end of Peter's construction, which we apply to our problem
as follows:

\begin{code}

JEq-converse :(โ {๐ฅ} โ โ-induction ๐ค ๐ฅ) โ is-univalent ๐ค
JEq-converse {๐ค} jeq' X = ฮณ
 where
  jeq : โ {๐ฅ} โ โ-induction ๐ค ๐ฅ
  jeq {๐ฅ} = prโ (JEq-improve (jeq' {๐ฅ}))
  jeq-comp : โ {๐ฅ} (X : ๐ค ฬ ) (A : (Y : ๐ค ฬ ) โ X โ Y โ ๐ฅ ฬ ) (b : A X (โ-refl X))
          โ jeq X A b X (โ-refl X) โก b
  jeq-comp {๐ฅ} = prโ (JEq-improve (jeq' {๐ฅ}))
  ฯ : (Y : ๐ค ฬ ) โ X โ Y โ X โก Y
  ฯ = jeq X (ฮป Y p โ X โก Y) refl
  ฯc : ฯ X (โ-refl X) โก refl
  ฯc = jeq-comp X (ฮป Y p โ X โก Y) refl
  idtoeqฯ : (Y : ๐ค ฬ ) (e : X โ Y) โ idtoeq X Y (ฯ Y e) โก e
  idtoeqฯ = jeq X (ฮป Y e โ idtoeq X Y (ฯ Y e) โก e) (ap (idtoeq X X) ฯc)
  ฯidtoeq : (Y : ๐ค ฬ ) (p : X โก Y) โ ฯ Y (idtoeq X Y p) โก p
  ฯidtoeq X refl = ฯc
  ฮณ : (Y : ๐ค ฬ ) โ is-equiv(idtoeq X Y)
  ฮณ Y =  (ฯ Y , idtoeqฯ Y) , (ฯ Y , ฯidtoeq Y)

\end{code}

This completes the deduction of univalence from equivalence. Now we
improve our original JEq', to get the computation rule for free (even
if the computation rule holds for the original JEq').

\begin{code}

JEq : is-univalent ๐ค โ โ {๐ฅ} โ โ-induction ๐ค ๐ฅ
JEq ua = prโ (JEq-improve (JEq' ua))

JEq-comp : (ua : is-univalent ๐ค) (X : ๐ค ฬ ) (A : (Y : ๐ค ฬ ) โ X โ Y โ ๐ฅ ฬ ) (b : A X (โ-refl X))
         โ JEq ua X A b X (โ-refl X) โก b
JEq-comp ua = prโ (JEq-improve (JEq' ua))

\end{code}

A much more transparent and shorter construction of JEq and JEq-comp
is in my MGS'2019 lecture notes and in the module
MGS-Equivalence-induction.

\begin{code}

โ-transport : is-univalent ๐ค
            โ โ {๐ฅ} (A : ๐ค ฬ โ ๐ฅ ฬ ) {X Y : ๐ค ฬ } โ X โ Y โ A X โ A Y
โ-transport {๐ค} ua {๐ฅ} A {X} {Y} e a = JEq ua X (ฮป Z e โ A Z) a Y e

โ-induction' : (๐ค ๐ฅ : Universe) โ (๐ค โ ๐ฅ)โบ ฬ
โ-induction' ๐ค  ๐ฅ = (A : (X Y : ๐ค ฬ ) โ X โ Y โ ๐ฅ ฬ )
                 โ ((X : ๐ค ฬ ) โ A X X (โ-refl X)) โ (X Y : ๐ค ฬ ) (e : X โ Y) โ A X Y e

JEqUnbased : is-univalent ๐ค โ โ {๐ฅ} โ โ-induction' ๐ค ๐ฅ
JEqUnbased ua A f X = JEq ua X (ฮป Y โ A X Y) (f X)

\end{code}

The following technical lemma is needed elsewhere.

\begin{code}

is-univalent-idtoeq-lc : is-univalent ๐ค โ (X Y : ๐ค ฬ ) โ left-cancellable(idtoeq X Y)
is-univalent-idtoeq-lc ua X Y = section-lc (idtoeq X Y) (prโ (ua X Y))

\end{code}

The following has a proof from function extensionality, but it has a
more direct proof from equivalence induction (we also give a proof
without univalence elsewhere, of course):

\begin{code}

equivs-are-vv-equivs' : is-univalent ๐ค โ {X Y : ๐ค ฬ } (f : X โ Y)
                      โ is-equiv f โ is-vv-equiv f
equivs-are-vv-equivs' {๐ค} ua {X} {Y} f ise = g Y (f , ise)
 where
  A : (Y : ๐ค ฬ ) โ X โ Y โ ๐ค ฬ
  A Y (f , ise) = is-vv-equiv f
  b : A X (โ-refl X)
  b = singleton-types'-are-singletons
  g : (Y : ๐ค ฬ ) (e : X โ Y) โ A Y e
  g = JEq ua X A b


univalence-gives-propext : is-univalent ๐ค โ propext ๐ค
univalence-gives-propext ua {P} {Q} i j f g = eqtoid ua P Q
                                       (f ,
                                       (g , (ฮป y โ j (f (g y)) y)) ,
                                       (g , (ฮป x โ i (g (f x)) x)))

Univalence-gives-PropExt : Univalence โ PropExt
Univalence-gives-PropExt ua ๐ค = univalence-gives-propext (ua ๐ค)

Univalence-gives-Prop-Ext : Univalence โ Prop-Ext
Univalence-gives-Prop-Ext ua {๐ค} = univalence-gives-propext (ua ๐ค)

\end{code}

If the identity function satisfies some property, then all
equivalences do, assuming univalence. This property need not be
prop valued.

\begin{code}

equiv-induction : is-univalent ๐ค
               โ (X : ๐ค ฬ )
               โ (P : (Y : ๐ค ฬ ) โ (X โ Y) โ ๐ฅ ฬ )
               โ P X id
               โ (Y : ๐ค ฬ ) (f : X โ Y) โ is-equiv f โ P Y f
equiv-induction {๐ค} {๐ฅ} ua X P b Y f e = JEq ua X A b Y (f , e)
 where
  A : (Y : ๐ค ฬ ) โ X โ Y โ ๐ฅ ฬ
  A Y (f , _) = P Y f

\end{code}
