Tom de Jong, 1-18 March 2021

We show that the induction principle for ๐ยน with propositional computation rules
follows from the universal property of ๐ยน.

This is claimed at the end of Section 6.2 in the HoTT Book and follows from a
general result by Sojakova in her PhD Thesis "Higher Inductive Types as
Homotopy-Initial Algebras" (CMU-CS-16-125). The proof of the general result is
quite complicated (see for instance Lemma 105 in the PhD thesis) and the
development below offers an alternative proof for ๐ยน.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base

open import UF-Equiv
open import UF-FunExt
open import UF-Subsingletons


module CircleInduction where

\end{code}

First some preliminaries on the free loop space.

\begin{code}

๐ : (X : ๐ค ฬ ) โ ๐ค ฬ
๐ X = ฮฃ x ๊ X , x โก x

๐-functor : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } (f : X โ Y) โ ๐ X โ ๐ Y
๐-functor f (x , p) = f x , ap f p

๐-functor-id : {X : ๐ค ฬ } โ ๐-functor id โผ id {๐ค} {๐ X}
๐-functor-id {๐ค} {X} (x , p) = to-ฮฃ-โก (refl , ฮณ p)
 where
  ฮณ : {y z : X} (q : y โก z) โ transport (ฮป - โ y โก -) q refl โก q
  ฮณ refl = refl

๐-functor-comp : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } {Z : ๐ฆ ฬ } (f : X โ Y) (g : Y โ Z)
               โ ๐-functor g โ ๐-functor f โผ ๐-functor (g โ f)
๐-functor-comp f g (x , p) = to-ฮฃ-โก (refl , (ap-ap f g p))

ap-๐-functor-lemma : {A : ๐ค ฬ } {B : ๐ฅ ฬ } (f g : A โ B)
                     {a : A} (p : a โก a) {b : B} (q : b โก b)
                     (u : ๐-functor f (a , p) โก (b , q))
                     (v : ๐-functor g (a , p) โก (b , q))
                     (w : (f , u) โก (g , v))
                   โ ap (ฮป - โ ๐-functor - (a , p)) (ap prโ w) โก u โ v โปยน
ap-๐-functor-lemma f g p q refl v refl = refl

happly-๐-functor-lemma : {A : ๐ค ฬ } {B : ๐ฅ ฬ } (f g : A โ B)
                         {a : A} (p : a โก a) {b : B} (q : b โก b)
                         (u : ๐-functor f (a , p) โก (b , q))
                         (v : ๐-functor g (a , p) โก (b , q))
                         (w : (f , u) โก (g , v))
                       โ happly (ap prโ w) a โก (ap prโ u) โ (ap prโ v) โปยน
happly-๐-functor-lemma f g p q refl v refl = refl

\end{code}

Next we introduce the circle ๐ยน with its point base, its loop at base and its
universal property.

\begin{code}

module _
        (๐ยน : ๐ค ฬ )
        (base : ๐ยน)
        (loop : base โก base)
       where

 ๐ยน-universal-map : (A : ๐ฅ ฬ )
                  โ (๐ยน โ A) โ ๐ A
 ๐ยน-universal-map A f = (f base , ap f loop)

 module _
         (๐ยน-universal-property : {๐ฅ : Universe} (A : ๐ฅ ฬ )
                                โ is-equiv (๐ยน-universal-map A))
        where

  ๐ยน-uniqueness-principle : {A : ๐ฅ ฬ } (a : A) (p : a โก a)
                          โ โ! r ๊ (๐ยน โ A) , (r base , ap r loop) โก (a , p)
  ๐ยน-uniqueness-principle {๐ฅ} {A} a p =
    equivs-are-vv-equivs (๐ยน-universal-map A)
                         (๐ยน-universal-property A) (a , p)

  ๐ยน-at-most-one-function : {A : ๐ฅ ฬ } (a : A) (p : a โก a)
                          โ is-prop (ฮฃ r ๊ (๐ยน โ A) , (r base , ap r loop) โก (a , p))
  ๐ยน-at-most-one-function a p = singletons-are-props (๐ยน-uniqueness-principle a p)

\end{code}

The recursion principle for ๐ยน with its computation rule follows immediately
from the universal property of ๐ยน.

\begin{code}

  ๐ยน-rec : {A : ๐ฅ ฬ } (a : A) (p : a โก a)
         โ ๐ยน โ A
  ๐ยน-rec {๐ฅ} {A} a p = โ!-witness (๐ยน-uniqueness-principle a p)

  ๐ยน-rec-comp : {A : ๐ฅ ฬ } (a : A) (p : a โก a)
              โ ๐-functor (๐ยน-rec a p) (base , loop) โก[ ๐ A ] (a , p)
  ๐ยน-rec-comp {๐ฅ} {A} a p = โ!-is-witness (๐ยน-uniqueness-principle a p)

  ๐ยน-rec-on-base : {A : ๐ฅ ฬ } (a : A) (p : a โก a)
                  โ ๐ยน-rec a p base โก a
  ๐ยน-rec-on-base a p = ap prโ (๐ยน-rec-comp a p)

  ๐ยน-rec-on-loop : {A : ๐ฅ ฬ } (a : A) (p : a โก a)
                 โ transport (ฮป - โ - โก -) (๐ยน-rec-on-base a p)
                     (ap (๐ยน-rec a p) loop)
                 โก p
  ๐ยน-rec-on-loop a p = from-ฮฃ-โก' (๐ยน-rec-comp a p)

\end{code}

The induction principle for ๐ยน also follows quite directly. The idea is to turn
a type family A over ๐ยน to the type ฮฃ A and consider a nondependent map ๐ยน โ ฮฃ A
as a substitute for the dependent function (x : ๐ยน) โ A x.

What is significantly harder is showing that it obeys the computation rules.

\begin{code}

  module ๐ยน-induction
          (A : ๐ยน โ ๐ฅ ฬ )
          (a : A base)
          (l : transport A loop a โก a)
         where

   lโบ : (base , a) โก[ ฮฃ A ] (base , a)
   lโบ = to-ฮฃ-โก (loop , l)

   r : ๐ยน โ ฮฃ A
   r = ๐ยน-rec (base , a) lโบ

\end{code}

Next we show that r is a retraction of prโ : ฮฃ A โ ๐ยน. This tells us that
r (x) = (x , prโ (r x)), so that we can define ๐ยน-induction by transport.

\begin{code}

   r-retraction-lemma : ๐-functor (prโ โ r) (base , loop) โก[ ๐ ๐ยน ] (base , loop)
   r-retraction-lemma =
    ((prโ โ r) base , ap (prโ โ r) loop) โกโจ I   โฉ
    ๐-functor prโ (r base , ap r loop)   โกโจ II  โฉ
    (base , ap prโ (to-ฮฃ-โก (loop , l)))  โกโจ III โฉ
    (base , loop)                        โ
     where
      I   = to-ฮฃ-โก (refl , ((ap-ap r prโ loop) โปยน))
      II  = ap (๐-functor prโ) (๐ยน-rec-comp (base , a) lโบ)
      III = to-ฮฃ-โก (refl , (ap-prโ-to-ฮฃ-โก (loop , l)))

   r-is-retraction-of-prโ : prโ โ r โก id
   r-is-retraction-of-prโ = ap prโ (๐ยน-at-most-one-function base loop
                                     (prโ โ r , r-retraction-lemma)
                                     (id , to-ฮฃ-โก (refl , ap-id-is-id loop)))

   ๐ยน-induction : (x : ๐ยน) โ A x
   ๐ยน-induction x = transport A (happly r-is-retraction-of-prโ x) (prโ (r x))

\end{code}

Next we set out to prove the computation rules for ๐ยน-induction.

\begin{code}

   ฯ : ๐ยน โ ฮฃ A
   ฯ x = (x , ๐ยน-induction x)

   r-comp : (r base , ap r loop) โก[ ๐ (ฮฃ A) ] ((base , a) , lโบ)
   r-comp = ๐ยน-rec-comp (base , a) lโบ

   ฯ-r-homotopy : ฯ โผ r
   ฯ-r-homotopy x = to-ฮฃ-โก ((ฮณโ โปยน) , ฮณโ)
    where
     ฮณโ : prโ (r x) โก prโ (ฯ x)
     ฮณโ = happly r-is-retraction-of-prโ x
     ฮณโ = transport A (ฮณโ โปยน) (prโ (ฯ x))                  โกโจ refl โฉ
          transport A (ฮณโ โปยน) (transport A ฮณโ (prโ (r x))) โกโจ I    โฉ
          transport A (ฮณโ โ ฮณโ โปยน) (prโ (r x))             โกโจ II   โฉ
          transport A refl (prโ (r x))                     โกโจ refl โฉ
          prโ (r x)                                        โ
      where
       I  = (transport-โ A ฮณโ (ฮณโ โปยน)) โปยน
       II = ap (ฮป - โ transport A - (prโ (r x))) ((right-inverse ฮณโ) โปยน)

   ฯ-and-r-on-base-and-loop : (ฯ base , ap ฯ loop) โก[ ๐ (ฮฃ A) ] (r base , ap r loop)
   ฯ-and-r-on-base-and-loop = to-ฮฃ-โก (ฯ-r-homotopy base , ฮณ)
    where
     ฮณ = transport (ฮป - โ - โก -) (ฯ-r-homotopy base) (ap ฯ loop) โกโจ I  โฉ
         ฯ-r-homotopy base โปยน โ ap ฯ loop โ ฯ-r-homotopy base    โกโจ II โฉ
         ap r loop                                               โ
      where
       I  = transport-along-โก (ฯ-r-homotopy base) (ap ฯ loop)
       II = homotopies-are-natural'' ฯ r ฯ-r-homotopy {base} {base} {loop}

   ฯ-comp : (ฯ base , ap ฯ loop) โก[ ๐ (ฮฃ A) ] ((base , a) , lโบ)
   ฯ-comp = ฯ-and-r-on-base-and-loop โ r-comp

\end{code}

Looking at ฯ-comp, we see that ฯ base = (base , ๐ยน-induction base) โก (base , a),
which looks promising, for if we can show that the equality in the first
component is refl, then ๐ยน-induction base โก a would follow. So that's exactly
what we do next.

\begin{code}

   ฯ-comp-lemma : ap prโ (ap prโ ฯ-comp) โก refl
   ฯ-comp-lemma =
    ap prโ (ap prโ ฯ-comp)                                          โกโจ I   โฉ
    ap (prโ โ prโ) ฯ-comp                                           โกโจ II  โฉ
    ap (prโ โ prโ) ฯ-and-r-on-base-and-loop โ ap (prโ โ prโ) r-comp โกโจ III โฉ
    p โปยน โ p                                                        โกโจ IV  โฉ
    refl                                                            โ
    where
     p = happly r-is-retraction-of-prโ base
     I   = ap-ap prโ prโ ฯ-comp
     II  = ap-โ (prโ โ prโ) ฯ-and-r-on-base-and-loop r-comp
     IV  = left-inverse p
     III = apโ _โ_ ฮณโ ฮณโ
      where
       ฮณโ : ap (prโ โ prโ) ฯ-and-r-on-base-and-loop  โก p โปยน
       ฮณโ = ap (prโ โ prโ) ฯ-and-r-on-base-and-loop  โกโจ Iโ   โฉ
            ap prโ (ap prโ ฯ-and-r-on-base-and-loop) โกโจ IIโ  โฉ
            ap prโ (ฯ-r-homotopy base)               โกโจ IIIโ โฉ
            p โปยน                                     โ
        where
         Iโ   = (ap-ap prโ prโ ฯ-and-r-on-base-and-loop) โปยน
         IIโ  = ap (ap prโ) (ap-prโ-to-ฮฃ-โก (ฯ-r-homotopy base , _))
         IIIโ = ap-prโ-to-ฮฃ-โก ((p โปยน) , _)
       ฮณโ : ap (prโ โ prโ) r-comp โก p
       ฮณโ = ฯ โปยน
        where
         ฮบ = r-retraction-lemma
         ฯ = p                                                     โกโจ Iโ    โฉ
             ap prโ ฮบ โ ap ฯ (to-ฮฃ-โก (refl , ap-id-is-id loop)) โปยน โกโจ IIโ   โฉ
             ap prโ ฮบ โ refl โปยน                                    โกโจ refl  โฉ
             ap prโ ฮบ                                              โกโจ IIIโ  โฉ
             ap prโ (ap prโ r-comp)                                โกโจ IVโ   โฉ
             ap (prโ โ prโ) r-comp                                 โ
          where
           ฯ : ๐ (๐ยน) โ ๐ยน
           ฯ = prโ
           Iโ   = happly-๐-functor-lemma (prโ โ r) id loop loop
                   ฮบ (to-ฮฃ-โก (refl , ap-id-is-id loop))
                   (๐ยน-at-most-one-function base loop
                     (prโ โ r , r-retraction-lemma)
                     (id , to-ฮฃ-โก (refl , ap-id-is-id loop)))
           IIโ  = ap (ฮป - โ ap prโ ฮบ โ - โปยน)
                   (ap-prโ-to-ฮฃ-โก {๐ค} {๐ค} {๐ยน} {ฮป - โ (- โก -)} {_} {_}
                    (refl , ap-id-is-id loop))
           IVโ  = ap-ap prโ prโ r-comp
           IIIโ = ap prโ ฮบ                        โกโจ refl โฉ
                  ap prโ (ฮบโ โ (ฮบโ โ ฮบโ))         โกโจ I'   โฉ
                  ap prโ ฮบโ โ ap prโ (ฮบโ โ ฮบโ)    โกโจ II'  โฉ
                  refl โ ap prโ (ฮบโ โ ฮบโ)         โกโจ III' โฉ
                  ap prโ (ฮบโ โ ฮบโ)                โกโจ IV'  โฉ
                  ap prโ ฮบโ โ ap prโ ฮบโ           โกโจ V'   โฉ
                  ap prโ ฮบโ โ refl                โกโจ refl โฉ
                  ap prโ ฮบโ                       โกโจ VI'  โฉ
                  ap (prโ โ ๐-functor prโ) r-comp โกโจ refl โฉ
                  ap (prโ โ prโ) r-comp           โกโจ VII' โฉ
                  ap prโ (ap prโ r-comp)          โ
                  where
                   ฮบโ = to-ฮฃ-โก (refl , ((ap-ap r prโ loop) โปยน))
                   ฮบโ = ap (๐-functor prโ) r-comp
                   ฮบโ = to-ฮฃ-โก (refl , (ap-prโ-to-ฮฃ-โก (loop , l)))
                   I'   = ap-โ prโ ฮบโ (ฮบโ โ ฮบโ)
                   II'  = ap (_โ (ap prโ (ฮบโ โ ฮบโ)))
                           (ap-prโ-to-ฮฃ-โก {๐ค} {๐ค} {๐ยน} {ฮป - โ (- โก -)} {_} {_}
                            (refl , ((ap-ap r prโ loop) โปยน)))
                   III' = refl-left-neutral
                   IV'  = ap-โ prโ ฮบโ ฮบโ
                   V'   = ap ((ap prโ ฮบโ) โ_)
                           (ap-prโ-to-ฮฃ-โก {๐ค} {๐ค} {๐ยน} {ฮป - โ (- โก -)} {_} {_}
                            (refl , ap-prโ-to-ฮฃ-โก (loop , l)))
                   VI'  = ap-ap (๐-functor prโ) prโ r-comp
                   VII' = (ap-ap prโ prโ r-comp) โปยน

   ๐ยน-induction-on-base : ๐ยน-induction base โก a
   ๐ยน-induction-on-base =
    transport (ฮป - โ transport A - (๐ยน-induction base) โก a) ฯ-comp-lemma ฮณ
     where
      ฮณ : transport A (ap prโ (ap prโ ฯ-comp)) (๐ยน-induction base) โก a
      ฮณ = from-ฮฃ-โก' (ap prโ ฯ-comp)

\end{code}

This takes care of the first computation rule for ๐ยน-induction. We can
get a fairly direct proof of the second computation rule (the one for
loop) by assuming that base โก base is a set, because this tells us
that every element of loop โก loop must be refl.

We can satisfy this assumption for our intended application (see
CircleConstruction.lagda), because for the construction involving โค-torsors it's
is quite easy to prove that base โก base is a set.

However, for completeness sake, below we also show that assuming function
extensionality and univalence, it is possible to prove that base โก base is a
set, by using both computation rules for ๐ยน-rec and the first computation rule
for ๐ยน-induction.

\begin{code}

   ๐ยน-induction-on-loop-lemma : (loop , transport (ฮป - โ transport A loop - โก -)
                                         ๐ยน-induction-on-base
                                         (apd ๐ยน-induction loop))
                              โก (loop , l)
   ๐ยน-induction-on-loop-lemma =
      (fromto-ฮฃ-โก (loop , transport (ฮป - โ transport A loop - โก -) ฯ ฯ)) โปยน
    โ (ap from-ฮฃ-โก ฮณ) โ (fromto-ฮฃ-โก (loop , l))
     where
      ฯ = ๐ยน-induction-on-base
      ฯ = apd ๐ยน-induction loop
      ฮณ : to-ฮฃ-โก (loop , transport (ฮป - โ transport A loop - โก -) ฯ ฯ)
        โก to-ฮฃ-โก (loop , l)
      ฮณ = to-ฮฃ-โก (loop , transport (ฮป - โ transport A loop - โก -) ฯ ฯ)    โกโจ I   โฉ
          transport (ฮป - โ - โก -) (to-ฮฃ-โก (refl , ฯ)) (to-ฮฃ-โก (loop , ฯ)) โกโจ II  โฉ
          transport (ฮป - โ - โก -) (ap prโ ฯ-comp) (to-ฮฃ-โก (loop , ฯ))     โกโจ III โฉ
          transport (ฮป - โ - โก -) (ap prโ ฯ-comp) (ap ฯ loop)             โกโจ IV  โฉ
          to-ฮฃ-โก (loop , l)                                               โ
       where
        I   = h loop ฯ ฯ
         where
          h : {X : ๐ฆ ฬ } {Y : X โ ๐ฃ ฬ } {x : X} (p : x โก x) {y y' : Y x}
              (q : y โก y') (q' : transport Y p y โก y)
            โ to-ฮฃ-โก (p , transport (ฮป - โ transport Y p - โก -) q q')
            โก transport (ฮป - โ - โก -) (to-ฮฃ-โก (refl , q)) (to-ฮฃ-โก (p , q'))
          h p refl q' = refl
        II  = ap (ฮป - โ transport (ฮป - โ - โก -) - (to-ฮฃ-โก (loop , ฯ))) h
         where
          h = to-ฮฃ-โก (refl , ฯ)                 โกโจ I'  โฉ
              to-ฮฃ-โก (from-ฮฃ-โก (ap prโ ฯ-comp)) โกโจ II' โฉ
              ap prโ ฯ-comp                     โ
           where
            I'  = (ap to-ฮฃ-โก (to-ฮฃ-โก (ฯ-comp-lemma , refl))) โปยน
            II' = tofrom-ฮฃ-โก (ap prโ ฯ-comp)
        III = ap (transport (ฮป - โ - โก -) (ap prโ ฯ-comp)) (h ๐ยน-induction loop)
         where
          h : {X : ๐ฆ ฬ } {Y : X โ ๐ฃ ฬ } (f : (x : X) โ Y x)
              {x x' : X} (p : x โก x')
            โ to-ฮฃ-โก (p , apd f p) โก ap (ฮป x โ (x , f x)) p
          h f refl = refl
        IV  = from-ฮฃ-โก' ฯ-comp

   module _
           (base-sethood : is-set (base โก base))
          where

    ๐ยน-induction-on-loop : transport (ฮป - โ transport A loop - โก -)
                            ๐ยน-induction-on-base (apd ๐ยน-induction loop)
                         โก l
    ๐ยน-induction-on-loop =
     ap-prโ-refl-lemma (ฮป - โ transport A - a โก a) ๐ยน-induction-on-loop-lemma ฮณ
     where
      ฮณ : ap prโ ๐ยน-induction-on-loop-lemma โก refl
      ฮณ = base-sethood (ap prโ ๐ยน-induction-on-loop-lemma) refl

    ๐ยน-induction-comp : (๐ยน-induction base , apd ๐ยน-induction loop)
                      โก[ ฮฃ y ๊ A base , transport A loop y โก y ] (a , l)
    ๐ยน-induction-comp = to-ฮฃ-โก (๐ยน-induction-on-base , ๐ยน-induction-on-loop)

\end{code}

As promised above, here follows a proof, assuming function
extensionality and univalence, that base โก base is a set, using both
computation rules for ๐ยน-rec and the first computation rule for
๐ยน-induction.

The proof uses the encode-decode method (Section 8.1.4 of the HoTT
Book) to show that base โก base is a retract of โค. Since sets are
closed under retracts, the claim follows.

\begin{code}

  open import Integers
  open import Integers-Properties

  open import UF-Univalence

  module _
          (ua : is-univalent ๐คโ)
         where

   succ-โค-โก : โค โก โค
   succ-โค-โก = eqtoid ua โค โค succ-โค-โ

   code : ๐ยน โ ๐คโ ฬ
   code = ๐ยน-rec โค succ-โค-โก

\end{code}

   Using the first computation rule for ๐ยน-rec:

\begin{code}

   code-on-base : code base โก โค
   code-on-base = ๐ยน-rec-on-base โค succ-โค-โก

   โค-to-code-base : โค โ code base
   โค-to-code-base = Idtofun (code-on-base โปยน)

   code-base-to-โค : code base โ โค
   code-base-to-โค = Idtofun code-on-base

   transport-code-loop-is-succ-โค : code-base-to-โค
                                 โ transport code loop
                                 โ โค-to-code-base
                                 โก succ-โค
   transport-code-loop-is-succ-โค =
    ฮด โ transport code loop โ ฮต                  โกโจ I    โฉ
    ฮด โ transport id acl โ ฮต                     โกโจ refl โฉ
    Idtofun cob โ Idtofun acl โ Idtofun (cob โปยน) โกโจ II   โฉ
    Idtofun cob โ Idtofun (cob โปยน โ acl)         โกโจ III  โฉ
    Idtofun (cob โปยน โ acl โ cob)                 โกโจ IV   โฉ
    Idtofun succ-โค-โก                             โกโจ V    โฉ
    succ-โค                                       โ
     where
      cob = code-on-base
      acl = ap code loop
      ฮต = โค-to-code-base
      ฮด = code-base-to-โค
      I   = ap (ฮป - โ ฮด โ - โ ฮต) (transport-ap' id code loop)
      II  = ap (_โ_ (Idtofun cob)) ((Idtofun-โ ua (cob โปยน) acl) โปยน)
      III = (Idtofun-โ ua (cob โปยน โ acl) cob) โปยน

\end{code}

      Using the second computation rule for ๐ยน-rec

\begin{code}

      IV  = ap Idtofun ((transport-along-โก cob acl) โปยน
                       โ (๐ยน-rec-on-loop โค succ-โค-โก))
      V   = Idtofun-eqtoid ua succ-โค-โ

   transport-code-loopโปยน-is-pred-โค : code-base-to-โค
                                   โ transport code (loop โปยน)
                                   โ โค-to-code-base
                                   โผ pred-โค
   transport-code-loopโปยน-is-pred-โค x = equivs-are-lc succ-โค succ-โค-is-equiv ฮณ
    where
     ฮณ : (succ-โค โ code-base-to-โค โ transport code (loop โปยน) โ โค-to-code-base) x
       โก (succ-โค โ pred-โค) x
     ฮณ = (succ-โค โ ฮด โ tโปยน โ ฮต) x    โกโจ I   โฉ
         (ฮด โ t โ ฮต โ ฮด โ tโปยน โ ฮต) x โกโจ II  โฉ
         (ฮด โ t โ tโปยน โ ฮต) x         โกโจ III โฉ
         (ฮด โ ฮต) x                   โกโจ IV  โฉ
         x                           โกโจ V   โฉ
         (succ-โค โ pred-โค) x         โ
      where
       ฮต = โค-to-code-base
       ฮด = code-base-to-โค
       tโปยน = transport code (loop โปยน)
       t   = transport code loop
       I   = happly (transport-code-loop-is-succ-โค โปยน) ((ฮด โ tโปยน โ ฮต) x)
       II  = ap (ฮด โ t) (Idtofun-section code-on-base (tโปยน (ฮต x)))
       III = ap ฮด (back-and-forth-transport loop)
       IV  = Idtofun-retraction code-on-base x
       V   = (succ-โค-is-retraction x) โปยน

   transport-code-loopโปยน-is-pred-โค' : transport code (loop โปยน)
                                    โผ โค-to-code-base โ pred-โค โ code-base-to-โค
   transport-code-loopโปยน-is-pred-โค' x =
    transport code (loop โปยน) x                   โกโจ I   โฉ
    (ฮต โ ฮด โ transport code (loop โปยน)) x         โกโจ II  โฉ
    (ฮต โ ฮด โ transport code (loop โปยน) โ ฮต โ ฮด) x โกโจ III โฉ
    (ฮต โ pred-โค โ ฮด) x                           โ
     where
      ฮต = โค-to-code-base
      ฮด = code-base-to-โค
      I   = (Idtofun-section code-on-base (transport code (loop โปยน) x)) โปยน
      II  = ap (ฮต โ ฮด โ transport code (loop โปยน))
             ((Idtofun-section code-on-base x) โปยน)
      III = ap ฮต (transport-code-loopโปยน-is-pred-โค (ฮด x))

   encode : (x : ๐ยน) โ (base โก x) โ code x
   encode x p = transport code p (โค-to-code-base ๐)

   iterated-path : {X : ๐ฆ ฬ } {x : X} โ x โก x โ โ โ x โก x
   iterated-path p zero     = refl
   iterated-path p (succ n) = p โ iterated-path p n

   iterated-path-comm : {X : ๐ฆ ฬ } {x : X} (p : x โก x) (n : โ)
                      โ iterated-path p n โ p โก p โ iterated-path p n
   iterated-path-comm p zero = refl โ p โกโจ refl-left-neutral โฉ
                               p        โกโจ refl              โฉ
                               p โ refl โ
   iterated-path-comm p (succ n) = p โ iterated-path p n โ p   โกโจ I  โฉ
                                   p โ (iterated-path p n โ p) โกโจ II โฉ
                                   p โ (p โ iterated-path p n) โ
    where
     I  =  โassoc p (iterated-path p n) p
     II = ap (p โ_) (iterated-path-comm p n)

   loops : โค โ base โก base
   loops ๐       = refl
   loops (pos n) = iterated-path loop (succ n)
   loops (neg n) = iterated-path (loop โปยน) (succ n)

   module _
           (fe : funext ๐คโ ๐ค)
          where

    open import UF-Lower-FunExt

    loops-lemma : (_โ loop) โ loops โ pred-โค โก loops
    loops-lemma = dfunext fe h
     where
      h : (k : โค) โ loops (pred-โค k) โ loop โก loops k
      h ๐ = loop โปยน โ refl โ loop โกโจ refl              โฉ
            loop โปยน โ loop        โกโจ left-inverse loop โฉ
            refl                  โ
      h (pos n) = g n
       where
        g : (n : โ) โ loops (pred-โค (pos n)) โ loop โก loops (pos n)
        g zero     = iterated-path-comm loop zero
        g (succ n) = iterated-path-comm loop (succ n)
      h (neg n) =
       loop โปยน โ (loop โปยน โ iterated-path (loop โปยน) n) โ loop โกโจ I'   โฉ
       loop โปยน โ (iterated-path (loop โปยน) n โ loop โปยน) โ loop โกโจ II'  โฉ
       loop โปยน โ iterated-path (loop โปยน) n โ (loop โปยน โ loop) โกโจ III' โฉ
       loop โปยน โ iterated-path (loop โปยน) n                    โ
        where
         I'   = ap (ฮป - โ loop โปยน โ - โ loop)
                 ((iterated-path-comm (loop โปยน) n) โปยน)
         II'  = โassoc (loop โปยน) (iterated-path (loop โปยน) n โ loop โปยน) loop
              โ ap (loop โปยน โ_)
                 (โassoc (iterated-path (loop โปยน) n) (loop โปยน) loop)
              โ (โassoc (loop โปยน) (iterated-path (loop โปยน) n)
                  (loop โปยน โ loop)) โปยน
         III' = ap ((loop โปยน โ iterated-path (loop โปยน) n) โ_)
                 (left-inverse loop)

    transport-loops-lemma : transport (ฮป - โ code - โ base โก -) loop
                             (loops โ code-base-to-โค)
                          โก (loops โ code-base-to-โค)
    transport-loops-lemma =
     transport (ฮป - โ code - โ base โก -) loop f                     โกโจ I   โฉ
     transport (ฮป - โ base โก -) loop โ f โ transport code (loop โปยน) โกโจ II  โฉ
     (_โ loop) โ f โ transport code (loop โปยน)                       โกโจ III โฉ
     (_โ loop) โ loops โ ฮด โ ฮต โ pred-โค โ ฮด                         โกโจ IV  โฉ
     (_โ loop) โ loops โ pred-โค โ ฮด                                 โกโจ V   โฉ
     loops โ ฮด                                                      โ
      where
       ฮต : โค โ code base
       ฮต = โค-to-code-base
       ฮด : code base โ โค
       ฮด = code-base-to-โค
       f : code base โ base โก base
       f = loops โ ฮด
       I   = transport-along-โ code (_โก_ base) loop f
       II  = refl
       III = ap ((_โ loop) โ f โ_)
              (dfunext (lower-funext ๐คโ ๐ค fe) transport-code-loopโปยน-is-pred-โค')
       IV  = ap (ฮป - โ (_โ loop) โ loops โ - โ pred-โค โ ฮด)
              (dfunext (lower-funext ๐คโ ๐ค fe) (Idtofun-retraction code-on-base))
       V   = ap (_โ ฮด) loops-lemma


    open ๐ยน-induction (ฮป - โ code - โ base โก -)
                      (loops โ code-base-to-โค)
                      transport-loops-lemma

    decode : (x : ๐ยน) โ code x โ base โก x
    decode = ๐ยน-induction

    decode-encode : (x : ๐ยน) (p : base โก x) โ decode x (encode x p) โก p
    decode-encode base refl =
     decode base (encode base refl)                       โกโจ refl โฉ
     decode base (transport code refl (โค-to-code-base ๐)) โกโจ refl โฉ
     decode base (โค-to-code-base ๐)                       โกโจ I    โฉ
     loops (code-base-to-โค (โค-to-code-base ๐))            โกโจ II   โฉ
     loops ๐                                              โกโจ refl โฉ
     refl                                                 โ
      where

\end{code}

       Using the first computation rule for ๐ยน-induction

\begin{code}

       I  = happly ๐ยน-induction-on-base (โค-to-code-base ๐)
       II = ap loops (Idtofun-retraction code-on-base ๐)

    open import UF-Retracts

    ฮฉ๐ยน-is-set : is-set (base โก base)
    ฮฉ๐ยน-is-set = subtypes-of-sets-are-sets (encode base)
                  (sections-are-lc (encode base)
                   ((decode base) , (decode-encode base)))
                   (transport is-set (code-on-base โปยน) โค-is-set)

  module ๐ยน-induction'
          {๐ฅ : Universe}
          (A : ๐ยน โ ๐ฅ ฬ )
          (a : A base)
          (l : transport A loop a โก a)
          (fe : funext ๐คโ ๐ค)
          (ua : is-univalent ๐คโ)
         where

   open ๐ยน-induction A a l

   ๐ยน-induction-on-loop' : transport (ฮป - โ transport A loop - โก -)
                            ๐ยน-induction-on-base (apd ๐ยน-induction loop)
                         โก l
   ๐ยน-induction-on-loop' = ๐ยน-induction-on-loop (ฮฉ๐ยน-is-set ua fe)

   ๐ยน-induction-comp' : (๐ยน-induction base , apd ๐ยน-induction loop)
                      โก[ ฮฃ y ๊ A base , transport A loop y โก y ] (a , l)
   ๐ยน-induction-comp' = ๐ยน-induction-comp (ฮฉ๐ยน-is-set ua fe)

\end{code}
