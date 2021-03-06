Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module MGS-Yoneda where

open import MGS-Unique-Existence public
open import MGS-Embeddings public

๐จ : {X : ๐ค ฬ } โ X โ (X โ ๐ค ฬ )
๐จ {๐ค} {X} = Id X

๐ : (X : ๐ค ฬ ) โ X โ (X โ ๐ค ฬ )
๐ {๐ค} X = ๐จ {๐ค} {X}

transport-lemma : {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ ) (x : X)
                โ (ฯ : Nat (๐จ x) A)
                โ (y : X) (p : x โก y) โ ฯ y p โก transport A p (ฯ x (refl x))

transport-lemma A x ฯ x (refl x) = refl (ฯ x (refl x))

๐ : {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ ) (x : X) โ Nat (๐จ x) A โ A x
๐ A x ฯ = ฯ x (refl x)

๐ : {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ ) (x : X) โ A x โ Nat (๐จ x) A
๐ A x a y p = transport A p a

yoneda-ฮท : dfunext ๐ค (๐ค โ ๐ฅ) โ dfunext ๐ค ๐ฅ
         โ {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ ) (x : X)
         โ ๐ A x โ ๐ A x โผ id

yoneda-ฮท fe fe' A x = ฮณ
 where
  ฮณ : (ฯ : Nat (๐จ x) A) โ (ฮป y p โ transport A p (ฯ x (refl x))) โก ฯ
  ฮณ ฯ = fe (ฮป y โ fe' (ฮป p โ (transport-lemma A x ฯ y p)โปยน))

yoneda-ฮต : {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ ) (x : X)
         โ ๐ A x โ ๐ A x โผ id

yoneda-ฮต A x = ฮณ
 where
  ฮณ : (a : A x) โ transport A (refl x) a โก a
  ฮณ = refl

is-fiberwise-equiv : {X : ๐ค ฬ } {A : X โ ๐ฅ ฬ } {B : X โ ๐ฆ ฬ } โ Nat A B โ ๐ค โ ๐ฅ โ ๐ฆ ฬ
is-fiberwise-equiv ฯ = โ x โ is-equiv (ฯ x)

๐-is-equiv : dfunext ๐ค (๐ค โ ๐ฅ) โ dfunext ๐ค ๐ฅ
           โ {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ )
           โ is-fiberwise-equiv (๐ A)

๐-is-equiv fe fe' A x = invertibles-are-equivs (๐ A x )
                         (๐ A x , yoneda-ฮท fe fe' A x , yoneda-ฮต A x)

๐-is-equiv : dfunext ๐ค (๐ค โ ๐ฅ) โ dfunext ๐ค ๐ฅ
           โ {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ )
           โ is-fiberwise-equiv (๐ A)

๐-is-equiv fe fe' A x = invertibles-are-equivs (๐ A x)
                         (๐ A x , yoneda-ฮต A x , yoneda-ฮท fe fe' A x)

Yoneda-Lemma : dfunext ๐ค (๐ค โ ๐ฅ) โ dfunext ๐ค ๐ฅ
             โ {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ ) (x : X)
             โ Nat (๐จ x) A โ A x

Yoneda-Lemma fe fe' A x = ๐ A x , ๐-is-equiv fe fe' A x

retract-universal-lemma : {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ ) (x : X)
                        โ ((y : X) โ A y โ (x โก y))
                        โ โ! A

retract-universal-lemma A x ฯ = i
 where
  ฯ : ฮฃ A โ singleton-type' x
  ฯ = ฮฃ-retract ฯ

  i : โ! A
  i = retract-of-singleton ฯ (singleton-types'-are-singletons (domain A) x)

fiberwise-equiv-universal : {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ )
                            (x : X) (ฯ : Nat (๐จ x) A)
                          โ is-fiberwise-equiv ฯ
                          โ โ! A

fiberwise-equiv-universal A x ฯ e = retract-universal-lemma A x ฯ
 where
  ฯ : โ y โ A y โ (x โก y)
  ฯ y = โ-gives-โท ((ฯ y) , e y)

universal-fiberwise-equiv : {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ )
                          โ โ! A
                          โ (x : X) (ฯ : Nat (๐จ x) A) โ is-fiberwise-equiv ฯ

universal-fiberwise-equiv {๐ค} {๐ฅ} {X} A u x ฯ = ฮณ
 where
  g : singleton-type' x โ ฮฃ A
  g = Natฮฃ ฯ

  e : is-equiv g
  e = maps-of-singletons-are-equivs g (singleton-types'-are-singletons X x) u

  ฮณ : is-fiberwise-equiv ฯ
  ฮณ = Natฮฃ-equiv-gives-fiberwise-equiv ฯ e

hfunextโ : hfunext ๐ค ๐ฅ
         โ ((X : ๐ค ฬ ) (A : X โ ๐ฅ ฬ ) (f : ฮ? A) โ โ! g ๊ ฮ? A , f โผ g)

hfunextโ hfe X A f = fiberwise-equiv-universal (f โผ_) f (happly f) (hfe f)

โhfunext : ((X : ๐ค ฬ ) (A : X โ ๐ฅ ฬ ) (f : ฮ? A) โ โ! g ๊ ฮ? A , f โผ g)
         โ hfunext ๐ค ๐ฅ

โhfunext ฯ {X} {A} f = universal-fiberwise-equiv (f โผ_) (ฯ X A f) f (happly f)

fiberwise-equiv-criterion : {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ )
                            (x : X)
                          โ ((y : X) โ A y โ (x โก y))
                          โ (ฯ : Nat (๐จ x) A) โ is-fiberwise-equiv ฯ

fiberwise-equiv-criterion A x ฯ ฯ = universal-fiberwise-equiv A
                                     (retract-universal-lemma A x ฯ) x ฯ

fiberwise-equiv-criterion' : {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ )
                            (x : X)
                          โ ((y : X) โ (x โก y) โ A y)
                          โ (ฯ : Nat (๐จ x) A) โ is-fiberwise-equiv ฯ

fiberwise-equiv-criterion' A x e = fiberwise-equiv-criterion A x
                                    (ฮป y โ โ-gives-โท (e y))

_โฬ_ : {X : ๐ค ฬ } โ (X โ ๐ฅ ฬ ) โ (X โ ๐ฆ ฬ ) โ ๐ค โ ๐ฅ โ ๐ฆ ฬ
A โฬ B = โ x โ A x โ B x

is-representable : {X : ๐ค ฬ } โ (X โ ๐ฅ ฬ ) โ ๐ค โ ๐ฅ ฬ
is-representable A = ฮฃ x ๊ domain A , ๐จ x โฬ A

representable-universal : {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ )
                        โ is-representable A
                        โ โ! A

representable-universal A (x , e) = retract-universal-lemma A x
                                     (ฮป x โ โ-gives-โท (e x))

universal-representable : {X : ๐ค ฬ } {A : X โ ๐ฅ ฬ }
                        โ โ! A
                        โ is-representable A

universal-representable {๐ค} {๐ฅ} {X} {A} ((x , a) , p) = x , ฯ
 where
  e : is-fiberwise-equiv (๐ A x a)
  e = universal-fiberwise-equiv A ((x , a) , p) x (๐ A x a)

  ฯ : (y : X) โ (x โก y) โ A y
  ฯ y = (๐ A x a y , e y)

fiberwise-retractions-are-equivs : {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ ) (x : X)
                                 โ (ฯ : Nat (๐จ x) A)
                                 โ ((y : X) โ has-section (ฯ y))
                                 โ is-fiberwise-equiv ฯ

fiberwise-retractions-are-equivs {๐ค} {๐ฅ} {X} A x ฯ s = ฮณ
 where
  ฯ : (y : X) โ A y โ (x โก y)
  ฯ y = ฯ y , s y

  i : โ! A
  i = retract-universal-lemma A x ฯ

  ฮณ : is-fiberwise-equiv ฯ
  ฮณ = universal-fiberwise-equiv A i x ฯ

fiberwise-โ-gives-โ : (X : ๐ค ฬ ) (A : X โ ๐ฅ ฬ ) (x : X)
                    โ ((y : X) โ A y โ (x โก y))
                    โ ((y : X) โ A y โ (x โก y))

fiberwise-โ-gives-โ X A x ฯ = ฮณ
 where
  f : (y : X) โ (x โก y) โ A y
  f y = retraction (ฯ y)

  e : is-fiberwise-equiv f
  e = fiberwise-retractions-are-equivs A x f (ฮป y โ retraction-has-section (ฯ y))

  ฮณ : (y : X) โ A y โ (x โก y)
  ฮณ y = โ-sym (f y , e y)

embedding-criterion' : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } (f : X โ Y)
                     โ ((x x' : X) โ (f x โก f x') โ (x โก x'))
                     โ is-embedding f

embedding-criterion' f ฯ = embedding-criterion f
                            (ฮป x โ fiberwise-โ-gives-โ (domain f)
                                    (ฮป - โ f x โก f -) x (ฯ x))

being-fiberwise-equiv-is-subsingleton : global-dfunext
                                      โ {X : ๐ค ฬ } {A : X โ ๐ฅ ฬ } {B : X โ ๐ฆ ฬ }
                                      โ (ฯ : Nat A B)
                                      โ is-subsingleton (is-fiberwise-equiv ฯ)

being-fiberwise-equiv-is-subsingleton fe ฯ =
 ฮ?-is-subsingleton fe (ฮป y โ being-equiv-is-subsingleton fe fe (ฯ y))

being-representable-is-subsingleton : global-dfunext
                                    โ {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ )
                                    โ is-subsingleton (is-representable A)

being-representable-is-subsingleton fe {X} A rโ rโ = ฮณ
 where
  u : โ! A
  u = representable-universal A rโ

  i : (x : X) (ฯ : Nat (๐จ x) A) โ is-singleton (is-fiberwise-equiv ฯ)
  i x ฯ = pointed-subsingletons-are-singletons
           (is-fiberwise-equiv ฯ)
           (universal-fiberwise-equiv A u x ฯ)
           (being-fiberwise-equiv-is-subsingleton fe ฯ)

  ฮต : (x : X) โ (๐จ x โฬ A) โ A x
  ฮต x = ((y : X) โ ๐จ x y โ A y)                       โโจ ฮ?ฮฃ-distr-โ โฉ
        (ฮฃ ฯ ๊ Nat (๐จ x) A , is-fiberwise-equiv ฯ)    โโจ prโ-โ (i x) โฉ
        Nat (๐จ x) A                                   โโจ Yoneda-Lemma fe fe A x โฉ
        A x                                           โ?

  ฮด : is-representable A โ ฮฃ A
  ฮด = ฮฃ-cong ฮต

  v : is-singleton (is-representable A)
  v = equiv-to-singleton ฮด u

  ฮณ : rโ โก rโ
  ฮณ = singletons-are-subsingletons (is-representable A) v rโ rโ

๐จ-is-embedding : Univalence โ (X : ๐ค ฬ ) โ is-embedding (๐ X)
๐จ-is-embedding {๐ค} ua X A = ฮณ
 where
  hfe : global-hfunext
  hfe = univalence-gives-global-hfunext ua

  dfe : global-dfunext
  dfe = univalence-gives-global-dfunext ua

  p = ฮป x โ (๐จ x โก A)                 โโจ i  x โฉ
            ((y : X) โ ๐จ x y โก A y)   โโจ ii x โฉ
            ((y : X) โ ๐จ x y โ A y)   โ?
    where
     i  = ฮป x โ (happly (๐จ x) A , hfe (๐จ x) A)
     ii = ฮป x โ ฮ?-cong dfe dfe
                 (ฮป y โ univalence-โ (ua ๐ค)
                         (๐จ x y) (A y))

  e : fiber ๐จ A โ is-representable A
  e = ฮฃ-cong p

  ฮณ : is-subsingleton (fiber ๐จ A)
  ฮณ = equiv-to-subsingleton e (being-representable-is-subsingleton dfe A)

\end{code}
