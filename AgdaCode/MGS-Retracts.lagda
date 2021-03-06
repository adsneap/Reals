Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module MGS-Retracts where

open import MGS-hlevels public

has-section : {X : π€ Μ } {Y : π₯ Μ } β (X β Y) β π€ β π₯ Μ
has-section r = Ξ£ s κ (codomain r β domain r), r β s βΌ id

_β_ : π€ Μ β π₯ Μ β π€ β π₯ Μ
X β Y = Ξ£ r κ (Y β X), has-section r

retraction : {X : π€ Μ } {Y : π₯ Μ } β X β Y β Y β X
retraction (r , s , Ξ·) = r

section : {X : π€ Μ } {Y : π₯ Μ } β X β Y β X β Y
section (r , s , Ξ·) = s

retract-equation : {X : π€ Μ } {Y : π₯ Μ } (Ο : X β Y)
                 β retraction Ο β section Ο βΌ ππ X

retract-equation (r , s , Ξ·) = Ξ·

retraction-has-section : {X : π€ Μ } {Y : π₯ Μ } (Ο : X β Y)
                       β has-section (retraction Ο)

retraction-has-section (r , h) = h

id-β : (X : π€ Μ ) β X β X
id-β X = ππ X , ππ X , refl

_ββ_ : {X : π€ Μ } {Y : π₯ Μ } {Z : π¦ Μ } β X β Y β Y β Z β X β Z

(r , s , Ξ·) ββ (r' , s' , Ξ·') = (r β r' , s' β s , Ξ·'')
 where
  Ξ·'' = Ξ» x β r (r' (s' (s x))) β‘β¨ ap r (Ξ·' (s x)) β©
              r (s x)           β‘β¨ Ξ· x β©
              x                 β

_ββ¨_β©_ : (X : π€ Μ ) {Y : π₯ Μ } {Z : π¦ Μ } β X β Y β Y β Z β X β Z
X ββ¨ Ο β© Ο = Ο ββ Ο

_β : (X : π€ Μ ) β X β X
X β = id-β X

Ξ£-retract : {X : π€ Μ } {A : X β π₯ Μ } {B : X β π¦ Μ }
          β ((x : X) β A x β  B x) β Ξ£ A β Ξ£ B

Ξ£-retract {π€} {π₯} {π¦} {X} {A} {B} Ο = NatΞ£ r , NatΞ£ s , Ξ·'
 where
  r : (x : X) β B x β A x
  r x = retraction (Ο x)

  s : (x : X) β A x β B x
  s x = section (Ο x)

  Ξ· : (x : X) (a : A x) β r x (s x a) β‘ a
  Ξ· x = retract-equation (Ο x)

  Ξ·' : (Ο : Ξ£ A) β NatΞ£ r (NatΞ£ s Ο) β‘ Ο
  Ξ·' (x , a) = x , r x (s x a) β‘β¨ to-Ξ£-β‘' (Ξ· x a) β©
               x , a           β

transport-is-retraction : {X : π€ Μ } (A : X β π₯ Μ ) {x y : X} (p : x β‘ y)
                        β transport A p β transport A (p β»ΒΉ) βΌ ππ (A y)

transport-is-retraction A (refl x) = refl

transport-is-section : {X : π€ Μ } (A : X β π₯ Μ ) {x y : X} (p : x β‘ y)
                     β transport A (p β»ΒΉ) β transport A p βΌ ππ (A x)

transport-is-section A (refl x) = refl

Ξ£-reindexing-retract : {X : π€ Μ } {Y : π₯ Μ } {A : X β π¦ Μ } (r : Y β X)
                     β has-section r
                     β (Ξ£ x κ X , A x) β (Ξ£ y κ Y , A (r y))

Ξ£-reindexing-retract {π€} {π₯} {π¦} {X} {Y} {A} r (s , Ξ·) = Ξ³ , Ο , Ξ³Ο
 where
  Ξ³ : Ξ£ (A β r) β Ξ£ A
  Ξ³ (y , a) = (r y , a)

  Ο : Ξ£ A β Ξ£ (A β r)
  Ο (x , a) = (s x , transport A ((Ξ· x)β»ΒΉ) a)

  Ξ³Ο : (Ο : Ξ£ A) β Ξ³ (Ο Ο) β‘ Ο
  Ξ³Ο (x , a) = p
   where
    p : (r (s x) , transport A ((Ξ· x)β»ΒΉ) a) β‘ (x , a)
    p = to-Ξ£-β‘ (Ξ· x , transport-is-retraction A (Ξ· x) a)

singleton-type : {X : π€ Μ } β X β π€ Μ
singleton-type {π€} {X} x = Ξ£ y κ X , y β‘ x

singleton-type-center : {X : π€ Μ } (x : X) β singleton-type x
singleton-type-center x = (x , refl x)

singleton-type-centered : {X : π€ Μ } (x : X) (Ο : singleton-type x)
                        β singleton-type-center x β‘ Ο

singleton-type-centered x (x , refl x) = refl (x , refl x)

singleton-types-are-singletons : (X : π€ Μ ) (x : X)
                               β is-singleton (singleton-type x)

singleton-types-are-singletons X x = singleton-type-center x ,
                                     singleton-type-centered x

retract-of-singleton : {X : π€ Μ } {Y : π₯ Μ }
                     β Y β X β is-singleton X β is-singleton Y

retract-of-singleton (r , s , Ξ·) (c , Ο) = r c , Ξ³
 where
  Ξ³ = Ξ» y β r c     β‘β¨ ap r (Ο (s y)) β©
            r (s y) β‘β¨ Ξ· y β©
            y       β

singleton-type' : {X : π€ Μ } β X β π€ Μ
singleton-type' {π€} {X} x = Ξ£ y κ X , x β‘ y

singleton-type'-center : {X : π€ Μ } (x : X) β singleton-type' x
singleton-type'-center x = (x , refl x)

singleton-type'-centered : {X : π€ Μ } (x : X) (Ο : singleton-type' x)
                         β singleton-type'-center x β‘ Ο

singleton-type'-centered x (x , refl x) = refl (x , refl x)

singleton-types'-are-singletons : (X : π€ Μ ) (x : X)
                                β is-singleton (singleton-type' x)

singleton-types'-are-singletons X x = singleton-type'-center x ,
                                      singleton-type'-centered x

infix  10 _β_
infixr  0 _ββ¨_β©_
infix   1 _β

\end{code}
