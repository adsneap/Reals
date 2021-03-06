Negation (and emptiness).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Negation where

open import Universes
open import Empty
open import Id
open import Pi
open import Plus
open import Sigma

Â¬_ : ð¤ Ì â ð¤ Ì
Â¬ A = A â ð {ð¤â}
_â¢_ : {X : ð¤ Ì } â (x y : X) â ð¤ Ì
x â¢ y = Â¬ (x â¡ y)

â¢-sym : {X : ð¤ Ì } â {x y : X} â x â¢ y â y â¢ x
â¢-sym u r = u (r â»Â¹)

is-empty : ð¤ Ì â ð¤ Ì
is-empty = Â¬_

Â¬Â¬_ : ð¤ Ì â ð¤ Ì
Â¬Â¬ A = Â¬ (Â¬ A)

is-nonempty : ð¤ Ì â ð¤ Ì
is-nonempty = Â¬Â¬_

dual : {X : ð¤ Ì } {Y : ð¥ Ì } (R : ð¦ Ì ) â (X â Y) â (Y â R) â (X â R)
dual R f p = p â f

contrapositive : {A : ð¤ Ì } {B : ð¥ Ì } â (A â B) â Â¬ B â Â¬ A
contrapositive = dual _

double-contrapositive : {A : ð¤ Ì } {B : ð¥ Ì } â (A â B) â Â¬Â¬ A â Â¬Â¬ B
double-contrapositive = contrapositive â contrapositive

Â¬Â¬-functor : {A : ð¤ Ì } {B : ð¥ Ì } â (A â B) â Â¬Â¬ A â Â¬Â¬ B
Â¬Â¬-functor = double-contrapositive

Â¬Â¬-kleisli : {A : ð¤ Ì } {B : ð¥ Ì } â (A â Â¬Â¬ B) â Â¬Â¬ A â Â¬Â¬ B
Â¬Â¬-kleisli f Ï h = Ï (Î» a â f a h)

decidable : ð¤ Ì â ð¤ Ì
decidable A = A + Â¬ A

double-negation-intro : {A : ð¤ Ì } â A â Â¬Â¬ A
double-negation-intro x u = u x

three-negations-imply-one : {A : ð¤ Ì } â Â¬ (Â¬Â¬ A) â Â¬ A
three-negations-imply-one = contrapositive double-negation-intro

dne' : {A : ð¤ Ì } {B : ð¥ Ì } â (A â B) â (Â¬Â¬ B â B) â Â¬Â¬ A â B
dne' f h Ï = h (Î» g â Ï (Î» a â g (f a)))

dne : {A : ð¤ Ì } {B : ð¥ Ì } â (A â Â¬ B) â Â¬Â¬ A â Â¬ B
dne f Ï b = Ï (Î» a â f a b)



double-negation-unshift : {X : ð¤ Ì } {A : X â ð¥ Ì } â Â¬Â¬ ((x : X) â A x) â (x : X) â Â¬Â¬ (A x)
double-negation-unshift f x g = f (Î» h â g (h x))

dnu : {A : ð¤ Ì } {B : ð¥ Ì } â Â¬Â¬ (A Ã B) â Â¬Â¬ A Ã Â¬Â¬ B
dnu Ï = (Â¬Â¬-functor prâ Ï) , (Â¬Â¬-functor prâ Ï)

und : {A : ð¤ Ì } {B : ð¥ Ì } â Â¬Â¬ A Ã Â¬Â¬ B â Â¬Â¬ (A Ã B)
und (Ï , Î³) w = Î³ (Î» y â Ï (Î» x â w (x , y)))

Â¬Â¬-stable : ð¤ Ì â ð¤ Ì
Â¬Â¬-stable A = Â¬Â¬ A â A

Â¬-is-Â¬Â¬-stable : {A : ð¤ Ì } â Â¬Â¬-stable (Â¬ A)
Â¬-is-Â¬Â¬-stable = three-negations-imply-one

Î -is-Â¬Â¬-stable : {A : ð¤ Ì } {B : A â ð¥ Ì }
               â ((a : A) â Â¬Â¬-stable (B a))
               â Â¬Â¬-stable (Î  B)
Î -is-Â¬Â¬-stable f Ï a = f a (Î» v â Ï (Î» g â v (g a)))

â-is-Â¬Â¬-stable : {A : ð¤ Ì } {B : ð¥ Ì }
               â Â¬Â¬-stable B
               â Â¬Â¬-stable (A â B)
â-is-Â¬Â¬-stable f = Î -is-Â¬Â¬-stable (Î» _ â f)

Ã-is-Â¬Â¬-stable : {A : ð¤ Ì } {B : ð¥ Ì }
               â Â¬Â¬-stable A
               â Â¬Â¬-stable B
               â Â¬Â¬-stable (A Ã B)
Ã-is-Â¬Â¬-stable f g Ï = f (Î» v â Ï (Î» (a , b) â v a)) ,
                       g (Î» v â Ï (Î» (a , b) â v b))

Double-negation-of-implicationâ : {A : ð¤ Ì } {B : ð¥ Ì }
                                  {R : ð¦ Ì } {S : ð£ Ì } {T : ð£' Ì }
                                â (((A â B) â T) â S)
                                â (((A â S) â R) Ã (B â T)) â R
Double-negation-of-implicationâ f g = prâ g (Î» a â f (Î» h â prâ g (h a)))

Double-negation-of-implicationâ : {A : ð¤ Ì } {B : ð¥ Ì }
                                  (R : ð¦ Ì ) {S : ð£ Ì } {T : ð£' Ì } {U : ð£' Ì }
                                â (S â B)
                                â ((((A â S) â T) Ã (B â T)) â U)
                                â ((A â B) â T) â U
Double-negation-of-implicationâ R k f g = f ((Î» h â g (Î» a â k (h a))) ,
                                             (Î» b â g (Î» a â b)))

double-negation-of-implicationâ : {A : ð¤ Ì } {B : ð¥ Ì } â Â¬Â¬ (A â B) â Â¬ (Â¬Â¬ A Ã Â¬ B)
double-negation-of-implicationâ = Double-negation-of-implicationâ

double-negation-of-implicationâ : {A : ð¤ Ì } {B : ð¥ Ì } â Â¬ (Â¬Â¬ A Ã Â¬ B) â Â¬Â¬ (A â B)
double-negation-of-implicationâ f g = Double-negation-of-implicationâ (ð {ð¤â}) ð-elim f g

not-Î£-implies-Î -not : {X : ð¤ Ì } {A : X â ð¥ Ì }
                    â Â¬ (Î£ x ê X , A x)
                    â (x : X) â Â¬ (A x)
not-Î£-implies-Î -not = curry

Î -not-implies-not-Î£ : {X : ð¤ Ì } {A : X â ð¥ Ì }
                    â ((x : X) â Â¬ (A x))
                    â Â¬ (Î£ x ê X , A x)
Î -not-implies-not-Î£ = uncurry

not-Î -implies-not-not-Î£' : {X : ð¤ Ì } {A : X â ð¥ Ì }
                         â Â¬ ((x : X) â Â¬Â¬ (A x))
                         â Â¬Â¬ (Î£ x ê X , Â¬ (A x))
not-Î -implies-not-not-Î£' = contrapositive not-Î£-implies-Î -not

not-Î -implies-not-not-Î£ : {X : ð¤ Ì } {A : X â ð¥ Ì }
                        â ((x : X) â Â¬Â¬ (A x) â A x)
                        â Â¬ ((x : X) â A x)
                        â Â¬Â¬ (Î£ x ê X , Â¬ (A x))
not-Î -implies-not-not-Î£ f g h = g (Î» x â f x (Î» u â h (x , u)))

\end{code}

Notation to try to make proofs readable:

\begin{code}

contradiction : ð¤â Ì
contradiction = ð

have_which-is-impossible-by_ : {A : ð¤ Ì } {B : ð¦ Ì }
                             â A â (A â ð {ð¤â}) â B
have a which-is-impossible-by Î½ = ð-elim (Î½ a)


have_which-contradicts_ : {A : ð¤ Ì } {B : ð¦ Ì }
                        â (A â ð {ð¤â}) â A â B
have Î½ which-contradicts a = ð-elim (Î½ a)

\end{code}

Fixities:

\begin{code}

infix  50 Â¬_
infix  50 Â¬Â¬_
infix  0 _â¢_

\end{code}
