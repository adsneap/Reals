This file needs reorganization and clean-up.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Base where

open import SpartanMLTT

Nat : {X : π€ Μ } β (X β π₯ Μ ) β (X β π¦ Μ ) β π€ β π₯ β π¦ Μ
Nat A B = β x β A x β B x

Nats-are-natural : {X : π€ Μ } (A : X β π₯ Μ ) (B : X β π¦ Μ )
                   (Ο : Nat A B) {x y : X} (p : x β‘ y)
                 β Ο y β transport A p β‘ transport B p β Ο x
Nats-are-natural A B Ο refl = refl

Nats-are-natural-βΌ : {X : π€ Μ } (A : X β π₯ Μ ) (B : X β π¦ Μ )
                     (Ο : Nat A B) {x y : X} (p : x β‘ y)
                   β Ο y β transport A p βΌ transport B p β Ο x
Nats-are-natural-βΌ A B Ο refl a = refl

NatΞ£ : {X : π€ Μ } {A : X β π₯ Μ } {B : X β π¦ Μ } β Nat A B β Ξ£ A β Ξ£ B
NatΞ£ ΞΆ (x , a) = (x , ΞΆ x a)

NatΞ  : {X : π€ Μ } {A : X β π₯ Μ } {B : X β π¦ Μ } β Nat A B β Ξ  A β Ξ  B
NatΞ  f g x = f x (g x) -- (S combinator from combinatory logic!)

Ξ Ξ£-distr : {X : π€ Μ } {A : X β π₯ Μ } {P : (x : X) β A x β π¦ Μ }
         β (Ξ  x κ X , Ξ£ a κ A x , P x a)
         β Ξ£ f κ Ξ  A , Ξ  x κ X , P x (f x)
Ξ Ξ£-distr Ο = (Ξ» x β prβ (Ο x)) , Ξ» x β prβ (Ο x)

Ξ Ξ£-distr-back : {X : π€ Μ } {A : X β π₯ Μ } {P : (x : X) β A x β π¦ Μ }
              β (Ξ£ f κ Ξ  A , Ξ  x κ X , P x (f x))
              β Ξ  x κ X , Ξ£ a κ A x , P x a
Ξ Ξ£-distr-back (f , Ο) x = f x , Ο x

_β_ : {X : π€ Μ } {x : X} {A : X β π₯ Μ } β Nat (Id x) A β Nat (Id x) A β π€ β π₯ Μ
Ξ· β ΞΈ = β y β Ξ· y βΌ ΞΈ y

ap-const : {X : π€ Μ } {Y : π₯ Μ } (y : Y) {x x' : X} (p : x β‘ x')
         β ap (Ξ» _ β y) p β‘ refl
ap-const y refl = refl

transport-fiber : {X : π€ Μ } {Y : π₯ Μ } (f : X β Y)
                  (x x' : X) (y : Y) (p : x β‘ x') (q : f x β‘ y)
                β transport (Ξ» - β f - β‘ y) p q β‘ ap f (p β»ΒΉ) β q
transport-fiber f x x' y refl refl = refl

transportβ : {X : π€ Μ } {Y : π₯ Μ } (A : X β Y β π¦ Μ )
             {x x' : X} {y y' : Y}
             β x β‘ x' β y β‘ y' β A x y β A x' y'
transportβ A refl refl = id

transportβ : {X : π€ Μ } {Y : π₯ Μ } {Z : π¦ Μ } (A : X β Y β Z β π£ Μ )
             {x x' : X} {y y' : Y} {z z' : Z}
           β x β‘ x' β y β‘ y' β z β‘ z' β A x y z β A x' y' z'
transportβ A refl refl refl = id

back-transportβ : {X : π€ Μ } {Y : π₯ Μ } (A : X β Y β π¦ Μ )
                  {x x' : X} {y y' : Y}
                β x β‘ x' β y β‘ y' β A x' y' β A x y
back-transportβ A refl refl = id

Idtofun : {X Y : π€ Μ } β X β‘ Y β X β Y
Idtofun = transport id

Idtofun-retraction : {X Y : π€ Μ } (p : X β‘ Y) β Idtofun p β Idtofun (p β»ΒΉ) βΌ id
Idtofun-retraction refl _ = refl

Idtofun-section : {X Y : π€ Μ } (p : X β‘ Y) β Idtofun (p β»ΒΉ) β Idtofun p βΌ id
Idtofun-section refl _ = refl

back-Idtofun : {X Y : π€ Μ } β X β‘ Y β Y β X
back-Idtofun = back-transport id

forth-and-back-transport : {X : π€ Μ } {A : X β π₯ Μ }
                           {x y : X} (p : x β‘ y) {a : A x}
                         β back-transport A p (transport A p a) β‘ a
forth-and-back-transport refl = refl

back-and-forth-transport : {X : π€ Μ } {A : X β π₯ Μ }
                           {x y : X} (p : y β‘ x) {a : A x}
                         β transport A p (back-transport A p a) β‘ a
back-and-forth-transport refl = refl

back-transport-is-pre-comp : {X X' : π€ Μ } {Y : π₯ Μ } (p : X β‘ X') (g : X' β Y)
                           β back-transport (Ξ» - β - β Y) p g β‘ g β Idtofun p
back-transport-is-pre-comp refl g = refl

transport-is-pre-comp : {X X' : π€ Μ } {Y : π₯ Μ } (p : X β‘ X') (g : X β Y)
                      β transport (Ξ» - β - β Y) p g β‘ g β Idtofun (p β»ΒΉ)
transport-is-pre-comp refl g = refl

trans-sym : {X : π€ Μ } {x y : X} (r : x β‘ y) β r β»ΒΉ β r β‘ refl
trans-sym refl = refl

trans-sym' : {X : π€ Μ } {x y : X} (r : x β‘ y) β r β r β»ΒΉ β‘ refl
trans-sym' refl = refl

transport-Γ : {X : π€ Μ } (A : X β π₯ Μ ) (B : X β π¦ Μ )
              {x y : X} {c : A x Γ B x} (p : x β‘ y)
            β transport (Ξ» x β A x Γ B x) p c
            β‘ (transport A p (prβ c) , transport B p (prβ c))
transport-Γ A B refl = refl

transport-β : {X : π€ Μ } (A : X β π₯ Μ )
                 {x y z : X} (q : x β‘ y) (p : y β‘ z) {a : A x}
               β transport A  (q β p) a β‘ transport A p (transport A q a)
transport-β A refl refl = refl

transport-β' : {X : π€ Μ } (A : X β π₯ Μ )
                  {x y z : X} (q : x β‘ y) (p : y β‘ z)
                β transport A  (q β p) β‘ transport A p β transport A q
transport-β' A refl refl = refl

transport-ap : {X : π€ Μ } {Y : π₯ Μ } (A : Y β π¦ Μ )
               (f : X β Y) {x x' : X} (p : x β‘ x') {a : A(f x)}
             β transport (A β f) p a β‘ transport A (ap f p) a
transport-ap A f refl = refl

transport-ap' : {X : π€ Μ } {Y : π₯ Μ } (A : Y β π¦ Μ )
                (f : X β Y) {x x' : X} (p : x β‘ x')
              β transport (A β f) p β‘ transport A (ap f p)
transport-ap' A f refl = refl

nat-transport : {X : π€ Μ } {A : X β π₯ Μ } {B : X β π¦ Μ }
                (f : Nat A B) {x y : X} (p : x β‘ y) {a : A x}
              β f y (transport A p a) β‘ transport B p (f x a)
nat-transport f refl = refl

transport-fam : {X : π€ Μ } {Y : X β π₯ Μ } (P : {x : X} β Y x β π¦ Μ )
               (x : X) (y : Y x) β P y β (x' : X) (r : x β‘ x') β P(transport Y r y)
transport-fam P x y p .x refl = p

transport-rel : {X : π€ Μ } {Y : X β π₯ Μ } (_βΊ_ : {x : X} β Y x β Y x β π¦ Μ )
              β (a x : X) (b : Y a) (v : Y x) (p : a β‘ x)
              β  v βΊ transport Y p b
              β back-transport Y p v βΊ b
transport-rel _βΊ_ a .a b v refl = id

transport-rel' : {X : π€ Μ } {Y : X β π₯ Μ } (_βΊ_ : {x : X} β Y x β Y x β π¦ Μ )
               β (a x : X) (b : Y a) (v : Y x) (r : x β‘ a)
               β transport Y r v βΊ b
               β v βΊ back-transport Y r b
transport-rel' _βΊ_ a .a b v refl = id

transport-const : {X : π€ Μ } {Y : π₯ Μ } {x x' : X} {y : Y} (p : x β‘ x')
                β transport (Ξ» (_ : X) β Y) p y β‘ y
transport-const refl = refl

apd' : {X : π€ Μ } (A : X β π₯ Μ ) (f : (x : X) β A x)
       {x y : X} (p : x β‘ y)
     β transport A p (f x) β‘ f y
apd' A f refl = refl

apd : {X : π€ Μ } {A : X β π₯ Μ } (f : (x : X) β A x)
      {x y : X} (p : x β‘ y)
    β transport A p (f x) β‘ f y
apd = apd' _

ap-id-is-id : {X : π€ Μ } {x y : X} (p : x β‘ y) β ap id p β‘ p
ap-id-is-id refl = refl

ap-id-is-id' : {X : π€ Μ } {x y : X} (p : x β‘ y) β p β‘ ap id p
ap-id-is-id' refl = refl

ap-β : {X : π€ Μ } {Y : π₯ Μ } (f : X β Y) {x y z : X} (p : x β‘ y) (q : y β‘ z)
     β ap f (p β q) β‘ ap f p β ap f q
ap-β f refl refl = refl

ap-β' : {X : π€ Μ } {Y : π₯ Μ } (f : X β Y) {x y : X} (p : x β‘ y)
      β ap f (p β»ΒΉ) β ap f p β‘ refl
ap-β' f refl = refl

ap-sym : {X : π€ Μ } {Y : π₯ Μ } (f : X β Y) {x y : X} (p : x β‘ y)
       β (ap f p) β»ΒΉ β‘ ap f (p β»ΒΉ)
ap-sym f refl = refl

ap-ap : {X : π€ Μ } {Y : π₯ Μ } {Z : π¦ Μ } (f : X β Y) (g : Y β Z)
        {x x' : X} (r : x β‘ x')
      β ap g (ap f r) β‘ ap (g β f) r
ap-ap {π€} {π₯} {π¦} {X} {Y} {Z} f g = J A (Ξ» x β refl)
 where
  A : (x x' : X) β x β‘ x' β π¦ Μ
  A x x' r = ap g (ap f r) β‘ ap (g β f) r

apβ : {X : π€ Μ } {Y : π₯ Μ } {Z : π¦ Μ } (f : X β Y β Z) {xβ xβ : X} {yβ yβ : Y}
    β xβ β‘ xβ β yβ β‘ yβ β f xβ yβ β‘ f xβ yβ
apβ f refl refl = refl

refl-left-neutral : {X : π€ Μ } {x y : X} {p : x β‘ y} β refl β p β‘ p
refl-left-neutral {π€} {X} {x} {_} {refl} = refl

refl-right-neutral : {X : π€ Μ } {x y : X} (p : x β‘ y) β p β‘ p β refl
refl-right-neutral p = refl

βassoc : {X : π€ Μ } {x y z t : X} (p : x β‘ y) (q : y β‘ z) (r : z β‘ t)
       β (p β q) β r β‘ p β (q β r)
βassoc refl refl refl = refl

happly' : {X : π€ Μ } {A : X β π₯ Μ } (f g : Ξ  A) β f β‘ g β f βΌ g
happly' f g p x = ap (Ξ» - β - x) p

happly : {X : π€ Μ } {A : X β π₯ Μ } {f g : Ξ  A} β f β‘ g β f βΌ g
happly = happly' _ _

sym-is-inverse : {X : π€ Μ } {x y : X} (p : x β‘ y)
               β refl β‘ p β»ΒΉ β p
sym-is-inverse = J (Ξ» x y p β refl β‘ p β»ΒΉ β p) (Ξ» x β refl)

sym-is-inverse' : {X : π€ Μ } {x y : X} (p : x β‘ y)
                β refl β‘ p β p β»ΒΉ
sym-is-inverse' refl = refl

β»ΒΉ-involutive : {X : π€ Μ } {x y : X} (p : x β‘ y) β (p β»ΒΉ)β»ΒΉ β‘ p
β»ΒΉ-involutive refl = refl

β»ΒΉ-contravariant : {X : π€ Μ } {x y : X} (p : x β‘ y) {z : X} (q : y β‘ z)
                 β q β»ΒΉ β p β»ΒΉ β‘ (p β q)β»ΒΉ
β»ΒΉ-contravariant refl refl = refl

left-inverse : {X : π€ Μ } {x y : X} (p : x β‘ y) β p β»ΒΉ β p β‘ refl
left-inverse {π€} {X} {x} {y} refl = refl

right-inverse : {X : π€ Μ } {x y : X} (p : x β‘ y) β refl β‘ p β p β»ΒΉ
right-inverse {π€} {X} {x} {y} refl = refl

cancel-left : {X : π€ Μ } {x y z : X} {p : x β‘ y} {q r : y β‘ z}
            β p β q β‘ p β r β q β‘ r
cancel-left {π€} {X} {x} {y} {z} {p} {q} {r} s =
       q              β‘β¨ refl-left-neutral β»ΒΉ β©
       refl β q       β‘β¨ ap (Ξ» - β - β q) ((left-inverse p)β»ΒΉ) β©
       (p β»ΒΉ β p) β q β‘β¨ βassoc (p β»ΒΉ) p q β©
       p β»ΒΉ β (p β q) β‘β¨ ap (Ξ» - β p β»ΒΉ β -) s β©
       p β»ΒΉ β (p β r) β‘β¨ (βassoc (p β»ΒΉ) p r)β»ΒΉ β©
       (p β»ΒΉ β p) β r β‘β¨ ap (Ξ» - β - β r) (left-inverse p) β©
       refl β r       β‘β¨ refl-left-neutral β©
       r              β

\end{code}

It is shorter to prove the above using pattern matching on refl, of course.

\begin{code}

cancelβ : {X : π€ Μ } {x y z : X} (p : x β‘ y) (q : z β‘ y)
        β (p β q β»ΒΉ) β (q β p β»ΒΉ) β‘ refl
cancelβ refl refl = refl

\end{code}

Added 24 February 2020 by Tom de Jong.

\begin{code}

cancel-left-β‘ : {X : π€ Μ } {x y z : X} {p : x β‘ y} {q r : y β‘ z}
              β (p β q β‘ p β r) β‘ (q β‘ r)
cancel-left-β‘ {π€} {X} {x} {y} {z} {refl} {q} {r} =
 apβ (Ξ» u v β u β‘ v) refl-left-neutral refl-left-neutral

\end{code}

\begin{code}

homotopies-are-natural' : {X : π€ Μ } {A : π₯ Μ } (f g : X β A) (H : f βΌ g) {x y : X} {p : x β‘ y}
                        β H x β ap g p β (H y)β»ΒΉ β‘ ap f p
homotopies-are-natural' f g H {x} {_} {refl} = trans-sym' (H x)

homotopies-are-natural'' : {X : π€ Μ } {A : π₯ Μ } (f g : X β A) (H : f βΌ g) {x y : X} {p : x β‘ y}
                         β (H x) β»ΒΉ β ap f p β H y β‘ ap g p
homotopies-are-natural'' f g H {x} {_} {refl} = trans-sym (H x)

homotopies-are-natural : {X : π€ Μ } {A : π₯ Μ } (f g : X β A) (H : f βΌ g) {x y : X} {p : x β‘ y}
                       β H x β ap g p β‘ ap f p β H y
homotopies-are-natural f g H {x} {_} {refl} = refl-left-neutral β»ΒΉ

to-Γ-β‘ : {X : π€ Μ } {Y : π₯ Μ } {x x' : X} {y y' : Y}
       β x β‘ x' β y β‘ y' β (x , y) β‘ (x' , y')
to-Γ-β‘ refl refl = refl

to-Γ-β‘' : {X : π€ Μ } {Y : π₯ Μ } {z z' : X Γ Y}
        β (prβ z β‘ prβ z') Γ (prβ z β‘ prβ z') β z β‘ z'
to-Γ-β‘' (refl , refl) = refl

from-Γ-β‘' : {X : π€ Μ } {Y : π₯ Μ } {z z' : X Γ Y}
          β z β‘ z'
          β (prβ z β‘ prβ z') Γ (prβ z β‘ prβ z' )
from-Γ-β‘' refl = (refl , refl)

tofrom-Γ-β‘ : {X : π€ Μ } {Y : π₯ Μ }
             {z z' : X Γ Y} (p : z β‘ z')
           β p β‘ to-Γ-β‘ (prβ (from-Γ-β‘' p)) (prβ (from-Γ-β‘' p))
tofrom-Γ-β‘ refl = refl

from-Ξ£-β‘' : {X : π€ Μ } {Y : X β π₯ Μ } {u v : Ξ£ Y} (r : u β‘ v)
          β transport Y (ap prβ r) (prβ u) β‘ (prβ v)
from-Ξ£-β‘' {π€} {π₯} {X} {Y} {u} {v} = J A (Ξ» u β refl) {u} {v}
 where
  A : (u v : Ξ£ Y) β u β‘ v β π₯ Μ
  A u v r = transport Y (ap prβ r) (prβ u) β‘ (prβ v)

from-Ξ£-β‘ : {X : π€ Μ } {Y : X β π₯ Μ } {Ο Ο : Ξ£ Y} (r : Ο β‘ Ο)
         β Ξ£ p κ prβ Ο β‘ prβ Ο , transport Y p (prβ Ο) β‘ (prβ Ο)
from-Ξ£-β‘ r = (ap prβ r , from-Ξ£-β‘' r)

to-Ξ£-β‘ : {X : π€ Μ } {A : X β π₯ Μ } {Ο Ο : Ξ£ A}
       β (Ξ£ p κ prβ Ο β‘ prβ Ο , transport A p (prβ Ο) β‘ prβ Ο)
       β Ο β‘ Ο
to-Ξ£-β‘ (refl , refl) = refl

ap-prβ-to-Ξ£-β‘ : {X : π€ Μ } {A : X β π₯ Μ } {Ο Ο : Ξ£ A}
                (w : Ξ£ p κ prβ Ο β‘ prβ Ο , transport A p (prβ Ο) β‘ prβ Ο)
              β ap prβ (to-Ξ£-β‘ w) β‘ prβ w
ap-prβ-to-Ξ£-β‘ (refl , refl) = refl

to-Ξ£-β‘' : {X : π€ Μ } {Y : X β π₯ Μ } {x : X} {y y' : Y x}
        β y β‘ y'
        β (x , y) β‘[ Ξ£ Y ] (x , y')
to-Ξ£-β‘' {π€} {π₯} {X} {Y} {x} = ap (Ξ» - β (x , -))

fromto-Ξ£-β‘ : {X : π€ Μ } {A : X β π₯ Μ }
             {Ο Ο : Ξ£ A}
             (w : Ξ£ p κ prβ Ο β‘ prβ Ο , transport A p (prβ Ο) β‘ prβ Ο)
           β from-Ξ£-β‘ (to-Ξ£-β‘ w) β‘ w
fromto-Ξ£-β‘ (refl , refl) = refl

tofrom-Ξ£-β‘ : {X : π€ Μ } {A : X β π₯ Μ } {Ο Ο : Ξ£ A} (r : Ο β‘ Ο)
           β to-Ξ£-β‘ (from-Ξ£-β‘ r) β‘ r
tofrom-Ξ£-β‘ refl = refl

ap-prβ-to-Γ-β‘ : {X : π€ Μ } {Y : π₯ Μ } {z t : X Γ Y}
              β (pβ : prβ z β‘ prβ t)
              β (pβ : prβ z β‘ prβ t)
              β ap prβ (to-Γ-β‘ pβ pβ) β‘ pβ
ap-prβ-to-Γ-β‘ refl refl = refl

ap-prβ-to-Γ-β‘ : {X : π€ Μ } {Y : π₯ Μ } {z t : X Γ Y}
              β (pβ : prβ z β‘ prβ t)
              β (pβ : prβ z β‘ prβ t)
              β ap prβ (to-Γ-β‘ pβ pβ) β‘ pβ
ap-prβ-to-Γ-β‘ refl refl = refl

\end{code}

Added by Tom de Jong
22 March 2021:

\begin{code}

ap-prβ-refl-lemma : {X : π€ Μ } (Y : X β π₯ Μ )
                    {x : X} {y y' : Y x}
                    (w : (x , y) β‘[ Ξ£ Y ] (x , y'))
                  β ap prβ w β‘ refl
                  β y β‘ y'
ap-prβ-refl-lemma Y {x} {y} {y'} w p = Ξ³ (ap prβ w) p β h
 where
  Ξ³ : (r : x β‘ x) β (r β‘ refl) β y β‘ transport Y r y
  Ξ³ r refl = refl
  h : transport Y (ap prβ w) y β‘ y'
  h = from-Ξ£-β‘' w

transport-along-β‘ : {X : π€ Μ } {x y : X} (q : x β‘ y) (p : x β‘ x)
                  β transport (Ξ» - β - β‘ -) q p β‘ q β»ΒΉ β p β q
transport-along-β‘ refl p = (refl β»ΒΉ β (p β refl) β‘β¨ refl              β©
                            refl β»ΒΉ β p          β‘β¨ refl-left-neutral β©
                            p                    β                     ) β»ΒΉ

transport-along-β : {X : π€ Μ } (Y : X β π₯ Μ ) (Z : X β π¦ Μ )
                    {x y : X}
                    (p : x β‘ y) (f : Y x β Z x)
                  β transport (Ξ» - β (Y - β Z -)) p f
                  β‘ transport Z p β f β transport Y (p β»ΒΉ)
transport-along-β Y Z refl f = refl

\end{code}
