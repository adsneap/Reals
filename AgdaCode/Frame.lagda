Ayberk Tosun, 8 March 2021.

Ported from `ayberkt/formal-topology-in-UF`.

 * Frames.
 * Frame homomorphisms.
 * Frame bases.

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (đ)
open import UF-Base
open import UF-PropTrunc
open import UF-FunExt
open import UF-PropTrunc
open import List hiding ([_])

module Frame
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import UF-Subsingletons
open import UF-Subsingleton-Combinators
open import UF-Subsingletons-FunExt

open AllCombinators pt fe

\end{code}

\section{Preliminaries}

By Fam_đ¤(A), we denote the type of families on type A with index types
living in universe đ¤.

\begin{code}

private
  variable
    đ¤â˛ đĽâ˛ đŚâ˛ : Universe

Fam : (đ¤ : Universe) â đĽ Ě â đ¤ âş â đĽ Ě
Fam đ¤ A = ÎŁ I ę (đ¤ Ě) , (I â A)

fmap-syntax : {A : đ¤ Ě} {B : đĽ Ě}
            â (A â B) â Fam đŚ A â Fam đŚ B
fmap-syntax h (I , f) = I , h â f

infix 2 fmap-syntax

syntax fmap-syntax (Îť x â e) U = â e âŁ x Îľ U â

compr-syntax : {A : đ¤ Ě} (I : đŚ Ě) â (I â A) â Fam đŚ A
compr-syntax I f = I , f

infix 2 compr-syntax

syntax compr-syntax I (Îť x â e) = â e âŁ x âś I â

\end{code}

We define two projections for families: (1) for the index type,
and (2) for the enumeration function.

\begin{code}

index : {A : đ¤ Ě} â Fam đĽ A â đĽ Ě
index (I , _) = I

_[_] : {A : đ¤ Ě} â (U : Fam đĽ A) â index U â A
(_ , f) [ i ] = f i

infixr 9 _[_]

\end{code}

We define some order-theoretic notions that are also defined in the
`Dcpo` module. Ideally, this should be factored out into a standalone
module to be imported by both this module and the `Dcpo` module.

\begin{code}

is-reflexive : {A : đ¤ Ě} â (A â A â ÎŠ đĽ) â ÎŠ (đ¤ â đĽ)
is-reflexive {A = A} _â¤_ = âąŻ x âś A , x â¤ x

is-transitive : {A : đ¤ Ě} â (A â A â ÎŠ đĽ) â ÎŠ (đ¤ â đĽ)
is-transitive {A = A} _â¤_ =
 âąŻ x âś A , âąŻ y âś A , âąŻ z âś A , x â¤ y â y â¤ z â x â¤ z

is-preorder : {A : đ¤ Ě} â (A â A â ÎŠ đĽ) â ÎŠ (đ¤ â đĽ)
is-preorder {A = A} _â¤_ = is-reflexive _â¤_ â§ is-transitive _â¤_

\end{code}

Antisymmetry is not propositional unless A is a set. We will always
work with sets but the fact they are sets will be a corollary of their
equipment with an antisymmetric order so they are not sets a priori.

\begin{code}

is-antisymmetric : {A : đ¤ Ě} â (A â A â ÎŠ đĽ) â (đ¤ â đĽ) Ě
is-antisymmetric {A = A} _â¤_ = {x y : A} â (x â¤ y) holds â (y â¤ x) holds â x âĄ y

being-antisymmetric-is-prop : {A : đ¤ Ě} (_â¤_ : A â A â ÎŠ đĽ)
                            â is-set A
                            â is-prop (is-antisymmetric _â¤_)
being-antisymmetric-is-prop {đ¤} {A} _â¤_ A-is-set =
 Î -is-prop' fe (Îť x â Î -is-prop' fe (Îť y â Î â-is-prop fe (Îť _ _ â A-is-set {x} {y})))

is-partial-order : (A : đ¤ Ě) â (A â A â ÎŠ đĽ) â đ¤ â đĽ Ě
is-partial-order A _â¤_ = is-preorder _â¤_ holds Ă  is-antisymmetric _â¤_

being-partial-order-is-prop : (A : đ¤ Ě) (_â¤_ : A â A â ÎŠ đĽ)
                            â is-prop (is-partial-order A _â¤_)
being-partial-order-is-prop A _â¤_ = prop-criterion Îł
 where
  Îł : is-partial-order A _â¤_ â is-prop (is-partial-order A _â¤_)
  Îł (p , a) = Ă-is-prop
               (holds-is-prop (is-preorder _â¤_))
               (being-antisymmetric-is-prop _â¤_ i)
   where
    i : is-set A
    i = type-with-prop-valued-refl-antisym-rel-is-set
         (Îť x y â (x â¤ y) holds)
         (Îť x y â holds-is-prop (x â¤ y))
         (prâ p)
         (Îť x y â a {x} {y})

\end{code}

\section{Definition of poset}

A (đ¤, đĽ)-poset is a poset whose

  - carrier lives in universe đ¤, and
  - whose relation lives in universe đĽ.

\begin{code}

poset-structure : (đĽ : Universe) â đ¤ Ě â đ¤ â đĽ âş Ě
poset-structure đĽ A =
 ÎŁ _â¤_ ę (A â A â ÎŠ đĽ) , (is-partial-order A _â¤_)

poset : (đ¤ đĽ : Universe) â đ¤ âş â đĽ âş Ě
poset đ¤ đĽ = ÎŁ A ę đ¤ Ě , poset-structure đĽ A

âŁ_âŁâ : poset đ¤ đĽ â đ¤ Ě
âŁ A , _ âŁâ = A

rel-syntax : (P : poset đ¤ đĽ)  â âŁ P âŁâ â âŁ P âŁâ â ÎŠ đĽ
rel-syntax (_ , _â¤_ , _) = _â¤_

syntax rel-syntax P x y = x â¤[ P ] y

poset-eq-syntax : (P : poset đ¤ đĽ) â âŁ P âŁâ â âŁ P âŁâ â ÎŠ đĽ
poset-eq-syntax P x y = x â¤[ P ] y â§ y â¤[ P ] x

syntax poset-eq-syntax P x y = x âŁ[ P ] y

â¤-is-reflexive : (P : poset đ¤ đĽ)
               â is-reflexive (Îť x y â x â¤[ P ] x) holds
â¤-is-reflexive (_ , _ , ((r , _) , _)) = r

reflexivity+ : (P : poset đ¤ đĽ)
             â {x y : prâ P} â x âĄ y â (x â¤[ P ] y) holds
reflexivity+ P {x} {y} p =
 transport (Îť - â (x â¤[ P ] -) holds) p (â¤-is-reflexive P x)

â¤-is-transitive : (P : poset đ¤ đĽ)
                â is-transitive (Îť x y â x â¤[ P ] y) holds
â¤-is-transitive (_ , _ , ((_ , t) , _)) = t

â¤-is-antisymmetric : (P : poset đ¤ đĽ)
                   â is-antisymmetric (Îť x y â x â¤[ P ] y)
â¤-is-antisymmetric (_ , _ , (_ , a)) = a

carrier-of-[_]-is-set : (P : poset đ¤ đĽ) â is-set âŁ P âŁâ
carrier-of-[_]-is-set P@ (A , _)=
 type-with-prop-valued-refl-antisym-rel-is-set
  (Îť x y â (x â¤[ P ] y) holds)
  (Îť x y â holds-is-prop (x â¤[ P ] y))
  (â¤-is-reflexive P)
  (Îť x y â â¤-is-antisymmetric P {x} {y})

\end{code}

Some convenient syntax for reasoning with posets.

\begin{code}

module PosetNotation (P : poset đ¤ đĽ) where

 _â¤_ : âŁ P âŁâ â âŁ P âŁâ â ÎŠ đĽ
 x â¤ y = x â¤[ P ] y

 infix 4 _â¤_

 _âŁ_ : âŁ P âŁâ â âŁ P âŁâ â ÎŠ đĽ
 x âŁ y = x âŁ[ P ] y

module PosetReasoning (P : poset đ¤ đĽ) where

 open PosetNotation P using (_â¤_)

 _â¤â¨_âŠ_ : (x : âŁ P âŁâ) {y z : âŁ P âŁâ}
        â (x â¤ y) holds â (y â¤ z) holds â (x â¤ z) holds
 x â¤â¨ p âŠ q = â¤-is-transitive P _ _ _ p q

 _âĄâ¨_âŠâ_ : (x : âŁ P âŁâ) {y z : âŁ P âŁâ}
         â x âĄ y â (y â¤ z) holds â (x â¤ z) holds
 x âĄâ¨ p âŠâ q = transport (Îť - â (- â¤ _) holds) (p âťÂš) q

 _â  : (x : âŁ P âŁâ) â (x â¤ x) holds
 _â  = â¤-is-reflexive P

 infixr 0 _â¤â¨_âŠ_
 infixr 0 _âĄâ¨_âŠâ_
 infix  1 _â 

infix 1 _âĄ[_]âĄ_

_âĄ[_]âĄ_ : {A : đ¤ Ě} â A â is-set A â A â ÎŠ đ¤
x âĄ[ iss ]âĄ y = (x âĄ y) , iss

\end{code}

\section{Meets}

\begin{code}

module Meets {A : đ¤ Ě} (_â¤_ : A â A â ÎŠ đĽ) where

 is-top : A â ÎŠ (đ¤ â đĽ)
 is-top t = âąŻ x âś A , (x â¤ t)

 _is-a-lower-bound-of_ : A â A Ă A â ÎŠ đĽ
 l is-a-lower-bound-of (x , y) = (l â¤ x) â§ (l â¤ y)

 lower-bound : A Ă A â đ¤ â đĽ Ě
 lower-bound (x , y) =
   ÎŁ l ę A , (l is-a-lower-bound-of (x , y)) holds

 _is-glb-of_ : A â A Ă A â ÎŠ (đ¤ â đĽ)
 l is-glb-of (x , y) = l is-a-lower-bound-of (x , y)
                     â§ (âąŻ (lâ˛ , _) âś lower-bound (x , y) , (lâ˛ â¤ l))

\end{code}

\section{Joins}

\begin{code}

module Joins {A : đ¤ Ě} (_â¤_ : A â A â ÎŠ đĽ) where

 _is-an-upper-bound-of_ : A â Fam đŚ A â ÎŠ (đĽ â đŚ)
 u is-an-upper-bound-of U = âąŻ i âś index U , (U [ i ]) â¤ u

 upper-bound : Fam đŚ A â đ¤ â đĽ â đŚ Ě
 upper-bound U = ÎŁ u ę A , (u is-an-upper-bound-of U) holds

 _is-lub-of_ : A â Fam đŚ A â ÎŠ (đ¤ â đĽ â đŚ)
 u is-lub-of U = (u is-an-upper-bound-of U)
               â§ (âąŻ (uâ˛ , _) âś upper-bound U , (u â¤ uâ˛))

module JoinNotation {A : đ¤ Ě} (â_ : Fam đŚ A â A) where

 join-syntax : (I : đŚ Ě) â (I â A) â A
 join-syntax I f = â (I , f)

 ââ¨âŠ-syntax : {I : đŚ Ě} â (I â A) â A
 ââ¨âŠ-syntax {I = I} f = join-syntax I f

 infix 2 join-syntax
 infix 2 ââ¨âŠ-syntax

 syntax join-syntax I (Îť i â e) = ââ¨ i âś I âŠ e
 syntax ââ¨âŠ-syntax    (Îť i â e) = ââ¨ i âŠ e

\end{code}

\section{Definition of frame}

A (đ¤, đĽ, đŚ)-frame is a frame whose

  - carrier lives in universe đ¤,
  - order lives in universe đĽ, and
  - index types live in universe đŚ.

\begin{code}

frame-data : (đĽ đŚ : Universe) â đ¤ Ě â đ¤ â đĽ âş â đŚ âş Ě
frame-data đĽ đŚ A = (A â A â ÎŠ đĽ)   -- order
                 Ă A               -- top element
                 Ă (A â A â A)     -- binary meets
                 Ă (Fam đŚ A â A)   -- arbitrary joins

satisfies-frame-laws : {A : đ¤ Ě} â frame-data đĽ đŚ A â đ¤ â đĽ â đŚ âş Ě
satisfies-frame-laws {đ¤ = đ¤} {đĽ} {đŚ} {A = A}  (_â¤_ , đ , _â_ , â_) =
 ÎŁ p ę is-partial-order A _â¤_ , rest p holds
 where
  open Meets _â¤_
  open Joins _â¤_
  open JoinNotation â_

  rest : is-partial-order A _â¤_ â ÎŠ (đ¤ â đĽ â đŚ âş)
  rest p = Î˛ â§ Îł â§ Î´ â§ Îľ
   where
    P : poset đ¤ đĽ
    P = A , _â¤_ , p

    iss : is-set A
    iss = carrier-of-[ P ]-is-set

    Î˛ = is-top đ
    Îł = âąŻ (x , y) âś (A Ă A) , ((x â y) is-glb-of (x , y))
    Î´ = âąŻ U âś Fam đŚ A , (â U) is-lub-of U
    Îľ = âąŻ (x , U) âś A Ă Fam đŚ A ,
        (x â (ââ¨ i âŠ U [ i ]) âĄ[ iss ]âĄ ââ¨ i âŠ x â (U [ i ]))

frame-structure : (đĽ đŚ : Universe) â đ¤ Ě â đ¤ â đĽ âş â đŚ âş Ě
frame-structure đĽ đŚ A =
  ÎŁ d ę (frame-data đĽ đŚ A) , satisfies-frame-laws d

\end{code}

The type of (đ¤, đĽ, đŚ)-frames is then defined as:

\begin{code}

frame : (đ¤ đĽ đŚ : Universe) â đ¤ âş â đĽ âş â đŚ âş Ě
frame đ¤ đĽ đŚ = ÎŁ A ę (đ¤ Ě) , frame-structure đĽ đŚ A

\end{code}

The underlying poset of a frame:

\begin{code}

poset-of : frame đ¤ đĽ đŚ â poset đ¤ đĽ
poset-of (A , (_â¤_ , _ , _ , _) , p , _) = A , _â¤_ , p

\end{code}

Some projections.

\begin{code}

â¨_âŠ : frame đ¤ đĽ đŚ â đ¤ Ě
â¨ (A , (_â¤_ , _ , _ , _) , p , _) âŠ = A

đ[_] : (F : frame đ¤ đĽ đŚ) â  â¨ F âŠ
đ[ (A , (_ , đ , _ , _) , p , _) ] = đ

is-top : (F : frame đ¤ đĽ đŚ) â â¨ F âŠ â ÎŠ (đ¤ â đĽ)
is-top F t = âąŻ x âś â¨ F âŠ , x â¤[ poset-of F ] t

đ-is-top : (F : frame đ¤ đĽ đŚ) â (is-top F đ[ F ]) holds
đ-is-top (A , _ , _ , p , _) = p

đ-is-unique : (F : frame đ¤ đĽ đŚ) â (t : â¨ F âŠ) â is-top F t holds â t âĄ đ[ F ]
đ-is-unique F t t-top = â¤-is-antisymmetric (poset-of F) Î˛ Îł
 where
  Î˛ : (t â¤[ poset-of F ] đ[ F ]) holds
  Î˛ = đ-is-top F t

  Îł : (đ[ F ] â¤[ poset-of F ] t) holds
  Îł = t-top đ[ F ]

only-đ-is-above-đ : (F : frame đ¤ đĽ đŚ) (x : â¨ F âŠ)
                  â (đ[ F ] â¤[ poset-of F ] x) holds â x âĄ đ[ F ]
only-đ-is-above-đ F x p =
 đ-is-unique F x Îť y â y â¤â¨ đ-is-top F y âŠ đ[ F ] â¤â¨ p âŠ x â 
  where
   open PosetReasoning (poset-of F)

meet-of : (F : frame đ¤ đĽ đŚ) â â¨ F âŠ â â¨ F âŠ â â¨ F âŠ
meet-of (_ , (_ , _ , _â§_ , _) , _ , _) x y = x â§ y

infix 4 meet-of

syntax meet-of F x y = x â§[ F ] y

join-of : (F : frame đ¤ đĽ đŚ) â Fam đŚ â¨ F âŠ â â¨ F âŠ
join-of (_ , (_ , _ , _ , â_) , _ , _) = â_

infix 4 join-of

syntax join-of F U = â[ F ] U

\end{code}

\begin{code}

â§[_]-lowerâ : (A : frame đ¤ đĽ đŚ) (x y : â¨ A âŠ)
            â ((x â§[ A ] y) â¤[ poset-of A ] x) holds
â§[_]-lowerâ (A , _ , _ , (_ , Îł , _ , _)) x y = prâ (prâ (Îł (x , y)))

â§[_]-lowerâ : (A : frame đ¤ đĽ đŚ) (x y : â¨ A âŠ)
            â ((x â§[ A ] y) â¤[ poset-of A ] y) holds
â§[_]-lowerâ (A , _ , _ , (_ , Îł , _ , _)) x y = prâ (prâ (Îł (x , y)))

â§[_]-greatest : (A : frame đ¤ đĽ đŚ) (x y : â¨ A âŠ)
              â (z : â¨ A âŠ)
              â (z â¤[ poset-of A ] x) holds
              â (z â¤[ poset-of A ] y) holds
              â (z â¤[ poset-of A ] (x â§[ A ] y)) holds
â§[_]-greatest (A , _ , _ , (_ , Îł , _ , _)) x y z p q =
  prâ (Îł (x , y)) (z , p , q)

\end{code}

\begin{code}

đ-right-unit-of-â§ : (F : frame đ¤ đĽ đŚ)
                  â (x : â¨ F âŠ) â x â§[ F ] đ[ F ] âĄ x
đ-right-unit-of-â§ F x = â¤-is-antisymmetric (poset-of F) Î˛ Îł
 where
  Î˛ : ((x â§[ F ] đ[ F ]) â¤[ poset-of F ] x) holds
  Î˛ = â§[ F ]-lowerâ x đ[ F ]

  Îł : (x â¤[ poset-of F ] (x â§[ F ] đ[ F ])) holds
  Îł = â§[ F ]-greatest x đ[ F ] x (â¤-is-reflexive (poset-of F) x) (đ-is-top F x)

\end{code}

\begin{code}

â[_]-upper : (A : frame đ¤ đĽ đŚ) (U : Fam đŚ â¨ A âŠ) (i : index U)
        â ((U [ i ]) â¤[ poset-of A ] (â[ A ] U)) holds
â[_]-upper (A , _ , _ , (_ , _ , c , _)) U i = prâ (c U) i

â[_]-least : (A : frame đ¤ đĽ đŚ) â (U : Fam đŚ â¨ A âŠ)
           â let open Joins (Îť x y â x â¤[ poset-of A ] y)
             in ((u , _) : upper-bound U) â ((â[ A ] U) â¤[ poset-of A ] u) holds
â[_]-least (A , _ , _ , (_ , _ , c , _)) U = prâ (c U)

\end{code}

\begin{code}

đ : (đ¤ : Universe) â đ¤ Ě
đ đ¤ = đ {đ¤} + đ {đ¤}

binary-family : {A : đ¤ Ě } â (đŚ : Universe) â A â A â Fam đŚ A
binary-family {A = A} đŚ x y = đ đŚ  , Îą
 where
  Îą : đ đŚ â A
  Îą (inl *) = x
  Îą (inr *) = y

fmap-binary-family : {A : đ¤ Ě } {B : đĽ Ě }
                   â (đŚ : Universe)
                   â (f : A â B)
                   â (x y : A)
                   â â f z âŁ z Îľ (binary-family đŚ x y) â
                   âĄ binary-family đŚ (f x) (f y)
fmap-binary-family đŚ f x y = ap (Îť - â đ đŚ , -) (dfunext fe Îł)
 where
  Îł : â f z âŁ z Îľ binary-family đŚ x y â [_] âź binary-family đŚ (f x) (f y) [_]
  Îł (inl *) = refl
  Îł (inr *) = refl


binary-join : (F : frame đ¤ đĽ đŚ) â â¨ F âŠ â â¨ F âŠ â â¨ F âŠ
binary-join {đŚ = đŚ} F x y = â[ F ] binary-family đŚ x y

infix 3 binary-join
syntax binary-join F x y = x â¨[ F ] y

â¨[_]-least : (F : frame đ¤ đĽ đŚ)
           â let open Joins (Îť x y â x â¤[ poset-of F ] y) in
             {x y z : â¨ F âŠ}
           â (x â¤[ poset-of F ] z) holds
           â (y â¤[ poset-of F ] z) holds
           â ((x â¨[ F ] y) â¤[ poset-of F ] z) holds
â¨[_]-least {đŚ = đŚ} F {x} {y} {z} xâ¤z yâ¤z =
 â[ F ]-least (binary-family đŚ x y) (z , Îł)
  where
   Îł : _
   Îł (inl *) = xâ¤z
   Îł (inr *) = yâ¤z

â¨[_]-upperâ : (F : frame đ¤ đĽ đŚ)
            â let open Joins (Îť x y â x â¤[ poset-of F ] y) in
              (x y : â¨ F âŠ) â (x â¤[ poset-of F ] (x â¨[ F ] y)) holds
â¨[_]-upperâ {đŚ = đŚ} F x y = â[ F ]-upper (binary-family đŚ x y) (inl â)

â¨[_]-upperâ : (F : frame đ¤ đĽ đŚ)
            â let open Joins (Îť x y â x â¤[ poset-of F ] y) in
              (x y : â¨ F âŠ) â (y â¤[ poset-of F ] (x â¨[ F ] y)) holds
â¨[_]-upperâ {đŚ = đŚ} F x y = â[ F ]-upper (binary-family đŚ x y) (inr â)

â¨[_]-is-commutative : (F : frame đ¤ đĽ đŚ)
                    â (x y : â¨ F âŠ)
                    â (x â¨[ F ] y) âĄ (y â¨[ F ] x)
â¨[_]-is-commutative F x y =
 â¤-is-antisymmetric (poset-of F) Î˛ Îł
  where
   open PosetNotation  (poset-of F)
   open PosetReasoning (poset-of F)

   Î˛ : ((x â¨[ F ] y) â¤ (y â¨[ F ] x)) holds
   Î˛ = â¨[ F ]-least (â¨[ F ]-upperâ y x) (â¨[ F ]-upperâ y x)

   Îł : ((y â¨[ F ] x) â¤ (x â¨[ F ] y)) holds
   Îł = â¨[ F ]-least (â¨[ F ]-upperâ x y) (â¨[ F ]-upperâ x y)

â¨[_]-assoc : (F : frame đ¤ đĽ đŚ)
           â (x y z : â¨ F âŠ)
           â (x â¨[ F ] y) â¨[ F ] z âĄ x â¨[ F ] (y â¨[ F ] z)
â¨[_]-assoc F x y z =
 â¤-is-antisymmetric (poset-of F) (â¨[ F ]-least Î˛ Îł) (â¨[ F ]-least Î´ Îľ)
 where
  open PosetNotation  (poset-of F)
  open PosetReasoning (poset-of F)

  Îˇ : (y â¤ ((x â¨[ F ] y) â¨[ F ] z)) holds
  Îˇ = y                     â¤â¨ â¨[ F ]-upperâ x y            âŠ
      x â¨[ F ] y            â¤â¨ â¨[ F ]-upperâ (x â¨[ F ] y) z âŠ
      (x â¨[ F ] y) â¨[ F ] z â 

  Î¸ : (y â¤ (x â¨[ F ] (y â¨[ F ] z))) holds
  Î¸ = y                     â¤â¨ â¨[ F ]-upperâ y z            âŠ
      y â¨[ F ] z            â¤â¨ â¨[ F ]-upperâ x (y â¨[ F ] z) âŠ
      x â¨[ F ] (y â¨[ F ] z) â 

  Î´ : (x â¤ ((x â¨[ F ] y) â¨[ F ] z)) holds
  Î´ = x                     â¤â¨ â¨[ F ]-upperâ x y            âŠ
      x â¨[ F ] y            â¤â¨ â¨[ F ]-upperâ (x â¨[ F ] y) z âŠ
      (x â¨[ F ] y) â¨[ F ] z â 

  Îľ : ((y â¨[ F ] z) â¤ ((x â¨[ F ] y) â¨[ F ] z)) holds
  Îľ = â¨[ F ]-least Îˇ (â¨[ F ]-upperâ (x â¨[ F ] y) z)

  Î˛ : ((x â¨[ F ] y) â¤ (x â¨[ F ] (y â¨[ F ] z))) holds
  Î˛ = â¨[ F ]-least (â¨[ F ]-upperâ x (y â¨[ F ] z)) Î¸

  Îł : (z â¤ (x â¨[ F ] (y â¨[ F ] z))) holds
  Îł = z                      â¤â¨ â¨[ F ]-upperâ y z            âŠ
      y â¨[ F ] z             â¤â¨ â¨[ F ]-upperâ x (y â¨[ F ] z) âŠ
      x â¨[ F ] (y â¨[ F ] z)  â 

\end{code}

By fixing the left or right argument of `_â¨_` to anything, we get a monotonic
map.

\begin{code}

â¨[_]-left-monotone : (F : frame đ¤ đĽ đŚ)
               â {x y z : â¨ F âŠ}
               â (x â¤[ poset-of F ] y) holds
               â ((x â¨[ F ] z) â¤[ poset-of F ] (y â¨[ F ] z)) holds
â¨[_]-left-monotone F {x = x} {y} {z} p = â¨[ F ]-least Îł (â¨[ F ]-upperâ y z)
 where
  open PosetNotation  (poset-of F) using (_â¤_)
  open PosetReasoning (poset-of F)

  Îł : (x â¤ (y â¨[ F ] z)) holds
  Îł = x â¤â¨ p âŠ y â¤â¨ â¨[ F ]-upperâ y z âŠ y â¨[ F ] z â 

â¨[_]-right-monotone : (F : frame đ¤ đĽ đŚ)
                â {x y z : â¨ F âŠ}
                â (x â¤[ poset-of F ] y) holds
                â ((z â¨[ F ] x) â¤[ poset-of F ] (z â¨[ F ] y)) holds
â¨[_]-right-monotone F {x} {y} {z} p =
 z â¨[ F ] x  âĄâ¨ â¨[ F ]-is-commutative z x âŠâ
 x â¨[ F ] z  â¤â¨ â¨[ F ]-left-monotone p    âŠ
 y â¨[ F ] z  âĄâ¨ â¨[ F ]-is-commutative y z âŠâ
 z â¨[ F ] y  â 
  where
   open PosetReasoning (poset-of F)

\end{code}

\begin{code}

đ[_] : (F : frame đ¤ đĽ đŚ) â â¨ F âŠ
đ[ F ] = â[ F ] đ , Îť ()

đ-is-bottom : (F : frame đ¤ đĽ đŚ)
            â (x : â¨ F âŠ) â (đ[ F ] â¤[ poset-of F ] x) holds
đ-is-bottom F x = â[ F ]-least (đ , Îť ()) (x , Îť ())

only-đ-is-below-đ : (F : frame đ¤ đĽ đŚ) (x : â¨ F âŠ)
                  â (x â¤[ poset-of F ] đ[ F ]) holds â x âĄ đ[ F ]
only-đ-is-below-đ F x p =
 â¤-is-antisymmetric (poset-of F) p (đ-is-bottom F x)

đ-is-unique : (F : frame đ¤ đĽ đŚ) (b : â¨ F âŠ)
            â ((x : â¨ F âŠ) â (b â¤[ poset-of F ] x) holds) â b âĄ đ[ F ]
đ-is-unique F b Ď = only-đ-is-below-đ F b (Ď đ[ F ])

đ-right-unit-of-â¨ : (F : frame đ¤ đĽ đŚ) (x : â¨ F âŠ) â đ[ F ] â¨[ F ] x âĄ x
đ-right-unit-of-â¨ {đŚ = đŚ} F x = â¤-is-antisymmetric (poset-of F) Î˛ Îł
 where
  open PosetNotation (poset-of F)

  Î˛ : ((đ[ F ] â¨[ F ] x) â¤ x) holds
  Î˛ = â¨[ F ]-least (đ-is-bottom F x) (â¤-is-reflexive (poset-of F) x)

  Îł : (x â¤ (đ[ F ] â¨[ F ] x)) holds
  Îł = â[ F ]-upper (binary-family đŚ đ[ F ] x) (inr â)

đ-left-unit-of-â¨ : (F : frame đ¤ đĽ đŚ) (x : â¨ F âŠ) â x â¨[ F ] đ[ F ] âĄ x
đ-left-unit-of-â¨ {đŚ = đŚ} F x =
 x â¨[ F ] đ[ F ]  âĄâ¨ â¨[ F ]-is-commutative x đ[ F ] âŠ
 đ[ F ] â¨[ F ] x  âĄâ¨ đ-right-unit-of-â¨ F x          âŠ
 x                â

\end{code}

\begin{code}

distributivity : (F : frame đ¤ đĽ đŚ)
               â (x : â¨ F âŠ)
               â (U : Fam đŚ â¨ F âŠ)
               â let open JoinNotation (Îť - â â[ F ] -) in
                 x â§[ F ] (ââ¨ i âŠ (U [ i ]))
               âĄ ââ¨ i âŠ (x â§[ F ] (U [ i ]))
distributivity (_ , _ , _ , (_ , _ , _ , d)) x U = d (x , U)

\end{code}

\section{Frame homomorphisms}

\begin{code}

is-a-frame-homomorphism : (F : frame đ¤  đĽ  đŚ)
                          (G : frame đ¤â˛ đĽâ˛ đŚâ˛)
                        â (â¨ F âŠ â â¨ G âŠ)
                        â ÎŠ (đ¤ â đŚ âş â đ¤â˛ â đĽâ˛)
is-a-frame-homomorphism {đŚ = đŚ} F G f = Îą â§ Î˛ â§ Îł
 where
  P = poset-of G

  iss : is-set â¨ G âŠ
  iss = carrier-of-[ P ]-is-set

  open Joins (Îť x y â x â¤[ P ] y)

  Îą = f đ[ F ] âĄ[ iss ]âĄ đ[ G ]
  Î˛ = âąŻ (x , y) âś â¨ F âŠ Ă â¨ F âŠ , (f (x â§[ F ] y) âĄ[ iss ]âĄ f x â§[ G ] f y)
  Îł = âąŻ U âś Fam đŚ â¨ F âŠ , f (â[ F ] U) is-lub-of â f x âŁ x Îľ U â

_âfâ_ : frame đ¤ đĽ đŚ â frame đ¤â˛ đĽâ˛ đŚâ˛ â đ¤ â đŚ âş â đ¤â˛ â đĽâ˛ Ě
F âfâ G =
 ÎŁ f ę (â¨ F âŠ â â¨ G âŠ) , is-a-frame-homomorphism F G f holds

is-monotonic : (P : poset đ¤ đĽ) (Q : poset đ¤â˛ đĽâ˛)
             â (prâ P â prâ Q) â ÎŠ (đ¤ â đĽ â đĽâ˛)
is-monotonic P Q f =
 âąŻ (x , y) âś (prâ P Ă prâ P) , ((x â¤[ P ] y) â f x â¤[ Q ] f y)

\end{code}

\section{Some properties of frames}

\begin{code}

â§[_]-unique : (F : frame đ¤ đĽ đŚ) {x y z : â¨ F âŠ}
            â let open Meets (Îť x y â x â¤[ poset-of F ] y) in
              (z is-glb-of (x , y)) holds â z âĄ (x â§[ F ] y)
â§[ F ]-unique {x} {y} {z} (p , q) = â¤-is-antisymmetric (poset-of F) Î˛ Îł
 where
  Î˛ : (z â¤[ poset-of F ] (x â§[ F ] y)) holds
  Î˛ = â§[ F ]-greatest x y z (prâ p) (prâ p)

  Îł : ((x â§[ F ] y) â¤[ poset-of F ] z) holds
  Îł = q ((x â§[ F ] y) , â§[ F ]-lowerâ x y , â§[ F ]-lowerâ x y)

\end{code}

\begin{code}

â[_]-unique : (F : frame đ¤ đĽ đŚ) (U : Fam đŚ â¨ F âŠ) (u : â¨ F âŠ)
         â let open Joins (Îť x y â x â¤[ poset-of F ] y) in
           (u is-lub-of U) holds â u âĄ â[ F ] U
â[_]-unique F U u (p , q) = â¤-is-antisymmetric (poset-of F) Îł Î˛
 where
  open PosetNotation (poset-of F)

  Îł : (u â¤ (â[ F ] U)) holds
  Îł = q ((â[ F ] U) , â[ F ]-upper U)

  Î˛ : ((â[ F ] U) â¤ u) holds
  Î˛ = â[ F ]-least U (u , p)

connecting-lemmaâ : (F : frame đ¤ đĽ đŚ) (x y : â¨ F âŠ)
                  â (x â¤[ poset-of F ] y) holds
                  â x âĄ x â§[ F ] y
connecting-lemmaâ F x y p = â§[ F ]-unique (Î˛ , Îł)
 where
  open Meets (Îť x y â x â¤[ poset-of F ] y)

  Î˛ : (x is-a-lower-bound-of (x , y)) holds
  Î˛ = â¤-is-reflexive (poset-of F) x , p

  Îł : (âąŻ (z , _) âś lower-bound (x , y) , z â¤[ poset-of F ] x) holds
  Îł (z , q , _) = q

connecting-lemmaâ : (F : frame đ¤ đĽ đŚ) {x y : â¨ F âŠ}
                  â x âĄ x â§[ F ] y
                  â (x â¤[ poset-of F ] y) holds
connecting-lemmaâ F {x} {y} p = x âĄâ¨ p âŠâ x â§[ F ] y â¤â¨ â§[ F ]-lowerâ x y âŠ y â 
 where
  open PosetReasoning (poset-of F)

frame-morphisms-are-monotonic : (F : frame đ¤  đĽ  đŚ)
                                (G : frame đ¤â˛ đĽâ˛ đŚâ˛)
                              â (f : â¨ F âŠ â â¨ G âŠ)
                              â is-a-frame-homomorphism F G f holds
                              â is-monotonic (poset-of F) (poset-of G) f holds
frame-morphisms-are-monotonic F G f (_ , Ď , _) (x , y) p =
 f x            â¤â¨ i                         âŠ
 f (x â§[ F ] y) â¤â¨ ii                        âŠ
 f x â§[ G ] f y â¤â¨ â§[ G ]-lowerâ (f x) (f y) âŠ
 f y            â 
  where
   open PosetReasoning (poset-of G)

   i  = reflexivity+ (poset-of G) (ap f (connecting-lemmaâ F x y p))
   ii = reflexivity+ (poset-of G) (Ď (x , y))


\end{code}

\begin{code}

â§[_]-is-commutative : (F : frame đ¤ đĽ đŚ) (x y : â¨ F âŠ)
                 â x â§[ F ] y âĄ y â§[ F ] x
â§[ F ]-is-commutative x y = â§[ F ]-unique (Î˛ , Îł)
 where
  open Meets (Îť x y â x â¤[ poset-of F ] y)
  open PosetNotation (poset-of F) using (_â¤_)

  Î˛ : ((x â§[ F ] y) is-a-lower-bound-of (y , x)) holds
  Î˛ = (â§[ F ]-lowerâ x y) , (â§[ F ]-lowerâ x y)

  Îł : (âąŻ (l , _) âś lower-bound (y , x) , l â¤ (x â§[ F ] y)) holds
  Îł (l , p , q) = â§[ F ]-greatest x y l q p

\end{code}

\begin{code}

đ-right-annihilator-for-â§ : (F : frame đ¤ đĽ đŚ) (x : â¨ F âŠ)
                          â x â§[ F ] đ[ F ] âĄ đ[ F ]
đ-right-annihilator-for-â§ F x =
 only-đ-is-below-đ F (x â§[ F ] đ[ F ]) (â§[ F ]-lowerâ x đ[ F ])

đ-left-annihilator-for-â§ : (F : frame đ¤ đĽ đŚ) (x : â¨ F âŠ)
                         â đ[ F ] â§[ F ] x âĄ đ[ F ]
đ-left-annihilator-for-â§ F x =
 đ[ F ] â§[ F ] x  âĄâ¨ â§[ F ]-is-commutative đ[ F ] x âŠ
 x â§[ F ] đ[ F ]  âĄâ¨ đ-right-annihilator-for-â§ F x  âŠ
 đ[ F ]           â

đ-right-annihilator-for-â¨ : (F : frame đ¤ đĽ đŚ) (x : â¨ F âŠ)
                          â x â¨[ F ] đ[ F ] âĄ đ[ F ]
đ-right-annihilator-for-â¨ F x =
 only-đ-is-above-đ F (x â¨[ F ] đ[ F ]) (â¨[ F ]-upperâ x đ[ F ])

đ-left-annihilator-for-â¨ : (F : frame đ¤ đĽ đŚ) (x : â¨ F âŠ)
                         â đ[ F ] â¨[ F ] x âĄ đ[ F ]
đ-left-annihilator-for-â¨ F x =
 đ[ F ] â¨[ F ] x  âĄâ¨ â¨[ F ]-is-commutative đ[ F ] x âŠ
 x â¨[ F ] đ[ F ]  âĄâ¨ đ-right-annihilator-for-â¨ F x  âŠ
 đ[ F ] â

\end{code}

\begin{code}

distributivityâ˛ : (F : frame đ¤ đĽ đŚ)
                â (x : â¨ F âŠ)
                â (S : Fam đŚ â¨ F âŠ)
                â let open JoinNotation (Îť - â â[ F ] -) in
                  x â§[ F ] (ââ¨ i âŠ (S [ i ]))
                âĄ ââ¨ i âŠ ((S [ i ]) â§[ F ] x)
distributivityâ˛ F x S =
 x â§[ F ] (ââ¨ i âŠ S [ i ])    âĄâ¨ distributivity F x S âŠ
 ââ¨ i âŠ (x â§[ F ] (S [ i ]))  âĄâ¨ â                     âŠ
 ââ¨ i âŠ (S [ i ]) â§[ F ] x    â
  where
   open PosetReasoning (poset-of F)
   open JoinNotation (Îť - â â[ F ] -)

   âĄ = â§[ F ]-is-commutative x â (_[_] S)
   â  = ap (Îť - â join-of F (index S , -)) (dfunext fe âĄ)

binary-distributivity : (F : frame đ¤ đĽ đŚ)
                      â (x y z : â¨ F âŠ)
                      â x â§[ F ] (y â¨[ F ] z) âĄ (x â§[ F ] y) â¨[ F ] (x â§[ F ] z)
binary-distributivity {đŚ = đŚ} F x y z =
 x â§[ F ] (y â¨[ F ] z)                            âĄâ¨ â  âŠ
 â[ F ] â x â§[ F ] w âŁ w Îľ binary-family đŚ y z â  âĄâ¨ âĄ âŠ
 (x â§[ F ] y) â¨[ F ] (x â§[ F ] z)                 â
  where
   â  = distributivity F x (binary-family đŚ y z)
   âĄ = ap (Îť - â join-of F -) (fmap-binary-family đŚ (Îť - â x â§[ F ] -) y z)

\end{code}

\begin{code}

â[_]-iterated-join : (F : frame đ¤ đĽ đŚ) (I : đŚ Ě) (J : I â đŚ Ě)
                â (f : (i : I) â J i â â¨ F âŠ)
                â â[ F ] ((ÎŁ i ę I , J i) , uncurry f)
                âĄ â[ F ] â â[ F ] â f i j âŁ j âś J i â âŁ i âś I â
â[ F ]-iterated-join I J f = â[ F ]-unique _ _ (Î˛ , Îł)
 where
  open Joins (Îť x y â x â¤[ poset-of F ] y)
  open PosetReasoning (poset-of F) renaming (_â  to _QED)

  Î˛ : ((â[ F ] (ÎŁ J , uncurry f))
      is-an-upper-bound-of
      â â[ F ] â f i j âŁ j âś J i â âŁ i âś I â) holds
  Î˛ i = â[ F ]-least _ (_ , Îť jáľ˘ â â[ F ]-upper _ (i , jáľ˘))

  Îł : (âąŻ (u , _) âś upper-bound â â[ F ] â f i j âŁ j âś J i â âŁ i âś I â ,
       (â[ F ] (ÎŁ J , uncurry f)) â¤[ poset-of F ] _ ) holds
  Îł (u , p) = â[ F ]-least (ÎŁ J , uncurry f) (_ , Î´)
   where
    Î´ : (u is-an-upper-bound-of (ÎŁ J , uncurry f)) holds
    Î´  (i , j) = f i j                      â¤â¨ â[ F ]-upper _ j âŠ
                 â[ F ] â f i j âŁ j âś J i â â¤â¨ p i              âŠ
                 u                          QED

\end{code}

\begin{code}

â§[_]-is-idempotent : (F : frame đ¤ đĽ đŚ)
                   â (x : â¨ F âŠ) â x âĄ x â§[ F ] x
â§[ F ]-is-idempotent x = â¤-is-antisymmetric (poset-of F) Î˛ Îł
 where
  Îą : (x â¤[ poset-of F ] x) holds
  Îą = â¤-is-reflexive (poset-of F) x

  Î˛ : (x â¤[ poset-of F ] (x â§[ F ] x)) holds
  Î˛ = â§[ F ]-greatest x x x Îą Îą

  Îł : ((x â§[ F ] x) â¤[ poset-of F ] x) holds
  Îł = â§[ F ]-lowerâ x x

\end{code}

\begin{code}

distributivity+ : (F : frame đ¤ đĽ đŚ)
                â let open JoinNotation (Îť - â â[ F ] -) in
                  (U@(I , _) V@(J , _) : Fam đŚ â¨ F âŠ)
                â (ââ¨ i âŠ (U [ i ])) â§[ F ] (ââ¨ j âŠ (V [ j ]))
                âĄ (ââ¨ (i , j) âś (I Ă J)  âŠ ((U [ i ]) â§[ F ] (V [ j ])))
distributivity+ F U@(I , _) V@(J , _) =
 (ââ¨ i âŠ (U [ i ])) â§[ F ] (ââ¨ j âŠ (V [ j ]))     âĄâ¨ i   âŠ
 (ââ¨ j âŠ (V [ j ])) â§[ F ] (ââ¨ i âŠ (U [ i ]))     âĄâ¨ ii  âŠ
 (ââ¨ i âŠ (ââ¨ j âŠ (V [ j ])) â§[ F ] (U [ i ]))     âĄâ¨ iii âŠ
 (ââ¨ i âŠ (U [ i ] â§[ F ] (ââ¨ j âŠ (V [ j ]))))     âĄâ¨ iv  âŠ
 (ââ¨ i âŠ (ââ¨ j âŠ (U [ i ] â§[ F ] V [ j ])))       âĄâ¨ v   âŠ
 (ââ¨ (i , j) âś I Ă J  âŠ (U [ i ] â§[ F ] V [ j ])) â
 where
  open JoinNotation (Îť - â â[ F ] -)

  i   = â§[ F ]-is-commutative (ââ¨ i âŠ (U [ i ])) (ââ¨ j âŠ (V [ j ]))
  ii  = distributivity F (ââ¨ j âŠ (V [ j ])) U
  iii = ap
         (Îť - â â[ F ] (I , -))
         (dfunext fe Îť i â â§[ F ]-is-commutative (ââ¨ j âŠ V [ j ]) (U [ i ]))
  iv  = ap
         (Îť - â join-of F (I , -))
         (dfunext fe Îť i â distributivity F (U [ i ]) V)
  v   = â[ F ]-iterated-join I (Îť _ â J) (Îť i j â U [ i ] â§[ F ] V [ j ]) âťÂš

\end{code}

\section{Bases of frames}

We first define the notion of a âsmallâ basis for a frame. Given a
(đ¤, đĽ, đŚ)-frame, a small basis for it is a đŚ-family, which has a
further subfamily covering any given element of the frame.

\begin{code}

is-basis-for : (F : frame đ¤ đĽ đŚ) â Fam đŚ â¨ F âŠ â (đ¤ â đĽ â đŚ âş) Ě
is-basis-for {đŚ = đŚ} F (I , Î˛) =
 (x : â¨ F âŠ) â ÎŁ J ę (Fam đŚ I) , (x is-lub-of â Î˛ j âŁ j Îľ J â) holds
  where
   open Joins (Îť x y â x â¤[ poset-of F ] y)

\end{code}

A đŚ-frame has a (small) basis iff there exists a đŚ-family
that forms a basis for it. Having a basis should be a property and
not a structure so this is important.

\begin{code}

has-basis : (F : frame đ¤ đĽ đŚ) â ÎŠ (đ¤ â đĽ â đŚ âş)
has-basis {đŚ = đŚ} F = âĽ ÎŁ âŹ ę Fam đŚ â¨ F âŠ , is-basis-for F âŹ âĽÎŠ

\end{code}

We also have the notion of a directed basis, in which every covering
family is directed.

\begin{code}

is-directed : (F : frame đ¤ đĽ đŚ) â Fam đŚ â¨ F âŠ â ÎŠ (đĽ â đŚ)
is-directed F (I , Î˛) =
   âĽ I âĽÎŠ
 â§ (âąŻ i âś I , âąŻ j âś I , (Ć k âś I , ((Î˛ i â¤ Î˛ k) â§ (Î˛ j â¤ Î˛ k)) holds))
  where open PosetNotation (poset-of F)

has-directed-basis : (F : frame đ¤ đĽ đŚ) â ÎŠ (đ¤ â đĽ â đŚ âş)
has-directed-basis {đŚ = đŚ} F =
 âĽ ÎŁ âŹ ę Fam đŚ â¨ F âŠ
 , ÎŁ b ę is-basis-for F âŹ ,
    Î  x ę â¨ F âŠ ,
     is-directed F (â âŹ [ i ] âŁ i Îľ prâ (b x) â) holds âĽÎŠ

\end{code}

The main development in this section is that every small basis can be
extended to a directed one whilst keeping it small.

\begin{code}

directify : (F : frame đ¤ đĽ đŚ) â Fam đŚ â¨ F âŠ â Fam đŚ â¨ F âŠ
directify F (I , Îą) = List I , (foldr (Îť i - â Îą i â¨[ F ] -) đ[ F ])
 where open PosetNotation (poset-of F)

\end{code}

Note that `directify` is a monoid homomorphism from the free monoid on I
to (_â¨_, đ).

\begin{code}

directify-functorial : (F : frame đ¤ đĽ đŚ) (S : Fam đŚ â¨ F âŠ)
                     â (is js : List (index S))
                     â directify F S [ is ++ js ]
                     âĄ directify F S [ is ] â¨[ F ] directify F S [ js ]
directify-functorial F S@(I , Îą) = Îł
 where
  Îł : (is js : List I)
    â directify F S [ is ++ js ]
    âĄ directify F S [ is ] â¨[ F ] directify F S [ js ]
  Îł []       js = directify F S [ [] ++ js ]          âĄâ¨ refl âŠ
                  directify F S [ js ]                âĄâ¨ â     âŠ
                  đ[ F ]  â¨[ F ] directify F S [ js ] â
                   where
                    â  = đ-right-unit-of-â¨ F (directify F S [ js ]) âťÂš
  Îł (i âˇ is) js =
   directify F S [ (i âˇ is) ++ js ]                              âĄâ¨ refl âŠ
   Îą i â¨[ F ] directify F S [ is ++ js ]                         âĄâ¨ â     âŠ
   Îą i â¨[ F ] (directify F S [ is ] â¨[ F ] directify F S [ js ]) âĄâ¨ âĄ    âŠ
   (Îą i â¨[ F ] directify F S [ is ]) â¨[ F ] directify F S [ js ] âĄâ¨ refl âŠ
   directify F S [ i âˇ is ] â¨[ F ] directify F S [ js ]          â
    where
     â  = ap (Îť - â binary-join F (Îą i) -) (Îł is js)
     âĄ = â¨[ F ]-assoc (Îą i) (directify F S [ is ]) (directify F S [ js ]) âťÂš

\end{code}

`directify` does what it is supposed to do: the family it gives is a
directed one.

\begin{code}

directify-is-directed : (F : frame đ¤ đĽ đŚ) (S : Fam đŚ â¨ F âŠ)
                      â is-directed F (directify F S) holds
directify-is-directed F S@(I , Îą) = âŁ [] âŁ , Ď
 where
  open PropositionalTruncation pt
  open PosetNotation (poset-of F)

  Ď : (âąŻ is âś List I
     , âąŻ js âś List I
     , (Ć ks âś List I
      , (((directify F S [ is ] â¤ directify F S [ ks ])
        â§ (directify F S [ js ] â¤ directify F S [ ks ])) holds))) holds
  Ď is js = âŁ (is ++ js) , Î˛ , Îł âŁ
    where
     open PosetReasoning (poset-of F)

     âĄ = directify-functorial F S is js âťÂš

     Î˛ : (directify F S [ is ] â¤ directify F S [ is ++ js ]) holds
     Î˛ = directify F S [ is ]                             â¤â¨ â  âŠ
         directify F S [ is ] â¨[ F ] directify F S [ js ] âĄâ¨ âĄ âŠâ
         directify F S [ is ++ js ]                       â 
          where
           â  = â¨[ F ]-upperâ (directify F S [ is ]) (directify F S [ js ])

     Îł : (directify F S [ js ] â¤ directify F S [ is ++ js ]) holds
     Îł = directify F S [ js ]                             â¤â¨ â  âŠ
         directify F S [ is ] â¨[ F ] directify F S [ js ] âĄâ¨ âĄ âŠâ
         directify F S [ is ++ js ] â 
          where
           â  = â¨[ F ]-upperâ (directify F S [ is ]) (directify F S [ js ])

\end{code}

`directify` also preserves the join while doing what it is supposed to
do.

\begin{code}

directify-preserves-joins : (F : frame đ¤ đĽ đŚ) (S : Fam đŚ â¨ F âŠ)
                          â â[ F ] S âĄ â[ F ] directify F S
directify-preserves-joins F S = â¤-is-antisymmetric (poset-of F) Î˛ Îł
 where
  open PosetNotation  (poset-of F)
  open PosetReasoning (poset-of F)

  Î˛ : ((â[ F ] S) â¤ (â[ F ] directify F S)) holds
  Î˛ = â[ F ]-least S ((â[ F ] (directify F S)) , Î˝)
   where
    Î˝ : (i : index S) â (S [ i ] â¤ (â[ F ] directify F S)) holds
    Î˝ i =
     S [ i ]                   âĄâ¨ đ-right-unit-of-â¨ F (S [ i ]) âťÂš       âŠâ
     đ[ F ] â¨[ F ] S [ i ]     âĄâ¨ â¨[ F ]-is-commutative đ[ F ] (S [ i ]) âŠâ
     S [ i ] â¨[ F ] đ[ F ]     âĄâ¨ refl                                   âŠâ
     directify F S [ i âˇ [] ]  â¤â¨ â[ F ]-upper (directify F S) (i âˇ [])  âŠ
     â[ F ] directify F S      â 

  Îł : ((â[ F ] directify F S) â¤[ poset-of F ] (â[ F ] S)) holds
  Îł = â[ F ]-least (directify F S) ((â[ F ] S) , Îş)
   where
    Îş : (is : List (index S)) â ((directify F S [ is ]) â¤ (â[ F ] S)) holds
    Îş []       = đ-is-bottom F (â[ F ] S)
    Îş (i âˇ is) = S [ i ] â¨[ F ] directify F S [ is ] â¤â¨ â  âŠ
                 â[ F ] S                              â 
                  where
                   â  = â¨[ F ]-least (â[ F ]-upper S i) (Îş is)

directify-preserves-joinsâ : (F : frame đ¤ đĽ đŚ) (S : Fam đŚ â¨ F âŠ)
                           â let open Joins (Îť x y â x â¤[ poset-of F ] y) in
                             (x : â¨ F âŠ)
                           â (x is-lub-of S â x is-lub-of directify F S) holds
directify-preserves-joinsâ F S x p =
 transport (Îť - â (- is-lub-of directify F S) holds) (q âťÂš)
  (â[ F ]-upper (directify F S) , â[ F ]-least (directify F S))
 where
  open Joins (Îť x y â x â¤[ poset-of F ] y)

  q : x âĄ â[ F ] directify F S
  q = x                    âĄâ¨ â[ F ]-unique S x p           âŠ
      â[ F ] S             âĄâ¨ directify-preserves-joins F S âŠ
      â[ F ] directify F S â

\end{code}

\begin{code}

directify-basis : (F : frame đ¤ đĽ đŚ)
                â (has-basis F â has-directed-basis F) holds
directify-basis {đŚ = đŚ} F = âĽâĽ-rec (holds-is-prop (has-directed-basis F)) Îł
 where
  open PropositionalTruncation pt
  open PosetNotation (poset-of F)
  open Joins (Îť x y â x â¤ y)

  Îł : ÎŁ âŹ ę Fam đŚ â¨ F âŠ , is-basis-for F âŹ â has-directed-basis F holds
  Îł (âŹ@(I , _) , b) = âŁ directify F âŹ , Î˛ , Î´ âŁ
   where
    đĽ : â¨ F âŠ â Fam đŚ I
    đĽ x = prâ (b x)

    đŚ : â¨ F âŠ â Fam đŚ (List I)
    đŚ x = List (index (đĽ x)) , (Îť - â đĽ x [ - ]) <$>_

    Ď : (x : â¨ F âŠ)
      â (is : List (index (đĽ x)))
      â directify F âŹ [ (Îť - â đĽ x [ - ]) <$> is ]
      âĄ directify F â âŹ [ j ] âŁ j Îľ đĽ x â [ is ]
    Ď x []       = refl
    Ď x (i âˇ is) = ap (Îť - â (_ â¨[ F ] -)) (Ď x is)

    Ď : (x : â¨ F âŠ)
      â â directify F âŹ [ is ] âŁ is Îľ đŚ x â âĄ directify F â âŹ [ j ] âŁ j Îľ đĽ x â
    Ď x = to-ÎŁ-âĄ (refl , dfunext fe (Ď x))

    Î˛ : (x : â¨ F âŠ)
      â ÎŁ J ę Fam đŚ (List I)
        , (x is-lub-of â directify F âŹ [ j ] âŁ j Îľ J â) holds
    Î˛ x = đŚ x , transport (Îť - â (x is-lub-of -) holds) (Ď x âťÂš) Î´
     where
      p : (x is-lub-of â âŹ [ j ] âŁ j Îľ đĽ x â) holds
      p = prâ (b x)

      Î´ : (x is-lub-of directify F â âŹ [ j ] âŁ j Îľ đĽ x â) holds
      Î´ = directify-preserves-joinsâ F â âŹ [ j ] âŁ j Îľ đĽ x â x p

    Î´ : (x : â¨ F âŠ)
      â is-directed F â directify F âŹ [ is ] âŁ is Îľ đŚ x â holds
    Î´ x = transport (Îť - â is-directed F - holds) (Ď x âťÂš) Îľ
     where
      Îľ = directify-is-directed F â âŹ [ j ] âŁ j Îľ đĽ x â

\end{code}

\section{Scott-continuity}

\begin{code}

is-scott-continuous : (F : frame đ¤  đĽ  đŚ)
                    â (G : frame đ¤â˛ đĽâ˛ đŚ)
                    â (f : â¨ F âŠ â â¨ G âŠ)
                    â ÎŠ (đ¤ â đĽ â đŚ âş â đ¤â˛ â đĽâ˛)
is-scott-continuous {đŚ = đŚ} F G f =
 âąŻ S âś Fam đŚ â¨ F âŠ , is-directed F S â f (â[ F ] S) is-lub-of â f s âŁ s Îľ S â
  where
   open Joins (Îť x y â x â¤[ poset-of G ] y) using (_is-lub-of_)

\end{code}
