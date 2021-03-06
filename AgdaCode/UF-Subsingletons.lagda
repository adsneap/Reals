Martin Escardo

In univalent logic, as opposed to Curry-Howard logic, a proposition is
a subsingleton or a type such that any two of its elements are
identified.

https://www.newton.ac.uk/files/seminar/20170711100011001-1009756.pdf
https://unimath.github.io/bham2017/uf.pdf

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Subsingletons where

open import SpartanMLTT
open import Unit-Properties

open import Plus-Properties
open import UF-Base

is-prop : ð¤ Ì â ð¤ Ì
is-prop X = (x y : X) â x â¡ y

\end{code}
c
And of course we could adopt a terminology borrowed from topos logic:

\begin{code}

is-truth-value is-subsingleton : ð¤ Ì â ð¤ Ì
is-truth-value  = is-prop
is-subsingleton = is-prop

\end{code}

\begin{code}

Î£-is-prop : {X : ð¤ Ì } {A : X â ð¥ Ì }
          â is-prop X â ((x : X) â is-prop (A x)) â is-prop (Î£ A)
Î£-is-prop {ð¤} {ð¥} {X} {A} i j (x , a) (y , b) =
  to-Î£-â¡ (i x y , j y (transport A (i x y) a) b)

\end{code}

Next we define singleton (or contractible types). The terminology
"contractible" is due to Voevodsky. I currently prefer the terminology
"singleton type", because it makes more sense when we consider
univalent type theory as interesting on its own right independently of
its homotopical (originally motivating) models. Also it emphasizes
that we don't require homotopy theory as a prerequisite to understand
univalent type theory.

\begin{code}

is-central : (X : ð¤ Ì ) â X â ð¤ Ì
is-central X c = (x : X) â c â¡ x

is-singleton : ð¤ Ì â ð¤ Ì
is-singleton X = Î£ c ê X , is-central X c

center : {X : ð¤ Ì } â is-singleton X â X
center = prâ

centrality : {X : ð¤ Ì } (i : is-singleton X) â is-central X (center i)
centrality = prâ

\end{code}

For compatibility with the homotopical terminology:

\begin{code}

is-center-of-contraction-of : (X : ð¤ Ì ) â X â ð¤ Ì
is-center-of-contraction-of = is-central

is-contr : ð¤ Ì â ð¤ Ì
is-contr = is-singleton

ð-is-singleton : is-singleton (ð {ð¤})
ð-is-singleton = â , (Î» (x : ð) â (ð-all-â x)â»Â¹)

singletons-are-props : {X : ð¤ Ì } â is-singleton X â is-prop X
singletons-are-props (c , Ï) x y = x â¡â¨ (Ï x) â»Â¹ â©
                                   c â¡â¨ Ï y â©
                                   y â

prop-criterion' : {X : ð¤ Ì } â (X â is-singleton X) â is-prop X
prop-criterion' Ï x = singletons-are-props (Ï x) x

prop-criterion : {X : ð¤ Ì } â (X â is-prop X) â is-prop X
prop-criterion Ï x = Ï x x

pointed-props-are-singletons : {X : ð¤ Ì } â X â is-prop X â is-singleton X
pointed-props-are-singletons x h = x , h x

\end{code}

The two prototypical propositions:

\begin{code}

ð-is-prop : is-prop (ð {ð¤})
ð-is-prop {ð¤} x y = unique-from-ð {ð¤} {ð¤} x

ð-is-prop : is-prop (ð {ð¤})
ð-is-prop {ð¤} â â = refl {ð¤}

\end{code}

A type is a set if all its identity types are subsingletons. In other
words, sets are types for which equality is a proposition (rather than
data or structure).

\begin{code}

is-h-isolated : {X : ð¤ Ì } (x : X) â ð¤ Ì
is-h-isolated x = â {y} â is-prop (x â¡ y)

is-set : ð¤ Ì â ð¤ Ì
is-set X = {x : X} â is-h-isolated x

hSet : (ð¤ : Universe) â ð¤ âº Ì
hSet ð¤ = Î£ A ê ð¤ Ì , is-set A

underlying-set : hSet ð¤ â ð¤ Ì
underlying-set = prâ

ð-is-set : is-set (ð {ð¤})
ð-is-set {ð¤} {x} = ð-elim x

refl-is-set : (X : ð¤ Ì )
            â ((x : X) (p : x â¡ x) â p â¡ refl)
            â is-set X
refl-is-set X r {x} {.x} p refl = r x p

\end{code}

We now consider some machinery for dealing with the above notions,
using weakly, or wildly, constant maps:

\begin{code}

wconstant : {X : ð¤ Ì } {Y : ð¥ Ì } â (f : X â Y) â ð¤ â ð¥ Ì
wconstant f = â x y â f x â¡ f y

wconstant-pre-comp : {X : ð¤ Ì } {Y : ð¥ Ì } {Z : ð¦ Ì } (f : X â Y) (g : Y â Z)
                   â wconstant f â wconstant (g â f)
wconstant-pre-comp f g c x x' = ap g (c x x')

wconstant-post-comp : {X : ð¤ Ì } {Y : ð¥ Ì } {Z : ð¦ Ì } (f : X â Y) (g : Y â Z)
                    â wconstant g â wconstant (g â f)
wconstant-post-comp f g c x x' = c (f x) (f x')

collapsible : ð¤ Ì â ð¤ Ì
collapsible X = Î£ f ê (X â X) , wconstant f

Id-collapsible : ð¤ Ì â ð¤ Ì
Id-collapsible X = {x y : X} â collapsible (x â¡ y)

sets-are-Id-collapsible : {X : ð¤ Ì } â is-set X â Id-collapsible X
sets-are-Id-collapsible u = (id , u)

local-hedberg : {X : ð¤ Ì } (x : X)
              â ((y : X) â collapsible (x â¡ y))
              â (y : X) â is-prop (x â¡ y)
local-hedberg {ð¤} {X} x pc y p q =
 p                    â¡â¨ c y p â©
 f x refl â»Â¹ â f y p  â¡â¨ ap (Î» - â (f x refl)â»Â¹ â -) (Îº y p q) â©
 f x refl â»Â¹ â f y q  â¡â¨ (c y q)â»Â¹ â©
 q                    â
 where
  f : (y : X) â x â¡ y â x â¡ y
  f y = prâ (pc y)
  Îº : (y : X) (p q : x â¡ y) â f y p â¡ f y q
  Îº y = prâ (pc y)
  c : (y : X) (r : x â¡ y) â r â¡ (f x refl)â»Â¹ â f y r
  c _ refl = sym-is-inverse (f x refl)

Id-collapsibles-are-sets : {X : ð¤ Ì } â Id-collapsible X â is-set X
Id-collapsibles-are-sets pc {x} {y} p q = local-hedberg x (Î» y â (prâ (pc {x} {y})) , (prâ (pc {x} {y}))) y p q

\end{code}

Here is an example. Any type that admits a prop-valued, reflexive and
antisymmetric relation is a set.

\begin{code}

type-with-prop-valued-refl-antisym-rel-is-set : {X : ð¤ Ì }
                                              â (_â¤_ : X â X â ð¥ Ì )
                                              â ((x y : X) â is-prop (x â¤ y))
                                              â ((x : X) â x â¤ x)
                                              â ((x y : X) â x â¤ y â y â¤ x â x â¡ y)
                                              â is-set X
type-with-prop-valued-refl-antisym-rel-is-set {ð¤} {ð¥} {X} _â¤_ â¤-prop-valued â¤-refl â¤-anti = Î³
 where
  Î± : â {x y} (l l' : x â¤ y) (m m' : y â¤ x) â â¤-anti x y l m â¡ â¤-anti x y l' m'
  Î± {x} {y} l l' m m' = apâ (â¤-anti x y)
                            (â¤-prop-valued x y l l')
                            (â¤-prop-valued y x m m')

  g : â {x y} â x â¡ y â x â¤ y
  g {x} p = transport (x â¤_) p (â¤-refl x)

  h : â {x y} â x â¡ y â y â¤ x
  h p = g (p â»Â¹)

  f : â {x y} â x â¡ y â x â¡ y
  f {x} {y} p = â¤-anti x y (g p) (h p)

  Îº : â {x y} p q â f {x} {y} p â¡ f {x} {y} q
  Îº p q = Î± (g p) (g q) (h p) (h q)

  Î³ : is-set X
  Î³ = Id-collapsibles-are-sets (f , Îº)

\end{code}

We also need the following symmetrical version of local Hedberg, which
can be proved by reduction to the above (using the fact that
collapsible types are closed under equivalence), but at this point we
don't have the machinery at our disposal (which is developed in
modules that depend on this one), and hence we prove it directly by
symmetrizing the proof.

\begin{code}

local-hedberg' : {X : ð¤ Ì } (x : X)
               â ((y : X) â collapsible (y â¡ x))
               â (y : X) â is-prop (y â¡ x)
local-hedberg' {ð¤} {X} x pc y p q =
  p                     â¡â¨ c y p â©
  f y p â (f x refl)â»Â¹  â¡â¨  ap (Î» - â - â (f x refl)â»Â¹) (Îº y p q) â©
  f y q â (f x refl)â»Â¹  â¡â¨ (c y q)â»Â¹ â©
  q                     â
 where
  f : (y : X) â y â¡ x â y â¡ x
  f y = prâ (pc y)
  Îº : (y : X) (p q : y â¡ x) â f y p â¡ f y q
  Îº y = prâ (pc y)
  c : (y : X) (r : y â¡ x) â r â¡  (f y r) â (f x refl)â»Â¹
  c _ refl = sym-is-inverse' (f x refl)

props-are-Id-collapsible : {X : ð¤ Ì } â is-prop X â Id-collapsible X
props-are-Id-collapsible h {x} {y} = (Î» p â h x y) , (Î» p q â refl)

props-are-sets : {X : ð¤ Ì } â is-prop X â is-set X
props-are-sets h = Id-collapsibles-are-sets (props-are-Id-collapsible h)

ð-is-collapsible : collapsible (ð {ð¤})
ð-is-collapsible {ð¤} = id , (Î» x y â ð-elim y)

pointed-types-are-collapsible : {X : ð¤ Ì } â X â collapsible X
pointed-types-are-collapsible x = (Î» y â x) , (Î» y y' â refl)

\end{code}

Under Curry-Howard, the function type X â ð is understood as the
negation of X when X is viewed as a proposition. But when X is
understood as a mathematical object, inhabiting the type X â ð amounts
to showing that X is empty. (In fact, assuming univalence, defined
below, the type X â ð is equivalent to the type X â¡ ð
(written (X â ð) â (X â¡ ð)).)

\begin{code}

empty-types-are-collapsible : {X : ð¤ Ì } â is-empty X â collapsible X
empty-types-are-collapsible u = (id , (Î» x x' â unique-from-ð (u x)))

ð-is-collapsible' : collapsible ð
ð-is-collapsible' = empty-types-are-collapsible id

singleton-type : {X : ð¤ Ì } (x : X) â ð¤ Ì
singleton-type x = Î£ y ê type-of x , x â¡ y

singleton-center : {X : ð¤ Ì } (x : X) â singleton-type x
singleton-center x = (x , refl)

singleton-types-are-singletons'' : {X : ð¤ Ì } {x x' : X} (r : x â¡ x') â singleton-center x â¡ (x' , r)
singleton-types-are-singletons'' {ð¤} {X} = J A (Î» x â refl)
 where
  A : (x x' : X) â x â¡ x' â ð¤ Ì
  A x x' r = singleton-center x â¡[ Î£ x' ê X , x â¡ x' ] (x' , r)

singleton-types-are-singletons : {X : ð¤ Ì } (xâ : X) â is-singleton (singleton-type xâ)
singleton-types-are-singletons xâ = singleton-center xâ , (Î» t â singleton-types-are-singletons'' (prâ t))

singleton-types-are-singletons' : {X : ð¤ Ì } {x : X} â is-central (singleton-type x) (x , refl)
singleton-types-are-singletons' {ð¤} {X} (y , refl) = refl

singleton-types-are-props : {X : ð¤ Ì } (x : X) â is-prop (singleton-type x)
singleton-types-are-props x = singletons-are-props (singleton-types-are-singletons x)

singleton-type' : {X : ð¤ Ì } â X â ð¤ Ì
singleton-type' x = Î£ y ê type-of x , y â¡ x

singleton'-center : {X : ð¤ Ì } (x : X) â singleton-type' x
singleton'-center x = (x , refl)

Ã-prop-criterion-necessity : {X : ð¤ Ì } {Y : ð¥ Ì }
                           â is-prop (X Ã Y) â (Y â is-prop X) Ã (X â is-prop Y)
Ã-prop-criterion-necessity i = (Î» y x x' â ap prâ (i (x , y) (x' , y ))) ,
                               (Î» x y y' â ap prâ (i (x , y) (x  , y')))

Ã-prop-criterion : {X : ð¤ Ì } {Y : ð¥ Ì }
                 â (Y â is-prop X) Ã (X â is-prop Y) â is-prop (X Ã Y)
Ã-prop-criterion (i , j) (x , y) (x' , y') = to-Î£-â¡ (i y x x' , j x _ _)

Ã-ð-is-prop : {X : ð¤ Ì } â is-prop (X Ã ð {ð¥})
Ã-ð-is-prop (x , z) _ = ð-elim z

ð-Ã-is-prop : {X : ð¤ Ì } â is-prop (ð {ð¥} Ã X)
ð-Ã-is-prop (z , x) _ = ð-elim z

Ã-is-prop : {X : ð¤ Ì } {Y : ð¥ Ì }
          â is-prop X â is-prop Y â is-prop (X Ã Y)
Ã-is-prop i j = Ã-prop-criterion ((Î» _ â i) , (Î» _ â j))

to-subtype-â¡ : {X : ð¦ Ì } {A : X â ð¥ Ì }
               {x y : X} {a : A x} {b : A y}
             â ((x : X) â is-prop (A x))
             â x â¡ y
             â (x , a) â¡ (y , b)
to-subtype-â¡ {ð¤} {ð¥} {X} {A} {x} {y} {a} {b} s p = to-Î£-â¡ (p , s y (transport A p a) b)

subtype-of-prop-is-prop : {X : ð¤ Ì } {Y : ð¥ Ì } (m : X â Y)
                          â left-cancellable m â is-prop Y â is-prop X
subtype-of-prop-is-prop {ð¤} {ð¥} {X} m lc i x x' = lc (i (m x) (m x'))

subtypes-of-sets-are-sets : {X : ð¤ Ì } {Y : ð¥ Ì } (m : X â Y)
                          â left-cancellable m â is-set Y â is-set X
subtypes-of-sets-are-sets {ð¤} {ð¥} {X} m i h = Id-collapsibles-are-sets (f , g)
 where
  f : {x x' : X} â x â¡ x' â x â¡ x'
  f r = i (ap m r)
  g : {x x' : X} (r s : x â¡ x') â f r â¡ f s
  g r s = ap i (h (ap m r) (ap m s))

prâ-lc : {X : ð¤ Ì } {Y : X â ð¥ Ì } â ({x : X} â is-prop (Y x))
       â left-cancellable (prâ {ð¤} {ð¥} {X} {Y})
prâ-lc f p = to-Î£-â¡ (p , (f _ _))

subsets-of-sets-are-sets : (X : ð¤ Ì ) (Y : X â ð¥ Ì )
                         â is-set X
                         â ({x : X} â is-prop (Y x))
                         â is-set (Î£ x ê X , Y x)
subsets-of-sets-are-sets X Y h p = subtypes-of-sets-are-sets prâ (prâ-lc p) h

inl-lc-is-section : {X : ð¤ Ì } {Y : ð¥ Ì } {x x' : X} â (p : inl {ð¤} {ð¥} {X} {Y} x â¡ inl x') â p â¡ ap inl (inl-lc p)
inl-lc-is-section refl = refl

inr-lc-is-section : {X : ð¤ Ì } {Y : ð¥ Ì } {y y' : Y} â (p : inr {ð¤} {ð¥} {X} {Y} y â¡ inr y') â p â¡ ap inr (inr-lc p)
inr-lc-is-section refl = refl

+-is-set : (X : ð¤ Ì ) (Y : ð¥ Ì ) â is-set X â is-set Y â is-set (X + Y)
+-is-set X Y i j {inl x} {inl x'} p q = inl-lc-is-section p â r â (inl-lc-is-section q)â»Â¹
 where
  r : ap inl (inl-lc p) â¡ ap inl (inl-lc q)
  r = ap (ap inl) (i (inl-lc p) (inl-lc q))
+-is-set X Y i j {inl x} {inr y} p q = ð-elim (+disjoint  p)
+-is-set X Y i j {inr y} {inl x} p q = ð-elim (+disjoint' p)
+-is-set X Y i j {inr y} {inr y'} p q = inr-lc-is-section p â r â (inr-lc-is-section q)â»Â¹
 where
  r : ap inr (inr-lc p) â¡ ap inr (inr-lc q)
  r = ap (ap inr) (j (inr-lc p) (inr-lc q))

Ã-is-set : {X : ð¤ Ì } {Y : ð¥ Ì } â is-set X â is-set Y â is-set (X Ã Y)
Ã-is-set i j {(x , y)} {(x' , y')} p q =
 p            â¡â¨ tofrom-Ã-â¡ p â©
 to-Ã-â¡ pâ pâ â¡â¨ apâ (Î» -â -â â to-Ã-â¡ -â -â) (i pâ qâ) (j pâ qâ) â©
 to-Ã-â¡ qâ qâ â¡â¨ (tofrom-Ã-â¡ q)â»Â¹ â©
 q            â where
  pâ : x â¡ x'
  pâ = prâ (from-Ã-â¡' p)
  pâ : y â¡ y'
  pâ = prâ (from-Ã-â¡' p)
  qâ : x â¡ x'
  qâ = prâ (from-Ã-â¡' q)
  qâ : y â¡ y'
  qâ = prâ (from-Ã-â¡' q)

\end{code}

Formulation of the K axiom for a universe U.

\begin{code}

K-axiom : â ð¤ â ð¤ âº Ì
K-axiom ð¤ = (X : ð¤ Ì ) â is-set X

\end{code}

Formulation of propositional extensionality:

\begin{code}

propext : â ð¤ â ð¤ âº Ì
propext ð¤ = {P Q : ð¤ Ì } â is-prop P â is-prop Q â (P â Q) â (Q â P) â P â¡ Q

PropExt : ð¤Ï
PropExt = â ð¤ â propext ð¤

Prop-Ext : ð¤Ï
Prop-Ext = â {ð¤} â propext ð¤

\end{code}

The following says that, in particular, for any proposition P, we have
that P + Â¬ P is a proposition, or that the decidability of a
proposition is a proposition:

\begin{code}

sum-of-contradictory-props : {P : ð¤ Ì } {Q : ð¥ Ì }
                           â is-prop P â is-prop Q â (P â Q â ð {ð¦}) â is-prop (P + Q)
sum-of-contradictory-props {ð¤} {ð¥} {ð¦} {P} {Q} i j f = Î³
 where
  Î³ : (x y : P + Q) â x â¡ y
  Î³ (inl p) (inl p') = ap inl (i p p')
  Î³ (inl p) (inr q)  = ð-elim {ð¤ â ð¥} {ð¦} (f p q)
  Î³ (inr q) (inl p)  = ð-elim (f p q)
  Î³ (inr q) (inr q') = ap inr (j q q')

\end{code}

Without assuming excluded middle, we have that there are no truth
values other than ð and ð:

\begin{code}

no-props-other-than-ð-or-ð : propext ð¤ â Â¬ (Î£ P ê ð¤ Ì , is-prop P Ã (P â¢ ð) Ã (P â¢ ð))
no-props-other-than-ð-or-ð pe (P , i , f , g) = ð-elim (Ï u)
 where
   u : Â¬ P
   u p = g l
     where
       l : P â¡ ð
       l = pe i ð-is-prop unique-to-ð (Î» _ â p)
   Ï : Â¬Â¬ P
   Ï u = f l
     where
       l : P â¡ ð
       l = pe i ð-is-prop (Î» p â ð-elim (u p)) ð-elim

\end{code}

Notice how we used ð-elim above to coerce a hypothetical value in ð
{ð¤â}, arising from negation, to a value in ð {ð¤}. Otherwise "u" would
have sufficed in place of "Î» p â ð-elim (u p)". The same technique is
used in the following construction.

\begin{code}

ð-is-not-ð : ð {ð¤} â¢ ð {ð¤}
ð-is-not-ð p = ð-elim (Idtofun (p â»Â¹) â)

\end{code}

Unique existence.

\begin{code}

â! : {X : ð¤ Ì } (A : X â ð¥ Ì ) â ð¤ â ð¥ Ì
â! A = is-singleton (Î£ A)

existsUnique : (X : ð¤ Ì ) (A : X â ð¥ Ì ) â ð¤ â ð¥ Ì
existsUnique X A = â! A

syntax existsUnique X (Î» x â b) = â! x ê X , b

witness-uniqueness : {X : ð¤ Ì } (A : X â ð¥ Ì )
                   â (â! x ê X , A x)
                   â (x y : X) â A x â A y â x â¡ y
witness-uniqueness A e x y a b = ap prâ (singletons-are-props e (x , a) (y , b))

infixr -1 existsUnique

â!-intro : {X : ð¤ Ì } {A : X â ð¥ Ì } (x : X) (a : A x) â ((Ï : Î£ A) â (x , a) â¡ Ï) â â! A
â!-intro x a o = (x , a) , o

â!-witness : {X : ð¤ Ì } {A : X â ð¥ Ì } â â! A â X
â!-witness ((x , a) , o) = x

â!-is-witness : {X : ð¤ Ì } {A : X â ð¥ Ì } (u : â! A) â A (â!-witness u)
â!-is-witness ((x , a) , o) = a

description : {X : ð¤ Ì } {A : X â ð¥ Ì } â â! A â Î£ A
description (Ï , o) = Ï

â!-uniqueness' : {X : ð¤ Ì } {A : X â ð¥ Ì } (u : â! A) â (Ï : Î£ A) â description u â¡ Ï
â!-uniqueness' ((x , a) , o) = o

â!-uniqueness : {X : ð¤ Ì } {A : X â ð¥ Ì } (u : â! A) â (x : X) (a : A x) â description u â¡ (x , a)
â!-uniqueness u x a = â!-uniqueness' u (x , a)

â!-uniqueness'' : {X : ð¤ Ì } {A : X â ð¥ Ì } (u : â! A) â (Ï Ï : Î£ A) â Ï â¡ Ï
â!-uniqueness'' u Ï Ï = â!-uniqueness' u Ï â»Â¹ â â!-uniqueness' u Ï

\end{code}

Added 5 March 2020 by Tom de Jong.

\begin{code}

+-is-prop : {X : ð¤ Ì } {Y : ð¥ Ì }
          â is-prop X â is-prop Y
          â (X â Â¬ Y)
          â is-prop (X + Y)
+-is-prop i j f (inl x) (inl x') = ap inl (i x x')
+-is-prop i j f (inl x) (inr y) = ð-induction (f x y)
+-is-prop i j f (inr y) (inl x) = ð-induction (f x y)
+-is-prop i j f (inr y) (inr y') = ap inr (j y y')

+-is-prop' : {X : ð¤ Ì } {Y : ð¥ Ì }
           â is-prop X â is-prop Y
           â (Y â Â¬ X)
           â is-prop (X + Y)
+-is-prop' {ð¤} {ð¥} {X} {Y} i j f = +-is-prop i j (Î» y x â f x y)

\end{code}

Added 16th June 2020 by Martin Escardo. (Should have added this ages ago to avoid boiler-plate code.)

\begin{code}

Ãâ-is-prop : {ð¥â ð¥â ð¥â : Universe}
             {Xâ : ð¥â Ì } {Xâ : ð¥â Ì } {Xâ : ð¥â Ì }
           â is-prop Xâ â is-prop Xâ â is-prop Xâ â is-prop (Xâ Ã Xâ Ã Xâ)
Ãâ-is-prop iâ iâ iâ = Ã-is-prop iâ (Ã-is-prop iâ iâ)

Ãâ-is-prop : {ð¥â ð¥â ð¥â ð¥â : Universe}
             {Xâ : ð¥â Ì } {Xâ : ð¥â Ì } {Xâ : ð¥â Ì } {Xâ : ð¥â Ì }
           â is-prop Xâ â is-prop Xâ â is-prop Xâ â is-prop Xâ â is-prop (Xâ Ã Xâ Ã Xâ Ã Xâ)
Ãâ-is-prop iâ iâ iâ iâ = Ã-is-prop iâ (Ãâ-is-prop iâ iâ iâ)

Ãâ-is-prop : {ð¥â ð¥â ð¥â ð¥â ð¥â : Universe}
             {Xâ : ð¥â Ì } {Xâ : ð¥â Ì } {Xâ : ð¥â Ì } {Xâ : ð¥â Ì } {Xâ : ð¥â Ì }
           â is-prop Xâ â is-prop Xâ â is-prop Xâ â is-prop Xâ â is-prop Xâ â is-prop (Xâ Ã Xâ Ã Xâ Ã Xâ Ã Xâ)
Ãâ-is-prop iâ iâ iâ iâ iâ = Ã-is-prop iâ (Ãâ-is-prop iâ iâ iâ iâ)

Ãâ-is-prop : {ð¥â ð¥â ð¥â ð¥â ð¥â ð¥â : Universe}
             {Xâ : ð¥â Ì } {Xâ : ð¥â Ì } {Xâ : ð¥â Ì } {Xâ : ð¥â Ì } {Xâ : ð¥â Ì } {Xâ : ð¥â Ì }
           â is-prop Xâ â is-prop Xâ â is-prop Xâ â is-prop Xâ â is-prop Xâ â is-prop Xâ â is-prop (Xâ Ã Xâ Ã Xâ Ã Xâ Ã Xâ Ã Xâ)
Ãâ-is-prop iâ iâ iâ iâ iâ iâ = Ã-is-prop iâ (Ãâ-is-prop iâ iâ iâ iâ iâ)

Ãâ-is-prop : {ð¥â ð¥â ð¥â ð¥â ð¥â ð¥â ð¥â : Universe}
             {Xâ : ð¥â Ì } {Xâ : ð¥â Ì } {Xâ : ð¥â Ì } {Xâ : ð¥â Ì } {Xâ : ð¥â Ì } {Xâ : ð¥â Ì } {Xâ : ð¥â Ì }
           â is-prop Xâ â is-prop Xâ â is-prop Xâ â is-prop Xâ â is-prop Xâ â is-prop Xâ â is-prop Xâ â is-prop (Xâ Ã Xâ Ã Xâ Ã Xâ Ã Xâ Ã Xâ Ã Xâ)
Ãâ-is-prop iâ iâ iâ iâ iâ iâ iâ = Ã-is-prop iâ (Ãâ-is-prop iâ iâ iâ iâ iâ iâ)

Ãâ-is-prop : {ð¥â ð¥â ð¥â ð¥â ð¥â ð¥â ð¥â ð¥â : Universe}
             {Xâ : ð¥â Ì } {Xâ : ð¥â Ì } {Xâ : ð¥â Ì } {Xâ : ð¥â Ì } {Xâ : ð¥â Ì } {Xâ : ð¥â Ì } {Xâ : ð¥â Ì } {Xâ : ð¥â Ì }
           â is-prop Xâ â is-prop Xâ â is-prop Xâ â is-prop Xâ â is-prop Xâ â is-prop Xâ â is-prop Xâ â is-prop Xâ â is-prop (Xâ Ã Xâ Ã Xâ Ã Xâ Ã Xâ Ã Xâ Ã Xâ Ã Xâ)
Ãâ-is-prop iâ iâ iâ iâ iâ iâ iâ iâ = Ã-is-prop iâ (Ãâ-is-prop iâ iâ iâ iâ iâ iâ iâ)
\end{code}

The type of truth values.

\begin{code}

Î© : â ð¤ â ð¤ âº Ì
Î© ð¤ = Î£ P ê ð¤ Ì , is-prop P

Î©â = Î© ð¤â

_holds : Î© ð¤ â ð¤ Ì
(P , i) holds = P


holds-is-prop : (p : Î© ð¤) â is-prop (p holds)
holds-is-prop (P , i) = i

â¥Î© â¤Î© : Î© ð¤
â¥Î© = ð , ð-is-prop   -- false
â¤Î© = ð , ð-is-prop   -- true

\end{code}
