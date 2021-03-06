Martin Escardo 2011, 2017, 2018, 2020.

We define and study totally separated types (which could also have
been called ð-separated types). Most of the material in this file is
from January 2018.

The terminology "totally separated" comes from topology, where it
means that the clopens separate the points. Here the maps into ð
separate the points, formulated in a positive way.

Any type has a totally separated reflection, assuming function
extensionality and propositional truncations.

All the simple types (those obtained from ð and â by iterating
function spaces) are totally separated (see the module
SimpleTypes). This is because the totally separated types form an
exponential ideal. Moreover, Î  Y is totally separated for any family
Y:XâU provided Y x is totally separated for all x:X. This assumes
function extensionality.

In particular, the Cantor and Baire types ð^â and â^â are totally
separated (like in topology).

Closure under Î£ fails in general. However, we have closure under _Ã_,
and ââ (defined with Î£) is totally separated (proved in the module
GenericConvergentSequence).

A counter-example to closure under Î£ (from 2012) is in the file
http://www.cs.bham.ac.uk/~mhe/TypeTopology/FailureOfTotalSeparatedness.html

This is the "compactification" of â with two points at infinity:

   Î£ u ê ââ , u â¡ â â ð.

If there is a ð-valued function separating the two points at infinity,
then WLPO holds. (The totally separated reflection of this type should
be ââ if Â¬WLPO holds.)

(In the context of topology, I learned this example from the late
Klaus Keimel (but the rendering in type theory is mine), where it is a
Tâ, non-Tâ, and non totally separated space which is zero dimensional
(has a base of clopen sets), and where the intersection of two compact
subsets need not be compact. The failure of the Hausdorff property is
with the two points an infinity, which can't be separated by disjoint
open neighbourhoods.)

The total separatedness of the reals (of any kind) should also give a
taboo. All non-sets fail (without the need of taboos) to be totally
separated, because totally separated spaces are sets.

Total separatedness is also characterized as the tightness of a
certain apartness relation that can be defined in any type.

We also show how to construct the tight reflection of any type
equipped with an apartness relation, given by a universal strongly
extensional map into a tight apartness type. Any type with a tight
apartness relation is a set, and so this reflection is always a set.


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module TotallySeparated where

open import SpartanMLTT

open import Two-Properties
open import DecidableAndDetachable
open import DiscreteAndSeparated hiding (tight)
open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Retracts
open import UF-Equiv
open import UF-LeftCancellable
open import UF-Embeddings
open import UF-FunExt
open import UF-Lower-FunExt
open import UF-PropTrunc
open import UF-ImageAndSurjection
open import UF-Miscelanea

\end{code}

An equality defined by a Leibniz principle with ð-valued functions:

\begin{code}

_â¡â_ : {X : ð¤ Ì } â X â X â ð¤ Ì
x â¡â y = (p : type-of x â ð) â p x â¡ p y

â¡â-is-prop-valued : funext ð¤ ð¤â
                  â (X : ð¤ Ì ) (x y : X) â is-prop (x â¡â y)
â¡â-is-prop-valued fe X x y = Î -is-prop fe (Î» p â ð-is-set)

\end{code}

In topological models, maps into ð classify clopens, and so total
separatedness amounts to "the clopens separate the points" in the
sense that any two points with the same clopen neighbourhoods are
equal. This notion in topology is called total separatedness. Notice
that we are not referring to homotopical models in this discussion.

\begin{code}

is-totally-separated : ð¤ Ì â ð¤ Ì
is-totally-separated X = {x y : X} â x â¡â y â x â¡ y

\end{code}

Synonym, emphasizing that we can use other types as separators:

\begin{code}

ð-separated : ð¤ Ì â ð¤ Ì
ð-separated = is-totally-separated

\end{code}

We now define an alternative characterization of total separatedness
(added December 11th 2020), still using the equivalence relation â¡â,
and also motivated by topological considerations, namely that the
quasi component of a point of a topological space is the intersection
of all clopen sets containing x and a space is totally separated of
the quasi-components are singletons:

\begin{code}

quasi-component : {X : ð¤ Ì } â X â ð¤ Ì
quasi-component {ð¤} {X} x = Î£ y ê X , x â¡â y

quasi-component-canonical-point : {X : ð¤ Ì } (x : X) â quasi-component x
quasi-component-canonical-point {ð¤} {X} x = (x , Î» p â refl)

\end{code}

The alternative characterization of total separatedness is that the
quasi-component of any point is a subsingleton, and hence a singleton:

\begin{code}

is-totally-separatedâ : ð¤ Ì â ð¤ Ì
is-totally-separatedâ X = (x : X) â is-prop (quasi-component x)

totally-separated-gives-totally-separatedâ : funext ð¤ ð¤â
                                           â {X : ð¤ Ì }
                                           â is-totally-separated X
                                           â is-totally-separatedâ X
totally-separated-gives-totally-separatedâ fe {X} ts x (y , a) (z , b) = Î³
 where
  c : y â¡â z
  c p = (a p)â»Â¹ â b p

  q : y â¡ z
  q = ts c

  Î³ : (y , a) â¡ (z , b)
  Î³ = to-subtype-â¡ (â¡â-is-prop-valued fe X x) q

totally-separatedâ-types-are-totally-separated : {X : ð¤ Ì }
                                               â is-totally-separatedâ X
                                               â is-totally-separated X
totally-separatedâ-types-are-totally-separated {ð¤} {X} Ï {x} {y} Ï = Î³
 where
  a b : quasi-component x
  a = x , Î» p â refl
  b = y , Ï

  e : a â¡ b
  e = Ï x a b

  Î³ : x â¡ y
  Î³ = ap prâ e

\end{code}

A third formulation of the notion of total separatedness, as the
tightness of a certain apartness relation, is given below.

Excluded middle implies that all sets are discrete and hence totally
separated:

\begin{code}

discrete-types-are-totally-separated : {X : ð¤ Ì }
                                     â is-discrete X
                                     â is-totally-separated X
discrete-types-are-totally-separated {ð¤} {X} d {x} {y} Î± = g
 where
  p : X â ð
  p = prâ (characteristic-function (d x))

  Ï : (y : X) â (p y â¡ â â x â¡ y) Ã (p y â¡ â â Â¬ (x â¡ y))
  Ï = prâ (characteristic-function (d x))

  b : p x â¡ â
  b = different-from-â-equal-â (Î» s â prâ (Ï x) s refl)

  a : p y â¡ â
  a = (Î± p)â»Â¹ â b

  g : x â¡ y
  g = prâ (Ï y) a

\end{code}

The converse fails: by the results below, e.g. (â â ð) is totally
separated, but its discreteness amounts to WLPO.

Totally separated spaces are closed under retracts:

\begin{code}

retract-of-totally-separated : {X : ð¤ Ì } {Y : ð¥ Ì }
                             â retract Y of X
                             â is-totally-separated X
                             â is-totally-separated Y
retract-of-totally-separated (r , s , rs) Ï {y} {y'} Î± = section-lc s (r , rs) h
 where
  h : s y â¡ s y'
  h = Ï (Î» p â Î± (p â s))

\end{code}

Recall that a type is called Â¬Â¬-separated if the doubly negated equality
of any two element implies their equality, and that such a type is a
set.

\begin{code}

totally-separated-types-are-separated : (X : ð¤ Ì )
                                      â is-totally-separated X
                                      â is-Â¬Â¬-separated X
totally-separated-types-are-separated X Ï = g
 where
  g : (x y : X) â Â¬Â¬ (x â¡ y) â x â¡ y
  g x y Ï  = Ï h
   where
    a : (p : X â ð) â Â¬Â¬ (p x â¡ p y)
    a p = Â¬Â¬-functor (ap p {x} {y}) Ï

    h : (p : X â ð) â p x â¡ p y
    h p = ð-is-Â¬Â¬-separated (p x) (p y) (a p)

totally-separated-types-are-sets : funext ð¤ ð¤â
                                 â (X : ð¤ Ì )
                                 â is-totally-separated X
                                 â is-set X
totally-separated-types-are-sets fe X t =
  Â¬Â¬-separated-types-are-sets fe (totally-separated-types-are-separated X t)

\end{code}

The converse fails: the type of propositions is a set, but its total
separatedness implies excluded middle. In fact, its Â¬Â¬-separatedness
already implies excluded middle:

\begin{code}

open import UF-ExcludedMiddle

Î©-separated-gives-DNE : propext ð¤
                      â funext ð¤ ð¤
                      â is-Â¬Â¬-separated (Î© ð¤)
                      â DNE ð¤
Î©-separated-gives-DNE {ð¤} pe fe Î©-is-Â¬Â¬-separated P P-is-prop not-not-P = d
 where
  p : Î© ð¤
  p = (P , P-is-prop)

  b : Â¬Â¬ (p â¡ â¤Î©)
  b = Â¬Â¬-functor (holds-gives-equal-â¤ pe fe p) not-not-P

  c : p â¡ â¤Î©
  c = Î©-is-Â¬Â¬-separated p â¤Î© b

  d : P
  d = equal-â¤-gives-holds p c

Î©-separated-gives-EM : propext ð¤
                     â funext ð¤ ð¤
                     â is-Â¬Â¬-separated (Î© ð¤)
                     â EM ð¤
Î©-separated-gives-EM {ð¤} pe fe Î©-is-Â¬Â¬-separated =
  DNE-gives-EM (lower-funext ð¤ ð¤ fe) (Î©-separated-gives-DNE pe fe Î©-is-Â¬Â¬-separated)

Î©-totally-separated-gives-EM : propext ð¤
                             â funext ð¤ ð¤
                             â is-totally-separated (Î© ð¤)
                             â EM ð¤
Î©-totally-separated-gives-EM {ð¤} pe fe Î©-is-totally-separated =
  Î©-separated-gives-EM pe fe
    (totally-separated-types-are-separated (Î© ð¤) Î©-is-totally-separated)

\end{code}

The need to define f and g in the following proof arises because the
function Î -is-prop requires a dependent function with explicit
arguments, but total separatedness is defined with implicit
arguments. The essence of the proof is that of p in the where clause.

\begin{code}

being-totally-separated-is-prop : funext ð¤ ð¤
                                â (X : ð¤ Ì )
                                â is-prop (is-totally-separated X)
being-totally-separated-is-prop {ð¤} fe X = Î³
 where
  T : ð¤ Ì
  T = (x y : X) â x â¡â y â x â¡ y

  f : T â is-totally-separated X
  f t {x} {y} Ï = t x y Ï

  g : is-totally-separated X â T
  g t x y Ï = t {x} {y} Ï

  p : T â is-prop T
  p t = Î -is-prop fe
           (Î» x â Î -is-prop fe
                    (Î» y â Î -is-prop fe
                              (Î» p â totally-separated-types-are-sets
                                      (lower-funext ð¤ ð¤ fe) X (f t))))

  Î³ : is-prop (is-totally-separated X)
  Î³ = subtype-of-prop-is-prop g (Î» {t} {u} (r : g t â¡ g u) â ap f r) (prop-criterion p)
\end{code}

Old proof, which by-passes the step via Â¬Â¬-separatedness and has a
different extensionlity hypothesis:

\begin{code}

totally-separated-types-are-sets' : funext ð¤ ð¤â
                                  â (X : ð¤ Ì )
                                  â is-totally-separated X
                                  â is-set X
totally-separated-types-are-sets' fe X t = Id-collapsibles-are-sets h
 where
  f : {x y : X} â x â¡ y â x â¡ y
  f r = t(Î» p â ap p r)

  b : {x y : X} (Ï Î³ : (p : X â ð) â p x â¡ p y) â Ï â¡ Î³
  b Ï Î³ = dfunext fe (Î» p â discrete-types-are-sets ð-is-discrete (Ï p) (Î³ p))

  c : {x y : X} (r s : x â¡ y) â (Î» p â ap p r) â¡ (Î» p â ap p s)
  c r s = b(Î» p â ap p r) (Î» p â ap p s)

  g : {x y : X} â wconstant(f {x} {y})
  g r s = ap t (c r s)

  h : Id-collapsible X
  h {x} {y} = f , g

\end{code}

As discussed above, we don't have general closure under Î£, but we have
the following particular cases:

\begin{code}

Ã-totally-separated : (X : ð¤ Ì ) (Y : ð¥ Ì )
                    â is-totally-separated X
                    â is-totally-separated Y
                    â is-totally-separated (X Ã Y)
Ã-totally-separated X Y t u {a , b} {x , y} Ï =
   to-Ã-â¡ (t (Î» (p : X â ð) â Ï (Î» (z : X Ã Y) â p (prâ z))))
          (u (Î» (q : Y â ð) â Ï (Î» (z : X Ã Y) â q (prâ z))))

Î£-is-totally-separated : (X : ð¤ Ì ) (Y : X â ð¥ Ì )
                       â is-discrete X
                       â ((x : X) â is-totally-separated (Y x))
                       â is-totally-separated (Î£ Y)
Î£-is-totally-separated X Y d t {a , b} {x , y} Ï = to-Î£-â¡ (r , s)
 where
  r : a â¡ x
  r = discrete-types-are-totally-separated d (Î» p â Ï (Î» z â p (prâ z)))
  sâ : transport Y r b â¡â y
  sâ q = g
   where
    f : {u : X} â (u â¡ x) + Â¬ (u â¡ x) â Y u â ð
    f (inl m) v = q (transport Y m v)
    f (inr _) v = â --<-- What we choose here is irrelevant.

    p : Î£ Y â ð
    p (u , v) = f (d u x) v

    i : p (a , b) â¡ q (transport Y r b)
    i = ap (Î» - â f - b) (discrete-inl d a x r)

    j : p (a , b) â¡ p (x , y)
    j = Ï p

    k : p (x , y) â¡ q (transport Y refl y)
    k = ap (Î» - â f - y) (discrete-inl d x x refl)

    g : q (transport Y r b) â¡ q y
    g = i â»Â¹ â j â k

  s : transport Y r b â¡ y
  s = t x sâ

\end{code}

Maybe this can be further generalized by replacing the discreteness of X
with the assumption that

  (x : X) (q : Y x â ð) â Î£ p ê Î£ Y â ð , (y : Y x) â q y â¡ p (x , y).

Then the previous few functions would be a particular case of this.

The following can also be considered as a special case of Î£ (indexed
by the type ð):

\begin{code}

+-totally-separated : (X : ð¤ Ì ) (Y : ð¥ Ì )
                    â is-totally-separated X
                    â is-totally-separated Y
                    â is-totally-separated (X + Y)
+-totally-separated X Y t u {inl x} {inl x'} Ï =
    ap inl (t (Î» p â Ï (cases p (Î» (_ : Y) â â))))
+-totally-separated X Y t u {inl x} {inr y} Ï =
    ð-elim (zero-is-not-one (Ï (cases (Î» _ â â) (Î» _ â â))))
+-totally-separated X Y t u {inr y} {inl x} Ï =
    ð-elim (zero-is-not-one (Ï (cases (Î» _ â â) (Î» _ â â))))
+-totally-separated X Y t u {inr y} {inr y'} Ï =
    ap inr (u (Î» p â Ï (cases (Î» (_ : X) â â) p)))

\end{code}

The Cantor type â â ð is totally separated:

\begin{code}

ð-is-totally-separated : is-totally-separated ð
ð-is-totally-separated e = e id

Î -is-totally-separated : funext ð¤ ð¥
                       â {X : ð¤ Ì } {Y : X â ð¥ Ì }
                       â ((x : X) â is-totally-separated(Y x))
                       â is-totally-separated(Î  Y)
Î -is-totally-separated fe {X} {Y} t {f} {g} e = dfunext fe h
 where
   P : (x : X) (p : Y x â ð) â Î  Y â ð
   P x p f = p (f x)

   h : (x : X) â f x â¡ g x
   h x = t x (Î» p â e(P x p))

Cantor-is-totally-separated : funext ð¤â ð¤â â is-totally-separated (â â ð)
Cantor-is-totally-separated fe = Î -is-totally-separated fe (Î» n â ð-is-totally-separated)

â-is-totally-separated : is-totally-separated â
â-is-totally-separated = discrete-types-are-totally-separated â-is-discrete

Baire-is-totally-separated : funext ð¤â ð¤â â is-totally-separated (â â â)
Baire-is-totally-separated fe = Î -is-totally-separated fe (Î» n â â-is-totally-separated)

\end{code}

More generally, all simple types are totally separated - see the
module SimpleTypes.

Closure under /-extensions defined in the module
InjectiveTypes. Notice that j doesn't need to be an embedding (in
which case the extension is merely a Kan extension rather than a
proper extension).

\begin{code}

module _ (fe : FunExt)  where

 open import InjectiveTypes fe

 /-is-totally-separated : (fe : FunExt)
                          {X : ð¤ Ì } {A : ð¥ Ì }
                          (j : X â A)
                          (Y : X â ð¦ Ì )
                        â ((x : X) â is-totally-separated (Y x))
                        â (a : A) â is-totally-separated ((Y / j) a)
 /-is-totally-separated {ð¤} {ð¥} {ð¦} fe j Y t a = Î -is-totally-separated (fe (ð¤ â ð¥) ð¦)
                                                    (Î» (Ï : fiber j a) â t (prâ Ï))

\end{code}

We now characterize the totally separated types X as those such that
the map eval X defined below is an embedding, in order to construct
totally separated reflections.

\begin{code}

eval : (X : ð¤ Ì ) â X â ((X â ð) â ð)
eval X = Î» x p â p x

is-totally-separatedâ : ð¤ Ì â ð¤ Ì
is-totally-separatedâ X = is-embedding (eval X)

totally-separated-gives-totally-separatedâ : funext ð¤ ð¤â
                                           â {X : ð¤ Ì }
                                           â is-totally-separated X
                                           â is-totally-separatedâ X
totally-separated-gives-totally-separatedâ fe {X} Ï Ï (x , p) (y , q) = to-Î£-â¡ (t , r)
  where
   s : eval X x â¡ eval X y
   s = p â q â»Â¹

   t : x â¡ y
   t = Ï (happly s)

   r : transport (Î» - â eval X - â¡ Ï) t p â¡ q
   r = totally-separated-types-are-sets fe
         ((X â ð) â ð) (Î -is-totally-separated fe (Î» p â ð-is-totally-separated)) _ q

totally-separatedâ-gives-totally-separated : funext ð¤ ð¤â
                                           â {X : ð¤ Ì }
                                           â is-totally-separatedâ X
                                           â is-totally-separated X
totally-separatedâ-gives-totally-separated fe {X} i {x} {y} e = ap prâ q
  where
   Ï : (X â ð) â ð
   Ï = eval X x

   h : is-prop (fiber (eval X) Ï)
   h = i Ï

   g : eval X y â¡ Ï
   g = dfunext fe (Î» p â (e p)â»Â¹)

   q : x , refl â¡ y , g
   q = h (x , refl) (y , g)

\end{code}

 Now, if a type X is not (necessarily) totally separated, we can
 consider the image of the map eval X, and this gives the totally
 separated reflection, with the corestriction of eval X to its image
 as its reflector.

\begin{code}

module TotallySeparatedReflection
         (fe : FunExt)
         (pt : propositional-truncations-exist)
 where

 open PropositionalTruncation pt
 open ImageAndSurjection pt

\end{code}

We construct the reflection as the image of the evaluation map.

\begin{code}

 ð : ð¤ Ì â ð¤ Ì
 ð X = image (eval X)

 Ï : {X : ð¤ Ì } â is-totally-separated (ð X)
 Ï {ð¤} {X} {Ï , s} {Î³ , t} = g
  where
   f : (e : (q : ð X â ð) â q (Ï , s) â¡ q (Î³ , t)) (p : X â ð) â Ï p â¡ Î³ p
   f e p = e (Î» (x' : ð X) â prâ x' p)

   g : (e : (q : ð X â ð) â q (Ï , s) â¡ q (Î³ , t)) â (Ï , s) â¡ (Î³ , t)
   g e = to-subtype-â¡ (Î» _ â â¥â¥-is-prop) (dfunext (fe ð¤ ð¤â) (f e))

\end{code}

Then the reflector is the corestriction of the evaluation map. The
induction principle for surjections gives an induction principle for
the reflector.

\begin{code}

 Î· : {X : ð¤ Ì } â X â ð X
 Î· {ð¤} {X} = corestriction (eval X)

 Î·-is-surjection : {X : ð¤ Ì } â is-surjection Î·
 Î·-is-surjection {ð¤} {X} = corestriction-is-surjection (eval X)

 Î·-induction :  {X : ð¤ Ì } (P : ð X â ð¦ Ì )
             â ((x' : ð X) â is-prop (P x'))
             â ((x : X) â P(Î· x))
             â (x' : ð X) â P x'
 Î·-induction {ð¤} {ð¦} {X} = surjection-induction Î· Î·-is-surjection

\end{code}

Perhaps we could have used more induction in the following proof
rather than direct proofs (as in the proof of tight reflection below).

\begin{code}

 totally-separated-reflection : {X : ð¤ Ì } {A : ð¥ Ì }
                              â is-totally-separated A
                              â (f : X â A) â â! f' ê (ð X â A) , f' â Î· â¡ f
 totally-separated-reflection {ð¤} {ð¥} {X} {A} Ï f = Î´
  where
   A-is-set : is-set A
   A-is-set = totally-separated-types-are-sets (fe ð¥ ð¤â) A Ï

   ie : (Î³ : (A â ð) â ð) â is-prop (Î£ a ê A , eval A a â¡ Î³)
   ie = totally-separated-gives-totally-separatedâ (fe ð¥ ð¤â) Ï

   h : (Ï : (X â ð) â ð) â (â x ê X , eval X x â¡ Ï)
     â Î£ a ê A , eval A a â¡ (Î» q â Ï(q â f))
   h Ï = â¥â¥-rec (ie Î³) u
    where
     Î³ : (A â ð) â ð
     Î³ q = Ï (q â f)

     u : (Î£ x ê X , (Î» p â p x) â¡ Ï) â Î£ a ê A , eval A a â¡ Î³
     u (x , r) = f x , dfunext (fe ð¥ ð¤â) (Î» q â happly r (q â f))

   h' : (x' : ð X) â Î£ a ê A , eval A a â¡ (Î» q â prâ x' (q â f))
   h' (Ï , s) = h Ï s

   f' : ð X â A
   f' (Ï , s) = prâ (h Ï s)

   b : (x' : ð X) (q : A â ð) â q(f' x') â¡ prâ x' (q â f)
   b (Ï , s) = happly (prâ (h Ï s))

   r : f' â Î· â¡ f
   r = dfunext (fe ð¤ ð¥) (Î» x â Ï (b (Î· x)))

   c : (Ï : Î£ f'' ê (ð X â A) , f'' â Î· â¡ f) â (f' , r) â¡ Ï
   c (f'' , s) = to-Î£-â¡ (t , v)
    where
     w : â x â f'(Î· x) â¡ f''(Î· x)
     w = happly (r â s â»Â¹)

     t : f' â¡ f''
     t = dfunext (fe ð¤ ð¥) (Î·-induction _ (Î» _ â A-is-set) w)

     u : f'' â Î· â¡ f
     u = transport (Î» - â - â Î· â¡ f) t r

     v : u â¡ s
     v = Î -is-set (fe ð¤ ð¥) (Î» _ â A-is-set) u s

   Î´ : â! f' ê (ð X â A) , f' â Î· â¡ f
   Î´ = (f' , r) , c

\end{code}

We package the above as follows for convenient use elsewhere
(including the module CompactTypes).

\begin{code}

 totally-separated-reflection' : {X : ð¤ Ì } {A : ð¥ Ì }
                               â is-totally-separated A
                               â is-equiv (Î» (f' : ð X â A) â f' â Î·)
 totally-separated-reflection' Ï = vv-equivs-are-equivs _ (totally-separated-reflection Ï)

 totally-separated-reflection'' : {X : ð¤ Ì } {A : ð¥ Ì } â is-totally-separated A
                                â (ð X â A) â (X â A)
 totally-separated-reflection'' Ï = (Î» f' â f' â Î·) , totally-separated-reflection' Ï

\end{code}

In particular, because ð is totally separated, ð X and X have the same
boolean predicates (which we exploit in the module CompactTypes).

The notion of total separatedness (or ð-separatedness) is analogous to
the Tâ-separation axiom (which says that any two points with the same
open neighbourhoods are equal).

\begin{code}

ð-sober : ð¦ Ì â ð¤ âº â ð¦ Ì
ð-sober {ð¦} {ð¤} A = ð-separated A Ã ((X : ð¤ Ì ) (e : A â X) â is-equiv(dual ð e) â is-equiv e)

\end{code}

TODO: example of ð-separated type that fails to be ð-sober, ð-sober
reflection (or ð-sobrification).

TODO: most of what we said doesn't depend on the type ð, and total
separatedness can be generalized to S-separatedness for an arbitrary
type S, where ð-separatedness is total separatedness. Then, for
example, Prop-separated is equivalent to is-set, all types in U are U
separated, Set-separatedness (where Set is the type of sets) should be
equivalent to is-1-groupoid, etc.

An interesting case is when S is (the total space of) a dominance,
generalizing the case S=Prop. Because the partial elements are defined
in terms of maps into S, the S-lifting of a type X should coincide
with the S-separated reflection of the lifting of X, and hence, in
this context, it makes sense to restrict our attention to S-separated
types.

Another useful thing is that in any type X we can define an apartness
relation xâ¯y by â(p:Xâð), p (x)ââ p (y), which is tight iff X is totally
separated, where tightness means Â¬ (xâ¯y)âx=y. Part of the following
should be moved to another module about apartness, but I keep it here
for the moment.

26 January 2018.

\begin{code}

module Apartness (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 is-prop-valued is-irreflexive is-symmetric is-cotransitive is-tight is-apartness
     : {X : ð¤ Ì } â (X â X â ð¥ Ì ) â ð¤ â ð¥ Ì

 is-prop-valued  _â¯_ = â x y â is-prop (x â¯ y)
 is-irreflexive  _â¯_ = â x â Â¬ (x â¯ x)
 is-symmetric    _â¯_ = â x y â x â¯ y â y â¯ x
 is-cotransitive _â¯_ = â x y z â x â¯ y â x â¯ z â¨ y â¯ z
 is-tight        _â¯_ = â x y â Â¬ (x â¯ y) â x â¡ y
 is-apartness    _â¯_ = is-prop-valued _â¯_ Ã is-irreflexive _â¯_ Ã is-symmetric _â¯_ Ã is-cotransitive _â¯_

\end{code}

We now show that a type is totally separated iff a particular
apartness relation _â¯â is tight:

\begin{code}

 _â¯â_ : {X : ð¤ Ì } â X â X â ð¤ Ì
 x â¯â y = â p ê (type-of x â ð), p x â¢ p y

 â¯â-is-apartness : {X : ð¤ Ì } â is-apartness (_â¯â_ {ð¤} {X})
 â¯â-is-apartness {ð¤} {X} = a , b , c , d
  where
   a : is-prop-valued _â¯â_
   a x y = â¥â¥-is-prop

   b : is-irreflexive _â¯â_
   b x = â¥â¥-rec ð-is-prop g
    where
     g : Â¬ (Î£ p ê (X â ð) , p x â¢ p x)
     g (p , u) = u refl

   c : is-symmetric _â¯â_
   c x y = â¥â¥-functor g
    where
     g : (Î£ p ê (X â ð) , p x â¢ p y) â Î£ p ê (X â ð) , p y â¢ p x
     g (p , u) = p , â¢-sym u

   d : is-cotransitive _â¯â_
   d x y z = â¥â¥-functor g
    where
     g : (Î£ p ê (X â ð) , p x â¢ p y) â (x â¯â z) + (y â¯â z)
     g (p , u) = h (discrete-is-cotransitive ð-is-discrete {p x} {p y} {p z} u)
      where
       h : (p x â¢ p z) + (p z â¢ p y) â (x â¯â z) + (y â¯â z)
       h (inl u) = inl â£ p , u â£
       h (inr v) = inr â£ p , â¢-sym v â£

 is-totally-separatedâ : ð¤ Ì â ð¤ Ì
 is-totally-separatedâ {ð¤} X = is-tight (_â¯â_ {ð¤} {X})

 totally-separatedâ-gives-totally-separated : {X : ð¤ Ì }
                                            â is-totally-separatedâ X
                                            â is-totally-separated X
 totally-separatedâ-gives-totally-separated {ð¤} {X} Ï {x} {y} Î± = Î³
  where
   h : Â¬ (Î£ p ê (X â ð) , p x â¢ p y)
   h (p , u) = u (Î± p)

   Î³ : x â¡ y
   Î³ = Ï x y (â¥â¥-rec ð-is-prop h)

 totally-separated-gives-totally-separatedâ : {X : ð¤ Ì }
                                            â is-totally-separated X
                                            â is-totally-separatedâ X
 totally-separated-gives-totally-separatedâ {ð¤} {X} Ï x y na = Ï Î±
  where
   h : Â¬ (Î£ p ê (X â ð) , p x â¢ p y)
   h (p , u) = na â£ p , u â£

   Î± : (p : X â ð) â p x â¡ p y
   Î± p = ð-is-Â¬Â¬-separated (p x) (p y) (Î» u â h (p , u))

\end{code}

 12 Feb 2018. This was prompted by the discussion
 https://nforum.ncatlab.org/discussion/8282/points-of-the-localic-quotient-with-respect-to-an-apartness-relation/

 But is clearly related to the above characterization of total
 separatedness.

\begin{code}

 is-reflexive is-transitive is-equivalence-rel
     : {X : ð¤ Ì } â (X â X â ð¥ Ì ) â ð¤ â ð¥ Ì

 is-reflexive       _â_ = â x â x â x
 is-transitive      _â_ = â x y z â x â y â y â z â x â z
 is-equivalence-rel _â_ = is-prop-valued _â_
                        Ã is-reflexive _â_
                        Ã is-symmetric _â_
                        Ã is-transitive _â_

\end{code}

 The following is the standard equivalence relation induced by an
 apartness relation. The tightness axiom defined above says that this
 equivalence relation is equality.

\begin{code}

 neg-apart-is-equiv : {X : ð¤ Ì }
                    â funext ð¤ ð¤â
                    â (_â¯_ : X â X â ð¤ Ì )
                    â is-apartness _â¯_
                    â is-equivalence-rel (Î» x y â Â¬ (x â¯ y))
 neg-apart-is-equiv {ð¤} {X} fe _â¯_ (â¯p , â¯i , â¯s , â¯c) = p , â¯i , s , t
  where
   p : (x y : X) â is-prop (Â¬ (x â¯ y))
   p x y = negations-are-props fe

   s : (x y : X) â Â¬ (x â¯ y) â Â¬ (y â¯ x)
   s x y u a = u (â¯s y x a)

   t : (x y z : X) â Â¬ (x â¯ y) â Â¬ (y â¯ z) â Â¬ (x â¯ z)
   t x y z u v a = v (â¯s z y (left-fails-gives-right-holds (â¯p z y) b u))
    where
     b : (x â¯ y) â¨ (z â¯ y)
     b = â¯c x z y a

 \end{code}

 The following positive formulation of Â¬ (x â¯ y), which says that two
 elements have the same elements apart from them iff they are not
 apart, gives another way to see that it is an equivalence relation:

 \begin{code}

 not-apart-have-same-apart : {X : ð¤ Ì } (x y : X) (_â¯_ : X â X â ð¥ Ì )
                           â is-apartness _â¯_
                           â Â¬ (x â¯ y)
                           â ((z : X) â x â¯ z â y â¯ z)
 not-apart-have-same-apart {ð¤} {ð¥} {X} x y _â¯_ (p , i , s , c) = g
  where
   g : Â¬ (x â¯ y) â (z : X) â x â¯ z â y â¯ z
   g n z = gâ , gâ
    where
     gâ : x â¯ z â y â¯ z
     gâ a = s z y (left-fails-gives-right-holds (p z y) b n)
      where
       b : (x â¯ y) â¨ (z â¯ y)
       b = c x z y a

     n' : Â¬ (y â¯ x)
     n' a = n (s y x a)

     gâ : y â¯ z â x â¯ z
     gâ a = s z x (left-fails-gives-right-holds (p z x) b n')
      where
       b : (y â¯ x) â¨ (z â¯ x)
       b = c y z x a

 have-same-apart-are-not-apart : {X : ð¤ Ì } (x y : X) (_â¯_ : X â X â ð¥ Ì )
                               â is-apartness _â¯_
                               â ((z : X) â x â¯ z â y â¯ z)
                               â Â¬ (x â¯ y)
 have-same-apart-are-not-apart {ð¤} {ð¥} {X} x y _â¯_ (p , i , s , c) = f
  where
   f : ((z : X) â x â¯ z â y â¯ z) â Â¬ (x â¯ y)
   f Ï a = i y (prâ(Ï y) a)

\end{code}

 As far as we know, the above observation that the negation of
 apartness can be characterized in positive terms is new.

 Not-not equal elements are not apart, and hence, in the presence of
 tightness, they are equal. It follows that tight apartness types are
 sets.

\begin{code}

 not-not-equal-not-apart : {X : ð¤ Ì } (x y : X) (_â¯_ : X â X â ð¥ Ì )
                         â is-apartness _â¯_
                         â Â¬Â¬ (x â¡ y) â Â¬ (x â¯ y)
 not-not-equal-not-apart x y _â¯_ (_ , i , _ , _) = contrapositive f
  where
   f : x â¯ y â Â¬ (x â¡ y)
   f a p = i y (transport (Î» - â - â¯ y) p a)

 tight-is-Â¬Â¬-separated : {X : ð¤ Ì } (_â¯_ : X â X â ð¥ Ì )
                       â is-apartness _â¯_
                       â is-tight _â¯_
                       â is-Â¬Â¬-separated X
 tight-is-Â¬Â¬-separated _â¯_ a t = f
  where
   f : â x y â Â¬Â¬ (x â¡ y) â x â¡ y
   f x y Ï = t x y (not-not-equal-not-apart x y _â¯_ a Ï)

 tight-is-set : {X : ð¤ Ì } (_â¯_ : X â X â ð¥ Ì )
              â funext ð¤ ð¤â
              â is-apartness _â¯_
              â is-tight _â¯_
              â is-set X
 tight-is-set _â¯_ fe a t = Â¬Â¬-separated-types-are-sets fe (tight-is-Â¬Â¬-separated _â¯_ a t)

\end{code}

 The above use apartness data, but its existence is enough, because
 being a Â¬Â¬-separated type and being a set are propositions.

\begin{code}

 tight-separated' : funext ð¤ ð¤
                  â {X : ð¤ Ì }
                  â (â _â¯_ ê (X â X â ð¤ Ì ), is-apartness _â¯_ Ã is-tight _â¯_)
                  â is-Â¬Â¬-separated X
 tight-separated' {ð¤} fe {X} = â¥â¥-rec (being-Â¬Â¬-separated-is-prop fe) f
   where
    f : (Î£ _â¯_ ê (X â X â ð¤ Ì ), is-apartness _â¯_ Ã is-tight _â¯_) â is-Â¬Â¬-separated X
    f (_â¯_ , a , t) = tight-is-Â¬Â¬-separated _â¯_ a t

 tight-is-set' : funext ð¤ ð¤
               â {X : ð¤ Ì }
               â (â _â¯_ ê (X â X â ð¤ Ì ), is-apartness _â¯_ Ã is-tight _â¯_)
               â is-set X
 tight-is-set' {ð¤} fe {X} = â¥â¥-rec (being-set-is-prop fe) f
   where
    f : (Î£ _â¯_ ê (X â X â ð¤ Ì ), is-apartness _â¯_ Ã is-tight _â¯_) â is-set X
    f (_â¯_ , a , t) = tight-is-set _â¯_ (lower-funext ð¤ ð¤ fe) a t

\end{code}

 A map is called strongly extensional if it reflects apartness. In the
 category of apartness types, the morphisms are the strongly
 extensional maps.

\begin{code}

 is-strongly-extensional : â {ð£} {X : ð¤ Ì } {Y : ð¥ Ì }
                         â (X â X â ð¦ Ì ) â (Y â Y â ð£ Ì ) â (X â Y) â ð¤ â ð¦ â ð£ Ì
 is-strongly-extensional _â¯_ _â¯'_ f = â {x x'} â f x â¯' f x' â x â¯ x'

 preserves : â {ð£} {X : ð¤ Ì } {Y : ð¥ Ì }
           â (X â X â ð¦ Ì ) â (Y â Y â ð£ Ì ) â (X â Y) â ð¤ â ð¦ â ð£ Ì
 preserves R S f = â {x x'} â R x x' â S (f x) (f x')

 module TightReflection
          (fe : FunExt)
          (pe : propext ð¥)
          (X : ð¤ Ì )
          (_â¯_ : X â X â ð¥ Ì )
          (â¯p : is-prop-valued _â¯_)
          (â¯i : is-irreflexive _â¯_)
          (â¯s : is-symmetric _â¯_)
          (â¯c : is-cotransitive _â¯_)
   where

\end{code}

  We now name the standard equivalence relation induced by _â¯_.

\begin{code}

  _~_ : X â X â ð¥ Ì
  x ~ y = Â¬ (x â¯ y)

\end{code}

  For certain purposes we need the apartness axioms packed in to a
  single axiom.

\begin{code}

  â¯a : is-apartness _â¯_
  â¯a = (â¯p , â¯i , â¯s , â¯c)

\end{code}

  Initially we tried to work with the function apart : X â (X â ð¥ Ì )
  defined by apart = _â¯_. However, at some point in the development
  below it was difficult to proceed, when we need that the identity
  type apart x = apart y is a proposition. This should be the case
  because _â¯_ is is-prop-valued. The most convenient way to achieve this
  is to restrict the codomain of apart from ð¥ to Î©, so that the
  codomain of apart is a set.

\begin{code}

  Î± : X â (X â Î© ð¥)
  Î± x y = x â¯ y , â¯p x y

\end{code}

  The following is an immediate consequence of the fact that two
  equivalent elements have the same apartness class, using functional
  and propositional extensionality.

\begin{code}

  Î±-lemma : (x y : X) â x ~ y â Î± x â¡ Î± y
  Î±-lemma x y na = dfunext (fe ð¤ (ð¥ âº)) h
   where
    f : (z : X) â x â¯ z â y â¯ z
    f = not-apart-have-same-apart x y _â¯_ â¯a na

    g : (z : X) â x â¯ z â¡ y â¯ z
    g z = pe (â¯p x z) (â¯p y z) (prâ (f z)) (prâ (f z))

    h : (z : X) â Î± x z â¡ Î± y z
    h z = to-Î£-â¡ (g z , being-prop-is-prop (fe ð¥ ð¥) _ _)

\end{code}

  We now construct the tight reflection of (X,â¯) to get (X',â¯')
  together with a universal strongly extensional map from X into tight
  apartness types. We take X' to be the image of the map Î±.

\begin{code}

  open ImageAndSurjection pt

  X' : ð¤ â ð¥ âº Ì
  X' = image Î±

\end{code}

The type X may or may not be a set, but its tight reflection is
necessarily a set, and we can see this before we define a tight
apartness on it.

\begin{code}

  X'-is-set : is-set X'
  X'-is-set = subsets-of-sets-are-sets (X â Î© ð¥) _
                (powersets-are-sets'' (fe ð¤ (ð¥ âº)) (fe ð¥ ð¥) pe) â¥â¥-is-prop

  Î· : X â X'
  Î· = corestriction Î±

\end{code}

  The following induction principle is our main tool. Its uses look
  convoluted at times by the need to show that the property one is
  doing induction over is proposition valued. Typically this involves
  the use of the fact the propositions form an exponential ideal, and,
  more generally, are closed under products.

\begin{code}

  Î·-is-surjection : is-surjection Î·
  Î·-is-surjection = corestriction-is-surjection Î±

  Î·-induction : (P : X' â ð¦ Ì )
              â ((x' : X') â is-prop (P x'))
              â ((x : X) â P (Î· x))
              â (x' : X') â P x'
  Î·-induction = surjection-induction Î· Î·-is-surjection

\end{code}

  The apartness relation _â¯'_ on X' is defined as follows.

\begin{code}

  _â¯'_ : X' â X' â ð¤ â ð¥ âº Ì
  (u , _) â¯' (v , _) = â x ê X , Î£ y ê X , (x â¯ y) Ã (Î± x â¡ u) Ã (Î± y â¡ v)

\end{code}

  Then Î· preserves and reflects apartness.

\begin{code}

  Î·-preserves-apartness : preserves _â¯_ _â¯'_ Î·
  Î·-preserves-apartness {x} {y} a = â£ x , y , a , refl , refl â£

  Î·-is-strongly-extensional : is-strongly-extensional _â¯_ _â¯'_ Î·
  Î·-is-strongly-extensional {x} {y} = â¥â¥-rec (â¯p x y) g
   where
    g : (Î£ x' ê X , Î£ y' ê X , (x' â¯ y') Ã (Î± x' â¡ Î± x) Ã (Î± y' â¡ Î± y))
      â x â¯ y
    g (x' , y' , a , p , q) = â¯s _ _ (j (â¯s _ _ (i a)))
     where
      i : x' â¯ y' â x â¯ y'
      i = idtofun _ _ (ap prâ (happly p y'))

      j : y' â¯ x â y â¯ x
      j = idtofun _ _ (ap prâ (happly q x))

\end{code}

  Of course, we must check that _â¯'_ is indeed an apartness
  relation. We do this by Î·-induction. These proofs by induction need
  routine proofs that some things are propositions. We include the
  following abbreviation `fuv` to avoid some long lines in such
  proofs.

\begin{code}

  fuv : funext (ð¤ â ð¥ âº) (ð¤ â ð¥ âº)
  fuv = fe (ð¤ â ð¥ âº) (ð¤ â ð¥ âº)

  â¯'p : is-prop-valued _â¯'_
  â¯'p _ _ = â¥â¥-is-prop

  â¯'i : is-irreflexive _â¯'_
  â¯'i = by-induction
   where
    induction-step : â x â Â¬ (Î· x â¯' Î· x)
    induction-step x a = â¯i x (Î·-is-strongly-extensional a)

    by-induction : _
    by-induction = Î·-induction (Î» x' â Â¬ (x' â¯' x'))
                      (Î» _ â Î -is-prop (fe (ð¤ â ð¥ âº) ð¤â) (Î» _ â ð-is-prop))
                      induction-step

  â¯'s : is-symmetric _â¯'_
  â¯'s = by-nested-induction
   where
    induction-step : â x y â Î· x â¯' Î· y â Î· y â¯' Î· x
    induction-step x y a = Î·-preserves-apartness(â¯s x y (Î·-is-strongly-extensional a))

    by-nested-induction : _
    by-nested-induction =
      Î·-induction (Î» x' â â y' â x' â¯' y' â y' â¯' x')
       (Î» x' â Î -is-prop fuv
                (Î» y' â Î -is-prop fuv (Î» _ â â¯'p y' x')))
       (Î» x â Î·-induction (Î» y' â Î· x â¯' y' â y' â¯' Î· x)
                (Î» y' â Î -is-prop fuv (Î» _ â â¯'p y' (Î· x)))
                (induction-step x))

  â¯'c : is-cotransitive _â¯'_
  â¯'c = by-nested-induction
   where
    induction-step : â x y z â Î· x â¯' Î· y â Î· x â¯' Î· z â¨ Î· y â¯' Î· z
    induction-step x y z a = â¥â¥-functor c b
     where
      a' : x â¯ y
      a' = Î·-is-strongly-extensional a

      b : x â¯ z â¨ y â¯ z
      b = â¯c x y z a'

      c : (x â¯ z) + (y â¯ z) â (Î· x â¯' Î· z) + (Î· y â¯' Î· z)
      c (inl e) = inl (Î·-preserves-apartness e)
      c (inr f) = inr (Î·-preserves-apartness f)

    by-nested-induction : _
    by-nested-induction =
      Î·-induction (Î» x' â â y' z' â x' â¯' y' â (x' â¯' z') â¨ (y' â¯' z'))
       (Î» _ â Î -is-prop fuv
                (Î» _ â Î -is-prop fuv
                         (Î» _ â Î -is-prop fuv (Î» _ â â¥â¥-is-prop))))
       (Î» x â Î·-induction (Î» y' â â z' â Î· x â¯' y' â (Î· x â¯' z') â¨ (y' â¯' z'))
                (Î» _ â Î -is-prop fuv
                         (Î» _ â Î -is-prop fuv (Î» _ â â¥â¥-is-prop)))
                (Î» y â Î·-induction (Î» z' â Î· x â¯' Î· y â (Î· x â¯' z') â¨ (Î· y â¯' z'))
                         (Î» _ â Î -is-prop fuv (Î» _ â â¥â¥-is-prop))
                         (induction-step x y)))

  â¯'a : is-apartness _â¯'_
  â¯'a = (â¯'p , â¯'i , â¯'s , â¯'c)

\end{code}

  The tightness of _â¯'_ cannot by proved by induction by reduction to
  properties of _â¯_, as above, because _â¯_ is not (necessarily)
  tight. We need to work with the definitions of X' and _â¯'_ directly.

\begin{code}

  â¯'t : is-tight _â¯'_
  â¯'t (u , e) (v , f) n = â¥â¥-rec X'-is-set (Î» Ï â â¥â¥-rec X'-is-set (h Ï) f) e
   where
    h : (Î£ x ê X , Î± x â¡ u) â (Î£ y ê X , Î± y â¡ v) â (u , e) â¡ (v , f)
    h (x , p) (y , q) = to-Î£-â¡ (t , â¥â¥-is-prop _ _)
     where
      remark : (â x ê X , Î£ y ê X , (x â¯ y) Ã (Î± x â¡ u) Ã (Î± y â¡ v)) â ð
      remark = n

      r : x â¯ y â ð
      r a = n â£ x , y , a , p , q â£

      s : Î± x â¡ Î± y
      s = Î±-lemma x y r

      t : u â¡ v
      t = p â»Â¹ â s â q

\end{code}

  The tightness of _â¯'_ gives that Î· maps equivalent elements to equal
  elements, and its irreflexity gives that elements with the same Î·
  image are equivalent.

\begin{code}

  Î·-equiv-equal : {x y : X} â x ~ y â Î· x â¡ Î· y
  Î·-equiv-equal = â¯'t _ _ â contrapositive Î·-is-strongly-extensional

  Î·-equal-equiv : {x y : X} â Î· x â¡ Î· y â x ~ y
  Î·-equal-equiv {x} {y} p a = â¯'i (Î· y) (transport (Î» - â - â¯' Î· y) p (Î·-preserves-apartness a))

\end{code}

  We now show that the above data provide the tight reflection, or
  universal strongly extensional map from X to tight apartness types,
  where unique existence is expressed by saying that a Î£ type is a
  singleton, as usual in univalent mathematics and homotopy type
  theory. Notice the use of Î·-induction to avoid dealing directly with
  the details of the constructions performed above.

\begin{code}

  tight-reflection : (A : ð¦ Ì ) (_â¯á´¬_ : A â A â ð£ Ì )
                   â is-apartness _â¯á´¬_
                   â is-tight _â¯á´¬_
                   â (f : X â A)
                   â is-strongly-extensional _â¯_ _â¯á´¬_ f
                   â â! f' ê (X' â A) , f' â Î· â¡ f
  tight-reflection {ð¦} {ð£} A  _â¯á´¬_  â¯á´¬a  â¯á´¬t  f  se = Î´
   where
    A-is-set : is-set A
    A-is-set = tight-is-set _â¯á´¬_ (fe ð¦ ð¤â) â¯á´¬a â¯á´¬t

    i : {x y : X} â x ~ y â f x â¡ f y
    i = â¯á´¬t _ _ â contrapositive se

    Ï : (x' : X') â is-prop (Î£ a ê A , â x ê X , (Î· x â¡ x') Ã (f x â¡ a))
    Ï = Î·-induction _ Î³ induction-step
      where
       induction-step : (y : X) â is-prop (Î£ a ê A , â x ê X , (Î· x â¡ Î· y) Ã (f x â¡ a))
       induction-step x (a , d) (b , e) = to-Î£-â¡ (p , â¥â¥-is-prop _ _)
        where
         h : (Î£ x' ê X , (Î· x' â¡ Î· x) Ã (f x' â¡ a))
           â (Î£ y' ê X , (Î· y' â¡ Î· x) Ã (f y' â¡ b))
           â a â¡ b
         h (x' , r , s) (y' , t , u) = s â»Â¹ â i (Î·-equal-equiv (r â t â»Â¹)) â u

         p : a â¡ b
         p = â¥â¥-rec A-is-set (Î» Ï â â¥â¥-rec A-is-set (h Ï) e) d

       Î³ : (x' : X') â is-prop (is-prop (Î£ a ê A , â x ê X , (Î· x â¡ x') Ã (f x â¡ a)))
       Î³ x' = being-prop-is-prop (fe (ð¤ â (ð¥ âº) â ð¦) (ð¤ â (ð¥ âº) â ð¦))

    k : (x' : X') â Î£ a ê A , â x ê X , (Î· x â¡ x') Ã (f x â¡ a)
    k = Î·-induction _ Ï induction-step
     where
      induction-step : (y : X) â Î£ a ê A , â x ê X , (Î· x â¡ Î· y) Ã (f x â¡ a)
      induction-step x = f x , â£ x , refl , refl â£

    f' : X' â A
    f' x' = prâ(k x')

    r : f' â Î· â¡ f
    r = dfunext (fe ð¤ ð¦) h
     where
      g : (y : X) â â x ê X , (Î· x â¡ Î· y) Ã (f x â¡ f' (Î· y))
      g y = prâ(k(Î· y))

      j : (y : X) â (Î£ x ê X , (Î· x â¡ Î· y) Ã (f x â¡ f' (Î· y))) â f'(Î· y) â¡ f y
      j y (x , p , q) = q â»Â¹ â i (Î·-equal-equiv p)

      h : (y : X) â f'(Î· y) â¡ f y
      h y = â¥â¥-rec A-is-set (j y) (g y)

    c : (Ï : Î£ f'' ê (X' â A), f'' â Î· â¡ f) â (f' , r) â¡ Ï
    c (f'' , s) = to-Î£-â¡ (t , v)
     where
      w : â x â f'(Î· x) â¡ f''(Î· x)
      w = happly (r â s â»Â¹)

      t : f' â¡ f''
      t = dfunext (fe (ð¤ â ð¥ âº) ð¦) (Î·-induction _ (Î» _ â A-is-set) w)

      u : f'' â Î· â¡ f
      u = transport (Î» - â - â Î· â¡ f) t r

      v : u â¡ s
      v = Î -is-set (fe ð¤ ð¦) (Î» _ â A-is-set) u s

    Î´ : â! f' ê (X' â A), f' â Î· â¡ f
    Î´ = (f' , r) , c

\end{code}

  The following is an immediate consequence of the tight reflection,
  by the usual categorical argument, using the fact that the identity
  map is strongly extensional (with the identity function as the
  proof). Notice that our construction of the reflection produces a
  result in a universe higher than those where the starting data are,
  to avoid impredicativity (aka propositional resizing). Nevertheless,
  the usual categorical argument is applicable.

  A direct proof that doesn't rely on the tight reflection is equally
  short in this case, and is also included.

  What the following construction says is that if _â¯_ is tight, then
  any element of X is uniquely determined by the set of elements apart
  from it.

\begin{code}

  tight-Î·-equiv-abstract-nonsense : is-tight _â¯_ â X â X'
  tight-Î·-equiv-abstract-nonsense â¯t = Î· , (Î¸ , happly pâ) , (Î¸ , happly pâ)
   where
    u : â! Î¸ ê (X' â X), Î¸ â Î· â¡ id
    u = tight-reflection X _â¯_ â¯a â¯t id id

    v : â! Î¶ ê (X' â X'), Î¶ â Î· â¡ Î·
    v = tight-reflection X' _â¯'_ â¯'a â¯'t Î· Î·-is-strongly-extensional

    Î¸ : X' â X
    Î¸ = prâ(prâ u)

    Î¶ : X' â X'
    Î¶ = prâ(prâ v)

    Ï : (Î¶' : X' â X') â Î¶' â Î· â¡ Î· â Î¶ â¡ Î¶'
    Ï Î¶' p = ap prâ (prâ v (Î¶' , p))

    pâ : Î¸ â Î· â¡ id
    pâ = prâ(prâ u)

    pâ : Î· â Î¸ â Î· â¡ Î·
    pâ = ap (_â_ Î·) pâ

    pâ : Î¶ â¡ Î· â Î¸
    pâ = Ï (Î· â Î¸) pâ

    pâ : Î¶ â¡ id
    pâ = Ï id refl

    pâ : Î· â Î¸ â¡ id
    pâ = pâ â»Â¹ â pâ

  tight-Î·-equiv-direct : is-tight _â¯_ â X â X'
  tight-Î·-equiv-direct t = (Î· , vv-equivs-are-equivs Î· cm)
   where
    lc : left-cancellable Î·
    lc {x} {y} p = i h
     where
      i : Â¬ (Î· x â¯' Î· y) â x â¡ y
      i = t x y â contrapositive (Î·-preserves-apartness {x} {y})

      h : Â¬ (Î· x â¯' Î· y)
      h a = â¯'i (Î· y) (transport (Î» - â - â¯' Î· y) p a)

    e : is-embedding Î·
    e =  lc-maps-into-sets-are-embeddings Î· lc X'-is-set

    cm : is-vv-equiv Î·
    cm = surjective-embeddings-are-vv-equivs Î· e Î·-is-surjection

\end{code}

TODO.

* The tight reflection has the universal property of the quotient by
  _~_. Conversely, the quotient by _~_ gives the tight reflection.

* The tight reflection of â¯â has the universal property of the totally
  separated reflection.
