Tom de Jong & Martin Escardo, 20 May 2019.
Refactored January 2020, December 2021 by Tom de Jong.

Definitions of:
 * Directed complete posets (dcpos).
 * Scott continuous maps.
 * Pointed dcpos (i.e. dcpos with a least element) and strict continuous maps
   (i.e. continuous maps that preserve the least element)

See Dcpos.lagda for an overview of the formalization the theory of dcpos.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

open import UF-FunExt
open import UF-PropTrunc

module Dcpo
        (pt : propositional-truncations-exist)
        (fe : â {ð¤ ð¥} â funext ð¤ ð¥)
        (ð¥ : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt hiding (is-inhabited; being-inhabited-is-prop)

open import UF-Subsingletons
open import UF-Subsingletons-FunExt

open import Poset fe

module _ {ð¤ ð£ : Universe}
         {D : ð¤ Ì }
         (_â_ : D â D â ð£ Ì )
       where

 open PosetAxioms _â_

 is-upperbound : {I : ð¥ Ì } (u : D) (Î± : I â D) â ð¥ â ð£ Ì
 is-upperbound u Î± = (i : domain Î±) â Î± i â u

 is-lowerbound-of-upperbounds : {I : ð¥ Ì } (u : D) (Î± : I â D) â ð¥ â ð¤ â ð£ Ì
 is-lowerbound-of-upperbounds u Î± = (v : D) â is-upperbound v Î± â u â v

 is-sup : {I : ð¥ Ì } â D â (I â D) â ð¤ â ð¥ â ð£ Ì
 is-sup s Î± = (is-upperbound s Î±) Ã (is-lowerbound-of-upperbounds s Î±)

 sup-is-upperbound : {I : ð¥ Ì } {s : D} {Î± : I â D}
                   â is-sup s Î±
                   â is-upperbound s Î±
 sup-is-upperbound i = prâ i

 sup-is-lowerbound-of-upperbounds : {I : ð¥ Ì } {s : D} {Î± : I â D}
                                  â is-sup s Î±
                                  â (u : D)
                                  â is-upperbound u Î± â s â u
 sup-is-lowerbound-of-upperbounds i = prâ i

 has-sup : {I : ð¥ Ì } â (I â D) â ð¤ â ð¥ â ð£ Ì
 has-sup Î± = Î£ s ê D , is-sup s Î±

 the-sup : {I : ð¥ Ì } {Î± : I â D} â has-sup Î± â D
 the-sup (s , i) = s

 sup-property : {I : ð¥ Ì } {Î± : I â D} (h : has-sup Î±) â is-sup (the-sup h) Î±
 sup-property (s , i) = i

 is-inhabited : (X : ð¥ Ì ) â ð¥ Ì
 is-inhabited = â¥_â¥

 is-semidirected : {I : ð¥ Ì  } â (I â D) â ð¥ â ð£ Ì
 is-semidirected {I} Î± = (i j : I) â â k ê I , (Î± i â Î± k) Ã (Î± j â Î± k)

 is-directed : {I : ð¥ Ì } â (I â D) â ð¥ â ð£ Ì
 is-directed {I} Î± = is-inhabited I Ã is-semidirected Î±

 inhabited-if-directed : {I : ð¥ Ì } (Î± : I â D) â is-directed Î± â â¥ I â¥
 inhabited-if-directed Î± = prâ

 semidirected-if-directed : {I : ð¥ Ì } (Î± : I â D) â is-directed Î±
                               â (i j : I) â â k ê I , (Î± i â Î± k) Ã (Î± j â Î± k)
 semidirected-if-directed Î± = prâ

 being-inhabited-is-prop : {I : ð¥ Ì } â is-prop (is-inhabited I)
 being-inhabited-is-prop = â¥â¥-is-prop

 being-semidirected-is-prop : {I : ð¥ Ì  } (Î± : I â D) â is-prop (is-semidirected Î±)
 being-semidirected-is-prop Î± = Î â-is-prop fe (Î» i j â â¥â¥-is-prop)

 being-directed-is-prop : {I : ð¥ Ì } (Î± : I â D) â is-prop (is-directed Î±)
 being-directed-is-prop Î± =
  Ã-is-prop being-inhabited-is-prop (being-semidirected-is-prop Î±)

 is-directed-complete : ð¤ â (ð¥ âº) â ð£  Ì
 is-directed-complete = (I : ð¥ Ì ) (Î± : I â D) â is-directed Î± â has-sup Î±

 dcpo-axioms : ð¤ â (ð¥ âº) â ð£ Ì
 dcpo-axioms = poset-axioms Ã is-directed-complete

 is-sup-is-prop : dcpo-axioms â {I : ð¥ Ì } (d : D) (Î± : I â D)
                â is-prop (is-sup d Î±)
 is-sup-is-prop ((s , p , r , t , a) , c) {I} d Î± = Î³
  where
   Î³ : is-prop (is-sup d Î±)
   Î³ = Ã-is-prop (Î -is-prop fe (Î» i â p (Î± i) d))
                 (Î â-is-prop fe (Î» x l â p d x))

 sups-are-unique : dcpo-axioms
                 â {I : ð¥ Ì } (Î± : I â D) {x y : D}
                 â is-sup x Î± â is-sup y Î± â x â¡ y
 sups-are-unique ((s , p , r , t , a) , c) {I} Î± {x} {y} x-is-sup y-is-sup =
  a x y
   (sup-is-lowerbound-of-upperbounds x-is-sup y (sup-is-upperbound y-is-sup))
   (sup-is-lowerbound-of-upperbounds y-is-sup x (sup-is-upperbound x-is-sup))

 having-sup-is-prop : dcpo-axioms â {I : ð¥ Ì } (Î± : I â D)
                    â is-prop (has-sup Î±)
 having-sup-is-prop ax {I} Î± Ï Ï =
  to-subtype-â¡ (Î» x â is-sup-is-prop ax x Î±)
               (sups-are-unique ax Î± (prâ Ï) (prâ Ï))

 being-directed-complete-is-prop : dcpo-axioms â is-prop is-directed-complete
 being-directed-complete-is-prop a =
  Î â-is-prop fe (Î» I Î± Î´ â having-sup-is-prop a Î±)

 dcpo-axioms-is-prop : is-prop dcpo-axioms
 dcpo-axioms-is-prop = prop-criterion Î³
  where
   Î³ : dcpo-axioms â is-prop dcpo-axioms
   Î³ a = Ã-is-prop poset-axioms-is-prop
                   (being-directed-complete-is-prop a)

\end{code}

Since we will also consider dcpos with a least element, we also make the
following definitions.

\begin{code}

 is-least : D â ð¤ â ð£ Ì
 is-least x = â (y : D) â x â y

 has-least : ð¤ â ð£ Ì
 has-least = Î£ x ê D , is-least x

\end{code}

We have now developed enough material to define dcpos and we introduce some
convenient projections.

\begin{code}

module _ {ð¤ ð£ : Universe} where

 open PosetAxioms

 DCPO-structure : ð¤ Ì â ð¤ â (ð¥ âº) â (ð£ âº) Ì
 DCPO-structure D = Î£ _â_ ê (D â D â ð£ Ì ), (dcpo-axioms {ð¤} {ð£} _â_)

 DCPO : (ð¤ âº) â (ð¥ âº) â (ð£ âº) Ì
 DCPO = Î£ D ê ð¤ Ì , DCPO-structure D

 â¨_â© : DCPO â ð¤ Ì
 â¨ D , _â_ , d â© = D

 underlying-order : (ð : DCPO) â â¨ ð â© â â¨ ð â© â ð£ Ì
 underlying-order (D , _â_ , d) = _â_

 syntax underlying-order ð x y = x ââ¨ ð â© y

 axioms-of-dcpo : (ð : DCPO) â dcpo-axioms (underlying-order ð)
 axioms-of-dcpo (D , _â_ , d) = d

 sethood : (ð : DCPO) â is-set â¨ ð â©
 sethood (D , _â_ , (s  , p  , r  , t  , a)  , c ) = s

 prop-valuedness : (ð : DCPO) â is-prop-valued (underlying-order ð )
 prop-valuedness (D , _â_ , (s  , p  , r  , t  , a)  , c ) = p

 reflexivity : (ð : DCPO) â is-reflexive (underlying-order ð)
 reflexivity (D , _â_ , (s  , p  , r  , t  , a)  , c ) = r

 transitivity : (ð : DCPO) â is-transitive (underlying-order ð)
 transitivity (D , _â_ , (s  , p  , r  , t  , a)  , c ) = t

 antisymmetry : (ð : DCPO) â is-antisymmetric (underlying-order ð)
 antisymmetry (D , _â_ , (s  , p  , r  , t  , a)  , c ) = a

\end{code}

We also consider pointed dcpos, i.e. dcpos with a least element.

\begin{code}

 DCPOâ¥ : (ð¥ âº) â (ð¤ âº) â (ð£ âº) Ì
 DCPOâ¥ = Î£ ð ê DCPO , has-least (underlying-order ð)

 _â» : DCPOâ¥ â DCPO
 _â» = prâ

 âª_â« : DCPOâ¥ â ð¤ Ì
 âª ð â« = â¨ ð â» â©

 underlying-orderâ¥ : (ð : DCPOâ¥) â âª ð â« â âª ð â« â ð£ Ì
 underlying-orderâ¥ ð = underlying-order (ð â»)

 syntax underlying-orderâ¥ ð x y = x ââª ð â« y

 â¥ : (ð : DCPOâ¥) â â¨ ð â» â©
 â¥ (ð , x , p) = x

 â¥-is-least : (ð : DCPOâ¥) â is-least (underlying-order (ð â»)) (â¥ ð)
 â¥-is-least (ð , x , p) = p

\end{code}

We introduce pretty syntax for chain reasoning with inequalities.
(Cf. â¡â¨_â© and â in Id.lagda, ââ¨_â© and â  in UF-Equiv.lagda)

For example, given (a b c d : â¨ ð â©) and
u : a ââ¨ ð â© b
v : b ââ¨ ð â© c
w : c ââ¨ ð â© d

this will allow us to write

z : a ââ¨ ð â© d
z = a ââ¨ ð â©[ u ]
    b ââ¨ ð â©[ v ]
    c ââ¨ ð â©[ w ]
    d ââ¨ ð â©

rather than the hard(er) to read

z : a ââ¨ ð â© d
z = transitivity ð a c d z' w
 where
  z' : a ââ¨ ð â© c
  z' = transitivity ð a b c u v

\begin{code}

 transitivity' : (ð : DCPO) (x : â¨ ð â©) {y z : â¨ ð â©}
               â x ââ¨ ð â© y â y ââ¨ ð â© z â x ââ¨ ð â© z
 transitivity' ð x {y} {z} u v = transitivity ð x y z u v

 syntax transitivity' ð x u v = x ââ¨ ð â©[ u ] v
 infixr 0 transitivity'

 syntax reflexivity ð x = x ââ¨ ð â©
 infix 1 reflexivity

 transitivity'' : (ð : DCPOâ¥) (x : âª ð â«) {y z : âª ð â«}
               â x ââª ð â« y â y ââª ð â« z â x ââª ð â« z
 transitivity'' ð = transitivity' (ð â»)

 reflexivity' : (ð : DCPOâ¥) â is-reflexive (underlying-order (ð â»))
 reflexivity' (D , _) = reflexivity D

 syntax transitivity'' ð x u v = x ââª ð â«[ u ] v
 infixr 0 transitivity''

 syntax reflexivity' ð x = x ââª ð â«
 infix 1 reflexivity'

\end{code}

Next, we introduce â-notation for the supremum of a directed family in a dcpo.

\begin{code}

 directed-completeness : (ð : DCPO) â is-directed-complete (underlying-order ð)
 directed-completeness (D , _â_ , a) = prâ a

 is-Semidirected : (ð : DCPO) {I : ð¥ Ì } (Î± : I â â¨ ð â©) â ð¥ â ð£ Ì
 is-Semidirected ð Î± = is-semidirected (underlying-order ð) Î±

 is-Directed : (ð : DCPO) {I : ð¥ Ì } (Î± : I â â¨ ð â©) â ð¥ â ð£ Ì
 is-Directed ð Î± = is-directed (underlying-order ð) Î±

 inhabited-if-Directed : (ð : DCPO) {I : ð¥ Ì} (Î± : I â â¨ ð â©)
                       â is-Directed ð Î±
                       â â¥ I â¥
 inhabited-if-Directed ð Î± = prâ

 semidirected-if-Directed : (ð : DCPO) {I : ð¥ Ì} (Î± : I â â¨ ð â©)
                          â is-Directed ð Î±
                          â is-Semidirected ð Î±
 semidirected-if-Directed ð Î± = prâ

 â : (ð : DCPO) {I : ð¥ Ì } {Î± : I â â¨ ð â©} â is-Directed ð Î± â â¨ ð â©
 â ð {I} {Î±} Î´ = prâ (directed-completeness ð I Î± Î´)

 â-is-sup : (ð : DCPO) {I : ð¥ Ì } {Î± : I â â¨ ð â©} (Î´ : is-Directed ð Î±)
          â is-sup (underlying-order ð) (â ð Î´) Î±
 â-is-sup ð {I} {Î±} Î´ = prâ (directed-completeness ð I Î± Î´)

 â-is-upperbound : (ð : DCPO) {I : ð¥ Ì } {Î± : I â â¨ ð â©} (Î´ : is-Directed ð Î±)
                 â is-upperbound (underlying-order ð) (â ð Î´) Î±
 â-is-upperbound ð Î´ = prâ (â-is-sup ð Î´)

 â-is-lowerbound-of-upperbounds : (ð : DCPO) {I : ð¥ Ì } {Î± : I â â¨ ð â©}
                                  (Î´ : is-Directed ð Î±)
                                â is-lowerbound-of-upperbounds
                                    (underlying-order ð) (â ð Î´) Î±
 â-is-lowerbound-of-upperbounds ð Î´ = prâ (â-is-sup ð Î´)

\end{code}

Finally, we define (strict) continuous maps between (pointed) dcpos.

\begin{code}

is-continuous : (ð : DCPO {ð¤} {ð£}) (ð : DCPO {ð¤'} {ð£'})
              â (â¨ ð â© â â¨ ð â©)
              â ð¥ âº â ð¤ â ð£ â ð¤' â ð£' Ì
is-continuous ð ð f = (I : ð¥ Ì ) (Î± : I â â¨ ð â©) (Î´ : is-Directed ð Î±)
                     â is-sup (underlying-order ð) (f (â ð Î´)) (f â Î±)

being-continuous-is-prop : (ð : DCPO {ð¤} {ð£}) (ð : DCPO {ð¤'} {ð£'})
                             (f : â¨ ð â© â â¨ ð â©)
                           â is-prop (is-continuous ð ð f)
being-continuous-is-prop ð ð f =
 Î â-is-prop fe (Î» I Î± Î´ â is-sup-is-prop (underlying-order ð)
                          (axioms-of-dcpo ð)
                          (f (â ð Î´)) (f â Î±))

DCPO[_,_] : DCPO {ð¤} {ð£} â DCPO {ð¤'} {ð£'} â ð¥ âº â ð¤ â ð£ â ð¤' â ð£' Ì
DCPO[ ð , ð ] = Î£ f ê (â¨ ð â© â â¨ ð â©) , is-continuous ð ð f

DCPOâ¥[_,_] : DCPOâ¥ {ð¤} {ð£} â DCPOâ¥ {ð¤'} {ð£'} â (ð¥ âº) â ð¤ â ð£ â ð¤' â ð£' Ì
DCPOâ¥[ ð , ð ] = DCPO[ ð â» , ð â» ]

underlying-function : (ð : DCPO {ð¤} {ð£}) (ð : DCPO {ð¤'} {ð£'})
                    â DCPO[ ð , ð ] â â¨ ð â© â â¨ ð â©
underlying-function ð ð (f , _) = f

syntax underlying-function ð ð f = [ ð , ð ]â¨ f â©

continuity-of-function : (ð : DCPO {ð¤} {ð£}) (ð : DCPO {ð¤'} {ð£'}) (f : DCPO[ ð , ð ])
                       â is-continuous ð ð [ ð ,  ð ]â¨ f â©
continuity-of-function ð ð (_ , c) = c

is-strict : (ð : DCPOâ¥ {ð¤} {ð£}) (ð : DCPOâ¥ {ð¤'} {ð£'})
          â (âª ð â« â âª ð â«)
          â ð¤' Ì
is-strict ð ð f = f (â¥ ð) â¡ â¥ ð

being-strict-is-prop : (ð : DCPOâ¥ {ð¤} {ð£}) (ð : DCPOâ¥ {ð¤'} {ð£'})
                       (f : âª ð â« â âª ð â«)
                     â is-prop (is-strict ð ð f)
being-strict-is-prop ð ð f = sethood (ð â»)

strictness-criterion : (ð : DCPOâ¥ {ð¤} {ð£}) (ð : DCPOâ¥ {ð¤'} {ð£'})
                       (f : âª ð â« â âª ð â«)
                     â f (â¥ ð) ââª ð â« â¥ ð
                     â is-strict ð ð f
strictness-criterion ð ð f crit =
 antisymmetry (ð â») (f (â¥ ð)) (â¥ ð) crit (â¥-is-least ð (f (â¥ ð)))

\end{code}
