Martin Escardo, 29 June 2018

The type Ordinals of ordinals in a universe U, and the subtype Ordinalsáµ of
ordinals with a top element.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

open import OrdinalNotions

open import UF-Base
open import UF-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Embeddings

module OrdinalsType where

\end{code}

An ordinal is a type equipped with ordinal structure. Such a type is
automatically a set.

\begin{code}

OrdinalStructure : ð¤ Ì â ð¤ âº Ì
OrdinalStructure {ð¤} X = Î£ _<_ ê (X â X â ð¤ Ì ) , (is-well-order _<_)

Ordinal : â ð¤ â ð¤ âº Ì
Ordinal ð¤ = Î£ X ê ð¤ Ì , OrdinalStructure X

Ord = Ordinal ð¤â

\end{code}

NB. Perhaps we will eventually need to have two parameters ð¤ (the
universe where the underlying type X lives) and ð¥ (the universe where
_<_ takes values in) for Ordinal.

Ordinals are ranged over by Î±,Î²,Î³.

The underlying type of an ordinal (which happens to be necessarily a
set):

\begin{code}

â¨_â© : Ordinal ð¤ â ð¤ Ì
â¨ X , _<_ , o â© = X

structure : (Î± : Ordinal ð¤) â OrdinalStructure â¨ Î± â©
structure (X , s) = s

underlying-order : (Î± : Ordinal ð¤) â â¨ Î± â© â â¨ Î± â© â ð¤ Ì
underlying-order (X , _<_ , o) = _<_

underlying-weak-order : (Î± : Ordinal ð¤) â â¨ Î± â© â â¨ Î± â© â ð¤ Ì
underlying-weak-order Î± x y = Â¬ (underlying-order Î± y x)

underlying-porder : (Î± : Ordinal ð¤) â â¨ Î± â© â â¨ Î± â© â ð¤ Ì
underlying-porder (X , _<_ , o) = extensional-po _<_

syntax underlying-order       Î± x y = x âºâ¨ Î± â© y
syntax underlying-weak-order  Î± x y = x â¾â¨ Î± â© y
syntax underlying-porder      Î± x y = x â¼â¨ Î± â© y

is-well-ordered : (Î± : Ordinal ð¤) â is-well-order (underlying-order Î±)
is-well-ordered (X , _<_ , o) = o

Prop-valuedness : (Î± : Ordinal ð¤) â is-prop-valued (underlying-order Î±)
Prop-valuedness Î± = prop-valuedness (underlying-order Î±) (is-well-ordered Î±)

Transitivity : (Î± : Ordinal ð¤) â is-transitive (underlying-order Î±)
Transitivity Î± = transitivity (underlying-order Î±) (is-well-ordered Î±)

Well-foundedness : (Î± : Ordinal ð¤) (x : â¨ Î± â©) â is-accessible (underlying-order Î±) x
Well-foundedness Î± = well-foundedness (underlying-order Î±) (is-well-ordered Î±)

Transfinite-induction : (Î± : Ordinal ð¤)
                      â (P : â¨ Î± â© â ð¦ Ì )
                      â ((x : â¨ Î± â©) â ((y : â¨ Î± â©) â y âºâ¨ Î± â© x â P y) â P x)
                      â (x : â¨ Î± â©) â P x
Transfinite-induction Î± = transfinite-induction
                           (underlying-order Î±)
                           (Well-foundedness Î±)

Extensionality : (Î± : Ordinal ð¤) â is-extensional (underlying-order Î±)
Extensionality Î± = extensionality (underlying-order Î±) (is-well-ordered Î±)

underlying-type-is-set : FunExt
                       â (Î± : Ordinal ð¤)
                       â is-set â¨ Î± â©
underlying-type-is-set fe Î± =
 extensionally-ordered-types-are-sets
  (underlying-order Î±)
  fe
  (Prop-valuedness Î±)
  (Extensionality Î±)

has-bottom : Ordinal ð¤ â ð¤ Ì
has-bottom Î± = Î£ â¥ ê â¨ Î± â© , ((x : â¨ Î± â©) â â¥ â¼â¨ Î± â© x)

having-bottom-is-prop : Fun-Ext â (Î± : Ordinal ð¤) â is-prop (has-bottom Î±)
having-bottom-is-prop fe Î± (â¥ , l) (â¥' , l') =
  to-subtype-â¡
    (Î» _ â Î â-is-prop fe (Î» x y _ â Prop-valuedness Î± y x))
    (Extensionality Î± â¥ â¥' (l â¥') (l' â¥))

\end{code}

TODO. We should add further properties of the order from the module
OrdinalNotions. For the moment, we add this:

\begin{code}

irrefl : (Î± : Ordinal ð¤) (x : â¨ Î± â©) â Â¬(x âºâ¨ Î± â© x)
irrefl Î± x = irreflexive (underlying-order Î±) x (Well-foundedness Î± x)

\end{code}

Characterization of equality of ordinals using the structure identity
principle:

\begin{code}

open import UF-Equiv
open import UF-Univalence

Ordinal-â¡ : FunExt
          â is-univalent ð¤
          â (Î± Î² : Ordinal ð¤)
          â (Î± â¡ Î²)
          â (Î£ f ê (â¨ Î± â© â â¨ Î² â©) ,
                 is-equiv f
               Ã ((Î» x x' â x âºâ¨ Î± â© x') â¡ (Î» x x' â f x âºâ¨ Î² â© f x')))
Ordinal-â¡ {ð¤} fe = generalized-metric-space.characterization-of-M-â¡ (ð¤ Ì )
                    (Î» _ â is-well-order)
                    (Î» X _<_ â being-well-order-is-prop _<_ fe)
 where
  open import UF-SIP-Examples

\end{code}

Often it is convenient to work with the following alternative notion
of ordinal equivalence, which we take as the official one:

\begin{code}

is-order-preserving : (Î± : Ordinal ð¤) (Î² : Ordinal ð¥)
                    â (â¨ Î± â© â â¨ Î² â©) â ð¤ â ð¥ Ì
is-order-preserving Î± Î² f = (x y : â¨ Î± â©) â x âºâ¨ Î± â© y â f x âºâ¨ Î² â© f y

is-order-equiv : (Î± : Ordinal ð¤) (Î² : Ordinal ð¥) â (â¨ Î± â© â â¨ Î² â©) â ð¤ â ð¥ Ì
is-order-equiv Î± Î² f = is-order-preserving Î± Î² f
                     Ã (Î£ e ê is-equiv f , is-order-preserving Î² Î± (inverse f e))

is-order-reflecting : (Î± : Ordinal ð¤) (Î² : Ordinal ð¥)
                    â (â¨ Î± â© â â¨ Î² â©) â ð¤ â ð¥ Ì
is-order-reflecting Î± Î² f = (x y : â¨ Î± â©) â f x âºâ¨ Î² â© f y â x âºâ¨ Î± â© y

order-equiv-criterion : (Î± : Ordinal ð¤) (Î² : Ordinal ð¥) (f : â¨ Î± â© â â¨ Î² â©)
                      â is-equiv f
                      â is-order-preserving Î± Î² f
                      â is-order-reflecting Î± Î² f
                      â is-order-equiv Î± Î² f
order-equiv-criterion Î± Î² f e p r = p , e , q
 where
  g : â¨ Î² â© â â¨ Î± â©
  g = inverse f e

  q : is-order-preserving Î² Î± g
  q x y l = m
   where
    l' : f (g x) âºâ¨ Î² â© f (g y)
    l' = transportâ (Î» x y â x âºâ¨ Î² â© y)
           ((inverses-are-sections f e x)â»Â¹) ((inverses-are-sections f e y)â»Â¹) l

    s : f (g x) âºâ¨ Î² â© f (g y) â g x âºâ¨ Î± â© g y
    s = r (g x) (g y)

    m : g x âºâ¨ Î± â© g y
    m = s l'


order-equiv-criterion-converse : (Î± : Ordinal ð¤) (Î² : Ordinal ð¥) (f : â¨ Î± â© â â¨ Î² â©)
                               â is-order-equiv Î± Î² f
                               â is-order-reflecting Î± Î² f
order-equiv-criterion-converse Î± Î² f (p , e , q) x y l = r
 where
  g : â¨ Î² â© â â¨ Î± â©
  g = inverse f e

  s : g (f x) âºâ¨ Î± â© g (f y)
  s = q (f x) (f y) l

  r : x âºâ¨ Î± â© y
  r = transportâ (Î» x y â x âºâ¨ Î± â© y)
       (inverses-are-retractions f e x) (inverses-are-retractions f e y) s

_ââ_ : Ordinal ð¤ â Ordinal ð¥ â ð¤ â ð¥ Ì
Î± ââ Î² = Î£ f ê (â¨ Î± â© â â¨ Î² â©) , is-order-equiv Î± Î² f

\end{code}

See the module  for a proof that Î± ââ Î² is
canonically equivalent to Î± â¡ Î². (For historical reasons, that proof
doesn't use the structure identity principle.)

\begin{code}

ââ-refl : (Î± : Ordinal ð¤) â Î± ââ Î±
ââ-refl Î± = id , (Î» x y â id) , id-is-equiv â¨ Î± â© , (Î» x y â id)

ââ-sym : â {ð¤} {ð¥} (Î± : Ordinal ð¤) (Î² : Ordinal ð¥ )
       â Î± ââ Î² â Î² ââ Î±
ââ-sym Î± Î² (f , p , e , q) = inverse f e , q , inverses-are-equivs f e , p

ââ-trans : â {ð¤} {ð¥} {ð¦} (Î± : Ordinal ð¤) (Î² : Ordinal ð¥ ) (Î³ : Ordinal ð¦)
         â Î± ââ Î² â Î² ââ Î³ â Î± ââ Î³
ââ-trans Î± Î² Î³ (f , p , e , q) (f' , p' , e' , q') =
  f' â f ,
  (Î» x y l â p' (f x) (f y) (p x y l)) ,
  â-is-equiv e e' ,
  (Î» x y l â q (inverse f' e' x) (inverse f' e' y) (q' x y l))

\end{code}
