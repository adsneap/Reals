Martin Escardo, 29th January 2019

If univalence holds, then any universe is embedded into any larger universe.

We do this without cumulativity, because it is not available in the
Martin-LoÌf type theory that we are working with in Agda.

Moreover, any map f : ð¤ Ì â ð¤ â ð¥ Ì with f X â X for all X : ð¤ Ì is an
embedding, e.g. the map X â¦ X + ð {ð¥}.

(Here the notion of a map being an embedding is stronger than that of
being left-cancellable, and it means that the fibers of the map are
propositions, or subsingletons, as in HoTT/UF.)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-UniverseEmbedding where

open import SpartanMLTT
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Embeddings
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-Lower-FunExt
open import UF-Equiv-FunExt
open import UF-Univalence
open import UF-UA-FunExt

is-universe-embedding : (ð¤ Ì â ð¥ Ì ) â (ð¤ âº) â ð¥ Ì
is-universe-embedding f = â X â f X â X

\end{code}

Of course:

\begin{code}

at-most-one-universe-embedding : Univalence
                               â (f g : ð¤ Ì â ð¥ Ì )
                               â is-universe-embedding f
                               â is-universe-embedding g
                               â f â¡ g
at-most-one-universe-embedding {ð¤} {ð¥} ua f g i j = p
 where
  h : â X â f X â g X
  h X = i X â â-sym (j X)

  H : f â¼ g
  H X = eqtoid (ua ð¥) (f X) (g X) (h X)

  p : f â¡ g
  p = dfunext (Univalence-gives-Fun-Ext ua) H

universe-embeddings-are-embeddings : Univalence
                                   â (ð¤ ð¥ : Universe) (f : ð¤ Ì â ð¥ Ì )
                                   â is-universe-embedding f
                                   â is-embedding f
universe-embeddings-are-embeddings ua ð¤ ð¥ f i = embedding-criterion' f Î³
 where
  Î³ : (X X' : ð¤ Ì ) â (f X â¡ f X') â (X â¡ X')
  Î³ X X' =  (f X â¡ f X')  ââ¨ a â©
            (f X â f X')  ââ¨ b â©
            (X â X')      ââ¨ c â©
            (X â¡ X')      â 
   where
    a = univalence-â (ua ð¥) (f X) (f X')
    b = â-cong (Univalence-gives-FunExt ua) (i X) (i X')
    c = â-sym (univalence-â (ua ð¤) X X')

\end{code}

For instance, the following function satisfies this condition and
hence is an embedding:

\begin{code}

Lift' : (ð¥ : Universe) â ð¤ Ì â ð¤ â ð¥ Ì
Lift' ð¥ X = X + ð {ð¥}

lift' : (ð¥ : Universe) {X : ð¤ Ì } â X â Lift' ð¥ X
lift' ð¥ = inl

lower' : {ð¥ : Universe} {X : ð¤ Ì } â Lift' ð¥ X â X
lower' (inl x) = x
lower' (inr x) = ð-elim x

Lift'-â : (ð¥ : Universe) (X : ð¤ Ì ) â Lift' ð¥ X â X
Lift'-â ð¥ X = ð-rneutral'

Lift'-is-embedding : Univalence â is-embedding (Lift' {ð¤} ð¥)
Lift'-is-embedding {ð¤} {ð¥} ua = universe-embeddings-are-embeddings ua ð¤ (ð¤ â ð¥)
                                  (Lift' ð¥) (Lift'-â ð¥)
\end{code}

The following embedding has better definitional properties:

\begin{code}

Lift : (ð¥ : Universe) â ð¤ Ì â ð¤ â ð¥ Ì
Lift ð¥ X = X Ã ð {ð¥}

lift : (ð¥ : Universe) {X : ð¤ Ì } â X â Lift ð¥ X
lift ð¥ x = (x , â)

lower : {X : ð¤ Ì } â Lift ð¥ X â X
lower (x , â) = x

Î·-Lift : (ð¥ : Universe) {X : ð¤ Ì } (ð : Lift ð¥ X)
       â lift ð¥ (lower ð) â¡ ð
Î·-Lift  ð¥ ð = refl

Îµ-Lift : (ð¥ : Universe) {X : ð¤ Ì } (x : X)
       â lower (lift ð¥ x) â¡ x
Îµ-Lift  ð¥ x = refl

lower-is-equiv : {X : ð¤ Ì } â is-equiv (lower {ð¤} {ð¥} {X})
lower-is-equiv {ð¤} {ð¥} = (lift ð¥ , Îµ-Lift ð¥) , (lift ð¥ , Î·-Lift ð¥)

lift-is-equiv : {X : ð¤ Ì } â is-equiv (lift ð¥ {X})
lift-is-equiv {ð¤} {ð¥} = (lower , Î·-Lift ð¥) , lower , Îµ-Lift ð¥

Lift-â : (ð¥ : Universe) (X : ð¤ Ì ) â Lift ð¥ X â X
Lift-â ð¥ X = lower , lower-is-equiv

â-Lift : (ð¥ : Universe) (X : ð¤ Ì ) â X â Lift ð¥ X
â-Lift ð¥ X = lift ð¥ , lift-is-equiv

Lift-is-universe-embedding : (ð¥ : Universe) â is-universe-embedding (Lift {ð¤} ð¥)
Lift-is-universe-embedding = Lift-â

Lift-is-embedding : Univalence â is-embedding (Lift {ð¤} ð¥)
Lift-is-embedding {ð¤} {ð¥} ua = universe-embeddings-are-embeddings ua ð¤ (ð¤ â ð¥)
                                 (Lift ð¥) (Lift-is-universe-embedding ð¥)
\end{code}

Added 7th Feb 2019. Assuming propositional and functional
extensionality instead of univalence, the lift-fibers of propositions
are propositions. (For use in the module UF-Resize.)

\begin{code}

prop-fiber-criterion : PropExt
                     â FunExt
                     â (ð¤ ð¥ : Universe)
                     â (f : ð¤ Ì â ð¥ Ì )
                     â is-universe-embedding f
                     â (Q : ð¥ Ì )
                     â is-prop Q
                     â is-prop (fiber f Q)
prop-fiber-criterion pe fe ð¤ ð¥ f i Q j (P , r) = d (P , r)
 where
  k : is-prop (f P)
  k = back-transport is-prop r j

  l : is-prop P
  l = equiv-to-prop (â-sym (i P)) k

  a : (X : ð¤ Ì ) â (f X â¡ f P) â (X â¡ P)
  a X = (f X â¡ f P)  ââ¨ prop-univalent-â (pe ð¥) (fe ð¥ ð¥) (f X) (f P) k â©
        (f X â f P)  ââ¨ â-cong fe (i X) (i P) â©
        (X â P)      ââ¨ â-sym (prop-univalent-â (pe ð¤) (fe ð¤ ð¤) X P l) â©
        (X â¡ P)      â 

  b : (Î£ X ê ð¤ Ì , f X â¡ f P) â (Î£ X ê ð¤ Ì  , X â¡ P)
  b = Î£-cong a

  c : is-prop (Î£ X ê ð¤ Ì , f X â¡ f P)
  c = equiv-to-prop b (singleton-types'-are-props P)

  d : is-prop (Î£ X ê ð¤ Ì , f X â¡ Q)
  d = transport (Î» - â is-prop (Î£ X ê ð¤ Ì , f X â¡ -)) r c

prop-fiber-Lift : PropExt
                â FunExt
                â (Q : ð¤ â ð¥ Ì )
                â is-prop Q
                â is-prop (fiber (Lift ð¥) Q)
prop-fiber-Lift {ð¤} {ð¥} pe fe = prop-fiber-criterion pe fe ð¤ (ð¤ â ð¥)
                                  (Lift {ð¤} ð¥) (Lift-is-universe-embedding ð¥)
\end{code}

Taken from the MGS'2019 lecture notes (22 December 2020):

\begin{code}

global-â-ap' : Univalence
             â (F : Universe â Universe)
             â (A : {ð¤ : Universe} â ð¤ Ì â (F ð¤) Ì )
             â ({ð¤ ð¥ : Universe} (X : ð¤ Ì ) â A X â A (Lift ð¥ X))
             â (X : ð¤ Ì ) (Y : ð¥ Ì ) â X â Y â A X â A Y
global-â-ap' {ð¤} {ð¥} ua F A Ï X Y e =

  A X          ââ¨ Ï X â©
  A (Lift ð¥ X) ââ¨ idtoeq (A (Lift ð¥ X)) (A (Lift ð¤ Y)) q â©
  A (Lift ð¤ Y) ââ¨ â-sym (Ï Y) â©
  A Y          â 
 where
  d : Lift ð¥ X â Lift ð¤ Y
  d = Lift ð¥ X ââ¨ Lift-is-universe-embedding ð¥ X â©
      X        ââ¨ e â©
      Y        ââ¨ â-sym (Lift-is-universe-embedding ð¤ Y) â©
      Lift ð¤ Y â 

  p : Lift ð¥ X â¡ Lift ð¤ Y
  p = eqtoid (ua (ð¤ â ð¥)) (Lift ð¥ X) (Lift ð¤ Y) d

  q : A (Lift ð¥ X) â¡ A (Lift ð¤ Y)
  q = ap A p

global-property-of-types : ð¤Ï
global-property-of-types = {ð¤ : Universe} â ð¤ Ì â ð¤ Ì

global-property-of-typesâº : ð¤Ï
global-property-of-typesâº = {ð¤ : Universe} â ð¤ Ì â ð¤ âº Ì

cumulative : global-property-of-types â ð¤Ï
cumulative A = {ð¤ ð¥ : Universe} (X : ð¤ Ì ) â A X â A (Lift ð¥ X)

cumulativeâº : global-property-of-typesâº â ð¤Ï
cumulativeâº A = {ð¤ ð¥ : Universe} (X : ð¤ Ì ) â A X â A (Lift ð¥ X)

global-â-ap : Univalence
            â (A : global-property-of-types)
            â cumulative A
            â (X : ð¤ Ì ) (Y : ð¥ Ì ) â X â Y â A X â A Y
global-â-ap ua = global-â-ap' ua id

global-â-apâº : Univalence
            â (A : global-property-of-typesâº)
            â cumulativeâº A
            â (X : ð¤ Ì ) (Y : ð¥ Ì ) â X â Y â A X â A Y
global-â-apâº ua = global-â-ap' ua (_âº)

\end{code}

Cumulativity in the above sense doesn't always hold. See the module
LawvereFPT for a counter-example.

Added 24th December 2020. Lifting of hSets.

\begin{code}

Lift-is-set : â {ð¤} ð¥ (X : ð¤ Ì ) â is-set X â is-set (Lift ð¥ X)
Lift-is-set ð¥ X X-is-set = equiv-to-set
                            (Lift-is-universe-embedding ð¥ X)
                            X-is-set

Lift-hSet : (ð¥ : Universe) â hSet ð¤ â hSet (ð¤ â ð¥)
Lift-hSet ð¥ = pair-fun (Lift ð¥) (Lift-is-set ð¥)

Lift-is-set-is-embedding : funext (ð¤ â ð¥) (ð¤ â ð¥)
                         â (X : ð¤ Ì ) â is-embedding (Lift-is-set ð¥ X)
Lift-is-set-is-embedding {ð¤} {ð¥} fe X = maps-of-props-are-embeddings
                                          (Lift-is-set ð¥ X)
                                          (being-set-is-prop (lower-funext ð¥ ð¥ fe))
                                          (being-set-is-prop fe)

Lift-hSet-is-embedding : Univalence
                       â is-embedding (Lift-hSet {ð¤} ð¥)
Lift-hSet-is-embedding {ð¤} {ð¥} ua = pair-fun-is-embedding
                                     (Lift ð¥)
                                     (Lift-is-set ð¥)
                                     (Lift-is-embedding ua)
                                     (Lift-is-set-is-embedding
                                       (Univalence-gives-FunExt ua (ð¤ â ð¥) (ð¤ â ð¥)))

is-hSet-embedding : (hSet ð¤ â hSet ð¥) â (ð¤ âº) â ð¥ Ì
is-hSet-embedding {ð¤} {ð¥} f = (ð§ : hSet ð¤) â underlying-set (f ð§)
                                             â underlying-set ð§

at-most-one-hSet-embedding : Univalence
                           â (f g : hSet ð¤ â hSet ð¥ )
                           â is-hSet-embedding f
                           â is-hSet-embedding g
                           â f â¡ g
at-most-one-hSet-embedding {ð¤} {ð¥} ua f g i j = p
 where
  h : â ð§ â underlying-set (f ð§) â underlying-set (g ð§)
  h ð§ = i ð§ â â-sym (j ð§)

  H : f â¼ g
  H ð§ = to-subtype-â¡
          (Î» ð¨ â being-set-is-prop (univalence-gives-funext (ua ð¥)))
          (eqtoid (ua ð¥) (underlying-set (f ð§)) (underlying-set (g ð§)) (h ð§))

  p : f â¡ g
  p = dfunext (Univalence-gives-FunExt ua (ð¤ âº) (ð¥ âº)) H

the-only-hSet-embedding-is-Lift-hSet : Univalence
                                     â (f : hSet ð¤ â hSet (ð¤ â ð¥ ))
                                     â is-hSet-embedding f
                                     â f â¡ Lift-hSet ð¥
the-only-hSet-embedding-is-Lift-hSet {ð¤} {ð¥} ua f i =
   at-most-one-hSet-embedding ua f
     (Lift-hSet ð¥) i
     (Î» ð§ â Lift-is-universe-embedding ð¥ (underlying-set ð§))

hSet-embeddings-are-embeddings : Univalence
                               â (f : hSet ð¤ â hSet (ð¤ â ð¥ ))
                               â is-hSet-embedding f
                               â is-embedding f
hSet-embeddings-are-embeddings {ð¤} {ð¥} ua f i =
    transport is-embedding
     ((the-only-hSet-embedding-is-Lift-hSet ua f i)â»Â¹)
     (Lift-hSet-is-embedding {ð¤} {ð¥} ua)

\end{code}
