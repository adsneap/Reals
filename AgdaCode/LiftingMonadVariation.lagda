Martin Escardo 7th November 2018.

Remark. Another equivalent way to define the multiplication, which has
a different universe level:

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module LiftingMonadVariation where

open import UF-Subsingletons
open import UF-Embeddings
open import UF-Equiv
open import UF-FunExt

open import Lifting
open import LiftingEmbeddingDirectly

ð* : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y) â is-embedding f â ð ð£ Y â ð (ð¤ â ð¥ â ð£) X
ð* f e (Q , Ï , j) = (Î£ q ê Q , fiber f (Ï q)) ,
                      (Î» p â prâ (prâ p)) ,
                      Î£-is-prop j (e â Ï)

Î¼* : (ð£ ð£' : Universe) {X : ð¤ Ì }
   â funext ð£ ð£
   â funext ð£' ð£'
   â funext ð£' ð¤
   â funext ð¤ (ð¤ â (ð£' âº))
   â propext ð£'
   â ð ð£ (ð ð£' X) â ð (ð¤ â ð£ â (ð£' âº)) X
Î¼* {ð¤} ð£ ð£' {X} fe fe' fe'' fe''' pe = ð* (Î· ð£') (Î·-is-embedding ð£' pe fe' fe'' fe''')

\end{code}
