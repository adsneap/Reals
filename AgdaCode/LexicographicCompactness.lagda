Martin Escardo, 20-21 December 2012.

This module is mainly for use in the module CompactOrdinals.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module LexicographicCompactness where

open import SpartanMLTT
open import LexicographicOrder
open import InfCompact

Î£-inf-compact : â {ð£} {X : ð¤ Ì } {Y : X â ð¥ Ì }
              â (_â¤_ : X â X â ð¦ Ì )
              â (_â¼_ : {x : X} â Y x â Y x â ð£ Ì )
              â inf-compact _â¤_
              â ((x : X) â inf-compact (_â¼_ {x}))
              â inf-compact (lex-order _â¤_ _â¼_)
Î£-inf-compact {ð¤} {ð¥} {ð¦} {ð£} {X} {Y} _â¤_ _â¼_ Îµ Î´ p =
 (xâ , yâ) , (putative-root-lemma , (lower-bound-lemma , uborlb-lemma))
 where
  lemma-next : (x : X) â Î£ yâ ê Y x , ((Î£ y ê Y x , p (x , y) â¡ â) â p (x , yâ) â¡ â)
                                        Ã ((y : Y x) â p (x , y) â¡ â â yâ â¼ y)
                                        Ã ((l : Y x) â ((y : Y x) â p (x , y) â¡ â â l â¼ y) â l â¼ yâ)
  lemma-next x = Î´ x (Î» y â p (x , y))

  next : (x : X) â Y x
  next x = prâ (lemma-next x)

  next-correctness : (x : X) â ((Î£ y ê Y x , p (x , y) â¡ â) â p (x , next x) â¡ â)
                              Ã ((y : Y x) â p (x , y) â¡ â â next x â¼ y)
                              Ã ((l : Y x) â ((y : Y x) â p (x , y) â¡ â â l â¼ y) â l â¼ next x)
  next-correctness x = prâ (lemma-next x)

  lemma-first : Î£ xâ ê X , ((Î£ x ê X , p (x , next x) â¡ â) â p (xâ , next xâ) â¡ â)
                            Ã ((x : X) â p (x , next x) â¡ â â xâ â¤ x)
                            Ã ((m : X) â ((x : X) â p (x , next x) â¡ â â m â¤ x) â m â¤ xâ)
  lemma-first = Îµ (Î» x â p (x , next x))

  xâ : X
  xâ = prâ lemma-first

  first-correctness : ((Î£ x ê X , p (x , next x) â¡ â) â p (xâ , next xâ) â¡ â)
                     Ã ((x : X) â p (x , next x) â¡ â â xâ â¤ x)
                     Ã ((m : X) â ((x : X) â p (x , next x) â¡ â â m â¤ x) â m â¤ xâ)
  first-correctness = prâ lemma-first

  yâ : Y xâ
  yâ = next xâ

  putative-root-lemma : (Î£ t ê (Î£ x ê X , Y x) , p t â¡ â) â p (xâ , yâ) â¡ â
  putative-root-lemma ((x , y) , r) = prâ first-correctness (x , prâ (next-correctness x) (y , r))

  _â_ : Î£ Y â Î£ Y â ð¤ â ð¦ â ð£ Ì
  _â_ = lex-order _â¤_ _â¼_

  Ï : {x x' : X} â x â¡ x' â Y x â Y x'
  Ï = transport Y

  lower-bound-lemma : (t : (Î£ x ê X , Y x)) â p t â¡ â â (xâ , yâ) â t
  lower-bound-lemma (x , y) r = â¤-lemma , â¼-lemma
   where
    f : p (x , next x) â¡ â â xâ â¤ x
    f = prâ (prâ first-correctness) x

    â¤-lemma : xâ â¤ x
    â¤-lemma = f (prâ (next-correctness x) (y , r))

    g : next x â¼ y
    g = prâ (prâ (next-correctness x)) y r

    j : {xâ x : X} (r : xâ â¡ x) {y : Y x} â next x â¼ y â Ï r (next xâ) â¼ y
    j refl = id

    â¼-lemma : (r : xâ â¡ x) â Ï r yâ â¼ y
    â¼-lemma r = j r g


  uborlb-lemma : (n : Î£ x ê X , Y x) â ((t : (Î£ x ê X , Y x)) â p t â¡ â â n â t) â n â (xâ , yâ)
  uborlb-lemma (x , y) lower-bounder = â¤-lemma , â¼-lemma
   where
    f : ((x' : X) â p (x' , next x') â¡ â â x â¤ x') â x â¤ xâ
    f = prâ (prâ first-correctness) x

    â¤-lower-bounder : (x' : X) (y' : Y x') â p (x' , y') â¡ â â x â¤ x'
    â¤-lower-bounder x' y' r' = prâ (lower-bounder ((x' , y')) r')

    â¤-lemma : x â¤ xâ
    â¤-lemma = f (Î» x' â â¤-lower-bounder x' (next x'))

    g :  ((y' : Y x) â p (x , y') â¡ â â y â¼ y') â y â¼ next x
    g = prâ (prâ (next-correctness x)) y

    â¼-lower-bounder : (x' : X) (y' : Y x') â p (x' , y') â¡ â â (r : x â¡ x') â Ï r y â¼ y'
    â¼-lower-bounder x' y' r' = prâ (lower-bounder ((x' , y')) r')

    j : {xâ x : X} â (r : x â¡ xâ) â {y : Y x} â y â¼ next x â Ï r y â¼ next xâ
    j refl = id

    â¼-lemma : (r : x â¡ xâ) â Ï r y â¼ yâ
    â¼-lemma r = j r (g (Î» y' r â â¼-lower-bounder x y' r refl))

\end{code}
