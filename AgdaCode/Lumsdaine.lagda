Martin Escardo, 17 May 2018,
while visiting the Hausdorff Research Institute for Mathematics in Bonn

This is an "improvement method" I learned from Peter Lumsdaine, 7th
July 2017 at the Newton Institute in Cambridge, adapted from an Agda
rendering by Andy Pitts of Peter's Coq code from 14th October 2015.

Given an identity system (Id, refl , J) with no given "computation
rule" for J, Peter produces another identity system (Id, refl , J' ,
J'-comp) with a "propositional computation rule" J'-comp for J'.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Universes

module Lumsdaine
        {ð¤}
        (Id : â {X : ð¤ Ì } â X â X â ð¤ Ì )
        (refl : â {X : ð¤ Ì } {x : X} â Id x x)
        (J : â {X : ð¤ Ì } (x : X) (A : (y : X) â Id x y â ð¤ Ì )
           â A x refl â (y : X) (p : Id x y) â A y p)
        where

private
  record Î£ {ð¤ ð¥ } {X : ð¤ Ì } (Y : X â ð¥ Ì ) : ð¤ â ð¥ Ì where
   constructor _,_
   field
    prâ : X
    prâ : Y prâ

  open Î£

  Sigma : {ð¤ ð¥ : Universe} (X : ð¤ Ì ) (Y : X â ð¥ Ì ) â ð¤ â ð¥ Ì
  Sigma X Y = Î£ Y

  syntax Sigma A (Î» x â b) = Î£ x ê A , b

  infixr -1 Sigma

  id : {X : ð¤ Ì }  â X â X
  id x = x

  lc-maps : (X Y : ð¤ Ì ) â ð¤ Ì
  lc-maps X Y = Î£ f ê (X â Y) , ({x x' : X} â Id (f x) (f x') â Id x x')

  id-lc-maps : {X : ð¤ Ì } â lc-maps X X
  id-lc-maps = (id , id)

module _ {X : ð¤ Ì }
         {x : X}
         (A : (y : X) â Id x y â ð¤ Ì )
 where
  private
    g : {t z : X} (p : Id x t) (q : Id x z) â lc-maps (A t p) (A z q)
    g {t} {z} p q = J x B (J x C id-lc-maps t p) z q
     where
      B : (y : X) â Id x y â ð¤ Ì
      B y q = lc-maps (A t p) (A y q)
      C : (y : X) â Id x y â ð¤ Ì
      C y p = lc-maps (A y p ) (A x refl)

    h : (b : A x refl) {y : X} (p : Id x y)
      â Î£ x ê A y p , Id (prâ (g p p) x) (prâ (g refl p) b)
    h b {y} p = J x B (b , refl) y p
     where
      B : (y : X) (p : Id x y) â ð¤ Ì
      B y p = Î£ x ê A y p , Id (prâ (g p p) x) (prâ (g refl p) b)

  J' : A x refl â (y : X) (p : Id x y) â A y p
  J' b y p = prâ (h b p)

  J'-comp : (b : A x refl) â Id (J' b x refl) b
  J'-comp b = prâ (g refl refl) (prâ (h b refl))

\end{code}
