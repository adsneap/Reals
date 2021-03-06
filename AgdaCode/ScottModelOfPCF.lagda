Tom de Jong, 31 May 2019

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc
open import UF-FunExt
open import UF-Subsingletons

module ScottModelOfPCF
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext π€β)
       where

open PropositionalTruncation pt

open import NaturalNumbers-Properties
open import UF-Miscelanea

open import PCF pt

open import Dcpo pt fe π€β
open import DcpoExponential pt fe π€β
open import DcpoMiscelanea pt fe π€β

open import DcpoPCFCombinators pt fe π€β
open IfZeroDenotationalSemantics pe

open import DcpoLeastFixedPoint pt fe

open import DcpoLifting pt fe π€β pe

open import Lifting π€β
open import LiftingMonad π€β hiding (ΞΌ)

β¦_β§ : type β DCPOβ₯ {π€β} {π€β}
β¦ ΞΉ β§     = π-DCPOβ₯ β-is-set
β¦ Ο β Ο β§ = β¦ Ο β§ βΉα΅αΆα΅α΅β₯ β¦ Ο β§

β¦_β§β : {Ο : type} (t : PCF Ο) β βͺ β¦ Ο β§ β«
β¦ Zero β§β            = Ξ· zero
β¦ Succ β§β            = πΜ succ , πΜ-continuous β-is-set β-is-set succ
β¦ Pred β§β            = πΜ pred , πΜ-continuous β-is-set β-is-set pred
β¦ ifZero β§β          = β¦ifZeroβ¦
β¦ Fix {Ο} β§β         = ΞΌ β¦ Ο β§
β¦ K {Ο} {Ο} β§β       = Kα΅αΆα΅α΅β₯ β¦ Ο β§ β¦ Ο β§
β¦ S {Ο} {Ο} {Ο} β§β   = Sα΅αΆα΅α΅β₯ β¦ Ο β§ β¦ Ο β§ β¦ Ο β§
β¦ _Β·_ {Ο} {Ο} s t β§β = [ β¦ Ο β§ β» ,  β¦ Ο β§ β» ]β¨ β¦ s β§β β© β¦ t β§β

\end{code}
