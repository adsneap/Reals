Andrew Sneap

\begin{code}
{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT renaming (_+_ to _β_)  -- TypeTopology
open import CanonicalMapNotation --TypeTopology
open import OrderNotation --TypeTopology
open import UF-FunExt -- TypeTopology
open import UF-PropTrunc -- TypeTopology
open import UF-Subsingletons --TypeTopology

module MetricSpaces
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
         (pe : Prop-Ext)
       where 

open import DedekindReals pe pt fe
open import DedekindRealsOrder pe pt fe
open PropositionalTruncation pt

M1 : {π€ : Universe} β (X : π€ Μ) β (d : X β X β β) β π€β β π€ Μ
M1 X d = (x y : X) β d x y β‘ 0β β x β‘ y

M2 : {π€ : Universe} β (X : π€ Μ) β (d : X β X β β) β π€β β π€ Μ
M2 X d = (x y : X) β d x y β‘ d y x

open import DedekindRealsAddition pe pt fe
open import DedekindRealsOrder pe pt fe

M3 : {π€ : Universe} β (X : π€ Μ) β (d : X β X β β) β π€ Μ
M3 X d = (x y z : X) β (d x y) + (d y z) β€ d x z

MetricSpace : {π€ : Universe} β (X : π€ Μ) β π€β β π€ Μ
MetricSpace X = Ξ£ d κ (X β X β β) , M1 X d Γ M2 X d Γ M3 X d

open import MetricSpaceAltDef pt fe pe
open import Rationals
open import RationalsOrder
{-
metric-spaceβMetricSpace : {π€ : Universe}
                         β (X : π€ Μ)
--                         β (B : X β X β (Ξ΅ : β) β 0β < Ξ΅ β π€β Μ)
--                         β (d : (X β X β β))
--                         β ((x y : X) β ((Ξ΅ , l) : ββ) β d x y β€ ΞΉ Ξ΅ β B x y Ξ΅ l)
                         β metric-space X
                         β MetricSpace X
metric-spaceβMetricSpace X (B , m1' , m2' , m3' , m4') = d , {!!}
 where
  d : X β X β β
  d x y = {!!}
-}

