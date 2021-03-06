Andrew Sneap


\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _ā_)  -- TypeTopology

open import NaturalsAddition renaming (_+_ to _ā+_) -- TypeTopology
open import NaturalsOrder --TypeTopology
open import OrderNotation -- TypeTopology
open import UF-FunExt -- TypeTopology
open import UF-PropTrunc --TypeTopology
open import UF-Subsingletons --TypeTopology

open import Rationals
open import RationalsAddition
open import RationalsOrder

module MetricSpaceAltDef
  (pt : propositional-truncations-exist)
  (fe : Fun-Ext)
  (pe : Prop-Ext)
 where 

open PropositionalTruncation pt
open import DedekindReals pe pt fe
open import DedekindRealsOrder pe pt fe

m1a : {š¤ : Universe} ā (X : š¤ Ģ) ā (B : X ā X ā (Īµ : ā) ā 0ā < Īµ ā š¤ā Ģ) ā š¤ Ģ
m1a X B = (x y : X) ā ((Īµ : ā) ā (l : 0ā < Īµ) ā B x y Īµ l) ā x ā” y

m1b : {š¤ : Universe} ā (X : š¤ Ģ) ā (B : X ā X ā (Īµ : ā) ā 0ā < Īµ ā š¤ā Ģ) ā š¤ Ģ
m1b X B = (x : X) ā ((Īµ : ā) ā (l : 0ā < Īµ) ā B x x Īµ l)

m2 : {š¤ : Universe} ā (X : š¤ Ģ) ā (B : X ā X ā (Īµ : ā) ā 0ā < Īµ ā š¤ā Ģ) ā š¤ Ģ
m2 X B = (x y : X) ā (Īµ : ā) ā (l : 0ā < Īµ) ā B x y Īµ l ā B y x Īµ l

m3 : {š¤ : Universe} ā (X : š¤ Ģ) ā (B : X ā X ā (Īµ : ā) ā 0ā < Īµ ā š¤ā Ģ) ā š¤ Ģ
m3 X B = (x y : X) ā (Īµā Īµā : ā) ā (lā : 0ā < Īµā) ā (lā : 0ā < Īµā) ā Īµā < Īµā ā B x y Īµā lā ā B x y Īµā lā

m4 : {š¤ : Universe} ā (X : š¤ Ģ) ā (B : X ā X ā (Īµ : ā) ā 0ā < Īµ ā š¤ā Ģ) ā š¤ Ģ
m4 X B = (x y z : X) ā (Īµā Īµā : ā) ā (lā : (0ā < Īµā)) ā (lā : (0ā < Īµā)) ā B x y Īµā lā ā B y z Īµā lā ā B x z (Īµā + Īµā) (ā<-adding-zero Īµā Īµā lā lā)

metric-space : {š¤ : Universe} ā (X : š¤ Ģ) ā š¤ā ā š¤ Ģ
metric-space X =
 Ī£ B ź (X ā X ā (Īµ : ā) ā 0ā < Īµ ā š¤ā Ģ) , m1a X B Ć m1b X B Ć m2 X B Ć m3 X B Ć m4 X B

\end{code}

A space is a complete metric space if every cauchy sequence in a metric space is also a convergent sequence.

Convergent and Cauchy Sequences are also defined below. In a metric space, all convergent sequences are cauchy sequences.

A definition is also given for what it means for a function to be continous, and what it means for a subspace of a space to be dense.

It is also useful to define the type of positive rationals.

\begin{code}

āā : š¤ā Ģ
āā = Ī£ Īµ ź ā , 0ā < Īµ

bounded-sequence : {š¤ : Universe} ā (X : š¤ Ģ) ā metric-space X ā (S : ā ā X) ā š¤ā Ģ
bounded-sequence X (B , _) S = ā K ź ā , ((x y : ā) ā (l : (0ā < K)) ā B (S x) (S y) K l)

bounded-sequence-is-prop : {š¤ : Universe} ā (X : š¤ Ģ) ā (m : metric-space X) ā (S : ā ā X) ā is-prop (bounded-sequence X m S)
bounded-sequence-is-prop X m S = ā-is-prop

convergent-sequence : {š¤ : Universe} ā (X : š¤ Ģ) ā metric-space X ā (S : ā ā X) ā š¤ Ģ
convergent-sequence X (B , _) S = ā x ź X , (((Īµ , l) : āā) ā Ī£ N ź ā , ((n : ā) ā N < n ā B x (S n) Īµ l))

cauchy-sequence : {š¤ : Universe} ā (X : š¤ Ģ) ā metric-space X ā (S : ā ā X) ā š¤ā Ģ
cauchy-sequence X (B , _) S = ((Īµ , l) : āā) ā Ī£ N ź ā , ((m n : ā) ā N ā¤ m ā N ā¤ n ā B (S m) (S n) Īµ l)

convergentācauchy : {š¤ : Universe} ā (X : š¤ Ģ) ā (m : metric-space X) ā (S : ā ā X) ā š¤ Ģ
convergentācauchy X m S = convergent-sequence X m S ā cauchy-sequence X m S

cauchyāconvergent : {š¤ : Universe} ā (X : š¤ Ģ) ā metric-space X ā (S : ā ā X) ā š¤ Ģ
cauchyāconvergent X m S = cauchy-sequence X m S ā convergent-sequence X m S

complete-metric-space : {š¤ : Universe} ā (X : š¤ Ģ) ā š¤ā ā š¤ Ģ
complete-metric-space X = Ī£ m ź (metric-space X) , ((S : ā ā X) ā cauchyāconvergent X m S)


\end{code}
