Andrew Sneap

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _β_) -- TypeTopology

open import OrderNotation
open import UF-Base -- TypeTopology
open import UF-PropTrunc -- TypeTopology
open import UF-Subsingletons --TypeTopology
open import UF-FunExt -- TypeTopology
open import UF-Powerset -- TypeTopology

open import Rationals
open import RationalsOrder
open import RationalsMultiplication

module DedekindRealsMultiplication
         (pe : Prop-Ext) 
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
       where

open import DedekindReals pe pt fe
open PropositionalTruncation pt

open import RationalsMinMax fe

transportβ : {X : π€ Μ } {Y : π₯ Μ } {Z : π¦ Μ } {U : π€' Μ} β (A : X β Y β Z β U β π£ Μ )
             {x x' : X} {y y' : Y} {z z' : Z} {u u' : U}
           β x β‘ x' β y β‘ y' β z β‘ z' β u β‘ u' β A x y z u β A x' y' z' u'
transportβ A refl refl refl refl = id

_*β_ : β β β β β
x *β y  = (L , R) , {!!}
 where
  L : β-subset-of-propositions
  L p = (β (a , b , c , d) κ β Γ β Γ β Γ β , a < x Γ x < b Γ c < y Γ y < d Γ p < minβ (a * c) (a * d) (b * c) (b * d)) , β-is-prop
  R : β-subset-of-propositions
  R q = (β (a , b , c , d) κ β Γ β Γ β Γ β , a < x Γ x < b Γ c < y Γ y < d Γ maxβ (a * c) (a * d) (b * c) (b * d) < q) , β-is-prop


infixl 31 _*β_

β*-comm : (x y : β) β x *β y β‘ y *β x
β*-comm x y = β-equality-from-left-cut' (x *β y) (y *β x) left right
 where
  generalised : (x y : β) (p : β) β Ξ£ (a , b , c , d) κ β Γ β Γ β Γ β , a < x Γ x < b Γ c < y Γ y < d Γ p < minβ (a * c) (a * d) (b * c) (b * d)
                                  β Ξ£ (c , d , a , b) κ β Γ β Γ β Γ β , c < y Γ y < d Γ a < x Γ x < b Γ p < minβ (c * a) (c * b) (d * a) (d * b)
  generalised x y p ((a , b , c , d) , a<x , x<b , c<y , y<d , p<m) = (c , d , a , b) , c<y , y<d , a<x , x<b , I
   where
    I : p < minβ (c * a) (c * b) (d * a) (d * b)
    I = transport (p <_) III p<m
     where
      III : minβ (a * c) (a * d) (b * c) (b * d) β‘ minβ (c * a) (c * b) (d * a) (d * b) 
      III = minβ (a * c) (a * d) (b * c) (b * d)            β‘β¨ ap (minβ (a * c) (a * d) (b * c)) (β*-comm b d)                   β©
            minβ (a * c) (a * d) (b * c) (d * b)            β‘β¨ ap (Ξ» Ξ± β min Ξ± (d * b)) (min-assoc (a * c) (a * d) (b * c))      β©
            min (min (a * c) (min (a * d) (b * c))) (d * b) β‘β¨ ap (Ξ» Ξ± β min (min (a * c) Ξ±) (d * b)) (min-comm (a * d) (b * c)) β©
            min (min (a * c) (min (b * c) (a * d))) (d * b) β‘β¨ ap (Ξ» Ξ± β min Ξ± (d * b)) (min-assoc (a * c) (b * c) (a * d) β»ΒΉ)   β©
            minβ (a * c) (b * c) (a * d) (d * b)            β‘β¨ ap (Ξ» Ξ± β minβ Ξ± (b * c) (a * d) (d * b)) (β*-comm a c)           β©
            minβ (c * a) (b * c) (a * d) (d * b)            β‘β¨ ap (Ξ» Ξ± β minβ (c * a) Ξ± (a * d) (d * b)) (β*-comm b c)           β©
            minβ (c * a) (c * b) (a * d) (d * b)            β‘β¨ ap (Ξ» Ξ± β minβ (c * a) (c * b) Ξ± (d * b)) (β*-comm a d)           β©   
            minβ (c * a) (c * b) (d * a) (d * b)            β
            
  left : (p : β) β p < x *β y β p < y *β x
  left p = β₯β₯-functor (generalised x y p)
              
  right : (p : β) β p < y *β x β p < x *β y
  right p = β₯β₯-functor (generalised y x p)

β*-assoc : (x y z : β) β x *β y *β z β‘ x *β (y *β z)
β*-assoc x y z = β-equality-from-left-cut' (x *β y *β z) (x *β (y *β z)) left right
 where
  left : (p : β) β p < x *β y *β z β p < x *β (y *β z)
  left p = β₯β₯-functor I
   where
    I : {!!}
    I = {!!}
  right : {!!}
  right = {!!}
