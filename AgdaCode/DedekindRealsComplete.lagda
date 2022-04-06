Andrew Sneap

\begin{code}

open import SpartanMLTT renaming (_+_ to _∔_)

open import UF-Subsingletons
open import UF-FunExt
open import UF-PropTrunc

open import FieldAxioms

module DedekindRealsComplete
  (fe : Fun-Ext)
  (pe : Prop-Ext)
  (pt : propositional-truncations-exist)
 where

open import DedekindReals pe pt fe

record DedekindRealsOrderedField : {!!} where
 field
  ℝ-Field-structure : Field-structure ℝ { {!!} } 
  ℝ-ordered-field : Ordered-field-structure' {!!} {!ℝ-Field-structure!}
  ℝ-Ordered-Field : {!!}



\end{code}
