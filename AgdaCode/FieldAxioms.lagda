Andrew Sneap - 27th April 2021

I link to this module within the Dedekind Reals and Discussion sections of my report.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


open import SpartanMLTT renaming (_+_ to _ā_) -- TypeTopology

open import UF-Subsingletons

module FieldAxioms where

distributive : {X : š¤ Ģ } ā (X ā X ā X) ā (X ā X ā X) ā š¤ Ģ
distributive _ā_ _ā_ = ā x y z ā x ā (y ā z) ā” ((x ā y) ā (x ā z))

field-structure : š¤ Ģ ā {š„ : Universe}  ā š¤ ā (š„ āŗ) Ģ
field-structure F {š„} = (F ā F ā F) Ć (F ā F ā F) Ć (F ā F ā š„ Ģ)

\end{code}

In the following axioms, eā is the additive identity element (usually
0), eā is the multiplicative identity element (usually 1). We cannot
simply say that eā ā¢ eā, since this is not constructive for the
Dedekind Reals, so we use an apartness relation.  For the rationals,
the apartness relation is defined as x ā¢ y, but for the reals it is
defined as (x < y) ā (y < x)

\begin{code}

field-axioms : (F : š¤ Ģ) ā { š„ : Universe } ā field-structure F { š„ } ā š¤ ā š„ Ģ
field-axioms F { š„ } (_ā_ , _ā_ , _#_) = is-set F Ć associative _ā_
                                                   Ć associative _ā_
                                                   Ć commutative _ā_
                                                   Ć commutative _ā_
                                                   Ć distributive _ā_ _ā_
                                                   Ć (Ī£ (eā , eā) ź F Ć F , ((eā # eā) Ć left-neutral eā _ā_
                                                                                       Ć ((x : F) ā Ī£ x' ź F , x ā x' ā” eā) 
                                                                                       Ć left-neutral eā _ā_
                                                                                       Ć ((x : F) ā (x # eā) ā Ī£ x' ź F , x ā x' ā” eā)))

Field-structure : š¤ Ģ ā { š„ : Universe } ā š¤ ā (š„ āŗ) Ģ
Field-structure F  { š„ } = Ī£ fs ź field-structure F { š„ } , field-axioms F fs

ordered-field-structure : {š¤ š„ š¦ : Universe} ā (F : š¤ Ģ) ā (fs : field-structure F { š„ }) ā (fa : field-axioms F fs) ā (š¤ ā (š¦ āŗ)) Ģ
ordered-field-structure {š¤} {š„} {š¦} F fs fa = (F ā F ā š¦ Ģ)

ordered-field-axioms : {š¤ š„ š¦ : Universe} ā (F : š¤ Ģ) ā (fs : field-structure F) ā (fa : field-axioms F fs) ā  ordered-field-structure { š¤ } { š„ } { š¦ } F fs fa ā (š¤ ā š¦) Ģ
ordered-field-axioms {š¤} {š„} {š¦} F (_ā_ , _ā_ , _#_) (s , a , a' , c , c' , d , (e , e') , i) _<_ = ((x y z : F) ā x < y ā (x ā z) < (y ā z))
                                                                                                     Ć ((x y : F) ā e < x ā e < y ā e < (x ā y))                                                                               
Ordered-field-structure : {š¤ š„ š¦ : Universe} ā (F : š¤ Ģ) ā Field-structure F { š„ } ā š¤ ā (š¦ āŗ) Ģ
Ordered-field-structure {š¤} {š„} {š¦} F (fs , fa) = Ī£ ofa ź (ordered-field-structure {š¤} {š„} {š¦} F fs fa) , ordered-field-axioms {š¤} {š„} F fs fa ofa

Field : (š¤ : Universe) ā { š„  : Universe} ā (š¤ āŗ) ā (š„ āŗ) Ģ
Field š¤ { š„ } = Ī£ X ź š¤ Ģ , Field-structure X { š„ }

ordered-field-structure' : (š¤ : Universe) ā {š„ š¦ : Universe} ā (F : Field š¤ { š„ }) ā š¤ ā (š¦ āŗ) Ģ 
ordered-field-structure' _ { š„ } { š¦ } (F , _) = F ā F ā š¦ Ģ

ordered-field-axioms' : (š¤ : Universe) ā {š„ š¦ : Universe} ā (F : Field š¤ { š„ }) ā ordered-field-structure' š¤ { š„ } { š¦ } F ā š¤ ā š¦ Ģ
ordered-field-axioms' š¤ {š„} {š¦} (F , (_ā_ , _ā_ , _) , (s , a , a' , c , c' , d , (e , e') , i)) _<_
 = ((x y z : F) ā x < y ā (x ā z) < (y ā z)) Ć ((x y : F) ā e < x ā e < y ā e < (x ā y))

Ordered-field-structure' : (š¤ : Universe) ā { š„ š¦ : Universe } ā (F : Field š¤ { š„ }) ā š¤ ā (š¦ āŗ) Ģ
Ordered-field-structure' š¤ {š„} {š¦} F = Ī£ ofs ź ordered-field-structure' š¤ { š„ } { š¦ } F , ordered-field-axioms' š¤ F ofs

Ordered-Field : (š¤ : Universe) ā { š„ š¦ : Universe } ā (š¤ āŗ) ā (š„ āŗ) ā (š¦ āŗ) Ģ 
Ordered-Field š¤ {š„} {š¦} = Ī£ X ź Field š¤ { š„ } , Ordered-field-structure' š¤ { š„ } { š¦ } X

āØ_ā© : Ordered-Field š¤ { š„ } { š¦ } ā š¤ Ģ
āØ (F , fs) , ofs ā© = F

addition : {š„ š¦ : Universe} ā (F : Ordered-Field š¤ { š„ } { š¦ }) ā āØ F ā© ā āØ F ā© ā āØ F ā©
addition ((F , (_+_ , _*_ , _āÆ_) , F-is-set , +-assoc , *-assoc , +-comm , *-comm , dist , (eā , eā) , eāāÆeā , zero-left-neutral , +-inverse , *-left-neutral , *-inverse) , _<_ , <-respects-additions , <-respects-multiplication) = _+_

addition-commutative : {š„ š¦ : Universe} ā (F : Ordered-Field š¤ { š„ } { š¦ }) ā _
addition-commutative ((F , (_+_ , _*_ , _āÆ_) , F-is-set , +-assoc , *-assoc , +-comm , *-comm , dist , (eā , eā) , eāāÆeā , zero-left-neutral , +-inverse , *-left-neutral , *-inverse) , _<_ , <-respects-additions , <-respects-multiplication) = +-comm

multiplication-commutative : {š„ š¦ : Universe} ā (F : Ordered-Field š¤ { š„ } { š¦ }) ā _
multiplication-commutative ((F , (_+_ , _*_ , _āÆ_) , F-is-set , +-assoc , *-assoc , +-comm , *-comm , dist , (eā , eā) , eāāÆeā , zero-left-neutral , +-inverse , *-left-neutral , *-inverse) , _<_ , <-respects-additions , <-respects-multiplication) = *-comm

multiplication : {š„ š¦ : Universe} ā (F : Ordered-Field š¤ { š„ } { š¦ }) ā āØ F ā© ā āØ F ā© ā āØ F ā©
multiplication ((F , (_+_ , _*_ , _āÆ_) , F-is-set , +-assoc , *-assoc , +-comm , *-comm , dist , (eā , eā) , eāāÆeā , zero-left-neutral , +-inverse , *-left-neutral , *-inverse) , _<_ , <-respects-additions , <-respects-multiplication) = _*_

apartness : {š„ š¦ : Universe} ā (F : Ordered-Field š¤ { š„ } { š¦ }) ā āØ F ā© ā āØ F ā© ā š„ Ģ
apartness ((F , (_+_ , _*_ , _āÆ_) , F-is-set , +-assoc , *-assoc , +-comm , *-comm , dist , (eā , eā) , eāāÆeā , zero-left-neutral , +-inverse , *-left-neutral , *-inverse) , _<_ , <-respects-additions , <-respects-multiplication) = _āÆ_

additive-identity : {š„ š¦ : Universe} ā (F : Ordered-Field š¤ { š„ } { š¦ }) ā āØ F ā©
additive-identity ((F , (_+_ , _*_ , _āÆ_) , F-is-set , +-assoc , *-assoc , +-comm , *-comm , dist , (eā , eā) , eāāÆeā , zero-left-neutral , +-inverse , *-left-neutral , *-inverse) , _<_ , <-respects-additions , <-respects-multiplication)  = eā

multiplicative-identity : {š„ š¦ : Universe} ā (F : Ordered-Field š¤ { š„ } { š¦ }) ā āØ F ā©
multiplicative-identity ((F , (_+_ , _*_ , _āÆ_) , F-is-set , +-assoc , *-assoc , +-comm , *-comm , dist , (eā , eā) , eāāÆeā , zero-left-neutral , +-inverse , *-left-neutral , *-inverse) , _<_ , <-respects-additions , <-respects-multiplication) =  eā

underlying-type-is-set : {š„ š¦ : Universe} ā (F : Ordered-Field š¤ { š„ } { š¦ }) ā is-set āØ F ā©
underlying-type-is-set {š„} ((a , (prā , prā) , F-is-set , c) , d) = F-is-set

zero-left-neutral : {š„ š¦ : Universe} ā (F : Ordered-Field š¤ { š„ } { š¦ }) ā _
zero-left-neutral ((F , (_+_ , _*_ , _āÆ_) , F-is-set , +-assoc , *-assoc , +-comm , *-comm , dist , (eā , eā) , eāāÆeā , zln , +-inverse , *-left-neutral , *-inverse) , _<_ , <-respects-additions , <-respects-multiplication) = zln

addition-associative : {š„ š¦ : Universe} ā (F : Ordered-Field š¤ { š„ } { š¦ }) ā _
addition-associative ((F , (_+_ , _*_ , _āÆ_) , F-is-set , +-assoc , *-assoc , +-comm , *-comm , dist , (eā , eā) , eāāÆeā , zln , +-inverse , *-left-neutral , *-inverse) , _<_ , <-respects-additions , <-respects-multiplication) = +-assoc

{-
open import Rationals

ArchimedeanOrderedField : (š¤ : Universe) ā {š„ š¦ : Universe} ā (š¤ āŗ) ā (š„ āŗ) ā (š¦ āŗ) Ģ
ArchimedeanOrderedField š¤ {š„} {š¦} = Ī£ (F , (_<_ , ofa)) ź Ordered-Field š¤ {š„ } { š¦ } , ((embedding : (ā ā āØ (F , (_<_ , ofa)) ā©)) ā (ā x y ā ā z ź ā , (x < embedding z) Ć (embedding z < y)))
-}

\end{code}
