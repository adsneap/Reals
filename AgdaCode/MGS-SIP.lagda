This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module MGS-SIP where

open import MGS-More-FunExt-Consequences public
open import MGS-Yoneda                   public
open import MGS-Powerset                 public
open import MGS-Classifiers              public
open import MGS-Subsingleton-Truncation  public

module sip where

 β¨_β© : {S : π€ Μ β π₯ Μ } β Ξ£ S β π€ Μ
 β¨ X , s β© = X

 structure : {S : π€ Μ β π₯ Μ } (A : Ξ£ S) β S β¨ A β©
 structure (X , s) = s

 canonical-map : {S : π€ Μ β π₯ Μ }
                 (ΞΉ : (A B : Ξ£ S) β β¨ A β© β β¨ B β© β π¦ Μ )
                 (Ο : (A : Ξ£ S) β ΞΉ A A (id-β β¨ A β©))
                 {X : π€ Μ }
                 (s t : S X)

               β s β‘ t β ΞΉ (X , s) (X , t) (id-β X)

 canonical-map ΞΉ Ο {X} s s (refl s) = Ο (X , s)

 SNS : (π€ Μ β π₯ Μ ) β (π¦ : Universe) β π€ βΊ β π₯ β (π¦ βΊ) Μ

 SNS {π€} {π₯} S π¦ = Ξ£ ΞΉ κ ((A B : Ξ£ S) β (β¨ A β© β β¨ B β© β π¦ Μ ))
                  , Ξ£ Ο κ ((A : Ξ£ S) β ΞΉ A A (id-β β¨ A β©))
                  , ({X : π€ Μ } (s t : S X) β is-equiv (canonical-map ΞΉ Ο s t))

 homomorphic : {S : π€ Μ β π₯ Μ } β SNS S π¦
             β (A B : Ξ£ S) β β¨ A β© β β¨ B β© β π¦ Μ

 homomorphic (ΞΉ , Ο , ΞΈ) = ΞΉ

 _β[_]_ : {S : π€ Μ β π₯ Μ } β Ξ£ S β SNS S π¦ β Ξ£ S β π€ β π¦ Μ

 A β[ Ο ] B = Ξ£ f κ (β¨ A β© β β¨ B β©)
            , Ξ£ i κ is-equiv f
            , homomorphic Ο A B (f , i)

 IdβhomEq : {S : π€ Μ β π₯ Μ } (Ο : SNS S π¦)
          β (A B : Ξ£ S) β (A β‘ B) β (A β[ Ο ] B)

 IdβhomEq (_ , Ο , _) A A (refl A) = id , id-is-equiv β¨ A β© , Ο A

 homomorphism-lemma : {S : π€ Μ β π₯ Μ } (Ο : SNS S π¦)
                      (A B : Ξ£ S) (p : β¨ A β© β‘ β¨ B β©)
                    β
                      (transport S p (structure A) β‘ structure B)
                    β  homomorphic Ο A B (IdβEq β¨ A β© β¨ B β© p)

 homomorphism-lemma (ΞΉ , Ο , ΞΈ) (X , s) (X , t) (refl X) = Ξ³
  where
   Ξ³ : (s β‘ t) β ΞΉ (X , s) (X , t) (id-β X)
   Ξ³ = (canonical-map ΞΉ Ο s t , ΞΈ s t)

 characterization-of-β‘ : is-univalent π€
                       β {S : π€ Μ β π₯ Μ } (Ο : SNS S π¦)
                       β (A B : Ξ£ S)

                       β (A β‘ B) β (A β[ Ο ] B)

 characterization-of-β‘ ua {S} Ο A B =

    (A β‘ B)                                                           ββ¨ i β©
    (Ξ£ p κ β¨ A β© β‘ β¨ B β© , transport S p (structure A) β‘ structure B) ββ¨ ii β©
    (Ξ£ p κ β¨ A β© β‘ β¨ B β© , ΞΉ A B (IdβEq β¨ A β© β¨ B β© p))               ββ¨ iii β©
    (Ξ£ e κ β¨ A β© β β¨ B β© , ΞΉ A B e)                                   ββ¨ iv β©
    (A β[ Ο ] B)                                                      β 

  where
   ΞΉ   = homomorphic Ο

   i   = Ξ£-β‘-β A B
   ii  = Ξ£-cong (homomorphism-lemma Ο A B)
   iii = β-sym (Ξ£-change-of-variable (ΞΉ A B) (IdβEq β¨ A β© β¨ B β©) (ua β¨ A β© β¨ B β©))
   iv  = Ξ£-assoc

 IdβhomEq-is-equiv : (ua : is-univalent π€) {S : π€ Μ β π₯ Μ } (Ο : SNS S π¦)
                   β (A B : Ξ£ S) β is-equiv (IdβhomEq Ο A B)

 IdβhomEq-is-equiv ua {S} Ο A B = Ξ³
  where
   h : (A B : Ξ£ S) β IdβhomEq Ο A B βΌ β characterization-of-β‘ ua Ο A B β
   h A A (refl A) = refl _

   Ξ³ : is-equiv (IdβhomEq Ο A B)
   Ξ³ = equivs-closed-under-βΌ
       (ββ-is-equiv (characterization-of-β‘ ua Ο A B))
       (h A B)

 module _ {S : π€ Μ β π₯ Μ }
          (ΞΉ : (A B : Ξ£ S) β β¨ A β© β β¨ B β© β π¦ Μ )
          (Ο : (A : Ξ£ S) β ΞΉ A A (id-β β¨ A β©))
          {X : π€ Μ }

        where

  canonical-map-charac : (s t : S X) (p : s β‘ t)

                       β canonical-map ΞΉ Ο s t p
                       β‘ transport (Ξ» - β ΞΉ (X , s) (X , -) (id-β X)) p (Ο (X , s))

  canonical-map-charac s = transport-lemma (Ξ» t β ΞΉ (X , s) (X , t) (id-β X)) s
                            (canonical-map ΞΉ Ο s)

  when-canonical-map-is-equiv : ((s t : S X) β is-equiv (canonical-map ΞΉ Ο s t))
                              β ((s : S X) β β! t κ S X , ΞΉ (X , s) (X , t) (id-β X))

  when-canonical-map-is-equiv = (Ξ» e s β fiberwise-equiv-universal (A s) s (Ο s) (e s)) ,
                                (Ξ» Ο s β universal-fiberwise-equiv (A s) (Ο s) s (Ο s))
   where
    A = Ξ» s t β ΞΉ (X , s) (X , t) (id-β X)
    Ο = canonical-map ΞΉ Ο

  canonical-map-equiv-criterion : ((s t : S X) β (s β‘ t) β ΞΉ (X , s) (X , t) (id-β X))
                                β (s t : S X) β is-equiv (canonical-map ΞΉ Ο s t)

  canonical-map-equiv-criterion Ο s = fiberwise-equiv-criterion'
                                       (Ξ» t β ΞΉ (X , s) (X , t) (id-β X))
                                       s (Ο s) (canonical-map ΞΉ Ο s)

  canonical-map-equiv-criterion' : ((s t : S X) β ΞΉ (X , s) (X , t) (id-β X) β (s β‘ t))
                                 β (s t : S X) β is-equiv (canonical-map ΞΉ Ο s t)

  canonical-map-equiv-criterion' Ο s = fiberwise-equiv-criterion
                                        (Ξ» t β ΞΉ (X , s) (X , t) (id-β X))
                                        s (Ο s) (canonical-map ΞΉ Ο s)

module β-magma {π€ : Universe} where

 open sip

 β-magma-structure : π€ Μ β π€ Μ
 β-magma-structure X = X β X β X

 β-Magma : π€ βΊ Μ
 β-Magma = Ξ£ X κ π€ Μ , β-magma-structure X

 sns-data : SNS β-magma-structure π€
 sns-data = (ΞΉ , Ο , ΞΈ)
  where
   ΞΉ : (A B : β-Magma) β β¨ A β© β β¨ B β© β π€ Μ
   ΞΉ (X , _Β·_) (Y , _*_) (f , _) = (Ξ» x x' β f (x Β· x')) β‘ (Ξ» x x' β f x * f x')

   Ο : (A : β-Magma) β ΞΉ A A (id-β β¨ A β©)
   Ο (X , _Β·_) = refl _Β·_

   h : {X : π€ Μ } {_Β·_ _*_ : β-magma-structure X}
     β canonical-map ΞΉ Ο _Β·_ _*_ βΌ ππ (_Β·_ β‘ _*_)

   h (refl _Β·_) = refl (refl _Β·_)

   ΞΈ : {X : π€ Μ } (_Β·_ _*_ : β-magma-structure X)
     β is-equiv (canonical-map ΞΉ Ο _Β·_ _*_)

   ΞΈ _Β·_ _*_ = equivs-closed-under-βΌ (id-is-equiv (_Β·_ β‘ _*_)) h

 _β_ : β-Magma β β-Magma β π€ Μ

 (X , _Β·_) β (Y , _*_) =

           Ξ£ f κ (X β Y), is-equiv f
                        Γ ((Ξ» x x' β f (x Β· x')) β‘ (Ξ» x x' β f x * f x'))

 characterization-of-β-Magma-β‘ : is-univalent π€ β (A B : β-Magma) β (A β‘ B) β (A β B)
 characterization-of-β-Magma-β‘ ua = characterization-of-β‘ ua sns-data

 characterization-of-characterization-of-β-Magma-β‘ :

    (ua : is-univalent π€) (A : β-Magma)
  β
    β characterization-of-β-Magma-β‘ ua A A β (refl A)
  β‘
    (ππ β¨ A β© , id-is-equiv β¨ A β© , refl _)

 characterization-of-characterization-of-β-Magma-β‘ ua A = refl _

module sip-with-axioms where

 open sip

 [_] : {S : π€ Μ β π₯ Μ } {axioms : (X : π€ Μ ) β S X β π¦ Μ }
     β (Ξ£ X κ π€ Μ , Ξ£ s κ S X , axioms X s) β Ξ£ S

 [ X , s , _ ] = (X , s)

 βͺ_β« : {S : π€ Μ β π₯ Μ } {axioms : (X : π€ Μ ) β S X β π¦ Μ }
     β (Ξ£ X κ π€ Μ , Ξ£ s κ S X , axioms X s) β π€ Μ

 βͺ X , _ , _ β« = X

 add-axioms : {S : π€ Μ β π₯ Μ }
              (axioms : (X : π€ Μ ) β S X β π¦ Μ )
            β ((X : π€ Μ ) (s : S X) β is-subsingleton (axioms X s))

            β SNS S π£
            β SNS (Ξ» X β Ξ£ s κ S X , axioms X s) π£

 add-axioms {π€} {π₯} {π¦} {π£} {S} axioms i (ΞΉ , Ο , ΞΈ) = ΞΉ' , Ο' , ΞΈ'
  where
   S' : π€ Μ β π₯ β π¦  Μ
   S' X = Ξ£ s κ S X , axioms X s

   ΞΉ' : (A B : Ξ£ S') β β¨ A β© β β¨ B β© β π£ Μ
   ΞΉ' A B = ΞΉ [ A ] [ B ]

   Ο' : (A : Ξ£ S') β ΞΉ' A A (id-β β¨ A β©)
   Ο' A = Ο [ A ]

   ΞΈ' : {X : π€ Μ } (s' t' : S' X) β is-equiv (canonical-map ΞΉ' Ο' s' t')
   ΞΈ' {X} (s , a) (t , b) = Ξ³
    where
     Ο : S' X β S X
     Ο (s , _) = s

     j : is-embedding Ο
     j = prβ-embedding (i X)

     k : {s' t' : S' X} β is-equiv (ap Ο {s'} {t'})
     k {s'} {t'} = embedding-gives-ap-is-equiv Ο j s' t'

     l : canonical-map ΞΉ' Ο' (s , a) (t , b)
       βΌ canonical-map ΞΉ Ο s t β ap Ο {s , a} {t , b}

     l (refl (s , a)) = refl (Ο (X , s))

     e : is-equiv (canonical-map ΞΉ Ο s t β ap Ο {s , a} {t , b})
     e = β-is-equiv (ΞΈ s t) k

     Ξ³ : is-equiv (canonical-map ΞΉ' Ο' (s , a) (t , b))
     Ξ³ = equivs-closed-under-βΌ e l

 characterization-of-β‘-with-axioms :

     is-univalent π€
   β {S : π€ Μ β π₯ Μ }
     (Ο : SNS S π£)
     (axioms : (X : π€ Μ ) β S X β π¦ Μ )
   β ((X : π€ Μ ) (s : S X) β is-subsingleton (axioms X s))
   β (A B : Ξ£ X κ π€ Μ , Ξ£ s κ S X , axioms X s)

   β (A β‘ B) β ([ A ] β[ Ο ] [ B ])

 characterization-of-β‘-with-axioms ua Ο axioms i =
   characterization-of-β‘ ua (add-axioms axioms i Ο)

module magma {π€ : Universe} where

 open sip-with-axioms

 Magma : π€ βΊ Μ
 Magma = Ξ£ X κ π€ Μ , (X β X β X) Γ is-set X

 _β_ : Magma β Magma β π€ Μ

 (X , _Β·_ , _) β (Y , _*_ , _) =

               Ξ£ f κ (X β Y), is-equiv f
                            Γ ((Ξ» x x' β f (x Β· x')) β‘ (Ξ» x x' β f x * f x'))

 characterization-of-Magma-β‘ : is-univalent π€ β (A B : Magma ) β (A β‘ B) β (A β B)
 characterization-of-Magma-β‘ ua =
   characterization-of-β‘-with-axioms ua
     β-magma.sns-data
     (Ξ» X s β is-set X)
     (Ξ» X s β being-set-is-subsingleton (univalence-gives-dfunext ua))

module pointed-type {π€ : Universe} where

 open sip

 Pointed : π€ Μ β π€ Μ
 Pointed X = X

 sns-data : SNS Pointed π€
 sns-data = (ΞΉ , Ο , ΞΈ)
  where
   ΞΉ : (A B : Ξ£ Pointed) β β¨ A β© β β¨ B β© β π€ Μ
   ΞΉ (X , xβ) (Y , yβ) (f , _) = (f xβ β‘ yβ)

   Ο : (A : Ξ£ Pointed) β ΞΉ A A (id-β β¨ A β©)
   Ο (X , xβ) = refl xβ

   ΞΈ : {X : π€ Μ } (xβ xβ : Pointed X) β is-equiv (canonical-map ΞΉ Ο xβ xβ)
   ΞΈ xβ xβ = equivs-closed-under-βΌ (id-is-equiv (xβ β‘ xβ)) h
    where
     h : canonical-map ΞΉ Ο xβ xβ βΌ ππ (xβ β‘ xβ)
     h (refl xβ) = refl (refl xβ)

 _β_ : Ξ£ Pointed β Ξ£ Pointed β π€ Μ
 (X , xβ) β (Y , yβ) = Ξ£ f κ (X β Y), is-equiv f Γ (f xβ β‘ yβ)

 characterization-of-pointed-type-β‘ : is-univalent π€
                                    β (A B : Ξ£ Pointed)

                                    β (A β‘ B) β (A β B)

 characterization-of-pointed-type-β‘ ua = characterization-of-β‘ ua sns-data

module sip-join where

 technical-lemma :
     {X : π€ Μ } {A : X β X β π₯ Μ }
     {Y : π¦ Μ } {B : Y β Y β π£ Μ }
     (f : (xβ xβ : X) β xβ β‘ xβ β A xβ xβ)
     (g : (yβ yβ : Y) β yβ β‘ yβ β B yβ yβ)
   β ((xβ xβ : X) β is-equiv (f xβ xβ))
   β ((yβ yβ : Y) β is-equiv (g yβ yβ))

   β ((xβ , yβ) (xβ , yβ) : X Γ Y) β is-equiv (Ξ» (p : (xβ , yβ) β‘ (xβ , yβ)) β f xβ xβ (ap prβ p) ,
                                                                               g yβ yβ (ap prβ p))
 technical-lemma {π€} {π₯} {π¦} {π£} {X} {A} {Y} {B} f g i j (xβ , yβ) = Ξ³
  where
   u : β! xβ κ X , A xβ xβ
   u = fiberwise-equiv-universal (A xβ) xβ (f xβ) (i xβ)

   v : β! yβ κ Y , B yβ yβ
   v = fiberwise-equiv-universal (B yβ) yβ (g yβ) (j yβ)

   C : X Γ Y β π₯ β π£ Μ
   C (xβ , yβ) = A xβ xβ Γ B yβ yβ

   w : (β! xβ κ X , A xβ xβ)
     β (β! yβ κ Y , B yβ yβ)
     β  β! (xβ , yβ) κ X Γ Y , C (xβ , yβ)
   w ((xβ , aβ) , Ο) ((yβ , bβ) , Ο) = ((xβ , yβ) , (aβ , bβ)) , Ξ΄
    where
     p : β x y a b
       β (xβ , aβ) β‘ (x , a)
       β (yβ , bβ) β‘ (y , b)
       β (xβ , yβ) , (aβ , bβ) β‘ (x , y) , (a , b)
     p .xβ .yβ .aβ .bβ (refl .(xβ , aβ)) (refl .(yβ , bβ)) = refl ((xβ , yβ) , (aβ , bβ))

     Ξ΄ : (((x , y) , (a , b)) : Ξ£ C) β (xβ , yβ) , (aβ , bβ) β‘ ((x , y) , (a , b))
     Ξ΄ ((x , y) , (a , b)) = p x y a b (Ο (x , a)) (Ο (y , b))

   Ο : Nat (π¨ (xβ , yβ)) C
   Ο (xβ , yβ) p = f xβ xβ (ap prβ p) , g yβ yβ (ap prβ p)

   Ξ³ : is-fiberwise-equiv Ο
   Ξ³ = universal-fiberwise-equiv C (w u v) (xβ , yβ) Ο


 variable
  π₯β π₯β π¦β π¦β : Universe

 open sip

 βͺ_β« : {Sβ : π€ Μ β π₯β Μ } {Sβ : π€ Μ β π₯β Μ }
     β (Ξ£ X κ π€ Μ , Sβ X Γ Sβ X) β π€ Μ

 βͺ X , sβ , sβ β« = X

 [_]β : {Sβ : π€ Μ β π₯β Μ } {Sβ : π€ Μ β π₯β Μ }
      β (Ξ£ X κ π€ Μ , Sβ X Γ Sβ X) β Ξ£ Sβ

 [ X , sβ , sβ ]β = (X , sβ)

 [_]β : {Sβ : π€ Μ β π₯β Μ } {Sβ : π€ Μ β π₯β Μ }
      β (Ξ£ X κ π€ Μ , Sβ X Γ Sβ X) β Ξ£ Sβ

 [ X , sβ , sβ ]β = (X , sβ)

 join : {Sβ : π€ Μ β π₯β Μ } {Sβ : π€ Μ β π₯β Μ }
      β SNS Sβ π¦β
      β SNS Sβ π¦β
      β SNS (Ξ» X β Sβ X Γ Sβ X) (π¦β β π¦β)

 join {π€} {π₯β} {π₯β} {π¦β} {π¦β} {Sβ} {Sβ} (ΞΉβ , Οβ , ΞΈβ) (ΞΉβ , Οβ , ΞΈβ) = ΞΉ , Ο , ΞΈ
  where
   S : π€ Μ β π₯β β π₯β Μ
   S X = Sβ X Γ Sβ X

   ΞΉ : (A B : Ξ£ S) β β¨ A β© β β¨ B β© β π¦β β π¦β Μ
   ΞΉ A B e = ΞΉβ [ A ]β [ B ]β e  Γ  ΞΉβ [ A ]β [ B ]β e

   Ο : (A : Ξ£ S) β ΞΉ A A (id-β β¨ A β©)
   Ο A = (Οβ [ A ]β , Οβ [ A ]β)

   ΞΈ : {X : π€ Μ } (s t : S X) β is-equiv (canonical-map ΞΉ Ο s t)
   ΞΈ {X} (sβ , sβ) (tβ , tβ) = Ξ³
    where
     c : (p : sβ , sβ β‘ tβ , tβ) β ΞΉβ (X , sβ) (X , tβ) (id-β X)
                                 Γ ΞΉβ (X , sβ) (X , tβ) (id-β X)

     c p = (canonical-map ΞΉβ Οβ sβ tβ (ap prβ p) ,
            canonical-map ΞΉβ Οβ sβ tβ (ap prβ p))

     i : is-equiv c
     i = technical-lemma
          (canonical-map ΞΉβ Οβ)
          (canonical-map ΞΉβ Οβ)
          ΞΈβ ΞΈβ (sβ , sβ) (tβ , tβ)

     e : canonical-map ΞΉ Ο (sβ , sβ) (tβ , tβ) βΌ c
     e (refl (sβ , sβ)) = refl (Οβ (X , sβ) , Οβ (X , sβ))

     Ξ³ : is-equiv (canonical-map ΞΉ Ο (sβ , sβ) (tβ , tβ))
     Ξ³ = equivs-closed-under-βΌ i e

 _ββ¦_,_β§_ : {Sβ : π€ Μ β π₯ Μ } {Sβ : π€ Μ β π₯β Μ }

          β (Ξ£ X κ π€ Μ , Sβ X Γ Sβ X)
          β SNS Sβ π¦β
          β SNS Sβ π¦β
          β (Ξ£ X κ π€ Μ , Sβ X Γ Sβ X)

          β π€ β π¦β β π¦β Μ

 A ββ¦ Οβ , Οβ β§ B = Ξ£ f κ (βͺ A β« β βͺ B β«)
                  , Ξ£ i κ is-equiv f , homomorphic Οβ [ A ]β [ B ]β (f , i)
                                     Γ homomorphic Οβ [ A ]β [ B ]β (f , i)

 characterization-of-join-β‘ : is-univalent π€
                            β {Sβ : π€ Μ β π₯ Μ } {Sβ : π€ Μ β π₯β Μ }
                              (Οβ : SNS Sβ π¦β)  (Οβ : SNS Sβ π¦β)
                              (A B : Ξ£ X κ π€ Μ , Sβ X Γ Sβ X)

                            β (A β‘ B) β (A ββ¦ Οβ , Οβ β§ B)

 characterization-of-join-β‘ ua Οβ Οβ = characterization-of-β‘ ua (join Οβ Οβ)

module pointed-β-magma {π€ : Universe} where

 open sip-join

 β-MagmaΒ· : π€ βΊ Μ
 β-MagmaΒ· = Ξ£ X κ π€ Μ , (X β X β X) Γ X

 _β_ : β-MagmaΒ· β β-MagmaΒ· β π€ Μ

 (X ,  _Β·_ , xβ) β (Y ,  _*_ , yβ) =

                 Ξ£ f κ (X β Y), is-equiv f
                              Γ ((Ξ» x x' β f (x Β· x')) β‘ (Ξ» x x' β f x * f x'))
                              Γ (f xβ β‘ yβ)

 characterization-of-pointed-magma-β‘ : is-univalent π€
                                     β (A B : β-MagmaΒ·)

                                     β (A β‘ B) β (A β B)

 characterization-of-pointed-magma-β‘ ua = characterization-of-join-β‘ ua
                                            β-magma.sns-data
                                            pointed-type.sns-data

module monoid {π€ : Universe} (ua : is-univalent π€) where

 dfe : dfunext π€ π€
 dfe = univalence-gives-dfunext ua

 open sip
 open sip-join
 open sip-with-axioms

 monoid-structure : π€ Μ β π€ Μ
 monoid-structure X = (X β X β X) Γ X

 monoid-axioms : (X : π€ Μ ) β monoid-structure X β π€ Μ
 monoid-axioms X (_Β·_ , e) = is-set X
                           Γ monoids.left-neutral  e _Β·_
                           Γ monoids.right-neutral e _Β·_
                           Γ monoids.associative     _Β·_

 Monoid : π€ βΊ Μ
 Monoid = Ξ£ X κ π€ Μ , Ξ£ s κ monoid-structure X , monoid-axioms X s

 monoid-axioms-subsingleton : (X : π€ Μ ) (s : monoid-structure X)
                            β is-subsingleton (monoid-axioms X s)

 monoid-axioms-subsingleton X (_Β·_ , e) s = Ξ³ s
  where
   i : is-set X
   i = prβ s

   Ξ³ : is-subsingleton (monoid-axioms X (_Β·_ , e))
   Ξ³ = Γ-is-subsingleton
         (being-set-is-subsingleton dfe)
      (Γ-is-subsingleton
         (Ξ -is-subsingleton dfe
           (Ξ» x β i (e Β· x) x))
      (Γ-is-subsingleton
         (Ξ -is-subsingleton dfe
           (Ξ» x β i (x Β· e) x))
         (Ξ -is-subsingleton dfe
           (Ξ» x β Ξ -is-subsingleton dfe
           (Ξ» y β Ξ -is-subsingleton dfe
           (Ξ» z β i ((x Β· y) Β· z) (x Β· (y Β· z))))))))

 sns-data : SNS (Ξ» X β Ξ£ s κ monoid-structure X , monoid-axioms X s) π€
 sns-data = add-axioms
              monoid-axioms monoid-axioms-subsingleton
              (join
                 β-magma.sns-data
                 pointed-type.sns-data)

 _β_ : Monoid β Monoid β π€ Μ

 (X , (_Β·_ , d) , _) β (Y , (_*_ , e) , _) =

                     Ξ£ f κ (X β Y), is-equiv f
                                  Γ ((Ξ» x x' β f (x Β· x')) β‘ (Ξ» x x' β f x * f x'))
                                  Γ (f d β‘ e)

 characterization-of-monoid-β‘ : is-univalent π€
                              β (A B : Monoid)

                              β (A β‘ B) β (A β B)

 characterization-of-monoid-β‘ ua = characterization-of-β‘ ua sns-data

module associative-β-magma
        {π€ : Universe}
        (ua : is-univalent π€)
       where

 fe : dfunext π€ π€
 fe = univalence-gives-dfunext ua

 associative : {X : π€ Μ } β (X β X β X) β π€ Μ
 associative _Β·_ = β x y z β (x Β· y) Β· z β‘ x Β· (y Β· z)

 β-amagma-structure : π€ Μ β π€ Μ
 β-amagma-structure X = Ξ£ _Β·_ κ (X β X β X), (associative _Β·_)

 β-aMagma : π€ βΊ Μ
 β-aMagma = Ξ£ X κ π€ Μ , β-amagma-structure X

 homomorphic : {X Y : π€ Μ } β (X β X β X) β (Y β Y β Y) β (X β Y) β π€ Μ
 homomorphic _Β·_ _*_ f = (Ξ» x y β f (x Β· y)) β‘ (Ξ» x y β f x * f y)

 respect-assoc : {X A : π€ Μ } (_Β·_ : X β X β X) (_*_ : A β A β A)
               β associative _Β·_ β associative _*_
               β (f : X β A) β homomorphic _Β·_ _*_ f β π€ Μ

 respect-assoc _Β·_ _*_ Ξ± Ξ² f h  =  fΞ± β‘ Ξ²f
  where
   l = Ξ» x y z β f ((x Β· y) Β· z)   β‘β¨ ap (Ξ» - β - (x Β· y) z) h β©
                 f (x Β· y) * f z   β‘β¨ ap (Ξ» - β - x y * f z) h β©
                 (f x * f y) * f z β

   r = Ξ» x y z β f (x Β· (y Β· z))   β‘β¨ ap (Ξ» - β - x (y Β· z)) h β©
                 f x * f (y Β· z)   β‘β¨ ap (Ξ» - β f x * - y z) h β©
                 f x * (f y * f z) β

   fΞ± Ξ²f : β x y z β (f x * f y) * f z β‘ f x * (f y * f z)
   fΞ± x y z = (l x y z)β»ΒΉ β ap f (Ξ± x y z) β r x y z
   Ξ²f x y z = Ξ² (f x) (f y) (f z)

 remark : {X : π€ Μ } (_Β·_ : X β X β X) (Ξ± Ξ² : associative _Β·_ )
        β respect-assoc _Β·_ _Β·_ Ξ± Ξ² id (refl _Β·_)
        β‘ ((Ξ» x y z β refl ((x Β· y) Β· z) β ap id (Ξ± x y z)) β‘ Ξ²)

 remark _Β·_ Ξ± Ξ² = refl _

 open sip hiding (homomorphic)

 sns-data : SNS β-amagma-structure π€
 sns-data = (ΞΉ , Ο , ΞΈ)
  where
   ΞΉ : (π§ π : β-aMagma) β β¨ π§ β© β β¨ π β© β π€ Μ
   ΞΉ (X , _Β·_ , Ξ±) (A , _*_ , Ξ²) (f , i) = Ξ£ h κ homomorphic _Β·_ _*_ f
                                               , respect-assoc _Β·_ _*_ Ξ± Ξ² f h

   Ο : (π§ : β-aMagma) β ΞΉ π§ π§ (id-β β¨ π§ β©)
   Ο (X , _Β·_ , Ξ±) = h , p
    where
     h : homomorphic _Β·_ _Β·_ id
     h = refl _Β·_

     p : (Ξ» x y z β refl ((x Β· y) Β· z) β ap id (Ξ± x y z)) β‘ Ξ±
     p = fe (Ξ» x β fe (Ξ» y β fe (Ξ» z β refl-left β ap-id (Ξ± x y z))))

   u : (X : π€ Μ ) β β s β β! t κ β-amagma-structure X , ΞΉ (X , s) (X , t) (id-β X)
   u X (_Β·_ , Ξ±) = c , Ο
    where
     c : Ξ£ t κ β-amagma-structure X , ΞΉ (X , _Β·_ , Ξ±) (X , t) (id-β X)
     c = (_Β·_ , Ξ±) , Ο (X , _Β·_ , Ξ±)

     Ο : (Ο : Ξ£ t κ β-amagma-structure X , ΞΉ (X , _Β·_ , Ξ±) (X , t) (id-β X)) β c β‘ Ο
     Ο ((_Β·_ , Ξ²) , refl _Β·_ , k) = Ξ³
      where
       a : associative _Β·_
       a x y z = refl ((x Β· y) Β· z) β ap id (Ξ± x y z)

       g : singleton-type' a β Ξ£ t κ β-amagma-structure X , ΞΉ (X , _Β·_ , Ξ±) (X , t) (id-β X)
       g (Ξ² , k) = (_Β·_ , Ξ²) , refl _Β·_ , k

       i : is-subsingleton (singleton-type' a)
       i = singletons-are-subsingletons _ (singleton-types'-are-singletons _ a)

       q : Ξ± , prβ (Ο (X , _Β·_ , Ξ±)) β‘ Ξ² , k
       q = i _ _

       Ξ³ : c β‘ (_Β·_ , Ξ²) , refl _Β·_ , k
       Ξ³ = ap g q

   ΞΈ : {X : π€ Μ } (s t : β-amagma-structure X) β is-equiv (canonical-map ΞΉ Ο s t)
   ΞΈ {X} s = universal-fiberwise-equiv (Ξ» t β ΞΉ (X , s) (X , t) (id-β X))
              (u X s) s (canonical-map ΞΉ Ο s)

 _β_ : β-aMagma β β-aMagma β π€ Μ
 (X , _Β·_ , Ξ±) β (Y , _*_ , Ξ²) = Ξ£ f κ (X β Y)
                                     , is-equiv f
                                     Γ (Ξ£ h κ homomorphic _Β·_ _*_ f
                                            , respect-assoc _Β·_ _*_ Ξ± Ξ² f h)

 characterization-of-β-aMagma-β‘ : (A B : β-aMagma) β (A β‘ B) β (A β B)
 characterization-of-β-aMagma-β‘ = characterization-of-β‘ ua sns-data

module group {π€ : Universe} (ua : is-univalent π€) where

 hfe : hfunext π€ π€
 hfe = univalence-gives-hfunext ua

 open sip
 open sip-with-axioms
 open monoid {π€} ua hiding (sns-data ; _β_)

 group-structure : π€ Μ β π€ Μ
 group-structure X = Ξ£ s κ monoid-structure X , monoid-axioms X s

 group-axiom : (X : π€ Μ ) β monoid-structure X β π€ Μ
 group-axiom X (_Β·_ , e) = (x : X) β Ξ£ x' κ X , (x Β· x' β‘ e) Γ (x' Β· x β‘ e)

 Group : π€ βΊ Μ
 Group = Ξ£ X κ π€ Μ , Ξ£ ((_Β·_ , e) , a) κ group-structure X , group-axiom X (_Β·_ , e)

 inv-lemma : (X : π€ Μ ) (_Β·_ : X β X β X) (e : X)
           β monoid-axioms X (_Β·_ , e)
           β (x y z : X)
           β (y Β· x) β‘ e
           β (x Β· z) β‘ e
           β y β‘ z

 inv-lemma X _Β·_  e (s , l , r , a) x y z q p =

    y             β‘β¨ (r y)β»ΒΉ β©
    (y Β· e)       β‘β¨ ap (y Β·_) (p β»ΒΉ) β©
    (y Β· (x Β· z)) β‘β¨ (a y x z)β»ΒΉ β©
    ((y Β· x) Β· z) β‘β¨ ap (_Β· z) q β©
    (e Β· z)       β‘β¨ l z β©
    z             β

 group-axiom-is-subsingleton : (X : π€ Μ )
                             β (s : group-structure X)
                             β is-subsingleton (group-axiom X (prβ s))

 group-axiom-is-subsingleton X ((_Β·_ , e) , (s , l , r , a)) = Ξ³
  where
   i : (x : X) β is-subsingleton (Ξ£ x' κ X , (x Β· x' β‘ e) Γ (x' Β· x β‘ e))
   i x (y , _ , q) (z , p , _) = u
    where
     t : y β‘ z
     t = inv-lemma X _Β·_ e (s , l , r , a) x y z q p

     u : (y , _ , q) β‘ (z , p , _)
     u = to-subtype-β‘ (Ξ» x' β Γ-is-subsingleton (s (x Β· x') e) (s (x' Β· x) e)) t

   Ξ³ : is-subsingleton (group-axiom X (_Β·_ , e))
   Ξ³ = Ξ -is-subsingleton dfe i

 sns-data : SNS (Ξ» X β Ξ£ s κ group-structure X , group-axiom X (prβ s)) π€
 sns-data = add-axioms
             (Ξ» X s β group-axiom X (prβ s)) group-axiom-is-subsingleton
             (monoid.sns-data ua)

 _β_ : Group β Group β π€ Μ

 (X , ((_Β·_ , d) , _) , _) β (Y , ((_*_ , e) , _) , _) =

            Ξ£ f κ (X β Y), is-equiv f
                         Γ ((Ξ» x x' β f (x Β· x')) β‘ (Ξ» x x' β f x * f x'))
                         Γ (f d β‘ e)

 characterization-of-group-β‘ : (A B : Group) β (A β‘ B) β (A β B)
 characterization-of-group-β‘ = characterization-of-β‘ ua sns-data

 _β'_ : Group β Group β π€ Μ

 (X , ((_Β·_ , d) , _) , _) β' (Y , ((_*_ , e) , _) , _) =

            Ξ£ f κ (X β Y), is-equiv f
                         Γ ((Ξ» x x' β f (x Β· x')) β‘ (Ξ» x x' β f x * f x'))

 group-structure-of : (G : Group) β group-structure β¨ G β©
 group-structure-of (X , ((_Β·_ , e) , i , l , r , a) , Ξ³) = (_Β·_ , e) , i , l , r , a

 monoid-structure-of : (G : Group) β monoid-structure β¨ G β©
 monoid-structure-of (X , ((_Β·_ , e) , i , l , r , a) , Ξ³) = (_Β·_ , e)

 monoid-axioms-of : (G : Group) β monoid-axioms β¨ G β© (monoid-structure-of G)
 monoid-axioms-of (X , ((_Β·_ , e) , i , l , r , a) , Ξ³) = i , l , r , a

 multiplication : (G : Group) β β¨ G β© β β¨ G β© β β¨ G β©
 multiplication (X , ((_Β·_ , e) , i , l , r , a) , Ξ³) = _Β·_

 syntax multiplication G x y = x Β·β¨ G β© y

 unit : (G : Group) β β¨ G β©
 unit (X , ((_Β·_ , e) , i , l , r , a) , Ξ³) = e

 group-is-set : (G : Group)
              β is-set β¨ G β©

 group-is-set (X , ((_Β·_ , e) , i , l , r , a) , Ξ³) = i

 unit-left : (G : Group) (x : β¨ G β©)
           β unit G Β·β¨ G β© x β‘ x

 unit-left (X , ((_Β·_ , e) , i , l , r , a) , Ξ³) x = l x

 unit-right : (G : Group) (x : β¨ G β©)
            β x Β·β¨ G β© unit G β‘ x

 unit-right (X , ((_Β·_ , e) , i , l , r , a) , Ξ³) x = r x

 assoc : (G : Group) (x y z : β¨ G β©)
       β (x Β·β¨ G β© y) Β·β¨ G β© z β‘ x Β·β¨ G β© (y Β·β¨ G β© z)

 assoc (X , ((_Β·_ , e) , i , l , r , a) , Ξ³) = a

 inv : (G : Group) β β¨ G β© β β¨ G β©
 inv (X , ((_Β·_ , e) , i , l , r , a) , Ξ³) x = prβ (Ξ³ x)

 inv-left : (G : Group) (x : β¨ G β©)
          β inv G x Β·β¨ G β© x β‘ unit G

 inv-left (X , ((_Β·_ , e) , i , l , r , a) , Ξ³) x = prβ (prβ (Ξ³ x))

 inv-right : (G : Group) (x : β¨ G β©)
           β x Β·β¨ G β© inv G x β‘ unit G

 inv-right (X , ((_Β·_ , e) , i , l , r , a) , Ξ³) x = prβ (prβ (Ξ³ x))

 preserves-multiplication : (G H : Group) β (β¨ G β© β β¨ H β©) β π€ Μ
 preserves-multiplication G H f = (Ξ» (x y : β¨ G β©) β f (x Β·β¨ G β© y))
                                β‘ (Ξ» (x y : β¨ G β©) β f x Β·β¨ H β© f y)

 preserves-unit : (G H : Group) β (β¨ G β© β β¨ H β©) β π€ Μ
 preserves-unit G H f = f (unit G) β‘ unit H

 idempotent-is-unit : (G : Group) (x : β¨ G β©)
                    β x Β·β¨ G β© x β‘ x
                    β x β‘ unit G

 idempotent-is-unit G x p = Ξ³
  where
   x' = inv G x
   Ξ³ = x                        β‘β¨ (unit-left G x)β»ΒΉ β©
       unit G Β·β¨ G β© x          β‘β¨ (ap (Ξ» - β - Β·β¨ G β© x) (inv-left G x))β»ΒΉ β©
       (x' Β·β¨ G β© x) Β·β¨ G β© x   β‘β¨ assoc G x' x x β©
       x' Β·β¨ G β© (x Β·β¨ G β© x)   β‘β¨ ap (Ξ» - β x' Β·β¨ G β© -) p β©
       x' Β·β¨ G β© x              β‘β¨ inv-left G x β©
       unit G                   β

 unit-preservation-lemma : (G H : Group) (f : β¨ G β© β β¨ H β©)
                         β preserves-multiplication G H f
                         β preserves-unit G H f

 unit-preservation-lemma G H f m = idempotent-is-unit H e p
  where
   e  = f (unit G)

   p = e Β·β¨ H β© e               β‘β¨ ap (Ξ» - β - (unit G) (unit G)) (m β»ΒΉ) β©
       f (unit G Β·β¨ G β© unit G) β‘β¨ ap f (unit-left G (unit G)) β©
       e                        β

 inv-Lemma : (G : Group) (x y z : β¨ G β©)
           β (y Β·β¨ G β© x) β‘ unit G
           β (x Β·β¨ G β© z) β‘ unit G
           β y β‘ z

 inv-Lemma G = inv-lemma β¨ G β© (multiplication G) (unit G) (monoid-axioms-of G)

 one-left-inv : (G : Group) (x x' : β¨ G β©)
              β (x' Β·β¨ G β© x) β‘ unit G
              β x' β‘ inv G x

 one-left-inv G x x' p = inv-Lemma G x x' (inv G x) p (inv-right G x)

 one-right-inv : (G : Group) (x x' : β¨ G β©)
               β (x Β·β¨ G β© x') β‘ unit G
               β x' β‘ inv G x

 one-right-inv G x x' p = (inv-Lemma G x (inv G x) x' (inv-left G x) p)β»ΒΉ

 preserves-inv : (G H : Group) β (β¨ G β© β β¨ H β©) β π€ Μ
 preserves-inv G H f = (x : β¨ G β©) β f (inv G x) β‘ inv H (f x)

 inv-preservation-lemma : (G H : Group) (f : β¨ G β© β β¨ H β©)
                        β preserves-multiplication G H f
                        β preserves-inv G H f

 inv-preservation-lemma G H f m x = Ξ³
  where
   p = f (inv G x) Β·β¨ H β© f x β‘β¨ (ap (Ξ» - β - (inv G x) x) m)β»ΒΉ β©
       f (inv G x Β·β¨ G β© x)   β‘β¨ ap f (inv-left G x) β©
       f (unit G)             β‘β¨ unit-preservation-lemma G H f m β©
       unit H                 β

   Ξ³ : f (inv G x) β‘ inv H (f x)
   Ξ³ = one-left-inv H (f x) (f (inv G x)) p

 is-homomorphism : (G H : Group) β (β¨ G β© β β¨ H β©) β π€ Μ
 is-homomorphism G H f = preserves-multiplication G H f
                       Γ preserves-unit G H f

 preservation-of-mult-is-subsingleton : (G H : Group) (f : β¨ G β© β β¨ H β©)
                                      β is-subsingleton (preserves-multiplication G H f)
 preservation-of-mult-is-subsingleton G H f = j
  where
   j : is-subsingleton (preserves-multiplication G H f)
   j = Ξ -is-set hfe
        (Ξ» _ β Ξ -is-set hfe
        (Ξ» _ β group-is-set H))
        (Ξ» (x y : β¨ G β©) β f (x Β·β¨ G β© y))
        (Ξ» (x y : β¨ G β©) β f x Β·β¨ H β© f y)

 being-homomorphism-is-subsingleton : (G H : Group) (f : β¨ G β© β β¨ H β©)
                                    β is-subsingleton (is-homomorphism G H f)
 being-homomorphism-is-subsingleton G H f = i
  where

   i : is-subsingleton (is-homomorphism G H f)
   i = Γ-is-subsingleton
        (preservation-of-mult-is-subsingleton G H f)
        (group-is-set H (f (unit G)) (unit H))

 notions-of-homomorphism-agree : (G H : Group) (f : β¨ G β© β β¨ H β©)
                               β is-homomorphism G H f
                               β preserves-multiplication G H f

 notions-of-homomorphism-agree G H f = Ξ³
  where
   Ξ± : is-homomorphism G H f β preserves-multiplication G H f
   Ξ± = prβ

   Ξ² : preserves-multiplication G H f β is-homomorphism G H f
   Ξ² m = m , unit-preservation-lemma G H f m

   Ξ³ : is-homomorphism G H f β preserves-multiplication G H f
   Ξ³ = logically-equivalent-subsingletons-are-equivalent _ _
        (being-homomorphism-is-subsingleton G H f)
        (preservation-of-mult-is-subsingleton G H f)
        (Ξ± , Ξ²)

 β-agreement : (G H : Group) β (G β H) β (G β' H)
 β-agreement G H = Ξ£-cong (Ξ» f β Ξ£-cong (Ξ» _ β notions-of-homomorphism-agree G H f))

 forget-unit-preservation : (G H : Group) β (G β H) β (G β' H)
 forget-unit-preservation G H (f , e , m , _) = f , e , m

 NB : (G H : Group) β β β-agreement G H β β‘ forget-unit-preservation G H
 NB G H = refl _

 forget-unit-preservation-is-equiv : (G H : Group)
                                   β is-equiv (forget-unit-preservation G H)

 forget-unit-preservation-is-equiv G H = ββ-is-equiv (β-agreement G H)

module subgroup
        (π€  : Universe)
        (ua : Univalence)
       where

 gfe : global-dfunext
 gfe = univalence-gives-global-dfunext ua

 open sip
 open monoid {π€} (ua π€) hiding (sns-data ; _β_)
 open group {π€} (ua π€)

 module ambient (G : Group) where

  _Β·_ : β¨ G β© β β¨ G β© β β¨ G β©
  x Β· y = x Β·β¨ G β© y

  infixl 42 _Β·_

  group-closed : (β¨ G β© β π₯ Μ ) β π€ β π₯ Μ
  group-closed π = π (unit G)
                 Γ ((x y : β¨ G β©) β π x β π y β π (x Β· y))
                 Γ ((x : β¨ G β©) β π x β π (inv G x))

  Subgroups : π€ βΊ Μ
  Subgroups = Ξ£ A κ π β¨ G β© , group-closed (_β A)

  βͺ_β« : Subgroups β π β¨ G β©
  βͺ A , u , c , ΞΉ β« = A

  being-group-closed-subset-is-subsingleton : (A : π β¨ G β©) β is-subsingleton (group-closed (_β A))
  being-group-closed-subset-is-subsingleton A = Γ-is-subsingleton
                                                  (β-is-subsingleton A (unit G))
                                               (Γ-is-subsingleton
                                                  (Ξ -is-subsingleton dfe
                                                     (Ξ» x β Ξ -is-subsingleton dfe
                                                     (Ξ» y β Ξ -is-subsingleton dfe
                                                     (Ξ» _ β Ξ -is-subsingleton dfe
                                                     (Ξ» _ β β-is-subsingleton A (x Β· y))))))
                                                  (Ξ -is-subsingleton dfe
                                                     (Ξ» x β Ξ -is-subsingleton dfe
                                                     (Ξ» _ β β-is-subsingleton A (inv G x)))))

  βͺβ«-is-embedding : is-embedding βͺ_β«
  βͺβ«-is-embedding = prβ-embedding being-group-closed-subset-is-subsingleton

  ap-βͺβ« : (S T : Subgroups) β S β‘ T β βͺ S β« β‘ βͺ T β«
  ap-βͺβ« S T = ap βͺ_β«

  ap-βͺβ«-is-equiv : (S T : Subgroups) β is-equiv (ap-βͺβ« S T)
  ap-βͺβ«-is-equiv = embedding-gives-ap-is-equiv βͺ_β« βͺβ«-is-embedding

  subgroups-form-a-set : is-set Subgroups
  subgroups-form-a-set S T = equiv-to-subsingleton
                              (ap-βͺβ« S T , ap-βͺβ«-is-equiv S T)
                              (powersets-are-sets' ua βͺ S β« βͺ T β«)

  subgroup-equality : (S T : Subgroups)
                    β (S β‘ T)
                    β ((x : β¨ G β©) β (x β βͺ S β«) β (x β βͺ T β«))

  subgroup-equality S T = Ξ³
   where
    f : S β‘ T β (x : β¨ G β©) β x β βͺ S β« β x β βͺ T β«
    f p x = transport (Ξ» - β x β βͺ - β«) p , transport (Ξ» - β x β βͺ - β«) (p β»ΒΉ)

    h : ((x : β¨ G β©) β x β βͺ S β« β x β βͺ T β«) β βͺ S β« β‘ βͺ T β«
    h Ο = subset-extensionality' ua Ξ± Ξ²
     where
      Ξ± : βͺ S β« β βͺ T β«
      Ξ± x = lr-implication (Ο x)

      Ξ² : βͺ T β« β βͺ S β«
      Ξ² x = rl-implication (Ο x)

    g : ((x : β¨ G β©) β x β βͺ S β« β x β βͺ T β«) β S β‘ T
    g = inverse (ap-βͺβ« S T) (ap-βͺβ«-is-equiv S T) β h

    Ξ³ : (S β‘ T) β ((x : β¨ G β©) β x β βͺ S β« β x β βͺ T β«)
    Ξ³ = logically-equivalent-subsingletons-are-equivalent _ _
          (subgroups-form-a-set S T)
          (Ξ -is-subsingleton dfe
             (Ξ» x β Γ-is-subsingleton
                      (Ξ -is-subsingleton dfe (Ξ» _ β β-is-subsingleton βͺ T β« x))
                      (Ξ -is-subsingleton dfe (Ξ» _ β β-is-subsingleton βͺ S β« x))))
          (f , g)

  T : π€ Μ β π€ Μ
  T X = Ξ£ ((_Β·_ , e) , a) κ group-structure X , group-axiom X (_Β·_ , e)

  module _ {X : π€ Μ } (h : X β β¨ G β©) (e : is-embedding h) where

   private
    h-lc : left-cancellable h
    h-lc = embeddings-are-lc h e

   having-group-closed-fiber-is-subsingleton : is-subsingleton (group-closed (fiber h))
   having-group-closed-fiber-is-subsingleton = being-group-closed-subset-is-subsingleton
                                                (Ξ» x β (fiber h x , e x))

   at-most-one-homomorphic-structure : is-subsingleton (Ξ£ Ο κ T X , is-homomorphism (X , Ο) G h)
   at-most-one-homomorphic-structure
      ((((_*_ ,  unitH) ,  maxioms) ,  gaxiom) ,  (pmult ,  punit))
      ((((_*'_ , unitH') , maxioms') , gaxiom') , (pmult' , punit'))
    = Ξ³
    where
     Ο Ο' : T X
     Ο  = ((_*_ ,  unitH) ,  maxioms) ,  gaxiom
     Ο' = ((_*'_ , unitH') , maxioms') , gaxiom'

     i :  is-homomorphism (X , Ο)  G h
     i  = (pmult ,  punit)

     i' : is-homomorphism (X , Ο') G h
     i' = (pmult' , punit')

     p : _*_ β‘ _*'_
     p = gfe (Ξ» x β gfe (Ξ» y β h-lc (h (x * y)  β‘β¨  ap (Ξ» - β - x y) pmult β©
                                     h x Β· h y  β‘β¨ (ap (Ξ» - β - x y) pmult')β»ΒΉ β©
                                     h (x *' y) β)))
     q : unitH β‘ unitH'
     q = h-lc (h unitH  β‘β¨  punit β©
               unit G   β‘β¨  punit' β»ΒΉ β©
               h unitH' β)

     r : (_*_ , unitH) β‘ (_*'_ , unitH')
     r = to-Γ-β‘ (p , q)

     Ξ΄ : Ο β‘ Ο'
     Ξ΄ = to-subtype-β‘
           (group-axiom-is-subsingleton X)
           (to-subtype-β‘
              (monoid-axioms-subsingleton X)
              r)

     Ξ³ : (Ο  , i) β‘ (Ο' , i')
     Ξ³ = to-subtype-β‘ (Ξ» Ο β being-homomorphism-is-subsingleton (X , Ο) G h) Ξ΄

   group-closed-fiber-gives-homomorphic-structure : group-closed (fiber h)
                                                  β (Ξ£ Ο κ T X , is-homomorphism (X , Ο) G h)

   group-closed-fiber-gives-homomorphic-structure (unitc , mulc , invc) = Ο , i
    where
     Ο : (x : X) β fiber h (h x)
     Ο x = (x , refl (h x))

     unitH : X
     unitH = fiber-point unitc

     _*_ : X β X β X
     x * y = fiber-point (mulc (h x) (h y) (Ο x) (Ο y))

     invH : X β X
     invH x = fiber-point (invc (h x) (Ο x))

     pmul : (x y : X) β h (x * y) β‘ h x Β· h y
     pmul x y = fiber-identification (mulc (h x) (h y) (Ο x) (Ο y))

     punit : h unitH β‘ unit G
     punit = fiber-identification unitc

     pinv : (x : X) β h (invH x) β‘ inv G (h x)
     pinv x = fiber-identification (invc (h x) (Ο x))

     unitH-left : (x : X) β unitH * x β‘ x
     unitH-left x = h-lc (h (unitH * x) β‘β¨ pmul unitH x β©
                          h unitH Β· h x β‘β¨ ap (_Β· h x) punit β©
                          unit G Β· h x  β‘β¨ unit-left G (h x) β©
                          h x           β)

     unitH-right : (x : X) β x * unitH β‘ x
     unitH-right x = h-lc (h (x * unitH) β‘β¨ pmul x unitH β©
                           h x Β· h unitH β‘β¨ ap (h x Β·_) punit β©
                           h x Β· unit G  β‘β¨ unit-right G (h x) β©
                           h x           β)

     assocH : (x y z : X) β ((x * y) * z) β‘ (x * (y * z))
     assocH x y z = h-lc (h ((x * y) * z)   β‘β¨ pmul (x * y) z β©
                          h (x * y) Β· h z   β‘β¨ ap (_Β· h z) (pmul x y) β©
                          (h x Β· h y) Β· h z β‘β¨ assoc G (h x) (h y) (h z) β©
                          h x Β· (h y Β· h z) β‘β¨ (ap (h x Β·_) (pmul y z))β»ΒΉ β©
                          h x Β· h (y * z)   β‘β¨ (pmul x (y * z))β»ΒΉ β©
                          h (x * (y * z))   β)

     group-axiomH : (x : X) β Ξ£ x' κ X , (x * x' β‘ unitH) Γ (x' * x β‘ unitH)
     group-axiomH x = invH x ,

                      h-lc (h (x * invH x)     β‘β¨ pmul x (invH x) β©
                            h x Β· h (invH x)   β‘β¨ ap (h x Β·_) (pinv x) β©
                            h x Β· inv G (h x)  β‘β¨ inv-right G (h x) β©
                            unit G             β‘β¨ punit β»ΒΉ β©
                            h unitH            β),

                      h-lc ((h (invH x * x)    β‘β¨ pmul (invH x) x β©
                             h (invH x) Β· h x  β‘β¨ ap (_Β· h x) (pinv x) β©
                             inv G (h x) Β· h x β‘β¨ inv-left G (h x) β©
                             unit G            β‘β¨ punit β»ΒΉ β©
                             h unitH           β))

     j : is-set X
     j = subtypes-of-sets-are-sets h h-lc (group-is-set G)

     Ο : T X
     Ο = ((_*_ , unitH) , (j , unitH-left , unitH-right , assocH)) , group-axiomH

     i : is-homomorphism (X , Ο) G h
     i = gfe (Ξ» x β gfe (pmul x)) , punit

   homomorphic-structure-gives-group-closed-fiber : (Ξ£ Ο κ T X , is-homomorphism (X , Ο) G h)
                                                  β group-closed (fiber h)

   homomorphic-structure-gives-group-closed-fiber
       ((((_*_ , unitH) , maxioms) , gaxiom) , (pmult , punit))
     = (unitc , mulc , invc)
    where
     H : Group
     H = X , ((_*_ , unitH) , maxioms) , gaxiom

     unitc : fiber h (unit G)
     unitc = unitH , punit

     mulc : ((x y : β¨ G β©) β fiber h x β fiber h y β fiber h (x Β· y))
     mulc x y (a , p) (b , q) = (a * b) ,
                                (h (a * b) β‘β¨ ap (Ξ» - β - a b) pmult β©
                                 h a Β· h b β‘β¨ apβ (Ξ» - -' β - Β· -') p q β©
                                 x Β· y     β)

     invc : ((x : β¨ G β©) β fiber h x β fiber h (inv G x))
     invc x (a , p) = inv H a ,
                      (h (inv H a) β‘β¨ inv-preservation-lemma H G h pmult a β©
                       inv G (h a) β‘β¨ ap (inv G) p β©
                       inv G x     β)

   fiber-structure-lemma : group-closed (fiber h)
                         β (Ξ£ Ο κ T X , is-homomorphism (X , Ο) G h)

   fiber-structure-lemma = logically-equivalent-subsingletons-are-equivalent _ _
                             having-group-closed-fiber-is-subsingleton
                             at-most-one-homomorphic-structure
                             (group-closed-fiber-gives-homomorphic-structure ,
                              homomorphic-structure-gives-group-closed-fiber)

  characterization-of-the-type-of-subgroups :  Subgroups β  (Ξ£ H κ Group
                                                           , Ξ£ h κ (β¨ H β© β β¨ G β©)
                                                           , is-embedding h
                                                           Γ is-homomorphism H G h)
  characterization-of-the-type-of-subgroups =

   Subgroups                                                                                       ββ¨ i β©
   (Ξ£ A κ π β¨ G β© , group-closed (_β A))                                                           ββ¨ ii β©
   (Ξ£ (X , h , e) κ Subtypes β¨ G β© , group-closed (fiber h))                                       ββ¨ iii β©
   (Ξ£ X κ π€ Μ , Ξ£ (h , e) κ X βͺ β¨ G β© , group-closed (fiber h))                                     ββ¨ iv β©
   (Ξ£ X κ π€ Μ , Ξ£ (h , e) κ X βͺ β¨ G β© , Ξ£ Ο κ T X , is-homomorphism (X , Ο) G h)                    ββ¨ v β©
   (Ξ£ X κ π€ Μ , Ξ£ h κ (X β β¨ G β©) , Ξ£ e κ is-embedding h , Ξ£ Ο κ T X , is-homomorphism (X , Ο) G h) ββ¨ vi β©
   (Ξ£ X κ π€ Μ , Ξ£ h κ (X β β¨ G β©) , Ξ£ Ο κ T X , Ξ£ e κ is-embedding h , is-homomorphism (X , Ο) G h) ββ¨ vii β©
   (Ξ£ X κ π€ Μ , Ξ£ Ο κ T X , Ξ£ h κ (X β β¨ G β©) , is-embedding h Γ is-homomorphism (X , Ο) G h)       ββ¨ viii β©
   (Ξ£ H κ Group , Ξ£ h κ (β¨ H β© β β¨ G β©) , is-embedding h Γ is-homomorphism H G h)                  β 

      where
       Ο : Subtypes β¨ G β© β π β¨ G β©
       Ο = Ο-special is-subsingleton β¨ G β©

       j : is-equiv Ο
       j = Ο-special-is-equiv (ua π€) gfe is-subsingleton β¨ G β©

       i    = id-β Subgroups
       ii   = Ξ£-change-of-variable (Ξ» (A : π β¨ G β©) β group-closed (_β A)) Ο j
       iii  = Ξ£-assoc
       iv   = Ξ£-cong (Ξ» X β Ξ£-cong (Ξ» (h , e) β fiber-structure-lemma h e))
       v    = Ξ£-cong (Ξ» X β Ξ£-assoc)
       vi   = Ξ£-cong (Ξ» X β Ξ£-cong (Ξ» h β Ξ£-flip))
       vii  = Ξ£-cong (Ξ» X β Ξ£-flip)
       viii = β-sym Ξ£-assoc

  induced-group : Subgroups β Group
  induced-group S = prβ (β characterization-of-the-type-of-subgroups β S)

module slice
        {π€ π₯ : Universe}
        (R : π₯ Μ )
       where

 open sip

 S : π€ Μ β π€ β π₯ Μ
 S X = X β R

 sns-data : SNS S (π€ β π₯)
 sns-data = (ΞΉ , Ο , ΞΈ)
  where
   ΞΉ : (A B : Ξ£ S) β β¨ A β© β β¨ B β© β π€ β π₯ Μ
   ΞΉ (X , g) (Y , h) (f , _) = (g β‘ h β f)

   Ο : (A : Ξ£ S) β ΞΉ A A (id-β β¨ A β©)
   Ο (X , g) = refl g

   k : {X : π€ Μ } {g h : S X} β canonical-map ΞΉ Ο g h βΌ ππ (g β‘ h)
   k (refl g) = refl (refl g)

   ΞΈ : {X : π€ Μ } (g h : S X) β is-equiv (canonical-map ΞΉ Ο g h)
   ΞΈ g h = equivs-closed-under-βΌ (id-is-equiv (g β‘ h)) k

 _β_  : π€ / R β π€ / R β π€ β π₯ Μ
 (X , g) β (Y , h) = Ξ£ f κ (X β Y), is-equiv f Γ (g β‘ h β f )

 characterization-of-/-β‘ : is-univalent π€ β (A B : π€ / R) β (A β‘ B) β (A β B)
 characterization-of-/-β‘ ua = characterization-of-β‘ ua sns-data

module generalized-metric-space
        {π€ π₯ : Universe}
        (R : π₯ Μ )
        (axioms  : (X : π€ Μ ) β (X β X β R) β π€ β π₯ Μ )
        (axiomss : (X : π€ Μ ) (d : X β X β R) β is-subsingleton (axioms X d))
       where

 open sip
 open sip-with-axioms

 S : π€ Μ β π€ β π₯ Μ
 S X = X β X β R

 sns-data : SNS S (π€ β π₯)
 sns-data = (ΞΉ , Ο , ΞΈ)
  where
   ΞΉ : (A B : Ξ£ S) β β¨ A β© β β¨ B β© β π€ β π₯ Μ
   ΞΉ (X , d) (Y , e) (f , _) = (d β‘ Ξ» x x' β e (f x) (f x'))

   Ο : (A : Ξ£ S) β ΞΉ A A (id-β β¨ A β©)
   Ο (X , d) = refl d

   h : {X : π€ Μ } {d e : S X} β canonical-map ΞΉ Ο d e βΌ ππ (d β‘ e)
   h (refl d) = refl (refl d)

   ΞΈ : {X : π€ Μ } (d e : S X) β is-equiv (canonical-map ΞΉ Ο d e)
   ΞΈ d e = equivs-closed-under-βΌ (id-is-equiv (d β‘ e)) h

 M : π€ βΊ β π₯  Μ
 M = Ξ£ X κ π€ Μ , Ξ£ d κ (X β X β R) , axioms X d

 _β_  : M β M β π€ β π₯ Μ
 (X , d , _) β (Y , e , _) = Ξ£ f κ (X β Y), is-equiv f
                                          Γ (d β‘ Ξ» x x' β e (f x) (f x'))

 characterization-of-M-β‘ : is-univalent π€
                         β (A B : M)

                         β (A β‘ B) β (A β B)

 characterization-of-M-β‘ ua = characterization-of-β‘-with-axioms ua
                                sns-data
                                axioms axiomss

module generalized-topological-space
        (π€ π₯ : Universe)
        (R : π₯ Μ )
        (axioms  : (X : π€ Μ ) β ((X β R) β R) β π€ β π₯ Μ )
        (axiomss : (X : π€ Μ ) (π : (X β R) β R) β is-subsingleton (axioms X π))
       where

 open sip
 open sip-with-axioms

 β : π¦ Μ β π₯ β π¦ Μ
 β X = X β R

 _β_ : {X : π¦ Μ } β X β β X β R
 x β A = A x

 inverse-image : {X Y : π€ Μ } β (X β Y) β β Y β β X
 inverse-image f B = Ξ» x β f x β B

 ββ : π€ Μ β π€ β π₯ Μ
 ββ X = β (β X)

 Space : π€ βΊ β π₯  Μ
 Space = Ξ£ X κ π€ Μ , Ξ£ π κ ββ X , axioms X π

 sns-data : SNS ββ (π€ β π₯)
 sns-data = (ΞΉ , Ο , ΞΈ)
  where
   ΞΉ : (A B : Ξ£ ββ) β β¨ A β© β β¨ B β© β π€ β π₯ Μ
   ΞΉ (X , πX) (Y , πY) (f , _) = (Ξ» (V : β Y) β inverse-image f V β πX) β‘ πY

   Ο : (A : Ξ£ ββ) β ΞΉ A A (id-β β¨ A β©)
   Ο (X , π) = refl π

   h : {X : π€ Μ } {π π' : ββ X} β canonical-map ΞΉ Ο π π' βΌ ππ (π β‘ π')
   h (refl π) = refl (refl π)

   ΞΈ : {X : π€ Μ } (π π' : ββ X) β is-equiv (canonical-map ΞΉ Ο π π')
   ΞΈ {X} π π' = equivs-closed-under-βΌ (id-is-equiv (π β‘ π')) h

 _β_  : Space β Space β π€ β π₯ Μ

 (X , πX , _) β (Y , πY , _) =

              Ξ£ f κ (X β Y), is-equiv f
                           Γ ((Ξ» V β inverse-image f V β πX) β‘ πY)

 characterization-of-Space-β‘ : is-univalent π€
                             β (A B : Space)

                             β (A β‘ B) β (A β B)

 characterization-of-Space-β‘ ua = characterization-of-β‘-with-axioms ua
                                   sns-data axioms axiomss

 _β'_  : Space β Space β π€ β π₯ Μ

 (X , F , _) β' (Y , G , _) =

             Ξ£ f κ (X β Y), is-equiv f
                          Γ ((Ξ» (v : Y β R) β F (v β f)) β‘ G)

 characterization-of-Space-β‘' : is-univalent π€
                              β (A B : Space)

                              β (A β‘ B) β (A β' B)

 characterization-of-Space-β‘' = characterization-of-Space-β‘

module selection-space
        (π€ π₯ : Universe)
        (R : π₯ Μ )
        (axioms  : (X : π€ Μ ) β ((X β R) β X) β π€ β π₯ Μ )
        (axiomss : (X : π€ Μ ) (Ξ΅ : (X β R) β X) β is-subsingleton (axioms X Ξ΅))
       where

 open sip
 open sip-with-axioms

 S : π€ Μ β π€ β π₯ Μ
 S X = (X β R) β X

 SelectionSpace : π€ βΊ β π₯  Μ
 SelectionSpace = Ξ£ X κ π€ Μ , Ξ£ Ξ΅ κ S X , axioms X Ξ΅

 sns-data : SNS S (π€ β π₯)
 sns-data = (ΞΉ , Ο , ΞΈ)
  where
   ΞΉ : (A B : Ξ£ S) β β¨ A β© β β¨ B β© β π€ β π₯ Μ
   ΞΉ (X , Ξ΅) (Y , Ξ΄) (f , _) = (Ξ» (q : Y β R) β f (Ξ΅ (q β f))) β‘ Ξ΄

   Ο : (A : Ξ£ S) β ΞΉ A A (id-β β¨ A β©)
   Ο (X , Ξ΅) = refl Ξ΅

   ΞΈ : {X : π€ Μ } (Ξ΅ Ξ΄ : S X) β is-equiv (canonical-map ΞΉ Ο Ξ΅ Ξ΄)
   ΞΈ {X} Ξ΅ Ξ΄ = Ξ³
    where
     h : canonical-map ΞΉ Ο Ξ΅ Ξ΄ βΌ ππ (Ξ΅ β‘ Ξ΄)
     h (refl Ξ΅) = refl (refl Ξ΅)

     Ξ³ : is-equiv (canonical-map ΞΉ Ο Ξ΅ Ξ΄)
     Ξ³ = equivs-closed-under-βΌ (id-is-equiv (Ξ΅ β‘ Ξ΄)) h

 _β_  :  SelectionSpace β SelectionSpace β π€ β π₯ Μ

 (X , Ξ΅ , _) β (Y , Ξ΄ , _) =

             Ξ£ f κ (X β Y), is-equiv f
                          Γ ((Ξ» (q : Y β R) β f (Ξ΅ (q β f))) β‘ Ξ΄)

 characterization-of-selection-space-β‘ : is-univalent π€
                                       β (A B : SelectionSpace)

                                       β (A β‘ B) β (A β B)

 characterization-of-selection-space-β‘ ua = characterization-of-β‘-with-axioms ua
                                             sns-data
                                             axioms axiomss

module contrived-example (π€ : Universe) where

 open sip

 contrived-β‘ : is-univalent π€ β

    (X Y : π€ Μ ) (Ο : (X β X) β X) (Ξ³ : (Y β Y) β Y)
  β
    ((X , Ο) β‘ (Y , Ξ³)) β (Ξ£ f κ (X β Y)
                         , Ξ£ i κ is-equiv f
                         , (Ξ» (g : Y β Y) β f (Ο (inverse f i β g β f))) β‘ Ξ³)

 contrived-β‘ ua X Y Ο Ξ³ =
   characterization-of-β‘ ua
    ((Ξ» (X , Ο) (Y , Ξ³) (f , i) β (Ξ» (g : Y β Y) β f (Ο (inverse f i β g β f))) β‘ Ξ³) ,
     (Ξ» (X , Ο) β refl Ο) ,
     (Ξ» Ο Ξ³ β equivs-closed-under-βΌ (id-is-equiv (Ο β‘ Ξ³)) (Ξ» {(refl Ο) β refl (refl Ο)})))
    (X , Ο) (Y , Ξ³)

module generalized-functor-algebra
         {π€ π₯ : Universe}
         (F : π€ Μ β π₯ Μ )
         (π : {X Y : π€ Μ } β (X β Y) β F X β F Y)
         (π-id : {X : π€ Μ } β π (ππ X) β‘ ππ (F X))
       where

 open sip

 S : π€ Μ β π€ β π₯ Μ
 S X = F X β X

 sns-data : SNS S (π€ β π₯)
 sns-data = (ΞΉ , Ο , ΞΈ)
  where
   ΞΉ : (A B : Ξ£ S) β β¨ A β© β β¨ B β© β π€ β π₯ Μ
   ΞΉ (X , Ξ±) (Y , Ξ²) (f , _) = f β Ξ± β‘ Ξ² β π f

   Ο : (A : Ξ£ S) β ΞΉ A A (id-β β¨ A β©)
   Ο (X , Ξ±) = Ξ±        β‘β¨ ap (Ξ± β_) (π-id β»ΒΉ) β©
               Ξ± β π id β

   ΞΈ : {X : π€ Μ } (Ξ± Ξ² : S X) β is-equiv (canonical-map ΞΉ Ο Ξ± Ξ²)
   ΞΈ {X} Ξ± Ξ² = Ξ³
    where
     c : Ξ± β‘ Ξ² β Ξ± β‘ Ξ² β π id
     c = transport (Ξ± β‘_) (Ο (X , Ξ²))

     i : is-equiv c
     i = transport-is-equiv (Ξ± β‘_) (Ο (X , Ξ²))

     h : canonical-map ΞΉ Ο Ξ± Ξ² βΌ c
     h (refl _) = Ο (X , Ξ±)          β‘β¨ refl-left β»ΒΉ β©
                  refl Ξ± β Ο (X , Ξ±) β

     Ξ³ : is-equiv (canonical-map ΞΉ Ο Ξ± Ξ²)
     Ξ³ = equivs-closed-under-βΌ i h

 characterization-of-functor-algebra-β‘ : is-univalent π€
   β (X Y : π€ Μ ) (Ξ± : F X β X) (Ξ² : F Y β Y)

   β ((X , Ξ±) β‘ (Y , Ξ²))  β  (Ξ£ f κ (X β Y), is-equiv f Γ (f β Ξ± β‘ Ξ² β π f))

 characterization-of-functor-algebra-β‘ ua X Y Ξ± Ξ² =
   characterization-of-β‘ ua sns-data (X , Ξ±) (Y , Ξ²)

type-valued-preorder-S : π€ Μ β π€ β (π₯ βΊ) Μ
type-valued-preorder-S {π€} {π₯} X = Ξ£ _β€_ κ (X β X β π₯ Μ )
                                         , ((x : X) β x β€ x)
                                         Γ ((x y z : X) β x β€ y β y β€ z β x β€ z)

module type-valued-preorder
        (π€ π₯ : Universe)
        (ua : Univalence)
       where

 open sip

 fe : global-dfunext
 fe = univalence-gives-global-dfunext ua

 hfe : global-hfunext
 hfe = univalence-gives-global-hfunext ua

 S : π€ Μ β π€ β (π₯ βΊ) Μ
 S = type-valued-preorder-S {π€} {π₯}

 Type-valued-preorder : (π€ β π₯) βΊ Μ
 Type-valued-preorder = Ξ£ S

 Ob : Ξ£ S β π€ Μ
 Ob (X , homX , idX , compX ) = X

 hom : (π§ : Ξ£ S) β Ob π§ β Ob π§ β π₯ Μ
 hom (X , homX , idX , compX) = homX

 πΎπΉ : (π§ : Ξ£ S) (x : Ob π§) β hom π§ x x
 πΎπΉ (X , homX , idX , compX) = idX

 comp : (π§ : Ξ£ S) (x y z : Ob π§) β hom π§ x y β hom π§ y z β hom π§ x z
 comp (X , homX , idX , compX) = compX

 functorial : (π§ π : Ξ£ S)
            β (F : Ob π§ β Ob π)
            β ((x y : Ob π§) β hom π§ x y β hom π (F x) (F y))
            β π€ β π₯ Μ

 functorial π§ π F π' = pidentity Γ pcomposition
  where

   _o_ : {x y z : Ob π§} β hom π§ y z β hom π§ x y β hom π§ x z
   g o f = comp π§ _ _ _ f g

   _β‘_ : {a b c : Ob π} β hom π b c β hom π a b β hom π a c
   g β‘ f = comp π _ _ _ f g

   π : {x y : Ob π§} β hom π§ x y β hom π (F x) (F y)
   π f = π' _ _ f

   pidentity = (Ξ» x β π (πΎπΉ π§ x)) β‘ (Ξ» x β πΎπΉ π (F x))

   pcomposition = (Ξ» x y z (f : hom π§ x y) (g : hom π§ y z) β π (g o f))
                β‘ (Ξ» x y z (f : hom π§ x y) (g : hom π§ y z) β π g β‘ π f)

 sns-data : SNS S (π€ β (π₯ βΊ))
 sns-data = (ΞΉ , Ο , ΞΈ)
  where
   ΞΉ : (π§ π : Ξ£ S) β β¨ π§ β© β β¨ π β© β π€ β (π₯ βΊ) Μ
   ΞΉ π§ π (F , _) = Ξ£ p κ hom π§ β‘ (Ξ» x y β hom π (F x) (F y))
                       , functorial π§ π F (Ξ» x y β transport (Ξ» - β - x y) p)

   Ο : (π§ : Ξ£ S) β ΞΉ π§ π§ (id-β β¨ π§ β©)
   Ο π§ = refl (hom π§) , refl (πΎπΉ π§) , refl (comp π§)

   ΞΈ : {X : π€ Μ } (s t : S X) β is-equiv (canonical-map ΞΉ Ο s t)
   ΞΈ {X} (homX , idX , compX) (homA , idA , compA) = g
    where
     Ο = canonical-map ΞΉ Ο (homX , idX , compX) (homA , idA , compA)

     Ξ³ : codomain Ο β domain Ο
     Ξ³ (refl _ , refl _ , refl _) = refl _

     Ξ· : Ξ³ β Ο βΌ id
     Ξ· (refl _) = refl _

     Ξ΅ : Ο β Ξ³ βΌ id
     Ξ΅ (refl _ , refl _ , refl _) = refl _

     g : is-equiv Ο
     g = invertibles-are-equivs Ο (Ξ³ , Ξ· , Ξ΅)

 lemma : (π§ π : Ξ£ S) (F : Ob π§ β Ob π)
       β
         (Ξ£ p κ hom π§ β‘ (Ξ» x y β hom π (F x) (F y))
              , functorial π§ π F (Ξ» x y β transport (Ξ» - β - x y) p))
       β
         (Ξ£ π κ ((x y : Ob π§) β hom π§ x y β hom π (F x) (F y))
              , (β x y β is-equiv (π x y))
              Γ functorial π§ π F π)

 lemma π§ π F = Ξ³
  where
   e = (hom π§ β‘ Ξ» x y β hom π (F x) (F y))                            ββ¨ i β©
       (β x y β hom π§ x y β‘ hom π (F x) (F y))                        ββ¨ ii β©
       (β x y β hom π§ x y β hom π (F x) (F y))                        ββ¨ iii β©
       (β x β Ξ£ Ο κ (β y β hom π§ x y β hom π (F x) (F y))
                  , β y β is-equiv (Ο y))                             ββ¨ iv β©
       (Ξ£ π κ ((x y : Ob π§) β hom π§ x y β hom π (F x) (F y))
            , (β x y β is-equiv (π x y)))                             β 
    where
     i   = hfunextβ-β hfe hfe (hom π§ )  Ξ» x y β hom π (F x) (F y)
     ii  = Ξ -cong fe fe
            (Ξ» x β Ξ -cong fe fe
            (Ξ» y β univalence-β (ua π₯) (hom π§ x y) (hom π (F x) (F y))))
     iii = Ξ -cong fe fe (Ξ» y β Ξ Ξ£-distr-β)
     iv  = Ξ Ξ£-distr-β

   v : (p : hom π§ β‘ Ξ» x y β hom π (F x) (F y))
     β functorial π§ π F (Ξ» x y β transport (Ξ» - β - x y) p)
     β functorial π§ π F (prβ (β e β p))

   v (refl _) = id-β _

   Ξ³ =

    (Ξ£ p κ hom π§ β‘ (Ξ» x y β hom π (F x) (F y))
         , functorial π§ π F (Ξ» x y β transport (Ξ» - β - x y) p)) ββ¨ vi β©

    (Ξ£ p κ hom π§ β‘ (Ξ» x y β hom π (F x) (F y))
         , functorial π§ π F (prβ (β e β p)))                     ββ¨ vii β©

    (Ξ£ Ο κ (Ξ£ π κ ((x y : Ob π§) β hom π§ x y β hom π (F x) (F y))
                , (β x y β is-equiv (π x y)))
         , functorial π§ π F (prβ Ο))                             ββ¨ viii β©

    (Ξ£ π κ ((x y : Ob π§) β hom π§ x y β hom π (F x) (F y))
                  , (β x y β is-equiv (π x y))
                  Γ functorial π§ π F π)                          β 
    where
     vi   = Ξ£-cong v
     vii  = β-sym (Ξ£-change-of-variable _ β e β (ββ-is-equiv e))
     viii = Ξ£-assoc

 characterization-of-type-valued-preorder-β‘ :

      (π§ π : Ξ£ S)
    β
      (π§ β‘ π)
    β
      (Ξ£ F κ (Ob π§ β Ob π)
           , is-equiv F
           Γ (Ξ£ π κ ((x y : Ob π§) β hom π§ x y β hom π (F x) (F y))
                  , (β x y β is-equiv (π x y))
                  Γ functorial π§ π F π))

 characterization-of-type-valued-preorder-β‘ π§ π =

   (π§ β‘ π)                                                              ββ¨ i β©
   (Ξ£ F κ (Ob π§ β Ob π)
        , is-equiv F
        Γ (Ξ£ p κ hom π§ β‘ (Ξ» x y β hom π (F x) (F y))
               , functorial π§ π F (Ξ» x y β transport (Ξ» - β - x y) p))) ββ¨ ii β©
   (Ξ£ F κ (Ob π§ β Ob π)
     , is-equiv F
     Γ (Ξ£ π κ ((x y : Ob π§) β hom π§ x y β hom π (F x) (F y))
            , (β x y β is-equiv (π x y))
            Γ functorial π§ π F π))                                      β 

  where
   i  = characterization-of-β‘ (ua π€) sns-data π§ π
   ii = Ξ£-cong (Ξ» F β Ξ£-cong (Ξ» _ β lemma π§ π F))

module type-valued-preorder-with-axioms
        (π€ π₯ π¦ : Universe)
        (ua : Univalence)
        (axioms  : (X : π€ Μ ) β type-valued-preorder-S {π€} {π₯} X β π¦ Μ )
        (axiomss : (X : π€ Μ ) (s : type-valued-preorder-S X) β is-subsingleton (axioms X s))
       where

 open sip
 open sip-with-axioms
 open type-valued-preorder π€ π₯ ua

 S' : π€ Μ β π€ β (π₯ βΊ) β π¦ Μ
 S' X = Ξ£ s κ S X , axioms X s

 sns-data' : SNS S' (π€ β (π₯ βΊ))
 sns-data' = add-axioms axioms axiomss sns-data

 characterization-of-type-valued-preorder-β‘-with-axioms :

      (π§' π' : Ξ£ S')
    β
      (π§' β‘ π')
    β
      (Ξ£ F κ (Ob [ π§' ] β Ob [ π' ])
           , is-equiv F
           Γ (Ξ£ π κ ((x y : Ob [ π§' ]) β hom [ π§' ] x y β hom [ π' ] (F x) (F y))
                    , (β x y β is-equiv (π x y))
                    Γ functorial [ π§' ] [ π' ] F π))

 characterization-of-type-valued-preorder-β‘-with-axioms π§' π' =

  (π§' β‘ π')                     ββ¨ i β©
  ([ π§' ] β[ sns-data ] [ π' ]) ββ¨ ii β©
  _                              β 

  where
   i  = characterization-of-β‘-with-axioms (ua π€) sns-data axioms axiomss π§' π'
   ii = Ξ£-cong (Ξ» F β Ξ£-cong (Ξ» _ β lemma [ π§' ] [ π' ] F))

module category
        (π€ π₯ : Universe)
        (ua : Univalence)
       where

 open type-valued-preorder-with-axioms π€ π₯ (π€ β π₯) ua

 fe : global-dfunext
 fe = univalence-gives-global-dfunext ua

 S : π€ Μ β π€ β (π₯ βΊ) Μ
 S = type-valued-preorder-S {π€} {π₯}

 category-axioms : (X : π€ Μ ) β S X β π€ β π₯ Μ
 category-axioms X (homX , idX , compX) = hom-sets Γ identityl Γ identityr Γ associativity
  where
   _o_ : {x y z : X} β homX y z β homX x y β homX x z
   g o f = compX _ _ _ f g

   hom-sets      = β x y β is-set (homX x y)

   identityl     = β x y (f : homX x y) β f o (idX x) β‘ f

   identityr     = β x y (f : homX x y) β (idX y) o f β‘ f

   associativity = β x y z t (f : homX x y) (g : homX y z) (h : homX z t)
                 β (h o g) o f β‘ h o (g o f)

 category-axioms-subsingleton : (X : π€ Μ ) (s : S X) β is-subsingleton (category-axioms X s)
 category-axioms-subsingleton X (homX , idX , compX) ca = Ξ³ ca
  where
   i : β x y β is-set (homX x y)
   i = prβ ca

   Ξ³ : is-subsingleton (category-axioms X (homX , idX , compX))
   Ξ³ = Γ-is-subsingleton ss (Γ-is-subsingleton ls (Γ-is-subsingleton rs as))
    where
     ss = Ξ -is-subsingleton fe
           (Ξ» x β Ξ -is-subsingleton fe
           (Ξ» y β being-set-is-subsingleton fe))

     ls = Ξ -is-subsingleton fe
           (Ξ» x β Ξ -is-subsingleton fe
           (Ξ» y β Ξ -is-subsingleton fe
           (Ξ» f β i x y (compX x x y (idX x) f) f)))

     rs = Ξ -is-subsingleton fe
           (Ξ» x β Ξ -is-subsingleton fe
           (Ξ» y β Ξ -is-subsingleton fe
           (Ξ» f β i x y (compX x y y f (idX y)) f)))

     as = Ξ -is-subsingleton fe
           (Ξ» x β Ξ -is-subsingleton fe
           (Ξ» y β Ξ -is-subsingleton fe
           (Ξ» z β Ξ -is-subsingleton fe
           (Ξ» t β Ξ -is-subsingleton fe
           (Ξ» f β Ξ -is-subsingleton fe
           (Ξ» g β Ξ -is-subsingleton fe
           (Ξ» h β i x t (compX x y t f (compX y z t g h))
                        (compX x z t (compX x y z f g) h))))))))

 Cat : (π€ β π₯)βΊ Μ
 Cat = Ξ£ X κ π€ Μ , Ξ£ s κ S X , category-axioms X s

 Ob : Cat β π€ Μ
 Ob (X , (homX , idX , compX) , _) = X

 hom : (π§ : Cat) β Ob π§ β Ob π§ β π₯ Μ
 hom (X , (homX , idX , compX) , _) = homX

 πΎπΉ : (π§ : Cat) (x : Ob π§) β hom π§ x x
 πΎπΉ (X , (homX , idX , compX) , _) = idX

 comp : (π§ : Cat) (x y z : Ob π§) (f : hom π§ x y) (g : hom π§ y z) β hom π§ x z
 comp (X , (homX , idX , compX) , _) = compX

 is-functorial : (π§ π : Cat)
               β (F : Ob π§ β Ob π)
               β ((x y : Ob π§) β hom π§ x y β hom π (F x) (F y))
               β π€ β π₯ Μ

 is-functorial π§ π F π' = pidentity Γ pcomposition
  where
   _o_ : {x y z : Ob π§} β hom π§ y z β hom π§ x y β hom π§ x z
   g o f = comp π§ _ _ _ f g

   _β‘_ : {a b c : Ob π} β hom π b c β hom π a b β hom π a c
   g β‘ f = comp π _ _ _ f g

   π : {x y : Ob π§} β hom π§ x y β hom π (F x) (F y)
   π f = π' _ _ f

   pidentity    = (Ξ» x β π (πΎπΉ π§ x)) β‘ (Ξ» x β πΎπΉ π (F x))

   pcomposition = (Ξ» x y z (f : hom π§ x y) (g : hom π§ y z) β π (g o f))
                β‘ (Ξ» x y z (f : hom π§ x y) (g : hom π§ y z) β π g β‘ π f)

 _β_ : Cat β Cat β π€ β π₯ Μ

 π§ β π = Ξ£ F κ (Ob π§ β Ob π)
              , is-equiv F
              Γ (Ξ£ π κ ((x y : Ob π§) β hom π§ x y β hom π (F x) (F y))
                     , (β x y β is-equiv (π x y))
                     Γ is-functorial π§ π F π)

 IdβEqCat : (π§ π : Cat) β π§ β‘ π β π§ β π
 IdβEqCat π§ π§ (refl π§) = ππ (Ob π§ ) ,
                         id-is-equiv (Ob π§ ) ,
                         (Ξ» x y β ππ (hom π§ x y)) ,
                         (Ξ» x y β id-is-equiv (hom π§ x y)) ,
                         refl (πΎπΉ π§) ,
                         refl (comp π§)

 characterization-of-category-β‘ : (π§ π : Cat) β (π§ β‘ π) β (π§ β π)
 characterization-of-category-β‘ = characterization-of-type-valued-preorder-β‘-with-axioms
                                   category-axioms category-axioms-subsingleton

 IdβEqCat-is-equiv : (π§ π : Cat) β is-equiv (IdβEqCat π§ π)
 IdβEqCat-is-equiv π§ π = equivs-closed-under-βΌ
                           (ββ-is-equiv (characterization-of-category-β‘ π§ π))
                           (Ξ³ π§ π)
  where
   Ξ³ : (π§ π : Cat) β IdβEqCat π§ π βΌ β characterization-of-category-β‘ π§ π β
   Ξ³ π§ π§ (refl π§) = refl _

module ring {π€ : Universe} (ua : Univalence) where
 open sip hiding (β¨_β©)
 open sip-with-axioms
 open sip-join

 fe : global-dfunext
 fe = univalence-gives-global-dfunext ua

 hfe : global-hfunext
 hfe = univalence-gives-global-hfunext ua

 rng-structure : π€ Μ β π€ Μ
 rng-structure X = (X β X β X) Γ (X β X β X)

 rng-axioms : (R : π€ Μ ) β rng-structure R β π€ Μ
 rng-axioms R (_+_ , _Β·_) = I Γ II Γ III Γ IV Γ V Γ VI Γ VII
  where
    I   = is-set R
    II  = (x y z : R) β (x + y) + z β‘ x + (y + z)
    III = (x y : R) β x + y β‘ y + x
    IV  = Ξ£ O κ R , ((x : R) β x + O β‘ x) Γ ((x : R) β Ξ£ x' κ R , x + x' β‘ O)
    V   = (x y z : R) β (x Β· y) Β· z β‘ x Β· (y Β· z)
    VI  = (x y z : R) β x Β· (y + z) β‘ (x Β· y) + (x Β· z)
    VII = (x y z : R) β (y + z) Β· x β‘ (y Β· x) + (z Β· x)

 Rng : π€ βΊ Μ
 Rng = Ξ£ R κ π€ Μ , Ξ£ s κ rng-structure R , rng-axioms R s

 rng-axioms-is-subsingleton : (R : π€ Μ ) (s : rng-structure R)
                            β is-subsingleton (rng-axioms R s)

 rng-axioms-is-subsingleton R (_+_ , _Β·_) (i , ii , iii , iv-vii) = Ξ΄
  where
    A   = Ξ» (O : R) β ((x : R) β x + O β‘ x)
                    Γ ((x : R) β Ξ£ x' κ R , x + x' β‘ O)

    IV  = Ξ£ A

    a : (O O' : R) β ((x : R) β x + O β‘ x) β ((x : R) β x + O' β‘ x) β O β‘ O'
    a O O' f f' = O       β‘β¨ (f' O)β»ΒΉ β©
                 (O + O') β‘β¨ iii O O' β©
                 (O' + O) β‘β¨ f O' β©
                  O'      β

    b : (O : R) β is-subsingleton ((x : R) β x + O β‘ x)
    b O = Ξ -is-subsingleton fe (Ξ» x β i (x + O) x)

    c : (O : R)
      β ((x : R) β x + O β‘ x)
      β (x : R) β is-subsingleton (Ξ£ x' κ R , x + x' β‘ O)
    c O f x (x' , p') (x'' , p'') = to-subtype-β‘ (Ξ» x' β i (x + x') O) r
     where
      r : x' β‘ x''
      r = x'               β‘β¨ (f x')β»ΒΉ β©
          (x' + O)         β‘β¨ ap (x' +_) (p'' β»ΒΉ) β©
          (x' + (x + x'')) β‘β¨ (ii x' x x'')β»ΒΉ β©
          ((x' + x) + x'') β‘β¨ ap (_+ x'') (iii x' x) β©
          ((x + x') + x'') β‘β¨ ap (_+ x'') p' β©
          (O + x'')        β‘β¨ iii O x'' β©
          (x'' + O)        β‘β¨ f x'' β©
          x''              β

    d : (O : R) β is-subsingleton (A O)
    d O (f , g) = Ο (f , g)
     where
      Ο : is-subsingleton (A O)
      Ο = Γ-is-subsingleton (b O) (Ξ -is-subsingleton fe (Ξ» x β c O f x))

    IV-is-subsingleton : is-subsingleton IV
    IV-is-subsingleton (O , f , g) (O' , f' , g') = e
     where
      e : (O , f , g) β‘ (O' , f' , g')
      e = to-subtype-β‘ d (a O O' f f')

    Ξ³ : is-subsingleton (rng-axioms R (_+_ , _Β·_))
    Ξ³ = Γ-is-subsingleton
          (being-set-is-subsingleton fe)
       (Γ-is-subsingleton
          (Ξ -is-subsingleton fe
          (Ξ» x β Ξ -is-subsingleton fe
          (Ξ» y β Ξ -is-subsingleton fe
          (Ξ» z β i ((x + y) + z) (x + (y + z))))))
       (Γ-is-subsingleton
          (Ξ -is-subsingleton fe
          (Ξ» x β Ξ -is-subsingleton fe
          (Ξ» y β i (x + y) (y + x))))
       (Γ-is-subsingleton
          IV-is-subsingleton
       (Γ-is-subsingleton
          (Ξ -is-subsingleton fe
          (Ξ» x β Ξ -is-subsingleton fe
          (Ξ» y β Ξ -is-subsingleton fe
          (Ξ» z β i ((x Β· y) Β· z) (x Β· (y Β· z))))))
       (Γ-is-subsingleton
          (Ξ -is-subsingleton fe
          (Ξ» x β Ξ -is-subsingleton fe
          (Ξ» y β Ξ -is-subsingleton fe
          (Ξ» z β i (x Β· (y + z)) ((x Β· y) + (x Β· z))))))

          (Ξ -is-subsingleton fe
          (Ξ» x β Ξ -is-subsingleton fe
          (Ξ» y β Ξ -is-subsingleton fe
          (Ξ» z β i ((y + z) Β· x) ((y Β· x) + (z Β· x)))))))))))

    Ξ΄ : (Ξ± : rng-axioms R (_+_ , _Β·_)) β (i , ii , iii , iv-vii) β‘ Ξ±
    Ξ΄ = Ξ³ (i , ii , iii , iv-vii)

 _β[Rng]_ : Rng β Rng β π€ Μ

 (R , (_+_ , _Β·_) , _) β[Rng] (R' , (_+'_ , _Β·'_) , _) =

                       Ξ£ f κ (R β R')
                           , is-equiv f
                           Γ ((Ξ» x y β f (x + y)) β‘ (Ξ» x y β f x +' f y))
                           Γ ((Ξ» x y β f (x Β· y)) β‘ (Ξ» x y β f x Β·' f y))

 characterization-of-rng-β‘ : (π‘ π‘' : Rng) β (π‘ β‘ π‘') β (π‘ β[Rng] π‘')
 characterization-of-rng-β‘ = characterization-of-β‘ (ua π€)
                              (add-axioms
                                rng-axioms
                                rng-axioms-is-subsingleton
                                (join
                                  β-magma.sns-data
                                  β-magma.sns-data))

 β¨_β© : (π‘ : Rng) β π€ Μ
 β¨ R , _ β© = R

 ring-structure : π€ Μ β π€ Μ
 ring-structure X = X Γ rng-structure X

 ring-axioms : (R : π€ Μ ) β ring-structure R β π€ Μ
 ring-axioms R (π , _+_ , _Β·_) = rng-axioms R (_+_ , _Β·_) Γ VIII
  where
   VIII = (x : R) β (x Β· π β‘ x) Γ (π Β· x β‘ x)

 ring-axioms-is-subsingleton : (R : π€ Μ ) (s : ring-structure R)
                             β is-subsingleton (ring-axioms R s)

 ring-axioms-is-subsingleton R (π , _+_ , _Β·_) ((i , ii-vii) , viii) = Ξ³ ((i , ii-vii) , viii)
  where
   Ξ³ : is-subsingleton (ring-axioms R (π , _+_ , _Β·_))
   Ξ³ = Γ-is-subsingleton
         (rng-axioms-is-subsingleton R (_+_ , _Β·_))
         (Ξ -is-subsingleton fe (Ξ» x β Γ-is-subsingleton (i (x Β· π) x) (i (π Β· x) x)))

 Ring : π€ βΊ Μ
 Ring = Ξ£ R κ π€ Μ , Ξ£ s κ ring-structure R , ring-axioms R s

 _β[Ring]_ : Ring β Ring β π€ Μ

 (R , (π , _+_ , _Β·_) , _) β[Ring] (R' , (π' , _+'_ , _Β·'_) , _) =

                           Ξ£ f κ (R β R')
                               , is-equiv f
                               Γ (f π β‘ π')
                               Γ ((Ξ» x y β f (x + y)) β‘ (Ξ» x y β f x +' f y))
                               Γ ((Ξ» x y β f (x Β· y)) β‘ (Ξ» x y β f x Β·' f y))

 characterization-of-ring-β‘ : (π‘ π‘' : Ring) β (π‘ β‘ π‘') β (π‘ β[Ring] π‘')
 characterization-of-ring-β‘ = sip.characterization-of-β‘ (ua π€)
                                (sip-with-axioms.add-axioms
                                  ring-axioms
                                  ring-axioms-is-subsingleton
                                  (sip-join.join
                                    pointed-type.sns-data
                                      (join
                                        β-magma.sns-data
                                        β-magma.sns-data)))

 is-commutative : Rng β π€ Μ
 is-commutative (R , (_+_ , _Β·_) , _) = (x y : R) β x Β· y β‘ y Β· x

 being-commutative-is-subsingleton : (π‘ : Rng) β is-subsingleton (is-commutative π‘)
 being-commutative-is-subsingleton (R , (_+_ , _Β·_) , i , ii-vii) =

   Ξ -is-subsingleton fe
   (Ξ» x β Ξ -is-subsingleton fe
   (Ξ» y β i (x Β· y) (y Β· x)))

 is-ideal : (π‘ : Rng) β π β¨ π‘ β© β π€ Μ
 is-ideal (R , (_+_ , _Β·_) , _) I = (x y : R) β (x β I β y β I β (x + y) β I)
                                              Γ (x β I β (x Β· y) β I)
                                              Γ (y β I β (x Β· y) β I)

 is-local : Rng β π€ βΊ Μ
 is-local π‘ = β! I κ π β¨ π‘ β© , (is-ideal π‘ I β (J : π β¨ π‘ β©) β is-ideal π‘ J β J β I)

 being-local-is-subsingleton : (π‘ : Rng) β is-subsingleton (is-local π‘)
 being-local-is-subsingleton π‘ = β!-is-subsingleton _ fe

 module _ (pt : subsingleton-truncations-exist) where

  open basic-truncation-development pt hfe
  open β-order

  is-noetherian : (π‘ : Rng) β π€ βΊ Μ
  is-noetherian π‘ = (I : β β π β¨ π‘ β©)
                  β ((n : β) β is-ideal π‘ (I n))
                  β ((n : β) β I n β I (succ n))
                  β β m κ β , ((n : β) β m β€ n β I m β‘ I n)

  NoetherianRng : π€ βΊ Μ
  NoetherianRng = Ξ£ π‘ κ Rng , is-noetherian π‘

  being-noetherian-is-subsingleton : (π‘ : Rng) β is-subsingleton (is-noetherian π‘)

  being-noetherian-is-subsingleton π‘ = Ξ -is-subsingleton fe
                                       (Ξ» I β Ξ -is-subsingleton fe
                                       (Ξ» _ β Ξ -is-subsingleton fe
                                       (Ξ» _ β β-is-subsingleton)))

  forget-Noether : NoetherianRng β Rng
  forget-Noether (π‘ , _) = π‘

  forget-Noether-is-embedding : is-embedding forget-Noether
  forget-Noether-is-embedding = prβ-embedding being-noetherian-is-subsingleton

  _β[NoetherianRng]_ : NoetherianRng β NoetherianRng β π€ Μ

  ((R , (_+_ , _Β·_) , _) , _) β[NoetherianRng] ((R' , (_+'_ , _Β·'_) , _) , _) =

                              Ξ£ f κ (R β R')
                                  , is-equiv f
                                  Γ ((Ξ» x y β f (x + y)) β‘ (Ξ» x y β f x +' f y))
                                  Γ ((Ξ» x y β f (x Β· y)) β‘ (Ξ» x y β f x Β·' f y))

  NB : (π‘ π‘' : NoetherianRng)
     β (π‘ β[NoetherianRng] π‘') β‘ (forget-Noether π‘ β[Rng] forget-Noether π‘')

  NB π‘ π‘' = refl _

  characterization-of-nrng-β‘ : (π‘ π‘' : NoetherianRng)
                             β (π‘ β‘ π‘') β (π‘ β[NoetherianRng] π‘')

  characterization-of-nrng-β‘ π‘ π‘' =

    (π‘ β‘ π‘')                               ββ¨ i β©
    (forget-Noether π‘ β‘ forget-Noether π‘') ββ¨ ii β©
    (π‘ β[NoetherianRng] π‘')                β 

    where
     i = β-sym (embedding-criterion-converse forget-Noether
                  forget-Noether-is-embedding π‘ π‘')
     ii = characterization-of-rng-β‘ (forget-Noether π‘) (forget-Noether π‘')

  isomorphic-NoetherianRng-transport :

      (A : NoetherianRng β π₯ Μ )
    β (π‘ π‘' : NoetherianRng) β π‘ β[NoetherianRng] π‘' β A π‘ β A π‘'

  isomorphic-NoetherianRng-transport A π‘ π‘' i a = a'
   where
    p : π‘ β‘ π‘'
    p = β β-sym (characterization-of-nrng-β‘ π‘ π‘') β i

    a' : A π‘'
    a' = transport A p a

  is-CNL : Ring β π€ βΊ Μ
  is-CNL (R , (π , _+_ , _Β·_) , i-vii , viii) = is-commutative π‘
                                              Γ is-noetherian π‘
                                              Γ is-local π‘
   where
    π‘ : Rng
    π‘ = (R , (_+_ , _Β·_) , i-vii)

  being-CNL-is-subsingleton : (π‘ : Ring) β is-subsingleton (is-CNL π‘)
  being-CNL-is-subsingleton (R , (π , _+_ , _Β·_) , i-vii , viii) =

     Γ-is-subsingleton (being-commutative-is-subsingleton π‘)
    (Γ-is-subsingleton (being-noetherian-is-subsingleton π‘)
                       (being-local-is-subsingleton π‘))
   where
    π‘ : Rng
    π‘ = (R , (_+_ , _Β·_) , i-vii)

  CNL-Ring : π€ βΊ Μ
  CNL-Ring = Ξ£ π‘ κ Ring , is-CNL π‘

  _β[CNL]_ : CNL-Ring β CNL-Ring β π€ Μ

  ((R , (π , _+_ , _Β·_) , _) , _) β[CNL] ((R' , (π' , _+'_ , _Β·'_) , _) , _) =

                                  Ξ£ f κ (R β R')
                                      , is-equiv f
                                      Γ (f π β‘ π')
                                      Γ ((Ξ» x y β f (x + y)) β‘ (Ξ» x y β f x +' f y))
                                      Γ ((Ξ» x y β f (x Β· y)) β‘ (Ξ» x y β f x Β·' f y))

  forget-CNL : CNL-Ring β Ring
  forget-CNL (π‘ , _) = π‘

  forget-CNL-is-embedding : is-embedding forget-CNL
  forget-CNL-is-embedding = prβ-embedding being-CNL-is-subsingleton

  NB' : (π‘ π‘' : CNL-Ring)
      β (π‘ β[CNL] π‘') β‘ (forget-CNL π‘ β[Ring] forget-CNL π‘')

  NB' π‘ π‘' = refl _

  characterization-of-CNL-ring-β‘ : (π‘ π‘' : CNL-Ring)
                                 β (π‘ β‘ π‘') β (π‘ β[CNL] π‘')

  characterization-of-CNL-ring-β‘ π‘ π‘' =

     (π‘ β‘ π‘')                               ββ¨ i β©
     (forget-CNL π‘ β‘ forget-CNL π‘')         ββ¨ ii β©
     (π‘ β[CNL] π‘')                          β 

     where
      i = β-sym (embedding-criterion-converse forget-CNL
                   forget-CNL-is-embedding π‘ π‘')
      ii = characterization-of-ring-β‘ (forget-CNL π‘) (forget-CNL π‘')

  isomorphic-CNL-Ring-transport :

      (A : CNL-Ring β π₯ Μ )
    β (π‘ π‘' : CNL-Ring) β π‘ β[CNL] π‘' β A π‘ β A π‘'

  isomorphic-CNL-Ring-transport A π‘ π‘' i a = a'
   where
    p : π‘ β‘ π‘'
    p = β β-sym (characterization-of-CNL-ring-β‘ π‘ π‘') β i

    a' : A π‘'
    a' = transport A p a

\end{code}
