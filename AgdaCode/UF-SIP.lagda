Martin Escardo, 30 April 2020

The structure identity principle and tools from

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html
 https://arxiv.org/abs/1911.00580
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

There are three submodules:

 * sip
 * sip-with-axioms
 * sip-join

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-SIP where

open import SpartanMLTT
open import UF-Base
open import UF-Equiv hiding (_β_)
open import UF-Univalence
open import UF-EquivalenceExamples
open import UF-Subsingletons
open import UF-Embeddings
open import UF-Yoneda
open import UF-Retracts


module sip where

 β¨_β© : {S : π€ Μ β π₯ Μ } β Ξ£ S β π€ Μ
 β¨ X , s β© = X

 structure : {S : π€ Μ β π₯ Μ } (A : Ξ£ S) β S β¨ A β©
 structure (X , s) = s

 canonical-map : {S : π€ Μ β π₯ Μ }
                 (ΞΉ : (A B : Ξ£ S) β β¨ A β© β β¨ B β© β π¦ Μ )
                 (Ο : (A : Ξ£ S) β ΞΉ A A (β-refl β¨ A β©))
                 {X : π€ Μ }
                 (s t : S X)
               β s β‘ t β ΞΉ (X , s) (X , t) (β-refl X)
 canonical-map ΞΉ Ο {X} s s (refl {s}) = Ο (X , s)

 SNS : (π€ Μ β π₯ Μ ) β (π¦ : Universe) β π€ βΊ β π₯ β (π¦ βΊ) Μ
 SNS {π€} {π₯} S π¦ = Ξ£ ΞΉ κ ((A B : Ξ£ S) β (β¨ A β© β β¨ B β© β π¦ Μ ))
                  , Ξ£ Ο κ ((A : Ξ£ S) β ΞΉ A A (β-refl β¨ A β©))
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
 IdβhomEq (_ , Ο , _) A A (refl {A}) = id , id-is-equiv β¨ A β© , Ο A

 homomorphism-lemma : {S : π€ Μ β π₯ Μ } (Ο : SNS S π¦)
                      (A B : Ξ£ S) (p : β¨ A β© β‘ β¨ B β©)
                    β
                      (transport S p (structure A) β‘ structure B)
                    β  homomorphic Ο A B (idtoeq β¨ A β© β¨ B β© p)
 homomorphism-lemma (ΞΉ , Ο , ΞΈ) (X , s) (X , t) (refl {X}) = Ξ³
  where
   Ξ³ : (s β‘ t) β ΞΉ (X , s) (X , t) (β-refl X)
   Ξ³ = (canonical-map ΞΉ Ο s t , ΞΈ s t)

 characterization-of-β‘ : is-univalent π€
                       β {S : π€ Μ β π₯ Μ } (Ο : SNS S π¦)
                       β (A B : Ξ£ S)

                       β (A β‘ B) β (A β[ Ο ] B)
 characterization-of-β‘ ua {S} Ο A B =
    (A β‘ B)                                                           ββ¨ i β©
    (Ξ£ p κ β¨ A β© β‘ β¨ B β© , transport S p (structure A) β‘ structure B) ββ¨ ii β©
    (Ξ£ p κ β¨ A β© β‘ β¨ B β© , ΞΉ A B (idtoeq β¨ A β© β¨ B β© p))               ββ¨ iii β©
    (Ξ£ e κ β¨ A β© β β¨ B β© , ΞΉ A B e)                                   ββ¨ iv β©
    (A β[ Ο ] B)                                                      β 
  where
   ΞΉ   = homomorphic Ο
   i   = Ξ£-β‘-β
   ii  = Ξ£-cong (homomorphism-lemma Ο A B)
   iii = Ξ£-change-of-variable (ΞΉ A B) (idtoeq β¨ A β© β¨ B β©) (ua β¨ A β© β¨ B β©)
   iv  = Ξ£-assoc

 IdβhomEq-is-equiv : (ua : is-univalent π€) {S : π€ Μ β π₯ Μ } (Ο : SNS S π¦)
                   β (A B : Ξ£ S) β is-equiv (IdβhomEq Ο A B)
 IdβhomEq-is-equiv ua {S} Ο A B = Ξ³
  where
   h : (A B : Ξ£ S) β IdβhomEq Ο A B βΌ β characterization-of-β‘ ua Ο A B β
   h A A (refl {A}) = refl

   Ξ³ : is-equiv (IdβhomEq Ο A B)
   Ξ³ = equiv-closed-under-βΌ _ _
        (ββ-is-equiv (characterization-of-β‘ ua Ο A B))
        (h A B)

 module _ {S : π€ Μ β π₯ Μ }
          (ΞΉ : (A B : Ξ£ S) β β¨ A β© β β¨ B β© β π¦ Μ )
          (Ο : (A : Ξ£ S) β ΞΉ A A (β-refl β¨ A β©))
          {X : π€ Μ }
        where

  canonical-map-charac : (s t : S X) (p : s β‘ t)
                       β canonical-map ΞΉ Ο s t p
                       β‘ transport (Ξ» - β ΞΉ (X , s) (X , -) (β-refl X)) p (Ο (X , s))
  canonical-map-charac s t p = (yoneda-lemma s (Ξ» t β ΞΉ (X , s) (X , t) (β-refl X)) (canonical-map ΞΉ Ο s) t p)β»ΒΉ

  when-canonical-map-is-equiv : ((s t : S X) β is-equiv (canonical-map ΞΉ Ο s t))
                              β ((s : S X) β β! t κ S X , ΞΉ (X , s) (X , t) (β-refl X))
  when-canonical-map-is-equiv = (Ξ» e s β Yoneda-Theorem-back  s (Ο s) (e s)) ,
                                (Ξ» Ο s β Yoneda-Theorem-forth s (Ο s) (Ο s))
   where
    A = Ξ» s t β ΞΉ (X , s) (X , t) (β-refl X)
    Ο = canonical-map ΞΉ Ο

  canonical-map-equiv-criterion : ((s t : S X) β (s β‘ t) β ΞΉ (X , s) (X , t) (β-refl X))
                                β (s t : S X) β is-equiv (canonical-map ΞΉ Ο s t)
  canonical-map-equiv-criterion Ο s = fiberwise-equiv-criterion'
                                       (Ξ» t β ΞΉ (X , s) (X , t) (β-refl X))
                                       s (Ο s) (canonical-map ΞΉ Ο s)

  canonical-map-equiv-criterion' : ((s t : S X) β ΞΉ (X , s) (X , t) (β-refl X) β (s β‘ t))
                                 β (s t : S X) β is-equiv (canonical-map ΞΉ Ο s t)
  canonical-map-equiv-criterion' Ο s = fiberwise-equiv-criterion
                                        (Ξ» t β ΞΉ (X , s) (X , t) (β-refl X))
                                        s (Ο s) (canonical-map ΞΉ Ο s)


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
            β ((X : π€ Μ ) (s : S X) β is-prop (axioms X s))
            β SNS S π£
            β SNS (Ξ» X β Ξ£ s κ S X , axioms X s) π£
 add-axioms {π€} {π₯} {π¦} {π£} {S} axioms i (ΞΉ , Ο , ΞΈ) = ΞΉ' , Ο' , ΞΈ'
  where
   S' : π€ Μ β π₯ β π¦  Μ
   S' X = Ξ£ s κ S X , axioms X s

   ΞΉ' : (A B : Ξ£ S') β β¨ A β© β β¨ B β© β π£ Μ
   ΞΉ' A B = ΞΉ [ A ] [ B ]

   Ο' : (A : Ξ£ S') β ΞΉ' A A (β-refl β¨ A β©)
   Ο' A = Ο [ A ]

   ΞΈ' : {X : π€ Μ } (s' t' : S' X) β is-equiv (canonical-map ΞΉ' Ο' s' t')
   ΞΈ' {X} (s , a) (t , b) = Ξ³
    where
     Ο : S' X β S X
     Ο (s , _) = s

     j : is-embedding Ο
     j = prβ-is-embedding (i X)

     k : {s' t' : S' X} β is-equiv (ap Ο {s'} {t'})
     k {s'} {t'} = embedding-embedding' Ο j s' t'

     l : canonical-map ΞΉ' Ο' (s , a) (t , b)
       βΌ canonical-map ΞΉ Ο s t β ap Ο {s , a} {t , b}

     l (refl {s , a}) = π»π?π»π΅ (Ο (X , s))

     e : is-equiv (canonical-map ΞΉ Ο s t β ap Ο {s , a} {t , b})
     e = β-is-equiv k (ΞΈ s t)

     Ξ³ : is-equiv (canonical-map ΞΉ' Ο' (s , a) (t , b))
     Ξ³ = equiv-closed-under-βΌ _ _ e l

 characterization-of-β‘-with-axioms :
     is-univalent π€
   β {S : π€ Μ β π₯ Μ }
     (Ο : SNS S π£)
     (axioms : (X : π€ Μ ) β S X β π¦ Μ )
   β ((X : π€ Μ ) (s : S X) β is-prop (axioms X s))
   β (A B : Ξ£ X κ π€ Μ , Ξ£ s κ S X , axioms X s)
   β (A β‘ B) β ([ A ] β[ Ο ] [ B ])
 characterization-of-β‘-with-axioms ua Ο axioms i =
   characterization-of-β‘ ua (add-axioms axioms i Ο)


module sip-join where

 technical-lemma :

     {X : π€ Μ } {A : X β X β π₯ Μ }
     {Y : π¦ Μ } {B : Y β Y β π£ Μ }
     (f : (xβ xβ : X) β xβ β‘ xβ β A xβ xβ)
     (g : (yβ yβ : Y) β yβ β‘ yβ β B yβ yβ)
   β ((xβ xβ : X) β is-equiv (f xβ xβ))
   β ((yβ yβ : Y) β is-equiv (g yβ yβ))

   β (zβ zβ : X Γ Y) β is-equiv (Ξ» (p : zβ β‘ zβ) β f (prβ zβ) (prβ zβ) (ap prβ p) ,
                                                   g (prβ zβ) (prβ zβ) (ap prβ p))

 technical-lemma {π€} {π₯} {π¦} {π£} {X} {A} {Y} {B} f g i j (xβ , yβ) = Ξ³
  where
   module _ (zβ : X Γ Y) where
     xβ = prβ zβ
     yβ = prβ zβ

     r : (xβ , yβ) β‘ (xβ , yβ) β A xβ xβ Γ B yβ yβ
     r p = f xβ xβ (ap prβ p) , g yβ yβ (ap prβ p)

     f' : (a : A xβ xβ) β xβ β‘ xβ
     f' = inverse (f xβ xβ) (i xβ xβ)

     g' : (b : B yβ yβ) β yβ β‘ yβ
     g' = inverse (g yβ yβ) (j yβ yβ)

     s : A xβ xβ Γ B yβ yβ β (xβ , yβ) β‘ (xβ , yβ)
     s (a , b) = to-Γ-β‘ (f' a) (g' b)

     Ξ· : (c : A xβ xβ Γ B yβ yβ) β r (s c) β‘ c
     Ξ· (a , b) =
       r (s (a , b))                              β‘β¨ refl β©
       r (to-Γ-β‘  (f' a) (g' b))                  β‘β¨ refl β©
       (f xβ xβ (ap prβ (to-Γ-β‘ (f' a) (g' b))) ,
        g yβ yβ (ap prβ (to-Γ-β‘ (f' a) (g' b))))  β‘β¨ ii β©
       (f xβ xβ (f' a) , g yβ yβ (g' b))          β‘β¨ iii β©
       a , b                                      β
      where
       ii  = apβ (Ξ» p q β f xβ xβ p , g yβ yβ q)
                 (ap-prβ-to-Γ-β‘ (f' a) (g' b))
                 (ap-prβ-to-Γ-β‘ (f' a) (g' b))
       iii = to-Γ-β‘ (inverses-are-sections (f xβ xβ) (i xβ xβ) a)
                    (inverses-are-sections (g yβ yβ) (j yβ yβ) b)

   Ξ³ : β zβ β is-equiv (r zβ)
   Ξ³ = nats-with-sections-are-equivs (xβ , yβ) r Ξ» zβ β (s zβ , Ξ· zβ)

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

   Ο : (A : Ξ£ S) β ΞΉ A A (β-refl β¨ A β©)
   Ο A = (Οβ [ A ]β , Οβ [ A ]β)

   ΞΈ : {X : π€ Μ } (s t : S X) β is-equiv (canonical-map ΞΉ Ο s t)
   ΞΈ {X} (sβ , sβ) (tβ , tβ) = Ξ³
    where
     c : (p : sβ , sβ β‘ tβ , tβ) β ΞΉβ (X , sβ) (X , tβ) (β-refl X)
                                 Γ ΞΉβ (X , sβ) (X , tβ) (β-refl X)

     c p = (canonical-map ΞΉβ Οβ sβ tβ (ap prβ p) ,
            canonical-map ΞΉβ Οβ sβ tβ (ap prβ p))

     i : is-equiv c
     i = technical-lemma
          (canonical-map ΞΉβ Οβ)
          (canonical-map ΞΉβ Οβ)
          ΞΈβ ΞΈβ (sβ , sβ) (tβ , tβ)

     e : canonical-map ΞΉ Ο (sβ , sβ) (tβ , tβ) βΌ c
     e (refl {sβ , sβ}) = π»π?π»π΅ (Οβ (X , sβ) , Οβ (X , sβ))

     Ξ³ : is-equiv (canonical-map ΞΉ Ο (sβ , sβ) (tβ , tβ))
     Ξ³ = equiv-closed-under-βΌ _ _ i e

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

\end{code}
