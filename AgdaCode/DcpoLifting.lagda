Tom de Jong, 27 May 2019.
Refactored 29 April 2020.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

open import UF-FunExt
open import UF-PropTrunc
open import UF-Subsingletons

module DcpoLifting
        (pt : propositional-truncations-exist)
        (fe : ā {š¤ š„} ā funext š¤ š„)
        (š£ : Universe)
        (pe : propext š£)
       where

open PropositionalTruncation pt

open import UF-Equiv

open import UF-Miscelanea
open import UF-Subsingletons-FunExt

open import UF-ImageAndSurjection
open ImageAndSurjection pt

open import Lifting š£ hiding (ā„)
open import LiftingMiscelanea š£
open import LiftingMiscelanea-PropExt-FunExt š£ pe fe
open import LiftingMonad š£

open import Dcpo pt fe š£ -- hiding (ā„)
open import DcpoMiscelanea pt fe š£

open import Poset fe

module _ {š¤ : Universe}
         {X : š¤ Ģ }
         (s : is-set X)
       where

 family-value-map : {I : š£ Ģ}
                  ā (Ī± : I ā š X)
                  ā (Ī£ i ź I , is-defined (Ī± i)) ā X
 family-value-map Ī± (i , d) = value (Ī± i) d

 directed-family-value-map-is-wconstant : {I : š£ Ģ  }
                                        ā (Ī± : I ā š X)
                                        ā (Ī“ : is-directed _ā'_ Ī± )
                                        ā wconstant (family-value-map Ī±)
 directed-family-value-map-is-wconstant {I} Ī± Ī“ (iā , dā) (iā , dā) =
  Ī³ (semidirected-if-directed _ā'_ Ī± Ī“ iā iā)
   where
    f : (Ī£ i ź I , is-defined (Ī± i)) ā X
    f = family-value-map Ī±
    Ī³ : (ā k ź I , (Ī± iā ā' Ī± k) Ć (Ī± iā ā' Ī± k)) ā f (iā , dā) ā” f (iā , dā)
    Ī³ = ā„ā„-rec s g
     where
      g : (Ī£ k ź I , (Ī± iā ā' Ī± k)
                   Ć (Ī± iā ā' Ī± k)) ā f (iā , dā) ā” f (iā , dā)
      g (k , l , m) =
       f (iā , dā)                             ā”āØ refl ā©
       value (Ī± iā) dā                         ā”āØ ā”-of-values-from-ā” (l dā) ā©
       value (Ī± k) (ā”-to-is-defined (l dā) dā) ā”āØ ā”-of-values-from-ā” ((m dā) ā»Ā¹) ā©
       value (Ī± iā) dā                         ā”āØ refl ā©
       f (iā , dā)                             ā

 lifting-sup-value : {I : š£ Ģ}
                   ā (Ī± : I ā š X)
                   ā (Ī“ : is-directed _ā'_ Ī± )
                   ā (ā i ź I , is-defined (Ī± i)) ā X
 lifting-sup-value {I} Ī± Ī“ =
  prā (wconstant-map-to-set-factors-through-truncation-of-domain
        s (family-value-map Ī±)
        (directed-family-value-map-is-wconstant Ī± Ī“))

 lifting-sup : {I : š£ Ģ} ā (Ī± : I ā š X) ā (Ī“ : is-directed _ā'_ Ī±) ā š X
 lifting-sup {I} Ī± Ī“ =
  (ā i ź I , is-defined (Ī± i)) , lifting-sup-value Ī± Ī“ , ā„ā„-is-prop

 lifting-sup-is-upperbound : {I : š£ Ģ} ā (Ī± : I ā š X)
                             (Ī“ : is-directed _ā'_ Ī±)
                           ā (i : I) ā Ī± i ā' lifting-sup Ī± Ī“
 lifting-sup-is-upperbound {I} Ī± Ī“ i = Ī³
  where
   Ī³ : Ī± i ā' lifting-sup Ī± Ī“
   Ī³ = ā-to-ā' (f , v)
    where
     f : is-defined (Ī± i) ā is-defined (lifting-sup Ī± Ī“)
     f d = ā£ i , d ā£
     v : (d : is-defined (Ī± i)) ā value (Ī± i) d ā” value (lifting-sup Ī± Ī“) (f d)
     v d = value (Ī± i) d                 ā”āØ p    ā©
           lifting-sup-value Ī± Ī“ (f d)   ā”āØ refl ā©
           value (lifting-sup Ī± Ī“) (f d) ā
      where
       p = (prā (wconstant-map-to-set-factors-through-truncation-of-domain
                  s (family-value-map Ī±)
                  (directed-family-value-map-is-wconstant Ī± Ī“)))
           (i , d)

 family-defined-somewhere-sup-ā” : {I : š£ Ģ} {Ī± : I ā š X}
                                ā (Ī“ : is-directed _ā'_ Ī±)
                                ā (i : I)
                                ā is-defined (Ī± i)
                                ā Ī± i ā” lifting-sup Ī± Ī“
 family-defined-somewhere-sup-ā” {I} {Ī±} Ī“ i d =
  (lifting-sup-is-upperbound Ī± Ī“ i) d

 lifting-sup-is-lowerbound-of-upperbounds : {I : š£ Ģ}
                                          ā {Ī± : I ā š X}
                                          ā (Ī“ : is-directed _ā'_ Ī±)
                                          ā (v : š X)
                                          ā ((i : I) ā Ī± i ā' v)
                                          ā lifting-sup Ī± Ī“ ā' v
 lifting-sup-is-lowerbound-of-upperbounds {I} {Ī±} Ī“ v b = h
  where
   h : lifting-sup Ī± Ī“ ā' v
   h d = ā„ā„-rec (lifting-of-set-is-set s) g d
    where
     g : (Ī£ i ź I , is-defined (Ī± i)) ā lifting-sup Ī± Ī“ ā” v
     g (i , dįµ¢) = lifting-sup Ī± Ī“ ā”āØ (family-defined-somewhere-sup-ā” Ī“ i dįµ¢) ā»Ā¹ ā©
                  Ī± i             ā”āØ b i dįµ¢ ā©
                  v               ā

 š-DCPO : DCPO {š£ āŗ ā š¤} {š£ āŗ ā š¤}
 š-DCPO = š X , _ā'_ , pa , c
  where
   pa : PosetAxioms.poset-axioms _ā'_
   pa = sl , p , r , t , a
    where
     open PosetAxioms {_} {_} {š X} _ā'_
     sl : is-set (š X)
     sl = lifting-of-set-is-set s
     p : is-prop-valued
     p _ _ = ā'-prop-valued s
     r : is-reflexive
     r _ = ā'-is-reflexive
     a : is-antisymmetric
     a _ _ = ā'-is-antisymmetric
     t : is-transitive
     t _ _ _ = ā'-is-transitive
   c : (I : š£ Ģ ) (Ī± : I ā š X) ā is-directed _ā'_ Ī± ā has-sup _ā'_ Ī±
   c I Ī± Ī“ = lifting-sup Ī± Ī“ ,
             lifting-sup-is-upperbound Ī± Ī“ ,
             lifting-sup-is-lowerbound-of-upperbounds Ī“

 š-DCPOā„ : DCPOā„ {š£ āŗ ā š¤} {š£ āŗ ā š¤}
 š-DCPOā„ = š-DCPO , l , (Ī» _ ā unique-from-š)
  where
   l : š X
   l = (š , š-elim , š-is-prop)

\end{code}

Now that we have the lifting as a dcpo, we prove that the lifting functor and
Kleisli extension yield continuous maps.

\begin{code}

module _ {š¤ : Universe}
         {X : š¤ Ģ }
         (sā : is-set X)
         {š„ : Universe}
         {Y : š„ Ģ }
         (sā : is-set Y)
       where

 āÆ-is-monotone : (f : X ā š Y) ā is-monotone (š-DCPO sā) (š-DCPO sā) (f āÆ)
 āÆ-is-monotone f l m ineq d = ap (f āÆ) (ineq (āÆ-is-defined f l d))

 āÆ-is-continuous : (f : X ā š Y) ā is-continuous (š-DCPO sā) (š-DCPO sā) (f āÆ)
 āÆ-is-continuous f I Ī± Ī“ = u , v
  where
   u : (i : I) ā (f āÆ) (Ī± i) āāØ (š-DCPO sā) ā© (f āÆ) (ā (š-DCPO sā) Ī“)
   u i = āÆ-is-monotone f (Ī± i) (ā (š-DCPO sā) Ī“)
         (ā-is-upperbound (š-DCPO sā) Ī“ i)
   v : (m : āØ š-DCPO sā ā©)
     ā ((i : I) ā (f āÆ) (Ī± i) āāØ (š-DCPO sā) ā© m)
     ā (f āÆ) (ā (š-DCPO sā) Ī“) āāØ (š-DCPO sā) ā© m
   v m ineqs d =
    ā„ā„-rec (lifting-of-set-is-set sā) g (āÆ-is-defined f (ā (š-DCPO sā) Ī“) d)
     where
      g : (Ī£ i ź I , is-defined (Ī± i)) ā (f āÆ) (ā (š-DCPO sā) Ī“) ā” m
      g (i , dįµ¢) = (f āÆ) (ā (š-DCPO sā) Ī“) ā”āØ h i dįµ¢ ā©
                   (f āÆ) (Ī± i)             ā”āØ ineqs i (ā”-to-is-defined (h i dįµ¢) d) ā©
                   m                       ā
       where
        h : (i : I) ā is-defined (Ī± i) ā (f āÆ) (ā (š-DCPO sā) Ī“) ā” (f āÆ) (Ī± i)
        h i d = ap (f āÆ) ((family-defined-somewhere-sup-ā” sā Ī“ i d) ā»Ā¹)

 šĢ-continuous : (f : X ā Y) ā is-continuous (š-DCPO sā) (š-DCPO sā) (šĢ f)
 šĢ-continuous f = transport
                   (is-continuous (š-DCPO sā) (š-DCPO sā))
                   (dfunext fe (šĢ-āÆ-ā¼ f))
                   (āÆ-is-continuous (Ī· ā f))

\end{code}

\begin{code}

module _
         {X : š¤ Ģ }
         (X-is-set : is-set X)
         (š : DCPOā„ {š„} {š¦})
         (f : X ā āŖ š ā«)
       where

 šX : DCPOā„ {š£ āŗ ā š¤} {š£ āŗ ā š¤}
 šX = š-DCPOā„ X-is-set

 fĢ : āŖ šX ā« ā āŖ š ā«
 fĢ (P , Ļ , P-is-prop) = āĖ¢Ė¢ š (f ā Ļ) P-is-prop

 fĢ-is-strict : is-strict šX š fĢ
 fĢ-is-strict = strictness-criterion šX š fĢ Ī³
  where
   Ī³ : fĢ (ā„ šX) āāŖ š ā« ā„ š
   Ī³ = āĖ¢Ė¢-is-lowerbound-of-upperbounds š
        (f ā unique-from-š) š-is-prop (ā„ š) š-induction

 fĢ-is-continuous : is-continuous (šX ā») (š ā») fĢ
 fĢ-is-continuous I Ī± Ī“ = ub , lb-of-ubs
  where
   s : š X
   s = ā (šX ā») Ī“
   Ļ : (l : š X) ā is-prop (is-defined l)
   Ļ = being-defined-is-prop
   lemma : (i : I) (p : is-defined (Ī± i))
         ā value (Ī± i) p ā” value s ā£ i , p ā£
   lemma i p = ā”-of-values-from-ā”
                (family-defined-somewhere-sup-ā” X-is-set Ī“ i p)
   ub : (i : I) ā fĢ (Ī± i) āāŖ š ā« fĢ s
   ub i = āĖ¢Ė¢-is-lowerbound-of-upperbounds š (f ā value (Ī± i)) (Ļ (Ī± i)) (fĢ s) Ī³
    where
     Ī³ : (p : is-defined (Ī± i))
       ā f (value (Ī± i) p) āāŖ š ā« fĢ s
     Ī³ p = f (value (Ī± i) p)     āāŖ š ā«[ ā¦1ā¦ ]
           f (value s ā£ i , p ā£) āāŖ š ā«[ ā¦2ā¦ ]
           fĢ s                   āāŖ š ā«
      where
       ā¦1ā¦ = ā”-to-ā (š ā») (ap f (lemma i p))
       ā¦2ā¦ = āĖ¢Ė¢-is-upperbound š (f ā value s) (Ļ s) ā£ i , p ā£
   lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (š ā»))
                (fĢ s) (fĢ ā Ī±)
   lb-of-ubs y y-is-ub = āĖ¢Ė¢-is-lowerbound-of-upperbounds š (f ā value s) (Ļ s)
                          y Ī³
    where
     Ī³ : (q : is-defined s)
       ā (f (value s q)) āāŖ š ā« y
     Ī³ q = ā„ā„-rec (prop-valuedness (š ā») (f (value s q)) y) r q
      where
       r : (Ī£ i ź I , is-defined (Ī± i)) ā f (value s q) āāŖ š ā« y
       r (i , p) = f (value s q)                     āāŖ š ā«[ ā¦1ā¦       ]
                   f (value s ā£ i , p ā£)             āāŖ š ā«[ ā¦2ā¦       ]
                   f (value (Ī± i) p)                 āāŖ š ā«[ ā¦3ā¦       ]
                   āĖ¢Ė¢ š (f ā value (Ī± i)) (Ļ (Ī± i)) āāŖ š ā«[ y-is-ub i ]
                   y                                 āāŖ š ā«
        where
         ā¦1ā¦ = ā”-to-ā (š ā») (ap f (value-is-constant s q ā£ i , p ā£))
         ā¦2ā¦ = ā”-to-ā (š ā») (ap f (lemma i p ā»Ā¹))
         ā¦3ā¦ = āĖ¢Ė¢-is-upperbound š (f ā value (Ī± i)) (being-defined-is-prop (Ī± i)) p

 fĢ-after-Ī·-is-f : fĢ ā Ī· ā¼ f
 fĢ-after-Ī·-is-f x = antisymmetry (š ā») (fĢ (Ī· x)) (f x) u v
  where
   u : fĢ (Ī· x) āāŖ š ā« f x
   u = āĖ¢Ė¢-is-lowerbound-of-upperbounds š (f ā (Ī» _ ā x)) š-is-prop
        (f x) (Ī» _ ā reflexivity (š ā») (f x))
   v : f x āāŖ š ā« fĢ (Ī· x)
   v = āĖ¢Ė¢-is-upperbound š (Ī» _ ā f x) š-is-prop ā

 all-partial-elements-are-subsingleton-sups :
    (l : āŖ šX ā«)
  ā l ā” āĖ¢Ė¢ šX (Ī· ā value l) (being-defined-is-prop l)
 all-partial-elements-are-subsingleton-sups (P , Ļ , Ļ) =
  antisymmetry (šX ā») (P , Ļ , Ļ) (āĖ¢Ė¢ šX (Ī· ā Ļ) Ļ) u v
   where
    v : āĖ¢Ė¢ šX (Ī· ā Ļ) Ļ ā' (P , Ļ , Ļ)
    v = āĖ¢Ė¢-is-lowerbound-of-upperbounds šX (Ī· ā Ļ) Ļ (P , Ļ , Ļ)
         (Ī» p ā ā (is-defined-Ī·-ā” p) ā»Ā¹)
    u : (P , Ļ , Ļ) ā' āĖ¢Ė¢ šX (Ī· ā Ļ) Ļ
    u p = antisymmetry (šX ā») (P , Ļ , Ļ) (āĖ¢Ė¢ šX (Ī· ā Ļ) Ļ)
           u' v
     where
      u' = (P , Ļ , Ļ)      āāŖ šX ā«[ ā”-to-ā (šX ā») (is-defined-Ī·-ā” p) ]
           Ī· (Ļ p)          āāŖ šX ā«[ āĖ¢Ė¢-is-upperbound šX (Ī· ā Ļ) Ļ p ]
           āĖ¢Ė¢ šX (Ī· ā Ļ) Ļ āāŖ šX ā«

 fĢ-is-unique : (g : āŖ šX ā« ā āŖ š ā«)
             ā is-continuous (šX ā») (š ā») g
             ā is-strict šX š g
             ā g ā Ī· ā” f
             ā g ā¼ fĢ
 fĢ-is-unique g con str eq (P , Ļ , Ļ) = g (P , Ļ , Ļ)        ā”āØ ā¦1ā¦  ā©
                                        g (āĖ¢Ė¢ šX (Ī· ā Ļ) Ļ) ā”āØ ā¦2ā¦  ā©
                                        āĖ¢Ė¢ š (g ā Ī· ā Ļ) Ļ  ā”āØ ā¦3ā¦  ā©
                                        āĖ¢Ė¢ š (f ā Ļ) Ļ      ā”āØ refl ā©
                                        fĢ (P , Ļ , Ļ)        ā
   where
    ā¦1ā¦ = ap g (all-partial-elements-are-subsingleton-sups (P , Ļ , Ļ))
    ā¦2ā¦ = āĖ¢Ė¢-ā”-if-continuous-and-strict šX š g con str (Ī· ā Ļ) Ļ
    ā¦3ā¦ = āĖ¢Ė¢-family-ā” š Ļ (ap (_ā Ļ) eq)

 š-gives-the-free-pointed-dcpo-on-a-set :
  ā! h ź (āŖ šX ā« ā āŖ š ā«) , is-continuous (šX ā») (š ā») h
                          Ć is-strict šX š h
                          Ć (h ā Ī· ā” f)
 š-gives-the-free-pointed-dcpo-on-a-set =
  (fĢ , fĢ-is-continuous , fĢ-is-strict , (dfunext fe fĢ-after-Ī·-is-f)) , Ī³
   where
    Ī³ : is-central (Ī£ h ź (āŖ šX ā« ā āŖ š ā«) , is-continuous (šX ā») (š ā») h
                                           Ć is-strict šX š h
                                           Ć (h ā Ī· ā” f))
         (fĢ , fĢ-is-continuous , fĢ-is-strict , dfunext fe fĢ-after-Ī·-is-f)
    Ī³ (g , cont , str , eq) =
     to-subtype-ā” (Ī» h ā Ćā-is-prop (being-continuous-is-prop (šX ā») (š ā») h)
                                    (being-strict-is-prop šX š h)
                                    (equiv-to-prop
                                      (ā-funext fe (h ā Ī·) f)
                                      (Ī -is-prop fe (Ī» _ ā sethood (š ā»)))))
                                    ((dfunext fe (fĢ-is-unique g cont str eq)) ā»Ā¹)

\end{code}
