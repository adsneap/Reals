Martin Escardo, 20th August 2018

We consider type and subtype classifiers, and discuss an obvious
generalization.

 * (ฮฃ X ๊ ๐ค ฬ , X โ Y) โ (Y โ ๐ค ฬ )
 * (ฮฃ X ๊ ๐ค ฬ , X โช Y) โ (Y โ ฮฉ ๐ค)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Classifiers-Old where

open import SpartanMLTT
open import UF-Subsingletons
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-Equiv-FunExt
open import UF-Base
open import UF-Univalence
open import UF-UA-FunExt
open import UF-FunExt
open import UF-Embeddings

module type-classifier
        {๐ค : Universe}
        (fe' : funext ๐ค (๐ค โบ))
        (ua : is-univalent ๐ค)
        (Y : ๐ค ฬ )
       where

 ฯ : (ฮฃ X ๊ ๐ค ฬ , (X โ Y))  โ (Y โ ๐ค ฬ )
 ฯ (X , f) = fiber f

 T : (Y โ ๐ค ฬ ) โ ฮฃ X ๊ ๐ค ฬ , (X โ Y)
 T A = ฮฃ A , prโ

 ฯT : (A : Y โ ๐ค ฬ ) โ ฯ (T A) โก A
 ฯT A = dfunext fe' ฮณ
  where
   f : โ y โ (ฮฃ ฯ ๊ ฮฃ A , prโ ฯ โก y) โ A y
   f y ((.y , a) , refl) = a
   g : โ y โ A y โ ฮฃ ฯ ๊ ฮฃ A , prโ ฯ โก y
   g y a = (y , a) , refl
   fg : โ y a โ f y (g y a) โก a
   fg y a = refl
   gf : โ y ฯ โ g y (f y ฯ) โก ฯ
   gf y ((.y , a) , refl) = refl
   ฮณ : โ y โ (ฮฃ ฯ ๊ ฮฃ A , prโ ฯ โก y) โก A y
   ฮณ y = eqtoid ua _ _ (f y , ((g y , fg y) , (g y , gf y)))

 transport-map : {X X' Y : ๐ค ฬ } (e : X โ X') (g : X โ Y)
               โ transport (ฮป - โ - โ Y) (eqtoid ua X X' e) g
               โก g โ eqtofun (โ-sym e)

 transport-map {X} {X'} {Y} e g = ฯ (eqtoid ua X X' e) refl
  where
   ฯ : (p : X โก X')
     โ p โก eqtoid ua X X' e
     โ transport (ฮป - โ - โ Y) p g โก g โ eqtofun (โ-sym e)
   ฯ refl q = ap (ฮป h โ g โ h) s
    where
     r : idtoeq X X refl โก e
     r = idtoeq X X refl              โกโจ ap (idtoeq X X) q โฉ
         idtoeq X X (eqtoid ua X X e) โกโจ idtoeq-eqtoid ua X X e โฉ
         e                            โ
     s : id โก eqtofun (โ-sym e)
     s = ap (ฮป - โ eqtofun (โ-sym -)) r

 Tฯ : (ฯ : ฮฃ X ๊ ๐ค ฬ , (X โ Y)) โ T (ฯ ฯ) โก ฯ
 Tฯ (X , f) = to-ฮฃ-โก (eqtoid ua _ _ (total-fiber-is-domain f) ,
                       transport-map (total-fiber-is-domain f) prโ)

 ฯ-is-equivalence : is-equiv ฯ
 ฯ-is-equivalence = (T , ฯT) , (T , Tฯ)

 classification-equivalence : (ฮฃ X ๊ ๐ค ฬ , (X โ Y)) โ (Y โ ๐ค ฬ )
 classification-equivalence = ฯ , ฯ-is-equivalence


module subtype-classifier
        {๐ค : Universe}
        (fe' : funext ๐ค (๐ค โบ))
        (ua : is-univalent ๐ค)
        (Y : ๐ค ฬ )
       where

 fe : funext ๐ค ๐ค
 fe = univalence-gives-funext ua

 ฯ : (ฮฃ X ๊ ๐ค ฬ , X โช Y)  โ (Y โ ฮฉ ๐ค)
 ฯ (X , f , i) y = fiber f y , i y

 T : (Y โ ฮฉ ๐ค) โ ฮฃ X ๊ ๐ค ฬ , X โช Y
 T P = (ฮฃ y ๊ Y , P y holds) , prโ , prโ-is-embedding (ฮป y โ holds-is-prop (P y))

 ฯT : (P : Y โ ฮฉ ๐ค) โ ฯ (T P) โก P
 ฯT P = dfunext fe' ฮณ
  where
   f : โ y โ ฯ (T P) y holds โ P y holds
   f y ((.y , h) , refl) = h
   g : โ y โ P y holds โ ฯ (T P) y holds
   g y h = (y , h) , refl
   ฮณ : (y : Y) โ ฯ (T P) y โก P y
   ฮณ y = ฮฉ-ext-from-univalence ua (f y) (g y)

 transport-embedding : {X X' Y : ๐ค ฬ } (e : X โ X') (g : X โ Y) (i : is-embedding g)
                    โ transport (ฮป - โ - โช Y) (eqtoid ua X X' e) (g , i)
                    โก g โ eqtofun (โ-sym e) , โ-is-embedding
                                                 (equivs-are-embeddings (eqtofun (โ-sym e))
                                                                        (eqtofun- (โ-sym e))) i
 transport-embedding {X} {X'} {Y} e g i = ฯ (eqtoid ua X X' e) refl
  where
   ฯ : (p : X โก X')
     โ p โก eqtoid ua X X' e
     โ transport (ฮป - โ - โช Y) p (g , i)
     โก g โ eqtofun (โ-sym e) , โ-is-embedding
                                  (equivs-are-embeddings (eqtofun (โ-sym e))
                                                         (eqtofun- (โ-sym e))) i
   ฯ refl q = to-ฮฃ-โก (ap (ฮป h โ g โ h) s ,
                      being-embedding-is-prop fe (g โ eqtofun (โ-sym e)) _ _)
    where
     r : idtoeq X X refl โก e
     r = ap (idtoeq X X) q โ idtoeq-eqtoid ua X X e
     s : id โก eqtofun (โ-sym e)
     s = ap (ฮป - โ eqtofun (โ-sym -)) r

 Tฯ : (ฯ : ฮฃ X ๊ ๐ค ฬ , X โช Y) โ T (ฯ ฯ) โก ฯ
 Tฯ (X , f , i) = to-ฮฃ-โก (eqtoid ua _ _ (total-fiber-is-domain f) ,
                          (transport-embedding (total-fiber-is-domain f) prโ (prโ-is-embedding i)
                         โ to-ฮฃ-โก' (being-embedding-is-prop fe f _ _)))

 ฯ-is-equivalence : is-equiv ฯ
 ฯ-is-equivalence = (T , ฯT) , (T , Tฯ)

 classification-equivalence : (ฮฃ X ๊ ๐ค ฬ , X โช Y) โ (Y โ ฮฉ ๐ค)
 classification-equivalence = ฯ , ฯ-is-equivalence

\end{code}

TODO. Consider a property "green" of types, and call a map green if
its fibers are all green. Then the maps of Y into green types should
correspond to the green maps X โ Y. This generalizes the above
situation. In particular, the case green = contractible is of interest
and describes a previously known situation. Another example is that
surjections X โ Y are in bijection with families
Y โ ฮฃ (Z : ๐ค ฬ ) โ โฅ Z โฅ), that is, families of inhabited types. It is
not necessary that "green" is proposition valued. It can be universe
valued in general. And then of course retractions X โ Y are in
bijections with families of pointed types.

Tom de Jong, September 2019. I implement the above TODO.

(There is an alternative solution at
https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/)

Fix type universes ๐ค and ๐ฅ and a type Y : ๐ค ฬ. Consider a property green : ๐ค โ ๐ฅ.
If X : ๐ค ฬ and f : X โ Y, then we say that f is a green map if all of its fibers
are green.

The general theorem says that type of green maps to Y is equivalent to the type
of green types: Green-map โ (Y โ Green).

The examples are obtained by specialising to a specific property green:

 * Every type and map is green.
   (ฮฃ X ๊ ๐ค ฬ , X โ Y) โ (Y โ ๐ค ฬ )

 * A type is green exactly if it is a subsingleton.
   Then a map is green exactly if it is an embedding.
   (ฮฃ X ๊ ๐ค ฬ , X โช Y) โ (Y โ ฮฉ ๐ค)

 * A type is green exactly if it is inhabited.
   Then a map is green exactly if it is a surjection.
   (ฮฃ X ๊ ๐ค ฬ , (ฮฃ f ๊ X โ Y , is-surjection f )) โ (Y โ (ฮฃ X ๊ ๐ค ฬ  , โฅ X โฅ))

 * A type is green exactly if it is pointed.
   Then a map is green exactly if it is a retraction.
   (ฮฃ X ๊ ๐ค ฬ , Y โ X) โ (Y โ (ฮฃ X ๊ ๐ค ฬ  , X))

\begin{code}

eqtoid-comp : (ua : is-univalent ๐ค) {X Y Z : ๐ค ฬ } (f : X โ Y) (g : Y โ Z)
            โ (eqtoid ua X Y f) โ (eqtoid ua Y Z g) โก eqtoid ua X Z (f โ g)
eqtoid-comp {๐ค} ua {X} {Y} {Z} f =
 JEq ua Y (ฮป Z g โ eqtoid ua X Y f โ eqtoid ua Y Z g โก eqtoid ua X Z (f โ g)) ฮณ Z
  where
   fe : funext ๐ค ๐ค
   fe = univalence-gives-funext ua
   h : f โก f โ โ-refl Y
   h = (โ-refl-right' fe fe fe f)โปยน

   ฮณ = eqtoid ua X Y f โ eqtoid ua Y Y (โ-refl Y) โกโจ ap (ฮป - โ eqtoid ua X Y f โ -) (eqtoid-refl ua Y) โฉ
       eqtoid ua X Y f                            โกโจ ap (ฮป - โ eqtoid ua X Y -) h โฉ
       eqtoid ua X Y (f โ โ-refl Y)               โ

module general-classifier
        {๐ค ๐ฅ : Universe}
        (fe : funext ๐ค ๐ฅ)
        (fe' : funext ๐ค (๐ค โบ โ ๐ฅ))
        (ua : is-univalent ๐ค)
        (Y : ๐ค ฬ )
        (green : ๐ค ฬ โ ๐ฅ ฬ )
       where

 green-map : {X : ๐ค ฬ } โ (X โ Y) โ ๐ค โ ๐ฅ ฬ
 green-map f = (y : Y) โ green (fiber f y)

 Green : ๐ค โบ โ ๐ฅ ฬ
 Green = ฮฃ X ๊ ๐ค ฬ , green X

 Green-map : ๐ค โบ โ ๐ฅ ฬ
 Green-map = ฮฃ X ๊ ๐ค ฬ , ฮฃ f ๊ (X โ Y) , green-map f

 ฯ : Green-map  โ (Y โ Green)
 ฯ (X , f , g) y = (fiber f y) , (g y)

 fiber-equiv-โก : (A : Y โ Green) (y : Y) โ prโ (A y) โก fiber prโ y
 fiber-equiv-โก A y =
  (eqtoid ua (fiber prโ y) (prโ (A y)) (prโ-fiber-equiv {๐ค} {๐ค} {Y} {prโ โ A} y)) โปยน

 T : (Y โ Green) โ Green-map
 T A = ฮฃ (prโ โ A) , prโ , g
  where
   g : green-map prโ
   g y = transport green (fiber-equiv-โก A y) (prโ (A y))

 ฯT : (A : Y โ Green) โ ฯ (T A) โก A
 ฯT A = dfunext fe' ฮณ
  where
   ฮณ : (y : Y) โ ฯ (T A) y โก A y
   ฮณ y = to-ฮฃ-โก ((a โปยน) , b)
    where
     a : prโ (A y) โก prโ (ฯ (T A) y)
     a = fiber-equiv-โก A y
     b = transport green (a โปยน) (prโ (ฯ (T A) y))               โกโจ refl โฉ
         transport green (a โปยน) (transport green a (prโ (A y))) โกโจ i โฉ
         transport green (a โ a โปยน) (prโ (A y))                 โกโจ ii โฉ
         transport green refl (prโ (A y))                       โกโจ refl โฉ
         prโ (A y)                                              โ
      where
       i  = (transport-โ green a (a โปยน)) โปยน
       ii = ap (ฮป - โ transport green - (prโ (A y))) (trans-sym' a)

 green-maps-are-closed-under-precomp-with-equivs : {X X' : ๐ค ฬ } (e : X' โ X)
                                                   {f : X โ Y}
                                                 โ green-map f
                                                 โ green-map (f โ eqtofun e)
 green-maps-are-closed-under-precomp-with-equivs e {f} g y =
  transport green p (g y)
   where
    p : fiber f y โก fiber (f โ eqtofun e) y
    p = (eqtoid ua _ _ (precomposition-with-equiv-does-not-change-fibers e f y)) โปยน

 precomp-with-โ-refl-green-map : {X : ๐ค ฬ } (f : X โ Y) (g : green-map f)
                           โ green-maps-are-closed-under-precomp-with-equivs
                              (โ-refl X) g
                             โก g
 precomp-with-โ-refl-green-map {X} f g = dfunext fe ฮณ
  where
   ฮณ : (y : Y) โ green-maps-are-closed-under-precomp-with-equivs (โ-refl X) g y โก g y
   ฮณ y = green-maps-are-closed-under-precomp-with-equivs (โ-refl X) g y         โกโจ refl โฉ
         transport green ((eqtoid ua _ _ (โ-refl (fiber f y))) โปยน) (g y)        โกโจ i โฉ
         g y                                                                    โ
    where
     i = ap (ฮป - โ transport green (- โปยน) (g y)) (eqtoid-refl ua (fiber f y))

 transport-green-map-eqtoid : {X X' : ๐ค ฬ } (e : X' โ X) (f : X โ Y)
                              (g : green-map f)
                            โ transport (ฮป - โ ฮฃ h ๊ (- โ Y) , green-map h)
                               ((eqtoid ua X' X e) โปยน) (f , g)
                              โก
                              f โ (eqtofun e) ,
                               green-maps-are-closed-under-precomp-with-equivs e g
 transport-green-map-eqtoid {X} {X'} = JEq ua X' E ฮณ X
  where
   B : ๐ค ฬ โ ๐ค โ ๐ฅ ฬ
   B Z = ฮฃ h ๊ (Z โ Y) , green-map h
   E : (Z : ๐ค ฬ ) โ X' โ Z โ ๐ค โ ๐ฅ ฬ
   E Z e = (f : Z โ Y) โ (g : green-map f)
         โ transport B ((eqtoid ua X' Z e) โปยน) (f , g)
           โก f โ (eqtofun e) , green-maps-are-closed-under-precomp-with-equivs e g
   ฮณ : E X' (โ-refl X')
   ฮณ f g = transport B ((eqtoid ua X' X' (โ-refl X')) โปยน) (f , g)            โกโจ i โฉ
           f , g                                                             โกโจ ii โฉ
           f , green-maps-are-closed-under-precomp-with-equivs (โ-refl X') g โ
    where
     i  = ap (ฮป - โ transport B (- โปยน) (f , g)) (eqtoid-refl ua X')
     ii = to-ฮฃ-โก (refl , ((precomp-with-โ-refl-green-map f g) โปยน))

 Tฯ : (f : Green-map) โ T (ฯ f) โก f
 Tฯ (X , f , g) = to-ฮฃ-โก (a , (to-ฮฃ-โก (b , c)))
  where
   X' : ๐ค ฬ
   X' = prโ (T (ฯ (X , f , g)))
   f' : X' โ Y
   f' = prโ (prโ (T (ฯ (X , f , g))))
   g' : green-map f'
   g' = prโ (prโ (T (ฯ (X , f , g))))
   e : X โ X'
   e = domain-is-total-fiber f
   a : X' โก X
   a = (eqtoid ua X X' e) โปยน
   B : ๐ค ฬ โ ๐ค โ ๐ฅ ฬ
   B Z = ฮฃ h ๊ (Z โ Y), green-map h
   t : transport B a (f' , g') โก
       (f' โ eqtofun e) , (green-maps-are-closed-under-precomp-with-equivs e g')
   t = transport-green-map-eqtoid e f' g'
   tโ : prโ (transport B a (f' , g')) โก f' โ eqtofun e
   tโ = prโ (from-ฮฃ-โก t)
   tโ : transport green-map tโ (prโ (transport B a (f' , g'))) โก
        green-maps-are-closed-under-precomp-with-equivs e g'
   tโ = prโ (from-ฮฃ-โก t)
   b : prโ (transport B a (f' , g')) โก f
   b = prโ (transport B a (f' , g')) โกโจ tโ โฉ
       f' โ eqtofun e                โกโจ refl โฉ
       f                             โ
   c : transport green-map b (prโ (transport B a (f' , g')))  โก g
   c = transport green-map b (prโ (transport B a (f' , g')))  โกโจ refl โฉ
       transport green-map tโ (prโ (transport B a (f' , g'))) โกโจ tโ โฉ
       green-maps-are-closed-under-precomp-with-equivs e g' โกโจ dfunext fe u โฉ
       g โ
    where
     u : (y : Y) โ green-maps-are-closed-under-precomp-with-equivs e g' y โก g y
     u y = green-maps-are-closed-under-precomp-with-equivs e g' y โกโจ refl โฉ
           transport green (p โปยน) (g' y)                          โกโจ refl โฉ
           transport green (p โปยน) (transport green (q โปยน) (g y))  โกโจ i โฉ
           transport green (q โปยน โ p โปยน) (g y)                    โกโจ ii โฉ
           g y                                                    โ
       where
        p : fiber (f' โ eqtofun e) y โก fiber f' y
        p = eqtoid ua _ _ (precomposition-with-equiv-does-not-change-fibers e f' y)
        q : fiber f' y โก fiber f y
        q = eqtoid ua (fiber f' y) (fiber f y) (prโ-fiber-equiv y)
        i  = (transport-โ green (q โปยน) (p โปยน)) โปยน
        ii = ap (ฮป - โ transport green - (g y)) v
         where
          v = q โปยน โ p โปยน โกโจ โปยน-contravariant p q โฉ
              (p โ q) โปยน  โกโจ ap (_โปยน) w โฉ
              refl        โ
           where
            w : p โ q โก refl
            w = eqtoid ua _ _ ฯ โ eqtoid ua _ _ ฯ โกโจ eqtoid-comp ua _ _ โฉ
                eqtoid ua _ _ (ฯ โ ฯ)             โกโจ ap (eqtoid ua _ _) ฯฯ โฉ
                eqtoid ua _ _ (โ-refl _)          โกโจ eqtoid-refl ua _ โฉ
                refl                              โ
             where
              ฯ : fiber (f' โ eqtofun e) y โ fiber f' y
              ฯ = precomposition-with-equiv-does-not-change-fibers e f' y
              ฯ : fiber prโ y โ prโ (ฯ (X , f , g) y)
              ฯ = prโ-fiber-equiv y
              ฯฯ : ฯ โ ฯ โก โ-refl (fiber (f' โ eqtofun e) y)
              ฯฯ = to-ฮฃ-โก (dfunext fe'' ฯฯ' ,
                           being-equiv-is-prop'' fe'' id _ (id-is-equiv _))
               where
                ฯฯ' : (z : fiber (f' โ eqtofun e) y)
                   โ eqtofun (ฯ โ ฯ) z โก z
                ฯฯ' (x , refl) = refl
                fe'' : funext ๐ค ๐ค
                fe'' = univalence-gives-funext ua

 ฯ-is-equivalence : is-equiv ฯ
 ฯ-is-equivalence = (T , ฯT) , (T , Tฯ)

 classification-equivalence : Green-map โ (Y โ Green)
 classification-equivalence = ฯ , ฯ-is-equivalence

\end{code}

We now can get type-classifier above as a special case of this more
general situation:

\begin{code}

module type-classifier-bis
        {๐ค : Universe}
        (fe' : funext ๐ค (๐ค โบ))
        (ua : is-univalent ๐ค)
        (Y : ๐ค ฬ )
       where

 open general-classifier (univalence-gives-funext ua) fe' ua Y (ฮป (X : ๐ค ฬ ) โ ๐)

 type-classification-equivalence : (ฮฃ X ๊ ๐ค ฬ , (X โ Y)) โ (Y โ ๐ค ฬ )
 type-classification-equivalence = (ฮฃ X ๊ ๐ค ฬ , (X โ Y)) โโจ ฯ โฉ
                                   Green-map โโจ classification-equivalence โฉ
                                   (Y โ Green) โโจ ฯ โฉ
                                   (Y โ ๐ค ฬ ) โ?
  where
   ฯ : (ฮฃ X ๊ ๐ค ฬ , (X โ Y)) โ Green-map
   ฯ = qinveq ฮฑ (ฮฒ , a , b)
    where
     ฮฑ : (ฮฃ X ๊ ๐ค ฬ , (X โ Y)) โ Green-map
     ฮฑ (X , f) = X , (f , (ฮป y โ โ))
     ฮฒ : Green-map โ (ฮฃ X ๊ ๐ค ฬ , (X โ Y))
     ฮฒ (X , f , g) = X , f
     a : (p : ฮฃ (ฮป X โ X โ Y)) โ ฮฒ (ฮฑ p) โก p
     a (X , f) = refl
     b : (q : Green-map) โ ฮฑ (ฮฒ q) โก q
     b (X , f , g) = to-ฮฃ-โก (refl ,
                             to-ฮฃ-โก (refl ,
                                     dfunext (univalence-gives-funext ua)
                                      (ฮป y โ ๐-is-prop โ (g y))))
   ฯ : (Y โ Green) โ (Y โ ๐ค ฬ )
   ฯ = โcong fe' fe' (โ-refl Y) ฮณ
    where
     ฮณ : Green โ ๐ค ฬ
     ฮณ = qinveq prโ ((ฮป X โ (X , โ )) , c , ฮป x โ refl)
      where
       c : (p : ฮฃ (ฮป X โ ๐)) โ prโ p , โ โก p
       c (x , โ) = refl

\end{code}

And we also get the other examples in the TODO:

\begin{code}

module subsingleton-classifier
        {๐ค : Universe}
        (fe' : funext ๐ค (๐ค โบ))
        (ua : is-univalent ๐ค)
        (Y : ๐ค ฬ )
       where

 open general-classifier (univalence-gives-funext ua) fe' ua Y
                         (ฮป (X : ๐ค ฬ ) โ is-prop X)

 subsingleton-classification-equivalence : (ฮฃ X ๊ ๐ค ฬ , X โช Y) โ (Y โ ฮฉ ๐ค )
 subsingleton-classification-equivalence = classification-equivalence

module singleton-classifier
        {๐ค : Universe}
        (fe' : funext ๐ค (๐ค โบ))
        (ua : is-univalent ๐ค)
        (Y : ๐ค ฬ )
       where

 open import UF-Subsingletons-FunExt
 open general-classifier (univalence-gives-funext ua) fe' ua Y
                         (ฮป (X : ๐ค ฬ ) โ is-singleton X)

 singleton-classification-equivalence : (ฮฃ X ๊ ๐ค ฬ , X โ Y) โ ๐ {๐ค}
 singleton-classification-equivalence =
  (ฮฃ X ๊ ๐ค ฬ , X โ Y)                            โโจ i โฉ
  (ฮฃ X ๊ ๐ค ฬ , (ฮฃ f ๊ (X โ Y), is-vv-equiv f)) โโจ ii โฉ
  (Y โ (ฮฃ X ๊ ๐ค ฬ , is-singleton X))             โโจ iii โฉ
  (Y โ ๐)                                             โโจ โ๐ fe โฉ
  ๐                                                   โ?
   where
    fe : funext ๐ค ๐ค
    fe = univalence-gives-funext ua

    i   = ฮฃ-cong (ฮป (X : ๐ค ฬ ) โ ฮฃ-cong (ฮป (f : X โ Y) โ
           logically-equivalent-props-are-equivalent
            (being-equiv-is-prop'' fe f)
            (ฮ?-is-prop fe (ฮป y โ being-singleton-is-prop fe))
            (equivs-are-vv-equivs f)
            (vv-equivs-are-equivs f)))
    ii  = classification-equivalence
    iii = โcong fe fe' (โ-refl Y) ฯ
     where
      ฯ : ฮฃ (ฮป X โ is-singleton X) โ ๐
      ฯ = qinveq unique-to-๐ ((ฮป _ โ ๐ , ๐-is-singleton) , (a , ๐-is-prop โ))
       where
       a : (p : ฮฃ (ฮป v โ is-singleton v)) โ ๐ , ๐-is-singleton โก p
       a (X , s) = to-ฮฃ-โก (eqtoid ua ๐ X (singleton-โ-๐' s) ,
                           being-singleton-is-prop fe _ s)

open import UF-PropTrunc

module inhabited-classifier
        {๐ค : Universe}
        (fe' : funext ๐ค (๐ค โบ))
        (ua : is-univalent ๐ค)
        (Y : ๐ค ฬ )
        (pt : propositional-truncations-exist)
       where

 open import UF-ImageAndSurjection
 open ImageAndSurjection pt
 open PropositionalTruncation pt
 open general-classifier (univalence-gives-funext ua) fe' ua Y
                         (ฮป (X : ๐ค ฬ ) โ โฅ X โฅ)

 inhabited-classification-equivalence :
  (ฮฃ X ๊ ๐ค ฬ , (ฮฃ f ๊ (X โ Y), is-surjection f )) โ
   (Y โ (ฮฃ X ๊ ๐ค ฬ , โฅ X โฅ))
 inhabited-classification-equivalence = classification-equivalence

module pointed-classifier
        {๐ค : Universe}
        (fe' : funext ๐ค (๐ค โบ))
        (ua : is-univalent ๐ค)
        (Y : ๐ค ฬ )
       where

 open import UF-Retracts
 open general-classifier (univalence-gives-funext ua) fe' ua Y (ฮป (X : ๐ค ฬ ) โ X)

 pointed-classification-equivalence :
  (ฮฃ X ๊ ๐ค ฬ , Y โ X) โ (Y โ (ฮฃ X ๊ ๐ค ฬ  , X))
 pointed-classification-equivalence =
  (ฮฃ X ๊ ๐ค ฬ , Y โ X)                                  โโจ i โฉ
  (ฮฃ X ๊ ๐ค ฬ , (ฮฃ f ๊ (X โ Y) , ((y : Y) โ fiber f y))) โโจ ii โฉ
  (Y โ (ฮฃ X ๊ ๐ค ฬ , X))                                โ?
   where
    i  = ฮฃ-cong (ฮป (X : ๐ค ฬ ) โ ฮฃ-cong (ฮป (f : X โ Y) โ retract-pointed-fibers))
    ii = classification-equivalence

\end{code}
