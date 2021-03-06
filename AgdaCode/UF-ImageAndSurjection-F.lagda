Martin Escardo and Tom de Jong, October 2021

Modified from UF-ImageAndSurjection.lagda to add the parameter F.

We use F to control the universe where propositional truncations live.
For more comments and explanations, see the original files.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module UF-ImageAndSurjection-F (F : Universe â Universe) where

open import UF-Base
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-Embeddings
open import UF-Subsingletons
open import UF-PropTrunc-F F
open import UF-Retracts

module ImageAndSurjection (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 _âimage_ : {X : ð¤ Ì } {Y : ð¥ Ì } â Y â (X â Y) â F (ð¤ â ð¥) Ì
 y âimage f = â x ê domain f , f x â¡ y

 being-in-the-image-is-prop : {X : ð¤ Ì } {Y : ð¥ Ì } (y : Y) (f : X â Y)
                            â is-prop (y âimage f)
 being-in-the-image-is-prop y f = â-is-prop

 image : {X : ð¤ Ì } {Y : ð¥ Ì } â (X â Y) â F (ð¤ â ð¥) â ð¥ Ì
 image f = Î£ y ê codomain f , y âimage f

 restriction : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
             â image f â Y
 restriction f (y , _) = y

 restriction-embedding : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                       â is-embedding (restriction f)
 restriction-embedding f = prâ-is-embedding (Î» y â â¥â¥-is-prop)

 corestriction : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
               â X â image f
 corestriction f x = f x , â£ x , refl â£

 wconstant-maps-to-sets-have-propositional-images : (X : ð¤ Ì ) {Y : ð¥ Ì }
                                                  â is-set Y
                                                  â (f : X â Y)
                                                  â wconstant f
                                                  â is-prop (image f)
 wconstant-maps-to-sets-have-propositional-images X s f c (y , p) (y' , p') =
  to-Î£-â¡ (â¥â¥-rec s (Î» u â â¥â¥-rec s (Î» v â h u v) p') p ,
          â¥â¥-is-prop _ p')
   where
    h : (Î£ x ê X , f x â¡ y) â (Î£ x' ê X , f x' â¡ y') â y â¡ y'
    h (x , e) (x' , e') = y    â¡â¨ e â»Â¹ â©
                          f x  â¡â¨ c x x' â©
                          f x' â¡â¨ e' â©
                          y'   â

 wconstant-map-to-set-truncation-of-domain-map' : (X : ð¤ Ì ) {Y : ð¥ Ì }
                                                â is-set Y
                                                 â (f : X â Y)
                                                â wconstant f
                                                â â¥ X â¥ â image f
 wconstant-map-to-set-truncation-of-domain-map' X s f c =
  â¥â¥-rec
  (wconstant-maps-to-sets-have-propositional-images X s f c)
  (corestriction f)

 wconstant-map-to-set-truncation-of-domain-map : (X : ð¤ Ì ) {Y : ð¥ Ì }
                                               â is-set Y
                                               â (f : X â Y)
                                               â wconstant f
                                                 â â¥ X â¥ â Y
 wconstant-map-to-set-truncation-of-domain-map X s f c =
  restriction f â wconstant-map-to-set-truncation-of-domain-map' X s f c

 wconstant-map-to-set-factors-through-truncation-of-domain : (X : ð¤ Ì ) {Y : ð¥ Ì }
                                                             (s : is-set Y)
                                                             (f : X â Y)
                                                             (c : wconstant f)
                                                           â f â¼ (wconstant-map-to-set-truncation-of-domain-map X s f c) â â£_â£
 wconstant-map-to-set-factors-through-truncation-of-domain X s f c = Î³
  where
   g : â¥ X â¥ â image f
   g = wconstant-map-to-set-truncation-of-domain-map' X s f c
   p : is-prop (image f)
   p = wconstant-maps-to-sets-have-propositional-images X s f c
   Î³ : (x : X) â f x â¡ restriction f (g â£ x â£)
   Î³ x = f x                               â¡â¨ refl â©
         restriction f (corestriction f x) â¡â¨ ap (restriction f)
                                              (p (corestriction f x) (g â£ x â£)) â©
         restriction f (g â£ x â£)           â

 is-surjection : {X : ð¤ Ì } {Y : ð¥ Ì } â (X â Y) â F (ð¤ â ð¥) â ð¥ Ì
 is-surjection f = â y â â x ê domain f , f x â¡ y

 _â _ : ð¤ Ì â ð¥ Ì â F (ð¤ â ð¥) â ð¤ â ð¥ Ì
 X â  Y = Î£ f ê (X â Y) , is-surjection f

 image-is-set : {X : ð¤ Ì } {Y : ð¥ Ì }
              â (f : X â Y)
              â is-set Y
              â is-set (image f)
 image-is-set f i = subsets-of-sets-are-sets _
                     (Î» y â y âimage f) i
                     (being-in-the-image-is-prop _ f)

 vv-equiv-iff-embedding-and-surjection  :  {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                                        â is-vv-equiv f â is-embedding f Ã is-surjection f
 vv-equiv-iff-embedding-and-surjection f = g , h
  where
   g : is-vv-equiv f â is-embedding f Ã is-surjection f
   g i = (Î» y â prâ (prâ the-singletons-are-the-inhabited-propositions (i y))) ,
         (Î» y â prâ (prâ the-singletons-are-the-inhabited-propositions (i y)))

   h : is-embedding f Ã is-surjection f â is-vv-equiv f
   h (e , s) = Î» y â prâ the-singletons-are-the-inhabited-propositions (e y , s y)

 surjective-embeddings-are-vv-equivs : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                                     â is-embedding f â is-surjection f â is-vv-equiv f
 surjective-embeddings-are-vv-equivs f e s = prâ (vv-equiv-iff-embedding-and-surjection f) (e , s)

 surjective-embeddings-are-equivs : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                                  â is-embedding f â is-surjection f â is-equiv f
 surjective-embeddings-are-equivs f e s = vv-equivs-are-equivs f (surjective-embeddings-are-vv-equivs f e s)

 corestriction-is-surjection : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                             â is-surjection (corestriction f)
 corestriction-is-surjection f (y , s) = â¥â¥-functor g s
  where
   g : (Î£ x ê domain f , f x â¡ y) â Î£ x ê domain f , corestriction f x â¡ (y , s)
   g (x , p) = x , to-Î£-â¡ (p , â¥â¥-is-prop _ _)

 pt-is-surjection : {X : ð¤ Ì } â is-surjection (Î» (x : X) â â£ x â£)
 pt-is-surjection t = â¥â¥-rec â¥â¥-is-prop (Î» x â â£ x , â¥â¥-is-prop (â£ x â£) t â£) t


 NatÎ£-is-surjection : {X : ð¤ Ì } (A : X â ð¥ Ì ) (B : X â ð¦ Ì ) (Î¶ : Nat A B)
                    â ((x : X) â is-surjection (Î¶ x))
                    â is-surjection (NatÎ£ Î¶)
 NatÎ£-is-surjection A B Î¶ i (x , b) = Î³
  where
   Î´ : (Î£ a ê A x , Î¶ x a â¡ b)
     â Î£ (x' , a) ê Î£ A , (x' , Î¶ x' a) â¡ (x , b)
   Î´ (a , p) = (x , a) , (ap (x ,_) p)

   Î³ : â (x' , a) ê Î£ A , (x' , Î¶ x' a) â¡ (x , b)
   Î³ = â¥â¥-functor Î´ (i x b)

 corestriction-of-embedding-is-equivalence : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                                           â is-embedding f
                                           â is-equiv (corestriction f)
 corestriction-of-embedding-is-equivalence f e =
  surjective-embeddings-are-equivs f' e' s'
   where
    f' : domain f â image f
    f' = corestriction f
    s' : is-surjection f'
    s' = corestriction-is-surjection f
    e' : is-embedding f'
    e' (y , p) = retract-of-prop Î³ (e y)
     where
      Î³ : fiber f' (y , p) â fiber f y
      Î³ = Î£-retract (Î» x â f' x â¡ y , p) (Î» x â f x â¡ y) Ï
       where
        Ï : (x : domain f) â (f' x â¡ (y , p)) â (f x â¡ y)
        Ï x = Ï , Ï , Î·
         where
          Ï : f x â¡ y â f' x â¡ (y , p)
          Ï q = to-subtype-â¡ (Î» y' â â¥â¥-is-prop) q
          Ï : f' x â¡ (y , p) â f x â¡ y
          Ï q' = ap prâ q'
          Î· : Ï â Ï â¼ id
          Î· refl = to-Î£-â¡ (refl , q)    â¡â¨ ap (Î» - â to-Î£-â¡ (refl , -)) h â©
                   to-Î£-â¡ (refl , refl) â¡â¨ refl â©
                   refl                 â
           where
            q : â£ x , refl â£ â¡ â£ x , refl â£
            q = â¥â¥-is-prop â£ x , refl â£ â£ x , refl â£
            h : q â¡ refl
            h = props-are-sets â¥â¥-is-prop q refl

 embedding-if-corestriction-is-equivalence : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                                           â is-equiv (corestriction f)
                                           â is-embedding f
 embedding-if-corestriction-is-equivalence f i =
  embedding-closed-under-â¼ f' f (â-is-embedding eâ eâ) H
   where
    f' : domain f â codomain f
    f' = prâ â corestriction f
    H : f â¼ prâ â corestriction f
    H x = refl
    eâ : is-embedding (corestriction f)
    eâ = equivs-are-embeddings (corestriction f) i
    eâ : is-embedding prâ
    eâ = prâ-is-embedding (Î» y â â¥â¥-is-prop)

 imageInduction : â {ð¦ ð¤ ð¥} {X : ð¤ Ì } {Y : ð¥ Ì } â (X â Y) â ð¤ â ð¥ â ð¦  âº Ì
 imageInduction {ð¦} {ð¤} {ð¥} {X} {Y} f =
                (P : Y â ð¦ Ì ) â ((y : Y) â is-prop (P y)) â ((x : X) â P (f x)) â (y : Y) â P y

 surjection-induction : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                      â is-surjection f â imageInduction {ð¦} f
 surjection-induction f is P isp a y = â¥â¥-rec (isp y)
                                             (Î» Ï â transport P (prâ Ï) (a (prâ Ï)))
                                             (is y)

 image-surjection-converse : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                           â imageInduction f â is-surjection f
 image-surjection-converse f is' = is' (Î» y â â¥ Î£ (Î» x â f x â¡ y) â¥)
                                       (Î» y â â¥â¥-is-prop)
                                       (Î» x â â£ x , refl â£)

 image-induction : â {ð¦} {X : ð¤ Ì } {Y : ð¥ Ì }
                   (f : X â Y) (P : image f â ð¦ Ì )
                 â (â y' â is-prop (P y'))
                 â (â x â P (corestriction f x))
                 â â y' â P y'
 image-induction f = surjection-induction (corestriction f)
                                          (corestriction-is-surjection f)

 retraction-surjection : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                       â has-section f â is-surjection f
 retraction-surjection {ð¤} {ð¥} {X} f Ï y = â£ prâ Ï y , prâ Ï y â£

 prâ-is-surjection : {X : ð¤ Ì } (A : X â ð¥ Ì )
                   â ((x : X) â â¥ A x â¥)
                   â is-surjection (Î» (Ï : Î£ A) â prâ Ï)
 prâ-is-surjection A s x = Î³
  where
   Î´ : A x â Î£ Ï ê Î£ A , prâ Ï â¡ x
   Î´ a = (x , a) , refl

   Î³ : â Ï ê Î£ A , prâ Ï â¡ x
   Î³ = â¥â¥-functor Î´ (s x)

 prâ-is-surjection-converse : {X : ð¤ Ì } (A : X â ð¥ Ì )
                            â is-surjection (Î» (Ï : Î£ A) â prâ Ï)
                            â ((x : X) â â¥ A x â¥)
 prâ-is-surjection-converse A s x = Î³
  where
   Î´ : (Î£ Ï ê Î£ A , prâ Ï â¡ x) â A x
   Î´ ((.x , a) , refl) = a

   Î³ : â¥ A x â¥
   Î³ = â¥â¥-functor Î´ (s x)

 surjection-â-image : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                    â is-surjection f
                    â image f â Y
 surjection-â-image {ð¤} {ð¥} {X} {Y} f s =
  image f                       ââ¨ â-refl _ â©
  (Î£ y ê Y , â x ê X , f x â¡ y) ââ¨ Î£-cong Î³ â©
  (Î£ y ê Y , ð)                 ââ¨ â-refl _ â©
  Y Ã ð                         ââ¨ ð-rneutral {ð¥} {ð¥} â©
  Y                             â 
   where
    Î³ : (y : Y) â (â x ê X , f x â¡ y) â ð
    Î³ y = singleton-â-ð (pointed-props-are-singletons (s y) â¥â¥-is-prop)

 â-is-surjection : {X : ð¤ Ì } {Y : ð¥ Ì } {Z : ð¦ Ì } {f : X â Y} {g : Y â Z}
                 â is-surjection f â is-surjection g â is-surjection (g â f)
 â-is-surjection {ð¤} {ð¥} {ð¦} {X} {Y} {Z} {f} {g} Ï Ï z =
  â¥â¥-rec â¥â¥-is-prop Î³â (Ï z)
   where
    Î³â : (Î£ y ê Y , g y â¡ z) â â x ê X , (g â f) x â¡ z
    Î³â (y , q) = â¥â¥-functor Î³â (Ï y)
     where
      Î³â : (Î£ x ê X , f x â¡ y) â Î£ x ê X , (g â f) x â¡ z
      Î³â (x , p) = (x , (g (f x) â¡â¨ ap g p â©
                         g y     â¡â¨ q â©
                         z       â))

 equivs-are-surjections : {X : ð¤ Ì } {Y : ð¥ Ì } {f : X â Y}
                        â is-equiv f â is-surjection f
 equivs-are-surjections ((Ï , Î·) , (Ï , Îµ)) y = â£ Ï y , Î· y â£

\end{code}
