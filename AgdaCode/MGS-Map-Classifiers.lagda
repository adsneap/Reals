Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module MGS-Map-Classifiers where

open import MGS-FunExt-from-Univalence public

_/_ : (๐ค : Universe) โ ๐ฅ ฬ โ ๐ค โบ โ ๐ฅ ฬ
๐ค / Y = ฮฃ X ๊ ๐ค ฬ , (X โ Y)

total-fiber-is-domain : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } (f : X โ Y)
                      โ ฮฃ (fiber f) โ X

total-fiber-is-domain {๐ค} {๐ฅ} {X} {Y} f = invertibility-gives-โ g (h , ฮท , ฮต)
 where
  g : (ฮฃ y ๊ Y , ฮฃ x ๊ X , f x โก y) โ X
  g (y , x , p) = x

  h : X โ ฮฃ y ๊ Y , ฮฃ x ๊ X , f x โก y
  h x = (f x , x , refl (f x))

  ฮท : โ t โ h (g t) โก t
  ฮท (_ , x , refl _) = refl (f x , x , refl _)

  ฮต : (x : X) โ g (h x) โก x
  ฮต = refl

ฯ : (Y : ๐ค ฬ ) โ ๐ค / Y  โ (Y โ ๐ค ฬ )
ฯ Y (X , f) = fiber f

is-map-classifier : (๐ค : Universe) โ ๐ค โบ ฬ
is-map-classifier ๐ค = (Y : ๐ค ฬ ) โ is-equiv (ฯ Y)

๐ : (Y : ๐ค ฬ ) โ (Y โ ๐ค ฬ ) โ ๐ค / Y
๐ Y A = ฮฃ A , prโ

ฯฮท : is-univalent ๐ค
   โ (Y : ๐ค ฬ ) (ฯ : ๐ค / Y) โ ๐ Y (ฯ Y ฯ) โก ฯ

ฯฮท ua Y (X , f) = r
 where
  e : ฮฃ (fiber f) โ X
  e = total-fiber-is-domain f

  p : ฮฃ (fiber f) โก X
  p = EqโId ua (ฮฃ (fiber f)) X e

  observation : โ โ-sym e โ โก (ฮป x โ f x , x , refl (f x))
  observation = refl _

  q = transport (ฮป - โ - โ Y) p prโ โกโจ transport-map-along-โ ua e prโ โฉ
      prโ โ โ โ-sym e โ             โกโจ refl _ โฉ
      f                             โ

  r : (ฮฃ (fiber f) , prโ) โก (X , f)
  r = to-ฮฃ-โก (p , q)

ฯฮต : is-univalent ๐ค โ dfunext ๐ค (๐ค โบ)
   โ (Y : ๐ค ฬ ) (A : Y โ ๐ค ฬ ) โ ฯ Y (๐ Y A) โก A

ฯฮต ua fe Y A = fe ฮณ
 where
  f : โ y โ fiber prโ y โ A y
  f y ((y , a) , refl p) = a

  g : โ y โ A y โ fiber prโ y
  g y a = (y , a) , refl y

  ฮท : โ y ฯ โ g y (f y ฯ) โก ฯ
  ฮท y ((y , a) , refl p) = refl ((y , a) , refl p)

  ฮต : โ y a โ f y (g y a) โก a
  ฮต y a = refl a

  ฮณ : โ y โ fiber prโ y โก A y
  ฮณ y = EqโId ua _ _ (invertibility-gives-โ (f y) (g y , ฮท y , ฮต y))

universes-are-map-classifiers : is-univalent ๐ค โ dfunext ๐ค (๐ค โบ)
                              โ is-map-classifier ๐ค

universes-are-map-classifiers ua fe Y = invertibles-are-equivs (ฯ Y)
                                         (๐ Y , ฯฮท ua Y , ฯฮต ua fe Y)

map-classification : is-univalent ๐ค โ dfunext ๐ค (๐ค โบ)
                   โ (Y : ๐ค ฬ ) โ ๐ค / Y โ (Y โ ๐ค ฬ )

map-classification ua fe Y = ฯ Y , universes-are-map-classifiers ua fe Y

\end{code}
