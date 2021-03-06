Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module MGS-Powerset where

open import MGS-More-FunExt-Consequences public

propext : โ ๐ค  โ ๐ค โบ ฬ
propext ๐ค = {P Q : ๐ค ฬ } โ is-prop P โ is-prop Q โ (P โ Q) โ (Q โ P) โ P โก Q

global-propext : ๐คฯ
global-propext = โ {๐ค} โ propext ๐ค

univalence-gives-propext : is-univalent ๐ค โ propext ๐ค
univalence-gives-propext ua {P} {Q} i j f g = EqโId ua P Q ฮณ
 where
  ฮณ : P โ Q
  ฮณ = logically-equivalent-subsingletons-are-equivalent P Q i j (f , g)

Id-from-subsingleton : propext ๐ค โ dfunext ๐ค ๐ค
                     โ (P : ๐ค ฬ )
                     โ is-subsingleton P
                     โ (X : ๐ค ฬ ) โ is-subsingleton (P โก X)

Id-from-subsingleton {๐ค} pe fe P i = Hedberg P (ฮป X โ h X , k X)
 where
  module _ (X : ๐ค ฬ ) where
   f : P โก X โ is-subsingleton X ร (P โ X)
   f p = transport is-subsingleton p i , Idโfun p , (Idโfun (p โปยน))

   g : is-subsingleton X ร (P โ X) โ P โก X
   g (l , ฯ , ฯ) = pe i l ฯ ฯ

   h : P โก X โ P โก X
   h = g โ f

   j : is-subsingleton (is-subsingleton X ร (P โ X))
   j = ร-is-subsingleton'
        ((ฮป (_ : P โ X) โ being-subsingleton-is-subsingleton fe) ,
         (ฮป (l : is-subsingleton X) โ ร-is-subsingleton
                                       (ฮ -is-subsingleton fe (ฮป p โ l))
                                       (ฮ -is-subsingleton fe (ฮป x โ i))))

   k : wconstant h
   k p q = ap g (j (f p) (f q))

subsingleton-univalence : propext ๐ค โ dfunext ๐ค ๐ค
                        โ (P : ๐ค ฬ )
                        โ is-subsingleton P
                        โ (X : ๐ค ฬ ) โ is-equiv (IdโEq P X)

subsingleton-univalence pe fe P i X = ฮณ
 where
  l : P โ X โ is-subsingleton X
  l e = equiv-to-subsingleton (โ-sym e) i

  eqtoid : P โ X โ P โก X
  eqtoid e = pe i (equiv-to-subsingleton (โ-sym e) i)
                  โ e โ โ โ-sym e โ

  m : is-subsingleton (P โ X)
  m (f , k) (f' , k') = to-subtype-โก
                          (being-equiv-is-subsingleton fe fe)
                          (fe (ฮป x โ j (f x) (f' x)))
    where
     j : is-subsingleton X
     j = equiv-to-subsingleton (โ-sym (f , k)) i

  ฮต : (e : P โ X) โ IdโEq P X (eqtoid e) โก e
  ฮต e = m (IdโEq P X (eqtoid e)) e

  ฮท : (q : P โก X) โ eqtoid (IdโEq P X q) โก q
  ฮท q = Id-from-subsingleton pe fe P i X (eqtoid (IdโEq P X q)) q

  ฮณ : is-equiv (IdโEq P X)
  ฮณ = invertibles-are-equivs (IdโEq P X) (eqtoid , ฮท , ฮต)

subsingleton-univalence-โ : propext ๐ค โ dfunext ๐ค ๐ค
                          โ (X P : ๐ค ฬ ) โ is-subsingleton P โ (P โก X) โ (P โ X)

subsingleton-univalence-โ pe fe X P i = IdโEq P X ,
                                        subsingleton-univalence pe fe P i X

ฮฉ : (๐ค : Universe) โ ๐ค โบ ฬ
ฮฉ ๐ค = ฮฃ P ๊ ๐ค ฬ , is-subsingleton P

_holds : ฮฉ ๐ค โ ๐ค ฬ
_holds (P , i) = P

holds-is-subsingleton : (p : ฮฉ ๐ค) โ is-subsingleton (p holds)
holds-is-subsingleton (P , i) = i

ฮฉ-ext : dfunext ๐ค ๐ค โ propext ๐ค โ {p q : ฮฉ ๐ค}
      โ (p holds โ q holds) โ (q holds โ p holds) โ p โก q

ฮฉ-ext {๐ค} fe pe {p} {q} f g = to-subtype-โก
                                 (ฮป _ โ being-subsingleton-is-subsingleton fe)
                                 (pe (holds-is-subsingleton p) (holds-is-subsingleton q) f g)

ฮฉ-is-set : dfunext ๐ค ๐ค โ propext ๐ค โ is-set (ฮฉ ๐ค)
ฮฉ-is-set {๐ค} fe pe = types-with-wconstant-โก-endomaps-are-sets (ฮฉ ๐ค) c
 where
  A : (p q : ฮฉ ๐ค) โ ๐ค ฬ
  A p q = (p holds โ q holds) ร (q holds โ p holds)

  i : (p q : ฮฉ ๐ค) โ is-subsingleton (A p q)
  i p q = ฮฃ-is-subsingleton
           (ฮ -is-subsingleton fe
             (ฮป _ โ holds-is-subsingleton q))
             (ฮป _ โ ฮ -is-subsingleton fe (ฮป _ โ holds-is-subsingleton p))

  g : (p q : ฮฉ ๐ค) โ p โก q โ A p q
  g p q e = (u , v)
   where
    a : p holds โก q holds
    a = ap _holds e

    u : p holds โ q holds
    u = Idโfun a

    v : q holds โ p holds
    v = Idโfun (a โปยน)

  h : (p q : ฮฉ ๐ค) โ A p q โ p โก q
  h p q (u , v) = ฮฉ-ext fe pe u v

  f : (p q : ฮฉ ๐ค) โ p โก q โ p โก q
  f p q e = h p q (g p q e)

  k : (p q : ฮฉ ๐ค) (d e : p โก q) โ f p q d โก f p q e
  k p q d e = ap (h p q) (i p q (g p q d) (g p q e))

  c : (p q : ฮฉ ๐ค) โ ฮฃ f ๊ (p โก q โ p โก q), wconstant f
  c p q = (f p q , k p q)

powersets-are-sets : hfunext ๐ค (๐ฅ โบ) โ dfunext ๐ฅ ๐ฅ โ propext ๐ฅ
                   โ {X : ๐ค ฬ } โ is-set (X โ ฮฉ ๐ฅ)

powersets-are-sets fe fe' pe = ฮ -is-set fe (ฮป x โ ฮฉ-is-set fe' pe)

๐ : ๐ค ฬ โ ๐ค โบ ฬ
๐ {๐ค} X = X โ ฮฉ ๐ค

powersets-are-sets' : Univalence
                    โ {X : ๐ค ฬ } โ is-set (๐ X)

powersets-are-sets' {๐ค} ua = powersets-are-sets
                               (univalence-gives-hfunext' (ua ๐ค) (ua (๐ค โบ)))
                               (univalence-gives-dfunext (ua ๐ค))
                               (univalence-gives-propext (ua ๐ค))

_โ_ : {X : ๐ค ฬ } โ X โ ๐ X โ ๐ค ฬ
x โ A = A x holds

_โ_ : {X : ๐ค ฬ } โ ๐ X โ ๐ X โ ๐ค ฬ
A โ B = โ x โ x โ A โ x โ B

โ-is-subsingleton : {X : ๐ค ฬ } (A : ๐ X) (x : X) โ is-subsingleton (x โ A)
โ-is-subsingleton A x = holds-is-subsingleton (A x)

โ-is-subsingleton : dfunext ๐ค ๐ค
                  โ {X : ๐ค ฬ } (A B : ๐ X) โ is-subsingleton (A โ B)

โ-is-subsingleton fe A B = ฮ -is-subsingleton fe
                            (ฮป x โ ฮ -is-subsingleton fe
                            (ฮป _ โ โ-is-subsingleton B x))

โ-refl : {X : ๐ค ฬ } (A : ๐ X) โ A โ A
โ-refl A x = ๐๐ (x โ A)

โ-refl-consequence : {X : ๐ค ฬ } (A B : ๐ X)
                   โ A โก B โ (A โ B) ร (B โ A)

โ-refl-consequence {X} A A (refl A) = โ-refl A , โ-refl A

subset-extensionality : propext ๐ค โ dfunext ๐ค ๐ค โ dfunext ๐ค (๐ค โบ)
                      โ {X : ๐ค ฬ } {A B : ๐ X}
                      โ A โ B โ B โ A โ A โก B

subset-extensionality pe fe fe' {X} {A} {B} h k = fe' ฯ
 where
  ฯ : (x : X) โ A x โก B x
  ฯ x = to-subtype-โก
           (ฮป _ โ being-subsingleton-is-subsingleton fe)
           (pe (holds-is-subsingleton (A x)) (holds-is-subsingleton (B x))
               (h x) (k x))

subset-extensionality' : Univalence
                       โ {X : ๐ค ฬ } {A B : ๐ X}
                       โ A โ B โ B โ A โ A โก B

subset-extensionality' {๐ค} ua = subset-extensionality
                                 (univalence-gives-propext (ua ๐ค))
                                 (univalence-gives-dfunext (ua ๐ค))
                                 (univalence-gives-dfunext' (ua ๐ค) (ua (๐ค โบ)))
infix  40 _โ_

\end{code}
