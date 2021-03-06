Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module MGS-FunExt-from-Univalence where

open import MGS-Equivalence-Induction public

funext : â đ¤ đĽ â (đ¤ â đĽ)âş Ě
funext đ¤ đĽ = {X : đ¤ Ě } {Y : đĽ Ě } {f g : X â Y} â f âź g â f âĄ g

precomp-is-equiv : is-univalent đ¤
                 â (X Y : đ¤ Ě ) (f : X â Y)
                 â is-equiv f
                 â (Z : đ¤ Ě ) â is-equiv (Îť (g : Y â Z) â g â f)

precomp-is-equiv {đ¤} ua =
   đ-equiv ua
     (Îť X Y (f : X â Y) â (Z : đ¤ Ě ) â is-equiv (Îť g â g â f))
     (Îť X Z â id-is-equiv (X â Z))

univalence-gives-funext : is-univalent đ¤ â funext đĽ đ¤
univalence-gives-funext {đ¤} {đĽ} ua {X} {Y} {fâ} {fâ} = Îł
 where
  Î : đ¤ Ě
  Î = ÎŁ yâ ę Y , ÎŁ yâ ę Y , yâ âĄ yâ

  Î´ : Y â Î
  Î´ y = (y , y , refl y)

  Ďâ Ďâ : Î â Y
  Ďâ (yâ , yâ , p) = yâ
  Ďâ (yâ , yâ , p) = yâ

  Î´-is-equiv : is-equiv Î´
  Î´-is-equiv = invertibles-are-equivs Î´ (Ďâ , Îˇ , Îľ)
   where
    Îˇ : (y : Y) â Ďâ (Î´ y) âĄ y
    Îˇ y = refl y

    Îľ : (d : Î) â Î´ (Ďâ d) âĄ d
    Îľ (y , y , refl y) = refl (y , y , refl y)

  Ď : (Î â Y) â (Y â Y)
  Ď Ď = Ď â Î´

  Ď-is-equiv : is-equiv Ď
  Ď-is-equiv = precomp-is-equiv ua Y Î Î´ Î´-is-equiv Y

  p : Ď Ďâ âĄ Ď Ďâ
  p = refl (đđ Y)

  q : Ďâ âĄ Ďâ
  q = equivs-are-lc Ď Ď-is-equiv p

  Îł : fâ âź fâ â fâ âĄ fâ
  Îł h = ap (Îť Ď x â Ď (fâ x , fâ x , h x)) q

  Îł' : fâ âź fâ â fâ âĄ fâ
  Îł' h = fâ                             âĄâ¨ refl _ âŠ
         (Îť x â fâ x)                   âĄâ¨ refl _ âŠ
         (Îť x â Ďâ (fâ x , fâ x , h x)) âĄâ¨ ap (Îť - x â - (fâ x , fâ x , h x)) q âŠ
         (Îť x â Ďâ (fâ x , fâ x , h x)) âĄâ¨ refl _ âŠ
         (Îť x â fâ x)                   âĄâ¨ refl _ âŠ
         fâ                             â

dfunext : â đ¤ đĽ â (đ¤ â đĽ)âş Ě
dfunext đ¤ đĽ = {X : đ¤ Ě } {A : X â đĽ Ě } {f g : Î  A} â f âź g â f âĄ g

happly : {X : đ¤ Ě } {A : X â đĽ Ě } (f g : Î  A) â f âĄ g â f âź g
happly f g p x = ap (Îť - â - x) p

hfunext : â đ¤ đĽ â (đ¤ â đĽ)âş Ě
hfunext đ¤ đĽ = {X : đ¤ Ě } {A : X â đĽ Ě } (f g : Î  A) â is-equiv (happly f g)

hfunext-gives-dfunext : hfunext đ¤ đĽ â dfunext đ¤ đĽ
hfunext-gives-dfunext hfe {X} {A} {f} {g} = inverse (happly f g) (hfe f g)

vvfunext : â đ¤ đĽ â (đ¤ â đĽ)âş Ě
vvfunext đ¤ đĽ = {X : đ¤ Ě } {A : X â đĽ Ě }
             â ((x : X) â is-singleton (A x))
             â is-singleton (Î  A)

dfunext-gives-vvfunext : dfunext đ¤ đĽ â vvfunext đ¤ đĽ
dfunext-gives-vvfunext fe {X} {A} i = Îł
 where
  f : Î  A
  f x = center (A x) (i x)

  c : (g : Î  A) â f âĄ g
  c g = fe (Îť (x : X) â centrality (A x) (i x) (g x))

  Îł : is-singleton (Î  A)
  Îł = f , c

postcomp-invertible : {X : đ¤ Ě } {Y : đĽ Ě } {A : đŚ Ě }
                    â funext đŚ đ¤
                    â funext đŚ đĽ
                    â (f : X â Y)
                    â invertible f
                    â invertible (Îť (h : A â X) â f â h)

postcomp-invertible {đ¤} {đĽ} {đŚ} {X} {Y} {A} nfe nfe' f (g , Îˇ , Îľ) = Îł
 where
  f' : (A â X) â (A â Y)
  f' h = f â h

  g' : (A â Y) â (A â X)
  g' k = g â k

  Îˇ' : (h : A â X) â g' (f' h) âĄ h
  Îˇ' h = nfe (Îˇ â h)

  Îľ' : (k : A â Y) â f' (g' k) âĄ k
  Îľ' k = nfe' (Îľ â k)

  Îł : invertible f'
  Îł = (g' , Îˇ' , Îľ')

postcomp-is-equiv : {X : đ¤ Ě } {Y : đĽ Ě } {A : đŚ Ě }
                  â funext đŚ đ¤
                  â funext đŚ đĽ
                  â (f : X â Y)
                  â is-equiv f
                  â is-equiv (Îť (h : A â X) â f â h)

postcomp-is-equiv fe fe' f e =
 invertibles-are-equivs
  (Îť h â f â h)
  (postcomp-invertible fe fe' f (equivs-are-invertible f e))

vvfunext-gives-hfunext : vvfunext đ¤ đĽ â hfunext đ¤ đĽ
vvfunext-gives-hfunext vfe {X} {Y} f = Îł
 where
  a : (x : X) â is-singleton (ÎŁ y ę Y x , f x âĄ y)
  a x = singleton-types'-are-singletons (Y x) (f x)

  c : is-singleton (Î  x ę X , ÎŁ y ę Y x , f x âĄ y)
  c = vfe a

  Ď : (ÎŁ g ę Î  Y , f âź g) â (Î  x ę X , ÎŁ y ę Y x , f x âĄ y)
  Ď = â-gives-âˇ Î ÎŁ-distr-â

  d : is-singleton (ÎŁ g ę Î  Y , f âź g)
  d = retract-of-singleton Ď c

  e : (ÎŁ g ę Î  Y , f âĄ g) â (ÎŁ g ę Î  Y , f âź g)
  e = NatÎŁ (happly f)

  i : is-equiv e
  i = maps-of-singletons-are-equivs e (singleton-types'-are-singletons (Î  Y) f) d

  Îł : (g : Î  Y) â is-equiv (happly f g)
  Îł = NatÎŁ-equiv-gives-fiberwise-equiv (happly f) i

funext-gives-vvfunext : funext đ¤ (đ¤ â đĽ) â funext đ¤ đ¤ â vvfunext đ¤ đĽ
funext-gives-vvfunext {đ¤} {đĽ} fe fe' {X} {A} Ď = Îł
 where
  f : ÎŁ A â X
  f = prâ

  f-is-equiv : is-equiv f
  f-is-equiv = prâ-equiv Ď

  g : (X â ÎŁ A) â (X â X)
  g h = f â h

  e : is-equiv g
  e = postcomp-is-equiv fe fe' f f-is-equiv

  i : is-singleton (ÎŁ h ę (X â ÎŁ A), f â h âĄ đđ X)
  i = e (đđ X)

  r : (ÎŁ h ę (X â ÎŁ A), f â h âĄ đđ X) â Î  A
  r (h , p) x = transport A (happly (f â h) (đđ X) p x) (prâ (h x))

  s : Î  A â (ÎŁ h ę (X â ÎŁ A), f â h âĄ đđ X)
  s Ď = (Îť x â x , Ď x) , refl (đđ X)

  Îˇ : â Ď â r (s Ď) âĄ Ď
  Îˇ Ď = refl (r (s Ď))

  Îł : is-singleton (Î  A)
  Îł = retract-of-singleton (r , s , Îˇ) i

abstract
 funext-gives-hfunext       : funext đ¤ (đ¤ â đĽ) â funext đ¤ đ¤ â hfunext đ¤ đĽ
 dfunext-gives-hfunext      : dfunext đ¤ đĽ â hfunext đ¤ đĽ
 funext-gives-dfunext       : funext đ¤ (đ¤ â đĽ) â funext đ¤ đ¤ â dfunext đ¤ đĽ
 univalence-gives-dfunext'  : is-univalent đ¤ â is-univalent (đ¤ â đĽ) â dfunext đ¤ đĽ
 univalence-gives-hfunext'  : is-univalent đ¤ â is-univalent (đ¤ â đĽ) â hfunext đ¤ đĽ
 univalence-gives-vvfunext' : is-univalent đ¤ â is-univalent (đ¤ â đĽ) â vvfunext đ¤ đĽ
 univalence-gives-hfunext   : is-univalent đ¤ â hfunext đ¤ đ¤
 univalence-gives-dfunext   : is-univalent đ¤ â dfunext đ¤ đ¤
 univalence-gives-vvfunext  : is-univalent đ¤ â vvfunext đ¤ đ¤

 funext-gives-hfunext fe fe' = vvfunext-gives-hfunext (funext-gives-vvfunext fe fe')

 funext-gives-dfunext fe fe' = hfunext-gives-dfunext (funext-gives-hfunext fe fe')

 dfunext-gives-hfunext fe = vvfunext-gives-hfunext (dfunext-gives-vvfunext fe)

 univalence-gives-dfunext' ua ua' = funext-gives-dfunext
                                     (univalence-gives-funext ua')
                                     (univalence-gives-funext ua)

 univalence-gives-hfunext' ua ua' = funext-gives-hfunext
                                      (univalence-gives-funext ua')
                                      (univalence-gives-funext ua)

 univalence-gives-vvfunext' ua ua' = funext-gives-vvfunext
                                      (univalence-gives-funext ua')
                                      (univalence-gives-funext ua)

 univalence-gives-hfunext ua = univalence-gives-hfunext' ua ua

 univalence-gives-dfunext ua = univalence-gives-dfunext' ua ua

 univalence-gives-vvfunext ua = univalence-gives-vvfunext' ua ua

\end{code}
