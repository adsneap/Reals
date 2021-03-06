]\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Equiv where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Retracts
open import Unit-Properties

\end{code}

We take Joyal's version of the notion of equivalence as the primary
one because it is more symmetrical.

\begin{code}

is-equiv : {X : ð¤ Ì } {Y : ð¥ Ì } â (X â Y) â ð¤ â ð¥ Ì
is-equiv f = has-section f Ã is-section f

inverse : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
        â is-equiv f â (Y â X)
inverse f = prâ â prâ

equivs-have-sections : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                     â is-equiv f â has-section f
equivs-have-sections f = prâ

equivs-are-sections : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                    â is-equiv f â is-section f
equivs-are-sections f = prâ

section-retraction-equiv : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                         â has-section f â is-section f â is-equiv f
section-retraction-equiv f hr hs = (hr , hs)

equivs-are-lc : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
              â is-equiv f â left-cancellable f
equivs-are-lc f e = sections-are-lc f (equivs-are-sections f e)

_â_ : ð¤ Ì â ð¥ Ì â ð¤ â ð¥ Ì
X â Y = Î£ f ê (X â Y) , is-equiv f

Aut : ð¤ Ì â ð¤ Ì
Aut X = (X â X)

id-is-equiv : (X : ð¤ Ì ) â is-equiv (id {ð¤} {X})
id-is-equiv X = (id , Î» x â refl) , (id , Î» x â refl)

â-refl : (X : ð¤ Ì ) â X â X
â-refl X = id , id-is-equiv X

â-is-equiv : {X : ð¤ Ì } {Y : ð¥ Ì } {Z : ð¦ Ì } {f : X â Y} {f' : Y â Z}
           â is-equiv f â is-equiv f' â is-equiv (f' â f)
â-is-equiv {ð¤} {ð¥} {ð¦} {X} {Y} {Z} {f} {f'} ((g , fg) , (h , hf)) ((g' , fg') , (h' , hf')) =
 (g â g' , fg'') , (h â h' , hf'')
 where
  fg'' : (z : Z) â f' (f (g (g' z))) â¡ z
  fg'' z =  ap f' (fg (g' z)) â fg' z
  hf'' : (x : X) â h (h' (f' (f x))) â¡ x
  hf'' x = ap h (hf' (f x)) â hf x

\end{code}

For type-checking efficiency reasons:

\begin{code}

â-is-equiv-abstract : {X : ð¤ Ì } {Y : ð¥ Ì } {Z : ð¦ Ì } {f : X â Y} {f' : Y â Z}
                    â is-equiv f â is-equiv f' â is-equiv (f' â f)
â-is-equiv-abstract {ð¤} {ð¥} {ð¦} {X} {Y} {Z} {f} {f'} = Î³
 where
  abstract
   Î³ : is-equiv f â is-equiv f' â is-equiv (f' â f)
   Î³ = â-is-equiv

â-comp : {X : ð¤ Ì } {Y : ð¥ Ì } {Z : ð¦ Ì } â X â Y â Y â Z â X â Z
â-comp {ð¤} {ð¥} {ð¦} {X} {Y} {Z} (f , d) (f' , e) = f' â f , â-is-equiv d e

_â_ : {X : ð¤ Ì } {Y : ð¥ Ì } {Z : ð¦ Ì } â X â Y â Y â Z â X â Z
_â_ = â-comp

_ââ¨_â©_ : (X : ð¤ Ì ) {Y : ð¥ Ì } {Z : ð¦ Ì } â X â Y â Y â Z â X â Z
_ ââ¨ d â© e = d â e

_â  : (X : ð¤ Ì ) â X â X
_â  = â-refl

Eqtofun : (X : ð¤ Ì ) (Y : ð¥ Ì ) â X â Y â X â Y
Eqtofun X Y (f , _) = f

eqtofun â_â : {X : ð¤ Ì } {Y : ð¥ Ì } â X â Y â X â Y
eqtofun = Eqtofun _ _
â_â     = eqtofun

eqtofun- ââ-is-equiv : {X : ð¤ Ì } {Y : ð¥ Ì } (e : X â Y) â is-equiv â e â
eqtofun-     = prâ
ââ-is-equiv  = eqtofun-

back-eqtofun â_ââ»Â¹ : {X : ð¤ Ì } {Y : ð¥ Ì } â X â Y â Y â X
back-eqtofun e = prâ (prâ (prâ e))
â_ââ»Â¹          = back-eqtofun

idtoeq : (X Y : ð¤ Ì ) â X â¡ Y â X â Y
idtoeq X Y p = transport (X â_) p (â-refl X)

idtoeq-traditional : (X Y : ð¤ Ì ) â X â¡ Y â X â Y
idtoeq-traditional X _ refl = â-refl X

\end{code}

We would have a definitional equality if we had defined the traditional
one using J (based), but because of the idiosyncracies of Agda, we
don't with the current definition:

\begin{code}

eqtoeq-agreement : (X Y : ð¤ Ì ) (p : X â¡ Y)
                 â idtoeq X Y p â¡ idtoeq-traditional X Y p
eqtoeq-agreement {ð¤} X _ refl = refl

idtofun : (X Y : ð¤ Ì ) â X â¡ Y â X â Y
idtofun X Y p = â idtoeq X Y p â

idtofun-agreement : (X Y : ð¤ Ì ) (p : X â¡ Y) â idtofun X Y p â¡ Idtofun p
idtofun-agreement X Y refl = refl

equiv-closed-under-â¼ : {X : ð¤ Ì } {Y : ð¥ Ì } (f g : X â Y)
                     â is-equiv f
                     â  g â¼ f
                     â is-equiv g
equiv-closed-under-â¼ {ð¤} {ð¥} {X} {Y} f g (hass , hasr) h =
  has-section-closed-under-â¼ f g hass h ,
  is-section-closed-under-â¼ f g hasr h

equiv-closed-under-â¼' : {X : ð¤ Ì } {Y : ð¥ Ì } {f g : X â Y}
                      â is-equiv f
                      â f â¼ g
                      â is-equiv g
equiv-closed-under-â¼' ise h = equiv-closed-under-â¼  _ _ ise (Î» x â (h x)â»Â¹)

invertible : {X : ð¤ Ì } {Y : ð¥ Ì } â (X â Y) â ð¤ â ð¥ Ì
invertible f = Î£ g ê (codomain f â domain f), (g â f â¼ id) Ã (f â g â¼ id)

qinv = invertible

equivs-are-qinvs : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y) â is-equiv f â qinv f
equivs-are-qinvs {ð¤} {ð¥} {X} {Y} f ((s , fs) , (r , rf)) = s , (sf , fs)
 where
  sf : (x : X) â s (f x) â¡ x
  sf x = s (f x)         â¡â¨ (rf (s (f x)))â»Â¹ â©
         r (f (s (f x))) â¡â¨ ap r (fs (f x)) â©
         r (f x)         â¡â¨ rf x â©
         x               â

inverses-are-sections : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y) (e : is-equiv f)
                      â f â inverse f e â¼ id
inverses-are-sections f ((s , fs) , (r , rf)) = fs

inverses-are-retractions : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y) (e : is-equiv f)
                         â inverse f e â f â¼ id
inverses-are-retractions f e = prâ (prâ (equivs-are-qinvs f e))

inverses-are-equivs : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y) (e : is-equiv f)
                    â is-equiv (inverse f e)

inverses-are-equivs f e = (f , inverses-are-retractions f e) , (f , inverses-are-sections f e)

âââ»Â¹-is-equiv : {X : ð¤ Ì } {Y : ð¥ Ì } (e : X â Y) â is-equiv â e ââ»Â¹
âââ»Â¹-is-equiv (f , i) = inverses-are-equivs f i

inversion-involutive : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y) (e : is-equiv f)
                     â inverse (inverse f e) (inverses-are-equivs f e) â¡ f
inversion-involutive f e = refl

\end{code}

That the above proof is refl is an accident of our choice of notion of
equivalence as primary.

\begin{code}

qinvs-are-equivs : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y) â qinv f â is-equiv f
qinvs-are-equivs f (g , (gf , fg)) = (g , fg) , (g , gf)

qinveq : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y) â qinv f â X â Y
qinveq f q = (f , qinvs-are-equivs f q)

lc-split-surjections-are-equivs : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                               â left-cancellable f
                               â ((y : Y) â Î£ x ê X , f x â¡ y)
                               â is-equiv f
lc-split-surjections-are-equivs f l s = qinvs-are-equivs f (g , Î· , Îµ)
 where
  g : codomain f â domain f
  g y = prâ (s y)

  Îµ : f â g â¼ id
  Îµ y = prâ (s y)

  Î· : g â f â¼ id
  Î· x = l p
   where
    p : f (g (f x)) â¡ f x
    p = Îµ (f x)


â-sym : {X : ð¤ Ì } {Y : ð¥ Ì }  â X â Y â Y â X
â-sym {ð¤} {ð¥} {X} {Y} (f , e) = inverse f e , inverses-are-equivs f e

â-sym-is-linv : {X : ð¤ Ì } {Y : ð¥ Ì }  (ð¯ : X â Y)
              â â ð¯ ââ»Â¹ â â ð¯ â â¼ id
â-sym-is-linv (f , e) x = inverses-are-retractions f e x

â-sym-is-rinv : {X : ð¤ Ì } {Y : ð¥ Ì }  (ð¯ : X â Y)
              â â ð¯ â â â ð¯ ââ»Â¹ â¼ id
â-sym-is-rinv (f , e) y = inverses-are-sections f e y

â-gives-â : {X : ð¤ Ì } {Y : ð¥ Ì } â X â Y â X â Y
â-gives-â (f , (g , fg) , (h , hf)) = h , f , hf

â-gives-â· : {X : ð¤ Ì } {Y : ð¥ Ì } â X â Y â Y â X
â-gives-â· (f , (g , fg) , (h , hf)) = f , g , fg

Id-retract-l : {X Y : ð¤ Ì } â X â¡ Y â retract X of Y
Id-retract-l p = â-gives-â (idtoeq (lhs p) (rhs p) p)

Id-retract-r : {X Y : ð¤ Ì } â X â¡ Y â retract Y of X
Id-retract-r p = â-gives-â· (idtoeq (lhs p) (rhs p) p)

equiv-to-prop : {X : ð¤ Ì } {Y : ð¥ Ì } â Y â X â is-prop X â is-prop Y
equiv-to-prop e = retract-of-prop (â-gives-â e)

equiv-to-singleton : {X : ð¤ Ì } {Y : ð¥ Ì } â Y â X â is-singleton X â is-singleton Y
equiv-to-singleton e = retract-of-singleton (â-gives-â e)

equiv-to-singleton' : {X : ð¤ Ì } {Y : ð¥ Ì } â X â Y â is-singleton X â is-singleton Y
equiv-to-singleton' e = retract-of-singleton (â-gives-â· e)

pt-pf-equiv : {X : ð¤ Ì } (x : X) â singleton-type x â singleton-type' x
pt-pf-equiv x = f , ((g , fg) , (g , gf))
 where
  f : singleton-type x â singleton-type' x
  f (y , p) = y , (p â»Â¹)
  g : singleton-type' x â singleton-type x
  g (y , p) = y , (p â»Â¹)
  fg : f â g â¼ id
  fg (y , p) = ap (Î» - â y , -) (â»Â¹-involutive p)
  gf : g â f â¼ id
  gf (y , p) = ap (Î» - â y , -) (â»Â¹-involutive p)

singleton-types'-are-singletons : {X : ð¤ Ì } (x : X) â is-singleton (singleton-type' x)
singleton-types'-are-singletons x = retract-of-singleton
                                      (prâ (pt-pf-equiv x) ,
                                      (prâ (prâ ((pt-pf-equiv x)))))
                                      (singleton-types-are-singletons x)

singleton-types'-are-props : {X : ð¤ Ì } (x : X) â is-prop (singleton-type' x)
singleton-types'-are-props x = singletons-are-props (singleton-types'-are-singletons x)

\end{code}

Equivalence of transports.

\begin{code}

transports-are-equivs : {X : ð¤ Ì } {A : X â ð¥ Ì } {x y : X} (p : x â¡ y)
                      â is-equiv (transport A p)
transports-are-equivs refl = id-is-equiv _

back-transports-are-equivs : {X : ð¤ Ì } {A : X â ð¥ Ì } {x y : X} (p : x â¡ y)
                           â is-equiv (back-transport A p)
back-transports-are-equivs p = transports-are-equivs (p â»Â¹)

\end{code}

\begin{code}

fiber : {X : ð¤ Ì } {Y : ð¥ Ì } â (X â Y) â Y â ð¤ â ð¥ Ì
fiber f y = Î£ x ê domain f , f x â¡ y

fiber-point : {X : ð¤ Ì } {Y : ð¥ Ì } {f : X â Y} {y : Y} â fiber f y â X
fiber-point = prâ

fiber-identification : {X : ð¤ Ì } {Y : ð¥ Ì } {f : X â Y} {y : Y} (w : fiber f y) â f (fiber-point w) â¡ y
fiber-identification = prâ

is-vv-equiv : {X : ð¤ Ì } {Y : ð¥ Ì } â (X â Y) â ð¤ â ð¥ Ì
is-vv-equiv f = â y â is-singleton (fiber f y)

is-vv-equiv-NB : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y) â is-vv-equiv f â¡ (Î  y ê Y , â! x ê X , f x â¡ y)
is-vv-equiv-NB f = refl

vv-equivs-are-equivs : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                     â is-vv-equiv f â is-equiv f
vv-equivs-are-equivs {ð¤} {ð¥} {X} {Y} f Ï = (g , fg) , (g , gf)
 where
  Ï' : (y : Y) â Î£ c ê (Î£ x ê X , f x â¡ y) , ((Ï : Î£ x ê X , f x â¡ y) â c â¡ Ï)
  Ï' = Ï
  c : (y : Y) â Î£ x ê X , f x â¡ y
  c y = prâ (Ï y)
  d : (y : Y) â (Ï : Î£ x ê X , f x â¡ y) â c y â¡ Ï
  d y = prâ (Ï y)
  g : Y â X
  g y = prâ (c y)
  fg : (y : Y) â f (g y) â¡ y
  fg y = prâ (c y)
  e : (x : X) â g (f x) , fg (f x) â¡ x , refl
  e x = d (f x) (x , refl)
  gf : (x : X) â g (f x) â¡ x
  gf x = ap prâ (e x)

fiber' : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y) â Y â ð¤ â ð¥ Ì
fiber' f y = Î£ x ê domain f , y â¡ f x

fiber-lemma : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y) (y : Y) â fiber f y â fiber' f y
fiber-lemma f y = g , (h , gh) , (h , hg)
 where
  g : fiber f y â fiber' f y
  g (x , p) = x , (p â»Â¹)
  h : fiber' f y â fiber f y
  h (x , p) = x , (p â»Â¹)
  hg : â Ï â h (g Ï) â¡ Ï
  hg (x , refl) = refl
  gh : â Ï â g (h Ï) â¡ Ï
  gh (x , refl) = refl

is-hae : {X : ð¤ Ì } {Y : ð¥ Ì } â (X â Y) â ð¤ â ð¥ Ì
is-hae {ð¤} {ð¥} {X} {Y} f = Î£ g ê (Y â X)
                         , Î£ Î· ê g â f â¼ id
                         , Î£ Îµ ê f â g â¼ id
                         , Î  x ê X , ap f (Î· x) â¡ Îµ (f x)

haes-are-equivs : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                â is-hae f â is-equiv f
haes-are-equivs {ð¤} {ð¥} {X} f (g , Î· , Îµ , Ï) = qinvs-are-equivs f (g , Î· , Îµ)

id-homotopies-are-natural : {X : ð¤ Ì } (h : X â X) (Î· : h â¼ id) {x : X}
                          â Î· (h x) â¡ ap h (Î· x)
id-homotopies-are-natural h Î· {x} =
   Î· (h x)                         â¡â¨ refl â©
   Î· (h x) â refl                  â¡â¨ ap (Î» - â Î· (h x) â -) ((trans-sym' (Î· x))â»Â¹) â©
   Î· (h x) â (Î· x â (Î· x)â»Â¹)       â¡â¨ (âassoc (Î· (h x)) (Î· x) (Î· x â»Â¹))â»Â¹ â©
   Î· (h x) â Î· x â (Î· x)â»Â¹         â¡â¨ ap (Î» - â Î· (h x) â - â (Î· x)â»Â¹) ((ap-id-is-id' (Î· x))) â©
   Î· (h x) â ap id (Î· x) â (Î· x)â»Â¹ â¡â¨ homotopies-are-natural' h id Î· {h x} {x} {Î· x} â©
   ap h (Î· x)                      â

qinvs-are-haes : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y) â qinv f â is-hae f
qinvs-are-haes {ð¤} {ð¥} {X} {Y} f (g , (Î· , Îµ)) = g , Î· , Îµ' , Ï
 where
  Îµ' : f â g â¼ id
  Îµ' y = f (g y)         â¡â¨ (Îµ (f (g y)))â»Â¹ â©
         f (g (f (g y))) â¡â¨ ap f (Î· (g y)) â©
         f (g y)         â¡â¨ Îµ y â©
         y               â

  a : (x : X) â Î· (g (f x)) â¡ ap g (ap f (Î· x))
  a x = Î· (g (f x))      â¡â¨ id-homotopies-are-natural (g â f) Î· â©
        ap (g â f) (Î· x)  â¡â¨ (ap-ap f g (Î· x))â»Â¹ â©
        ap g (ap f (Î· x)) â

  b : (x : X) â ap f (Î· (g (f x))) â Îµ (f x) â¡ Îµ (f (g (f x))) â ap f (Î· x)
  b x = ap f (Î· (g (f x))) â Îµ (f x)         â¡â¨ ap (Î» - â - â Îµ (f x)) (ap (ap f) (a x)) â©
        ap f (ap g (ap f (Î· x))) â Îµ (f x)   â¡â¨ ap (Î» - â - â Îµ (f x)) (ap-ap g f (ap f (Î· x))) â©
        ap (f â g) (ap f (Î· x)) â Îµ (f x)    â¡â¨ (homotopies-are-natural (f â g) id Îµ {f (g (f x))} {f x} {ap f (Î· x)})â»Â¹ â©
        Îµ (f (g (f x))) â ap id (ap f (Î· x)) â¡â¨ ap (Î» - â Îµ (f (g (f x))) â -) (ap-ap f id (Î· x)) â©
        Îµ (f (g (f x))) â ap f (Î· x)         â

  Ï : (x : X) â ap f (Î· x) â¡ Îµ' (f x)
  Ï x = ap f (Î· x)                                           â¡â¨ refl-left-neutral â»Â¹ â©
        refl â ap f (Î· x)                                    â¡â¨ ap (Î» - â - â ap f (Î· x)) ((trans-sym (Îµ (f (g (f x)))))â»Â¹) â©
        (Îµ (f (g (f x))))â»Â¹ â Îµ (f (g (f x))) â ap f (Î· x)   â¡â¨ âassoc ((Îµ (f (g (f x))))â»Â¹) (Îµ (f (g (f x)))) (ap f (Î· x)) â©
        (Îµ (f (g (f x))))â»Â¹ â (Îµ (f (g (f x))) â ap f (Î· x)) â¡â¨ ap (Î» - â (Îµ (f (g (f x))))â»Â¹ â -) (b x)â»Â¹ â©
        (Îµ (f (g (f x))))â»Â¹ â (ap f (Î· (g (f x))) â Îµ (f x)) â¡â¨ refl â©
        Îµ' (f x)                                             â

equivs-are-haes : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                â is-equiv f â is-hae f
equivs-are-haes f e = qinvs-are-haes f (equivs-are-qinvs f e)

\end{code}

The following could be defined by combining functions we already have,
but a proof by path induction is direct:

\begin{code}

identifications-in-fibers : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                            (y : Y) (x x' : X) (p : f x â¡ y) (p' : f x' â¡ y)
                          â (Î£ Î³ ê x â¡ x' , ap f Î³ â p' â¡ p) â (x , p) â¡ (x' , p')
identifications-in-fibers f . (f x) x .x refl p' (refl , r) = g
 where
  g : x , refl â¡ x , p'
  g = ap (Î» - â (x , -)) (r â»Â¹ â refl-left-neutral)

\end{code}

Using this we see that half adjoint equivalences have singleton fibers:

\begin{code}

haes-are-vv-equivs : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                   â is-hae f â is-vv-equiv f
haes-are-vv-equivs {ð¤} {ð¥} {X} f (g , Î· , Îµ , Ï) y = (c , Î» Ï â Î± (prâ Ï) (prâ Ï))
 where
  c : fiber f y
  c = (g y , Îµ y)

  Î± : (x : X) (p : f x â¡ y) â c â¡ (x , p)
  Î± x p = Ï
   where
    Î³ : g y â¡ x
    Î³ = (ap g p)â»Â¹ â Î· x
    q : ap f Î³ â p â¡ Îµ y
    q = ap f Î³ â p                          â¡â¨ refl â©
        ap f ((ap g p)â»Â¹ â Î· x) â p         â¡â¨ ap (Î» - â - â p) (ap-â f ((ap g p)â»Â¹) (Î· x)) â©
        ap f ((ap g p)â»Â¹) â ap f (Î· x) â p  â¡â¨ ap (Î» - â ap f - â ap f (Î· x) â p) (ap-sym g p) â©
        ap f (ap g (p â»Â¹)) â ap f (Î· x) â p â¡â¨ ap (Î» - â ap f (ap g (p â»Â¹)) â - â p) (Ï x) â©
        ap f (ap g (p â»Â¹)) â Îµ (f x) â p    â¡â¨ ap (Î» - â - â Îµ (f x) â p) (ap-ap g f (p â»Â¹)) â©
        ap (f â g) (p â»Â¹) â Îµ (f x) â p     â¡â¨ ap (Î» - â - â p) (homotopies-are-natural (f â g) id Îµ {y} {f x} {p â»Â¹})â»Â¹ â©
        Îµ y â ap id (p â»Â¹) â p              â¡â¨ ap (Î» - â Îµ y â - â p) (ap-id-is-id (p â»Â¹)) â©
        Îµ y â p â»Â¹ â p                      â¡â¨ âassoc (Îµ y) (p â»Â¹) p         â©
        Îµ y â (p â»Â¹ â p)                    â¡â¨ ap (Î» - â Îµ y â -) (trans-sym p) â©
        Îµ y â refl                          â¡â¨ refl â©
        Îµ y                                 â

    Ï : g y , Îµ y â¡ x , p
    Ï = identifications-in-fibers f y (g y) x (Îµ y) p (Î³ , q)

\end{code}

Here are some corollaries:

\begin{code}

qinvs-are-vv-equivs : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                    â qinv f â is-vv-equiv f
qinvs-are-vv-equivs f q = haes-are-vv-equivs f (qinvs-are-haes f q)

equivs-are-vv-equivs : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                     â is-equiv f â is-vv-equiv f
equivs-are-vv-equivs f ie = qinvs-are-vv-equivs f (equivs-are-qinvs f ie)

\end{code}

We pause to characterize negation and singletons. Recall that Â¬ X and
is-empty X are synonyms for the function type X â ð.

\begin{code}

equiv-can-assume-pointed-codomain : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                                  â (Y â is-vv-equiv f) â is-vv-equiv f
equiv-can-assume-pointed-codomain f Ï y = Ï y y

maps-to-ð-are-equivs : {X : ð¤ Ì } (f : Â¬ X) â is-vv-equiv f
maps-to-ð-are-equivs f = equiv-can-assume-pointed-codomain f ð-elim

negations-are-equiv-to-ð : {X : ð¤ Ì } â is-empty X â X â ð
negations-are-equiv-to-ð = (Î» f â f , vv-equivs-are-equivs f (maps-to-ð-are-equivs f)), prâ

\end{code}

Then with functional and propositional extensionality, which follow
from univalence, we conclude that Â¬X = (X â 0) = (X â¡ 0).

And similarly, with similar a observation:

\begin{code}

singletons-are-equiv-to-ð : {X : ð¤ Ì } â is-singleton X â X â ð {ð¥}
singletons-are-equiv-to-ð {ð¤} {ð¥} {X} = forth , back
 where
  forth : is-singleton X â X â ð
  forth (xâ , Ï) = unique-to-ð , (((Î» _ â xâ) , (Î» x â (ð-all-â x)â»Â¹)) , ((Î» _ â xâ) , Ï))
  back : X â ð â is-singleton X
  back (f , (s , fs) , (r , rf)) = retract-of-singleton (r , f , rf) ð-is-singleton

\end{code}

The following again could be defined by combining functions we already
have:

\begin{code}

from-identifications-in-fibers : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                                 (y : Y) (x x' : X) (p : f x â¡ y) (p' : f x' â¡ y)
                               â (x , p) â¡ (x' , p') â Î£ Î³ ê x â¡ x' , ap f Î³ â p' â¡ p
from-identifications-in-fibers f . (f x) x .x refl .refl refl = refl , refl

Î·-pif : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
        (y : Y) (x x' : X) (p : f x â¡ y) (p' : f x' â¡ y)
        (Ï : Î£ Î³ ê x â¡ x' , ap f Î³ â p' â¡ p)
      â from-identifications-in-fibers f y x x' p p' (identifications-in-fibers f y x x' p p' Ï) â¡ Ï
Î·-pif f .(f x) x .x _ refl (refl , refl) = refl

\end{code}

Then the following is a consequence of natural-section-is-section,
but also has a direct proof by path induction:

\begin{code}
Îµ-pif : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
        (y : Y) (x x' : X) (p : f x â¡ y) (p' : f x' â¡ y)
        (q : (x , p) â¡ (x' , p'))
      â identifications-in-fibers f y x x' p p' (from-identifications-in-fibers f y x x' p p' q) â¡ q
Îµ-pif f .(f x) x .x refl .refl refl = refl

prâ-is-vv-equiv : (X : ð¤ Ì ) (Y : X â ð¥ Ì )
             â ((x : X) â is-singleton (Y x))
             â is-vv-equiv (prâ {ð¤} {ð¥} {X} {Y})
prâ-is-vv-equiv {ð¤} {ð¥} X Y iss x = g
 where
  c : fiber prâ x
  c = (x , prâ (iss x)) , refl
  p : (y : Y x) â prâ (iss x) â¡ y
  p = prâ (iss x)
  f : (w : Î£ Ï ê Î£ Y , prâ Ï â¡ x) â c â¡ w
  f ((.x , y) , refl) = ap (Î» - â (x , -) , refl) (p y)
  g : is-singleton (fiber prâ x)
  g = c , f

prâ-is-equiv : (X : ð¤ Ì ) (Y : X â ð¥ Ì )
             â ((x : X) â is-singleton (Y x))
             â is-equiv (prâ {ð¤} {ð¥} {X} {Y})
prâ-is-equiv {ð¤} {ð¥} X Y iss = vv-equivs-are-equivs prâ (prâ-is-vv-equiv X Y iss)

prâ-is-vv-equiv-converse : {X : ð¤ Ì } {A : X â ð¥ Ì }
                         â is-vv-equiv (prâ {ð¤} {ð¥} {X} {A})
                         â ((x : X) â is-singleton (A x))
prâ-is-vv-equiv-converse {ð¤} {ð¥} {X} {A} isv x = retract-of-singleton (r , s , rs) (isv x)
  where
    f : Î£ A â X
    f = prâ {ð¤} {ð¥} {X} {A}
    s : A x â fiber f x
    s a = (x , a) , refl
    r : fiber f x â A x
    r ((x , a) , refl) = a
    rs : (a : A x) â r (s a) â¡ a
    rs a = refl

logically-equivalent-props-give-is-equiv : {P : ð¤ Ì } {Q : ð¥ Ì }
                                         â is-prop P
                                         â is-prop Q
                                         â (f : P â Q)
                                         â (Q â P)
                                         â is-equiv f
logically-equivalent-props-give-is-equiv i j f g =
  qinvs-are-equivs f (g , (Î» x â i (g (f x)) x) ,
                          (Î» x â j (f (g x)) x))

logically-equivalent-props-are-equivalent : {P : ð¤ Ì } {Q : ð¥ Ì }
                                          â is-prop P
                                          â is-prop Q
                                          â (P â Q)
                                          â (Q â P)
                                          â P â Q
logically-equivalent-props-are-equivalent i j f g =
  (f , logically-equivalent-props-give-is-equiv i j f g)

equiv-to-set : {X : ð¤ Ì } {Y : ð¥ Ì } â X â Y â is-set Y â is-set X
equiv-to-set e = subtypes-of-sets-are-sets â e â (equivs-are-lc â e â (ââ-is-equiv e))
\end{code}

5th March 2019. A more direct proof that quasi-invertible maps
are Voevodky equivalences (have contractible fibers).

\begin{code}

qinv-is-vv-equiv : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y) â qinv f â is-vv-equiv f
qinv-is-vv-equiv {ð¤} {ð¥} {X} {Y} f (g , Î· , Îµ) yâ = Î³
 where
  a : (y : Y) â (f (g y) â¡ yâ) â (y â¡ yâ)
  a y = r , s , rs
   where
    r : y â¡ yâ â f (g y) â¡ yâ
    r p = Îµ y â p
    s : f (g y) â¡ yâ â y â¡ yâ
    s q = (Îµ y)â»Â¹ â q
    rs : (q : f (g y) â¡ yâ) â r (s q) â¡ q
    rs q = Îµ y â ((Îµ y)â»Â¹ â q) â¡â¨ (âassoc (Îµ y) ((Îµ y)â»Â¹) q)â»Â¹ â©
           (Îµ y â (Îµ y)â»Â¹) â q â¡â¨ ap (_â q) ((sym-is-inverse' (Îµ y))â»Â¹) â©
           refl â q            â¡â¨ refl-left-neutral â©
           q                   â
  b : fiber f yâ â singleton-type' yâ
  b = (Î£ x ê X , f x â¡ yâ)     ââ¨ Î£-reindex-retract g (f , Î·) â©
      (Î£ y ê Y , f (g y) â¡ yâ) ââ¨ Î£-retract (Î» y â f (g y) â¡ yâ) (Î» y â y â¡ yâ) a â©
      (Î£ y ê Y , y â¡ yâ)       â
  Î³ : is-contr (fiber f yâ)
  Î³ = retract-of-singleton b (singleton-types'-are-singletons yâ)

maps-of-singletons-are-equivs : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                              â is-singleton X â is-singleton Y â is-equiv f
maps-of-singletons-are-equivs f (c , Ï) (d , Î³) =
 ((Î» y â c) , (Î» x â f c â¡â¨ singletons-are-props (d , Î³) (f c) x â©
                     x   â)) ,
 ((Î» y â c) , Ï)

is-fiberwise-equiv : {X : ð¤ Ì } {A : X â ð¥ Ì } {B : X â ð¦ Ì } â Nat A B â ð¤ â ð¥ â ð¦ Ì
is-fiberwise-equiv Ï = â x â is-equiv (Ï x)

\end{code}

Added 1st December 2019.

Sometimes it is is convenient to reason with quasi-equivalences
directly, in particular if we want to avoid function extensionality,
and we introduce some machinery for this.

\begin{code}

_â_ : ð¤ Ì â ð¥ Ì â ð¤ â ð¥ Ì
X â Y = Î£ f ê (X â Y) , qinv f

id-qinv : (X : ð¤ Ì ) â qinv (id {ð¤} {X})
id-qinv X = id , (Î» x â refl) , (Î» x â refl)

â-refl : (X : ð¤ Ì ) â X â X
â-refl X = id , (id-qinv X)

â-qinv : {X : ð¤ Ì } {Y : ð¥ Ì } {Z : ð¦ Ì } {f : X â Y} {f' : Y â Z}
       â qinv f â qinv f' â qinv (f' â f)
â-qinv {ð¤} {ð¥} {ð¦} {X} {Y} {Z} {f} {f'} = Î³
 where
   Î³ : qinv f â qinv f' â qinv (f' â f)
   Î³ (g , gf , fg) (g' , gf' , fg') = (g â g' , gf'' , fg'' )
    where
     fg'' : (z : Z) â f' (f (g (g' z))) â¡ z
     fg'' z =  ap f' (fg (g' z)) â fg' z
     gf'' : (x : X) â g (g' (f' (f x))) â¡ x
     gf'' x = ap g (gf' (f x)) â gf x

â-comp : {X : ð¤ Ì } {Y : ð¥ Ì } {Z : ð¦ Ì } â X â Y â Y â Z â X â Z
â-comp {ð¤} {ð¥} {ð¦} {X} {Y} {Z} (f , d) (f' , e) = f' â f , â-qinv d e

_ââ¨_â©_ : (X : ð¤ Ì ) {Y : ð¥ Ì } {Z : ð¦ Ì } â X â Y â Y â Z â X â Z
_ ââ¨ d â© e = â-comp d e

_â¾ : (X : ð¤ Ì ) â X â X
_â¾ = â-refl

\end{code}

Associativities and precedences.

\begin{code}

infix  0 _â_
infix  0 _â_
infix  1 _â 
infixr 0 _ââ¨_â©_
infixl 2 _â_
infix  1 â_â
\end{code}
