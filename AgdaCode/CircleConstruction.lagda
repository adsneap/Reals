Tom de Jong, 28 January 2021
(Following Bezem, Buchholtz, Grayson and Shulman)

We construct the circle ðÂ¹ as the type of â¤-torsors, following "Construction of
the circle in UniMath" by Bezem, Buchholtz, Grayson and Shulman
(doi:10.1016/j.jpaa.2021.106687). The construction needs univalence of ð¤â,
propositional truncations and function extensionality for every two universes.

Rather than proving the induction principle directly as in "Construction of the
circle in UniMath", we prove the induction principle abstractly from the
universal property.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base

open import UF-Embeddings
open import UF-Equiv hiding (_â_)
open import UF-EquivalenceExamples
open import UF-Equiv-FunExt
open import UF-FunExt
open import UF-Lower-FunExt
open import UF-SIP
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-PropTrunc
open import UF-Univalence
open import UF-UA-FunExt

open import Integers
open import Integers-Properties
open import Integers-SymmetricInduction

module CircleConstruction
        (pt : propositional-truncations-exist)
        (ua : is-univalent ð¤â)
       where

feâ : funext ð¤â ð¤â
feâ = univalence-gives-funext ua

open PropositionalTruncation pt
open sip
open sip-with-axioms

\end{code}

The pointed type of â¤-torsors base : Tâ¤. This type is connected (like ðÂ¹) almost
by definition.

\begin{code}

Tâ¤ : ð¤â Ì
Tâ¤ = Î£ X ê ð¤â Ì , Î£ f ê (X â X) , â¥ (â¤ , succ-â¤) â¡ (X , f) â¥

base : Tâ¤
base = (â¤ , succ-â¤ , â£ refl â£)

Tâ¤-is-connected : (X Y : Tâ¤) â â¥ X â¡ Y â¥
Tâ¤-is-connected (X , f , p) (Y , g , q) = â¥â¥-rec â¥â¥-is-prop Ï p
 where
  Ï : (â¤ , succ-â¤) â¡ (X , f)
    â â¥ X , f , p â¡ Y , g , q â¥
  Ï refl = â¥â¥-rec â¥â¥-is-prop Ï q
   where
    Ï : (â¤ , succ-â¤) â¡ (Y , g)
      â â¥ â¤ , succ-â¤ , p â¡ Y , g , q â¥
    Ï refl = â£ ap â Î£-assoc â (to-subtype-â¡ (Î» _ â â¥â¥-is-prop) refl) â£

\end{code}

Next, we wish to define loop : base â¡ base. To this end, we first characterize
equality of â¤-torsors, for which we use the Structure Identity Principle.

\begin{code}

_â_ : Tâ¤ â Tâ¤ â ð¤â Ì
(X , f , _) â (Y , g , _) = Î£ e ê (X â Y) , is-equiv e
                                          Ã (e â f â¡ g â e)

Tâ¤-structure : ð¤â Ì â ð¤â Ì
Tâ¤-structure X = X â X

Tâ¤â» : ð¤â Ì
Tâ¤â» = Î£ X ê ð¤â Ì , Tâ¤-structure X

sns-data : SNS Tâ¤-structure ð¤â
sns-data = (Î¹ , Ï , Î¸)
 where
  Î¹ : (X Y : Tâ¤â») â â¨ X â© â â¨ Y â© â ð¤â Ì
  Î¹ (X , f) (Y , g) (e , _) = e â f â¡ g â e
  Ï : (X : Tâ¤â») â Î¹ X X (â-refl â¨ X â©)
  Ï (X , f) = refl
  h : {X : ð¤â Ì } {f g : Tâ¤-structure X}
    â canonical-map Î¹ Ï f g â¼ id {ð¤â} {f â¡ g}
  h refl = refl
  Î¸ : {X : ð¤â Ì} (f g : Tâ¤-structure X)
    â is-equiv (canonical-map Î¹ Ï f g)
  Î¸ f g = equiv-closed-under-â¼ _ _ (id-is-equiv (f â¡ g)) h

characterization-of-Tâ¤-â¡ : (X Y : Tâ¤)
                         â (X â¡ Y) â (X â Y)
characterization-of-Tâ¤-â¡ =
 characterization-of-â¡-with-axioms ua
  sns-data
  (Î» X f â â¥ (â¤ , succ-â¤) â¡ (X , f) â¥)
  (Î» X f â â¥â¥-is-prop)

to-Tâ¤-â¡ : (X Y : Tâ¤) â X â Y â X â¡ Y
to-Tâ¤-â¡ X Y = â characterization-of-Tâ¤-â¡ X Y ââ»Â¹

loop-â : base â base
loop-â = (succ-â¤ , succ-â¤-is-equiv , refl)

loop : base â¡ base
loop = to-Tâ¤-â¡ base base loop-â

\end{code}

Another nice consequence of having characterized the equality of â¤-torsors (and
the symmetric induction principle of â¤) is that we can quickly prove that
(base â¡ base) â â¤.

\begin{code}

loops-at-base-equivalent-to-â¤ : (base â¡ base) â â¤
loops-at-base-equivalent-to-â¤ =
 (base â¡ base)                                            ââ¨ I   â©
 (Î£ e ê (â¤ â â¤) , is-equiv e Ã (e â succ-â¤ â¡ succ-â¤ â e)) ââ¨ II  â©
 (Î£ e ê (â¤ â â¤) , is-equiv e Ã (e â succ-â¤ â¼ succ-â¤ â e)) ââ¨ III â©
 (Î£ e ê (â¤ â â¤) , (e â succ-â¤ â¼ succ-â¤ â e) Ã is-equiv e) ââ¨ IV  â©
 (Î£ e ê (â¤ â â¤) , (e â succ-â¤ â¼ succ-â¤ â e))              ââ¨ V   â©
 â¤                                                        â 
  where
   I   = characterization-of-Tâ¤-â¡ base base
   II  = Î£-cong (Î» e â Ã-cong (â-refl (is-equiv e))
                              (â-funext feâ (e â succ-â¤) (succ-â¤ â e)))
   III = Î£-cong (Î» e â Ã-comm)
   IV  = Î£-cong Î³
    where
     Î³ : (e : â¤ â â¤)
       â (e â succ-â¤ â¼ succ-â¤ â e) Ã is-equiv e
       â (e â succ-â¤ â¼ succ-â¤ â e)
     Î³ e = qinveq prâ (Ï , Î· , Îµ)
      where
       Ï : e â succ-â¤ â¼ succ-â¤ â e
         â (e â succ-â¤ â¼ succ-â¤ â e) Ã is-equiv e
       Ï c = (c , is-equiv-if-commute-with-succ-â¤ e c)
       Î· : Ï â prâ â¼ id
       Î· (i , c) = to-subtype-â¡
                    (Î» _ â being-equiv-is-prop' feâ feâ feâ feâ e) refl
       Îµ : prâ â Ï â¼ id
       Îµ _ = refl
   V   = â¤-symmetric-induction feâ (Î» _ â â¤) (Î» _ â succ-â¤-â)

â¨_â©â : (X : Tâ¤) â â¨ X â© â â¨ X â©
â¨ (X , f , t) â©â = f

_â» : Tâ¤ â Tâ¤â»
X â» = â¨ X â© , â¨ X â©â

Tâ¤-â¡-from-Tâ¤â»-â¡ : {X Y : Tâ¤} â X â» â¡ Y â» â X â¡ Y
Tâ¤-â¡-from-Tâ¤â»-â¡ q = ap â Î£-assoc â (to-subtype-â¡ (Î» _ â â¥â¥-is-prop) q)

\end{code}

The connectedness of Tâ¤ gets us the following propositional induction principle,
which allows us to prove some further properties of â¤-torsors. What's remarkable
(and in my opinion this is the crux of the paper by Bezem et al.) is that this
principle can be used to get the full recursion principle for Tâ¤.

\begin{code}

Tâ¤-prop-induction : {ð¤ : Universe} {P : Tâ¤ â ð¤ Ì }
                  â ((X : Tâ¤) â is-prop (P X))
                  â P base
                  â (X : Tâ¤) â P X
Tâ¤-prop-induction {ð¤} {P} i p (X , f , t) = â¥â¥-rec (i (X , f , t)) Î³ t
 where
  Î³ : (â¤ , succ-â¤) â¡ (X , f) â P (X , f , t)
  Î³ q = transport P (Tâ¤-â¡-from-Tâ¤â»-â¡ q) p

â¨â©-is-set : (X : Tâ¤) â is-set â¨ X â©
â¨â©-is-set = Tâ¤-prop-induction (Î» _ â being-set-is-prop feâ) â¤-is-set

â¨â©â-is-equiv : (X : Tâ¤) â is-equiv â¨ X â©â
â¨â©â-is-equiv = Tâ¤-prop-induction
                (Î» X â being-equiv-is-prop' feâ feâ feâ feâ â¨ X â©â)
                succ-â¤-is-equiv

â¨_â©â-â : (X : Tâ¤) â â¨ X â© â â¨ X â©
â¨_â©â-â X = (â¨ X â©â , â¨â©â-is-equiv X)

â¨_â©ââ»Â¹ : (X : Tâ¤) â â¨ X â© â â¨ X â©
â¨_â©ââ»Â¹ X = â â¨ X â©â-â ââ»Â¹

\end{code}

Next we derive the recursion principle following Bezem et al.

\begin{code}

module Tâ¤-rec
        {A : ð¤ Ì }
        (fe : funext ð¤ ð¤)
       where

 module _
         ((a , p) : Î£ a' ê A , a' â¡ a')
        where

  -- Bezem, Buchholtz, Grayson
  BBG : (X : Tâ¤â») â ð¤ Ì
  BBG (X , f) = Î£ a' ê A , Î£ h ê (X â a â¡ a') , ((x : X) â h (f x) â¡ p â h x)

  BBG-base : ð¤ Ì
  BBG-base = BBG (â¤ , succ-â¤)

  BBG-base-is-singleton : is-singleton BBG-base
  BBG-base-is-singleton = equiv-to-singleton Ï (singleton-types-are-singletons a)
   where
    Ï : BBG-base â singleton-type a
    Ï = Î£-cong Ï
     where
      Ï : (a' : A)
        â (Î£ h ê (â¤ â a â¡ a') , ((z : â¤) â h (succ-â¤ z) â¡ p â h z))
        â (a â¡ a')
      Ï a' = â¤-symmetric-induction (lower-funext ð¤ ð¤ fe) (Î» _ â a â¡ a') (Î» _ â g)
       where
        g : (a â¡ a') â (a â¡ a')
        g = ((p â_) , â-is-equiv-left p)

  abstract
   BBG-is-singleton : ((X , f , _) : Tâ¤) â is-singleton (BBG (X , f))
   BBG-is-singleton = Tâ¤-prop-induction (Î» _ â being-singleton-is-prop fe)
                                        BBG-base-is-singleton

  Tâ¤-rec : Tâ¤ â A
  Tâ¤-rec X = prâ (center (BBG-is-singleton X))

\end{code}

The corresponding computation rule is a bit more work.

\begin{code}

  Tâ¤-rec-lemmaâ : (X : Tâ¤) â (â¨ X â©) â a â¡ Tâ¤-rec X
  Tâ¤-rec-lemmaâ X = prâ (prâ (center (BBG-is-singleton X)))

  Tâ¤-rec-lemmaâ : (X : Tâ¤) (x : â¨ X â©)
                â Tâ¤-rec-lemmaâ X (â¨ X â©â x) â¡ p â Tâ¤-rec-lemmaâ X x
  Tâ¤-rec-lemmaâ X = prâ (prâ (center (BBG-is-singleton X)))

  ap-Tâ¤-rec-lemma : {X Y : Tâ¤} (e : X â¡ Y) (x : â¨ X â©)
                  â ap Tâ¤-rec e
                  â¡ (Tâ¤-rec-lemmaâ X x) â»Â¹
                    â (Tâ¤-rec-lemmaâ Y (â idtoeq â¨ X â© â¨ Y â© (ap â¨_â© e) â x))
  ap-Tâ¤-rec-lemma {X} {Y} refl x =
   ap Tâ¤-rec refl                                     â¡â¨ refl â©
   refl                                               â¡â¨ Î³    â©
   (t X x) â»Â¹ â (t X x)                               â¡â¨ refl â©
   (t X x) â»Â¹ â (t X (â idtoeq â¨ X â© â¨ Y â© refl â x)) â
    where
     t : (W : Tâ¤) â â¨ W â© â a â¡ Tâ¤-rec W
     t = Tâ¤-rec-lemmaâ
     Î³ = (left-inverse (t X x)) â»Â¹

  ap-Tâ¤-rec-loop-lemmaâ : ap Tâ¤-rec loop
                        â¡ (Tâ¤-rec-lemmaâ base ð) â»Â¹ â p â Tâ¤-rec-lemmaâ base ð
  ap-Tâ¤-rec-loop-lemmaâ =
   ap Tâ¤-rec loop                                            â¡â¨ I   â©
   (t base ð) â»Â¹ â (t base (â idtoeq â¤ â¤ (ap â¨_â© loop) â ð)) â¡â¨ II  â©
   (t base ð) â»Â¹ â (t base (succ-â¤ ð))                       â¡â¨ III â©
   (t base ð) â»Â¹ â (p â t base ð)                            â¡â¨ IV  â©
   (t base ð) â»Â¹ â p â t base ð                              â
    where
     t : (X : Tâ¤) â â¨ X â© â a â¡ Tâ¤-rec X
     t = Tâ¤-rec-lemmaâ
     I   = ap-Tâ¤-rec-lemma loop ð
     III = ap (Î» - â (t base ð) â»Â¹ â -) (Tâ¤-rec-lemmaâ base ð)
     IV  = âassoc (t base ð â»Â¹) p (t base ð) â»Â¹
     II  = ap (Î» - â (t base ð) â»Â¹ â (t base (â - â ð))) Î³
      where
       Î³ : idtoeq â¤ â¤ (ap â¨_â© loop) â¡ succ-â¤-â
       Î³ =  idtoeq â¤ â¤ (ap â¨_â© loop)                        â¡â¨ I'   â©
            (prâ (Ï loop)       , prâ (prâ (Ï loop)))       â¡â¨ refl â©
            (prâ (Ï (Ï loop-â)) , prâ (prâ (Ï (Ï loop-â)))) â¡â¨ II'  â©
            (prâ loop-â         , prâ (prâ loop-â))         â
             where
              Ï : base â¡ base â base â base
              Ï = â characterization-of-Tâ¤-â¡ base base â
              Ï : base â base â base â¡ base
              Ï = â characterization-of-Tâ¤-â¡ base base ââ»Â¹
              I' = h loop
               where
                h : {X Y : Tâ¤} (p : X â¡ Y)
                     â idtoeq â¨ X â© â¨ Y â© (ap â¨_â© p)
                     â¡ (prâ ( â characterization-of-Tâ¤-â¡ X Y â p) ,
                        prâ (prâ (â characterization-of-Tâ¤-â¡ X Y â p)))
                h refl = refl
              II' = ap (Î» - â (prâ - , prâ (prâ -))) (Îµ loop-â)
               where
                Îµ : Ï â Ï â¼ id
                Îµ = inverses-are-sections Ï
                     (ââ-is-equiv (characterization-of-Tâ¤-â¡ base base))

  ap-Tâ¤-rec-loop-lemmaâ : ap Tâ¤-rec loop
                        â¡ transport (Î» - â - â¡ -) (Tâ¤-rec-lemmaâ base ð) p
  ap-Tâ¤-rec-loop-lemmaâ =
   ap Tâ¤-rec loop                                       â¡â¨ I  â©
   (Tâ¤-rec-lemmaâ base ð) â»Â¹ â p â Tâ¤-rec-lemmaâ base ð â¡â¨ II â©
   transport (Î» - â - â¡ -) (Tâ¤-rec-lemmaâ base ð) p     â
    where
     I  = ap-Tâ¤-rec-loop-lemmaâ
     II = (transport-along-â¡ (Tâ¤-rec-lemmaâ base ð) p) â»Â¹

  Tâ¤-rec-comp : (Tâ¤-rec base , ap Tâ¤-rec loop) â¡ (a , p)
  Tâ¤-rec-comp = (to-Î£-â¡ ((Tâ¤-rec-lemmaâ base ð) , (ap-Tâ¤-rec-loop-lemmaâ â»Â¹))) â»Â¹

\end{code}

Now we will deviate from Bezem et al. a bit by deriving the universal property
rather than the induction principle. The proof of the universal property uses
lemmas and techniques from Section 4.2 of the paper by Bezem et al.

Above we constructed a map of type Tâ¤ â A, namely Tâ¤-rec using the BBG-type. In
what follows we take the reverse route: we start with a map f : Tâ¤ â A and then
construct something in the BBG-type so that f and Tâ¤-rec coincide.

First some general lemmas.

\begin{code}

â-comp-Tâ¤ : (X Y Z : Tâ¤) â X â Y â Y â Z â X â Z
â-comp-Tâ¤ X Y Z (e , i , c) (e' , i' , c') =
 (e' â e , â-is-equiv-abstract i i' , Ï)
  where
   abstract
    Ï : e' â e â â¨ X â©â â¡ â¨ Z â©â â e' â e
    Ï = dfunext feâ Î³
     where
      Î³ : e' â e â â¨ X â©â â¼ â¨ Z â©â â e' â e
      Î³ x = e' (e (â¨ X â©â x)) â¡â¨ ap e' (happly c x) â©
            e' (â¨ Y â©â (e x)) â¡â¨ happly c' (e x) â©
            â¨ Z â©â (e' (e x)) â

to-â¡-of-â : (X Y : Tâ¤) {f g : X â Y}
          â prâ f â¼ prâ g
          â f â¡ g
to-â¡-of-â X Y h =
 to-subtype-â¡
  (Î» f' â Ã-is-prop (being-equiv-is-prop' feâ feâ feâ feâ f')
         (equiv-to-prop (â-funext feâ _ _)
          (Î -is-prop feâ (Î» _ â â¨â©-is-set Y))))
  (dfunext feâ h)

to-Tâ¤-â¡-comp : (X Y Z : Tâ¤) (f : X â Y) (g : Y â Z)
             â to-Tâ¤-â¡ X Z (â-comp-Tâ¤ X Y Z f g)
             â¡ to-Tâ¤-â¡ X Y f â to-Tâ¤-â¡ Y Z g
to-Tâ¤-â¡-comp X Y Z f g =
 Ï X Z (â-comp-Tâ¤ X Y Z f g)                 â¡â¨ I    â©
 Ï X Z (Ï X Z (p â q))                       â¡â¨ II   â©
 p â q                                       â¡â¨ refl â©
 Ï X Y f â Ï Y Z g                           â
  where
   Ï : (X Y : Tâ¤) â X â Y â X â¡ Y
   Ï = to-Tâ¤-â¡
   Ï : (X Y : Tâ¤) â X â¡ Y â X â Y
   Ï X Y = â characterization-of-Tâ¤-â¡ X Y â
   p : X â¡ Y
   p = Ï X Y f
   q : Y â¡ Z
   q = Ï Y Z g
   II = Î· X Z (p â q)
    where
     Î· : (X Y : Tâ¤) â Ï X Y â Ï X Y â¼ id
     Î· X Y = inverses-are-retractions (Ï X Y)
              (ââ-is-equiv (characterization-of-Tâ¤-â¡ X Y))
   I = ap (Ï X Z) Î³

\end{code}

    The proof below is done with to-â¡-of-â (rather than directly) for
    type-checking efficiency reasons.

\begin{code}

    where
     Î³ = â-comp-Tâ¤ X Y Z f g                 â¡â¨ to-â¡-of-â X Z w      â©
         â-comp-Tâ¤ X Y Z (Ï X Y p) (Ï Y Z q) â¡â¨ (lemma X Y Z p q) â»Â¹ â©
         Ï X Z (p â q)                       â
      where
       lemma : (X Y Z : Tâ¤) (p : X â¡ Y) (q : Y â¡ Z)
             â Ï X Z (p â q) â¡ â-comp-Tâ¤ X Y Z (Ï X Y p) (Ï Y Z q)
       lemma X Y Z refl refl = to-â¡-of-â X Z (Î» x â refl)
       w : prâ g â prâ f â¼ prâ (Ï Y Z (to-Tâ¤-â¡ Y Z g)) â prâ (Ï X Y p)
       w x = v (prâ f x) â ap (prâ (Ï Y Z q)) (u x)
        where
         Îµ : (X Y : Tâ¤) â Ï X Y â Ï X Y â¼ id
         Îµ X Y = inverses-are-sections (Ï X Y)
                  (ââ-is-equiv (characterization-of-Tâ¤-â¡ X Y))
         u : prâ f â¼ prâ (Ï X Y p)
         u = happly (ap prâ ((Îµ X Y f) â»Â¹))
         v : prâ g â¼ prâ (Ï Y Z q)
         v = happly (ap prâ ((Îµ Y Z g) â»Â¹))

\end{code}

Now some constructions for the BBG-type. The map Tâ¤-action appears in Lemma 4.6
of Bezem et al.

\begin{code}

Tâ¤-action : (X : Tâ¤) â â¨ X â© â â¤ â â¨ X â©
Tâ¤-action X x ð       = x
Tâ¤-action X x (pos n) = (â¨ X â©â   ^ (succ n)) x
Tâ¤-action X x (neg n) = (â¨ X â©ââ»Â¹ ^ (succ n)) x

Tâ¤-action-commutes-with-â¨â©â : (X : Tâ¤) (x : â¨ X â©)
                            â Tâ¤-action X (â¨ X â©â x)
                            â¼ â¨ X â©â â Tâ¤-action X x
Tâ¤-action-commutes-with-â¨â©â X x ð       = refl
Tâ¤-action-commutes-with-â¨â©â X x (pos n) =
 ap â¨ X â©â ((commute-with-iterated-function â¨ X â©â â¨ X â©â (Î» _ â refl) n x) â»Â¹)
Tâ¤-action-commutes-with-â¨â©â X x (neg n) = Î³
 where
  Î³ : (â¨ X â©ââ»Â¹ ^ (succ n)) (â¨ X â©â x) â¡ â¨ X â©â ((â¨ X â©ââ»Â¹ ^ (succ n)) x)
  Î³ = (commute-with-iterated-function â¨ X â©â â¨ X â©ââ»Â¹ Ï (succ n) x) â»Â¹
   where
    Ï : â¨ X â©â â â¨ X â©ââ»Â¹ â¼ â¨ X â©ââ»Â¹ â â¨ X â©â
    Ï y = â¨ X â©â (â¨ X â©ââ»Â¹ y) â¡â¨ I  â©
          y                   â¡â¨ II â©
          â¨ X â©ââ»Â¹ (â¨ X â©â y) â
     where
      I  = inverses-are-sections â¨ X â©â (â¨â©â-is-equiv X) y
      II = (inverses-are-retractions â¨ X â©â (â¨â©â-is-equiv X) y) â»Â¹

Tâ¤-action-commutes-with-â¨â©â-â¡ : (X : Tâ¤) (x : â¨ X â©)
                              â Tâ¤-action X (â¨ X â©â x) â¡ â¨ X â©â â Tâ¤-action X x
Tâ¤-action-commutes-with-â¨â©â-â¡ X x = dfunext feâ (Tâ¤-action-commutes-with-â¨â©â X x)

Tâ¤-action-base-is-shift : (x : â¤) â Tâ¤-action base x â¼ (Î» y â y +â¤ x)
Tâ¤-action-base-is-shift x ð       = refl
Tâ¤-action-base-is-shift x (pos n) = refl
Tâ¤-action-base-is-shift x (neg n) = happly (ap (_^ succ n) (ap â_ââ»Â¹ Ï)) x
 where
  Ï : â¨ base â©â-â â¡ succ-â¤-â
  Ï = to-subtype-â¡ (being-equiv-is-prop' feâ feâ feâ feâ) refl

Tâ¤-action-is-equiv : (X : Tâ¤) (x : â¨ X â©) â is-equiv (Tâ¤-action X x)
Tâ¤-action-is-equiv =
 Tâ¤-prop-induction (Î» X â Î -is-prop feâ
                   (Î» x â being-equiv-is-prop' feâ feâ feâ feâ (Tâ¤-action X x)))
                   Î³
  where
   Î³ : (x : â¤) â is-equiv (Tâ¤-action base x)
   Î³ x = equiv-closed-under-â¼ (Î» y â y +â¤ x) (Tâ¤-action base x)
          (+â¤-is-equiv-right x) (Tâ¤-action-base-is-shift x)

Tâ¤-action-is-Tâ¤-map : (X : Tâ¤) (x : â¨ X â©)
                    â (Tâ¤-action X x â succ-â¤ â¡ â¨ X â©â â Tâ¤-action X x)
Tâ¤-action-is-Tâ¤-map = Tâ¤-prop-induction i Î³
 where
  i : (X : Tâ¤)
    â is-prop ((x : â¨ X â©) â (Tâ¤-action X x â succ-â¤ â¡ â¨ X â©â â Tâ¤-action X x))
  i X = Î -is-prop feâ
         (Î» x â equiv-to-prop
                 (â-funext feâ (Tâ¤-action X x â succ-â¤) (â¨ X â©â â Tâ¤-action X x))
                 (Î -is-prop feâ (Î» _ â â¨â©-is-set X)))
  Î³ : (x : â¤)
    â  Tâ¤-action base x â succ-â¤ â¡ succ-â¤ â Tâ¤-action base x
  Î³ x = dfunext feâ h
   where
    h : Tâ¤-action base x â succ-â¤ â¼ succ-â¤ â Tâ¤-action base x
    h y = Tâ¤-action base x (succ-â¤ y) â¡â¨ I   â©
          (succ-â¤ y) +â¤ x             â¡â¨ II  â©
          succ-â¤ (y +â¤ x)             â¡â¨ III â©
          succ-â¤ (Tâ¤-action base x y) â
     where
      I   = Tâ¤-action-base-is-shift x (succ-â¤ y)
      II  = right-shift-commutes-with-succ-â¤ x y
      III = ap succ-â¤ ((Tâ¤-action-base-is-shift x y) â»Â¹)

Tâ¤-action-â : (X : Tâ¤) (x : â¨ X â©) â base â X
Tâ¤-action-â X x =
 (Tâ¤-action X x , Tâ¤-action-is-equiv X x , Tâ¤-action-is-Tâ¤-map X x)

Tâ¤-action-â¡ : (X : Tâ¤) (x : â¨ X â©) â base â¡ X
Tâ¤-action-â¡ X x = to-Tâ¤-â¡ base X (Tâ¤-action-â X x)

Tâ¤-action-lemma : (X : Tâ¤) (x : â¨ X â©)
                â Tâ¤-action X (â¨ X â©â x)
                â¡ Tâ¤-action X x â succ-â¤
Tâ¤-action-lemma X x = Tâ¤-action-commutes-with-â¨â©â-â¡ X x
                    â (Tâ¤-action-is-Tâ¤-map X x) â»Â¹

Tâ¤-action-â¡-lemma : (X : Tâ¤) (x : â¨ X â©)
                  â Tâ¤-action-â¡ X (â¨ X â©â x) â¡ loop â Tâ¤-action-â¡ X x
Tâ¤-action-â¡-lemma X x =
 Tâ¤-action-â¡ X (â¨ X â©â x)                                        â¡â¨ refl â©
 to-Tâ¤-â¡ base X (Tâ¤-action-â X (â¨ X â©â x))                       â¡â¨ I    â©
 to-Tâ¤-â¡ base X (â-comp-Tâ¤ base base X loop-â (Tâ¤-action-â X x)) â¡â¨ II   â©
 to-Tâ¤-â¡ base base loop-â â to-Tâ¤-â¡ base X (Tâ¤-action-â X x)     â¡â¨ refl â©
 loop â Tâ¤-action-â¡ X x                                          â
  where
   I  = ap (to-Tâ¤-â¡ base X) Ï
    where
     Ï = to-â¡-of-â base X (happly (Tâ¤-action-lemma X x))
   II = to-Tâ¤-â¡-comp base base X loop-â (Tâ¤-action-â X x)

\end{code}

Finally, as promised, every map r : Tâ¤ â A gives rise to an element of the
BBG-type so that r and Tâ¤-rec coincide.

\begin{code}

module _
        {A : ð¤ Ì }
        (r : Tâ¤ â A)
       where

 BBG-map : (X : Tâ¤) â â¨ X â© â r base â¡ r X
 BBG-map X x = ap r (Tâ¤-action-â¡ X x)

 BBG-map-lemma : (X : Tâ¤) (x : â¨ X â©)
               â BBG-map X (â¨ X â©â x) â¡ ap r loop â BBG-map X x
 BBG-map-lemma X x = BBG-map X (â¨ X â©â x)                      â¡â¨ refl â©
                     ap r (Tâ¤-action-â¡ X (â¨ X â©â x))           â¡â¨ I    â©
                     ap r (loop â Tâ¤-action-â¡ X x)             â¡â¨ II   â©
                     ap r loop â ap r (Tâ¤-action-â¡ X x)        â¡â¨ refl â©
                     ap r loop â BBG-map X x                   â
  where
   I  = ap (ap r) (Tâ¤-action-â¡-lemma X x)
   II = ap-â r loop (Tâ¤-action-â¡ X x)

 module _
         (fe : funext ð¤ ð¤)
        where

  open Tâ¤-rec {ð¤} {A} fe

  â¼-to-Tâ¤-rec : r â¼ Tâ¤-rec (r base , ap r loop)
  â¼-to-Tâ¤-rec X = ap prâ e
   where
    bâ : BBG (r base , ap r loop) (X â»)
    bâ = (r X , BBG-map X , BBG-map-lemma X)
    bâ : BBG (r base , ap r loop) (X â»)
    bâ = center (BBG-is-singleton (r base , ap r loop) X)
    e : bâ â¡ bâ
    e = singletons-are-props (BBG-is-singleton (r base , ap r loop) X) bâ bâ

\end{code}

But the above gives us the uniqueness principle for ðÂ¹ (Lemma 6.2.8 in the HoTT
Book) which says that any two maps f,g : ðÂ¹ â A that agree on base and loop must
coincide. Combined with the recursion principle, this quickly gives us the
universal property.

\begin{code}

Tâ¤-universal-map : (A : ð¤ Ì ) â (Tâ¤ â A) â Î£ a ê A , a â¡ a
Tâ¤-universal-map A f = (f base , ap f loop)

Tâ¤-universal-property : FunExt
                      â (A : ð¤ Ì )
                      â is-equiv (Tâ¤-universal-map A)
Tâ¤-universal-property {ð¤} fe A = qinvs-are-equivs Ï (Ï , Î· , Îµ)
 where
  open Tâ¤-rec {ð¤} {A} (fe ð¤ ð¤)
  Ï : (Tâ¤ â A) â (Î£ a ê A , a â¡ a)
  Ï f = (f base , ap f loop)
  Ï : (Î£ a ê A , a â¡ a) â (Tâ¤ â A)
  Ï (a , p) = Tâ¤-rec (a , p)
  Î· : Ï â Ï â¼ id
  Î· f = dfunext (fe ð¤â ð¤) (Î» X â â¼-to-Tâ¤-rec f (fe ð¤ ð¤) X â»Â¹)
  Îµ : Ï â Ï â¼ id
  Îµ = Tâ¤-rec-comp

\end{code}

Finally, we use our abstract proof that the universal property implies induction
(which is developed separately in CircleInduction) to derive the induction
principle.

\begin{code}

open import CircleInduction

module _
        (fe : FunExt)
        (A : Tâ¤ â ð¤ Ì )
        (a : A base)
        (l : transport A loop a â¡ a)
       where

 open ðÂ¹-induction Tâ¤ base loop (Tâ¤-universal-property fe) A a l

 Tâ¤-induction : (x : Tâ¤) â A x
 Tâ¤-induction = ðÂ¹-induction

 Tâ¤-induction-comp : (Tâ¤-induction base , apd Tâ¤-induction loop)
                   â¡[ Î£ y ê A base , transport A loop y â¡ y ] (a , l)
 Tâ¤-induction-comp = ðÂ¹-induction-comp
                      (equiv-to-set loops-at-base-equivalent-to-â¤ â¤-is-set)

\end{code}
