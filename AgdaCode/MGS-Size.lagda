This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module MGS-Size where

open import MGS-Powerset                public
open import MGS-Universe-Lifting        public
open import MGS-Subsingleton-Truncation public

_has-size_ : ð¤ Ì â (ð¥ : Universe) â ð¥ âº â ð¤ Ì
X has-size ð¥ = Î£ Y ê ð¥ Ì , X â Y

propositional-resizing : (ð¤ ð¥ : Universe) â (ð¤ â ð¥)âº Ì
propositional-resizing ð¤ ð¥ = (P : ð¤ Ì ) â is-subsingleton P â P has-size ð¥

resize-up : (X : ð¤ Ì ) â X has-size (ð¤ â ð¥)
resize-up {ð¤} {ð¥} X = (Lift ð¥ X , â-Lift X)

resize-up-subsingleton : propositional-resizing ð¤ (ð¤ â ð¥)
resize-up-subsingleton {ð¤} {ð¥} P i = resize-up {ð¤} {ð¥} P

resize : propositional-resizing ð¤ ð¥
       â (P : ð¤ Ì ) (i : is-subsingleton P) â ð¥ Ì

resize Ï P i = prâ (Ï P i)

resize-is-subsingleton : (Ï : propositional-resizing ð¤ ð¥)
                         (P : ð¤ Ì ) (i : is-subsingleton P)
                       â is-subsingleton (resize Ï P i)

resize-is-subsingleton Ï P i = equiv-to-subsingleton (â-sym (prâ (Ï P i))) i

to-resize : (Ï : propositional-resizing ð¤ ð¥)
            (P : ð¤ Ì ) (i : is-subsingleton P)
          â P â resize Ï P i

to-resize Ï P i = â prâ (Ï P i) â

from-resize : (Ï : propositional-resizing ð¤ ð¥)
              (P : ð¤ Ì ) (i : is-subsingleton P)
            â resize Ï P i â P

from-resize Ï P i = â â-sym (prâ (Ï P i)) â

Propositional-resizing : ð¤Ï
Propositional-resizing = {ð¤ ð¥ : Universe} â propositional-resizing ð¤ ð¥

EM-gives-PR : EM ð¤ â propositional-resizing ð¤ ð¥
EM-gives-PR {ð¤} {ð¥} em P i = Q (em P i) , e
 where
   Q : P + Â¬ P â ð¥ Ì
   Q (inl p) = Lift ð¥ ð
   Q (inr n) = Lift ð¥ ð

   j : (d : P + Â¬ P) â is-subsingleton (Q d)
   j (inl p) = equiv-to-subsingleton (Lift-â ð) ð-is-subsingleton
   j (inr n) = equiv-to-subsingleton (Lift-â ð) ð-is-subsingleton

   f : (d : P + Â¬ P) â P â Q d
   f (inl p) p' = lift â
   f (inr n) p  = !ð (Lift ð¥ ð) (n p)

   g : (d : P + Â¬ P) â Q d â P
   g (inl p) q = p
   g (inr n) q = !ð P (lower q)

   e : P â Q (em P i)
   e = logically-equivalent-subsingletons-are-equivalent
        P (Q (em P i)) i (j (em P i)) (f (em P i) , g (em P i))

has-size-is-subsingleton : Univalence
                         â (X : ð¤ Ì ) (ð¥ :  Universe)
                         â is-subsingleton (X has-size ð¥)

has-size-is-subsingleton {ð¤} ua X ð¥ = univalenceâ' (ua ð¥) (ua (ð¤ â ð¥)) X

PR-is-subsingleton : Univalence â is-subsingleton (propositional-resizing ð¤ ð¥)
PR-is-subsingleton {ð¤} {ð¥} ua =
 Î -is-subsingleton (univalence-gives-global-dfunext ua)
  (Î» P â Î -is-subsingleton (univalence-gives-global-dfunext ua)
  (Î» i â has-size-is-subsingleton ua P ð¥))

Impredicativity : (ð¤ ð¥ : Universe) â (ð¤ â ð¥ )âº Ì
Impredicativity ð¤ ð¥ = (Î© ð¤) has-size ð¥

is-impredicative : (ð¤ : Universe) â ð¤ âº Ì
is-impredicative ð¤ = Impredicativity ð¤ ð¤

PR-gives-Impredicativityâº : global-propext
                          â global-dfunext
                          â propositional-resizing ð¥ ð¤
                          â propositional-resizing ð¤ ð¥
                          â Impredicativity ð¤ (ð¥ âº)

PR-gives-Impredicativityâº {ð¥} {ð¤} pe fe Ï Ï = Î³
 where
  Ï : Î© ð¥ â Î© ð¤
  Ï (Q , j) = resize Ï Q j , resize-is-subsingleton Ï Q j

  Ï : Î© ð¤ â Î© ð¥
  Ï (P , i) = resize Ï P i , resize-is-subsingleton Ï P i

  Î· : (p : Î© ð¤) â Ï (Ï p) â¡ p
  Î· (P , i) = Î©-ext fe pe a b
   where
    Q : ð¥ Ì
    Q = resize Ï P i

    j : is-subsingleton Q
    j = resize-is-subsingleton Ï P i

    a : resize Ï Q j â P
    a = from-resize Ï P i â from-resize Ï Q j

    b : P â resize Ï Q j
    b = to-resize Ï Q j â to-resize Ï P i

  Îµ : (q : Î© ð¥) â Ï (Ï q) â¡ q
  Îµ (Q , j) = Î©-ext fe pe a b
   where
    P : ð¤ Ì
    P = resize Ï Q j

    i : is-subsingleton P
    i = resize-is-subsingleton Ï Q j

    a : resize Ï P i â Q
    a = from-resize Ï Q j â from-resize Ï P i

    b : Q â resize Ï P i
    b = to-resize Ï P i â to-resize Ï Q j

  Î³ : (Î© ð¤) has-size (ð¥ âº)
  Î³ = Î© ð¥ , invertibility-gives-â Ï (Ï , Î· , Îµ)

PR-gives-impredicativityâº : global-propext
                          â global-dfunext
                          â propositional-resizing (ð¤ âº) ð¤
                          â is-impredicative (ð¤ âº)

PR-gives-impredicativityâº pe fe = PR-gives-Impredicativityâº
                                   pe fe (Î» P i â resize-up P)

PR-gives-impredicativityâ : global-propext
                          â global-dfunext
                          â propositional-resizing ð¤ ð¤â
                          â Impredicativity ð¤ ð¤â

PR-gives-impredicativityâ pe fe = PR-gives-Impredicativityâº
                                   pe fe (Î» P i â resize-up P)

Impredicativity-gives-PR : propext ð¤
                         â dfunext ð¤ ð¤
                         â Impredicativity ð¤ ð¥
                         â propositional-resizing ð¤ ð¥

Impredicativity-gives-PR {ð¤} {ð¥} pe fe (O , e) P i = Q , Îµ
 where
  ð'' : ð¤ Ì
  ð'' = Lift ð¤ ð

  k : is-subsingleton ð''
  k (lift â) (lift â) = refl (lift â)

  down : Î© ð¤ â O
  down = â e â

  O-is-set : is-set O
  O-is-set = equiv-to-set (â-sym e) (Î©-is-set fe pe)

  Q : ð¥ Ì
  Q = down (ð'' , k) â¡ down (P , i)

  j : is-subsingleton Q
  j = O-is-set (down (Lift ð¤ ð , k)) (down (P , i))

  Ï : Q â P
  Ï q = Idâfun
         (ap _holds (equivs-are-lc down (ââ-is-equiv e) q))
         (lift â)

  Î³ : P â Q
  Î³ p = ap down (to-subtype-â¡
                    (Î» _ â being-subsingleton-is-subsingleton fe)
                    (pe k i (Î» _ â p) (Î» _ â lift â)))

  Îµ : P â Q
  Îµ = logically-equivalent-subsingletons-are-equivalent P Q i j (Î³ , Ï)

PR-gives-existence-of-truncations : global-dfunext
                                  â Propositional-resizing
                                  â subsingleton-truncations-exist

PR-gives-existence-of-truncations fe R =
 record
 {
   â¥_â¥ =

    Î» {ð¤} X â resize R
               (is-inhabited X)
               (inhabitation-is-subsingleton fe X) ;

   â¥â¥-is-subsingleton =

    Î» {ð¤} {X} â resize-is-subsingleton R
                 (is-inhabited X)
                 (inhabitation-is-subsingleton fe X) ;

   â£_â£ =

    Î» {ð¤} {X} x â to-resize R
                   (is-inhabited X)
                   (inhabitation-is-subsingleton fe X)
                   (inhabited-intro x) ;

   â¥â¥-recursion =

    Î» {ð¤} {ð¥} {X} {P} i u s â from-resize R P i
                                (inhabited-recursion
                                  (resize-is-subsingleton R P i)
                                  (to-resize R P i â u)
                                  (from-resize R
                                    (is-inhabited X)
                                    (inhabitation-is-subsingleton fe X) s))
 }

module powerset-union-existence
        (pt  : subsingleton-truncations-exist)
        (hfe : global-hfunext)
       where

 open basic-truncation-development pt hfe

 family-union : {X : ð¤ â ð¥ Ì } {I : ð¥ Ì } â (I â ð X) â ð X
 family-union {ð¤} {ð¥} {X} {I} A = Î» x â (â i ê I , x â A i) , â-is-subsingleton

 ðð : ð¤ Ì â ð¤ âºâº Ì
 ðð X = ð (ð X)

 existence-of-unions : (ð¤ : Universe) â ð¤ âºâº Ì
 existence-of-unions ð¤ =
  (X : ð¤ Ì ) (ð : ðð X) â Î£ B ê ð X , ((x : X) â (x â B) â (â A ê ð X , (A â ð) Ã (x â A)))

 existence-of-unionsâ : (ð¤ :  Universe) â _ Ì
 existence-of-unionsâ ð¤ =
  (X : ð¤ Ì )
  (ð : (X â Î© _) â Î© _)
     â Î£ B ê (X â Î© _) , ((x : X) â (x â B) â (â A ê (X â Î© _) , (A â ð) Ã (x â A)))

 existence-of-unionsâ : (ð¤ :  Universe) â ð¤ âºâº Ì
 existence-of-unionsâ ð¤ =
  (X : ð¤ Ì )
  (ð : (X â Î© ð¤) â Î© (ð¤ âº))
     â Î£ B ê (X â Î© ð¤) , ((x : X) â (x â B) â (â A ê (X â Î© ð¤) , (A â ð) Ã (x â A)))

 existence-of-unions-agreement : existence-of-unions ð¤ â¡ existence-of-unionsâ ð¤
 existence-of-unions-agreement = refl _

 existence-of-unions-gives-PR : existence-of-unions ð¤
                              â propositional-resizing (ð¤ âº) ð¤

 existence-of-unions-gives-PR {ð¤} Î± = Î³
  where
   Î³ : (P : ð¤ âº Ì ) â (i : is-subsingleton P) â P has-size ð¤
   Î³ P i = Q , e
    where
    ðáµ¤ : ð¤ Ì
    ðáµ¤ = Lift ð¤ ð

    âáµ¤ : ðáµ¤
    âáµ¤ = lift â

    ðáµ¤-is-subsingleton : is-subsingleton ðáµ¤
    ðáµ¤-is-subsingleton = equiv-to-subsingleton (Lift-â ð) ð-is-subsingleton

    ð : ðð ðáµ¤
    ð = Î» (A : ð ðáµ¤) â P , i

    B : ð ðáµ¤
    B = prâ (Î± ðáµ¤ ð)

    Ï : (x : ðáµ¤) â (x â B) â (â A ê ð ðáµ¤ , (A â ð) Ã (x â A))
    Ï = prâ (Î± ðáµ¤ ð)

    Q : ð¤ Ì
    Q = âáµ¤ â B

    j : is-subsingleton Q
    j = â-is-subsingleton B âáµ¤

    f : P â Q
    f p = b
     where
      a : Î£ A ê ð ðáµ¤ , (A â ð) Ã (âáµ¤ â A)
      a = (Î» (x : ðáµ¤) â ðáµ¤ , ðáµ¤-is-subsingleton) , p , âáµ¤

      b : âáµ¤ â B
      b = rl-implication (Ï âáµ¤) â£ a â£

    g : Q â P
    g q = â¥â¥-recursion i b a
     where
      a : â A ê ð ðáµ¤ , (A â ð) Ã (âáµ¤ â A)
      a = lr-implication (Ï âáµ¤) q

      b : (Î£ A ê ð ðáµ¤ , (A â ð) Ã (âáµ¤ â A)) â P
      b (A , m , _) = m

    e : P â Q
    e = logically-equivalent-subsingletons-are-equivalent P Q i j (f , g)

 PR-gives-existence-of-unions : propositional-resizing (ð¤ âº) ð¤
                              â existence-of-unions ð¤

 PR-gives-existence-of-unions {ð¤} Ï X ð = B , (Î» x â lr x , rl x)
  where
   Î² : X â ð¤ âº Ì
   Î² x = â A ê ð X , (A â ð) Ã (x â A)

   i : (x : X) â is-subsingleton (Î² x)
   i x = â-is-subsingleton

   B : ð X
   B x = (resize Ï (Î² x) (i x) , resize-is-subsingleton Ï (Î² x) (i x))

   lr : (x : X) â x â B â â A ê ð X , (A â ð) Ã (x â A)
   lr x = from-resize Ï (Î² x) (i x)

   rl : (x : X) â (â A ê ð X , (A â ð) Ã (x â A)) â x â B
   rl x = to-resize Ï (Î² x) (i x)

module basic-powerset-development
        (hfe : global-hfunext)
        (Ï   : Propositional-resizing)
       where

  pt : subsingleton-truncations-exist
  pt = PR-gives-existence-of-truncations (hfunext-gives-dfunext hfe) Ï

  open basic-truncation-development pt hfe
  open powerset-union-existence pt hfe

  â : {X : ð¤ Ì } â ðð X â ð X
  â ð = prâ (PR-gives-existence-of-unions Ï _ ð)

  â-property : {X : ð¤ Ì } (ð : ðð X)
             â (x : X) â (x â â ð) â (â A ê ð X , (A â ð) Ã (x â A))

  â-property ð = prâ (PR-gives-existence-of-unions Ï _ ð)

  intersections-exist :
    (X : ð¤ Ì )
    (ð : ðð X)
       â Î£ B ê ð X , ((x : X) â (x â B) â ((A : ð X) â A â ð â x â A))

  intersections-exist {ð¤} X ð = B , (Î» x â lr x , rl x)
   where
    Î² : X â ð¤ âº Ì
    Î² x = (A : ð X) â A â ð â x â A

    i : (x : X) â is-subsingleton (Î² x)
    i x = Î -is-subsingleton hunapply
           (Î» A â Î -is-subsingleton hunapply
           (Î» _ â â-is-subsingleton A x))

    B : ð X
    B x = (resize Ï (Î² x) (i x) , resize-is-subsingleton Ï (Î² x) (i x))

    lr : (x : X) â x â B â (A : ð X) â A â ð â x â A
    lr x = from-resize Ï (Î² x) (i x)

    rl : (x : X) â ((A : ð X) â A â ð â x â A) â x â B
    rl x = to-resize Ï (Î² x) (i x)

  â : {X : ð¤ Ì } â ðð X â ð X
  â {ð¤} {X} ð = prâ (intersections-exist X ð)

  â-property : {X : ð¤ Ì } (ð : ðð X)
             â (x : X) â (x â â ð) â ((A : ð X) â A â ð â x â A)

  â-property {ð¤} {X} ð = prâ (intersections-exist X ð)

  â full : {X : ð¤ Ì } â ð X

  â    = Î» x â (Lift _ ð , equiv-to-subsingleton (Lift-â ð) ð-is-subsingleton)

  full = Î» x â (Lift _ ð , equiv-to-subsingleton (Lift-â ð) ð-is-subsingleton)

  â-property : (X : ð¤ Ì ) â (x : X) â Â¬ (x â â)
  â-property X x = lower

  full-property : (X : ð¤ Ì ) â (x : X) â x â full
  full-property X x = lift â

  _â©_ _âª_ : {X : ð¤ Ì } â ð X â ð X â ð X

  (A âª B) = Î» x â ((x â A) â¨ (x â B)) , â¨-is-subsingleton

  (A â© B) = Î» x â ((x â A) Ã (x â B)) ,
                  Ã-is-subsingleton
                    (â-is-subsingleton A x)
                    (â-is-subsingleton B x)

  âª-property : {X : ð¤ Ì } (A B : ð X)
             â (x : X) â x â (A âª B) â (x â A) â¨ (x â B)

  âª-property {ð¤} {X} A B x = id , id

  â©-property : {X : ð¤ Ì } (A B : ð X)
             â (x : X) â x â (A â© B) â (x â A) Ã (x â B)

  â©-property {ð¤} {X} A B x = id , id

  infix  20 _â©_
  infix  20 _âª_

  Top : (ð¤ : Universe) â ð¤ âºâº Ì
  Top ð¤ = Î£ X ê ð¤ Ì , is-set X
                     Ã (Î£ ð ê ðð X , full â ð
                                   Ã ((U V : ð X) â U â ð â V â ð â (U â© V) â ð)
                                   Ã ((ð : ðð X) â ð â ð â â ð â ð))

\end{code}
