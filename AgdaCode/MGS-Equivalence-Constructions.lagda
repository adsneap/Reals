Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module MGS-Equivalence-Constructions where

open import MGS-More-FunExt-Consequences public

id-â-left : dfunext ð¥ (ð¤ â ð¥)
          â dfunext (ð¤ â ð¥) (ð¤ â ð¥)
          â {X : ð¤ Ì } {Y : ð¥ Ì } (Î± : X â Y)
          â id-â X â Î± â¡ Î±

id-â-left fe fe' Î± = to-subtype-â¡ (being-equiv-is-subsingleton fe fe') (refl _)

â-sym-left-inverse : dfunext ð¥ ð¥
                   â {X : ð¤ Ì } {Y : ð¥ Ì } (Î± : X â Y)
                   â â-sym Î± â Î± â¡ id-â Y

â-sym-left-inverse fe (f , e) = to-subtype-â¡ (being-equiv-is-subsingleton fe fe) p
 where
  p : f â inverse f e â¡ id
  p = fe (inverses-are-sections f e)

â-sym-right-inverse : dfunext ð¤ ð¤
                    â {X : ð¤ Ì } {Y : ð¥ Ì } (Î± : X â Y)
                    â Î± â â-sym Î± â¡ id-â X

â-sym-right-inverse fe (f , e) = to-subtype-â¡ (being-equiv-is-subsingleton fe fe) p
 where
  p : inverse f e â f â¡ id
  p = fe (inverses-are-retractions f e)

â-Sym : dfunext ð¥ (ð¤ â ð¥) â dfunext ð¤ (ð¤ â ð¥) â dfunext (ð¤ â ð¥) (ð¤ â ð¥)
      â {X : ð¤ Ì } {Y : ð¥ Ì }
      â (X â Y) â (Y â X)

â-Sym feâ feâ feâ = â-sym , â-sym-is-equiv feâ feâ feâ

â-cong' : dfunext ð¦ (ð¥ â ð¦) â dfunext (ð¥ â ð¦) (ð¥ â ð¦ )
       â dfunext ð¥ ð¥ â dfunext ð¦ (ð¤ â ð¦)
       â dfunext (ð¤ â ð¦) (ð¤ â ð¦ ) â dfunext ð¤ ð¤
       â {X : ð¤ Ì } {Y : ð¥ Ì } (Z : ð¦ Ì )
       â X â Y â (Y â Z) â (X â Z)

â-cong' feâ feâ feâ feâ feâ feâ Z Î± = invertibility-gives-â (Î± â_)
                                      ((â-sym Î± â_) , p , q)
 where
  p = Î» Î² â â-sym Î± â (Î± â Î²) â¡â¨ â-assoc feâ feâ (â-sym Î±) Î± Î² â©
            (â-sym Î± â Î±) â Î² â¡â¨ ap (_â Î²) (â-sym-left-inverse feâ Î±) â©
            id-â _ â Î²        â¡â¨ id-â-left feâ feâ _ â©
            Î²                 â

  q = Î» Î³ â Î± â (â-sym Î± â Î³) â¡â¨ â-assoc feâ feâ Î± (â-sym Î±) Î³ â©
            (Î± â â-sym Î±) â Î³ â¡â¨ ap (_â Î³) (â-sym-right-inverse feâ Î±) â©
            id-â _ â Î³        â¡â¨ id-â-left feâ feâ _ â©
            Î³                 â

Eq-Eq-cong' : dfunext ð¥ (ð¤ â ð¥) â dfunext (ð¤ â ð¥) (ð¤ â ð¥) â dfunext ð¤ ð¤
            â dfunext ð¥ (ð¥ â ð¦) â dfunext (ð¥ â ð¦) (ð¥ â ð¦) â dfunext ð¦ ð¦
            â dfunext ð¦ (ð¥ â ð¦) â dfunext ð¥ ð¥ â dfunext ð¦ (ð¦ â ð£)
            â dfunext (ð¦ â ð£) (ð¦ â ð£) â dfunext ð£ ð£ â dfunext ð£ (ð¦ â ð£)
            â {X : ð¤ Ì } {Y : ð¥ Ì } {A : ð¦ Ì } {B : ð£ Ì }
            â X â A â Y â B â (X â Y) â (A â B)

Eq-Eq-cong' feâ feâ feâ feâ feâ feâ feâ feâ feâ feâ feââ feââ {X} {Y} {A} {B} Î± Î² =

  X â Y   ââ¨ â-cong' feâ feâ feâ feâ feâ feâ Y (â-sym Î±) â©
  A â Y   ââ¨ â-Sym feâ feâ feâ â©
  Y â A   ââ¨ â-cong' feâ feâ feâ feâ feâ feââ A (â-sym Î²) â©
  B â A   ââ¨ â-Sym feâ feââ feâ â©
  A â B   â 

Eq-Eq-cong : global-dfunext
           â {X : ð¤ Ì } {Y : ð¥ Ì } {A : ð¦ Ì } {B : ð£ Ì }
           â X â A â Y â B â (X â Y) â (A â B)

Eq-Eq-cong fe = Eq-Eq-cong' fe fe fe fe fe fe fe fe fe fe fe fe

\end{code}
