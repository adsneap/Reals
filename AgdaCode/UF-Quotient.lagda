Martin Escardo, August 2018.

Set quotients in univalent mathematics in Agda notation.

This took place during the Dagstuhl meeting "Formalization of
Mathematics in Type Theory", because Dan Grayson wanted to see how
universe levels work in Agda and I thought that this would be a nice
example to illustrate that.

We assume, in addition to Spartan Martin-LĂ¶f type theory,

 * function extensionality
   (any two pointwise equal functions are equal),

 * propositional extensionality
   (any two logically equivalent propositions are equal),

 * propositional truncation
   (any type can be universally mapped into a prop in the same
   universe),

and no resizing axioms.

The K axiom is not used (the without-K option below). We also make
sure pattern matching corresponds to Martin-LĂ¶f eliminators, using the
option exact-split. With the option safe we make sure that nothing
is postulated - any non-MLTT axiom has to be an explicit assumption
(argument to a function or a module).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

open import UF-FunExt
open import UF-PropTrunc
open import UF-Base hiding (_â_)
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-ImageAndSurjection
open import UF-Equiv

module UF-Quotient
        (pt  : propositional-truncations-exist)
        (fe  : Fun-Ext)
        (pe  : Prop-Ext)
       where

\end{code}

We define when a relation is subsingleton (or proposition) valued,
reflexive, transitive or an equivalence.

What is noteworthy, for the purpose of explaining universes in Agda to
Dan, is that X is in a universe đ€, and the value of the relation is in
a universe đ„, where đ€ and đ„ are arbitrary.

(NB. The Agda library uses the word "Level" for universes, and then
what we write "đ€ Ì" here is written "Set đ€". This is not good for
univalent mathematics, because the types in đ€ Ì need not be sets, and
also because it places emphasis on levels rather than universes
themselves.)

Then, for example, the function is-prop-valued defined below takes
values in the least upper bound of đ€ and đ„, which is denoted by đ€ â đ„.

We first define the type of five functions and then define them, where
_â_ is a variable:

\begin{code}

is-prop-valued is-equiv-relation : {X : đ€ Ì } â (X â X â đ„ Ì ) â đ€ â đ„ Ì
is-prop-valued _â_ = â x y â is-prop (x â y)
is-equiv-relation _â_ = is-prop-valued _â_ Ă reflexive _â_ Ă symmetric _â_ Ă transitive _â_

\end{code}

Now, using an anonymous module with parameters (corresponding to a
section in Coq), we assume propositional truncations that stay in the
same universe, function extensionality for all universes, two
universes đ€ and đ„, propositional truncation for the universe đ„, a type
X : đ€ Ì, and an equivalence relation _â_ with values in đ„ Ì.

\begin{code}

module quotient
       {đ€ đ„ : Universe}
       (X   : đ€ Ì )
       (_â_ : X â X â đ„ Ì )
       (âp  : is-prop-valued _â_)
       (âr  : reflexive _â_)
       (âs  : symmetric _â_)
       (ât  : transitive _â_)
      where

 open PropositionalTruncation pt
 open ImageAndSurjection pt

\end{code}

Now, Î© đ„ is the type of subsingletons, or (univalent) propositions, or
h-propositions, or mere propositions, in the universe đ„, which lives
in the next universe đ„ âș.

From the relation _â_ : X â (X â đ„ Ì ) we define a relation
X â (X â Î© đ„), which of course is formally a function. We then take
the quotient X/â to be the image of this function.

Of course, it is for constructing the image that we need propositional
truncations.

\begin{code}

 equiv-rel : X â (X â Î© đ„)
 equiv-rel x y = x â y , âp x y

\end{code}

Then the quotient lives in the least upper bound of đ€ and đ„ âș, where đ„ âș
is the successor of the universe đ„:

\begin{code}

 X/â : đ€ â (đ„ âș) Ì
 X/â = image equiv-rel

 X/â-is-set : is-set X/â
 X/â-is-set = subsets-of-sets-are-sets (X â Î© đ„) _
                (powersets-are-sets'' fe fe pe)
                â„â„-is-prop

 Î· : X â X/â
 Î· = corestriction equiv-rel

\end{code}

Then Î· is the universal solution to the problem of transforming
equivalence _â_ into equality _âĄ_ (in Agda the notation for the
identity type is _âĄ_ - we can't use _=_ because this is a reserved
symbol for definitional equality).

By construction, Î· is a surjection, of course:

\begin{code}

 Î·-surjection : is-surjection Î·
 Î·-surjection = corestriction-is-surjection equiv-rel

\end{code}

It is convenient to use the following induction principle for
reasoning about the image. Notice that the property we consider has
values in any universe đŠ we please:

\begin{code}

 quotient-induction : â {đŠ} (P : X/â â đŠ Ì )
                    â ((x' : X/â) â is-prop (P x'))
                    â ((x : X) â P (Î· x))
                    â (x' : X/â) â P x'
 quotient-induction = surjection-induction Î· Î·-surjection

\end{code}

The first part of the universal property of Î· says that equivalent
points are mapped to equal points:

\begin{code}

 Î·-equiv-equal : {x y : X} â x â y â Î· x âĄ Î· y
 Î·-equiv-equal {x} {y} e =
   to-ÎŁ-âĄ (dfunext fe
          (Î» z â to-ÎŁ-âĄ (pe (âp x z) (âp y z) (ât y x z (âs x y e)) (ât x y z e) ,
                         being-prop-is-prop fe _ _)) ,
       â„â„-is-prop _ _)

\end{code}

We also need the fact that Î· reflects equality into equivalence:

\begin{code}

 Î·-equal-equiv : {x y : X} â Î· x âĄ Î· y â x â y
 Î·-equal-equiv {x} {y} p = equiv-rel-reflect (ap prâ p)
  where
   equiv-rel-reflect : equiv-rel x âĄ equiv-rel y â x â y
   equiv-rel-reflect q = b (âr y)
    where
     a : (y â y) âĄ (x â y)
     a = ap (Î» - â prâ (- y)) (q â»Âč)
     b : (y â y) â (x â y)
     b = Idtofun a

\end{code}

We are now ready to formulate and prove the universal property of the
quotient. What is noteworthy here, regarding universes, is that the
universal property says that we can eliminate into any set A of any
universe đŠ.

                   Î·
              X ------> X/â
               \       .
                \     .
               f \   . f'
                  \ .
                   v
                   A

\begin{code}

 universal-property : â {đŠ} (A : đŠ Ì )
                    â is-set A
                    â (f : X â A)
                    â ({x x' : X} â x â x' â f x âĄ f x')
                    â â! f' ê ( X/â â A), f' â Î· âĄ f
 universal-property {đŠ} A iss f pr = ic
  where
   Ï : (x' : X/â) â is-prop (ÎŁ a ê A , â x ê X ,  (Î· x âĄ x') Ă (f x âĄ a))
   Ï = quotient-induction _ Îł induction-step
     where
      induction-step : (y : X) â is-prop (ÎŁ a ê A , â x ê X ,  (Î· x âĄ Î· y) Ă (f x âĄ a))
      induction-step x (a , d) (b , e) = to-ÎŁ-âĄ (p , â„â„-is-prop _ _)
       where
        h : (ÎŁ x' ê X , (Î· x' âĄ Î· x) Ă (f x' âĄ a))
          â (ÎŁ y' ê X , (Î· y' âĄ Î· x) Ă (f y' âĄ b))
          â a âĄ b
        h (x' , r , s) (y' , t , u) = s â»Âč â pr (Î·-equal-equiv (r â t â»Âč)) â u

        p : a âĄ b
        p = â„â„-rec iss (Î» Ï â â„â„-rec iss (h Ï) e) d

      Îł : (x' : X/â) â is-prop (is-prop (ÎŁ a ê A , â x ê X , (Î· x âĄ x') Ă (f x âĄ a)))
      Îł x' = being-prop-is-prop fe

   k : (x' : X/â) â ÎŁ a ê A , â x ê X , (Î· x âĄ x') Ă (f x âĄ a)
   k = quotient-induction _ Ï induction-step
    where
     induction-step : (y : X) â ÎŁ a ê A , â x ê X , (Î· x âĄ Î· y) Ă (f x âĄ a)
     induction-step x = f x , âŁ x , refl , refl âŁ

   f' : X/â â A
   f' x' = prâ (k x')

   r : f' â Î· âĄ f
   r = dfunext fe h
    where
     g : (y : X) â â x ê X , (Î· x âĄ Î· y) Ă (f x âĄ f' (Î· y))
     g y = prâ (k (Î· y))

     j : (y : X) â (ÎŁ x ê X , (Î· x âĄ Î· y) Ă (f x âĄ f' (Î· y))) â f' (Î· y) âĄ f y
     j y (x , p , q) = q â»Âč â pr (Î·-equal-equiv p)

     h : (y : X) â f' (Î· y) âĄ f y
     h y = â„â„-rec iss (j y) (g y)

   c : (Ï : ÎŁ f'' ê (X/â â A), f'' â Î· âĄ f) â (f' , r) âĄ Ï
   c (f'' , s) = to-ÎŁ-âĄ (t , v)
    where
     w : â x â f' (Î· x) âĄ f'' (Î· x)
     w = happly (r â s â»Âč)

     t : f' âĄ f''
     t = dfunext fe (quotient-induction _ (Î» _ â iss) w)

     u : f'' â Î· âĄ f
     u = transport (Î» - â - â Î· âĄ f) t r

     v : u âĄ s
     v = Î -is-set fe (Î» _ â iss) u s

   ic : â! f' ê (X/â â A), f' â Î· âĄ f
   ic = (f' , r) , c

\end{code}

Added 11th February 2021. We now repackage the above for convenient
use:

\begin{code}

module _ {đ€ đ„ : Universe} where

 open quotient
 open ImageAndSurjection pt

 EqRel : đ€ Ì â đ€ â (đ„ âș) Ì
 EqRel X = ÎŁ R ê (X â X â đ„ Ì ) , is-equiv-relation R

 _â[_]_ : {X : đ€ Ì } â X â EqRel X â X â đ„ Ì
 x â[ _â_ , _ ] y = x â y

 _/_ : (X : đ€ Ì ) â EqRel X â đ€ â (đ„ âș) Ì
 X / (_â_ , p , r , s , t) = X/â X _â_ p r s t

 module _ {X : đ€ Ì }
          ((_â_ , âp , âr , âs , ât) : EqRel X)
        where

  private
   â : EqRel X
   â = (_â_ , âp , âr , âs , ât)

  quotient-is-set : is-set (X / â)
  quotient-is-set = X/â-is-set _ _â_ âp âr âs ât

  Î·/ : X â X / â
  Î·/ = Î· X _â_ âp âr âs ât

  Î·/-is-surjection : is-surjection Î·/
  Î·/-is-surjection = Î·-surjection X _â_ âp âr âs ât

  /-induction : â {đŠ} (P : X / â â đŠ Ì )
              â ((x' : X / â) â is-prop (P x'))
              â ((x : X) â P (Î·/ x))
              â (x' : X / â) â P x'
  /-induction = surjection-induction Î·/ Î·/-is-surjection

  identifies-related-points : {A : đŠ Ì } â (X â A) â đ€ â đ„ â đŠ Ì
  identifies-related-points f = â {x x'} â x â x' â f x âĄ f x'

  Î·/-identifies-related-points : identifies-related-points Î·/
  Î·/-identifies-related-points = Î·-equiv-equal X _â_ âp âr âs ât

  Î·/-relates-identified-points : {x y : X}
                               â Î·/ x âĄ Î·/ y
                               â x â y
  Î·/-relates-identified-points = Î·-equal-equiv X _â_ âp âr âs ât

  module _ {đŠ : Universe}
           {A : đŠ Ì }
         where

   abstract
    universal-property/ : is-set A
                        â (f : X â A)
                        â identifies-related-points f
                        â â! f' ê (X / â â A), f' â Î·/ âĄ f
    universal-property/ = universal-property X _â_ âp âr âs ât A

    mediating-map/ : is-set A
                   â (f : X â A)
                   â identifies-related-points f
                   â X / â â A
    mediating-map/ i f p = prâ (center (universal-property/ i f p))

    universality-triangle/âĄ : (i : is-set A) (f : X â A)
                              (p : identifies-related-points f)
                            â mediating-map/ i f p â Î·/ âĄ f
    universality-triangle/âĄ i f p = prâ (center (universal-property/ i f p))


    universality-triangle/ : (i : is-set A) (f : X â A)
                             (p : identifies-related-points f)
                           â mediating-map/ i f p â Î·/ âŒ f
    universality-triangle/ i f p = happly (universality-triangle/âĄ i f p)


    at-most-one-mediating-map/âĄ : is-set A
                               â (g h : X / â â A)
                               â g â Î·/ âĄ h â Î·/
                               â g âĄ h
    at-most-one-mediating-map/âĄ i g h p = q â»Âč â r
     where
      f : X â A
      f = g â Î·/

      j : identifies-related-points f
      j e = ap g (Î·/-identifies-related-points e)

      q : mediating-map/ i f j âĄ g
      q = witness-uniqueness (Î» f' â f' â Î·/ âĄ f)
           (universal-property/ i f j)
           (mediating-map/ i f j) g (universality-triangle/âĄ i f j)
           refl

      r : mediating-map/ i f j âĄ h
      r = witness-uniqueness (Î» f' â f' â Î·/ âĄ f)
           (universal-property/ i f j)
           (mediating-map/ i f j) h (universality-triangle/âĄ i f j)
           (p â»Âč)

    at-most-one-mediating-map/ : is-set A
                               â (g h : X / â â A)
                               â g â Î·/ âŒ h â Î·/
                               â g âŒ h
    at-most-one-mediating-map/ i g h p = happly (at-most-one-mediating-map/âĄ i g h
                                                   (dfunext fe p))
\end{code}

Extending unary and binary operations to the quotient:

\begin{code}

  extension/ : (f : X â X / â)
             â identifies-related-points f
             â (X / â â X / â)
  extension/ = mediating-map/ quotient-is-set

  extension-triangle/ : (f : X â X / â)
                        (i : identifies-related-points f)
                      â extension/ f i â Î·/ âŒ f
  extension-triangle/ = universality-triangle/ quotient-is-set

  module _ (f : X â X)
           (p : {x y : X} â x â y â f x â f y)
         where

   abstract
    private
      Ï : identifies-related-points (Î·/ â f)
      Ï e = Î·/-identifies-related-points (p e)

   extensionâ/ : X / â â X / â
   extensionâ/ = extension/ (Î·/ â f) Ï

   naturality/ : extensionâ/ â Î·/ âŒ Î·/ â f
   naturality/ = universality-triangle/ quotient-is-set (Î·/ â f) Ï

  module _ (f : X â X â X)
           (p : {x y x' y' : X} â x â x' â y â y' â f x y â f x' y')
         where

   abstract
    private
     Ï : (x : X) â identifies-related-points (Î·/ â f x)
     Ï x {y} {y'} e = Î·/-identifies-related-points (p {x} {y} {x} {y'} (âr x) e)

     p' : (x : X) {y y' : X} â y â y' â f x y â f x y'
     p' x {x'} {y'} = p {x} {x'} {x} {y'} (âr x)

     fâ : X â X / â â X / â
     fâ x = extensionâ/ (f x) (p' x)

     n/ : (x : X) â fâ x â Î·/ âŒ Î·/ â f x
     n/ x = naturality/ (f x) (p' x)

     ÎŽ : {x x' : X} â x â x' â (y : X) â fâ x (Î·/ y) âĄ fâ x' (Î·/ y)
     ÎŽ {x} {x'} e y =
       fâ x (Î·/ y)   âĄâš naturality/ (f x) (p' x) y â©
       Î·/ (f x y)    âĄâš Î·/-identifies-related-points (p e (âr y)) â©
       Î·/ (f x' y)   âĄâš (naturality/ (f x') (p' x') y)â»Âč â©
       fâ x' (Î·/ y)  â

     Ï : (b : X / â) {x x' : X} â x â x' â fâ x b âĄ fâ x' b
     Ï b {x} {x'} e = /-induction (Î» b â fâ x b âĄ fâ x' b)
                        (Î» y â quotient-is-set) (ÎŽ e) b

     fâ : X / â â X / â â X / â
     fâ d e = extension/ (Î» x â fâ x e) (Ï e) d

   extensionâ/ : X / â â X / â â X / â
   extensionâ/ = fâ

   abstract
    naturalityâ/ : (x y : X) â fâ (Î·/ x) (Î·/ y) âĄ Î·/ (f x y)
    naturalityâ/ x y =
     fâ (Î·/ x) (Î·/ y) âĄâš extension-triangle/ (Î» x â fâ x (Î·/ y)) (Ï (Î·/ y)) x â©
     fâ x (Î·/ y)      âĄâš naturality/ (f x) (p (âr x)) y â©
     Î·/ (f x y)       â

\end{code}

Without the above abstract declarations, the use of naturalityâ/ takes
for ever in the module FreeGroup.lagda.

\begin{code}

quotients-equivalent : (X : đ€ Ì ) (R : EqRel {đ€} {đ„} X) (R' : EqRel {đ€} {đŠ} X)
                     â ({x y : X} â x â[ R ] y â x â[ R' ] y)
                     â (X / R) â (X / R')
quotients-equivalent X (_â_  , âp ,  âr  , âs  , ât )
                       (_â'_ , âp' , âr' , âs' , ât') Î” = Îł
 where
  â  = (_â_  , âp ,  âr  , âs  , ât )
  â' = (_â'_ , âp' , âr' , âs' , ât')

  i : {x y : X} â x â y â Î·/ â' x âĄ Î·/ â' y
  i e = Î·/-identifies-related-points â' (lr-implication Î” e)

  i' : {x y : X} â x â' y â Î·/ â x âĄ Î·/ â y
  i' e = Î·/-identifies-related-points â (rl-implication Î” e)

  f : X / â â X / â'
  f = mediating-map/ â (quotient-is-set â') (Î·/ â') i

  f' : X / â' â X / â
  f' = mediating-map/ â' (quotient-is-set â) (Î·/ â) i'

  a : (x : X) â f (f' (Î·/ â' x)) âĄ Î·/ â' x
  a x = f (f' (Î·/ â' x)) âĄâš I â©
        f (Î·/ â x)       âĄâš II â©
        Î·/ â' x          â
   where
    I  = ap f (universality-triangle/ â' (quotient-is-set â) (Î·/ â) i' x)
    II = universality-triangle/ â (quotient-is-set â') (Î·/ â') i x

  Î± : f â f' âŒ id
  Î± = /-induction â' (Î» u â f (f' u) âĄ u) (Î» u â quotient-is-set â') a

  a' : (x : X) â f' (f (Î·/ â x)) âĄ Î·/ â x
  a' x = f' (f (Î·/ â x)) âĄâš I â©
        f' (Î·/ â' x)     âĄâš II â©
        Î·/ â x           â
   where
    I  = ap f' (universality-triangle/ â (quotient-is-set â') (Î·/ â') i x)
    II = universality-triangle/ â' (quotient-is-set â) (Î·/ â) i' x

  Î±' : f' â f âŒ id
  Î±' = /-induction â (Î» u â f' (f u) âĄ u) (Î» u â quotient-is-set â) a'


  Îł : (X / â) â (X / â')
  Îł = qinveq f (f' , Î±' , Î±)

\end{code}
