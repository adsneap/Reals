Martin Escardo and Paulo Oliva 2021

Non-spartan types in MLTT, which are definable from spartan MLTT, but we include here for some work on game theory with Paulo Oliva.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module NonSpartanMLTTTypes where

open import SpartanMLTT

open import Universes

data Maybe {๐ค : Universe} (A : ๐ค ฬ ) : ๐ค ฬ where
 Nothing : Maybe A
 Just    : A โ Maybe A

Just-is-not-Nothing : {A : ๐ค ฬ } {a : A} โ Just a โข Nothing
Just-is-not-Nothing ()

Nothing-is-isolated : {A : ๐ค ฬ } (x : Maybe A) โ decidable (Nothing โก x)
Nothing-is-isolated Nothing  = inl refl
Nothing-is-isolated (Just a) = inr (ฮป (p : Nothing โก Just a) โ Just-is-not-Nothing (p โปยน))

Nothing-is-isolated' : {A : ๐ค ฬ } (x : Maybe A) โ decidable (x โก Nothing)
Nothing-is-isolated' Nothing  = inl refl
Nothing-is-isolated' (Just a) = inr Just-is-not-Nothing

open import UF-Miscelanea
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-Subsingletons

Nothing-is-h-isolated : {A : ๐ค ฬ } (x : Maybe A) โ is-prop (Nothing โก x)
Nothing-is-h-isolated x = isolated-is-h-isolated Nothing Nothing-is-isolated

Nothing-is-h-isolated' : {A : ๐ค ฬ } (x : Maybe A) โ is-prop (x โก Nothing)
Nothing-is-h-isolated' x = equiv-to-prop โก-flip (Nothing-is-h-isolated x)

data Bool : ๐คโ ฬ where
 true false : Bool

true-is-not-false : true โข false
true-is-not-false ()

if_then_else_ : {X : ๐ค ฬ } โ Bool โ X โ X โ X
if true  then x else y = x
if false then x else y = y

Bool-induction : (A : Bool โ ๐ค ฬ ) โ A true โ A false โ (b : Bool) โ A b
Bool-induction A x y true  = x
Bool-induction A x y false = y

Bool-equality-cases : {A : ๐ค ฬ } (x : Bool) โ (x โก true โ A) โ (x โก false โ A) โ A
Bool-equality-cases true  f g = f refl
Bool-equality-cases false f g = g refl

not : Bool โ Bool
not false = true
not true  = false

_||_ _&&_ : Bool โ Bool โ Bool

true  || y = true
false || y = y

true  && y = y
false && y = false

true-right-||-absorptive : (x : Bool) โ x || true โก true
true-right-||-absorptive true  = refl
true-right-||-absorptive false = refl

||-left-intro : ({x} y : Bool) โ x โก true โ x || y โก true
||-left-intro {true} y e = refl

||-right-intro : ({x} y : Bool) โ y โก true โ x || y โก true
||-right-intro {true}  true e = refl
||-right-intro {false} true e = refl

||-gives-+ : {x y : Bool} โ x || y โก true โ (x โก true) + (y โก true)
||-gives-+ {true}  {y}    _ = inl refl
||-gives-+ {false} {true} _ = inr refl

&&-gives-ร : {x y : Bool} โ x && y โก true โ (x โก true) ร (y โก true)
&&-gives-ร {true} {true} _ = refl , refl

&&-intro : {x y : Bool} โ x โก true โ y โก true โ x && y โก true
&&-intro {true} {true} refl refl = refl

infixl 10 _||_
infixl 20 _&&_

record Eq {๐ค} (X : ๐ค ฬ ) : ๐ค ฬ  where
  field
    _==_    : X โ X โ Bool
    ==-refl : (x : X) โ (x == x) โก true

open Eq {{...}} public

data List {๐ค : Universe} (X : ๐ค ฬ ) : ๐ค ฬ where
 []  : List X
 _โท_ : X โ List X โ List X

infixr 3 _โท_

_++_ : {๐ค : Universe} {X : ๐ค ฬ } โ List X โ List X โ List X
[]       ++ ys = ys
(x โท xs) ++ ys = x โท (xs ++ ys)

empty : {๐ค : Universe} {X : ๐ค ฬ } โ List X โ Bool
empty []       = true
empty (x โท xs) = false

map : {X : ๐ค ฬ } {Y : ๐ฅ ฬ }
    โ (X โ Y)
    โ List X โ List Y
map f []       = []
map f (x โท xs) = f x โท map f xs

module list-util
          {๐ค : Universe}
          {X : ๐ค ฬ }
          {{_ : Eq X}}
        where

  _is-in_ : X โ List X โ Bool
  x is-in []       = false
  x is-in (y โท ys) = (x == y) || (x is-in ys)

  insert : X โ List X โ List X
  insert x xs = x โท xs

  _contained-in_ : List X โ List X โ Bool
  []       contained-in ys = true
  (x โท xs) contained-in ys = (x is-in ys) && (xs contained-in ys)

  contained-lemmaโ : (x z : X) (xs ys : List X)
                   โ ys contained-in (x โท xs) โก true
                   โ ys contained-in (x โท z โท xs) โก true
  contained-lemmaโ x z xs []       e = e
  contained-lemmaโ x z xs (y โท ys) e = ฮณ
   where
    IH : ys contained-in (x โท xs) โก true โ ys contained-in (x โท z โท xs) โก true
    IH = contained-lemmaโ x z xs ys

    eโ : (y == x) || (y is-in xs) โก true
    eโ = prโ (&&-gives-ร e)

    eโ : ys contained-in (x โท xs) โก true
    eโ = prโ (&&-gives-ร e)

    a : (y == x) || ((y == z) || (y is-in xs)) โก true
    a = Cases (||-gives-+ eโ)
         (ฮป (e : (y == x) โก true)   โ ||-left-intro ((y == z) || (y is-in xs)) e)
         (ฮป (e : y is-in xs โก true) โ ||-right-intro {y == x} ((y == z) || (y is-in xs)) (||-right-intro (y is-in xs) e))

    b : ys contained-in (x โท z โท xs) โก true
    b = IH eโ

    ฮณ : ((y == x) || ((y == z) || (y is-in xs))) && (ys contained-in (x โท z โท xs)) โก true
    ฮณ = &&-intro a b

  contained-lemmaโ : (x : X) (ys : List X)
                   โ ys contained-in (x โท ys) โก true
  contained-lemmaโ x []       = refl
  contained-lemmaโ x (y โท ys) = ฮณ
   where
    IH : ys contained-in (x โท ys) โก true
    IH = contained-lemmaโ x ys

    a : y == x || (y == y || (y is-in ys)) โก true
    a = ||-right-intro {y == x} ((y == y) || (y is-in ys)) (||-left-intro (y is-in ys) (==-refl y))

    b : ys contained-in (x โท y โท ys) โก true
    b = contained-lemmaโ x y ys ys IH

    ฮณ : (y == x || (y == y || (y is-in ys))) && (ys contained-in (x โท y โท ys)) โก true
    ฮณ = &&-intro a b

  some-contained : List (List X) โ List X โ Bool
  some-contained []         ys = false
  some-contained (xs โท xss) ys = xs contained-in ys || some-contained xss ys

  remove-first : X โ List X โ List X
  remove-first x []       = []
  remove-first x (y โท ys) = if x == y then ys else (y โท remove-first x ys)

  remove-all : X โ List X โ List X
  remove-all x []       = []
  remove-all x (y โท ys) = if x == y then remove-all x ys else (y โท remove-all x ys)

  _minus_ : List X โ List X โ List X
  xs minus []       = xs
  xs minus (y โท ys) = (remove-all y xs) minus ys

data Fin : โ โ ๐คโ  ฬ  where
 ๐   : {n : โ} โ Fin (succ n)
 suc : {n : โ} โ Fin n โ Fin (succ n)

pattern ๐ = suc ๐
pattern ๐ = suc ๐
pattern ๐ = suc ๐
pattern ๐ = suc ๐
pattern ๐ = suc ๐
pattern ๐ = suc ๐
pattern ๐ = suc ๐
pattern ๐ = suc ๐
pattern ๐ = suc ๐

list-Fin : (n : โ) โ List (Fin n)
list-Fin zero     = []
list-Fin (succ n) = ๐ โท map suc (list-Fin n)

Fin-== : {n : โ} โ Fin n โ Fin n โ Bool
Fin-== {succ n} (suc x) (suc y) = Fin-== {n} x y
Fin-== {succ n} (suc x) ๐       = false
Fin-== {succ n} ๐       (suc y) = false
Fin-== {succ n} ๐       ๐       = true

Fin-refl : {n : โ} (x : Fin n) โ (Fin-== x x) โก true
Fin-refl {succ n} (suc x) = Fin-refl {n} x
Fin-refl {succ n} ๐       = refl

module _ {n : โ} where
 instance
  eqFin : Eq (Fin n)
  _==_    {{eqFin}} = Fin-== {n}
  ==-refl {{eqFin}} = Fin-refl {n}

\end{code}
