Martin Escardo, 15th December 2019, 9th Feb 2021.

Vectors with a different type for each entry (vec), usual vectors
(Vec) and lists (List) in our spartan MLTT.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module SpartanMLTT-List where

open import SpartanMLTT
open import Fin

vec : (n : β) β (Fin n β π€ Μ ) β π€ Μ
vec 0        X = π
vec (succ n) X = X π Γ vec n (X β suc)

Vec : π€ Μ β β β π€ Μ
Vec X n = vec n (Ξ» _ β X)

List : π€ Μ β π€ Μ
List X = Ξ£ n κ β , Vec X n

length : {X : π€ Μ } β List X β β
length = prβ

pattern [] = (0 , β)

_β·_ : {X : π€ Μ } β X β List X β List X
x β· (n , s) = succ n , x , s

[_] : {X : π€ Μ } β X β List X
[ x ] = x β· []

\end{code}

Our list encoding satisfies Martin-LΓΆf's rules for lists:

\begin{code}

List-induction : {X : π€ Μ } (P : List X β π₯ Μ )
               β P []
               β ((x : X) (xs : List X) β P xs β P (x β· xs))
               β (xs : List X) β P xs
List-induction {π€} {π₯} {X} P p f = h
 where
  h : (xs : List X) β P xs
  h []               = p
  h (succ n , x , s) = f x (n , s) (h (n , s))

\end{code}

With the computation rules holding definitionally, as required:

\begin{code}

List-induction-[] : {X : π€ Μ } (P : List X β π₯ Μ )
               β (p : P [])
               β (f : (x : X) (xs : List X) β P xs β P (x β· xs))
               β List-induction P p f [] β‘ p
List-induction-[] {π€} {π₯} {X} P p f = refl

List-induction-β· : {X : π€ Μ } (P : List X β π₯ Μ )
               β (p : P [])
               β (f : (x : X) (xs : List X) β P xs β P (x β· xs))
               β (x : X)
               β (xs : List X)
               β List-induction P p f (x β· xs) β‘ f x xs (List-induction P p f xs)
List-induction-β· {π€} {π₯} {X} P p f x xs = refl

pattern β¨β©       = β
pattern _::_ x xs = (x , xs)

hd : {n : β} {X : Fin (succ n) β π€ Μ } β vec (succ n) X β X π
hd (x :: xs) = x

tl : {n : β} {X : Fin (succ n) β π€ Μ } β vec (succ n) X β vec n (X β suc)
tl (x :: xs) = xs

index : (n : β) {X : Fin n β π€ Μ } β vec n X β (i : Fin n) β X i
index 0        xs        i       = π-elim i
index (succ n) (x :: xs) π       = x
index (succ n) (x :: xs) (suc i) = index n xs i

_!!_ : {n : β} {X : π€ Μ } β Vec X n β (i : Fin n) β X
_!!_ {π€} {n} = index n

\end{code}

An isomorphic copy of vec n X.

\begin{code}

vec' : (n : β) β (Fin n β π€ Μ ) β π€ Μ
vec' n X = (i : Fin n) β X i

Vec' : β β π€ Μ β π€ Μ
Vec' n X = vec' n (Ξ» _ β X)

hd' : {n : β} {X : Fin (succ n) β π€ Μ } β vec' (succ n) X β X π
hd' xs = xs π

tl' : {n : β} {X : Fin (succ n) β π€ Μ } β vec' (succ n) X β vec' n (X β suc)
tl' xs = Ξ» i β xs (suc i)


β¨β©' : {X : Fin 0 β π€ Μ } β vec' 0 X
β¨β©' = Ξ» i β unique-from-π i


_::'_ : {n : β} {X : Fin (succ n) β π€ Μ }
     β X π β vec' n (X β suc) β vec' (succ n) X
(x ::' xs) π       = x
(x ::' xs) (suc i) = xs i


xedni : (n : β) {X : Fin n β π€ Μ } β ((i : Fin n) β X i) β vec n X
xedni 0        xs' = β¨β©
xedni (succ n) xs' = hd' xs' :: xedni n (tl' xs')


vecΞ· : (n : β) {X : Fin n β π€ Μ } β xedni n {X} β index n {X} βΌ id
vecΞ· zero     β¨β©       = refl
vecΞ· (succ n) (x :: xs) = ap (x ::_) (vecΞ· n xs)

open import UF-FunExt
open import UF-Base
open import UF-Equiv

module _ {π€} (fe : funext π€β π€) where

 vecΞ΅ : (n : β) {X : Fin n β π€ Μ } β index n {X} β xedni n {X} βΌ id
 vecΞ΅ 0        xs' = dfunext fe (Ξ» i β π-elim i)
 vecΞ΅ (succ n) xs' = dfunext fe h
  where
   h : (i : Fin (succ n)) β index (succ n) (xs' π :: xedni n (tl' xs')) i β‘ xs' i
   h π       = refl
   h (suc i) = happly (vecΞ΅ n (tl' xs')) i


 vec-β : (n : β) {X : Fin n β π€ Μ } β vec n X β vec' n X
 vec-β n {X} = qinveq (index n) (xedni n {X} , vecΞ· n , vecΞ΅ n)

\end{code}

9th Feb 2021. More operations on vectors. The stuff on
vectors should be eventually moved to another module.

\begin{code}

β¨_β© : {X : π€ Μ } β X β Vec X 1
β¨ x β© = x :: β¨β©

_β_ : β β β β β
zero   β n = n
succ m β n = succ (m β n)

append : {X : π€ Μ } (m n : β) β Vec X m β Vec X n β Vec X (m β n)
append zero     n β¨β©      t = t
append (succ m) n (x :: s) t = x :: append m n s t

_++_ : {X : π€ Μ } {m n : β} β Vec X m β Vec X n β Vec X (m β n)
_++_ = append _ _

plus-1-is-succ : (n : β) β n β 1 β‘ succ n
plus-1-is-succ zero     = refl
plus-1-is-succ (succ n) = ap succ (plus-1-is-succ n)

rev' : {X : π€ Μ } (n : β) β Vec X n β Vec X n
rev' zero     β¨β©      = β¨β©
rev' (succ n) (x :: s) = Ξ³
 where
  IH : Vec _ (n β 1)
  IH = rev' n s ++ β¨ x β©

  Ξ³ : Vec _ (succ n)
  Ξ³ = transport (Vec _) (plus-1-is-succ n) IH

rev : {X : π€ Μ } {n : β} β Vec X n β Vec X n
rev = rev' _

_+β_ : β β β β β
zero   +β n = n
succ m +β n = m +β succ n

rev-append : {X : π€ Μ } (m n : β) β Vec X m β Vec X n β Vec X (m +β n)
rev-append zero     n β¨β©       t = t
rev-append (succ m) n (x :: s) t = rev-append m (succ n) s (x :: t)

revβ : {X : π€ Μ } (m : β) β Vec X m β Vec X (m +β zero)
revβ n s = rev-append n zero s β¨β©

\end{code}
