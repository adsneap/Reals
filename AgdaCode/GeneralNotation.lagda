General terminology and notation.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module GeneralNotation where

open import Sigma
open import Universes
open import Id
open import Negation public

Type  = Set
Typeโ = Setโ

reflexive : {X : ๐ค ฬ } โ (X โ X โ ๐ฅ ฬ ) โ ๐ค โ ๐ฅ ฬ
reflexive R = โ x โ R x x

symmetric : {X : ๐ค ฬ } โ (X โ X โ ๐ฅ ฬ ) โ ๐ค โ ๐ฅ ฬ
symmetric R = โ x y โ R x y โ R y x

antisymmetric : {X : ๐ค ฬ } โ (X โ X โ ๐ฅ ฬ ) โ ๐ค โ ๐ฅ ฬ
antisymmetric R = โ x y โ R x y โ R y x โ x โก y

transitive : {X : ๐ค ฬ } โ (X โ X โ ๐ฅ ฬ ) โ ๐ค โ ๐ฅ ฬ
transitive R = โ x y z โ R x y โ R y z โ R x z

idempotent-map : {X : ๐ฅ ฬ } โ (f : X โ X) โ ๐ฅ ฬ
idempotent-map f = โ x โ f (f x) โก f x

involutive : {X : ๐ฅ ฬ } โ (f : X โ X) โ ๐ฅ ฬ
involutive f = โ x โ f (f x) โก x

left-neutral : {X : ๐ค ฬ } โ X โ (X โ X โ X) โ ๐ค ฬ
left-neutral e _ยท_ = โ x โ e ยท x โก x

right-neutral : {X : ๐ค ฬ } โ X โ (X โ X โ X) โ ๐ค ฬ
right-neutral e _ยท_ = โ x โ x ยท e โก x

associative : {X : ๐ค ฬ } โ (X โ X โ X) โ ๐ค ฬ
associative _ยท_ = โ x y z โ (x ยท y) ยท z โก x ยท (y ยท z)

commutative : {X : ๐ค ฬ } โ (X โ X โ X) โ ๐ค ฬ
commutative _ยท_ = โ x y โ (x ยท y) โก (y ยท x)

left-cancellable : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } โ (X โ Y) โ ๐ค โ ๐ฅ ฬ
left-cancellable f = โ {x x'} โ f x โก f x' โ x โก x'

left-cancellable' : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } โ (X โ Y) โ ๐ค โ ๐ฅ ฬ
left-cancellable' f = โ x x' โ f x โก f x' โ x โก x'

_โ_ : ๐ค ฬ โ ๐ฅ ฬ โ ๐ค โ ๐ฅ ฬ
A โ B = (A โ B) ร (B โ A)

lr-implication : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } โ (X โ Y) โ (X โ Y)
lr-implication = prโ

rl-implication : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } โ (X โ Y) โ (Y โ X)
rl-implication = prโ

\end{code}

This is to avoid naming implicit arguments:

\begin{code}

type-of : {X : ๐ค ฬ } โ X โ ๐ค ฬ
type-of {๐ค} {X} x = X

\end{code}

We use the following to indicate the type of a subterm (where "โถ"
(typed "\:" in emacs) is not the same as ":"):

\begin{code}

-id : (X : ๐ค ฬ ) โ X โ X
-id X x = x

syntax -id X x = x โถ X

\end{code}

This is used for efficiency as a substitute for lazy "let" (or "where"):

\begin{code}

case_of_ : {A : ๐ค ฬ } {B : A โ ๐ฅ ฬ } โ (a : A) โ ((a : A) โ B a) โ B a
case x of f = f x

Case_of_ : {A : ๐ค ฬ } {B : A โ ๐ฅ ฬ } โ (a : A) โ (f : (x : A) โ x โก a โ B a) โ B a
Case x of f = f x refl

{-# NOINLINE case_of_ #-}

\end{code}

Notation to try to make proofs readable:

\begin{code}

need_which-is-given-by_ : (A : ๐ค ฬ ) โ A โ A
need A which-is-given-by a = a

have_so_ : {A : ๐ค ฬ } {B : ๐ฅ ฬ } โ A โ B โ B
have a so b = b

have_so-use_ : {A : ๐ค ฬ } {B : ๐ฅ ฬ } โ A โ B โ B
have a so-use b = b

have_and_ : {A : ๐ค ฬ } {B : ๐ฅ ฬ } โ A โ B โ B
have a and b = b

apply_to_ : {A : ๐ค ฬ } {B : ๐ฅ ฬ } โ (A โ B) โ A โ B
apply f to a = f a

have_so-apply_ : {A : ๐ค ฬ } {B : ๐ฅ ฬ } โ A โ (A โ B) โ B
have a so-apply f = f a

assume-then : (A : ๐ค ฬ ) {B : A โ ๐ฅ ฬ } โ ((a : A) โ B a) โ (a : A) โ B a
assume-then A f x = f x

syntax assume-then A (ฮป x โ b) = assume x โถ A then b

assume-and : (A : ๐ค ฬ ) {B : A โ ๐ฅ ฬ } โ ((a : A) โ B a) โ (a : A) โ B a
assume-and A f x = f x

syntax assume-and A (ฮป x โ b) = assume x โถ A and b

mapsto : {A : ๐ค ฬ } {B : A โ ๐ฅ ฬ } โ ((a : A) โ B a) โ (a : A) โ B a
mapsto f = f

syntax mapsto (ฮป x โ b) = x โฆ b

infixr 10 mapsto

Mapsto : (A : ๐ค ฬ ) {B : A โ ๐ฅ ฬ } โ ((a : A) โ B a) โ (a : A) โ B a
Mapsto A f = f

syntax Mapsto A (ฮป x โ b) = x ๊ A โฆ b

infixr 10 Mapsto

\end{code}

Get rid of this:

\begin{code}

ฮฃ! : {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ ) โ ๐ค โ ๐ฅ ฬ
ฮฃ! {๐ค} {๐ฅ} {X} A = (ฮฃ x ๊ X , A x) ร ((x x' : X) โ A x โ A x' โ x โก x')

Sigma! : (X : ๐ค ฬ ) (A : X โ ๐ฅ ฬ ) โ ๐ค โ ๐ฅ ฬ
Sigma! X A = ฮฃ! A

syntax Sigma! A (ฮป x โ b) = ฮฃ! x ๊ A , b

infixr -1 Sigma!

\end{code}

Note: ฮฃ! is to be avoided, in favour of the contractibility of ฮฃ,
following univalent mathematics.

Fixities:

\begin{code}

infixl -1 -id
infix -1 _โ_

\end{code}
