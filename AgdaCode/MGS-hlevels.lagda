Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module MGS-hlevels where

open import MGS-Basic-UF public

_is-of-hlevel_ : π€ Μ β β β π€ Μ
X is-of-hlevel 0        = is-singleton X
X is-of-hlevel (succ n) = (x x' : X) β ((x β‘ x') is-of-hlevel n)

wconstant : {X : π€ Μ } {Y : π₯ Μ } β (X β Y) β π€ β π₯ Μ
wconstant f = (x x' : domain f) β f x β‘ f x'

wconstant-endomap : π€ Μ β π€ Μ
wconstant-endomap X = Ξ£ f κ (X β X), wconstant f

wcmap : (X : π€ Μ ) β wconstant-endomap X β (X β X)
wcmap X (f , w) = f

wcmap-constancy : (X : π€ Μ ) (c : wconstant-endomap X)
                β wconstant (wcmap X c)
wcmap-constancy X (f , w) = w

Hedberg : {X : π€ Μ } (x : X)
        β ((y : X) β wconstant-endomap (x β‘ y))
        β (y : X) β is-subsingleton (x β‘ y)

Hedberg {π€} {X} x c y p q =

 p                         β‘β¨ a y p β©
 (f x (refl x))β»ΒΉ β f y p  β‘β¨ ap (Ξ» - β (f x (refl x))β»ΒΉ β -) (ΞΊ y p q) β©
 (f x (refl x))β»ΒΉ β f y q  β‘β¨ (a y q)β»ΒΉ β©
 q                         β

 where
  f : (y : X) β x β‘ y β x β‘ y
  f y = wcmap (x β‘ y) (c y)

  ΞΊ : (y : X) (p q : x β‘ y) β f y p β‘ f y q
  ΞΊ y = wcmap-constancy (x β‘ y) (c y)

  a : (y : X) (p : x β‘ y) β p β‘ (f x (refl x))β»ΒΉ β f y p
  a x (refl x) = (β»ΒΉ-leftβ (f x (refl x)))β»ΒΉ

wconstant-β‘-endomaps : π€ Μ β π€ Μ
wconstant-β‘-endomaps X = (x y : X) β wconstant-endomap (x β‘ y)

sets-have-wconstant-β‘-endomaps : (X : π€ Μ ) β is-set X β wconstant-β‘-endomaps X
sets-have-wconstant-β‘-endomaps X s x y = (f , ΞΊ)
 where
  f : x β‘ y β x β‘ y
  f p = p

  ΞΊ : (p q : x β‘ y) β f p β‘ f q
  ΞΊ p q = s x y p q

types-with-wconstant-β‘-endomaps-are-sets : (X : π€ Μ )
                                         β wconstant-β‘-endomaps X β is-set X

types-with-wconstant-β‘-endomaps-are-sets X c x = Hedberg x
                                                  (Ξ» y β wcmap (x β‘ y) (c x y) ,
                                                   wcmap-constancy (x β‘ y) (c x y))

subsingletons-have-wconstant-β‘-endomaps : (X : π€ Μ )
                                        β is-subsingleton X
                                        β wconstant-β‘-endomaps X

subsingletons-have-wconstant-β‘-endomaps X s x y = (f , ΞΊ)
 where
  f : x β‘ y β x β‘ y
  f p = s x y

  ΞΊ : (p q : x β‘ y) β f p β‘ f q
  ΞΊ p q = refl (s x y)

subsingletons-are-sets : (X : π€ Μ ) β is-subsingleton X β is-set X
subsingletons-are-sets X s = types-with-wconstant-β‘-endomaps-are-sets X
                               (subsingletons-have-wconstant-β‘-endomaps X s)

singletons-are-sets : (X : π€ Μ ) β is-singleton X β is-set X
singletons-are-sets X = subsingletons-are-sets X β singletons-are-subsingletons X

π-is-set : is-set π
π-is-set = subsingletons-are-sets π π-is-subsingleton

π-is-set : is-set π
π-is-set = subsingletons-are-sets π π-is-subsingleton

subsingletons-are-of-hlevel-1 : (X : π€ Μ )
                              β is-subsingleton X
                              β X is-of-hlevel 1

subsingletons-are-of-hlevel-1 X = g
 where
  g : ((x y : X) β x β‘ y) β (x y : X) β is-singleton (x β‘ y)
  g t x y = t x y , subsingletons-are-sets X t x y (t x y)

types-of-hlevel-1-are-subsingletons : (X : π€ Μ )
                                    β X is-of-hlevel 1
                                    β is-subsingleton X

types-of-hlevel-1-are-subsingletons X = f
 where
  f : ((x y : X) β is-singleton (x β‘ y)) β (x y : X) β x β‘ y
  f s x y = center (x β‘ y) (s x y)

sets-are-of-hlevel-2 : (X : π€ Μ ) β is-set X β X is-of-hlevel 2
sets-are-of-hlevel-2 X = g
 where
  g : ((x y : X) β is-subsingleton (x β‘ y)) β (x y : X) β (x β‘ y) is-of-hlevel 1
  g t x y = subsingletons-are-of-hlevel-1 (x β‘ y) (t x y)

types-of-hlevel-2-are-sets : (X : π€ Μ ) β X is-of-hlevel 2 β is-set X
types-of-hlevel-2-are-sets X = f
 where
  f : ((x y : X) β (x β‘ y) is-of-hlevel 1) β (x y : X) β is-subsingleton (x β‘ y)
  f s x y = types-of-hlevel-1-are-subsingletons (x β‘ y) (s x y)

hlevel-upper : (X : π€ Μ ) (n : β) β X is-of-hlevel n β X is-of-hlevel (succ n)
hlevel-upper X zero = Ξ³
 where
  Ξ³ : is-singleton X β (x y : X) β is-singleton (x β‘ y)
  Ξ³ h x y = p , subsingletons-are-sets X k x y p
   where
    k : is-subsingleton X
    k = singletons-are-subsingletons X h

    p : x β‘ y
    p = k x y

hlevel-upper X (succ n) = Ξ» h x y β hlevel-upper (x β‘ y) n (h x y)

_has-minimal-hlevel_ : π€ Μ β β β π€ Μ
X has-minimal-hlevel 0        = X is-of-hlevel 0
X has-minimal-hlevel (succ n) = (X is-of-hlevel (succ n)) Γ Β¬ (X is-of-hlevel n)

_has-minimal-hlevel-β : π€ Μ β π€ Μ
X has-minimal-hlevel-β = (n : β) β Β¬ (X is-of-hlevel n)

pointed-types-have-wconstant-endomap : {X : π€ Μ } β X β wconstant-endomap X
pointed-types-have-wconstant-endomap x = ((Ξ» y β x) , (Ξ» y y' β refl x))

empty-types-have-wconstant-endomap : {X : π€ Μ } β is-empty X β wconstant-endomap X
empty-types-have-wconstant-endomap e = (id , (Ξ» x x' β !π (x β‘ x') (e x)))

decidable-has-wconstant-endomap : {X : π€ Μ } β decidable X β wconstant-endomap X
decidable-has-wconstant-endomap (inl x) = pointed-types-have-wconstant-endomap x
decidable-has-wconstant-endomap (inr e) = empty-types-have-wconstant-endomap e

hedberg-lemma : {X : π€ Μ } β has-decidable-equality X β wconstant-β‘-endomaps X
hedberg-lemma {π€} {X} d x y = decidable-has-wconstant-endomap (d x y)

hedberg : {X : π€ Μ } β has-decidable-equality X β is-set X
hedberg {π€} {X} d = types-with-wconstant-β‘-endomaps-are-sets X (hedberg-lemma d)

β-is-set : is-set β
β-is-set = hedberg β-has-decidable-equality

π-is-set : is-set π
π-is-set = hedberg π-has-decidable-equality

\end{code}
