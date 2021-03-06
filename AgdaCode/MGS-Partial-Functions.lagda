Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module MGS-Partial-Functions where

open import MGS-More-FunExt-Consequences public

ฮ โ : {X : ๐ค ฬ } โ (X โ ๐ฅ ฬ ) โ ๐ค โ (๐ฅ โบ) ฬ
ฮ โ {๐ค} {๐ฅ} {X} A = ฮฃ R ๊ ((x : X) โ A x โ ๐ฅ ฬ )
                       , ((x : X) โ is-subsingleton (ฮฃ a ๊ A x , R x a))

_โ_ : ๐ค ฬ โ ๐ฅ ฬ โ ๐ค โ (๐ฅ โบ) ฬ
X โ Y = ฮ โ (ฮป (_ : X) โ Y)

is-defined : {X : ๐ค ฬ } {A : X โ ๐ฅ ฬ } โ ฮ โ A โ X โ ๐ฅ ฬ
is-defined (R , ฯ) x = ฮฃ a ๊ _ , R x a

being-defined-is-subsingleton : {X : ๐ค ฬ } {A : X โ ๐ฅ ฬ } (f : ฮ โ A) (x : X)
                              โ is-subsingleton (is-defined f x)

being-defined-is-subsingleton (R , ฯ) x = ฯ x

_[_,_] :  {X : ๐ค ฬ } {A : X โ ๐ฅ ฬ } (f : ฮ โ A) (x : X) โ is-defined f x โ A x
(R , s) [ x , (a , r)] = a

_โกโ_ : {X : ๐ค ฬ } {A : X โ ๐ฅ ฬ } โ ฮ โ A โ ฮ โ A โ ๐ค โ ๐ฅ ฬ
f โกโ g = โ x โ (is-defined f x โ is-defined g x)
             ร ((i : is-defined f x) (j : is-defined g x) โ f [ x , i ] โก g [ x , j ])

module ฮผ-operator (fe : dfunext ๐คโ ๐คโ) where

 open basic-arithmetic-and-order

 being-minimal-root-is-subsingleton : (f : โ โ โ) (m : โ)
                                    โ is-subsingleton (is-minimal-root f m)

 being-minimal-root-is-subsingleton f m = ร-is-subsingleton
                                           (โ-is-set (f m) 0)
                                           (ฮ -is-subsingleton fe
                                              (ฮป _ โ ฮ -is-subsingleton fe
                                              (ฮป _ โ ฮ -is-subsingleton fe
                                              (ฮป _ โ ๐-is-subsingleton))))

 minimal-root-is-subsingleton : (f : โ โ โ)
                              โ is-subsingleton (minimal-root f)

 minimal-root-is-subsingleton f (m , p , ฯ) (m' , p' , ฯ') =
   to-subtype-โก
    (being-minimal-root-is-subsingleton f)
    (at-most-one-minimal-root f m m' (p , ฯ) (p' , ฯ'))

 ฮผ : (โ โ โ) โ โ
 ฮผ = is-minimal-root , minimal-root-is-subsingleton

 ฮผ-propertyโ : (f : โ โ โ) โ (ฮฃ n ๊ โ , f n โก 0) โ is-defined ฮผ f
 ฮผ-propertyโ = root-gives-minimal-root

 ฮผ-propertyโ : (f : โ โ โ) (i : is-defined ฮผ f)
             โ (f (ฮผ [ f , i ]) โก 0)
             ร ((n : โ) โ n < ฮผ [ f , i ] โ f n โข 0)

 ฮผ-propertyโ f = prโ

is-total : {X : ๐ค ฬ } {A : X โ ๐ฅ ฬ } โ ฮ โ A โ ๐ค โ ๐ฅ ฬ
is-total f = โ x โ is-defined f x

infix  30 _[_,_]

\end{code}
