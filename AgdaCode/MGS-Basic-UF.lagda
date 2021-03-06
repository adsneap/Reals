Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module MGS-Basic-UF where

open import MGS-MLTT public

is-center : (X : ๐ค ฬ ) โ X โ ๐ค ฬ
is-center X c = (x : X) โ c โก x

is-singleton : ๐ค ฬ โ ๐ค ฬ
is-singleton X = ฮฃ c ๊ X , is-center X c

๐-is-singleton : is-singleton ๐
๐-is-singleton = โ , ๐-induction (ฮป x โ โ โก x) (refl โ)

center : (X : ๐ค ฬ ) โ is-singleton X โ X
center X (c , ฯ) = c

centrality : (X : ๐ค ฬ ) (i : is-singleton X) (x : X) โ center X i โก x
centrality X (c , ฯ) = ฯ

is-subsingleton : ๐ค ฬ โ ๐ค ฬ
is-subsingleton X = (x y : X) โ x โก y

๐-is-subsingleton : is-subsingleton ๐
๐-is-subsingleton x y = !๐ (x โก y) x

singletons-are-subsingletons : (X : ๐ค ฬ ) โ is-singleton X โ is-subsingleton X
singletons-are-subsingletons X (c , ฯ) x y = x โกโจ (ฯ x)โปยน โฉ
                                             c โกโจ ฯ y โฉ
                                             y โ

๐-is-subsingleton : is-subsingleton ๐
๐-is-subsingleton = singletons-are-subsingletons ๐ ๐-is-singleton

pointed-subsingletons-are-singletons : (X : ๐ค ฬ )
                                     โ X โ is-subsingleton X โ is-singleton X

pointed-subsingletons-are-singletons X x s = (x , s x)

singleton-iff-pointed-and-subsingleton : {X : ๐ค ฬ }
                                       โ is-singleton X โ (X ร is-subsingleton X)

singleton-iff-pointed-and-subsingleton {๐ค} {X} = (a , b)
 where
  a : is-singleton X โ X ร is-subsingleton X
  a s = center X s , singletons-are-subsingletons X s

  b : X ร is-subsingleton X โ is-singleton X
  b (x , t) = pointed-subsingletons-are-singletons X x t

is-prop is-truth-value : ๐ค ฬ โ ๐ค ฬ
is-prop        = is-subsingleton
is-truth-value = is-subsingleton

is-set : ๐ค ฬ โ ๐ค ฬ
is-set X = (x y : X) โ is-subsingleton (x โก y)

EM EM' : โ ๐ค โ ๐ค โบ ฬ
EM  ๐ค = (X : ๐ค ฬ ) โ is-subsingleton X โ X + ยฌ X
EM' ๐ค = (X : ๐ค ฬ ) โ is-subsingleton X โ is-singleton X + is-empty X

EM-gives-EM' : EM ๐ค โ EM' ๐ค
EM-gives-EM' em X s = ฮณ (em X s)
 where
  ฮณ : X + ยฌ X โ is-singleton X + is-empty X
  ฮณ (inl x) = inl (pointed-subsingletons-are-singletons X x s)
  ฮณ (inr x) = inr x

EM'-gives-EM : EM' ๐ค โ EM ๐ค
EM'-gives-EM em' X s = ฮณ (em' X s)
 where
  ฮณ : is-singleton X + is-empty X โ X + ยฌ X
  ฮณ (inl i) = inl (center X i)
  ฮณ (inr x) = inr x

no-unicorns : ยฌ (ฮฃ X ๊ ๐ค ฬ , is-subsingleton X ร ยฌ (is-singleton X) ร ยฌ (is-empty X))
no-unicorns (X , i , f , g) = c
 where
  e : is-empty X
  e x = f (pointed-subsingletons-are-singletons X x i)

  c : ๐
  c = g e

module magmas where

 Magma : (๐ค : Universe) โ ๐ค โบ ฬ
 Magma ๐ค = ฮฃ X ๊ ๐ค ฬ , is-set X ร (X โ X โ X)

 โจ_โฉ : Magma ๐ค โ ๐ค ฬ
 โจ X , i , _ยท_ โฉ = X

 magma-is-set : (M : Magma ๐ค) โ is-set โจ M โฉ
 magma-is-set (X , i , _ยท_) = i

 magma-operation : (M : Magma ๐ค) โ โจ M โฉ โ โจ M โฉ โ โจ M โฉ
 magma-operation (X , i , _ยท_) = _ยท_

 syntax magma-operation M x y = x ยทโจ M โฉ y

 is-magma-hom : (M N : Magma ๐ค) โ (โจ M โฉ โ โจ N โฉ) โ ๐ค ฬ
 is-magma-hom M N f = (x y : โจ M โฉ) โ f (x ยทโจ M โฉ y) โก f x ยทโจ N โฉ f y

 id-is-magma-hom : (M : Magma ๐ค) โ is-magma-hom M M (๐๐ โจ M โฉ)
 id-is-magma-hom M = ฮป (x y : โจ M โฉ) โ refl (x ยทโจ M โฉ y)

 is-magma-iso : (M N : Magma ๐ค) โ (โจ M โฉ โ โจ N โฉ) โ ๐ค ฬ
 is-magma-iso M N f = is-magma-hom M N f
                    ร (ฮฃ g ๊ (โจ N โฉ โ โจ M โฉ), is-magma-hom N M g
                                            ร (g โ f โผ ๐๐ โจ M โฉ)
                                            ร (f โ g โผ ๐๐ โจ N โฉ))

 id-is-magma-iso : (M : Magma ๐ค) โ is-magma-iso M M (๐๐ โจ M โฉ)
 id-is-magma-iso M = id-is-magma-hom M ,
                     ๐๐ โจ M โฉ ,
                     id-is-magma-hom M ,
                     refl ,
                     refl

 Idโiso : {M N : Magma ๐ค} โ M โก N โ โจ M โฉ โ โจ N โฉ
 Idโiso p = transport โจ_โฉ p

 Idโiso-is-iso : {M N : Magma ๐ค} (p : M โก N) โ is-magma-iso M N (Idโiso p)
 Idโiso-is-iso (refl M) = id-is-magma-iso M

 _โโ_ : Magma ๐ค โ Magma ๐ค โ ๐ค ฬ
 M โโ N = ฮฃ f ๊ (โจ M โฉ โ โจ N โฉ), is-magma-iso M N f

 magma-Idโiso : {M N : Magma ๐ค} โ M โก N โ M โโ N
 magma-Idโiso p = (Idโiso p , Idโiso-is-iso p)

 โ-Magma : (๐ค : Universe) โ ๐ค โบ ฬ
 โ-Magma ๐ค = ฮฃ X ๊ ๐ค ฬ , (X โ X โ X)

module monoids where

 left-neutral : {X : ๐ค ฬ } โ X โ (X โ X โ X) โ ๐ค ฬ
 left-neutral e _ยท_ = โ x โ e ยท x โก x

 right-neutral : {X : ๐ค ฬ } โ X โ (X โ X โ X) โ ๐ค ฬ
 right-neutral e _ยท_ = โ x โ x ยท e โก x

 associative : {X : ๐ค ฬ } โ (X โ X โ X) โ ๐ค ฬ
 associative _ยท_ = โ x y z โ (x ยท y) ยท z โก x ยท (y ยท z)

 Monoid : (๐ค : Universe) โ ๐ค โบ ฬ
 Monoid ๐ค = ฮฃ X ๊ ๐ค  ฬ , is-set X
                      ร (ฮฃ ยท ๊ (X โ X โ X) , (ฮฃ e ๊ X , (left-neutral e ยท)
                                                      ร (right-neutral e ยท)
                                                      ร (associative ยท)))

refl-left : {X : ๐ค ฬ } {x y : X} {p : x โก y} โ refl x โ p โก p
refl-left {๐ค} {X} {x} {x} {refl x} = refl (refl x)

refl-right : {X : ๐ค ฬ } {x y : X} {p : x โก y} โ p โ refl y โก p
refl-right {๐ค} {X} {x} {y} {p} = refl p

โassoc : {X : ๐ค ฬ } {x y z t : X} (p : x โก y) (q : y โก z) (r : z โก t)
       โ (p โ q) โ r โก p โ (q โ r)

โassoc p q (refl z) = refl (p โ q)

โปยน-leftโ : {X : ๐ค ฬ } {x y : X} (p : x โก y)
         โ p โปยน โ p โก refl y

โปยน-leftโ (refl x) = refl (refl x)

โปยน-rightโ : {X : ๐ค ฬ } {x y : X} (p : x โก y)
          โ p โ p โปยน โก refl x

โปยน-rightโ (refl x) = refl (refl x)

โปยน-involutive : {X : ๐ค ฬ } {x y : X} (p : x โก y)
              โ (p โปยน)โปยน โก p

โปยน-involutive (refl x) = refl (refl x)

ap-refl : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } (f : X โ Y) (x : X)
        โ ap f (refl x) โก refl (f x)

ap-refl f x = refl (refl (f x))

ap-โ : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } (f : X โ Y) {x y z : X} (p : x โก y) (q : y โก z)
     โ ap f (p โ q) โก ap f p โ ap f q

ap-โ f p (refl y) = refl (ap f p)

apโปยน : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } (f : X โ Y) {x y : X} (p : x โก y)
     โ (ap f p)โปยน โก ap f (p โปยน)

apโปยน f (refl x) = refl (refl (f x))

ap-id : {X : ๐ค ฬ } {x y : X} (p : x โก y)
      โ ap id p โก p

ap-id (refl x) = refl (refl x)

ap-โ : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } {Z : ๐ฆ ฬ }
       (f : X โ Y) (g : Y โ Z) {x y : X} (p : x โก y)
     โ ap (g โ f) p โก (ap g โ ap f) p

ap-โ f g (refl x) = refl (refl (g (f x)))

transportโ : {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ ) {x y z : X} (p : x โก y) (q : y โก z)
           โ transport A (p โ q) โก transport A q โ transport A p

transportโ A p (refl y) = refl (transport A p)

Nat : {X : ๐ค ฬ } โ (X โ ๐ฅ ฬ ) โ (X โ ๐ฆ ฬ ) โ ๐ค โ ๐ฅ โ ๐ฆ ฬ
Nat A B = (x : domain A) โ A x โ B x

Nats-are-natural : {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ ) (B : X โ ๐ฆ ฬ ) (ฯ : Nat A B)
                 โ {x y : X} (p : x โก y)
                 โ ฯ y โ transport A p โก transport B p โ ฯ x

Nats-are-natural A B ฯ (refl x) = refl (ฯ x)

Natฮฃ : {X : ๐ค ฬ } {A : X โ ๐ฅ ฬ } {B : X โ ๐ฆ ฬ } โ Nat A B โ ฮฃ A โ ฮฃ B
Natฮฃ ฯ (x , a) = (x , ฯ x a)

transport-ap : {X : ๐ค ฬ } {Y : ๐ฅ ฬ } (A : Y โ ๐ฆ ฬ )
               (f : X โ Y) {x x' : X} (p : x โก x') (a : A (f x))
             โ transport (A โ f) p a โก transport A (ap f p) a

transport-ap A f (refl x) a = refl a

data Color : ๐คโ ฬ  where
 Black White : Color

apd : {X : ๐ค ฬ } {A : X โ ๐ฅ ฬ } (f : (x : X) โ A x) {x y : X}
      (p : x โก y) โ transport A p (f x) โก f y

apd f (refl x) = refl (f x)

to-ฮฃ-โก : {X : ๐ค ฬ } {A : X โ ๐ฅ ฬ } {ฯ ฯ : ฮฃ A}
       โ (ฮฃ p ๊ prโ ฯ โก prโ ฯ , transport A p (prโ ฯ) โก prโ ฯ)
       โ ฯ โก ฯ

to-ฮฃ-โก (refl x , refl a) = refl (x , a)

from-ฮฃ-โก : {X : ๐ค ฬ } {A : X โ ๐ฅ ฬ } {ฯ ฯ : ฮฃ A}
         โ ฯ โก ฯ
         โ ฮฃ p ๊ prโ ฯ โก prโ ฯ , transport A p (prโ ฯ) โก prโ ฯ

from-ฮฃ-โก (refl (x , a)) = (refl x , refl a)

to-ฮฃ-โก' : {X : ๐ค ฬ } {A : X โ ๐ฅ ฬ } {x : X} {a a' : A x}
        โ a โก a' โ Id (ฮฃ A) (x , a) (x , a')

to-ฮฃ-โก' {๐ค} {๐ฅ} {X} {A} {x} = ap (ฮป - โ (x , -))

transport-ร : {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ ) (B : X โ ๐ฆ ฬ )
                {x y : X} (p : x โก y) {c : A x ร B x}

            โ transport (ฮป x โ A x ร B x) p c
            โก (transport A p (prโ c) , transport B p (prโ c))

transport-ร A B (refl _) = refl _

transportd : {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ ) (B : (x : X) โ A x โ ๐ฆ ฬ )
             {x : X} (a : A x) ((a' , b) : ฮฃ a ๊ A x , B x a) {y : X} (p : x โก y)
           โ B x a' โ B y (transport A p a')

transportd A B a ฯ (refl y) = id

transport-ฮฃ : {X : ๐ค ฬ } (A : X โ ๐ฅ ฬ ) (B : (x : X) โ A x โ ๐ฆ ฬ )
              {x : X} (y : X) (p : x โก y) (a : A x) {(a' , b) : ฮฃ a ๊ A x , B x a}

            โ transport (ฮป x โ ฮฃ y ๊ A x , B x y) p (a' , b)
            โก transport A p a' , transportd A B a (a' , b) p b

transport-ฮฃ A B {x} x (refl x) a {ฯ} = refl ฯ

\end{code}
