Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module MGS-Embeddings where

open import MGS-More-FunExt-Consequences public

is-embedding : {X : ð¤ Ì } {Y : ð¥ Ì } â (X â Y) â ð¤ â ð¥ Ì
is-embedding f = (y : codomain f) â is-subsingleton (fiber f y)

being-embedding-is-subsingleton : global-dfunext
                                â {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                                â is-subsingleton (is-embedding f)

being-embedding-is-subsingleton fe f =
 Î -is-subsingleton fe
  (Î» x â being-subsingleton-is-subsingleton fe)

prâ-embedding : (A : ð¤ Ì ) (X : ð¥ Ì )
              â is-subsingleton A
              â is-embedding (Î» (z : A Ã X) â prâ z)

prâ-embedding A X i x ((a , x) , refl x) ((b , x) , refl x) = p
 where
  p : ((a , x) , refl x) â¡ ((b , x) , refl x)
  p = ap (Î» - â ((- , x) , refl x)) (i a b)

prâ-embedding : {X : ð¤ Ì } {A : X â ð¥ Ì }
              â ((x : X) â is-subsingleton (A x))
              â is-embedding (Î» (Ï : Î£ A) â prâ Ï)

prâ-embedding i x ((x , a) , refl x) ((x , a') , refl x) = Î³
 where
  p : a â¡ a'
  p = i x a a'

  Î³ : (x , a) , refl x â¡ (x , a') , refl x
  Î³ = ap (Î» - â (x , -) , refl x) p

equivs-are-embeddings : {X : ð¤ Ì } {Y : ð¥ Ì }
                        (f : X â Y)
                      â is-equiv f â is-embedding f

equivs-are-embeddings f i y = singletons-are-subsingletons (fiber f y) (i y)

id-is-embedding : {X : ð¤ Ì } â is-embedding (ðð X)
id-is-embedding {ð¤} {X} = equivs-are-embeddings id (id-is-equiv X)

â-embedding : {X : ð¤ Ì } {Y : ð¥ Ì } {Z : ð¦ Ì }
              {f : X â Y} {g : Y â Z}
            â is-embedding g  â is-embedding f â is-embedding (g â f)

â-embedding {ð¤} {ð¥} {ð¦} {X} {Y} {Z} {f} {g} d e = h
 where
  A : (z : Z) â ð¤ â ð¥ â ð¦ Ì
  A z = Î£ (y , p) ê fiber g z , fiber f y

  i : (z : Z) â is-subsingleton (A z)
  i z = Î£-is-subsingleton (d z) (Î» w â e (prâ w))

  Ï : (z : Z) â fiber (g â f) z â A z
  Ï z (x , p) = (f x , p) , x , refl (f x)

  Î³ : (z : Z) â A z â fiber (g â f) z
  Î³ z ((_ , p) , x , refl _) = x , p

  Î· : (z : Z) (t : fiber (g â f) z) â Î³ z (Ï z t) â¡ t
  Î· _ (x , refl _) = refl (x , refl ((g â f) x))

  h : (z : Z) â is-subsingleton (fiber (g â f) z)
  h z = lc-maps-reflect-subsingletons (Ï z) (sections-are-lc (Ï z) (Î³ z , Î· z)) (i z)

embedding-lemma : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                â ((x : X) â is-singleton (fiber f (f x)))
                â is-embedding f

embedding-lemma f Ï = Î³
 where
  Î³ : (y : codomain f) (u v : fiber f y) â u â¡ v
  Î³ y (x , p) v = j (x , p) v
   where
    q : fiber f (f x) â¡ fiber f y
    q = ap (fiber f) p

    i : is-singleton (fiber f y)
    i = transport is-singleton q (Ï x)

    j : is-subsingleton (fiber f y)
    j = singletons-are-subsingletons (fiber f y) i

embedding-criterion : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                    â ((x x' : X) â (f x â¡ f x') â (x â¡ x'))
                    â is-embedding f

embedding-criterion f e = embedding-lemma f b
 where
  X = domain f

  a : (x : X) â (Î£ x' ê X , f x' â¡ f x) â (Î£ x' ê X , x' â¡ x)
  a x = Î£-cong (Î» x' â e x' x)

  a' : (x : X) â fiber f (f x) â singleton-type x
  a' = a

  b : (x : X) â is-singleton (fiber f (f x))
  b x = equiv-to-singleton (a' x) (singleton-types-are-singletons X x)

ap-is-equiv-gives-embedding : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                            â ((x x' : X) â is-equiv (ap f {x} {x'}))
                            â is-embedding f

ap-is-equiv-gives-embedding f i = embedding-criterion f
                                   (Î» x' x â â-sym (ap f {x'} {x} , i x' x))

embedding-gives-ap-is-equiv : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                            â is-embedding f
                            â (x x' : X) â is-equiv (ap f {x} {x'})

embedding-gives-ap-is-equiv {ð¤} {ð¥} {X} f e = Î³
 where
  d : (x' : X) â (Î£ x ê X , f x' â¡ f x) â (Î£ x ê X , f x â¡ f x')
  d x' = Î£-cong (Î» x â â»Â¹-â (f x') (f x))

  s : (x' : X) â is-subsingleton (Î£ x ê X , f x' â¡ f x)
  s x' = equiv-to-subsingleton (d x') (e (f x'))

  Î³ : (x x' : X) â is-equiv (ap f {x} {x'})
  Î³ x = singleton-equiv-lemma x (Î» x' â ap f {x} {x'})
         (pointed-subsingletons-are-singletons
           (Î£ x' ê X , f x â¡ f x') (x , (refl (f x))) (s x))

embedding-criterion-converse : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                             â is-embedding f
                             â ((x' x : X) â (f x' â¡ f x) â (x' â¡ x))

embedding-criterion-converse f e x' x = â-sym
                                         (ap f {x'} {x} ,
                                          embedding-gives-ap-is-equiv f e x' x)

embeddings-are-lc : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                  â is-embedding f
                  â left-cancellable f

embeddings-are-lc f e {x} {y} = â embedding-criterion-converse f e x y â

embedding-with-section-is-equiv : {X : ð¤ Ì } {Y : ð¥ Ì } (f : X â Y)
                                â is-embedding f
                                â has-section f
                                â is-equiv f
embedding-with-section-is-equiv f i (g , Î·) y = pointed-subsingletons-are-singletons
                                                 (fiber f y) (g y , Î· y) (i y)

NatÎ  : {X : ð¤ Ì } {A : X â ð¥ Ì } {B : X â ð¦ Ì } â Nat A B â Î  A â Î  B
NatÎ  Ï f x = Ï x (f x)

NatÎ -is-embedding : hfunext ð¤ ð¥
                  â hfunext ð¤ ð¦
                  â {X : ð¤ Ì } {A : X â ð¥ Ì } {B : X â ð¦ Ì }
                  â (Ï : Nat A B)
                  â ((x : X) â is-embedding (Ï x))
                  â is-embedding (NatÎ  Ï)

NatÎ -is-embedding v w {X} {A} Ï i = embedding-criterion (NatÎ  Ï) Î³
 where
  Î³ : (f g : Î  A) â (NatÎ  Ï f â¡ NatÎ  Ï g) â (f â¡ g)
  Î³ f g = (NatÎ  Ï f â¡ NatÎ  Ï g) ââ¨ hfunext-â w (NatÎ  Ï f) (NatÎ  Ï g) â©
          (NatÎ  Ï f â¼ NatÎ  Ï g) ââ¨ b â©
          (f â¼ g)               ââ¨ â-sym (hfunext-â v f g) â©
          (f â¡ g)               â 

   where
    a : (x : X) â (NatÎ  Ï f x â¡ NatÎ  Ï g x) â (f x â¡ g x)
    a x = embedding-criterion-converse (Ï x) (i x) (f x) (g x)

    b : (NatÎ  Ï f â¼ NatÎ  Ï g) â (f â¼ g)
    b = Î -cong (hfunext-gives-dfunext w) (hfunext-gives-dfunext v) a

_âª_ : ð¤ Ì â ð¥ Ì â ð¤ â ð¥ Ì
X âª Y = Î£ f ê (X â Y), is-embedding f

Embâfun : {X : ð¤ Ì } {Y : ð¥ Ì } â X âª Y â X â Y
Embâfun (f , i) = f

\end{code}
