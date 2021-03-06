This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module MGS-Choice where

open import MGS-Unique-Existence        public
open import MGS-Yoneda                  public
open import MGS-Subsingleton-Truncation public
open import MGS-Universe-Lifting        public

simple-unique-choice : (X : ð¤ Ì ) (A : X â ð¥ Ì ) (R : (x : X) â A x â ð¦ Ì )

                     â ((x : X) â â! a ê A x , R x a)
                     â Î£ f ê Î  A , ((x : X) â R x (f x))

simple-unique-choice X A R s = f , Ï
 where
  f : (x : X) â A x
  f x = prâ (center (Î£ a ê A x , R x a) (s x))

  Ï : (x : X) â R x (f x)
  Ï x = prâ (center (Î£ a ê A x , R x a) (s x))

Unique-Choice : (ð¤ ð¥ ð¦ : Universe) â (ð¤ â ð¥ â ð¦)âº Ì
Unique-Choice ð¤ ð¥ ð¦ = (X : ð¤ Ì ) (A : X â ð¥ Ì ) (R : (x : X) â A x â ð¦ Ì )
                     â ((x : X) â â! a ê A x , R x a)
                     â â! f ê Î  A , ((x : X) â R x (f x))

vvfunext-gives-unique-choice : vvfunext ð¤ (ð¥ â ð¦) â Unique-Choice ð¤ ð¥ ð¦
vvfunext-gives-unique-choice vv X A R s = c
 where
  a : ((x : X) â Î£ a ê A x , R x a)
    â (Î£ f ê ((x : X) â A x), ((x : X) â R x (f x)))

  a = Î Î£-distr-â

  b : is-singleton ((x : X) â Î£ a ê A x , R x a)
  b = vv s

  c : is-singleton (Î£ f ê ((x : X) â A x), ((x : X) â R x (f x)))
  c = equiv-to-singleton' a b

unique-choice-gives-vvfunext : Unique-Choice ð¤ ð¥ ð¥ â vvfunext ð¤ ð¥
unique-choice-gives-vvfunext {ð¤} {ð¥} uc {X} {A} Ï = Î³
 where
  R : (x : X) â A x â ð¥  Ì
  R x a = A x

  s' : (x : X) â is-singleton (A x Ã A x)
  s' x = Ã-is-singleton (Ï x) (Ï x)

  s : (x : X) â â! y ê A x , R x y
  s = s'

  e : â! f ê Î  A , ((x : X) â R x (f x))
  e = uc X A R s

  e' : is-singleton (Î  A Ã Î  A)
  e' = e

  Ï : Î  A â Î  A Ã Î  A
  Ï = prâ , (Î» y â y , y) , refl

  Î³ : is-singleton (Î  A)
  Î³ = retract-of-singleton Ï e'

unique-choice-gives-hfunext : Unique-Choice ð¤ ð¥ ð¥ â hfunext ð¤ ð¥
unique-choice-gives-hfunext {ð¤} {ð¥} uc = âhfunext Î³
 where
  Î³ : (X : ð¤ Ì ) (A : X â ð¥ Ì ) (f : Î  A) â â! g ê Î  A , f â¼ g
  Î³ X A f = uc X A R e
   where
    R : (x : X) â A x â ð¥ Ì
    R x a = f x â¡ a
    e : (x : X) â â! a ê A x , f x â¡ a
    e x = singleton-types'-are-singletons (A x) (f x)

unique-choiceâvvfunext : Unique-Choice ð¤ ð¥ ð¥ â vvfunext ð¤ ð¥
unique-choiceâvvfunext = unique-choice-gives-vvfunext ,
                         vvfunext-gives-unique-choice

module _ (hfe : global-hfunext) where

 private
   hunapply : {X : ð¤ Ì } {A : X â ð¥ Ì } {f g : Î  A} â f â¼ g â f â¡ g
   hunapply = inverse (happly _ _) (hfe _ _)

 transport-hunapply : {X : ð¤ Ì } (A : X â ð¥ Ì ) (R : (x : X) â A x â ð¦ Ì )
                      (f g : Î  A)
                      (Ï : (x : X) â R x (f x))
                      (h : f â¼ g)
                      (x : X)
                    â transport (Î» - â (x : X) â R x (- x)) (hunapply h) Ï x
                    â¡ transport (R x) (h x) (Ï x)

 transport-hunapply A R f g Ï h x =

   transport (Î» - â â x â R x (- x)) (hunapply h) Ï x â¡â¨ i â©
   transport (R x) (happly f g (hunapply h) x) (Ï x)  â¡â¨ ii â©
   transport (R x) (h x) (Ï x)                        â

  where
   a : {f g : Î  A} {Ï : â x â R x (f x)} (p : f â¡ g) (x : domain A)
     â transport (Î» - â â x â R x (- x)) p Ï x
     â¡ transport (R x) (happly f g p x) (Ï x)

   a (refl _) x = refl _

   b : happly f g (hunapply h) â¡ h
   b = inverses-are-sections (happly f g) (hfe f g) h

   i  = a (hunapply h) x
   ii = ap (Î» - â transport (R x) (- x) (Ï x)) b

 unique-choice : (X : ð¤ Ì ) (A : X â ð¥ Ì ) (R : (x : X) â A x â ð¦ Ì )

               â ((x : X) â â! a ê A x , R x a)
               â â! f ê ((x : X) â A x), ((x : X) â R x (f x))

 unique-choice X A R s = C , Î¦
  where
   fâ : (x : X) â A x
   fâ x = prâ (center (Î£ a ê A x , R x a) (s x))

   Ïâ : (x : X) â R x (fâ x)
   Ïâ x = prâ (center (Î£ a ê A x , R x a) (s x))

   C : Î£ f ê ((x : X) â A x), ((x : X) â R x (f x))
   C = fâ , Ïâ

   c : (x : X) â (Ï : Î£ a ê A x , R x a) â fâ x , Ïâ x â¡ Ï
   c x = centrality (Î£ a ê A x , R x a) (s x)

   câ : (x : X) (a : A x) (r : R x a) â fâ x â¡ a
   câ x a r = ap prâ (c x (a , r))

   câ : (x : X) (a : A x) (r : R x a)
      â transport (Î» - â R x (prâ -)) (c x (a , r)) (Ïâ x) â¡ r

   câ x a r = apd prâ (c x (a , r))

   Î¦ : (Ï : Î£ f ê ((x : X) â A x), ((x : X) â R x (f x))) â C â¡ Ï
   Î¦ (f , Ï) = to-Î£-â¡ (p , hunapply q)
    where
     p : fâ â¡ f
     p = hunapply (Î» x â câ x (f x) (Ï x))

     q : transport (Î» - â (x : X) â R x (- x)) p Ïâ â¼ Ï
     q x = transport (Î» - â (x : X) â R x (- x)) p Ïâ x           â¡â¨ i â©
           transport (R x) (ap prâ (c x (f x , Ï x))) (Ïâ x)      â¡â¨ ii â©
           transport (Î» Ï â R x (prâ Ï)) (c x (f x , Ï x)) (Ïâ x) â¡â¨ iii â©
           Ï x                                                    â
      where
       i   = transport-hunapply A R fâ f Ïâ (Î» x â câ x (f x) (Ï x)) x
       ii  = (transport-ap (R x) prâ (c x (f x , Ï x)) (Ïâ x))â»Â¹
       iii = câ x (f x) (Ï x)

module choice
        (pt  : subsingleton-truncations-exist)
        (hfe : global-hfunext)
       where

  open basic-truncation-development pt hfe public

  simple-unique-choice' : (X : ð¤ Ì ) (A : X â ð¥ Ì ) (R : (x : X) â A x â ð¦ Ì )

                        â ((x : X) â is-subsingleton (Î£ a ê A x , R x a))

                        â ((x : X) â â a ê A x , R x a)
                        â Î£ f ê Î  A , ((x : X) â R x (f x))

  simple-unique-choice' X A R u Ï = simple-unique-choice X A R s
   where
    s : (x : X) â â! a ê A x , R x a
    s x = inhabited-subsingletons-are-singletons (Î£ a ê A x , R x a) (Ï x) (u x)

  AC : â ð£ (X : ð¤ Ì ) (A : X â ð¥ Ì )
     â is-set X â ((x : X) â is-set (A x)) â ð£ âº â ð¤ â ð¥ Ì

  AC ð£ X A i j = (R : (x : X) â A x â ð£ Ì )
               â ((x : X) (a : A x) â is-subsingleton (R x a))

               â ((x : X) â â a ê A x , R x a)
               â â f ê Î  A , ((x : X) â R x (f x))

  Choice : â ð¤ â ð¤ âº Ì
  Choice ð¤ = (X : ð¤ Ì ) (A : X â ð¤ Ì ) (i : is-set X) (j : (x : X) â is-set (A x))
           â AC ð¤ X A i j

  IAC : (X : ð¤ Ì ) (Y : X â ð¥ Ì ) â is-set X â ((x : X) â is-set (Y x)) â ð¤ â ð¥ Ì
  IAC X Y i j = ((x : X) â â¥ Y x â¥) â â¥ Î  Y â¥

  IChoice : â ð¤ â ð¤ âº Ì
  IChoice ð¤ = (X : ð¤ Ì ) (Y : X â ð¤ Ì ) (i : is-set X) (j : (x : X) â is-set (Y x))
            â IAC X Y i j

  Choice-gives-IChoice : Choice ð¤ â IChoice ð¤
  Choice-gives-IChoice {ð¤} ac X Y i j Ï = Î³
   where
    R : (x : X) â Y x â ð¤ Ì
    R x y = x â¡ x -- Any singleton type in ð¤ will do.

    k : (x : X) (y : Y x) â is-subsingleton (R x y)
    k x y = i x x

    h : (x : X) â Y x â Î£ y ê Y x , R x y
    h x y = (y , refl x)

    g : (x : X) â â y ê Y x , R x y
    g x = â¥â¥-functor (h x) (Ï x)

    c : â f ê Î  Y , ((x : X) â R x (f x))
    c = ac X Y i j R k g

    Î³ : â¥ Î  Y â¥
    Î³ = â¥â¥-functor prâ c

  IChoice-gives-Choice : IChoice ð¤ â Choice ð¤
  IChoice-gives-Choice {ð¤} iac X A i j R k Ï = Î³
   where
    Y : X â ð¤ Ì
    Y x = Î£ a ê A x , R x a

    l : (x : X) â is-set (Y x)
    l x = subsets-of-sets-are-sets (A x) (R x) (j x) (k x)

    a : â¥ Î  Y â¥
    a = iac X Y i l Ï

    h : Î  Y â Î£ f ê Î  A , ((x : X) â R x (f x))
    h g = (Î» x â prâ (g x)) , (Î» x â prâ (g x))

    Î³ : â f ê Î  A , ((x : X) â R x (f x))
    Î³ = â¥â¥-functor h a

  TAC : (X : ð¤ Ì ) (A : X â ð¥ Ì ) â is-set X â ((x : X) â is-set (A x)) â ð¤ â ð¥ Ì
  TAC X A i j = â¥ ((x : X) â â¥ A x â¥ â A x)â¥

  TChoice : â ð¤ â ð¤ âº Ì
  TChoice ð¤ = (X : ð¤ Ì ) (A : X â ð¤ Ì ) (i : is-set X) (j : (x : X) â is-set (A x))
            â TAC X A i j

  IChoice-gives-TChoice : IChoice ð¤ â TChoice ð¤
  IChoice-gives-TChoice {ð¤} iac X A i j = Î³
   where
    B : (x : X) â â¥ A x â¥ â ð¤ Ì
    B x s = A x

    k : (x : X) (s : â¥ A x â¥) â is-set (B x s)
    k x s = j x

    l : (x : X) â is-set â¥ A x â¥
    l x = subsingletons-are-sets â¥ A x â¥ â¥â¥-is-subsingleton

    m : (x : X) â  is-set (â¥ A x â¥ â A x)
    m x = Î -is-set hfe (Î» s â j x)

    Ï : (x : X) â â¥ (â¥ A x â¥ â A x) â¥
    Ï x = iac â¥ A x â¥ (B x) (l x) (k x) (ðð â¥ A x â¥)

    Î³ : â¥ ((x : X) â â¥ A x â¥ â A x)â¥
    Î³ = iac X (Î» x â â¥ A x â¥ â A x) i m Ï

  TChoice-gives-IChoice : TChoice ð¤ â IChoice ð¤
  TChoice-gives-IChoice tac X A i j = Î³
   where
    Î³ : ((x : X) â â¥ A x â¥) â â¥ Î  A â¥
    Î³ g = â¥â¥-functor Ï (tac X A i j)
     where
      Ï : ((x : X) â â¥ A x â¥ â A x) â Î  A
      Ï f x = f x (g x)

  decidable-equality-criterion : {X : ð¤ Ì } (Î± : ð â X)
                               â ((x : X) â (â n ê ð , Î± n â¡ x)
                                          â (Î£ n ê ð , Î± n â¡ x))
                               â decidable (Î± â â¡ Î± â)

  decidable-equality-criterion Î± c = Î³ d
   where
    r : ð â image Î±
    r = corestriction Î±

    Ï : (y : image Î±) â Î£ n ê ð , r n â¡ y
    Ï (x , t) = f u
     where
      u : Î£ n ê ð , Î± n â¡ x
      u = c x t

      f : (Î£ n ê ð , Î± n â¡ x) â Î£ n ê ð , r n â¡ (x , t)
      f (n , p) = n , to-subtype-â¡ (Î» _ â â-is-subsingleton) p

    s : image Î± â ð
    s y = prâ (Ï y)

    Î· : (y : image Î±) â r (s y) â¡ y
    Î· y = prâ (Ï y)

    l : left-cancellable s
    l = sections-are-lc s (r , Î·)

    Î±r : {m n : ð} â Î± m â¡ Î± n â r m â¡ r n
    Î±r p = to-subtype-â¡ (Î» _ â â-is-subsingleton) p

    rÎ± : {m n : ð} â r m â¡ r n â Î± m â¡ Î± n
    rÎ± = ap prâ

    Î±s : {m n : ð} â Î± m â¡ Î± n â s (r m) â¡ s (r n)
    Î±s p = ap s (Î±r p)

    sÎ± : {m n : ð} â s (r m) â¡ s (r n) â Î± m â¡ Î± n
    sÎ± p = rÎ± (l p)

    Î³ : decidable (s (r â) â¡ s (r â)) â decidable (Î± â â¡ Î± â)
    Î³ (inl p) = inl (sÎ± p)
    Î³ (inr u) = inr (contrapositive Î±s u)

    d : decidable (s (r â) â¡ s (r â))
    d = ð-has-decidable-equality (s (r â)) (s (r â))

  choice-gives-decidable-equality : TChoice ð¤
                                  â (X : ð¤ Ì ) â is-set X â has-decidable-equality X

  choice-gives-decidable-equality {ð¤} tac X i xâ xâ = Î³
   where
    Î± : ð â X
    Î± â = xâ
    Î± â = xâ

    A : X â ð¤ Ì
    A x = Î£ n ê ð , Î± n â¡ x

    l : is-subsingleton (decidable (xâ â¡ xâ))
    l = +-is-subsingleton' hunapply (i (Î± â) (Î± â))

    Î´ : â¥ ((x : X) â â¥ A x â¥ â A x)â¥ â decidable (xâ â¡ xâ)
    Î´ = â¥â¥-recursion l (decidable-equality-criterion Î±)

    j : (x : X) â is-set (A x)
    j x = subsets-of-sets-are-sets ð (Î» n â Î± n â¡ x) ð-is-set (Î» n â i (Î± n) x)

    h : â¥ ((x : X) â â¥ A x â¥ â A x)â¥
    h = tac X A i j

    Î³ : decidable (xâ â¡ xâ)
    Î³ = Î´ h

  choice-gives-EM : propext ð¤ â TChoice (ð¤ âº) â EM ð¤
  choice-gives-EM {ð¤} pe tac = em
   where
    â¤ : Î© ð¤
    â¤ = (Lift ð¤ ð , equiv-to-subsingleton (Lift-â ð) ð-is-subsingleton)

    Î´ : (Ï : Î© ð¤) â decidable (â¤ â¡ Ï)
    Î´ = choice-gives-decidable-equality tac (Î© ð¤) (Î©-is-set hunapply pe) â¤

    em : (P : ð¤ Ì ) â is-subsingleton P â P + Â¬ P
    em P i = Î³ (Î´ (P , i))
     where
      Î³ : decidable (â¤ â¡ (P , i)) â P + Â¬ P

      Î³ (inl r) = inl (Idâfun s (lift â))
       where
        s : Lift ð¤ ð â¡ P
        s = ap prâ r

      Î³ (inr n) = inr (contrapositive f n)
       where
        f : P â â¤ â¡ P , i
        f p = Î©-ext hunapply pe (Î» (_ : Lift ð¤ ð) â p) (Î» (_ : P) â lift â)

  global-choice : (ð¤ : Universe) â ð¤ âº Ì
  global-choice ð¤ = (X : ð¤ Ì ) â X + is-empty X

  global-â¥â¥-choice : (ð¤ : Universe) â ð¤ âº Ì
  global-â¥â¥-choice ð¤ = (X : ð¤ Ì ) â â¥ X â¥ â X

  open exit-â¥â¥ pt hfe

  global-choice-gives-wconstant : global-choice ð¤
                                â (X : ð¤ Ì ) â wconstant-endomap X

  global-choice-gives-wconstant g X = decidable-has-wconstant-endomap (g X)

  global-choice-gives-global-â¥â¥-choice : global-choice  ð¤
                                       â global-â¥â¥-choice ð¤

  global-choice-gives-global-â¥â¥-choice {ð¤} c X = Î³ (c X)
   where
    Î³ : X + is-empty X â â¥ X â¥ â X
    Î³ (inl x) s = x
    Î³ (inr n) s = !ð X (â¥â¥-recursion ð-is-subsingleton n s)

  global-â¥â¥-choice-gives-all-types-are-sets : global-â¥â¥-choice ð¤
                                            â (X : ð¤ Ì ) â is-set  X

  global-â¥â¥-choice-gives-all-types-are-sets {ð¤} c X =
    types-with-wconstant-â¡-endomaps-are-sets X
        (Î» x y â â¥â¥-choice-function-gives-wconstant-endomap (c (x â¡ y)))

  global-â¥â¥-choice-gives-universe-is-set : global-â¥â¥-choice (ð¤ âº)
                                         â is-set (ð¤ Ì )

  global-â¥â¥-choice-gives-universe-is-set {ð¤} c =
    global-â¥â¥-choice-gives-all-types-are-sets c (ð¤ Ì )

  global-â¥â¥-choice-gives-choice : global-â¥â¥-choice ð¤
                                â TChoice ð¤

  global-â¥â¥-choice-gives-choice {ð¤} c X A i j = â£(Î» x â c (A x))â£

  global-â¥â¥-choice-gives-EM : propext ð¤
                           â global-â¥â¥-choice (ð¤ âº)
                           â EM  ð¤

  global-â¥â¥-choice-gives-EM {ð¤} pe c =
    choice-gives-EM pe (global-â¥â¥-choice-gives-choice c)

  global-â¥â¥-choice-gives-global-choice : propext ð¤
                                      â global-â¥â¥-choice ð¤
                                      â global-â¥â¥-choice (ð¤ âº)
                                      â global-choice ð¤

  global-â¥â¥-choice-gives-global-choice {ð¤} pe c câº X = Î³
   where
    d : decidable â¥ X â¥
    d = global-â¥â¥-choice-gives-EM pe câº â¥ X â¥ â¥â¥-is-subsingleton

    f : decidable â¥ X â¥ â X + is-empty X
    f (inl i) = inl (c X i)
    f (inr Ï) = inr (contrapositive â£_â£ Ï)

    Î³ : X + is-empty X
    Î³ = f d

  Global-Choice Global-â¥â¥-Choice : ð¤Ï
  Global-Choice    = â ð¤ â global-choice  ð¤
  Global-â¥â¥-Choice = â ð¤ â global-â¥â¥-choice ð¤

  Global-Choice-gives-Global-â¥â¥-Choice : Global-Choice â Global-â¥â¥-Choice
  Global-Choice-gives-Global-â¥â¥-Choice c ð¤ =
    global-choice-gives-global-â¥â¥-choice (c ð¤)

  Global-â¥â¥-Choice-gives-Global-Choice : global-propext
                                       â Global-â¥â¥-Choice â Global-Choice

  Global-â¥â¥-Choice-gives-Global-Choice pe c ð¤ =
    global-â¥â¥-choice-gives-global-choice pe (c ð¤) (c (ð¤ âº))

  global-â¥â¥-choice-inconsistent-with-univalence : Global-â¥â¥-Choice
                                               â Univalence
                                               â ð

  global-â¥â¥-choice-inconsistent-with-univalence g ua = Î³ (g ð¤â) (ua ð¤â)
   where
    open example-of-a-nonset

    Î³ : global-â¥â¥-choice ð¤â â is-univalent ð¤â â ð
    Î³ g ua = ð¤â-is-not-a-set ua (global-â¥â¥-choice-gives-universe-is-set g)

  global-choice-inconsistent-with-univalence : Global-Choice
                                             â Univalence
                                             â ð

  global-choice-inconsistent-with-univalence g =
    global-â¥â¥-choice-inconsistent-with-univalence
      (Global-Choice-gives-Global-â¥â¥-Choice g)

  global-choice-gives-all-types-are-sets : global-choice ð¤
                                         â (X : ð¤ Ì ) â is-set  X

  global-choice-gives-all-types-are-sets {ð¤} c X = hedberg (Î» x y â c (x â¡ y))

\end{code}
