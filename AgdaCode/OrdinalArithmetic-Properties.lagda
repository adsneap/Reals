Martin Escardo, 18 January 2021.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-Univalence

module OrdinalArithmetic-Properties
       (ua : Univalence)
       where

open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-UA-FunExt
open import UF-FunExt
open import UF-EquivalenceExamples
open import UF-Embeddings
open import UF-ExcludedMiddle

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {π€} {π₯} = fe π€ π₯

 pe : PropExt
 pe = Univalence-gives-PropExt ua

open import SpartanMLTT
open import OrdinalsType
open import OrdinalNotions
open import OrdinalOfOrdinals ua
open import OrdinalArithmetic fe
open import Plus-Properties

πβ-left-neutral : (Ξ± : Ordinal π€) β πβ +β Ξ± β‘ Ξ±
πβ-left-neutral Ξ± = eqtoidβ (πβ +β Ξ±) Ξ± h
 where
  f : π + β¨ Ξ± β© β β¨ Ξ± β©
  f = β π-lneutral β

  f-preserves-order : (x y : π + β¨ Ξ± β©) β x βΊβ¨ πβ +β Ξ± β© y β f x βΊβ¨ Ξ± β© f y
  f-preserves-order (inr x) (inr y) l = l

  f-reflects-order : (x y : π + β¨ Ξ± β©) β f x βΊβ¨ Ξ± β© f y β x βΊβ¨ πβ +β Ξ± β© y
  f-reflects-order (inr x) (inr y) l = l


  h : (πβ +β Ξ±) ββ Ξ±
  h = f , order-equiv-criterion (πβ +β Ξ±) Ξ± f
           (ββ-is-equiv π-lneutral) f-preserves-order f-reflects-order

πβ-right-neutral : (Ξ± : Ordinal π€) β Ξ±  +β πβ β‘ Ξ±
πβ-right-neutral Ξ± = eqtoidβ (Ξ± +β πβ) Ξ± h
 where
  f : β¨ Ξ± β© + π β β¨ Ξ± β©
  f = β π-rneutral' β

  f-preserves-order : is-order-preserving (Ξ±  +β πβ) Ξ± f
  f-preserves-order (inl x) (inl y) l = l

  f-reflects-order : is-order-reflecting (Ξ±  +β πβ) Ξ± f
  f-reflects-order (inl x) (inl y) l = l


  h : (Ξ± +β πβ) ββ Ξ±
  h = f , order-equiv-criterion (Ξ± +β πβ) Ξ± f
           (ββ-is-equiv π-rneutral') f-preserves-order f-reflects-order

+β-assoc : (Ξ± Ξ² Ξ³ : Ordinal π€) β (Ξ±  +β Ξ²) +β Ξ³ β‘ Ξ±  +β (Ξ² +β Ξ³)
+β-assoc Ξ± Ξ² Ξ³ = eqtoidβ ((Ξ±  +β Ξ²) +β Ξ³) (Ξ±  +β (Ξ² +β Ξ³)) h
 where
  f : β¨ (Ξ± +β Ξ²) +β Ξ³ β© β β¨ Ξ± +β (Ξ² +β Ξ³) β©
  f = β +assoc β

  f-preserves-order : is-order-preserving  ((Ξ±  +β Ξ²) +β Ξ³) (Ξ±  +β (Ξ² +β Ξ³)) f
  f-preserves-order (inl (inl x)) (inl (inl y)) l = l
  f-preserves-order (inl (inl x)) (inl (inr y)) l = l
  f-preserves-order (inl (inr x)) (inl (inr y)) l = l
  f-preserves-order (inl (inl x)) (inr y)       l = l
  f-preserves-order (inl (inr x)) (inr y)       l = l
  f-preserves-order (inr x)       (inr y)       l = l


  f-reflects-order : is-order-reflecting ((Ξ±  +β Ξ²) +β Ξ³) (Ξ±  +β (Ξ² +β Ξ³)) f
  f-reflects-order (inl (inl x)) (inl (inl y)) l = l
  f-reflects-order (inl (inl x)) (inl (inr y)) l = l
  f-reflects-order (inl (inr x)) (inl (inr y)) l = l
  f-reflects-order (inl (inl x)) (inr y)       l = l
  f-reflects-order (inl (inr x)) (inr y)       l = l
  f-reflects-order (inr x)       (inl (inl y)) l = l
  f-reflects-order (inr x)       (inl (inr y)) l = l
  f-reflects-order (inr x)       (inr y)       l = l


  h : ((Ξ±  +β Ξ²) +β Ξ³) ββ (Ξ±  +β (Ξ² +β Ξ³))
  h = f , order-equiv-criterion ((Ξ±  +β Ξ²) +β Ξ³) (Ξ±  +β (Ξ² +β Ξ³)) f
           (ββ-is-equiv +assoc) f-preserves-order f-reflects-order

+β-β-left : {Ξ± Ξ² : Ordinal π€} (a : β¨ Ξ± β©)
          β (Ξ± β a) β‘ ((Ξ± +β Ξ²) β inl a)
+β-β-left {π€} {Ξ±} {Ξ²} a = h
 where
  Ξ³ = Ξ± β a
  Ξ΄ = (Ξ±  +β Ξ²) β inl a

  f : β¨ Ξ³ β© β β¨ Ξ΄ β©
  f (x , l) = inl x , l

  g :  β¨ Ξ΄ β© β β¨ Ξ³ β©
  g (inl x , l) = x , l

  Ξ· : g β f βΌ id
  Ξ· u = refl

  Ξ΅ : f β g βΌ id
  Ξ΅ (inl x , l) = refl

  f-is-equiv : is-equiv f
  f-is-equiv = qinvs-are-equivs f (g , Ξ· , Ξ΅)

  f-is-order-preserving : is-order-preserving Ξ³ Ξ΄ f
  f-is-order-preserving (x , _) (x' , _) l = l


  g-is-order-preserving : is-order-preserving Ξ΄ Ξ³ g
  g-is-order-preserving (inl x , _) (inl x' , _) l = l

  h : Ξ³ β‘ Ξ΄
  h = eqtoidβ Ξ³ Ξ΄ (f , f-is-order-preserving , f-is-equiv , g-is-order-preserving)


+β-β-right : {Ξ± Ξ² : Ordinal π€} (b : β¨ Ξ² β©)
           β (Ξ± +β (Ξ² β b)) β‘ ((Ξ± +β Ξ²) β inr b)
+β-β-right {π€} {Ξ±} {Ξ²} b = h
 where
  Ξ³ = Ξ±  +β (Ξ² β b)
  Ξ΄ = (Ξ±  +β Ξ²) β inr b

  f : β¨ Ξ³ β© β β¨ Ξ΄ β©
  f (inl a)       = inl a , β
  f (inr (y , l)) = inr y , l

  g :  β¨ Ξ΄ β© β β¨ Ξ³ β©
  g (inl a , β) = inl a
  g (inr y , l) = inr (y , l)

  Ξ· : g β f βΌ id
  Ξ· (inl a)       = refl
  Ξ· (inr (y , l)) = refl

  Ξ΅ : f β g βΌ id
  Ξ΅ (inl a , β) = refl
  Ξ΅ (inr y , l) = refl

  f-is-equiv : is-equiv f
  f-is-equiv = qinvs-are-equivs f (g , Ξ· , Ξ΅)

  f-is-order-preserving : is-order-preserving Ξ³ Ξ΄ f
  f-is-order-preserving (inl _) (inl _) l = l
  f-is-order-preserving (inl _) (inr _) l = l
  f-is-order-preserving (inr _) (inr _) l = l

  g-is-order-preserving : is-order-preserving Ξ΄ Ξ³ g
  g-is-order-preserving (inl _ , _) (inl _ , _) l = l
  g-is-order-preserving (inl _ , _) (inr _ , _) l = l
  g-is-order-preserving (inr _ , _) (inr _ , _) l = l

  h : Ξ³ β‘ Ξ΄
  h = eqtoidβ Ξ³ Ξ΄ (f , f-is-order-preserving , f-is-equiv , g-is-order-preserving)

+β-β²-left : {Ξ± Ξ² : Ordinal π€} (a : β¨ Ξ± β©)
          β (Ξ± β a) β² (Ξ± +β Ξ²)
+β-β²-left {π€} {Ξ±} {Ξ²} a = inl a , +β-β-left a

+β-β²-right : {Ξ± Ξ² : Ordinal π€} (b : β¨ Ξ² β©)
           β (Ξ± +β (Ξ² β b)) β² (Ξ± +β Ξ²)
+β-β²-right {π€} {Ξ±} {Ξ²} b = inr b , +β-β-right {π€} {Ξ±} {Ξ²} b

+β-increasing-on-right : {Ξ± Ξ² Ξ³ : Ordinal π€}
                       β Ξ² β² Ξ³
                       β (Ξ± +β Ξ²) β² (Ξ± +β Ξ³)
+β-increasing-on-right {π€} {Ξ±} {Ξ²} {Ξ³} (c , p) = inr c , q
 where
  q =  (Ξ± +β Ξ²)           β‘β¨ ap (Ξ± +β_) p β©
       (Ξ± +β (Ξ³ β c))     β‘β¨ +β-β-right c β©
       ((Ξ± +β Ξ³) β inr c) β

+β-right-monotone : (Ξ± Ξ² Ξ³ : Ordinal π€)
                  β Ξ² βΌ Ξ³
                  β (Ξ± +β Ξ²) βΌ (Ξ± +β Ξ³)
+β-right-monotone Ξ± Ξ² Ξ³ m = to-βΌ Ο
 where
  l : (a : β¨ Ξ± β©) β ((Ξ± +β Ξ²) β inl a) β²  (Ξ± +β Ξ³)
  l a = o
   where
    n : (Ξ±  β a) β² (Ξ± +β Ξ³)
    n = +β-β²-left a

    o : ((Ξ± +β Ξ²) β inl a) β²  (Ξ± +β Ξ³)
    o = transport (_β² (Ξ± +β Ξ³)) (+β-β-left a) n

  r : (b : β¨ Ξ² β©) β ((Ξ± +β Ξ²) β inr b) β² (Ξ± +β Ξ³)
  r b = s
   where
    o : (Ξ² β b) β² Ξ³
    o = from-βΌ m b

    p : (Ξ± +β (Ξ² β b)) β² (Ξ± +β Ξ³)
    p = +β-increasing-on-right o

    q : Ξ± +β (Ξ² β b) β‘ (Ξ± +β Ξ²) β inr b
    q = +β-β-right b

    s : ((Ξ± +β Ξ²) β inr b) β² (Ξ± +β Ξ³)
    s = transport (_β² (Ξ±  +β Ξ³)) q p

  Ο : (x : β¨ Ξ± +β Ξ² β©) β ((Ξ± +β Ξ²) β x) β² (Ξ± +β Ξ³)
  Ο = dep-cases l r


\end{code}

TODO. Find better names for the following lemmas.

\begin{code}

lemmaβ : {Ξ± Ξ² : Ordinal π€}
       β Ξ± βΌ (Ξ± +β Ξ²)
lemmaβ {π€} {Ξ±} {Ξ²} = to-βΌ Ο
 where
  Ο : (a : β¨ Ξ± β©) β Ξ£ z κ β¨ Ξ± +β Ξ² β© , (Ξ± β a) β‘ ((Ξ± +β Ξ²) β z)
  Ο a = inl a , (+β-β-left a)

lemmaβ : {Ξ± Ξ² : Ordinal π€}
         (a : β¨ Ξ± β©)
       β (Ξ± +β Ξ²) β’ (Ξ± β a)
lemmaβ {π€} {Ξ±} {Ξ²} a p = irrefl (OO π€) (Ξ± +β Ξ²) m
 where
  l : (Ξ± +β Ξ²) β² Ξ±
  l = (a , p)

  m : (Ξ± +β Ξ²) β² (Ξ± +β Ξ²)
  m = lemmaβ (Ξ± +β Ξ²) l

lemmaβ : {Ξ± Ξ² : Ordinal π€} (a : β¨ Ξ± β©)
       β Ξ± β‘ Ξ²
       β Ξ£ b κ β¨ Ξ² β© , (Ξ± β a) β‘ (Ξ² β b)
lemmaβ a refl = a , refl

lemmaβ : {Ξ± Ξ² Ξ³ : Ordinal π€} (b : β¨ Ξ² β©) (z : β¨ Ξ± +β Ξ³ β©)
       β ((Ξ± +β Ξ²) β inr b) β‘ ((Ξ± +β Ξ³) β z)
       β Ξ£ c κ β¨ Ξ³ β© , z β‘ inr c
lemmaβ {π€} {Ξ±} {Ξ²} {Ξ³} b (inl a) p = π-elim (lemmaβ a q)
 where
  q : (Ξ± +β (Ξ² β b)) β‘ (Ξ± β a)
  q = +β-β-right b β p β (+β-β-left a)β»ΒΉ

lemmaβ b (inr c) p = c , refl

+β-left-cancellable : (Ξ± Ξ² Ξ³ : Ordinal π€)
                    β (Ξ± +β Ξ²) β‘ (Ξ± +β Ξ³)
                    β Ξ² β‘ Ξ³
+β-left-cancellable {π€} Ξ± = g
 where
  P : Ordinal π€ β π€ βΊ Μ
  P Ξ² = β Ξ³ β (Ξ± +β Ξ²) β‘ (Ξ± +β Ξ³) β Ξ² β‘ Ξ³

  Ο : β Ξ²
    β (β b β P (Ξ² β b))
    β P Ξ²
  Ο Ξ² f Ξ³ p = Extensionality (OO π€) Ξ² Ξ³ (to-βΌ u) (to-βΌ v)
   where
    u : (b : β¨ Ξ² β©) β (Ξ² β b) β² Ξ³
    u b = c , t
     where
      z : β¨ Ξ± +β Ξ³ β©
      z = prβ (lemmaβ (inr b) p)

      r : ((Ξ± +β Ξ²) β inr b) β‘ ((Ξ± +β Ξ³) β z)
      r = prβ (lemmaβ (inr b) p)

      c : β¨ Ξ³ β©
      c = prβ (lemmaβ b z r)

      s : z β‘ inr c
      s = prβ (lemmaβ b z r)

      q = (Ξ± +β (Ξ² β b))     β‘β¨ +β-β-right b β©
          ((Ξ± +β Ξ²) β inr b) β‘β¨ r β©
          ((Ξ± +β Ξ³) β z)     β‘β¨ ap ((Ξ± +β Ξ³) β_) s β©
          ((Ξ± +β Ξ³) β inr c) β‘β¨ (+β-β-right c)β»ΒΉ β©
          (Ξ± +β (Ξ³ β c))     β

      t : (Ξ² β b) β‘ (Ξ³ β c)
      t = f b (Ξ³ β c) q

    v : (c : β¨ Ξ³ β©) β (Ξ³ β c) β² Ξ²
    v c = b , (t β»ΒΉ)
     where
      z : β¨ Ξ± +β Ξ² β©
      z = prβ (lemmaβ (inr c) (p β»ΒΉ))

      r : ((Ξ± +β Ξ³) β inr c) β‘ ((Ξ± +β Ξ²) β z)
      r = prβ (lemmaβ (inr c) (p β»ΒΉ))

      b : β¨ Ξ² β©
      b = prβ (lemmaβ c z r)

      s : z β‘ inr b
      s = prβ (lemmaβ c z r)

      q = (Ξ± +β (Ξ³ β c))     β‘β¨ +β-β-right c β©
          ((Ξ± +β Ξ³) β inr c) β‘β¨ r β©
          ((Ξ± +β Ξ²) β z)     β‘β¨ ap ((Ξ± +β Ξ²) β_) s β©
          ((Ξ± +β Ξ²) β inr b) β‘β¨ (+β-β-right b)β»ΒΉ β©
          (Ξ± +β (Ξ² β b))     β

      t : (Ξ² β b) β‘ (Ξ³ β c)
      t = f b (Ξ³ β c) (q β»ΒΉ)

  g : (Ξ² : Ordinal π€) β P Ξ²
  g = transfinite-induction-on-OO P Ο


left-+β-is-embedding : (Ξ± : Ordinal π€) β is-embedding (Ξ± +β_)
left-+β-is-embedding Ξ± = lc-maps-into-sets-are-embeddings (Ξ± +β_)
                           (Ξ» {Ξ²} {Ξ³} β +β-left-cancellable Ξ± Ξ² Ξ³)
                           the-type-of-ordinals-is-a-set

\end{code}

This implies that the function Ξ± +β_ reflects the _β²_ ordering:

\begin{code}

+β-left-reflects-β² : (Ξ± Ξ² Ξ³ : Ordinal π€)
                   β (Ξ± +β Ξ²) β² (Ξ± +β Ξ³)
                   β Ξ² β² Ξ³
+β-left-reflects-β² Ξ± Ξ² Ξ³ (inl a , p) = π-elim (lemmaβ a q)
   where
    q : (Ξ± +β Ξ²) β‘ (Ξ± β a)
    q = p β (+β-β-left a)β»ΒΉ

+β-left-reflects-β² Ξ± Ξ² Ξ³ (inr c , p) = l
   where
    q : (Ξ± +β Ξ²) β‘ (Ξ± +β (Ξ³ β c))
    q = p β (+β-β-right c)β»ΒΉ

    r : Ξ² β‘ (Ξ³ β c)
    r = +β-left-cancellable Ξ± Ξ² (Ξ³ β c) q

    l : Ξ² β² Ξ³
    l = c , r

\end{code}

And in turn this implies that the function Ξ± +β_ reflects the _βΌ_
partial ordering:

\begin{code}

+β-left-reflects-βΌ : (Ξ± Ξ² Ξ³ : Ordinal π€)
                   β (Ξ± +β Ξ²) βΌ (Ξ± +β Ξ³)
                   β Ξ² βΌ Ξ³
+β-left-reflects-βΌ {π€} Ξ± Ξ² Ξ³ l = to-βΌ (Ο Ξ² l)
 where
  Ο : (Ξ² : Ordinal π€)
    β (Ξ± +β Ξ²) βΌ (Ξ± +β Ξ³)
    β (b : β¨ Ξ² β©) β (Ξ² β b) β² Ξ³
  Ο Ξ² l b = o
   where
    m : (Ξ± +β (Ξ² β b)) β² (Ξ± +β Ξ²)
    m = +β-β²-right b

    n : (Ξ± +β (Ξ² β b)) β² (Ξ± +β Ξ³)
    n = l (Ξ± +β (Ξ² β b)) m

    o : (Ξ² β b) β² Ξ³
    o = +β-left-reflects-β² Ξ± (Ξ² β b) Ξ³ n

\end{code}

Classically, if Ξ± βΌ Ξ² then there is (a necessarily unique) Ξ³ with
Ξ± +β Ξ³ β‘ Ξ². But this not the case constructively. For that purpose, we
first consider characterize the order to subsingleton ordinals.

\begin{code}

module _ {π€ : Universe}
         (P Q : π€ Μ )
         (P-is-prop : is-prop P)
         (Q-is-prop : is-prop Q)
       where

 private
   p q : Ordinal π€
   p = prop-ordinal P P-is-prop
   q = prop-ordinal Q Q-is-prop

 factβ : p β² q β Β¬ P Γ Q
 factβ (y , r) = u , y
  where
   s : P β‘ (Q Γ π)
   s = ap β¨_β© r

   u : Β¬ P
   u p = π-elim (prβ (β idtoeq P (Q Γ π) s β p))

 factβ-converse : Β¬ P Γ Q β p β² q
 factβ-converse (u , y) = (y , g)
  where
   r : P β‘ Q Γ π
   r = univalence-gives-propext (ua π€)
        P-is-prop
        Γ-π-is-prop
        (Ξ» p β π-elim (u p))
        (Ξ» (q , z) β π-elim z)

   g : p β‘ (q β y)
   g = to-Ξ£-β‘ (r ,
       to-Ξ£-β‘ (dfunext fe' (Ξ» (y , z) β π-elim z) ,
               being-well-order-is-prop (underlying-order (q β y)) fe _ _))

 factβ : p βΌ q β (P β Q)
 factβ l x = prβ (from-βΌ {π€} {p} {q} l x)

 factβ-converse : (P β Q) β p βΌ q
 factβ-converse f = to-βΌ {π€} {p} {q} Ο
  where
   r : P Γ π β‘ Q Γ π
   r = univalence-gives-propext (ua π€)
        Γ-π-is-prop
        Γ-π-is-prop
        (Ξ» (p , z) β π-elim z)
        (Ξ» (q , z) β π-elim z)

   Ο : (x : β¨ p β©) β (p β x) β² q
   Ο x = f x , s
    where
     s : ((P Γ π) , (Ξ» x x' β π) , _) β‘ ((Q Γ π) , (Ξ» y y' β π) , _)
     s = to-Ξ£-β‘ (r ,
         to-Ξ£-β‘ (dfunext fe' (Ξ» z β π-elim (prβ z)) ,
                 being-well-order-is-prop (underlying-order (q β f x)) fe _ _))
\end{code}

The existence of ordinal subtraction implies excluded middle.

\begin{code}

existence-of-subtraction : (π€ : Universe) β π€ βΊ Μ
existence-of-subtraction π€ = (Ξ± Ξ² : Ordinal π€) β Ξ± βΌ Ξ² β Ξ£ Ξ³ κ Ordinal π€ , Ξ± +β Ξ³ β‘ Ξ²

existence-of-subtraction-is-prop : is-prop (existence-of-subtraction π€)
existence-of-subtraction-is-prop = Ξ β-is-prop (Ξ» {π€} {π₯} β fe π€ π₯)
                                     (Ξ» Ξ± Ξ² l β left-+β-is-embedding Ξ± Ξ²)


ordinal-subtraction-gives-excluded-middle : existence-of-subtraction π€ β EM π€
ordinal-subtraction-gives-excluded-middle {π€} Ο P P-is-prop = g
 where
  Ξ± = prop-ordinal P P-is-prop
  Ξ² = prop-ordinal π π-is-prop
  Ο = Ο Ξ± Ξ² (factβ-converse {π€} P π P-is-prop π-is-prop (Ξ» _ β β))
  Ξ³ : Ordinal π€
  Ξ³ = prβ Ο

  r : Ξ± +β Ξ³ β‘ Ξ²
  r = prβ Ο

  s : P + β¨ Ξ³ β© β‘ π
  s = ap β¨_β© r

  t : P + β¨ Ξ³ β©
  t = idtofun π (P + β¨ Ξ³ β©) (s β»ΒΉ) β

  f : β¨ Ξ³ β© β Β¬ P
  f c p = z
   where
    A : π€ Μ β π€ Μ
    A X = Ξ£ x κ X , Ξ£ y κ X , x β’ y

    u : A (P + β¨ Ξ³ β©)
    u = inl p , inr c , +disjoint

    v : Β¬ A π
    v (x , y , d) = d (π-is-prop x y)

    w : A (P + β¨ Ξ³ β©) β A π
    w = transport A s

    z : π
    z = v (w u)

  g : P + Β¬ P
  g = Cases t inl (Ξ» c β inr (f c))

\end{code}

Another example where subtraction doesn't exist is (ββ +β πβ) βΌ βββ,
discussed in the module . The types ββ +β πβ and βββ
are equal if and only if LPO holds. Without assuming LPO, the image of
the inclusion (ββ +β πβ) β βββ, has empty complement, and so there is
nothing that can be added to (ββ +β πβ) to get βββ, unless LPO holds.

\begin{code}

open import UF-Retracts

retract-Ξ©-of-Ordinal : retract (Ξ© π€) of (Ordinal π€)
retract-Ξ©-of-Ordinal {π€} = r , s , Ξ·
 where
  s : Ξ© π€ β Ordinal π€
  s (P , i) = prop-ordinal P i

  r : Ordinal π€ β Ξ© π€
  r Ξ± = has-bottom Ξ± , having-bottom-is-prop fe' Ξ±

  Ξ· : r β s βΌ id
  Ξ· (P , i) = to-subtype-β‘ (Ξ» _ β being-prop-is-prop fe') t
   where
    f : P β has-bottom (prop-ordinal P i)
    f p = p , (Ξ» x u β id)

    g : has-bottom (prop-ordinal P i) β P
    g (p , _) = p

    t : has-bottom (prop-ordinal P i) β‘ P
    t = pe π€ (having-bottom-is-prop fe' (prop-ordinal P i)) i g f

\end{code}
