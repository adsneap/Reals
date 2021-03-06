Martin Escardo, 2017, written in Agda November 2019.

If X is discrete then

  (X + ๐) ร Aut X โ Aut (X + ๐),

where

  Aut X := (X โ X)

is the type of automorphisms of the type X.

This is proved by Danielsson in

 http://www.cse.chalmers.se/~nad/listings/equality/Function-universe.html#[โคโโโคโ]โ[โคโรโ]

See also Coquand's

 https://github.com/simhu/cubical/blob/master/examples/finite.cub

and our

 https://www.cs.bham.ac.uk/~mhe/TypeTopology/PlusOneLC.html


More generally, for an arbitraty type X, we prove that

  co-derived-set (X + ๐) ร Aut X โ Aut (X + ๐),

where the co-derived-set of a type is the subtype of isolated points.

In particular, if X is discrete (all its points are isolated), then we
get the "factorial equivalence"

  (X + ๐) ร Aut X โ Aut (X + ๐).

On the other hand, if X is perfect (has no isolated points), then

  Aut X โ Aut (X + ๐),

This is the case, for example, if X is the circle Sยน.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

\end{code}

We need functional extensionality (but not propositional
extensionality or univalence).

\begin{code}

module UF-Factorial (fe : FunExt) where

open import SpartanMLTT
open import Plus-Properties
open import DiscreteAndSeparated
open import Swap
open import UF-Base
open import UF-Retracts
open import UF-Equiv
open import UF-Subsingletons-FunExt
open import UF-EquivalenceExamples
open import UF-Embeddings
open import UF-Subsingletons
open import UF-Equiv-FunExt
open import UF-Miscelanea

\end{code}

We refer to set of isolated points as the co derived set (for
complement of the derived set, in the sense of Cantor, consisting of
the limit points, i.e. non-isolated points).

Recall that a point x : X is isolated if the identity type x โก y is
decidable for every y : X.

\begin{code}

co-derived-set : ๐ค ฬ โ ๐ค ฬ
co-derived-set X = ฮฃ x ๊ X , is-isolated x

cods-embedding : (X : ๐ค ฬ ) โ co-derived-set X โ X
cods-embedding X = prโ

cods-embedding-is-embedding : (X : ๐ค ฬ ) โ is-embedding (cods-embedding X)
cods-embedding-is-embedding X = prโ-is-embedding (being-isolated-is-prop fe)

cods-embedding-is-equiv : (X : ๐ค ฬ ) โ is-discrete X โ is-equiv (cods-embedding X)
cods-embedding-is-equiv X d = prโ-is-equiv X is-isolated
                               (ฮป x โ pointed-props-are-singletons (d x)
                                       (being-isolated-is-prop fe x))

โ-cods : (X : ๐ค ฬ ) โ is-discrete X โ co-derived-set X โ X
โ-cods X d = cods-embedding X , cods-embedding-is-equiv X d

\end{code}

Exercise. Prove that the co derived set is a set in the sense of
univalent mathematics.

Recall that a type is perfect if it has no isolated points.

\begin{code}

perfect-coderived-empty : (X : ๐ค ฬ ) โ is-perfect X โ is-empty (co-derived-set X)
perfect-coderived-empty X i (x , j) = i (x , j)

perfect-coderived-singleton : (X : ๐ค ฬ ) โ is-perfect X โ is-singleton (co-derived-set (X + ๐ {๐ฅ}))
perfect-coderived-singleton X i = (inr โ , new-point-is-isolated) , ฮณ
 where
  ฮณ : (c : co-derived-set (X + ๐)) โ inr โ , new-point-is-isolated โก c
  ฮณ (inl x , j) = ๐-elim (i (x , a))
   where
    a : is-isolated x
    a = embeddings-reflect-isolatedness inl (inl-is-embedding X ๐) x j
  ฮณ (inr โ , j) = to-ฮฃ-โก' (being-isolated-is-prop fe (inr โ) new-point-is-isolated j)

\end{code}

For a type A, denote by A' the co-derived set of A.

Then we get a map

  (Y+๐)' ร (X โ Y) โ (X+๐ โ Y+๐),

where the choice of isolated point a:Y+๐ controls which equivalence
X+๐โY+๐ we get from the equivalence f: XโY:

       f+๐       swap (a , inr (โ))
  X+๐ ----> Y+๐ --------------------> Y+๐

The claim is that the above map is an equivalence.

We construct/prove this in four steps:

(1)  (X โ Y)
    โ ฮฃ f ๊ X + ๐ โ Y + ๐ , f (inr โ) โก inr โ

Hence

(2) (Y + ๐)' ร (X โ Y)
  โ (Y + ๐)' ร ฮฃ f ๊ X + ๐ โ Y + ๐ , f (inr โ) โก inr โ

Also

(3) (Y + ๐)' ร (ฮฃ f ๊ X + ๐ โ Y + ๐ , f (inr โ) โก inr โ)
  โ (X + ๐ โ Y + ๐)

And therefore

(4) (Y + ๐)' ร (X โ Y)
  โ (X + ๐ โ Y + ๐)

\end{code}


\begin{code}

module factorial-steps
        {๐ค ๐ฅ : Universe}
        (๐ฆ ๐ฃ : Universe)
        (X : ๐ค ฬ )
        (Y : ๐ฅ ฬ )
       where

 X+๐ = X + ๐ {๐ฆ}
 Y+๐ = Y + ๐ {๐ฃ}

\end{code}

In the following, we use the fact that if f (inr โ) โก inr โ for a
function, f : X+๐ โ Y+๐, then f (inl x) is of the form inl y
(inl-preservation).

\begin{code}

 lemma : (f : X+๐ โ Y+๐)
       โ f (inr โ) โก inr โ
       โ is-equiv f
       โ ฮฃ f' ๊ (X โ Y), is-equiv f' ร (f โผ +functor f' unique-to-๐)
 lemma f p i = ฮณ (equivs-are-qinvs f i)
  where
   ฮณ : qinv f โ ฮฃ f' ๊ (X โ Y), is-equiv f' ร (f โผ +functor f' unique-to-๐)
   ฮณ (g , ฮท , ฮต) = f' , qinvs-are-equivs f' (g' , ฮท' , ฮต') , h
    where
     f' : X โ Y
     f' x = prโ (inl-preservation f p (sections-are-lc f (g , ฮท)) x)

     a : (x : X) โ f (inl x) โก inl (f' x)
     a x = prโ (inl-preservation f p (sections-are-lc f (g , ฮท)) x)

     q = g (inr โ)     โกโจ (ap g p)โปยน โฉ
         g (f (inr โ)) โกโจ ฮท (inr โ) โฉ
         inr โ         โ

     g' : Y โ X
     g' x = prโ (inl-preservation g q (sections-are-lc g (f , ฮต)) x)

     b : (y : Y) โ g (inl y) โก inl (g' y)
     b y = prโ (inl-preservation g q (sections-are-lc g (f , ฮต)) y)

     ฮท' : g' โ f' โผ id
     ฮท' x = inl-lc (inl (g' (f' x)) โกโจ (b (f' x))โปยน โฉ
                    g (inl (f' x))  โกโจ (ap g (a x))โปยน โฉ
                    g (f (inl x))   โกโจ ฮท (inl x) โฉ
                    inl x           โ)

     ฮต' : f' โ g' โผ id
     ฮต' y = inl-lc (inl (f' (g' y)) โกโจ (a (g' y))โปยน โฉ
                    f (inl (g' y))  โกโจ (ap f (b y))โปยน โฉ
                    f (g (inl y))   โกโจ ฮต (inl y) โฉ
                    inl y           โ)

     h : f โผ +functor f' unique-to-๐
     h (inl x) = a x
     h (inr โ) = p

 stepโ : (X โ Y) โ (ฮฃ f ๊ X+๐ โ Y+๐ , โ f โ (inr โ) โก inr โ)
 stepโ = qinveq ฯ (ฮณ , ฮท , ฮต)
  where
   a : (g : X โ Y) โ qinv g โ Y+๐ โ X+๐
   a g (g' , ฮท , ฮต) = +functor g' unique-to-๐

   b : (g : X โ Y) (q : qinv g) โ a g q โ +functor g unique-to-๐ โผ id
   b g (g' , ฮท , ฮต) (inl x) = ap inl (ฮท x)
   b g (g' , ฮท , ฮต) (inr โ) = refl

   c : (g : X โ Y) (q : qinv g) โ +functor g unique-to-๐ โ a g q โผ id
   c g (g' , ฮท , ฮต) (inl y) = ap inl (ฮต y)
   c g (g' , ฮท , ฮต) (inr โ) = refl

   d : (g : X โ Y) โ qinv g โ is-equiv (+functor g unique-to-๐)
   d g q = qinvs-are-equivs (+functor g unique-to-๐) (a g q , b g q , c g q)

   ฯ : (X โ Y) โ ฮฃ e ๊ X+๐ โ Y+๐ , โ e โ (inr โ) โก inr โ
   ฯ (g , i) = (+functor g unique-to-๐ , d g (equivs-are-qinvs g i)) , refl

   ฮณ : (ฮฃ e ๊ X+๐ โ Y+๐ , โ e โ (inr โ) โก inr โ) โ (X โ Y)
   ฮณ ((f , i) , p) = prโ (lemma f p i) , prโ (prโ (lemma f p i))

   ฮท : ฮณ โ ฯ โผ id
   ฮท (g , i) = to-ฮฃ-โก (refl , being-equiv-is-prop fe g _ i)

   ฮต : ฯ โ ฮณ โผ id
   ฮต ((f , i) , p) = to-ฮฃ-โก
                      (to-subtype-โก (being-equiv-is-prop fe) r ,
                      isolated-is-h-isolated (f (inr โ))
                       (equivs-preserve-isolatedness f i (inr โ) new-point-is-isolated) _ p)
    where
     s : f โผ prโ (prโ ((ฯ โ ฮณ) ((f , i) , p)))
     s (inl x) = prโ (prโ (lemma f p i)) (inl x)
     s (inr โ) = p

     r : prโ (prโ ((ฯ โ ฮณ) ((f , i) , p))) โก f
     r = dfunext (fe _ _) (ฮป z โ (s z)โปยน)


 stepโ : co-derived-set (Y+๐) ร (X โ Y)
       โ co-derived-set (Y+๐) ร (ฮฃ e ๊ X+๐ โ Y+๐ , โ e โ (inr โ) โก inr โ)
 stepโ = ร-cong (โ-refl (co-derived-set (Y+๐))) stepโ


 stepโ : (co-derived-set (Y+๐) ร (ฮฃ e ๊ X+๐ โ Y+๐ , โ e โ (inr โ) โก inr โ))
       โ (X+๐ โ Y+๐)
 stepโ = qinveq ฯ (ฮณ , ฮท , ฮต)
  where
   A = co-derived-set (Y+๐) ร (ฮฃ e ๊ X+๐ โ Y+๐ , โ e โ (inr โ) โก inr โ)
   B = X+๐ โ Y+๐

   ฯ : A โ B
   ฯ ((t , i) , ((f , j) , p)) = g , k
    where
     g : X+๐ โ Y+๐
     g = swap t (inr โ) i new-point-is-isolated โ f

     k : is-equiv g
     k = โ-is-equiv-abstract j (swap-is-equiv t (inr โ) i new-point-is-isolated)

   ฮณ : B โ A
   ฮณ (g , k) = (t , i) , ((f , j) , p)
    where
     t : Y+๐
     t = g (inr โ)

     i : is-isolated t
     i = equivs-preserve-isolatedness g k (inr โ) new-point-is-isolated

     f : X+๐ โ Y+๐
     f = swap t (inr โ) i new-point-is-isolated โ g

     j : is-equiv f
     j = โ-is-equiv-abstract k (swap-is-equiv t (inr โ) i new-point-is-isolated)

     p : f (inr โ) โก inr โ
     p = swap-equationโ t (inr โ) i new-point-is-isolated

   ฮท : ฮณ โ ฯ โผ id
   ฮท ((t , i) , ((f , j) , p)) = s
    where
     g : X+๐ โ Y+๐
     g = swap t (inr โ) i new-point-is-isolated โ f

     k : is-equiv g
     k = โ-is-equiv-abstract j (swap-is-equiv t (inr โ) i new-point-is-isolated)

     t' : Y+๐
     t' = g (inr โ)

     i' : is-isolated t'
     i' = equivs-preserve-isolatedness g k (inr โ) new-point-is-isolated

     q : t' โก t
     q = g (inr โ)                                      โกโจ a โฉ
         swap t (inr โ) i new-point-is-isolated (inr โ) โกโจ b โฉ
         t                                              โ
      where
       a = ap (swap t (inr โ) i new-point-is-isolated) p
       b = swap-equationโ t (inr โ) i new-point-is-isolated

     r : (t' , i') โก (t , i)
     r = to-subtype-โก (being-isolated-is-prop fe) q

     f' : X+๐ โ Y+๐
     f' = swap t' (inr โ) i' new-point-is-isolated โ g

     j' : is-equiv f'
     j' = โ-is-equiv-abstract k (swap-is-equiv t' (inr โ) i' new-point-is-isolated)

     h : f' โผ f
     h z = swap t' (inr โ) i' new-point-is-isolated
            (swap t (inr โ) i new-point-is-isolated (f z))    โกโจ a โฉ

           swap t (inr โ) i new-point-is-isolated
            (swap t (inr โ) i new-point-is-isolated (f z))    โกโจ b โฉ

           f z                                                โ
      where
       ฯ : co-derived-set (Y+๐) โ Y+๐
       ฯ (t' , i') = swap t' (inr โ) i' new-point-is-isolated
                      (swap t (inr โ) i new-point-is-isolated (f z))
       a = ap ฯ r
       b = swap-involutive t (inr โ) i new-point-is-isolated (f z)

     m : is-isolated (f (inr โ))
     m = equivs-preserve-isolatedness f j (inr โ) new-point-is-isolated

     n : {t : Y+๐} โ is-prop (f (inr โ) โก t)
     n = isolated-is-h-isolated (f (inr โ)) m

     o : f' , j' โก f , j
     o = to-subtype-โก (being-equiv-is-prop fe) (dfunext (fe _ _) h)

     p' : f' (inr โ) โก inr โ
     p' = swap-equationโ t' (inr โ) i' new-point-is-isolated

     s : ((t' , i') , ((f' , j') , p')) โก ((t , i) , ((f , j) , p))
     s = to-ร-โก r (to-ฮฃ-โก (o , n top' p))
      where
       top' = transport (ฮป - โ โ - โ (inr โ) โก inr โ) o p'

   ฮต : ฯ โ ฮณ โผ id
   ฮต (g , k) = r
    where
     z : Y+๐
     z = g (inr โ)

     i : is-isolated z
     i = equivs-preserve-isolatedness g k (inr โ) new-point-is-isolated

     h : (swap (g (inr โ)) (inr โ) i new-point-is-isolated)
       โ (swap (g (inr โ)) (inr โ) i new-point-is-isolated)
       โ g
       โผ g
     h = swap-involutive z (inr โ) i new-point-is-isolated โ g

     r : ฯ (ฮณ (g , k)) โก (g , k)
     r = to-ฮฃ-โก (dfunext (fe _ _) h , being-equiv-is-prop fe g _ k)


 stepโ : co-derived-set (Y+๐) ร (X โ Y) โ (X+๐ โ Y+๐)
 stepโ = stepโ โ stepโ

\end{code}

This is the end of the submodule, which has the following corollaries:

\begin{code}

general-factorial : (X : ๐ค ฬ ) โ co-derived-set (X + ๐) ร Aut X โ Aut (X + ๐)
general-factorial {๐ค} X = factorial-steps.stepโ ๐ค ๐ค X X

discrete-factorial : (X : ๐ค ฬ )
                   โ is-discrete X
                   โ (X + ๐) ร Aut X โ Aut (X + ๐)
discrete-factorial X d = ฮณ
 where
 i = ร-cong (โ-sym (โ-cods (X + ๐) ( +-is-discrete d ๐-is-discrete))) (โ-refl (Aut X))

 ฮณ = (X + ๐) ร Aut X                โโจ i โฉ
     co-derived-set (X + ๐) ร Aut X โโจ general-factorial X โฉ
     Aut (X + ๐)                    โ?

perfect-factorial : (X : ๐ค ฬ )
                  โ is-perfect X
                  โ Aut X โ Aut (X + ๐)
perfect-factorial X i =
  Aut X                          โโจ I โฉ
  ๐ ร Aut X                      โโจ II โฉ
  co-derived-set (X + ๐) ร Aut X โโจ III โฉ
  Aut (X + ๐)                    โ?
   where
    I   =  โ-sym (๐-lneutral {universe-of X} {universe-of X})
    II  = ร-cong (โ-sym (singleton-โ-๐ (perfect-coderived-singleton X i))) (โ-refl (Aut X))
    III = general-factorial X

\end{code}

Exercise. Conclude that the map (-)+๐ : ๐ค ฬ โ ๐ค ฬ, although it is
left-cancellable, is not an embedding, but that it is an embedding
when restricted to perfect types.

We should not forget the (trivial) "base case":

\begin{code}

factorial-base : ๐ {๐ฅ} โ Aut (๐ {๐ค})
factorial-base = f , ((g , ฮท) , (g , ฮต))
 where
  f : ๐ โ Aut ๐
  f _ = id , ((id , (ฮป _ โ refl)) , (id , (ฮป _ โ refl)))

  g : Aut ๐ โ ๐
  g = unique-to-๐

  ฮท : (e : Aut ๐) โ f (g e) โก e
  ฮท _ = to-subtype-โก (being-equiv-is-prop fe) (dfunext (fe _ _) (ฮป y โ ๐-elim y))

  ฮต : (x : ๐) โ g (f x) โก x
  ฮต โ = refl

\end{code}
