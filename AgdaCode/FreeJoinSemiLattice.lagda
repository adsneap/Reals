Tom de Jong, 18-24 December 2020

Formalizing a paper proof sketch from 12 November 2020.
Refactored 24 January 2022.

We construct the free join-semilattice on a set X as the Kuratowski finite
subsets of X.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

open import ArithmeticViaEquivalence
open import Fin
open import Fin-Properties
open import JoinSemiLattices

open import UF-Base
open import UF-Equiv
open import UF-FunExt
open import UF-Lower-FunExt
open import UF-ImageAndSurjection
open import UF-Powerset
open import UF-PropTrunc
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

module FreeJoinSemiLattice
        (pt : propositional-truncations-exist)
       where

open import UF-Powerset-Fin pt hiding (Îş)

open binary-union-of-subsets pt

open Kuratowski-finiteness pt

open ImageAndSurjection pt
open PropositionalTruncation pt hiding (_â¨_)

\end{code}

The proof that the Kuratowski finite subsets of X denoted by đ X and ordered by
subset inclusion is a join-semilattice (with joins given by unions) is given in
UF-Powerset-Fin.lagda.

So we proceed directly to showing that đ X is the *free* join-semilattice on a
set X. Concretely, if L is a join-semilattice and f : X â L is any function,
then there is a *unique* mediating map fâ­ : đ X â L such that:

(i)  fâ­ is a join-semilattice homomorphism, i.e.
     - fâ­ preserves the least element;
     - fâ­ preserves binary joins.
(ii) the diagram
           f
     X ---------> L
      \          ^
       \        /
      Îˇ \      / â! fâ­
         \    /
          v  /
          đ X
     commutes.

The map Îˇ : X â đ X is given by mapping x to the singleton subset â´ x âľ.

The idea in defining fâ­ is to map a Kuratowski finite subset A to the finite
join â¨âż (f â đ-to-carrier â¨ A âŠ â e) in L, where e is some eumeration
(i.e. surjection) e : Fin n â  đ â¨ A âŠ.

However, since Kuratowski finite subsets come with an *unspecified* such
enumeration, we must show that the choice of enumeration is irrelevant, i.e. any
two enumerations give rise to the same finite join. We then use a theorem by
Kraus et al. [1] (see wconstant-map-to-set-factors-through-truncation-of-domain)
to construct the desired mapping.

[1] Theorem 5.4 in
    "Notions of Anonymous Existence in Martin-LĂśf Type Theory"
    by Nicolai Kraus, MartĂ­n EscardĂł, Thierry Coquand and Thorsten Altenkirch.
    In Logical Methods in Computer Science, volume 13, issue 1.
    2017.

\begin{code}

module _
        (đ : JoinSemiLattice đĽ đŁ)
       where

 open JoinSemiLattice đ

 module _
         {X : đ¤ Ě }
         (X-is-set : is-set X)
         (f : X â L)
        where

  open singleton-subsets X-is-set
  open singleton-Kuratowski-finite-subsets X-is-set

  Îˇ : X â đ X
  Îˇ x = â´ x âľ[đ]

\end{code}

We start by defining the mapping for a specified enumeration and we show that
the choice of enumeration is irrelevant, i.e. fâ A is weakly constant.

\begin{code}
  fâ : (A : đ X)
     â (ÎŁ n ę â , ÎŁ e ę (Fin n â đ A) , is-surjection e)
     â L
  fâ A (_ , e , _) = â¨âż (f â đ-to-carrier A â e)

  fâ-is-wconstant : (A : đ X) â wconstant (fâ A)
  fâ-is-wconstant A (n , e , Ď) (n' , e' , Ď') = â-is-antisymmetric _ _ u v
   where
    f' : đ A â L
    f' = f â đ-to-carrier A
    u : â¨âż (f' â e) â â¨âż (f' â e')
    u = â¨âż-is-lowerbound-of-upperbounds (f' â e) (â¨âż (f' â e')) Ď
     where
      Ď : (k : Fin n) â (f' â e) k â â¨âż (f' â e')
      Ď k = âĽâĽ-rec (â-is-prop-valued _ _) Ď (Ď' (e k))
       where
        Ď : (ÎŁ k' ę Fin n' , e' k' âĄ e k) â (f' â e) k â â¨âż (f' â e')
        Ď (k' , p) = (f' â e) k   ââ¨ âĄ-to-â (ap f' p âťÂš)           âŠ
                     (f' â e') k' ââ¨ â¨âż-is-upperbound (f' â e') k' âŠ
                     â¨âż (f' â e') ââ
    v : â¨âż (f' â e') â â¨âż (f' â e)
    v = â¨âż-is-lowerbound-of-upperbounds (f' â e') (â¨âż (f' â e)) Ď
     where
      Ď : (k' : Fin n') â (f' â e') k' â â¨âż (f' â e)
      Ď k' = âĽâĽ-rec (â-is-prop-valued _ _) Ď (Ď (e' k'))
       where
        Ď : (ÎŁ k ę Fin n , e k âĄ e' k') â (f' â e') k' â â¨âż (f' â e)
        Ď (k , p) = (f' â e') k' ââ¨ âĄ-to-â (ap f' p âťÂš)         âŠ
                    (f' â e) k   ââ¨ â¨âż-is-upperbound (f' â e) k âŠ
                    â¨âż (f' â e)  ââ

\end{code}

We now use the theorem by Kraus et al. to construct the map fâ­ from fâ.

\begin{code}

  fâ­ : đ X â L
  fâ­ (A , Îş) =
   prâ (wconstant-map-to-set-factors-through-truncation-of-domain L-is-set
    (fâ A) (fâ-is-wconstant A)) Îş

  fâ­-in-terms-of-fâ : (A : đ X) {n : â} {e : (Fin n â đ A)} (Ď : is-surjection e)
                      (Îş : is-Kuratowski-finite-subset A)
                    â fâ­ (A , Îş) âĄ fâ A (n , e , Ď)
  fâ­-in-terms-of-fâ A {n} {e} Ď Îş = fâ­ (A , Îş)             âĄâ¨ I  âŠ
                                    fâ­ (A , âŁ n , e , Ď âŁ) âĄâ¨ II âŠ
                                    fâ A (n , e , Ď)       â
   where
    I  = ap (Îť - â fâ­ (A , -)) (âĽâĽ-is-prop Îş âŁ n , e , Ď âŁ)
    II = (prâ (wconstant-map-to-set-factors-through-truncation-of-domain
                L-is-set
                (fâ A) (fâ-is-wconstant A))
          (n , e , Ď)) âťÂš

\end{code}

Recall that we must show that
(i)  fâ­ is a join-semilattice homomorphism, i.e.
     - fâ­ preserves the least element;
     - fâ­ preserves binary joins.
(ii) the diagram
           f
     X ---------> L
      \          ^
       \        /
      Îˇ \      / â! fâ­
         \    /
          v  /
          đ X
     commutes.

We show (ii) and then (i) now.

\begin{code}

  fâ­-after-Îˇ-is-f : fâ­ â Îˇ âź f
  fâ­-after-Îˇ-is-f x = fâ­ (Îˇ x)             âĄâ¨ I  âŠ
                      fâ â´ x âľ (1 , e , Ď) âĄâ¨ II âŠ
                      f x                  â
   where
    e : Fin 1 â đ â´ x âľ
    e đ = x , refl
    Ď : is-surjection e
    Ď (x , refl) = âŁ đ , refl âŁ
    I = fâ­-in-terms-of-fâ â´ x âľ Ď â¨ Îˇ x âŠâ
    II = â-is-antisymmetric _ _
          (â¨-is-lowerbound-of-upperbounds _ _ _
           (âĽ-is-least (f x)) (â-is-reflexive (f x)))
          (â¨-is-upperboundâ _ _)

  fâ­-preserves-âĽ : fâ­ â[đ] âĄ âĽ
  fâ­-preserves-âĽ = â-is-antisymmetric _ _ u v
   where
    u : fâ­ â[đ] â âĽ
    u = fâ­ â[đ]                     ââ¨ uâ âŠ
        â¨âż (f â đ-to-carrier â â e) ââ¨ uâ âŠ
        âĽ                           ââ
     where
      e : Fin 0 â đ {đ¤} {X} â
      e = đ-elim
      Ď : is-surjection e
      Ď (x , x-in-emptyset) = đ-elim x-in-emptyset
      uâ = âĄ-to-â (fâ­-in-terms-of-fâ â Ď â-is-Kuratowski-finite-subset)
      uâ = â-is-reflexive âĽ
    v : âĽ â fâ­ â[đ]
    v = âĽ-is-least (fâ­ â[đ])

  fâ­-is-monotone : (A B : đ X)
                â ((x : X) â x â â¨ A âŠ â x â â¨ B âŠ)
                â fâ­ A â fâ­ B
  fâ­-is-monotone đ¸@(A , Îşâ) đš@(B , Îşâ) s =
   âĽâĽ-recâ (â-is-prop-valued (fâ­ đ¸) (fâ­ đš)) Îł Îşâ Îşâ
    where
     Îł : (ÎŁ n ę â , Fin n â  đ A)
       â (ÎŁ m ę â , Fin m â  đ B)
       â fâ­ (A , Îşâ) â fâ­ (B , Îşâ)
     Îł (n , e , e-surj) (n' , e' , e'-surj) =
      fâ­ đ¸                         ââ¨ uâ âŠ
      â¨âż (f â đ-to-carrier A â e)  ââ¨ uâ âŠ
      â¨âż (f â đ-to-carrier B â e') ââ¨ uâ âŠ
      fâ­ đš                         ââ
       where
        uâ = âĄ-to-â (fâ­-in-terms-of-fâ A e-surj Îşâ)
        uâ = âĄ-to-â ((fâ­-in-terms-of-fâ B e'-surj Îşâ) âťÂš)
        uâ = â¨âż-is-lowerbound-of-upperbounds (f â đ-to-carrier A â e)
                                             (â¨âż (f â đ-to-carrier B â e')) Îłâ
         where
          Îłâ : (k : Fin n) â (f â đ-to-carrier A â e) k
                           â â¨âż (f â đ-to-carrier B â e')
          Îłâ k = âĽâĽ-rec (â-is-prop-valued _ _) Îłâ t
           where
            x : X
            x = đ-to-carrier A (e k)
            a : x â A
            a = đ-to-membership A (e k)
            b : x â B
            b = s x a
            t : â k' ę Fin n' , e' k' âĄ (x , b)
            t = e'-surj (x , b)
            Îłâ : (ÎŁ k' ę Fin n' , e' k' âĄ (x , b))
               â (f â prâ â e) k â â¨âż (f â prâ â e')
            Îłâ (k' , p) = (f â đ-to-carrier A) (e k)   ââ¨ vâ âŠ
                          (f â đ-to-carrier B) (e' k') ââ¨ vâ âŠ
                          â¨âż (f â đ-to-carrier B â e') ââ
             where
              vâ = âĄ-to-â (ap f q)
               where
                q : đ-to-carrier A (e k) âĄ đ-to-carrier B (e' k')
                q = ap prâ (p âťÂš)
              vâ = â¨âż-is-upperbound (f â đ-to-carrier B â e') k'

  fâ­-preserves-â¨ : (A B : đ X) â fâ­ (A âŞ[đ] B) âĄ fâ­ A â¨ fâ­ B
  fâ­-preserves-â¨ A B = â-is-antisymmetric _ _ u v
   where
    v : (fâ­ A â¨ fâ­ B) â fâ­ (A âŞ[đ] B)
    v = â¨-is-lowerbound-of-upperbounds _ _ _
        (fâ­-is-monotone A (A âŞ[đ] B) (âŞ[đ]-is-upperboundâ A B))
        (fâ­-is-monotone B (A âŞ[đ] B) (âŞ[đ]-is-upperboundâ A B))
    u : fâ­ (A âŞ[đ] B) â (fâ­ A â¨ fâ­ B)
    u = âĽâĽ-rec (â-is-prop-valued (fâ­ (A âŞ[đ] B)) (fâ­ A â¨ fâ­ B)) Îłâ (â¨ A âŠâ)
     where
      Îłâ : (ÎŁ n ę â , ÎŁ e ę (Fin n â đ â¨ A âŠ) , is-surjection e)
         â fâ­ (A âŞ[đ] B) â (fâ­ A â¨ fâ­ B)
      Îłâ (n , e , Ď) = âĽâĽ-rec (â-is-prop-valued _ _) Îłâ (â¨ B âŠâ)
       where
        Îłâ : (ÎŁ n' ę â , ÎŁ e' ę (Fin n' â đ â¨ B âŠ) , is-surjection e')
           â fâ­ (A âŞ[đ] B) â (fâ­ A â¨ fâ­ B)
        Îłâ (n' , e' , Ď') = fâ­ (A âŞ[đ] B)    ââ¨ lâ âŠ
                            â¨âż (f' â [e,e']) ââ¨ lâ âŠ
                            fâ­ A â¨ fâ­ B      ââ
         where
          f' : đ (â¨ A âŠ âŞ â¨ B âŠ) â L
          f' = f â đ-to-carrier (â¨ A âŠ âŞ â¨ B âŠ)
          [e,e'] : Fin (n +' n') â đ (â¨ A âŠ âŞ â¨ B âŠ)
          [e,e'] = (âŞ-enum â¨ A âŠ â¨ B âŠ e e')
          Ď : is-surjection [e,e']
          Ď = âŞ-enum-is-surjection â¨ A âŠ â¨ B âŠ e e' Ď Ď'
          lâ = âĄ-to-â p
           where
            p : fâ­ (A âŞ[đ] B) âĄ fâ (â¨ A âŠ âŞ â¨ B âŠ) (n +' n' , [e,e'] , Ď)
            p = fâ­-in-terms-of-fâ (â¨ A âŠ âŞ â¨ B âŠ) Ď â¨ A âŞ[đ] B âŠâ
          lâ = â¨âż-is-lowerbound-of-upperbounds (f' â [e,e']) (fâ­ A â¨ fâ­ B) Ď
           where
            Ď : (k : Fin (n +' n'))
              â (f' â [e,e']) k â (fâ­ A â¨ fâ­ B)
            Ď k = (f' â [e,e']) k                   ââ¨ â-is-reflexive _ âŠ
                  (f' â âŞ-enum' â¨ A âŠ â¨ B âŠ e e') c ââ¨ Ď c âŠ
                  (fâ­ A â¨ fâ­ B)                     ââ
             where
              c : Fin n + Fin n'
              c = â Fin+homo n n' â k
              Ď : (c : Fin n + Fin n')
                â (f' â âŞ-enum' â¨ A âŠ â¨ B âŠ e e') c â (fâ­ A â¨ fâ­ B)
              Ď (inl k) = (f' â âŞ-enum' â¨ A âŠ â¨ B âŠ e e') (inl k) ââ¨ uâ âŠ
                          (f â đ-to-carrier â¨ A âŠ â e) k          ââ¨ uâ âŠ
                          â¨âż (f â đ-to-carrier â¨ A âŠ â e)         ââ¨ uâ âŠ
                          fâ â¨ A âŠ (n , e , Ď)                    ââ¨ uâ âŠ
                          fâ­ A                                    ââ¨ uâ âŠ
                          fâ­ A â¨ fâ­ B                             ââ
               where
                uâ = â-is-reflexive ((f â đ-to-carrier â¨ A âŠ â e) k)
                uâ = â¨âż-is-upperbound (f â đ-to-carrier â¨ A âŠ â e) k
                uâ = â-is-reflexive (â¨âż (f â đ-to-carrier â¨ A âŠ â e))
                uâ = âĄ-to-â ((fâ­-in-terms-of-fâ â¨ A âŠ Ď â¨ A âŠâ) âťÂš)
                uâ = â¨-is-upperboundâ (fâ­ A) (fâ­ B)
              Ď (inr k) = (f' â âŞ-enum' â¨ A âŠ â¨ B âŠ e e') (inr k) ââ¨ uâ' âŠ
                          (f â đ-to-carrier â¨ B âŠ â e') k         ââ¨ uâ' âŠ
                          â¨âż (f â đ-to-carrier â¨ B âŠ â e')        ââ¨ uâ' âŠ
                          fâ â¨ B âŠ (n' , e' , Ď')                 ââ¨ uâ' âŠ
                          fâ­ B                                    ââ¨ uâ' âŠ
                          fâ­ A â¨ fâ­ B                             ââ
               where
                uâ' = â-is-reflexive ((f â đ-to-carrier â¨ B âŠ â e') k)
                uâ' = â¨âż-is-upperbound (f â đ-to-carrier â¨ B âŠ â e') k
                uâ' = â-is-reflexive (â¨âż (f â đ-to-carrier â¨ B âŠ â e'))
                uâ' = âĄ-to-â ((fâ­-in-terms-of-fâ â¨ B âŠ Ď' â¨ B âŠâ) âťÂš)
                uâ' = â¨-is-upperboundâ (fâ­ A) (fâ­ B)

\end{code}

Finally we prove that fâ­ is the unique map with the above properties (i) & (ii).
We do so by using the induction principle for Kuratowski finite subsets, which
is proved in UF-Powerset-Fin.lagda.

\begin{code}

  module _
          (pe : propext đ¤)
          (fe : funext đ¤ (đ¤ âş))
         where

   fâ­-is-unique : (h : đ X â L)
                â h â[đ] âĄ âĽ
                â ((A B : đ X) â h (A âŞ[đ] B) âĄ h A â¨ h B)
                â (h â Îˇ âź f)
                â h âź fâ­
   fâ­-is-unique h pâ pâ pâ = Kuratowski-finite-subset-induction pe fe
                             X X-is-set
                             (Îť A â h A âĄ fâ­ A)
                             (Îť _ â L-is-set)
                             qâ qâ qâ
    where
     qâ : h â[đ] âĄ fâ­ â[đ]
     qâ = h â[đ]  âĄâ¨ pâ                âŠ
          âĽ       âĄâ¨ fâ­-preserves-âĽ âťÂš âŠ
          fâ­ â[đ] â
     qâ : (x : X) â h (Îˇ x) âĄ fâ­ (Îˇ x)
     qâ x = h (Îˇ x)  âĄâ¨ pâ x                   âŠ
            f x      âĄâ¨ (fâ­-after-Îˇ-is-f x) âťÂš âŠ
            fâ­ (Îˇ x) â
     qâ : (A B : đ X)
        â h A âĄ fâ­ A
        â h B âĄ fâ­ B
        â h (A âŞ[đ] B) âĄ fâ­ (A âŞ[đ] B)
     qâ A B râ râ = h (A âŞ[đ] B)  âĄâ¨ pâ A B                  âŠ
                    h A â¨ h B     âĄâ¨ apâ _â¨_ râ râ           âŠ
                    fâ­ A â¨ fâ­ B   âĄâ¨ (fâ­-preserves-â¨ A B) âťÂš âŠ
                    fâ­ (A âŞ[đ] B) â

\end{code}

Assuming some more function extensionality axioms, we can prove "homotopy
uniqueness", i.e. the tuple consisting of fâ­ together with the proofs of (i) and
(ii) is unique. This follows easily from the above, because (i) and (ii) are
subsingletons (as L is a set).

\begin{code}

  module _
          (pe : propext đ¤)
          (fe : funext (đ¤ âş) (đ¤ âş â đĽ))
         where

   homotopy-uniqueness-of-fâ­ :
    â! h ę (đ X â L) , (h â[đ] âĄ âĽ)
                     Ă ((A B : đ X) â h (A âŞ[đ] B) âĄ h A â¨ h B)
                     Ă h â Îˇ âź f
   homotopy-uniqueness-of-fâ­ =
    (fâ­ , fâ­-preserves-âĽ , fâ­-preserves-â¨ , fâ­-after-Îˇ-is-f) , Îł
     where
      Îł : (t : (ÎŁ h ę (đ X â L) , (h â[đ] âĄ âĽ)
                                Ă ((A B : đ X) â h (A âŞ[đ] B) âĄ h A â¨ h B)
                                Ă h â Îˇ âź f))
        â (fâ­ , fâ­-preserves-âĽ , fâ­-preserves-â¨ , fâ­-after-Îˇ-is-f) âĄ t
      Îł (h , pâ , pâ , pâ) = to-subtype-âĄ Ď
                             (dfunext (lower-funext (đ¤ âş) (đ¤ âş) fe)
                               (Îť A â (fâ­-is-unique
                                         pe
                                         (lower-funext (đ¤ âş) đĽ fe)
                                         h pâ pâ pâ A) âťÂš))
       where
        Ď : (k : đ X â L)
          â is-prop ((k â[đ] âĄ âĽ)
                    Ă ((A B : đ X) â k (A âŞ[đ] B) âĄ (k A â¨ k B))
                    Ă k â Îˇ âź f)
        Ď k = Ă-is-prop L-is-set (Ă-is-prop
                                   (Î -is-prop fe
                                     (Îť _ â Î -is-prop (lower-funext (đ¤ âş) (đ¤ âş) fe)
                                     (Îť _ â L-is-set)))
                                   (Î -is-prop (lower-funext (đ¤ âş) (đ¤ âş) fe)
                                     (Îť _ â L-is-set)))

\end{code}

Added 17th March 2021 by Martin Escardo. Alternative definition of đ:

\begin{code}

open import UF-Embeddings

đ' : đ¤ Ě â đ¤ âş Ě
đ' {đ¤} X = ÎŁ A ę đ¤ Ě , (A âŞ X) Ă is-Kuratowski-finite A

\end{code}

TODO. Show that đ' X is equivalent to đ X (using UF-Classifiers).

Tom de Jong, 27 August 2021. We implement this TODO.

\begin{code}

open import UF-Univalence

module _
        (ua : Univalence)
       where

 open import UF-Classifiers hiding (đ)
 open import UF-EquivalenceExamples

 đ-is-equivalent-to-đ' : (X : đ¤ Ě ) â  đ X â đ' X
 đ-is-equivalent-to-đ' {đ¤} X = Îł
  where
   Ď : Subtypes X â đ X
   Ď = ÎŠ-is-subtype-classifier ua X
   Îş : đ¤ Ě â đ¤ Ě
   Îş = is-Kuratowski-finite
   Îł = đ X                                                ââ¨ â-refl _ âŠ
       (ÎŁ A ę đ X , Îş (đ A))                              ââ¨ I        âŠ
       (ÎŁ S ę Subtypes X , Îş (đ (â Ď â S)))               ââ¨ ÎŁ-assoc  âŠ
       (ÎŁ A ę đ¤ Ě , ÎŁ e ę (A âŞ X) , Îş (đ (â Ď â (A , e)))) ââ¨ II       âŠ
       (ÎŁ A ę đ¤ Ě , ÎŁ e ę (A âŞ X) , Îş A)                   ââ¨ â-refl _ âŠ
       (ÎŁ A ę đ¤ Ě , (A âŞ X) Ă Îş A)                         ââ¨ â-refl _ âŠ
       đ' X                                               â 
    where
     I  = â-sym (ÎŁ-change-of-variable (Îť A â is-Kuratowski-finite-subset A)
                   â Ď â (ââ-is-equiv Ď))
     II = ÎŁ-cong (Îť A â ÎŁ-cong (Îť e â Ď A e))
      where
       Ď : (A : đ¤ Ě ) (e : A âŞ X)
         â Îş (đ (â Ď â (A , e))) â Îş A
       Ď A e = idtoeq (Îş A') (Îş A)
                (ap Îş (eqtoid (ua đ¤) A' A lemma))
        where
         A' : đ¤ Ě
         A' = đ (â Ď â (A , e))
         lemma = A'                                   ââ¨ â-refl _ âŠ
                 (ÎŁ x ę X , ÎŁ a ę A , etofun e a âĄ x) ââ¨ Ď        âŠ
                 A                                    â 
          where
           Ď = total-fiber-is-domain (etofun e)

\end{code}
