Chuangjie Xu, 2012.

This is an Agda formalization of Theorem 8.2 of the extended version
of Escardo's paper "Infinite sets that satisfy the principle of
omniscience in all varieties of constructive mathematics", Journal of
Symbolic Logic, volume 78, number 3, September 2013, pages 764-784.

The theorem says that, for any p : ββ β π, the proposition
(n : β) β p (ΞΉ n) β‘ β is decidable where ΞΉ : β β β is the inclusion.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt

module ADecidableQuantificationOverTheNaturals (fe : funext π€β π€β) where

open import Two-Properties
open import GenericConvergentSequence
open import CompactTypes
open import GenericConvergentSequence
open import ConvergentSequenceCompact fe
open import DecidableAndDetachable
open import DiscreteAndSeparated
open import CanonicalMapNotation
open import UF-PropTrunc

Lemma-8Β·1 : (p : ββ β π) β (Ξ£ x κ ββ , (x β’ β) Γ (p x β‘ β))
                         + ((n : β) β p (ΞΉ n) β‘ β)
Lemma-8Β·1 p = cases claimβ claimβ claimβ
 where
  claimβ : (Ξ£ y κ ββ , p y β’ p (Succ y))
         β (Ξ£ x κ ββ , (x β’ β) Γ (p x β‘ β)) + ((n : β) β p (ΞΉ n) β‘ β)
  claimβ e = inl (π-equality-cases caseβ caseβ)
   where
    x : ββ
    x = prβ e

    ne : p x β’ p (Succ x)
    ne = prβ e

    caseβ : p x β‘ β β Ξ£ x κ ββ , (x β’ β) Γ (p x β‘ β)
    caseβ r = x , (s , r)
     where
      s : x β’ β
      s t = ne (ap p (t β (Succ-β-is-β fe)β»ΒΉ β (ap Succ t)β»ΒΉ))

    caseβ : p x β‘ β β Ξ£ x κ ββ , (x β’ β) Γ (p x β‘ β)
    caseβ r = (Succ x) , (s , s')
     where
      s : Succ x β’ β
      s t = ne (ap p (Succ-lc (t β (Succ-β-is-β fe)β»ΒΉ) β t β»ΒΉ))

      s' : p (Succ x) β‘ β
      s' = different-from-β-equal-β (Ξ» t β ne (r β t β»ΒΉ))

  claimβ : ((y : ββ) β p y β‘ p (Succ y)) β
            (Ξ£ x κ ββ , (x β’ β) Γ (p x β‘ β)) + ((n : β) β p (ΞΉ n) β‘ β)
  claimβ f = π-equality-cases caseβ caseβ
   where
    caseβ : p Zero β‘ β β
            (Ξ£ x κ ββ , (x β’ β) Γ (p x β‘ β)) + ((n : β) β p (ΞΉ n) β‘ β)
    caseβ r = inl (Zero , (s , r))
     where
      s : Zero β’ β
      s t = β-is-not-finite 0 (t β»ΒΉ)

    caseβ : p Zero β‘ β β
            (Ξ£ x κ ββ , (x β’ β) Γ (p x β‘ β)) + ((n : β) β p (ΞΉ n) β‘ β)
    caseβ r = inr by-induction
     where
      by-induction : (n : β) β p (ΞΉ n) β‘ β
      by-induction 0 = r
      by-induction (succ n) = (f (ΞΉ n))β»ΒΉ β by-induction n

  claimβ : (Ξ£ y κ ββ , p y β’ p (Succ y)) + ((y : ββ) β p y β‘ p (Succ y))
  claimβ = g (ββ-compact q)
   where
    fact : (y : ββ) β (p y β’ p (Succ y)) + Β¬ (p y β’ p (Succ y))
    fact y = Β¬-preserves-decidability (π-is-discrete (p y) (p (Succ y)))

    f : Ξ£ q κ (ββ β π), ((y : ββ) β (q y β‘ β β p y β’ p (Succ y))
                                  Γ (q y β‘ β β Β¬ (p y β’ p (Succ y))))
    f = characteristic-function fact

    q : ββ β π
    q = prβ f

    g : (Ξ£ y κ ββ , q y β‘ β) + ((y : ββ) β q y β‘ β)
     β (Ξ£ y κ ββ , p y β’ p (Succ y)) + ((y : ββ) β p y β‘ p (Succ y))
    g (inl (y , r)) = inl (y , (prβ (prβ f y) r))
    g (inr h ) = inr (Ξ» y β discrete-is-Β¬Β¬-separated
                             π-is-discrete
                             (p y) (p (Succ y))
                             (prβ (prβ f y) (h y)))

abstract
 Theorem-8Β·2 : (p : ββ β π) β decidable ((n : β) β p (ΞΉ n) β‘ β)
 Theorem-8Β·2 p = cases claimβ claimβ (Lemma-8Β·1 p)
  where
   claimβ : (Ξ£ x κ ββ , (x β’ β) Γ (p x β‘ β)) β
             decidable ((n : β) β p (ΞΉ n) β‘ β)
   claimβ e = inr cβ
    where
     x : ββ
     x = prβ e

     cβ : Β¬ ((n : β) β x β’ ΞΉ n)
     cβ = Ξ» g β prβ (prβ e) (not-finite-is-β fe g)

     cβ : Β¬ ((n : β) β p (ΞΉ n) β‘ β)
     cβ g = cβ d
      where
       d : (n : β) β x β’ ΞΉ n
       d n r = equal-β-different-from-β (prβ (prβ e)) (ap p r β g n)

   claimβ : ((n : β) β p (ΞΉ n) β‘ β) β decidable ((n : β) β p (ΞΉ n) β‘ β)
   claimβ f = inl f

\end{code}

Some examples:

\begin{code}

module examples where

    to-β : {A : π€ Μ } β decidable A β β
    to-β (inl _) = 0
    to-β (inr _) = 1

\end{code}

    0 means that (n : β) β p (ΞΉ n) β‘ β
    1 means that Β¬ ((n : β) β p (ΞΉ n) β‘ β)

\begin{code}

    eval : (ββ β π) β β
    eval p = to-β (Theorem-8Β·2 p)

    pβ : ββ β π
    pβ _ = β

    pβ : ββ β π
    pβ _ = β

\end{code}

    If the first boolean is less than or equal to the second
    then it has value β; otherwise, it has value β.

\begin{code}

    _<=_ : π β π β π
    β <= y = β
    β <= β = β
    β <= β = β

\end{code}

    If the two booleans are equal then it has value β;
    otherwise, it has value β.

\begin{code}

    _==_ : π β π β π
    β == β = β
    β == β = β
    β == β = β
    β == β = β

    pβ : ββ β π
    pβ (Ξ± , _) = Ξ± 10 <= Ξ± 1

    pβ : ββ β π
    pβ (Ξ± , _) = Ξ± 0 <= Ξ± 1

    pβ : ββ β π
    pβ (Ξ± , _) = Ξ± 5 == Ξ± 100

    to-something : (p : ββ β π) β decidable ((n : β) β p (ΞΉ n) β‘ β) β (p (ΞΉ 17) β‘ β) + β
    to-something p (inl f) = inl (f 17)
    to-something p (inr _) = inr 1070

    eval1 : (p : ββ β π) β (p (ΞΉ 17) β‘ β) + β
    eval1 p = to-something p (Theorem-8Β·2 p)

\end{code}

    Despite the fact that we use function extensionality, eval pi
    evaluates to a numeral for i=0,...,4.
