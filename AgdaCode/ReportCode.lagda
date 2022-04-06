

\begin{code}[hide]

open import NaturalNumbers
open import Universes

\end{code}

\newcommand{\TypeExample}{
\AgdaNoSpaceAroundCode{}
\begin{code}

data ℤ : 𝓤₀ ̇ where
 pos      : ℕ → ℤ
 negsucc  : ℕ → ℤ

\end{code}
\AgdaSpaceAroundCode{}
}

\newcommand{\UnitType}{
\AgdaNoSpaceAroundCode{}
\begin{code}

data 𝟙 : 𝓤₀ ̇ where
 ⋆ : 𝟙

\end{code}
\AgdaSpaceAroundCode{}

}

\newcommand{\EmptyType}{
\AgdaNoSpaceAroundCode{}
\begin{code}

data 𝟘 : 𝓤₀ ̇ where

\end{code}
\AgdaSpaceAroundCode{}


}


\begin{code}
open import SpartanMLTT
\end{code}

\newcommand{\ListDef}{
\AgdaNoSpaceAroundCode{}
\begin{code}
data List (X : 𝓤 ̇) : 𝓤 ̇ where
 []    : List X
 _::_  : X → List X → List X
\end{code}
\AgdaSpaceAroundCode{}
}


\newcommand{\MapDef}{
\AgdaNoSpaceAroundCode{}
\begin{code}
map : {X Y : Type} → (X → Y) → List X → List Y
map f []        = []
map f (x :: xs) = f x :: map f xs
\end{code}
\AgdaSpaceAroundCode{}
}

\newcommand{\MapProofs}{
\AgdaNoSpaceAroundCode{}
\begin{code}
map-id-preserves-list : {X : Type} (xs : List X) → map id xs ≡ xs
map-id-preserves-list [] = refl
map-id-preserves-list (x :: xs) = ap (x ::_) (map-id-preserves-list xs)

map-composition-proof : {X Y Z : Type} (g : Y → Z) (f : X → Y) (xs : List X)
         → map (λ x → g (f x)) xs ≡ map g (map f xs)
map-composition-proof g f []        = refl
map-composition-proof g f (x :: xs) = ap (g (f x) ::_) (map-composition-proof g f xs)

\end{code}
\AgdaSpaceAroundCode{}
}








