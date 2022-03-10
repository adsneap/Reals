

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

\newcommand{\SigmaType}{
\AgdaNoSpaceAroundCode{}
\begin{code}

data Σ : {!{A : ?} → ?!} where
 _,_ {A} {b} : {!!} → {!!} → Σ A b

\end{code}
\AgdaSpaceAroundCode{}


}



