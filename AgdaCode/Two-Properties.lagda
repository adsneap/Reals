Martin Escardo

The two-point type is defined, together with its induction principle,
in the module SpartanMLTT. Here we develop some general machinery.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Two-Properties where

open import SpartanMLTT
open import Unit-Properties
open import OrderNotation

open import UF-Subsingletons

π-Cases : {A : π€ Μ } β π β A β A β A
π-Cases a b c = π-cases b c a

π-equality-cases : {A : π€ Μ } {b : π} β (b β‘ β β A) β (b β‘ β β A) β A
π-equality-cases {π€} {A} {β} fβ fβ = fβ refl
π-equality-cases {π€} {A} {β} fβ fβ = fβ refl

π-equality-casesβ : {A : π€ Μ } {b : π} {fβ : b β‘ β β A} {fβ : b β‘ β β A}
                  β (p : b β‘ β) β π-equality-cases {π€} {A} {b} fβ fβ β‘ fβ p
π-equality-casesβ {π€} {A} {.β} refl = refl

π-equality-casesβ : {A : π€ Μ } {b : π} {fβ : b β‘ β β A} {fβ : b β‘ β β A}
                  β (p : b β‘ β) β π-equality-cases {π€} {A} {b} fβ fβ β‘ fβ p
π-equality-casesβ {π€} {A} {.β} refl = refl

π-equality-cases' : {Aβ Aβ : π€ Μ } {b : π} β (b β‘ β β Aβ) β (b β‘ β β Aβ) β Aβ + Aβ
π-equality-cases' {π€} {Aβ} {Aβ} {β} fβ fβ = inl (fβ refl)
π-equality-cases' {π€} {Aβ} {Aβ} {β} fβ fβ = inr (fβ refl)

π-possibilities : (b : π) β (b β‘ β) + (b β‘ β)
π-possibilities β = inl refl
π-possibilities β = inr refl

π-excluded-third : (b : π) β b β’ β β b β’ β β π {π€β}
π-excluded-third β u v = u refl
π-excluded-third β u v = v refl

π-things-distinct-from-a-third-are-equal : (x y z : π) β x β’ z β y β’ z β x β‘ y
π-things-distinct-from-a-third-are-equal β β z u v = refl
π-things-distinct-from-a-third-are-equal β β z u v = π-elim (π-excluded-third z (β’-sym u) (β’-sym v))
π-things-distinct-from-a-third-are-equal β β z u v = π-elim (π-excluded-third z (β’-sym v) (β’-sym u))
π-things-distinct-from-a-third-are-equal β β z u v = refl

one-is-not-zero : β β’ β
one-is-not-zero p = π-is-not-π q
 where
  f : π β π€β Μ
  f β = π
  f β = π

  q : π β‘ π
  q = ap f p

zero-is-not-one : β β’ β
zero-is-not-one p = one-is-not-zero (p β»ΒΉ)

equal-β-different-from-β : {b : π} β b β‘ β β b β’ β
equal-β-different-from-β r s = zero-is-not-one (s β»ΒΉ β r)

different-from-β-equal-β : {b : π} β b β’ β β b β‘ β
different-from-β-equal-β f = π-equality-cases (π-elim β f) (Ξ» r β r)

different-from-β-equal-β : {b : π} β b β’ β β b β‘ β
different-from-β-equal-β f = π-equality-cases (Ξ» r β r) (π-elim β f)

equal-β-different-from-β : {b : π} β b β‘ β β b β’ β
equal-β-different-from-β r s = zero-is-not-one (r β»ΒΉ β s)

[aβ‘ββbβ‘β]-gives-[bβ‘ββaβ‘β] : {a b : π} β (a β‘ β β b β‘ β) β b β‘ β β a β‘ β
[aβ‘ββbβ‘β]-gives-[bβ‘ββaβ‘β] f = different-from-β-equal-β β (contrapositive f) β equal-β-different-from-β

[aβ‘ββbβ‘β]-gives-[bβ‘ββaβ‘β] : {a b : π} β (a β‘ β β b β‘ β) β b β‘ β β a β‘ β
[aβ‘ββbβ‘β]-gives-[bβ‘ββaβ‘β] f = different-from-β-equal-β β (contrapositive f) β equal-β-different-from-β

\end{code}

π-Characteristic function of equality on π:

\begin{code}

complement : π β π
complement β = β
complement β = β

complement-no-fp : (n : π) β n β’ complement n
complement-no-fp β p = π-elim (zero-is-not-one p)
complement-no-fp β p = π-elim (one-is-not-zero p)

complement-involutive : (b : π) β complement (complement b) β‘ b
complement-involutive β = refl
complement-involutive β = refl

eqπ : π β π β π
eqπ β n = complement n
eqπ β n = n

eqπ-equal : (m n : π) β eqπ m n β‘ β β m β‘ n
eqπ-equal β n p = ap complement (p β»ΒΉ) β complement-involutive n
eqπ-equal β n p = p β»ΒΉ

equal-eqπ : (m n : π) β m β‘ n β eqπ m n β‘ β
equal-eqπ β β refl = refl
equal-eqπ β β refl = refl

\end{code}

Natural order of binary numbers:

\begin{code}

_<β_ : (a b : π) β π€β Μ
β <β β = π
β <β β = π
β <β b = π

_β€β_ : (a b : π) β π€β Μ
β β€β b = π
β β€β β = π
β β€β β = π

instance
 strict-order-π-π : Strict-Order π π
 _<_ {{strict-order-π-π}} = _<β_

 order-π-π : Order π π
 _β€_ {{order-π-π}} = _β€β_

<β-is-prop-valued : {b c : π} β is-prop (b < c)
<β-is-prop-valued {β} {β} = π-is-prop
<β-is-prop-valued {β} {β} = π-is-prop
<β-is-prop-valued {β} {c} = π-is-prop

β€β-is-prop-valued : {b c : π} β is-prop (b β€ c)
β€β-is-prop-valued {β} {c} = π-is-prop
β€β-is-prop-valued {β} {β} = π-is-prop
β€β-is-prop-valued {β} {β} = π-is-prop

<β-criterion : {a b : π} β (a β‘ β) β (b β‘ β) β a <β b
<β-criterion {β} {β} refl refl = β

<β-criterion-converse : {a b : π} β a <β b β (a β‘ β) Γ (b β‘ β)
<β-criterion-converse {β} {β} l = refl , refl

β€β-criterion : {a b : π} β (a β‘ β β b β‘ β) β a β€β b
β€β-criterion {β} {b} f = β
β€β-criterion {β} {β} f = π-elim (zero-is-not-one (f refl))
β€β-criterion {β} {β} f = β

β€β-criterion-converse : {a b : π} β a β€β b β a β‘ β β b β‘ β
β€β-criterion-converse {β} {β} l refl = refl

<β-gives-β€β : {a b : π} β a < b β a β€ b
<β-gives-β€β {β} {β} ()
<β-gives-β€β {β} {β} β = β
<β-gives-β€β {β} {c} ()

<β-trans : (a b c : π) β a < b β b < c β a < c
<β-trans β β c l m = m
<β-trans β β c l ()

Lemma[aβ‘ββb<cβa<c] : {a b c : π} β a β‘ β β b < c β a < c
Lemma[aβ‘ββb<cβa<c] {β} {β} {c} refl l = l

Lemma[a<bβcβ’ββa<c] : {a b c : π} β a < b β c β’ β β a < c
Lemma[a<bβcβ’ββa<c] {β} {β} {β} l Ξ½ = Ξ½ refl
Lemma[a<bβcβ’ββa<c] {β} {β} {β} l Ξ½ = β

β-top : {b : π} β b β€ β
β-top {β} = β
β-top {β} = β

β-bottom : {b : π} β β β€ b
β-bottom {β} = β
β-bottom {β} = β

β-maximal : {b : π} β β β€ b β b β‘ β
β-maximal {β} l = refl

β-maximal-converse : {b : π} β b β‘ β β β β€ b
β-maximal-converse {β} refl = β

β-minimal : {b : π} β b β€ β β b β‘ β
β-minimal {β} l = refl

β-minimal-converse : {b : π} β b β‘ β β b β€ β
β-minimal-converse {β} refl = β

_β€β'_ : (a b : π) β π€β Μ
a β€β' b = b β‘ β β a β‘ β

β€β-gives-β€β' : {a b : π} β a β€ b β a β€β' b
β€β-gives-β€β' {β} {b} _ p = refl
β€β-gives-β€β' {β} {β} () p
β€β-gives-β€β' {β} {β} _ p = p

β€β'-gives-β€β : {a b : π} β a β€β' b β a β€ b
β€β'-gives-β€β {β} {b} _ = β
β€β'-gives-β€β {β} {β} l = π-elim (one-is-not-zero (l refl))
β€β'-gives-β€β {β} {β} _ = β

β€β-refl : {b : π} β b β€ b
β€β-refl {β} = β
β€β-refl {β} = β

β€β-trans : (a b c : π) β a β€ b β b β€ c β a β€ c
β€β-trans β b c l m = β
β€β-trans β β β l m = β

β€β-anti : {a b : π} β a β€ b β b β€ a β a β‘ b
β€β-anti {β} {β} l m = refl
β€β-anti {β} {β} l ()
β€β-anti {β} {β} () m
β€β-anti {β} {β} l m = refl

minπ : π β π β π
minπ β b = β
minπ β b = b

minπ-preserves-β€ : {a b a' b' : π} β a β€ a' β b β€ b' β minπ a b β€ minπ a' b'
minπ-preserves-β€ {β} {b} {a'} {b'} l m = l
minπ-preserves-β€ {β} {b} {β}  {b'} l m = m

Lemma[minabβ€βa] : {a b : π} β minπ a b β€ a
Lemma[minabβ€βa] {β} {b} = β
Lemma[minabβ€βa] {β} {β} = β
Lemma[minabβ€βa] {β} {β} = β

Lemma[minabβ€βb] : {a b : π} β minπ a b β€ b
Lemma[minabβ€βb] {β} {b} = β
Lemma[minabβ€βb] {β} {β} = β
Lemma[minabβ€βb] {β} {β} = β

Lemma[minπabβ‘ββbβ‘β] : {a b : π} β minπ a b β‘ β β b β‘ β
Lemma[minπabβ‘ββbβ‘β] {β} {β} r = r
Lemma[minπabβ‘ββbβ‘β] {β} {β} r = refl
Lemma[minπabβ‘ββbβ‘β] {β} {β} r = r
Lemma[minπabβ‘ββbβ‘β] {β} {β} r = refl

Lemma[minπabβ‘ββaβ‘β] : {a b : π} β minπ a b β‘ β β a β‘ β
Lemma[minπabβ‘ββaβ‘β] {β} r = r
Lemma[minπabβ‘ββaβ‘β] {β} r = refl

Lemma[aβ‘ββbβ‘ββminπabβ‘β] : {a b : π} β a β‘ β β b β‘ β β minπ a b β‘ β
Lemma[aβ‘ββbβ‘ββminπabβ‘β] {β} {β} p q = refl

Lemma[aβ€βbβminπabβ‘a] : {a b : π} β a β€ b β minπ a b β‘ a
Lemma[aβ€βbβminπabβ‘a] {β} {b} p = refl
Lemma[aβ€βbβminπabβ‘a] {β} {β} p = refl

Lemma[minπabβ‘β] : {a b : π} β (a β‘ β) + (b β‘ β) β minπ a b β‘ β
Lemma[minπabβ‘β] {β} {b} (inl p) = refl
Lemma[minπabβ‘β] {β} {β} (inr q) = refl
Lemma[minπabβ‘β] {β} {β} (inr q) = refl

lemma[minπabβ‘β] : {a b : π} β minπ a b β‘ β β (a β‘ β) + (b β‘ β)
lemma[minπabβ‘β] {β} {b} p = inl p
lemma[minπabβ‘β] {β} {b} p = inr p

maxπ : π β π β π
maxπ β b = b
maxπ β b = β

maxπ-lemma : (a b : π) β maxπ a b β‘ β β (a β‘ β) + (b β‘ β)
maxπ-lemma β b r = inr r
maxπ-lemma β b r = inl refl

maxπ-lemma-converse : (a b : π) β (a β‘ β) + (b β‘ β) β maxπ a b β‘ β
maxπ-lemma-converse β b (inl r) = unique-from-π (zero-is-not-one r)
maxπ-lemma-converse β b (inr r) = r
maxπ-lemma-converse β b x = refl

maxπ-preserves-β€ : {a b a' b' : π} β a β€ a' β b β€ b' β maxπ a b β€ maxπ a' b'
maxπ-preserves-β€ {β} {b} {β} {b'} l m = m
maxπ-preserves-β€ {β} {β} {β} {b'} l m = m
maxπ-preserves-β€ {β} {β} {β} {b'} l m = l
maxπ-preserves-β€ {β} {b} {β} {b'} l m = l

\end{code}

Addition modulo 2:

\begin{code}

_β_ : π β π β π
β β x = x
β β x = complement x

complement-of-eqπ-is-β : (m n : π) β complement (eqπ m n) β‘ m β n
complement-of-eqπ-is-β β n = complement-involutive n
complement-of-eqπ-is-β β n = refl

Lemma[bβbβ‘β] : {b : π} β b β b β‘ β
Lemma[bβbβ‘β] {β} = refl
Lemma[bβbβ‘β] {β} = refl

Lemma[bβ‘cβbβcβ‘β] : {b c : π} β b β‘ c β b β c β‘ β
Lemma[bβ‘cβbβcβ‘β] {b} {c} r = ap (Ξ» - β b β -) (r β»ΒΉ) β (Lemma[bβbβ‘β] {b})

Lemma[bβcβ‘ββbβ‘c] : {b c : π} β b β c β‘ β β b β‘ c
Lemma[bβcβ‘ββbβ‘c] {β} {β} r = refl
Lemma[bβcβ‘ββbβ‘c] {β} {β} r = r β»ΒΉ
Lemma[bβcβ‘ββbβ‘c] {β} {β} r = r
Lemma[bβcβ‘ββbβ‘c] {β} {β} r = refl

Lemma[bβ’cβbβcβ‘β] : {b c : π} β b β’ c β b β c β‘ β
Lemma[bβ’cβbβcβ‘β] = different-from-β-equal-β β (contrapositive Lemma[bβcβ‘ββbβ‘c])

Lemma[bβcβ‘ββbβ’c] : {b c : π} β b β c β‘ β β b β’ c
Lemma[bβcβ‘ββbβ’c] = (contrapositive Lemma[bβ‘cβbβcβ‘β]) β equal-β-different-from-β

complement-left : {b c : π} β complement b β€ c β complement c β€ b
complement-left {β} {β} l = β
complement-left {β} {β} l = β
complement-left {β} {β} l = β

complement-right : {b c : π} β b β€ complement c β c β€ complement b
complement-right {β} {β} l = β
complement-right {β} {β} l = β
complement-right {β} {β} l = β

complement-both-left : {b c : π} β complement b β€ complement c β c β€ b
complement-both-left {β} {β} l = β
complement-both-left {β} {β} l = β
complement-both-left {β} {β} l = β

complement-both-right : {b c : π} β b β€ c β complement c β€ complement b
complement-both-right {β} {β} l = β
complement-both-right {β} {β} l = β
complement-both-right {β} {β} l = β

β-involutive : {a b : π} β a β a β b β‘ b
β-involutive {β} {b} = refl
β-involutive {β} {b} = complement-involutive b

β-propertyβ : {a b : π} (g : a β₯ b)
            β a β b β‘ β β (a β‘ β) Γ (b β‘ β)
β-propertyβ {β} {β} g ()
β-propertyβ {β} {β} () p
β-propertyβ {β} {β} g p = refl , refl

β-introββ : {a b : π} β a β‘ β β b β‘ β β a β b β‘ β
β-introββ {β} {β} p q = refl

β-introββ : {a b : π} β a β‘ β β b β‘ β β a β b β‘ β
β-introββ {β} {β} p q = refl

β-introββ : {a b : π} β a β‘ β β b β‘ β β a β b β‘ β
β-introββ {β} {β} p q = refl

β-introββ : {a b : π} β a β‘ β β b β‘ β β a β b β‘ β
β-introββ {β} {β} p q = refl

complement-introβ : {a : π} β a β‘ β β complement a β‘ β
complement-introβ {β} p = refl

complement-introβ : {a : π} β a β‘ β β complement a β‘ β
complement-introβ {β} p = refl

β-β-right-neutral : {a : π} β a β β β‘ a
β-β-right-neutral {β} = refl
β-β-right-neutral {β} = refl

β-β-right-neutral' : {a b : π} β b β‘ β β a β b β‘ a
β-β-right-neutral' {β} {β} p = refl
β-β-right-neutral' {β} {β} p = refl

β-left-complement : {a b : π} β b β‘ β β a β b β‘ complement a
β-left-complement {β} {β} p = refl
β-left-complement {β} {β} p = refl

β€β-add-left : (a b : π) β b β€ a β a β b β€ a
β€β-add-left β b = id
β€β-add-left β b = Ξ» _ β β-top

β€β-remove-left : (a b : π) β a β b β€ a β b β€ a
β€β-remove-left β b = id
β€β-remove-left β b = Ξ» _ β β-top

\end{code}


Fixities and precedences:

\begin{code}

infixr 31 _β_

\end{code}
