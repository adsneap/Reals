Martin Escardo, 23 December 2020.

We discuss how to transport well-orders along equivalences. This cannot
be done with univalence when the types live in different universes.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt

module OrdinalsWellOrderTransport (fe : FunExt) where

open import OrdinalNotions
open import OrdinalsType
open import OrdinalsWellOrderArithmetic
open import UF-Base
open import UF-Subsingletons
open import UF-Retracts
open import UF-Equiv
open import UF-Univalence

\end{code}

Univalence makes the following trivial:

\begin{code}

transport-ordinal-structure : is-univalent π€
                            β (X Y : π€ Μ )
                            β X β Y
                            β OrdinalStructure X β OrdinalStructure Y
transport-ordinal-structure ua X Y = Ξ³
 where
  Ξ΄ : X β‘ Y β OrdinalStructure X β‘ OrdinalStructure Y
  Ξ΄ = ap OrdinalStructure

  Ξ³ : X β Y β OrdinalStructure X β OrdinalStructure Y
  Ξ³ e = idtoeq (OrdinalStructure X) (OrdinalStructure Y) (Ξ΄ (eqtoid ua X Y e))

\end{code}

The above can be done without univance.

We could hope to get, more generally,

                               (X : π€ Μ ) (Y : π₯ Μ )
                             β X β Y
                             β OrdinalStructure X β OrdinalStructure Y.

But this not possible, not even assuming univalence.

The reason is that it is not possible to transport an order
_<_ : X β X β π€ to an order _βΊ_ : Y β Y β π₯ along a given equivalence
X β Y without propositional resizing, which we prefer not to assume.

However, if a particular order is resizable we can perform the
transport, although univalence won't help, which is what we do in this
file.

\begin{code}

module order-transfer-lemmaβ
         (X : π€ Μ )
         (Y : π₯ Μ )
         (π : X β Y)
       where

  private
   f : X β Y
   f = β π β

   g : Y β X
   g = inverse f (ββ-is-equiv π)

   Ξ· : g β f βΌ id
   Ξ· = inverses-are-retractions f (ββ-is-equiv π)

   Ξ΅ : f β g βΌ id
   Ξ΅ = inverses-are-sections f (ββ-is-equiv π)

\end{code}

The point is that the derived relation has values in the universe π€,
but we would need it to have values in the universe π₯. If the relation
is proposition-valued and propositional resizing holds, then this is
not a problem, but we prefer not to assume propositional resizing.

So we assume that the order relation on X already has values in π₯,
and, as it turns out, this will be enough for our intended application
of this file.

So we make one further assumption and a definition:

\begin{code}

  module _ (_<_ : X β X β π₯ Μ ) where
    private
       _βΊ_ : Y β Y β π₯ Μ
       y βΊ y' = g y < g y'

    order = _βΊ_

    order-preservationβ : (x x' : X) β x < x' β f x βΊ f x'
    order-preservationβ x x' = transportβ _<_ ((Ξ· x)β»ΒΉ) ((Ξ· x')β»ΒΉ)

    order-preservationβ : (y y' : Y) β y βΊ y' β g y < g y'
    order-preservationβ y y' = id

\end{code}

Then our objective will be to prove the following:

\begin{code}

    transport-well-order : is-well-order _<_ β is-well-order _βΊ_

\end{code}

This is easy but painful, and will need a number of routine steps.

But notice that

\begin{code}

    private

      NB-< : type-of (is-well-order _<_) β‘ π€ β π₯ Μ
      NB-< = refl

      NB-βΊ : type-of (is-well-order _βΊ_) β‘ π₯ Μ
      NB-βΊ = refl

\end{code}

So we can't assert that the types (is-well-order _<_) and
(is-well-order _βΊ_) are equal.

However, we can easily establish their equivalence:

\begin{code}

    transport-well-order-β : (is-well-order _<_) β (is-well-order _βΊ_)
    transport-well-order-β = logically-equivalent-props-are-equivalent
                               (being-well-order-is-prop (_<_) fe)
                               (being-well-order-is-prop (_βΊ_) fe)
                               (lr-implication transport-well-order)
                               (rl-implication transport-well-order)

\end{code}

And now we provide all steps needed to establish transport-well-order.

\begin{code}

    is-prop-valuedβ : is-prop-valued _<_ β is-prop-valued _βΊ_
    is-prop-valuedβ j y y' = j (g y) (g y')

    is-prop-valuedβ : is-prop-valued _βΊ_ β is-prop-valued _<_
    is-prop-valuedβ i x x' = Ξ³
     where
      Ξ΄ : is-prop (g (f x) < g (f x'))
      Ξ΄ = i (f x) (f x')

      Ξ³ : is-prop (x < x')
      Ξ³ = transportβ (Ξ» x x' β is-prop (x < x')) (Ξ· x) (Ξ· x') Ξ΄

    is-well-foundedβ : is-well-founded _<_ β is-well-founded _βΊ_
    is-well-foundedβ = retract-well-founded _<_ _βΊ_ f g Ξ΅ Ξ³
     where
      Ξ³ : (x : X) (y : Y) β y βΊ f x β g y < x
      Ξ³ x y = transport ( g y <_) (Ξ· x)

    is-well-foundedβ : is-well-founded _βΊ_ β is-well-founded _<_
    is-well-foundedβ = retract-well-founded _βΊ_ _<_ g f Ξ· Ξ³
     where
      Ξ³ : (y : Y) (x : X) β x < g y β f x βΊ y
      Ξ³ y x = transport (_< g y) ((Ξ· x)β»ΒΉ)

    is-extensionalβ : is-extensional _<_ β is-extensional _βΊ_
    is-extensionalβ e y y' Ο Ξ³ = p
     where
      Ξ± : (x : X) β x < g y β x < g y'
      Ξ± x l = transport (_< g y') (Ξ· x) a
       where
        a : g (f x) < g y'
        a = Ο (f x) (transport (_< g y) ((Ξ· x)β»ΒΉ) l)

      Ξ² : (x : X) β x < g y' β x < g y
      Ξ² x l = transport (_< g y) (Ξ· x) b
       where
        b : g (f x) < g y
        b = Ξ³ (f x) (transport (_< g y') ((Ξ· x)β»ΒΉ) l)

      q : g y β‘ g y'
      q = e (g y) (g y') Ξ± Ξ²

      p : y β‘ y'
      p = sections-are-lc g (f , Ξ΅) q

    is-extensionalβ : is-extensional _βΊ_ β is-extensional _<_
    is-extensionalβ e x x' Ο Ξ³ = p
     where
      Ξ± : (y : Y) β g y < g (f x) β g y < g (f x')
      Ξ± y l = transport (g y <_) ((Ξ· x')β»ΒΉ) a
       where
        a : g y < x'
        a = Ο (g y) (transport (g y <_) (Ξ· x) l)

      Ξ² : (y : Y) β g y < g (f x') β g y < g (f x)
      Ξ² y l = transport (g y <_) ((Ξ· x)β»ΒΉ) b
       where
        b : g y < x
        b = Ξ³ (g y) (transport (g y <_) (Ξ· x') l)

      q : f x β‘ f x'
      q = e (f x) (f x') Ξ± Ξ²

      p : x β‘ x'
      p = sections-are-lc f (g , Ξ·) q

    is-transitiveβ : is-transitive _<_ β is-transitive _βΊ_
    is-transitiveβ t x y z = t (g x) (g y) (g z)

    is-transitiveβ : is-transitive _βΊ_ β is-transitive _<_
    is-transitiveβ t x y z = Ξ³
     where
      Ξ΄ : g (f x) < g (f y) β g (f y) < g (f z) β g (f x) < g (f z)
      Ξ΄ = t (f x) (f y) (f z)

      Ξ³ : x < y β y < z β x < z
      Ξ³ = transportβ (Ξ» a b c β a < b β b < c β a < c) (Ξ· x) (Ξ· y) (Ξ· z) Ξ΄

\end{code}

Putting all this together, we get the desired result:

\begin{code}

    well-orderβ : is-well-order _<_ β is-well-order _βΊ_
    well-orderβ (p , w , e , t) = is-prop-valuedβ p ,
                                  is-well-foundedβ w ,
                                  is-extensionalβ e ,
                                  is-transitiveβ t

    well-orderβ : is-well-order _βΊ_ β is-well-order _<_
    well-orderβ (p , w , e , t) = is-prop-valuedβ p ,
                                  is-well-foundedβ w ,
                                  is-extensionalβ e ,
                                  is-transitiveβ t

    transport-well-order = well-orderβ , well-orderβ

\end{code}

So we see how much work univalence is performing behind the scenes,
when it is available, as in the construction
transport-ordinal-structure.

\begin{code}

module order-transfer-lemmaβ
         (X   : π€ Μ )
         (_<_ : X β X β π₯ Μ )
         (_βΊ_ : X β X β π¦ Μ )
         (π : (x y : X) β (x < y) β (x βΊ y))
       where

    private
      f : {x y : X} β x < y β x βΊ y
      f {x} {y} = β π x y β

      g : {x y : X} β x βΊ y β x < y
      g {x} {y} = inverse (f {x} {y}) (ββ-is-equiv (π x y))

    is-prop-valuedβ : is-prop-valued _<_ β is-prop-valued _βΊ_
    is-prop-valuedβ i x y = equiv-to-prop (β-sym (π x y)) (i x y)

    is-well-foundedβ : is-well-founded _<_ β is-well-founded _βΊ_
    is-well-foundedβ = retract-well-founded _<_ _βΊ_ id id
                        (Ξ» x β refl) (Ξ» x y β g {y} {x})

    is-extensionalβ : is-extensional _<_ β is-extensional _βΊ_
    is-extensionalβ e x y Ο Ξ³ = p
     where
      Ξ± : (u : X) β u < x β u < y
      Ξ± u l = g (Ο u (f l))

      Ξ² : (u : X) β u < y β u < x
      Ξ² u l = g (Ξ³ u (f l))

      p : x β‘ y
      p = e x y Ξ± Ξ²

    is-transitiveβ : is-transitive _<_ β is-transitive _βΊ_
    is-transitiveβ t x y z l m = f (t x y z (g l) (g m))

module order-transfer-lemmaβ
         (X   : π€ Μ )
         (_<_ : X β X β π€ Μ )
         (_βΊ_ : X β X β π₯ Μ )
         (π : (x y : X) β (x < y) β (x βΊ y))
       where

    well-orderβ : is-well-order _<_ β is-well-order _βΊ_
    well-orderβ (p , w , e , t) = is-prop-valuedβ p ,
                                  is-well-foundedβ w ,
                                  is-extensionalβ e ,
                                  is-transitiveβ t
     where
      open order-transfer-lemmaβ X _<_ _βΊ_ π

    well-orderβ : is-well-order _βΊ_ β is-well-order _<_
    well-orderβ (p , w , e , t) = is-prop-valuedβ p ,
                                  is-well-foundedβ w ,
                                  is-extensionalβ e ,
                                  is-transitiveβ t
     where
      open order-transfer-lemmaβ X _βΊ_ _<_ (Ξ» x y β β-sym (π x y))

    transport-well-order : is-well-order _<_ β is-well-order _βΊ_
    transport-well-order = well-orderβ , well-orderβ

    transport-well-order-β : (is-well-order _<_) β (is-well-order _βΊ_)
    transport-well-order-β = logically-equivalent-props-are-equivalent
                               (being-well-order-is-prop (_<_) fe)
                               (being-well-order-is-prop (_βΊ_) fe)
                               (lr-implication transport-well-order)
                               (rl-implication transport-well-order)
\end{code}

We can transport structures of ordinals with resizable order:

\begin{code}

resizable-order : Ordinal π€ β (π₯ : Universe) β π€ β (π₯ βΊ) Μ
resizable-order Ξ± π₯ = Ξ£ _<_ κ (β¨ Ξ± β© β β¨ Ξ± β© β π₯ Μ ) ,
                              ((x y : β¨ Ξ± β©) β (x βΊβ¨ Ξ± β© y) β (x < y))


transfer-structure : (X : π€ Μ ) (Ξ± : Ordinal π₯)
                   β X β β¨ Ξ± β©
                   β resizable-order Ξ± π€
                   β Ξ£ s κ OrdinalStructure X , (X , s) ββ Ξ±
transfer-structure {π€} {π₯} X Ξ± π (_<_ , <-is-equivalent-to-βΊ) = Ξ³
 where
  f : X β β¨ Ξ± β©
  f = β π β

  g : β¨ Ξ± β© β X
  g = inverse f (ββ-is-equiv π)

  Ξ΅ : f β g βΌ id
  Ξ΅ = inverses-are-sections f (ββ-is-equiv π)

  wβ» : is-well-order _<_
  wβ» = order-transfer-lemmaβ.well-orderβ β¨ Ξ± β© (underlying-order Ξ±) _<_
                               <-is-equivalent-to-βΊ (is-well-ordered Ξ±)

  _βΊ_ : X β X β π€ Μ
  x βΊ y = f x < f y

  w : is-well-order _βΊ_
  w = order-transfer-lemmaβ.well-orderβ β¨ Ξ± β© X (β-sym π) _<_ wβ»

  g-preserves-order : (a b : β¨ Ξ± β©) β a βΊβ¨ Ξ± β© b β g a βΊ g b
  g-preserves-order a b l = Ξ³
   where
    Ξ΄ : a < b
    Ξ΄ = β <-is-equivalent-to-βΊ a b β l

    Ξ³ : f (g a) < f (g b)
    Ξ³ = transportβ _<_ ((Ξ΅ a)β»ΒΉ) ((Ξ΅ b)β»ΒΉ) Ξ΄

  f-preserves-order : (x y : X) β x βΊ y β f x βΊβ¨ Ξ± β© f y
  f-preserves-order x y = β <-is-equivalent-to-βΊ (f x) (f y) ββ»ΒΉ

  e : (X , _βΊ_ , w) ββ Ξ±
  e = (f , f-preserves-order , ββ-is-equiv π , g-preserves-order)

  Ξ³ : Ξ£ s κ OrdinalStructure X , (X , s) ββ Ξ±
  Ξ³ = ((_βΊ_ , w) , e)

\end{code}
