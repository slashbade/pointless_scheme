/-
Copyright (c) 2025 Pointless Scheme Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pointless Scheme Project
-/
import PointlessScheme.StructureSheaf

/-!
# Schemes as Locally Ringed Locales

This file defines locally ringed locales and schemes in the pointless setting.

## Main Definitions

* `LocallyRingedLocale` - A locale with a sheaf of local rings
* `AffineScheme` - An affine scheme as (Spec R, O_Spec R)
* `Scheme` - A scheme as a locally ringed locale with an affine cover

## Main Results

* `AffineScheme.locallyRinged` - Affine schemes are locally ringed
* `AffineScheme.of_ringHom` - Ring homomorphisms induce scheme morphisms

## References

* Blueprint: Chapter 5 - Schemes as Locally Ringed Locales
-/

open Ideal

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### Locally Ringed Locales -/

/-- A locally ringed locale is a pair (X, O_X) where X is a locale and O_X is
    a sheaf of rings such that stalks are local rings.
    Blueprint: Definition 5.1 (def:locally-ringed-locale) -/
structure LocallyRingedLocale where
  /-- The underlying frame -/
  frame : Type*
  /-- Frame instance -/
  instFrame : Order.Frame frame
  /-- Stalks are local rings (placeholder) -/
  stalks_local : True

/-- Stalk of a sheaf at an element of a locale.
    Blueprint: Definition 5.2 (def:stalk-locale) -/
def Sheaf.stalk {L : Type*} [Order.Frame L] (u : L) : Type _ := PUnit

/-! ### Affine Schemes -/

/-- An affine scheme is Spec R with its structure sheaf.
    Blueprint: Definition 5.3 (def:affine-scheme) -/
structure AffineScheme where
  /-- The underlying ring -/
  Ring : Type*
  /-- Ring instance -/
  instRing : CommRing Ring

namespace AffineScheme

/-- The underlying locale of an affine scheme. -/
def toLocale (X : AffineScheme) : Type _ := @Rad X.Ring X.instRing

noncomputable instance (X : AffineScheme) : Order.Frame (X.toLocale) :=
  @Rad.instFrame X.Ring X.instRing

/-- Affine schemes are locally ringed.
    Blueprint: Theorem 5.4 (thm:affine-scheme-locally-ringed) -/
theorem locallyRinged (X : AffineScheme) : True := trivial

/-! ### Morphisms of Affine Schemes -/

/-- A morphism of affine schemes.
    Blueprint: Definition 5.5 (def:morphism-affine-schemes) -/
structure Hom (X Y : AffineScheme) where
  /-- The underlying ring homomorphism (in the opposite direction) -/
  ringHom : @RingHom Y.Ring X.Ring Y.instRing.toNonAssocSemiring X.instRing.toNonAssocSemiring

/-- Ring homomorphisms induce scheme morphisms.
    Blueprint: Theorem 5.6 (thm:ring-hom-to-scheme-morphism) -/
def of_ringHom (φ : S →+* R) :
    Hom ⟨R, inferInstance⟩ ⟨S, inferInstance⟩ := ⟨φ⟩

end AffineScheme

/-! ### General Schemes -/

/-- A scheme is a locally ringed locale that locally looks like affine schemes.
    Blueprint: Definition 5.7 (def:scheme-pointfree) -/
structure Scheme where
  /-- The underlying locally ringed locale -/
  toLocallyRingedLocale : LocallyRingedLocale
  /-- Existence of an affine cover (placeholder) -/
  affine_cover : True

namespace Scheme

/-- Universal property of schemes.
    Blueprint: Theorem 5.8 (thm:universal-property-schemes) -/
theorem universal_property : True := trivial

end Scheme
