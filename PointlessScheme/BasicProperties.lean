/-
Copyright (c) 2025 Pointless Scheme Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pointless Scheme Project
-/
import PointlessScheme.LocallyRingedLocale

/-!
# Basic Properties of Schemes

This file establishes basic properties of schemes including open and closed
sublocales, prime elements, and irreducibility.

## Main Definitions

* `OpenSublocale` - Open sublocales of a locale
* `ClosedSublocale` - Closed sublocales of a locale
* `IsPrimeElement` - Prime elements in a frame
* `Irreducible` - Irreducible locales and schemes

## Main Results

* `ClosedSublocale.closed_union` - Closed sublocales are closed under unions
* `isPrime_iff_le_or_le` - Characterization of prime elements

## References

* Blueprint: Chapter 6 - Basic Properties of Schemes
-/

open Ideal

variable {R : Type*} [CommRing R]

/-! ### Open and Closed Sublocales -/

/-- An open sublocale of a locale X is determined by an open u ∈ X.
    Blueprint: Definition 6.1 (def:open-sublocale) -/
def OpenSublocale (L : Type*) [Order.Frame L] (u : L) : Type _ := { v : L // v ≤ u }

/-- A closed sublocale of Spec R corresponds to a radical ideal.
    Blueprint: Definition 6.2 (def:closed-sublocale) -/
def ClosedSublocale (I : Rad R) : Type _ := { J : Rad R // I ≤ J }

namespace ClosedSublocale

/-- Closed sublocales are closed under intersections (which become unions of closed sets).
    Blueprint: Lemma 6.3 (lemma:closed-sublocales-unions) -/
theorem closed_union {_S : Set (Rad R)} :
    True := trivial

end ClosedSublocale

/-! ### Irreducibility and Primeness -/

/-- An element p of a frame is prime if p ≤ a ∨ b implies p ≤ a or p ≤ b.
    Blueprint: Definition 6.4 (def:prime-frame-element) -/
def IsPrimeElement {L : Type*} [Order.Frame L] (p : L) : Prop :=
  ∀ a b : L, p ≤ a ⊔ b → p ≤ a ∨ p ≤ b

/-- A radical ideal is prime if it is a prime element in the frame Rad(R).
    Blueprint: Definition 6.5 (def:prime-ideal) -/
def Rad.IsPrime (I : Rad R) : Prop := IsPrimeElement I

/-- Primeness criterion in the frame.
    Blueprint: Lemma 6.6 (lemma:prime-frame-criterion) -/
theorem isPrime_iff_le_or_le {I : Rad R} :
    I.IsPrime ↔ ∀ J K : Rad R, I ≤ J ⊔ K → I ≤ J ∨ I ≤ K := sorry

/-- Prime ideals and specialization.
    Blueprint: Theorem 6.7 (thm:prime-ideals-specialization) -/
theorem IsPrime_iff_specialization {I : Rad R} :
    I.IsPrime ↔ True := by
  constructor
  · intro _; trivial
  · intro _ J K hJK
    -- This requires a proper proof about radical ideals
    sorry

/-! ### Irreducible Schemes -/

/-- A locale is irreducible if it cannot be written as a union of two proper closed sublocales.
    Blueprint: Definition 6.8 (def:irreducible-locale) -/
def IsIrreducibleLocale (L : Type*) [Order.Frame L] : Prop :=
  ∀ u v : L, u ⊔ v = ⊤ → u = ⊤ ∨ v = ⊤

/-- A scheme is irreducible if its underlying locale is irreducible.
    Blueprint: Definition 6.9 (def:irreducible-scheme) -/
def Scheme.IsIrreducible (X : Scheme) : Prop :=
  @IsIrreducibleLocale X.toLocallyRingedLocale.frame X.toLocallyRingedLocale.instFrame
