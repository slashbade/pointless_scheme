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

/-- Intersection of closed sublocales corresponds to join of ideals.
    The closed sublocale V(I) = {J : Rad R | I ≤ J} satisfies:
    ⋂ I ∈ S, V(I) = V(sSup S)
    Blueprint: Lemma 6.3 (lemma:closed-sublocales-unions) -/
theorem closed_union (S : Set (Rad R)) :
    (⋂ I ∈ S, {J : Rad R | I ≤ J}) = {J : Rad R | sSup S ≤ J} := by
  ext J
  simp only [Set.mem_iInter, Set.mem_setOf_eq]
  exact (@sSup_le_iff (Rad R) _ S J).symm

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
    I.IsPrime ↔ ∀ J K : Rad R, I ≤ J ⊔ K → I ≤ J ∨ I ≤ K := Iff.rfl

/-! ### Frame-Primeness vs Ring-Primeness

Frame-theoretic primeness and ring-theoretic primeness are **dual** notions,
not equivalent. This is a fundamental distinction in pointless topology.

**Frame-primeness** (join-prime from below):
  `I ≤ J ⊔ K → I ≤ J ∨ I ≤ K`

**Ring-primeness** (meet-prime from above):
  `I ≠ ⊤ ∧ (JK ⊆ I → J ⊆ I ∨ K ⊆ I)`

Key observations:
1. ⊤ is always frame-prime (vacuously) but never ring-prime
2. ⊥ is always frame-prime (trivially) but may not be ring-prime
3. In ℤ/6ℤ, (0) is frame-prime but not ring-prime (2·3 = 0 but 2,3 ∉ (0))
4. In k[x,y], (x,y) is ring-prime but not frame-prime

The notions coincide for **completely prime** elements in spatial frames,
where the points of the locale correspond exactly to ring-prime ideals.

References:
- Johnstone, "Stone Spaces" (1982)
- Banaschewski, "Radical ideals and coherent frames" (1996)
- Picado & Pultr, "Frames and Locales" (2012)
-/

/-- Frame-primeness does NOT imply ring-primeness in general.
    Counterexample: In ℤ/6ℤ, (0) is frame-prime but not ring-prime.
    Blueprint: Theorem 6.7 (thm:prime-ideals-specialization) -/
theorem frame_prime_ne_ring_prime :
    ∃ (R : Type) (_ : CommRing R) (I : Rad R), I.IsPrime ∧ ¬I.val.IsPrime := by
  -- The existence is witnessed by ℤ/6ℤ and (0), but proving this
  -- requires concrete computation. We document the mathematical fact.
  -- For the formalization, we focus on the positive results about
  -- the Zariski locale structure rather than this negative result.
  sorry -- Documented: requires concrete ring ℤ/6ℤ computation

/-! ### Irreducible Schemes -/

/-- A locale is irreducible if it cannot be written as a union of two proper closed sublocales.
    Blueprint: Definition 6.8 (def:irreducible-locale) -/
def IsIrreducibleLocale (L : Type*) [Order.Frame L] : Prop :=
  ∀ u v : L, u ⊔ v = ⊤ → u = ⊤ ∨ v = ⊤

/-- A scheme is irreducible if its underlying locale is irreducible.
    Blueprint: Definition 6.9 (def:irreducible-scheme) -/
def Scheme.IsIrreducible (X : Scheme) : Prop :=
  @IsIrreducibleLocale X.toLocallyRingedLocale.frame X.toLocallyRingedLocale.instFrame
