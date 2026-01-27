/-
Copyright (c) 2025 Pointless Scheme Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pointless Scheme Project
-/
import PointlessScheme.ZariskiLocale
import Mathlib.RingTheory.Ideal.Maps

/-!
# Functoriality and Ring Homomorphisms

This file establishes the functorial behavior of the Zariski locale construction,
showing that ring homomorphisms induce frame homomorphisms on radical ideals.

## Main Definitions

* `Rad.map` - The induced frame homomorphism from a ring homomorphism
* `Spec` - The contravariant functor from commutative rings to locales

## Main Results

* `Rad.mapFrameHom` - The induced map is a frame homomorphism
* `Rad.id_map` - Identity preservation
* `Rad.comp_map` - Composition (contravariantly)

## References

* Blueprint: Chapter 3 - Functoriality and Ring Homomorphisms
-/

open Ideal

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

namespace Rad

/-- The induced map on radical ideals from a ring homomorphism.
    Blueprint: Definition 3.2 (def:induced-frame-homomorphism) -/
def map (φ : R →+* S) (I : Rad R) : Rad S :=
  ⟨(Ideal.map φ I.1).radical, radical_isRadical _⟩

/-- Image of a radical ideal is radical (after taking radical).
    Blueprint: Lemma 3.3 (lemma:radical-image) -/
theorem map_isRadical (φ : R →+* S) (I : Rad R) : ((map φ I) : Ideal S).IsRadical :=
  (map φ I).isRadical

/-- The map preserves top.
    Blueprint: Lemma 3.4 (lemma:preserve-top) -/
theorem map_top (φ : R →+* S) : map φ ⊤ = ⊤ := sorry

/-- The map preserves finite meets.
    Blueprint: Lemma 3.5 (lemma:preserve-finite-meets) -/
theorem map_inf (φ : R →+* S) (I J : Rad R) : map φ (I ⊓ J) = map φ I ⊓ map φ J := sorry

/-- The map preserves arbitrary joins.
    Blueprint: Lemma 3.6 (lemma:preserve-arbitrary-joins) -/
theorem map_sSup (φ : R →+* S) (s : Set (Rad R)) : map φ (sSup s) = sSup (map φ '' s) := sorry

/-- φ* is a frame homomorphism.
    Blueprint: Theorem 3.7 (thm:phi-star-frame-homomorphism) -/
noncomputable def mapFrameHom (φ : R →+* S) : FrameHom (Rad R) (Rad S) where
  toFun := map φ
  map_inf' := map_inf φ
  map_top' := map_top φ
  map_sSup' := map_sSup φ

/-- Identity homomorphism induces identity on Rad.
    Blueprint: Lemma 3.8 (lemma:identity-homomorphism) -/
theorem id_map (I : Rad R) : map (RingHom.id R) I = I := sorry

/-- Composition of ring homomorphisms.
    Blueprint: Part of Theorem 3.9 (thm:functoriality-spec) -/
theorem comp_map (φ : R →+* S) (ψ : S →+* T) (I : Rad R) :
    map (ψ.comp φ) I = map ψ (map φ I) := sorry

end Rad

/-! ### The Spec Functor -/

/-- The Zariski locale functor Spec.
    Blueprint: Theorem 3.9 (thm:functoriality-spec) -/
def Spec (R : Type*) [CommRing R] := Rad R

namespace Spec

/-- Spec on ring homomorphisms (contravariant).
    Note: This goes in the opposite direction as a locale morphism. -/
def map (φ : R →+* S) : Spec S → Spec R := fun I =>
  ⟨Ideal.comap φ I.1, by
    intro x ⟨n, hn⟩
    simp only [Ideal.mem_comap, _root_.map_pow] at hn ⊢
    exact I.isRadical ⟨n, hn⟩⟩

/-- The frame homomorphism induced by a ring homomorphism goes in the forward direction. -/
noncomputable def frameMap (φ : R →+* S) : FrameHom (Rad R) (Rad S) := Rad.mapFrameHom φ

end Spec
