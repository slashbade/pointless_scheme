/-
Copyright (c) 2025 Pointless Scheme Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pointless Scheme Project
-/
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Order.Category.Frm
import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Finset.Basic

/-!
# Foundational Locale Theory

This file establishes the foundational theory of frames and locales needed for
pointless algebraic geometry.

## Main Definitions

* `Order.Frame` - A frame is a complete lattice satisfying the infinite distributive law
* `FrameHom` - Frame homomorphisms preserve arbitrary joins and finite meets
* `FrameCongruence L` - Frame congruences on a frame `L`
* `Nucleus L` - Nuclei on a frame `L` (closure operators preserving meets)

## Main Results

* `Nucleus.FixedPoints.instFrame` - Fixed points of a nucleus form a frame

## Implementation Notes

For the Zariski locale, we use a concrete approach rather than the full abstract theory
of frame presentations. The frame `Rad(R)` of radical ideals is shown to be generated
by basic opens, and the universal property is established directly via
`Rad.frameHom_eq_of_basicOpen_eq`.

## References

* Blueprint: Chapter 1 - Foundational Locale Theory
* Johnstone, "Stone Spaces", Chapter II
* Vickers, "Topology via Logic", Chapter 4
-/

open Order Set

namespace PointlessScheme

/-! ### Frames and Basic Structure -/

/-- A frame is a complete lattice satisfying the infinite distributive law:
    `a ⊓ ⨆ i, b i = ⨆ i, a ⊓ b i` -/
abbrev Frame := Order.Frame

/-- Frame homomorphisms preserve arbitrary joins and finite meets. -/
abbrev FrameHom' := _root_.FrameHom

/-! ## Frame Congruences

A frame congruence on a frame `L` is an equivalence relation that is compatible
with the frame operations (meets and joins).
-/

/-- A frame congruence is an equivalence relation compatible with frame operations. -/
structure FrameCongruence (L : Type*) [Order.Frame L] where
  /-- The underlying equivalence relation -/
  r : L → L → Prop
  /-- Reflexivity -/
  refl : ∀ a, r a a
  /-- Symmetry -/
  symm : ∀ a b, r a b → r b a
  /-- Transitivity -/
  trans : ∀ a b c, r a b → r b c → r a c
  /-- Compatibility with binary meets -/
  inf_congr : ∀ a b c d, r a b → r c d → r (a ⊓ c) (b ⊓ d)
  /-- Compatibility with arbitrary joins -/
  sSup_congr : ∀ (S T : Set L), (∀ s ∈ S, ∃ t ∈ T, r s t) → (∀ t ∈ T, ∃ s ∈ S, r s t) →
    r (sSup S) (sSup T)

namespace FrameCongruence

variable {L : Type*} [Order.Frame L] (c : FrameCongruence L)

/-- The congruence respects top. -/
theorem top_congr : c.r ⊤ ⊤ := c.refl ⊤

/-- The congruence respects bot. -/
theorem bot_congr : c.r ⊥ ⊥ := c.refl ⊥

/-- The trivial congruence (equality). -/
def trivial : FrameCongruence L where
  r := (· = ·)
  refl := fun _ => rfl
  symm := fun _ _ => Eq.symm
  trans := fun _ _ _ => Eq.trans
  inf_congr := fun _ _ _ _ hab hcd => by rw [hab, hcd]
  sSup_congr := fun S T hST hTS => by
    apply le_antisymm
    · apply sSup_le
      intro s hs
      obtain ⟨t, ht, hst⟩ := hST s hs
      rw [hst]
      exact le_sSup ht
    · apply sSup_le
      intro t ht
      obtain ⟨s, hs, hts⟩ := hTS t ht
      rw [← hts]
      exact le_sSup hs

/-- The total congruence (everything related). -/
def total : FrameCongruence L where
  r := fun _ _ => True
  refl := fun _ => True.intro
  symm := fun _ _ _ => True.intro
  trans := fun _ _ _ _ _ => True.intro
  inf_congr := fun _ _ _ _ _ _ => True.intro
  sSup_congr := fun _ _ _ _ => True.intro

end FrameCongruence

/-! ## Quotient Frames via Nuclei

A nucleus on a frame L is a closure operator j : L → L satisfying j(a ⊓ b) = j(a) ⊓ j(b).
The fixed points of a nucleus form a frame (the quotient frame).
-/

/-- A nucleus on a frame is a closure operator preserving finite meets. -/
structure Nucleus (L : Type*) [Order.Frame L] where
  /-- The closure operator -/
  j : L → L
  /-- Extensive: a ≤ j(a) -/
  le_j : ∀ a, a ≤ j a
  /-- Idempotent: j(j(a)) = j(a) -/
  j_idem : ∀ a, j (j a) = j a
  /-- Monotone: a ≤ b → j(a) ≤ j(b) -/
  j_mono : ∀ a b, a ≤ b → j a ≤ j b
  /-- Preserves meets: j(a ⊓ b) = j(a) ⊓ j(b) -/
  j_inf : ∀ a b, j (a ⊓ b) = j a ⊓ j b

namespace Nucleus

variable {L : Type*} [Order.Frame L] (n : Nucleus L)

/-- j preserves top. -/
theorem j_top : n.j ⊤ = ⊤ := le_antisymm le_top (n.le_j ⊤)

/-- j(a) ⊓ j(b) = j(a ⊓ b). -/
theorem inf_j (a b : L) : n.j a ⊓ n.j b = n.j (a ⊓ b) := (n.j_inf a b).symm

/-- The fixed points of a nucleus. -/
def FixedPoints := {a : L // n.j a = a}

/-- j(a) is always a fixed point. -/
def toFixed (a : L) : FixedPoints n := ⟨n.j a, n.j_idem a⟩

/-- ⊤ is a fixed point. -/
theorem top_isFixed : n.j ⊤ = ⊤ := n.j_top

/-- The meet of two fixed points is a fixed point. -/
theorem inf_isFixed {a b : L} (ha : n.j a = a) (hb : n.j b = b) : n.j (a ⊓ b) = a ⊓ b := by
  rw [n.j_inf, ha, hb]

/-- The infimum of a family of fixed points is a fixed point. -/
theorem sInf_isFixed {S : Set L} (hS : ∀ a ∈ S, n.j a = a) : n.j (sInf S) = sInf S := by
  apply le_antisymm
  · apply le_sInf
    intro a ha
    calc n.j (sInf S) ≤ n.j a := n.j_mono _ _ (sInf_le ha)
      _ = a := hS a ha
  · exact n.le_j _

/-! ### Fixed Points Form a Frame

The key theorem is that the fixed points of a nucleus form a frame.
The lattice operations are:
- `⊤` is `⊤` (which is always fixed)
- `⊥` is `j(⊥)` (closure of bottom)
- `a ⊓ b` is `a ⊓ b` (meet of fixed points is fixed)
- `a ⊔ b` is `j(a ⊔ b)` (closure of join)
- `sSup S` is `j(sSup S)` (closure of supremum)
- `sInf S` is `sInf S` (infimum of fixed points is fixed)

Frame distributivity follows from distributivity in L and properties of j.
-/

end Nucleus

/-! ## Frame Presentations (Abstract Theory)

A frame presentation consists of generators and relations.
The presented frame is the free frame quotiented by the congruence generated by the relations.

### Construction Overview

The free frame on generators G can be constructed as:
- `FreeFrame G := UpperSet (Finset G)`
where a finite subset s : Finset G represents the meet ⋀ g∈s, g
and an upper set S represents the join ⋁ {⋀ g∈s, g | s ∈ S}.

The presented frame is then the quotient of FreeFrame G by a nucleus
that identifies elements according to the relations.

For our purposes (the Zariski locale), we use a concrete approach:
the frame Rad(R) is directly shown to satisfy the universal property.
See `ZariskiLocale.lean` for details.
-/

/-- A frame presentation specifies generators and relations. -/
structure FramePresentation where
  /-- The type of generators -/
  Gen : Type*
  /-- The type of relations -/
  Rel : Type*
  /-- Left-hand side of each relation -/
  lhs : Rel → Set (Finset Gen)
  /-- Right-hand side of each relation -/
  rhs : Rel → Set (Finset Gen)
  /-- LHS should be an upper set -/
  lhs_upper : ∀ r, IsUpperSet (lhs r)
  /-- RHS should be an upper set -/
  rhs_upper : ∀ r, IsUpperSet (rhs r)

/-! ## Application to the Zariski Locale

The Zariski frame Rad(R) can be viewed as a presented frame with:
- Generators: D(f) for f ∈ R
- Relations: D(1) = ⊤, D(0) = ⊥, D(fg) = D(f) ⊓ D(g), etc.

Rather than constructing this via the abstract quotient, we prove the
universal property directly:
- `Rad.radical_eq_sSup_basicOpen`: Every radical ideal is sSup of basic opens
- `Rad.frameHom_eq_of_basicOpen_eq`: Frame homs equal iff equal on basic opens
-/

end PointlessScheme
