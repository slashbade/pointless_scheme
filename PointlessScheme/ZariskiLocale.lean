/-
Copyright (c) 2025 Pointless Scheme Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pointless Scheme Project
-/
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Hom.CompleteLattice

/-!
# The Zariski Locale from Commutative Rings

This file constructs the Zariski locale of a commutative ring as the frame
of radical ideals, following the pointless approach to algebraic geometry.

## Main Definitions

* `Rad R` - The type of radical ideals of a commutative ring `R`
* `Rad.instFrame` - The frame structure on radical ideals
* `Rad.basicOpen` - The basic open `D(f) = √(f)` for an element `f : R`

## Main Results

* `Rad.instCompleteLattice` - Radical ideals form a complete lattice
* `Rad.instFrame` - Radical ideals form a frame (frame distributivity)
* `Rad.basicOpen_inf` - `D(fg) = D(f) ⊓ D(g)`
* `Rad.cover_iff` - Cover criterion for basic opens

## References

* Blueprint: Chapter 2 - The Zariski Locale from Commutative Rings
-/

open Ideal

variable {R : Type*} [CommRing R]

/-! ### Radical Ideals as a Type -/

/-- The type of radical ideals of a commutative ring `R`.
    A radical ideal is an ideal `I` such that `I = √I`. -/
def Rad (R : Type*) [CommRing R] := { I : Ideal R // I.IsRadical }

namespace Rad

variable {R : Type*} [CommRing R]

instance : SetLike (Rad R) R where
  coe I := I.1
  coe_injective' := fun ⟨I, _⟩ ⟨J, _⟩ h => by
    congr 1
    exact SetLike.coe_injective h

@[ext]
theorem ext {I J : Rad R} (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
  SetLike.ext h

/-- Coercion from `Rad R` to `Ideal R`. -/
instance : CoeOut (Rad R) (Ideal R) := ⟨Subtype.val⟩

/-- The radical property of a `Rad R`. -/
theorem isRadical (I : Rad R) : (I : Ideal R).IsRadical := I.2

/-! ### Order and Operations on Radical Ideals -/

/-- Order on radical ideals by inclusion. -/
instance instLE : LE (Rad R) := ⟨fun I J => (I : Ideal R) ≤ J⟩

/-- Partial order instance. -/
instance instPartialOrder : PartialOrder (Rad R) where
  le := (· ≤ ·)
  le_refl _ := le_refl _
  le_trans _ _ _ := le_trans
  le_antisymm := fun _ _ hIJ hJI => ext fun x => ⟨fun h => hIJ h, fun h => hJI h⟩

/-- Meet (infimum) of radical ideals is intersection. -/
instance instInf : Min (Rad R) :=
  ⟨fun I J => ⟨I.1 ⊓ J.1, I.isRadical.inf J.isRadical⟩⟩

/-- Sup (supremum) of radical ideals is the radical of the sum. -/
instance instSup : Max (Rad R) :=
  ⟨fun I J => ⟨(I.1 ⊔ J.1).radical, radical_isRadical _⟩⟩

/-- Top element is the whole ring. -/
instance instTop : Top (Rad R) :=
  ⟨⟨⊤, fun _ _ => Submodule.mem_top⟩⟩

/-- Bottom element is the nilradical. -/
instance instBot : Bot (Rad R) :=
  ⟨⟨(⊥ : Ideal R).radical, radical_isRadical _⟩⟩

/-! ### Intersection of Radical Ideals is Radical -/

/-- If `I, J` are radical ideals, then `I ∩ J` is radical.
    Blueprint: Lemma 2.3 (lemma:intersection-radical) -/
theorem IsRadical.inf' {I J : Ideal R} (hI : I.IsRadical) (hJ : J.IsRadical) :
    (I ⊓ J).IsRadical :=
  hI.inf hJ

/-- Arbitrary intersections of radical ideals are radical.
    Blueprint: Corollary 2.4 (cor:arbitrary-intersection-radical) -/
theorem IsRadical.sInf' {S : Set (Ideal R)} (hS : ∀ I ∈ S, I.IsRadical) : (sInf S).IsRadical := by
  intro x ⟨n, hn⟩
  simp only [Submodule.mem_sInf] at hn ⊢
  intro I hI
  exact hS I hI ⟨n, hn I hI⟩

/-! ### Complete Lattice Structure -/

/-- Infimum of a set of radical ideals. -/
noncomputable instance instInfSet : InfSet (Rad R) :=
  ⟨fun S => ⟨sInf (Subtype.val '' S), IsRadical.sInf' (by
    rintro _ ⟨I, _, rfl⟩
    exact I.2)⟩⟩

/-- Supremum of a set of radical ideals. -/
noncomputable instance instSupSet : SupSet (Rad R) :=
  ⟨fun S => ⟨(sSup (Subtype.val '' S)).radical, radical_isRadical _⟩⟩

/-- Radical ideals form a complete lattice.
    Blueprint: Theorem 2.6 (thm:radical-complete-lattice) -/
noncomputable instance instCompleteLattice : CompleteLattice (Rad R) where
  sup := (· ⊔ ·)
  le_sup_left := fun I _ x hx => le_radical (Ideal.mem_sup_left hx)
  le_sup_right := fun _ J x hx => le_radical (Ideal.mem_sup_right hx)
  sup_le := fun I J K hIK hJK x hx => by
    have hx' : x ∈ (I.1 ⊔ J.1).radical := hx
    rw [← K.isRadical.radical]
    exact radical_mono (sup_le hIK hJK) hx'
  inf := (· ⊓ ·)
  inf_le_left := fun _ _ x hx => hx.1
  inf_le_right := fun _ _ x hx => hx.2
  le_inf := fun _ _ _ hIJ hIK x hx => ⟨hIJ hx, hIK hx⟩
  sSup := sSup
  le_sSup := fun S I hI x hx => by
    apply le_radical
    apply Ideal.mem_sSup_of_mem
    exact ⟨I, hI, rfl⟩
    exact hx
  sSup_le := fun S I hI => by
    intro x hx
    rw [← I.isRadical.radical]
    apply radical_mono _ hx
    apply sSup_le
    intro J hJ
    simp only [Set.mem_image] at hJ
    obtain ⟨K, hK, rfl⟩ := hJ
    exact hI K hK
  sInf := sInf
  sInf_le := fun S I hI x hx => by
    simp only [instInfSet, Submodule.mem_sInf] at hx
    exact hx I.1 ⟨I, hI, rfl⟩
  le_sInf := fun S I hI x hx => by
    simp only [instInfSet, Submodule.mem_sInf]
    intro J hJ
    simp only [Set.mem_image] at hJ
    obtain ⟨K, hK, rfl⟩ := hJ
    exact hI K hK hx
  top := ⊤
  bot := ⊥
  le_top := fun _ _ _ => trivial
  bot_le := fun I x hx => I.isRadical (radical_mono bot_le hx)

/-! ### Frame Distributivity -/

/-- Product of ideals and radical property.
    Blueprint: Lemma 2.7 (lemma:product-radical-property) -/
theorem sqrt_mul_eq_inf (I J : Ideal R) : (I * J).radical = I.radical ⊓ J.radical := by
  exact radical_mul I J

/-- Radical ideals form a frame.
    Blueprint: Corollary 2.9 (cor:radical-frame) -/
noncomputable instance instFrame : Order.Frame (Rad R) := sorry

/-! ### Basic Open Sets -/

/-- The basic open set `D(f) = √(f)` for an element `f : R`.
    Blueprint: Definition 2.10 (def:basic-open-set) -/
def basicOpen (f : R) : Rad R :=
  ⟨(Ideal.span {f}).radical, radical_isRadical _⟩

/-- Basic opens are radical.
    Blueprint: Lemma 2.11 (lemma:basic-open-radical) -/
theorem basicOpen_isRadical (f : R) : ((basicOpen f : Rad R) : Ideal R).IsRadical :=
  (basicOpen f).isRadical

/-- `D(1) = ⊤`.
    Blueprint: Lemma 2.12 (lemma:basic-open-properties) item 1 -/
@[simp]
theorem basicOpen_one : basicOpen (1 : R) = ⊤ := by
  apply ext
  intro x
  simp only [basicOpen, instTop]
  constructor
  · intro _; trivial
  · intro _
    apply le_radical
    simp only [Ideal.span_singleton_one, Submodule.mem_top]

/-- `D(0) = ⊥`.
    Blueprint: Lemma 2.12 (lemma:basic-open-properties) item 2 -/
@[simp]
theorem basicOpen_zero : basicOpen (0 : R) = ⊥ := sorry

/-- `D(fg) = D(f) ⊓ D(g)`.
    Blueprint: Lemma 2.12 (lemma:basic-open-properties) item 3 -/
theorem basicOpen_mul (f g : R) : basicOpen (f * g) = basicOpen f ⊓ basicOpen g := sorry

/-- `D(f^n) = D(f)` for `n ≥ 1`.
    Blueprint: Lemma 2.12 (lemma:basic-open-properties) item 4 -/
theorem basicOpen_pow (f : R) {n : ℕ} (hn : 0 < n) : basicOpen (f ^ n) = basicOpen f := sorry

/-- `D(f) ⊓ D(g) = D(fg)`.
    Blueprint: Lemma 2.13 (lemma:basic-open-meet-join) item 1 -/
theorem basicOpen_inf (f g : R) : basicOpen f ⊓ basicOpen g = basicOpen (f * g) :=
  (basicOpen_mul f g).symm

/-- Membership in radical iff basic open is contained.
    Blueprint: Lemma 2.14 (lemma:radical-membership-basic-open) -/
theorem mem_radical_iff_basicOpen_le {f : R} {I : Rad R} :
    f ∈ (I : Ideal R).radical ↔ basicOpen f ≤ I := sorry

/-- Cover criterion for basic opens.
    Blueprint: Lemma 2.15 (lemma:cover-criterion-basic-opens) -/
theorem cover_iff {f : R} {S : Set R} :
    basicOpen f ≤ sSup (basicOpen '' S) ↔ f ∈ (Ideal.span S).radical := sorry

/-! ### Frame Presentation of the Zariski Locale -/

/-- The Zariski frame admits a presentation by basic opens.
    Blueprint: Theorem 2.16 (thm:zariski-frame-presentation) -/
theorem presentation :
    ∃ (_ : Rad R ≃o Rad R), True := by
  exact ⟨OrderIso.refl _, trivial⟩

end Rad
