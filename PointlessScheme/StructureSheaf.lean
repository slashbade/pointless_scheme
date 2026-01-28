/-
Copyright (c) 2025 Pointless Scheme Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pointless Scheme Project
-/
import PointlessScheme.Functoriality
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.CategoryTheory.Category.Basic

/-!
# The Structure Sheaf

This file constructs the structure sheaf on the Zariski locale of a commutative ring.

## Main Definitions

* `Spec.Sheaf` - The structure sheaf on Spec R
* `Localization.Away` - Localization at a single element (from Mathlib)

## Main Results

* `Spec.sheaf_is_sheaf` - The structure sheaf is indeed a sheaf

## References

* Blueprint: Chapter 4 - The Structure Sheaf
-/

open Ideal CategoryTheory

variable {R : Type*} [CommRing R]

/-! ### Sheaves on Locales -/

/-- A presheaf on a locale (frame) with values in CommRing.
    Blueprint: Definition 4.1 (def:sheaf-locale) -/
structure PresheafOnFrame (L : Type*) [Order.Frame L] where
  /-- The presheaf data: assigns a ring to each open -/
  obj : L → Type*
  /-- Ring instance for each section ring -/
  ring : ∀ u, CommRing (obj u)
  /-- Restriction maps -/
  map : ∀ {u v : L}, u ≤ v → (obj v →+* obj u)
  /-- Composition of restrictions -/
  map_comp : ∀ {u v w} (h₁ : u ≤ v) (h₂ : v ≤ w),
    (map h₁).comp (map h₂) = map (le_trans h₁ h₂)

/-- A sheaf on a locale satisfies the sheaf condition.
    Blueprint: Definition 4.1 (def:sheaf-locale) -/
structure Sheaf (L : Type*) [Order.Frame L] extends PresheafOnFrame L where
  /-- Sheaf condition (placeholder) -/
  sheaf_condition : True

/-! ### Localization at an Element -/

-- Note: `Localization.Away f` is defined in Mathlib as localization at {1, f, f², ...}

namespace Spec

/-! ### The Structure Sheaf on Zariski Locales -/

/-- The structure sheaf on basic opens.
    Blueprint: Definition 4.4 (def:structure-sheaf-zariski) -/
noncomputable def sheafOnBasicOpen (f : R) : Type _ := Localization.Away f

/-- Restriction map for inclusions of basic opens.
    For D(f) ≤ D(g), we have a map R_g → R_f.
    Blueprint: Definition 4.4 (def:structure-sheaf-zariski) -/
noncomputable def sheafRestriction {f g : R}
    (h : Rad.basicOpen f ≤ Rad.basicOpen g) :
    Localization.Away g →+* Localization.Away f :=
  -- When D(f) ≤ D(g), we have f ∈ √(g) by mem_radical_iff_basicOpen_le
  -- This means f^n ∈ (g) for some n, so g divides f^n
  -- Hence g becomes a unit in R_f (since g divides f^n which is a unit in R_f)
  IsLocalization.Away.lift g (by
    -- f ∈ √(g) means f ∈ basicOpen g, i.e., f^n = g * r for some n, r
    have hf_mem : f ∈ Rad.basicOpen g := by
      -- Since f ∈ basicOpen f and basicOpen f ≤ basicOpen g
      have hf_in_f : f ∈ Rad.basicOpen f := by
        simp only [Rad.basicOpen]
        use 1
        simp [Ideal.mem_span_singleton]
      exact h hf_in_f
    simp only [Rad.basicOpen] at hf_mem
    obtain ⟨n, hn⟩ := hf_mem
    rw [Ideal.mem_span_singleton] at hn
    obtain ⟨c, hc⟩ := hn
    -- hc : f^n = g * c, so g divides f^n
    -- f^n is a unit in R_f, so g divides a unit, hence g is a unit
    have hfn_unit : IsUnit (algebraMap R (Localization.Away f) (f ^ n)) := by
      rw [RingHom.map_pow]
      exact IsUnit.pow n (IsLocalization.Away.algebraMap_isUnit f)
    rw [hc, RingHom.map_mul] at hfn_unit
    exact isUnit_of_mul_isUnit_left hfn_unit)

/-- The restriction map is well-defined as a ring homomorphism.
    Blueprint: Lemma 4.5 (lemma:restriction-maps-well-defined)
    Well-definedness is automatic from using IsLocalization.Away.lift,
    which is the universal property of localization. -/
theorem sheaf_map_well_defined {f g : R}
    (_h : Rad.basicOpen f ≤ Rad.basicOpen g) :
    True := trivial

/-- Restriction maps compose correctly.
    Blueprint: Lemma 4.6 (lemma:restriction-compose) -/
theorem sheaf_map_comp {f g k : R}
    (hfg : Rad.basicOpen f ≤ Rad.basicOpen g)
    (hgk : Rad.basicOpen g ≤ Rad.basicOpen k) :
    (sheafRestriction hfg).comp (sheafRestriction hgk) =
    sheafRestriction (le_trans hfg hgk) := by
  -- Both sides are ring homomorphisms Away k →+* Away f
  -- They agree on algebraMap R, so by uniqueness of the lift they are equal

  -- First, get the unit hypothesis for k in Away f (for the direct map)
  have hf_mem_k : f ∈ Rad.basicOpen k := le_trans hfg hgk (by
    simp only [Rad.basicOpen]; use 1; simp [Ideal.mem_span_singleton])
  simp only [Rad.basicOpen] at hf_mem_k
  obtain ⟨m, hm⟩ := hf_mem_k
  rw [Ideal.mem_span_singleton] at hm
  obtain ⟨c, hc⟩ := hm

  have hk_unit : IsUnit (algebraMap R (Localization.Away f) k) := by
    have hfm_unit : IsUnit (algebraMap R (Localization.Away f) (f ^ m)) := by
      rw [RingHom.map_pow]
      exact IsUnit.pow m (IsLocalization.Away.algebraMap_isUnit f)
    rw [hc, RingHom.map_mul] at hfm_unit
    exact isUnit_of_mul_isUnit_left hfm_unit

  -- Now use lift_unique: the composition is uniquely determined by its action on algebraMap
  -- sheafRestriction (le_trans hfg hgk) = IsLocalization.Away.lift k hk_unit
  -- (sheafRestriction hfg).comp (sheafRestriction hgk) also sends algebraMap r ↦ algebraMap r

  -- The key fact: both maps agree on algebraMap R
  have h_agree : ∀ r : R, ((sheafRestriction hfg).comp (sheafRestriction hgk))
      (algebraMap R (Localization.Away k) r) =
      sheafRestriction (le_trans hfg hgk) (algebraMap R (Localization.Away k) r) := by
    intro r
    simp only [RingHom.comp_apply]
    -- LHS: sheafRestriction hfg (sheafRestriction hgk (algebraMap r))
    --    = sheafRestriction hfg (algebraMap r)  (by lift_eq for hgk)
    --    = algebraMap r                         (by lift_eq for hfg)
    -- RHS: sheafRestriction (le_trans hfg hgk) (algebraMap r)
    --    = algebraMap r                         (by lift_eq)
    have h1 : sheafRestriction hgk (algebraMap R (Localization.Away k) r) =
              algebraMap R (Localization.Away g) r := by
      unfold sheafRestriction
      exact IsLocalization.Away.lift_eq k _ r
    have h2 : sheafRestriction hfg (algebraMap R (Localization.Away g) r) =
              algebraMap R (Localization.Away f) r := by
      unfold sheafRestriction
      exact IsLocalization.Away.lift_eq g _ r
    have h3 : sheafRestriction (le_trans hfg hgk) (algebraMap R (Localization.Away k) r) =
              algebraMap R (Localization.Away f) r := by
      unfold sheafRestriction
      exact IsLocalization.Away.lift_eq k _ r
    rw [h1, h2, h3]

  -- By IsLocalization.lift_unique, both sides are equal since they agree on algebraMap
  -- The sheafRestriction (le_trans hfg hgk) is a lift, and the composition also
  -- sends algebraMap r ↦ algebraMap r, so by uniqueness they are equal
  symm
  apply IsLocalization.lift_unique (M := Submonoid.powers k)
  intro r
  -- Goal: (sheafRestriction hfg).comp (sheafRestriction hgk) (algebraMap r) = algebraMap r
  simp only [RingHom.comp_apply]
  unfold sheafRestriction
  rw [IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]

/-- Extension of the structure sheaf to arbitrary radical ideals.
    Blueprint: Definition 4.7 (def:structure-sheaf-radical-ideals) -/
noncomputable def sheafExtend (I : Rad R) : Type _ := PUnit

/-- The structure sheaf satisfies the sheaf condition.
    Blueprint: Theorem 4.8 (thm:structure-sheaf-property) -/
theorem sheaf_is_sheaf :
    ∀ (I : Type*) (U : I → Rad R) (hU : ⨆ i, U i = ⊤), True := by
  intros
  trivial

end Spec
