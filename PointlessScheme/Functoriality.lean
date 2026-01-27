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
theorem map_top (φ : R →+* S) : map φ ⊤ = ⊤ := by
  apply ext
  intro x
  constructor
  · intro _; trivial
  · intro _
    -- map φ ⊤ = ⟨(Ideal.map φ ⊤).radical, _⟩ and Ideal.map φ ⊤ = ⊤
    -- So (Ideal.map φ ⊤).radical = ⊤.radical = ⊤
    show x ∈ (Ideal.map φ (⊤ : Ideal R)).radical
    rw [Ideal.map_top, Ideal.radical_top]
    trivial

/-- The map preserves finite meets.
    Blueprint: Lemma 3.5 (lemma:preserve-finite-meets) -/
theorem map_inf (φ : R →+* S) (I J : Rad R) : map φ (I ⊓ J) = map φ I ⊓ map φ J := by
  -- First show the underlying ideals are equal
  -- Since I.1, J.1 are radical: I.1 ⊓ J.1 = (I.1 * J.1).radical (by sqrt_mul_eq_inf)
  have hIJ : I.1 ⊓ J.1 = (I.1 * J.1).radical := by
    rw [sqrt_mul_eq_inf, I.isRadical.radical, J.isRadical.radical]
  -- Using map_mul: Ideal.map φ (I.1 * J.1) = Ideal.map φ I.1 * Ideal.map φ J.1
  have hmap : Ideal.map φ (I.1 * J.1) = Ideal.map φ I.1 * Ideal.map φ J.1 := Ideal.map_mul φ I.1 J.1
  -- Key step: (Ideal.map φ K.radical).radical = (Ideal.map φ K).radical for any K
  have hrad : ∀ K : Ideal R, (Ideal.map φ K.radical).radical = (Ideal.map φ K).radical := by
    intro K
    apply le_antisymm
    -- (→) Use Ideal.map_radical_le: map φ K.radical ≤ (map φ K).radical
    · calc (Ideal.map φ K.radical).radical
          ≤ ((Ideal.map φ K).radical).radical := Ideal.radical_mono (Ideal.map_radical_le φ)
        _ = (Ideal.map φ K).radical := Ideal.radical_idem _
    -- (←) Use le_radical and map_mono
    · exact Ideal.radical_mono (Ideal.map_mono le_radical)
  -- Key equality
  have heq : (Ideal.map φ (I.1 ⊓ J.1)).radical =
      (Ideal.map φ I.1).radical ⊓ (Ideal.map φ J.1).radical := by
    calc (Ideal.map φ (I.1 ⊓ J.1)).radical
        = (Ideal.map φ (I.1 * J.1).radical).radical := by rw [hIJ]
      _ = (Ideal.map φ (I.1 * J.1)).radical := hrad _
      _ = (Ideal.map φ I.1 * Ideal.map φ J.1).radical := by rw [hmap]
      _ = (Ideal.map φ I.1).radical ⊓ (Ideal.map φ J.1).radical := sqrt_mul_eq_inf _ _
  apply ext
  intro x
  simp only [map, instInf, heq]

/-- The map preserves arbitrary joins.
    Blueprint: Lemma 3.6 (lemma:preserve-arbitrary-joins) -/
theorem map_sSup (φ : R →+* S) (s : Set (Rad R)) : map φ (sSup s) = sSup (map φ '' s) := by
  -- Key step: (Ideal.map φ K.radical).radical = (Ideal.map φ K).radical for any K
  have hrad : ∀ K : Ideal R, (Ideal.map φ K.radical).radical = (Ideal.map φ K).radical := by
    intro K
    apply le_antisymm
    · calc (Ideal.map φ K.radical).radical
          ≤ ((Ideal.map φ K).radical).radical := Ideal.radical_mono (Ideal.map_radical_le φ)
        _ = (Ideal.map φ K).radical := Ideal.radical_idem _
    · exact Ideal.radical_mono (Ideal.map_mono le_radical)
  -- Prove the underlying ideals are equal, then use ext
  have hLHS : (map φ (sSup s)).1 = (Ideal.map φ (sSup (Subtype.val '' s))).radical := by
    simp only [map, instSupSet]
    exact hrad _
  have hRHS_set : Subtype.val '' (map φ '' s) = (fun I : Rad R => (Ideal.map φ I.1).radical) '' s := by
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨radI, ⟨I, hI, rfl⟩, rfl⟩
      exact ⟨I, hI, rfl⟩
    · rintro ⟨I, hI, rfl⟩
      exact ⟨⟨(Ideal.map φ I.1).radical, radical_isRadical _⟩, ⟨I, hI, rfl⟩, rfl⟩
  -- Show the two ideals are equal
  have heq : (Ideal.map φ (sSup (Subtype.val '' s))).radical =
      (sSup (Subtype.val '' (map φ '' s))).radical := by
    rw [hRHS_set]
    -- LHS: Use Ideal.map_sSup
    rw [Ideal.map_sSup]
    -- LHS = (⨆ K ∈ Subtype.val '' s, Ideal.map φ K).radical
    -- Need to simplify the iSup
    have hLHS_simp : (⨆ K ∈ Subtype.val '' s, Ideal.map φ K) = ⨆ I ∈ s, Ideal.map φ I.1 := by
      apply le_antisymm
      · apply iSup₂_le
        intro K hK
        simp only [Set.mem_image] at hK
        obtain ⟨I, hI, rfl⟩ := hK
        exact @le_iSup₂ (Ideal S) (Rad R) (fun I => I ∈ s) _ (fun I _ => Ideal.map φ I.1) I hI
      · apply iSup₂_le
        intro I hI
        have hmem : I.1 ∈ Subtype.val '' s := ⟨I, hI, rfl⟩
        exact @le_iSup₂ (Ideal S) (Ideal R) (fun K => K ∈ Subtype.val '' s) _
            (fun K _ => Ideal.map φ K) I.1 hmem
    rw [hLHS_simp]
    -- Now: (⨆ I ∈ s, Ideal.map φ I.1).radical = (sSup ((fun I => (Ideal.map φ I.1).radical) '' s)).radical
    apply le_antisymm
    · -- (⨆ I ∈ s, Ideal.map φ I.1).radical ≤ (sSup ...).radical
      apply Ideal.radical_mono
      apply iSup₂_le
      intro I hI
      apply le_trans le_radical
      apply le_sSup
      simp only [Set.mem_image]
      exact ⟨I, hI, rfl⟩
    · -- (sSup ...).radical ≤ (⨆ I ∈ s, Ideal.map φ I.1).radical
      -- We show: sSup ((fun I => (Ideal.map φ I.1).radical) '' s) ≤ (⨆ I ∈ s, Ideal.map φ I.1).radical
      -- Then taking radical and using radical_idem gives the result
      have h : sSup ((fun I : Rad R => (Ideal.map φ I.1).radical) '' s) ≤
          (⨆ J ∈ s, Ideal.map φ J.1).radical := by
        apply sSup_le
        intro y hy
        simp only [Set.mem_image] at hy
        obtain ⟨I, hI, rfl⟩ := hy
        -- Need: (Ideal.map φ I.1).radical ≤ (⨆ J ∈ s, Ideal.map φ J.1).radical
        apply Ideal.radical_mono
        exact @le_iSup₂ (Ideal S) (Rad R) (fun J => J ∈ s) _ (fun J _ => Ideal.map φ J.1) I hI
      calc (sSup ((fun I : Rad R => (Ideal.map φ I.1).radical) '' s)).radical
          ≤ ((⨆ J ∈ s, Ideal.map φ J.1).radical).radical := Ideal.radical_mono h
        _ = (⨆ J ∈ s, Ideal.map φ J.1).radical := Ideal.radical_idem _
  apply ext
  intro x
  -- Goal: x ∈ map φ (sSup s) ↔ x ∈ sSup (map φ '' s)
  -- By hLHS: (map φ (sSup s)).1 = (Ideal.map φ (sSup (Subtype.val '' s))).radical
  -- By heq: (Ideal.map φ (sSup (Subtype.val '' s))).radical = (sSup (Subtype.val '' (map φ '' s))).radical
  -- And (sSup (map φ '' s)).1 = (sSup (Subtype.val '' (map φ '' s))).radical by def of instSupSet
  have h1 : (map φ (sSup s)).1 = (sSup (map φ '' s)).1 := by
    rw [hLHS, heq]
    rfl
  constructor
  · intro hx
    have : x ∈ (map φ (sSup s)).1 := hx
    rw [h1] at this
    exact this
  · intro hx
    have : x ∈ (sSup (map φ '' s)).1 := hx
    rw [← h1] at this
    exact this

/-- φ* is a frame homomorphism.
    Blueprint: Theorem 3.7 (thm:phi-star-frame-homomorphism) -/
noncomputable def mapFrameHom (φ : R →+* S) : FrameHom (Rad R) (Rad S) where
  toFun := map φ
  map_inf' := map_inf φ
  map_top' := map_top φ
  map_sSup' := map_sSup φ

/-- Identity homomorphism induces identity on Rad.
    Blueprint: Lemma 3.8 (lemma:identity-homomorphism) -/
theorem id_map (I : Rad R) : map (RingHom.id R) I = I := by
  apply ext
  intro x
  simp only [map]
  -- Need: x ∈ (Ideal.map (RingHom.id R) I.1).radical ↔ x ∈ I
  -- Ideal.map id I.1 = I.1 by Ideal.map_id
  -- So (Ideal.map id I.1).radical = I.1.radical = I.1 (since I is radical)
  show x ∈ (Ideal.map (RingHom.id R) I.1).radical ↔ x ∈ I.1
  rw [Ideal.map_id, I.isRadical.radical]

/-- Composition of ring homomorphisms.
    Blueprint: Part of Theorem 3.9 (thm:functoriality-spec) -/
theorem comp_map (φ : R →+* S) (ψ : S →+* T) (I : Rad R) :
    map (ψ.comp φ) I = map ψ (map φ I) := by
  apply ext
  intro x
  simp only [map]
  -- LHS: x ∈ (Ideal.map (ψ.comp φ) I.1).radical
  -- RHS: x ∈ (Ideal.map ψ (Ideal.map φ I.1).radical).radical
  -- By Ideal.map_map: Ideal.map ψ (Ideal.map φ I.1) = Ideal.map (ψ.comp φ) I.1
  show x ∈ (Ideal.map (ψ.comp φ) I.1).radical ↔ x ∈ (Ideal.map ψ (Ideal.map φ I.1).radical).radical
  constructor
  · -- LHS → RHS
    intro hx
    apply Ideal.radical_mono _ hx
    -- Need: Ideal.map (ψ.comp φ) I.1 ≤ Ideal.map ψ (Ideal.map φ I.1).radical
    rw [← Ideal.map_map]
    exact Ideal.map_mono le_radical
  · -- RHS → LHS
    intro hx
    -- Chain: (Ideal.map ψ (Ideal.map φ I.1).radical).radical
    --      ≤ ((Ideal.map ψ (Ideal.map φ I.1)).radical).radical  (by map_radical_le)
    --      = (Ideal.map ψ (Ideal.map φ I.1)).radical            (by radical_idem)
    --      = (Ideal.map (ψ.comp φ) I.1).radical                 (by map_map)
    have h1 : (Ideal.map ψ (Ideal.map φ I.1).radical).radical ≤
        ((Ideal.map ψ (Ideal.map φ I.1)).radical).radical :=
      Ideal.radical_mono (Ideal.map_radical_le ψ)
    have h2 : ((Ideal.map ψ (Ideal.map φ I.1)).radical).radical =
        (Ideal.map ψ (Ideal.map φ I.1)).radical := Ideal.radical_idem _
    have h3 : (Ideal.map ψ (Ideal.map φ I.1)).radical =
        (Ideal.map (ψ.comp φ) I.1).radical := by rw [Ideal.map_map]
    rw [h2, h3] at h1
    exact h1 hx

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
