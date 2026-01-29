/-
Copyright (c) 2025 Pointless Scheme Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pointless Scheme Project
-/
import PointlessScheme.LocallyRingedLocale
import Mathlib.Data.ZMod.Basic

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
  -- Witness: ℤ/6ℤ and ⊥ (the nilradical)
  use ZMod 6, inferInstance, ⊥
  constructor
  · -- ⊥ is always frame-prime: ⊥ ≤ a ⊔ b → ⊥ ≤ a ∨ ⊥ ≤ b
    -- Since ⊥ ≤ anything, both sides of the disjunction are trivially true
    intro a b _
    left
    exact bot_le
  · -- ⊥.val (the nilradical of ℤ/6ℤ = {0}) is not ring-prime
    -- Because 2 * 3 = 0 in ℤ/6ℤ, but 2 ≠ 0 and 3 ≠ 0
    intro hprime
    -- In ℤ/6ℤ: 2 * 3 = 0
    have h23 : (2 : ZMod 6) * 3 = 0 := by native_decide
    -- 0 is in the nilradical (it's nilpotent: 0^1 = 0)
    have h0_nil : (0 : ZMod 6) ∈ (⊥ : Rad (ZMod 6)).val := by
      simp only [Rad.instBot]
      -- 0 ∈ radical(⊥) ↔ ∃ n, 0^n ∈ ⊥
      use 1
      simp only [pow_one, Submodule.zero_mem]
    -- Rewrite h23: 2 * 3 ∈ nilradical
    have h23_nil : (2 : ZMod 6) * 3 ∈ (⊥ : Rad (ZMod 6)).val := by
      rw [h23]; exact h0_nil
    -- By primeness: 2 ∈ nilradical or 3 ∈ nilradical
    have h_or := hprime.mem_or_mem h23_nil
    -- But 2 and 3 are not nilpotent in ℤ/6ℤ
    -- We prove this by showing 2^n and 3^n are never 0 for any n
    have h2_not_nil : (2 : ZMod 6) ∉ (⊥ : Rad (ZMod 6)).val := by
      simp only [Rad.instBot]
      intro ⟨n, hn⟩
      -- 2^n ∈ ⊥ means 2^n = 0 in ZMod 6
      -- In ZMod 6, powers of 2 cycle: 2^1=2, 2^2=4, 2^3=2, ...
      -- They never equal 0
      simp only [Submodule.mem_bot] at hn
      -- Need: 2^n ≠ 0 for any n
      -- We handle the cases
      rcases n with _ | n
      · -- n = 0: 2^0 = 1 ≠ 0
        exact (by native_decide : (1 : ZMod 6) ≠ 0) hn
      · -- For n ≥ 1, 2^(n+1) mod 6 is either 2 or 4, never 0
        have h : ∀ m : ℕ, (2 : ZMod 6) ^ (m + 1) = 2 ∨ (2 : ZMod 6) ^ (m + 1) = 4 := by
          intro m
          induction m with
          | zero => left; rfl
          | succ m ih =>
            rcases ih with h2 | h4
            · right; simp [pow_succ, h2]; native_decide
            · left; simp [pow_succ, h4]; native_decide
        rcases h n with h2 | h4
        · rw [h2] at hn; exact (by native_decide : (2 : ZMod 6) ≠ 0) hn
        · rw [h4] at hn; exact (by native_decide : (4 : ZMod 6) ≠ 0) hn
    have h3_not_nil : (3 : ZMod 6) ∉ (⊥ : Rad (ZMod 6)).val := by
      simp only [Rad.instBot]
      intro ⟨n, hn⟩
      simp only [Submodule.mem_bot] at hn
      rcases n with _ | n
      · -- n = 0: 3^0 = 1 ≠ 0
        exact (by native_decide : (1 : ZMod 6) ≠ 0) hn
      · -- For n ≥ 1, 3^(n+1) mod 6 is always 3, never 0
        have h : ∀ m : ℕ, (3 : ZMod 6) ^ (m + 1) = 3 := by
          intro m
          induction m with
          | zero => rfl
          | succ m ih => simp [pow_succ, ih]; native_decide
        rw [h n] at hn
        exact (by native_decide : (3 : ZMod 6) ≠ 0) hn
    exact h_or.elim h2_not_nil h3_not_nil

/-! ### Irreducible Schemes -/

/-- A locale is irreducible if it cannot be written as a union of two proper closed sublocales.
    Blueprint: Definition 6.8 (def:irreducible-locale) -/
def IsIrreducibleLocale (L : Type*) [Order.Frame L] : Prop :=
  ∀ u v : L, u ⊔ v = ⊤ → u = ⊤ ∨ v = ⊤

/-- A scheme is irreducible if its underlying locale is irreducible.
    Blueprint: Definition 6.9 (def:irreducible-scheme) -/
def Scheme.IsIrreducible (X : Scheme) : Prop :=
  @IsIrreducibleLocale X.toLocallyRingedLocale.frame X.toLocallyRingedLocale.instFrame
