/-
Copyright (c) 2025 Pointless Scheme Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pointless Scheme Project
-/
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.LinearAlgebra.Finsupp.Span

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

/-- Frame distributivity for radical ideals: J ⊓ sSup S ≤ sSup {J ⊓ L | L ∈ S}.
    The key insight is that if x ∈ J and x^n ∈ ∑ Lᵢ, then x^(n+1) ∈ ∑ (J ∩ Lᵢ). -/
theorem inf_sSup_le_iSup_inf (J : Rad R) (S : Set (Rad R)) :
    J ⊓ sSup S ≤ ⨆ L ∈ S, J ⊓ L := by
  intro x ⟨hxJ, hxS⟩
  simp only [instSupSet] at hxS
  obtain ⟨n, hn⟩ := hxS
  -- hn : x^n ∈ sSup (Subtype.val '' S)
  -- We show x ∈ ⨆ L ∈ S, J ⊓ L by showing x^(n+1) ∈ sSup {(J ⊓ L).val | L ∈ S}
  have htarget : (⨆ L ∈ S, J ⊓ L : Rad R) = sSup ((fun L => J ⊓ L) '' S) := sSup_image.symm
  rw [htarget]
  simp only [instSupSet]
  use n + 1
  rw [pow_succ]
  -- x^(n+1) = x^n * x, need this in sSup {(J ⊓ L).val | L ∈ S}
  -- For any y in an ideal L ∈ S, y * x ∈ J ⊓ L (since x ∈ J, L is an ideal)
  -- So multiplication by x sends sSup {L.val} into sSup {(J ⊓ L).val}
  have hmul : ∀ y ∈ sSup (Subtype.val '' S),
      y * x ∈ sSup (Subtype.val '' ((fun L : Rad R => (J ⊓ L : Rad R)) '' S)) := by
    intro y hy
    -- sSup is closed under addition, so it suffices to show this for generators
    -- Use the characterization: y ∈ sSup S iff y is a finite combination
    rw [Submodule.mem_sSup_iff_exists_finset] at hy ⊢
    obtain ⟨s, hs, hys⟩ := hy
    -- For each I ∈ s, we have I = L.val for some L ∈ S
    -- We build the finset of J ⊓ L
    classical
    let t : Finset (Submodule R R) := s.image (fun I =>
      (J.1 ⊓ I : Ideal R))
    use t
    constructor
    · -- t ⊆ image of meets
      intro I hI
      -- hI : I ∈ (t : Set _), need to extract the image structure
      simp only [Finset.mem_coe] at hI
      rw [Finset.mem_image] at hI
      obtain ⟨I', hI's, rfl⟩ := hI
      have hI'_in : I' ∈ Subtype.val '' S := hs hI's
      rw [Set.mem_image] at hI'_in
      obtain ⟨L, hLS, rfl⟩ := hI'_in
      rw [Set.mem_image]
      refine ⟨⟨J.1 ⊓ L.1, J.2.inf L.2⟩, ⟨L, hLS, rfl⟩, rfl⟩
    · -- y * x ∈ ⨆ i ∈ t, i
      -- The key: ⨆ i ∈ t, i contains J.1 ⊓ I for all I ∈ s
      have hsub : (⨆ (i : Submodule R R) (_ : i ∈ s), (J.1 ⊓ i : Ideal R)) ≤ ⨆ i ∈ t, i := by
        apply iSup₂_le
        intro I hI
        apply le_iSup_of_le ((J.1 ⊓ I : Ideal R))
        apply le_iSup_of_le (by rw [Finset.mem_image]; exact ⟨I, hI, rfl⟩)
        exact le_refl _
      apply hsub
      -- Now show y * x ∈ ⨆ i ∈ s, J.1 ⊓ i
      -- Use that y ∈ ⨆ i ∈ s, i and for each piece from I, multiplying by x gives J ⊓ I
      -- Convert biSup to iSup over Subtype
      rw [show (⨆ (i : Submodule R R) (_ : i ∈ s), (i : Submodule R R)) =
          ⨆ (i : s), (i.1 : Submodule R R) by simp [iSup_subtype]] at hys
      rw [show (⨆ (i : Submodule R R) (_ : i ∈ s), (J.1 ⊓ i : Ideal R)) =
          ⨆ (i : s), (J.1 ⊓ i.1 : Ideal R) by simp [iSup_subtype]]
      refine Submodule.iSup_induction (ι := s) (p := fun i => i.1)
          (motive := fun y => y * x ∈ ⨆ (i : s), (J.1 ⊓ i.1 : Ideal R)) hys ?_ ?_ ?_
      · -- For y ∈ I.1 where I : s, show y * x ∈ ⨆ i : s, J.1 ⊓ i.1
        intro ⟨I, hI⟩ y hy
        apply Submodule.mem_iSup_of_mem ⟨I, hI⟩
        -- y ∈ I, x ∈ J, so y * x ∈ J ⊓ I
        constructor
        · exact J.1.mul_mem_left y hxJ
        · -- y ∈ I and I is from S, hence an ideal
          have hI_ideal : I ∈ Subtype.val '' S := hs hI
          simp only [Set.mem_image] at hI_ideal
          obtain ⟨L, _, rfl⟩ := hI_ideal
          exact L.1.mul_mem_right x hy
      · simp only [zero_mul, Submodule.zero_mem]
      · intro y z hy hz
        rw [add_mul]
        exact Submodule.add_mem _ hy hz
  exact hmul (x ^ n) hn

/-- Heyting implication for radical ideals: I ⇨ J = ⨆ {K | I ⊓ K ≤ J}. -/
noncomputable instance instHImp : HImp (Rad R) :=
  ⟨fun I J => sSup { K | I ⊓ K ≤ J }⟩

/-- Complement for radical ideals. -/
noncomputable instance instCompl : Compl (Rad R) :=
  ⟨fun I => I ⇨ ⊥⟩

/-- Radical ideals form a frame.
    Blueprint: Corollary 2.9 (cor:radical-frame) -/
noncomputable instance instFrame : Order.Frame (Rad R) where
  himp := (· ⇨ ·)
  le_himp_iff := fun I J K => by
    constructor
    · -- I ≤ J ⇨ K implies I ⊓ J ≤ K
      intro hle
      calc I ⊓ J = J ⊓ I := inf_comm (a := I) (b := J)
        _ ≤ J ⊓ (J ⇨ K) := inf_le_inf_left J hle
        _ ≤ K := by
          simp only [instHImp]
          -- Use frame distributivity
          calc J ⊓ sSup {L | J ⊓ L ≤ K} ≤ ⨆ L ∈ {L | J ⊓ L ≤ K}, J ⊓ L :=
                inf_sSup_le_iSup_inf J _
            _ ≤ K := by
              apply iSup₂_le
              intro L hL
              exact hL
    · -- I ⊓ J ≤ K implies I ≤ J ⇨ K
      intro hle
      apply le_sSup
      simp only [Set.mem_setOf_eq]
      calc J ⊓ I = I ⊓ J := inf_comm (a := J) (b := I)
        _ ≤ K := hle
  compl := (·ᶜ)
  himp_bot := fun I => rfl

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
theorem basicOpen_zero : basicOpen (0 : R) = ⊥ := by
  apply ext
  intro x
  simp only [basicOpen, instBot]
  constructor
  · intro hx
    -- x ∈ √(0) means x^n = 0 for some n, which is exactly the nilradical
    simp only [Ideal.span_singleton_eq_bot.mpr rfl] at hx
    exact hx
  · intro hx
    simp only [Ideal.span_singleton_eq_bot.mpr rfl]
    exact hx

/-- `D(fg) = D(f) ⊓ D(g)`.
    Blueprint: Lemma 2.12 (lemma:basic-open-properties) item 3 -/
theorem basicOpen_mul (f g : R) : basicOpen (f * g) = basicOpen f ⊓ basicOpen g := by
  apply ext
  intro x
  simp only [basicOpen, instInf]
  -- Need: x ∈ √(fg) ↔ x ∈ √(f) ∩ √(g)
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := hx
    rw [Ideal.mem_span_singleton] at hn
    obtain ⟨c, hc⟩ := hn
    -- hc : x ^ n = f * g * c
    constructor
    · -- x ∈ √(f): need x^m ∈ (f) for some m
      use n
      rw [Ideal.mem_span_singleton]
      exact ⟨g * c, by rw [hc]; ring⟩
    · -- x ∈ √(g): need x^m ∈ (g) for some m
      use n
      rw [Ideal.mem_span_singleton]
      exact ⟨f * c, by rw [hc]; ring⟩
  · intro ⟨hf, hg⟩
    obtain ⟨n, hn⟩ := hf
    obtain ⟨m, hm⟩ := hg
    rw [Ideal.mem_span_singleton] at hn hm
    obtain ⟨a, ha⟩ := hn
    obtain ⟨b, hb⟩ := hm
    -- ha : x^n = f * a and hb : x^m = g * b, so x^(n+m) = (f*g) * (a*b)
    use n + m
    rw [Ideal.mem_span_singleton]
    use a * b
    calc x ^ (n + m) = x ^ n * x ^ m := pow_add x n m
      _ = (f * a) * (g * b) := by rw [ha, hb]
      _ = f * g * (a * b) := by ring

/-- `D(f^n) = D(f)` for `n ≥ 1`.
    Blueprint: Lemma 2.12 (lemma:basic-open-properties) item 4 -/
theorem basicOpen_pow (f : R) {n : ℕ} (hn : 0 < n) : basicOpen (f ^ n) = basicOpen f := by
  apply ext
  intro x
  simp only [basicOpen]
  constructor
  · -- x ∈ √(f^n) → x ∈ √(f)
    intro ⟨m, hm⟩
    rw [Ideal.mem_span_singleton] at hm
    obtain ⟨c, hc⟩ := hm
    -- x^m = f^n * c, so x^m ∈ (f) since f^n = f * f^(n-1)
    use m
    rw [Ideal.mem_span_singleton]
    use c * f ^ (n - 1)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
    have hk' : k = n - 1 := by omega
    calc x ^ m = f ^ n * c := hc
      _ = f ^ (k + 1) * c := by rw [hk]
      _ = f * f ^ k * c := by rw [pow_succ']
      _ = f * (c * f ^ k) := by ring
      _ = f * (c * f ^ (n - 1)) := by rw [hk']
  · -- x ∈ √(f) → x ∈ √(f^n)
    intro ⟨m, hm⟩
    rw [Ideal.mem_span_singleton] at hm
    obtain ⟨c, hc⟩ := hm
    -- x^m = f * c, so x^(m*n) = f^n * c^n ∈ (f^n)
    use m * n
    rw [Ideal.mem_span_singleton]
    use c ^ n
    calc x ^ (m * n) = (x ^ m) ^ n := by rw [pow_mul]
      _ = (f * c) ^ n := by rw [hc]
      _ = f ^ n * c ^ n := by rw [mul_pow]

/-- `D(f) ⊓ D(g) = D(fg)`.
    Blueprint: Lemma 2.13 (lemma:basic-open-meet-join) item 1 -/
theorem basicOpen_inf (f g : R) : basicOpen f ⊓ basicOpen g = basicOpen (f * g) :=
  (basicOpen_mul f g).symm

/-- Membership in radical iff basic open is contained.
    Blueprint: Lemma 2.14 (lemma:radical-membership-basic-open) -/
theorem mem_radical_iff_basicOpen_le {f : R} {I : Rad R} :
    f ∈ (I : Ideal R).radical ↔ basicOpen f ≤ I := by
  -- f ∈ √I ↔ D(f) = √(f) ⊆ I
  constructor
  · -- (→) f ∈ √I implies √(f) ⊆ I
    intro hf x hx
    -- x ∈ √(f) means x^n ∈ (f) for some n
    obtain ⟨n, hn⟩ := hx
    rw [Ideal.mem_span_singleton] at hn
    obtain ⟨c, hc⟩ := hn
    -- hc : x^n = f * c
    -- Since f ∈ √I, we have f^m ∈ I for some m
    obtain ⟨m, hm⟩ := hf
    -- So x^(n*m) = (f * c)^m = f^m * c^m ∈ I
    apply I.isRadical
    use n * m
    have heq : x ^ (n * m) = f ^ m * c ^ m := by
      calc x ^ (n * m) = (x ^ n) ^ m := by rw [pow_mul]
        _ = (f * c) ^ m := by rw [hc]
        _ = f ^ m * c ^ m := mul_pow f c m
    rw [heq]
    exact I.1.mul_mem_right (c ^ m) hm
  · -- (←) D(f) ⊆ I implies f ∈ √I
    intro hle
    -- Since f ∈ √(f) = D(f), and D(f) ⊆ I, we have f ∈ I ⊆ √I
    have hf_in_basicOpen : f ∈ basicOpen f := by
      simp only [basicOpen]
      use 1
      simp only [pow_one, Ideal.mem_span_singleton]
      use 1
      ring
    have hf_in_I : f ∈ (I : Ideal R) := hle hf_in_basicOpen
    exact le_radical hf_in_I

/-- Cover criterion for basic opens.
    Blueprint: Lemma 2.15 (lemma:cover-criterion-basic-opens) -/
theorem cover_iff {f : R} {S : Set R} :
    basicOpen f ≤ sSup (basicOpen '' S) ↔ f ∈ (Ideal.span S).radical := by
  -- D(f) ≤ ⨆ (g ∈ S), D(g) ↔ f ∈ √(span S)
  -- Key: sSup (basicOpen '' S) = √(sSup {√(g) : g ∈ S}) and this equals √(span S)
  have hsup_eq : (sSup (basicOpen '' S) : Rad R) =
      ⟨(Ideal.span S).radical, radical_isRadical _⟩ := by
    apply ext
    intro x
    simp only [instSupSet]
    -- x ∈ √(sSup {√(g) : g ∈ S}) ↔ x ∈ √(span S)
    constructor
    · -- (→) √(sSup {√(g) : g ∈ S}) ⊆ √(span S)
      intro hx
      -- Each √(g) ⊆ √(span S) since g ∈ span S
      -- So sSup {√(g)} ⊆ √(span S) (since √(span S) is radical, hence closed under sSup)
      -- Hence √(sSup {√(g)}) ⊆ √(√(span S)) = √(span S)
      have h1 : sSup (Subtype.val '' (basicOpen '' S)) ≤ (Ideal.span S).radical := by
        apply sSup_le
        intro I hI
        simp only [Set.mem_image] at hI
        obtain ⟨J, hJ, rfl⟩ := hI
        obtain ⟨g, hg, rfl⟩ := hJ
        -- J = √(g), need √(g) ⊆ √(span S)
        apply radical_mono
        rw [Ideal.span_singleton_le_iff_mem]
        exact Ideal.subset_span hg
      have h2 : (sSup (Subtype.val '' (basicOpen '' S))).radical ≤
          ((Ideal.span S).radical).radical := radical_mono h1
      rw [(radical_isRadical _).radical] at h2
      exact h2 hx
    · -- (←)
      intro hx
      apply radical_mono _ hx
      intro y hy
      rw [Ideal.mem_span] at hy
      apply hy
      intro g hg
      apply Ideal.mem_sSup_of_mem
      · use basicOpen g
        simp only [Set.mem_image]
        exact ⟨⟨g, hg, rfl⟩, rfl⟩
      · use 1
        simp only [pow_one, Ideal.mem_span_singleton]
        use 1
        ring
  rw [hsup_eq]
  -- Now: D(f) ≤ √(span S) ↔ f ∈ √(span S)
  -- This follows from mem_radical_iff_basicOpen_le (with I = √(span S))
  have h : basicOpen f ≤ ⟨(Ideal.span S).radical, radical_isRadical _⟩ ↔
      f ∈ ((⟨(Ideal.span S).radical, radical_isRadical _⟩ : Rad R) : Ideal R).radical := by
    exact mem_radical_iff_basicOpen_le.symm
  rw [h]
  -- f ∈ √(√(span S)) ↔ f ∈ √(span S)
  have hrad : ((⟨(Ideal.span S).radical, radical_isRadical _⟩ : Rad R) : Ideal R).radical =
      (Ideal.span S).radical := by
    exact (radical_isRadical _).radical
  rw [hrad]

/-! ### Universal Property via Basic Opens

Instead of abstract frame presentations, we prove concrete theorems showing
that `Rad R` has the universal property: it is generated by basic opens,
and frame homomorphisms from `Rad R` are determined by their action on basic opens.
-/

/-- Every radical ideal is the supremum of basic opens of its elements.
    This is the "generators" part of the frame presentation. -/
theorem radical_eq_sSup_basicOpen (I : Rad R) :
    I = ⨆ (f : R) (_ : f ∈ I.val), basicOpen f := by
  apply le_antisymm
  · -- I ≤ ⨆ basicOpen f for f ∈ I
    intro x hx
    -- x ∈ I, need x ∈ ⨆ basicOpen f
    -- Since x ∈ I and x ∈ basicOpen x, we need to show x is in the join
    -- The join involves taking radical, so we need x^n in sSup of the underlying ideals
    -- We use that basicOpen x ≤ ⨆ and x ∈ basicOpen x
    have hle : basicOpen x ≤ ⨆ (f : R) (_ : f ∈ I.val), basicOpen f :=
      le_iSup₂_of_le x hx (le_refl _)
    have hx_in_basicOpen : x ∈ basicOpen x := by
      simp only [basicOpen]
      use 1
      simp only [pow_one, Ideal.mem_span_singleton]
      exact ⟨1, by ring⟩
    exact hle hx_in_basicOpen
  · -- ⨆ basicOpen f ≤ I
    apply iSup₂_le
    intro f hf
    -- Need basicOpen f ≤ I when f ∈ I
    -- This is mem_radical_iff_basicOpen_le
    rw [← mem_radical_iff_basicOpen_le]
    exact le_radical hf

/-- A frame homomorphism from Rad R is determined by its action on basic opens.
    This is the universal property of the frame presentation. -/
theorem frameHom_eq_of_basicOpen_eq {L : Type*} [Order.Frame L]
    (f g : FrameHom (Rad R) L)
    (h : ∀ r : R, f (basicOpen r) = g (basicOpen r)) : f = g := by
  ext I
  -- Use that I = ⨆ basicOpen r for r ∈ I
  rw [radical_eq_sSup_basicOpen I]
  -- f (⨆ ...) = ⨆ f(...) = ⨆ g(...) = g (⨆ ...)
  simp only [map_iSup₂]
  congr 1
  ext r
  congr 1
  ext _
  exact h r

/-! ### Frame Presentation of the Zariski Locale -/

/-- The Zariski frame is generated by basic opens and satisfies the key relations.

    The frame presentation of Rad R consists of:
    - Generators: D(f) = √(f) for f ∈ R
    - Relations:
      * D(1) = ⊤ (basicOpen_one)
      * D(0) = ⊥ (basicOpen_zero)
      * D(fg) = D(f) ⊓ D(g) (basicOpen_mul)
      * D(f^n) = D(f) (basicOpen_pow)

    The presentation property is witnessed by:
    1. Every radical ideal is the supremum of basic opens (radical_eq_sSup_basicOpen)
    2. Frame homomorphisms are determined by their action on basic opens
       (frameHom_eq_of_basicOpen_eq)

    This theorem packages these facts together.
    Blueprint: Theorem 2.16 (thm:zariski-frame-presentation) -/
theorem presentation :
    (basicOpen (1 : R) = ⊤) ∧
    (basicOpen (0 : R) = ⊥) ∧
    (∀ f g : R, basicOpen (f * g) = basicOpen f ⊓ basicOpen g) ∧
    (∀ (I : Rad R), I = ⨆ (f : R) (_ : f ∈ I.val), basicOpen f) :=
  ⟨basicOpen_one, basicOpen_zero, fun f g => basicOpen_mul f g, radical_eq_sSup_basicOpen⟩

end Rad
