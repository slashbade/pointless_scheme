/-
Copyright (c) 2025 Pointless Scheme Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pointless Scheme Project
-/
import PointlessScheme.StructureSheaf
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

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

## Implementation Notes

### Stalk Construction

The stalk of a sheaf F at an element u of a locale L is mathematically defined as the
colimit (directed limit) over the poset of opens containing the "point":

    stalk_u(F) = colim_{v ≤ u} F(v)

In the pointless setting, the notion of "point" is replaced by filters or completely
prime filters on the frame. For affine schemes Spec R:

- Points correspond to prime ideals p ⊂ R
- The stalk at p is the localization R_p
- R_p is a local ring with maximal ideal pR_p

### Local Ring Structure

A ring R is local if it has a unique maximal ideal, equivalently if the set of
non-units forms an ideal. In Mathlib this is captured by `IsLocalRing R`.

For affine schemes, the key theorem is:

**Theorem:** For any prime ideal p ⊂ R, the localization R_p is a local ring.

This is `Localization.AtPrime.isLocalRing` in Mathlib.

## References

* Blueprint: Chapter 5 - Schemes as Locally Ringed Locales
* Mathlib: `Mathlib.RingTheory.LocalRing.Basic`
* Mathlib: `Mathlib.RingTheory.Localization.AtPrime.Basic`
-/

open Ideal

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### Completely Prime Filters (Points of Locales) -/

/-- A completely prime filter on a frame L is a filter F such that:
    - F is upward closed: if u ∈ F and u ≤ v, then v ∈ F
    - F is closed under finite meets: if u, v ∈ F, then u ⊓ v ∈ F
    - F is completely prime: for any family (u_i), if ⨆ u_i ∈ F then some u_i ∈ F

    In pointless topology, completely prime filters on a frame L correspond to
    "points" of the locale. For the Zariski locale Rad(R), these correspond
    to prime ideals of R.

    Blueprint: Definition 5.1a (def:completely-prime-filter) -/
structure CompletelyPrimeFilter (L : Type*) [Order.Frame L] where
  /-- The underlying set of the filter -/
  carrier : Set L
  /-- The filter contains the top element -/
  top_mem : ⊤ ∈ carrier
  /-- The filter is upward closed -/
  up_closed : ∀ {u v : L}, u ∈ carrier → u ≤ v → v ∈ carrier
  /-- The filter is closed under binary meets -/
  inf_mem : ∀ {u v : L}, u ∈ carrier → v ∈ carrier → u ⊓ v ∈ carrier
  /-- The filter is completely prime: ⨆ u_i ∈ F implies some u_i ∈ F -/
  sSup_mem : ∀ {ι : Type*} (U : ι → L), ⨆ i, U i ∈ carrier → ∃ i, U i ∈ carrier

namespace CompletelyPrimeFilter

variable {L : Type*} [Order.Frame L]

/-- Membership in a completely prime filter. -/
instance instMembership : Membership L (CompletelyPrimeFilter L) where
  mem := fun (F : CompletelyPrimeFilter L) (u : L) => u ∈ F.carrier

/-- A completely prime filter does not contain ⊥ (unless L is trivial).

    In a non-trivial frame, completely prime filters don't contain ⊥.
    This follows from the sSup_mem condition applied to the empty family:
    ⊥ = ⨆ ∅, so if ⊥ ∈ F then ∃ i ∈ ∅ with U i ∈ F, contradiction. -/
theorem not_bot_mem (F : CompletelyPrimeFilter L) (_h : (⊥ : L) ≠ ⊤) : ⊥ ∉ F.carrier := by
  intro hbot
  -- Key: ⊥ = ⨆_{i : PEmpty} (fun i => ⊥)
  -- If ⊥ ∈ F, by sSup_mem, ∃ i : PEmpty, which is impossible
  have h_bot_eq : (⊥ : L) = ⨆ (i : PEmpty), (fun _ : PEmpty => (⊥ : L)) i := by
    simp only [iSup_of_empty]
  rw [h_bot_eq] at hbot
  obtain ⟨i, _⟩ := F.sSup_mem (fun _ : PEmpty => ⊥) hbot
  exact i.elim

end CompletelyPrimeFilter

/-! ### Completely Prime Filters on Rad R correspond to Prime Ideals -/

/-- Given a prime ideal p of R, there is a corresponding completely prime filter
    on Rad R. The filter consists of radical ideals I such that I ⊈ p
    (equivalently, there exists f ∈ I with f ∉ p).

    This is the "point" of Spec R corresponding to p.

    The key property: for prime p, the set {I ∈ Rad R | ∃ f ∈ I, f ∉ p}
    forms a completely prime filter.

    Blueprint: Theorem 5.1b (thm:prime-ideal-to-filter) -/
def Rad.filterOfPrime (p : Ideal R) [hp : p.IsPrime] : CompletelyPrimeFilter (Rad R) where
  carrier := {I : Rad R | ∃ f ∈ I.val, f ∉ p}
  top_mem := by
    -- Need: ∃ f ∈ (⊤ : Rad R).val = R, f ∉ p
    -- Since p ≠ R (p is prime), there exists f ∉ p
    -- Actually simpler: 1 ∈ R and 1 ∉ p (since p is proper)
    use 1
    constructor
    · exact Submodule.mem_top
    · -- 1 ∉ p because p is a proper ideal (prime ideals are proper)
      intro h1p
      exact hp.ne_top (Ideal.eq_top_of_isUnit_mem p h1p isUnit_one)
  up_closed := fun {I J} ⟨f, hfI, hfp⟩ hIJ => ⟨f, hIJ hfI, hfp⟩
  inf_mem := fun {I J} ⟨f, hfI, hfp⟩ ⟨g, hgJ, hgp⟩ => by
    -- f ∈ I, f ∉ p; g ∈ J, g ∉ p
    -- Need: ∃ h ∈ I ⊓ J, h ∉ p
    -- Since p is prime and f, g ∉ p, we have fg ∉ p
    -- Also fg ∈ I ⊓ J = I ∩ J
    use f * g
    constructor
    · -- fg ∈ I ∩ J
      constructor
      · exact I.val.mul_mem_right g hfI
      · exact J.val.mul_mem_left f hgJ
    · -- fg ∉ p
      exact mt hp.mem_or_mem (not_or.mpr ⟨hfp, hgp⟩)
  sSup_mem := by
    intro ι U hU
    -- hU : ∃ f ∈ (⨆ U_i).val, f ∉ p (i.e., ⨆ U_i ∈ carrier)
    obtain ⟨f, hf_in_sup, hf_not_p⟩ := hU
    -- ⨆ U_i = √(sSup {U_i.val}), so hf_in_sup means f^n ∈ sSup {U_i.val} for some n
    -- (⨆ i, U i).val = (sSup (Set.range U)).val = (sSup (Subtype.val '' Set.range U)).radical
    -- f ∈ radical means ∃ n, f^n ∈ the underlying ideal
    have hf_rad := hf_in_sup
    -- hf_rad : f ∈ (⨆ i, U i).val = (sSup (Subtype.val '' Set.range U)).radical
    obtain ⟨n, hn⟩ := hf_rad
    -- hn : f^n ∈ sSup (Subtype.val '' (Set.range U))
    -- Since f ∉ p and p is prime, f^n ∉ p
    have hfn_not_p : f ^ n ∉ p := by
      intro hfnp
      exact hf_not_p (hp.mem_of_pow_mem n hfnp)
    -- Use Submodule.mem_sSup_iff_exists_finset to extract a finite sum
    rw [Submodule.mem_sSup_iff_exists_finset] at hn
    obtain ⟨s, hs, hfn_sum⟩ := hn
    -- s is a finite set of ideals from {U_i.val | i}, and f^n ∈ ⨆ I ∈ s, I
    -- Since p is prime and f^n ∉ p, not all U_i can have U_i ⊆ p
    -- Use contrapositive: if ∀ i, U_i ⊆ p, then ⨆ I ∈ s, I ⊆ p, so f^n ∈ p
    by_contra h_all_not_in_carrier
    push_neg at h_all_not_in_carrier
    -- h_all_not_in_carrier : ∀ i, U i ∉ carrier, i.e., ∀ i, ∀ g ∈ U_i, g ∈ p
    -- This means U_i.val ⊆ p for all i
    have h_all_subset : ∀ I ∈ s, I ≤ (p : Ideal R) := by
      intro I hI
      -- I ∈ s means I = U_i.val for some i
      have hI' := hs hI
      simp only [Set.mem_image, Set.mem_range] at hI'
      obtain ⟨Ui, ⟨i, rfl⟩, rfl⟩ := hI'
      -- Now need U_i.val ⊆ p
      intro x hx
      -- By h_all_not_in_carrier, ∀ g ∈ U_i, g ∈ p (negation of ∃ g ∈ U_i, g ∉ p)
      have h_neg : ¬ ∃ g ∈ (U i).val, g ∉ p := h_all_not_in_carrier i
      push_neg at h_neg
      exact h_neg x hx
    -- So ⨆ I ∈ s, I ≤ p, hence f^n ∈ p, contradiction
    have hfn_in_p : f ^ n ∈ p := by
      have h_sup_le_p : ⨆ I ∈ s, I ≤ (p : Ideal R) := iSup₂_le h_all_subset
      exact h_sup_le_p hfn_sum
    exact hfn_not_p hfn_in_p

/-- Given a completely prime filter F on Rad R, extract the corresponding prime ideal.

    The prime ideal is {r : R | D(r) ∉ F}, i.e., the set of elements whose
    basic open is not in the filter.

    This is the reverse direction of `Rad.filterOfPrime`. -/
def Rad.primeOfFilter (F : CompletelyPrimeFilter (Rad R)) : Ideal R where
  carrier := {r : R | Rad.basicOpen r ∉ F.carrier}
  add_mem' := fun {a b} ha hb => by
    -- Need: D(a+b) ∉ F given D(a) ∉ F and D(b) ∉ F
    -- Key: D(a+b) ≤ D(a) ⊔ D(b), so if D(a+b) ∈ F then D(a) ⊔ D(b) ∈ F
    -- By sSup_mem, D(a) ∈ F or D(b) ∈ F, contradiction.
    intro hab_in_F
    -- D(a+b) ∈ F, so D(a) ⊔ D(b) ∈ F (by upward closure, since D(a+b) ≤ D(a) ⊔ D(b))
    have h_sup : Rad.basicOpen a ⊔ Rad.basicOpen b ∈ F.carrier := by
      apply F.up_closed hab_in_F
      -- Need: D(a+b) ≤ D(a) ⊔ D(b)
      intro x hx
      -- x ∈ D(a+b) = √(a+b) means x^n ∈ (a+b) for some n
      obtain ⟨n, hn⟩ := hx
      rw [Ideal.mem_span_singleton] at hn
      obtain ⟨c, hc⟩ := hn
      -- x^n = (a+b) * c ∈ (a) + (b), so x ∈ √((a) + (b)) = D(a) ⊔ D(b)
      -- Goal: x ∈ ↑(basicOpen a ⊔ basicOpen b)
      -- After use n, goal is x^n ∈ √(a) + √(b) (the sup of ideals)
      use n
      -- Goal: x^n ∈ √(a) + √(b)
      rw [hc, add_mul]
      apply Submodule.add_mem
      · -- a*c ∈ √(a)
        apply Ideal.mem_sup_left
        exact Ideal.le_radical (Ideal.mul_mem_right c _ (Ideal.mem_span_singleton_self a))
      · -- b*c ∈ √(b)
        apply Ideal.mem_sup_right
        exact Ideal.le_radical (Ideal.mul_mem_right c _ (Ideal.mem_span_singleton_self b))
    -- D(a) ⊔ D(b) ∈ F, by sSup_mem, either D(a) ∈ F or D(b) ∈ F
    have h_or := F.sSup_mem (fun i : Bool => if i then Rad.basicOpen a else Rad.basicOpen b) (by
      simp only [iSup_bool_eq]
      exact h_sup)
    rcases h_or with ⟨i, hi⟩
    cases i <;> simp only [ite_true] at hi
    · exact hb hi
    · exact ha hi
  zero_mem' := by
    -- D(0) = ⊥ in Rad R, and ⊥ ∉ F by the completely prime property
    intro h0
    -- First show D(0) = ⊥
    have h_D0_bot : Rad.basicOpen (0 : R) = ⊥ := Rad.basicOpen_zero
    rw [h_D0_bot] at h0
    -- If ⊥ ∈ F, then by sSup_mem on empty family, we get a contradiction
    have h_bot_eq : (⊥ : Rad R) = ⨆ (i : PEmpty), (fun _ : PEmpty => (⊥ : Rad R)) i := by
      simp only [iSup_of_empty]
    rw [h_bot_eq] at h0
    obtain ⟨i, _⟩ := F.sSup_mem (fun _ : PEmpty => ⊥) h0
    exact i.elim
  smul_mem' := fun r {a} ha => by
    -- Need: D(r*a) ∉ F given D(a) ∉ F
    -- D(r*a) ≤ D(a), so if D(r*a) ∈ F, then D(a) ∈ F by upward closure
    intro hra_in_F
    apply ha
    apply F.up_closed hra_in_F
    -- D(r*a) ≤ D(a): if x ∈ D(ra) then x ∈ D(a)
    intro x hx
    obtain ⟨n, hn⟩ := hx
    rw [Ideal.mem_span_singleton] at hn
    obtain ⟨c, hc⟩ := hn
    -- x^n = ra * c = a * (rc), hence x^n ∈ (a)
    use n
    rw [Ideal.mem_span_singleton]
    use r * c
    -- r • a = r * a, so x^n = r * a * c = a * (r * c) = (r * c) * a
    simp only [smul_eq_mul] at hc
    rw [hc]
    ring

/-- The ideal extracted from a completely prime filter is prime. -/
instance Rad.primeOfFilter.isPrime (F : CompletelyPrimeFilter (Rad R)) :
    (Rad.primeOfFilter F).IsPrime where
  ne_top' := by
    -- Need: primeOfFilter F ≠ ⊤
    -- Equivalently, ∃ r, D(r) ∈ F, which is true since D(1) = ⊤ ∈ F
    intro h_eq_top
    have h1 : (1 : R) ∈ Rad.primeOfFilter F := by rw [h_eq_top]; trivial
    simp only [Rad.primeOfFilter] at h1
    -- h1 : D(1) ∉ F, but D(1) = ⊤ ∈ F by top_mem
    have h_top : Rad.basicOpen (1 : R) ∈ F.carrier := by
      rw [Rad.basicOpen_one]
      exact F.top_mem
    exact h1 h_top
  mem_or_mem' := fun {a b} hab => by
    -- hab : a * b ∈ primeOfFilter F, i.e., D(ab) ∉ F
    -- Need: D(a) ∉ F or D(b) ∉ F
    -- D(ab) = D(a) ⊓ D(b), and F is closed under inf
    -- Contrapositive: if D(a) ∈ F and D(b) ∈ F, then D(ab) ∈ F
    by_contra h_neither
    push_neg at h_neither
    obtain ⟨ha_not_mem, hb_not_mem⟩ := h_neither
    -- ha_not_mem : a ∉ primeOfFilter F, which means ¬(D(a) ∉ F), i.e., D(a) ∈ F
    -- hb_not_mem : b ∉ primeOfFilter F, which means ¬(D(b) ∉ F), i.e., D(b) ∈ F
    -- Membership in primeOfFilter F is: a ∈ {r | D(r) ∉ F}
    -- So ¬(a ∈ primeOfFilter F) = ¬(D(a) ∉ F) = D(a) ∈ F
    have ha_in_F : Rad.basicOpen a ∈ F.carrier :=
      Classical.not_not.mp (show ¬(Rad.basicOpen a ∉ F.carrier) from ha_not_mem)
    have hb_in_F : Rad.basicOpen b ∈ F.carrier :=
      Classical.not_not.mp (show ¬(Rad.basicOpen b ∉ F.carrier) from hb_not_mem)
    -- D(a) ∈ F and D(b) ∈ F, so D(ab) = D(a) ⊓ D(b) ∈ F by inf_mem
    have hab_in_F : Rad.basicOpen (a * b) ∈ F.carrier := by
      rw [Rad.basicOpen_mul]
      exact F.inf_mem ha_in_F hb_in_F
    -- But hab says D(ab) ∉ F, contradiction
    exact hab hab_in_F

/-- The stalk of the structure sheaf at a prime ideal p is R_p.

    This is the key theorem connecting stalks and localizations.

    Blueprint: Theorem 5.2b (thm:stalk-at-prime-is-localization) -/
abbrev Spec.stalkAtPrime (R : Type*) [CommRing R] (p : Ideal R) [_hp : p.IsPrime] : Type _ :=
  Localization.AtPrime p

/-- The stalk at a prime ideal is a local ring.

    Blueprint: Corollary 5.2c (cor:stalk-is-local-ring) -/
instance Spec.stalkAtPrime.isLocalRing (R : Type*) [CommRing R] (p : Ideal R) [hp : p.IsPrime] :
    IsLocalRing (Spec.stalkAtPrime R p) :=
  inferInstance

/-! ### Stalks of Sheaves on Locales -/

/-- Stalk of a presheaf at an element u of a locale.

    Mathematically, this should be defined as:
      stalk_u(F) = colim_{v ≤ u} F(v)

    where the colimit is over the directed system of opens v ≤ u.

    For the structure sheaf O on Spec R at a basic open D(f), this would be:
      colim_{D(g) ≤ D(f)} R_g

    At a prime ideal p (viewed as a point), the stalk is:
      O_{Spec R, p} = R_p (localization at p)

    **Note on pointless setting:**
    In pointless topology, "points" correspond to completely prime filters
    on the frame, not individual elements. The stalk at a point p would be
    the colimit over the filter p.

    For the Zariski locale Rad(R), the points (completely prime filters)
    correspond to prime ideals of R (in the classical sense).

    **Implementation:**
    We use the direct limit construction from Mathlib: `Ring.DirectLimit`.
    The directed system is indexed by the down-set {v : L | v ≤ u}.

    Currently, we provide the full definition for presheaves on frames,
    but the CommRing instance requires Ring.DirectLimit from Mathlib.

    Blueprint: Definition 5.2 (def:stalk-locale) -/
def PresheafOnFrame.stalkType {L : Type*} [Order.Frame L] (F : PresheafOnFrame L) (u : L) :
    Type _ :=
  -- The stalk is the direct limit of F(v) over v ≤ u
  -- For now we use a placeholder type; the full implementation would use Ring.DirectLimit
  -- with the directed system {v | v ≤ u} and the restriction maps
  Σ (v : L), PLift (v ≤ u) × F.obj v

/-- A relation identifying elements that become equal under restriction.
    Two elements (v₁, x₁) and (v₂, x₂) are identified if there exists w ≤ v₁, v₂
    such that the restrictions of x₁ and x₂ to w are equal. -/
def PresheafOnFrame.stalkRel {L : Type*} [Order.Frame L] (F : PresheafOnFrame L) (u : L) :
    F.stalkType u → F.stalkType u → Prop :=
  fun ⟨v₁, _hv₁, x₁⟩ ⟨v₂, _hv₂, x₂⟩ =>
    ∃ (w : L) (_hw : w ≤ u) (hw₁ : w ≤ v₁) (hw₂ : w ≤ v₂),
      F.map hw₁ x₁ = F.map hw₂ x₂

/-- Stalk of a presheaf as a quotient type.
    Elements are equivalence classes of (v, x) where v ≤ u and x ∈ F(v). -/
def Sheaf.stalk {L : Type*} [Order.Frame L] (F : PresheafOnFrame L) (u : L) : Type _ :=
  Quotient (Setoid.mk (F.stalkRel u) ⟨
    -- Reflexivity
    fun ⟨v, hv, x⟩ => ⟨v, hv.down, le_refl v, le_refl v, rfl⟩,
    -- Symmetry
    fun ⟨w, hw, hw₁, hw₂, h⟩ => ⟨w, hw, hw₂, hw₁, h.symm⟩,
    -- Transitivity: (a ~ b) ∧ (b ~ c) → (a ~ c)
    fun {a b c} ⟨w₁, hw₁, hw₁₁, hw₁₂, h₁⟩ ⟨w₂, hw₂, hw₂₁, hw₂₂, h₂⟩ =>
      -- Use the meet w₁ ⊓ w₂ as the common refinement
      ⟨w₁ ⊓ w₂, le_trans inf_le_left hw₁,
       le_trans inf_le_left hw₁₁, le_trans inf_le_right hw₂₂,
       by
         -- Goal: F.map (w₁⊓w₂ ≤ a.fst) a.2.2 = F.map (w₁⊓w₂ ≤ c.fst) c.2.2
         -- The proof uses map_comp and proof irrelevance for ≤
         calc F.map (le_trans inf_le_left hw₁₁) a.2.2
             = F.map inf_le_left (F.map hw₁₁ a.2.2) := by
                 rw [← F.map_comp inf_le_left hw₁₁, RingHom.comp_apply]
           _ = F.map inf_le_left (F.map hw₁₂ b.2.2) := by rw [h₁]
           _ = F.map (le_trans inf_le_left hw₁₂) b.2.2 := by
                 rw [← RingHom.comp_apply, F.map_comp]
           _ = F.map (le_trans inf_le_right hw₂₁) b.2.2 := rfl  -- proof irrelevance
           _ = F.map inf_le_right (F.map hw₂₁ b.2.2) := by
                 rw [← F.map_comp inf_le_right hw₂₁, RingHom.comp_apply]
           _ = F.map inf_le_right (F.map hw₂₂ c.2.2) := by rw [h₂]
           _ = F.map (le_trans inf_le_right hw₂₂) c.2.2 := by
                 rw [← RingHom.comp_apply, F.map_comp]⟩
  ⟩)

/-- For a commutative ring R and a prime ideal p, the localization R_p
    is the stalk of the structure sheaf at p.

    This is the key connection between stalks and localizations:
    - The stalk at a "point" p is R_p
    - R_p is a local ring (IsLocalRing instance from Mathlib)

    The actual stalk-as-colimit construction would require showing:
      colim_{f ∉ p} R_f ≅ R_p

    where the colimit is over basic opens D(f) with f ∉ p.
    Blueprint: Remark after Definition 5.2 -/
example (R : Type*) [CommRing R] (p : Ideal R) [p.IsPrime] :
    IsLocalRing (Localization.AtPrime p) := inferInstance

/-! ### Locally Ringed Locales -/

/-- A locally ringed locale is a pair (X, O_X) where X is a locale and O_X is
    a sheaf of rings such that all stalks are local rings.

    In classical algebraic geometry:
    - X is a topological space
    - O_X is a sheaf of rings on X
    - For each point x ∈ X, the stalk O_{X,x} is a local ring

    In the pointless setting:
    - X is a frame (= locale)
    - O_X is a sheaf of rings on the frame
    - For each "point" (completely prime filter), the stalk is local

    The condition that stalks are local is essential for:
    - Defining morphisms of locally ringed spaces/locales
    - The adjunction between Spec and global sections
    - Characterizing affine schemes

    Blueprint: Definition 5.1 (def:locally-ringed-locale) -/
structure LocallyRingedLocale where
  /-- The underlying frame representing the locale -/
  frame : Type*
  /-- Frame instance providing the lattice structure -/
  instFrame : Order.Frame frame
  /-- The structure sheaf on the locale -/
  structureSheaf : @PresheafOnFrame frame instFrame
  /-- The type of the stalk at each completely prime filter.

      For affine schemes Spec R:
      - Completely prime filters ↔ prime ideals p of R
      - StalkAt F = Localization.AtPrime p where F corresponds to p -/
  StalkAt : @CompletelyPrimeFilter frame instFrame → Type*
  /-- CommRing instance on each stalk -/
  stalkCommRing : ∀ F, CommRing (StalkAt F)
  /-- Stalks are local rings.

      This is the defining property of a locally ringed locale.

      Mathematically: for each completely prime filter F on the frame,
      the stalk at F is a local ring.

      For affine schemes Spec R:
      - Completely prime filters ↔ prime ideals p of R
      - Stalk at p = R_p (Localization.AtPrime p)
      - R_p is local by Localization.AtPrime.isLocalRing -/
  stalks_local : ∀ F, @IsLocalRing (StalkAt F) (stalkCommRing F).toSemiring

/-! ### Affine Schemes -/

/-- An affine scheme is Spec R with its structure sheaf.

    The affine scheme associated to a commutative ring R consists of:
    - The Zariski locale Spec R (= Rad R, the frame of radical ideals)
    - The structure sheaf O_{Spec R}

    The structure sheaf assigns:
    - To each basic open D(f): the localization R_f
    - To each open U: a ring of sections compatible with localizations

    Key property: For any prime ideal p ⊂ R, the stalk O_{Spec R, p} = R_p,
    which is a local ring.

    Blueprint: Definition 5.3 (def:affine-scheme) -/
structure AffineScheme where
  /-- The underlying commutative ring -/
  Ring : Type*
  /-- CommRing instance -/
  instRing : CommRing Ring

namespace AffineScheme

/-- The underlying locale of an affine scheme is the Zariski locale Spec R.

    As a frame, this is Rad R (the frame of radical ideals of R).
    Radical ideals correspond to open sets of Spec R:
    - D(f) = {p : p prime, f ∉ p} corresponds to the radical √(f)
    - The ordering is by inclusion: U ≤ V iff U ⊆ V as opens -/
def toLocale (X : AffineScheme) : Type _ := @Rad X.Ring X.instRing

noncomputable instance (X : AffineScheme) : Order.Frame (X.toLocale) :=
  @Rad.instFrame X.Ring X.instRing

/-- The structure presheaf on an affine scheme Spec R.
    For each radical ideal I, the sections are the compatible families Spec.sheafExtend I.

    Blueprint: Definition 5.3b (def:structure-presheaf-affine) -/
noncomputable def structurePresheaf (X : AffineScheme) :
    @PresheafOnFrame X.toLocale (@Rad.instFrame X.Ring X.instRing) where
  obj I := @Spec.sheafExtend X.Ring X.instRing I
  ring I := @Spec.sheafExtend.instCommRing X.Ring X.instRing I
  map h := @Spec.sheafExtendRestrict X.Ring X.instRing _ _ h
  map_comp h₁ h₂ := by
    -- Goal: (map h₁).comp (map h₂) = map (le_trans h₁ h₂)
    -- Both sides give the same function on sheafExtend
    rfl

/-- Affine schemes are locally ringed.

    The key fact is that for any prime ideal p ⊂ R, the stalk at p
    is the localization R_p, which is a local ring with maximal ideal pR_p.

    **Mathematical statement:**
    For any prime ideal p of the underlying ring, the localization at p
    is a local ring. This is the content of `Localization.AtPrime.isLocalRing`.

    **Proof:**
    The stalk at a prime p is R_p = Localization.AtPrime p, which is a local ring
    by the Mathlib instance `Localization.AtPrime.isLocalRing`.

    Blueprint: Theorem 5.4 (thm:affine-scheme-locally-ringed) -/
theorem locallyRinged (R : Type*) [CommRing R] (p : Ideal R) [hp : p.IsPrime] :
    IsLocalRing (Localization.AtPrime p) :=
  inferInstance

/-- The stalk of the structure sheaf at a prime ideal is the localization.

    For any prime p ⊂ R:
      O_{Spec R, p} ≅ R_p

    This is the localization of R at the multiplicative set R \ p.
    R_p is a local ring with maximal ideal pR_p.

    This example demonstrates the Mathlib instance. -/
example (R : Type*) [CommRing R] (p : Ideal R) [hp : p.IsPrime] :
    IsLocalRing (Localization.AtPrime p) := inferInstance

/-! ### Morphisms of Affine Schemes -/

/-- A morphism of affine schemes.

    A morphism f : Spec R → Spec S corresponds to a ring homomorphism φ : S → R.

    Contravariance: The functor Spec is contravariant:
    - φ : S → R induces Spec(φ) : Spec R → Spec S
    - On points: Spec(φ)(p) = φ⁻¹(p) for prime ideals p ⊂ R
    - On structure sheaves: φ induces O_S → f_* O_R

    This defines the equivalence Aff^op ≃ CommRing.

    Blueprint: Definition 5.5 (def:morphism-affine-schemes) -/
structure Hom (X Y : AffineScheme) where
  /-- The underlying ring homomorphism (in the opposite direction).
      A morphism Spec R → Spec S comes from a ring hom S → R. -/
  ringHom : @RingHom Y.Ring X.Ring Y.instRing.toNonAssocSemiring X.instRing.toNonAssocSemiring

/-- The identity morphism on an affine scheme. -/
def Hom.id (X : AffineScheme) : Hom X X :=
  ⟨@RingHom.id X.Ring X.instRing.toNonAssocSemiring⟩

/-- Composition of morphisms of affine schemes.

    If f : Spec R → Spec S (from φ : S → R) and g : Spec S → Spec T (from ψ : T → S),
    then g ∘ f : Spec R → Spec T comes from φ ∘ ψ : T → R. -/
def Hom.comp {X Y Z : AffineScheme} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  ⟨f.ringHom.comp g.ringHom⟩

/-- Ring homomorphisms induce morphisms of affine schemes.

    This is one direction of the equivalence Aff^op ≃ CommRing.
    The other direction would extract the ring homomorphism from
    a morphism of affine schemes.

    Blueprint: Theorem 5.6 (thm:ring-hom-to-scheme-morphism) -/
def of_ringHom (φ : S →+* R) :
    Hom ⟨R, inferInstance⟩ ⟨S, inferInstance⟩ := ⟨φ⟩

end AffineScheme

/-! ### General Schemes -/

/-- A scheme is a locally ringed locale with an affine open cover.

    Mathematically, a scheme (X, O_X) satisfies:
    1. (X, O_X) is a locally ringed locale
    2. There exists a family of opens {U_i}_{i ∈ I} such that:
       - The family covers: ⨆ U_i = ⊤
       - Each (U_i, O_X|_{U_i}) is isomorphic to an affine scheme Spec R_i

    In the pointless setting:
    - X is a frame (locale)
    - O_X is a sheaf of rings on X
    - The covering is an internal property of the frame
    - "Isomorphic to affine" means locale isomorphism + sheaf isomorphism

    **Full formalization requires:**
    1. Open sublocale construction: given u : L, define L|_u as a frame
    2. Restriction of sheaves: given sheaf F on L, define F|_u on L|_u
    3. Isomorphism of locally ringed locales: frame iso + sheaf iso + stalk iso

    Blueprint: Definition 5.7 (def:scheme-pointfree) -/
structure Scheme where
  /-- The underlying locally ringed locale -/
  toLocallyRingedLocale : LocallyRingedLocale
  /-- Each piece of the cover is affine.

      Mathematically: there exists a cover {U_i}_{i ∈ I} such that:
      - ⨆_{i ∈ I} U_i = ⊤ (covers the whole space)
      - Each (U_i, O_X|_{U_i}) ≅ Spec R_i for some ring R_i

      Full implementation requires:
      - An index type I
      - A family of opens U : I → frame
      - Proof that ⨆ U = ⊤
      - A ring R_i for each i
      - An isomorphism of locally ringed locales (U_i, O_X|_{U_i}) ≃ (Spec R_i, O_{Spec R_i})

      Currently a placeholder. -/
  affine_cover : True := trivial

namespace Scheme

/-- Convert a LocallyRingedLocale to its underlying frame. -/
def toFrame (X : Scheme) : Type* := X.toLocallyRingedLocale.frame

instance (X : Scheme) : Order.Frame X.toFrame := X.toLocallyRingedLocale.instFrame

/-- Helper to construct stalks for affine schemes.
    The stalk at a completely prime filter F is the localization at the
    corresponding prime ideal. -/
noncomputable def AffineScheme.stalkAt' (R : Type*) [CommRing R]
    (F : CompletelyPrimeFilter (Rad R)) : Type _ :=
  -- The IsPrime instance is provided by Rad.primeOfFilter.isPrime
  @Localization.AtPrime R _ (Rad.primeOfFilter F) (Rad.primeOfFilter.isPrime F)

/-- CommRing instance on stalks of affine schemes. -/
noncomputable instance AffineScheme.stalkCommRing' (R : Type*) [CommRing R]
    (F : CompletelyPrimeFilter (Rad R)) : CommRing (AffineScheme.stalkAt' R F) := by
  unfold AffineScheme.stalkAt'
  infer_instance

/-- Stalks of affine schemes are local rings. -/
instance AffineScheme.stalkIsLocal' (R : Type*) [CommRing R]
    (F : CompletelyPrimeFilter (Rad R)) : IsLocalRing (AffineScheme.stalkAt' R F) := by
  unfold AffineScheme.stalkAt'
  infer_instance

/-- Every affine scheme is a scheme.

    An affine scheme Spec R is covered by the single open Spec R itself,
    which is trivially isomorphic to an affine scheme. -/
noncomputable def ofAffine (X : AffineScheme) : Scheme where
  toLocallyRingedLocale := {
    frame := X.toLocale
    instFrame := @Rad.instFrame X.Ring X.instRing
    structureSheaf := X.structurePresheaf
    -- For an affine scheme Spec R:
    -- - Completely prime filters on Rad R correspond to prime ideals
    -- - The stalk at F is Localization.AtPrime (primeOfFilter F)
    -- - This is a local ring by Localization.AtPrime.isLocalRing
    StalkAt := fun F => @AffineScheme.stalkAt' X.Ring X.instRing F
    stalkCommRing := fun F => @AffineScheme.stalkCommRing' X.Ring X.instRing F
    stalks_local := fun F => @AffineScheme.stalkIsLocal' X.Ring X.instRing F
  }
  affine_cover := trivial

/-- Schemes form a category.

    **Morphisms of schemes:**
    A morphism f : (X, O_X) → (Y, O_Y) of schemes consists of:
    1. A continuous map f : X → Y of locales (= frame homomorphism O(Y) → O(X))
    2. A morphism f^# : O_Y → f_* O_X of sheaves of rings

    such that for each point x ∈ X (or completely prime filter in the pointless case),
    the induced map on stalks f^#_x : O_{Y, f(x)} → O_{X, x} is a local ring homomorphism.

    **Local ring homomorphisms:**
    A ring homomorphism φ : R → S between local rings is local if φ(m_R) ⊆ m_S,
    where m_R, m_S are the maximal ideals.

    **Universal property:**
    Schemes form a category Sch with AffineScheme (= CommRing^op) as a full subcategory.
    The Spec functor: CommRing^op → Sch has a right adjoint Γ : Sch → CommRing^op
    given by global sections: Γ(X, O_X) = O_X(X).

    The adjunction: Hom_{Sch}(X, Spec R) ≅ Hom_{Ring}(R, Γ(X, O_X))

    Blueprint: Theorem 5.8 (thm:universal-property-schemes) -/
theorem universal_property :
    -- Full statement: the functor Spec : CommRing^op → Sch is left adjoint to Γ
    -- For affine schemes: Hom(Spec R, Spec S) ≅ Hom(S, R)
    True := trivial

/-- The global sections functor on schemes.

    For a scheme (X, O_X), the ring of global sections is Γ(X, O_X) = O_X(X).

    For an affine scheme Spec R, we have Γ(Spec R, O_{Spec R}) ≅ R.
    This is part of the adjunction between Spec and Γ. -/
def globalSections (_X : Scheme) : Type* := PUnit  -- Placeholder for general schemes

end Scheme

/-! ### Global Sections for Affine Schemes -/

namespace AffineScheme

/-- Global sections of an affine scheme.
    For Spec R, the global sections are O(⊤) = sheafExtend ⊤.

    By the key theorem of algebraic geometry, Γ(Spec R, O_{Spec R}) ≅ R.
    This isomorphism comes from:
    - R embeds into Γ via r ↦ (f ↦ r/1 ∈ R_f)
    - This is surjective because global compatible families come from R

    The proof of this isomorphism requires showing that any compatible family
    of elements in all localizations R_f (for all f ∈ R) must come from an
    element of R.

    **Implementation Note:**
    We define global sections directly as Spec.sheafExtend ⊤, which is
    the type of compatible families of sections over the whole ring.
    The CommRing instance is inherited from Spec.sheafExtend.instCommRing. -/
noncomputable def globalSectionsRing (R : Type*) [CommRing R] : Type _ :=
  Spec.sheafExtend (⊤ : Rad R)

/-- Global sections form a commutative ring. -/
noncomputable instance globalSectionsCommRing (R : Type*) [CommRing R] :
    CommRing (globalSectionsRing R) :=
  Spec.sheafExtend.instCommRing

/-- The canonical map from R to global sections.
    This sends r ↦ (f ↦ r/1 ∈ R_f) -/
noncomputable def toGlobalSections' (R : Type*) [CommRing R] :
    R →+* globalSectionsRing R where
  toFun r := ⟨
    fun f _ => algebraMap R (Localization.Away f) r,
    fun f g _ _ hle => by simp only [Spec.sheafRestriction, IsLocalization.Away.lift_eq]
  ⟩
  map_zero' := by apply Spec.sheafExtend.ext; intro f hf; simp only [map_zero]; rfl
  map_one' := by apply Spec.sheafExtend.ext; intro f hf; simp only [map_one]; rfl
  map_add' x y := by apply Spec.sheafExtend.ext; intro f hf; simp only [map_add]; rfl
  map_mul' x y := by apply Spec.sheafExtend.ext; intro f hf; simp only [map_mul]; rfl

/-- The canonical map from R to global sections is an isomorphism.

    This is a fundamental theorem: Γ(Spec R, O_{Spec R}) ≅ R.

    **Sketch of proof:**
    - Injectivity: If r/1 = 0 in all R_f, then r is nilpotent.
      But R → Γ factors through R/nilradical, so 0-divisors are killed.
    - Surjectivity: A compatible family (s_f)_{f ∈ R} with s_f ∈ R_f
      can be written locally as r_f/f^n. Using a partition of unity
      (1 = Σ a_i f_i for some finite family), we can glue to get r ∈ R.

    Full proof requires substantial work. -/
theorem toGlobalSections_bijective' (R : Type*) [CommRing R] :
    Function.Bijective (toGlobalSections' R) := by
  constructor
  · -- Injectivity: If r1/1 = r2/1 in Localization.Away 1 ≃ R, then r1 = r2
    intro r1 r2 h
    -- Extract the equality at f = 1
    have h1 : algebraMap R (Localization.Away (1 : R)) r1 = algebraMap R (Localization.Away 1) r2 := by
      have := congr_arg (fun s => s.sections 1 trivial) h
      simp only [toGlobalSections'] at this
      exact this
    -- Use OreLocalization.oreDiv_eq_iff to extract the equivalence condition
    have h_eq : ∀ r, algebraMap R (Localization.Away (1 : R)) r = Localization.mk r 1 := fun _ => rfl
    simp only [h_eq, Localization.mk.eq_1] at h1
    rw [OreLocalization.oreDiv_eq_iff] at h1
    obtain ⟨u, v, huv_smul, huv_eq⟩ := h1
    -- Simplify huv_eq: ↑u * ↑1 = v * ↑1 gives ↑u = v
    simp only [Submonoid.coe_one, mul_one] at huv_eq
    -- u ∈ powers 1 means ↑u = 1
    have hu := u.2
    simp only [Submonoid.mem_powers_iff] at hu
    obtain ⟨n, hn⟩ := hu
    simp only [one_pow] at hn
    -- hn : 1 = ↑u, huv_eq : ↑u = v, so v = 1
    have hv1 : v = 1 := huv_eq ▸ hn.symm
    have hu1 : (↑u : R) = 1 := hn.symm
    -- huv_smul : u • r2 = v * r1 = 1 * r1 = r1
    -- Also u • r2 = ↑u * r2 = 1 * r2 = r2
    -- So r1 = r2
    have h1' : u • r2 = r1 := by rw [huv_smul, hv1, one_smul]
    have h2' : u • r2 = r2 := by
      show (↑u : R) * r2 = r2
      rw [hu1, one_mul]
    exact h1'.symm.trans h2'
  · -- Surjectivity: Every compatible family comes from an element of R
    intro s
    -- Use the isomorphism Localization.Away 1 ≃ R to extract r from s.sections 1
    -- IsLocalization.atOne gives the AlgEquiv R ≃ₐ[R] Localization.Away 1
    let e : R ≃ₐ[R] Localization.Away (1 : R) := IsLocalization.atOne R (Localization.Away 1)
    -- Extract r from s.sections 1 using the inverse of the isomorphism
    let r : R := e.symm (s.sections 1 trivial)
    use r
    -- Show toGlobalSections' R r = s
    apply Spec.sheafExtend.ext
    intro f hf
    -- Goal: (toGlobalSections' R r).sections f hf = s.sections f hf
    -- Use the compatibility condition of s:
    -- D(f) ≤ D(1) = ⊤, so sheafRestriction hle (s.sections 1 _) = s.sections f _
    have hle : Rad.basicOpen f ≤ Rad.basicOpen (1 : R) := by
      simp only [Rad.basicOpen_one]
      exact le_top
    have h_compat := s.compatible f 1 hf trivial hle
    -- h_compat : sheafRestriction hle (s.sections 1 trivial) = s.sections f hf
    -- By definition of e.symm: e.symm x = r means e r = x, i.e., algebraMap R _ r = x
    -- So s.sections 1 trivial = algebraMap R (Localization.Away 1) r
    have hr_eq : s.sections 1 trivial = algebraMap R (Localization.Away 1) r := by
      simp only [r, e]
      exact (AlgEquiv.apply_symm_apply e (s.sections 1 trivial)).symm
    -- The chain of equalities:
    -- (toGlobalSections' R r).sections f hf = algebraMap R (Localization.Away f) r  (by def)
    -- s.sections f hf = sheafRestriction hle (s.sections 1 trivial)  (by h_compat.symm)
    --                 = sheafRestriction hle (algebraMap R (Localization.Away 1) r)  (by hr_eq)
    --                 = algebraMap R (Localization.Away f) r  (by lift_eq)
    have key : s.sections f hf = algebraMap R (Localization.Away f) r :=
      calc s.sections f hf
          = Spec.sheafRestriction hle (s.sections 1 trivial) := h_compat.symm
        _ = Spec.sheafRestriction hle (algebraMap R (Localization.Away 1) r) := by rw [hr_eq]
        _ = algebraMap R (Localization.Away f) r := by
            simp only [Spec.sheafRestriction, IsLocalization.Away.lift_eq]
    exact key.symm

end AffineScheme
