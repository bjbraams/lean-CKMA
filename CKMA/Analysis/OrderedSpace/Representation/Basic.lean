/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.OrderedSpace.Bands.Lattice
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice

/-!
# AM spaces, AL spaces, KB spaces and weak units

An AM space is a normed lattice with `‖x ⊔ y‖ = max ‖x‖ ‖y‖` on the positive cone; an AM unit is
a positive vector `e` whose order interval `[-e, e]` is the closed unit ball. An AL space is a
normed lattice with `‖x + y‖ = ‖x‖ + ‖y‖` on the positive cone, and a KB space is one in which
increasing norm-bounded positive sequences converge in norm. A weak unit is a positive vector
whose disjoint complement is zero.

## Main definitions

* `CKMA.IsAMSpace`: the AM identity `‖x ⊔ y‖ = max ‖x‖ ‖y‖` on the positive cone.
* `CKMA.IsAMSpaceUnit`: positive unit whose order interval is the closed norm unit ball.
* `CKMA.IsALSpace`: the AL identity `‖x + y‖ = ‖x‖ + ‖y‖` on the positive cone.
* `CKMA.IsKBSpace`: norm convergence of increasing norm-bounded positive sequences.
* `CKMA.IsWeakUnit`: positive vector with zero disjoint complement.

## Main results

* `CKMA.IsAMSpaceUnit.abs_le_norm_smul`: `|x| ≤ ‖x‖ • e` for an AM unit `e`.
* `CKMA.IsAMSpaceUnit.norm_le_of_abs_le_smul`: `|x| ≤ c • e` with `c ≥ 0` gives `‖x‖ ≤ c`.
* `CKMA.IsAMSpaceUnit.isAMSpace`: a normed lattice with a solid norm and an AM unit is an AM
  space.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology Metric Set

/-- The maximum norm identity on the positive cone defining an AM space. -/
@[expose]
def IsAMSpace (E : Type*) [NormedAddCommGroup E] [Lattice E] : Prop :=
  ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x ⊔ y‖ = max ‖x‖ ‖y‖

/-- Defining property of `IsAMSpace`. -/
theorem isAMSpace_iff {E : Type*} [NormedAddCommGroup E] [Lattice E] :
    IsAMSpace E ↔ ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x ⊔ y‖ = max ‖x‖ ‖y‖ := Iff.rfl

/-- A positive vector whose order interval equals the closed norm unit ball. -/
@[expose]
def IsAMSpaceUnit {E : Type*} [NormedAddCommGroup E] [Lattice E] (e : E) : Prop :=
  0 ≤ e ∧ closedBall (0 : E) 1 = Icc (-e) e

/-- Defining property of `IsAMSpaceUnit`. -/
theorem isAMSpaceUnit_iff {E : Type*} [NormedAddCommGroup E] [Lattice E] {e : E} :
    IsAMSpaceUnit e ↔ 0 ≤ e ∧ closedBall (0 : E) 1 = Icc (-e) e := Iff.rfl

/-- Norm additivity on the positive cone defining an AL space. -/
@[expose]
def IsALSpace (E : Type*) [NormedAddCommGroup E] [Lattice E] : Prop :=
  ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖

/-- Defining property of `IsALSpace`. -/
theorem isALSpace_iff {E : Type*} [NormedAddCommGroup E] [Lattice E] :
    IsALSpace E ↔ ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖ := Iff.rfl

/-- The KB property, formulated with norm convergence of increasing bounded positive sequences. -/
@[expose]
def IsKBSpace (E : Type*) [NormedAddCommGroup E] [Lattice E] : Prop :=
  ∀ x : ℕ → E, Monotone x → (∀ n, 0 ≤ x n) →
    (∃ M : ℝ, ∀ n, ‖x n‖ ≤ M) → ∃ y : E, Tendsto x atTop (𝓝 y)

/-- Defining property of `IsKBSpace`. -/
theorem isKBSpace_iff {E : Type*} [NormedAddCommGroup E] [Lattice E] :
    IsKBSpace E ↔ ∀ x : ℕ → E, Monotone x → (∀ n, 0 ≤ x n) →
      (∃ M : ℝ, ∀ n, ‖x n‖ ≤ M) → ∃ y : E, Tendsto x atTop (𝓝 y) := Iff.rfl

/-- A weak unit: a positive vector whose disjoint complement is `{0}`. -/
@[expose]
def IsWeakUnit {E : Type*} [AddCommGroup E] [Lattice E] (u : E) : Prop :=
  0 ≤ u ∧ latticeDisjointComplement {u} ⊆ {0}

/-- Defining property of `IsWeakUnit`. -/
theorem isWeakUnit_iff {E : Type*} [AddCommGroup E] [Lattice E] {u : E} :
    IsWeakUnit u ↔ 0 ≤ u ∧ latticeDisjointComplement {u} ⊆ {0} := Iff.rfl

/-- A weak unit is nonnegative. -/
theorem IsWeakUnit.nonneg {E : Type*} [AddCommGroup E] [Lattice E] {u : E} (hu : IsWeakUnit u) :
    0 ≤ u :=
  hu.1

/-- Only zero is disjoint from a weak unit. -/
theorem IsWeakUnit.eq_zero_of_mem {E : Type*} [AddCommGroup E] [Lattice E] {u x : E}
    (hu : IsWeakUnit u) (hx : x ∈ latticeDisjointComplement {u}) : x = 0 :=
  hu.2 hx

section AMUnit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E]
  [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] {e : E}

/-- Every vector lies below the norm multiple of an AM unit: `|x| ≤ ‖x‖ • e`. -/
theorem IsAMSpaceUnit.abs_le_norm_smul (he : IsAMSpaceUnit e) (x : E) : |x| ≤ ‖x‖ • e := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hu : ‖‖x‖⁻¹ • x‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have hmem : ‖x‖⁻¹ • x ∈ Icc (-e) e := by
      rw [← he.2, mem_closedBall_iff_norm]
      simpa using hu.le
    have hz2 : -(‖x‖⁻¹ • x) ≤ e := by simpa using neg_le_neg hmem.1
    have habs : |‖x‖⁻¹ • x| ≤ e := sup_le hmem.2 hz2
    rw [abs_smul_of_lattice, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))] at habs
    have hmul := smul_le_smul_of_nonneg_left habs (norm_nonneg x)
    simpa [smul_smul, mul_inv_cancel₀ hn] using hmul

/-- For an AM unit `e` of a normed lattice with a solid norm, `|x| ≤ c • e` with `c ≥ 0` gives
`‖x‖ ≤ c`. -/
theorem IsAMSpaceUnit.norm_le_of_abs_le_smul [HasSolidNorm E] (he : IsAMSpaceUnit e) {x : E}
    {c : ℝ} (hc : 0 ≤ c) (hx : |x| ≤ c • e) : ‖x‖ ≤ c := by
  rcases hc.eq_or_lt with rfl | hc
  · have habs : |x| = 0 := le_antisymm (by simpa using hx) (abs_nonneg x)
    rw [← norm_abs_eq_norm, habs, norm_zero]
  · have hinv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
    have habs : |c⁻¹ • x| ≤ e := by
      rw [abs_smul_of_lattice, abs_of_nonneg hinv]
      calc c⁻¹ • |x| ≤ c⁻¹ • (c • e) := smul_le_smul_of_nonneg_left hx hinv
        _ = e := by rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    have hmem : c⁻¹ • x ∈ closedBall (0 : E) 1 := by
      rw [he.2]
      exact ⟨neg_le.mp ((neg_le_abs _).trans habs), (le_abs_self _).trans habs⟩
    rw [mem_closedBall_iff_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv,
      inv_mul_le_iff₀ hc, mul_one] at hmem
    exact hmem

/-- A normed lattice with a solid norm and an AM unit is an AM space. -/
theorem IsAMSpaceUnit.isAMSpace [HasSolidNorm E] (he : IsAMSpaceUnit e) : IsAMSpace E := by
  intro x y hx hy
  have hxy : 0 ≤ x ⊔ y := le_sup_of_le_left hx
  refine le_antisymm ?_ (max_le ?_ ?_)
  · have hle : ∀ z : E, 0 ≤ z → ‖z‖ ≤ max ‖x‖ ‖y‖ → z ≤ max ‖x‖ ‖y‖ • e := fun z hz hzr ↦
      (abs_of_nonneg hz).symm.le.trans ((he.abs_le_norm_smul z).trans
        (smul_le_smul_of_nonneg_right hzr he.1))
    refine he.norm_le_of_abs_le_smul ((norm_nonneg x).trans (le_max_left _ _)) ?_
    rw [abs_of_nonneg hxy]
    exact sup_le (hle x hx (le_max_left _ _)) (hle y hy (le_max_right _ _))
  · exact norm_le_norm_of_abs_le_abs
      (by rw [abs_of_nonneg hx, abs_of_nonneg hxy]; exact le_sup_left)
  · exact norm_le_norm_of_abs_le_abs
      (by rw [abs_of_nonneg hy, abs_of_nonneg hxy]; exact le_sup_right)

end AMUnit

end CKMA
