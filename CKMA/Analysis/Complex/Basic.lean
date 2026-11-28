/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Normal summability and basic complex domains

Normal summability is a predicate on families of functions into a normed additive group.
On a set, every compact subset must have bounded summands and a summable sequence of
compact-supremum norms. This module also defines the open unit disk in `ℂ` shared across
complex analysis and complex geometry.

## Main definitions

* `CKMA.NormallySummableOn`: normal summability of a function family on compact subsets of a set.
* `CKMA.complexUnitDisk`: the open unit disk `Metric.ball (0 : ℂ) 1`.
* `CKMA.taylorCoefficient`: the Taylor coefficient `f⁽ⁿ⁾(0) / n!` at the origin.

## Main results

* `CKMA.NormallySummableOn.of_norm_le`: a summable bound on each compact subset gives normal
  summability.
* `CKMA.NormallySummableOn.summable_norm`: normal summability on `s` implies pointwise absolute
  summability at each `x ∈ s`.
* `CKMA.isOpen_complexUnitDisk`: `complexUnitDisk` is open.
-/

public section

noncomputable section

namespace CKMA

open scoped BigOperators

/-- The open unit disk `Metric.ball (0 : ℂ) 1`, shared by the analytic function-space
interfaces. It is an abbreviation, so the `Metric.ball` API applies to it directly. -/
abbrev complexUnitDisk : Set ℂ := Metric.ball 0 1

/-- A point lies in the unit disk exactly when its norm is less than one. -/
theorem mem_complexUnitDisk {z : ℂ} : z ∈ complexUnitDisk ↔ ‖z‖ < 1 :=
  mem_ball_zero_iff

/-- The shared unit disk is open. -/
theorem isOpen_complexUnitDisk : IsOpen complexUnitDisk := Metric.isOpen_ball

/-- The `n`th Taylor coefficient `f⁽ⁿ⁾(0) / n!` of `f` at the origin. It is defined for every
`f`; the iterated derivative of a function that is not differentiable is `0`. -/
@[expose]
def taylorCoefficient (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0

/-- The Taylor coefficient is `(n!)⁻¹ f⁽ⁿ⁾(0)`. -/
theorem taylorCoefficient_def (f : ℂ → ℂ) (n : ℕ) :
    taylorCoefficient f n = (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0 :=
  rfl

/-- The Taylor coefficient is `f⁽ⁿ⁾(0) / n!`. -/
theorem taylorCoefficient_eq_div (f : ℂ → ℂ) (n : ℕ) :
    taylorCoefficient f n = iteratedDeriv n f 0 / (n.factorial : ℂ) := by
  rw [taylorCoefficient, inv_mul_eq_div]

/-- Normal summability on compact subsets, requiring bounded summands and summability
of their compact supremum norms. -/
@[expose]
def NormallySummableOn {ι X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    (f : ι → X → E) (s : Set X) : Prop :=
  ∀ K : Set X, IsCompact K → K ⊆ s →
    (∀ i, BddAbove ((fun x ↦ ‖f i x‖) '' K)) ∧
      Summable (fun i ↦ sSup ((fun x ↦ ‖f i x‖) '' K))

/-- Normal summability on `s` unfolds to its condition on compact subsets of `s`. -/
theorem normallySummableOn_iff {ι X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    {f : ι → X → E} {s : Set X} :
    NormallySummableOn f s ↔ ∀ K : Set X, IsCompact K → K ⊆ s →
      (∀ i, BddAbove ((fun x ↦ ‖f i x‖) '' K)) ∧
        Summable (fun i ↦ sSup ((fun x ↦ ‖f i x‖) '' K)) :=
  Iff.rfl

/-- A family is normally summable on `s` once, on each compact `K ⊆ s`, its summands are bounded
by a summable sequence. -/
theorem NormallySummableOn.of_norm_le {ι X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] {f : ι → X → E} {s : Set X}
    (h : ∀ K : Set X, IsCompact K → K ⊆ s →
      ∃ B : ι → ℝ, Summable B ∧ ∀ i, ∀ x ∈ K, ‖f i x‖ ≤ B i) :
    NormallySummableOn f s := by
  intro K hK hKs
  obtain ⟨B, hB, hle⟩ := h K hK hKs
  have hbdd : ∀ i, BddAbove ((fun x ↦ ‖f i x‖) '' K) :=
    fun i ↦ ⟨B i, by rintro y ⟨x, hx, rfl⟩; exact hle i x hx⟩
  refine ⟨hbdd, Summable.of_nonneg_of_le (fun i ↦ Real.sSup_nonneg ?_) (fun i ↦ ?_) hB.abs⟩
  · rintro y ⟨x, -, rfl⟩
    exact norm_nonneg _
  · rcases K.eq_empty_or_nonempty with rfl | hKne
    · simp
    · refine csSup_le (hKne.image _) ?_
      rintro y ⟨x, hx, rfl⟩
      exact (hle i x hx).trans (le_abs_self _)

/-- A normally summable family is absolutely summable at each point of its domain. -/
theorem NormallySummableOn.summable_norm {ι X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] {f : ι → X → E} {s : Set X}
    (hf : NormallySummableOn f s) {x : X} (hx : x ∈ s) :
    Summable (fun i ↦ ‖f i x‖) := by
  have h := (hf {x} isCompact_singleton (Set.singleton_subset_iff.mpr hx)).2
  simpa only [Set.image_singleton, csSup_singleton] using h

end CKMA
