/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.Process.Indistinguishable
public import Mathlib.Topology.Instances.NNReal.Lemmas

import Mathlib.Data.NNRat.Encodable

/-!
# Indistinguishability from agreement on a dense set of times

Two processes with almost surely continuous paths that agree almost surely at each time of a
countable dense set are indistinguishable (Mathlib's `ProbabilityTheory.Indistinguishable`).
The nonnegative rationals are such a set of times in `ℝ≥0`.

## Main results

* `CKMA.denseRange_coe_nnrat_nnreal`: the nonnegative rationals are dense in `ℝ≥0`.
* `CKMA.indistinguishable_of_continuous_of_dense`: continuous modifications that agree on a
  countable dense set of times are indistinguishable.
-/

public section

namespace CKMA

open Filter MeasureTheory Metric ProbabilityTheory Set
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Nonnegative rationals are dense in nonnegative time. -/
theorem denseRange_coe_nnrat_nnreal : DenseRange (fun q : ℚ≥0 => (q : ℝ≥0)) := by
  intro x
  rw [mem_closure_range_iff]
  intro ε hε
  by_cases hx : x = 0
  · refine ⟨0, ?_⟩
    simpa [hx, dist_self] using hε
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hx
  have hlt : max 0 ((x : ℝ) - ε) < (x : ℝ) := max_lt hx0 (sub_lt_self (x : ℝ) hε)
  obtain ⟨q, hqlo, hqx⟩ := exists_rat_btwn hlt
  have hq0r : (0 : ℝ) ≤ (q : ℝ) :=
    le_trans (le_max_left (0 : ℝ) ((x : ℝ) - ε)) hqlo.le
  have hq0 : 0 ≤ q := by exact_mod_cast hq0r
  refine ⟨q.toNNRat, ?_⟩
  rw [NNReal.dist_eq]
  have hcoe : ((q.toNNRat : ℝ≥0) : ℝ) = (q : ℝ) := by
    change (q.toNNRat : ℝ) = (q : ℝ)
    exact_mod_cast Rat.coe_toNNRat q hq0
  rw [hcoe, abs_of_nonneg (sub_nonneg.2 hqx.le)]
  have hlo : (x : ℝ) - ε < (q : ℝ) :=
    lt_of_le_of_lt (le_max_right (0 : ℝ) ((x : ℝ) - ε)) hqlo
  linarith

/-- Processes with almost surely continuous paths that agree almost surely at each point of a
countable dense set of times are indistinguishable. -/
theorem indistinguishable_of_continuous_of_dense {ι E : Type*} [TopologicalSpace ι]
    [TopologicalSpace E] [T2Space E] {B C : ι → Ω → E} {D : Set ι} (hD : D.Countable)
    (hdense : Dense D) (hC : ∀ᵐ ω ∂μ, Continuous (fun t => C t ω))
    (hB : ∀ᵐ ω ∂μ, Continuous (fun t => B t ω)) (hQ : ∀ q ∈ D, C q =ᵐ[μ] B q) :
    C ≡ᵐ[μ] B := by
  have hcount : ∀ᵐ ω ∂μ, ∀ q ∈ D, C q ω = B q ω := (ae_ball_iff hD).2 hQ
  filter_upwards [hcount, hC, hB] with ω hω hcontC hcontB t
  exact congrFun (Continuous.ext_on hdense hcontC hcontB fun u hu => hω u hu) t

end CKMA
