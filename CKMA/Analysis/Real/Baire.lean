/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

/-!
# Baire class one and derivatives

Baire class one on a subset is defined by pointwise limits of functions continuous there.
Restriction and continuous-function inclusion hold for arbitrary topological targets.
The derivative of a differentiable real function on an open set is approximated by
continuous difference quotients with positive interior step sizes. The proof uses
Mathlib's distance-to-complement and derivative slope-limit lemmas.
Source: GAPS 05.7.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A function of Baire class one on a set is a pointwise limit of continuous functions there. -/
def IsBaireOneOn (f : X → Y) (s : Set X) : Prop :=
  ∃ g : ℕ → X → Y, (∀ n, ContinuousOn (g n) s) ∧
    ∀ x ∈ s, Tendsto (fun n ↦ g n x) atTop (𝓝 (f x))

/-- Restricting a Baire class one function preserves its class. -/
theorem IsBaireOneOn.mono {f : X → Y} {s t : Set X}
    (hf : IsBaireOneOn f s) (ht : t ⊆ s) : IsBaireOneOn f t := by
  obtain ⟨g, hg, hlim⟩ := hf
  exact ⟨g, fun n ↦ (hg n).mono ht, fun x hx ↦ hlim x (ht hx)⟩

/-- A continuous function is of Baire class one. -/
theorem ContinuousOn.isBaireOneOn {f : X → Y} {s : Set X}
    (hf : ContinuousOn f s) : IsBaireOneOn f s :=
  ⟨fun _ ↦ f, fun _ ↦ hf, fun _ _ ↦ tendsto_const_nhds⟩

/-- **05.7**: the derivative on an open set is of Baire class one. -/
theorem DifferentiableOn.isBaireOneOn_deriv {f : ℝ → ℝ} {s : Set ℝ}
    (hf : DifferentiableOn ℝ f s) (hs : IsOpen s) : IsBaireOneOn (deriv f) s := by
  classical
  let d : ℝ → ℝ := fun x ↦ if sᶜ.Nonempty then Metric.infDist x sᶜ / 2 else 1
  have hd : Continuous d := by
    dsimp [d]
    split_ifs
    · exact (Metric.continuous_infDist_pt sᶜ).div_const 2
    · exact continuous_const
  have hdpos : ∀ x ∈ s, 0 < d x := by
    intro x hx
    dsimp [d]
    split_ifs with h
    · have hdist : 0 < Metric.infDist x sᶜ :=
        (hs.isClosed_compl.notMem_iff_infDist_pos h).mp (by simpa using hx)
      linarith
    · exact zero_lt_one
  let h : ℕ → ℝ → ℝ := fun n x ↦ min ((n + 1 : ℝ)⁻¹) (d x)
  have hhcont : ∀ n, Continuous (h n) := fun n ↦ continuous_const.min hd
  have hhpos : ∀ n x, x ∈ s → 0 < h n x := by
    intro n x hx
    exact lt_min (inv_pos.mpr (by positivity)) (hdpos x hx)
  have hmem : ∀ n x, x ∈ s → x + h n x ∈ s := by
    intro n x hx
    by_cases hne : sᶜ.Nonempty
    · apply Metric.ball_infDist_compl_subset
      rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (hhpos n x hx)]
      have hle : h n x ≤ Metric.infDist x sᶜ / 2 := by
        simp [h, d, hne]
      have hdist : 0 < Metric.infDist x sᶜ := by
        have := hdpos x hx
        simpa [d, hne] using (show 0 < Metric.infDist x sᶜ / 2 by simpa [d, hne] using this)
      linarith
    · have hs' : s = Set.univ := by simpa using (Set.not_nonempty_iff_eq_empty.mp hne)
      simp [hs']
  refine ⟨fun n x ↦ (h n x)⁻¹ * (f (x + h n x) - f x), ?_, ?_⟩
  · intro n
    exact ((hhcont n).continuousOn.inv₀ (fun x hx ↦ ne_of_gt (hhpos n x hx))).mul
      ((hf.continuousOn.comp (continuous_id.add (hhcont n)).continuousOn
        (fun x hx ↦ hmem n x hx)).sub hf.continuousOn)
  · intro x hx
    have hhzero : Tendsto (fun n ↦ h n x) atTop (𝓝 0) := by
      have hi : Tendsto (fun n : ℕ ↦ ((n + 1 : ℝ)⁻¹)) atTop (𝓝 0) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa [h, min_eq_left (le_of_lt (hdpos x hx))] using hi.min (tendsto_const_nhds (x := d x))
    have hhne : Tendsto (fun n ↦ h n x) atTop (𝓝[≠] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hhzero, Filter.Eventually.of_forall
        (fun n ↦ ne_of_gt (hhpos n x hx))⟩
    simpa [smul_eq_mul, Function.comp_def] using
      ((hf x hx).differentiableAt (hs.mem_nhds hx)).hasDerivAt.tendsto_slope_zero.comp hhne

end CKMA
