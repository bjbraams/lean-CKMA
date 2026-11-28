/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.RectangularDifferentiation.Base
public import CKMA.Analysis.Real.RectangularDifferentiation.Step

import CKMA.Analysis.Real.RectangularDifferentiation.Approximate
import CKMA.Analysis.Real.RectangularDifferentiation.CounterexampleSum
import CKMA.Analysis.Real.RectangularDifferentiation.Differentiate

/-!
# Strong maximal averages and rectangular differentiation

Axis-parallel rectangles with positive side lengths, their signed averages and the
positive strong maximal operator. Shrinking rectangles have unrestricted eccentricity.
The endpoint estimate uses `u(1+log⁺u)^(d-1)`; this local integrability class is differentiated
almost everywhere, whereas L¹ alone is insufficient in dimension at least two.
Source: GAPS 05.31.

The definitions `CKMA.OpenRectangle`, `CKMA.strongMaximalFunction`, `CKMA.strongMaximalGrowth`,
`CKMA.IsLocallyLLog`, and `CKMA.RectanglesDifferentiateAt` are re-exported from
`CKMA.Analysis.Real.RectangularDifferentiation.Base`, and the endpoint bound
`CKMA.strongMaximal_endpoint` from `CKMA.Analysis.Real.RectangularDifferentiation.Step`.

## Main results

* `CKMA.strongMaximal_endpoint`: the Jessen–Marcinkiewicz–Zygmund endpoint weak-type bound for the
  strong maximal operator (**05.31**), in every dimension.
* `CKMA.ae_rectanglesDifferentiateAt`: almost-everywhere rectangular differentiation of functions in
  `L(log⁺ L)^{d-1}_{loc}`, in every dimension `d` (trivially in dimension `0`, where the only
  rectangle is the whole space, a single point).
* `CKMA.exists_integrable_not_ae_rectanglesDifferentiateAt`: existence of an integrable function on
  `ℝ^d` (`d ≥ 2`) whose rectangular averages do not converge to its values on a set of positive
  measure.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Set Metric

/-- In dimension zero every function is rectangularly differentiable at every point: the only
rectangle is the whole space, a single point of volume one. -/
private theorem rectanglesDifferentiateAt_of_fin_zero (f : (Fin 0 → ℝ) → ℝ) (x : Fin 0 → ℝ) :
    RectanglesDifferentiateAt f x := by
  intro ε hε
  refine ⟨1, one_pos, fun R _ _ ↦ ?_⟩
  have hc : R.carrier = univ := eq_univ_of_forall fun _ j ↦ j.elim0
  have hf : (fun y ↦ f y) = fun _ ↦ f x := funext fun y ↦ by rw [Subsingleton.elim y x]
  have hv : volume (univ : Set (Fin 0 → ℝ)) = 1 := by
    rw [volume_pi, Measure.pi_of_empty, Measure.dirac_apply_of_mem (mem_univ _)]
  simp only [OpenRectangle.average, hc, Measure.restrict_univ]
  rw [hf]
  simp [Measure.real, hv, hε]

/-- Rectangles differentiate the local `L(log⁺L)^(d-1)` class almost everywhere, in every
dimension. -/
theorem ae_rectanglesDifferentiateAt {d : ℕ}
    {f : (Fin d → ℝ) → ℝ} (hm : Measurable f) (hf : IsLocallyLLog d f) :
    ∀ᵐ x ∂volume, RectanglesDifferentiateAt f x := by
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · exact Filter.Eventually.of_forall (rectanglesDifferentiateAt_of_fin_zero f)
  choose φ hφc hφs hφ1 hφi using fun m : ℕ ↦
    exists_compactCutoff hm hf (m + 1 : ℝ)
  have hnull : ∀ m : ℕ,
      volume {x | ¬ RectanglesDifferentiateAt (fun y ↦ f y * φ m y) x} = 0 := by
    intro m
    have hmφ : Measurable (fun y ↦ f y * φ m y) := hm.mul (hφc m).measurable
    have hae := ae_rectanglesDifferentiateAt_of_integrable_growth hd0 hmφ (hφi m)
    rwa [ae_iff] at hae
  rw [ae_iff]
  have hsub : {x | ¬ RectanglesDifferentiateAt f x} ⊆ ⋃ n : ℕ,
      {x | ¬ RectanglesDifferentiateAt (fun y ↦ f y * φ n y) x} := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    have hrad : ‖x‖ < (n + 1 : ℝ) := hn.trans_le (by exact_mod_cast Nat.le_succ n)
    refine mem_iUnion.2 ⟨n, ?_⟩
    intro hdiff
    exact hx (rectanglesDifferentiateAt_of_cutoff hd0 hrad (hφ1 n) hdiff)
  exact measure_mono_null hsub (measure_iUnion_null hnull)

/-- In dimension at least two the same basis does not differentiate all of `L¹`. -/
theorem exists_integrable_not_ae_rectanglesDifferentiateAt {d : ℕ} (hd : 2 ≤ d) :
    ∃ f : (Fin d → ℝ) → ℝ, Measurable f ∧ Integrable f volume ∧
      0 < volume {x | ¬ RectanglesDifferentiateAt f x} := by
  refine ⟨SaksCounterexample.saks d hd, SaksCounterexample.measurable_saks d hd,
    SaksCounterexample.integrable_saks d hd, ?_⟩
  have hsub : SaksCounterexample.limsupSet d hd ⊆
      {x | ¬ RectanglesDifferentiateAt (SaksCounterexample.saks d hd) x} :=
    fun _ hx ↦ SaksCounterexample.not_rectanglesDifferentiateAt_on_limsup d hd hx
  exact (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 3 / 32)).trans_le
    ((SaksCounterexample.volume_limsupSet_ge d hd).trans (measure_mono hsub))

end CKMA
