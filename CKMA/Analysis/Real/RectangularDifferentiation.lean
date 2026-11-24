/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.RectangularDifferentiation.CounterexampleSum
public import CKMA.Analysis.Real.RectangularDifferentiation.Differentiate

import CKMA.Analysis.Real.RectangularDifferentiation.Approximate
import CKMA.Analysis.Real.RectangularDifferentiation.Step

/-!
# Strong maximal averages and rectangular differentiation

Axis-parallel rectangles with positive side lengths, their signed averages and the
positive strong maximal operator. Shrinking rectangles have unrestricted eccentricity.
The endpoint estimate uses `u(1+log⁺u)^(d-1)`; this local integrability class is differentiated
almost everywhere, whereas L¹ alone is insufficient in dimension at least two.
Measures, real logarithms and extended integrals use Mathlib. Source: GAPS 05.31.

The definitions `CKMA.OpenRectangle`, `CKMA.strongMaximalFunction`, `CKMA.strongMaximalGrowth`,
`CKMA.IsLocallyLLog`, and `CKMA.RectanglesDifferentiateAt` are re-exported from
`CKMA.Analysis.Real.RectangularDifferentiation.Base`.

## Main results

* `CKMA.strongMaximal_endpoint`: the Jessen–Marcinkiewicz–Zygmund endpoint weak-type bound for the
  strong maximal operator (**05.31**).
* `CKMA.ae_rectanglesDifferentiateAt`: almost-everywhere rectangular differentiation of functions in
  `L(log⁺ L)^{d-1}_{loc}`, in every dimension `d ≥ 1`.
* `CKMA.exists_integrable_not_rectangularlyDifferentiable`: existence of an integrable function on
  `ℝ^d` (`d ≥ 2`) whose rectangular averages do not converge to its values on a set of positive
  measure.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Set Metric

/-- **05.31**: the endpoint strong maximal bound, in every positive dimension. -/
theorem strongMaximal_endpoint {d : ℕ} (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : (Fin d → ℝ) → ℝ), Measurable f →
      ∀ a : ℝ, 0 < a → volume {x | ENNReal.ofReal a < strongMaximalFunction f x} ≤
        ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth d (|f x| / a)) := by
  exact strongMaximal_orlicz hd

/-- Rectangles differentiate the local `L(log⁺L)^(d-1)` class, in every positive dimension. -/
theorem ae_rectanglesDifferentiateAt {d : ℕ} (hd : 1 ≤ d)
    {f : (Fin d → ℝ) → ℝ} (hm : Measurable f) (hf : IsLocallyLLog d f) :
    ∀ᵐ x ∂volume, RectanglesDifferentiateAt f x := by
  have hd0 : 0 < d := hd
  choose φ hφc hφs hφ1 hφi using fun m : ℕ ↦
    exists_compactCutoff hm hf (m + 1 : ℝ)
  have hnull : ∀ m : ℕ,
      volume {x | ¬ RectanglesDifferentiateAt (fun y ↦ f y * φ m y) x} = 0 := by
    intro m
    have hmφ : Measurable (fun y ↦ f y * φ m y) := hm.mul (hφc m).measurable
    have hae := ae_rectanglesDifferentiateAt_of_integrable_growth hd hmφ (hφi m)
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
  refine measure_mono_null hsub ?_
  suffices hzero : ∑' n : ℕ,
      volume {x | ¬ RectanglesDifferentiateAt (fun y ↦ f y * φ n y) x} = 0 by
    exact le_antisymm ((measure_iUnion_le _).trans hzero.le) bot_le
  rw [ENNReal.tsum_eq_zero]
  intro m
  exact hnull m

@[deprecated (since := "2026-11-15")]
alias ae_rectanglesDifferentiateAt_of_strongMaximal := ae_rectanglesDifferentiateAt

/-- In dimension at least two the same basis does not differentiate all of `L¹`. -/
theorem exists_integrable_not_rectangularlyDifferentiable {d : ℕ} (hd : 2 ≤ d) :
    ∃ f : (Fin d → ℝ) → ℝ, Measurable f ∧ Integrable f volume ∧
      0 < volume {x | ¬ RectanglesDifferentiateAt f x} := by
  refine ⟨Bohr.saks d hd, Bohr.measurable_saks d hd, Bohr.integrable_saks d hd, ?_⟩
  have hsub : Bohr.limsupSet d hd ⊆ {x | ¬ RectanglesDifferentiateAt (Bohr.saks d hd) x} :=
    fun _ hx => Bohr.not_rectanglesDifferentiateAt_on_limsup d hd hx
  exact (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 3 / 32)).trans_le
    ((Bohr.volume_limsupSet_ge d hd).trans (measure_mono hsub))

@[deprecated (since := "2026-11-15")]
alias Bohr.exists_integrable_not_rectangularlyDifferentiable :=
  exists_integrable_not_rectangularlyDifferentiable

end CKMA
