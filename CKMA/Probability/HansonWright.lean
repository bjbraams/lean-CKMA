/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.Concentration.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
import TauCeti.Probability.Moments.HansonWright

/-!
# Hanson–Wright concentration for quadratic forms (07.43)

`hanson_wright` gives the two-scale exponential bound for the centered quadratic form
`xᵀ A x = x ⬝ᵥ A *ᵥ x` of a random vector with independent centered sub-Gaussian coordinates,
with sub-Gaussianity measured by the `ψ₂` gauge `psiTwoGauge`. The scales are the squared
Frobenius norm `∑ i, ∑ j, A i j ^ 2` and the Euclidean operator norm `‖A‖` (Mathlib's scoped
`Matrix.Norms.L2Operator` norm).

The theorem is derived from TauCeti's `TauCeti.hanson_wright`, whose coordinates are
sub-Gaussian in the moment generating function sense; `psiTwoGauge_le_ofReal_iff` and
`HasPsiTwoBound.hasSubgaussianMGF` convert the gauge bound into that form.

Matrices need not be symmetric. The universal constant is independent of dimension,
and positive threshold and scale hypotheses specify the meaningful concentration range.

## Main results

* `CKMA.hanson_wright`: Hanson–Wright concentration inequality with a universal constant.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

universe u

/-- **07.43**: Hanson–Wright with a constant uniform over dimensions, probability spaces,
coordinate laws and matrices. The Frobenius denominator is squared, and the operator norm is
Euclidean. -/
theorem hanson_wright : ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : Fin n → Ω → ℝ), (∀ i, AEMeasurable (X i) μ) → iIndepFun X μ →
      (∀ i, ∫ ω, X i ω ∂μ = 0) →
      ∀ K : ℝ, 0 < K → (∀ i, psiTwoGauge (X i) μ ≤ ENNReal.ofReal K) →
      ∀ (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ), 0 < t →
      μ {ω | t < |(fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) -
          ∫ η, (fun i ↦ X i η) ⬝ᵥ A *ᵥ (fun i ↦ X i η) ∂μ|} ≤
        ENNReal.ofReal (2 * Real.exp (-c * min
          (t ^ 2 / (K ^ 4 * ∑ i, ∑ j, A i j ^ 2))
          (t / (K ^ 2 * ‖A‖)))) := by
  obtain ⟨c, hc, hHW⟩ := TauCeti.hanson_wright
  refine ⟨c / 256, by positivity, fun n Ω _ μ _ X hm hi h0 K hK hgauge A t ht ↦ ?_⟩
  let L : ℝ≥0 := ⟨16 * K ^ 2, by positivity⟩
  have hT := hHW μ X L hi (fun i ↦
    ((psiTwoGauge_le_ofReal_iff (hm i) hK).1 (hgauge i)).hasSubgaussianMGF (hm i) (h0 i)) A t
    ht.le
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal (hT.trans ?_)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) zero_le_two
  set a := t ^ 2 / (K ^ 4 * ∑ i, ∑ j, A i j ^ 2)
  set b := t / (K ^ 2 * ‖A‖)
  have hb : 0 ≤ b := div_nonneg ht.le (mul_nonneg (by positivity) (norm_nonneg _))
  have hL : (L : ℝ) = 16 * K ^ 2 := rfl
  have ha' : t ^ 2 / ((L : ℝ) ^ 2 * ∑ i, ∑ j, A i j ^ 2) = a / 256 := by
    simp only [a, hL]
    ring
  have hb' : t / ((L : ℝ) * ‖A‖) = b / 16 := by
    simp only [b, hL]
    ring
  have hb16 : b / 256 ≤ b / 16 := div_le_div_of_nonneg_left hb (by norm_num) (by norm_num)
  have key : min a b / 256 ≤ min (a / 256) (b / 16) :=
    le_min (by gcongr; exact min_le_left a b)
      ((div_le_div_of_nonneg_right (min_le_right a b) (by norm_num)).trans hb16)
  rw [ha', hb']
  nlinarith [mul_le_mul_of_nonneg_left key hc.le]

end CKMA
