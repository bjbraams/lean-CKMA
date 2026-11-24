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

The matrix adapters are the squared Frobenius norm and Euclidean operator norm of a
real finite matrix. `sampledQuadraticForm` evaluates the corresponding form on a random
vector. `hanson_wright` gives the two-scale exponential bound for its centered value
under independent centered sub-Gaussian coordinates, with sub-Gaussianity measured by the
`ψ₂` gauge `psiTwoGauge`.

The theorem is derived from TauCeti's `TauCeti.hanson_wright`, whose coordinates are
sub-Gaussian in the moment generating function sense; `HasPsiTwoBound.hasSubgaussianMGF`
converts the gauge bound into that form.

Matrices need not be symmetric. The universal constant is independent of dimension,
and positive threshold and scale hypotheses specify the meaningful concentration range.

## Main definitions

* `CKMA.realMatrixFrobeniusSq`: squared Frobenius norm of a real matrix.
* `CKMA.realMatrixOperatorNorm`: Euclidean operator norm of a real matrix.
* `CKMA.sampledQuadraticForm`: quadratic form sampled at a coordinate family.

## Main results

* `CKMA.hanson_wright`: Hanson–Wright concentration inequality with a universal constant.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

universe u

variable {n : ℕ}

/-- The squared Frobenius norm of a real matrix, given by its entries. -/
@[expose]
def realMatrixFrobeniusSq (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- Euclidean operator norm, Mathlib's scoped `Matrix.Norms.L2Operator` norm, as distinct
from the entrywise matrix norm. -/
@[expose]
def realMatrixOperatorNorm (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖A‖

/-- The real quadratic form sampled at a coordinate family. -/
@[expose]
def sampledQuadraticForm {Ω : Type*} (A : Matrix (Fin n) (Fin n) ℝ) (X : Fin n → Ω → ℝ)
    (ω : Ω) : ℝ :=
  ∑ i, ∑ j, A i j * X i ω * X j ω

/-- Squared entry sums are nonnegative. -/
lemma realMatrixFrobeniusSq_nonneg (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ realMatrixFrobeniusSq A :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The adapter is the scoped Euclidean operator norm. -/
lemma realMatrixOperatorNorm_eq (A : Matrix (Fin n) (Fin n) ℝ) :
    realMatrixOperatorNorm A = ‖A‖ :=
  rfl

/-- The Euclidean operator norm is nonnegative. -/
lemma realMatrixOperatorNorm_nonneg (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ realMatrixOperatorNorm A :=
  norm_nonneg _

/-- The sampled quadratic form is `xᵀ A x` at the sampled vector. -/
lemma sampledQuadraticForm_eq_dotProduct {Ω : Type*} (A : Matrix (Fin n) (Fin n) ℝ)
    (X : Fin n → Ω → ℝ) (ω : Ω) :
    sampledQuadraticForm A X ω = (fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) := by
  simp only [sampledQuadraticForm, dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- **07.43**: Hanson–Wright with a constant uniform over dimensions, probability spaces,
coordinate laws and matrices. The Frobenius denominator is squared, and the operator norm is
Euclidean. -/
theorem hanson_wright : ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : Fin n → Ω → ℝ), (∀ i, Measurable (X i)) → iIndepFun X μ →
      (∀ i, ∫ ω, X i ω ∂μ = 0) →
      ∀ K : ℝ, 0 < K → (∀ i, psiTwoGauge (X i) μ ≤ ENNReal.ofReal K) →
      ∀ (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ), 0 < t →
      μ {ω | t < |sampledQuadraticForm A X ω - ∫ η, sampledQuadraticForm A X η ∂μ|} ≤
        ENNReal.ofReal (2 * Real.exp (-c * min
          (t ^ 2 / (K ^ 4 * realMatrixFrobeniusSq A))
          (t / (K ^ 2 * realMatrixOperatorNorm A)))) := by
  obtain ⟨c, hc, hHW⟩ := TauCeti.hanson_wright
  refine ⟨c / 4096, by positivity, fun n Ω _ μ _ X hm hi h0 K hK hgauge A t ht ↦ ?_⟩
  let L : ℝ≥0 := ⟨16 * (2 * K) ^ 2, by positivity⟩
  have hT := hHW μ X L hi (fun i ↦
    (hasPsiTwoBound_of_psiTwoGauge_le hK (hgauge i)).hasSubgaussianMGF (hm i) (h0 i)) A t ht.le
  simp only [← sampledQuadraticForm_eq_dotProduct] at hT
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal (hT.trans ?_)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) zero_le_two
  set a := t ^ 2 / (K ^ 4 * realMatrixFrobeniusSq A)
  set b := t / (K ^ 2 * realMatrixOperatorNorm A)
  have hb : 0 ≤ b := div_nonneg ht.le (mul_nonneg (by positivity) (norm_nonneg _))
  have hL : (L : ℝ) = 16 * (2 * K) ^ 2 := rfl
  have ha' : t ^ 2 / ((L : ℝ) ^ 2 * ∑ i, ∑ j, A i j ^ 2) = a / 4096 := by
    simp only [a, hL, realMatrixFrobeniusSq]
    ring
  have hb' : t / ((L : ℝ) * ‖A‖) = b / 64 := by
    simp only [b, hL, realMatrixOperatorNorm_eq]
    ring
  have hb64 : b / 4096 ≤ b / 64 := div_le_div_of_nonneg_left hb (by norm_num) (by norm_num)
  have key : min a b / 4096 ≤ min (a / 4096) (b / 64) :=
    le_min (by gcongr; exact min_le_left a b)
      ((div_le_div_of_nonneg_right (min_le_right a b) (by norm_num)).trans hb64)
  rw [ha', hb']
  nlinarith [mul_le_mul_of_nonneg_left key hc.le]

end CKMA
