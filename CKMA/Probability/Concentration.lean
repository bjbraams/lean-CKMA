/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.Concentration.Basic
public import CKMA.Probability.Concentration.Bernstein
public import CKMA.Probability.Concentration.JohnsonLindenstrauss

/-!
# Sub-Gaussian gauges, Bernstein and dimension reduction (07.4, 07.6, 07.47)

`HasPsiTwoBound`, `HasGaussianTail` and `HasGaussianMoments` express the exponential,
tail and moment descriptions of a real sub-Gaussian random variable. The extended
nonnegative `psiTwoGauge` is infinite if no positive admissible scale exists.
The implication theorems compare these descriptions and Mathlib's sub-Gaussian MGF API.

The other main statements are Bernstein's inequality for independent centered variables
and the Johnson–Lindenstrauss finite-set embedding bound. Scale and probability
normalizations are explicit at the theorem interfaces.

## Main definitions

* `CKMA.HasPsiTwoBound`: exponential square integrability at scale `K` (in `Concentration.Basic`).
* `CKMA.psiTwoGauge`: the sub-Gaussian Luxemburg gauge (in `Concentration.Basic`).
* `CKMA.HasGaussianTail`: two-sided Gaussian tail decay (in `Concentration.Basic`).
* `CKMA.HasGaussianMoments`: square-root growth of `L^p` norms (in `Concentration.Basic`).

## Main results

* `CKMA.bernstein`: scalar Bernstein inequality for independent bounded centered summands.
* `CKMA.HasPsiTwoBound.hasGaussianTail`: exponential square control implies Gaussian tails.
* `CKMA.HasGaussianTail.hasPsiTwoBound`: Gaussian tails imply exponential square control.
* `CKMA.HasPsiTwoBound.hasGaussianMoments`: exponential square control implies moment growth.
* `CKMA.HasGaussianMoments.hasPsiTwoBound`: moment growth implies exponential square control.
* `CKMA.HasPsiTwoBound.hasSubgaussianMGF`: centered exponential square control implies
  sub-Gaussian MGF.
* `CKMA.johnson_lindenstrauss`: Johnson–Lindenstrauss finite-set dimension reduction.

## Notation

No new notation is introduced in this file.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped NNReal ENNReal BigOperators
open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **07.4**: scalar Bernstein inequality for independent bounded centered summands. -/
theorem bernstein [IsProbabilityMeasure μ] {n : ℕ} (X : Fin n → Ω → ℝ)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hc : ∀ i, ∫ ω, X i ω ∂μ = 0) {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b) :
    μ {ω | t ≤ |∑ i, X i ω|} ≤ ENNReal.ofReal
      (2 * Real.exp (-(t ^ 2 / (2 * ((∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) + b * t / 3))))) :=
  bernstein_of_bounded X hm hi hc hb ht hbound

/-- **07.6**: exponential square control implies Gaussian tails, without centering. -/
theorem HasPsiTwoBound.hasGaussianTail
    {X : Ω → ℝ} (hm : Measurable X) {K : ℝ} (h : HasPsiTwoBound X μ K) :
    HasGaussianTail X μ K :=
  hasGaussianTail_of_hasPsiTwoBound hm h

/-- Gaussian tails give the exponential square condition at twice the scale. -/
theorem HasGaussianTail.hasPsiTwoBound [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hm : Measurable X) {K : ℝ} (h : HasGaussianTail X μ K) :
    HasPsiTwoBound X μ (2 * K) :=
  hasPsiTwoBound_of_hasGaussianTail hm h

/-- Exponential square control implies square-root moment growth, without probability
normalization. -/
theorem HasPsiTwoBound.hasGaussianMoments
    {X : Ω → ℝ} (hm : Measurable X) {K : ℝ} (h : HasPsiTwoBound X μ K) :
    HasGaussianMoments X μ (2 * K) :=
  hasGaussianMoments_of_hasPsiTwoBound hm h

/-- Moment growth gives exponential square integrability, with a universal change of scale. -/
theorem HasGaussianMoments.hasPsiTwoBound [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hm : Measurable X) {K : ℝ} (h : HasGaussianMoments X μ K) :
    HasPsiTwoBound X μ (4 * K) :=
  hasPsiTwoBound_of_hasGaussianMoments hm h

/-- Centered exponential square control implies a sub-Gaussian MGF.
The numerical constant is deliberately nonoptimal. -/
theorem HasPsiTwoBound.hasSubgaussianMGF [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hm : Measurable X) (hc : ∫ ω, X ω ∂μ = 0)
    {K : ℝ} (h : HasPsiTwoBound X μ K) :
    HasSubgaussianMGF X (⟨16 * K ^ 2, by positivity⟩ : ℝ≥0) μ :=
  hasSubgaussianMGF_of_hasPsiTwoBound hm hc h

/-- **07.47**: Johnson–Lindenstrauss, with a constant uniform in dimensions and points.
The `max N 1` convention includes the empty configuration. -/
theorem johnson_lindenstrauss : ∃ C : ℝ, 0 < C ∧
    ∀ (d N : ℕ) (x : Fin N → EuclideanSpace ℝ (Fin d)) (ε : ℝ), 0 < ε → ε < 1 →
    ∃ (m : ℕ) (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)),
      (m : ℝ) ≤ C * ε⁻¹ ^ 2 * Real.log (2 * (max N 1 : ℕ)) ∧
      ∀ i j, (1 - ε) * ‖x i - x j‖ ^ 2 ≤ ‖T (x i - x j)‖ ^ 2 ∧
        ‖T (x i - x j)‖ ^ 2 ≤ (1 + ε) * ‖x i - x j‖ ^ 2 :=
  ⟨64, by norm_num, johnson_lindenstrauss_explicit⟩

end CKMA
