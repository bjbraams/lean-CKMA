/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Weighted disk Bergman spaces

The normalized disk measure has density `(α+1)(1-|z|²)^α/π` for `α > -1`.
The principal-power kernel `(1-z conj(w))^(-α-2)` reproduces square-integrable
holomorphic functions. Monomial norms, closedness of the analytic subspace and the
orthogonal projection describe the Hilbert case; kernel bounds also cover `1 < p < ∞`.

Sources: GAPS 42.51 and 42.52.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped ENNReal ComplexConjugate

/-- The normalized weighted disk measure, with total mass one when `-1 < α`. -/
def bergmanMeasure (α : ℝ) : Measure ℂ :=
  volume.withDensity (fun z ↦ if ‖z‖ < 1 then
    ENNReal.ofReal (((α + 1) / Real.pi) * (1 - ‖z‖ ^ 2) ^ α) else 0)

/-- The weighted disk Bergman kernel, with the principal complex power. -/
def bergmanKernel (α : ℝ) (z w : ℂ) : ℂ := (1 - z * conj w) ^ (-(α : ℂ) - 2)

/-- The analytic part of a weighted `Lᵖ` space, expressed through an a.e. holomorphic
  representative. -/
def bergmanSet (α : ℝ) (p : ℝ≥0∞) : Set (Lp ℂ p (bergmanMeasure α)) :=
  {u | ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 0 1) ∧ u =ᵐ[bergmanMeasure α] f}

/-- The integral formula for the weighted Bergman projection. -/
def bergmanIntegral (α : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ w, bergmanKernel α z w * f w ∂bergmanMeasure α

/-- **42.51**: reproduction on the weighted square-integrable holomorphic space. -/
theorem bergman_reproducing {α : ℝ} (hα : -1 < α) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) (hLp : MemLp f 2 (bergmanMeasure α))
    {z : ℂ} (hz : ‖z‖ < 1) : bergmanIntegral α f z = f z := by
  sorry

/-- The monomial square norms; for `α = 0` this is `1/(n+1)`. -/
theorem integral_norm_monomial_sq {α : ℝ} (hα : -1 < α) (n : ℕ) :
    (∫ z : ℂ, ‖z ^ n‖ ^ 2 ∂bergmanMeasure α) =
      Real.Gamma (α + 2) * n.factorial / Real.Gamma (n + α + 2) := by
  sorry

/-- The holomorphic `L²` subspace is closed. -/
theorem isClosed_bergmanSet {α : ℝ} (hα : -1 < α) : IsClosed (bergmanSet α 2) := by
  sorry

/-- **42.52**, Hilbert clause: the integral operator is an orthogonal projection with norm one. -/
theorem exists_bergmanProjection {α : ℝ} (hα : -1 < α) :
    ∃ P : Lp ℂ 2 (bergmanMeasure α) →L[ℂ] Lp ℂ 2 (bergmanMeasure α),
      (∀ f, (fun z ↦ P f z) =ᵐ[bergmanMeasure α] bergmanIntegral α f) ∧
      P.comp P = P ∧ P.adjoint = P ∧ ‖P‖ = 1 ∧ Set.range P = bergmanSet α 2 := by
  sorry

/-- The all-`p` weighted kernel estimate, which is outside the short `L²` argument. -/
theorem bergmanIntegral_bounded {α : ℝ} (hα : -1 < α) {p : ℝ≥0∞}
    (hp : 1 < p) (hp_top : p < ∞) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ f : ℂ → ℂ, MemLp f p (bergmanMeasure α) →
        MemLp (bergmanIntegral α f) p (bergmanMeasure α) ∧
        eLpNorm (bergmanIntegral α f) p (bergmanMeasure α) ≤
          C * eLpNorm f p (bergmanMeasure α) := by
  sorry

end CKMA
