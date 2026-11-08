/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Fourier summation on the probability circle

Symmetric Fourier partial sums and their Fejér averages use Mathlib's circle
characters, Fourier coefficients and normalized Haar measure. Fejér means converge
in finite Lᵖ norms, uniformly for continuous functions and pointwise at Lebesgue
points. The Carleson–Hunt interface combines maximal control with almost-everywhere
convergence of ordinary partial sums for `p > 1`.

Sources: GAPS 27.17 and 27.22.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

/-- Symmetric Fourier partial sums on the probability circle. -/
def fourierPartialSum (f : AddCircle (1 : ℝ) → ℂ) (N : ℕ)
    (x : AddCircle (1 : ℝ)) : ℂ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f k * fourier k x

/-- Fejer's Cesaro averages of the symmetric partial sums. -/
def fejerMean (f : AddCircle (1 : ℝ) → ℂ) (N : ℕ) (x : AddCircle (1 : ℝ)) : ℂ :=
  (N + 1 : ℂ)⁻¹ * ∑ n ∈ Finset.range (N + 1), fourierPartialSum f n x

/-- The positive Carleson maximal function, retaining infinite suprema. -/
def carlesonMaximalFunction (f : AddCircle (1 : ℝ) → ℂ) (x : AddCircle (1 : ℝ)) : ℝ≥0∞ :=
  ⨆ N : ℕ, ENNReal.ofReal ‖fourierPartialSum f N x‖

/-- A Lebesgue point on the circle, defined through local lifted averages. -/
def IsCircleLebesguePoint (f : AddCircle (1 : ℝ) → ℂ) (x : AddCircle (1 : ℝ)) : Prop :=
  Tendsto (fun r : ℝ ↦ (2 * r)⁻¹ * ∫ t in (-r)..r,
    ‖f (x + (t : AddCircle (1 : ℝ))) - f x‖) (𝓝[>] 0) (𝓝 0)

/-- The zero function has zero symmetric Fourier partial sums. -/
@[simp]
theorem fourierPartialSum_zero (N : ℕ) : fourierPartialSum (fun _ ↦ 0) N = 0 := by
  funext x
  simp [fourierPartialSum, fourierCoeff]

/-- **27.17**, the finite-p circle Fejer theorem. -/
theorem fejerMean_tendsto_Lp {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p < ∞)
    {f : AddCircle (1 : ℝ) → ℂ} (hf : MemLp f p AddCircle.haarAddCircle) :
    Tendsto (fun N ↦ eLpNorm (fun x ↦ fejerMean f N x - f x) p AddCircle.haarAddCircle)
      atTop (𝓝 0) := by
  sorry

/-- Continuous circle functions have uniformly convergent Fejer means. -/
theorem fejerMean_tendstoUniformly {f : AddCircle (1 : ℝ) → ℂ} (hf : Continuous f) :
    TendstoUniformly (fun N x ↦ fejerMean f N x) f atTop := by
  sorry

/-- Fejer means recover the value at every circle Lebesgue point. -/
theorem fejerMean_tendsto_at_lebesguePoint {f : AddCircle (1 : ℝ) → ℂ}
    (hf : Integrable f AddCircle.haarAddCircle) {x : AddCircle (1 : ℝ)}
    (hx : IsCircleLebesguePoint f x) :
    Tendsto (fun N ↦ fejerMean f N x) atTop (𝓝 (f x)) := by
  sorry

/-- **27.22**: Carleson–Hunt maximal control and almost-everywhere ordinary Fourier convergence. -/
theorem carleson_hunt {p : ℝ} (hp : 1 < p) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧
    ∀ f : AddCircle (1 : ℝ) → ℂ, MemLp f (ENNReal.ofReal p) AddCircle.haarAddCircle →
      (∫⁻ x, (carlesonMaximalFunction f x) ^ p ∂AddCircle.haarAddCircle) ≤
        C * (eLpNorm f (ENNReal.ofReal p) AddCircle.haarAddCircle) ^ p ∧
      ∀ᵐ x ∂AddCircle.haarAddCircle, Tendsto (fun N ↦ fourierPartialSum f N x) atTop (𝓝 (f x)) := by
  sorry

end CKMA
