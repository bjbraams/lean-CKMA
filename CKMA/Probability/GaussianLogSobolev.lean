/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Gaussian entropy and the log-Sobolev inequality (07.16)

`nonnegativeFunctionEntropy` uses Mathlib's `klFun` to express entropy relative to the
mean of an integrable nonnegative function on a probability space. Its zero-mean
convention is explicit. `gaussian_logSobolev` bounds the entropy of a square by its
gradient energy for a finite-dimensional real Gaussian law.

The theorem supplies the L² and gradient integrability conditions needed by the raw
entropy formula; inner products and covariance follow Mathlib's Gaussian conventions.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Nonnegative extended entropy of an integrable nonnegative function over a probability measure.
Normalization uses Mathlib's nonnegative KL integrand, retaining infinite positive entropy.
For positive mass this equals `∫ h log h - (∫ h) log (∫ h)`, and zero mass gives zero. -/
def nonnegativeFunctionEntropy {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (h : E → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (∫ x, h x ∂μ) *
    ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun (h x / (∫ y, h y ∂μ))) ∂μ

/-- **07.17**: Gaussian logarithmic Sobolev inequality with exact constant two.
The extended integral formulation does not assume in advance that the entropy is finite. -/
theorem gaussian_logSobolev {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (g : E → ℝ) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (hLp : MemLp g 2 (stdGaussian E)) :
    nonnegativeFunctionEntropy (stdGaussian E) (fun x ↦ g x ^ 2) ≤
      2 * ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ g x‖ ^ 2) ∂stdGaussian E := by
  sorry

end CKMA
