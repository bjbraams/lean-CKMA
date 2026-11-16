/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import CKMA.Probability.GaussianLogSobolev.OneDimLSI
import CKMA.Probability.GaussianLogSobolev.EntropyTensorization
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Calculus.FDeriv.Pi.Lp
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.MeasureTheory.Integral.Pi

/-!
# Gaussian entropy and the log-Sobolev inequality (07.17)

`nonnegativeFunctionEntropy` uses Mathlib's `klFun` to express entropy relative to the
mean of an integrable nonnegative function on a probability space. Its zero-mean
convention is explicit. `gaussian_logSobolev` bounds the entropy of a square by its
gradient energy for a finite-dimensional real Gaussian law.

The theorem supplies the L² and gradient integrability conditions needed by the raw
entropy formula; inner products and covariance follow Mathlib's Gaussian conventions.

The proof tensorizes the one-dimensional inequality `CKMA.gaussian_logSobolev_oneDim` with the
subadditivity of entropy `CKMA.nonnegativeFunctionEntropy_pi_le` on the product of standard
Gaussians on `PiLp 2`, and transports the result to `stdGaussian E` along the linear isometry
given by an orthonormal basis, as in TauCeti's proof of the Gaussian Poincaré inequality.

## Main definitions

* `CKMA.nonnegativeFunctionEntropy` (in `GaussianLogSobolev.OneDimLSI`): Extended entropy of a
  nonnegative function over a probability measure using `InformationTheory.klFun`.

## Main results

* `CKMA.gaussian_logSobolev_piLp`: the inequality for the product of standard Gaussians on a
  finite Hilbert product `PiLp 2 (fun _ : ι ↦ ℝ)`.
* `CKMA.gaussian_logSobolev`: Gaussian logarithmic Sobolev inequality with sharp constant `2`.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Gaussian logarithmic Sobolev inequality on a finite Hilbert product.** For the product of
standard Gaussians on `PiLp 2 (fun _ : ι ↦ ℝ)`, the entropy of the square of a smooth
square-integrable function is at most twice its gradient energy. -/
theorem gaussian_logSobolev_piLp {ι : Type*} [Fintype ι] (g : PiLp 2 (fun _ : ι ↦ ℝ) → ℝ)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (hLp : MemLp g 2 ((Measure.pi fun _ : ι ↦ gaussianReal 0 1).map (WithLp.toLp 2))) :
    nonnegativeFunctionEntropy ((Measure.pi fun _ : ι ↦ gaussianReal 0 1).map (WithLp.toLp 2))
        (fun x ↦ g x ^ 2) ≤
      2 * ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ g x‖ ^ 2)
        ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 1).map (WithLp.toLp 2) := by
  classical
  let μ : ι → Measure ℝ := fun _ ↦ gaussianReal 0 1
  let ρ := (Measure.pi μ).map (WithLp.toLp 2)
  let T := MeasurableEquiv.toLp 2 (ι → ℝ)
  have hm : MeasurePreserving T (Measure.pi μ) ρ := ⟨T.measurable, rfl⟩
  let F : (ι → ℝ) → ℝ := fun x ↦ g (WithLp.toLp 2 x)
  let G : (ι → ℝ) → PiLp 2 (fun _ : ι ↦ ℝ) := fun x ↦ gradient g (WithLp.toLp 2 x)
  have hFL : MemLp F 2 (Measure.pi μ) := hLp.comp_measurePreserving hm
  have hGm : Measurable G := (TauCeti.measurable_gradient g).comp T.measurable
  have hGim (i : ι) : Measurable fun x ↦ ENNReal.ofReal (‖G x i‖ ^ 2) :=
    (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι ↦ ℝ) i).continuous.measurable.comp hGm).norm.pow_const
      2).ennreal_ofReal
  have hF2m : Measurable fun x ↦ F x ^ 2 :=
    ((hg.continuous.comp (PiLp.continuous_toLp 2 _)).pow 2).measurable
  have hEnt : nonnegativeFunctionEntropy ρ (fun x ↦ g x ^ 2) =
      nonnegativeFunctionEntropy (Measure.pi μ) (fun x ↦ F x ^ 2) :=
    (nonnegativeFunctionEntropy_comp_measurePreserving hm T.measurableEmbedding _).symm
  have hcoord (i : ι) :
      ∫⁻ x, nonnegativeFunctionEntropy (μ i) (fun y ↦ F (Function.update x i y) ^ 2)
          ∂Measure.pi μ ≤
        2 * ∫⁻ x, ENNReal.ofReal (‖G x i‖ ^ 2) ∂Measure.pi μ := by
    have hsec : ∀ᵐ x ∂Measure.pi μ,
        nonnegativeFunctionEntropy (μ i) (fun y ↦ F (Function.update x i y) ^ 2) ≤
          2 * ∫⁻ y, ENNReal.ofReal (‖G (Function.update x i y) i‖ ^ 2) ∂μ i := by
      filter_upwards [TauCeti.ae_memLp_pi_update μ i hFL] with x hxF
      have hs : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y ↦ F (Function.update x i y)) :=
        hg.comp (PiLp.contDiff_toLp.comp (contDiff_update _ x i))
      have hnorm (y : ℝ) : deriv (fun z ↦ F (Function.update x i z)) y ^ 2 =
          ‖G (Function.update x i y) i‖ ^ 2 := by
        rw [← PiLp.norm_fderiv_update g x i y (hg.differentiable (by simp) _),
          ← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs, sq_abs]
      simpa only [hnorm] using gaussian_logSobolev_oneDim _ hs hxF
    calc _ ≤ ∫⁻ x, 2 * ∫⁻ y, ENNReal.ofReal (‖G (Function.update x i y) i‖ ^ 2) ∂μ i
            ∂Measure.pi μ := lintegral_mono_ae hsec
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
          TauCeti.lintegral_pi_update μ (hGim i) i]
  have hsum : ∑ i, 2 * ∫⁻ x, ENNReal.ofReal (‖G x i‖ ^ 2) ∂Measure.pi μ =
      2 * ∫⁻ z, ENNReal.ofReal (‖fderiv ℝ g z‖ ^ 2) ∂ρ := by
    rw [← Finset.mul_sum, ← lintegral_finsetSum' _ fun i _ ↦ (hGim i).aemeasurable,
      ← hm.lintegral_comp_emb T.measurableEmbedding
        (fun z ↦ ENNReal.ofReal (‖fderiv ℝ g z‖ ^ 2))]
    congr 1
    refine lintegral_congr fun x ↦ ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ sq_nonneg _, ← PiLp.norm_sq_eq_of_L2,
      TauCeti.norm_gradient_eq_norm_fderiv]
    rfl
  rw [hEnt, ← hsum]
  exact (nonnegativeFunctionEntropy_pi_le μ hF2m (fun _ ↦ sq_nonneg _)
    hFL.integrable_sq).trans (Finset.sum_le_sum fun i _ ↦ hcoord i)

/-- **07.17**: Gaussian logarithmic Sobolev inequality with exact constant two.
The extended integral formulation does not assume in advance that the entropy is finite. -/
theorem gaussian_logSobolev {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (g : E → ℝ) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (hLp : MemLp g 2 (stdGaussian E)) :
    nonnegativeFunctionEntropy (stdGaussian E) (fun x ↦ g x ^ 2) ≤
      2 * ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ g x‖ ^ 2) ∂stdGaussian E := by
  let e : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃ₗᵢ[ℝ] E :=
    (stdOrthonormalBasis ℝ E).repr.symm
  have hmp : MeasurePreserving e (stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
      (stdGaussian E) := ⟨e.continuous.measurable, stdGaussian_map e⟩
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hnorm (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
      ‖fderiv ℝ (fun y ↦ g (e y)) x‖ = ‖fderiv ℝ g (e x)‖ := by
    have := e.toContinuousLinearEquiv.comp_right_fderiv (𝕜 := ℝ) (f := g) (x := x)
    simp only [Function.comp_def, LinearIsometryEquiv.coe_toContinuousLinearEquiv] at this
    rw [this]
    exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ e
  have key := gaussian_logSobolev_piLp (fun y ↦ g (e y)) (hg.comp e.contDiff)
    (by rw [map_pi_eq_stdGaussian]; exact hLp.comp_measurePreserving hmp)
  rw [map_pi_eq_stdGaussian] at key
  rw [← nonnegativeFunctionEntropy_comp_measurePreserving hmp hemb,
    ← hmp.lintegral_comp_emb hemb]
  simpa only [hnorm] using key

end CKMA
