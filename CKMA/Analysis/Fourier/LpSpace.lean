/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Fourier.LpSpace

import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Fourier.Continuous
/-!
# The inverse Fourier integral on `L¹ ∩ L²`

On a finite-dimensional real inner product space, the `L²` inverse Fourier transform of the class
of an integrable, square-integrable function agrees almost everywhere with its inverse Fourier
integral. This is the inverse counterpart of TauCeti's
`MeasureTheory.Integrable.coeFn_fourier_toLp`, proved in the same way from TauCeti's
`MeasureTheory.Lp.fourierInv_toTemperedDistribution_apply`. It gives Plancherel's theorem for the
inverse Fourier integral on `L¹ ∩ L²`.

## Main results

* `CKMA.Integrable.coeFn_fourierInv_toLp`: on `L¹ ∩ L²` the `L²` inverse Fourier transform is
  the inverse Fourier integral.
* `CKMA.Integrable.eLpNorm_fourierInv_two_eq`: Plancherel's theorem for the inverse Fourier
  integral on `L¹ ∩ L²`.
* `CKMA.Lp.norm_fourierInv_eq`: the `L²` inverse Fourier transform preserves the norm.
-/

public section

open MeasureTheory
open scoped ENNReal FourierTransform

namespace CKMA.Integrable

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] {f : E → F}

/-- On `L¹ ∩ L²` the inverse Fourier transform on `L²` is the inverse Fourier integral: for `f`
integrable and square integrable, the `L²` inverse Fourier transform of the class of `f` is almost
everywhere `𝓕⁻ f`. -/
theorem coeFn_fourierInv_toLp (hf : Integrable f) (hf₂ : MemLp f 2) :
    ⇑(𝓕⁻ (hf₂.toLp f) : Lp F 2 (volume : Measure E)) =ᵐ[volume] 𝓕⁻ f := by
  refine Lp.ae_eq_of_toTemperedDistribution_apply_eq _
    hf.continuous_fourierInv.locallyIntegrable fun φ => ?_
  rw [← Lp.fourierInv_toTemperedDistribution_eq]
  exact Lp.fourierInv_toTemperedDistribution_apply _ hf hf₂.coeFn_toLp φ

/-- **Plancherel's theorem for the inverse Fourier integral on `L¹ ∩ L²`.** The inverse Fourier
integral of an integrable, square integrable function has the same `L²` norm as the function. -/
theorem eLpNorm_fourierInv_two_eq (hf : Integrable f) (hf₂ : MemLp f 2) :
    eLpNorm (𝓕⁻ f) 2 volume = eLpNorm f 2 volume := by
  rw [← eLpNorm_congr_ae (coeFn_fourierInv_toLp hf hf₂), ← eLpNorm_congr_ae hf₂.coeFn_toLp,
    ← ENNReal.toReal_eq_toReal_iff' (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _), ← Lp.norm_def,
    ← Lp.norm_def]
  exact (Lp.fourierTransformₗᵢ E F).symm.norm_map _

end CKMA.Integrable

namespace CKMA.Lp

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- The inverse Fourier transform on `L²` preserves the norm; the inverse counterpart of
Mathlib's `MeasureTheory.Lp.norm_fourier_eq`. -/
theorem norm_fourierInv_eq (f : Lp F 2 (volume : Measure E)) : ‖𝓕⁻ f‖ = ‖f‖ :=
  (Lp.fourierTransformₗᵢ E F).symm.norm_map f

end CKMA.Lp
