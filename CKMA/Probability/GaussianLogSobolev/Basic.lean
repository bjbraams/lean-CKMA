/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import TauCeti.MeasureTheory.Integral.Entropy

/-!
# Extended entropy of a nonnegative function

`nonnegativeFunctionEntropy μ h = ENNReal.ofReal (∫ h) * ∫⁻ klFun (h / ∫ h)` is an extended
nonnegative entropy that needs no integrability of `h log h`. For a probability measure, a
nonnegative `h` with `h` and `h log h` integrable, it is `ENNReal.ofReal` of TauCeti's real entropy
`MeasureTheory.Measure.entropy μ h = ∫ h log h - (∫ h) log (∫ h)`.

## Main definitions

* `CKMA.nonnegativeFunctionEntropy`: extended entropy
  `ENNReal.ofReal (∫ h) * ∫⁻ klFun (h / ∫ h)`.

## Main results

* `CKMA.nonnegativeFunctionEntropy_eq_lintegral`: the entropy as one lower integral.
* `CKMA.nonnegativeFunctionEntropy_comp_measurePreserving`: invariance under measure-preserving
  embeddings.
* `CKMA.nonnegativeFunctionEntropy_eq_ofReal_entropy`: agreement with TauCeti's real entropy
  for probability measures and integrable `h`, `h log h`.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory InformationTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- Extended entropy `ENNReal.ofReal (∫ h) * ∫⁻ klFun (h / ∫ h)`, with no integrability or
probability hypothesis. The Bochner integral of a non-integrable function is `0`, and then the
entropy is `0`. For a finite measure of mass `c` and `m = ∫ h > 0` with `h ≥ 0` and `h log h`
integrable it equals `ENNReal.ofReal (∫ h log h - m log m + m (c - 1))`; it agrees with the
classical entropy `∫ h log h - m log m` for probability measures
(`nonnegativeFunctionEntropy_eq_ofReal_entropy`). -/
@[expose]
def nonnegativeFunctionEntropy (μ : Measure X) (h : X → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (∫ x, h x ∂μ) *
    ∫⁻ x, ENNReal.ofReal (klFun (h x / (∫ y, h y ∂μ))) ∂μ

/-- Defining formula of `nonnegativeFunctionEntropy`. -/
lemma nonnegativeFunctionEntropy_def (μ : Measure X) (h : X → ℝ) :
    nonnegativeFunctionEntropy μ h = ENNReal.ofReal (∫ x, h x ∂μ) *
      ∫⁻ x, ENNReal.ofReal (klFun (h x / (∫ y, h y ∂μ))) ∂μ :=
  rfl

/-- For a function of nonnegative mean, the entropy is the lower integral of the perspective
`m * klFun (h x / m)` of `klFun` at the mean `m`. -/
theorem nonnegativeFunctionEntropy_eq_lintegral {μ : Measure X} {h : X → ℝ}
    (hm : 0 ≤ ∫ x, h x ∂μ) :
    nonnegativeFunctionEntropy μ h =
      ∫⁻ x, ENNReal.ofReal ((∫ y, h y ∂μ) * klFun (h x / ∫ y, h y ∂μ)) ∂μ := by
  rw [nonnegativeFunctionEntropy, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp_rw [ENNReal.ofReal_mul hm]

/-- The entropy is invariant under composition with a measure-preserving embedding. -/
theorem nonnegativeFunctionEntropy_comp_measurePreserving {Y : Type*} [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} (hf : MeasurePreserving f μ ν)
    (he : MeasurableEmbedding f) (h : Y → ℝ) :
    nonnegativeFunctionEntropy μ (fun x ↦ h (f x)) = nonnegativeFunctionEntropy ν h := by
  simp only [nonnegativeFunctionEntropy, hf.integral_comp he]
  rw [hf.lintegral_comp_emb he (fun y ↦ ENNReal.ofReal (klFun (h y / ∫ z, h z ∂ν)))]

/-- Algebraic form of `m * klFun (t / m)`, valid at `t = 0`. -/
lemma mul_klFun_div_of_nonneg {t m : ℝ} (hm : 0 < m) (ht : 0 ≤ t) :
    m * klFun (t / m) = t * Real.log t - t * Real.log m + m - t := by
  rcases ht.eq_or_lt with rfl | ht0
  · simp [klFun, Real.log_zero, zero_div]
  · rw [klFun, Real.log_div ht0.ne' hm.ne']
    field_simp

/-- For a probability measure and a nonnegative `h` with `h` and `h log h` integrable, the
extended entropy is `ENNReal.ofReal` of TauCeti's real entropy `∫ h log h - (∫ h) log (∫ h)`. -/
theorem nonnegativeFunctionEntropy_eq_ofReal_entropy {μ : Measure X} [IsProbabilityMeasure μ]
    {h : X → ℝ} (hnn : ∀ x, 0 ≤ h x) (hint : Integrable h μ)
    (hlog : Integrable (fun x ↦ h x * Real.log (h x)) μ) :
    nonnegativeFunctionEntropy μ h = ENNReal.ofReal (μ.entropy h) := by
  set m : ℝ := ∫ x, h x ∂μ with hm_def
  have hm0 : 0 ≤ m := integral_nonneg hnn
  rcases hm0.eq_or_lt with hm | hm
  · have hae : h =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hnn hint).1 hm.symm
    have hlog0 : ∫ x, h x * Real.log (h x) ∂μ = 0 :=
      integral_eq_zero_of_ae (hae.mono fun x hx ↦ by simp [hx])
    rw [nonnegativeFunctionEntropy, ← hm_def, ← hm, Measure.entropy_def, ← hm_def, ← hm,
      hlog0]
    simp
  · have hpt : ∀ x, m * klFun (h x / m) = h x * Real.log (h x) - h x * Real.log m + m - h x :=
      fun x ↦ mul_klFun_div_of_nonneg hm (hnn x)
    have hA : Integrable (fun x ↦ h x * Real.log (h x) - h x * Real.log m) μ :=
      hlog.sub (hint.mul_const _)
    have hB : Integrable (fun x ↦ h x * Real.log (h x) - h x * Real.log m + m) μ :=
      hA.add (integrable_const _)
    have hint_rhs : Integrable (fun x ↦ h x * Real.log (h x) - h x * Real.log m + m - h x) μ :=
      hB.sub hint
    have hint_kl : Integrable (fun x ↦ klFun (h x / m)) μ :=
      (integrable_const_mul_iff (IsUnit.mk0 m hm.ne') (fun x ↦ klFun (h x / m))).1
        (hint_rhs.congr (ae_of_all _ fun x ↦ (hpt x).symm))
    have hval : m * ∫ x, klFun (h x / m) ∂μ = μ.entropy h := by
      rw [← integral_const_mul, integral_congr_ae (ae_of_all _ hpt), integral_sub hB hint,
        integral_add hA (integrable_const _), integral_sub hlog (hint.mul_const _),
        integral_mul_const, integral_const,
        Measure.entropy_def, ← hm_def]
      simp
    rw [nonnegativeFunctionEntropy, ← hm_def, ← ofReal_integral_eq_lintegral_ofReal hint_kl
      (ae_of_all _ fun x ↦ klFun_nonneg (div_nonneg (hnn x) hm.le)),
      ← ENNReal.ofReal_mul hm.le, hval]

end CKMA
