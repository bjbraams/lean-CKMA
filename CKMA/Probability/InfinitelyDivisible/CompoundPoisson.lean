/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.InfinitelyDivisible.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import TauCeti.Probability.Distributions.CompoundPoisson.Basic

/-!
# Compound Poisson laws of a finite jump intensity

A finite jump intensity `lam` on `ℝ` determines a compound Poisson probability, TauCeti's
`TauCeti.Probability.compoundPoissonMeasure` with rate `lam ℝ` and normalized jump law. Its
characteristic function is the exponential of `∫ (exp(I t x) - 1) ∂lam`, derived from TauCeti's
`charFun_compoundPoissonMeasure`.

## Main definitions

* `CKMA.compoundPoisson`: compound Poisson probability law associated to a finite jump measure.

## Main results

* `CKMA.isProbabilityMeasure_compoundPoisson`: a compound Poisson law is a probability measure.
* `CKMA.charFun_compoundPoisson`: the characteristic function of a compound Poisson law is
  `exp (∫ x, (exp (I * t * x) - 1) ∂ν)`.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Complex
open scoped BigOperators NNReal ENNReal Nat Real

/-- A finite measure of real total mass zero is the zero measure. -/
private lemma eq_zero_of_measure_real_univ_eq_zero {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (h : μ.real Set.univ = 0) : μ = 0 := by
  refine Measure.ext fun s hs => ?_
  have htop : μ Set.univ ≠ ∞ := measure_ne_top μ _
  have huniv : μ Set.univ = 0 := by
    rw [← ENNReal.ofReal_toReal htop, ← Measure.real, h, ENNReal.ofReal_zero]
  exact le_antisymm ((measure_mono (Set.subset_univ s)).trans_eq huniv) bot_le

namespace InfinitelyDivisible

/-- The normalized jump law of a finite intensity, with a Dirac mass at zero when the intensity
vanishes. -/
@[expose]
def normalizedJump (lam : Measure ℝ) : Measure ℝ :=
  let c := lam.real Set.univ
  if c = 0 then Measure.dirac 0 else (ENNReal.ofReal c)⁻¹ • lam

/-- Defining formula of `normalizedJump`. -/
lemma normalizedJump_def (lam : Measure ℝ) :
    normalizedJump lam = if lam.real Set.univ = 0 then Measure.dirac 0
      else (ENNReal.ofReal (lam.real Set.univ))⁻¹ • lam :=
  rfl

/-- The normalized jump of a finite measure is a probability measure. -/
private lemma isProbabilityMeasure_normalizedJump {lam : Measure ℝ} [IsFiniteMeasure lam] :
    IsProbabilityMeasure (normalizedJump lam) := by
  by_cases hc : lam.real Set.univ = 0
  · rw [normalizedJump, ite_eq_left hc]
    infer_instance
  · rw [normalizedJump, ite_eq_right hc]
    refine ⟨?_⟩
    rw [smul_apply]
    have htop : lam Set.univ ≠ ∞ := measure_ne_top _ _
    have hcoe : lam Set.univ = ENNReal.ofReal (lam.real Set.univ) :=
      (ENNReal.ofReal_toReal htop).symm
    have hcpos : 0 < lam.real Set.univ :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hc)
    rw [hcoe, smul_eq_mul, ENNReal.inv_mul_cancel]
    · exact ne_of_gt ((ENNReal.ofReal_pos).2 hcpos)
    · exact ENNReal.ofReal_ne_top

end InfinitelyDivisible

open InfinitelyDivisible

/-- The compound Poisson law of a finite intensity `lam` on `ℝ`: TauCeti's
`compoundPoissonMeasure` with rate `lam ℝ` and jump law `lam / lam ℝ` (the point mass at zero
when `lam = 0`). For an infinite `lam` the rate is the junk value `0`, and the law is `δ₀`. -/
@[expose]
def compoundPoisson (lam : Measure ℝ) : Measure ℝ :=
  TauCeti.Probability.compoundPoissonMeasure (lam.real Set.univ).toNNReal (normalizedJump lam)

/-- Defining formula of `compoundPoisson`. -/
lemma compoundPoisson_def (lam : Measure ℝ) :
    compoundPoisson lam = TauCeti.Probability.compoundPoissonMeasure
      (lam.real Set.univ).toNNReal (normalizedJump lam) :=
  rfl

/-- A compound Poisson law is a probability measure. -/
lemma isProbabilityMeasure_compoundPoisson {lam : Measure ℝ} [IsFiniteMeasure lam] :
    IsProbabilityMeasure (compoundPoisson lam) := by
  have := isProbabilityMeasure_normalizedJump (lam := lam)
  rw [compoundPoisson_def]
  infer_instance

/-- `c` times one less than the normalized characteristic function is the compensated integral. -/
private lemma mul_charFun_normalizedJump_sub_one {lam : Measure ℝ} [IsFiniteMeasure lam] (t : ℝ) :
    (lam.real Set.univ : ℂ) * (charFun (normalizedJump lam) t - 1) =
      ∫ x, exp (I * t * x) - 1 ∂lam := by
  set c : ℝ := lam.real Set.univ
  by_cases hc : c = 0
  · have hlam : lam = 0 := eq_zero_of_measure_real_univ_eq_zero (by simpa [c] using hc)
    have hρ : normalizedJump lam = Measure.dirac 0 := by
      rw [normalizedJump, ite_eq_left hc]
    simp [hlam, hc]
  · have hcpos : 0 < c := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hc)
    have hρ : normalizedJump lam = (ENNReal.ofReal c)⁻¹ • lam := by
      rw [normalizedJump, ite_eq_right hc]
    have hint : Integrable (fun x : ℝ => exp (t * x * I)) lam := by
      refine (integrable_const (1 : ℂ)).mono (by fun_prop) (ae_of_all _ fun x => ?_)
      rw [norm_exp]
      simp [mul_assoc]
    have hexp : ∀ x : ℝ, exp (t * x * I) = exp (I * t * x) := fun x => by
      congr 1
      ring
    rw [hρ, charFun_apply_real, integral_smul_measure, RCLike.real_smul_eq_coe_mul]
    have hto : ((ENNReal.ofReal c)⁻¹).toReal = c⁻¹ := by
      simp [ENNReal.toReal_inv, ENNReal.toReal_ofReal hcpos.le]
    rw [hto, integral_congr_ae (ae_of_all _ hexp)]
    have hint' : Integrable (fun x : ℝ => exp (I * t * x)) lam :=
      hint.congr (ae_of_all _ hexp)
    rw [integral_sub hint' (integrable_const _), integral_const]
    have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    rw [RCLike.real_smul_eq_coe_mul, mul_sub, ← mul_assoc, RCLike.ofReal_inv]
    field_simp [hcC]
    rfl

/-- The characteristic function of a compound Poisson law. -/
lemma charFun_compoundPoisson {lam : Measure ℝ} [IsFiniteMeasure lam] (t : ℝ) :
    charFun (compoundPoisson lam) t = exp (∫ x, exp (I * t * x) - 1 ∂lam) := by
  have := isProbabilityMeasure_normalizedJump (lam := lam)
  rw [compoundPoisson_def, TauCeti.Probability.charFun_compoundPoissonMeasure,
    Real.coe_toNNReal _ measureReal_nonneg, mul_charFun_normalizedJump_sub_one]

end CKMA
