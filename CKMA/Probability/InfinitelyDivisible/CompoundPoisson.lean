/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.InfinitelyDivisible.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Convolution powers and compound Poisson laws

The characteristic function of an additive convolution power is the corresponding power of the
characteristic function. A finite jump intensity determines a compound Poisson probability, whose
characteristic function is the exponential of `∫ (exp(I t x) - 1)`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Complex
open scoped BigOperators NNReal ENNReal Nat Real

/-- Every convolution power of a probability measure is a probability measure. -/
lemma isProbabilityMeasure_convolutionPower (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ n : ℕ, IsProbabilityMeasure (convolutionPower μ n)
  | 0 => by
      rw [convolutionPower]
      infer_instance
  | n + 1 => by
      have := isProbabilityMeasure_convolutionPower μ n
      rw [convolutionPower]
      infer_instance

/-- The characteristic function of a convolution power is the power of the characteristic
function. -/
lemma charFun_convolutionPower (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) (t : ℝ) :
    charFun (convolutionPower μ n) t = charFun μ t ^ n := by
  induction n with
  | zero =>
      rw [convolutionPower]
      simp [charFun_dirac, exp_zero]
  | succ n ih =>
      have := isProbabilityMeasure_convolutionPower μ n
      rw [convolutionPower, charFun_conv, ih, pow_succ, mul_comm]

/-- A finite measure of real total mass zero is the zero measure. -/
lemma eq_zero_of_measure_real_univ_eq_zero {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (h : μ.real Set.univ = 0) : μ = 0 := by
  refine Measure.ext fun s hs => ?_
  have htop : μ Set.univ ≠ ∞ := measure_ne_top μ _
  have huniv : μ Set.univ = 0 := by
    rw [← ENNReal.ofReal_toReal htop, ← Measure.real, h, ENNReal.ofReal_zero]
  exact le_antisymm ((measure_mono (Set.subset_univ s)).trans_eq huniv) bot_le

/-- Poisson weight `exp(-c) cⁿ / n!`, as an extended nonnegative real. -/
def poissonWeight (c : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-c) * c ^ n / (n)!)

/-- The Poisson weights of a nonnegative intensity sum to one. -/
lemma poissonWeight_tsum {c : ℝ} (hc : 0 ≤ c) : ∑' n, poissonWeight c n = 1 := by
  have hnn : ∀ n, 0 ≤ Real.exp (-c) * c ^ n / (n)! := fun _ => by positivity
  have hsum : Summable fun n : ℕ => Real.exp (-c) * c ^ n / (n)! :=
    ((Real.summable_pow_div_factorial c).mul_left (Real.exp (-c))).congr fun n =>
      mul_div (Real.exp (-c)) (c ^ n) ((n)! : ℝ)
  unfold poissonWeight
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  have hsplit : ∑' n, Real.exp (-c) * c ^ n / (n)! =
      Real.exp (-c) * ∑' n, c ^ n / (n)! := by
    have hfun : (fun n => Real.exp (-c) * c ^ n / (n)!) =
        fun n => Real.exp (-c) * (c ^ n / (n)!) := by
      ext n
      exact (mul_div _ _ _).symm
    rw [hfun, tsum_mul_left]
  rw [hsplit]
  have hexp : ∑' n : ℕ, c ^ n / (n)! = Real.exp c := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [hexp, ← Real.exp_add, neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one]

/-- The normalized jump law of a finite intensity, with a Dirac mass at zero when the intensity
vanishes. -/
def normalizedJump (lam : Measure ℝ) : Measure ℝ :=
  let c := lam.real Set.univ
  if c = 0 then Measure.dirac 0 else (ENNReal.ofReal c)⁻¹ • lam

/-- The normalized jump of a finite measure is a probability measure. -/
lemma isProbabilityMeasure_normalizedJump {lam : Measure ℝ} [IsFiniteMeasure lam] :
    IsProbabilityMeasure (normalizedJump lam) := by
  by_cases hc : lam.real Set.univ = 0
  · rw [normalizedJump, ite_eq_left hc]
    infer_instance
  · rw [normalizedJump, ite_eq_right hc]
    refine ⟨?_⟩
    rw [Measure.smul_apply]
    have htop : lam Set.univ ≠ ∞ := measure_ne_top _ _
    have hcoe : lam Set.univ = ENNReal.ofReal (lam.real Set.univ) :=
      (ENNReal.ofReal_toReal htop).symm
    have hcpos : 0 < lam.real Set.univ :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hc)
    rw [hcoe, smul_eq_mul, ENNReal.inv_mul_cancel]
    · exact ne_of_gt ((ENNReal.ofReal_pos).2 hcpos)
    · exact ENNReal.ofReal_ne_top

/-- The compound Poisson law of a finite intensity on `ℝ`. -/
def compoundPoisson (lam : Measure ℝ) [IsFiniteMeasure lam] : Measure ℝ :=
  Measure.sum fun n : ℕ =>
    poissonWeight (lam.real Set.univ) n • convolutionPower (normalizedJump lam) n

/-- A compound Poisson law is a probability measure. -/
lemma isProbabilityMeasure_compoundPoisson {lam : Measure ℝ} [IsFiniteMeasure lam] :
    IsProbabilityMeasure (compoundPoisson lam) := by
  have hρ : IsProbabilityMeasure (normalizedJump lam) := isProbabilityMeasure_normalizedJump
  refine ⟨?_⟩
  rw [compoundPoisson, Measure.sum_apply_of_countable]
  simp_rw [Measure.smul_apply, smul_eq_mul]
  have hpow : ∀ n, convolutionPower (normalizedJump lam) n Set.univ = 1 := fun n => by
    have := isProbabilityMeasure_convolutionPower (normalizedJump lam) n
    simp
  simp_rw [hpow, mul_one]
  exact poissonWeight_tsum ENNReal.toReal_nonneg

/-- The exponential series weighted by Poisson probabilities sums to `exp(c(z - 1))`. -/
lemma tsum_poisson_mul_pow (c : ℝ) (z : ℂ) :
    ∑' n : ℕ, (Real.exp (-c) * c ^ n / (n)! : ℂ) * z ^ n = exp (c * (z - 1)) := by
  have hsum : HasSum (fun n : ℕ => ((c : ℂ) * z) ^ n / (n)!) (exp ((c : ℂ) * z)) := by
    simpa [← Complex.exp_eq_exp_ℂ] using
      NormedSpace.expSeries_div_hasSum_exp ((c : ℂ) * z)
  have hmul := hsum.mul_left (exp (-(c : ℂ)))
  have hfun : (fun n : ℕ => exp (-(c : ℂ)) * (((c : ℂ) * z) ^ n / (n)!)) =
      fun n : ℕ => (Real.exp (-c) * c ^ n / (n)! : ℂ) * z ^ n := by
    ext n
    rw [ofReal_exp, ofReal_neg]
    ring_nf
  rw [← hfun, hmul.tsum_eq, ← exp_add]
  congr 1
  ring

/-- `c` times one less than the normalized characteristic function is the compensated integral. -/
lemma mul_charFun_normalizedJump_sub_one {lam : Measure ℝ} [IsFiniteMeasure lam] (t : ℝ) :
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
  have hprob : IsProbabilityMeasure (compoundPoisson lam) := isProbabilityMeasure_compoundPoisson
  have hρ : IsProbabilityMeasure (normalizedJump lam) := isProbabilityMeasure_normalizedJump
  set c : ℝ := lam.real Set.univ
  set ρ : Measure ℝ := normalizedJump lam
  have hint : Integrable (fun x : ℝ => exp (t * x * I)) (compoundPoisson lam) := by
    refine (integrable_const (1 : ℂ)).mono (by fun_prop) (ae_of_all _ fun x => ?_)
    rw [norm_exp]
    simp [mul_assoc]
  rw [charFun_apply_real, compoundPoisson]
  rw [integral_sum_measure hint]
  have hterm : ∀ n, ∫ x, exp (t * x * I) ∂
      (poissonWeight c n • convolutionPower ρ n) =
      (Real.exp (-c) * c ^ n / (n)! : ℂ) * charFun ρ t ^ n := by
    intro n
    have := isProbabilityMeasure_convolutionPower ρ n
    rw [integral_smul_measure, poissonWeight, ENNReal.toReal_ofReal (by positivity),
      RCLike.real_smul_eq_coe_mul, ← charFun_apply_real, charFun_convolutionPower ρ n t]
    push_cast
    rw [← ofReal_neg, ← ofReal_exp]
    rfl
  rw [tsum_congr hterm]
  rw [tsum_poisson_mul_pow, mul_charFun_normalizedJump_sub_one]

end CKMA
