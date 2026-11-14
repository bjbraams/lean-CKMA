/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Bernstein concentration inequality

Exponential series remainder bounds and the scalar Bernstein concentration inequality for
independent centered bounded random variables.

## Main definitions

No new public definitions are introduced in this file.

## Main results

* `CKMA.bernstein_of_bounded`: two-sided Bernstein tail bound for independent centered
  almost-everywhere bounded summands.

## Notation

No new notation is introduced in this file.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped NNReal ENNReal BigOperators
open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `2 * 3 ^ k ≤ (k + 2)!`, the coefficient comparison for the exponential remainder. -/
private lemma two_mul_three_pow_le_factorial (k : ℕ) : 2 * 3 ^ k ≤ (k + 2).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      2 * 3 ^ (k + 1) = 3 * (2 * 3 ^ k) := by ring
      _ ≤ 3 * (k + 2).factorial := Nat.mul_le_mul_left _ ih
      _ ≤ (k + 3) * (k + 2).factorial := Nat.mul_le_mul_right _ (by omega)
      _ = (k + 1 + 2).factorial := by
        rw [show k + 1 + 2 = (k + 2).succ by omega, Nat.factorial_succ (k + 2)]

/-- Remainder coefficients of `exp` are at most a geometric series of ratio `1 / 3`. -/
private lemma two_div_factorial_le_inv_three_pow (k : ℕ) :
    (2 : ℝ) / (k + 2).factorial ≤ (1 / 3 : ℝ) ^ k := by
  have hcast : (2 : ℝ) * 3 ^ k ≤ (k + 2).factorial := mod_cast two_mul_three_pow_le_factorial k
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((k + 2).factorial : ℝ))]
  calc
    (2 : ℝ) = 2 * 3 ^ k / 3 ^ k := by rw [mul_div_assoc, div_self h3.ne', mul_one]
    _ ≤ ((k + 2).factorial : ℝ) / 3 ^ k := div_le_div_of_nonneg_right hcast h3.le
    _ = (1 / 3) ^ k * (k + 2).factorial := by
      rw [div_eq_mul_inv, ← inv_pow, ← one_div, mul_comm]

/-- The tail of the exponential series is bounded by the Bernstein quadratic, for `|u| < 3`. -/
private lemma exp_remainder_tsum_le (u : ℝ) (hu : |u| < 3) :
    ∑' k : ℕ, u ^ (k + 2) / (k + 2).factorial ≤ u ^ 2 / (2 * (1 - |u| / 3)) := by
  have hsum : Summable fun n : ℕ ↦ u ^ n / n.factorial := Real.summable_pow_div_factorial u
  have hsumAbs : Summable fun n : ℕ ↦ |u| ^ n / n.factorial :=
    Real.summable_pow_div_factorial |u|
  have htail : Summable fun k : ℕ ↦ u ^ (k + 2) / (k + 2).factorial :=
    (summable_nat_add_iff 2).2 hsum
  have htailAbs : Summable fun k : ℕ ↦ |u| ^ (k + 2) / (k + 2).factorial :=
    (summable_nat_add_iff 2).2 hsumAbs
  have hr0 : 0 ≤ |u| / 3 := div_nonneg (abs_nonneg _) (by norm_num)
  have hr : |u| / 3 < 1 := (div_lt_one (by norm_num : (0 : ℝ) < 3)).2 hu
  have hrAbs : |(|u| / 3)| < 1 := by rwa [abs_of_nonneg hr0]
  have hgeom : Summable fun k : ℕ ↦ (|u| / 3) ^ k := summable_geometric_of_abs_lt_one hrAbs
  have heq (k : ℕ) : |u| ^ (k + 2) / (k + 2).factorial =
      u ^ 2 / 2 * (2 * |u| ^ k / (k + 2).factorial) := by
    have htwo : u ^ 2 / 2 * (2 * |u| ^ k) = u ^ 2 * |u| ^ k := by
      rw [← mul_assoc, div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [pow_add, sq_abs, mul_comm (|u| ^ k), ← htwo, mul_div_assoc]
  have hcoeff (k : ℕ) : 2 * |u| ^ k / (k + 2).factorial ≤ (|u| / 3) ^ k := by
    calc
      2 * |u| ^ k / (k + 2).factorial = |u| ^ k * (2 / (k + 2).factorial) := by
        rw [mul_comm (2 : ℝ), mul_div_assoc]
      _ ≤ |u| ^ k * (1 / 3) ^ k :=
        mul_le_mul_of_nonneg_left (two_div_factorial_le_inv_three_pow k)
          (pow_nonneg (abs_nonneg _) _)
      _ = (|u| / 3) ^ k := by rw [← mul_pow, mul_one_div]
  have hnonneg (k : ℕ) : 0 ≤ 2 * |u| ^ k / (k + 2).factorial :=
    div_nonneg (mul_nonneg (by norm_num) (pow_nonneg (abs_nonneg _) _)) (Nat.cast_nonneg _)
  have hcoeffSum : Summable fun k : ℕ ↦ 2 * |u| ^ k / (k + 2).factorial :=
    hgeom.of_nonneg_of_le hnonneg hcoeff
  have hstep1 : ∑' k, u ^ (k + 2) / (k + 2).factorial ≤
      ∑' k, |u| ^ (k + 2) / (k + 2).factorial :=
    htail.tsum_le_tsum (fun k ↦ div_le_div_of_nonneg_right
      ((le_abs_self _).trans_eq (abs_pow u (k + 2))) (Nat.cast_nonneg _)) htailAbs
  have hstep2 : ∑' k, |u| ^ (k + 2) / (k + 2).factorial =
      u ^ 2 / 2 * ∑' k, 2 * |u| ^ k / (k + 2).factorial := by
    rw [tsum_congr heq, tsum_mul_left]
  have hstep3 : u ^ 2 / 2 * ∑' k, 2 * |u| ^ k / (k + 2).factorial ≤
      u ^ 2 / 2 * ∑' k, (|u| / 3) ^ k :=
    mul_le_mul_of_nonneg_left (hcoeffSum.tsum_le_tsum hcoeff hgeom)
      (div_nonneg (sq_nonneg _) (by norm_num))
  have hstep4 : u ^ 2 / 2 * ∑' k, (|u| / 3) ^ k =
      u ^ 2 / (2 * (1 - |u| / 3)) := by
    rw [tsum_geometric_of_abs_lt_one hrAbs, ← div_eq_mul_inv, div_div]
  exact hstep1.trans (hstep2.trans_le (hstep3.trans_eq hstep4))

/-- For `|u| < 3`, the exponential admits the quadratic Bernstein upper bound. -/
private lemma exp_le_one_add_sq_div (u : ℝ) (hu : |u| < 3) :
    Real.exp u ≤ 1 + u + u ^ 2 / (2 * (1 - |u| / 3)) := by
  have hsum : Summable fun n : ℕ ↦ u ^ n / n.factorial := Real.summable_pow_div_factorial u
  have hexp : Real.exp u = ∑' n : ℕ, u ^ n / n.factorial := by
    rw [Real.exp_eq_exp_ℝ]
    exact congr_fun NormedSpace.exp_eq_tsum_div u
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hhead : ∑ i ∈ Finset.range 2, u ^ i / i.factorial = 1 + u := by
    simp [Finset.sum_range_succ, Nat.factorial_zero, Nat.factorial_one]
  rw [hhead] at hsplit
  rw [hexp, ← hsplit]
  exact add_le_add le_rfl (exp_remainder_tsum_le u hu)

/-- One-sided Chernoff bound from Markov's inequality on a nonnegative exponential. -/
private lemma measure_ge_le_exp_mul_integral [IsProbabilityMeasure μ] {S : Ω → ℝ} {l t : ℝ}
    (hl : 0 ≤ l) (hS : Integrable (fun ω ↦ Real.exp (l * S ω)) μ) :
    μ {ω | t ≤ S ω} ≤
      ENNReal.ofReal (Real.exp (-l * t) * ∫ ω, Real.exp (l * S ω) ∂μ) := by
  have hsub : {ω | t ≤ S ω} ⊆ {ω | Real.exp (l * t) ≤ Real.exp (l * S ω)} := by
    intro ω hω
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hl)
  have hε : 0 < Real.exp (l * t) := Real.exp_pos _
  have hf_nonneg : 0 ≤ᵐ[μ] fun ω ↦ Real.exp (l * S ω) :=
    Filter.Eventually.of_forall fun _ ↦ (Real.exp_pos _).le
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hf_nonneg hS (Real.exp (l * t))
  have hdiv : μ.real {ω | Real.exp (l * t) ≤ Real.exp (l * S ω)} ≤
      (∫ ω, Real.exp (l * S ω) ∂μ) / Real.exp (l * t) := by
    rw [le_div_iff₀ hε]
    simpa [mul_comm] using hmarkov
  have hfin : μ {ω | Real.exp (l * t) ≤ Real.exp (l * S ω)} ≠ ∞ := measure_ne_top _ _
  calc
    μ {ω | t ≤ S ω} ≤ μ {ω | Real.exp (l * t) ≤ Real.exp (l * S ω)} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {ω | Real.exp (l * t) ≤ Real.exp (l * S ω)}) := by
      rw [measureReal_def, ENNReal.ofReal_toReal hfin]
    _ ≤ ENNReal.ofReal ((∫ ω, Real.exp (l * S ω) ∂μ) / Real.exp (l * t)) :=
      ENNReal.ofReal_le_ofReal hdiv
    _ = ENNReal.ofReal (Real.exp (-l * t) * ∫ ω, Real.exp (l * S ω) ∂μ) := by
      congr 1
      rw [div_eq_mul_inv, mul_comm, ← Real.exp_neg, neg_mul]

/-- A measurable variable bounded by `b` has an integrable square. -/
private lemma integrable_sq_of_ae_bound [IsProbabilityMeasure μ] {X : Ω → ℝ} (hm : Measurable X)
    {b : ℝ} (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ b) :
    Integrable (fun ω ↦ X ω ^ 2) μ := by
  refine Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable (b ^ 2) ?_
  filter_upwards [hbound] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc
    X ω ^ 2 = |X ω| ^ 2 := (sq_abs _).symm
    _ ≤ b ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hω 2

/-- Bernstein moment-generating bound for one centered variable bounded by `b`. -/
private lemma integral_exp_le_bernstein [IsProbabilityMeasure μ] {X : Ω → ℝ} (hm : Measurable X)
    (hc : ∫ ω, X ω ∂μ = 0) {b l : ℝ} (hl : 0 ≤ l) (hlb : l * b < 3)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ b) :
    ∫ ω, Real.exp (l * X ω) ∂μ ≤
      Real.exp ((∫ ω, X ω ^ 2 ∂μ) * l ^ 2 / (2 * (1 - b * l / 3))) := by
  have hden : 0 < 1 - b * l / 3 := by
    have : b * l < 3 := by rwa [mul_comm]
    linarith
  let c := l ^ 2 / (2 * (1 - b * l / 3))
  have hX : Integrable X μ := Integrable.of_bound hm.aestronglyMeasurable b hbound
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) μ := integrable_sq_of_ae_bound hm hbound
  have hlin : Integrable (fun ω ↦ 1 + l * X ω) μ := (integrable_const 1).add (hX.const_mul l)
  have hquad : Integrable (fun ω ↦ c * X ω ^ 2) μ := hX2.const_mul c
  have hRHS : Integrable (fun ω ↦ 1 + l * X ω + c * X ω ^ 2) μ := hlin.add hquad
  have hexp : Integrable (fun ω ↦ Real.exp (l * X ω)) μ := by
    refine Integrable.of_bound ((hm.const_mul l).exp).aestronglyMeasurable (Real.exp (l * b)) ?_
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_abs_le hω) hl)
  have hpoint : ∀ᵐ ω ∂μ, Real.exp (l * X ω) ≤ 1 + l * X ω + c * X ω ^ 2 := by
    filter_upwards [hbound] with ω hω
    have habs : |l * X ω| ≤ l * b := by
      rw [abs_mul, abs_of_nonneg hl]
      exact mul_le_mul_of_nonneg_left hω hl
    have hlt : |l * X ω| < 3 := habs.trans_lt hlb
    have hrem := exp_le_one_add_sq_div (l * X ω) hlt
    have hcX : c * X ω ^ 2 = l ^ 2 * X ω ^ 2 / (2 * (1 - b * l / 3)) := by
      dsimp [c]
      ring
    have hsq : (l * X ω) ^ 2 / (2 * (1 - |l * X ω| / 3)) ≤ c * X ω ^ 2 := by
      rw [hcX, show (l * X ω) ^ 2 = l ^ 2 * X ω ^ 2 by ring]
      refine div_le_div_of_nonneg_left (by positivity)
        (mul_pos (by norm_num : (0 : ℝ) < 2) hden) ?_
      gcongr
      linarith
    exact hrem.trans (add_le_add le_rfl hsq)
  have hint : ∫ ω, 1 + l * X ω + c * X ω ^ 2 ∂μ =
      1 + c * ∫ ω, X ω ^ 2 ∂μ := by
    rw [integral_add hlin hquad, integral_add (integrable_const 1) (hX.const_mul l),
      integral_const, integral_const_mul, integral_const_mul, hc]
    simp
  calc
    ∫ ω, Real.exp (l * X ω) ∂μ ≤ ∫ ω, 1 + l * X ω + c * X ω ^ 2 ∂μ :=
      integral_mono_ae hexp hRHS hpoint
    _ = 1 + c * ∫ ω, X ω ^ 2 ∂μ := hint
    _ ≤ Real.exp (c * ∫ ω, X ω ^ 2 ∂μ) := by
      have h1 := Real.add_one_le_exp (c * ∫ ω, X ω ^ 2 ∂μ)
      rwa [add_comm] at h1
    _ = Real.exp ((∫ ω, X ω ^ 2 ∂μ) * l ^ 2 / (2 * (1 - b * l / 3))) := by
      congr 1
      dsimp [c]
      ring

/-- Independence factorizes the moment generating function of a finite sum. -/
private lemma integral_exp_sum_eq_prod {n : ℕ} {X : Fin n → Ω → ℝ} {l : ℝ}
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ) :
    ∫ ω, Real.exp (l * ∑ i, X i ω) ∂μ = ∏ i, ∫ ω, Real.exp (l * X i ω) ∂μ := by
  have hfun (ω : Ω) : Real.exp (l * ∑ i, X i ω) = ∏ i, Real.exp (l * X i ω) := by
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [hfun]
  refine hi.integral_fun_prod_comp (f := fun _ (x : ℝ) ↦ Real.exp (l * x))
    (fun i ↦ (hm i).aemeasurable) ?_
  intro i
  exact ((measurable_id.const_mul l).exp).aestronglyMeasurable

/-- The optimizing Chernoff parameter reproduces the Bernstein exponent. -/
private lemma bernstein_exponent_eq {v b t : ℝ} (hv : 0 < v) (hb : 0 ≤ b) (ht : 0 ≤ t) :
    t / (v + b * t / 3) * t -
        v * (t / (v + b * t / 3)) ^ 2 /
          (2 * (1 - b * (t / (v + b * t / 3)) / 3)) =
      t ^ 2 / (2 * (v + b * t / 3)) := by
  set D : ℝ := v + b * t / 3
  have hD : 0 < D := add_pos_of_pos_of_nonneg hv
    (div_nonneg (mul_nonneg hb ht) (by norm_num : (0 : ℝ) ≤ 3))
  set l : ℝ := t / D
  have hden : 1 - b * l / 3 = v / D := by
    dsimp [l]
    field_simp [hD.ne']
    ring
  rw [hden]
  dsimp [l]
  field_simp [hD.ne', hv.ne']
  ring

/-- One-sided Bernstein tail, under a strictly positive sum of second moments. -/
private lemma measure_ge_le_bernstein_tail [IsProbabilityMeasure μ] {n : ℕ} (X : Fin n → Ω → ℝ)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hc : ∀ i, ∫ ω, X i ω ∂μ = 0) {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (hv : 0 < ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) :
    μ {ω | t ≤ ∑ i, X i ω} ≤ ENNReal.ofReal
      (Real.exp (-(t ^ 2 / (2 * ((∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) + b * t / 3))))) := by
  set v : ℝ := ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ
  set D : ℝ := v + b * t / 3
  set l : ℝ := t / D
  have hD : 0 < D := add_pos_of_pos_of_nonneg hv
    (div_nonneg (mul_nonneg hb ht) (by norm_num : (0 : ℝ) ≤ 3))
  have hl : 0 ≤ l := div_nonneg ht hD.le
  have hlb : l * b < 3 := by
    have hmul : l * b = b * t / D := by
      dsimp [l]
      ring
    rw [hmul, div_lt_iff₀ hD]
    dsimp [D]
    linarith [mul_pos hv (by norm_num : (0 : ℝ) < 3)]
  have hSmeas : Measurable (fun ω ↦ ∑ i, X i ω) :=
    Finset.measurable_sum Finset.univ fun i _ ↦ hm i
  have hSbound : ∀ᵐ ω ∂μ, |∑ i, X i ω| ≤ (n : ℝ) * b := by
    filter_upwards [ae_all_iff.2 hbound] with ω hω
    calc
      |∑ i, X i ω| ≤ ∑ i, |X i ω| := by
        simpa only [Real.norm_eq_abs] using norm_sum_le Finset.univ fun i ↦ X i ω
      _ ≤ ∑ i, b := Finset.sum_le_sum fun i _ ↦ hω i
      _ = (n : ℝ) * b := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hSint : Integrable (fun ω ↦ Real.exp (l * ∑ i, X i ω)) μ := by
    refine Integrable.of_bound (hSmeas.const_mul l).exp.aestronglyMeasurable
      (Real.exp (l * (n : ℝ) * b)) ?_
    filter_upwards [hSbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      l * ∑ i, X i ω ≤ l * |∑ i, X i ω| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hl
      _ ≤ l * ((n : ℝ) * b) := mul_le_mul_of_nonneg_left hω hl
      _ = l * (n : ℝ) * b := by ring
  have hmgf : ∫ ω, Real.exp (l * ∑ i, X i ω) ∂μ ≤
      Real.exp (v * l ^ 2 / (2 * (1 - b * l / 3))) := by
    rw [integral_exp_sum_eq_prod hm hi]
    calc
      ∏ i, ∫ ω, Real.exp (l * X i ω) ∂μ ≤
          ∏ i, Real.exp ((∫ ω, (X i ω) ^ 2 ∂μ) * l ^ 2 / (2 * (1 - b * l / 3))) :=
        Finset.prod_le_prod₀ (fun i _ ↦ integral_nonneg fun _ ↦ (Real.exp_pos _).le)
          fun i _ ↦ integral_exp_le_bernstein (hm i) (hc i) hl hlb (hbound i)
      _ = Real.exp (∑ i, (∫ ω, (X i ω) ^ 2 ∂μ) * l ^ 2 / (2 * (1 - b * l / 3))) := by
        rw [← Real.exp_sum]
      _ = Real.exp (v * l ^ 2 / (2 * (1 - b * l / 3))) := by
        congr 1
        unfold v
        trans ∑ i, (∫ ω, (X i ω) ^ 2 ∂μ) * (l ^ 2 / (2 * (1 - b * l / 3)))
        · refine Finset.sum_congr rfl fun _ _ ↦ ?_
          rw [mul_div_assoc]
        · rw [← Finset.sum_mul, mul_div_assoc']
  have hchernoff := measure_ge_le_exp_mul_integral (t := t) hl hSint
  refine hchernoff.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    Real.exp (-l * t) * ∫ ω, Real.exp (l * ∑ i, X i ω) ∂μ ≤
        Real.exp (-l * t) * Real.exp (v * l ^ 2 / (2 * (1 - b * l / 3))) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-(l * t - v * l ^ 2 / (2 * (1 - b * l / 3)))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (-(t ^ 2 / (2 * D))) := by
      congr 1
      apply congrArg Neg.neg
      unfold l D
      exact bernstein_exponent_eq hv hb ht

/-- Scalar Bernstein inequality for independent bounded centered summands. -/
lemma bernstein_of_bounded [IsProbabilityMeasure μ] {n : ℕ} (X : Fin n → Ω → ℝ)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hc : ∀ i, ∫ ω, X i ω ∂μ = 0) {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b) :
    μ {ω | t ≤ |∑ i, X i ω|} ≤ ENNReal.ofReal
      (2 * Real.exp (-(t ^ 2 / (2 * ((∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) + b * t / 3))))) := by
  rcases eq_or_lt_of_le ht with rfl | ht0
  · have hset : {ω | (0 : ℝ) ≤ |∑ i, X i ω|} = Set.univ := by
      ext ω
      simp [abs_nonneg]
    rw [hset, measure_univ]
    have hzero : (0 : ℝ) ^ 2 /
        (2 * ((∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) + b * 0 / 3)) = 0 := by
      simp
    rw [hzero, neg_zero, Real.exp_zero, mul_one]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  set v : ℝ := ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ
  have hv0 : 0 ≤ v := Finset.sum_nonneg fun _ _ ↦ integral_nonneg fun _ ↦ sq_nonneg _
  rcases eq_or_lt_of_le hv0 with hv | hv
  · have hint (i : Fin n) : ∫ ω, (X i ω) ^ 2 ∂μ = 0 := by
      have hsum : ∑ j, ∫ ω, (X j ω) ^ 2 ∂μ = 0 := hv.symm
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ integral_nonneg fun _ ↦ sq_nonneg _)).1 hsum i (Finset.mem_univ _)
    have hX0 (i : Fin n) : X i =ᵐ[μ] 0 := by
      have hsq : (fun ω ↦ (X i ω) ^ 2) =ᵐ[μ] 0 :=
        (integral_eq_zero_iff_of_nonneg_ae (ae_of_all μ fun _ ↦ sq_nonneg _)
          (integrable_sq_of_ae_bound (hm i) (hbound i))).1 (hint i)
      filter_upwards [hsq] with ω hω
      exact sq_eq_zero_iff.mp hω
    have hS : μ {ω | ∑ i, X i ω ≠ 0} = 0 := by
      rw [← ae_iff]
      filter_upwards [ae_all_iff.2 hX0] with ω hω
      simp [hω]
    have hnull : μ {ω | t ≤ |∑ i, X i ω|} = 0 := by
      refine measure_mono_null ?_ hS
      intro ω hω
      rw [Set.mem_ofPred_eq]
      intro hzero
      have : t ≤ 0 := by simpa [hzero, abs_zero] using hω
      exact absurd this (not_le.mpr ht0)
    rw [hnull]
    exact zero_le
  · have htail : μ {ω | t ≤ ∑ i, X i ω} ≤ ENNReal.ofReal
        (Real.exp (-(t ^ 2 / (2 * (v + b * t / 3))))) :=
      measure_ge_le_bernstein_tail X hm hi hc hb ht hbound hv
    have hnegX : iIndepFun (fun i ↦ (- ·) ∘ X i) μ :=
      hi.comp (fun _ ↦ Neg.neg) fun _ ↦ measurable_neg
    have htailNeg : μ {ω | t ≤ ∑ i, -X i ω} ≤ ENNReal.ofReal
        (Real.exp (-(t ^ 2 / (2 * (v + b * t / 3))))) := by
      have hvar : ∑ i, ∫ ω, (-X i ω) ^ 2 ∂μ = v := by
        simp [v]
      simpa [hvar] using
        measure_ge_le_bernstein_tail (fun i ω ↦ -X i ω)
          (fun i ↦ (hm i).neg) hnegX
          (fun i ↦ by rw [integral_neg, hc i, neg_zero]) hb ht
          (fun i ↦ (hbound i).mono fun ω hω ↦ by simpa [abs_neg] using hω)
          (by simpa [hvar] using hv)
    have hunion : μ {ω | t ≤ |∑ i, X i ω|} ≤
        μ {ω | t ≤ ∑ i, X i ω} + μ {ω | t ≤ -(∑ i, X i ω)} := by
      refine le_trans (measure_mono ?_) (measure_union_le _ _)
      intro ω hω
      rw [Set.mem_ofPred_eq] at hω
      rcases le_total 0 (∑ i, X i ω) with hs | hs
      · left
        rw [Set.mem_ofPred_eq]
        rwa [abs_of_nonneg hs] at hω
      · right
        rw [Set.mem_ofPred_eq]
        rwa [abs_of_nonpos hs] at hω
    have hnegSet : μ {ω | t ≤ ∑ i, -X i ω} = μ {ω | t ≤ -(∑ i, X i ω)} := by
      simp [Finset.sum_neg_distrib]
    calc
      μ {ω | t ≤ |∑ i, X i ω|} ≤
          μ {ω | t ≤ ∑ i, X i ω} + μ {ω | t ≤ -(∑ i, X i ω)} := hunion
      _ ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * (v + b * t / 3))))) +
          ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * (v + b * t / 3))))) := by
        rw [← hnegSet]
        exact add_le_add htail htailNeg
      _ = ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / (2 * (v + b * t / 3))))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        congr 1
        ring
      _ = ENNReal.ofReal
          (2 * Real.exp (-(t ^ 2 / (2 * ((∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) + b * t / 3))))) := by
        simp [v]

end CKMA
