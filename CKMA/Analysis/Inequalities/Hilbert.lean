/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Hilbert integral and sequence inequalities

Hilbert's bilinear inequality on the positive half-line and its sequence analogue,
with conjugate exponents and constant `pi / sin (pi / p)`. The discrete denominator
`m+n+2` corresponds to positive integers `m+1,n+1`. Nonnegative integrals and sums
preserve infinite values; the input norms use Mathlib's `MemLp` and `eLpNorm`.

The constant is the Beta integral `Beta(b, 1 - b)`. The substitution `t = u / (1 - u)`
and Euler's reflection formula are Mathlib's `Complex.betaIntegral` and
`Real.Gamma_mul_Gamma_one_sub`. The bilinear bound is Hölder's inequality in
`ENNReal`, and the sequence bound compares the decreasing kernel with that integral.
Source: GAPS 11.37.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Set intervalIntegral
open scoped Classical ENNReal

/-- Hilbert's sharp constant at exponent `p`. -/
def hilbertConstant (p : ℝ) : ℝ := Real.pi / Real.sin (Real.pi / p)

/-- Real power `x ^ c` for `x > 0`, and `0` otherwise. -/
private def rpowPos (c x : ℝ) : ℝ :=
  if 0 < x then Real.exp (c * Real.log x) else 0

/-- `rpowPos` agrees with `Real.rpow` on positive bases. -/
private lemma rpowPos_eq {c x : ℝ} (hx : 0 < x) : rpowPos c x = x ^ c := by
  simp [rpowPos, hx, Real.rpow_def_of_pos hx, mul_comm]

/-- `rpowPos` is nonnegative. -/
private lemma rpowPos_nonneg (c x : ℝ) : 0 ≤ rpowPos c x := by
  unfold rpowPos
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

/-- `rpowPos` is positive on a positive base. -/
private lemma rpowPos_pos {c x : ℝ} (hx : 0 < x) : 0 < rpowPos c x := by
  simp [rpowPos, hx, Real.exp_pos]

/-- `rpowPos` is measurable in the base. -/
@[fun_prop]
private lemma measurable_rpowPos (c : ℝ) : Measurable (rpowPos c) := by
  unfold rpowPos
  exact Measurable.ite measurableSet_Ioi
    (Real.measurable_exp.comp (measurable_const.mul Real.measurable_log)) measurable_const

/-- Integrand `u ^ (b - 1) * (1 - u) ^ (-b)` of the Beta reflection identity. -/
private def betaIntegrand (b u : ℝ) : ℝ :=
  u ^ (b - 1) * (1 - u) ^ (-b)

/-- Integrand `t ^ (b - 1) / (1 + t)` on the positive half-line. -/
private def betaTail (b t : ℝ) : ℝ :=
  t ^ (b - 1) / (1 + t)

/-- The complex Beta integrand agrees with the real one on `[0, 1]`. -/
private lemma betaIntegrand_eqOn {b : ℝ} :
    EqOn (fun x : ℝ => (x : ℂ) ^ ((b : ℂ) - 1) *
        (1 - (x : ℂ)) ^ (((1 - b : ℝ) : ℂ) - 1))
      (fun x : ℝ => (betaIntegrand b x : ℂ)) (Icc 0 1) := by
  intro x hx
  have hx0 : 0 ≤ x := hx.1
  have h1x : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  have hbexp : ((b : ℂ) - 1) = (b - 1 : ℝ) := by push_cast; ring
  have hvexp : (((1 - b : ℝ) : ℂ) - 1) = (-b : ℝ) := by push_cast; ring
  have hsub : (1 : ℂ) - (x : ℂ) = (1 - x : ℝ) := by push_cast; ring
  dsimp
  rw [hbexp, hvexp, hsub, betaIntegrand, ← Complex.ofReal_cpow hx0,
    ← Complex.ofReal_cpow h1x, ← Complex.ofReal_mul]

/-- The Beta integrand is interval-integrable on `[0, 1]`. -/
private lemma betaIntegrand_intervalIntegrable {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    IntervalIntegrable (betaIntegrand b) volume 0 1 := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hbC : 0 < ((b : ℂ).re) := by simpa using hb0
  have h1bC : 0 < (((1 - b : ℝ) : ℂ).re) := by simpa using sub_pos.mpr hb1
  have hEqOn : EqOn (fun x : ℝ => (x : ℂ) ^ ((b : ℂ) - 1) *
      (1 - (x : ℂ)) ^ (((1 - b : ℝ) : ℂ) - 1))
      (fun x => (betaIntegrand b x : ℂ)) (uIoc 0 1) := by
    intro x hx
    rw [uIoc_of_le h01] at hx
    exact betaIntegrand_eqOn (Ioc_subset_Icc_self hx)
  have hEqC : IntervalIntegrable (fun x : ℝ => (betaIntegrand b x : ℂ)) volume 0 1 :=
    (intervalIntegrable_congr hEqOn).1 (Complex.betaIntegral_convergent hbC h1bC)
  have hI : Integrable (fun x => (betaIntegrand b x : ℂ))
      (volume.restrict (Ioc 0 1)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le h01).1 hEqC).integrable
  have hLip := LipschitzWith.integrable_comp_iff_of_antilipschitz
    Complex.ofRealLI.lipschitzWith Complex.ofRealLI.antilipschitzWith
    Complex.ofRealLI.map_zero (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (f := betaIntegrand b)
  have hcomp : Integrable (Complex.ofRealLI ∘ betaIntegrand b)
      (volume.restrict (Ioc 0 1)) := by
    simpa [Function.comp_def, Complex.ofRealLI_apply] using hI
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h01, IntegrableOn]
  exact hLip.1 hcomp

/-- Reflection evaluation of the real Beta integral on `(0, 1)`. -/
private lemma intervalIntegral_betaIntegrand {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∫ u in (0 : ℝ)..1, betaIntegrand b u =
      Real.pi / Real.sin (Real.pi * b) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hbC : 0 < ((b : ℂ).re) := by simpa using hb0
  have h1bC : 0 < (((1 - b : ℝ) : ℂ).re) := by simpa using sub_pos.mpr hb1
  have hsum : (b : ℂ) + ((1 - b : ℝ) : ℂ) = 1 := by push_cast; ring
  have hbeta : Complex.betaIntegral (b : ℂ) ((1 - b : ℝ) : ℂ) =
      Complex.ofReal (Real.pi / Real.sin (Real.pi * b)) := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hbC h1bC, hsum, Complex.Gamma_one, div_one,
      Complex.Gamma_ofReal b, Complex.Gamma_ofReal (1 - b), ← Complex.ofReal_mul,
      Real.Gamma_mul_Gamma_one_sub]
  have hcongr : EqOn (fun x : ℝ => (x : ℂ) ^ ((b : ℂ) - 1) *
      (1 - (x : ℂ)) ^ (((1 - b : ℝ) : ℂ) - 1))
      (fun x => (betaIntegrand b x : ℂ)) (uIcc 0 1) := by
    rw [uIcc_of_le h01]
    exact betaIntegrand_eqOn
  rw [Complex.betaIntegral, intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_ofReal] at hbeta
  exact Complex.ofReal_inj.mp hbeta

/-- Lebesgue form of the Beta reflection integral on `(0, 1)`. -/
private lemma lintegral_betaIntegrand {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (betaIntegrand b u) =
      ENNReal.ofReal (Real.pi / Real.sin (Real.pi * b)) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hInt : Integrable (betaIntegrand b) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le h01).1
      (betaIntegrand_intervalIntegrable hb0 hb1)).integrable
  have hnn : ∀ u ∈ Ioc (0 : ℝ) 1, 0 ≤ betaIntegrand b u := by
    intro u hu
    exact mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.rpow_nonneg (sub_nonneg.mpr hu.2) _)
  rw [setLIntegral_congr (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1)),
    ← ofReal_integral_eq_lintegral_ofReal hInt
      (ae_restrict_of_forall_mem measurableSet_Ioc hnn),
    ← intervalIntegral.integral_of_le h01, intervalIntegral_betaIntegrand hb0 hb1]

/-- Derivative of the substitution `u ↦ u / (1 - u)`. -/
private lemma phi_hasDerivAt {u : ℝ} (hu : u ≠ 1) :
    HasDerivAt (fun v => v / (1 - v)) (1 / (1 - u) ^ 2) u := by
  have hne : 1 - u ≠ 0 := sub_ne_zero.mpr (ne_comm.mp hu)
  have hd : HasDerivAt (fun v => 1 - v) (-1) u :=
    (hasDerivAt_id' u).const_sub (1 : ℝ)
  refine ((hasDerivAt_id' u).fun_div hd hne).congr_deriv ?_
  rw [one_mul, mul_neg, mul_one, sub_neg_eq_add, sub_add_cancel]

/-- The substitution `u ↦ u / (1 - u)` sends `(0, 1)` onto `(0, ∞)`. -/
private lemma phi_image :
    (fun u : ℝ => u / (1 - u)) '' Ioo 0 1 = Ioi (0 : ℝ) := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact div_pos hu.1 (sub_pos.mpr hu.2)
  · intro ht
    have h1t : 0 < 1 + t := add_pos zero_lt_one ht
    have hu0 : 0 < t / (1 + t) := div_pos ht h1t
    have hu1 : t / (1 + t) < 1 := by
      rw [div_lt_one h1t]
      linarith
    refine ⟨t / (1 + t), ⟨hu0, hu1⟩, ?_⟩
    have hsub : 1 - t / (1 + t) = 1 / (1 + t) := by
      rw [one_sub_div h1t.ne', add_sub_cancel_right]
    dsimp
    rw [hsub, div_div_eq_mul_div, div_one, div_mul_cancel₀ _ h1t.ne']

/-- The substitution `u ↦ u / (1 - u)` is injective on `(0, 1)`. -/
private lemma phi_injOn : InjOn (fun u : ℝ => u / (1 - u)) (Ioo (0 : ℝ) 1) := by
  intro u hu v hv h
  have hu' : 1 - u ≠ 0 := sub_ne_zero.mpr (ne_comm.mp hu.2.ne)
  have hv' : 1 - v ≠ 0 := sub_ne_zero.mpr (ne_comm.mp hv.2.ne)
  field_simp at h
  linarith

/-- Jacobian identity for `t = u / (1 - u)` in the Beta substitution. -/
private lemma phi_kernel {b u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    |1 / (1 - u) ^ 2| * ((u / (1 - u)) ^ (b - 1) / (1 + u / (1 - u))) =
      betaIntegrand b u := by
  have ha : 0 < 1 - u := sub_pos.mpr hu1
  have ha0 : 1 - u ≠ 0 := ha.ne'
  have habs : |1 / (1 - u) ^ 2| = 1 / (1 - u) ^ 2 :=
    abs_of_pos (div_pos one_pos (sq_pos_of_pos ha))
  have hden : 1 + u / (1 - u) = 1 / (1 - u) := by
    rw [one_add_div ha0, sub_add_cancel]
  have hr : (u / (1 - u)) ^ (b - 1) = u ^ (b - 1) / (1 - u) ^ (b - 1) :=
    Real.div_rpow hu0.le ha.le _
  have hstep : (1 / (1 - u) ^ 2) *
      ((u / (1 - u)) ^ (b - 1) / (1 / (1 - u))) =
      (u / (1 - u)) ^ (b - 1) / (1 - u) := by
    set a : ℝ := 1 - u
    set W : ℝ := (u / a) ^ (b - 1)
    have hcoef : (1 / a ^ 2) * a = 1 / a := by
      rw [div_mul_eq_mul_div, one_mul, sq, ← div_div, div_self ha0]
    rw [div_div_eq_mul_div, div_one, mul_left_comm, hcoef, mul_one_div]
  have hexp : -(b - 1) + (-1 : ℝ) = -b := by
    calc
      -(b - 1) + (-1) = (1 - b) + (-1) := by rw [neg_sub]
      _ = (1 + -b) + -1 := by rw [sub_eq_add_neg]
      _ = 1 + (-b + -1) := by rw [add_assoc]
      _ = 1 + (-1 + -b) := by rw [add_comm (-b)]
      _ = (1 + -1) + -b := by rw [← add_assoc]
      _ = 0 + -b := by rw [add_neg_cancel]
      _ = -b := by rw [zero_add]
  calc
    |1 / (1 - u) ^ 2| * ((u / (1 - u)) ^ (b - 1) / (1 + u / (1 - u)))
        = (u / (1 - u)) ^ (b - 1) / (1 - u) := by rw [habs, hden, hstep]
    _ = u ^ (b - 1) / (1 - u) ^ (b - 1) / (1 - u) := by rw [hr]
    _ = u ^ (b - 1) * ((1 - u) ^ (b - 1))⁻¹ * (1 - u)⁻¹ := by
        rw [div_div, div_eq_mul_inv, mul_inv, mul_assoc]
    _ = u ^ (b - 1) * (1 - u) ^ (-(b - 1)) * (1 - u) ^ (-1 : ℝ) := by
        rw [← Real.rpow_neg ha.le, ← Real.rpow_neg_one]
    _ = u ^ (b - 1) * (1 - u) ^ (-b) := by
        rw [mul_assoc, ← Real.rpow_add ha, hexp]
    _ = betaIntegrand b u := by rw [betaIntegrand]

/-- Half-line form of the reflection integral, for `0 < b < 1`. -/
private lemma lintegral_betaTail {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (betaTail b t) =
      ENNReal.ofReal (Real.pi / Real.sin (Real.pi * b)) := by
  let φ : ℝ → ℝ := fun u => u / (1 - u)
  have hderiv : ∀ u ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt φ (1 / (1 - u) ^ 2) (Ioo 0 1) u := by
    intro u hu
    exact (phi_hasDerivAt hu.2.ne).hasDerivWithinAt
  rw [← phi_image, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hderiv phi_injOn]
  refine (setLIntegral_congr_fun measurableSet_Ioo ?_).trans (lintegral_betaIntegrand hb0 hb1)
  intro u hu
  dsimp
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  exact congrArg ENNReal.ofReal <| by
    simpa [φ, betaTail] using phi_kernel hu.1 hu.2

/-- `π / sin (π α)` is positive for `α ∈ (0, 1)`. -/
private lemma pi_div_sin_pi_pos {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    0 < Real.pi / Real.sin (Real.pi * α) := by
  refine div_pos Real.pi_pos (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
  · exact mul_pos Real.pi_pos hα0
  · calc
      Real.pi * α < Real.pi * 1 := mul_lt_mul_of_pos_left hα1 Real.pi_pos
      _ = Real.pi := mul_one _

/-- Scaling identity `(x / (x t)) ^ α / (x + x t) * x = t ^ (-α) / (1 + t)`. -/
private lemma scale_kernel {α x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    |x| * ((x / (x * t)) ^ α / (x + x * t)) = t ^ (-α) / (1 + t) := by
  have hxt : 0 < x * t := mul_pos hx ht
  rw [abs_of_pos hx]
  have hdiv : x / (x * t) = t⁻¹ := by field_simp
  have hsum : x + x * t = x * (1 + t) := by ring
  have hpow : (t⁻¹) ^ α = t ^ (-α) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_mul ht.le]
    congr 1
    ring
  rw [hdiv, hsum, hpow]
  field_simp

/-- Schur slice: `∫_{y > 0} (x / y) ^ α / (x + y) dy = π / sin (π α)`. -/
private lemma lintegral_hilbert_slice {α x : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hx : 0 < x) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal ((x / y) ^ α / (x + y)) =
      ENNReal.ofReal (Real.pi / Real.sin (Real.pi * α)) := by
  let ψ : ℝ → ℝ := fun t => x * t
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt ψ x (Ioi 0) t := fun t _ =>
    (hasDerivAt_const_mul (x := t) x).hasDerivWithinAt
  have hinj : InjOn ψ (Ioi (0 : ℝ)) := fun _ _ _ _ h => mul_right_injective₀ hx.ne' h
  have himg : ψ '' Ioi (0 : ℝ) = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact mul_pos hx ht
    · intro hy
      refine ⟨y / x, div_pos hy hx, ?_⟩
      dsimp [ψ]
      exact mul_div_cancel₀ y hx.ne'
  have htail : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (betaTail (1 - α) t) =
      ENNReal.ofReal (Real.pi / Real.sin (Real.pi * α)) := by
    rw [lintegral_betaTail (sub_pos.mpr hα1) (sub_lt_self 1 hα0)]
    congr 1
    rw [show Real.pi * (1 - α) = Real.pi - Real.pi * α by ring, Real.sin_pi_sub]
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj]
  refine (setLIntegral_congr_fun measurableSet_Ioi ?_).trans htail
  intro t ht
  dsimp
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  apply congrArg ENNReal.ofReal
  dsimp [ψ]
  have hexp : (1 - α) - 1 = -α := by
    rw [sub_right_comm, sub_self, zero_sub]
  rw [scale_kernel hx ht, betaTail, hexp]

/-- Positive kernel `(k / t) ^ α / (k + t)`, extended by `0` off `(0, ∞)`. -/
private def hilbertKernel (k α t : ℝ) : ℝ :=
  if 0 < t then rpowPos α (k / t) / (k + t) else 0

/-- The kernel is nonnegative. -/
private lemma hilbertKernel_nonneg (k α t : ℝ) : 0 ≤ hilbertKernel k α t := by
  unfold hilbertKernel
  split_ifs with ht
  · by_cases hkt : 0 < k / t
    · have hk : 0 < k := by
        rw [← div_mul_cancel₀ k ht.ne']
        exact mul_pos hkt ht
      exact div_nonneg (rpowPos_nonneg _ _) (add_pos hk ht).le
    · rw [rpowPos, ite_eq_right_iff.mpr fun h => (hkt h).elim, zero_div]
  · exact le_rfl

/-- On `(0, ∞)` the kernel is the real power `(k / t) ^ α / (k + t)`. -/
private lemma hilbertKernel_eq {k α t : ℝ} (hk : 0 < k) (ht : 0 < t) :
    hilbertKernel k α t = (k / t) ^ α / (k + t) := by
  have hdiv : 0 < k / t := div_pos hk ht
  simp [hilbertKernel, ht, rpowPos_eq (c := α) hdiv]

/-- The kernel is measurable. -/
private lemma measurable_hilbertKernel (k α : ℝ) : Measurable (hilbertKernel k α) := by
  unfold hilbertKernel
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  exact ((measurable_rpowPos α).comp (measurable_const.div measurable_id)).div
    (measurable_const.add measurable_id)

/-- The kernel decreases on `(0, ∞)` for a positive exponent. -/
private lemma hilbertKernel_antitone {k α : ℝ} (hk : 0 < k) (hα : 0 < α) :
    AntitoneOn (hilbertKernel k α) (Ioi (0 : ℝ)) := by
  intro s hs t ht hst
  rw [hilbertKernel_eq hk hs, hilbertKernel_eq hk ht]
  have hrat : k / t ≤ k / s := div_le_div_of_nonneg_left hk.le hs hst
  have hnum : (k / t) ^ α ≤ (k / s) ^ α :=
    Real.rpow_le_rpow (div_nonneg hk.le ht.le) hrat hα.le
  have hden : k + s ≤ k + t := add_le_add_right hst k
  exact le_trans (div_le_div_of_nonneg_right hnum (add_pos hk ht).le)
    (div_le_div_of_nonneg_left (Real.rpow_nonneg (div_pos hk hs).le _) (add_pos hk hs) hden)

/-- Lebesgue integral of the kernel, for `0 < α < 1` and `k > 0`. -/
private lemma lintegral_hilbertKernel {k α : ℝ} (hk : 0 < k) (hα0 : 0 < α) (hα1 : α < 1) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (hilbertKernel k α t) =
      ENNReal.ofReal (Real.pi / Real.sin (Real.pi * α)) := by
  refine (setLIntegral_congr_fun measurableSet_Ioi ?_).trans (lintegral_hilbert_slice hα0 hα1 hk)
  intro t ht
  dsimp
  rw [hilbertKernel_eq hk ht]

/-- The kernel is integrable on `(0, ∞)`. -/
private lemma integrableOn_hilbertKernel {k α : ℝ} (hk : 0 < k) (hα0 : 0 < α) (hα1 : α < 1) :
    IntegrableOn (hilbertKernel k α) (Ioi (0 : ℝ)) := by
  refine ⟨(measurable_hilbertKernel k α).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  rw [setLIntegral_congr_fun measurableSet_Ioi
      (fun t ht => by rw [Real.enorm_eq_ofReal (hilbertKernel_nonneg k α t)])]
  rw [lintegral_hilbertKernel hk hα0 hα1]
  exact ENNReal.ofReal_lt_top

/-- Bochner integral of the kernel. -/
private lemma integral_hilbertKernel {k α : ℝ} (hk : 0 < k) (hα0 : 0 < α) (hα1 : α < 1) :
    ∫ t in Ioi (0 : ℝ), hilbertKernel k α t =
      Real.pi / Real.sin (Real.pi * α) := by
  have hint := integrableOn_hilbertKernel hk hα0 hα1
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] hilbertKernel k α :=
    ae_of_all _ (hilbertKernel_nonneg k α)
  have hlin := lintegral_hilbertKernel hk hα0 hα1
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn] at hlin
  exact (ENNReal.ofReal_eq_ofReal_iff
    (setIntegral_nonneg measurableSet_Ioi fun t _ => hilbertKernel_nonneg k α t)
    (pi_div_sin_pi_pos hα0 hα1).le).mp hlin

/-- A value at `1` is at most the integral of an antitone function over `(0, 1]`. -/
private lemma antitone_at_one_le_integral {f : ℝ → ℝ}
    (hanti : AntitoneOn f (Ioi (0 : ℝ))) (hint : IntegrableOn f (Ioi (0 : ℝ))) :
    f 1 ≤ ∫ t in Ioc (0 : ℝ) 1, f t := by
  have hconst : IntegrableOn (fun _ : ℝ => f 1) (Ioc (0 : ℝ) 1) :=
    integrableOn_const (by simp)
  have hf : IntegrableOn f (Ioc (0 : ℝ) 1) := hint.mono_set Ioc_subset_Ioi_self
  have hmono : ∫ t in Ioc (0 : ℝ) 1, f 1 ≤ ∫ t in Ioc (0 : ℝ) 1, f t :=
    setIntegral_mono_on hconst hf measurableSet_Ioc fun t ht =>
      hanti ht.1 (by norm_num : (0 : ℝ) < 1) ht.2
  have hconstInt : ∫ t in Ioc (0 : ℝ) 1, f 1 = f 1 := by
    rw [setIntegral_const, Measure.real, Real.volume_Ioc]
    simp
  exact hconstInt.symm.trans_le hmono

/-- Partial sums of an antitone nonnegative function are bounded by the half-line integral. -/
private lemma sum_range_antitone_Ioi_le {f : ℝ → ℝ}
    (hanti : AntitoneOn f (Ioi (0 : ℝ))) (hint : IntegrableOn f (Ioi (0 : ℝ)))
    (hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ f t) (N : ℕ) :
    ∑ i ∈ Finset.range N, f (↑i + 1) ≤ ∫ t in Ioi (0 : ℝ), f t := by
  cases N with
  | zero =>
    simp
    exact setIntegral_nonneg measurableSet_Ioi hnn
  | succ N =>
    have hpos : 0 < N + 1 := Nat.succ_pos N
    have hcast : ∀ i : ℕ, f (↑i + 1) = f ↑(i + 1) := fun i => by
      congr 1
      rw [Nat.cast_add, Nat.cast_one]
    rw [Finset.sum_range_eq_add_Ico (fun i => f (↑i + 1)) hpos]
    have hsub : Icc ((1 : ℕ) : ℝ) ((N + 1 : ℕ) : ℝ) ⊆ Ioi (0 : ℝ) := by
      intro t ht
      have h1 : (1 : ℝ) ≤ t := by simpa [Nat.cast_one] using ht.1
      exact lt_of_lt_of_le zero_lt_one h1
    have htail : ∑ i ∈ Finset.Ico 1 (N + 1), f (↑i + 1) ≤ ∫ t in Ioi (1 : ℝ), f t := by
      simp_rw [hcast]
      simpa [Nat.cast_one] using
        AntitoneOn.sum_Ico_le_integral (a := 1) (b := N + 1) (hanti.mono hsub)
          (hint.mono_set (Ioi_subset_Ioi (Nat.cast_nonneg (1 : ℕ))))
          (fun t ht => hnn t (Ioi_subset_Ioi (Nat.cast_nonneg (1 : ℕ)) ht))
    have hadd : (∫ t in Ioc (0 : ℝ) 1, f t) + (∫ t in Ioi (1 : ℝ), f t) =
        ∫ t in Ioi (0 : ℝ), f t := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
          (hint.mono_set Ioc_subset_Ioi_self)
          (hint.mono_set (Ioi_subset_Ioi zero_le_one)),
        Ioc_union_Ioi_eq_Ioi zero_le_one]
    have hhead : f (↑(0 : ℕ) + 1) ≤ ∫ t in Ioc (0 : ℝ) 1, f t := by
      rw [Nat.cast_zero, zero_add]
      exact antitone_at_one_le_integral hanti hint
    exact (add_le_add hhead htail).trans_eq hadd

/-- The series of kernel samples is at most the kernel integral. -/
private lemma tsum_hilbertKernel_le {k α : ℝ} (hk : 0 < k) (hα0 : 0 < α) (hα1 : α < 1) :
    ∑' n : ℕ, ENNReal.ofReal (hilbertKernel k α (↑n + 1)) ≤
      ENNReal.ofReal (Real.pi / Real.sin (Real.pi * α)) := by
  have hint := integrableOn_hilbertKernel hk hα0 hα1
  have hanti := hilbertKernel_antitone hk hα0
  have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ hilbertKernel k α t :=
    fun _ _ => hilbertKernel_nonneg k α _
  have hpartial : ∀ N, ∑ i ∈ Finset.range N, hilbertKernel k α (↑i + 1) ≤
      ∫ t in Ioi (0 : ℝ), hilbertKernel k α t :=
    fun N => sum_range_antitone_Ioi_le hanti hint hnn N
  have hterm : ∀ n : ℕ, 0 ≤ hilbertKernel k α (↑n + 1) :=
    fun _ => hilbertKernel_nonneg k α _
  have hsummable : Summable fun n : ℕ => hilbertKernel k α (↑n + 1) :=
    summable_of_sum_range_le hterm hpartial
  rw [← ENNReal.ofReal_tsum_of_nonneg hterm hsummable]
  exact ENNReal.ofReal_le_ofReal
    ((Real.tsum_le_of_sum_range_le hterm hpartial).trans_eq (integral_hilbertKernel hk hα0 hα1))

/-- Left Schur factor `f(x) (x / y) ^ (1 / (p q)) / (x + y) ^ (1 / p)`. -/
private def hilbertLeft (p q : ℝ) (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  if 0 < x ∧ 0 < y then
    f x * rpowPos (1 / (p * q)) (x / y) / rpowPos (1 / p) (x + y)
  else 0

/-- Right Schur factor `g(y) (y / x) ^ (1 / (p q)) / (x + y) ^ (1 / q)`. -/
private def hilbertRight (p q : ℝ) (g : ℝ → ℝ) (x y : ℝ) : ℝ :=
  if 0 < x ∧ 0 < y then
    g y * rpowPos (1 / (p * q)) (y / x) / rpowPos (1 / q) (x + y)
  else 0

/-- The left factor is nonnegative when `f` is. -/
private lemma hilbertLeft_nonneg {p q : ℝ} {f : ℝ → ℝ} {x y : ℝ} (hf : 0 ≤ f x) :
    0 ≤ hilbertLeft p q f x y := by
  unfold hilbertLeft
  split_ifs with h
  · exact div_nonneg (mul_nonneg hf (rpowPos_nonneg _ _)) (rpowPos_pos (by linarith [h.1, h.2])).le
  · exact le_rfl

/-- The right factor is nonnegative when `g` is. -/
private lemma hilbertRight_nonneg {p q : ℝ} {g : ℝ → ℝ} {x y : ℝ} (hg : 0 ≤ g y) :
    0 ≤ hilbertRight p q g x y := by
  unfold hilbertRight
  split_ifs with h
  · exact div_nonneg (mul_nonneg hg (rpowPos_nonneg _ _)) (rpowPos_pos (by linarith [h.1, h.2])).le
  · exact le_rfl

/-- Real form of the left factor on the positive quadrant. -/
private lemma hilbertLeft_eq {p q x y fx : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hilbertLeft p q (fun _ => fx) x y =
      fx * (x / y) ^ (1 / (p * q)) / (x + y) ^ (1 / p) := by
  have hxy : 0 < x / y := div_pos hx hy
  have hs : 0 < x + y := add_pos hx hy
  rw [hilbertLeft, ite_eq_left ⟨hx, hy⟩, rpowPos_eq hxy, rpowPos_eq hs]

/-- Real form of the right factor on the positive quadrant. -/
private lemma hilbertRight_eq {p q x y gy : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hilbertRight p q (fun _ => gy) x y =
      gy * (y / x) ^ (1 / (p * q)) / (x + y) ^ (1 / q) := by
  have hyx : 0 < y / x := div_pos hy hx
  have hs : 0 < x + y := add_pos hx hy
  rw [hilbertRight, ite_eq_left ⟨hx, hy⟩, rpowPos_eq hyx, rpowPos_eq hs]

/-- The two Schur factors multiply back to the Hilbert kernel. -/
private lemma hilbertFactor_mul {p q : ℝ} (hpq : p.HolderConjugate q) {x y fx gy : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    hilbertLeft p q (fun _ => fx) x y * hilbertRight p q (fun _ => gy) x y =
      fx * gy / (x + y) := by
  have hs : 0 < x + y := add_pos hx hy
  have hxy : 0 < x / y := div_pos hx hy
  have hyx : 0 < y / x := div_pos hy hx
  rw [hilbertLeft_eq hx hy, hilbertRight_eq hx hy]
  have hprod : (x / y) ^ (1 / (p * q)) * (y / x) ^ (1 / (p * q)) = 1 := by
    rw [← Real.mul_rpow hxy.le hyx.le]
    have : (x / y) * (y / x) = 1 := by field_simp
    rw [this, Real.one_rpow]
  have hden : (x + y) ^ (1 / p) * (x + y) ^ (1 / q) = x + y := by
    rw [← Real.rpow_add hs]
    have hadd : (1 / p + 1 / q : ℝ) = 1 := by simpa [one_div] using hpq.inv_add_inv_eq_one
    rw [hadd, Real.rpow_one]
  calc
    (fx * (x / y) ^ (1 / (p * q)) / (x + y) ^ (1 / p)) *
        (gy * (y / x) ^ (1 / (p * q)) / (x + y) ^ (1 / q))
        = (fx * (x / y) ^ (1 / (p * q)) * (gy * (y / x) ^ (1 / (p * q)))) /
          ((x + y) ^ (1 / p) * (x + y) ^ (1 / q)) := by
            rw [div_mul_div_comm]
    _ = (fx * gy * ((x / y) ^ (1 / (p * q)) * (y / x) ^ (1 / (p * q)))) /
          ((x + y) ^ (1 / p) * (x + y) ^ (1 / q)) := by
            rw [mul_mul_mul_comm]
    _ = (fx * gy * 1) / (x + y) := by rw [hprod, hden]
    _ = fx * gy / (x + y) := by rw [mul_one]

/-- Raising the left factor to `p` recovers `f(x) ^ p` times the kernel of exponent `1 / q`. -/
private lemma hilbertLeft_pow {p q : ℝ} (hpq : p.HolderConjugate q) {x y fx : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hfx : 0 ≤ fx) :
    hilbertLeft p q (fun _ => fx) x y ^ p =
      fx ^ p * hilbertKernel x q⁻¹ y := by
  have hs : 0 < x + y := add_pos hx hy
  have hxy : 0 ≤ x / y := (div_pos hx hy).le
  rw [hilbertLeft_eq hx hy, hilbertKernel_eq hx hy]
  have hbase : 0 ≤ fx * (x / y) ^ (1 / (p * q)) :=
    mul_nonneg hfx (Real.rpow_nonneg hxy _)
  have hc : 0 ≤ (x + y) ^ (1 / p) := Real.rpow_nonneg hs.le _
  rw [Real.div_rpow hbase hc, Real.mul_rpow hfx (Real.rpow_nonneg hxy _)]
  rw [← Real.rpow_mul hxy, ← Real.rpow_mul hs.le]
  have hθ : 1 / (p * q) * p = q⁻¹ := by
    rw [one_div, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hpq.pos.ne', mul_one]
  have hp : (1 / p) * p = 1 := by field_simp [hpq.pos.ne']
  rw [hθ, hp, Real.rpow_one, mul_div_assoc]

/-- Raising the right factor to `q` recovers `g(y) ^ q` times the kernel of exponent `1 / p`. -/
private lemma hilbertRight_pow {p q : ℝ} (hpq : p.HolderConjugate q) {x y gy : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hgy : 0 ≤ gy) :
    hilbertRight p q (fun _ => gy) x y ^ q =
      gy ^ q * hilbertKernel y p⁻¹ x := by
  have hs : 0 < x + y := add_pos hx hy
  have hyx : 0 ≤ y / x := (div_pos hy hx).le
  rw [hilbertRight_eq hx hy, hilbertKernel_eq hy hx]
  have hbase : 0 ≤ gy * (y / x) ^ (1 / (p * q)) :=
    mul_nonneg hgy (Real.rpow_nonneg hyx _)
  have hc : 0 ≤ (x + y) ^ (1 / q) := Real.rpow_nonneg hs.le _
  rw [Real.div_rpow hbase hc, Real.mul_rpow hgy (Real.rpow_nonneg hyx _)]
  rw [← Real.rpow_mul hyx, ← Real.rpow_mul hs.le]
  have hθ : 1 / (p * q) * q = p⁻¹ := by
    rw [one_div, mul_inv_rev, mul_assoc, mul_left_comm q⁻¹ p⁻¹ q,
      inv_mul_cancel₀ hpq.symm.pos.ne', mul_one]
  have hq : (1 / q) * q = 1 := by field_simp [hpq.symm.pos.ne']
  rw [hθ, hq, Real.rpow_one, add_comm x y, mul_div_assoc]

/-- `ENNReal` form of the product of the two factors. -/
private lemma ofReal_hilbertFactor_mul {p q : ℝ} (hpq : p.HolderConjugate q) {x y fx gy : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hfx : 0 ≤ fx) :
    ENNReal.ofReal (hilbertLeft p q (fun _ => fx) x y) *
        ENNReal.ofReal (hilbertRight p q (fun _ => gy) x y) =
      ENNReal.ofReal (fx * gy / (x + y)) := by
  rw [← ENNReal.ofReal_mul (hilbertLeft_nonneg hfx), hilbertFactor_mul hpq hx hy]

/-- `ENNReal` form of the left factor raised to `p`. -/
private lemma ofReal_hilbertLeft_pow {p q : ℝ} (hpq : p.HolderConjugate q) {x y fx : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hfx : 0 ≤ fx) :
    ENNReal.ofReal (hilbertLeft p q (fun _ => fx) x y) ^ p =
      ENNReal.ofReal fx ^ p * ENNReal.ofReal (hilbertKernel x q⁻¹ y) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (hilbertLeft_nonneg hfx) hpq.pos.le,
    hilbertLeft_pow hpq hx hy hfx, ENNReal.ofReal_mul (Real.rpow_nonneg hfx _),
    ← ENNReal.ofReal_rpow_of_nonneg hfx hpq.pos.le]

/-- `ENNReal` form of the right factor raised to `q`. -/
private lemma ofReal_hilbertRight_pow {p q : ℝ} (hpq : p.HolderConjugate q) {x y gy : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hgy : 0 ≤ gy) :
    ENNReal.ofReal (hilbertRight p q (fun _ => gy) x y) ^ q =
      ENNReal.ofReal gy ^ q * ENNReal.ofReal (hilbertKernel y p⁻¹ x) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (hilbertRight_nonneg hgy) hpq.symm.pos.le,
    hilbertRight_pow hpq hx hy hgy, ENNReal.ofReal_mul (Real.rpow_nonneg hgy _),
    ← ENNReal.ofReal_rpow_of_nonneg hgy hpq.symm.pos.le]

/-- The left factor is jointly measurable when `f` is measurable. -/
private lemma measurable_hilbertLeft {p q : ℝ} {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (Function.uncurry (hilbertLeft p q f)) := by
  unfold hilbertLeft
  refine Measurable.ite ?_ ?_ measurable_const
  · have hs : {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2} = Ioi 0 ×ˢ Ioi 0 := by
      ext z
      simp
    rw [hs]
    exact measurableSet_Ioi.prod measurableSet_Ioi
  · exact (((hf.comp measurable_fst).mul ((measurable_rpowPos _).comp
      (measurable_fst.div measurable_snd))).div
      ((measurable_rpowPos _).comp (measurable_fst.add measurable_snd)))

/-- The right factor is jointly measurable when `g` is measurable. -/
private lemma measurable_hilbertRight {p q : ℝ} {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (Function.uncurry (hilbertRight p q g)) := by
  unfold hilbertRight
  refine Measurable.ite ?_ ?_ measurable_const
  · have hs : {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2} = Ioi 0 ×ˢ Ioi 0 := by
      ext z
      simp
    rw [hs]
    exact measurableSet_Ioi.prod measurableSet_Ioi
  · exact (((hg.comp measurable_snd).mul ((measurable_rpowPos _).comp
      (measurable_snd.div measurable_fst))).div
      ((measurable_rpowPos _).comp (measurable_fst.add measurable_snd)))

/-- The nonnegative integrand `f(x) g(y) / (x + y)` is jointly measurable. -/
private lemma measurable_hilbert_integrand {f g : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun z : ℝ × ℝ => ENNReal.ofReal (f z.1 * g z.2 / (z.1 + z.2)) :=
  ENNReal.measurable_ofReal.comp <|
    ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).div
      (measurable_fst.add measurable_snd)

/-- Hilbert's constant is positive for `p > 1`. -/
private lemma hilbertConstant_pos {p : ℝ} (hp : 1 < p) : 0 < hilbertConstant p := by
  unfold hilbertConstant
  refine div_pos Real.pi_pos (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
  · exact div_pos Real.pi_pos (by linarith)
  · rw [div_lt_iff₀ (by linarith : (0 : ℝ) < p)]
    nlinarith [Real.pi_pos]

/-- `sin (π / q) = sin (π / p)` for the conjugate exponent. -/
private lemma sin_pi_conjExponent {p : ℝ} (hp : 1 < p) :
    Real.sin (Real.pi * (Real.conjExponent p)⁻¹) = Real.sin (Real.pi / p) := by
  have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp
  calc
    Real.sin (Real.pi * (Real.conjExponent p)⁻¹)
        = Real.sin (Real.pi * (1 - p⁻¹)) := by rw [← hpq.one_sub_inv]
    _ = Real.sin (Real.pi - Real.pi / p) := by
        rw [mul_sub, mul_one, ← div_eq_mul_inv]
    _ = Real.sin (Real.pi / p) := Real.sin_pi_sub _

/-- Inner integral of the left factor to the power `p`. -/
private lemma lintegral_hilbertLeft_pow {p q : ℝ} (hpq : p.HolderConjugate q) {x fx : ℝ}
    (hx : 0 < x) (hfx : 0 ≤ fx) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (hilbertLeft p q (fun _ => fx) x y) ^ p =
      ENNReal.ofReal fx ^ p * ENNReal.ofReal (hilbertConstant p) := by
  have hpoint : EqOn
      (fun y => ENNReal.ofReal (hilbertLeft p q (fun _ => fx) x y) ^ p)
      (fun y => ENNReal.ofReal fx ^ p * ENNReal.ofReal (hilbertKernel x q⁻¹ y))
      (Ioi (0 : ℝ)) := fun y hy => ofReal_hilbertLeft_pow hpq hx hy hfx
  rw [setLIntegral_congr_fun measurableSet_Ioi hpoint,
    lintegral_const_mul' _ _
      (ENNReal.rpow_ne_top_of_nonneg hpq.pos.le ENNReal.ofReal_ne_top),
    lintegral_hilbertKernel hx (inv_pos.mpr hpq.symm.pos)
      (inv_lt_one_of_one_lt₀ hpq.symm.lt)]
  congr 1
  unfold hilbertConstant
  rw [← hpq.conjExponent_eq, sin_pi_conjExponent hpq.lt]

/-- Inner integral of the right factor to the power `q`. -/
private lemma lintegral_hilbertRight_pow {p q : ℝ} (hpq : p.HolderConjugate q) {y gy : ℝ}
    (hy : 0 < y) (hgy : 0 ≤ gy) :
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (hilbertRight p q (fun _ => gy) x y) ^ q =
      ENNReal.ofReal gy ^ q * ENNReal.ofReal (hilbertConstant p) := by
  have hpoint : EqOn
      (fun x => ENNReal.ofReal (hilbertRight p q (fun _ => gy) x y) ^ q)
      (fun x => ENNReal.ofReal gy ^ q * ENNReal.ofReal (hilbertKernel y p⁻¹ x))
      (Ioi (0 : ℝ)) := fun x hx => ofReal_hilbertRight_pow hpq hx hy hgy
  rw [setLIntegral_congr_fun measurableSet_Ioi hpoint,
    lintegral_const_mul' _ _
      (ENNReal.rpow_ne_top_of_nonneg hpq.symm.pos.le ENNReal.ofReal_ne_top),
    lintegral_hilbertKernel hy (inv_pos.mpr hpq.pos) (inv_lt_one_of_one_lt₀ hpq.lt)]
  congr 1

/-- `(eLpNorm f p) ^ p` is the integral of `‖f‖ₑ ^ p` for a nonnegative measurable function. -/
private lemma lintegral_ofReal_rpow_eq_eLpNorm_rpow {α : Type*} [MeasurableSpace α]
    {p : ℝ} (hp : 1 < p) {f : α → ℝ} {μ : Measure α}
    (hf0 : ∀ x, 0 ≤ f x) (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp.le
  have hppos : 0 < p := lt_trans zero_lt_one hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hppos).ne'
      ENNReal.ofReal_ne_top hf, ENNReal.toReal_ofReal hp0]
  rw [show (1 / p : ℝ) = p⁻¹ from (inv_eq_one_div p).symm, ENNReal.rpow_inv_rpow hppos.ne']
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal (hf0 x)]

/-- Product of the normalized Schur integrals. -/
private lemma holder_schur_mul {c n m : ℝ≥0∞} {p q : ℝ}
    (hc0 : c ≠ 0) (hct : c ≠ ∞) (hp : 0 < p) (hq : 0 < q) (hpq : p⁻¹ + q⁻¹ = 1) :
    (c * n ^ p) ^ p⁻¹ * (c * m ^ q) ^ q⁻¹ = c * n * m := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp.le),
    ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hq.le),
    ENNReal.rpow_rpow_inv hp.ne', ENNReal.rpow_rpow_inv hq.ne']
  have hre : c ^ p⁻¹ * n * (c ^ q⁻¹ * m) = c ^ p⁻¹ * c ^ q⁻¹ * n * m := by
    calc
      c ^ p⁻¹ * n * (c ^ q⁻¹ * m)
          = c ^ p⁻¹ * (n * (c ^ q⁻¹ * m)) := mul_assoc _ _ _
      _ = c ^ p⁻¹ * (c ^ q⁻¹ * (n * m)) := congrArg (c ^ p⁻¹ * ·) (mul_left_comm _ _ _)
      _ = (c ^ p⁻¹ * c ^ q⁻¹) * (n * m) := (mul_assoc _ _ _).symm
      _ = (c ^ p⁻¹ * c ^ q⁻¹) * n * m := (mul_assoc _ _ _).symm
  rw [hre, ← ENNReal.rpow_add _ _ hc0 hct, hpq, ENNReal.rpow_one]

/-- **11.37**: Hilbert's integral inequality for nonnegative functions on the positive half-line.
The nonnegative integral avoids the totalized Bochner integral for infinite bilinear forms. -/
theorem hilbert_integral {p : ℝ} (hp : 1 < p) {f g : ℝ → ℝ}
    (hf0 : ∀ᵐ x ∂volume.restrict (Set.Ioi 0), 0 ≤ f x)
    (hg0 : ∀ᵐ x ∂volume.restrict (Set.Ioi 0), 0 ≤ g x)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0)))
    (hg : MemLp g (ENNReal.ofReal (p / (p - 1))) (volume.restrict (Set.Ioi 0))) :
    (∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ y in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (f x * g y / (x + y))) ≤
      ENNReal.ofReal (hilbertConstant p) *
        eLpNorm f (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0)) *
        eLpNorm g (ENNReal.ofReal (p / (p - 1))) (volume.restrict (Set.Ioi 0)) := by
  let ν : Measure ℝ := volume.restrict (Set.Ioi 0)
  have hf_ae : AEMeasurable f ν := hf.aemeasurable
  have hg_ae : AEMeasurable g ν := hg.aemeasurable
  let f2 : ℝ → ℝ := fun x => max (hf_ae.mk f x) 0
  let g2 : ℝ → ℝ := fun x => max (hg_ae.mk g x) 0
  have hf2m : Measurable f2 := (hf_ae.measurable_mk).max measurable_const
  have hg2m : Measurable g2 := (hg_ae.measurable_mk).max measurable_const
  have hf2nn : ∀ x, 0 ≤ f2 x := fun x => le_max_right _ _
  have hg2nn : ∀ x, 0 ≤ g2 x := fun x => le_max_right _ _
  have hf2ae : f2 =ᵐ[ν] f := by
    filter_upwards [hf_ae.ae_eq_mk, hf0] with x hx hx0
    simp only [f2]
    rw [← hx, max_eq_left hx0]
  have hg2ae : g2 =ᵐ[ν] g := by
    filter_upwards [hg_ae.ae_eq_mk, hg0] with x hx hx0
    simp only [g2]
    rw [← hx, max_eq_left hx0]
  have hint : ∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ y in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (f x * g y / (x + y)) =
      ∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ y in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (f2 x * g2 y / (x + y)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hf2ae] with x hx
    refine lintegral_congr_ae ?_
    filter_upwards [hg2ae] with y hy
    rw [hx, hy]
  rw [hint, eLpNorm_congr_ae hf2ae.symm, eLpNorm_congr_ae hg2ae.symm]
  let q : ℝ := Real.conjExponent p
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  let F : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (hilbertLeft p q f2 z.1 z.2)
  let G : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (hilbertRight p q g2 z.1 z.2)
  have hF : Measurable F := ENNReal.measurable_ofReal.comp (measurable_hilbertLeft hf2m)
  have hG : Measurable G := ENNReal.measurable_ofReal.comp (measurable_hilbertRight hg2m)
  have hprod : ∫⁻ z, (F * G) z ∂(ν.prod ν) =
      ∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ y in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (f2 x * g2 y / (x + y)) := by
    rw [lintegral_prod _ (hF.mul hG).aemeasurable]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hL : hilbertLeft p q f2 x y = hilbertLeft p q (fun _ => f2 x) x y := by
      unfold hilbertLeft
      rfl
    have hR : hilbertRight p q g2 x y = hilbertRight p q (fun _ => g2 y) x y := by
      unfold hilbertRight
      rfl
    rw [Pi.mul_apply]
    dsimp only [F, G]
    rw [hL, hR]
    exact ofReal_hilbertFactor_mul hpq hx hy (hf2nn x)
  have hc0 : ENNReal.ofReal (hilbertConstant p) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (hilbertConstant_pos hp)).ne'
  have hct : ENNReal.ofReal (hilbertConstant p) ≠ ∞ := ENNReal.ofReal_ne_top
  have hFp : ∫⁻ z, F z ^ p ∂(ν.prod ν) =
      ENNReal.ofReal (hilbertConstant p) *
        eLpNorm f2 (ENNReal.ofReal p) ν ^ p := by
    rw [lintegral_prod _ (hF.pow_const p).aemeasurable]
    have hinner : ∀ᵐ x ∂ν, ∫⁻ y, F (x, y) ^ p ∂ν =
        ENNReal.ofReal (f2 x) ^ p * ENNReal.ofReal (hilbertConstant p) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hpoint : ∫⁻ y, F (x, y) ^ p ∂ν =
          ∫⁻ y, ENNReal.ofReal (hilbertLeft p q (fun _ => f2 x) x y) ^ p ∂ν := by
        refine lintegral_congr fun y => ?_
        simp only [F]
        unfold hilbertLeft
        rfl
      rw [hpoint]
      exact lintegral_hilbertLeft_pow hpq hx (hf2nn x)
    rw [lintegral_congr_ae hinner, lintegral_mul_const' _ _ hct,
      lintegral_ofReal_rpow_eq_eLpNorm_rpow hp hf2nn
        (hf2m.aestronglyMeasurable.mono_measure Measure.restrict_le_self),
      mul_comm]
  have hGq : ∫⁻ z, G z ^ q ∂(ν.prod ν) =
      ENNReal.ofReal (hilbertConstant p) *
        eLpNorm g2 (ENNReal.ofReal q) ν ^ q := by
    rw [lintegral_prod_symm (fun z => G z ^ q) (hG.pow_const q).aemeasurable]
    have hinner : ∀ᵐ y ∂ν, ∫⁻ x, G (x, y) ^ q ∂ν =
        ENNReal.ofReal (g2 y) ^ q * ENNReal.ofReal (hilbertConstant p) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hpoint : ∫⁻ x, G (x, y) ^ q ∂ν =
          ∫⁻ x, ENNReal.ofReal (hilbertRight p q (fun _ => g2 y) x y) ^ q ∂ν := by
        refine lintegral_congr fun x => ?_
        simp only [G]
        unfold hilbertRight
        rfl
      rw [hpoint]
      exact lintegral_hilbertRight_pow hpq hy (hg2nn y)
    rw [lintegral_congr_ae hinner, lintegral_mul_const' _ _ hct,
      lintegral_ofReal_rpow_eq_eLpNorm_rpow hpq.symm.lt hg2nn
        (hg2m.aestronglyMeasurable.mono_measure Measure.restrict_le_self),
      mul_comm]
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (ν.prod ν) hpq
    hF.aemeasurable hG.aemeasurable
  rw [hprod] at hHolder
  refine hHolder.trans ?_
  rw [hFp, hGq]
  rw [show (1 / p : ℝ) = p⁻¹ from (inv_eq_one_div p).symm,
    show (1 / q : ℝ) = q⁻¹ from (inv_eq_one_div q).symm,
    holder_schur_mul hc0 hct hpq.pos hpq.symm.pos hpq.inv_add_inv_eq_one]
  have hqexp : q = p / (p - 1) := by
    unfold q
    rfl
  rw [hqexp]

/-- Positive-integer samples of the kernel are at most Hilbert's constant. -/
private lemma tsum_hilbertKernel_le_hilbertConstant {p : ℝ} {k α : ℝ}
    (hk : 0 < k) (hα0 : 0 < α) (hα1 : α < 1)
    (hsin : Real.sin (Real.pi * α) = Real.sin (Real.pi / p)) :
    ∑' n : ℕ, ENNReal.ofReal (hilbertKernel k α (n + 1)) ≤
      ENNReal.ofReal (hilbertConstant p) := by
  refine (tsum_hilbertKernel_le hk hα0 hα1).trans_eq ?_
  unfold hilbertConstant
  rw [hsin]

/-- The discrete Hilbert inequality; indices `m,n : ℕ` represent the positive integers `m+1,n+1`. -/
theorem hilbert_tsum {p : ℝ} (hp : 1 < p) {a b : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n)
    (ha : MemLp a (ENNReal.ofReal p) Measure.count)
    (hb : MemLp b (ENNReal.ofReal (p / (p - 1))) Measure.count) :
    (∑' m, ∑' n, ENNReal.ofReal (a m * b n / (m + n + 2 : ℝ))) ≤
      ENNReal.ofReal (hilbertConstant p) * eLpNorm a (ENNReal.ofReal p) Measure.count *
        eLpNorm b (ENNReal.ofReal (p / (p - 1))) Measure.count := by
  let q : ℝ := Real.conjExponent p
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  let ι : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hpos : ∀ n : ℕ, 0 < ι n := fun n =>
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
  have hcast : ∀ m n : ℕ, ι m + ι n = (m + n + 2 : ℝ) := fun m n => by
    simp only [ι]
    calc
      (m : ℝ) + 1 + ((n : ℝ) + 1) = (m : ℝ) + (n : ℝ) + (1 + 1) := add_add_add_comm _ _ _ _
      _ = ((m + n : ℕ) : ℝ) + 2 := by rw [← Nat.cast_add, one_add_one_eq_two]
      _ = (m + n + 2 : ℝ) := by rw [← Nat.cast_add]
  let μ : Measure (ℕ × ℕ) := Measure.count.prod Measure.count
  let F : ℕ × ℕ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (hilbertLeft p q (fun _ => a z.1) (ι z.1) (ι z.2))
  let G : ℕ × ℕ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (hilbertRight p q (fun _ => b z.2) (ι z.1) (ι z.2))
  have hF : Measurable F := Measurable.of_discrete
  have hG : Measurable G := Measurable.of_discrete
  have hc0 : ENNReal.ofReal (hilbertConstant p) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (hilbertConstant_pos hp)).ne'
  have hct : ENNReal.ofReal (hilbertConstant p) ≠ ∞ := ENNReal.ofReal_ne_top
  have hprod : ∫⁻ z, (F * G) z ∂μ =
      ∑' m, ∑' n, ENNReal.ofReal (a m * b n / (m + n + 2 : ℝ)) := by
    rw [lintegral_prod _ (hF.mul hG).aemeasurable]
    simp_rw [lintegral_count]
    refine tsum_congr fun m => tsum_congr fun n => ?_
    rw [Pi.mul_apply, ofReal_hilbertFactor_mul hpq (hpos m) (hpos n) (ha0 m), hcast m n]
  have hLeft : ∀ m, ∑' n, ENNReal.ofReal (hilbertKernel (ι m) q⁻¹ (ι n)) ≤
      ENNReal.ofReal (hilbertConstant p) := fun m => by
    simpa [ι] using tsum_hilbertKernel_le_hilbertConstant (hpos m)
      (inv_pos.mpr hpq.symm.pos) (inv_lt_one_of_one_lt₀ hpq.symm.lt)
      (sin_pi_conjExponent hp)
  have hRight : ∀ n, ∑' m, ENNReal.ofReal (hilbertKernel (ι n) p⁻¹ (ι m)) ≤
      ENNReal.ofReal (hilbertConstant p) := fun n => by
    simpa [ι] using tsum_hilbertKernel_le_hilbertConstant (hpos n)
      (inv_pos.mpr hpq.pos) (inv_lt_one_of_one_lt₀ hpq.lt) (by rw [← div_eq_mul_inv])
  have hFp : ∫⁻ z, F z ^ p ∂μ ≤
      ENNReal.ofReal (hilbertConstant p) *
        eLpNorm a (ENNReal.ofReal p) Measure.count ^ p := by
    rw [lintegral_prod _ (hF.pow_const p).aemeasurable]
    simp_rw [lintegral_count]
    have hinner : ∀ m, ∑' n, F (m, n) ^ p ≤
        ENNReal.ofReal (a m) ^ p * ENNReal.ofReal (hilbertConstant p) := by
      intro m
      have hpoint : ∀ n, F (m, n) ^ p =
          ENNReal.ofReal (a m) ^ p *
            ENNReal.ofReal (hilbertKernel (ι m) q⁻¹ (ι n)) := fun n => by
        simpa [F] using ofReal_hilbertLeft_pow hpq (hpos m) (hpos n) (ha0 m)
      simp_rw [hpoint, ENNReal.tsum_mul_left]
      exact mul_le_mul_right (hLeft m) _
    refine (ENNReal.tsum_le_tsum hinner).trans_eq ?_
    rw [ENNReal.tsum_mul_right, ← lintegral_count,
      lintegral_ofReal_rpow_eq_eLpNorm_rpow hp ha0 ha.aestronglyMeasurable, mul_comm]
  have hGq : ∫⁻ z, G z ^ q ∂μ ≤
      ENNReal.ofReal (hilbertConstant p) *
        eLpNorm b (ENNReal.ofReal q) Measure.count ^ q := by
    rw [lintegral_prod_symm (fun z => G z ^ q) (hG.pow_const q).aemeasurable]
    simp_rw [lintegral_count]
    have hinner : ∀ n, ∑' m, G (m, n) ^ q ≤
        ENNReal.ofReal (b n) ^ q * ENNReal.ofReal (hilbertConstant p) := by
      intro n
      have hpoint : ∀ m, G (m, n) ^ q =
          ENNReal.ofReal (b n) ^ q *
            ENNReal.ofReal (hilbertKernel (ι n) p⁻¹ (ι m)) := fun m => by
        simpa [G] using ofReal_hilbertRight_pow hpq (hpos m) (hpos n) (hb0 n)
      simp_rw [hpoint, ENNReal.tsum_mul_left]
      exact mul_le_mul_right (hRight n) _
    refine (ENNReal.tsum_le_tsum hinner).trans_eq ?_
    rw [ENNReal.tsum_mul_right, ← lintegral_count,
      lintegral_ofReal_rpow_eq_eLpNorm_rpow hpq.symm.lt hb0 hb.aestronglyMeasurable, mul_comm]
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hF.aemeasurable hG.aemeasurable
  rw [hprod] at hHolder
  refine hHolder.trans ?_
  refine (mul_le_mul' (ENNReal.rpow_le_rpow hFp hpq.one_div_nonneg)
      (ENNReal.rpow_le_rpow hGq hpq.symm.one_div_nonneg)).trans_eq ?_
  rw [show (1 / p : ℝ) = p⁻¹ from (inv_eq_one_div p).symm,
    show (1 / q : ℝ) = q⁻¹ from (inv_eq_one_div q).symm]
  rw [holder_schur_mul hc0 hct hpq.pos hpq.symm.pos hpq.inv_add_inv_eq_one]
  have hqexp : q = p / (p - 1) := by
    unfold q
    rfl
  rw [hqexp]

end CKMA
