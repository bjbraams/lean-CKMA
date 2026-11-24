/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SumIntegralComparisons

/-!
# The Hilbert kernel

Auxiliary analysis of the kernel `k_α(x, y) = (x / y) ^ α / (x + y)` on the positive
half-line, used for Hilbert's inequality and the optimality of its constant.

The slice integral `∫_{y > 0} k_α(x, y) dy = π / sin (π α)` for `0 < α < 1` is the Beta
integral `Beta(1 - α, α)`, evaluated by the substitution `t = u / (1 - u)` in Mathlib's
`Complex.betaIntegral` and Euler's reflection formula `Real.Gamma_mul_Gamma_one_sub`. The kernel
decreases in `y`, so its samples at positive integers are bounded by the slice integral.

For optimality, the slice integral truncated to `(1, M)` misses at most the explicit tails
`x ^ (α - 1) / (1 - α)` on `(0, 1]` and `x ^ α M ^ (-α) / α` on `[M, ∞)`. Elementary
comparisons of antitone functions with their integrals, power integrals, and a limiting
argument for affine bounds in `ℝ≥0∞` complete the toolkit. Source: GAPS 11.37.

## Main definitions

* `CKMA.Hilbert.hilbertKernel`: the kernel `(k / t) ^ α / (k + t)` on `t > 0`, extended by `0`.

## Main results

* `CKMA.Hilbert.lintegral_hilbertKernel`: the slice integral equals `π / sin (π α)`.
* `CKMA.Hilbert.tsum_hilbertKernel_le`: the integer samples are bounded by the slice integral.
* `CKMA.Hilbert.ofReal_pi_div_sin_le_lintegral_Ioo`: the truncated slice estimate.
-/

public section

noncomputable section

namespace CKMA.Hilbert

open MeasureTheory Set intervalIntegral
open scoped ENNReal

/-- Real power `x ^ c` for `x > 0`, and `0` otherwise. -/
@[expose]
def rpowPos (c x : ℝ) : ℝ :=
  if 0 < x then Real.exp (c * Real.log x) else 0

/-- `rpowPos` agrees with `Real.rpow` on positive bases. -/
lemma rpowPos_eq {c x : ℝ} (hx : 0 < x) : rpowPos c x = x ^ c := by
  simp [rpowPos, hx, Real.rpow_def_of_pos hx, mul_comm]

/-- `rpowPos` is nonnegative. -/
lemma rpowPos_nonneg (c x : ℝ) : 0 ≤ rpowPos c x := by
  unfold rpowPos
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

/-- `rpowPos` is positive on a positive base. -/
lemma rpowPos_pos {c x : ℝ} (hx : 0 < x) : 0 < rpowPos c x := by
  simp [rpowPos, hx, Real.exp_pos]

/-- `rpowPos` is measurable in the base. -/
@[fun_prop]
lemma measurable_rpowPos (c : ℝ) : Measurable (rpowPos c) := by
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
@[expose]
def hilbertKernel (k α t : ℝ) : ℝ :=
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
lemma hilbertKernel_eq {k α t : ℝ} (hk : 0 < k) (ht : 0 < t) :
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
lemma hilbertKernel_antitone {k α : ℝ} (hk : 0 < k) (hα : 0 < α) :
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
lemma lintegral_hilbertKernel {k α : ℝ} (hk : 0 < k) (hα0 : 0 < α) (hα1 : α < 1) :
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
lemma tsum_hilbertKernel_le {k α : ℝ} (hk : 0 < k) (hα0 : 0 < α) (hα1 : α < 1) :
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

/-- Lebesgue integral of `y ^ r` over `(0, M]` for `r > -1`. -/
lemma lintegral_Ioc_rpow {r M : ℝ} (hr : -1 < r) (hM : 0 < M) :
    ∫⁻ y in Ioc (0 : ℝ) M, ENNReal.ofReal (y ^ r) =
      ENNReal.ofReal (M ^ (r + 1) / (r + 1)) := by
  have hint : IntegrableOn (fun y : ℝ => y ^ r) (Ioc 0 M) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hM.le).mp
      (intervalIntegral.intervalIntegrable_rpow' hr)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_restrict_of_forall_mem measurableSet_Ioc fun y hy => Real.rpow_nonneg hy.1.le r),
    ← intervalIntegral.integral_of_le hM.le, integral_rpow (Or.inl hr),
    Real.zero_rpow (by linarith), sub_zero]

/-- Lebesgue integral of `y ^ r` over `(M, ∞)` for `r < -1`. -/
lemma lintegral_Ioi_rpow {r M : ℝ} (hr : r < -1) (hM : 0 < M) :
    ∫⁻ y in Ioi M, ENNReal.ofReal (y ^ r) = ENNReal.ofReal (-M ^ (r + 1) / (r + 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hr hM)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy =>
        Real.rpow_nonneg (hM.trans hy).le r),
    integral_Ioi_rpow_of_lt hr hM]

/-- Near the origin the kernel is at most `x ^ (a - 1) y ^ (-a)`. -/
private lemma hilbertKernel_le_left {a x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hilbertKernel x a y ≤ x ^ (a - 1) * y ^ (-a) := by
  rw [hilbertKernel_eq hx hy, Real.div_rpow hx.le hy.le, Real.rpow_sub_one hx.ne',
    Real.rpow_neg hy.le]
  have h : x ^ a / y ^ a / (x + y) ≤ x ^ a / y ^ a / x :=
    div_le_div_of_nonneg_left (by positivity) hx (by linarith)
  exact h.trans_eq (by ring)

/-- Away from the origin the kernel is at most `x ^ a y ^ (-a - 1)`. -/
private lemma hilbertKernel_le_right {a x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hilbertKernel x a y ≤ x ^ a * y ^ (-a - 1) := by
  rw [hilbertKernel_eq hx hy, Real.div_rpow hx.le hy.le, Real.rpow_sub_one hy.ne',
    Real.rpow_neg hy.le]
  have h : x ^ a / y ^ a / (x + y) ≤ x ^ a / y ^ a / y :=
    div_le_div_of_nonneg_left (by positivity) hy (by linarith)
  exact h.trans_eq (by ring)

/-- Truncating the kernel integral to `(1, M)` loses at most two explicit tail terms. -/
lemma ofReal_pi_div_sin_le_lintegral_Ioo {a x M : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hx : 0 < x) (hM : 0 < M) :
    ENNReal.ofReal (Real.pi / Real.sin (Real.pi * a)) ≤
      (∫⁻ y in Ioo 1 M, ENNReal.ofReal (hilbertKernel x a y)) +
        (ENNReal.ofReal (x ^ (a - 1) / (1 - a)) + ENNReal.ofReal (x ^ a * (M ^ (-a) / a))) := by
  rw [← lintegral_hilbertKernel hx ha0 ha1]
  have hcover : Ioi (0 : ℝ) ⊆ Ioo 1 M ∪ (Ioc 0 1 ∪ Ici M) := by
    intro y hy
    by_cases h1 : y ≤ 1
    · exact Or.inr (Or.inl ⟨hy, h1⟩)
    · by_cases h2 : y < M
      · exact Or.inl ⟨lt_of_not_ge h1, h2⟩
      · exact Or.inr (Or.inr (le_of_not_gt h2))
  have hleft : ∫⁻ y in Ioc (0 : ℝ) 1, ENNReal.ofReal (hilbertKernel x a y) ≤
      ENNReal.ofReal (x ^ (a - 1) / (1 - a)) := by
    calc ∫⁻ y in Ioc (0 : ℝ) 1, ENNReal.ofReal (hilbertKernel x a y)
        ≤ ∫⁻ y in Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ (a - 1)) * ENNReal.ofReal (y ^ (-a)) :=
          setLIntegral_mono' measurableSet_Ioc fun y hy => by
            rw [← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal (hilbertKernel_le_left hx hy.1)
      _ = ENNReal.ofReal (x ^ (a - 1) / (1 - a)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_Ioc_rpow (by linarith) one_pos, Real.one_rpow,
            ← ENNReal.ofReal_mul (by positivity), neg_add_eq_sub, mul_one_div]
  have hright : ∫⁻ y in Ici M, ENNReal.ofReal (hilbertKernel x a y) ≤
      ENNReal.ofReal (x ^ a * (M ^ (-a) / a)) := by
    rw [← setLIntegral_congr Ioi_ae_eq_Ici]
    calc ∫⁻ y in Ioi M, ENNReal.ofReal (hilbertKernel x a y)
        ≤ ∫⁻ y in Ioi M, ENNReal.ofReal (x ^ a) * ENNReal.ofReal (y ^ (-a - 1)) :=
          setLIntegral_mono' measurableSet_Ioi fun y hy => by
            rw [← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal (hilbertKernel_le_right hx (hM.trans hy))
      _ = ENNReal.ofReal (x ^ a * (M ^ (-a) / a)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_Ioi_rpow (by linarith) hM, ← ENNReal.ofReal_mul (by positivity),
            show -a - 1 + 1 = -a by ring, neg_div_neg_eq]
  calc ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (hilbertKernel x a y)
      ≤ ∫⁻ y in Ioo 1 M ∪ (Ioc 0 1 ∪ Ici M), ENNReal.ofReal (hilbertKernel x a y) :=
        lintegral_mono_set hcover
    _ ≤ _ := (lintegral_union_le _ _ _).trans
        (add_le_add le_rfl ((lintegral_union_le _ _ _).trans (add_le_add hleft hright)))

/-- The test integrand factors as `x⁻¹` times the kernel with exponent `a`. -/
lemma rpow_mul_rpow_div_eq {a x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x ^ (a - 1) * y ^ (-a) / (x + y) = x⁻¹ * hilbertKernel x a y := by
  rw [hilbertKernel_eq hx hy, Real.div_rpow hx.le hy.le, Real.rpow_sub_one hx.ne',
    Real.rpow_neg hy.le]
  ring

/-- The two tail terms of the row estimate, multiplied by `x⁻¹`. -/
lemma ofReal_inv_mul_tail {a x c : ℝ} (hx : 0 < x) :
    ENNReal.ofReal x⁻¹ *
        (ENNReal.ofReal (x ^ (a - 1) / (1 - a)) + ENNReal.ofReal (x ^ a * c)) =
      ENNReal.ofReal (x ^ (a - 2)) * ENNReal.ofReal (1 - a)⁻¹ +
        ENNReal.ofReal (x ^ (a - 1)) * ENNReal.ofReal c := by
  have h1 : x⁻¹ * (x ^ (a - 1) / (1 - a)) = x ^ (a - 2) * (1 - a)⁻¹ := by
    rw [show a - 2 = (a - 1) - 1 by ring, Real.rpow_sub_one hx.ne' (a - 1)]
    ring
  have h2 : x⁻¹ * (x ^ a * c) = x ^ (a - 1) * c := by
    rw [Real.rpow_sub_one hx.ne']
    ring
  have hinv : 0 ≤ x⁻¹ := inv_nonneg.mpr hx.le
  rw [mul_add, ← ENNReal.ofReal_mul hinv, ← ENNReal.ofReal_mul hinv, h1, h2,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]

/-- Numerical form of the optimality argument: an affine bound `k L ≤ c L + d` along
unbounded finite `L` forces `k ≤ c`. -/
lemma le_of_forall_nat_le_mul_le {k c d : ℝ≥0∞} (hd : d ≠ ⊤)
    (h : ∀ n : ℕ, ∃ L : ℝ≥0∞, (n : ℝ≥0∞) ≤ L ∧ L ≠ ⊤ ∧ k * L ≤ c * L + d) : k ≤ c := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt (tsub_pos_of_lt hlt).ne' hd
  obtain ⟨L, hnL, hLt, hkL⟩ := h n
  have hsub : (k - c) * L ≤ d := by
    rw [ENNReal.sub_mul fun _ _ => hLt]
    exact tsub_le_iff_right.mpr (by rwa [add_comm])
  exact (hn.trans_le ((mul_le_mul_left hnL _).trans_eq (mul_comm _ _))).not_ge hsub

/-- `∫_1^N dx / x = log N`. -/
lemma lintegral_Ioo_inv {N : ℝ} (hN : 1 < N) :
    ∫⁻ x in Ioo 1 N, ENNReal.ofReal x⁻¹ = ENNReal.ofReal (Real.log N) := by
  have hsub : Icc (1 : ℝ) N ⊆ {0}ᶜ := fun x hx => (zero_lt_one.trans_le hx.1).ne'
  have hint : IntegrableOn (fun x : ℝ => x⁻¹) (Ioc 1 N) :=
    ((continuousOn_inv₀.mono hsub).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, ← ofReal_integral_eq_lintegral_ofReal hint
      (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx =>
        (inv_pos.mpr (zero_lt_one.trans hx.1)).le),
    ← intervalIntegral.integral_of_le hN.le, integral_inv_of_pos one_pos (one_pos.trans hN),
    div_one]

/-- An antitone function on `(0, ∞)` has integral over `(1, N + 1)` at most the sum of its
values at `1, …, N`. -/
lemma lintegral_Ioo_le_sum_of_antitoneOn {φ : ℝ → ℝ≥0∞} (hφ : AntitoneOn φ (Ioi 0))
    (N : ℕ) : ∫⁻ y in Ioo 1 ((N : ℝ) + 1), φ y ≤ ∑ n ∈ Finset.range N, φ ((n : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN : (0 : ℝ) ≤ N := N.cast_nonneg
    have hcover : Ioo 1 (((N + 1 : ℕ) : ℝ) + 1) ⊆
        Ioo 1 ((N : ℝ) + 1) ∪ Ico ((N : ℝ) + 1) ((N : ℝ) + 1 + 1) := by
      intro y hy
      push_cast at hy
      by_cases h : y < (N : ℝ) + 1
      · exact Or.inl ⟨hy.1, h⟩
      · exact Or.inr ⟨le_of_not_gt h, hy.2⟩
    have hlast : ∫⁻ y in Ico ((N : ℝ) + 1) ((N : ℝ) + 1 + 1), φ y ≤ φ ((N : ℝ) + 1) := by
      calc ∫⁻ y in Ico ((N : ℝ) + 1) ((N : ℝ) + 1 + 1), φ y
          ≤ ∫⁻ _ in Ico ((N : ℝ) + 1) ((N : ℝ) + 1 + 1), φ ((N : ℝ) + 1) :=
            setLIntegral_mono' measurableSet_Ico fun y hy =>
              hφ (show (0 : ℝ) < N + 1 by positivity)
                (show (0 : ℝ) < y by linarith [hy.1]) hy.1
        _ = φ ((N : ℝ) + 1) := by simp [Real.volume_Ico]
    rw [Finset.sum_range_succ]
    exact (lintegral_mono_set hcover).trans
      ((lintegral_union_le _ _ _).trans (add_le_add ih hlast))

/-- The values of an antitone function on `(0, ∞)` at `1, …, N` sum to at most its integral
over `(0, N]`. -/
lemma sum_le_lintegral_Ioc_of_antitoneOn {ψ : ℝ → ℝ≥0∞} (hψ : AntitoneOn ψ (Ioi 0))
    (N : ℕ) : ∑ m ∈ Finset.range N, ψ ((m : ℝ) + 1) ≤ ∫⁻ x in Ioc 0 (N : ℝ), ψ x := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN : (0 : ℝ) ≤ N := N.cast_nonneg
    have hlast : ψ ((N : ℝ) + 1) ≤ ∫⁻ x in Ioc (N : ℝ) ((N : ℝ) + 1), ψ x := by
      calc ψ ((N : ℝ) + 1) = ∫⁻ _ in Ioc (N : ℝ) ((N : ℝ) + 1), ψ ((N : ℝ) + 1) := by
            simp [Real.volume_Ioc]
        _ ≤ _ := setLIntegral_mono' measurableSet_Ioc fun x hx =>
            hψ (show (0 : ℝ) < x from lt_of_le_of_lt hN hx.1)
              (show (0 : ℝ) < N + 1 by positivity) hx.2
    rw [Finset.sum_range_succ, Nat.cast_succ,
      ← Ioc_union_Ioc_eq_Ioc hN (by linarith : (N : ℝ) ≤ N + 1),
      lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)]
    exact add_le_add ih hlast

end CKMA.Hilbert
