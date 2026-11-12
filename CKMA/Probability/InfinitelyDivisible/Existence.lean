/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.InfinitelyDivisible.Law
public import CKMA.Probability.InfinitelyDivisible.Tightness

import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Existence of a Lévy–Khintchine triplet

Quadratically weighted convolution roots are tight. Along an ultrafilter, their kernel integrals
converge, and the compensating drifts converge with them. The atom at the origin is the Gaussian
variance. Inverting the quadratic weight off the origin produces the Lévy measure. A bounded
correction on `{1 / 2 ≤ |x| ≤ 1}` replaces the continuous cutoff by the truncation `|x| ≤ 1`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Complex Filter Topology Set BoundedContinuousFunction
open scoped NNReal ENNReal

/-- The Lévy kernel vanishes to the Gaussian symbol at the origin. -/
lemma levyKernel_zero (t : ℝ) : levyKernel t 0 = -((t : ℂ) ^ 2) / 2 := by
  simp [levyKernel]

/-- Real numbers are recovered from multiplication by `I` and then by `-I`. -/
lemma re_neg_I_mul_I (b : ℝ) : (-I * (I * (b : ℂ))).re = b := by
  have hmul : -I * (I * (b : ℂ)) = (b : ℂ) := by
    ring_nf
    simp [I_sq]
  rw [hmul, Complex.ofReal_re]

/-- `n + 1` times one minus a root characteristic function tends to the exponent. -/
lemma tendsto_nat_mul_charFun_sub_one {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) (t : ℝ) :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * (charFun (positiveRoot h n) t - 1))
      atTop (𝓝 (charExponent h t)) := by
  have hcomp := (tendsto_nat_mul_exp_div_sub_one (charExponent h t)).comp
    (tendsto_add_atTop_nat 1)
  refine hcomp.congr fun n => ?_
  rw [Function.comp_apply, charFun_positiveRoot]

/-- The root increment splits into a kernel integral and a continuous drift. -/
lemma charFun_sub_one_eq_kernel {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) (n : ℕ) (t : ℝ) :
    ((n + 1 : ℕ) : ℂ) * (charFun (positiveRoot h n) t - 1) =
      ∫ x, levyKernel t x ∂(idRootMeasure h n : Measure ℝ) +
        I * ↑t * ↑(contDrift (n + 1) (positiveRoot h n)) := by
  simpa [idRootMeasure, FiniteMeasure.toMeasure_mk] using
    nat_mul_charFun_sub_one_eq (ν := positiveRoot h n) (n + 1) t

/-- Kernel integrals pass to the weak limit of the weighted roots. -/
lemma tendsto_integral_levyKernel {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) {u : Ultrafilter ℕ} {ρ : FiniteMeasure ℝ}
    (htend : Tendsto (idRootMeasure h) (u : Filter ℕ) (𝓝 ρ)) (t : ℝ) :
    Tendsto (fun n => ∫ x, levyKernel t x ∂(idRootMeasure h n : Measure ℝ))
      (u : Filter ℕ) (𝓝 (∫ x, levyKernel t x ∂(ρ : Measure ℝ))) := by
  have hint :=
    ((FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp htend) (levyKernelBdd t)
  have hcoe : (levyKernelBdd t : ℝ → ℂ) = levyKernel t := by
    unfold levyKernelBdd
    rfl
  rw [hcoe] at hint
  exact hint

/-- The continuous drifts converge along any ultrafilter on which the weighted roots converge. -/
lemma tendsto_contDrift_ultra {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) {u : Ultrafilter ℕ} {ρ : FiniteMeasure ℝ}
    (hu : (u : Filter ℕ) ≤ atTop)
    (htend : Tendsto (idRootMeasure h) (u : Filter ℕ) (𝓝 ρ)) :
    Tendsto (fun n => contDrift (n + 1) (positiveRoot h n)) (u : Filter ℕ)
      (𝓝 ((-I * (charExponent h 1 -
        ∫ x, levyKernel 1 x ∂(ρ : Measure ℝ))).re)) := by
  set z : ℂ := charExponent h 1 - ∫ x, levyKernel 1 x ∂(ρ : Measure ℝ)
  have hseq := ((tendsto_nat_mul_charFun_sub_one h 1).mono_left hu).sub
    (tendsto_integral_levyKernel h htend 1)
  have hid : ∀ n, contDrift (n + 1) (positiveRoot h n) =
      (-I * (((n + 1 : ℕ) : ℂ) * (charFun (positiveRoot h n) 1 - 1) -
        ∫ x, levyKernel 1 x ∂(idRootMeasure h n : Measure ℝ))).re := by
    intro n
    have heq := charFun_sub_one_eq_kernel h n 1
    have hsub : ((n + 1 : ℕ) : ℂ) * (charFun (positiveRoot h n) 1 - 1) -
        ∫ x, levyKernel 1 x ∂(idRootMeasure h n : Measure ℝ) =
        I * ↑(contDrift (n + 1) (positiveRoot h n)) := by
      have hI : (I * ↑(1 : ℝ) * ↑(contDrift (n + 1) (positiveRoot h n))) =
          I * ↑(contDrift (n + 1) (positiveRoot h n)) := by
        push_cast
        ring
      rw [heq, add_sub_cancel_left, hI]
    rw [hsub, re_neg_I_mul_I]
  have hmul := hseq.const_mul (-I)
  have hre := (continuous_re.tendsto ((-I) * z)).comp hmul
  refine hre.congr fun n => ?_
  exact (hid n).symm

/-- Every frequency has the kernel-and-drift representation along that ultrafilter. -/
lemma charExponent_eq_kernel_drift {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) {u : Ultrafilter ℕ} {ρ : FiniteMeasure ℝ}
    (hu : (u : Filter ℕ) ≤ atTop)
    (htend : Tendsto (idRootMeasure h) (u : Filter ℕ) (𝓝 ρ)) (t : ℝ) :
    charExponent h t = ∫ x, levyKernel t x ∂(ρ : Measure ℝ) +
      I * ↑t * ↑((-I * (charExponent h 1 -
        ∫ x, levyKernel 1 x ∂(ρ : Measure ℝ))).re) := by
  set b : ℝ := (-I * (charExponent h 1 -
    ∫ x, levyKernel 1 x ∂(ρ : Measure ℝ))).re
  have hb := tendsto_contDrift_ultra h hu htend
  have hL := (tendsto_nat_mul_charFun_sub_one h t).mono_left hu
  have hK := tendsto_integral_levyKernel h htend t
  have hD : Tendsto (fun n => I * ↑t * ↑(contDrift (n + 1) (positiveRoot h n)))
      (u : Filter ℕ) (𝓝 (I * ↑t * ↑b)) := by
    have hcoe := (continuous_ofReal.tendsto b).comp hb
    simpa [mul_assoc] using hcoe.const_mul (I * ↑t)
  have hsum := hK.add hD
  have hpoint : ∀ n, ((n + 1 : ℕ) : ℂ) * (charFun (positiveRoot h n) t - 1) =
      ∫ x, levyKernel t x ∂(idRootMeasure h n : Measure ℝ) +
        I * ↑t * ↑(contDrift (n + 1) (positiveRoot h n)) :=
    fun n => charFun_sub_one_eq_kernel h n t
  exact tendsto_nhds_unique (hL.congr hpoint) hsum

/-- The Lévy measure obtained by inverting the quadratic weight. -/
def levyJump (ρ : Measure ℝ) : Measure ℝ :=
  ρ.withDensity fun x => ENNReal.ofReal (quadTrunc x)⁻¹

/-- The inverted quadratic weight is measurable. -/
lemma measurable_quadTrunc_inv :
    Measurable fun x : ℝ => ENNReal.ofReal (quadTrunc x)⁻¹ := by
  fun_prop

/-- Inverting the quadratic weight of a finite measure yields a Lévy measure. -/
lemma isLevyMeasure_levyJump {ρ : Measure ℝ} [IsFiniteMeasure ρ] :
    IsLevyMeasure (levyJump ρ) := by
  refine ⟨?_, ?_⟩
  · rw [levyJump, withDensity_apply _ (measurableSet_singleton _), lintegral_singleton]
    simp [quadTrunc, inv_zero]
  · show (∫⁻ x, ENNReal.ofReal (quadTrunc x) ∂levyJump ρ) < ∞
    rw [levyJump, lintegral_withDensity_eq_lintegral_mul ρ measurable_quadTrunc_inv
      (by fun_prop : Measurable fun x => ENNReal.ofReal (quadTrunc x))]
    have hpt :
        (fun x => ENNReal.ofReal (quadTrunc x)⁻¹) * (fun x => ENNReal.ofReal (quadTrunc x)) =
          fun x => ENNReal.ofReal (if x = 0 then 0 else 1) := by
      ext x
      rw [Pi.mul_apply, ← ENNReal.ofReal_mul (inv_nonneg.mpr (quadTrunc_nonneg x))]
      congr 1
      by_cases hx : x = 0
      · simp [hx, quadTrunc, inv_zero]
      · rw [inv_mul_cancel₀ (quadTrunc_eq_zero_iff.not.mpr hx)]
        simp [hx]
    rw [hpt]
    have hind : (fun x => ENNReal.ofReal (if x = 0 then (0 : ℝ) else 1)) =
        Set.indicator {(0 : ℝ)}ᶜ (fun _ => (1 : ℝ≥0∞)) := by
      ext x
      by_cases hx : x = 0
      · simp [hx]
      · simp [hx, ENNReal.ofReal_one]
    rw [hind, lintegral_indicator (measurableSet_singleton _).compl, setLIntegral_one]
    exact measure_lt_top ρ {(0 : ℝ)}ᶜ

/-- The continuous compensator is integrable against a Lévy measure. -/
lemma integrable_contIntegrand_levy {ν : Measure ℝ} (hν : IsLevyMeasure ν) (t : ℝ) :
    Integrable (contIntegrand t) ν := by
  have hbnd : 0 ≤ levyKernelBound t := by
    unfold levyKernelBound
    positivity
  have hdom : Integrable (fun x => levyKernelBound t * quadTrunc x) ν :=
    (integrable_min_one_sq hν).const_mul _
  refine hdom.mono' (by
    unfold contIntegrand
    fun_prop) ?_
  refine ae_of_all _ fun x => ?_
  rw [contIntegrand_eq_levyKernel_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (quadTrunc_nonneg x)]
  exact mul_le_mul_of_nonneg_right (norm_levyKernel_le t x) (quadTrunc_nonneg x)

/-- The cutoff correction vanishes for `|x| < 1 / 2`. -/
lemma contTrunc_sub_trunc_eq_zero_of_abs_lt {x : ℝ} (hx : |x| < 1 / 2) :
    contTrunc x - truncCompensator x = 0 := by
  have hle : |x| ≤ 1 / 2 := hx.le
  have htrunc : truncCompensator x = x := by
    rw [truncCompensator, ite_eq_left]
    exact hle.trans (by norm_num)
  rw [contTrunc_eq_id_of_abs_le_half hle, htrunc, sub_self]

/-- The cutoff correction is integrable against a Lévy measure. -/
lemma integrable_contTrunc_sub_trunc {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    Integrable (fun x : ℝ => contTrunc x - truncCompensator x) ν := by
  set s : Set ℝ := {x | (1 / 2 : ℝ) ≤ |x|}
  have hs : MeasurableSet s := measurableSet_abs_ge (1 / 2)
  have : IsFiniteMeasure (ν.restrict s) :=
    isFiniteMeasure_restrict_abs_ge hν (by norm_num)
  have hint : IntegrableOn (fun x : ℝ => contTrunc x - truncCompensator x) s ν := by
    refine (integrable_const (2 : ℝ)).mono'
      ((continuous_contTrunc.measurable.sub measurable_truncCompensator).aestronglyMeasurable) ?_
    refine ae_of_all _ fun x => ?_
    rw [Real.norm_eq_abs]
    have htrunc : |truncCompensator x| ≤ 1 := by
      simp only [truncCompensator]
      by_cases hx : |x| ≤ 1
      · rw [ite_eq_left hx]
        exact hx
      · rw [ite_eq_right hx, abs_zero]
        exact zero_le_one
    have hsum : |contTrunc x - truncCompensator x| ≤
        |contTrunc x| + |truncCompensator x| := by
      rw [sub_eq_add_neg, ← abs_neg (truncCompensator x)]
      exact abs_add_le (contTrunc x) (-truncCompensator x)
    have habs : |contTrunc x| + |truncCompensator x| ≤ 2 := by
      linarith [abs_contTrunc_le_one x, htrunc]
    linarith
  have heq : s.indicator (fun x : ℝ => contTrunc x - truncCompensator x) =
      fun x => contTrunc x - truncCompensator x := by
    ext x
    by_cases hx : x ∈ s
    · simp [hx]
    · rw [indicator_of_notMem hx]
      have habs : |x| < 1 / 2 := by
        simpa [s] using hx
      exact (contTrunc_sub_trunc_eq_zero_of_abs_lt habs).symm
  rw [← heq]
  exact hint.integrable_indicator hs

/-- The frozen truncation and the continuous cutoff differ by a pure drift integrand. -/
lemma levyIntegrand_eq_contIntegrand_add (t x : ℝ) :
    levyIntegrand t x = contIntegrand t x +
      I * ↑t * ↑(contTrunc x - truncCompensator x) := by
  by_cases hx : |x| ≤ 1
  · rw [levyIntegrand, contIntegrand, truncCompensator, ite_eq_left hx, ite_eq_left hx]
    push_cast
    ring_nf
  · have hc : contTrunc x = 0 := contTrunc_eq_zero_of_one_le_abs (le_of_not_ge hx)
    rw [levyIntegrand, contIntegrand, truncCompensator, ite_eq_right hx, ite_eq_right hx, hc]
    push_cast
    ring_nf

/-- Integrating the cutoff correction produces the drift adjustment. -/
lemma integral_levyIntegrand_eq_cont {ν : Measure ℝ} (hν : IsLevyMeasure ν) (t : ℝ) :
    ∫ x, levyIntegrand t x ∂ν = ∫ x, contIntegrand t x ∂ν +
      I * ↑t * ↑(∫ x, contTrunc x - truncCompensator x ∂ν) := by
  have hfun : (fun x => levyIntegrand t x) = fun x => contIntegrand t x +
      (I * ↑t) * ↑(contTrunc x - truncCompensator x) := by
    ext x
    simpa [mul_assoc] using levyIntegrand_eq_contIntegrand_add t x
  have hintc : Integrable (fun x => (I * ↑t) * ↑(contTrunc x - truncCompensator x)) ν :=
    (integrable_contTrunc_sub_trunc hν).ofReal.const_mul _
  rw [hfun, integral_add (integrable_contIntegrand_levy hν t) hintc, integral_const_mul,
    integral_complex_ofReal]

/-- On the complement of the origin the kernel integral is the continuous compensator. -/
lemma integral_contIntegrand_levyJump {ρ : FiniteMeasure ℝ} (t : ℝ) :
    ∫ x, contIntegrand t x ∂levyJump (ρ : Measure ℝ) =
      ∫ x in {(0 : ℝ)}ᶜ, levyKernel t x ∂(ρ : Measure ℝ) := by
  have hfin : ∀ᵐ x ∂(ρ : Measure ℝ), ENNReal.ofReal (quadTrunc x)⁻¹ < ∞ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  rw [levyJump, integral_withDensity_eq_integral_toReal_smul measurable_quadTrunc_inv hfin]
  have hpt : ∀ x, (ENNReal.ofReal (quadTrunc x)⁻¹).toReal • contIntegrand t x =
      Set.indicator {(0 : ℝ)}ᶜ (levyKernel t) x := by
    intro x
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (quadTrunc_nonneg x)),
      RCLike.real_smul_eq_coe_mul, contIntegrand_eq_levyKernel_mul]
    by_cases hx : x = 0
    · simp [hx, quadTrunc, inv_zero, levyKernel]
    · have hq : (quadTrunc x : ℂ) ≠ 0 := by
        exact_mod_cast quadTrunc_eq_zero_iff.not.mpr hx
      rw [indicator_of_mem (by simpa using hx)]
      calc
        (↑(quadTrunc x)⁻¹ : ℂ) * (levyKernel t x * ↑(quadTrunc x)) =
            levyKernel t x * (↑(quadTrunc x)⁻¹ * ↑(quadTrunc x)) := by ring
        _ = levyKernel t x * ↑((quadTrunc x)⁻¹ * quadTrunc x) := by
          rw [← Complex.ofReal_mul]
        _ = levyKernel t x := by
          rw [inv_mul_cancel₀ (quadTrunc_eq_zero_iff.not.mpr hx), Complex.ofReal_one, mul_one]
  rw [funext hpt, integral_indicator (measurableSet_singleton _).compl]

/-- The kernel integral splits into the Gaussian atom and the continuous compensator. -/
lemma integral_levyKernel_eq_atom {ρ : FiniteMeasure ℝ} (t : ℝ) :
    ∫ x, levyKernel t x ∂(ρ : Measure ℝ) =
      (ρ : Measure ℝ).real {0} • levyKernel t 0 +
        ∫ x, contIntegrand t x ∂levyJump (ρ : Measure ℝ) := by
  have hint : Integrable (levyKernel t) (ρ : Measure ℝ) := by
    refine (integrable_const (levyKernelBound t)).mono'
      (continuous_levyKernel t).aestronglyMeasurable ?_
    refine ae_of_all _ fun x => ?_
    simpa [levyKernelBound] using norm_levyKernel_le t x
  have hsplit := integral_add_compl (measurableSet_singleton (0 : ℝ)) hint
  rw [integral_singleton] at hsplit
  rw [integral_contIntegrand_levyJump]
  exact hsplit.symm

/-- A kernel-and-drift representation is the exponent of an explicit Lévy triplet. -/
lemma exists_levyTriplet_of_kernel_drift {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) {ρ : FiniteMeasure ℝ} {b : ℝ}
    (hψ : ∀ t, charExponent h t =
      ∫ x, levyKernel t x ∂(ρ : Measure ℝ) + I * ↑t * ↑b) :
    ∃ L : LevyTriplet, ∀ t, charFun μ t = exp (L.exponent t) := by
  let ν : Measure ℝ := levyJump (ρ : Measure ℝ)
  have hν : IsLevyMeasure ν := isLevyMeasure_levyJump
  set aReal : ℝ := (ρ : Measure ℝ).real {0}
  set a : ℝ≥0 := Real.toNNReal aReal
  have ha0 : 0 ≤ aReal := ENNReal.toReal_nonneg
  have ha : (a : ℝ) = aReal := Real.coe_toNNReal _ ha0
  set c : ℝ := ∫ x, contTrunc x - truncCompensator x ∂ν
  let L : LevyTriplet :=
    { gaussianVariance := a
      drift := b - c
      jumpMeasure := ν
      isLevyMeasure := hν }
  refine ⟨L, fun t => ?_⟩
  rw [← exp_charExponent h t]
  congr 1
  rw [hψ t, integral_levyKernel_eq_atom, levyKernel_zero, LevyTriplet.exponent_eq_levyIntegrand]
  have hint := integral_levyIntegrand_eq_cont hν t
  have hsmul : aReal • (-((t : ℂ) ^ 2) / 2) = -((a : ℂ) * (t : ℂ) ^ 2 / 2) := by
    rw [ha.symm, RCLike.real_smul_eq_coe_mul]
    conv_lhs => rw [← mul_div_assoc, mul_neg]
    exact neg_div (2 : ℂ) ((a : ℂ) * (t : ℂ) ^ 2)
  rw [show levyJump (ρ : Measure ℝ) = ν from rfl, hsmul, hint]
  simp only [L]
  dsimp only [c]
  push_cast
  ring_nf

/-- Some weak limit of the weighted roots supplies a Lévy triplet. -/
lemma exists_levyTriplet_of_isInfinitelyDivisible {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) :
    ∃ L : LevyTriplet, ∀ t, charFun μ t = exp (L.exponent t) := by
  let u : Ultrafilter ℕ := Ultrafilter.of atTop
  have hu : (u : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  let T : Set (FiniteMeasure ℝ) := {ρ |
    ρ.mass ≤ idMass h ∧ ∀ k, ρ (tailSet k)ᶜ ≤ idTail h k}
  have hT : IsCompact T := by simpa [T] using isCompact_idApproximant h
  let uf : Ultrafilter (FiniteMeasure ℝ) := u.map (idRootMeasure h)
  have hTmem : T ∈ uf := by
    rw [Ultrafilter.mem_map]
    exact univ_mem' (idRootMeasure_mem h)
  obtain ⟨ρ, hρT, hlim⟩ := hT.ultrafilter_le_nhds' uf hTmem
  have htend : Tendsto (idRootMeasure h) (u : Filter ℕ) (𝓝 ρ) := by
    change Filter.map (idRootMeasure h) ↑u ≤ 𝓝 ρ
    simpa [uf, Ultrafilter.coe_map] using hlim
  have hψ : ∀ t, charExponent h t =
      ∫ x, levyKernel t x ∂(ρ : Measure ℝ) +
        I * ↑t * ↑((-I * (charExponent h 1 -
          ∫ x, levyKernel 1 x ∂(ρ : Measure ℝ))).re) :=
    fun t => charExponent_eq_kernel_drift h hu htend t
  exact exists_levyTriplet_of_kernel_drift h hψ

end CKMA
