/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.InfinitelyDivisible.CharRoot
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Continuous Lévy kernel

The truncation `x` on `{|x| ≤ 1}` makes the Lévy integrand discontinuous on that boundary.
A continuous cutoff, equal to the identity on `[-1/2, 1/2]` and vanishing for `|x| ≥ 1`,
produces a bounded continuous kernel. Against the quadratically weighted convolution roots,
its integral recovers `n` times one minus the root characteristic function, up to a real drift.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Complex Filter Topology Finset
open scoped NNReal ENNReal BoundedContinuousFunction

/-- Quadratic weight `min(1, x²)`, vanishing only at the origin. -/
def quadTrunc (x : ℝ) : ℝ := min 1 (x ^ 2)

/-- The quadratic weight is nonnegative. -/
lemma quadTrunc_nonneg (x : ℝ) : 0 ≤ quadTrunc x :=
  le_min (by norm_num) (sq_nonneg x)

/-- The quadratic weight is at most one. -/
lemma quadTrunc_le_one (x : ℝ) : quadTrunc x ≤ 1 := min_le_left _ _

/-- The quadratic weight vanishes exactly at the origin. -/
lemma quadTrunc_eq_zero_iff {x : ℝ} : quadTrunc x = 0 ↔ x = 0 := by
  unfold quadTrunc
  constructor
  · intro h
    rcases min_eq_iff.mp h with ⟨h1, -⟩ | ⟨h2, -⟩
    · norm_num at h1
    · exact sq_eq_zero_iff.mp h2
  · rintro rfl
    simp

/-- On `{|x| ≤ 1}` the quadratic weight equals `x²`. -/
lemma quadTrunc_eq_sq_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) : quadTrunc x = x ^ 2 := by
  have : x ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg _) hx
  exact min_eq_right this

/-- Continuous cutoff, equal to `x` on `[-1/2, 1/2]` and equal to `0` for `|x| ≥ 1`. -/
def contTrunc (x : ℝ) : ℝ := x * max 0 (min 1 (2 - 2 * |x|))

/-- The continuous cutoff is continuous. -/
@[fun_prop]
lemma continuous_contTrunc : Continuous contTrunc := by
  unfold contTrunc
  fun_prop

/-- The cutoff factor lies in the unit interval. -/
lemma contTrunc_factor_bounds (x : ℝ) :
    0 ≤ max 0 (min 1 (2 - 2 * |x|)) ∧ max 0 (min 1 (2 - 2 * |x|)) ≤ 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- The continuous cutoff is bounded by one. -/
lemma abs_contTrunc_le_one (x : ℝ) : |contTrunc x| ≤ 1 := by
  simp only [contTrunc, abs_mul]
  by_cases hx : |x| ≤ 1
  · have h0 : 0 ≤ max 0 (min 1 (2 - 2 * |x|)) := le_max_left _ _
    rw [abs_of_nonneg h0]
    have h1 : max 0 (min 1 (2 - 2 * |x|)) ≤ 1 := max_le (by norm_num) (min_le_left _ _)
    have hx0 : 0 ≤ |x| := abs_nonneg _
    nlinarith
  · have hle : 2 - 2 * |x| ≤ 0 := by linarith
    simp [min_eq_right (hle.trans zero_le_one), max_eq_left hle]

/-- The cutoff agrees with the identity for `|x| ≤ 1/2`. -/
lemma contTrunc_eq_id_of_abs_le_half {x : ℝ} (hx : |x| ≤ 1 / 2) : contTrunc x = x := by
  have : min 1 (2 - 2 * |x|) = 1 := min_eq_left (by linarith)
  simp [contTrunc, this]

/-- The cutoff vanishes for `|x| ≥ 1`. -/
lemma contTrunc_eq_zero_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) : contTrunc x = 0 := by
  have : 2 - 2 * |x| ≤ 0 := by linarith
  simp [contTrunc, min_eq_right (this.trans zero_le_one), max_eq_left this]

/-- On the unit interval the cutoff differs from the identity by at most one. -/
lemma abs_sub_contTrunc_le_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    |x - contTrunc x| ≤ 1 := by
  by_cases hhalf : |x| ≤ 1 / 2
  · simp [contTrunc_eq_id_of_abs_le_half hhalf]
  · have hmid : 1 / 2 ≤ |x| := le_of_not_ge hhalf
    have hfac : max 0 (min 1 (2 - 2 * |x|)) = 2 - 2 * |x| := by
      have hle : 2 - 2 * |x| ≤ 1 := by linarith
      have hge : 0 ≤ 2 - 2 * |x| := by linarith
      simp [min_eq_right hle, max_eq_right hge]
    have hdiff : x - contTrunc x = x * (2 * |x| - 1) := by
      simp only [contTrunc, hfac]
      ring
    rw [hdiff, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * |x| - 1)]
    nlinarith [abs_nonneg x, hx, hmid]

/-- Continuous compensator `exp(i t x) - 1 - i t c(x)`. -/
def contIntegrand (t x : ℝ) : ℂ :=
  exp (I * ↑t * ↑x) - 1 - I * ↑t * ↑(contTrunc x)

/-- Lévy kernel for the continuous cutoff, with value `-t² / 2` at the origin. -/
def levyKernel (t x : ℝ) : ℂ :=
  if x = 0 then -((t : ℂ) ^ 2) / 2 else contIntegrand t x / ↑(quadTrunc x)

/-- Second-order Taylor remainder of the complex exponential. -/
lemma norm_exp_sub_taylor2_le (y : ℂ) :
    ‖exp y - 1 - y - y ^ 2 / 2‖ ≤ ‖y‖ ^ 3 * Real.exp ‖y‖ := by
  have h := norm_exp_sub_sum_le_norm_mul_exp y 3
  have hs : ∑ m ∈ range 3, y ^ m / (m.factorial : ℂ) = 1 + y + y ^ 2 / 2 := by
    simp [sum_range_succ, Nat.factorial]
  have heq : ‖exp y - 1 - y - y ^ 2 / 2‖ =
      ‖exp y - ∑ m ∈ range 3, y ^ m / (m.factorial : ℂ)‖ := by
    congr 1
    rw [hs]
    ring
  exact heq.trans_le h

/-- First-order remainder of the complex exponential. -/
lemma norm_exp_sub_one_sub_le (y : ℂ) :
    ‖exp y - 1 - y‖ ≤ ‖y‖ ^ 2 * Real.exp ‖y‖ := by
  have h := norm_exp_sub_sum_le_norm_mul_exp y 2
  have hs : ∑ m ∈ range 2, y ^ m / (m.factorial : ℂ) = 1 + y := by
    simp [sum_range_succ, Nat.factorial]
  have heq : ‖exp y - 1 - y‖ = ‖exp y - ∑ m ∈ range 2, y ^ m / (m.factorial : ℂ)‖ := by
    congr 1
    rw [hs]
    ring
  exact heq.trans_le h

/-- `(exp y - 1 - y) / y²`, with value `1/2` at the origin. -/
def expTaylorQuotient (y : ℂ) : ℂ :=
  if y = 0 then 1 / 2 else (exp y - 1 - y) / y ^ 2

/-- The normalized remainder tends to `1/2`. -/
lemma tendsto_expTaylorQuotient :
    Tendsto expTaylorQuotient (𝓝 (0 : ℂ)) (𝓝 ((1 : ℂ) / 2)) := by
  have hnorm : ∀ y, ‖expTaylorQuotient y - 1 / 2‖ ≤ ‖y‖ * Real.exp ‖y‖ := by
    intro y
    by_cases hy : y = 0
    · simp [expTaylorQuotient, hy]
    · have hsub : expTaylorQuotient y - 1 / 2 =
          (exp y - 1 - y - y ^ 2 / 2) / y ^ 2 := by
        simp only [expTaylorQuotient, ite_eq_right hy]
        have hhalf : (1 : ℂ) / 2 = (y ^ 2 / 2) / y ^ 2 := by
          field_simp [hy]
        rw [hhalf, div_sub_div_same]
      rw [hsub, norm_div, norm_pow]
      have hpos : 0 < ‖y‖ ^ 2 := pow_pos (norm_pos_iff.mpr hy) 2
      rw [div_le_iff₀ hpos]
      calc
        ‖exp y - 1 - y - y ^ 2 / 2‖ ≤ ‖y‖ ^ 3 * Real.exp ‖y‖ :=
          norm_exp_sub_taylor2_le y
        _ = ‖y‖ * Real.exp ‖y‖ * ‖y‖ ^ 2 := by ring
  have h0 : Tendsto (fun y : ℂ => expTaylorQuotient y - 1 / 2) (𝓝 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ ?_ hnorm
    · have hlim := (continuous_norm.tendsto (0 : ℂ)).mul
        ((Real.continuous_exp.comp continuous_norm).tendsto (0 : ℂ))
      simpa [norm_zero, Real.exp_zero, zero_mul] using hlim
    · intro y
      exact norm_nonneg _
  have hadd := h0.add (tendsto_const_nhds (x := (1 : ℂ) / 2))
  have hfun : (fun y => expTaylorQuotient y - 1 / 2 + 1 / 2) = expTaylorQuotient := by
    ext y
    ring
  rw [hfun, zero_add] at hadd
  exact hadd

/-- Near the origin the kernel is the second-order Taylor quotient of `exp`. -/
lemma levyKernel_eq_taylor_of_abs_le_half {t x : ℝ} (hx : |x| ≤ 1 / 2) :
    levyKernel t x = expTaylorQuotient (I * ↑t * ↑x) * (I * ↑t) ^ 2 := by
  by_cases hx0 : x = 0
  · simp only [levyKernel, expTaylorQuotient, hx0, Complex.ofReal_zero, mul_zero]
    rw [ite_eq_left trivial, ite_eq_left trivial, mul_pow, I_sq]
    ring
  · by_cases ht0 : t = 0
    · simp [levyKernel, expTaylorQuotient, contIntegrand, hx0, ht0,
        contTrunc_eq_id_of_abs_le_half hx]
    · set y : ℂ := I * ↑t * ↑x
      have hy : y ≠ 0 := by
        intro h
        rcases mul_eq_zero.mp h with hIt | hx'
        · rcases mul_eq_zero.mp hIt with hI | ht
          · exact I_ne_zero hI
          · exact ht0 (Complex.ofReal_eq_zero.mp ht)
        · exact hx0 (Complex.ofReal_eq_zero.mp hx')
      have hq : quadTrunc x = x ^ 2 :=
        quadTrunc_eq_sq_of_abs_le_one (hx.trans (by norm_num))
      have hc : contTrunc x = x := contTrunc_eq_id_of_abs_le_half hx
      have hy2 : y ^ 2 = (I * ↑t) ^ 2 * ↑(x ^ 2) := by
        simp only [y]
        push_cast
        ring
      rw [levyKernel, ite_eq_right hx0, contIntegrand, hc, hq, expTaylorQuotient,
        ite_eq_right hy]
      rw [div_eq_iff (by exact_mod_cast pow_ne_zero 2 hx0 : (↑(x ^ 2) : ℂ) ≠ 0)]
      calc
        exp (I * ↑t * ↑x) - 1 - I * ↑t * ↑x = exp y - 1 - y := by simp [y]
        _ = (exp y - 1 - y) / y ^ 2 * y ^ 2 := by
          rw [div_mul_cancel₀ _ (pow_ne_zero 2 hy)]
        _ = (exp y - 1 - y) / y ^ 2 * ((I * ↑t) ^ 2 * ↑(x ^ 2)) := by rw [hy2]
        _ = (exp y - 1 - y) / y ^ 2 * (I * ↑t) ^ 2 * ↑(x ^ 2) := by ring

/-- The Lévy kernel is continuous. -/
lemma continuous_levyKernel (t : ℝ) : Continuous (levyKernel t) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases hx : x = 0
  · subst hx
    let g : ℝ → ℂ := fun y => expTaylorQuotient (I * ↑t * ↑y) * (I * ↑t) ^ 2
    have hnear : levyKernel t =ᶠ[𝓝 0] g := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with y hy
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
      exact levyKernel_eq_taylor_of_abs_le_half hy.le
    have hinner : Tendsto (fun y : ℝ => I * ↑t * ↑y) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_ofReal.const_mul (I * ↑t)).tendsto (0 : ℝ)
    have hg : Tendsto g (𝓝 0) (𝓝 ((1 : ℂ) / 2 * (I * ↑t) ^ 2)) :=
      (tendsto_expTaylorQuotient.comp hinner).mul tendsto_const_nhds
    have hval : (1 : ℂ) / 2 * (I * ↑t) ^ 2 = levyKernel t 0 := by
      rw [levyKernel, ite_eq_left rfl, mul_pow, I_sq]
      ring
    rw [hval] at hg
    exact hg.congr' hnear.symm
  · have hcont : ContinuousAt (fun y => contIntegrand t y / ↑(quadTrunc y)) x := by
      have hden : ContinuousAt (fun y : ℝ => (quadTrunc y : ℂ)) x := by
        unfold quadTrunc
        fun_prop
      have hnum : ContinuousAt (contIntegrand t) x := by
        unfold contIntegrand
        fun_prop
      exact hnum.div hden (by exact_mod_cast quadTrunc_eq_zero_iff.not.mpr hx)
    refine hcont.congr ?_
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [levyKernel, hy]

/-- The Lévy kernel is bounded by a constant depending only on the frequency. -/
lemma norm_levyKernel_le (t x : ℝ) :
    ‖levyKernel t x‖ ≤ 8 * (t ^ 2 + 1) * Real.exp |t| + 2 := by
  have hroom : t ^ 2 * Real.exp |t| + 4 * |t| ≤
      8 * (t ^ 2 + 1) * Real.exp |t| + 2 := by
    have hexp : 1 ≤ Real.exp |t| := Real.one_le_exp (abs_nonneg _)
    have habs : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith [sq_nonneg t, hexp, sq_nonneg (|t| - 1)]
  by_cases hx0 : x = 0
  · rw [levyKernel, ite_eq_left hx0]
    have : ‖-((t : ℂ) ^ 2) / 2‖ = t ^ 2 / 2 := by
      have ht : ‖(t : ℂ)‖ = |t| := by rw [Complex.norm_real, Real.norm_eq_abs]
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [norm_div, norm_neg, norm_pow, ht, h2, sq_abs]
    rw [this]
    have hexp : 1 ≤ Real.exp |t| := Real.one_le_exp (abs_nonneg _)
    nlinarith [sq_nonneg t, hexp]
  · by_cases hlarge : 1 ≤ |x|
    · have hq : quadTrunc x = 1 := by
        have : (1 : ℝ) ≤ x ^ 2 := by
          rw [← sq_abs]
          exact one_le_pow₀ hlarge
        exact min_eq_left this
      rw [levyKernel, ite_eq_right hx0, contIntegrand,
        contTrunc_eq_zero_of_one_le_abs hlarge, hq]
      have hnorm : ‖exp (I * ↑t * ↑x)‖ = 1 := by
        rw [norm_exp]
        simp [mul_assoc]
      have : ‖exp (I * ↑t * ↑x) - 1‖ ≤ 2 := by
        calc
          ‖exp (I * ↑t * ↑x) - 1‖ ≤ ‖exp (I * ↑t * ↑x)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [hnorm, norm_one]; norm_num
      have h2 : (2 : ℝ) ≤ 8 * (t ^ 2 + 1) * Real.exp |t| + 2 := by
        have : 0 ≤ 8 * (t ^ 2 + 1) * Real.exp |t| := by positivity
        linarith
      simpa using this.trans h2
    · have hxle : |x| ≤ 1 := le_of_not_ge hlarge
      have hq : quadTrunc x = x ^ 2 := quadTrunc_eq_sq_of_abs_le_one hxle
      have hxsq : x ≠ 0 := hx0
      rw [levyKernel, ite_eq_right hx0, hq]
      have hy : ‖I * ↑t * ↑x‖ = |t| * |x| := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
      by_cases hhalf : |x| ≤ 1 / 2
      · rw [contIntegrand, contTrunc_eq_id_of_abs_le_half hhalf]
        have hle := norm_exp_sub_one_sub_le (I * ↑t * ↑x)
        have hdiv : ‖(exp (I * ↑t * ↑x) - 1 - I * ↑t * ↑x) / ↑(x ^ 2)‖ =
            ‖exp (I * ↑t * ↑x) - 1 - I * ↑t * ↑x‖ / x ^ 2 := by
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
        rw [hdiv]
        have : ‖exp (I * ↑t * ↑x) - 1 - I * ↑t * ↑x‖ / x ^ 2 ≤
            t ^ 2 * Real.exp |t| := by
          have hpos : 0 < x ^ 2 := sq_pos_of_ne_zero hxsq
          rw [div_le_iff₀ hpos]
          have habs : |t| * |x| ≤ |t| := by nlinarith [abs_nonneg t, hhalf]
          have hexp := Real.exp_le_exp.mpr habs
          have hsq : (|t| * |x|) ^ 2 = t ^ 2 * x ^ 2 := by
            rw [mul_pow, sq_abs, sq_abs]
          calc
            ‖exp (I * ↑t * ↑x) - 1 - I * ↑t * ↑x‖ ≤ ‖I * ↑t * ↑x‖ ^ 2 *
                Real.exp ‖I * ↑t * ↑x‖ := hle
            _ = (|t| * |x|) ^ 2 * Real.exp (|t| * |x|) := by rw [hy]
            _ = t ^ 2 * x ^ 2 * Real.exp (|t| * |x|) := by rw [hsq]
            _ ≤ t ^ 2 * x ^ 2 * Real.exp |t| := by
              gcongr
            _ = t ^ 2 * Real.exp |t| * x ^ 2 := by ring
        exact this.trans (le_trans (by
          have : t ^ 2 * Real.exp |t| ≤ 8 * (t ^ 2 + 1) * Real.exp |t| + 2 := by
            have hexp : 0 ≤ Real.exp |t| := Real.exp_nonneg _
            nlinarith
          exact this) le_rfl)
      · have hmid : 1 / 2 ≤ |x| := le_of_not_ge hhalf
        have hdiff : ‖I * ↑t * ↑x - I * ↑t * ↑(contTrunc x)‖ ≤ |t| := by
          have : I * ↑t * ↑x - I * ↑t * ↑(contTrunc x) =
              I * ↑t * ↑(x - contTrunc x) := by
            push_cast
            ring
          rw [this, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
          have : |x - contTrunc x| ≤ 1 := abs_sub_contTrunc_le_of_abs_le_one hxle
          nlinarith [abs_nonneg t]
        have hsplit : ‖contIntegrand t x‖ ≤
            ‖exp (I * ↑t * ↑x) - 1 - I * ↑t * ↑x‖ + |t| := by
          unfold contIntegrand
          have : exp (I * ↑t * ↑x) - 1 - I * ↑t * ↑(contTrunc x) =
              (exp (I * ↑t * ↑x) - 1 - I * ↑t * ↑x) +
                (I * ↑t * ↑x - I * ↑t * ↑(contTrunc x)) := by ring
          rw [this]
          exact (norm_add_le _ _).trans (add_le_add_right hdiff _)
        have hle := norm_exp_sub_one_sub_le (I * ↑t * ↑x)
        have hnum : ‖contIntegrand t x‖ ≤ t ^ 2 * x ^ 2 * Real.exp |t| + |t| := by
          calc
            ‖contIntegrand t x‖ ≤ ‖I * ↑t * ↑x‖ ^ 2 * Real.exp ‖I * ↑t * ↑x‖ + |t| :=
              hsplit.trans (add_le_add_left hle _)
            _ = (|t| * |x|) ^ 2 * Real.exp (|t| * |x|) + |t| := by rw [hy]
            _ = t ^ 2 * x ^ 2 * Real.exp (|t| * |x|) + |t| := by
              rw [mul_pow, sq_abs, sq_abs]
            _ ≤ t ^ 2 * x ^ 2 * Real.exp |t| + |t| := by
              have habs : |t| * |x| ≤ |t| := by nlinarith [abs_nonneg t, hxle]
              have hexp := Real.exp_le_exp.mpr habs
              gcongr
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
        have hpos : 0 < x ^ 2 := sq_pos_of_ne_zero hxsq
        rw [div_le_iff₀ hpos]
        calc
          ‖contIntegrand t x‖ ≤ t ^ 2 * x ^ 2 * Real.exp |t| + |t| := hnum
          _ ≤ (t ^ 2 * Real.exp |t| + 4 * |t|) * x ^ 2 := by
            have hden : (1 / 4 : ℝ) ≤ x ^ 2 := by
              rw [← sq_abs]
              nlinarith
            have : |t| ≤ 4 * |t| * x ^ 2 := by
              have : (1 : ℝ) ≤ 4 * x ^ 2 := by nlinarith
              nlinarith [abs_nonneg t]
            nlinarith [sq_nonneg t, Real.exp_nonneg |t|]
          _ ≤ (8 * (t ^ 2 + 1) * Real.exp |t| + 2) * x ^ 2 := by
            gcongr

/-- A frequency-dependent bound for the Lévy kernel. -/
def levyKernelBound (t : ℝ) : ℝ :=
  8 * (t ^ 2 + 1) * Real.exp |t| + 2

/-- The Lévy kernel as a bounded continuous function. -/
def levyKernelBdd (t : ℝ) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (levyKernel t) (continuous_levyKernel t)
    (levyKernelBound t) (norm_levyKernel_le t)

/-- The continuous compensator equals the kernel times the quadratic weight. -/
lemma contIntegrand_eq_levyKernel_mul (t x : ℝ) :
    contIntegrand t x = levyKernel t x * ↑(quadTrunc x) := by
  by_cases hx : x = 0
  · simp [contIntegrand, levyKernel, quadTrunc, contTrunc, hx, exp_zero]
  · have hq : (quadTrunc x : ℂ) ≠ 0 := by
      exact_mod_cast quadTrunc_eq_zero_iff.not.mpr hx
    rw [levyKernel, ite_eq_right hx, div_mul_cancel₀ _ hq]

/-- The quadratic weight is continuous. -/
@[fun_prop]
lemma continuous_quadTrunc : Continuous quadTrunc := by
  unfold quadTrunc
  fun_prop

/-- The frequency exponential is integrable on a finite measure. -/
lemma integrable_exp_frequency {ν : Measure ℝ} [IsFiniteMeasure ν] (t : ℝ) :
    Integrable (fun x : ℝ => exp (I * ↑t * ↑x)) ν := by
  refine (integrable_const (1 : ℝ)).mono'
    (by fun_prop : Continuous fun x : ℝ => exp (I * ↑t * ↑x)).aestronglyMeasurable ?_
  refine ae_of_all _ fun x => ?_
  have : ‖exp (I * ↑t * ↑x)‖ = 1 := by
    rw [norm_exp]
    simp [mul_assoc]
  exact le_of_eq this

/-- The continuous cutoff is integrable on a finite measure. -/
lemma integrable_contTrunc {ν : Measure ℝ} [IsFiniteMeasure ν] :
    Integrable contTrunc ν := by
  refine (integrable_const (1 : ℝ)).mono' continuous_contTrunc.aestronglyMeasurable ?_
  refine ae_of_all _ fun x => ?_
  simpa [Real.norm_eq_abs] using abs_contTrunc_le_one x

/-- `(I t)` times the continuous cutoff is integrable on a finite measure. -/
lemma integrable_contCompensator {ν : Measure ℝ} [IsFiniteMeasure ν] (t : ℝ) :
    Integrable (fun x : ℝ => (I * ↑t) * ↑(contTrunc x)) ν := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (I * ↑t) * ↑(contTrunc x)) ν := by
    fun_prop
  refine (integrable_const |t|).mono' hmeas ?_
  refine ae_of_all _ fun x => ?_
  rw [norm_mul, norm_mul, norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]
  have habs : 0 ≤ |t| := abs_nonneg t
  nlinarith [habs, abs_contTrunc_le_one x]

/-- The continuous compensator is integrable on a finite measure. -/
lemma integrable_contIntegrand {ν : Measure ℝ} [IsFiniteMeasure ν] (t : ℝ) :
    Integrable (contIntegrand t) ν := by
  have hsub : contIntegrand t = fun x : ℝ =>
      (exp (I * ↑t * ↑x) - 1) - (I * ↑t) * ↑(contTrunc x) := by
    ext x
    simp [contIntegrand]
  rw [hsub]
  exact (integrable_exp_frequency t).sub (integrable_const _) |>.sub (integrable_contCompensator t)

/-- Integrating the continuous compensator recovers the characteristic function. -/
lemma integral_contIntegrand {ν : Measure ℝ} [IsProbabilityMeasure ν] (t : ℝ) :
    ∫ x, contIntegrand t x ∂ν =
      charFun ν t - 1 - I * ↑t * ↑(∫ x, contTrunc x ∂ν) := by
  have hchar : charFun ν t = ∫ x, exp (I * ↑t * ↑x) ∂ν := by
    rw [charFun_apply_real]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    push_cast
    ring_nf
  let f : ℝ → ℂ := fun x => exp (I * ↑t * ↑x) - 1
  let g : ℝ → ℂ := fun x => (I * ↑t) * ↑(contTrunc x)
  have heq : contIntegrand t = fun x => f x - g x := by
    ext x
    simp [contIntegrand, f, g]
  have hone : ∫ _ : ℝ, (1 : ℂ) ∂ν = 1 := by simp [integral_const, probReal_univ]
  have hf : Integrable f ν := (integrable_exp_frequency t).sub (integrable_const (1 : ℂ))
  rw [heq, integral_sub hf (integrable_contCompensator t), integral_sub
      (integrable_exp_frequency t) (integrable_const (1 : ℂ)),
    integral_const_mul, integral_complex_ofReal, hone, hchar]

/-- `n` copies of a law, weighted by the quadratic truncation. -/
def quadWeighted (n : ℕ) (ν : Measure ℝ) : Measure ℝ :=
  (n : ℝ≥0∞) • ν.withDensity (fun x => ENNReal.ofReal (quadTrunc x))

/-- Quadratic weighting preserves finiteness. -/
lemma isFiniteMeasure_quadWeighted {ν : Measure ℝ} [IsFiniteMeasure ν] (n : ℕ) :
    IsFiniteMeasure (quadWeighted n ν) := by
  rw [quadWeighted]
  have hden :
      (ν.withDensity fun x => ENNReal.ofReal (quadTrunc x)) Set.univ < ∞ := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have hle : ∀ x, ENNReal.ofReal (quadTrunc x) ≤ 1 := fun x =>
      (ENNReal.ofReal_le_ofReal (quadTrunc_le_one x)).trans_eq (by simp)
    exact (lintegral_mono hle).trans_lt (by simp [measure_lt_top])
  exact ⟨by
    rw [Measure.smul_apply]
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top n) hden⟩

/-- The real drift carried by the continuous cutoff. -/
def contDrift (n : ℕ) (ν : Measure ℝ) : ℝ :=
  (n : ℝ) * ∫ x, contTrunc x ∂ν

/-- The kernel integral against the weighted law is `n` times the compensator. -/
lemma integral_levyKernel_quadWeighted {ν : Measure ℝ} [IsProbabilityMeasure ν] (n : ℕ)
    (t : ℝ) :
    ∫ x, levyKernel t x ∂quadWeighted n ν =
      (n : ℂ) * ∫ x, contIntegrand t x ∂ν := by
  have hf : Measurable fun x => ENNReal.ofReal (quadTrunc x) := by fun_prop
  have hfin : ∀ᵐ x ∂ν, ENNReal.ofReal (quadTrunc x) < ∞ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  rw [quadWeighted, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hf hfin]
  have hpoint : ∀ x, (ENNReal.ofReal (quadTrunc x)).toReal • levyKernel t x =
      contIntegrand t x := by
    intro x
    rw [ENNReal.toReal_ofReal (quadTrunc_nonneg x), RCLike.real_smul_eq_coe_mul, mul_comm]
    exact (contIntegrand_eq_levyKernel_mul t x).symm
  simp_rw [hpoint]
  have hto : (n : ℝ≥0∞).toReal = (n : ℝ) := by
    simp [ENNReal.toReal, ENNReal.toNNReal_natCast]
  rw [hto, RCLike.real_smul_eq_coe_mul]
  exact congrArg (fun w : ℂ => w * ∫ x, contIntegrand t x ∂ν) (Complex.ofReal_natCast n)

/-- `n` times one minus a root characteristic function splits into kernel and drift. -/
lemma nat_mul_charFun_sub_one_eq {ν : Measure ℝ} [IsProbabilityMeasure ν] (n : ℕ) (t : ℝ) :
    (n : ℂ) * (charFun ν t - 1) =
      ∫ x, levyKernel t x ∂quadWeighted n ν + I * ↑t * ↑(contDrift n ν) := by
  rw [integral_levyKernel_quadWeighted, integral_contIntegrand, contDrift]
  push_cast
  ring_nf

/-- Scalar multiplication by `n` sends the exponential increment to the exponent. -/
lemma tendsto_nat_mul_exp_div_sub_one (z : ℂ) :
    Tendsto (fun n : ℕ => (n : ℂ) * (exp (z / (n : ℂ)) - 1)) atTop (𝓝 z) := by
  by_cases hz : z = 0
  · simp [hz]
  · have hu : Tendsto (fun n : ℕ => z / (n : ℂ)) atTop (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_div_atTop_nhds_zero_nat z, ?_⟩
      filter_upwards [eventually_ne_atTop 0] with n hn
      exact div_ne_zero hz (by exact_mod_cast hn)
    have hcomp := ((hasDerivAt_exp (0 : ℂ)).tendsto_slope_zero).comp hu
    simp only [Function.comp_def, zero_add, exp_zero, smul_eq_mul] at hcomp
    have hfun : ∀ n : ℕ, z * ((z / (n : ℂ))⁻¹ * (exp (z / (n : ℂ)) - 1)) =
        (n : ℂ) * (exp (z / (n : ℂ)) - 1) := by
      intro n
      by_cases hn : n = 0
      · simp [hn, div_zero, inv_zero, exp_zero]
      · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
        field_simp [hz, hnC]
    have hmul : Tendsto (fun n : ℕ => (n : ℂ) * (exp (z / (n : ℂ)) - 1)) atTop
        (𝓝 (z * 1)) :=
      (hcomp.const_mul z).congr' (Eventually.of_forall hfun)
    simpa [mul_one] using hmul

/-- The exponential increment of order `n` is controlled by the exponent. -/
lemma norm_nat_mul_exp_div_sub_one_le {n : ℕ} (hn : 0 < n) (z : ℂ) :
    ‖(n : ℂ) * (exp (z / (n : ℂ)) - 1)‖ ≤ ‖z‖ * (1 + ‖z‖ * Real.exp ‖z‖) := by
  set y : ℂ := z / (n : ℂ)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hy : ‖y‖ = ‖z‖ / n := by
    rw [norm_div, Complex.norm_natCast]
  have hy_le : ‖y‖ ≤ ‖z‖ := by
    rw [hy]
    exact div_le_self (norm_nonneg _) hnR
  have hy_exp : Real.exp ‖y‖ ≤ Real.exp ‖z‖ := Real.exp_le_exp.mpr hy_le
  have hrem := norm_exp_sub_one_sub_le y
  have hsplit : ‖exp y - 1‖ ≤ ‖y‖ ^ 2 * Real.exp ‖y‖ + ‖y‖ := by
    calc
      ‖exp y - 1‖ ≤ ‖exp y - 1 - y‖ + ‖y‖ := by
        have hsum : exp y - 1 = (exp y - 1 - y) + y :=
          (sub_add_cancel (exp y - 1) y).symm
        nth_rw 1 [hsum]
        exact norm_add_le (exp y - 1 - y) y
      _ ≤ ‖y‖ ^ 2 * Real.exp ‖y‖ + ‖y‖ := add_le_add hrem le_rfl
  have hnmul : ‖(n : ℂ) * (exp y - 1)‖ = (n : ℝ) * ‖exp y - 1‖ := by
    rw [norm_mul, Complex.norm_natCast]
  rw [hnmul]
  have hscale : (n : ℝ) * (‖y‖ ^ 2 * Real.exp ‖y‖ + ‖y‖) =
      ‖z‖ ^ 2 / n * Real.exp ‖y‖ + ‖z‖ := by
    rw [hy]
    field_simp [hn0]
  calc
    (n : ℝ) * ‖exp y - 1‖ ≤ (n : ℝ) * (‖y‖ ^ 2 * Real.exp ‖y‖ + ‖y‖) := by
      gcongr
    _ = ‖z‖ ^ 2 / n * Real.exp ‖y‖ + ‖z‖ := hscale
    _ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ + ‖z‖ := by
      have hdiv : ‖z‖ ^ 2 / n ≤ ‖z‖ ^ 2 := div_le_self (sq_nonneg _) hnR
      have hmul : ‖z‖ ^ 2 / n * Real.exp ‖y‖ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ :=
        mul_le_mul hdiv hy_exp (Real.exp_nonneg _) (sq_nonneg _)
      linarith
    _ = ‖z‖ * (1 + ‖z‖ * Real.exp ‖z‖) := by ring

end CKMA
