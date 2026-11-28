/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.CDF
import TauCeti.Probability.Distributions.Gaussian.Cdf
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Mills' ratio and the Stein solution for half-line indicators

Write `Φ = cdf (gaussianReal 0 1)` and `φ = gaussianPDFReal 0 1`. For `z : ℝ` the Stein
equation for the indicator of `(-∞, z]` is `f' (w) - w f (w) = 1{w ≤ z} - Φ z`. Its bounded
solution is

`f_z (w) = (Φ (min w z) - Φ w Φ z) / φ w`.

This file proves Mills' inequality `x Φ(-x) ≤ φ x` for `x > 0` and the pointwise properties of
`f_z` used in Stein's method: `0 ≤ f_z ≤ 6`, `|w f_z (w)| ≤ 1`, `|steinDeriv z| ≤ 3`, the right
derivative `w f_z (w) + 1{w < z} - Φ z` at every point, the Lipschitz bound with constant `2`,
and a first-order Taylor bound in terms of `steinDeriv`. The constants are not optimal.

## Main definitions

* `CKMA.steinSolution`: the solution `f_z` of the Stein equation for `1{· ≤ z}`.
* `CKMA.steinDeriv`: the right-hand side `w f_z (w) + 1{w ≤ z} - Φ z`.

## Main results

* `CKMA.mul_cdf_neg_le_gaussianPDFReal`: Mills' inequality.
* `CKMA.abs_mul_steinSolution_le_one`, `CKMA.steinSolution_le`: boundedness of `f_z`.
* `CKMA.abs_steinDeriv_le`: boundedness of `steinDeriv z`.
* `CKMA.abs_steinSolution_sub_le`: `f_z` is `2`-Lipschitz.
* `CKMA.abs_steinDeriv_add_sub_le`, `CKMA.abs_steinSolution_add_sub_sub_le`: increments of
  `steinDeriv` and the first-order Taylor remainder of `f_z`.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- **Mills' inequality**: for `x > 0` the standard Gaussian upper tail `Φ (-x)` is at most
`φ x / x`. -/
theorem mul_cdf_neg_le_gaussianPDFReal {x : ℝ} (hx : 0 < x) :
    x * cdf (gaussianReal 0 1) (-x) ≤ gaussianPDFReal 0 1 x := by
  -- `h t = φ t / t - Φ (-t)` is antitone on `(0, ∞)` and tends to `0`.
  let h : ℝ → ℝ := fun t ↦ gaussianPDFReal 0 1 t / t - cdf (gaussianReal 0 1) (-t)
  have hderiv (t : ℝ) (ht : 0 < t) :
      HasDerivAt h (-(gaussianPDFReal 0 1 t / t ^ 2)) t := by
    have h1 := (TauCeti.Probability.hasDerivAt_gaussianPDFReal 0 1 t).div (hasDerivAt_id t)
      ht.ne'
    have h2 := (TauCeti.Probability.hasDerivAt_cdf_gaussianReal 0 one_ne_zero (-t)).comp t
      (hasDerivAt_neg t)
    convert h1.sub h2 using 1
    · rfl
    rw [TauCeti.Probability.gaussianPDFReal_zero_neg]
    simp only [id, NNReal.coe_one, sub_zero, div_one]
    field_simp
    ring
  have hanti : AntitoneOn h (Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_
    · exact fun t ht ↦ (hderiv t ht).continuousAt.continuousWithinAt
    · rw [interior_Ioi]
      exact fun t ht ↦ (hderiv t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]
      intro t ht
      rw [(hderiv t ht).deriv, neg_nonpos]
      exact div_nonneg (gaussianPDFReal_nonneg 0 1 t) (sq_nonneg t)
  have hlim : Tendsto h atTop (𝓝 0) := by
    have hφ : Tendsto (gaussianPDFReal 0 1) atTop (𝓝 0) := by
      have := (TauCeti.Probability.tendsto_mul_gaussianPDFReal_zero_one_cocompact.mono_left
        (atTop_le_cocompact)).mul tendsto_inv_atTop_zero
      rw [zero_mul] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      field_simp
    have hΦ : Tendsto (fun t ↦ cdf (gaussianReal 0 1) (-t)) atTop (𝓝 0) :=
      (tendsto_cdf_atBot _).comp tendsto_neg_atTop_atBot
    have := (hφ.mul tendsto_inv_atTop_zero).sub hΦ
    rw [zero_mul, sub_zero] at this
    exact this.congr fun t ↦ by simp only [h, div_eq_mul_inv]
  have h0 : 0 ≤ h x := by
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop x] with t ht
    exact hanti hx (hx.trans_le ht) ht
  simp only [h] at h0
  rw [sub_nonneg, le_div_iff₀ hx] at h0
  linarith

/-- The bounded solution `f_z (w) = (Φ (min w z) - Φ w Φ z) / φ w` of the Stein equation
`f' (w) - w f (w) = 1{w ≤ z} - Φ z`, where `Φ` and `φ` are the standard Gaussian distribution
function and density. -/
@[expose] def steinSolution (z w : ℝ) : ℝ :=
  (cdf (gaussianReal 0 1) (min w z) - cdf (gaussianReal 0 1) w * cdf (gaussianReal 0 1) z) /
    gaussianPDFReal 0 1 w

/-- Defining formula of `steinSolution`. -/
lemma steinSolution_def (z w : ℝ) : steinSolution z w =
    (cdf (gaussianReal 0 1) (min w z) - cdf (gaussianReal 0 1) w * cdf (gaussianReal 0 1) z) /
      gaussianPDFReal 0 1 w :=
  rfl

/-- The right-hand side `w f_z (w) + 1{w ≤ z} - Φ z` of the Stein equation. It is the derivative
of `steinSolution z` at every `w ≠ z`. -/
@[expose] def steinDeriv (z w : ℝ) : ℝ :=
  w * steinSolution z w + (if w ≤ z then 1 else 0) - cdf (gaussianReal 0 1) z

/-- The defining formula of `steinDeriv`. -/
theorem steinDeriv_def (z w : ℝ) :
    steinDeriv z w = w * steinSolution z w + (if w ≤ z then 1 else 0) -
      cdf (gaussianReal 0 1) z := rfl

private lemma gaussianPDFReal_zero_one_pos (w : ℝ) : 0 < gaussianPDFReal 0 1 w :=
  gaussianPDFReal_pos 0 1 w one_ne_zero

private lemma numerator_nonneg (z w : ℝ) :
    0 ≤ cdf (gaussianReal 0 1) (min w z) -
      cdf (gaussianReal 0 1) w * cdf (gaussianReal 0 1) z := by
  rw [(monotone_cdf (gaussianReal 0 1)).map_min, sub_nonneg]
  have h0w := cdf_nonneg (gaussianReal 0 1) w
  have h1w := cdf_le_one (gaussianReal 0 1) w
  have h0z := cdf_nonneg (gaussianReal 0 1) z
  have h1z := cdf_le_one (gaussianReal 0 1) z
  rcases le_total (cdf (gaussianReal 0 1) w) (cdf (gaussianReal 0 1) z) with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

/-- `f_z` is nonnegative. -/
theorem steinSolution_nonneg (z w : ℝ) : 0 ≤ steinSolution z w :=
  div_nonneg (numerator_nonneg z w) (gaussianPDFReal_zero_one_pos w).le

/-- `|w f_z (w)| ≤ 1`, a consequence of Mills' inequality. -/
theorem abs_mul_steinSolution_le_one (z w : ℝ) : |w * steinSolution z w| ≤ 1 := by
  set Φ := cdf (gaussianReal 0 1)
  have hφ := gaussianPDFReal_zero_one_pos w
  have hmono := monotone_cdf (gaussianReal 0 1)
  have h0w := cdf_nonneg (gaussianReal 0 1) w
  have h1z := cdf_le_one (gaussianReal 0 1) z
  have h0z := cdf_nonneg (gaussianReal 0 1) z
  have h1w := cdf_le_one (gaussianReal 0 1) w
  rw [abs_mul, steinSolution, abs_of_nonneg (div_nonneg (numerator_nonneg z w) hφ.le),
    mul_div_assoc', div_le_one hφ]
  rcases lt_trichotomy w 0 with hw | rfl | hw
  · -- the numerator is at most `Φ w = Φ (-|w|)`
    have hN : Φ (min w z) - Φ w * Φ z ≤ Φ (-(-w)) := by
      rw [neg_neg]
      nlinarith [hmono (min_le_left w z)]
    have hM := mul_cdf_neg_le_gaussianPDFReal (neg_pos.2 hw)
    rw [TauCeti.Probability.gaussianPDFReal_zero_neg] at hM
    rw [abs_of_neg hw]
    nlinarith
  · simp
  · -- the numerator is at most `Φ z (1 - Φ w) ≤ Φ (-w)`
    have hN : Φ (min w z) - Φ w * Φ z ≤ Φ (-w) := by
      rw [TauCeti.Probability.cdf_gaussianReal_zero_one_neg]
      nlinarith [hmono (min_le_right w z)]
    have hM := mul_cdf_neg_le_gaussianPDFReal hw
    rw [abs_of_pos hw]
    nlinarith

private lemma exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

/-- `f_z` is bounded by `6`. -/
theorem steinSolution_le (z w : ℝ) : steinSolution z w ≤ 6 := by
  rcases le_or_gt |w| 1 with hw | hw
  · have hφ := gaussianPDFReal_zero_one_pos w
    have hN : cdf (gaussianReal 0 1) (min w z) -
        cdf (gaussianReal 0 1) w * cdf (gaussianReal 0 1) z ≤ 1 := by
      nlinarith [cdf_le_one (gaussianReal 0 1) (min w z), cdf_nonneg (gaussianReal 0 1) w,
        cdf_nonneg (gaussianReal 0 1) z]
    have hlow : 1 / 6 ≤ gaussianPDFReal 0 1 w := by
      rw [TauCeti.Probability.gaussianPDFReal_zero_one]
      have hsq : Real.sqrt (2 * Real.pi) ≤ 3 := by
        rw [Real.sqrt_le_left (by norm_num)]
        nlinarith [Real.pi_le_four]
      have hexp : Real.exp (-(1 / 2)) ≤ Real.exp (-(w ^ 2 / 2)) := by
        gcongr
        nlinarith [abs_le.1 hw, sq_abs w, abs_nonneg w]
      have hexp' : 1 / 2 < Real.exp (-(1 / 2)) := by
        rw [Real.exp_neg, lt_inv_comm₀ (by norm_num) (Real.exp_pos _)]
        norm_num
        linarith [exp_half_lt_two]
      have hpos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
      rw [inv_mul_eq_div, le_div_iff₀ hpos]
      nlinarith
    calc steinSolution z w ≤ 1 / gaussianPDFReal 0 1 w :=
          div_le_div_of_nonneg_right hN hφ.le
      _ ≤ 1 / (1 / 6) := by gcongr
      _ = 6 := by norm_num
  · have h := abs_mul_steinSolution_le_one z w
    rw [abs_mul, abs_of_nonneg (steinSolution_nonneg z w)] at h
    nlinarith [steinSolution_nonneg z w]

/-- `|f_z| ≤ 6`. -/
theorem abs_steinSolution_le (z w : ℝ) : |steinSolution z w| ≤ 6 := by
  rw [abs_of_nonneg (steinSolution_nonneg z w)]
  exact steinSolution_le z w

/-- `f_z` is continuous. -/
theorem continuous_steinSolution (z : ℝ) : Continuous (steinSolution z) := by
  have hΦ : Continuous (cdf (gaussianReal 0 1)) := continuous_iff_continuousAt.2 fun x ↦
    (TauCeti.Probability.hasDerivAt_cdf_gaussianReal 0 one_ne_zero x).continuousAt
  have hφ : Continuous (gaussianPDFReal 0 1) := continuous_iff_continuousAt.2 fun x ↦
    (TauCeti.Probability.hasDerivAt_gaussianPDFReal 0 1 x).continuousAt
  exact ((hΦ.comp (continuous_id.min continuous_const)).sub (hΦ.mul continuous_const)).div hφ
    fun w ↦ (gaussianPDFReal_zero_one_pos w).ne'

/-- `f_z` is measurable. -/
theorem measurable_steinSolution (z : ℝ) : Measurable (steinSolution z) :=
  (continuous_steinSolution z).measurable

/-- `steinDeriv z` is measurable. -/
theorem measurable_steinDeriv (z : ℝ) : Measurable (steinDeriv z) := by
  unfold steinDeriv
  exact ((measurable_id.mul (measurable_steinSolution z)).add
    (Measurable.ite measurableSet_Iic measurable_const measurable_const)).sub measurable_const

/-- `|steinDeriv z w| ≤ 3`. -/
theorem abs_steinDeriv_le (z w : ℝ) : |steinDeriv z w| ≤ 3 := by
  have h1 := abs_mul_steinSolution_le_one z w
  have h2 := cdf_nonneg (gaussianReal 0 1) z
  have h3 := cdf_le_one (gaussianReal 0 1) z
  rw [steinDeriv_def]
  rw [abs_le] at h1 ⊢
  constructor <;> split_ifs <;> linarith

/-- The right derivative of `f_z` at `w` is `w f_z (w) + 1{w < z} - Φ z`. -/
theorem hasDerivWithinAt_steinSolution (z w : ℝ) :
    HasDerivWithinAt (steinSolution z)
      (w * steinSolution z w + (if w < z then 1 else 0) - cdf (gaussianReal 0 1) z)
      (Ici w) w := by
  set Φ := cdf (gaussianReal 0 1)
  set φ := gaussianPDFReal 0 1
  have hΦ (x : ℝ) : HasDerivAt Φ (φ x) x :=
    TauCeti.Probability.hasDerivAt_cdf_gaussianReal 0 one_ne_zero x
  have hφ : HasDerivAt φ (-w * φ w) w := by
    simpa using TauCeti.Probability.hasDerivAt_gaussianPDFReal 0 1 w
  have hmin : HasDerivWithinAt (fun s ↦ Φ (min s z)) (if w < z then φ w else 0) (Ici w) w := by
    split_ifs with h
    · refine ((hΦ w).hasDerivWithinAt).congr_of_eventuallyEq ?_ (by rw [min_eq_left h.le])
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds h)] with s hs
      rw [min_eq_left (le_of_lt hs)]
    · refine (hasDerivWithinAt_const w (Ici w) (Φ z)).congr (fun s hs ↦ ?_) ?_
      · rw [min_eq_right ((not_lt.1 h).trans hs)]
      · rw [min_eq_right (not_lt.1 h)]
  have hpos := gaussianPDFReal_zero_one_pos w
  have hd := (hmin.sub ((hΦ w).hasDerivWithinAt.mul_const (Φ z))).div hφ.hasDerivWithinAt
    hpos.ne'
  convert hd using 1
  · rfl
  unfold steinSolution
  simp only [Pi.sub_apply, Φ, φ]
  split_ifs <;> field_simp <;> ring

/-- A function with right derivatives bounded by `C` on a segment is `C`-Lipschitz there. -/
private lemma abs_sub_le_of_hasDerivWithinAt {g g' : ℝ → ℝ} {C : ℝ} (hc : Continuous g)
    (hd : ∀ s, HasDerivWithinAt g (g' s) (Ici s) s) {u v : ℝ}
    (hb : ∀ s ∈ uIcc u v, |g' s| ≤ C) : |g v - g u| ≤ C * |v - u| := by
  rcases le_total u v with huv | hvu
  · have := norm_image_sub_le_of_norm_deriv_right_le_segment hc.continuousOn
      (fun s _ ↦ hd s) (fun s hs ↦ hb s (Icc_subset_uIcc (Ico_subset_Icc_self hs))) v
      ⟨huv, le_rfl⟩
    rwa [abs_of_nonneg (sub_nonneg.2 huv)]
  · have := norm_image_sub_le_of_norm_deriv_right_le_segment hc.continuousOn
      (fun s _ ↦ hd s) (fun s hs ↦ hb s (Icc_subset_uIcc' (Ico_subset_Icc_self hs))) u
      ⟨hvu, le_rfl⟩
    rw [abs_sub_comm, abs_sub_comm v u, abs_of_nonneg (sub_nonneg.2 hvu)]
    exact this

private lemma abs_rightDeriv_le (z s : ℝ) :
    |s * steinSolution z s + (if s < z then 1 else 0) - cdf (gaussianReal 0 1) z| ≤ 2 := by
  have h1 := abs_mul_steinSolution_le_one z s
  have h2 := cdf_nonneg (gaussianReal 0 1) z
  have h3 := cdf_le_one (gaussianReal 0 1) z
  rw [abs_le] at h1 ⊢
  constructor <;> split_ifs <;> linarith

/-- `f_z` is `2`-Lipschitz. -/
theorem abs_steinSolution_sub_le (z u v : ℝ) :
    |steinSolution z v - steinSolution z u| ≤ 2 * |v - u| :=
  abs_sub_le_of_hasDerivWithinAt (continuous_steinSolution z)
    (hasDerivWithinAt_steinSolution z) fun s _ ↦ abs_rightDeriv_le z s

private lemma abs_ite_lt_sub_ite_le (z w t : ℝ) :
    |(if w + t < z then (1 : ℝ) else 0) - (if w ≤ z then 1 else 0)| ≤
      if |w - z| ≤ |t| then 1 else 0 := by
  split_ifs with h1 h2 h3 h3 h2 h3 h3 <;> norm_num
  all_goals
    first
    | (exfalso; apply h3; rw [abs_le]; constructor <;>
        (rcases abs_cases t with ⟨ht, _⟩ | ⟨ht, _⟩ <;> rw [ht] <;> linarith))

private lemma abs_ite_le_sub_ite_le (z w t : ℝ) :
    |(if w + t ≤ z then (1 : ℝ) else 0) - (if w ≤ z then 1 else 0)| ≤
      if |w - z| ≤ |t| then 1 else 0 := by
  split_ifs with h1 h2 h3 h3 h2 h3 h3 <;> norm_num
  all_goals
    first
    | (exfalso; apply h3; rw [abs_le]; constructor <;>
        (rcases abs_cases t with ⟨ht, _⟩ | ⟨ht, _⟩ <;> rw [ht] <;> linarith))

private lemma abs_mul_steinSolution_add_sub_le (z w t : ℝ) :
    |(w + t) * steinSolution z (w + t) - w * steinSolution z w| ≤ (2 * |w| + 6) * |t| := by
  have hL := abs_steinSolution_sub_le z w (w + t)
  rw [add_sub_cancel_left] at hL
  have hB := abs_steinSolution_le z (w + t)
  have : (w + t) * steinSolution z (w + t) - w * steinSolution z w =
      w * (steinSolution z (w + t) - steinSolution z w) + t * steinSolution z (w + t) := by
    ring
  rw [this]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  nlinarith [abs_nonneg w, abs_nonneg t]

/-- The increment of the right derivative of `f_z` from `w` to `w + t`, compared with
`steinDeriv z w`. -/
private lemma abs_rightDeriv_add_sub_steinDeriv_le (z w t : ℝ) :
    |((w + t) * steinSolution z (w + t) + (if w + t < z then 1 else 0) -
        cdf (gaussianReal 0 1) z) - steinDeriv z w| ≤
      (2 * |w| + 6) * |t| + if |w - z| ≤ |t| then 1 else 0 := by
  rw [steinDeriv]
  calc _ = |((w + t) * steinSolution z (w + t) - w * steinSolution z w) +
        ((if w + t < z then (1 : ℝ) else 0) - (if w ≤ z then 1 else 0))| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans
      (add_le_add (abs_mul_steinSolution_add_sub_le z w t) (abs_ite_lt_sub_ite_le z w t))

/-- Increments of `steinDeriv z`. -/
theorem abs_steinDeriv_add_sub_le (z w x : ℝ) :
    |steinDeriv z (w + x) - steinDeriv z w| ≤
      (2 * |w| + 6) * |x| + if |w - z| ≤ |x| then 1 else 0 := by
  rw [steinDeriv, steinDeriv]
  calc _ = |((w + x) * steinSolution z (w + x) - w * steinSolution z w) +
        ((if w + x ≤ z then (1 : ℝ) else 0) - (if w ≤ z then 1 else 0))| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans
      (add_le_add (abs_mul_steinSolution_add_sub_le z w x) (abs_ite_le_sub_ite_le z w x))

/-- First-order Taylor bound for `f_z`: the remainder of `f_z (w + x) - f_z (w)` after the
linear term `x · steinDeriv z w`. -/
theorem abs_steinSolution_add_sub_sub_le (z w x : ℝ) :
    |steinSolution z (w + x) - steinSolution z w - x * steinDeriv z w| ≤
      |x| * ((2 * |w| + 6) * |x| + if |w - z| ≤ |x| then 1 else 0) := by
  set C := (2 * |w| + 6) * |x| + if |w - z| ≤ |x| then 1 else 0
  have hd (s : ℝ) : HasDerivWithinAt (fun s ↦ steinSolution z s - s * steinDeriv z w)
      ((s * steinSolution z s + (if s < z then 1 else 0) - cdf (gaussianReal 0 1) z) -
        steinDeriv z w) (Ici s) s := by
    exact (hasDerivWithinAt_steinSolution z s).sub
      (hasDerivAt_mul_const (steinDeriv z w)).hasDerivWithinAt
  have hb : ∀ s ∈ uIcc w (w + x), |(s * steinSolution z s + (if s < z then 1 else 0) -
      cdf (gaussianReal 0 1) z) - steinDeriv z w| ≤ C := by
    intro s hs
    have hst : |s - w| ≤ |x| := by
      have := abs_sub_left_of_mem_uIcc hs
      rwa [add_sub_cancel_left] at this
    have h := abs_rightDeriv_add_sub_steinDeriv_le z w (s - w)
    rw [add_sub_cancel] at h
    refine h.trans (add_le_add (by gcongr) ?_)
    split_ifs with h1 h2 <;> first | exact absurd (h1.trans hst) h2 | norm_num
  have := abs_sub_le_of_hasDerivWithinAt
    ((continuous_steinSolution z).sub (continuous_id.mul continuous_const)) hd hb
  rw [add_sub_cancel_left, mul_comm C] at this
  calc _ = |(steinSolution z (w + x) - (w + x) * steinDeriv z w) -
        (steinSolution z w - w * steinDeriv z w)| := by ring_nf
    _ ≤ _ := this

end CKMA
