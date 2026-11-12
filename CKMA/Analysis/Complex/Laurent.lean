/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Laurent series on annuli

Contour integrals on positively oriented circles define Laurent coefficients.
Holomorphic functions on annuli have bilateral expansions, independent of the chosen
intermediate circle, and normal convergence on compact subsets.

Source: GAPS 40.25. Circle integration reuses Mathlib's Cauchy integral API.
Normal summability is the predicate from `CKMA.Analysis.Complex.Basic`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology Metric Complex
open scoped BigOperators Real Interval

/-- The open annulus with finite real inner and outer radii. -/
def complexAnnulus (a : ℂ) (r R : ℝ) : Set ℂ := {z | r < ‖z - a‖ ∧ ‖z - a‖ < R}

/-- Laurent coefficient computed on the positively oriented circle of radius `ρ`. -/
def laurentCoefficient (f : ℂ → ℂ) (a : ℂ) (ρ : ℝ) (n : ℤ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * ∮ z in C(a, ρ), (z - a) ^ (-n - 1) * f z

/-- The annulus is open. -/
lemma isOpen_complexAnnulus (a : ℂ) (r R : ℝ) : IsOpen (complexAnnulus a r R) := by
  have hnorm : Continuous fun z : ℂ ↦ ‖z - a‖ :=
    continuous_norm.comp (continuous_id.sub continuous_const)
  simpa only [complexAnnulus, Set.ofPred_and] using
    (isOpen_lt continuous_const hnorm).inter (isOpen_lt hnorm continuous_const)

/-- A circle strictly between the radii lies in the open annulus. -/
lemma sphere_subset_complexAnnulus {a : ℂ} {r R ρ : ℝ} (hρ : r < ρ) (hρR : ρ < R) :
    sphere a ρ ⊆ complexAnnulus a r R := by
  intro z hz
  have hnorm : ‖z - a‖ = ρ := by simpa [mem_sphere_iff_norm] using hz
  rw [complexAnnulus, Set.mem_ofPred_eq, hnorm]
  exact ⟨hρ, hρR⟩

/-- A closed concentric annulus with radii strictly inside `(r, R)` lies in the open annulus. -/
lemma closedBall_sdiff_ball_subset_complexAnnulus {a : ℂ} {r R s S : ℝ}
    (hs : r < s) (hS : S < R) :
    closedBall a S \ ball a s ⊆ complexAnnulus a r R := by
  intro w hw
  have hlower : s ≤ ‖w - a‖ := by
    rw [← not_lt, ← mem_ball_iff_norm]
    exact hw.2
  have hupper : ‖w - a‖ ≤ S := by
    rw [← mem_closedBall_iff_norm]
    exact hw.1
  exact ⟨lt_of_lt_of_le hs hlower, lt_of_le_of_lt hupper hS⟩

/-- The open concentric annulus between two radii strictly inside `(r, R)` lies in the annulus. -/
lemma ball_sdiff_closedBall_subset_complexAnnulus {a : ℂ} {r R s S : ℝ}
    (hs : r < s) (hS : S < R) :
    ball a S \ closedBall a s ⊆ complexAnnulus a r R := by
  intro w hw
  have hlower : s < ‖w - a‖ := by
    rw [← not_le, ← mem_closedBall_iff_norm]
    exact hw.2
  have hupper : ‖w - a‖ < S := by
    rw [← mem_ball_iff_norm]
    exact hw.1
  exact ⟨lt_trans hs hlower, lt_trans hupper hS⟩

/-- Points of an annulus with nonnegative inner radius are distinct from the center. -/
lemma ne_center_of_mem_complexAnnulus {a z : ℂ} {r R : ℝ} (hr : 0 ≤ r)
    (hz : z ∈ complexAnnulus a r R) : z ≠ a := by
  intro hza
  have hr0 : r < 0 := by simpa [hza, norm_zero] using hz.1
  exact lt_irrefl r (lt_of_lt_of_le hr0 hr)

/-- Integer powers of `(· - a)`, multiplied by a holomorphic function, stay holomorphic. -/
lemma differentiableOn_laurentIntegrand {f : ℂ → ℂ} {a : ℂ} {r R : ℝ} (n : ℤ)
    (hr : 0 ≤ r) (hf : DifferentiableOn ℂ f (complexAnnulus a r R)) :
    DifferentiableOn ℂ (fun z ↦ (z - a) ^ n * f z) (complexAnnulus a r R) := by
  intro z hz
  have hopen := isOpen_complexAnnulus a r R
  have hza : z - a ≠ 0 := sub_ne_zero.2 (ne_center_of_mem_complexAnnulus hr hz)
  have hf' : DifferentiableAt ℂ f z := hf.differentiableAt (hopen.mem_nhds hz)
  have hzpow : DifferentiableAt ℂ (fun w ↦ (w - a) ^ n) z :=
    (differentiableAt_id.sub_const a).zpow (Or.inl hza)
  exact (hzpow.mul hf').differentiableWithinAt

/-- A continuous function on a positive circle is bounded in norm. -/
lemma exists_norm_bound_on_sphere {f : ℂ → ℂ} {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : ContinuousOn f (sphere a ρ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ sphere a ρ, ‖f w‖ ≤ M := by
  obtain ⟨w, hw, hmax⟩ := (isCompact_sphere a ρ).exists_isMaxOn
      ⟨a + ρ, by simp [mem_sphere_iff_norm, norm_real, abs_of_pos hρ]⟩ hf.norm
  exact ⟨‖f w‖, norm_nonneg _, fun z hz ↦ hmax hz⟩

/-- Cauchy estimate: a Laurent coefficient is at most `M` times `ρ ^ (-n)`. -/
lemma norm_laurentCoefficient_le (f : ℂ → ℂ) (a : ℂ) {ρ : ℝ} (hρ : 0 < ρ) {M : ℝ}
    (hM : ∀ w ∈ sphere a ρ, ‖f w‖ ≤ M) (n : ℤ) :
    ‖laurentCoefficient f a ρ n‖ ≤ M * ρ ^ (-n) := by
  have hpow : ∀ w ∈ sphere a ρ, ‖(w - a) ^ (-n - 1) * f w‖ ≤ ρ ^ (-n - 1) * M := by
    intro w hw
    have hnorm : ‖w - a‖ = ρ := by simpa [mem_sphere_iff_norm] using hw
    rw [norm_mul, norm_zpow, hnorm]
    exact mul_le_mul_of_nonneg_left (hM w hw) (zpow_nonneg hρ.le _)
  have hsmul : laurentCoefficient f a ρ n =
      (2 * π * I)⁻¹ • ∮ w in C(a, ρ), (w - a) ^ (-n - 1) * f w := by
    simp [laurentCoefficient, smul_eq_mul]
  rw [hsmul]
  refine (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hρ.le hpow).trans ?_
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have hexp : (1 : ℤ) + (-n - 1) = -n := by ring
  have hpow1 : ρ * ρ ^ (-n - 1) = ρ ^ (-n) := by
    nth_rw 1 [← zpow_one ρ]
    rw [← zpow_add₀ hρ0, hexp]
  refine le_of_eq ?_
  rw [← mul_assoc, hpow1, mul_comm]

/-- Circle integrals of monomials: `2πI` at power `-1`, and zero otherwise. -/
lemma circleIntegral_sub_center_zpow (a : ℂ) {ρ : ℝ} (hρ : ρ ≠ 0) (m : ℤ) :
    (∮ z in C(a, ρ), (z - a) ^ m) = if m = -1 then 2 * π * I else 0 := by
  by_cases hm : m = -1
  · simpa [hm, zpow_neg_one] using circleIntegral.integral_sub_center_inv a hρ
  · simpa [hm] using circleIntegral.integral_sub_zpow_of_ne hm a a ρ

/-- On a circle avoiding `z`, the slope integrand splits into the Cauchy kernel and a constant. -/
lemma circleIntegral_slope_sub {f : ℂ → ℂ} {a z : ℂ} {radius : ℝ} (hpos : 0 < radius)
    (hne : ∀ w ∈ sphere a radius, w ≠ z) (hf : ContinuousOn f (sphere a radius)) :
    (∮ w in C(a, radius), (w - z)⁻¹ * (f w - f z)) =
      (∮ w in C(a, radius), (w - z)⁻¹ * f w) -
        f z * ∮ w in C(a, radius), (w - z)⁻¹ := by
  have hinv : ContinuousOn (fun w ↦ (w - z)⁻¹) (sphere a radius) :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun w hw ↦ sub_ne_zero.2 (hne w hw)
  have hEq : Set.EqOn (fun w ↦ (w - z)⁻¹ * (f w - f z))
      (fun w ↦ (w - z)⁻¹ * f w - f z * (w - z)⁻¹) (sphere a radius) := by
    intro w _
    ring
  rw [circleIntegral.integral_congr hpos.le hEq]
  have hkern : CircleIntegrable (fun w ↦ (w - z)⁻¹ * f w) a radius :=
    (hinv.mul hf).circleIntegrable hpos.le
  have hconst : CircleIntegrable (fun w ↦ f z * (w - z)⁻¹) a radius :=
    (continuousOn_const.mul hinv).circleIntegrable hpos.le
  rw [circleIntegral.integral_sub hkern hconst, circleIntegral.integral_const_mul]

/-- The kernel of an exterior point integrates to zero over the circle. -/
lemma circleIntegral_inv_of_outside {a z : ℂ} {radius : ℝ} (hpos : 0 ≤ radius)
    (hout : radius < ‖z - a‖) : (∮ w in C(a, radius), (w - z)⁻¹) = 0 := by
  refine circleIntegral_eq_zero_of_differentiable_on_off_countable hpos
      (s := (∅ : Set ℂ)) Set.countable_empty ?_ ?_
  · refine ((continuousOn_id.sub continuousOn_const).inv₀ fun w hw ↦ ?_)
    intro hzero
    have hwNorm : ‖w - a‖ ≤ radius := by
      rw [← mem_closedBall_iff_norm]
      exact hw
    have hwz : w - z = 0 := by simpa using hzero
    rw [sub_eq_zero.mp hwz] at hwNorm
    exact lt_irrefl _ (lt_of_le_of_lt hwNorm hout)
  · intro w hw
    have hwball : w ∈ ball a radius := by simpa [Set.sdiff_empty] using hw
    refine ((differentiableAt_id.sub_const z).inv ?_)
    intro hzero
    have hwNorm : ‖w - a‖ < radius := by
      rw [← mem_ball_iff_norm]
      exact hwball
    have hwz : w - z = 0 := by simpa using hzero
    rw [sub_eq_zero.mp hwz] at hwNorm
    exact lt_irrefl _ (lt_of_lt_of_le hwNorm hout.le)

/-- The kernel of an interior point integrates to `2πI`. -/
lemma circleIntegral_inv_of_inside {a z : ℂ} {radius : ℝ} (hin : ‖z - a‖ < radius) :
    (∮ w in C(a, radius), (w - z)⁻¹) = 2 * π * I :=
  circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_iff_norm.mpr hin)

/-- Two-circle Cauchy formula on a finite annulus. -/
lemma two_pi_I_mul_eq_circleIntegral_sub {f : ℂ → ℂ} {a z : ℂ} {r R innerRadius outerRadius : ℝ}
    (hr : 0 ≤ r) (hf : DifferentiableOn ℂ f (complexAnnulus a r R))
    (hinner : r < innerRadius) (hinside : innerRadius < ‖z - a‖)
    (houtside : ‖z - a‖ < outerRadius) (houter : outerRadius < R) :
    (2 * π * I) * f z =
      (∮ w in C(a, outerRadius), (w - z)⁻¹ * f w) -
        ∮ w in C(a, innerRadius), (w - z)⁻¹ * f w := by
  have hopen : IsOpen (complexAnnulus a r R) := isOpen_complexAnnulus a r R
  have hz : z ∈ complexAnnulus a r R :=
    ⟨lt_trans hinner hinside, lt_trans houtside houter⟩
  have hinner0 : 0 < innerRadius := lt_of_le_of_lt hr hinner
  have houter0 : 0 < outerRadius := lt_trans hinner0 (lt_trans hinside houtside)
  have hle : innerRadius ≤ outerRadius := (lt_trans hinside houtside).le
  have hφ : DifferentiableOn ℂ (dslope f z) (complexAnnulus a r R) := by
    intro w hw
    by_cases hwz : w = z
    · rw [hwz] at hw ⊢
      exact (((hf.analyticAt (hopen.mem_nhds hw)).dslope z).differentiableAt).differentiableWithinAt
    · exact ((differentiableAt_dslope_of_ne hwz).mpr
        (hf.differentiableAt (hopen.mem_nhds hw))).differentiableWithinAt
  have hclosed := closedBall_sdiff_ball_subset_complexAnnulus (a := a) hinner houter
  have hbetween := ball_sdiff_closedBall_subset_complexAnnulus (a := a) hinner houter
  have hintegrals := circleIntegral_eq_of_differentiable_on_annulus_off_countable
      (c := a) (r := innerRadius) (R := outerRadius) hinner0 hle (f := dslope f z)
      (s := (∅ : Set ℂ)) Set.countable_empty (hφ.continuousOn.mono hclosed)
      fun w hw ↦ hφ.differentiableAt (hopen.mem_nhds
        (hbetween (by simpa [Set.sdiff_empty] using hw)))
  have hne_outer : ∀ w ∈ sphere a outerRadius, w ≠ z := by
    intro w hw heq
    have : ‖z - a‖ = outerRadius := by simpa [heq, mem_sphere_iff_norm] using hw
    linarith [houtside]
  have hne_inner : ∀ w ∈ sphere a innerRadius, w ≠ z := by
    intro w hw heq
    have : ‖z - a‖ = innerRadius := by simpa [heq, mem_sphere_iff_norm] using hw
    linarith [hinside]
  have hEq_outer : Set.EqOn (dslope f z) (fun w ↦ (w - z)⁻¹ * (f w - f z))
      (sphere a outerRadius) := by
    intro w hw
    rw [dslope_of_ne _ (hne_outer w hw), slope, smul_eq_mul, vsub_eq_sub]
  have hEq_inner : Set.EqOn (dslope f z) (fun w ↦ (w - z)⁻¹ * (f w - f z))
      (sphere a innerRadius) := by
    intro w hw
    rw [dslope_of_ne _ (hne_inner w hw), slope, smul_eq_mul, vsub_eq_sub]
  have houter_quot := (circleIntegral.integral_congr houter0.le hEq_outer).trans
      (circleIntegral_slope_sub houter0 hne_outer
        (hf.continuousOn.mono (sphere_subset_complexAnnulus
          (lt_trans hinner (lt_trans hinside houtside)) houter)))
  have hinner_quot := (circleIntegral.integral_congr hinner0.le hEq_inner).trans
      (circleIntegral_slope_sub hinner0 hne_inner
        (hf.continuousOn.mono (sphere_subset_complexAnnulus hinner
          (lt_trans hinside (lt_trans houtside houter)))))
  have hinv_outer := circleIntegral_inv_of_inside (a := a) (z := z) houtside
  have hinv_inner := circleIntegral_inv_of_outside (a := a) (z := z) hinner0.le hinside
  have houter_split :
      (∮ w in C(a, outerRadius), dslope f z w) =
        (∮ w in C(a, outerRadius), (w - z)⁻¹ * f w) - f z * (2 * π * I) := by
    rw [houter_quot, hinv_outer]
  have hinner_split :
      (∮ w in C(a, innerRadius), dslope f z w) =
        ∮ w in C(a, innerRadius), (w - z)⁻¹ * f w := by
    rw [hinner_quot, hinv_inner, mul_zero, sub_zero]
  have hsame :
      (∮ w in C(a, outerRadius), (w - z)⁻¹ * f w) - f z * (2 * π * I) =
        ∮ w in C(a, innerRadius), (w - z)⁻¹ * f w := by
    rw [← houter_split, ← hinner_split, hintegrals]
  calc
    (2 * π * I) * f z = f z * (2 * π * I) := by ring
    _ = (∮ w in C(a, outerRadius), (w - z)⁻¹ * f w) -
          ∮ w in C(a, innerRadius), (w - z)⁻¹ * f w := by
      have hA := hsame.symm
      calc
        f z * (2 * π * I) =
            (∮ w in C(a, outerRadius), (w - z)⁻¹ * f w) -
              ((∮ w in C(a, outerRadius), (w - z)⁻¹ * f w) - f z * (2 * π * I)) := by ring
        _ = (∮ w in C(a, outerRadius), (w - z)⁻¹ * f w) -
              ∮ w in C(a, innerRadius), (w - z)⁻¹ * f w := by rw [hA]

/-- Geometric term for the Cauchy kernel outside the point. -/
lemma geometric_outer_term {a z w : ℂ} (n : ℕ) (hw : w ≠ a) :
    (z - a) ^ n * (w - a) ^ (-(n : ℤ) - 1) =
      ((z - a) / (w - a)) ^ n * (w - a)⁻¹ := by
  have hwa : w - a ≠ 0 := sub_ne_zero.2 hw
  have hexp : -(n : ℤ) - 1 = -(n : ℤ) + (-1) := by ring
  calc
    (z - a) ^ n * (w - a) ^ (-(n : ℤ) - 1)
        = (z - a) ^ n * ((w - a) ^ (-(n : ℤ)) * (w - a) ^ (-1 : ℤ)) := by
          rw [hexp, zpow_add₀ hwa]
    _ = (z - a) ^ n * (((w - a) ^ n)⁻¹ * (w - a)⁻¹) := by
          rw [zpow_neg, zpow_natCast, zpow_neg_one]
    _ = ((z - a) ^ n * ((w - a) ^ n)⁻¹) * (w - a)⁻¹ := by ring
    _ = ((z - a) / (w - a)) ^ n * (w - a)⁻¹ := by
          congr 1
          exact (div_pow (z - a) (w - a) n).symm

/-- Outside a point, the Cauchy kernel expands by the geometric series and integrates termwise. -/
lemma hasSum_circleIntegral_geometric_outer (f : ℂ → ℂ) (a z : ℂ) {outerRadius : ℝ}
    (hS : 0 < outerRadius) (hf : CircleIntegrable f a outerRadius) (hz : ‖z - a‖ < outerRadius) :
    HasSum (fun n : ℕ ↦ (z - a) ^ n *
        ∮ w in C(a, outerRadius), (w - a) ^ (-(n : ℤ) - 1) * f w)
      (∮ w in C(a, outerRadius), (w - z)⁻¹ * f w) := by
  have hsum := hasSum_two_pi_I_cauchyPowerSeries_integral (w := z - a) hf hz
  simp only [add_sub_cancel, smul_eq_mul] at hsum
  have hfun : (fun n : ℕ ↦ ∮ w in C(a, outerRadius),
      ((z - a) / (w - a)) ^ n * ((w - a)⁻¹ * f w)) =
      fun n : ℕ ↦ (z - a) ^ n *
        ∮ w in C(a, outerRadius), (w - a) ^ (-(n : ℤ) - 1) * f w := by
    ext n
    rw [← circleIntegral.integral_const_mul]
    refine circleIntegral.integral_congr hS.le fun w hw ↦ ?_
    have hwa : w ≠ a := by
      intro hwa
      have : ‖w - a‖ = outerRadius := by simpa [mem_sphere_iff_norm] using hw
      rw [hwa, sub_self, norm_zero] at this
      exact hS.ne' this.symm
    calc
      ((z - a) / (w - a)) ^ n * ((w - a)⁻¹ * f w)
          = (((z - a) / (w - a)) ^ n * (w - a)⁻¹) * f w := by ring
      _ = ((z - a) ^ n * (w - a) ^ (-(n : ℤ) - 1)) * f w := by
          rw [← geometric_outer_term n hwa]
      _ = (z - a) ^ n * ((w - a) ^ (-(n : ℤ) - 1) * f w) := by ring
  rw [hfun] at hsum
  exact hsum

/-- Geometric expansion of `(w - z)⁻¹` when `‖w - a‖ < ‖z - a‖`. -/
lemma hasSum_inv_sub_of_norm_lt {a z w : ℂ} (h : ‖w - a‖ < ‖z - a‖) :
    HasSum (fun k : ℕ ↦ -((w - a) ^ (k : ℤ) * (z - a) ^ (-(k + 1 : ℤ)))) ((w - z)⁻¹) := by
  have hza : z - a ≠ 0 := by
    intro hzero
    have hlt : ‖w - a‖ < 0 := by simpa [hzero, norm_zero] using h
    exact lt_irrefl _ (lt_of_le_of_lt (norm_nonneg _) hlt)
  have hwz : w ≠ z := by
    intro hwz
    rw [hwz] at h
    exact lt_irrefl _ h
  let ratio : ℂ := (w - a) / (z - a)
  have hratio : ‖ratio‖ < 1 := by
    simp only [ratio, norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hza)).2 h
  have hgeom : HasSum (fun k : ℕ ↦ ratio ^ k) (1 - ratio)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hratio
  have hmul : HasSum (fun k : ℕ ↦ -(z - a)⁻¹ * ratio ^ k) (-(z - a)⁻¹ * (1 - ratio)⁻¹) :=
    hgeom.mul_left (-(z - a)⁻¹)
  have hterm : ∀ k : ℕ, -(z - a)⁻¹ * ratio ^ k =
      -((w - a) ^ (k : ℤ) * (z - a) ^ (-(k + 1 : ℤ))) := by
    intro k
    have hexp : -(k : ℤ) + (-1) = -(k + 1 : ℤ) := by ring
    calc
      -(z - a)⁻¹ * ratio ^ k
          = -(z - a)⁻¹ * (((w - a) * (z - a)⁻¹) ^ k) := by
            simp only [ratio, div_eq_mul_inv]
      _ = -(z - a)⁻¹ * ((w - a) ^ k * ((z - a)⁻¹) ^ k) := by rw [mul_pow]
      _ = -(z - a)⁻¹ * ((w - a) ^ k * ((z - a) ^ k)⁻¹) := by rw [inv_pow]
      _ = -((w - a) ^ k * (((z - a) ^ k)⁻¹ * (z - a)⁻¹)) := by ring
      _ = -((w - a) ^ (k : ℤ) * (z - a) ^ (-(k + 1 : ℤ))) := by
          rw [← zpow_natCast (w - a), ← zpow_natCast (z - a), ← zpow_neg, ← zpow_neg_one,
            ← zpow_add₀ hza, hexp]
  have hval : -(z - a)⁻¹ * (1 - ratio)⁻¹ = (w - z)⁻¹ := by
    have hzw : z - w ≠ 0 := sub_ne_zero.2 hwz.symm
    have hdiff : 1 - ratio = (z - w) * (z - a)⁻¹ := by
      calc
        1 - ratio = (z - a) / (z - a) - (w - a) / (z - a) := by
          simp [ratio, div_self hza]
        _ = ((z - a) - (w - a)) / (z - a) := by rw [← sub_div]
        _ = ((z - a) - (w - a)) * (z - a)⁻¹ := by rw [div_eq_mul_inv]
        _ = (z - w) * (z - a)⁻¹ := by ring
    calc
      -(z - a)⁻¹ * (1 - ratio)⁻¹
          = -(z - a)⁻¹ * ((z - w) * (z - a)⁻¹)⁻¹ := by rw [hdiff]
      _ = -(z - a)⁻¹ * ((z - a) * (z - w)⁻¹) := by rw [mul_inv_rev, inv_inv]
      _ = -((z - a)⁻¹ * ((z - a) * (z - w)⁻¹)) := by ring
      _ = -((z - w)⁻¹) := by rw [inv_mul_cancel_left₀ hza]
      _ = (w - z)⁻¹ := by rw [← neg_sub z w, inv_neg]
  have hfun : (fun k : ℕ ↦ -(z - a)⁻¹ * ratio ^ k) =
      fun k : ℕ ↦ -((w - a) ^ (k : ℤ) * (z - a) ^ (-(k + 1 : ℤ))) := by
    ext k
    exact hterm k
  rw [hfun, hval] at hmul
  exact hmul

/-- The inner Cauchy kernel integrates termwise against its geometric series. -/
lemma hasSum_circleIntegral_geometric_inner (f : ℂ → ℂ) (a z : ℂ) {innerRadius : ℝ}
    (hs : 0 < innerRadius) (hf : ContinuousOn f (sphere a innerRadius))
    (hlt : innerRadius < ‖z - a‖) :
    HasSum (fun k : ℕ ↦ -((z - a) ^ (-(k + 1 : ℤ)) *
        ∮ w in C(a, innerRadius), (w - a) ^ (k : ℤ) * f w))
      (∮ w in C(a, innerRadius), (w - z)⁻¹ * f w) := by
  have hza : 0 < ‖z - a‖ := lt_trans hs hlt
  obtain ⟨M, _, hM⟩ := exists_norm_bound_on_sphere hs hf
  let ratio : ℝ := innerRadius / ‖z - a‖
  have hratio0 : 0 ≤ ratio := div_nonneg hs.le hza.le
  have hratio1 : ratio < 1 := (div_lt_one hza).2 hlt
  have hderiv : Continuous (deriv (circleMap a innerRadius)) := by
    rw [funext (deriv_circleMap a innerRadius)]
    exact (continuous_circleMap 0 innerRadius).mul continuous_const
  have hbase : Continuous fun θ : ℝ ↦ circleMap a innerRadius θ - a :=
    (continuous_circleMap a innerRadius).sub continuous_const
  have hfθ : Continuous fun θ : ℝ ↦ f (circleMap a innerRadius θ) :=
    hf.comp_continuous (continuous_circleMap a innerRadius)
      fun θ ↦ circleMap_mem_sphere a hs.le θ
  let F : ℕ → ℝ → ℂ := fun k θ ↦
    deriv (circleMap a innerRadius) θ *
      (-((circleMap a innerRadius θ - a) ^ (k : ℤ) *
        ((z - a) ^ (-(k + 1 : ℤ)) * f (circleMap a innerRadius θ))))
  let target : ℝ → ℂ := fun θ ↦
    deriv (circleMap a innerRadius) θ *
      ((circleMap a innerRadius θ - z)⁻¹ * f (circleMap a innerRadius θ))
  have hnormθ : ∀ θ, ‖circleMap a innerRadius θ - a‖ = innerRadius := by
    intro θ
    rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hs]
  have hbound : ∀ k θ, ‖F k θ‖ ≤ M * ratio ^ (k + 1) := by
    intro k θ
    have hderivN : ‖deriv (circleMap a innerRadius) θ‖ = innerRadius := by
      rw [deriv_circleMap, norm_mul, norm_circleMap_zero, norm_I, mul_one, abs_of_pos hs]
    have hbaseN : ‖(circleMap a innerRadius θ - a) ^ (k : ℤ)‖ = innerRadius ^ k := by
      rw [norm_zpow, hnormθ, zpow_natCast]
    have hscaleN : ‖(z - a) ^ (-(k + 1 : ℤ))‖ = ‖z - a‖ ^ (-(k + 1 : ℤ)) :=
      norm_zpow _ _
    have hfN : ‖f (circleMap a innerRadius θ)‖ ≤ M :=
      hM _ (circleMap_mem_sphere a hs.le θ)
    have hnormF : ‖F k θ‖ =
        ‖deriv (circleMap a innerRadius) θ‖ *
          (‖(circleMap a innerRadius θ - a) ^ (k : ℤ)‖ *
            (‖(z - a) ^ (-(k + 1 : ℤ))‖ * ‖f (circleMap a innerRadius θ)‖)) := by
      simp only [F, norm_mul, norm_neg]
    rw [hnormF, hderivN, hbaseN, hscaleN]
    have hmul : innerRadius * (innerRadius ^ k *
          (‖z - a‖ ^ (-(k + 1 : ℤ)) * ‖f (circleMap a innerRadius θ)‖)) ≤
        innerRadius * (innerRadius ^ k * (‖z - a‖ ^ (-(k + 1 : ℤ)) * M)) := by
      refine mul_le_mul_of_nonneg_left ?_ hs.le
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hs.le _)
      exact mul_le_mul_of_nonneg_left hfN (zpow_nonneg (norm_nonneg _) _)
    refine hmul.trans_eq ?_
    have hexp : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by
      rw [← Nat.cast_one, ← Nat.cast_add]
    have hzpow : ‖z - a‖ ^ (-((k : ℤ) + 1)) = (‖z - a‖ ^ (k + 1))⁻¹ := by
      rw [zpow_neg, hexp, zpow_natCast]
    have hpowMul : innerRadius * innerRadius ^ k = innerRadius ^ (k + 1) := by
      rw [mul_comm, ← pow_succ]
    calc
      innerRadius * (innerRadius ^ k * (‖z - a‖ ^ (-((k : ℤ) + 1)) * M))
          = (innerRadius * innerRadius ^ k) *
            (‖z - a‖ ^ (-((k : ℤ) + 1)) * M) := by ring
      _ = innerRadius ^ (k + 1) * ((‖z - a‖ ^ (k + 1))⁻¹ * M) := by rw [hpowMul, hzpow]
      _ = (innerRadius ^ (k + 1) * (‖z - a‖ ^ (k + 1))⁻¹) * M := by ring
      _ = (innerRadius ^ (k + 1) / ‖z - a‖ ^ (k + 1)) * M := by rw [← div_eq_mul_inv]
      _ = ratio ^ (k + 1) * M := by rw [← div_pow]
      _ = M * ratio ^ (k + 1) := by ring
  have htail : Summable fun k : ℕ ↦ M * ratio ^ (k + 1) :=
    ((summable_geometric_of_lt_one hratio0 hratio1).comp_injective
      Nat.succ_injective).mul_left M
  have hlim : ∀ θ, HasSum (fun k ↦ F k θ) (target θ) := by
    intro θ
    have hltθ : ‖circleMap a innerRadius θ - a‖ < ‖z - a‖ := by rwa [hnormθ]
    have hgeom := (hasSum_inv_sub_of_norm_lt hltθ).mul_left
      (deriv (circleMap a innerRadius) θ * f (circleMap a innerRadius θ))
    have hfun : (fun k : ℕ ↦ (deriv (circleMap a innerRadius) θ *
          f (circleMap a innerRadius θ)) *
        (-((circleMap a innerRadius θ - a) ^ (k : ℤ) *
          (z - a) ^ (-(k + 1 : ℤ))))) = fun k : ℕ ↦ F k θ := by
      ext k
      simp only [F]
      ring
    have htarget : (deriv (circleMap a innerRadius) θ * f (circleMap a innerRadius θ)) *
        (circleMap a innerRadius θ - z)⁻¹ = target θ := by
      simp only [target]
      ring
    rw [hfun, htarget] at hgeom
    exact hgeom
  have hsum : HasSum (fun k ↦ ∫ θ in 0..2 * π, F k θ) (∫ θ in 0..2 * π, target θ) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k _θ ↦ M * ratio ^ (k + 1)) ?_ ?_ ?_ ?_ ?_
    · intro k
      have hpowC : Continuous fun θ ↦ (circleMap a innerRadius θ - a) ^ (k : ℤ) :=
        hbase.zpow₀ (k : ℤ) fun θ ↦
          Or.inl (sub_ne_zero.2 (circleMap_ne_center (c := a) (R := innerRadius) hs.ne'))
      exact (hderiv.mul ((hpowC.mul (continuous_const.mul hfθ)).neg)).aestronglyMeasurable
    · intro k
      exact Eventually.of_forall fun θ _ ↦ hbound k θ
    · exact Eventually.of_forall fun _ _ ↦ htail
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun θ _ ↦ hlim θ
  have htargetInt : (∫ θ in 0..2 * π, target θ) =
      ∮ w in C(a, innerRadius), (w - z)⁻¹ * f w := by
    simp [target, circleIntegral, smul_eq_mul]
  have htermInt : ∀ k, (∫ θ in 0..2 * π, F k θ) =
      -((z - a) ^ (-(k + 1 : ℤ)) *
        ∮ w in C(a, innerRadius), (w - a) ^ (k : ℤ) * f w) := by
    intro k
    have hEq : ∀ θ, F k θ = -((z - a) ^ (-(k + 1 : ℤ)) *
        (deriv (circleMap a innerRadius) θ *
          ((circleMap a innerRadius θ - a) ^ (k : ℤ) * f (circleMap a innerRadius θ)))) := by
      intro θ
      simp only [F]
      ring
    rw [intervalIntegral.integral_congr fun θ _ ↦ hEq θ, intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul]
    simp [circleIntegral, smul_eq_mul]
  have hfunInt : (fun k : ℕ ↦ ∫ θ in 0..2 * π, F k θ) =
      fun k : ℕ ↦ -((z - a) ^ (-(k + 1 : ℤ)) *
        ∮ w in C(a, innerRadius), (w - a) ^ (k : ℤ) * f w) := by
    ext k
    exact htermInt k
  rw [hfunInt, htargetInt] at hsum
  exact hsum

/-- Laurent coefficients taken on any two circles in the annulus agree. -/
theorem laurentCoefficient_eq {f : ℂ → ℂ} {a : ℂ} {r R ρ σ : ℝ} (hr : 0 ≤ r)
    (hf : DifferentiableOn ℂ f (complexAnnulus a r R)) (hρ : r < ρ) (hρR : ρ < R)
    (hσ : r < σ) (hσR : σ < R) : laurentCoefficient f a ρ = laurentCoefficient f a σ := by
  ext n
  have hρ0 : 0 < ρ := lt_of_le_of_lt hr hρ
  have hσ0 : 0 < σ := lt_of_le_of_lt hr hσ
  let g : ℂ → ℂ := fun z ↦ (z - a) ^ (-n - 1) * f z
  have hdiff : DifferentiableOn ℂ g (complexAnnulus a r R) :=
    differentiableOn_laurentIntegrand (-n - 1) hr hf
  have hopen : IsOpen (complexAnnulus a r R) := isOpen_complexAnnulus a r R
  rcases le_total ρ σ with hle | hle
  · have hint := circleIntegral_eq_of_differentiable_on_annulus_off_countable
        (c := a) (r := ρ) (R := σ) hρ0 hle (f := g) (s := (∅ : Set ℂ)) Set.countable_empty
        (hdiff.continuousOn.mono (closedBall_sdiff_ball_subset_complexAnnulus
          (a := a) (s := ρ) (S := σ) hρ hσR))
        fun w hw ↦ hdiff.differentiableAt (hopen.mem_nhds
          (ball_sdiff_closedBall_subset_complexAnnulus (a := a) (s := ρ) (S := σ) hρ hσR
            (by simpa [Set.sdiff_empty] using hw)))
    simp only [laurentCoefficient]
    rw [hint.symm]
  · have hint := circleIntegral_eq_of_differentiable_on_annulus_off_countable
        (c := a) (r := σ) (R := ρ) hσ0 hle (f := g) (s := (∅ : Set ℂ)) Set.countable_empty
        (hdiff.continuousOn.mono (closedBall_sdiff_ball_subset_complexAnnulus
          (a := a) (s := σ) (S := ρ) hσ hρR))
        fun w hw ↦ hdiff.differentiableAt (hopen.mem_nhds
          (ball_sdiff_closedBall_subset_complexAnnulus (a := a) (s := σ) (S := ρ) hσ hρR
            (by simpa [Set.sdiff_empty] using hw)))
    simp only [laurentCoefficient]
    rw [hint]

/-- A function holomorphic on an annulus equals its Laurent series at each point. -/
theorem hasSum_laurentSeries {f : ℂ → ℂ} {a : ℂ} {r R ρ : ℝ} (hr : 0 ≤ r)
    (hf : DifferentiableOn ℂ f (complexAnnulus a r R)) (hρ : r < ρ) (hρR : ρ < R)
    {z : ℂ} (hz : z ∈ complexAnnulus a r R) :
    HasSum (fun n : ℤ ↦ laurentCoefficient f a ρ n * (z - a) ^ n) (f z) := by
  have hz0 : 0 < ‖z - a‖ := lt_of_le_of_lt hr hz.1
  let innerRadius : ℝ := (r + ‖z - a‖) / 2
  let outerRadius : ℝ := (‖z - a‖ + R) / 2
  have hinner : r < innerRadius := by dsimp [innerRadius]; linarith [hz.1]
  have hinside : innerRadius < ‖z - a‖ := by dsimp [innerRadius]; linarith [hz.1]
  have houtside : ‖z - a‖ < outerRadius := by dsimp [outerRadius]; linarith [hz.2]
  have houter : outerRadius < R := by dsimp [outerRadius]; linarith [hz.2]
  have hinner0 : 0 < innerRadius := lt_of_le_of_lt hr hinner
  have houter0 : 0 < outerRadius := lt_trans hz0 houtside
  have houterIn : r < outerRadius := lt_trans hinner (lt_trans hinside houtside)
  have hinnerOut : innerRadius < R := lt_trans (lt_trans hinside houtside) houter
  have htwo := two_pi_I_mul_eq_circleIntegral_sub hr hf hinner hinside houtside houter
  have hfOuter : ContinuousOn f (sphere a outerRadius) :=
    hf.continuousOn.mono (sphere_subset_complexAnnulus houterIn houter)
  have hfInner : ContinuousOn f (sphere a innerRadius) :=
    hf.continuousOn.mono (sphere_subset_complexAnnulus hinner hinnerOut)
  have houterSum := hasSum_circleIntegral_geometric_outer f a z houter0
    (hfOuter.circleIntegrable houter0.le) houtside
  have hinnerSum := hasSum_circleIntegral_geometric_inner f a z hinner0 hfInner hinside
  have h2π : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  let term : ℤ → ℂ := fun n ↦ laurentCoefficient f a ρ n * (z - a) ^ n
  have hpos : HasSum (fun n : ℕ ↦ term n)
      ((2 * π * I)⁻¹ * ∮ w in C(a, outerRadius), (w - z)⁻¹ * f w) := by
    have hscaled := houterSum.mul_left ((2 * π * I)⁻¹)
    have hfun : (fun n : ℕ ↦ (2 * π * I)⁻¹ * ((z - a) ^ n *
          ∮ w in C(a, outerRadius), (w - a) ^ (-(n : ℤ) - 1) * f w)) =
        fun n : ℕ ↦ term n := by
      ext n
      have hcoeff := laurentCoefficient_eq (ρ := outerRadius) (σ := ρ) hr hf
        houterIn houter hρ hρR
      dsimp only [term]
      rw [← hcoeff, laurentCoefficient, zpow_natCast]
      ring
    rw [hfun] at hscaled
    exact hscaled
  have hneg : HasSum (fun k : ℕ ↦ term (-(k + 1 : ℤ)))
      ((-(2 * π * I)⁻¹) * ∮ w in C(a, innerRadius), (w - z)⁻¹ * f w) := by
    have hscaled := hinnerSum.mul_left (-(2 * π * I)⁻¹)
    have hfun : (fun k : ℕ ↦ -(2 * π * I)⁻¹ *
          (-((z - a) ^ (-(k + 1 : ℤ)) *
            ∮ w in C(a, innerRadius), (w - a) ^ (k : ℤ) * f w))) =
        fun k : ℕ ↦ term (-(k + 1 : ℤ)) := by
      ext k
      have hcoeff := laurentCoefficient_eq (ρ := innerRadius) (σ := ρ) hr hf
        hinner hinnerOut hρ hρR
      have hexp : -(-(k + 1 : ℤ)) - 1 = (k : ℤ) := by ring
      dsimp only [term]
      rw [← hcoeff, laurentCoefficient, hexp]
      ring
    rw [hfun] at hscaled
    exact hscaled
  have hseries := hpos.of_nat_of_neg_add_one hneg
  have hvalue : (2 * π * I)⁻¹ * (∮ w in C(a, outerRadius), (w - z)⁻¹ * f w) +
      (-(2 * π * I)⁻¹) * (∮ w in C(a, innerRadius), (w - z)⁻¹ * f w) = f z := by
    calc
      (2 * π * I)⁻¹ * (∮ w in C(a, outerRadius), (w - z)⁻¹ * f w) +
          (-(2 * π * I)⁻¹) * (∮ w in C(a, innerRadius), (w - z)⁻¹ * f w)
        = (2 * π * I)⁻¹ * ((∮ w in C(a, outerRadius), (w - z)⁻¹ * f w) -
            ∮ w in C(a, innerRadius), (w - z)⁻¹ * f w) := by ring
      _ = (2 * π * I)⁻¹ * ((2 * π * I) * f z) := by rw [← htwo]
      _ = f z := inv_mul_cancel_left₀ h2π _
  rw [hvalue] at hseries
  exact hseries

/-- The Laurent series of a holomorphic function converges normally on the annulus. -/
theorem normallySummableOn_laurentSeries {f : ℂ → ℂ} {a : ℂ} {r R ρ : ℝ} (hr : 0 ≤ r)
    (hf : DifferentiableOn ℂ f (complexAnnulus a r R)) (hρ : r < ρ) (hρR : ρ < R) :
    NormallySummableOn (fun n ↦ fun z ↦ laurentCoefficient f a ρ n * (z - a) ^ n)
      (complexAnnulus a r R) := by
  intro K hK hKsub
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · refine ⟨fun _ ↦ by rw [Set.image_empty]; exact bddAbove_empty, ?_⟩
    simp only [Set.image_empty, Real.sSup_empty]
    exact summable_zero
  · have hnormCont : ContinuousOn (fun w : ℂ ↦ ‖w - a‖) K :=
      (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn
    obtain ⟨wMin, hwMin, hmin⟩ := hK.exists_isMinOn hKne hnormCont
    obtain ⟨wMax, hwMax, hmax⟩ := hK.exists_isMaxOn hKne hnormCont
    let minNorm : ℝ := ‖wMin - a‖
    let maxNorm : ℝ := ‖wMax - a‖
    have hminR : r < minNorm := (hKsub hwMin).1
    have hmaxR : maxNorm < R := (hKsub hwMax).2
    have hminPos : 0 < minNorm := lt_of_le_of_lt hr hminR
    have hle : minNorm ≤ maxNorm := hmax hwMin
    let innerRadius : ℝ := (r + minNorm) / 2
    let outerRadius : ℝ := (maxNorm + R) / 2
    have hinner : r < innerRadius := by dsimp [innerRadius]; linarith
    have hinnerLt : innerRadius < minNorm := by dsimp [innerRadius]; linarith
    have houterLt : maxNorm < outerRadius := by dsimp [outerRadius]; linarith
    have houterR : outerRadius < R := by dsimp [outerRadius]; linarith
    have houter : r < outerRadius := lt_trans hminR (lt_of_le_of_lt hle houterLt)
    have hinnerR : innerRadius < R := lt_trans hinnerLt (lt_of_le_of_lt hle hmaxR)
    have hinner0 : 0 < innerRadius := lt_of_le_of_lt hr hinner
    have houter0 : 0 < outerRadius := lt_trans hminPos (lt_of_le_of_lt hle houterLt)
    obtain ⟨outerMax, houterMax0, houterMax⟩ := exists_norm_bound_on_sphere houter0
      (hf.continuousOn.mono (sphere_subset_complexAnnulus houter houterR))
    obtain ⟨innerMax, hinnerMax0, hinnerMax⟩ := exists_norm_bound_on_sphere hinner0
      (hf.continuousOn.mono (sphere_subset_complexAnnulus hinner hinnerR))
    let outerRatio : ℝ := maxNorm / outerRadius
    let innerRatio : ℝ := innerRadius / minNorm
    have houterRatio0 : 0 ≤ outerRatio := div_nonneg (le_trans hminPos.le hle) houter0.le
    have houterRatio1 : outerRatio < 1 := (div_lt_one houter0).2 houterLt
    have hinnerRatio0 : 0 ≤ innerRatio := div_nonneg hinner0.le hminPos.le
    have hinnerRatio1 : innerRatio < 1 := (div_lt_one hminPos).2 hinnerLt
    let majorant : ℤ → ℝ := fun n ↦
      if 0 ≤ n then outerMax * outerRatio ^ n else innerMax * innerRatio ^ (-n)
    let normTerm : ℤ → ℂ → ℝ :=
      fun n z ↦ ‖laurentCoefficient f a ρ n * (z - a) ^ n‖
    have hcoefOuter : ∀ n : ℤ, ‖laurentCoefficient f a ρ n‖ ≤
        outerMax * outerRadius ^ (-n) := by
      intro n
      rw [← laurentCoefficient_eq (ρ := outerRadius) (σ := ρ) hr hf houter houterR hρ hρR]
      exact norm_laurentCoefficient_le f a houter0 houterMax n
    have hcoefInner : ∀ n : ℤ, ‖laurentCoefficient f a ρ n‖ ≤
        innerMax * innerRadius ^ (-n) := by
      intro n
      rw [← laurentCoefficient_eq (ρ := innerRadius) (σ := ρ) hr hf hinner hinnerR hρ hρR]
      exact norm_laurentCoefficient_le f a hinner0 hinnerMax n
    have hpoint : ∀ n : ℤ, ∀ z ∈ K, normTerm n z ≤ majorant n := by
      intro n z hz
      by_cases hn : 0 ≤ n
      · have habs : normTerm n z = ‖laurentCoefficient f a ρ n‖ * ‖z - a‖ ^ n := by
          simp [normTerm, norm_zpow]
        have hpow : ‖z - a‖ ^ n ≤ maxNorm ^ n :=
          zpow_le_zpow_left₀ hn (norm_nonneg _) (hmax hz)
        have hmul : ‖laurentCoefficient f a ρ n‖ * ‖z - a‖ ^ n ≤
            (outerMax * outerRadius ^ (-n)) * maxNorm ^ n :=
          mul_le_mul (hcoefOuter n) hpow (zpow_nonneg (norm_nonneg _) _)
            (mul_nonneg houterMax0 (zpow_nonneg houter0.le _))
        have hdiv : outerRadius ^ (-n) * maxNorm ^ n = (maxNorm / outerRadius) ^ n := by
          rw [zpow_neg]
          calc
            (outerRadius ^ n)⁻¹ * maxNorm ^ n = maxNorm ^ n * (outerRadius ^ n)⁻¹ := by ring
            _ = maxNorm ^ n / outerRadius ^ n := by rw [← div_eq_mul_inv]
            _ = (maxNorm / outerRadius) ^ n := by rw [← div_zpow]
        have hid : (outerMax * outerRadius ^ (-n)) * maxNorm ^ n =
            outerMax * outerRatio ^ n := by
          calc
            (outerMax * outerRadius ^ (-n)) * maxNorm ^ n
                = outerMax * (outerRadius ^ (-n) * maxNorm ^ n) := by ring
            _ = outerMax * (maxNorm / outerRadius) ^ n := by rw [hdiv]
            _ = outerMax * outerRatio ^ n := by rfl
        rw [habs]
        dsimp only [majorant]
        rw [ite_eq_left hn]
        exact hmul.trans_eq hid
      · have hnlt : n < 0 := lt_of_not_ge hn
        have hnpos : 0 ≤ -n := neg_nonneg.mpr hnlt.le
        have habs : normTerm n z = ‖laurentCoefficient f a ρ n‖ * ‖z - a‖ ^ n := by
          simp [normTerm, norm_zpow]
        have hpow : ‖z - a‖ ^ n ≤ minNorm ^ n := by
          calc
            ‖z - a‖ ^ n = (‖z - a‖ ^ (-n))⁻¹ := by rw [← zpow_neg, neg_neg]
            _ ≤ (minNorm ^ (-n))⁻¹ :=
                inv_anti₀ (zpow_pos hminPos _)
                  (zpow_le_zpow_left₀ hnpos hminPos.le (hmin hz))
            _ = minNorm ^ n := by rw [← zpow_neg, neg_neg]
        have hmul : ‖laurentCoefficient f a ρ n‖ * ‖z - a‖ ^ n ≤
            (innerMax * innerRadius ^ (-n)) * minNorm ^ n :=
          mul_le_mul (hcoefInner n) hpow (zpow_nonneg (norm_nonneg _) _)
            (mul_nonneg hinnerMax0 (zpow_nonneg hinner0.le _))
        have hinvPow : minNorm ^ n = (minNorm ^ (-n))⁻¹ := by rw [← zpow_neg, neg_neg]
        have hdiv : innerRadius ^ (-n) * minNorm ^ n = (innerRadius / minNorm) ^ (-n) := by
          rw [hinvPow]
          calc
            innerRadius ^ (-n) * (minNorm ^ (-n))⁻¹
                = innerRadius ^ (-n) / minNorm ^ (-n) := by rw [← div_eq_mul_inv]
            _ = (innerRadius / minNorm) ^ (-n) := by rw [← div_zpow]
        have hid : (innerMax * innerRadius ^ (-n)) * minNorm ^ n =
            innerMax * innerRatio ^ (-n) := by
          calc
            (innerMax * innerRadius ^ (-n)) * minNorm ^ n
                = innerMax * (innerRadius ^ (-n) * minNorm ^ n) := by ring
            _ = innerMax * (innerRadius / minNorm) ^ (-n) := by rw [hdiv]
            _ = innerMax * innerRatio ^ (-n) := by rfl
        rw [habs]
        dsimp only [majorant]
        rw [ite_eq_right hn]
        exact hmul.trans_eq hid
    have hbdd : ∀ n, BddAbove (normTerm n '' K) := fun n ↦ ⟨majorant n, by
      rintro y ⟨z, hz, rfl⟩
      exact hpoint n z hz⟩
    have hsle : ∀ n, sSup (normTerm n '' K) ≤ majorant n := fun n ↦
      csSup_le (hKne.image (normTerm n)) (by
        rintro y ⟨z, hz, rfl⟩
        exact hpoint n z hz)
    have hnonneg : ∀ n, 0 ≤ sSup (normTerm n '' K) := by
      intro n
      obtain ⟨z0, hz0⟩ := hKne
      exact le_trans (norm_nonneg _)
        (le_csSup (hbdd n) (Set.mem_image_of_mem (normTerm n) hz0))
    refine ⟨hbdd, Summable.of_nonneg_of_le hnonneg hsle ?_⟩
    refine Summable.of_nat_of_neg_add_one ?_ ?_
    · have hgeom : Summable fun k : ℕ ↦ outerMax * outerRatio ^ k :=
        (summable_geometric_of_lt_one houterRatio0 houterRatio1).mul_left outerMax
      refine hgeom.congr fun k ↦ ?_
      simp only [majorant, ite_eq_left (Int.natCast_nonneg k), zpow_natCast]
    · have hgeom : Summable fun k : ℕ ↦ innerMax * innerRatio ^ (k + 1) :=
        ((summable_geometric_of_lt_one hinnerRatio0 hinnerRatio1).comp_injective
          Nat.succ_injective).mul_left innerMax
      refine hgeom.congr fun k ↦ ?_
      have hk : ¬ 0 ≤ -(k + 1 : ℤ) := by
        have hpos : (0 : ℤ) < (k : ℤ) + 1 := by
          have := Int.natCast_nonneg k
          linarith
        exact not_le.mpr (neg_lt_zero.mpr hpos)
      simp only [majorant, ite_eq_right hk, neg_neg]
      have hcast : innerRatio ^ ((k : ℤ) + 1) = innerRatio ^ (k + 1) := by
        have hexp : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by
          rw [← Nat.cast_one, ← Nat.cast_add]
        rw [hexp, zpow_natCast]
      rw [hcast]

/-- A normally summable Laurent expansion is the contour series of its sum. -/
theorem eq_laurentCoefficient {f : ℂ → ℂ} {a : ℂ} {r R ρ : ℝ} (c : ℤ → ℂ) (hr : 0 ≤ r)
    (hρ : r < ρ) (hρR : ρ < R)
    (hn : NormallySummableOn (fun n ↦ fun z ↦ c n * (z - a) ^ n) (complexAnnulus a r R))
    (hs : ∀ z ∈ complexAnnulus a r R, HasSum (fun n ↦ c n * (z - a) ^ n) (f z)) :
    c = laurentCoefficient f a ρ := by
  ext k
  have hρ0 : 0 < ρ := lt_of_le_of_lt hr hρ
  have h2π : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hsphere : sphere a ρ ⊆ complexAnnulus a r R := sphere_subset_complexAnnulus hρ hρR
  obtain ⟨hbdd, hsup⟩ := hn (sphere a ρ) (isCompact_sphere a ρ) hsphere
  let supNorm : ℤ → ℝ := fun n ↦ sSup ((fun w ↦ ‖c n * (w - a) ^ n‖) '' sphere a ρ)
  have hderiv : Continuous (deriv (circleMap a ρ)) := by
    rw [funext (deriv_circleMap a ρ)]
    exact (continuous_circleMap 0 ρ).mul continuous_const
  have hbase : Continuous fun θ : ℝ ↦ circleMap a ρ θ - a :=
    (continuous_circleMap a ρ).sub continuous_const
  let F : ℤ → ℝ → ℂ := fun n θ ↦
    (deriv (circleMap a ρ) θ * (circleMap a ρ θ - a) ^ (-k - 1)) *
      (c n * (circleMap a ρ θ - a) ^ n)
  let target : ℝ → ℂ := fun θ ↦
    deriv (circleMap a ρ) θ *
      ((circleMap a ρ θ - a) ^ (-k - 1) * f (circleMap a ρ θ))
  have hboundConst : ∀ n θ, ‖F n θ‖ ≤ ρ * ρ ^ (-k - 1) * supNorm n := by
    intro n θ
    have hw := circleMap_mem_sphere a hρ0.le θ
    have hderivN : ‖deriv (circleMap a ρ) θ‖ = ρ := by
      rw [deriv_circleMap, norm_mul, norm_circleMap_zero, norm_I, mul_one, abs_of_pos hρ0]
    have hpowN : ‖(circleMap a ρ θ - a) ^ (-k - 1)‖ = ρ ^ (-k - 1) := by
      rw [norm_zpow, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hρ0]
    have htermN : ‖c n * (circleMap a ρ θ - a) ^ n‖ ≤ supNorm n :=
      le_csSup (hbdd n) (Set.mem_image_of_mem (fun w ↦ ‖c n * (w - a) ^ n‖) hw)
    calc
      ‖F n θ‖ = ‖deriv (circleMap a ρ) θ‖ * ‖(circleMap a ρ θ - a) ^ (-k - 1)‖ *
          ‖c n * (circleMap a ρ θ - a) ^ n‖ := by
        simp only [F, norm_mul, mul_assoc]
      _ = ρ * ρ ^ (-k - 1) * ‖c n * (circleMap a ρ θ - a) ^ n‖ := by rw [hderivN, hpowN]
      _ ≤ ρ * ρ ^ (-k - 1) * supNorm n :=
        mul_le_mul_of_nonneg_left htermN (mul_nonneg hρ0.le (zpow_nonneg hρ0.le _))
  have htail : Summable fun n : ℤ ↦ ρ * ρ ^ (-k - 1) * supNorm n := hsup.mul_left _
  have hlim : ∀ θ, HasSum (fun n ↦ F n θ) (target θ) := by
    intro θ
    have hw := circleMap_mem_sphere a hρ0.le θ
    have hsumθ := (hs _ (hsphere hw)).mul_left
      (deriv (circleMap a ρ) θ * (circleMap a ρ θ - a) ^ (-k - 1))
    have htarget : (deriv (circleMap a ρ) θ * (circleMap a ρ θ - a) ^ (-k - 1)) *
        f (circleMap a ρ θ) = target θ := by
      simp only [target]
      ring
    rw [htarget] at hsumθ
    simpa only [F] using hsumθ
  have hsum : HasSum (fun n ↦ ∫ θ in 0..2 * π, F n θ) (∫ θ in 0..2 * π, target θ) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _θ ↦ ρ * ρ ^ (-k - 1) * supNorm n) ?_ ?_ ?_ ?_ ?_
    · intro n
      have hneθ : ∀ θ, circleMap a ρ θ - a ≠ 0 := fun θ ↦
        sub_ne_zero.2 (circleMap_ne_center hρ0.ne')
      have hpow : Continuous fun θ ↦ (circleMap a ρ θ - a) ^ n :=
        hbase.zpow₀ n fun θ ↦ Or.inl (hneθ θ)
      have hfixed : Continuous fun θ ↦ (circleMap a ρ θ - a) ^ (-k - 1) :=
        hbase.zpow₀ (-k - 1) fun θ ↦ Or.inl (hneθ θ)
      exact ((hderiv.mul hfixed).mul (continuous_const.mul hpow)).aestronglyMeasurable
    · intro n
      exact Eventually.of_forall fun θ _ ↦ hboundConst n θ
    · exact Eventually.of_forall fun _ _ ↦ htail
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun θ _ ↦ hlim θ
  have hpowInt : ∀ n : ℤ, (∫ θ in 0..2 * π, F n θ) =
      if n = k then c k * (2 * π * I) else 0 := by
    intro n
    have hEq : ∀ θ, F n θ = c n * (deriv (circleMap a ρ) θ *
        (circleMap a ρ θ - a) ^ (n - k - 1)) := by
      intro θ
      have hne0 : circleMap a ρ θ - a ≠ 0 :=
        sub_ne_zero.2 (circleMap_ne_center hρ0.ne')
      have hexp : n + (-k - 1) = n - k - 1 := by ring
      simp only [F]
      calc
        (deriv (circleMap a ρ) θ * (circleMap a ρ θ - a) ^ (-k - 1)) *
            (c n * (circleMap a ρ θ - a) ^ n)
          = c n * (deriv (circleMap a ρ) θ *
              ((circleMap a ρ θ - a) ^ n * (circleMap a ρ θ - a) ^ (-k - 1))) := by ring
        _ = c n * (deriv (circleMap a ρ) θ * (circleMap a ρ θ - a) ^ (n - k - 1)) := by
            rw [← zpow_add₀ hne0, hexp]
    rw [intervalIntegral.integral_congr fun θ _ ↦ hEq θ, intervalIntegral.integral_const_mul]
    have hcircle : (∫ θ in 0..2 * π, deriv (circleMap a ρ) θ *
        (circleMap a ρ θ - a) ^ (n - k - 1)) =
        ∮ w in C(a, ρ), (w - a) ^ (n - k - 1) := by
      simp [circleIntegral, smul_eq_mul]
    rw [hcircle, circleIntegral_sub_center_zpow a hρ0.ne' (n - k - 1)]
    by_cases hnk : n = k
    · simp [hnk]
    · have hne : n - k - 1 ≠ -1 := by
        intro h
        apply hnk
        linarith
      simp [hnk, hne]
  have hfun : (fun n ↦ ∫ θ in 0..2 * π, F n θ) =
      fun n ↦ if n = k then c k * (2 * π * I) else 0 := by
    ext n
    exact hpowInt n
  rw [hfun] at hsum
  have htargetInt : (∫ θ in 0..2 * π, target θ) =
      ∮ w in C(a, ρ), (w - a) ^ (-k - 1) * f w := by
    simp [target, circleIntegral, smul_eq_mul]
  rw [htargetInt] at hsum
  have hint := hsum.unique (hasSum_ite_eq k (c k * (2 * π * I)))
  rw [laurentCoefficient, hint, mul_comm (c k) (2 * π * I), ← mul_assoc, inv_mul_cancel₀ h2π,
    one_mul]
