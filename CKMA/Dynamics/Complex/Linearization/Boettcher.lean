/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Complex.Linearization.Koenigs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Böttcher coordinate at a superattracting fixed point

Helpers for a germ `f(z) = z ^ k * g(z)` with `k ≥ 2` and `g 0 ≠ 0`. The coordinate is
`φ(z) = c * z * exp (S z)`, where `S` sums the branched logarithm of `g` along the orbit,
and `c ^ (k - 1) = g 0`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Finset Function Metric Set Topology

/-- Binomial expansion of `(ζ + w) ^ k - ζ` when `ζ ^ k = ζ`. -/
theorem exists_pow_sub_factor {zeta : ℂ} {k : ℕ} (hk : 1 ≤ k) (hpow : zeta ^ k = zeta) :
    ∃ Q : ℂ → ℂ, AnalyticAt ℂ Q 0 ∧ Q 0 = (k : ℂ) * zeta ^ (k - 1) ∧
      ∀ w : ℂ, (zeta + w) ^ k - zeta = w * Q w := by
  let term : ℕ → ℂ → ℂ := fun m w ↦
    (k.choose m : ℂ) * zeta ^ m * w ^ (k - 1 - m)
  let Q : ℂ → ℂ := fun w ↦ ∑ m ∈ range k, term m w
  have hterm : ∀ m, AnalyticAt ℂ (term m) 0 := by
    intro m
    have hconst : AnalyticAt ℂ (fun _ : ℂ ↦ (k.choose m : ℂ) * zeta ^ m) 0 :=
      analyticAt_const
    exact hconst.mul ((analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) 0).pow _)
  have hQa : AnalyticAt ℂ Q 0 :=
    Finset.analyticAt_fun_sum (range k) fun m _ ↦ hterm m
  have hchoose : k.choose (k - 1) = k := by
    rw [Nat.choose_symm (by omega : 1 ≤ k), Nat.choose_one_right]
  have hQ0 : Q 0 = (k : ℂ) * zeta ^ (k - 1) := by
    have hone : (0 : ℂ) ^ (0 : ℕ) = 1 := pow_zero _
    rw [show Q 0 = ∑ m ∈ range k, term m 0 by rfl]
    rw [Finset.sum_eq_single (k - 1)]
    · simp only [term, hone, mul_one, Nat.sub_self, hchoose]
    · intro m hm hmne
      have hm0 : k - 1 - m ≠ 0 := by
        have hmlt : m < k := mem_range.mp hm
        omega
      simp [term, zero_pow hm0]
    · intro hmiss
      exact absurd (mem_range.mpr (by omega : k - 1 < k)) hmiss
  refine ⟨Q, hQa, hQ0, fun w ↦ ?_⟩
  have hbin := add_pow zeta w k
  rw [sum_range_succ] at hbin
  have hlast : zeta ^ k * w ^ (k - k) * (k.choose k : ℂ) = zeta ^ k := by
    simp [Nat.choose_self, pow_zero]
  have hfactor : ∑ m ∈ range k, zeta ^ m * w ^ (k - m) * (k.choose m : ℂ) = w * Q w := by
    rw [show Q w = ∑ m ∈ range k, term m w by rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    have hmlt : m < k := mem_range.mp hm
    have hexp : k - m = (k - 1 - m) + 1 := by omega
    calc
      zeta ^ m * w ^ (k - m) * (k.choose m : ℂ)
          = zeta ^ m * (w ^ (k - 1 - m) * w) * (k.choose m : ℂ) := by
            rw [hexp, pow_succ]
      _ = w * ((k.choose m : ℂ) * zeta ^ m * w ^ (k - 1 - m)) := by ring
      _ = w * term m w := by rfl
  calc
    (zeta + w) ^ k - zeta
        = (∑ m ∈ range k, zeta ^ m * w ^ (k - m) * (k.choose m : ℂ)) + zeta ^ k - zeta := by
          rw [hbin, hlast]
    _ = w * Q w + zeta ^ k - zeta := by rw [hfactor]
    _ = w * Q w := by rw [hpow, add_sub_cancel_right]

/-- A normalized Böttcher germ built from the logarithm of the leading coefficient. -/
theorem exists_boettcher_data {f g : ℂ → ℂ} {k : ℕ} (hk : 2 ≤ k) (hg : AnalyticAt ℂ g 0)
    (hg₀ : g 0 ≠ 0) (hf : ∀ᶠ z in 𝓝 (0 : ℂ), f z = z ^ k * g z) {c : ℂ}
    (hc : c ^ (k - 1) = g 0) :
    ∃ phi : ℂ → ℂ, AnalyticAt ℂ f 0 ∧ f 0 = 0 ∧ AnalyticAt ℂ phi 0 ∧ phi 0 = 0 ∧
      deriv phi 0 = c ∧ ∀ᶠ z in 𝓝 (0 : ℂ), phi (f z) = phi z ^ k := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : 1 ≤ k := by omega
  have hc0 : c ≠ 0 := by
    intro hzero
    apply hg₀
    rw [← hc, hzero, zero_pow (by omega : k - 1 ≠ 0)]
  let F : ℂ → ℂ := fun z ↦ z ^ k * g z
  have hFa : AnalyticAt ℂ F 0 :=
    ((analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) 0).pow k).mul hg
  have hfa : AnalyticAt ℂ f 0 := hFa.congr (Filter.EventuallyEq.symm hf)
  have hf0 : f 0 = 0 := by
    have hval : f 0 = (0 : ℂ) ^ k * g 0 := Filter.EventuallyEq.eq_of_nhds hf
    rw [zero_pow hk0, zero_mul] at hval
    exact hval
  let quot : ℂ → ℂ := fun z ↦ g z / g 0
  have hqa : AnalyticAt ℂ quot 0 := hg.div analyticAt_const hg₀
  have hq0 : quot 0 = 1 := by simp [quot, div_self hg₀]
  have hone : (1 : ℂ) ∈ Complex.slitPlane := by
    have hnorm : ‖(0 : ℂ)‖ < 1 := by
      rw [norm_zero]
      exact zero_lt_one
    rw [← add_zero (1 : ℂ)]
    exact Complex.mem_slitPlane_of_norm_lt_one hnorm
  obtain ⟨δL, hδL, hLclose⟩ :=
    (Metric.continuousAt_iff.mp (continuousAt_clog hone)) 1 zero_lt_one
  let eps : ℝ := min (1 / 2) δL
  have heps : 0 < eps := lt_min (div_pos one_pos zero_lt_two) hδL
  obtain ⟨δQ, hδQ, hQclose⟩ := (Metric.continuousAt_iff.mp hqa.continuousAt) eps heps
  obtain ⟨δEq, hδEq, hEq⟩ := Metric.eventually_nhds_iff_ball.mp hf
  obtain ⟨pg, hpg⟩ := hg
  obtain ⟨δG, hδG, hGdiff⟩ := Metric.eventually_nhds_iff_ball.mp hpg.eventually_differentiableAt
  obtain ⟨δN, hδN, hNclose⟩ :=
    (Metric.continuousAt_iff.mp hpg.continuousAt) 1 zero_lt_one
  let M : ℝ := ‖g 0‖ + 1
  have hM : 0 < M := add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
  let r : ℝ := min (min (min (min (min δEq δG) δQ) δN) 1) (1 / (2 * M))
  have hr : 0 < r := by
    have hinv : 0 < 1 / (2 * M) := div_pos one_pos (mul_pos zero_lt_two hM)
    exact lt_min (lt_min (lt_min (lt_min (lt_min hδEq hδG) hδQ) hδN) zero_lt_one) hinv
  have hrEq : r ≤ δEq := le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (min_le_left _ _))))
  have hrG : r ≤ δG := le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (min_le_right _ _))))
  have hrQ : r ≤ δQ := le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hrN : r ≤ δN := le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (min_le_right _ _))
  have hr1 : r ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hrM : r ≤ 1 / (2 * M) := min_le_right _ _
  have hMr : M * r ≤ 1 / 2 := by
    calc
      M * r ≤ M * (1 / (2 * M)) := mul_le_mul_of_nonneg_left hrM hM.le
      _ = M / (2 * M) := by rw [one_div, ← div_eq_mul_inv]
      _ = M / (M * 2) := by rw [mul_comm 2 M]
      _ = M / M / 2 := by rw [div_mul_eq_div_div]
      _ = 1 / 2 := by rw [div_self hM.ne']
  have hFeq : ∀ z ∈ ball (0 : ℂ) r, f z = z ^ k * g z := by
    intro z hz
    exact hEq z (ball_subset_ball hrEq hz)
  have hgnorm : ∀ z ∈ ball (0 : ℂ) r, ‖g z‖ ≤ M := by
    intro z hz
    have hdist : ‖g z - g 0‖ < 1 := by
      have hzN : dist z 0 < δN := by
        rw [dist_eq_norm, sub_zero]
        exact lt_of_lt_of_le (by simpa [mem_ball, dist_eq_norm, sub_zero] using hz) hrN
      rw [← dist_eq_norm]
      exact hNclose hzN
    have htri : ‖g z‖ ≤ ‖g z - g 0‖ + ‖g 0‖ := by
      simpa [sub_add_cancel] using norm_add_le (g z - g 0) (g 0)
    have hltM : ‖g z‖ < M := by
      have hsum : ‖g z - g 0‖ + ‖g 0‖ < 1 + ‖g 0‖ := by linarith
      exact htri.trans_lt (by simpa [M, add_comm] using hsum)
    exact hltM.le
  have hmaps : MapsTo f (ball 0 r) (ball 0 r) := by
    intro z hz
    rw [mem_ball, dist_eq_norm, sub_zero]
    by_cases hz0 : z = 0
    · simp [hz0, hf0, hr]
    · have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hzlt : ‖z‖ < r := by simpa [mem_ball, dist_eq_norm, sub_zero] using hz
      have hz1 : ‖z‖ ≤ 1 := le_trans hzlt.le hr1
      have hpow : ‖z‖ ^ k ≤ ‖z‖ ^ 2 :=
        pow_le_pow_of_le_one (norm_nonneg _) hz1 (by omega : 2 ≤ k)
      have hsq : ‖z‖ ^ 2 < r * ‖z‖ := by
        have hmul : ‖z‖ * ‖z‖ < r * ‖z‖ := mul_lt_mul_of_pos_right hzlt hzn
        simpa [pow_two, mul_comm] using hmul
      have hfz : ‖f z‖ ≤ M * ‖z‖ ^ 2 := by
        rw [hFeq z hz, norm_mul, norm_pow]
        calc
          ‖z‖ ^ k * ‖g z‖ ≤ ‖z‖ ^ k * M :=
            mul_le_mul_of_nonneg_left (hgnorm z hz) (pow_nonneg (norm_nonneg _) _)
          _ ≤ ‖z‖ ^ 2 * M := mul_le_mul_of_nonneg_right hpow hM.le
          _ = M * ‖z‖ ^ 2 := mul_comm _ _
      have hstrict : M * ‖z‖ ^ 2 < (1 / 2) * ‖z‖ := by
        calc
          M * ‖z‖ ^ 2 < M * (r * ‖z‖) := mul_lt_mul_of_pos_left hsq hM
          _ = (M * r) * ‖z‖ := by ring
          _ ≤ (1 / 2) * ‖z‖ := mul_le_mul_of_nonneg_right hMr (norm_nonneg _)
      exact lt_of_le_of_lt hfz (lt_of_lt_of_le hstrict (by
        have hhalf : (1 / 2) * ‖z‖ ≤ (1 / 2) * r :=
          mul_le_mul_of_nonneg_left hzlt.le (div_pos one_pos zero_lt_two).le
        have hrhalf : (1 / 2) * r ≤ r := by
          have honele : (1 / 2 : ℝ) ≤ 1 := by linarith
          simpa [one_mul] using mul_le_mul_of_nonneg_right honele hr.le
        exact le_trans hhalf hrhalf))
  have hquotClose : ∀ z ∈ ball (0 : ℂ) r, ‖quot z - 1‖ < eps := by
    intro z hz
    have hzQ : dist z 0 < δQ := by
      rw [dist_eq_norm, sub_zero]
      exact lt_of_lt_of_le (by simpa [mem_ball, dist_eq_norm, sub_zero] using hz) hrQ
    have hdist := hQclose hzQ
    rw [hq0, dist_eq_norm] at hdist
    simpa using hdist
  have hsplit : ∀ z ∈ ball (0 : ℂ) r, quot z ∈ Complex.slitPlane := by
    intro z hz
    have hnorm : ‖quot z - 1‖ < 1 :=
      lt_of_lt_of_le (hquotClose z hz) (le_trans (min_le_left _ _) (by linarith : (1 / 2 : ℝ) ≤ 1))
    rw [show quot z = 1 + (quot z - 1) by ring]
    exact Complex.mem_slitPlane_of_norm_lt_one hnorm
  let hlog : ℂ → ℂ := fun z ↦ Complex.log (quot z)
  have hlog0 : hlog 0 = 0 := by simp [hlog, hq0, Complex.log_one]
  have hlogOn : DifferentiableOn ℂ hlog (ball 0 r) := by
    intro z hz
    have hgz : DifferentiableAt ℂ g z := hGdiff z (ball_subset_ball hrG hz)
    have hquotAt : DifferentiableAt ℂ quot z := hgz.div_const (g 0)
    exact (hquotAt.clog (hsplit z hz)).differentiableWithinAt
  have hlog_le : ∀ z ∈ ball (0 : ℂ) r, ‖hlog z‖ ≤ 1 := by
    intro z hz
    have hdist1 : dist (quot z) 1 < δL := by
      have hdist_eps : dist (quot z) 1 < eps := by
        rw [dist_eq_norm]
        exact hquotClose z hz
      exact lt_of_lt_of_le hdist_eps (min_le_right _ _)
    have hlt : ‖Complex.log (quot z) - Complex.log 1‖ < 1 := by
      rw [← dist_eq_norm]
      exact hLclose hdist1
    rw [Complex.log_one, sub_zero] at hlt
    exact hlt.le
  have hfOn : DifferentiableOn ℂ f (ball 0 r) := by
    intro z hz
    have hFAt : DifferentiableAt ℂ (fun w ↦ w ^ k * g w) z :=
      ((differentiableAt_id.pow k).mul (hGdiff z (ball_subset_ball hrG hz)))
    have hnear : f =ᶠ[𝓝 z] fun w ↦ w ^ k * g w := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      exact hFeq w hw
    exact (hFAt.congr_of_eventuallyEq hnear).differentiableWithinAt
  let kinv : ℂ := (k : ℂ)⁻¹
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
  have hkinv : (k : ℂ) * kinv = 1 := mul_inv_cancel₀ hkC
  have hratio : (k : ℝ)⁻¹ < 1 := by
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < k))
  have hgeom : Summable fun j : ℕ ↦ (k : ℝ)⁻¹ ^ j :=
    summable_geometric_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg _)) hratio
  have htail : Summable fun j : ℕ ↦ (k : ℝ)⁻¹ ^ (j + 1) :=
    (summable_nat_add_iff 1).mpr hgeom
  let term : ℕ → ℂ → ℂ := fun j z ↦ kinv ^ (j + 1) * hlog ((f^[j]) z)
  have htermOn : ∀ j, DifferentiableOn ℂ (term j) (ball 0 r) := by
    intro j
    have hcomp : DifferentiableOn ℂ (fun z ↦ hlog ((f^[j]) z)) (ball 0 r) := by
      intro z hz
      have hiter : DifferentiableAt ℂ (f^[j]) z :=
        ((hfOn.iterate hmaps j) z hz).differentiableAt (isOpen_ball.mem_nhds hz)
      have hzj : (f^[j]) z ∈ ball 0 r := (hmaps.iterate j) hz
      have hlogAt : DifferentiableAt ℂ hlog ((f^[j]) z) :=
        (hlogOn _ hzj).differentiableAt (isOpen_ball.mem_nhds hzj)
      exact (DifferentiableAt.fun_comp' (x := z) hlogAt hiter).differentiableWithinAt
    have hmul := hcomp.const_mul (kinv ^ (j + 1))
    have hfun : term j = fun z ↦ kinv ^ (j + 1) * hlog ((f^[j]) z) := rfl
    rw [hfun]
    exact hmul
  have hbound : ∀ j, ∀ z ∈ ball (0 : ℂ) r, ‖term j z‖ ≤ (k : ℝ)⁻¹ ^ (j + 1) := by
    intro j z hz
    have hzj : (f^[j]) z ∈ ball 0 r := (hmaps.iterate j) hz
    have hknorm : ‖kinv‖ = (k : ℝ)⁻¹ := by
      simp [kinv, norm_inv]
    calc
      ‖term j z‖ = ‖kinv‖ ^ (j + 1) * ‖hlog ((f^[j]) z)‖ := by
        simp [term, norm_pow]
      _ ≤ ‖kinv‖ ^ (j + 1) * 1 :=
        mul_le_mul_of_nonneg_left (hlog_le _ hzj) (pow_nonneg (norm_nonneg _) _)
      _ = (k : ℝ)⁻¹ ^ (j + 1) := by rw [hknorm, mul_one]
  let S : ℂ → ℂ := fun z ↦ ∑' j, term j z
  have hSdiff : DifferentiableOn ℂ S (ball 0 r) :=
    Complex.differentiableOn_tsum_of_summable_norm htail (fun j ↦ htermOn j) isOpen_ball
      fun j w hw ↦ hbound j w hw
  have hterm0 : ∀ j, term j 0 = 0 := by
    intro j
    unfold term
    rw [iterate_fixed hf0 j, hlog0, mul_zero]
  have hS0 : S 0 = 0 := by
    have hfun : (fun j ↦ term j 0) = fun _ : ℕ ↦ (0 : ℂ) := by
      ext j
      exact hterm0 j
    unfold S
    rw [hfun, tsum_zero]
  have hpow_cancel : ∀ j : ℕ, (k : ℂ) * kinv ^ (j + 2) = kinv ^ (j + 1) := by
    intro j
    calc
      (k : ℂ) * kinv ^ (j + 2) = (k : ℂ) * (kinv * kinv ^ (j + 1)) := by rw [pow_succ']
      _ = ((k : ℂ) * kinv) * kinv ^ (j + 1) := by ring
      _ = kinv ^ (j + 1) := by rw [hkinv, one_mul]
  have hstepS : ∀ z ∈ ball (0 : ℂ) r, S (f z) = (k : ℂ) * S z - hlog z := by
    intro z hz
    have hzf : f z ∈ ball 0 r := hmaps hz
    have hsumz : Summable fun j ↦ term j z :=
      htail.of_norm_bounded fun j ↦ hbound j z hz
    have hsumf : Summable fun j ↦ term j (f z) :=
      htail.of_norm_bounded fun j ↦ hbound j (f z) hzf
    have hfun : (fun j ↦ term j (f z)) =
        fun j ↦ (k : ℂ) * term (j + 1) z := by
      ext j
      unfold term
      rw [← iterate_succ_apply f j z]
      have hcoef : (k : ℂ) * kinv ^ (j + 1 + 1) = kinv ^ (j + 1) := by
        simpa [Nat.add_assoc] using hpow_cancel j
      calc
        kinv ^ (j + 1) * hlog ((f^[j + 1]) z)
            = ((k : ℂ) * kinv ^ (j + 1 + 1)) * hlog ((f^[j + 1]) z) := by rw [hcoef]
        _ = (k : ℂ) * (kinv ^ ((j + 1) + 1) * hlog ((f^[j + 1]) z)) := by ring
    have htailz : Summable fun j ↦ term (j + 1) z := (summable_nat_add_iff 1).mpr hsumz
    have hsplit : S z = term 0 z + ∑' j, term (j + 1) z := by
      unfold S
      exact hsumz.tsum_eq_zero_add
    have htermZero : term 0 z = kinv * hlog z := by
      simp [term, pow_one, iterate_zero_apply]
    have hSf : S (f z) = (k : ℂ) * ∑' j, term (j + 1) z := by
      unfold S
      rw [hfun]
      exact htailz.tsum_mul_left (k : ℂ)
    calc
      S (f z) = (k : ℂ) * ∑' j, term (j + 1) z := hSf
      _ = (k : ℂ) * (S z - term 0 z) := by
        rw [hsplit, add_sub_cancel_left]
      _ = (k : ℂ) * S z - hlog z := by
        rw [htermZero, mul_sub, ← mul_assoc, hkinv, one_mul]
  let phi : ℂ → ℂ := fun z ↦ c * (z * Complex.exp (S z))
  have hphiOn : DifferentiableOn ℂ phi (ball 0 r) := by
    have hexp : DifferentiableOn ℂ (fun z ↦ Complex.exp (S z)) (ball 0 r) := hSdiff.cexp
    exact ((differentiableOn_id.mul hexp).const_mul c)
  have hphia : AnalyticAt ℂ phi 0 :=
    hphiOn.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hphi0 : phi 0 = 0 := by simp [phi, mul_zero]
  have hderiv : deriv phi 0 = c := by
    have hSAt : DifferentiableAt ℂ S 0 :=
      (hSdiff 0 (mem_ball_self hr)).differentiableAt
        (isOpen_ball.mem_nhds (mem_ball_self hr))
    have hexp : DifferentiableAt ℂ (fun z ↦ Complex.exp (S z)) 0 := hSAt.cexp
    have hid : DifferentiableAt ℂ (fun z : ℂ ↦ z) 0 := differentiableAt_id
    have hu : DifferentiableAt ℂ (fun z ↦ z * Complex.exp (S z)) 0 := hid.mul hexp
    have hprod : deriv (fun z ↦ z * Complex.exp (S z)) 0 = 1 := by
      rw [deriv_fun_mul hid hexp, deriv_id'', deriv_cexp hSAt, hS0, Complex.exp_zero]
      simp
    rw [show phi = fun z ↦ c * (z * Complex.exp (S z)) by rfl,
      deriv_const_mul c hu, hprod, mul_one]
  have heqBall : ∀ z ∈ ball (0 : ℂ) r, phi (f z) = phi z ^ k := by
    intro z hz
    have hfz := hFeq z hz
    have hSz := hstepS z hz
    have hne : quot z ≠ 0 := Complex.slitPlane_ne_zero (hsplit z hz)
    have hgnz : g z ≠ 0 := by
      intro hgz
      apply hne
      simp [quot, hgz, zero_div]
    have hexpLog : Complex.exp (hlog z) = g z / g 0 := by
      simpa [hlog, quot] using Complex.exp_log hne
    have hgexp : g z / Complex.exp (hlog z) = g 0 := by
      rw [hexpLog, div_div_cancel₀ hgnz]
    have hExpS : Complex.exp ((k : ℂ) * S z) = Complex.exp (S z) ^ k :=
      Complex.exp_nat_mul (S z) k
    have hcg : c * g 0 = c ^ k := by
      rw [← hc, mul_comm, ← pow_succ, Nat.sub_add_cancel hk1]
    calc
      phi (f z) = c * (f z * Complex.exp (S (f z))) := rfl
      _ = c * (f z * Complex.exp ((k : ℂ) * S z - hlog z)) := by rw [hSz]
      _ = c * ((z ^ k * g z) * Complex.exp ((k : ℂ) * S z - hlog z)) := by rw [hfz]
      _ = c * ((z ^ k * g z) *
          (Complex.exp ((k : ℂ) * S z) / Complex.exp (hlog z))) := by
        rw [Complex.exp_sub]
      _ = c * ((z ^ k * g z) * (Complex.exp (S z) ^ k / Complex.exp (hlog z))) := by
        rw [hExpS]
      _ = c * (z ^ k * (g z / Complex.exp (hlog z)) * Complex.exp (S z) ^ k) := by ring
      _ = c * (z ^ k * g 0 * Complex.exp (S z) ^ k) := by rw [hgexp]
      _ = (c * g 0) * (z * Complex.exp (S z)) ^ k := by
        rw [mul_pow]
        ring
      _ = c ^ k * (z * Complex.exp (S z)) ^ k := by rw [hcg]
      _ = (c * (z * Complex.exp (S z))) ^ k := by rw [← mul_pow]
      _ = phi z ^ k := rfl
  refine ⟨phi, hfa, hf0, hphia, hphi0, hderiv, ?_⟩
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
  exact heqBall z hz

/-- Two Böttcher coordinates differ by a `(k - 1)`st root of unity. -/
theorem boettcherCoordinate_eq_mul_unity {f phi psi : ℂ → ℂ} {k : ℕ} (hk : 2 ≤ k)
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) (hφa : AnalyticAt ℂ phi 0) (hφ0 : phi 0 = 0)
    (hφd : deriv phi 0 ≠ 0) (hφe : ∀ᶠ z in 𝓝 (0 : ℂ), phi (f z) = phi z ^ k)
    (hψa : AnalyticAt ℂ psi 0) (hψ0 : psi 0 = 0) (hψd : deriv psi 0 ≠ 0)
    (hψe : ∀ᶠ z in 𝓝 (0 : ℂ), psi (f z) = psi z ^ k) :
    ∃ zeta : ℂ, zeta ^ (k - 1) = 1 ∧ ∀ᶠ z in 𝓝 (0 : ℂ), psi z = zeta * phi z := by
  have htend : Tendsto f (𝓝 (0 : ℂ)) (𝓝 0) := by
    have hcont : Tendsto f (𝓝 0) (𝓝 (f 0)) := hf.continuousAt.tendsto
    rwa [hf0] at hcont
  obtain ⟨u, hua, hu0, hufac⟩ := exists_linear_factor hφa hφ0 hφd
  obtain ⟨v, hva, hv0, hvfac⟩ := exists_linear_factor hψa hψ0 hψd
  have hu0' : u 0 ≠ 0 := by simpa [hu0] using hφd
  have hv0' : v 0 ≠ 0 := by simpa [hv0] using hψd
  let ratio : ℂ → ℂ := fun z ↦ v z / u z
  have hratioA : AnalyticAt ℂ ratio 0 := hva.div hua hu0'
  have hu_ne : ∀ᶠ z in 𝓝 (0 : ℂ), u z ≠ 0 := by
    have hset : ∀ᶠ w in 𝓝 (u 0), w ≠ 0 := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hu0'] with w hw
      simpa using hw
    exact hua.continuousAt.tendsto.eventually hset
  have hv_ne : ∀ᶠ z in 𝓝 (0 : ℂ), v z ≠ 0 := by
    have hset : ∀ᶠ w in 𝓝 (v 0), w ≠ 0 := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hv0'] with w hw
      simpa using hw
    exact hva.continuousAt.tendsto.eventually hset
  have huf : ∀ᶠ z in 𝓝 (0 : ℂ), u (f z) ≠ 0 := htend.eventually hu_ne
  have hvf : ∀ᶠ z in 𝓝 (0 : ℂ), v (f z) ≠ 0 := htend.eventually hv_ne
  have hufEq : ∀ᶠ z in 𝓝 (0 : ℂ), phi (f z) = f z * u (f z) :=
    Filter.EventuallyEq.comp_tendsto hufac htend
  have hvfEq : ∀ᶠ z in 𝓝 (0 : ℂ), psi (f z) = f z * v (f z) :=
    Filter.EventuallyEq.comp_tendsto hvfac htend
  have hfz_imp : ∀ᶠ z in 𝓝 (0 : ℂ), f z = 0 → z = 0 := by
    filter_upwards [hφe, hufac, hufEq, hu_ne] with z hφ hu hufz huN hfz
    have hφ' : f z * u (f z) = (z * u z) ^ k := by rw [← hufz, hφ, hu]
    rw [hfz, zero_mul] at hφ'
    exact (mul_eq_zero.mp ((pow_eq_zero_iff (by omega : k ≠ 0)).mp hφ'.symm)).resolve_right
      huN
  have hcontL : ContinuousAt (ratio ∘ f) 0 := by
    have hrat : ContinuousAt ratio (f 0) := by
      rw [hf0]
      exact hratioA.continuousAt
    exact hrat.comp hf.continuousAt
  have hcontR : ContinuousAt (ratio ^ k) 0 := hratioA.continuousAt.pow k
  have : (𝓝[≠] (0 : ℂ)).NeBot := Real.punctured_nhds_module_neBot 0
  have hratio_eq : ratio ∘ f =ᶠ[𝓝 (0 : ℂ)] ratio ^ k := by
    have hpunct : ratio ∘ f =ᶠ[𝓝[≠] (0 : ℂ)] ratio ^ k := by
      filter_upwards [
        hφe.filter_mono nhdsWithin_le_nhds, hψe.filter_mono nhdsWithin_le_nhds,
        hufac.filter_mono nhdsWithin_le_nhds, hvfac.filter_mono nhdsWithin_le_nhds,
        hufEq.filter_mono nhdsWithin_le_nhds, hvfEq.filter_mono nhdsWithin_le_nhds,
        hu_ne.filter_mono nhdsWithin_le_nhds, huf.filter_mono nhdsWithin_le_nhds,
        hfz_imp.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
        with z hφ hψ hu hv hufz hvfz huN huF hfz0 hzne
      simp only [Function.comp_def, Pi.pow_apply]
      have hφ' : f z * u (f z) = (z * u z) ^ k := by rw [← hufz, hφ, hu]
      have hψ' : f z * v (f z) = (z * v z) ^ k := by rw [← hvfz, hψ, hv]
      have hfz : f z ≠ 0 := fun hzero ↦ hzne (hfz0 hzero)
      have hcross : u (f z) * v z ^ k = v (f z) * u z ^ k := by
        have hleft : f z * (u (f z) * v z ^ k) = (z * u z) ^ k * v z ^ k := by
          calc
            f z * (u (f z) * v z ^ k) = f z * u (f z) * v z ^ k := by ring
            _ = (z * u z) ^ k * v z ^ k := by rw [hφ']
        have hright : f z * (v (f z) * u z ^ k) = (z * v z) ^ k * u z ^ k := by
          calc
            f z * (v (f z) * u z ^ k) = f z * v (f z) * u z ^ k := by ring
            _ = (z * v z) ^ k * u z ^ k := by rw [hψ']
        have hcomm : (z * u z) ^ k * v z ^ k = (z * v z) ^ k * u z ^ k := by ring
        exact mul_left_cancel₀ hfz (hleft.trans (hcomm.trans hright.symm))
      have hdiv : v (f z) / u (f z) = v z ^ k / u z ^ k := by
        rw [div_eq_div_iff huF (pow_ne_zero k huN), hcross.symm]
        rw [mul_comm (u (f z)) (v z ^ k)]
      unfold ratio
      rw [div_pow]
      exact hdiv
    exact (hcontL.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hcontR).mp hpunct
  let zeta : ℂ := ratio 0
  have hzeta_ne : zeta ≠ 0 := by
    simp [zeta, ratio, div_ne_zero hv0' hu0']
  have hzeta_pow : zeta ^ k = zeta := by
    have h0 := Filter.Eventually.self_of_nhds hratio_eq
    have h0' : ratio (f 0) = ratio 0 ^ k := by
      simpa [Function.comp_def, Pi.pow_apply] using h0
    rw [hf0] at h0'
    simpa [zeta] using h0'.symm
  have hroot : zeta ^ (k - 1) = 1 := by
    apply mul_right_cancel₀ hzeta_ne
    calc
      zeta ^ (k - 1) * zeta = zeta ^ k := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
      _ = zeta := hzeta_pow
      _ = 1 * zeta := (one_mul zeta).symm
  obtain ⟨Q, hQa, hQ0, hQeq⟩ :=
    exists_pow_sub_factor (by omega : 1 ≤ k) hzeta_pow
  have hQne : Q 0 ≠ 0 := by
    rw [hQ0, hroot, mul_one]
    exact Nat.cast_ne_zero.mpr (by omega : k ≠ 0)
  let gap : ℂ → ℂ := fun z ↦ ratio z - zeta
  have hgapA : AnalyticAt ℂ gap 0 := hratioA.sub analyticAt_const
  have hgap0 : gap 0 = 0 := by simp [gap, zeta]
  have hshift : ∀ᶠ z in 𝓝 (0 : ℂ), gap (f z) = (zeta + gap z) ^ k - zeta := by
    filter_upwards [hratio_eq] with z hz
    have hz' : ratio (f z) = ratio z ^ k := by
      simpa [Function.comp_def, Pi.pow_apply] using hz
    simp only [gap]
    rw [hz']
    ring
  have hfactor : gap ∘ f =ᶠ[𝓝 (0 : ℂ)] gap * (Q ∘ gap) := by
    filter_upwards [hshift] with z hz
    simp only [Function.comp_def, Pi.mul_apply]
    exact hz.trans (hQeq (gap z))
  have hordφ : analyticOrderAt phi 0 = 1 :=
    hφa.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hφ0 hφd
  have hordRight : analyticOrderAt (phi ^ k) 0 = k := by
    rw [analyticOrderAt_pow hφa k, hordφ, nsmul_one]
  have hsubf : analyticOrderAt (fun z ↦ f z - f 0) 0 = analyticOrderAt f 0 := by
    refine analyticOrderAt_congr ?_
    filter_upwards with z
    simp [hf0]
  have hordComp : analyticOrderAt (phi ∘ f) 0 = analyticOrderAt f 0 := by
    have hφf : AnalyticAt ℂ phi (f 0) := by
      rw [hf0]
      exact hφa
    rw [hφf.analyticOrderAt_comp hf, hsubf, hf0, hordφ, one_mul]
  have hordf : analyticOrderAt f 0 = k := by
    have hcong : analyticOrderAt (phi ∘ f) 0 = analyticOrderAt (phi ^ k) 0 := by
      refine analyticOrderAt_congr ?_
      filter_upwards [hφe] with z hz
      simp [Pi.pow_apply, hz]
    rw [← hordComp, hcong, hordRight]
  by_cases htop : analyticOrderAt gap 0 = ⊤
  · refine ⟨zeta, hroot, ?_⟩
    have hgap_zero : ∀ᶠ z in 𝓝 (0 : ℂ), gap z = 0 := analyticOrderAt_eq_top.mp htop
    filter_upwards [hgap_zero, hufac, hvfac, hu_ne] with z hgz hφz hψz huN
    have hrat : ratio z = zeta := by
      unfold gap at hgz
      exact sub_eq_zero.mp hgz
    have hvz : v z = zeta * u z := by
      unfold ratio at hrat
      exact (div_eq_iff huN).mp hrat
    calc
      psi z = z * v z := hψz
      _ = z * (zeta * u z) := by rw [hvz]
      _ = zeta * (z * u z) := by ring
      _ = zeta * phi z := by rw [hφz]
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
    have hm1 : 1 ≤ m := by
      have hne : analyticOrderAt gap 0 ≠ 0 := by
        intro hzero
        rw [analyticOrderAt_eq_zero] at hzero
        rcases hzero with hnot | hval
        · exact hnot hgapA
        · exact hval hgap0
      have hm0 : m ≠ 0 := by
        intro hm0
        apply hne
        rw [← hm, hm0]
        rfl
      exact Nat.one_le_iff_ne_zero.mpr hm0
    have hordL : analyticOrderAt (gap ∘ f) 0 = ↑m * ↑k := by
      have hgapf : AnalyticAt ℂ gap (f 0) := by
        rw [hf0]
        exact hgapA
      rw [hgapf.analyticOrderAt_comp hf, hsubf, hf0, ← hm, hordf]
    have hQcomp : AnalyticAt ℂ (Q ∘ gap) 0 :=
      AnalyticAt.comp_of_eq hQa hgapA hgap0
    have hordQ : analyticOrderAt (Q ∘ gap) 0 = 0 := by
      rw [hQcomp.analyticOrderAt_eq_zero]
      change Q (gap 0) ≠ 0
      rw [hgap0]
      exact hQne
    have hordR : analyticOrderAt (gap * (Q ∘ gap)) 0 = ↑m := by
      rw [analyticOrderAt_mul hgapA hQcomp, hm, hordQ, add_zero]
    have hagree : analyticOrderAt (gap ∘ f) 0 =
        analyticOrderAt (gap * (Q ∘ gap)) 0 :=
      analyticOrderAt_congr hfactor
    rw [hordL, hordR, ← Nat.cast_mul] at hagree
    have hnat : m * k = m := ENat.natCast_inj.mp hagree
    have hk1 : k = 1 := by
      have hmul : m * k = m * 1 := by rw [hnat, Nat.mul_one]
      exact Nat.mul_left_cancel (by omega : 0 < m) hmul
    exact absurd hk1 (by omega)
