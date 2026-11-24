/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic

import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.Order

/-!
# Koenigs linearization at an attracting or repelling fixed point

Helpers for the germ conjugacy of `f(z) = λz + O(z²)` with multiplication by `λ`,
when `0 < ‖λ‖ ≠ 1`. The normalized coordinate is built from rescaled iterates in the
attracting case and transferred along a local inverse in the repelling case.

## Main results

* `CKMA.exists_koenigsCoordinate_of_norm_lt_one`: existence of a Koenigs coordinate in the
  attracting case `0 < ‖deriv f 0‖ < 1`.
* `CKMA.exists_koenigsCoordinate_of_norm_gt_one`: existence of a Koenigs coordinate in the
  repelling case `1 < ‖deriv f 0‖`.
* `CKMA.koenigsCoordinate_eventuallyEq_of_analyticAt`: germ uniqueness of normalized Koenigs
  coordinates.
-/

public section

noncomputable section

namespace CKMA

open Filter Finset Function Metric Set Topology

/-- The rescaled quadratic weight in the Koenigs Cauchy estimate. -/
private theorem koenigs_remainder_ratio (a q z : ℝ) (n : ℕ) :
    a⁻¹ ^ (n + 1) * (q ^ n * z) ^ 2 = a⁻¹ * (q ^ 2 * a⁻¹) ^ n * z ^ 2 := by
  rw [pow_succ', mul_pow]
  have hq : (q ^ n) ^ 2 = (q ^ 2) ^ n := by
    rw [← pow_mul, ← pow_mul, mul_comm n 2]
  rw [hq]
  calc
    (a⁻¹ * a⁻¹ ^ n) * ((q ^ 2) ^ n * z ^ 2)
        = a⁻¹ * (a⁻¹ ^ n * (q ^ 2) ^ n) * z ^ 2 := by ring
    _ = a⁻¹ * (a⁻¹ * q ^ 2) ^ n * z ^ 2 := by rw [← mul_pow]
    _ = a⁻¹ * (q ^ 2 * a⁻¹) ^ n * z ^ 2 := by rw [mul_comm a⁻¹ (q ^ 2)]

/-- A holomorphic factor of an eventually vanishing monomial is eventually zero. -/
private theorem eventually_eq_zero_of_pow_mul_eq_zero {n : ℕ} {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (h : ∀ᶠ z in 𝓝 (0 : ℂ), z ^ n * F z = 0) : ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0 := by
  let powz : ℂ → ℂ := fun z ↦ z ^ n
  have hpow : AnalyticAt ℂ powz 0 := (analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) 0).pow n
  have htop : analyticOrderAt (powz * F) 0 = ⊤ :=
    analyticOrderAt_eq_top.mpr <| by simpa [powz, Pi.mul_apply] using h
  have hord : analyticOrderAt powz 0 = n := by
    rw [show powz = (id : ℂ → ℂ) ^ n by rfl, analyticOrderAt_pow analyticAt_id n,
      analyticOrderAt_id, nsmul_one]
  rw [analyticOrderAt_mul hpow hF, hord] at htop
  exact analyticOrderAt_eq_top.mp <|
    (ENat.add_eq_top.mp htop).resolve_left (ENat.natCast_ne_top n)

/-- A simple zero factors as the identity times a holomorphic function with the same derivative. -/
theorem exists_analyticAt_eventually_eq_mul {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (hf' : deriv f 0 ≠ 0) :
    ∃ p : ℂ → ℂ, AnalyticAt ℂ p 0 ∧ p 0 = deriv f 0 ∧ ∀ᶠ z in 𝓝 (0 : ℂ), f z = z * p z := by
  have hord : analyticOrderAt f 0 = 1 :=
    hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hf0 hf'
  obtain ⟨p, hp, hpne, hfp⟩ := hf.analyticOrderAt_eq_natCast.mp hord
  have hfeq : ∀ᶠ z in 𝓝 (0 : ℂ), f z = z * p z := by
    filter_upwards [hfp] with z hz
    simpa [sub_zero, pow_one, smul_eq_mul] using hz
  have hp0 : p 0 = deriv f 0 := by
    have hid : DifferentiableAt ℂ (fun z : ℂ ↦ z) 0 := differentiableAt_id
    have hmul : deriv (fun z ↦ z * p z) 0 = p 0 := by
      rw [deriv_fun_mul hid hp.differentiableAt, deriv_id'']
      simp
    exact hmul.symm.trans (Filter.EventuallyEq.deriv_eq hfeq).symm
  exact ⟨p, hp, hp0, hfeq⟩

@[deprecated (since := "2026-11-15")]
alias exists_linear_factor := exists_analyticAt_eventually_eq_mul

/-- Contraction, invariance, and quadratic remainder on a small disk about an attracting point. -/
private theorem exists_attracting_disk {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (hc : deriv f 0 ≠ 0) (hlt : ‖deriv f 0‖ < 1) :
    ∃ q r C : ℝ, 0 < r ∧ 0 < C ∧ 0 < q ∧ q < 1 ∧ ‖deriv f 0‖ < q ∧ q ^ 2 < ‖deriv f 0‖ ∧
      DifferentiableOn ℂ f (ball 0 r) ∧ MapsTo f (ball 0 r) (ball 0 r) ∧
      ∀ z ∈ ball (0 : ℂ) r,
        ‖f z‖ ≤ q * ‖z‖ ∧ ‖f z - deriv f 0 * z‖ ≤ C * ‖z‖ ^ 2 := by
  let lam : ℂ := deriv f 0
  have hlam : lam = deriv f 0 := rfl
  have hpos : 0 < ‖lam‖ := norm_pos_iff.mpr (hlam ▸ hc)
  obtain ⟨q, hq_gt, hq_sqrt⟩ :=
    exists_between (Real.lt_sqrt_self_iff.2 ⟨hpos.ne', hlam ▸ hlt⟩)
  have hq_pos : 0 < q := lt_trans hpos hq_gt
  have hsqrt_lt_one : Real.sqrt ‖lam‖ < 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt hpos.le (hlam ▸ hlt)
  have hq_lt_one : q < 1 := lt_trans hq_sqrt hsqrt_lt_one
  have hq2 : q ^ 2 < ‖lam‖ := by
    rw [← Real.sq_sqrt hpos.le]
    exact (sq_lt_sq₀ hq_pos.le (Real.sqrt_nonneg _)).mpr hq_sqrt
  let quad : ℂ → ℂ := fun z ↦ f z - lam * z
  have hqa : AnalyticAt ℂ quad 0 :=
    hf.sub ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ ↦ lam) 0).mul analyticAt_id)
  have hderiv_quad : deriv quad 0 = 0 := by
    have hlin : HasDerivAt (fun z : ℂ ↦ lam * z) lam 0 := hasDerivAt_const_mul lam
    rw [deriv_fun_sub hf.differentiableAt hlin.differentiableAt, hlin.deriv, hlam, sub_self]
  have hord : (2 : ℕ) ≤ analyticOrderAt quad 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hqa]
    intro i hi
    rcases i with _ | i
    · simp [iteratedDeriv_zero, quad, hf0]
    · rcases i with _ | i
      · simpa [iteratedDeriv_one] using hderiv_quad
      · omega
  obtain ⟨F, hFa, hFeq⟩ := (natCast_le_analyticOrderAt hqa).mp hord
  obtain ⟨δId, hδId, hId⟩ := Metric.eventually_nhds_iff_ball.mp hFeq
  obtain ⟨δF, hδF, hFclose⟩ := (Metric.continuousAt_iff.mp hFa.continuousAt) 1 zero_lt_one
  obtain ⟨pf, hpf⟩ := hf
  obtain ⟨δD, hδD, hdiff⟩ := Metric.eventually_nhds_iff_ball.mp hpf.eventually_differentiableAt
  let C : ℝ := ‖F 0‖ + 1
  have hC : 0 < C := add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
  let rLin : ℝ := (q - ‖lam‖) / C
  have hrLin_pos : 0 < rLin := div_pos (sub_pos.mpr hq_gt) hC
  let r : ℝ := min (min (min δId δF) δD) rLin
  have hr : 0 < r := lt_min (lt_min (lt_min hδId hδF) hδD) hrLin_pos
  have hrId : r ≤ δId := by
    refine le_trans (min_le_left _ _) ?_
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hrF : r ≤ δF := by
    refine le_trans (min_le_left _ _) ?_
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hrD : r ≤ δD := le_trans (min_le_left _ _) (min_le_right _ _)
  have hrL : r ≤ rLin := min_le_right _ _
  have hCr : C * r ≤ q - ‖lam‖ := by
    calc
      C * r ≤ C * ((q - ‖lam‖) / C) := mul_le_mul_of_nonneg_left hrL hC.le
      _ = q - ‖lam‖ := mul_div_cancel₀ _ hC.ne'
  have hFest : ∀ z ∈ ball (0 : ℂ) r, ‖F z‖ ≤ C := by
    intro z hz
    have hzF : dist z 0 < δF := by
      rw [dist_eq_norm, sub_zero]
      exact lt_of_lt_of_le (by simpa [mem_ball, dist_eq_norm, sub_zero] using hz) hrF
    have hclose : ‖F z - F 0‖ < 1 := by
      rw [← dist_eq_norm]
      exact hFclose hzF
    have htri : ‖F z‖ ≤ ‖F z - F 0‖ + ‖F 0‖ := by
      simpa [sub_add_cancel] using norm_add_le (F z - F 0) (F 0)
    have hltF : ‖F z‖ < C := by
      have hsum : ‖F z - F 0‖ + ‖F 0‖ < 1 + ‖F 0‖ := by linarith
      calc
        ‖F z‖ ≤ ‖F z - F 0‖ + ‖F 0‖ := htri
        _ < 1 + ‖F 0‖ := hsum
        _ = C := by rw [add_comm]
    exact hltF.le
  have hIdBall : ∀ z ∈ ball (0 : ℂ) r, f z - lam * z = z ^ 2 * F z := by
    intro z hz
    have hzId : z ∈ ball 0 δId := ball_subset_ball hrId hz
    have hzEq := hId z hzId
    simpa [quad, sub_zero, pow_two, smul_eq_mul] using hzEq
  have hquad : ∀ z ∈ ball (0 : ℂ) r, ‖f z - lam * z‖ ≤ C * ‖z‖ ^ 2 := by
    intro z hz
    rw [hIdBall z hz, norm_mul, norm_pow]
    calc
      ‖z‖ ^ 2 * ‖F z‖ ≤ ‖z‖ ^ 2 * C :=
        mul_le_mul_of_nonneg_left (hFest z hz) (sq_nonneg _)
      _ = C * ‖z‖ ^ 2 := mul_comm _ _
  have hcontr : ∀ z ∈ ball (0 : ℂ) r, ‖f z‖ ≤ q * ‖z‖ := by
    intro z hz
    have hz_norm : ‖z‖ < r := by simpa [mem_ball, dist_eq_norm, sub_zero] using hz
    have htri : ‖f z‖ ≤ ‖f z - lam * z‖ + ‖lam‖ * ‖z‖ := by
      have hsum : ‖f z‖ ≤ ‖f z - lam * z‖ + ‖lam * z‖ := by
        simpa [sub_add_cancel] using norm_add_le (f z - lam * z) (lam * z)
      simpa [norm_mul] using hsum
    calc
      ‖f z‖ ≤ ‖f z - lam * z‖ + ‖lam‖ * ‖z‖ := htri
      _ ≤ C * ‖z‖ ^ 2 + ‖lam‖ * ‖z‖ := by linarith [hquad z hz]
      _ = (C * ‖z‖ + ‖lam‖) * ‖z‖ := by ring
      _ ≤ (C * r + ‖lam‖) * ‖z‖ := by
        have hzle : ‖z‖ ≤ r := le_of_lt hz_norm
        have hmul : C * ‖z‖ ≤ C * r := mul_le_mul_of_nonneg_left hzle hC.le
        have hsum : C * ‖z‖ + ‖lam‖ ≤ C * r + ‖lam‖ := by linarith
        exact mul_le_mul_of_nonneg_right hsum (norm_nonneg z)
      _ ≤ q * ‖z‖ := by
        have hsum : C * r + ‖lam‖ ≤ q := by linarith
        exact mul_le_mul_of_nonneg_right hsum (norm_nonneg z)
  have hmaps : MapsTo f (ball 0 r) (ball 0 r) := by
    intro z hz
    have hz_norm : ‖z‖ < r := by simpa [mem_ball, dist_eq_norm, sub_zero] using hz
    have hltq : q * ‖z‖ < r := by
      calc
        q * ‖z‖ < q * r := mul_lt_mul_of_pos_left hz_norm hq_pos
        _ < 1 * r := mul_lt_mul_of_pos_right hq_lt_one hr
        _ = r := one_mul r
    rw [mem_ball, dist_eq_norm, sub_zero]
    exact lt_of_le_of_lt (hcontr z hz) hltq
  have hdiffOn : DifferentiableOn ℂ f (ball 0 r) := by
    intro z hz
    exact (hdiff z (ball_subset_ball hrD hz)).differentiableWithinAt
  refine ⟨q, r, C, hr, hC, hq_pos, hq_lt_one, ?_, ?_, hdiffOn, hmaps, ?_⟩
  · simpa [hlam] using hq_gt
  · simpa [hlam] using hq2
  · intro z hz
    refine ⟨hcontr z hz, ?_⟩
    simpa [hlam] using hquad z hz

/-- Iterates of a map that contracts the norm by `q` on an invariant set contract by `q ^ n`. -/
private theorem norm_iterate_le_pow_mul {f : ℂ → ℂ} {s : Set ℂ} {q : ℝ} (hq : 0 ≤ q)
    (hmaps : MapsTo f s s) (hf : ∀ z ∈ s, ‖f z‖ ≤ q * ‖z‖) (n : ℕ) {z : ℂ} (hz : z ∈ s) :
    ‖(f^[n]) z‖ ≤ q ^ n * ‖z‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply']
    calc
      ‖f ((f^[n]) z)‖ ≤ q * ‖(f^[n]) z‖ := hf _ ((hmaps.iterate n) hz)
      _ ≤ q * (q ^ n * ‖z‖) := mul_le_mul_of_nonneg_left ih hq
      _ = q ^ (n + 1) * ‖z‖ := by rw [← mul_assoc, ← pow_succ']

/-- Consecutive rescaled iterates `λ⁻ⁿ fⁿ` on the attracting disk differ by a geometric
quantity with ratio `q ^ 2 / ‖λ‖`. -/
private theorem norm_inv_pow_mul_iterate_sub_le {f : ℂ → ℂ} {lam : ℂ} {q r C : ℝ}
    (hlam : lam ≠ 0) (hC : 0 < C) (hq : 0 < q) (hmaps : MapsTo f (ball 0 r) (ball 0 r))
    (hball : ∀ z ∈ ball (0 : ℂ) r, ‖f z‖ ≤ q * ‖z‖ ∧ ‖f z - lam * z‖ ≤ C * ‖z‖ ^ 2)
    (n : ℕ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) :
    ‖lam⁻¹ ^ (n + 1) * (f^[n + 1]) z - lam⁻¹ ^ n * (f^[n]) z‖ ≤
      C * ‖lam‖⁻¹ * r ^ 2 * (q ^ 2 / ‖lam‖) ^ n := by
  have hw : (f^[n]) z ∈ ball (0 : ℂ) r := (hmaps.iterate n) hz
  have hiter : ‖(f^[n]) z‖ ^ 2 ≤ (q ^ n * ‖z‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _)
      (norm_iterate_le_pow_mul hq.le hmaps (fun w hw ↦ (hball w hw).1) n hz) 2
  have hz2 : ‖z‖ ^ 2 ≤ r ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (mem_ball_zero_iff.mp hz).le 2
  have hcoef : lam⁻¹ ^ n = lam⁻¹ ^ (n + 1) * lam := by
    rw [pow_succ, mul_assoc, inv_mul_cancel₀ hlam, mul_one]
  have halg : lam⁻¹ ^ (n + 1) * (f^[n + 1]) z - lam⁻¹ ^ n * (f^[n]) z =
      lam⁻¹ ^ (n + 1) * (f ((f^[n]) z) - lam * (f^[n]) z) := by
    rw [iterate_succ_apply', hcoef]
    ring
  have hnonneg : 0 ≤ ‖lam‖⁻¹ ^ (n + 1) := pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _
  have hfac : 0 ≤ C * ‖lam‖⁻¹ * (q ^ 2 / ‖lam‖) ^ n :=
    mul_nonneg (mul_nonneg hC.le (inv_nonneg.mpr (norm_nonneg _)))
      (pow_nonneg (div_nonneg (sq_nonneg _) (norm_nonneg _)) _)
  calc
    ‖lam⁻¹ ^ (n + 1) * (f^[n + 1]) z - lam⁻¹ ^ n * (f^[n]) z‖
        = ‖lam‖⁻¹ ^ (n + 1) * ‖f ((f^[n]) z) - lam * (f^[n]) z‖ := by
          rw [halg, norm_mul, norm_pow, norm_inv]
    _ ≤ ‖lam‖⁻¹ ^ (n + 1) * (C * (q ^ n * ‖z‖) ^ 2) :=
          mul_le_mul_of_nonneg_left
            ((hball _ hw).2.trans (mul_le_mul_of_nonneg_left hiter hC.le)) hnonneg
    _ = C * (‖lam‖⁻¹ ^ (n + 1) * (q ^ n * ‖z‖) ^ 2) := by ring
    _ = C * ‖lam‖⁻¹ * (q ^ 2 / ‖lam‖) ^ n * ‖z‖ ^ 2 := by
          rw [koenigs_remainder_ratio, div_eq_mul_inv]
          ring
    _ ≤ C * ‖lam‖⁻¹ * (q ^ 2 / ‖lam‖) ^ n * r ^ 2 := mul_le_mul_of_nonneg_left hz2 hfac
    _ = C * ‖lam‖⁻¹ * r ^ 2 * (q ^ 2 / ‖lam‖) ^ n := by ring

/-- The rescaled iterate `λ⁻ⁿ fⁿ` has derivative one at the fixed point, where `λ = f'(0)`. -/
private theorem hasDerivAt_inv_pow_mul_iterate {f : ℂ → ℂ} (hf : DifferentiableAt ℂ f 0)
    (hf0 : f 0 = 0) (hc : deriv f 0 ≠ 0) (n : ℕ) :
    HasDerivAt (fun z ↦ (deriv f 0)⁻¹ ^ n * (f^[n]) z) 1 0 := by
  have hmul := (HasDerivAt.iterate (x := 0) hf.hasDerivAt hf0 n).const_mul ((deriv f 0)⁻¹ ^ n)
  rwa [← mul_pow, inv_mul_cancel₀ hc, one_pow] at hmul

/-- A pointwise limit of maps satisfying `φₙ₊₁ = λ⁻¹ • (φₙ ∘ f)` on an invariant set
conjugates `f` to multiplication by `λ` there. -/
private theorem eq_mul_of_tendsto_of_succ_eq {f φ : ℂ → ℂ} {phi : ℕ → ℂ → ℂ} {s : Set ℂ}
    {lam : ℂ} (hlam : lam ≠ 0) (hmaps : MapsTo f s s)
    (hstep : ∀ n z, phi (n + 1) z = lam⁻¹ * phi n (f z))
    (hlim : ∀ z ∈ s, Tendsto (fun n ↦ phi n z) atTop (𝓝 (φ z))) {z : ℂ} (hz : z ∈ s) :
    φ (f z) = lam * φ z := by
  have hshift : Tendsto (fun n ↦ phi (n + 1) z) atTop (𝓝 (φ z)) :=
    (hlim z hz).comp (tendsto_add_atTop_nat 1)
  have hright : Tendsto (fun n ↦ phi (n + 1) z) atTop (𝓝 (lam⁻¹ * φ (f z))) := by
    simp only [hstep]
    exact (tendsto_const_nhds (x := lam⁻¹)).mul (hlim (f z) (hmaps hz))
  rw [tendsto_nhds_unique hshift hright, mul_inv_cancel_left₀ hlam]

/-- Rescaled iterates converge to a normalized Koenigs coordinate when `‖f'(0)‖ < 1`. -/
theorem exists_koenigsCoordinate_of_norm_lt_one {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hf0 : f 0 = 0) (hc : deriv f 0 ≠ 0) (hlt : ‖deriv f 0‖ < 1) :
    ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ 0 ∧ φ 0 = 0 ∧ deriv φ 0 = 1 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), φ (f z) = deriv f 0 * φ z := by
  obtain ⟨q, r, C, hr, hC, hq_pos, -, -, hq2, hdiff, hmaps, hball⟩ :=
    exists_attracting_disk hf hf0 hc hlt
  have hphiN : ∀ n, HasDerivAt (fun z ↦ (deriv f 0)⁻¹ ^ n * (f^[n]) z) 1 0 :=
    hasDerivAt_inv_pow_mul_iterate hf.differentiableAt hf0 hc
  set lam : ℂ := deriv f 0
  have hpos : 0 < ‖lam‖ := norm_pos_iff.mpr hc
  let rho : ℝ := q ^ 2 / ‖lam‖
  have hrho_nonneg : 0 ≤ rho := div_nonneg (sq_nonneg _) (norm_nonneg _)
  have hrho_lt : rho < 1 := (div_lt_one hpos).mpr hq2
  let phiN : ℕ → ℂ → ℂ := fun n z ↦ lam⁻¹ ^ n * (f^[n]) z
  let D : ℕ → ℂ → ℂ := fun n z ↦ phiN (n + 1) z - phiN n z
  let K : ℝ := C * ‖lam‖⁻¹ * r ^ 2
  have hDbound : ∀ n, ∀ z ∈ ball (0 : ℂ) r, ‖D n z‖ ≤ K * rho ^ n :=
    fun n _ hz ↦ norm_inv_pow_mul_iterate_sub_le hc hC hq_pos hmaps hball n hz
  have hu : Summable fun n : ℕ ↦ K * rho ^ n :=
    (summable_geometric_of_lt_one hrho_nonneg hrho_lt).mul_left K
  have hDon : ∀ n, DifferentiableOn ℂ (D n) (ball 0 r) := fun n ↦
    ((hdiff.iterate hmaps _).const_mul (lam⁻¹ ^ (n + 1))).sub
      ((hdiff.iterate hmaps _).const_mul (lam⁻¹ ^ n))
  have hSdiff : DifferentiableOn ℂ (fun w ↦ ∑' n, D n w) (ball 0 r) :=
    Complex.differentiableOn_tsum_of_summable_norm hu hDon isOpen_ball
      fun n w hw ↦ hDbound n w hw
  let φ : ℂ → ℂ := fun z ↦ z + ∑' n, D n z
  have hphi_an : AnalyticAt ℂ φ 0 :=
    (differentiableOn_id.add hSdiff).analyticAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hD0 : ∀ n, D n 0 = 0 := fun n ↦ by
    simp only [D, phiN, iterate_fixed hf0, mul_zero, sub_self]
  have hphi0 : φ 0 = 0 := by simp [φ, hD0]
  have hderivS : deriv (fun w ↦ ∑' n, D n w) 0 = 0 := by
    have hHas := Complex.hasSum_deriv_of_summable_norm hu hDon isOpen_ball
      (fun n w hw ↦ hDbound n w hw) (mem_ball_self hr)
    have hDderiv : ∀ n, deriv (D n) 0 = 0 := fun n ↦
      ((hphiN (n + 1)).sub (hphiN n)).deriv.trans (sub_self 1)
    have hzero : HasSum (fun n : ℕ ↦ deriv (D n) 0) 0 := by
      simp [hDderiv]
    exact hHas.tsum_eq.symm.trans hzero.tsum_eq
  have hderiv_phi : deriv φ 0 = 1 := by
    have hadd : HasDerivAt φ (1 + deriv (fun w ↦ ∑' n, D n w) 0) 0 :=
      (hasDerivAt_id' 0).add ((hSdiff 0 (mem_ball_self hr)).differentiableAt
        (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt
    rw [hadd.deriv, hderivS, add_zero]
  have hpartial : ∀ n z, ∑ i ∈ range n, D i z = phiN n z - z := by
    intro n z
    refine sum_range_induction (fun i ↦ D i z) (fun k ↦ phiN k z - z) ?_ n ?_
    · simp [phiN, pow_zero, iterate_zero_apply]
    · intro k _
      simp only [D]
      ring
  have hlim : ∀ z ∈ ball (0 : ℂ) r, Tendsto (fun n ↦ phiN n z) atTop (𝓝 (φ z)) := by
    intro z hz
    have ht : Tendsto (fun n ↦ (∑ i ∈ range n, D i z) + z) atTop
        (𝓝 ((∑' n, D n z) + z)) :=
      (hu.of_norm_bounded fun n ↦ hDbound n z hz).tendsto_sum_tsum_nat.add tendsto_const_nhds
    have hfun : (fun n ↦ phiN n z) = fun n ↦ (∑ i ∈ range n, D i z) + z := by
      ext n
      rw [hpartial, sub_add_cancel]
    have hlimval : (∑' n, D n z) + z = φ z := by simp [φ, add_comm]
    simpa [hfun, hlimval] using ht
  have hstep : ∀ n z, phiN (n + 1) z = lam⁻¹ * phiN n (f z) := by
    intro n z
    simp only [phiN]
    rw [iterate_succ_apply, pow_succ', mul_assoc]
  refine ⟨φ, hphi_an, hphi0, hderiv_phi, ?_⟩
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
  exact eq_mul_of_tendsto_of_succ_eq hc hmaps hstep hlim hz

/-- A repelling fixed point is linearized by the attracting coordinate of a local inverse. -/
theorem exists_koenigsCoordinate_of_norm_gt_one {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hf0 : f 0 = 0) (hc : deriv f 0 ≠ 0) (hgt : 1 < ‖deriv f 0‖) :
    ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ 0 ∧ φ 0 = 0 ∧ deriv φ 0 = 1 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), φ (f z) = deriv f 0 * φ z := by
  let lam : ℂ := deriv f 0
  have hlam : lam = deriv f 0 := rfl
  have hlam_ne : lam ≠ 0 := hlam ▸ hc
  let hstrict : HasStrictDerivAt f lam 0 := by
    simpa [hlam] using hf.hasStrictDerivAt
  let g : ℂ → ℂ := hstrict.localInverse f lam 0 hlam_ne
  have hg_an : AnalyticAt ℂ g 0 := by
    simpa [g, hf0] using hf.analyticAt_localInverse (hlam ▸ hc)
  have hg0 : g 0 = 0 := by
    have hleft := hstrict.eventually_left_inverse hlam_ne
    simpa [g, hf0] using hleft.self_of_nhds
  have hdg : deriv g 0 = lam⁻¹ := by
    have hgderiv := hstrict.to_localInverse hlam_ne
    simpa [g, hf0] using hgderiv.hasDerivAt.deriv
  have hdg_ne : deriv g 0 ≠ 0 := by
    rw [hdg]
    exact inv_ne_zero hlam_ne
  have hdg_lt : ‖deriv g 0‖ < 1 := by
    rw [hdg, norm_inv]
    exact inv_lt_one_of_one_lt₀ (hlam ▸ hgt)
  obtain ⟨ψ, hpsi_an, hpsi0, hpsid, hpsie⟩ :=
    exists_koenigsCoordinate_of_norm_lt_one hg_an hg0 hdg_ne hdg_lt
  have hpsie' : ∀ᶠ w in 𝓝 (0 : ℂ), ψ (g w) = lam⁻¹ * ψ w := by
    filter_upwards [hpsie] with w hw
    rw [hw, hdg]
  have hleft : ∀ᶠ z in 𝓝 (0 : ℂ), g (f z) = z := by
    simpa [g] using hstrict.eventually_left_inverse hlam_ne
  have htend : Tendsto f (𝓝 (0 : ℂ)) (𝓝 0) := by
    have hcont : Tendsto f (𝓝 0) (𝓝 (f 0)) := hf.continuousAt.tendsto
    rwa [hf0] at hcont
  have hcomp : ∀ᶠ z in 𝓝 (0 : ℂ), ψ (g (f z)) = lam⁻¹ * ψ (f z) :=
    Filter.EventuallyEq.comp_tendsto hpsie' htend
  refine ⟨ψ, hpsi_an, hpsi0, hpsid, ?_⟩
  filter_upwards [hleft, hcomp] with z hzleft hzcomp
  have hval : ψ z = lam⁻¹ * ψ (f z) := by simpa [hzleft] using hzcomp
  calc
    ψ (f z) = lam * (lam⁻¹ * ψ (f z)) := by rw [mul_inv_cancel_left₀ hlam_ne]
    _ = lam * ψ z := by rw [← hval]
    _ = deriv f 0 * ψ z := by rw [hlam]

/-- Two normalized Koenigs coordinates for the same multiplier agree as germs. -/
theorem koenigsCoordinate_eventuallyEq_of_analyticAt {f φ ψ : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hunit : ‖c‖ ≠ 1) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) (hφa : AnalyticAt ℂ φ 0)
    (hφ0 : φ 0 = 0) (hφd : deriv φ 0 = 1)
    (hφe : ∀ᶠ z in 𝓝 (0 : ℂ), φ (f z) = c * φ z) (hψa : AnalyticAt ℂ ψ 0)
    (hψ0 : ψ 0 = 0) (hψd : deriv ψ 0 = 1)
    (hψe : ∀ᶠ z in 𝓝 (0 : ℂ), ψ (f z) = c * ψ z) :
    φ =ᶠ[𝓝 (0 : ℂ)] ψ := by
  let delta : ℂ → ℂ := φ - ψ
  have hδa : AnalyticAt ℂ delta 0 := hφa.sub hψa
  have hδ0 : delta 0 = 0 := by simp [delta, hφ0, hψ0]
  have hδd : deriv delta 0 = 0 := by
    rw [deriv_sub hφa.differentiableAt hψa.differentiableAt, hφd, hψd, sub_self]
  have hδe : ∀ᶠ z in 𝓝 (0 : ℂ), delta (f z) = c * delta z := by
    filter_upwards [hφe, hψe] with z hzφ hzψ
    simp [delta, hzφ, hzψ, mul_sub]
  have hfc : deriv f 0 = c := by
    have hφdf : DifferentiableAt ℂ φ (f 0) := by
      simpa [hf0] using hφa.differentiableAt
    have hleft : deriv (φ ∘ f) 0 = deriv f 0 := by
      rw [deriv_comp (x := 0) hφdf hf.differentiableAt, hf0, hφd, one_mul]
    have hright : deriv (fun z ↦ c * φ z) 0 = c := by
      rw [deriv_const_mul c hφa.differentiableAt, hφd, mul_one]
    have heq : φ ∘ f =ᶠ[𝓝 (0 : ℂ)] fun z ↦ c * φ z := by
      filter_upwards [hφe] with z hz
      exact hz
    exact hleft.symm.trans ((Filter.EventuallyEq.deriv_eq heq).trans hright)
  have htwo : (2 : ℕ) ≤ analyticOrderAt delta 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hδa]
    intro i hi
    rcases i with _ | i
    · simpa [iteratedDeriv_zero] using hδ0
    · rcases i with _ | i
      · simpa [iteratedDeriv_one] using hδd
      · omega
  by_cases htop : analyticOrderAt delta 0 = ⊤
  · filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
    exact sub_eq_zero.mp (by simpa [delta] using hz)
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
    have hm2 : 2 ≤ m := by
      have hle : (2 : ℕ∞) ≤ m := by simpa [hm] using htwo
      exact_mod_cast hle
    obtain ⟨rem, hrem, hrem0, hδfac⟩ := hδa.analyticOrderAt_eq_natCast.mp hm.symm
    have hfac : ∀ᶠ z in 𝓝 (0 : ℂ), delta z = z ^ m * rem z := by
      filter_upwards [hδfac] with z hz
      simpa [sub_zero, smul_eq_mul] using hz
    obtain ⟨p, hp, hp0, hpf⟩ := exists_analyticAt_eventually_eq_mul hf hf0 (hfc ▸ hc)
    have hp0' : p 0 = c := by rw [hp0, hfc]
    have htend : Tendsto f (𝓝 (0 : ℂ)) (𝓝 0) := by
      have hcont : Tendsto f (𝓝 0) (𝓝 (f 0)) := hf.continuousAt.tendsto
      rwa [hf0] at hcont
    have hfacf : ∀ᶠ z in 𝓝 (0 : ℂ), delta (f z) = (f z) ^ m * rem (f z) :=
      Filter.EventuallyEq.comp_tendsto hfac htend
    let R : ℂ → ℂ := fun z ↦ (p z) ^ m * rem (f z) - c * rem z
    have hRa : AnalyticAt ℂ R 0 :=
      ((hp.pow m).mul (AnalyticAt.comp_of_eq hrem hf hf0)).sub (analyticAt_const.mul hrem)
    have hRz : ∀ᶠ z in 𝓝 (0 : ℂ), z ^ m * R z = 0 := by
      filter_upwards [hδe, hfac, hfacf, hpf] with z hzδ hzfac hzfacf hzpf
      have hpow : (f z) ^ m = (z * p z) ^ m := by rw [hzpf]
      have h1 : (f z) ^ m * rem (f z) = c * (z ^ m * rem z) := by
        rw [← hzfacf, hzδ, hzfac]
      rw [hpow] at h1
      have halg : (z * p z) ^ m * rem (f z) - c * (z ^ m * rem z) =
          z ^ m * R z := by
        simp only [R]
        ring
      rw [← halg, h1, sub_self]
    have hR0 : R 0 = 0 := (eventually_eq_zero_of_pow_mul_eq_zero hRa hRz).self_of_nhds
    have hcm : c ^ m = c := by
      have hval : c ^ m * rem 0 - c * rem 0 = 0 := by
        simpa [R, hf0, hp0'] using hR0
      have hprod : (c ^ m - c) * rem 0 = 0 := by
        simpa [sub_mul] using hval
      have hsub : c ^ m - c = 0 := by
        exact (mul_eq_zero.mp hprod).resolve_right hrem0
      exact sub_eq_zero.mp hsub
    have hpow : c ^ (m - 1) = 1 := by
      apply mul_right_cancel₀ hc
      calc
        c ^ (m - 1) * c = c ^ m := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega)]
        _ = c := hcm
        _ = 1 * c := (one_mul c).symm
    have hnorm : ‖c‖ ^ (m - 1) = 1 := by
      rw [← norm_pow, hpow, norm_one]
    exact absurd ((pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega : m - 1 ≠ 0)).1 hnorm) hunit

@[deprecated (since := "2026-11-15")]
alias koenigsCoordinate_eventuallyEq_of := koenigsCoordinate_eventuallyEq_of_analyticAt

end CKMA
