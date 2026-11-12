/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Set.Function
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Koenigs linearization at an attracting or repelling fixed point

Helpers for the germ conjugacy of `f(z) = λz + O(z²)` with multiplication by `λ`,
when `0 < ‖λ‖ ≠ 1`. The normalized coordinate is built from rescaled iterates in the
attracting case and transferred along a local inverse in the repelling case.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Finset Function Metric Set Topology

/-- A nonnegative real different from `1` has no positive power equal to `1`. -/
theorem pow_ne_one_of_ne_one {r : ℝ} {n : ℕ} (hr : 0 ≤ r) (h1 : r ≠ 1) (hn : n ≠ 0) :
    r ^ n ≠ 1 := by
  intro h
  by_cases hlt : r < 1
  · exact (pow_lt_one₀ hr hlt hn).ne h
  · exact ((one_lt_pow₀ (lt_of_le_of_ne (not_lt.mp hlt) h1.symm) hn).ne') h

/-- A positive real strictly less than `1` is strictly less than its square root. -/
theorem lt_sqrt_of_pos_of_lt_one {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : r < Real.sqrt r := by
  rw [Real.lt_sqrt hr0.le]
  have hmul : r * r < r * 1 := mul_lt_mul_of_pos_left hr1 hr0
  simpa [sq, mul_one] using hmul

/-- A ratio strictly between a positive real and its square root, when that real is below `1`. -/
theorem exists_between_self_and_sqrt {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ q : ℝ, r < q ∧ q < Real.sqrt r := by
  have hlt : r < Real.sqrt r := lt_sqrt_of_pos_of_lt_one hr0 hr1
  refine ⟨(r + Real.sqrt r) / 2, ?_, ?_⟩
  · rw [lt_div_iff₀ zero_lt_two]
    linarith
  · rw [div_lt_iff₀ zero_lt_two]
    linarith

/-- The rescaled quadratic weight in the Koenigs Cauchy estimate. -/
theorem koenigs_remainder_ratio (a q z : ℝ) (n : ℕ) :
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
theorem eventually_eq_zero_of_pow_mul_eq_zero {n : ℕ} {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
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
theorem exists_linear_factor {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
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

/-- Contraction, invariance, and quadratic remainder on a small disk about an attracting point. -/
theorem exists_attracting_disk {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (hc : deriv f 0 ≠ 0) (hlt : ‖deriv f 0‖ < 1) :
    ∃ q r C : ℝ, 0 < r ∧ 0 < C ∧ 0 < q ∧ q < 1 ∧ ‖deriv f 0‖ < q ∧ q ^ 2 < ‖deriv f 0‖ ∧
      DifferentiableOn ℂ f (ball 0 r) ∧ MapsTo f (ball 0 r) (ball 0 r) ∧
      ∀ z ∈ ball (0 : ℂ) r,
        ‖f z‖ ≤ q * ‖z‖ ∧ ‖f z - deriv f 0 * z‖ ≤ C * ‖z‖ ^ 2 := by
  let lam : ℂ := deriv f 0
  have hlam : lam = deriv f 0 := rfl
  have hpos : 0 < ‖lam‖ := norm_pos_iff.mpr (hlam ▸ hc)
  obtain ⟨q, hq_gt, hq_sqrt⟩ := exists_between_self_and_sqrt hpos (hlam ▸ hlt)
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

/-- Rescaled iterates converge to a normalized Koenigs coordinate when `‖f'(0)‖ < 1`. -/
theorem exists_koenigsCoordinate_of_norm_lt_one {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hf0 : f 0 = 0) (hc : deriv f 0 ≠ 0) (hlt : ‖deriv f 0‖ < 1) :
    ∃ phi : ℂ → ℂ, AnalyticAt ℂ phi 0 ∧ phi 0 = 0 ∧ deriv phi 0 = 1 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), phi (f z) = deriv f 0 * phi z := by
  obtain ⟨q, r, C, hr, hC, hq_pos, hq_lt_one, hq_gt, hq2, hdiff, hmaps, hball⟩ :=
    exists_attracting_disk hf hf0 hc hlt
  let lam : ℂ := deriv f 0
  have hlam : lam = deriv f 0 := rfl
  have hlam_ne : lam ≠ 0 := hlam ▸ hc
  have hpos : 0 < ‖lam‖ := norm_pos_iff.mpr hlam_ne
  let rho : ℝ := q ^ 2 / ‖lam‖
  have hrho_nonneg : 0 ≤ rho := div_nonneg (sq_nonneg _) (norm_nonneg _)
  have hrho_lt : rho < 1 := by
    rw [div_lt_one hpos]
    simpa [hlam] using hq2
  have hrho_mul : rho = q ^ 2 * ‖lam‖⁻¹ := by simp [rho, div_eq_mul_inv]
  let phiN : ℕ → ℂ → ℂ := fun n z ↦ lam⁻¹ ^ n * (f^[n]) z
  let D : ℕ → ℂ → ℂ := fun n z ↦ phiN (n + 1) z - phiN n z
  have hnorm_iter : ∀ n, ∀ z ∈ ball (0 : ℂ) r, ‖(f^[n]) z‖ ≤ q ^ n * ‖z‖ := by
    intro n
    induction n with
    | zero =>
        intro z hz
        simp [iterate_zero_apply, pow_zero]
    | succ n ih =>
        intro z hz
        rw [iterate_succ_apply']
        have hw : (f^[n]) z ∈ ball 0 r := (hmaps.iterate n) hz
        calc
          ‖f ((f^[n]) z)‖ ≤ q * ‖(f^[n]) z‖ := (hball _ hw).1
          _ ≤ q * (q ^ n * ‖z‖) :=
            mul_le_mul_of_nonneg_left (ih z hz) hq_pos.le
          _ = q ^ (n + 1) * ‖z‖ := by rw [← mul_assoc, ← pow_succ']
  have hDalg : ∀ n z,
      D n z = lam⁻¹ ^ (n + 1) * ((f^[n + 1]) z - lam * (f^[n]) z) := by
    intro n z
    have hcoef : lam⁻¹ ^ n = lam⁻¹ ^ (n + 1) * lam := by
      rw [pow_succ, mul_assoc, inv_mul_cancel₀ hlam_ne, mul_one]
    simp only [D, phiN]
    rw [hcoef]
    ring
  let K : ℝ := (C * ‖lam‖⁻¹) * r ^ 2
  have hDbound : ∀ n, ∀ z ∈ ball (0 : ℂ) r, ‖D n z‖ ≤ K * rho ^ n := by
    intro n z hz
    let w : ℂ := (f^[n]) z
    have hw : w ∈ ball 0 r := (hmaps.iterate n) hz
    have hz_norm : ‖z‖ < r := by simpa [mem_ball, dist_eq_norm, sub_zero] using hz
    have hw2 : ‖w‖ ^ 2 ≤ (q ^ n * ‖z‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hnorm_iter n z hz) 2
    have hz2 : ‖z‖ ^ 2 ≤ r ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hz_norm) 2
    have hmain : ‖D n z‖ ≤ ‖lam‖⁻¹ ^ (n + 1) * (C * ‖w‖ ^ 2) := by
      have hnonneg : 0 ≤ ‖lam‖⁻¹ ^ (n + 1) :=
        pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _
      calc
        ‖D n z‖ = ‖lam⁻¹ ^ (n + 1)‖ * ‖f w - lam * w‖ := by
          rw [hDalg, iterate_succ_apply', norm_mul]
        _ = ‖lam‖⁻¹ ^ (n + 1) * ‖f w - lam * w‖ := by rw [norm_pow, norm_inv]
        _ ≤ ‖lam‖⁻¹ ^ (n + 1) * (C * ‖w‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hball w hw).2 hnonneg
    have hreplace : ‖lam‖⁻¹ ^ (n + 1) * (C * ‖w‖ ^ 2) ≤
        ‖lam‖⁻¹ ^ (n + 1) * (C * (q ^ n * ‖z‖) ^ 2) := by
      have hnonneg : 0 ≤ ‖lam‖⁻¹ ^ (n + 1) :=
        pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _
      have hCnonneg : 0 ≤ C := hC.le
      have : C * ‖w‖ ^ 2 ≤ C * (q ^ n * ‖z‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hw2 hCnonneg
      exact mul_le_mul_of_nonneg_left this hnonneg
    have hid : ‖lam‖⁻¹ ^ (n + 1) * (C * (q ^ n * ‖z‖) ^ 2) =
        (C * ‖lam‖⁻¹) * (q ^ 2 * ‖lam‖⁻¹) ^ n * ‖z‖ ^ 2 := by
      have hratio := koenigs_remainder_ratio ‖lam‖ q ‖z‖ n
      calc
        ‖lam‖⁻¹ ^ (n + 1) * (C * (q ^ n * ‖z‖) ^ 2)
            = C * (‖lam‖⁻¹ ^ (n + 1) * (q ^ n * ‖z‖) ^ 2) := by ring
        _ = C * (‖lam‖⁻¹ * (q ^ 2 * ‖lam‖⁻¹) ^ n * ‖z‖ ^ 2) := by rw [hratio]
        _ = (C * ‖lam‖⁻¹) * (q ^ 2 * ‖lam‖⁻¹) ^ n * ‖z‖ ^ 2 := by ring
    have hlast : (C * ‖lam‖⁻¹) * (q ^ 2 * ‖lam‖⁻¹) ^ n * ‖z‖ ^ 2 ≤ K * rho ^ n := by
      rw [← hrho_mul]
      have hnonneg : 0 ≤ (C * ‖lam‖⁻¹) * rho ^ n :=
        mul_nonneg (mul_nonneg hC.le (inv_nonneg.mpr (norm_nonneg _)))
          (pow_nonneg hrho_nonneg _)
      calc
        (C * ‖lam‖⁻¹) * rho ^ n * ‖z‖ ^ 2
            = ((C * ‖lam‖⁻¹) * rho ^ n) * ‖z‖ ^ 2 := by ring
        _ ≤ ((C * ‖lam‖⁻¹) * rho ^ n) * r ^ 2 :=
          mul_le_mul_of_nonneg_left hz2 hnonneg
        _ = ((C * ‖lam‖⁻¹) * r ^ 2) * rho ^ n := by ring
        _ = K * rho ^ n := rfl
    exact le_trans hmain (le_trans hreplace (le_of_eq hid |>.trans hlast))
  have hu : Summable fun n : ℕ ↦ K * rho ^ n :=
    (summable_geometric_of_lt_one hrho_nonneg hrho_lt).mul_left K
  have hDon : ∀ n, DifferentiableOn ℂ (D n) (ball 0 r) := by
    intro n
    have hnext : DifferentiableOn ℂ (f^[n + 1]) (ball 0 r) := hdiff.iterate hmaps _
    have hthis : DifferentiableOn ℂ (f^[n]) (ball 0 r) := hdiff.iterate hmaps _
    have hsub : DifferentiableOn ℂ
        (fun z ↦ lam⁻¹ ^ (n + 1) * (f^[n + 1]) z - lam⁻¹ ^ n * (f^[n]) z) (ball 0 r) :=
      (hnext.const_mul (lam⁻¹ ^ (n + 1))).sub (hthis.const_mul (lam⁻¹ ^ n))
    exact hsub
  have hSdiff : DifferentiableOn ℂ (fun w ↦ ∑' n, D n w) (ball 0 r) :=
    Complex.differentiableOn_tsum_of_summable_norm hu hDon isOpen_ball
      fun n w hw ↦ hDbound n w hw
  let phi : ℂ → ℂ := fun z ↦ z + ∑' n, D n z
  have hphi_an : AnalyticAt ℂ phi 0 := by
    have hsum : DifferentiableOn ℂ (fun z ↦ z + ∑' n, D n z) (ball 0 r) :=
      differentiableOn_id.add hSdiff
    simpa [phi] using hsum.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hD0 : ∀ n, D n 0 = 0 := by
    intro n
    have hfix : (f^[n]) 0 = 0 := iterate_fixed hf0 n
    have hfix' : (f^[n + 1]) 0 = 0 := iterate_fixed hf0 (n + 1)
    unfold D phiN
    rw [hfix, hfix']
    simp
  have hS0 : (∑' n, D n 0) = 0 := by
    have hfun : (fun n ↦ D n 0) = fun _ : ℕ ↦ (0 : ℂ) := by
      ext n
      exact hD0 n
    rw [hfun]
    exact hasSum_zero.tsum_eq
  have hphi0 : phi 0 = 0 := by simp [phi, hS0]
  have hIter : ∀ n, HasDerivAt (f^[n]) (lam ^ n) 0 :=
    fun n ↦ HasDerivAt.iterate (x := 0) hf.differentiableAt.hasDerivAt hf0 n
  have hphiN : ∀ n, HasDerivAt (phiN n) 1 0 := by
    intro n
    have hmul : HasDerivAt (fun z ↦ lam⁻¹ ^ n * (f^[n]) z) (lam⁻¹ ^ n * lam ^ n) 0 :=
      (hIter n).const_mul (lam⁻¹ ^ n)
    have hcoeff : lam⁻¹ ^ n * lam ^ n = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hlam_ne, one_pow]
    rw [hcoeff] at hmul
    have hfun : (phiN n) = fun z ↦ lam⁻¹ ^ n * (f^[n]) z := rfl
    rw [hfun]
    exact hmul
  have hDderiv : ∀ n, deriv (D n) 0 = 0 := by
    intro n
    rw [show D n = phiN (n + 1) - phiN n by
      ext z
      rfl]
    rw [deriv_sub (hphiN (n + 1)).differentiableAt (hphiN n).differentiableAt]
    simp [(hphiN _).deriv]
  have hderivS : deriv (fun w ↦ ∑' n, D n w) 0 = 0 := by
    have hHas := Complex.hasSum_deriv_of_summable_norm hu hDon isOpen_ball
      (fun n w hw ↦ hDbound n w hw) (mem_ball_self hr)
    have hzero : HasSum (fun n : ℕ ↦ deriv (D n) 0) 0 := by
      simp [hDderiv]
    exact hHas.tsum_eq.symm.trans hzero.tsum_eq
  have hderiv_phi : deriv phi 0 = 1 := by
    have hSdiff0 : DifferentiableAt ℂ (fun w ↦ ∑' n, D n w) 0 :=
      (hSdiff 0 (mem_ball_self hr)).differentiableAt
        (isOpen_ball.mem_nhds (mem_ball_self hr))
    have hid : HasDerivAt (fun z : ℂ ↦ z) (1 : ℂ) 0 := hasDerivAt_id' 0
    have hadd : HasDerivAt (fun z ↦ z + ∑' n, D n z)
        (1 + deriv (fun w ↦ ∑' n, D n w) 0) 0 :=
      hid.add hSdiff0.hasDerivAt
    rw [show phi = fun z ↦ z + ∑' n, D n z by rfl, hadd.deriv, hderivS, add_zero]
  have hpartial : ∀ n z, ∑ i ∈ range n, D i z = phiN n z - z := by
    intro n z
    refine sum_range_induction (fun i ↦ D i z) (fun k ↦ phiN k z - z) ?_ n ?_
    · simp [phiN, pow_zero, iterate_zero_apply]
    · intro k hk
      simp only [D]
      ring
  have hlim : ∀ z ∈ ball (0 : ℂ) r, Tendsto (fun n ↦ phiN n z) atTop (𝓝 (phi z)) := by
    intro z hz
    have hsumz : Summable fun n ↦ D n z :=
      hu.of_norm_bounded fun n ↦ hDbound n z hz
    have ht : Tendsto (fun n ↦ (∑ i ∈ range n, D i z) + z) atTop
        (𝓝 ((∑' n, D n z) + z)) :=
      hsumz.tendsto_sum_tsum_nat.add tendsto_const_nhds
    have hfun : (fun n ↦ phiN n z) = fun n ↦ (∑ i ∈ range n, D i z) + z := by
      ext n
      rw [hpartial, sub_add_cancel]
    have hlimval : (∑' n, D n z) + z = phi z := by simp [phi, add_comm]
    simpa [hfun, hlimval] using ht
  have hstep : ∀ n z, phiN (n + 1) z = lam⁻¹ * phiN n (f z) := by
    intro n z
    simp only [phiN]
    rw [iterate_succ_apply, pow_succ', mul_assoc]
  have heq_ball : ∀ z ∈ ball (0 : ℂ) r, phi (f z) = lam * phi z := by
    intro z hz
    have hzf : f z ∈ ball 0 r := hmaps hz
    have hshift : Tendsto (fun n ↦ phiN (n + 1) z) atTop (𝓝 (phi z)) :=
      (hlim z hz).comp (tendsto_add_atTop_nat 1)
    have hright : Tendsto (fun n ↦ lam⁻¹ * phiN n (f z)) atTop
        (𝓝 (lam⁻¹ * phi (f z))) :=
      tendsto_const_nhds.mul (hlim (f z) hzf)
    have hright' : Tendsto (fun n ↦ phiN (n + 1) z) atTop (𝓝 (lam⁻¹ * phi (f z))) := by
      have hseq : (fun n ↦ phiN (n + 1) z) = fun n ↦ lam⁻¹ * phiN n (f z) := by
        ext n
        exact hstep n z
      simpa [hseq] using hright
    have hval : phi z = lam⁻¹ * phi (f z) := tendsto_nhds_unique hshift hright'
    calc
      phi (f z) = lam * (lam⁻¹ * phi (f z)) := by rw [mul_inv_cancel_left₀ hlam_ne]
      _ = lam * phi z := by rw [← hval]
  refine ⟨phi, hphi_an, hphi0, hderiv_phi, ?_⟩
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
  simpa [hlam] using heq_ball z hz

/-- A repelling fixed point is linearized by the attracting coordinate of a local inverse. -/
theorem exists_koenigsCoordinate_of_norm_gt_one {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hf0 : f 0 = 0) (hc : deriv f 0 ≠ 0) (hgt : 1 < ‖deriv f 0‖) :
    ∃ phi : ℂ → ℂ, AnalyticAt ℂ phi 0 ∧ phi 0 = 0 ∧ deriv phi 0 = 1 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), phi (f z) = deriv f 0 * phi z := by
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
  obtain ⟨psi, hpsi_an, hpsi0, hpsid, hpsie⟩ :=
    exists_koenigsCoordinate_of_norm_lt_one hg_an hg0 hdg_ne hdg_lt
  have hpsie' : ∀ᶠ w in 𝓝 (0 : ℂ), psi (g w) = lam⁻¹ * psi w := by
    filter_upwards [hpsie] with w hw
    rw [hw, hdg]
  have hleft : ∀ᶠ z in 𝓝 (0 : ℂ), g (f z) = z := by
    simpa [g] using hstrict.eventually_left_inverse hlam_ne
  have htend : Tendsto f (𝓝 (0 : ℂ)) (𝓝 0) := by
    have hcont : Tendsto f (𝓝 0) (𝓝 (f 0)) := hf.continuousAt.tendsto
    rwa [hf0] at hcont
  have hcomp : ∀ᶠ z in 𝓝 (0 : ℂ), psi (g (f z)) = lam⁻¹ * psi (f z) :=
    Filter.EventuallyEq.comp_tendsto hpsie' htend
  refine ⟨psi, hpsi_an, hpsi0, hpsid, ?_⟩
  filter_upwards [hleft, hcomp] with z hzleft hzcomp
  have hval : psi z = lam⁻¹ * psi (f z) := by simpa [hzleft] using hzcomp
  calc
    psi (f z) = lam * (lam⁻¹ * psi (f z)) := by rw [mul_inv_cancel_left₀ hlam_ne]
    _ = lam * psi z := by rw [← hval]
    _ = deriv f 0 * psi z := by rw [hlam]

/-- Two normalized Koenigs coordinates for the same multiplier agree as germs. -/
theorem koenigsCoordinate_eventuallyEq_of {f phi psi : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hunit : ‖c‖ ≠ 1) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) (hφa : AnalyticAt ℂ phi 0)
    (hφ0 : phi 0 = 0) (hφd : deriv phi 0 = 1)
    (hφe : ∀ᶠ z in 𝓝 (0 : ℂ), phi (f z) = c * phi z) (hψa : AnalyticAt ℂ psi 0)
    (hψ0 : psi 0 = 0) (hψd : deriv psi 0 = 1)
    (hψe : ∀ᶠ z in 𝓝 (0 : ℂ), psi (f z) = c * psi z) :
    phi =ᶠ[𝓝 (0 : ℂ)] psi := by
  let delta : ℂ → ℂ := phi - psi
  have hδa : AnalyticAt ℂ delta 0 := hφa.sub hψa
  have hδ0 : delta 0 = 0 := by simp [delta, hφ0, hψ0]
  have hδd : deriv delta 0 = 0 := by
    rw [deriv_sub hφa.differentiableAt hψa.differentiableAt, hφd, hψd, sub_self]
  have hδe : ∀ᶠ z in 𝓝 (0 : ℂ), delta (f z) = c * delta z := by
    filter_upwards [hφe, hψe] with z hzφ hzψ
    simp [delta, hzφ, hzψ, mul_sub]
  have hfc : deriv f 0 = c := by
    have hφdf : DifferentiableAt ℂ phi (f 0) := by
      simpa [hf0] using hφa.differentiableAt
    have hleft : deriv (phi ∘ f) 0 = deriv f 0 := by
      rw [deriv_comp (x := 0) hφdf hf.differentiableAt, hf0, hφd, one_mul]
    have hright : deriv (fun z ↦ c * phi z) 0 = c := by
      rw [deriv_const_mul c hφa.differentiableAt, hφd, mul_one]
    have heq : phi ∘ f =ᶠ[𝓝 (0 : ℂ)] fun z ↦ c * phi z := by
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
    obtain ⟨p, hp, hp0, hpf⟩ := exists_linear_factor hf hf0 (hfc ▸ hc)
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
    exact absurd hnorm <|
      pow_ne_one_of_ne_one (norm_nonneg _) hunit (by omega : m - 1 ≠ 0)

end CKMA
