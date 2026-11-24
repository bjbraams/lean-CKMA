/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic

import CKMA.Dynamics.Complex.Linearization.Koenigs
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.Order

/-!
# Böttcher coordinate at a superattracting fixed point

Helpers for a germ `f(z) = z ^ k * g(z)` with `k ≥ 2` and `g 0 ≠ 0`. The coordinate is
`φ(z) = c * z * exp (S z)`, where `S` sums the branched logarithm of `g` along the orbit,
and `c ^ (k - 1) = g 0`.

## Main results

* `CKMA.exists_boettcherCoordinate_of_analyticAt`: existence of a local analytic Böttcher
  coordinate with prescribed compatible leading coefficient.
* `CKMA.boettcherCoordinate_eq_mul_unity`: uniqueness of Böttcher coordinates up to a `(k - 1)`st
  root of unity.
-/

public section

noncomputable section

namespace CKMA

open Filter Finset Function Metric Set Topology

/-- Binomial expansion of `(ζ + w) ^ k - ζ` when `ζ ^ k = ζ`. -/
private theorem exists_pow_sub_factor {ζ : ℂ} {k : ℕ} (hk : 1 ≤ k) (hpow : ζ ^ k = ζ) :
    ∃ Q : ℂ → ℂ, AnalyticAt ℂ Q 0 ∧ Q 0 = (k : ℂ) * ζ ^ (k - 1) ∧
      ∀ w : ℂ, (ζ + w) ^ k - ζ = w * Q w := by
  let term : ℕ → ℂ → ℂ := fun m w ↦
    (k.choose m : ℂ) * ζ ^ m * w ^ (k - 1 - m)
  let Q : ℂ → ℂ := fun w ↦ ∑ m ∈ range k, term m w
  have hterm : ∀ m, AnalyticAt ℂ (term m) 0 := by
    intro m
    have hconst : AnalyticAt ℂ (fun _ : ℂ ↦ (k.choose m : ℂ) * ζ ^ m) 0 :=
      analyticAt_const
    exact hconst.mul ((analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) 0).pow _)
  have hQa : AnalyticAt ℂ Q 0 :=
    Finset.analyticAt_fun_sum (range k) fun m _ ↦ hterm m
  have hchoose : k.choose (k - 1) = k := by
    rw [Nat.choose_symm (by omega : 1 ≤ k), Nat.choose_one_right]
  have hQ0 : Q 0 = (k : ℂ) * ζ ^ (k - 1) := by
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
  have hbin := add_pow ζ w k
  rw [sum_range_succ] at hbin
  have hlast : ζ ^ k * w ^ (k - k) * (k.choose k : ℂ) = ζ ^ k := by
    simp [Nat.choose_self, pow_zero]
  have hfactor : ∑ m ∈ range k, ζ ^ m * w ^ (k - m) * (k.choose m : ℂ) = w * Q w := by
    rw [show Q w = ∑ m ∈ range k, term m w by rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    have hmlt : m < k := mem_range.mp hm
    have hexp : k - m = (k - 1 - m) + 1 := by omega
    calc
      ζ ^ m * w ^ (k - m) * (k.choose m : ℂ)
          = ζ ^ m * (w ^ (k - 1 - m) * w) * (k.choose m : ℂ) := by
            rw [hexp, pow_succ]
      _ = w * ((k.choose m : ℂ) * ζ ^ m * w ^ (k - 1 - m)) := by ring
      _ = w * term m w := by rfl
  calc
    (ζ + w) ^ k - ζ
        = (∑ m ∈ range k, ζ ^ m * w ^ (k - m) * (k.choose m : ℂ)) + ζ ^ k - ζ := by
          rw [hbin, hlast]
    _ = w * Q w + ζ ^ k - ζ := by rw [hfactor]
    _ = w * Q w := by rw [hpow, add_sub_cancel_right]

/-- A disk of radius at most `1` and `1 / (2M)` is mapped into itself by `z ^ k * g z` when
`k ≥ 2` and `‖g‖ ≤ M` on it. -/
private theorem mapsTo_ball_of_eq_pow_mul {f g : ℂ → ℂ} {k : ℕ} (hk : 2 ≤ k) {r M : ℝ}
    (hM : 0 < M) (hr1 : r ≤ 1) (hrM : M * r ≤ 1 / 2)
    (hfeq : ∀ z ∈ ball (0 : ℂ) r, f z = z ^ k * g z) (hg : ∀ z ∈ ball (0 : ℂ) r, ‖g z‖ ≤ M) :
    MapsTo f (ball 0 r) (ball 0 r) := by
  intro z hz
  have hzr : ‖z‖ < r := mem_ball_zero_iff.mp hz
  have hpow : ‖z‖ ^ k ≤ ‖z‖ ^ 2 := pow_le_pow_of_le_one (norm_nonneg _) (hzr.le.trans hr1) hk
  have hMz : M * ‖z‖ ≤ 1 / 2 := (mul_le_mul_of_nonneg_left hzr.le hM.le).trans hrM
  have hhalf := mul_le_mul_of_nonneg_left hMz (norm_nonneg z)
  rw [mem_ball_zero_iff, hfeq z hz, norm_mul, norm_pow]
  calc
    ‖z‖ ^ k * ‖g z‖ ≤ ‖z‖ ^ 2 * M := mul_le_mul hpow (hg z hz) (norm_nonneg _) (by positivity)
    _ < r := by nlinarith [norm_nonneg z]

/-- A small invariant disk for a superattracting germ `z ^ k * g z`, on which `g / g 0` stays
in the slit plane and its principal logarithm has norm less than one. -/
private theorem exists_boettcher_disk {f g : ℂ → ℂ} {k : ℕ} (hk : 2 ≤ k) (hg : AnalyticAt ℂ g 0)
    (hg₀ : g 0 ≠ 0) (hf : ∀ᶠ z in 𝓝 (0 : ℂ), f z = z ^ k * g z) :
    ∃ r : ℝ, 0 < r ∧ (∀ z ∈ ball (0 : ℂ) r, f z = z ^ k * g z) ∧
      DifferentiableOn ℂ g (ball 0 r) ∧ MapsTo f (ball 0 r) (ball 0 r) ∧
      ∀ z ∈ ball (0 : ℂ) r, g z / g 0 ∈ Complex.slitPlane ∧ ‖Complex.log (g z / g 0)‖ < 1 := by
  let quot : ℂ → ℂ := fun z ↦ g z / g 0
  have hqc : ContinuousAt quot 0 := (hg.div analyticAt_const hg₀).continuousAt
  have hq0 : quot 0 ∈ Complex.slitPlane := by simp [quot, div_self hg₀]
  let M : ℝ := ‖g 0‖ + 1
  have hM : 0 < M := by positivity
  have h3 : ∀ᶠ z in 𝓝 (0 : ℂ), ‖g z‖ < M :=
    hg.continuousAt.norm.eventually_lt continuousAt_const (lt_add_one _)
  have h4 : ∀ᶠ z in 𝓝 (0 : ℂ), quot z ∈ Complex.slitPlane :=
    hqc.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds hq0)
  have h5 : ∀ᶠ z in 𝓝 (0 : ℂ), ‖Complex.log (quot z)‖ < 1 :=
    ((continuousAt_clog hq0).comp hqc).norm.eventually_lt continuousAt_const
      (by simp [quot, div_self hg₀])
  have hev := hf.and
    ((hg.eventually_analyticAt.mono fun z hz ↦ hz.differentiableAt).and (h3.and (h4.and h5)))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  let r : ℝ := min δ (min 1 (1 / (2 * M)))
  have hr : 0 < r := lt_min hδ (lt_min one_pos (div_pos one_pos (mul_pos two_pos hM)))
  have hrδ : ∀ z ∈ ball (0 : ℂ) r, z ∈ ball (0 : ℂ) δ := fun z hz ↦
    ball_subset_ball (min_le_left _ _) hz
  have hrM : M * r ≤ 1 / 2 := by
    calc
      M * r ≤ M * (1 / (2 * M)) :=
        mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_right _ _)) hM.le
      _ = 1 / 2 := by field_simp
  refine ⟨r, hr, fun z hz ↦ (hball z (hrδ z hz)).1, fun z hz ↦
    (hball z (hrδ z hz)).2.1.differentiableWithinAt, ?_, fun z hz ↦ (hball z (hrδ z hz)).2.2.2⟩
  exact mapsTo_ball_of_eq_pow_mul hk hM ((min_le_right _ _).trans (min_le_left _ _)) hrM
    (fun z hz ↦ (hball z (hrδ z hz)).1) (fun z hz ↦ (hball z (hrδ z hz)).2.2.1.le)

/-- The Böttcher logarithm series `S z = ∑ⱼ k⁻ʲ⁻¹ h (fʲ z)` is holomorphic on an invariant
disk, vanishes at `0`, and satisfies `S (f z) = k S z - h z`. -/
private theorem exists_boettcherSeries {f h : ℂ → ℂ} {k : ℕ} (hk : 2 ≤ k) {r : ℝ}
    (hf0 : f 0 = 0) (hfOn : DifferentiableOn ℂ f (ball 0 r))
    (hmaps : MapsTo f (ball 0 r) (ball 0 r)) (hh0 : h 0 = 0)
    (hhOn : DifferentiableOn ℂ h (ball 0 r)) (hh_le : ∀ z ∈ ball (0 : ℂ) r, ‖h z‖ ≤ 1) :
    ∃ S : ℂ → ℂ, DifferentiableOn ℂ S (ball 0 r) ∧ S 0 = 0 ∧
      ∀ z ∈ ball (0 : ℂ) r, S (f z) = (k : ℂ) * S z - h z := by
  let kinv : ℂ := (k : ℂ)⁻¹
  have hkinv : (k : ℂ) * kinv = 1 := mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (by omega))
  have hratio : (k : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < k))
  have htail : Summable fun j : ℕ ↦ (k : ℝ)⁻¹ ^ (j + 1) :=
    (summable_nat_add_iff 1).mpr
      (summable_geometric_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg _)) hratio)
  let term : ℕ → ℂ → ℂ := fun j z ↦ kinv ^ (j + 1) * h ((f^[j]) z)
  have htermOn : ∀ j, DifferentiableOn ℂ (term j) (ball 0 r) := by
    intro j
    have hcomp : DifferentiableOn ℂ (fun z ↦ h ((f^[j]) z)) (ball 0 r) := by
      intro z hz
      have hiter : DifferentiableAt ℂ (f^[j]) z :=
        ((hfOn.iterate hmaps j) z hz).differentiableAt (isOpen_ball.mem_nhds hz)
      have hzj : (f^[j]) z ∈ ball 0 r := (hmaps.iterate j) hz
      have hhAt : DifferentiableAt ℂ h ((f^[j]) z) :=
        (hhOn _ hzj).differentiableAt (isOpen_ball.mem_nhds hzj)
      exact (DifferentiableAt.fun_comp' (x := z) hhAt hiter).differentiableWithinAt
    exact hcomp.const_mul (kinv ^ (j + 1))
  have hbound : ∀ j, ∀ z ∈ ball (0 : ℂ) r, ‖term j z‖ ≤ (k : ℝ)⁻¹ ^ (j + 1) := by
    intro j z hz
    have hknorm : ‖kinv‖ = (k : ℝ)⁻¹ := by simp [kinv, norm_inv]
    calc
      ‖term j z‖ = ‖kinv‖ ^ (j + 1) * ‖h ((f^[j]) z)‖ := by simp [term, norm_pow]
      _ ≤ ‖kinv‖ ^ (j + 1) * 1 :=
        mul_le_mul_of_nonneg_left (hh_le _ ((hmaps.iterate j) hz)) (pow_nonneg (norm_nonneg _) _)
      _ = (k : ℝ)⁻¹ ^ (j + 1) := by rw [hknorm, mul_one]
  let S : ℂ → ℂ := fun z ↦ ∑' j, term j z
  have hSdiff : DifferentiableOn ℂ S (ball 0 r) :=
    Complex.differentiableOn_tsum_of_summable_norm htail (fun j ↦ htermOn j) isOpen_ball
      fun j w hw ↦ hbound j w hw
  have hS0 : S 0 = 0 := by
    have hfun : (fun j ↦ term j 0) = fun _ : ℕ ↦ (0 : ℂ) := by
      ext j
      simp only [term, iterate_fixed hf0 j, hh0, mul_zero]
    simp only [S, hfun, tsum_zero]
  refine ⟨S, hSdiff, hS0, fun z hz ↦ ?_⟩
  have hsumz : Summable fun j ↦ term j z := htail.of_norm_bounded fun j ↦ hbound j z hz
  have hfun : (fun j ↦ term j (f z)) = fun j ↦ (k : ℂ) * term (j + 1) z := by
    ext j
    simp only [term]
    rw [← iterate_succ_apply f j z]
    calc
      kinv ^ (j + 1) * h ((f^[j + 1]) z)
          = ((k : ℂ) * kinv) * kinv ^ (j + 1) * h ((f^[j + 1]) z) := by rw [hkinv, one_mul]
      _ = (k : ℂ) * (kinv ^ (j + 1 + 1) * h ((f^[j + 1]) z)) := by ring
  have hSf : S (f z) = (k : ℂ) * ∑' j, term (j + 1) z := by
    simp only [S]
    rw [hfun]
    exact ((summable_nat_add_iff 1).mpr hsumz).tsum_mul_left (k : ℂ)
  have hsplit : S z = term 0 z + ∑' j, term (j + 1) z := hsumz.tsum_eq_zero_add
  have htermZero : term 0 z = kinv * h z := by simp [term]
  rw [hSf, hsplit, htermZero, mul_add, ← mul_assoc, hkinv, one_mul, add_sub_cancel_left]

/-- The pointwise Böttcher functional equation for `φ z = c z exp (S z)`: if `f z = z ^ k g z`,
`c ^ (k - 1) = g 0` and `S (f z) = k S z - log (g z / g 0)`, then `φ (f z) = φ z ^ k`. -/
private theorem mul_mul_exp_eq_pow {k : ℕ} (hk : 1 ≤ k) {a c w z fz s t : ℂ} (ha : a ≠ 0)
    (hc : c ^ (k - 1) = a) (hw : w / a ∈ Complex.slitPlane) (hfz : fz = z ^ k * w)
    (ht : t = (k : ℂ) * s - Complex.log (w / a)) :
    c * (fz * Complex.exp t) = (c * (z * Complex.exp s)) ^ k := by
  have hwa : w / a ≠ 0 := Complex.slitPlane_ne_zero hw
  have hw0 : w ≠ 0 := fun h ↦ hwa (by simp [h])
  have hca : c * a = c ^ k := by rw [← hc, ← pow_succ', Nat.sub_add_cancel hk]
  have hexp : Complex.exp t = Complex.exp s ^ k * a / w := by
    rw [ht, Complex.exp_sub, Complex.exp_log hwa, Complex.exp_nat_mul]
    field_simp
  rw [hfz, hexp, mul_pow, mul_pow, ← hca]
  field_simp

/-- A normalized Böttcher germ built from the logarithm of the leading coefficient. -/
theorem exists_boettcherCoordinate_of_analyticAt {f g : ℂ → ℂ} {k : ℕ} (hk : 2 ≤ k)
    (hg : AnalyticAt ℂ g 0)
    (hg₀ : g 0 ≠ 0) (hf : ∀ᶠ z in 𝓝 (0 : ℂ), f z = z ^ k * g z) {c : ℂ}
    (hc : c ^ (k - 1) = g 0) :
    ∃ φ : ℂ → ℂ, AnalyticAt ℂ f 0 ∧ f 0 = 0 ∧ AnalyticAt ℂ φ 0 ∧ φ 0 = 0 ∧
      deriv φ 0 = c ∧ ∀ᶠ z in 𝓝 (0 : ℂ), φ (f z) = φ z ^ k := by
  let F : ℂ → ℂ := fun z ↦ z ^ k * g z
  have hFa : AnalyticAt ℂ F 0 :=
    ((analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) 0).pow k).mul hg
  have hfa : AnalyticAt ℂ f 0 := hFa.congr (Filter.EventuallyEq.symm hf)
  have hf0 : f 0 = 0 := by
    have hval : f 0 = (0 : ℂ) ^ k * g 0 := Filter.EventuallyEq.eq_of_nhds hf
    rwa [zero_pow (by omega), zero_mul] at hval
  obtain ⟨r, hr, hFeq, hgOn, hmaps, hlogB⟩ := exists_boettcher_disk hk hg hg₀ hf
  have hfOn : DifferentiableOn ℂ f (ball 0 r) := by
    intro z hz
    have hFAt : DifferentiableAt ℂ F z :=
      (differentiableAt_id.pow k).mul ((hgOn z hz).differentiableAt (isOpen_ball.mem_nhds hz))
    have hnear : f =ᶠ[𝓝 z] F := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      exact hFeq w hw
    exact (hFAt.congr_of_eventuallyEq hnear).differentiableWithinAt
  let hlog : ℂ → ℂ := fun z ↦ Complex.log (g z / g 0)
  have hlogOn : DifferentiableOn ℂ hlog (ball 0 r) := fun z hz ↦
    ((((hgOn z hz).differentiableAt (isOpen_ball.mem_nhds hz)).div_const (g 0)).clog
      (hlogB z hz).1).differentiableWithinAt
  obtain ⟨S, hSdiff, hS0, hstepS⟩ := exists_boettcherSeries hk hf0 hfOn hmaps
    (by simp [hlog]) hlogOn fun z hz ↦ (hlogB z hz).2.le
  let φ : ℂ → ℂ := fun z ↦ c * (z * Complex.exp (S z))
  have hphiOn : DifferentiableOn ℂ φ (ball 0 r) :=
    (differentiableOn_id.mul hSdiff.cexp).const_mul c
  have hphia : AnalyticAt ℂ φ 0 :=
    hphiOn.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hphi0 : φ 0 = 0 := by simp [φ, mul_zero]
  have hderiv : deriv φ 0 = c := by
    have hSAt : DifferentiableAt ℂ S 0 :=
      (hSdiff 0 (mem_ball_self hr)).differentiableAt
        (isOpen_ball.mem_nhds (mem_ball_self hr))
    have hexp : DifferentiableAt ℂ (fun z ↦ Complex.exp (S z)) 0 := hSAt.cexp
    have hid : DifferentiableAt ℂ (fun z : ℂ ↦ z) 0 := differentiableAt_id
    have hu : DifferentiableAt ℂ (fun z ↦ z * Complex.exp (S z)) 0 := hid.mul hexp
    have hprod : deriv (fun z ↦ z * Complex.exp (S z)) 0 = 1 := by
      rw [deriv_fun_mul hid hexp, deriv_id'', deriv_cexp hSAt, hS0, Complex.exp_zero]
      simp
    rw [show φ = fun z ↦ c * (z * Complex.exp (S z)) by rfl,
      deriv_const_mul c hu, hprod, mul_one]
  refine ⟨φ, hfa, hf0, hphia, hphi0, hderiv, ?_⟩
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
  exact mul_mul_exp_eq_pow (by omega) hg₀ hc (hlogB z hz).1 (hFeq z hz) (hstepS z hz)

@[deprecated (since := "2026-11-15")]
alias exists_boettcher_data := exists_boettcherCoordinate_of_analyticAt

/-- If `φ = z u` and `ψ = z v` near `0` both conjugate `f` to `z ↦ z ^ k`, then the ratio
`v / u` satisfies `(v / u) ∘ f = (v / u) ^ k` near `0`. -/
private theorem div_comp_eventuallyEq_pow {f φ ψ u v : ℂ → ℂ} {k : ℕ} (hk : k ≠ 0)
    (hf : ContinuousAt f 0) (hf0 : f 0 = 0)
    (hφe : ∀ᶠ z in 𝓝 (0 : ℂ), φ (f z) = φ z ^ k) (hψe : ∀ᶠ z in 𝓝 (0 : ℂ), ψ (f z) = ψ z ^ k)
    (hu : ContinuousAt u 0) (hv : ContinuousAt v 0) (hu0 : u 0 ≠ 0)
    (hufac : ∀ᶠ z in 𝓝 (0 : ℂ), φ z = z * u z) (hvfac : ∀ᶠ z in 𝓝 (0 : ℂ), ψ z = z * v z) :
    (fun z ↦ v z / u z) ∘ f =ᶠ[𝓝 (0 : ℂ)] (fun z ↦ v z / u z) ^ k := by
  let ratio : ℂ → ℂ := fun z ↦ v z / u z
  have htend : Tendsto f (𝓝 (0 : ℂ)) (𝓝 0) := by
    have hcont : Tendsto f (𝓝 0) (𝓝 (f 0)) := hf.tendsto
    rwa [hf0] at hcont
  have hu_ne : ∀ᶠ z in 𝓝 (0 : ℂ), u z ≠ 0 := hu.eventually_ne hu0
  have huf : ∀ᶠ z in 𝓝 (0 : ℂ), u (f z) ≠ 0 := htend.eventually hu_ne
  have hufEq : ∀ᶠ z in 𝓝 (0 : ℂ), φ (f z) = f z * u (f z) :=
    Filter.EventuallyEq.comp_tendsto hufac htend
  have hvfEq : ∀ᶠ z in 𝓝 (0 : ℂ), ψ (f z) = f z * v (f z) :=
    Filter.EventuallyEq.comp_tendsto hvfac htend
  have hfz_imp : ∀ᶠ z in 𝓝 (0 : ℂ), f z = 0 → z = 0 := by
    filter_upwards [hφe, hufac, hufEq, hu_ne] with z hφ hu hufz huN hfz
    have hφ' : f z * u (f z) = (z * u z) ^ k := by rw [← hufz, hφ, hu]
    rw [hfz, zero_mul] at hφ'
    exact (mul_eq_zero.mp ((pow_eq_zero_iff hk).mp hφ'.symm)).resolve_right huN
  have hratioC : ContinuousAt ratio 0 := hv.div hu hu0
  have hcontL : ContinuousAt (ratio ∘ f) 0 := by
    have hrat : ContinuousAt ratio (f 0) := by
      rw [hf0]
      exact hratioC
    exact hrat.comp hf
  have hcontR : ContinuousAt (ratio ^ k) 0 := hratioC.pow k
  have : (𝓝[≠] (0 : ℂ)).NeBot := Real.punctured_nhds_module_neBot 0
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
        rw [← mul_assoc, hφ']
      have hright : f z * (v (f z) * u z ^ k) = (z * v z) ^ k * u z ^ k := by
        rw [← mul_assoc, hψ']
      have hcomm : (z * u z) ^ k * v z ^ k = (z * v z) ^ k * u z ^ k := by ring
      exact mul_left_cancel₀ hfz (hleft.trans (hcomm.trans hright.symm))
    simp only [ratio]
    rw [div_pow, div_eq_div_iff huF (pow_ne_zero k huN), hcross.symm,
      mul_comm (u (f z)) (v z ^ k)]
  exact (hcontL.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hcontR).mp hpunct

/-- Composition with a germ vanishing at `0` multiplies analytic orders at `0`. -/
private theorem analyticOrderAt_comp_of_eq_zero {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hf0 : f 0 = 0) (hg : AnalyticAt ℂ g 0) :
    analyticOrderAt (g ∘ f) 0 = analyticOrderAt g 0 * analyticOrderAt f 0 := by
  have hsubf : analyticOrderAt (fun z ↦ f z - f 0) 0 = analyticOrderAt f 0 := by
    refine analyticOrderAt_congr ?_
    filter_upwards with z
    simp [hf0]
  have hgf : AnalyticAt ℂ g (f 0) := by
    rw [hf0]
    exact hg
  rw [hgf.analyticOrderAt_comp hf, hsubf, hf0]

/-- A germ conjugated to `z ↦ z ^ k` by a coordinate with a simple zero at `0` vanishes to
order `k` at `0`. -/
private theorem analyticOrderAt_eq_of_comp_eq_pow {f φ : ℂ → ℂ} {k : ℕ} (hf : AnalyticAt ℂ f 0)
    (hf0 : f 0 = 0) (hφa : AnalyticAt ℂ φ 0) (hφ0 : φ 0 = 0) (hφd : deriv φ 0 ≠ 0)
    (hφe : ∀ᶠ z in 𝓝 (0 : ℂ), φ (f z) = φ z ^ k) : analyticOrderAt f 0 = k := by
  have hordφ : analyticOrderAt φ 0 = 1 :=
    hφa.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hφ0 hφd
  have hcong : analyticOrderAt (φ ∘ f) 0 = analyticOrderAt (φ ^ k) 0 := by
    refine analyticOrderAt_congr ?_
    filter_upwards [hφe] with z hz
    simp [Pi.pow_apply, hz]
  rw [analyticOrderAt_comp_of_eq_zero hf hf0 hφa, hordφ, one_mul,
    analyticOrderAt_pow hφa k, hordφ, nsmul_one] at hcong
  exact hcong

/-- If `gap ∘ f = gap * (Q ∘ gap)` near `0`, where `gap 0 = 0`, `Q 0 ≠ 0` and `f` vanishes to
order `k ≥ 2` at `0`, then `gap` vanishes identically near `0`. -/
private theorem analyticOrderAt_eq_top_of_comp_eq_mul {f gap Q : ℂ → ℂ} {k : ℕ} (hk : 2 ≤ k)
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) (hordf : analyticOrderAt f 0 = k)
    (hgapA : AnalyticAt ℂ gap 0) (hgap0 : gap 0 = 0) (hQa : AnalyticAt ℂ Q 0) (hQne : Q 0 ≠ 0)
    (hfactor : gap ∘ f =ᶠ[𝓝 (0 : ℂ)] gap * (Q ∘ gap)) : analyticOrderAt gap 0 = ⊤ := by
  by_contra htop
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
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
    rw [analyticOrderAt_comp_of_eq_zero hf hf0 hgapA, ← hm, hordf]
  have hQcomp : AnalyticAt ℂ (Q ∘ gap) 0 := AnalyticAt.comp_of_eq hQa hgapA hgap0
  have hordQ : analyticOrderAt (Q ∘ gap) 0 = 0 := by
    rw [hQcomp.analyticOrderAt_eq_zero, Function.comp_apply, hgap0]
    exact hQne
  have hordR : analyticOrderAt (gap * (Q ∘ gap)) 0 = ↑m := by
    rw [analyticOrderAt_mul hgapA hQcomp, hm, hordQ, add_zero]
  have hagree : analyticOrderAt (gap ∘ f) 0 = analyticOrderAt (gap * (Q ∘ gap)) 0 :=
    analyticOrderAt_congr hfactor
  rw [hordL, hordR, ← Nat.cast_mul] at hagree
  have hnat : m * k = m := ENat.natCast_inj.mp hagree
  have hk1 : k = 1 := by
    have hmul : m * k = m * 1 := by rw [hnat, Nat.mul_one]
    exact Nat.mul_left_cancel (by omega : 0 < m) hmul
  omega

/-- Two Böttcher coordinates differ by a `(k - 1)`st root of unity. -/
theorem boettcherCoordinate_eq_mul_unity {f φ ψ : ℂ → ℂ} {k : ℕ} (hk : 2 ≤ k)
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) (hφa : AnalyticAt ℂ φ 0) (hφ0 : φ 0 = 0)
    (hφd : deriv φ 0 ≠ 0) (hφe : ∀ᶠ z in 𝓝 (0 : ℂ), φ (f z) = φ z ^ k)
    (hψa : AnalyticAt ℂ ψ 0) (hψ0 : ψ 0 = 0) (hψd : deriv ψ 0 ≠ 0)
    (hψe : ∀ᶠ z in 𝓝 (0 : ℂ), ψ (f z) = ψ z ^ k) :
    ∃ ζ : ℂ, ζ ^ (k - 1) = 1 ∧ ∀ᶠ z in 𝓝 (0 : ℂ), ψ z = ζ * φ z := by
  obtain ⟨u, hua, hu0, hufac⟩ := exists_analyticAt_eventually_eq_mul hφa hφ0 hφd
  obtain ⟨v, hva, hv0, hvfac⟩ := exists_analyticAt_eventually_eq_mul hψa hψ0 hψd
  have hu0' : u 0 ≠ 0 := by simpa [hu0] using hφd
  have hv0' : v 0 ≠ 0 := by simpa [hv0] using hψd
  let ratio : ℂ → ℂ := fun z ↦ v z / u z
  have hratioA : AnalyticAt ℂ ratio 0 := hva.div hua hu0'
  have hratio_eq : ratio ∘ f =ᶠ[𝓝 (0 : ℂ)] ratio ^ k :=
    div_comp_eventuallyEq_pow (by omega) hf.continuousAt hf0 hφe hψe hua.continuousAt
      hva.continuousAt hu0' hufac hvfac
  let ζ : ℂ := ratio 0
  have hzeta_ne : ζ ≠ 0 := by
    simp [ζ, ratio, div_ne_zero hv0' hu0']
  have hzeta_pow : ζ ^ k = ζ := by
    have h0 := Filter.Eventually.self_of_nhds hratio_eq
    have h0' : ratio (f 0) = ratio 0 ^ k := by
      simpa [Function.comp_def, Pi.pow_apply] using h0
    rw [hf0] at h0'
    simpa [ζ] using h0'.symm
  have hroot : ζ ^ (k - 1) = 1 := by
    apply mul_right_cancel₀ hzeta_ne
    calc
      ζ ^ (k - 1) * ζ = ζ ^ k := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
      _ = ζ := hzeta_pow
      _ = 1 * ζ := (one_mul ζ).symm
  obtain ⟨Q, hQa, hQ0, hQeq⟩ :=
    exists_pow_sub_factor (by omega : 1 ≤ k) hzeta_pow
  have hQne : Q 0 ≠ 0 := by
    rw [hQ0, hroot, mul_one]
    exact Nat.cast_ne_zero.mpr (by omega : k ≠ 0)
  let gap : ℂ → ℂ := fun z ↦ ratio z - ζ
  have hgapA : AnalyticAt ℂ gap 0 := hratioA.sub analyticAt_const
  have hgap0 : gap 0 = 0 := by simp [gap, ζ]
  have hfactor : gap ∘ f =ᶠ[𝓝 (0 : ℂ)] gap * (Q ∘ gap) := by
    filter_upwards [hratio_eq] with z hz
    have hz' : ratio (f z) = ratio z ^ k := by
      simpa [Function.comp_def, Pi.pow_apply] using hz
    simp only [Function.comp_def, Pi.mul_apply]
    rw [← hQeq (gap z)]
    simp only [gap]
    rw [hz']
    ring
  have htop : analyticOrderAt gap 0 = ⊤ :=
    analyticOrderAt_eq_top_of_comp_eq_mul hk hf hf0
      (analyticOrderAt_eq_of_comp_eq_pow hf hf0 hφa hφ0 hφd hφe) hgapA hgap0 hQa hQne hfactor
  refine ⟨ζ, hroot, ?_⟩
  filter_upwards [analyticOrderAt_eq_top.mp htop, hufac, hvfac,
    hua.continuousAt.eventually_ne hu0'] with z hgz hφz hψz huN
  have hvz : v z = ζ * u z := (div_eq_iff huN).mp (sub_eq_zero.mp hgz)
  rw [hψz, hφz, hvz]
  ring

end CKMA
