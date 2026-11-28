/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Fourier.LpSpace

import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Frequency bump cutoffs and coordinate integration by parts

Coordinate integration by parts for smooth `L²` functions, smooth compactly supported
frequency-space cutoffs `φₙ`, used in the proof of Heisenberg coordinate uncertainty.

Source: GAPS 27.13.

All declarations live in the auxiliary namespace `CKMA.Heisenberg`.

## Main definitions

* `CKMA.Heisenberg.coordVec`: coordinate unit vector `eⱼ` in `EuclideanSpace ℝ (Fin d)`.
* `CKMA.Heisenberg.coordFun`: complex coordinate function `x ↦ (xⱼ : ℂ)`.
* `CKMA.Heisenberg.freqBump`: real frequency bump `φₙ` at scale `n + 1`, equal to one on the
  ball of radius `n + 1` and supported in the ball of radius `2 (n + 1)`.
* `CKMA.Heisenberg.freqCutoff`: pointwise product of an `L²` class with the frequency bump.
* `CKMA.Heisenberg.freqBumpScaled`: complex-valued frequency bump function `φₙ`.
* `CKMA.Heisenberg.freqBumpDeriv`: complexified directional derivative `∂ⱼ φₙ` of the frequency
  bump.

## Main results

* `CKMA.Heisenberg.integral_norm_sq_le_two_mul_coord`: coordinate integration by parts bounding
  `‖g‖²` by `2 ‖xⱼ g‖ ‖∂ⱼ g‖`.
* `CKMA.Heisenberg.tendsto_freqBump_mul`: `L²` convergence of frequency cutoff truncations
  `φₙ u → u`.

## Notation

* `V`: local notation for `EuclideanSpace ℝ (Fin d)`.
-/

public section

noncomputable section

namespace CKMA.Heisenberg

open Filter MeasureTheory FourierTransform Real Complex VectorFourier Topology
open scoped ENNReal FourierTransform RealInnerProductSpace ComplexInnerProductSpace LineDeriv
  Topology

section HeisenbergAux

variable {d : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin d)

/-- Squared `L²` norm as the integral of the squared pointwise norm. -/
private lemma norm_sq_eq_integral_norm_sq
    {α : Type*} {m : MeasurableSpace α} {μ : Measure α} (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hf : AEStronglyMeasurable (⇑f) μ := Lp.aestronglyMeasurable f
  have hlp : lpNorm (⇑f) 2 μ =
      (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (2 : ℝ)⁻¹ := by
    simpa using lpNorm_eq_integral_norm_rpow_toReal (p := 2) (f := ⇑f) (μ := μ)
      (by simp) (by simp) hf
  have hnorm : ‖f‖ = lpNorm (⇑f) 2 μ := by
    simp [Lp.norm_def, toReal_eLpNorm]
  rw [hnorm, hlp]
  have hI : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ :=
    integral_nonneg fun _ ↦ by positivity
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hI]
  simp [Nat.cast_ofNat, Real.rpow_one]

/-- Coordinate vector `eⱼ` in Euclidean space. -/
@[expose]
def coordVec (j : Fin d) : V :=
  EuclideanSpace.single j 1

/-- `coordVec j` is `EuclideanSpace.single j 1`. -/
lemma coordVec_def (j : Fin d) : coordVec j = EuclideanSpace.single j 1 := rfl

/-- The `j`-th coordinate of `eⱼ` is `1`. -/
private lemma coordVec_apply (j : Fin d) : coordVec j j = 1 := by
  simp [coordVec]

/-- Each coordinate vector is a unit vector. -/
private lemma norm_coordVec (j : Fin d) : ‖coordVec j‖ = 1 := by
  simp [coordVec, PiLp.norm_single]

/-- The coordinate `x ↦ xⱼ`, as a complex scalar. -/
@[expose]
def coordFun (j : Fin d) : V → ℂ :=
  fun x ↦ (x j : ℂ)

/-- `coordFun j x` is the complexified `j`-th coordinate. -/
lemma coordFun_apply (j : Fin d) (x : V) : coordFun j x = (x j : ℂ) := rfl

/-- The complex coordinate agrees with the real inner product against `eⱼ`. -/
lemma coordFun_eq_inner (j : Fin d) (x : V) :
    coordFun j x = (inner ℝ x (coordVec j) : ℂ) := by
  simp [coordFun, coordVec, EuclideanSpace.inner_single_right]

/-- Coordinate multiplication has temperate growth. -/
lemma hasTemperateGrowth_coordFun (j : Fin d) :
    (coordFun j).HasTemperateGrowth := by
  have h := (Complex.ofRealCLM.comp (EuclideanSpace.proj j)).hasTemperateGrowth
  convert h using 1
  ext x
  simp [coordFun, ContinuousLinearMap.comp_apply]

/-- Integration by parts for `‖g‖²` against the coordinate `xⱼ`. The derivative is the
Fréchet derivative in the direction `eⱼ`, and both weighted factors are square-integrable. -/
lemma integral_norm_sq_le_two_mul_coord
    (j : Fin d) {g : V → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hL2 : MemLp g 2 volume)
    (hx : MemLp (fun x ↦ coordFun j x * g x) 2 volume)
    (hd : MemLp (fun x ↦ fderiv ℝ g x (coordVec j)) 2 volume) :
    ‖hL2.toLp g‖ ^ 2 ≤
      2 * ‖hx.toLp (fun x ↦ coordFun j x * g x)‖ *
        ‖hd.toLp (fun x ↦ fderiv ℝ g x (coordVec j))‖ := by
  let v : V := coordVec j
  let m : V → ℝ := fun x ↦ x j
  let ρ : V → ℝ := fun x ↦ ‖g x‖ ^ 2
  let xf := hx.toLp (fun x ↦ coordFun j x * g x)
  let dg := hd.toLp (fun x ↦ fderiv ℝ g x v)
  have hg_diff : Differentiable ℝ g := hg.differentiable (by simp)
  have hρ_int : Integrable ρ volume :=
    (memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).1 hL2
  have hx_int : Integrable (fun x ↦ ‖coordFun j x * g x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hx.aestronglyMeasurable).1 hx
  have hd_int : Integrable (fun x ↦ ‖fderiv ℝ g x v‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).1 hd
  have hm_fderiv : ∀ x, fderiv ℝ m x v = 1 := by
    intro x
    have hm : m = ⇑(EuclideanSpace.proj (𝕜 := ℝ) j) := by
      ext y
      simp [m]
    rw [hm, ContinuousLinearMap.fderiv]
    simp [coordVec_apply, v]
  have hρ_fderiv : ∀ x, fderiv ℝ ρ x v = 2 * re (inner ℂ (g x) (fderiv ℝ g x v)) := by
    intro x
    have hF := (hg_diff x).hasFDerivAt.norm_sq
    rw [hF.fderiv, smul_apply, two_smul]
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      real_inner_eq_re_inner (𝕜 := ℂ), RCLike.re_eq_complex_re]
    ring
  have hfderiv : Continuous (fun x : V ↦ fderiv ℝ g x) :=
    hg.continuous_fderiv (by simp)
  have hcross_cont : Continuous fun x : V ↦
      m x * re (inner ℂ (g x) (fderiv ℝ g x v)) := by
    apply Continuous.mul
    · fun_prop
    · exact continuous_re.comp (Continuous.inner hg.continuous
        ((ContinuousLinearMap.apply ℝ ℂ v).continuous.comp hfderiv))
  have hcross_int : Integrable
      (fun x ↦ m x * re (inner ℂ (g x) (fderiv ℝ g x v))) volume := by
    refine Integrable.mono' ((hx_int.add hd_int).div_const (2 : ℝ))
      hcross_cont.aestronglyMeasurable ?_
    filter_upwards with x
    have hre : |re (inner ℂ (g x) (fderiv ℝ g x v))| ≤
        ‖g x‖ * ‖fderiv ℝ g x v‖ :=
      (abs_re_le_norm _).trans (norm_inner_le_norm _ _)
    have hxm : |m x| * ‖g x‖ = ‖coordFun j x * g x‖ := by
      simp [m, coordFun, Complex.norm_real, Real.norm_eq_abs]
    have hAM := two_mul_le_add_sq ‖coordFun j x * g x‖ ‖fderiv ℝ g x v‖
    calc ‖m x * re (inner ℂ (g x) (fderiv ℝ g x v))‖
        = |m x| * |re (inner ℂ (g x) (fderiv ℝ g x v))| := by
          simp [Real.norm_eq_abs]
      _ ≤ |m x| * ‖g x‖ * ‖fderiv ℝ g x v‖ := by
          rw [mul_assoc]
          gcongr
      _ = ‖coordFun j x * g x‖ * ‖fderiv ℝ g x v‖ := by rw [hxm]
      _ ≤ (‖coordFun j x * g x‖ ^ 2 + ‖fderiv ℝ g x v‖ ^ 2) / 2 := by
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2)]
          convert hAM using 1
          ring
  have hρ_cont : Continuous ρ := by fun_prop
  have hm_cont : Continuous m := by fun_prop
  have hmρ_int : Integrable (fun x ↦ m x * ρ x) volume := by
    refine Integrable.mono' ((hx_int.add hρ_int).div_const (2 : ℝ))
      (hm_cont.mul hρ_cont).aestronglyMeasurable ?_
    filter_upwards with x
    have hxm : |m x| * ‖g x‖ = ‖coordFun j x * g x‖ := by
      simp [m, coordFun, Complex.norm_real, Real.norm_eq_abs]
    have hAM := two_mul_le_add_sq ‖coordFun j x * g x‖ ‖g x‖
    have hρ0 : 0 ≤ ρ x := sq_nonneg _
    calc ‖m x * ρ x‖ = |m x| * ρ x := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hρ0]
      _ = ‖coordFun j x * g x‖ * ‖g x‖ := by
          simp only [ρ, pow_two]
          rw [← mul_assoc, hxm]
      _ ≤ (‖coordFun j x * g x‖ ^ 2 + ‖g x‖ ^ 2) / 2 := by
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2)]
          convert hAM using 1
          ring
  have hfderiv_m_ρ : Integrable (fun x ↦ fderiv ℝ m x v * ρ x) volume := by
    simpa [hm_fderiv, one_mul] using hρ_int
  have hρ_diff : ∀ x, DifferentiableAt ℝ ρ x :=
    fun x ↦ ((hg_diff x).hasFDerivAt.norm_sq).differentiableAt
  have hm_diff : ∀ x, DifferentiableAt ℝ m x := by
    intro x
    have hm : m = ⇑(EuclideanSpace.proj (𝕜 := ℝ) j) := by
      ext y
      simp [m]
    rw [hm]
    exact ContinuousLinearMap.differentiableAt (EuclideanSpace.proj (𝕜 := ℝ) j)
  have hρderiv_int : Integrable (fun x ↦ m x * fderiv ℝ ρ x v) volume := by
    have hEq : (fun x ↦ m x * fderiv ℝ ρ x v) =
        fun x ↦ 2 * (m x * re (inner ℂ (g x) (fderiv ℝ g x v))) := by
      ext x
      rw [hρ_fderiv, mul_left_comm]
    rw [hEq]
    exact hcross_int.const_mul 2
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := m) (g := ρ) (v := v) (μ := (volume : Measure V))
    hfderiv_m_ρ hρderiv_int hmρ_int (fun x _ ↦ hm_diff x) (fun x _ ↦ hρ_diff x)
  have hfactor : ∫ x, m x * re (inner ℂ (g x) (fderiv ℝ g x v)) ∂volume =
      re (inner ℂ xf dg) := by
    have hint := L2.integrable_inner (𝕜 := ℂ) xf dg
    rw [L2.inner_def, ← RCLike.re_eq_complex_re]
    rw [← integral_re (μ := (volume : Measure V))
      (f := fun a => inner ℂ (xf a) (dg a)) hint]
    refine integral_congr_ae ?_
    filter_upwards [hx.coeFn_toLp, hd.coeFn_toLp] with x hxf hdx
    rw [hxf, hdx]
    simp only [m, coordFun, RCLike.re_eq_complex_re, RCLike.inner_apply,
      map_mul, Complex.conj_ofReal]
    rw [← Complex.re_ofReal_mul]
    congr 1
    ring
  have hmass : ∫ x, ρ x ∂volume = -2 * re (inner ℂ xf dg) := by
    have hIBP' : ∫ x, m x * fderiv ℝ ρ x v ∂volume = -∫ x, ρ x ∂volume := by
      simpa [hm_fderiv, one_mul] using hIBP
    have h2 : ∫ x, m x * fderiv ℝ ρ x v ∂volume =
        2 * ∫ x, m x * re (inner ℂ (g x) (fderiv ℝ g x v)) ∂volume := by
      have hEq : (fun x => m x * fderiv ℝ ρ x v) =
          fun x => (2 : ℝ) * (m x * re (inner ℂ (g x) (fderiv ℝ g x v))) := by
        ext x
        rw [hρ_fderiv, mul_left_comm]
      rw [hEq, integral_const_mul]
    have hneg : ∫ x, ρ x ∂volume = -∫ x, m x * fderiv ℝ ρ x v ∂volume :=
      neg_eq_iff_eq_neg.mp hIBP'.symm
    rw [hneg, h2, hfactor]
    ring
  have hnorm : ‖hL2.toLp g‖ ^ 2 = ∫ x, ρ x ∂volume := by
    rw [norm_sq_eq_integral_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [hL2.coeFn_toLp] with x hxg
    simp [ρ, hxg]
  have hinner : |re (inner ℂ xf dg)| ≤ ‖xf‖ * ‖dg‖ :=
    (abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  calc ‖hL2.toLp g‖ ^ 2
      = -2 * re (inner ℂ xf dg) := hnorm.trans hmass
    _ ≤ 2 * |re (inner ℂ xf dg)| := by
        have hneg : -(re (inner ℂ xf dg)) ≤ |re (inner ℂ xf dg)| := neg_le_abs _
        linarith
    _ ≤ 2 * ‖xf‖ * ‖dg‖ := by
        rw [mul_assoc]
        gcongr

/-- Euclidean norm of the Fourier weight `2πi`. -/
lemma norm_two_pi_I : ‖(2 * π * I : ℂ)‖ = 2 * π := by
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_two,
    Complex.norm_of_nonneg Real.pi_pos.le]

/-- Coordinate multiplication on an `L²` class agrees with the distributional product. -/
private lemma toTemperedDistribution_coord_mul (j : Fin d)
    (u : Lp ℂ 2 (volume : Measure V))
    (hu : MemLp (fun x ↦ coordFun j x * u x) 2 volume) :
    TemperedDistribution.smulLeftCLM ℂ (coordFun j) (u : TemperedDistribution V ℂ) =
      (hu.toLp (fun x ↦ coordFun j x * u x) : TemperedDistribution V ℂ) := by
  ext φ
  rw [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_coordFun j)]
  simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Distributional derivative of `𝓕 f` along `eⱼ`, represented by an `L²` function. -/
lemma lineDeriv_fourier_lp_eq (j : Fin d)
    (f : Lp ℂ 2 (volume : Measure V))
    (hx : MemLp (fun x ↦ coordFun j x * f x) 2 volume) :
    ∂_{coordVec j} (𝓕 (f : TemperedDistribution V ℂ)) =
      Lp.toTemperedDistribution (𝓕 (-(2 * π * I : ℂ) •
        hx.toLp (fun x ↦ coordFun j x * f x))) := by
  rw [TemperedDistribution.lineDerivOp_fourier_eq]
  have hinner : coordFun j = fun x ↦ (inner ℝ x (coordVec j) : ℂ) := by
    ext x
    exact coordFun_eq_inner j x
  have hsmul : TemperedDistribution.smulLeftCLM ℂ (coordFun j)
      (f : TemperedDistribution V ℂ) =
      TemperedDistribution.smulLeftCLM ℂ (fun x ↦ (inner ℝ x (coordVec j) : ℂ))
        (f : TemperedDistribution V ℂ) := by
    rw [hinner]
  rw [← hsmul, toTemperedDistribution_coord_mul j f hx, FourierTransform.fourier_smul,
    Lp.fourier_toTemperedDistribution_eq, FourierTransform.fourier_smul]
  change -(2 * π * I) • (Lp.toTemperedDistributionCLM ℂ (volume : Measure V) 2)
      (𝓕 (hx.toLp (fun x ↦ coordFun j x * f x))) =
    (Lp.toTemperedDistributionCLM ℂ (volume : Measure V) 2)
      (-(2 * π * I) • 𝓕 (hx.toLp (fun x ↦ coordFun j x * f x)))
  exact ((Lp.toTemperedDistributionCLM ℂ (volume : Measure V) 2).map_smul _ _).symm

/-- `L²` norm of the Fourier transform of the weighted spatial moment. -/
lemma norm_fourier_coord_eq (j : Fin d) (f : Lp ℂ 2 (volume : Measure V))
    (hx : MemLp (fun x ↦ coordFun j x * f x) 2 volume) :
    ‖𝓕 (-(2 * π * I : ℂ) • hx.toLp (fun x ↦ coordFun j x * f x))‖ =
      2 * π * ‖hx.toLp (fun x ↦ coordFun j x * f x)‖ := by
  rw [FourierTransform.fourier_smul, norm_smul, norm_neg, Lp.norm_fourier_eq, norm_two_pi_I]

/-- Smooth bump equal to one on the unit ball and supported in the ball of radius two. -/
@[expose]
def baseBump : ContDiffBump (0 : V) :=
  ⟨1, 2, zero_lt_one, one_lt_two⟩

/-- The inner radius of the base bump is `1`. -/
lemma baseBump_rIn : (baseBump : ContDiffBump (0 : V)).rIn = 1 := rfl

/-- The outer radius of the base bump is `2`. -/
lemma baseBump_rOut : (baseBump : ContDiffBump (0 : V)).rOut = 2 := rfl

/-- Frequency cutoff `φₙ` at scale `n + 1`: the base bump rescaled by `n + 1`, equal to one
on the ball of radius `n + 1` and supported in the ball of radius `2 (n + 1)`. -/
@[expose]
def freqBump (n : ℕ) (x : V) : ℝ :=
  (baseBump : ContDiffBump (0 : V)) (((n : ℝ) + 1)⁻¹ • x)

/-- Unfolding the frequency cutoff. -/
lemma freqBump_def (n : ℕ) (x : V) :
    freqBump n x = (baseBump : ContDiffBump (0 : V)) (((n : ℝ) + 1)⁻¹ • x) := rfl

/-- The frequency cutoff is smooth. -/
private lemma contDiff_freqBump (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (freqBump n : V → ℝ) := by
  refine ((baseBump : ContDiffBump (0 : V)).contDiff (n := (⊤ : ℕ∞))).comp ?_
  exact (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ V).contDiff

/-- The frequency cutoff has compact support. -/
private lemma hasCompactSupport_freqBump (n : ℕ) :
    HasCompactSupport (freqBump n : V → ℝ) := by
  refine HasCompactSupport.intro
    (K := Metric.closedBall (0 : V) (2 * ((n : ℝ) + 1))) (isCompact_closedBall _ _) ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  rw [freqBump]
  apply (baseBump : ContDiffBump (0 : V)).zero_of_le_dist
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < ((n : ℝ) + 1)⁻¹)]
  calc (2 : ℝ)
      = 2 * ((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹ := by field_simp
    _ ≤ ‖x‖ * ((n : ℝ) + 1)⁻¹ := by gcongr
    _ = ((n : ℝ) + 1)⁻¹ * ‖x‖ := by ring

/-- The frequency cutoff takes values in the unit interval. -/
private lemma freqBump_mem_Icc (n : ℕ) (x : V) :
    freqBump n x ∈ Set.Icc 0 1 := by
  rw [freqBump]
  exact ⟨(baseBump : ContDiffBump (0 : V)).nonneg,
    (baseBump : ContDiffBump (0 : V)).le_one⟩

/-- On each point the cutoff is eventually equal to one. -/
private lemma eventually_freqBump_eq_one (x : V) :
    ∀ᶠ n in Filter.atTop, freqBump n x = 1 := by
  refine Filter.eventually_atTop.2 ⟨Nat.ceil ‖x‖, fun n hn ↦ ?_⟩
  rw [freqBump]
  apply (baseBump : ContDiffBump (0 : V)).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < ((n : ℝ) + 1)⁻¹)]
  rw [inv_mul_le_iff₀ (by positivity)]
  have hr : (baseBump : ContDiffBump (0 : V)).rIn = 1 := rfl
  rw [hr, mul_one]
  exact (Nat.ceil_le.mp hn).trans (le_add_of_nonneg_right zero_le_one)

/-- Derivative of the cutoff along `eⱼ` is `O(1 / n)`. -/
private lemma exists_norm_fderiv_freqBump_le (j : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x,
      ‖fderiv ℝ (freqBump n) x (coordVec j)‖ ≤ C / ((n : ℝ) + 1) := by
  have hcont : Continuous fun x ↦ ‖fderiv ℝ (⇑(baseBump : ContDiffBump (0 : V))) x‖ :=
    continuous_norm.comp
      (((baseBump : ContDiffBump (0 : V)).contDiff
        (n := (⊤ : ℕ∞))).continuous_fderiv (by simp))
  have hsup : HasCompactSupport fun x ↦
      ‖fderiv ℝ (⇑(baseBump : ContDiffBump (0 : V))) x‖ :=
    (baseBump : ContDiffBump (0 : V)).hasCompactSupport.fderiv ℝ |>.norm
  obtain ⟨x0, hx0⟩ := hcont.exists_forall_ge_of_hasCompactSupport hsup
  refine ⟨‖fderiv ℝ (⇑(baseBump : ContDiffBump (0 : V))) x0‖, norm_nonneg _,
    fun n x ↦ ?_⟩
  have hf := fderiv_comp_smul (𝕜 := ℝ)
    (f := (⇑(baseBump : ContDiffBump (0 : V))))
    (c := ((n : ℝ) + 1)⁻¹) (x := x)
  have hfun : (freqBump n : V → ℝ) = fun y ↦
      (baseBump : ContDiffBump (0 : V)) (((n : ℝ) + 1)⁻¹ • y) := by
    ext y
    rfl
  rw [hfun, hf, smul_apply]
  calc ‖((n : ℝ) + 1)⁻¹ •
        (fderiv ℝ (⇑(baseBump : ContDiffBump (0 : V))) (((n : ℝ) + 1)⁻¹ • x))
          (coordVec j)‖
      = ((n : ℝ) + 1)⁻¹ * ‖(fderiv ℝ (⇑(baseBump : ContDiffBump (0 : V)))
          (((n : ℝ) + 1)⁻¹ • x)) (coordVec j)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ((n : ℝ) + 1)⁻¹)]
    _ ≤ ((n : ℝ) + 1)⁻¹ * (‖fderiv ℝ (⇑(baseBump : ContDiffBump (0 : V)))
          (((n : ℝ) + 1)⁻¹ • x)‖ * ‖coordVec j‖) := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ((n : ℝ) + 1)⁻¹ * ‖fderiv ℝ (⇑(baseBump : ContDiffBump (0 : V)))
          (((n : ℝ) + 1)⁻¹ • x)‖ := by
        rw [norm_coordVec, mul_one]
    _ ≤ ((n : ℝ) + 1)⁻¹ * ‖fderiv ℝ (⇑(baseBump : ContDiffBump (0 : V))) x0‖ := by
        gcongr
        exact hx0 _
    _ = ‖fderiv ℝ (⇑(baseBump : ContDiffBump (0 : V))) x0‖ / ((n : ℝ) + 1) := by
        rw [div_eq_mul_inv, mul_comm]

/-- A pointwise bound of one preserves membership in `L²`. -/
private lemma mul_memLp_of_norm_le_one {b : V → ℂ} (hb : AEStronglyMeasurable b volume)
    (hbound : ∀ x, ‖b x‖ ≤ 1) (u : Lp ℂ 2 (volume : Measure V)) :
    MemLp (fun x ↦ b x * u x) 2 volume := by
  refine (Lp.memLp u).of_le (hb.mul (Lp.aestronglyMeasurable u)) ?_
  filter_upwards with x
  calc ‖b x * u x‖ = ‖b x‖ * ‖u x‖ := norm_mul _ _
    _ ≤ 1 * ‖u x‖ := by gcongr; exact hbound x
    _ = ‖u x‖ := one_mul _

/-- Multiplication by the frequency cutoff preserves `L²`. -/
lemma memLp_freqBump_mul (n : ℕ) (u : Lp ℂ 2 (volume : Measure V)) :
    MemLp (fun x ↦ (freqBump n x : ℂ) * u x) 2 volume := by
  refine mul_memLp_of_norm_le_one ?_ ?_ u
  · exact (Complex.ofRealCLM.continuous.comp
      (contDiff_freqBump n).continuous).aestronglyMeasurable
  · intro x
    have hφ := freqBump_mem_Icc n x
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hφ.1]
    exact hφ.2

/-- The complex scalar `φₙ(x) - 1` has absolute value at most one. -/
private lemma sub_one_freqBump_norm_le (n : ℕ) (x : V) :
    ‖(freqBump n x : ℂ) - 1‖ ≤ 1 := by
  have hφ := freqBump_mem_Icc n x
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hφ.2)]
  linarith [hφ.1]

/-- Multiplication by `φₙ - 1` preserves `L²`. -/
private lemma sub_one_freqBump_mul_memLp (n : ℕ) (u : Lp ℂ 2 (volume : Measure V)) :
    MemLp (fun x ↦ ((freqBump n x : ℂ) - 1) * u x) 2 volume := by
  refine mul_memLp_of_norm_le_one ?_ (sub_one_freqBump_norm_le n) u
  exact (((Complex.ofRealCLM.continuous.comp
    (contDiff_freqBump n).continuous).sub continuous_const).aestronglyMeasurable)

/-- Cutoff multiplication converges to the original class in `L²`. -/
lemma tendsto_freqBump_mul (u : Lp ℂ 2 (volume : Measure V)) :
    Tendsto (fun n ↦ (memLp_freqBump_mul n u).toLp
      (fun x ↦ (freqBump n x : ℂ) * u x)) atTop (𝓝 u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let dlt : ℕ → Lp ℂ 2 (volume : Measure V) := fun n ↦
    (sub_one_freqBump_mul_memLp n u).toLp
      (fun x ↦ ((freqBump n x : ℂ) - 1) * u x)
  have hdlt (n : ℕ) : (memLp_freqBump_mul n u).toLp
      (fun x ↦ (freqBump n x : ℂ) * u x) - u = dlt n := by
    apply Lp.ext
    filter_upwards [(memLp_freqBump_mul n u).coeFn_toLp,
      (sub_one_freqBump_mul_memLp n u).coeFn_toLp,
      Lp.coeFn_sub ((memLp_freqBump_mul n u).toLp
        (fun x ↦ (freqBump n x : ℂ) * u x)) u] with x hφu hsub hdiff
    rw [hdiff, Pi.sub_apply, hφu, hsub]
    ring
  have hnorm (n : ℕ) : ‖dlt n‖ ^ 2 =
      ∫ x, ‖((freqBump n x : ℂ) - 1) * u x‖ ^ 2 ∂volume := by
    rw [norm_sq_eq_integral_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [(sub_one_freqBump_mul_memLp n u).coeFn_toLp] with x hx
    simp [dlt, hx]
  have hbound_int : Integrable (fun x ↦ ‖u x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).1 (Lp.memLp u)
  have hlim : Tendsto (fun n ↦ ∫ x, ‖((freqBump n x : ℂ) - 1) * u x‖ ^ 2 ∂volume)
      atTop (𝓝 (0 : ℝ)) := by
    have hzero : (∫ x, (0 : ℝ) ∂volume) = 0 := integral_zero V ℝ
    rw [← hzero]
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖u x‖ ^ 2)
      (fun n ↦ ?_) hbound_int (fun n ↦ ?_) ?_
    · exact (continuous_pow 2).comp_aestronglyMeasurable
        (continuous_norm.comp_aestronglyMeasurable
          (sub_one_freqBump_mul_memLp n u).aestronglyMeasurable)
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      gcongr
      calc ‖((freqBump n x : ℂ) - 1) * u x‖
          = ‖(freqBump n x : ℂ) - 1‖ * ‖u x‖ := norm_mul _ _
        _ ≤ 1 * ‖u x‖ := by gcongr; exact sub_one_freqBump_norm_le n x
        _ = ‖u x‖ := one_mul _
    · filter_upwards with x
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_freqBump_eq_one x] with n hn
      have hzero : ((freqBump n x : ℂ) - 1) * u x = 0 := by
        rw [hn, Complex.ofReal_one, sub_self, zero_mul]
      rw [hzero, norm_zero, pow_two, mul_zero]
  refine (tendsto_congr fun n ↦ congrArg norm (hdlt n)).2 ?_
  have hsq : Tendsto (fun n ↦ ‖dlt n‖ ^ 2) atTop (𝓝 0) :=
    (tendsto_congr fun n ↦ hnorm n).2 hlim
  have ht : Tendsto (fun n ↦ Real.sqrt (‖dlt n‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
    (continuous_sqrt.tendsto 0).comp hsq
  simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at ht
  exact ht

/-- Polynomial moments of a compactly supported `L²` function are integrable. -/
private lemma integrable_pow_mul_freqBump (n k : ℕ) (u : Lp ℂ 2 (volume : Measure V)) :
    Integrable (fun x ↦ ‖x‖ ^ k * ‖(freqBump n x : ℂ) * u x‖) volume := by
  let b : V → ℝ := fun x ↦ ‖x‖ ^ k * freqBump n x
  have hb_cont : Continuous b :=
    (continuous_norm.pow k).mul (contDiff_freqBump n).continuous
  have hb_sup : HasCompactSupport b :=
    (hasCompactSupport_freqBump n).mul_left (f := fun x ↦ ‖x‖ ^ k)
  have hb_c_cont : Continuous fun x ↦ (b x : ℂ) :=
    Complex.ofRealCLM.continuous.comp hb_cont
  have hb_c_sup : HasCompactSupport fun x ↦ (b x : ℂ) :=
    hb_sup.comp_left (g := Complex.ofReal) (by simp)
  have hb_lp : MemLp (fun x ↦ (b x : ℂ)) 2 volume :=
    hb_c_cont.memLp_of_hasCompactSupport (p := 2) (μ := volume) hb_c_sup
  have hmul : MemLp (fun x ↦ (b x : ℂ) * u x) 1 volume := hb_lp.mul (Lp.memLp u)
  have hint : Integrable (fun x ↦ (b x : ℂ) * u x) volume :=
    (memLp_one_iff_integrable).1 hmul
  have hnorm : Integrable (fun x ↦ ‖(b x : ℂ) * u x‖) volume :=
    (integrable_norm_iff hint.aestronglyMeasurable).2 hint
  refine hnorm.congr ?_
  filter_upwards with x
  have hφ := freqBump_mem_Icc n x
  simp only [b, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hφ.1, abs_of_nonneg (pow_nonneg (norm_nonneg _) _), mul_assoc]

/-- Pointwise product of an `L²` class by the frequency cutoff. -/
abbrev freqCutoff (n : ℕ) (u : Lp ℂ 2 (volume : Measure V)) : V → ℂ :=
  fun x ↦ (freqBump n x : ℂ) * u x

/-- The frequency cutoff of an `L²` function is integrable. -/
lemma integrable_freqCutoff (n : ℕ) (u : Lp ℂ 2 (volume : Measure V)) :
    Integrable (freqCutoff n u) volume := by
  have hnorm : Integrable (fun x ↦ ‖freqCutoff n u x‖) volume := by
    refine (integrable_pow_mul_freqBump n 0 u).congr ?_
    filter_upwards with x
    simp [freqCutoff, pow_zero]
  exact (integrable_norm_iff (memLp_freqBump_mul n u).aestronglyMeasurable).1 hnorm

/-- Every polynomial moment of a frequency cutoff is integrable. -/
private lemma integrable_pow_freqCutoff (n k : ℕ) (u : Lp ℂ 2 (volume : Measure V)) :
    Integrable (fun x ↦ ‖x‖ ^ k * ‖freqCutoff n u x‖) volume := by
  refine (integrable_pow_mul_freqBump n k u).congr ?_
  filter_upwards with x
  simp [freqCutoff]

/-- The inverse Fourier integral of a frequency cutoff is smooth. -/
lemma contDiff_fourierInv_freqCutoff (n : ℕ) (u : Lp ℂ 2 (volume : Measure V)) :
    ContDiff ℝ (⊤ : ℕ∞) (𝓕⁻ (freqCutoff n u)) := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (𝓕 (freqCutoff n u)) :=
    contDiff_fourier fun k _ ↦ integrable_pow_freqCutoff n k u
  have hEq : 𝓕⁻ (freqCutoff n u) = fun x ↦ 𝓕 (freqCutoff n u) (-x) := by
    ext x
    exact fourierInv_eq_fourier_neg _ x
  rw [hEq]
  exact hF.comp (contDiff_id.neg)

/-- Directional derivative of the inverse Fourier integral along `eⱼ`. -/
lemma fderiv_fourierInv_freqCutoff_coord (n : ℕ) (j : Fin d)
    (u : Lp ℂ 2 (volume : Measure V)) (x : V) :
    fderiv ℝ (𝓕⁻ (freqCutoff n u)) x (coordVec j) =
      𝓕⁻ (fun v ↦ (2 * π * I) * (v j : ℂ) * freqCutoff n u v) x := by
  have hint := integrable_freqCutoff n u
  have hmom : Integrable (fun v ↦ ‖v‖ * ‖freqCutoff n u v‖) volume := by
    refine (integrable_pow_freqCutoff n 1 u).congr ?_
    filter_upwards with v
    simp [pow_one]
  have hfun : 𝓕⁻ (freqCutoff n u) = fun y ↦ 𝓕 (freqCutoff n u) (-y) := by
    ext y
    exact fourierInv_eq_fourier_neg _ y
  have hneg : HasFDerivAt (fun y : V ↦ -y) (-ContinuousLinearMap.id ℝ V) x := by
    simpa using (hasFDerivAt_id x).fun_neg
  have hF : HasFDerivAt (𝓕 (freqCutoff n u))
      (fderiv ℝ (𝓕 (freqCutoff n u)) (-x)) (-x) :=
    (differentiable_fourier hint hmom).differentiableAt.hasFDerivAt
  rw [hfun]
  change (fderiv ℝ (𝓕 (freqCutoff n u) ∘ Neg.neg) x) (coordVec j) = _
  rw [(hF.comp x hneg).fderiv]
  rw [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id, neg_apply]
  rw [fderiv_fourier hint hmom]
  have hmeas : AEStronglyMeasurable
      (fun v ↦ fourierSMulRight (innerSL ℝ) (freqCutoff n u) v) volume :=
    (memLp_freqBump_mul n u).aestronglyMeasurable.fourierSMulRight
  have hintL : Integrable
      (fun v ↦ fourierSMulRight (innerSL ℝ) (freqCutoff n u) v) volume := by
    rw [← integrable_norm_iff hmeas]
    refine (hmom.const_mul (2 * π)).congr ?_
    filter_upwards with v
    rw [norm_fourierSMulRight, innerSL_apply_norm]
    ring
  rw [fourier_continuousLinearMap_apply hintL, fourierInv_eq_fourier_neg]
  have hmulv : (fun v ↦ fourierSMulRight (innerSL ℝ) (freqCutoff n u) v (coordVec j)) =
      fun v ↦ -(2 * π * I) * (v j : ℂ) * freqCutoff n u v := by
    ext v
    rw [fourierSMulRight_apply, innerSL_apply_apply, coordVec,
      EuclideanSpace.inner_single_right]
    simp [smul_eq_mul, Complex.real_smul, mul_assoc]
  rw [hmulv]
  have hnegF : 𝓕 (fun v ↦ -(2 * π * I) * (v j : ℂ) * freqCutoff n u v) (-x) =
      -𝓕 (fun v ↦ (2 * π * I) * (v j : ℂ) * freqCutoff n u v) (-x) := by
    simp [fourier_eq, mul_assoc, neg_mul, integral_neg]
  rw [hnegF, neg_neg]

/-- Complex coordinate cutoff `φₙ`. -/
@[expose]
def freqBumpScaled (n : ℕ) : V → ℂ :=
  fun x ↦ (freqBump n x : ℂ)

/-- Unfolding the complex cutoff. -/
lemma freqBumpScaled_apply (n : ℕ) (x : V) : freqBumpScaled n x = (freqBump n x : ℂ) := rfl

/-- The complex cutoff has temperate growth. -/
private lemma freqBumpScaled_hasTemperateGrowth (n : ℕ) :
    Function.HasTemperateGrowth (freqBumpScaled n : V → ℂ) := by
  have hEq : (freqBumpScaled n : V → ℂ) = Complex.ofReal ∘ (freqBump n : V → ℝ) :=
      rfl
  rw [hEq]
  exact Complex.hasTemperateGrowth_ofReal.comp
    ((hasCompactSupport_freqBump n).hasTemperateGrowth
      (contDiff_freqBump n))

/-- The complex cutoff lies in `L^∞`. -/
lemma memLp_top_freqBumpScaled (n : ℕ) :
    MemLp (freqBumpScaled n : V → ℂ) ∞ volume := by
  have hsup : HasCompactSupport (freqBumpScaled n : V → ℂ) := by
    have hEq : (freqBumpScaled n : V → ℂ) = Complex.ofReal ∘ (freqBump n : V → ℝ) :=
      rfl
    rw [hEq]
    exact (hasCompactSupport_freqBump n).comp_left (g := Complex.ofReal) (by simp)
  exact (Complex.ofRealCLM.continuous.comp
    (contDiff_freqBump n).continuous).memLp_top_of_hasCompactSupport hsup volume

/-- Complexified derivative of the cutoff along `eⱼ`. -/
@[expose]
def freqBumpDeriv (n : ℕ) (j : Fin d) : V → ℂ :=
  fun x ↦ (fderiv ℝ (freqBump n) x (coordVec j) : ℂ)

/-- Unfolding the complexified cutoff derivative. -/
lemma freqBumpDeriv_apply (n : ℕ) (j : Fin d) (x : V) :
    freqBumpDeriv n j x = (fderiv ℝ (freqBump n) x (coordVec j) : ℂ) := rfl

/-- The complexified cutoff derivative is the chain-rule derivative of `φₙ`. -/
private lemma freqBumpDeriv_eq_fderiv (n : ℕ) (j : Fin d) (x : V) :
    fderiv ℝ (freqBumpScaled n) x (coordVec j) = freqBumpDeriv n j x := by
  have hEq : (freqBumpScaled n : V → ℂ) = (Complex.ofRealCLM : ℝ → ℂ) ∘ (freqBump n : V → ℝ) :=
      rfl
  have hf : DifferentiableAt ℝ (freqBump n) x :=
    ((contDiff_freqBump n).differentiable (by simp)) x
  rw [hEq, freqBumpDeriv]
  rw [fderiv_comp (f := (freqBump n : V → ℝ)) x
    Complex.ofRealCLM.differentiableAt hf]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv]
  rfl

/-- The cutoff derivative is smooth. -/
private lemma freqBumpDeriv_contDiff (n : ℕ) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (freqBumpDeriv n j) := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (freqBump n : V → ℝ) :=
    contDiff_freqBump n
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (freqBump n)) :=
    (contDiff_infty_iff_fderiv.mp hφ).2
  have happly : ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ fderiv ℝ (freqBump n) x (coordVec j)) :=
    (ContinuousLinearMap.apply ℝ ℝ (coordVec j)).contDiff.comp hfd
  have hEq : freqBumpDeriv n j =
      Complex.ofReal ∘ fun x ↦ fderiv ℝ (freqBump n) x (coordVec j) := by
    rfl
  rw [hEq]
  exact Complex.ofRealCLM.contDiff.comp happly

/-- The cutoff derivative has compact support. -/
private lemma freqBumpDeriv_hasCompactSupport (n : ℕ) (j : Fin d) :
    HasCompactSupport (freqBumpDeriv n j) := by
  have hreal : HasCompactSupport
      (fun x ↦ fderiv ℝ (freqBump n) x (coordVec j)) :=
    (hasCompactSupport_freqBump n).fderiv_apply ℝ (coordVec j)
  have hEq : freqBumpDeriv n j =
      Complex.ofReal ∘ fun x ↦ fderiv ℝ (freqBump n) x (coordVec j) := by
    rfl
  rw [hEq]
  exact hreal.comp_left (g := Complex.ofReal) (by simp)

/-- The cutoff derivative has temperate growth. -/
private lemma freqBumpDeriv_hasTemperateGrowth (n : ℕ) (j : Fin d) :
    (freqBumpDeriv n j).HasTemperateGrowth :=
  (freqBumpDeriv_hasCompactSupport n j).hasTemperateGrowth (freqBumpDeriv_contDiff n j)

/-- The cutoff derivative lies in `L^∞`. -/
lemma memLp_top_freqBumpDeriv (n : ℕ) (j : Fin d) :
    MemLp (freqBumpDeriv n j) ∞ volume :=
  (freqBumpDeriv_contDiff n j).continuous.memLp_top_of_hasCompactSupport
    (freqBumpDeriv_hasCompactSupport n j) volume

/-- Pointwise size of the cutoff derivative. -/
private lemma freqBumpDeriv_norm_le (j : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, ‖freqBumpDeriv n j x‖ ≤ C / ((n : ℝ) + 1) := by
  obtain ⟨C, hC, h⟩ := exists_norm_fderiv_freqBump_le j
  refine ⟨C, hC, fun n x ↦ ?_⟩
  rw [freqBumpDeriv, Complex.norm_real]
  exact h n x

/-- `L^∞` norm of the cutoff derivative is `O(1 / n)`. -/
lemma exists_norm_toLp_freqBumpDeriv_le (j : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      ‖(memLp_top_freqBumpDeriv n j).toLp (freqBumpDeriv n j)‖ ≤
        C / ((n : ℝ) + 1) := by
  obtain ⟨C, hC, h⟩ := freqBumpDeriv_norm_le j
  refine ⟨C, hC, fun n ↦ ?_⟩
  rw [Lp.norm_toLp,
    eLpNorm_exponent_top (memLp_top_freqBumpDeriv n j).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (div_nonneg hC (by positivity))
    (eLpNormEssSup_le_of_ae_bound (Eventually.of_forall (h n)))

/-- Heterogeneous product by `φₙ` agrees with the pointwise cutoff. -/
lemma toLp_freqCutoff_eq_smul (n : ℕ) (u : Lp ℂ 2 (volume : Measure V)) :
    (memLp_freqBump_mul n u).toLp (freqCutoff n u) =
      HSMul.hSMul (γ := Lp ℂ 2 (volume : Measure V))
        ((memLp_top_freqBumpScaled n).toLp (freqBumpScaled n) :
          Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V)) u := by
  symm
  rw [Lp.smul_def]
  refine MemLp.toLp_congr _ _ ?_
  filter_upwards [(memLp_top_freqBumpScaled n).coeFn_toLp] with x hb
  simp only [Pi.smul_apply']
  rw [hb]
  simp [freqBumpScaled, freqCutoff, smul_eq_mul]

/-- Distributional multiplication by `φₙ` agrees with the `L²` product. -/
lemma toLp_freqCutoff_eq_smulLeftCLM (n : ℕ) (u : Lp ℂ 2 (volume : Measure V)) :
    ((memLp_freqBump_mul n u).toLp (freqCutoff n u) : TemperedDistribution V ℂ) =
      TemperedDistribution.smulLeftCLM ℂ (freqBumpScaled n)
        (u : TemperedDistribution V ℂ) := by
  rw [toLp_freqCutoff_eq_smul]
  exact Lp.toTemperedDistribution_smul_eq (freqBumpScaled_hasTemperateGrowth n)
    (memLp_top_freqBumpScaled n) u

/-- Distributional multiplication by `∂ⱼφₙ` agrees with the `L²` product. -/
lemma toLp_freqBumpDeriv_smul_eq_smulLeftCLM (n : ℕ) (j : Fin d)
    (u : Lp ℂ 2 (volume : Measure V)) :
    (((memLp_top_freqBumpDeriv n j).toLp (freqBumpDeriv n j) • u :
        Lp ℂ 2 (volume : Measure V)) : TemperedDistribution V ℂ) =
      TemperedDistribution.smulLeftCLM ℂ (freqBumpDeriv n j)
        (u : TemperedDistribution V ℂ) :=
  Lp.toTemperedDistribution_smul_eq (freqBumpDeriv_hasTemperateGrowth n j)
    (memLp_top_freqBumpDeriv n j) u

/-- Product rule for the cutoff on Schwartz functions. -/
private lemma lineDeriv_freqBump_mul (n : ℕ) (j : Fin d) (ζ : SchwartzMap V ℂ) :
    ∂_{coordVec j} (SchwartzMap.smulLeftCLM ℂ (freqBumpScaled n) ζ) =
      SchwartzMap.smulLeftCLM ℂ (freqBumpScaled n) (∂_{coordVec j} ζ) +
        SchwartzMap.smulLeftCLM ℂ (freqBumpDeriv n j) ζ := by
  ext x
  have hφ : Function.HasTemperateGrowth (freqBumpScaled n : V → ℂ) :=
    freqBumpScaled_hasTemperateGrowth n
  have hderiv := freqBumpDeriv_hasTemperateGrowth n j
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, add_apply,
    SchwartzMap.smulLeftCLM_apply_apply hφ, SchwartzMap.smulLeftCLM_apply_apply hderiv]
  have hfun : (SchwartzMap.smulLeftCLM ℂ (freqBumpScaled n) ζ : V → ℂ) =
      fun y ↦ freqBumpScaled n y * ζ y := by
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply hφ]
    simp [smul_eq_mul]
  rw [hfun, fderiv_fun_mul ((freqBumpScaled_hasTemperateGrowth n).1.differentiable
        (by simp) x) ζ.differentiableAt, add_apply, smul_apply, smul_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, freqBumpDeriv_eq_fderiv]
  simp [smul_eq_mul]
  exact mul_comm _ _

/-- Distributional product rule for cutoff multiplication on `L²`. -/
lemma lineDeriv_smulLeftCLM_freqBumpScaled (n : ℕ) (j : Fin d)
    (u : Lp ℂ 2 (volume : Measure V)) :
    ∂_{coordVec j} (TemperedDistribution.smulLeftCLM ℂ (freqBumpScaled n)
        (u : TemperedDistribution V ℂ)) =
      TemperedDistribution.smulLeftCLM ℂ (freqBumpScaled n)
          (∂_{coordVec j} (u : TemperedDistribution V ℂ)) +
        TemperedDistribution.smulLeftCLM ℂ (freqBumpDeriv n j)
          (u : TemperedDistribution V ℂ) := by
  ext ζ
  have hpr := lineDeriv_freqBump_mul n j ζ
  simp only [TemperedDistribution.lineDerivOp_apply_apply,
    TemperedDistribution.smulLeftCLM_apply_apply]
  have hsch : SchwartzMap.smulLeftCLM ℂ (freqBumpScaled n) (-∂_{coordVec j} ζ) =
      -∂_{coordVec j} (SchwartzMap.smulLeftCLM ℂ (freqBumpScaled n) ζ) +
        SchwartzMap.smulLeftCLM ℂ (freqBumpDeriv n j) ζ := by
    rw [(SchwartzMap.smulLeftCLM ℂ (freqBumpScaled n)).map_neg]
    have hsub : SchwartzMap.smulLeftCLM ℂ (freqBumpScaled n) (∂_{coordVec j} ζ) =
        ∂_{coordVec j} (SchwartzMap.smulLeftCLM ℂ (freqBumpScaled n) ζ) -
          SchwartzMap.smulLeftCLM ℂ (freqBumpDeriv n j) ζ := by
      rw [hpr, add_sub_cancel_right]
    rw [hsub, neg_sub, sub_eq_add_neg, add_comm]
  rw [hsch]
  simp [map_add, map_neg]

end HeisenbergAux

end CKMA.Heisenberg
