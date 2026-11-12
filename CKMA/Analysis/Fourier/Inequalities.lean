/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Order.Compact

/-!
# Coordinate uncertainty

Coordinate uncertainty for unit-norm L² data bounds the product of the physical and
Fourier-side second moments by `1/(4π)`, at Mathlib's `exp(-2πi x·ξ)` normalization.

Source: GAPS 27.13.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter MeasureTheory FourierTransform Real Complex VectorFourier Topology
open scoped ENNReal FourierTransform RealInnerProductSpace ComplexInnerProductSpace LineDeriv
  Topology

section HeisenbergAux

variable {d : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin d)

private lemma pi_pos_four : 0 < 4 * (Real.pi : ℝ) := by
  positivity

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
private def coordVec (j : Fin d) : V :=
  EuclideanSpace.single j 1

/-- The `j`-th coordinate of `eⱼ` is `1`. -/
private lemma coordVec_apply (j : Fin d) : coordVec j j = 1 := by
  simp [coordVec]

/-- Each coordinate vector is a unit vector. -/
private lemma norm_coordVec (j : Fin d) : ‖coordVec j‖ = 1 := by
  simp [coordVec, PiLp.norm_single]

/-- The coordinate `x ↦ xⱼ`, as a complex scalar. -/
private def coordFun (j : Fin d) : V → ℂ :=
  fun x ↦ (x j : ℂ)

/-- The complex coordinate agrees with the real inner product against `eⱼ`. -/
private lemma coordFun_eq_inner (j : Fin d) (x : V) :
    coordFun j x = (inner ℝ x (coordVec j) : ℂ) := by
  simp [coordFun, coordVec, EuclideanSpace.inner_single_right]

/-- Coordinate multiplication has temperate growth. -/
private lemma coordFun_hasTemperateGrowth (j : Fin d) :
    (coordFun j).HasTemperateGrowth := by
  have h := (Complex.ofRealCLM.comp (EuclideanSpace.proj j)).hasTemperateGrowth
  convert h using 1
  ext x
  simp [coordFun, ContinuousLinearMap.comp_apply]

/-- Integration by parts for `‖g‖²` against the coordinate `xⱼ`. The derivative is the
Fréchet derivative in the direction `eⱼ`, and both weighted factors are square-integrable. -/
private lemma integral_norm_sq_le_two_mul_coord
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
private lemma norm_two_pi_I : ‖(2 * π * I : ℂ)‖ = 2 * π := by
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_two,
    Complex.norm_of_nonneg Real.pi_pos.le]

/-- The scalar `2πi` is nonzero. -/
private lemma two_pi_I_ne_zero : (2 * π * I : ℂ) ≠ 0 := by
  simp [Complex.I_ne_zero, Real.pi_ne_zero]

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
  rw [hx, SchwartzMap.smulLeftCLM_apply_apply (coordFun_hasTemperateGrowth j)]
  simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Distributional derivative of `𝓕 f` along `eⱼ`, represented by an `L²` function. -/
private lemma lineDeriv_fourier_lp_eq (j : Fin d)
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

/-- Integration by parts for the distributional derivative of `𝓕 f`. -/
private lemma integral_fourier_lineDeriv_eq (j : Fin d)
    (f : Lp ℂ 2 (volume : Measure V))
    (hx : MemLp (fun x ↦ coordFun j x * f x) 2 volume)
    (ζ : SchwartzMap V ℂ) :
    ∫ x, (∂_{coordVec j} ζ) x * (𝓕 f) x ∂volume =
      -∫ x, ζ x *
        (𝓕 (-(2 * π * I : ℂ) • hx.toLp (fun x ↦ coordFun j x * f x))) x ∂volume := by
  have hdist := lineDeriv_fourier_lp_eq j f hx
  have happly := congrArg (fun T : TemperedDistribution V ℂ ↦ T ζ) hdist
  rw [TemperedDistribution.lineDerivOp_apply_apply, Lp.fourier_toTemperedDistribution_eq,
    Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply] at happly
  simp only [smul_eq_mul] at happly
  have hneg : ∫ x, (-∂_{coordVec j} ζ) x * (𝓕 f) x ∂volume =
      -∫ x, (∂_{coordVec j} ζ) x * (𝓕 f) x ∂volume := by
    simp [integral_neg, neg_mul]
  apply neg_eq_iff_eq_neg.mp
  rw [← hneg]
  exact happly

/-- `L²` norm of the Fourier transform of the weighted spatial moment. -/
private lemma norm_fourier_coord_eq (j : Fin d) (f : Lp ℂ 2 (volume : Measure V))
    (hx : MemLp (fun x ↦ coordFun j x * f x) 2 volume) :
    ‖𝓕 (-(2 * π * I : ℂ) • hx.toLp (fun x ↦ coordFun j x * f x))‖ =
      2 * π * ‖hx.toLp (fun x ↦ coordFun j x * f x)‖ := by
  rw [FourierTransform.fourier_smul, norm_smul, norm_neg, Lp.norm_fourier_eq, norm_two_pi_I]

/-- Smooth bump equal to one on the unit ball and supported in the ball of radius two. -/
private def heisenbergBaseBump : ContDiffBump (0 : V) :=
  ⟨1, 2, zero_lt_one, one_lt_two⟩

/-- Frequency cutoff at scale `n + 1`. -/
private def heisenbergFreqBump (n : ℕ) (x : V) : ℝ :=
  (heisenbergBaseBump : ContDiffBump (0 : V)) (((n : ℝ) + 1)⁻¹ • x)

/-- The frequency cutoff is smooth. -/
private lemma heisenbergFreqBump_contDiff (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (heisenbergFreqBump n : V → ℝ) := by
  refine ((heisenbergBaseBump : ContDiffBump (0 : V)).contDiff (n := (⊤ : ℕ∞))).comp ?_
  exact (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ V).contDiff

/-- The frequency cutoff has compact support. -/
private lemma heisenbergFreqBump_hasCompactSupport (n : ℕ) :
    HasCompactSupport (heisenbergFreqBump n : V → ℝ) := by
  refine HasCompactSupport.intro
    (K := Metric.closedBall (0 : V) (2 * ((n : ℝ) + 1))) (isCompact_closedBall _ _) ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  rw [heisenbergFreqBump]
  apply (heisenbergBaseBump : ContDiffBump (0 : V)).zero_of_le_dist
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < ((n : ℝ) + 1)⁻¹)]
  calc (2 : ℝ)
      = 2 * ((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹ := by field_simp
    _ ≤ ‖x‖ * ((n : ℝ) + 1)⁻¹ := by gcongr
    _ = ((n : ℝ) + 1)⁻¹ * ‖x‖ := by ring

/-- The frequency cutoff takes values in the unit interval. -/
private lemma heisenbergFreqBump_mem_Icc (n : ℕ) (x : V) :
    heisenbergFreqBump n x ∈ Set.Icc 0 1 := by
  rw [heisenbergFreqBump]
  exact ⟨(heisenbergBaseBump : ContDiffBump (0 : V)).nonneg,
    (heisenbergBaseBump : ContDiffBump (0 : V)).le_one⟩

/-- On each point the cutoff is eventually equal to one. -/
private lemma heisenbergFreqBump_eventually_one (x : V) :
    ∀ᶠ n in Filter.atTop, heisenbergFreqBump n x = 1 := by
  refine Filter.eventually_atTop.2 ⟨Nat.ceil ‖x‖, fun n hn ↦ ?_⟩
  rw [heisenbergFreqBump]
  apply (heisenbergBaseBump : ContDiffBump (0 : V)).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < ((n : ℝ) + 1)⁻¹)]
  rw [inv_mul_le_iff₀ (by positivity)]
  have hr : (heisenbergBaseBump : ContDiffBump (0 : V)).rIn = 1 := rfl
  rw [hr, mul_one]
  exact (Nat.ceil_le.mp hn).trans (le_add_of_nonneg_right zero_le_one)

/-- Derivative of the cutoff along `eⱼ` is `O(1 / n)`. -/
private lemma heisenbergFreqBump_fderiv_le (j : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x,
      ‖fderiv ℝ (heisenbergFreqBump n) x (coordVec j)‖ ≤ C / ((n : ℝ) + 1) := by
  have hcont : Continuous fun x ↦ ‖fderiv ℝ (⇑(heisenbergBaseBump : ContDiffBump (0 : V))) x‖ :=
    continuous_norm.comp
      (((heisenbergBaseBump : ContDiffBump (0 : V)).contDiff
        (n := (⊤ : ℕ∞))).continuous_fderiv (by simp))
  have hsup : HasCompactSupport fun x ↦
      ‖fderiv ℝ (⇑(heisenbergBaseBump : ContDiffBump (0 : V))) x‖ :=
    (heisenbergBaseBump : ContDiffBump (0 : V)).hasCompactSupport.fderiv ℝ |>.norm
  obtain ⟨x0, hx0⟩ := hcont.exists_forall_ge_of_hasCompactSupport hsup
  refine ⟨‖fderiv ℝ (⇑(heisenbergBaseBump : ContDiffBump (0 : V))) x0‖, norm_nonneg _,
    fun n x ↦ ?_⟩
  have hf := fderiv_comp_smul (𝕜 := ℝ)
    (f := (⇑(heisenbergBaseBump : ContDiffBump (0 : V))))
    (c := ((n : ℝ) + 1)⁻¹) (x := x)
  have hfun : (heisenbergFreqBump n : V → ℝ) = fun y ↦
      (heisenbergBaseBump : ContDiffBump (0 : V)) (((n : ℝ) + 1)⁻¹ • y) := by
    ext y
    rfl
  rw [hfun, hf, smul_apply]
  calc ‖((n : ℝ) + 1)⁻¹ •
        (fderiv ℝ (⇑(heisenbergBaseBump : ContDiffBump (0 : V))) (((n : ℝ) + 1)⁻¹ • x))
          (coordVec j)‖
      = ((n : ℝ) + 1)⁻¹ * ‖(fderiv ℝ (⇑(heisenbergBaseBump : ContDiffBump (0 : V)))
          (((n : ℝ) + 1)⁻¹ • x)) (coordVec j)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ((n : ℝ) + 1)⁻¹)]
    _ ≤ ((n : ℝ) + 1)⁻¹ * (‖fderiv ℝ (⇑(heisenbergBaseBump : ContDiffBump (0 : V)))
          (((n : ℝ) + 1)⁻¹ • x)‖ * ‖coordVec j‖) := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ((n : ℝ) + 1)⁻¹ * ‖fderiv ℝ (⇑(heisenbergBaseBump : ContDiffBump (0 : V)))
          (((n : ℝ) + 1)⁻¹ • x)‖ := by
        rw [norm_coordVec, mul_one]
    _ ≤ ((n : ℝ) + 1)⁻¹ * ‖fderiv ℝ (⇑(heisenbergBaseBump : ContDiffBump (0 : V))) x0‖ := by
        gcongr
        exact hx0 _
    _ = ‖fderiv ℝ (⇑(heisenbergBaseBump : ContDiffBump (0 : V))) x0‖ / ((n : ℝ) + 1) := by
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
private lemma freqBump_mul_memLp (n : ℕ) (u : Lp ℂ 2 (volume : Measure V)) :
    MemLp (fun x ↦ (heisenbergFreqBump n x : ℂ) * u x) 2 volume := by
  refine mul_memLp_of_norm_le_one ?_ ?_ u
  · exact (Complex.ofRealCLM.continuous.comp
      (heisenbergFreqBump_contDiff n).continuous).aestronglyMeasurable
  · intro x
    have hφ := heisenbergFreqBump_mem_Icc n x
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hφ.1]
    exact hφ.2

/-- The complex scalar `φₙ(x) - 1` has absolute value at most one. -/
private lemma sub_one_freqBump_norm_le (n : ℕ) (x : V) :
    ‖(heisenbergFreqBump n x : ℂ) - 1‖ ≤ 1 := by
  have hφ := heisenbergFreqBump_mem_Icc n x
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hφ.2)]
  linarith [hφ.1]

/-- Multiplication by `φₙ - 1` preserves `L²`. -/
private lemma sub_one_freqBump_mul_memLp (n : ℕ) (u : Lp ℂ 2 (volume : Measure V)) :
    MemLp (fun x ↦ ((heisenbergFreqBump n x : ℂ) - 1) * u x) 2 volume := by
  refine mul_memLp_of_norm_le_one ?_ (sub_one_freqBump_norm_le n) u
  exact (((Complex.ofRealCLM.continuous.comp
    (heisenbergFreqBump_contDiff n).continuous).sub continuous_const).aestronglyMeasurable)

/-- Cutoff multiplication converges to the original class in `L²`. -/
private lemma tendsto_freqBump_mul (u : Lp ℂ 2 (volume : Measure V)) :
    Tendsto (fun n ↦ (freqBump_mul_memLp n u).toLp
      (fun x ↦ (heisenbergFreqBump n x : ℂ) * u x)) atTop (𝓝 u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let dlt : ℕ → Lp ℂ 2 (volume : Measure V) := fun n ↦
    (sub_one_freqBump_mul_memLp n u).toLp
      (fun x ↦ ((heisenbergFreqBump n x : ℂ) - 1) * u x)
  have hdlt (n : ℕ) : (freqBump_mul_memLp n u).toLp
      (fun x ↦ (heisenbergFreqBump n x : ℂ) * u x) - u = dlt n := by
    apply Lp.ext
    filter_upwards [(freqBump_mul_memLp n u).coeFn_toLp,
      (sub_one_freqBump_mul_memLp n u).coeFn_toLp,
      Lp.coeFn_sub ((freqBump_mul_memLp n u).toLp
        (fun x ↦ (heisenbergFreqBump n x : ℂ) * u x)) u] with x hφu hsub hdiff
    rw [hdiff, Pi.sub_apply, hφu, hsub]
    ring
  have hnorm (n : ℕ) : ‖dlt n‖ ^ 2 =
      ∫ x, ‖((heisenbergFreqBump n x : ℂ) - 1) * u x‖ ^ 2 ∂volume := by
    rw [norm_sq_eq_integral_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [(sub_one_freqBump_mul_memLp n u).coeFn_toLp] with x hx
    simp [dlt, hx]
  have hbound_int : Integrable (fun x ↦ ‖u x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).1 (Lp.memLp u)
  have hlim : Tendsto (fun n ↦ ∫ x, ‖((heisenbergFreqBump n x : ℂ) - 1) * u x‖ ^ 2 ∂volume)
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
      calc ‖((heisenbergFreqBump n x : ℂ) - 1) * u x‖
          = ‖(heisenbergFreqBump n x : ℂ) - 1‖ * ‖u x‖ := norm_mul _ _
        _ ≤ 1 * ‖u x‖ := by gcongr; exact sub_one_freqBump_norm_le n x
        _ = ‖u x‖ := one_mul _
    · filter_upwards with x
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [heisenbergFreqBump_eventually_one x] with n hn
      have hzero : ((heisenbergFreqBump n x : ℂ) - 1) * u x = 0 := by
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
    Integrable (fun x ↦ ‖x‖ ^ k * ‖(heisenbergFreqBump n x : ℂ) * u x‖) volume := by
  let b : V → ℝ := fun x ↦ ‖x‖ ^ k * heisenbergFreqBump n x
  have hb_cont : Continuous b :=
    (continuous_norm.pow k).mul (heisenbergFreqBump_contDiff n).continuous
  have hb_sup : HasCompactSupport b :=
    (heisenbergFreqBump_hasCompactSupport n).mul_left (f := fun x ↦ ‖x‖ ^ k)
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
  have hφ := heisenbergFreqBump_mem_Icc n x
  simp only [b, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hφ.1, abs_of_nonneg (pow_nonneg (norm_nonneg _) _), mul_assoc]

/-- Pointwise product of an `L²` class by the frequency cutoff. -/
private abbrev freqCutoff (n : ℕ) (u : Lp ℂ 2 (volume : Measure V)) : V → ℂ :=
  fun x ↦ (heisenbergFreqBump n x : ℂ) * u x

/-- The frequency cutoff of an `L²` function is integrable. -/
private lemma integrable_freqCutoff (n : ℕ) (u : Lp ℂ 2 (volume : Measure V)) :
    Integrable (freqCutoff n u) volume := by
  have hnorm : Integrable (fun x ↦ ‖freqCutoff n u x‖) volume := by
    refine (integrable_pow_mul_freqBump n 0 u).congr ?_
    filter_upwards with x
    simp [freqCutoff, pow_zero]
  exact (integrable_norm_iff (freqBump_mul_memLp n u).aestronglyMeasurable).1 hnorm

/-- Every polynomial moment of a frequency cutoff is integrable. -/
private lemma integrable_pow_freqCutoff (n k : ℕ) (u : Lp ℂ 2 (volume : Measure V)) :
    Integrable (fun x ↦ ‖x‖ ^ k * ‖freqCutoff n u x‖) volume := by
  refine (integrable_pow_mul_freqBump n k u).congr ?_
  filter_upwards with x
  simp [freqCutoff]

/-- The inverse Fourier integral of a frequency cutoff is smooth. -/
private lemma contDiff_fourierInv_freqCutoff (n : ℕ) (u : Lp ℂ 2 (volume : Measure V)) :
    ContDiff ℝ (⊤ : ℕ∞) (𝓕⁻ (freqCutoff n u)) := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (𝓕 (freqCutoff n u)) :=
    contDiff_fourier fun k _ ↦ integrable_pow_freqCutoff n k u
  have hEq : 𝓕⁻ (freqCutoff n u) = fun x ↦ 𝓕 (freqCutoff n u) (-x) := by
    ext x
    exact fourierInv_eq_fourier_neg _ x
  rw [hEq]
  exact hF.comp (contDiff_id.neg)

/-- Directional derivative of the inverse Fourier integral along `eⱼ`. -/
private lemma fderiv_fourierInv_freqCutoff_coord (n : ℕ) (j : Fin d)
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
    (freqBump_mul_memLp n u).aestronglyMeasurable.fourierSMulRight
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
private def freqBumpCLM (n : ℕ) : V → ℂ :=
  fun x ↦ (heisenbergFreqBump n x : ℂ)

/-- The complex cutoff has temperate growth. -/
private lemma freqBumpCLM_hasTemperateGrowth (n : ℕ) :
    Function.HasTemperateGrowth (freqBumpCLM n : V → ℂ) := by
  have hEq : (freqBumpCLM n : V → ℂ) =
      Complex.ofReal ∘ (heisenbergFreqBump n : V → ℝ) := by
    ext; rfl
  rw [hEq]
  exact Complex.hasTemperateGrowth_ofReal.comp
    ((heisenbergFreqBump_hasCompactSupport n).hasTemperateGrowth
      (heisenbergFreqBump_contDiff n))

/-- The complex cutoff lies in `L^∞`. -/
private lemma freqBumpCLM_memLp_top (n : ℕ) :
    MemLp (freqBumpCLM n : V → ℂ) ∞ volume := by
  have hsup : HasCompactSupport (freqBumpCLM n : V → ℂ) := by
    have hEq : (freqBumpCLM n : V → ℂ) =
        Complex.ofReal ∘ (heisenbergFreqBump n : V → ℝ) := by
      ext; rfl
    rw [hEq]
    exact (heisenbergFreqBump_hasCompactSupport n).comp_left (g := Complex.ofReal) (by simp)
  exact (Complex.ofRealCLM.continuous.comp
    (heisenbergFreqBump_contDiff n).continuous).memLp_top_of_hasCompactSupport hsup volume

/-- Complexified derivative of the cutoff along `eⱼ`. -/
private def freqBumpDeriv (n : ℕ) (j : Fin d) : V → ℂ :=
  fun x ↦ (fderiv ℝ (heisenbergFreqBump n) x (coordVec j) : ℂ)

/-- The complexified cutoff derivative is the chain-rule derivative of `φₙ`. -/
private lemma freqBumpDeriv_eq_fderiv (n : ℕ) (j : Fin d) (x : V) :
    fderiv ℝ (freqBumpCLM n) x (coordVec j) = freqBumpDeriv n j x := by
  have hEq : (freqBumpCLM n : V → ℂ) =
      (Complex.ofRealCLM : ℝ → ℂ) ∘ (heisenbergFreqBump n : V → ℝ) := by
    ext; rfl
  have hf : DifferentiableAt ℝ (heisenbergFreqBump n) x :=
    ((heisenbergFreqBump_contDiff n).differentiable (by simp)) x
  rw [hEq, freqBumpDeriv]
  rw [fderiv_comp (f := (heisenbergFreqBump n : V → ℝ)) x
    Complex.ofRealCLM.differentiableAt hf]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv]
  rfl

/-- The cutoff derivative is smooth. -/
private lemma freqBumpDeriv_contDiff (n : ℕ) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (freqBumpDeriv n j) := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (heisenbergFreqBump n : V → ℝ) :=
    heisenbergFreqBump_contDiff n
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (heisenbergFreqBump n)) :=
    (contDiff_infty_iff_fderiv.mp hφ).2
  have happly : ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ fderiv ℝ (heisenbergFreqBump n) x (coordVec j)) :=
    (ContinuousLinearMap.apply ℝ ℝ (coordVec j)).contDiff.comp hfd
  have hEq : freqBumpDeriv n j =
      Complex.ofReal ∘ fun x ↦ fderiv ℝ (heisenbergFreqBump n) x (coordVec j) := by
    ext; rfl
  rw [hEq]
  exact Complex.ofRealCLM.contDiff.comp happly

/-- The cutoff derivative has compact support. -/
private lemma freqBumpDeriv_hasCompactSupport (n : ℕ) (j : Fin d) :
    HasCompactSupport (freqBumpDeriv n j) := by
  have hreal : HasCompactSupport
      (fun x ↦ fderiv ℝ (heisenbergFreqBump n) x (coordVec j)) :=
    (heisenbergFreqBump_hasCompactSupport n).fderiv_apply ℝ (coordVec j)
  have hEq : freqBumpDeriv n j =
      Complex.ofReal ∘ fun x ↦ fderiv ℝ (heisenbergFreqBump n) x (coordVec j) := by
    ext; rfl
  rw [hEq]
  exact hreal.comp_left (g := Complex.ofReal) (by simp)

/-- The cutoff derivative has temperate growth. -/
private lemma freqBumpDeriv_hasTemperateGrowth (n : ℕ) (j : Fin d) :
    (freqBumpDeriv n j).HasTemperateGrowth :=
  (freqBumpDeriv_hasCompactSupport n j).hasTemperateGrowth (freqBumpDeriv_contDiff n j)

/-- The cutoff derivative lies in `L^∞`. -/
private lemma freqBumpDeriv_memLp_top (n : ℕ) (j : Fin d) :
    MemLp (freqBumpDeriv n j) ∞ volume :=
  (freqBumpDeriv_contDiff n j).continuous.memLp_top_of_hasCompactSupport
    (freqBumpDeriv_hasCompactSupport n j) volume

/-- Pointwise size of the cutoff derivative. -/
private lemma freqBumpDeriv_norm_le (j : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, ‖freqBumpDeriv n j x‖ ≤ C / ((n : ℝ) + 1) := by
  obtain ⟨C, hC, h⟩ := heisenbergFreqBump_fderiv_le j
  refine ⟨C, hC, fun n x ↦ ?_⟩
  rw [freqBumpDeriv, Complex.norm_real]
  exact h n x

/-- `L^∞` norm of the cutoff derivative is `O(1 / n)`. -/
private lemma freqBumpDeriv_lpNorm_le (j : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      ‖(freqBumpDeriv_memLp_top n j).toLp (freqBumpDeriv n j)‖ ≤
        C / ((n : ℝ) + 1) := by
  obtain ⟨C, hC, h⟩ := freqBumpDeriv_norm_le j
  refine ⟨C, hC, fun n ↦ ?_⟩
  rw [Lp.norm_toLp,
    eLpNorm_exponent_top (freqBumpDeriv_memLp_top n j).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (div_nonneg hC (by positivity))
    (eLpNormEssSup_le_of_ae_bound (Eventually.of_forall (h n)))

/-- Heterogeneous product by `φₙ` agrees with the pointwise cutoff. -/
private lemma freqBump_smul_eq_toLp (n : ℕ) (u : Lp ℂ 2 (volume : Measure V)) :
    (freqBump_mul_memLp n u).toLp (freqCutoff n u) =
      HSMul.hSMul (γ := Lp ℂ 2 (volume : Measure V))
        ((freqBumpCLM_memLp_top n).toLp (freqBumpCLM n) :
          Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V)) u := by
  symm
  rw [Lp.smul_def]
  refine MemLp.toLp_congr _ _ ?_
  filter_upwards [(freqBumpCLM_memLp_top n).coeFn_toLp] with x hb
  simp only [Pi.smul_apply']
  rw [hb]
  simp [freqBumpCLM, freqCutoff, smul_eq_mul]

/-- Distributional multiplication by `φₙ` agrees with the `L²` product. -/
private lemma freqBump_smul_eq_smulLeft (n : ℕ) (u : Lp ℂ 2 (volume : Measure V)) :
    ((freqBump_mul_memLp n u).toLp (freqCutoff n u) : TemperedDistribution V ℂ) =
      TemperedDistribution.smulLeftCLM ℂ (freqBumpCLM n)
        (u : TemperedDistribution V ℂ) := by
  rw [freqBump_smul_eq_toLp]
  exact Lp.toTemperedDistribution_smul_eq (freqBumpCLM_hasTemperateGrowth n)
    (freqBumpCLM_memLp_top n) u

/-- Distributional multiplication by `∂ⱼφₙ` agrees with the `L²` product. -/
private lemma freqBumpDeriv_smul_eq_smulLeft (n : ℕ) (j : Fin d)
    (u : Lp ℂ 2 (volume : Measure V)) :
    (((freqBumpDeriv_memLp_top n j).toLp (freqBumpDeriv n j) • u :
        Lp ℂ 2 (volume : Measure V)) : TemperedDistribution V ℂ) =
      TemperedDistribution.smulLeftCLM ℂ (freqBumpDeriv n j)
        (u : TemperedDistribution V ℂ) :=
  Lp.toTemperedDistribution_smul_eq (freqBumpDeriv_hasTemperateGrowth n j)
    (freqBumpDeriv_memLp_top n j) u

/-- Product rule for the cutoff on Schwartz functions. -/
private lemma lineDeriv_freqBump_mul (n : ℕ) (j : Fin d) (ζ : SchwartzMap V ℂ) :
    ∂_{coordVec j} (SchwartzMap.smulLeftCLM ℂ (freqBumpCLM n) ζ) =
      SchwartzMap.smulLeftCLM ℂ (freqBumpCLM n) (∂_{coordVec j} ζ) +
        SchwartzMap.smulLeftCLM ℂ (freqBumpDeriv n j) ζ := by
  ext x
  have hφ : Function.HasTemperateGrowth (freqBumpCLM n : V → ℂ) :=
    freqBumpCLM_hasTemperateGrowth n
  have hderiv := freqBumpDeriv_hasTemperateGrowth n j
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, add_apply,
    SchwartzMap.smulLeftCLM_apply_apply hφ, SchwartzMap.smulLeftCLM_apply_apply hderiv]
  have hfun : (SchwartzMap.smulLeftCLM ℂ (freqBumpCLM n) ζ : V → ℂ) =
      fun y ↦ freqBumpCLM n y * ζ y := by
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply hφ]
    simp [smul_eq_mul]
  rw [hfun, fderiv_fun_mul ((freqBumpCLM_hasTemperateGrowth n).1.differentiable
        (by simp) x) ζ.differentiableAt, add_apply, smul_apply, smul_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, freqBumpDeriv_eq_fderiv]
  simp [smul_eq_mul]
  exact mul_comm _ _

/-- Distributional product rule for cutoff multiplication on `L²`. -/
private lemma lineDeriv_freqBump_lp (n : ℕ) (j : Fin d)
    (u : Lp ℂ 2 (volume : Measure V)) :
    ∂_{coordVec j} (TemperedDistribution.smulLeftCLM ℂ (freqBumpCLM n)
        (u : TemperedDistribution V ℂ)) =
      TemperedDistribution.smulLeftCLM ℂ (freqBumpCLM n)
          (∂_{coordVec j} (u : TemperedDistribution V ℂ)) +
        TemperedDistribution.smulLeftCLM ℂ (freqBumpDeriv n j)
          (u : TemperedDistribution V ℂ) := by
  ext ζ
  have hpr := lineDeriv_freqBump_mul n j ζ
  simp only [TemperedDistribution.lineDerivOp_apply_apply,
    TemperedDistribution.smulLeftCLM_apply_apply]
  have hsch : SchwartzMap.smulLeftCLM ℂ (freqBumpCLM n) (-∂_{coordVec j} ζ) =
      -∂_{coordVec j} (SchwartzMap.smulLeftCLM ℂ (freqBumpCLM n) ζ) +
        SchwartzMap.smulLeftCLM ℂ (freqBumpDeriv n j) ζ := by
    rw [(SchwartzMap.smulLeftCLM ℂ (freqBumpCLM n)).map_neg]
    have hsub : SchwartzMap.smulLeftCLM ℂ (freqBumpCLM n) (∂_{coordVec j} ζ) =
        ∂_{coordVec j} (SchwartzMap.smulLeftCLM ℂ (freqBumpCLM n) ζ) -
          SchwartzMap.smulLeftCLM ℂ (freqBumpDeriv n j) ζ := by
      rw [hpr, add_sub_cancel_right]
    rw [hsub, neg_sub, sub_eq_add_neg, add_comm]
  rw [hsch]
  simp [map_add, map_neg]

/-- Reflected self-adjointness of the Fourier integral. -/
private lemma integral_fourier_mul_neg {u : V → ℂ} (hu : Integrable u volume)
    (φ : SchwartzMap V ℂ) :
    ∫ x, 𝓕 u x * (φ : V → ℂ) (-x) ∂volume =
      ∫ x, u x * 𝓕 (fun y ↦ (φ : V → ℂ) (-y)) x ∂volume := by
  have hg : Integrable (fun x ↦ (φ : V → ℂ) (-x)) volume :=
    (integrable_comp (LinearIsometryEquiv.neg ℝ) (φ : V → ℂ)).2
      (SchwartzMap.integrable (μ := volume) φ)
  simpa [ContinuousLinearMap.mul_apply', flip_innerₗ] using!
    VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ V) (μ := volume) (ν := volume)
      continuous_fourierChar continuous_inner hu hg

/-- The inverse Fourier integral is self-adjoint on `L¹` against Schwartz functions. -/
private lemma integral_fourierInv_mul {u : V → ℂ} (hu : Integrable u volume)
    (φ : SchwartzMap V ℂ) :
    ∫ x, 𝓕⁻ u x * (φ : V → ℂ) x ∂volume =
      ∫ x, u x * 𝓕⁻ (φ : V → ℂ) x ∂volume := by
  have hchg : ∫ x, 𝓕 u (-x) * (φ : V → ℂ) x ∂volume =
      ∫ x, 𝓕 u x * (φ : V → ℂ) (-x) ∂volume := by
    have h := integral_comp (LinearIsometryEquiv.neg ℝ)
      (fun x ↦ 𝓕 u (-x) * (φ : V → ℂ) x)
    simpa [neg_neg] using h.symm
  have hinv : ∀ x, 𝓕⁻ u x = 𝓕 u (-x) := fun x ↦ fourierInv_eq_fourier_neg _ x
  simp_rw [hinv]
  rw [hchg, integral_fourier_mul_neg hu φ]
  simp [fourierInv_eq_fourier_comp_neg]

/-- The inverse Fourier integral of an integrable function is continuous. -/
private lemma continuous_fourierInv_of_integrable {u : V → ℂ} (hu : Integrable u volume) :
    Continuous (𝓕⁻ u) := by
  have hEq : 𝓕⁻ u = fun x ↦ 𝓕 u (-x) := by
    ext x
    exact fourierInv_eq_fourier_neg _ x
  rw [hEq]
  refine Continuous.comp ?_ continuous_neg
  have hF : 𝓕 u = VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) u := rfl
  rw [hF]
  exact VectorFourier.fourierIntegral_continuous continuous_fourierChar continuous_inner hu

/-- Agreement of the two inverse Fourier transforms on `L¹ ∩ L²`. -/
private lemma fourierInv_congr_ae {u v : V → ℂ} (h : u =ᵐ[volume] v) (x : V) :
    𝓕⁻ u x = 𝓕⁻ v x := by
  rw [fourierInv_eq_fourier_neg, fourierInv_eq_fourier_neg, fourier_congr_ae h]

/-- The integral inverse Fourier transform represents the `L²` inverse transform. -/
private lemma fourierInv_ae_eq_lp {u : V → ℂ} (hu1 : Integrable u volume)
    (hu2 : MemLp u 2 volume) :
    𝓕⁻ u =ᵐ[volume] fun x ↦ (𝓕⁻ (hu2.toLp u) : Lp ℂ 2 (volume : Measure V)) x := by
  let gLp : Lp ℂ 2 (volume : Measure V) := 𝓕⁻ (hu2.toLp u)
  apply ae_eq_of_integral_contDiff_smul_eq
    (continuous_fourierInv_of_integrable hu1).locallyIntegrable
    ((Lp.memLp gLp).locallyIntegrable one_le_two)
  intro ψ hψ hψsup
  let ψC : V → ℂ := fun x ↦ (ψ x : ℂ)
  have hψC : ContDiff ℝ (⊤ : ℕ∞) ψC := Complex.ofRealCLM.contDiff.comp hψ
  have hsupC : HasCompactSupport ψC :=
    hψsup.comp_left (g := Complex.ofReal) (by simp)
  let ζ : SchwartzMap V ℂ := hsupC.toSchwartzMap hψC
  have hcoe : (ζ : V → ℂ) = ψC := by
    ext x
    rfl
  have hintL : Integrable (fun x ↦ ψC x * 𝓕⁻ u x) volume :=
    ((hψC.continuous).mul (continuous_fourierInv_of_integrable hu1)).integrable_of_hasCompactSupport
      (hsupC.mul_right)
  have hintR : Integrable (fun x ↦ ψC x * gLp x) volume := by
    have hmul : MemLp (fun x ↦ (ζ : V → ℂ) x * gLp x) 1 volume :=
      (SchwartzMap.memLp ζ 2 volume).mul (Lp.memLp gLp)
    simpa [hcoe] using (memLp_one_iff_integrable).1 hmul
  have hreal : ∀ x, ψ x • 𝓕⁻ u x = ψC x * 𝓕⁻ u x := by
    intro x
    simp [ψC, Complex.real_smul]
  have hreal' : ∀ x, ψ x • gLp x = ψC x * gLp x := by
    intro x
    simp [ψC, Complex.real_smul]
  rw [integral_congr_ae (ae_of_all volume hreal),
    integral_congr_ae (ae_of_all volume hreal')]
  rw [show (fun x ↦ ψC x * 𝓕⁻ u x) = fun x ↦ 𝓕⁻ u x * (ζ : V → ℂ) x by
    ext x; simp [hcoe, mul_comm]]
  rw [integral_fourierInv_mul hu1 ζ]
  rw [show (fun x ↦ u x * 𝓕⁻ (ζ : V → ℂ) x) = fun x ↦ (𝓕⁻ ζ) x * u x by
    ext x; rw [SchwartzMap.fourierInv_coe]; ring]
  have hg : (gLp : TemperedDistribution V ℂ) =
      𝓕⁻ (hu2.toLp u : TemperedDistribution V ℂ) :=
    (Lp.fourierInv_toTemperedDistribution_eq (hu2.toLp u)).symm
  have happly := congrArg (fun T : TemperedDistribution V ℂ ↦ T ζ) hg
  rw [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply] at happly
  simp only [smul_eq_mul] at happly
  rw [show (fun x ↦ ψC x * gLp x) = fun x ↦ (ζ : V → ℂ) x * gLp x by
    ext x; simp [hcoe]]
  rw [happly]
  refine integral_congr_ae ?_
  filter_upwards [hu2.coeFn_toLp] with x hx
  rw [hx]

/-- The inverse Fourier transform preserves the `L²` norm. -/
private lemma norm_fourierInv_eq (u : Lp ℂ 2 (volume : Measure V)) : ‖𝓕⁻ u‖ = ‖u‖ := by
  rw [← Lp.norm_fourier_eq (𝓕⁻ u), fourier_fourierInv_eq]

/-- `L²` representative of the distributional derivative of `φₙ 𝓕 f`. -/
private def cutoffDerivLp (n : ℕ) (j : Fin d) (f : Lp ℂ 2 (volume : Measure V))
    (hx : MemLp (fun x ↦ coordFun j x * f x) 2 volume) : Lp ℂ 2 (volume : Measure V) :=
  HSMul.hSMul (γ := Lp ℂ 2 (volume : Measure V))
      ((freqBumpCLM_memLp_top (d := d) n).toLp (freqBumpCLM n) :
        Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V))
      (𝓕 (-(2 * π * I : ℂ) • hx.toLp (fun x ↦ coordFun j x * f x))) +
    HSMul.hSMul (γ := Lp ℂ 2 (volume : Measure V))
      ((freqBumpDeriv_memLp_top n j).toLp (freqBumpDeriv n j) :
        Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V)) (𝓕 f)

/-- The distributional derivative of the cutoff of `𝓕 f` is `cutoffDerivLp`. -/
private lemma lineDeriv_freqCutoff_eq (n : ℕ) (j : Fin d) (f : Lp ℂ 2 (volume : Measure V))
    (hx : MemLp (fun x ↦ coordFun j x * f x) 2 volume) :
    ∂_{coordVec j}
        ((freqBump_mul_memLp n (𝓕 f)).toLp (freqCutoff n (𝓕 f)) :
          TemperedDistribution V ℂ) =
      (cutoffDerivLp n j f hx : TemperedDistribution V ℂ) := by
  let Dû : Lp ℂ 2 (volume : Measure V) :=
    𝓕 (-(2 * π * I : ℂ) • hx.toLp (fun x ↦ coordFun j x * f x))
  rw [freqBump_smul_eq_smulLeft]
  rw [lineDeriv_freqBump_lp]
  nth_rw 1 [← Lp.fourier_toTemperedDistribution_eq f]
  rw [lineDeriv_fourier_lp_eq j f hx]
  rw [← freqBump_smul_eq_smulLeft n Dû]
  rw [← freqBumpDeriv_smul_eq_smulLeft n j (𝓕 f)]
  rw [freqBump_smul_eq_toLp, cutoffDerivLp]
  exact ((Lp.toTemperedDistributionCLM ℂ (volume : Measure V) 2).map_add _ _).symm

/-- Multiplication by the cutoff derivative tends to zero in `L²`. -/
private lemma tendsto_freqBumpDeriv_smul (j : Fin d) (u : Lp ℂ 2 (volume : Measure V)) :
    Tendsto (fun n ↦ HSMul.hSMul (γ := Lp ℂ 2 (volume : Measure V))
      ((freqBumpDeriv_memLp_top n j).toLp (freqBumpDeriv n j) :
        Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V)) u) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  obtain ⟨C, _, hCle⟩ := freqBumpDeriv_lpNorm_le j
  have hupper : Tendsto (fun n : ℕ ↦ C / ((n : ℝ) + 1) * ‖u‖) atTop (𝓝 (0 : ℝ)) := by
    have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    simpa [div_eq_mul_inv] using (hinv.const_mul C).mul_const ‖u‖
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hupper
  · exact (Lp.norm_smul_le _ _).trans
      (mul_le_mul_of_nonneg_right (hCle n) (norm_nonneg _))

/-- Frequency cutoff of the Fourier-side coordinate moment. -/
private abbrev freqMomentCut (n : ℕ) (j : Fin d) (f : Lp ℂ 2 (volume : Measure V))
    (hξ : MemLp (fun ξ ↦ coordFun j ξ * (𝓕 f) ξ) 2 volume) :
    Lp ℂ 2 (volume : Measure V) :=
  let ξLp := hξ.toLp (fun ξ ↦ coordFun j ξ * (𝓕 f) ξ)
  (freqBump_mul_memLp n ξLp).toLp (freqCutoff n ξLp)

/-- The coordinate derivative of the cutoff inverse transform is the weighted moment. -/
private lemma fderiv_cutoff_ae (n : ℕ) (j : Fin d) (f : Lp ℂ 2 (volume : Measure V))
    (hξ : MemLp (fun ξ ↦ coordFun j ξ * (𝓕 f) ξ) 2 volume) :
    (fun x ↦ fderiv ℝ (𝓕⁻ (freqCutoff n (𝓕 f))) x (coordVec j)) =ᵐ[volume]
      fun x ↦ (𝓕⁻ ((2 * π * I : ℂ) • freqMomentCut n j f hξ)) x := by
  let c : ℂ := 2 * π * I
  let ξLp : Lp ℂ 2 (volume : Measure V) := hξ.toLp (fun ξ ↦ coordFun j ξ * (𝓕 f) ξ)
  let ξCut : Lp ℂ 2 (volume : Measure V) := freqMomentCut n j f hξ
  let ψ : V → ℂ := fun v ↦ c * (v j : ℂ) * freqCutoff n (𝓕 f) v
  have hderiv : ∀ x, fderiv ℝ (𝓕⁻ (freqCutoff n (𝓕 f))) x (coordVec j) = 𝓕⁻ ψ x :=
    fun x ↦ fderiv_fourierInv_freqCutoff_coord n j (𝓕 f) x
  have hψ : ψ =ᵐ[volume] fun v ↦ c * freqCutoff n ξLp v := by
    filter_upwards [hξ.coeFn_toLp] with v hξv
    simp only [ψ, freqCutoff]
    rw [hξv]
    simp only [coordFun]
    ring
  have hcoe : (fun v ↦ (c • ξCut) v) =ᵐ[volume] fun v ↦ c * freqCutoff n ξLp v := by
    filter_upwards [Lp.coeFn_smul c ξCut, (freqBump_mul_memLp n ξLp).coeFn_toLp] with v hc hcut
    simp only [ξCut, freqMomentCut]
    rw [hc, Pi.smul_apply, smul_eq_mul, hcut]
  have hint : Integrable (fun v ↦ (c • ξCut) v) volume :=
    (integrable_congr hcoe).2 ((integrable_freqCutoff n ξLp).smul c)
  have hae := fourierInv_ae_eq_lp hint (Lp.memLp (c • ξCut))
  filter_upwards [hae, hψ, hcoe] with x hx hψx hcoex
  rw [hderiv]
  rw [fourierInv_congr_ae hψ]
  rw [fourierInv_congr_ae hcoe.symm]
  rw [hx]
  rw [Lp.toLp_coeFn _ (Lp.memLp (c • ξCut))]

/-- Coordinate weight of the cutoff inverse transform, identified in `L²`. -/
private lemma coord_mul_cutoff_ae (n : ℕ) (j : Fin d) (f : Lp ℂ 2 (volume : Measure V))
    (hx : MemLp (fun x ↦ coordFun j x * f x) 2 volume) :
    (fun x ↦ coordFun j x * 𝓕⁻ (freqCutoff n (𝓕 f)) x) =ᵐ[volume]
      fun x ↦ ((-(2 * π * I : ℂ))⁻¹ • 𝓕⁻ (cutoffDerivLp n j f hx)) x := by
  let uLp : Lp ℂ 2 (volume : Measure V) :=
    (freqBump_mul_memLp n (𝓕 f)).toLp (freqCutoff n (𝓕 f))
  let w : Lp ℂ 2 (volume : Measure V) := cutoffDerivLp n j f hx
  let g : V → ℂ := 𝓕⁻ (freqCutoff n (𝓕 f))
  let gLp : Lp ℂ 2 (volume : Measure V) := 𝓕⁻ uLp
  let c : ℂ := -(2 * π * I)
  have hFT : 𝓕⁻ (w : TemperedDistribution V ℂ) =
      c • TemperedDistribution.smulLeftCLM ℂ (coordFun j) (gLp : TemperedDistribution V ℂ) := by
    have hderiv : (w : TemperedDistribution V ℂ) =
        ∂_{coordVec j} (uLp : TemperedDistribution V ℂ) :=
      (lineDeriv_freqCutoff_eq n j f hx).symm
    rw [hderiv]
    rw [TemperedDistribution.fourierInv_lineDerivOp_eq]
    rw [Lp.fourierInv_toTemperedDistribution_eq uLp]
    have hinner : coordFun j = fun x ↦ (inner ℝ x (coordVec j) : ℂ) := by
      ext x; exact coordFun_eq_inner j x
    have hsmul : TemperedDistribution.smulLeftCLM ℂ (coordFun j)
          (gLp : TemperedDistribution V ℂ) =
        TemperedDistribution.smulLeftCLM ℂ (fun x ↦ (inner ℝ x (coordVec j) : ℂ))
          (gLp : TemperedDistribution V ℂ) := by rw [hinner]
    rw [← hsmul]
  have hg_ae : g =ᵐ[volume] fun x ↦ gLp x :=
    fourierInv_ae_eq_lp (integrable_freqCutoff n (𝓕 f)) (freqBump_mul_memLp n (𝓕 f))
  apply ae_eq_of_integral_contDiff_smul_eq
    ((coordFun_hasTemperateGrowth j).1.continuous.mul
      (continuous_fourierInv_of_integrable (integrable_freqCutoff n (𝓕 f)))).locallyIntegrable
    ((Lp.memLp (c⁻¹ • 𝓕⁻ w)).locallyIntegrable one_le_two)
  intro ψ hψ hsup
  let ψC : V → ℂ := fun x ↦ (ψ x : ℂ)
  have hψC : ContDiff ℝ (⊤ : ℕ∞) ψC := Complex.ofRealCLM.contDiff.comp hψ
  have hsupC : HasCompactSupport ψC := hsup.comp_left (g := Complex.ofReal) (by simp)
  let ζ : SchwartzMap V ℂ := hsupC.toSchwartzMap hψC
  have hcoe : (ζ : V → ℂ) = ψC := by ext x; rfl
  have hreal : ∀ x, ψ x • (coordFun j * g) x = ψC x * (coordFun j x * g x) := by
    intro x
    rw [Pi.mul_apply]
    simp [ψC, Complex.real_smul]
  have hreal' : ∀ x, ψ x • (c⁻¹ • 𝓕⁻ w) x = ψC x * (c⁻¹ • 𝓕⁻ w) x := by
    intro x; simp [ψC, Complex.real_smul]
  rw [integral_congr_ae (ae_of_all volume hreal), integral_congr_ae (ae_of_all volume hreal')]
  rw [Lp.fourierInv_toTemperedDistribution_eq] at hFT
  have happly := congrArg (fun T : TemperedDistribution V ℂ ↦ T ζ) hFT
  rw [smul_apply] at happly
  rw [TemperedDistribution.smulLeftCLM_apply_apply] at happly
  rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply] at happly
  simp only [smul_eq_mul] at happly
  have hζg : (fun x ↦ ((SchwartzMap.smulLeftCLM ℂ (coordFun j)) ζ) x * gLp x) =
      fun x ↦ ζ x * (coordFun j x * gLp x) := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply (coordFun_hasTemperateGrowth j)]
    simp only [smul_eq_mul]
    ring
  have hpair : ∫ (x : V), ζ x * (𝓕⁻ w) x =
      c * ∫ (x : V), ζ x * (coordFun j x * gLp x) := by
    simpa [hζg] using happly
  have hc : c ≠ 0 := by
    simpa only [c, neg_ne_zero] using two_pi_I_ne_zero
  have hmul : ∫ (x : V), ζ x * (c⁻¹ * (𝓕⁻ w) x) =
      ∫ (x : V), ζ x * (coordFun j x * gLp x) := by
    apply mul_left_cancel₀ hc
    have hscale : (fun x ↦ c * (ζ x * (c⁻¹ * (𝓕⁻ w) x))) =
        fun x ↦ ζ x * (𝓕⁻ w) x := by
      ext x
      have hrearr : c * (ζ x * (c⁻¹ * (𝓕⁻ w) x)) =
          (c * c⁻¹) * (ζ x * (𝓕⁻ w) x) := by ring
      rw [hrearr, mul_inv_cancel₀ hc, one_mul]
    calc
      c * ∫ (x : V), ζ x * (c⁻¹ * (𝓕⁻ w) x)
          = ∫ (x : V), c * (ζ x * (c⁻¹ * (𝓕⁻ w) x)) := by
            rw [← integral_const_mul]
      _ = ∫ (x : V), ζ x * (𝓕⁻ w) x := by rw [hscale]
      _ = c * ∫ (x : V), ζ x * (coordFun j x * gLp x) := hpair
  have hψζ : (fun x ↦ ψC x * (coordFun j x * g x)) =
      fun x ↦ ζ x * (coordFun j x * g x) := by
    ext x; rw [← congrFun hcoe x]
  have hζψ : (fun x ↦ ζ x * (c⁻¹ • 𝓕⁻ w) x) =
      fun x ↦ ψC x * (c⁻¹ • 𝓕⁻ w) x := by
    ext x; rw [congrFun hcoe x]
  calc
    ∫ (x : V), ψC x * (coordFun j x * g x)
        = ∫ (x : V), ζ x * (coordFun j x * g x) := by rw [hψζ]
    _ = ∫ (x : V), ζ x * (coordFun j x * gLp x) := by
          refine integral_congr_ae ?_
          filter_upwards [hg_ae] with x hxg
          rw [hxg]
    _ = ∫ (x : V), ζ x * (c⁻¹ * (𝓕⁻ w) x) := hmul.symm
    _ = ∫ (x : V), ζ x * (c⁻¹ • 𝓕⁻ w) x := by
          refine integral_congr_ae ?_
          filter_upwards [Lp.coeFn_smul c⁻¹ (𝓕⁻ w)] with x hsm
          rw [hsm, Pi.smul_apply, smul_eq_mul]
    _ = ∫ (x : V), ψC x * (c⁻¹ • 𝓕⁻ w) x := by rw [hζψ]

/-- Cutoff form of the commutator estimate. -/
private lemma cutoff_sq_le (n : ℕ) (j : Fin d) (f : Lp ℂ 2 (volume : Measure V))
    (hx : MemLp (fun x ↦ coordFun j x * f x) 2 volume)
    (hξ : MemLp (fun ξ ↦ coordFun j ξ * (𝓕 f) ξ) 2 volume) :
    ‖(freqBump_mul_memLp n (𝓕 f)).toLp (freqCutoff n (𝓕 f))‖ ^ 2 ≤
      2 * ‖cutoffDerivLp n j f hx‖ * ‖freqMomentCut n j f hξ‖ := by
  let uLp : Lp ℂ 2 (volume : Measure V) :=
    (freqBump_mul_memLp n (𝓕 f)).toLp (freqCutoff n (𝓕 f))
  let g : V → ℂ := 𝓕⁻ (freqCutoff n (𝓕 f))
  let c : ℂ := -(2 * π * I)
  have hgcont : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_fourierInv_freqCutoff n (𝓕 f)
  have hgae : g =ᵐ[volume] fun x ↦ (𝓕⁻ uLp) x :=
    fourierInv_ae_eq_lp (integrable_freqCutoff n (𝓕 f)) (freqBump_mul_memLp n (𝓕 f))
  have hgmem : MemLp g 2 volume := (Lp.memLp (𝓕⁻ uLp)).ae_eq hgae.symm
  have hxae := coord_mul_cutoff_ae n j f hx
  have hxmem : MemLp (fun x ↦ coordFun j x * g x) 2 volume :=
    (Lp.memLp (c⁻¹ • 𝓕⁻ (cutoffDerivLp n j f hx))).ae_eq hxae.symm
  have hdae := fderiv_cutoff_ae n j f hξ
  have hdmem : MemLp (fun x ↦ fderiv ℝ g x (coordVec j)) 2 volume :=
    (Lp.memLp (𝓕⁻ ((2 * π * I : ℂ) • freqMomentCut n j f hξ))).ae_eq hdae.symm
  have hNg : ‖hgmem.toLp g‖ = ‖uLp‖ := by
    rw [show hgmem.toLp g = 𝓕⁻ uLp from
      (MemLp.toLp_congr hgmem (Lp.memLp (𝓕⁻ uLp)) hgae).trans
        (Lp.toLp_coeFn (𝓕⁻ uLp) (Lp.memLp (𝓕⁻ uLp)))]
    exact norm_fourierInv_eq uLp
  have hNx : ‖hxmem.toLp (fun x ↦ coordFun j x * g x)‖ =
      ‖c⁻¹‖ * ‖cutoffDerivLp n j f hx‖ := by
    rw [show hxmem.toLp (fun x ↦ coordFun j x * g x) =
        c⁻¹ • 𝓕⁻ (cutoffDerivLp n j f hx) from
      (MemLp.toLp_congr hxmem (Lp.memLp (c⁻¹ • 𝓕⁻ (cutoffDerivLp n j f hx))) hxae).trans
        (Lp.toLp_coeFn _ (Lp.memLp _))]
    rw [norm_smul, norm_fourierInv_eq]
  have hNd : ‖hdmem.toLp (fun x ↦ fderiv ℝ g x (coordVec j))‖ =
      (2 * π) * ‖freqMomentCut n j f hξ‖ := by
    rw [show hdmem.toLp (fun x ↦ fderiv ℝ g x (coordVec j)) =
        𝓕⁻ ((2 * π * I : ℂ) • freqMomentCut n j f hξ) from
      (MemLp.toLp_congr hdmem
        (Lp.memLp (𝓕⁻ ((2 * π * I : ℂ) • freqMomentCut n j f hξ))) hdae).trans
        (Lp.toLp_coeFn _ (Lp.memLp _))]
    rw [norm_fourierInv_eq, norm_smul, norm_two_pi_I]
  have hinv : ‖c⁻¹‖ = (2 * π)⁻¹ := by rw [norm_inv, norm_neg, norm_two_pi_I]
  have hbase := integral_norm_sq_le_two_mul_coord j hgcont hgmem hxmem hdmem
  calc ‖uLp‖ ^ 2 = ‖hgmem.toLp g‖ ^ 2 := by rw [hNg]
    _ ≤ 2 * ‖hxmem.toLp (fun x ↦ coordFun j x * g x)‖ *
        ‖hdmem.toLp (fun x ↦ fderiv ℝ g x (coordVec j))‖ := hbase
    _ = 2 * (‖cutoffDerivLp n j f hx‖ * (2 * π)⁻¹) * ((2 * π) * ‖freqMomentCut n j f hξ‖) := by
      rw [hNx, hNd, hinv]
      ring
    _ = 2 * ‖cutoffDerivLp n j f hx‖ * ‖freqMomentCut n j f hξ‖ := by field_simp

/-- Unit-norm coordinate uncertainty for the explicit coordinate weight. -/
private lemma heisenberg_aux (j : Fin d) (f : Lp ℂ 2 (volume : Measure V)) (hf : ‖f‖ = 1)
    (hx : MemLp (fun x ↦ coordFun j x * f x) 2 volume)
    (hξ : MemLp (fun ξ ↦ coordFun j ξ * (𝓕 f) ξ) 2 volume) :
    (1 / (4 * π) : ℝ) ≤ (eLpNorm (fun x ↦ coordFun j x * f x) 2 volume).toReal *
      (eLpNorm (fun ξ ↦ coordFun j ξ * (𝓕 f) ξ) 2 volume).toReal := by
  let xf := hx.toLp (fun x ↦ coordFun j x * f x)
  let ξf := hξ.toLp (fun ξ ↦ coordFun j ξ * (𝓕 f) ξ)
  let Dû : Lp ℂ 2 (volume : Measure V) := 𝓕 (-(2 * π * I : ℂ) • xf)
  have hD : ‖Dû‖ = 2 * π * ‖xf‖ := norm_fourier_coord_eq j f hx
  have hun : Tendsto (fun n ↦ ‖(freqBump_mul_memLp n (𝓕 f)).toLp (freqCutoff n (𝓕 f))‖)
      atTop (𝓝 ‖f‖) := by
    have h := (continuous_norm.tendsto (𝓕 f)).comp (tendsto_freqBump_mul (𝓕 f))
    rwa [Lp.norm_fourier_eq] at h
  have hξn : Tendsto (fun n ↦ ‖freqMomentCut n j f hξ‖) atTop (𝓝 ‖ξf‖) :=
    (continuous_norm.tendsto ξf).comp (tendsto_freqBump_mul ξf)
  have hφ : Tendsto (fun n ↦ HSMul.hSMul (γ := Lp ℂ 2 (volume : Measure V))
      ((freqBumpCLM_memLp_top (d := d) n).toLp (freqBumpCLM n) :
        Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V)) Dû) atTop (𝓝 Dû) :=
    (tendsto_congr fun n ↦ freqBump_smul_eq_toLp n Dû).mp (tendsto_freqBump_mul Dû)
  have hw : Tendsto (fun n ↦ ‖cutoffDerivLp n j f hx‖) atTop (𝓝 ‖Dû‖) := by
    have hsum := hφ.add (tendsto_freqBumpDeriv_smul j (𝓕 f))
    have hEq : ∀ n, cutoffDerivLp n j f hx =
        HSMul.hSMul (γ := Lp ℂ 2 (volume : Measure V))
          ((freqBumpCLM_memLp_top (d := d) n).toLp (freqBumpCLM n) :
            Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V)) Dû +
        HSMul.hSMul (γ := Lp ℂ 2 (volume : Measure V))
          ((freqBumpDeriv_memLp_top n j).toLp (freqBumpDeriv n j) :
            Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V)) (𝓕 f) := fun _ ↦ rfl
    have hsum0 : Tendsto (fun n ↦ cutoffDerivLp n j f hx) atTop (𝓝 Dû) :=
      (tendsto_congr fun n ↦ (hEq n).symm).mp (by simpa [add_zero] using hsum)
    exact (continuous_norm.tendsto Dû).comp hsum0
  have hineq : ∀ n, ‖(freqBump_mul_memLp n (𝓕 f)).toLp (freqCutoff n (𝓕 f))‖ ^ 2 ≤
      2 * ‖cutoffDerivLp n j f hx‖ * ‖freqMomentCut n j f hξ‖ :=
    fun n ↦ cutoff_sq_le n j f hx hξ
  have hlim : ‖f‖ ^ 2 ≤ 2 * ‖Dû‖ * ‖ξf‖ :=
    le_of_tendsto_of_tendsto' ((continuous_pow 2).tendsto ‖f‖ |>.comp hun)
      ((tendsto_const_nhds.mul hw).mul hξn) hineq
  have hfour : ‖f‖ ^ 2 ≤ 4 * π * ‖xf‖ * ‖ξf‖ := by
    rw [hD] at hlim
    calc ‖f‖ ^ 2 ≤ 2 * (2 * π * ‖xf‖) * ‖ξf‖ := hlim
      _ = 4 * π * ‖xf‖ * ‖ξf‖ := by ring
  have hunit : (1 : ℝ) ≤ 4 * π * ‖xf‖ * ‖ξf‖ := by simpa [hf] using hfour
  suffices (1 / (4 * π) : ℝ) ≤ ‖xf‖ * ‖ξf‖ by
    simpa only [xf, ξf, Lp.norm_toLp] using this
  rw [div_le_iff₀ pi_pos_four]
  calc (1 : ℝ) ≤ 4 * π * ‖xf‖ * ‖ξf‖ := hunit
    _ = ‖xf‖ * ‖ξf‖ * (4 * π) := by ring

end HeisenbergAux

/-- **27.13**: coordinate uncertainty at Mathlib's `exp(-2πix·ξ)` normalization.
The input and Fourier-side second moments are explicit, and the input has unit `L²` norm. -/
theorem heisenberg_uncertainty {d : ℕ} (j : Fin d)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hf : ‖f‖ = 1)
    (hx : MemLp (fun x ↦ (x j : ℂ) * f x) 2 volume)
    (hξ : MemLp (fun ξ ↦ (ξ j : ℂ) * (𝓕 f) ξ) 2 volume) :
    (1 / (4 * Real.pi) : ℝ) ≤
      (eLpNorm (fun x ↦ (x j : ℂ) * f x) 2 volume).toReal *
      (eLpNorm (fun ξ ↦ (ξ j : ℂ) * (𝓕 f) ξ) 2 volume).toReal :=
  heisenberg_aux j f hf hx hξ

end CKMA
