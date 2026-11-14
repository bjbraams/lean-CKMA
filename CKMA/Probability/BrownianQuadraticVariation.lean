/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.BrownianQuadraticVariation.TimePartition
public import CKMA.Probability.BrownianQuadraticVariation.KolmogorovMaximal
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Brownian quadratic variation and covariation (08.7)

`TimePartition` records ordered deterministic nodes, allowing repeated nodes and the
zero time interval. Its mesh controls quadratic and bilinear covariation sums formed
from completed partition intervals. The main statements give uniform convergence in
probability, almost-sure convergence under a summable mesh condition, and cross-coordinate
covariation for independent Brownian coordinates.

The process interface is pre-Brownian: for a sequence of deterministic partitions only
countably many evaluation times are involved. Time and partition nodes are nonnegative
reals; covariance normalization is the standard Brownian one.

The uniform estimate is Kolmogorov's maximal inequality applied to the centered sum of
squared increments. The Gaussian fourth moment is read from the fourth derivative of the
moment-generating function. Cross variation reduces to quadratic variation by polarization.

## Main definitions

* `CKMA.TimePartition`: finite deterministic partition of `[0, T]`
  (in `BrownianQuadraticVariation.TimePartition`).
* `CKMA.TimePartition.mesh`: largest time increment of a partition
  (in `BrownianQuadraticVariation.TimePartition`).
* `CKMA.TimePartition.covariation`: quadratic covariation sum over completed partition intervals
  (in `BrownianQuadraticVariation.TimePartition`).

## Main results

* `CKMA.brownian_quadraticVariation_ucp`: uniform-on-compact convergence in probability of
  Brownian quadratic variation along deterministic partitions with vanishing mesh.
* `CKMA.brownian_quadraticVariation_ae`: almost-sure uniform convergence under summable meshes.
* `CKMA.brownian_covariation_ucp`: diagonal quadratic covariation for independent Brownian
  coordinates.

## Notation

No new notation is introduced in this file.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped NNReal ENNReal ProbabilityTheory BigOperators
open Classical
open MeasureTheory ProbabilityTheory Filter Topology

/-- Real Gaussian parameter of one partition increment. -/
private lemma increment_eq_nndist {T : ℝ≥0} (π : TimePartition T) (i : Fin π.size) :
    (nndist (π.node i.succ : ℝ) (π.node i.castSucc : ℝ) : ℝ) = π.increment i := by
  have hle : π.node i.castSucc ≤ π.node i.succ := π.monotone_node (Fin.castSucc_le_succ i)
  have hnonneg : 0 ≤ (π.node i.succ : ℝ) - π.node i.castSucc :=
    sub_nonneg.mpr (NNReal.coe_le_coe.mpr hle)
  calc
    (nndist (π.node i.succ : ℝ) (π.node i.castSucc : ℝ) : ℝ)
        = |(π.node i.succ : ℝ) - π.node i.castSucc| := by
          simp [nndist_eq_nnnorm, Real.norm_eq_abs]
    _ = (π.node i.succ : ℝ) - π.node i.castSucc := abs_of_nonneg hnonneg
    _ = π.increment i := by simp [TimePartition.increment, NNReal.coe_sub hle]

/-- Second moment of a centered Gaussian increment. -/
private lemma integral_sq_increment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {T : ℝ≥0} (π : TimePartition T) (i : Fin π.size) :
    ∫ ω, (B (π.node i.succ) ω - B (π.node i.castSucc) ω) ^ 2 ∂μ = π.increment i := by
  let raw : Ω → ℝ := fun ω ↦ B (π.node i.succ) ω - B (π.node i.castSucc) ω
  have hlaw : HasLaw raw (gaussianReal 0
      (nndist (π.node i.succ : ℝ) (π.node i.castSucc : ℝ))) μ :=
    hB.hasLaw_sub (π.node i.succ) (π.node i.castSucc)
  have hmean : ∫ ω, raw ω ∂μ = 0 := by
    rw [hlaw.integral_eq, integral_id_gaussianReal]
  have hvar : variance raw μ = π.increment i := by
    rw [hlaw.variance_eq, variance_id_gaussianReal, increment_eq_nndist π i]
  rw [variance_of_integral_eq_zero hlaw.aemeasurable hmean] at hvar
  simpa [raw] using hvar

/-- Fourth moment of the centered standard Gaussian measure, via its moment-generating function. -/
private lemma integral_id_pow_four_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 4 ∂gaussianReal 0 v = 3 * (v : ℝ) ^ 2 := by
  let φ : ℝ → ℝ := fun t ↦ Real.exp ((v : ℝ) * t ^ 2 / 2)
  have hφder (t : ℝ) : HasDerivAt φ ((v : ℝ) * t * φ t) t := by
    have hpow : HasDerivAt (fun s ↦ s ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have hmul : HasDerivAt (fun s ↦ (v : ℝ) * s ^ 2) ((v : ℝ) * (2 * t)) t :=
      hpow.const_mul (v : ℝ)
    have hdiv : HasDerivAt (fun s ↦ (v : ℝ) * s ^ 2 / 2) ((v : ℝ) * t) t := by
      have h := hmul.div_const 2
      exact h.congr_deriv (by ring)
    exact (hdiv.exp).congr_deriv (by simp [φ, mul_comm])
  have hψder (t : ℝ) : HasDerivAt (fun s ↦ (v : ℝ) * s * φ s)
      (((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * φ t) t := by
    exact ((hasDerivAt_id t).const_mul (v : ℝ)).mul (hφder t) |>.congr_deriv
      (by simp only [id_eq]; ring)
  have hρder (t : ℝ) : HasDerivAt (fun s ↦ ((v : ℝ) + (v : ℝ) ^ 2 * s ^ 2) * φ s)
      ((v : ℝ) ^ 2 * t * (3 + (v : ℝ) * t ^ 2) * φ t) t := by
    have hpow : HasDerivAt (fun s ↦ s ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have hcoeff : HasDerivAt (fun s ↦ (v : ℝ) + (v : ℝ) ^ 2 * s ^ 2)
        (2 * (v : ℝ) ^ 2 * t) t := by
      exact ((hasDerivAt_const t (v : ℝ)).add (hpow.const_mul ((v : ℝ) ^ 2))).congr_deriv
        (by ring)
    exact (hcoeff.mul (hφder t)).congr_deriv (by ring)
  have hσ : deriv (fun s ↦ (v : ℝ) ^ 2 * s * (3 + (v : ℝ) * s ^ 2) * φ s) 0 =
      3 * (v : ℝ) ^ 2 := by
    have hlin : HasDerivAt (fun s ↦ (v : ℝ) ^ 2 * s) ((v : ℝ) ^ 2) 0 := by
      refine HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq
        ((hasDerivAt_id 0).const_mul ((v : ℝ) ^ 2))
        (Eventually.of_forall fun s ↦ by simp [id_eq])) (by simp)
    have hcube : HasDerivAt (fun s : ℝ ↦ s ^ 3) (0 : ℝ) 0 := by
      simpa using hasDerivAt_pow 3 (0 : ℝ)
    have hpoly : HasDerivAt (fun s ↦ 3 * (v : ℝ) ^ 2 * s + (v : ℝ) ^ 3 * s ^ 3)
        (3 * (v : ℝ) ^ 2) 0 := by
      refine (((hlin.const_mul 3).add (hcube.const_mul ((v : ℝ) ^ 3))).congr_deriv
        (by simp [mul_zero, add_zero])).congr_of_eventuallyEq
        (Eventually.of_forall fun s ↦ by simp only [Pi.add_apply]; ring)
    have hpoly' : HasDerivAt (fun s ↦ (v : ℝ) ^ 2 * s * (3 + (v : ℝ) * s ^ 2))
        (3 * (v : ℝ) ^ 2) 0 := by
      convert hpoly using 1
      ext s
      ring
    exact ((hpoly'.mul (hφder 0)).congr_deriv
      (by simp [φ, Real.exp_zero, mul_zero, zero_mul, add_zero, mul_one])).deriv
  calc
    ∫ x, x ^ 4 ∂gaussianReal 0 v
        = iteratedDeriv 4 (mgf (fun x ↦ x) (gaussianReal 0 v)) 0 := by
          rw [iteratedDeriv_mgf_zero (by simp) 4]
          simp
    _ = iteratedDeriv 4 φ 0 := by
          rw [mgf_fun_id_gaussianReal]
          congr 1
          ext t
          simp [φ]
    _ = deriv (deriv (deriv (deriv φ))) 0 := by
          rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
            iteratedDeriv_succ, iteratedDeriv_zero]
    _ = 3 * (v : ℝ) ^ 2 := by
          have h1 : deriv φ = fun t ↦ (v : ℝ) * t * φ t := by
            ext t
            exact (hφder t).deriv
          have h2 : deriv (fun t ↦ (v : ℝ) * t * φ t) =
              fun t ↦ ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * φ t := by
            ext t
            exact (hψder t).deriv
          have h3 : deriv (fun t ↦ ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * φ t) =
              fun t ↦ (v : ℝ) ^ 2 * t * (3 + (v : ℝ) * t ^ 2) * φ t := by
            ext t
            exact (hρder t).deriv
          rw [h1, h2, h3, hσ]

/-- Fourth moment of a centered Gaussian increment. -/
private lemma integral_pow_four_increment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {T : ℝ≥0} (π : TimePartition T) (i : Fin π.size) :
    ∫ ω, (B (π.node i.succ) ω - B (π.node i.castSucc) ω) ^ 4 ∂μ =
      3 * π.increment i ^ 2 := by
  let v : ℝ≥0 := nndist (π.node i.succ : ℝ) (π.node i.castSucc : ℝ)
  let raw : Ω → ℝ := fun ω ↦ B (π.node i.succ) ω - B (π.node i.castSucc) ω
  have hlaw : HasLaw raw (gaussianReal 0 v) μ := hB.hasLaw_sub _ _
  have hint := hlaw.integral_comp (f := fun x : ℝ ↦ x ^ 4)
    ((continuous_pow 4).aestronglyMeasurable)
  rw [Function.comp_def] at hint
  have hv : (v : ℝ) = π.increment i := increment_eq_nndist π i
  calc
    ∫ ω, raw ω ^ 4 ∂μ = ∫ x, x ^ 4 ∂gaussianReal 0 v := hint
    _ = 3 * (v : ℝ) ^ 2 := integral_id_pow_four_gaussianReal v
    _ = 3 * π.increment i ^ 2 := by rw [hv]

/-- Fourth-moment and squared second-moment `L^p` bounds for a measurable version of a
pre-Brownian increment. -/
private lemma memLp_increment_and_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {T : ℝ≥0} (π : TimePartition T) {Y : Fin π.size → Ω → ℝ}
    (hYmeas : ∀ i, Measurable (Y i))
    (hYae : ∀ i, (fun ω ↦ B (π.node i.succ) ω - B (π.node i.castSucc) ω) =ᵐ[μ] Y i)
    (i : Fin π.size) :
    MemLp (Y i) 4 μ ∧ MemLp (fun ω ↦ Y i ω ^ 2) 2 μ := by
  have hYLp4 : MemLp (Y i) 4 μ := by
    have hlaw := hB.hasLaw_sub (π.node i.succ) (π.node i.castSucc)
    exact (hlaw.memLp (memLp_id_gaussianReal' 4 (by simp))).ae_eq (hYae i)
  refine ⟨hYLp4, ?_⟩
  rw [memLp_two_iff_integrable_sq ((hYmeas i).pow_const 2).aestronglyMeasurable]
  convert hYLp4.integrable_norm_pow (by decide : (4 : ℕ) ≠ 0) using 1
  ext x
  rw [Real.norm_eq_abs]
  have hinner : Y i x ^ 2 = |Y i x| ^ 2 := (sq_abs (Y i x)).symm
  rw [hinner, ← pow_mul]

/-- Energy of the centered squared increments is at most twice mesh times `T`. -/
private lemma centeredIncrement_energy_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {T : ℝ≥0} (π : TimePartition T) (Y : Fin π.size → Ω → ℝ)
    (hYmeas : ∀ i, Measurable (Y i))
    (hYae : ∀ i, (fun ω ↦ B (π.node i.succ) ω - B (π.node i.castSucc) ω) =ᵐ[μ] Y i)
    (hYindep : iIndepFun Y μ) :
    ∫ ω, (∑ i : Fin π.size, ((Y i ω) ^ 2 - π.increment i)) ^ 2 ∂μ ≤
      2 * (π.mesh : ℝ) * (T : ℝ) := by
  let X : Fin π.size → Ω → ℝ := fun i ω ↦ (Y i ω) ^ 2 - π.increment i
  have hsq (i : Fin π.size) : ∫ ω, (Y i ω) ^ 2 ∂μ = π.increment i := by
    have hpow : (fun ω ↦ (B (π.node i.succ) ω - B (π.node i.castSucc) ω) ^ 2) =ᵐ[μ]
        fun ω ↦ (Y i ω) ^ 2 := (hYae i).mono fun ω h ↦ by simp [h]
    rw [← integral_congr_ae hpow]
    exact integral_sq_increment hB π i
  have hfour (i : Fin π.size) : ∫ ω, (Y i ω) ^ 4 ∂μ = 3 * π.increment i ^ 2 := by
    have hpow : (fun ω ↦ (B (π.node i.succ) ω - B (π.node i.castSucc) ω) ^ 4) =ᵐ[μ]
        fun ω ↦ (Y i ω) ^ 4 := (hYae i).mono fun ω h ↦ by simp [h]
    rw [← integral_congr_ae hpow]
    exact integral_pow_four_increment hB π i
  have hsqLp (i : Fin π.size) : MemLp (fun ω ↦ Y i ω ^ 2) 2 μ :=
    (memLp_increment_and_sq hB π hYmeas hYae i).2
  have hmeanX (i : Fin π.size) : ∫ ω, X i ω ∂μ = 0 := by
    have hint : Integrable (fun ω ↦ Y i ω ^ 2) μ :=
      memLp_one_iff_integrable.1 ((hsqLp i).mono_exponent (by simp : (1 : ℝ≥0∞) ≤ 2))
    rw [show X i = fun ω ↦ Y i ω ^ 2 - π.increment i by rfl,
      integral_sub hint (integrable_const _), hsq i, integral_const, probReal_univ]
    simp
  have hvar (i : Fin π.size) : ∫ ω, (X i ω) ^ 2 ∂μ = 2 * π.increment i ^ 2 := by
    have hAE : AEStronglyMeasurable (fun ω ↦ Y i ω ^ 2) μ :=
      ((hYmeas i).pow_const 2).aestronglyMeasurable
    have hsub : variance (X i) μ = variance (fun ω ↦ Y i ω ^ 2) μ := by
      simpa [X, sub_eq_add_neg] using variance_sub_const hAE (π.increment i)
    have heq : variance (fun ω ↦ Y i ω ^ 2) μ =
        ∫ ω, (Y i ω ^ 2) ^ 2 ∂μ - (∫ ω, Y i ω ^ 2 ∂μ) ^ 2 :=
      variance_eq_sub (hsqLp i)
    have hpow4 : ∫ ω, (Y i ω ^ 2) ^ 2 ∂μ = ∫ ω, (Y i ω) ^ 4 ∂μ := by
      refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
      ring
    have hXvar : variance (X i) μ = ∫ ω, (X i ω) ^ 2 ∂μ :=
      variance_of_integral_eq_zero ((hYmeas i).pow_const 2 |>.sub measurable_const).aemeasurable
        (hmeanX i)
    rw [← hXvar, hsub, heq, hpow4, hsq i, hfour i]
    ring
  have hXLp (i : Fin π.size) : MemLp (X i) 2 μ := (hsqLp i).sub (memLp_const _)
  have hXindep : iIndepFun X μ := by
    have hcomp := hYindep.comp (fun i x ↦ x ^ 2 - π.increment i)
      (fun i ↦ (measurable_id.pow_const 2).sub measurable_const)
    simpa [X, Function.comp_def] using hcomp
  have hvarSum : variance (fun ω ↦ ∑ i : Fin π.size, X i ω) μ =
      ∑ i : Fin π.size, variance (X i) μ := by
    have hpi := IndepFun.variance_sum (s := (Finset.univ : Finset (Fin π.size)))
      (fun i _ ↦ hXLp i) (fun i _ j _ hij ↦ hXindep.indepFun hij)
    have hcongr : (fun ω ↦ ∑ i : Fin π.size, X i ω) =ᵐ[μ]
        ∑ i ∈ Finset.univ, X i :=
      ae_of_all _ fun ω ↦ (Finset.sum_apply _ _ _).symm
    rw [variance_congr hcongr]
    simpa using hpi
  have hmeanSum : ∫ ω, (∑ i : Fin π.size, X i ω) ∂μ = 0 := by
    rw [integral_finsetSum]
    · simp [hmeanX]
    · intro i _
      exact memLp_one_iff_integrable.1
        ((hXLp i).mono_exponent (by simp : (1 : ℝ≥0∞) ≤ 2))
  have henergy : ∫ ω, (∑ i : Fin π.size, X i ω) ^ 2 ∂μ =
      ∑ i : Fin π.size, 2 * π.increment i ^ 2 := by
    have hvarFun : variance (fun ω ↦ ∑ i : Fin π.size, X i ω) μ =
        ∫ ω, (∑ i : Fin π.size, X i ω) ^ 2 ∂μ :=
      variance_of_integral_eq_zero
        (Finset.measurable_sum Finset.univ fun i _ ↦
          ((hYmeas i).pow_const 2).sub measurable_const).aemeasurable hmeanSum
    have hvarI (i : Fin π.size) : variance (X i) μ = ∫ ω, (X i ω) ^ 2 ∂μ :=
      variance_of_integral_eq_zero
        (((hYmeas i).pow_const 2).sub measurable_const).aemeasurable (hmeanX i)
    rw [← hvarFun, hvarSum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hvarI i, hvar i]
  rw [henergy]
  calc
    ∑ i : Fin π.size, 2 * π.increment i ^ 2
        = 2 * ∑ i : Fin π.size, π.increment i ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 2 * ((π.mesh : ℝ) * (T : ℝ)) := by
      gcongr
      exact π.sum_sq_increment_le
    _ = 2 * (π.mesh : ℝ) * (T : ℝ) := by ring

/-- One-partition bound for the nonstrict quadratic-variation deviation. -/
private lemma quadraticVariation_measure_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {T : ℝ≥0} (π : TimePartition T) {ε : ℝ} (hε : 0 < ε)
    (hmesh : (π.mesh : ℝ) < ε / 2) :
    μ {ω | ∃ t ≤ T, ε ≤ |π.covariation B B t ω - (t : ℝ)|} ≤
      ENNReal.ofReal (8 * (π.mesh : ℝ) * (T : ℝ) / ε ^ 2) := by
  let raw : Fin π.size → Ω → ℝ :=
    fun i ω ↦ B (π.node i.succ) ω - B (π.node i.castSucc) ω
  let hAe : ∀ i, AEMeasurable (raw i) μ :=
    fun i ↦ (hB.aemeasurable (π.node i.succ)).sub (hB.aemeasurable (π.node i.castSucc))
  let Y : Fin π.size → Ω → ℝ := fun i ↦ (hAe i).mk (raw i)
  have hYmeas : ∀ i, Measurable (Y i) := fun i ↦ (hAe i).measurable_mk
  have hYae : ∀ i, raw i =ᵐ[μ] Y i := fun i ↦ (hAe i).ae_eq_mk
  have hYindep : iIndepFun Y μ :=
    (iIndepFun_congr hYae).1 (hB.hasIndepIncrements π.size π.node π.monotone_node)
  have hsqLp (i : Fin π.size) : MemLp (fun ω ↦ Y i ω ^ 2) 2 μ :=
    (memLp_increment_and_sq hB π hYmeas hYae i).2
  let X : Fin π.size → Ω → ℝ := fun i ω ↦ (Y i ω) ^ 2 - π.increment i
  have hXmeas : ∀ i, Measurable (X i) :=
    fun i ↦ ((hYmeas i).pow_const 2).sub measurable_const
  have hXmean : ∀ i, ∫ ω, X i ω ∂μ = 0 := by
    intro i
    have hsq : ∫ ω, (Y i ω) ^ 2 ∂μ = π.increment i := by
      have hpow : (fun ω ↦ (raw i ω) ^ 2) =ᵐ[μ] fun ω ↦ (Y i ω) ^ 2 :=
        (hYae i).mono fun ω hω ↦ congrArg (fun z ↦ z ^ 2) hω
      rw [← integral_congr_ae hpow]
      unfold raw
      exact integral_sq_increment hB π i
    have hint : Integrable (fun ω ↦ Y i ω ^ 2) μ :=
      memLp_one_iff_integrable.1 ((hsqLp i).mono_exponent (by simp : (1 : ℝ≥0∞) ≤ 2))
    rw [show X i = fun ω ↦ Y i ω ^ 2 - π.increment i by rfl,
      integral_sub hint (integrable_const _), hsq, integral_const, probReal_univ]
    simp
  have hXLp : ∀ i, MemLp (X i) 2 μ := fun i ↦ (hsqLp i).sub (memLp_const _)
  have hXindep : iIndepFun X μ := by
    have hcomp := hYindep.comp (fun i x ↦ x ^ 2 - π.increment i)
      (fun _ ↦ (measurable_id.pow_const 2).sub measurable_const)
    simpa [X, Function.comp_def] using hcomp
  have hkol := kolmogorov_maximal hXmeas hXmean hXLp hXindep (half_pos hε)
  have henergy := centeredIncrement_energy_le hB π Y hYmeas hYae hYindep
  have hlast : ∀ ω, partialSum X (Fin.last π.size) ω =
      ∑ i : Fin π.size, X i ω := partialSum_last X
  have hintLe : ∫ ω, (partialSum X (Fin.last π.size) ω) ^ 2 ∂μ ≤
      2 * (π.mesh : ℝ) * (T : ℝ) := by
    have hfun : (fun ω ↦ (partialSum X (Fin.last π.size) ω) ^ 2) =
        fun ω ↦ (∑ i : Fin π.size, ((Y i ω) ^ 2 - π.increment i)) ^ 2 := by
      ext ω
      rw [hlast ω]
    rw [hfun]
    exact henergy
  have hdiv : (∫ ω, (partialSum X (Fin.last π.size) ω) ^ 2 ∂μ) / (ε / 2) ^ 2 ≤
      8 * (π.mesh : ℝ) * (T : ℝ) / ε ^ 2 := by
    have hrewrite : 2 * (π.mesh : ℝ) * (T : ℝ) / (ε / 2) ^ 2 =
        8 * (π.mesh : ℝ) * (T : ℝ) / ε ^ 2 := by
      field_simp
      ring
    exact (div_le_div_of_nonneg_right hintLe (sq_nonneg _)).trans (le_of_eq hrewrite)
  let N : Set Ω := ⋃ i, {ω | Y i ω ≠ raw i ω}
  have hN : μ N = 0 := by
    refine (measure_iUnion_null_iff).2 fun i ↦ ?_
    exact ae_iff.1 (hYae i).symm
  have hsub : {ω | ∃ t ≤ T, ε ≤ |π.covariation B B t ω - (t : ℝ)|} ⊆
      {ω | ∃ k : Fin (π.size + 1), ε / 2 ≤ |partialSum X k ω|} ∪ N := by
    intro ω hω
    by_cases hωN : ω ∈ N
    · exact Or.inr hωN
    · refine Or.inl ?_
      obtain ⟨t, ht, hdev⟩ := hω
      let k : Fin (π.size + 1) :=
        ⟨π.completedCount t, Nat.lt_succ_of_le (π.completedCount_le_size t)⟩
      refine ⟨k, ?_⟩
      have hagree : ∀ i, Y i ω = raw i ω := by
        intro i
        by_contra hne
        exact hωN (Set.mem_iUnion.2 ⟨i, hne⟩)
      have hQ : π.covariation B B t ω = ∑ i ∈ pastFinset π.size k, (Y i ω) ^ 2 := by
        have hfilt : Finset.univ.filter (fun i : Fin π.size ↦ π.node i.succ ≤ t) =
            pastFinset π.size k := by
          ext i
          simp only [pastFinset, Finset.mem_filter, Finset.mem_univ, true_and]
          have hkval : k.val = π.completedCount t := by simp [k]
          rw [hkval]
          exact π.completed_iff_val_lt t i
        unfold TimePartition.covariation
        rw [← Finset.sum_filter, hfilt]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hrw : B (π.node i.succ) ω - B (π.node i.castSucc) ω = Y i ω := by
          have hraw := (hagree i).symm
          unfold raw at hraw
          exact hraw
        rw [hrw]
        ring
      have hpartial : partialSum X k ω =
          π.covariation B B t ω - (π.covered t : ℝ) := by
        rw [partialSum, Finset.sum_sub_distrib, hQ]
        have hsumΔ : ∑ i ∈ pastFinset π.size k, π.increment i = (π.covered t : ℝ) := by
          have hidx : (⟨k.val, k.isLt⟩ : Fin (π.size + 1)) = k := by ext; simp
          simpa [pastFinset, hidx, TimePartition.covered] using
            π.sum_increment_initial k.val (π.completedCount_le_size t)
        linarith
      have htri : |π.covariation B B t ω - (t : ℝ)| ≤
          |partialSum X k ω| + |(π.covered t : ℝ) - (t : ℝ)| := by
        have hEq : π.covariation B B t ω - (t : ℝ) =
            partialSum X k ω + ((π.covered t : ℝ) - (t : ℝ)) := by
          linarith [hpartial]
        rw [hEq]
        exact abs_add_le _ _
      have hgap : |(π.covered t : ℝ) - (t : ℝ)| < ε / 2 :=
        lt_of_le_of_lt (by simpa [abs_sub_comm] using π.abs_t_sub_covered_le_mesh ht) hmesh
      have hgt : ε / 2 < |partialSum X k ω| := by linarith [htri, hdev, hgap, hε]
      exact hgt.le
  calc
    μ {ω | ∃ t ≤ T, ε ≤ |π.covariation B B t ω - (t : ℝ)|}
        ≤ μ ({ω | ∃ k : Fin (π.size + 1), ε / 2 ≤ |partialSum X k ω|} ∪ N) :=
          measure_mono hsub
    _ ≤ μ {ω | ∃ k : Fin (π.size + 1), ε / 2 ≤ |partialSum X k ω|} + μ N :=
          measure_union_le _ _
    _ ≤ ENNReal.ofReal ((∫ ω, (partialSum X (Fin.last π.size) ω) ^ 2 ∂μ) / (ε / 2) ^ 2) + 0 := by
          rw [hN, add_zero, add_zero]
          exact hkol
    _ ≤ ENNReal.ofReal (8 * (π.mesh : ℝ) * (T : ℝ) / ε ^ 2) := by
          rw [add_zero]
          exact ENNReal.ofReal_le_ofReal hdiv

/-- **08.7**: uniform-on-compact convergence in probability along deterministic vanishing mesh.
No path continuity assumption is needed for completed-interval quadratic sums. -/
theorem brownian_quadraticVariation_ucp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) {T : ℝ≥0} (π : ℕ → TimePartition T)
    (hmesh : Tendsto (fun n ↦ (π n).mesh) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ μ {ω | ∃ t ≤ T,
      ε < |(π n).covariation B B t ω - (t : ℝ)|}) atTop (𝓝 0) := by
  intro ε hε
  have hmeshR : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0) := NNReal.tendsto_coe.mpr hmesh
  have hev : ∀ᶠ n in atTop, ((π n).mesh : ℝ) < ε / 2 :=
    hmeshR.eventually (Iio_mem_nhds (half_pos hε))
  have hupper : Tendsto (fun n ↦ ENNReal.ofReal
      (8 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2)) atTop (𝓝 0) := by
    have hlin : Tendsto (fun n ↦ 8 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2) atTop (𝓝 0) := by
      have hrewrite : (fun n ↦ 8 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2) =
          fun n ↦ (8 * (T : ℝ) / ε ^ 2) * ((π n).mesh : ℝ) := by
        ext n
        ring
      rw [hrewrite]
      simpa using hmeshR.const_mul (8 * (T : ℝ) / ε ^ 2)
    simpa [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hlin
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [hev] with n hn
  calc
    μ {ω | ∃ t ≤ T, ε < |(π n).covariation B B t ω - (t : ℝ)|}
        ≤ μ {ω | ∃ t ≤ T, ε ≤ |(π n).covariation B B t ω - (t : ℝ)|} := by
          apply measure_mono
          intro ω ⟨t, ht, hlt⟩
          exact ⟨t, ht, hlt.le⟩
    _ ≤ ENNReal.ofReal (8 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2) :=
          quadraticVariation_measure_le hB (π n) hε hn

/-- Summable meshes give almost sure uniform convergence, hence in particular dyadic convergence. -/
theorem brownian_quadraticVariation_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) {T : ℝ≥0} (π : ℕ → TimePartition T)
    (hmesh : Summable (fun n ↦ ((π n).mesh : ℝ))) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ t ≤ T, |(π n).covariation B B t ω - (t : ℝ)| < ε := by
  have hone : ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      ∀ t ≤ T, |(π n).covariation B B t ω - (t : ℝ)| < ε := by
    intro ε hε
    let bad : ℕ → Set Ω := fun n ↦
      {ω | ∃ t ≤ T, ε ≤ |(π n).covariation B B t ω - (t : ℝ)|}
    let bump : ℕ → ℝ≥0∞ := fun n ↦ if ((π n).mesh : ℝ) < ε / 2 then 0 else 1
    have hle : ∀ n, μ (bad n) ≤
        ENNReal.ofReal (8 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2) + bump n := by
      intro n
      by_cases hn : ((π n).mesh : ℝ) < ε / 2
      · simpa [bad, bump, hn] using quadraticVariation_measure_le hB (π n) hε hn
      · have hprob : μ (bad n) ≤ 1 := by
          calc
            μ (bad n) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        have hnonneg : 0 ≤ ENNReal.ofReal (8 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2) :=
          bot_le
        simpa [bump, hn] using le_trans hprob (by simp)
    have hofReal : ∑' n, ENNReal.ofReal (8 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2) ≠ ∞ := by
      refine Summable.tsum_ofReal_ne_top ?_
      have hrewrite : (fun n ↦ 8 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2) =
          fun n ↦ (8 * (T : ℝ) / ε ^ 2) * ((π n).mesh : ℝ) := by
        ext n
        ring
      rw [hrewrite]
      exact hmesh.mul_left _
    have hzero : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0) := hmesh.tendsto_atTop_zero
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hzero.eventually (Iio_mem_nhds (half_pos hε)))
    have htail : ∑' i, bump (i + N) = 0 := by
      rw [ENNReal.tsum_eq_zero]
      intro i
      simp [bump, hN (i + N) (Nat.le_add_left N i)]
    have heq := Summable.sum_add_tsum_nat_add' (f := bump) (k := N)
      (ENNReal.summable (f := fun i ↦ bump (i + N)))
    have hsumLe : ∑ i ∈ Finset.range N, bump i ≤ N := by
      calc
        ∑ i ∈ Finset.range N, bump i ≤ ∑ i ∈ Finset.range N, (1 : ℝ≥0∞) := by
          gcongr with i hi
          simp only [bump]
          split_ifs <;> simp
        _ = N := by simp
    have hbump : ∑' n, bump n ≠ ∞ := by
      rw [← heq, htail, add_zero]
      exact ne_top_of_le_ne_top (by simp) hsumLe
    have htsum : ∑' n, μ (bad n) ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
      rw [ENNReal.tsum_add]
      exact ENNReal.add_ne_top.2 ⟨hofReal, hbump⟩
    filter_upwards [ae_eventually_notMem htsum] with ω hω
    exact hω.mono fun n hn t ht ↦ by
      have hnot : ¬ ε ≤ |(π n).covariation B B t ω - (t : ℝ)| := by
        intro hle'
        exact hn ⟨t, ht, hle'⟩
      exact lt_of_not_ge hnot
  filter_upwards [ae_all_iff.2 fun m : ℕ ↦
      hone (1 / ((m : ℝ) + 1)) (by positivity)] with ω hω
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  exact (hω m).mono fun n hn t ht ↦ lt_trans (hn t ht) hm

/-- Algebraic polarization identity for one pair of increments. -/
private lemma sq_sub_sq_div_sqrt_two (a b : ℝ) :
    ((a + b) / Real.sqrt 2) * ((a + b) / Real.sqrt 2) -
      ((a - b) / Real.sqrt 2) * ((a - b) / Real.sqrt 2) = 2 * (a * b) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
  field_simp [Real.sqrt_ne_zero'.mpr two_pos]
  rw [h2]
  ring

/-- Polarization expresses bilinear covariation through two quadratic variations. -/
private lemma covariation_polarization {Ω : Type*} {T : ℝ≥0} (π : TimePartition T)
    (B C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    π.covariation (fun s ω ↦ (B s ω + C s ω) / Real.sqrt 2)
        (fun s ω ↦ (B s ω + C s ω) / Real.sqrt 2) t ω -
      π.covariation (fun s ω ↦ (B s ω - C s ω) / Real.sqrt 2)
        (fun s ω ↦ (B s ω - C s ω) / Real.sqrt 2) t ω =
      2 * π.covariation B C t ω := by
  unfold TimePartition.covariation
  rw [← Finset.sum_sub_distrib]
  refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) (Finset.mul_sum _ _ _).symm
  by_cases h : π.node i.succ ≤ t
  · simp only [h, ↓reduceIte]
    set u : ℝ := B (π.node i.succ) ω
    set v : ℝ := B (π.node i.castSucc) ω
    set p : ℝ := C (π.node i.succ) ω
    set q : ℝ := C (π.node i.castSucc) ω
    have hL : (u + p) / Real.sqrt 2 - (v + q) / Real.sqrt 2 =
        ((u - v) + (p - q)) / Real.sqrt 2 := by ring
    have hR : (u - p) / Real.sqrt 2 - (v - q) / Real.sqrt 2 =
        ((u - v) - (p - q)) / Real.sqrt 2 := by ring
    rw [hL, hR]
    exact sq_sub_sq_div_sqrt_two (u - v) (p - q)
  · simp [h]

/-- A normalized sum of independent pre-Brownian motions is pre-Brownian. -/
private lemma isPreBrownianReal_normalizedSum {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {B C : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) (hC : IsPreBrownianReal C μ)
    (hind : IndepFun (fun ω ↦ fun t ↦ B t ω) (fun ω ↦ fun t ↦ C t ω) μ) :
    IsPreBrownianReal (fun t ω ↦ (B t ω + C t ω) / Real.sqrt 2) μ := by
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ ?_ ?_
  · refine ⟨fun I ↦ ?_⟩
    have hm : Measurable (fun f : ℝ≥0 → ℝ ↦ I.restrict f) :=
      Measurable.of_eval fun i ↦ measurable_pi_apply (i : ℝ≥0)
    have hindI : IndepFun (fun ω ↦ I.restrict (fun t ↦ B t ω))
        (fun ω ↦ I.restrict (fun t ↦ C t ω)) μ := hind.comp hm hm
    have hpair := hindI.hasGaussianLaw (hB.isGaussianProcess.hasGaussianLaw I)
      (hC.isGaussianProcess.hasGaussianLaw I)
    have hsmul := hpair.fun_add.fun_smul (Real.sqrt 2)⁻¹
    convert hsmul using 1
    ext ω i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Finset.restrict, div_eq_mul_inv]
    ring
  · intro t
    have hint : Integrable (fun ω ↦ B t ω + C t ω) μ :=
      (hB.integrable_eval t).add (hC.integrable_eval t)
    rw [show (fun ω ↦ (B t ω + C t ω) / Real.sqrt 2) =
        fun ω ↦ (Real.sqrt 2)⁻¹ * (B t ω + C t ω) by ext; ring,
      integral_const_mul, integral_add (hB.integrable_eval t) (hC.integrable_eval t),
      hB.integral_eval, hC.integral_eval]
    simp
  · intro s t hst
    have hBs : MemLp (B s) 2 μ := (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
    have hBt : MemLp (B t) 2 μ := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
    have hCs : MemLp (C s) 2 μ := (hC.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
    have hCt : MemLp (C t) 2 μ := (hC.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
    have hcross : cov[B s, C t; μ] = 0 :=
      (hind.comp (measurable_pi_apply s) (measurable_pi_apply t)).covariance_eq_zero hBs hCt
    have hcross' : cov[C s, B t; μ] = 0 := by
      rw [covariance_comm]
      exact (hind.comp (measurable_pi_apply t) (measurable_pi_apply s)).covariance_eq_zero hBt hCs
    have hsum : cov[fun ω ↦ B s ω + C s ω, fun ω ↦ B t ω + C t ω; μ] =
        (s : ℝ) + s := by
      have hLs : (fun ω ↦ B s ω + C s ω) = B s + C s := by
        ext ω
        rfl
      have hLt : (fun ω ↦ B t ω + C t ω) = B t + C t := by
        ext ω
        rfl
      rw [hLs, hLt, covariance_add_left hBs hCs (hBt.add hCt),
        covariance_add_right hBs hBt hCt, covariance_add_right hCs hBt hCt,
        hB.covariance_eval, hC.covariance_eval, hcross, hcross']
      simp [min_eq_left hst]
    have hfun : (fun ω ↦ (B s ω + C s ω) / Real.sqrt 2) =
        fun ω ↦ (Real.sqrt 2)⁻¹ * (B s ω + C s ω) := by
      ext ω
      ring
    have hfun' : (fun ω ↦ (B t ω + C t ω) / Real.sqrt 2) =
        fun ω ↦ (Real.sqrt 2)⁻¹ * (B t ω + C t ω) := by
      ext ω
      ring
    rw [hfun, hfun', covariance_const_mul_left, covariance_const_mul_right, hsum]
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
    field_simp [Real.sqrt_ne_zero'.mpr two_pos]
    rw [hsq]
    ring

/-- Independent Brownian coordinates have diagonal quadratic covariation.
Independence is imposed on the coordinate processes as random elements, rather than only
on pairs of one-time marginals. -/
theorem brownian_covariation_ucp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (B : Fin d → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) μ)
    (hind : iIndepFun (fun i ω ↦ fun t ↦ B i t ω) μ)
    {T : ℝ≥0} (π : ℕ → TimePartition T)
    (hmesh : Tendsto (fun n ↦ (π n).mesh) atTop (𝓝 0)) (i j : Fin d) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ μ {ω | ∃ t ≤ T,
      ε < |(π n).covariation (B i) (B j) t ω - if i = j then (t : ℝ) else 0|})
      atTop (𝓝 0) := by
  intro ε hε
  by_cases hij : i = j
  · subst hij
    simpa using brownian_quadraticVariation_ucp μ (hB i) π hmesh ε hε
  · let P : ℝ≥0 → Ω → ℝ := fun t ω ↦ (B i t ω + B j t ω) / Real.sqrt 2
    let M : ℝ≥0 → Ω → ℝ := fun t ω ↦ (B i t ω - B j t ω) / Real.sqrt 2
    have hP : IsPreBrownianReal P μ :=
      isPreBrownianReal_normalizedSum (hB i) (hB j) (hind.indepFun hij)
    have hM : IsPreBrownianReal M μ := by
      have hneg : IsPreBrownianReal (-B j) μ := (hB j).neg
      have hnegMeas : Measurable (fun f : ℝ≥0 → ℝ ↦ -f) :=
        Measurable.of_eval fun t ↦ measurable_neg.comp (measurable_pi_apply t)
      have hindneg := (hind.indepFun hij).comp measurable_id hnegMeas
      have hsum := isPreBrownianReal_normalizedSum (hB i) hneg hindneg
      refine IsPreBrownianReal.congr hsum fun t ↦ ae_of_all μ fun ω ↦ ?_
      simp [M, Pi.neg_apply, sub_eq_add_neg]
    have htendP := brownian_quadraticVariation_ucp μ hP π hmesh ε hε
    have htendM := brownian_quadraticVariation_ucp μ hM π hmesh ε hε
    have hupper : Tendsto
        (fun n ↦ μ {ω | ∃ t ≤ T, ε < |(π n).covariation P P t ω - (t : ℝ)|} +
          μ {ω | ∃ t ≤ T, ε < |(π n).covariation M M t ω - (t : ℝ)|})
        atTop (𝓝 0) := by
      rw [show (0 : ℝ≥0∞) = 0 + 0 by simp]
      exact htendP.add htendM
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun _ ↦ bot_le) ?_
    refine Eventually.of_forall fun n ↦ ?_
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ω ⟨t, ht, hdev⟩
    have hpol := covariation_polarization (π n) (B i) (B j) t ω
    have hbound : |(π n).covariation (B i) (B j) t ω| ≤
        (|(π n).covariation P P t ω - (t : ℝ)| +
          |(π n).covariation M M t ω - (t : ℝ)|) / 2 := by
      have hEq : (π n).covariation (B i) (B j) t ω =
          (((π n).covariation P P t ω - (t : ℝ)) -
            ((π n).covariation M M t ω - (t : ℝ))) / 2 := by
        linarith [hpol]
      rw [hEq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      gcongr
      exact abs_sub _ _
    have hsum : ε < (|(π n).covariation P P t ω - (t : ℝ)| +
        |(π n).covariation M M t ω - (t : ℝ)|) / 2 := by
      have hdev0 : ε < |(π n).covariation (B i) (B j) t ω| := by
        rw [ite_eq_right hij, sub_zero] at hdev
        exact hdev
      exact lt_of_lt_of_le hdev0 hbound
    by_cases hp : ε < |(π n).covariation P P t ω - (t : ℝ)|
    · exact Or.inl ⟨t, ht, hp⟩
    · refine Or.inr ⟨t, ht, ?_⟩
      have hle : |(π n).covariation P P t ω - (t : ℝ)| ≤ ε := le_of_not_gt hp
      linarith

end CKMA
