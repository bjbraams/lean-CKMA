/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.BrownianQuadraticVariation.TimePartition
public import CKMA.Probability.BrownianQuadraticVariation.KolmogorovMaximal
public import Mathlib.Probability.BrownianMotion.Basic

import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import TauCeti.Probability.BrownianMotion.QuadraticVariation

/-!
# Brownian quadratic variation and covariation (08.7)

`TimePartition` records ordered deterministic nodes, allowing repeated nodes and the
zero time interval. Its mesh controls quadratic and bilinear covariation sums formed
from completed partition intervals. The main statements give uniform convergence in
probability, almost-sure convergence under a summable mesh condition, and cross-coordinate
covariation for independent Brownian coordinates, in probability and almost surely. The bracket
`quadraticCovariation` packages the limit as a process, determined almost surely at each time.

The process interface is pre-Brownian: for a sequence of deterministic partitions only
countably many evaluation times are involved. Time and partition nodes are nonnegative
reals; covariance normalization is the standard Brownian one.

The uniform estimate is Kolmogorov's maximal inequality applied to the centered sum of
squared increments; its `L²` bound is TauCeti's mean-square estimate for Brownian quadratic
sums. Cross variation reduces to quadratic variation by polarization.

## Main definitions

* `CKMA.TimePartition`: finite deterministic partition of `[0, T]`
  (in `BrownianQuadraticVariation.TimePartition`).
* `CKMA.TimePartition.mesh`: largest time increment of a partition
  (in `BrownianQuadraticVariation.TimePartition`).
* `CKMA.TimePartition.covariation`: quadratic covariation sum over completed partition intervals
  (in `BrownianQuadraticVariation.TimePartition`).
* `CKMA.IsQuadraticCovariation`: a process is the limit, uniformly on compacts in probability,
  of the covariation sums along every deterministic vanishing-mesh partition sequence.
* `CKMA.quadraticCovariation`: the bracket `[X, Y]`, a chosen quadratic covariation process.

## Main results

* `CKMA.brownian_quadraticVariation_ucp`: uniform-on-compact convergence in probability of
  Brownian quadratic variation along deterministic partitions with vanishing mesh.
* `CKMA.brownian_quadraticVariation_ae`: almost-sure uniform convergence under summable meshes.
* `CKMA.brownian_covariation_ucp`: diagonal quadratic covariation for independent Brownian
  coordinates.
* `CKMA.brownian_covariation_ae`: almost-sure diagonal covariation under summable meshes.
* `CKMA.IsQuadraticCovariation.ae_eq`: quadratic covariation processes agree almost surely at
  each time.
* `CKMA.brownian_quadraticCovariation`: `[Bⁱ, Bʲ]_t = δᵢⱼ t` almost surely.
-/

public section

noncomputable section

namespace CKMA

open scoped NNReal ENNReal ProbabilityTheory BigOperators
open MeasureTheory ProbabilityTheory Filter Topology Kolmogorov

/-- Energy of the centered squared increments is at most twice mesh times `T`
(TauCeti's `IsPreBrownianReal.integral_sq_quadraticSum_sub_le`). -/
private lemma centeredIncrement_energy_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {T : ℝ≥0} (π : TimePartition T) (Y : Fin π.size → Ω → ℝ)
    (hYae : ∀ i, (fun ω ↦ B (π.node i.succ) ω - B (π.node i.castSucc) ω) =ᵐ[μ] Y i) :
    ∫ ω, (∑ i : Fin π.size, ((Y i ω) ^ 2 - π.increment i)) ^ 2 ∂μ ≤
      2 * (π.mesh : ℝ) * (T : ℝ) := by
  have hae : (fun ω ↦ (∑ i : Fin π.size, ((Y i ω) ^ 2 - π.increment i)) ^ 2) =ᵐ[μ]
      fun ω ↦ (TauCeti.Probability.quadraticSum B π.node ω -
        ((π.node (Fin.last π.size) : ℝ) - π.node 0)) ^ 2 := by
    filter_upwards [ae_all_iff.2 hYae] with ω hω
    have h (i : Fin π.size) : Y i ω = B (π.node i.succ) ω - B (π.node i.castSucc) ω :=
      (hω i).symm
    simp only [TauCeti.Probability.quadraticSum_def, h, Finset.sum_sub_distrib, π.sum_increment,
      π.node_last, π.node_zero, NNReal.coe_zero, sub_zero]
  rw [integral_congr_ae hae]
  calc
    _ ≤ 2 * ((π.node (Fin.last π.size) : ℝ) - π.node 0) * π.mesh :=
      hB.integral_sq_quadraticSum_sub_le π.monotone_node fun i ↦
        (π.increment_eq_sub i).symm.trans_le (π.increment_le_mesh i)
    _ = 2 * (π.mesh : ℝ) * (T : ℝ) := by
      rw [π.node_last, π.node_zero, NNReal.coe_zero, sub_zero]
      ring

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
    (hB.memLp_sq_sub (π.node i.succ) (π.node i.castSucc)).ae_eq <|
      (hYae i).mono fun ω hω ↦ by simp only [raw] at hω ⊢; rw [hω]
  let X : Fin π.size → Ω → ℝ := fun i ω ↦ (Y i ω) ^ 2 - π.increment i
  have hXmeas : ∀ i, Measurable (X i) :=
    fun i ↦ ((hYmeas i).pow_const 2).sub measurable_const
  have hXmean : ∀ i, ∫ ω, X i ω ∂μ = 0 := by
    intro i
    have hsq : ∫ ω, (Y i ω) ^ 2 ∂μ = π.increment i := by
      have hpow : (fun ω ↦ (raw i ω) ^ 2) =ᵐ[μ] fun ω ↦ (Y i ω) ^ 2 :=
        (hYae i).mono fun ω hω ↦ congrArg (fun z ↦ z ^ 2) hω
      rw [← integral_congr_ae hpow, π.increment_eq_sub]
      exact hB.integral_sq_sub_of_le (π.monotone_node (Fin.castSucc_le_succ i))
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
  have hkol := measure_exists_le_abs_partialSum_le hXmeas hXmean hXLp hXindep (half_pos hε)
  have henergy := centeredIncrement_energy_le hB π Y hYae
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
        lt_of_le_of_lt (by simpa [abs_sub_comm] using π.abs_sub_covered_le_mesh ht) hmesh
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
      rw [tsum_eq_zero_iff]
      intro i
      simp [bump, hN (i + N) (Nat.le_add_left N i)]
    have heq := Summable.sum_add_tsum_nat_add' (f := bump) (k := N)
      (CompleteLattice.summable (f := fun i ↦ bump (i + N)))
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
      refine ne_top_of_le_ne_top ?_ (tsum_le_tsum hle)
      rw [tsum_add]
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

/-- A normalized difference of independent pre-Brownian motions is pre-Brownian. -/
private lemma isPreBrownianReal_normalizedDiff {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {B C : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) (hC : IsPreBrownianReal C μ)
    (hind : IndepFun (fun ω ↦ fun t ↦ B t ω) (fun ω ↦ fun t ↦ C t ω) μ) :
    IsPreBrownianReal (fun t ω ↦ (B t ω - C t ω) / Real.sqrt 2) μ := by
  have hnegMeas : Measurable (fun f : ℝ≥0 → ℝ ↦ -f) :=
    Measurable.of_eval fun t ↦ measurable_neg.comp (measurable_pi_apply t)
  have hsum := isPreBrownianReal_normalizedSum hB hC.neg (hind.comp measurable_id hnegMeas)
  refine IsPreBrownianReal.congr hsum fun t ↦ ae_of_all μ fun ω ↦ ?_
  simp [Pi.neg_apply, sub_eq_add_neg]

/-- Polarization bound: the bilinear covariation is at most the mean of the deviations of
the two normalized quadratic variations from elapsed time. -/
private lemma abs_covariation_le_polarized {Ω : Type*} {T : ℝ≥0} (π : TimePartition T)
    (B C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    |π.covariation B C t ω| ≤
      (|π.covariation (fun s ω ↦ (B s ω + C s ω) / Real.sqrt 2)
          (fun s ω ↦ (B s ω + C s ω) / Real.sqrt 2) t ω - (t : ℝ)| +
        |π.covariation (fun s ω ↦ (B s ω - C s ω) / Real.sqrt 2)
          (fun s ω ↦ (B s ω - C s ω) / Real.sqrt 2) t ω - (t : ℝ)|) / 2 := by
  have hpol := covariation_polarization π B C t ω
  rw [show π.covariation B C t ω =
      ((π.covariation (fun s ω ↦ (B s ω + C s ω) / Real.sqrt 2)
          (fun s ω ↦ (B s ω + C s ω) / Real.sqrt 2) t ω - (t : ℝ)) -
        (π.covariation (fun s ω ↦ (B s ω - C s ω) / Real.sqrt 2)
          (fun s ω ↦ (B s ω - C s ω) / Real.sqrt 2) t ω - (t : ℝ))) / 2 by linarith,
    abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  gcongr
  exact abs_sub _ _

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
    have hM : IsPreBrownianReal M μ :=
      isPreBrownianReal_normalizedDiff (hB i) (hB j) (hind.indepFun hij)
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
    have hbound : |(π n).covariation (B i) (B j) t ω| ≤
        (|(π n).covariation P P t ω - (t : ℝ)| +
          |(π n).covariation M M t ω - (t : ℝ)|) / 2 :=
      abs_covariation_le_polarized (π n) (B i) (B j) t ω
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

/-- **08.7**, almost-sure covariation: for independent Brownian coordinates and partitions with
summable meshes (for example dyadic partitions), the completed-interval covariation sums converge
almost surely to `δᵢⱼ t`, uniformly on `[0, T]`. -/
theorem brownian_covariation_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (B : Fin d → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) μ)
    (hind : iIndepFun (fun i ω ↦ fun t ↦ B i t ω) μ)
    {T : ℝ≥0} (π : ℕ → TimePartition T)
    (hmesh : Summable (fun n ↦ ((π n).mesh : ℝ))) (i j : Fin d) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t ≤ T,
      |(π n).covariation (B i) (B j) t ω - if i = j then (t : ℝ) else 0| < ε := by
  by_cases hij : i = j
  · subst hij
    simpa using brownian_quadraticVariation_ae μ (hB i) π hmesh
  · have hP := brownian_quadraticVariation_ae μ
      (isPreBrownianReal_normalizedSum (hB i) (hB j) (hind.indepFun hij)) π hmesh
    have hM := brownian_quadraticVariation_ae μ
      (isPreBrownianReal_normalizedDiff (hB i) (hB j) (hind.indepFun hij)) π hmesh
    filter_upwards [hP, hM] with ω hPω hMω
    intro ε hε
    filter_upwards [hPω ε hε, hMω ε hε] with n hPn hMn t ht
    rw [ite_eq_right hij, sub_zero]
    have hb := abs_covariation_le_polarized (π n) (B i) (B j) t ω
    linarith [hPn t ht, hMn t ht]

section Bracket

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `A` is a quadratic covariation process of `X` and `Y` under `μ`: for every horizon `T` and
every sequence of deterministic partitions of `[0, T]` with mesh tending to zero, the
completed-interval covariation sums converge to `A` in probability, uniformly on `[0, T]`. -/
@[expose]
def IsQuadraticCovariation (X Y : ℝ≥0 → Ω → ℝ) (μ : Measure Ω) (A : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ (T : ℝ≥0) (π : ℕ → TimePartition T), Tendsto (fun n ↦ (π n).mesh) atTop (𝓝 0) →
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ μ {ω | ∃ t ≤ T,
      ε < |(π n).covariation X Y t ω - A t ω|}) atTop (𝓝 0)

/-- Defining property of `IsQuadraticCovariation`. -/
theorem isQuadraticCovariation_iff {X Y : ℝ≥0 → Ω → ℝ} {μ : Measure Ω}
    {A : ℝ≥0 → Ω → ℝ} : IsQuadraticCovariation X Y μ A ↔
      ∀ (T : ℝ≥0) (π : ℕ → TimePartition T), Tendsto (fun n ↦ (π n).mesh) atTop (𝓝 0) →
        ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ μ {ω | ∃ t ≤ T,
          ε < |(π n).covariation X Y t ω - A t ω|}) atTop (𝓝 0) :=
  Iff.rfl

/-- The uniform partitions of `[0, T]` have mesh tending to zero. -/
theorem TimePartition.tendsto_mesh_uniform (T : ℝ≥0) :
    Tendsto (fun n ↦ (TimePartition.uniform T n).mesh) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ ↦ T * (1 / ((n : ℝ≥0) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul T
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ zero_le) fun n ↦ ?_
  rw [mul_one_div]
  exact TimePartition.mesh_uniform_le T n

/-- Quadratic covariation processes are unique up to modification: two of them agree almost
surely at each fixed time. -/
theorem IsQuadraticCovariation.ae_eq {X Y : ℝ≥0 → Ω → ℝ} {μ : Measure Ω}
    {A A' : ℝ≥0 → Ω → ℝ} (hA : IsQuadraticCovariation X Y μ A)
    (hA' : IsQuadraticCovariation X Y μ A') (t : ℝ≥0) : A t =ᵐ[μ] A' t := by
  have hsmall : ∀ ε : ℝ, 0 < ε → μ {ω | ε < |A t ω - A' t ω|} = 0 := by
    intro ε hε
    let π := TimePartition.uniform t
    have h1 := hA t π (TimePartition.tendsto_mesh_uniform t) (ε / 2) (half_pos hε)
    have h2 := hA' t π (TimePartition.tendsto_mesh_uniform t) (ε / 2) (half_pos hε)
    refine le_antisymm (ge_of_tendsto' (by simpa using h1.add h2) fun n ↦ ?_) zero_le
    refine (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
    have hω : ε < |A t ω - A' t ω| := hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and, not_lt] at hnot
    have ha := hnot.1 t le_rfl
    have hb := hnot.2 t le_rfl
    have htri : |A t ω - A' t ω| ≤ |(π n).covariation X Y t ω - A t ω| +
        |(π n).covariation X Y t ω - A' t ω| := by
      calc
        |A t ω - A' t ω| = |((π n).covariation X Y t ω - A' t ω) -
            ((π n).covariation X Y t ω - A t ω)| := by ring_nf
        _ ≤ _ := (abs_sub _ _).trans_eq (add_comm _ _)
    linarith
  have hunion : {ω | A t ω ≠ A' t ω} ⊆ ⋃ m : ℕ, {ω | 1 / ((m : ℝ) + 1) < |A t ω - A' t ω|} := by
    intro ω hω
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (abs_pos.2 (sub_ne_zero.2 hω))
    exact Set.mem_iUnion.2 ⟨m, hm⟩
  exact ae_iff.2 (measure_mono_null hunion
    (measure_iUnion_null fun m ↦ hsmall _ (by positivity)))

open Classical in
/-- The quadratic covariation bracket `[X, Y]`: a chosen quadratic covariation process when one
exists, and `0` otherwise. By `IsQuadraticCovariation.ae_eq` it is determined almost surely at
each time. -/
@[expose]
def quadraticCovariation (X Y : ℝ≥0 → Ω → ℝ) (μ : Measure Ω) : ℝ≥0 → Ω → ℝ :=
  if h : ∃ A, IsQuadraticCovariation X Y μ A then h.choose else 0

/-- If a quadratic covariation process exists, the bracket is one. -/
theorem IsQuadraticCovariation.isQuadraticCovariation_quadraticCovariation
    {X Y : ℝ≥0 → Ω → ℝ} {μ : Measure Ω} {A : ℝ≥0 → Ω → ℝ}
    (hA : IsQuadraticCovariation X Y μ A) :
    IsQuadraticCovariation X Y μ (quadraticCovariation X Y μ) := by
  have h : ∃ A, IsQuadraticCovariation X Y μ A := ⟨A, hA⟩
  rw [quadraticCovariation, dite_eq_left h]
  exact h.choose_spec

/-- The bracket agrees almost surely, at each time, with any quadratic covariation process. -/
theorem IsQuadraticCovariation.quadraticCovariation_ae_eq
    {X Y : ℝ≥0 → Ω → ℝ} {μ : Measure Ω} {A : ℝ≥0 → Ω → ℝ}
    (hA : IsQuadraticCovariation X Y μ A) (t : ℝ≥0) :
    quadraticCovariation X Y μ t =ᵐ[μ] A t :=
  hA.isQuadraticCovariation_quadraticCovariation.ae_eq hA t

/-- **08.7**: for independent Brownian coordinates, `δᵢⱼ t` is a quadratic covariation process
of `Bⁱ` and `Bʲ`. -/
theorem brownian_isQuadraticCovariation (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (B : Fin d → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) μ)
    (hind : iIndepFun (fun i ω ↦ fun t ↦ B i t ω) μ) (i j : Fin d) :
    IsQuadraticCovariation (B i) (B j) μ (fun t _ ↦ if i = j then (t : ℝ) else 0) :=
  fun _ π hmesh ↦ brownian_covariation_ucp μ B hB hind π hmesh i j

/-- **08.7**, bracket form: `[Bⁱ, Bʲ]_t = δᵢⱼ t` almost surely, for each time `t`. -/
theorem brownian_quadraticCovariation (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (B : Fin d → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) μ)
    (hind : iIndepFun (fun i ω ↦ fun t ↦ B i t ω) μ) (i j : Fin d) (t : ℝ≥0) :
    quadraticCovariation (B i) (B j) μ t =ᵐ[μ] fun _ ↦ if i = j then (t : ℝ) else 0 :=
  (brownian_isQuadraticCovariation μ B hB hind i j).quadraticCovariation_ae_eq t

end Bracket

end CKMA
