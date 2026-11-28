/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.BrownianQuadraticVariation.QuadraticCovariation
public import Mathlib.Probability.BrownianMotion.Basic
public import TauCeti.Probability.BrownianMotion.PartitionMaximal

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

The uniform estimate is TauCeti's Doob maximal inequality for the time-centered quadratic sums at
the partition nodes (`TauCeti.Probability.BrownianMotion.PartitionMaximal`), together with the
gap between a time and the last completed node; `TimePartition.covariation_self_sub_covered`
identifies the two sums. Cross variation reduces to quadratic variation by polarization.

## Main definitions

* `CKMA.TimePartition`: finite deterministic partition of `[0, T]`
  (in `BrownianQuadraticVariation.TimePartition`).
* `CKMA.TimePartition.mesh`: largest time increment of a partition
  (in `BrownianQuadraticVariation.TimePartition`).
* `CKMA.TimePartition.covariation`: quadratic covariation sum over completed partition intervals
  (in `BrownianQuadraticVariation.TimePartition`).
* `CKMA.IsQuadraticCovariation`: a process is the limit, uniformly on compacts in probability,
  of the covariation sums along every deterministic vanishing-mesh partition sequence
  (in `BrownianQuadraticVariation.QuadraticCovariation`).
* `CKMA.quadraticCovariation`: the bracket `[X, Y]`, a chosen quadratic covariation process
  (in `BrownianQuadraticVariation.QuadraticCovariation`).

## Main results

* `CKMA.brownian_quadraticVariation_ucp`: uniform-on-compact convergence in probability of
  Brownian quadratic variation along deterministic partitions with vanishing mesh.
* `CKMA.brownian_quadraticVariation_ae`: almost-sure uniform convergence under summable meshes.
* `CKMA.brownian_covariation_ucp`: diagonal quadratic covariation for independent Brownian
  coordinates.
* `CKMA.brownian_covariation_ae`: almost-sure diagonal covariation under summable meshes.
* `CKMA.TimePartition.covariation_self_sub_covered`: the completed-interval quadratic sum minus
  the covered time is TauCeti's time-centered quadratic sum along the nodes.
* `CKMA.brownian_isQuadraticCovariation`: `δᵢⱼ t` is a quadratic covariation process of
  independent Brownian coordinates.
* `CKMA.brownian_quadraticCovariation`: `[Bⁱ, Bʲ]_t = δᵢⱼ t` almost surely.
-/

public section

noncomputable section

namespace CKMA

open scoped NNReal ENNReal ProbabilityTheory BigOperators
open MeasureTheory ProbabilityTheory Filter Topology

namespace TimePartition

/-- Covariation minus the covered time is TauCeti's time-centered quadratic sum along the node
sequence, up to the number of completed intervals. -/
theorem covariation_self_sub_covered {T : ℝ≥0} (π : TimePartition T) {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    π.covariation B B t ω - π.covered t =
      TauCeti.Probability.quadraticSumSubTime B π.nodeSeq (π.completedCount t) ω := by
  set k := π.completedCount t
  have hk : k ≤ π.size := π.completedCount_le_size t
  let g : ℕ → ℝ := fun i ↦ (B (π.nodeSeq (i + 1)) ω - B (π.nodeSeq i) ω) ^ 2
  have hcov : π.covariation B B t ω = ∑ i ∈ Finset.range k, g i := by
    have hterm (i : Fin π.size) : (if π.node i.succ ≤ t then
        (B (π.node i.succ) ω - B (π.node i.castSucc) ω) *
          (B (π.node i.succ) ω - B (π.node i.castSucc) ω) else 0) =
        if (i : ℕ) < k then g i else 0 := by
      have hiff : π.node i.succ ≤ t ↔ (i : ℕ) < k := π.completed_iff_val_lt t i
      by_cases h : π.node i.succ ≤ t
      · simp only [h, hiff.1 h, ↓reduceIte, ← sq, g, π.nodeSeq_of_le i.isLt,
          π.nodeSeq_of_le i.isLt.le]
        rfl
      · simp only [h, mt hiff.2 h, ↓reduceIte]
    rw [covariation, Finset.sum_congr rfl fun i _ ↦ hterm i,
      Fin.sum_univ_eq_sum_range (fun i ↦ if i < k then g i else 0), ← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have h0 : π.node ⟨0, Nat.lt_succ_of_le (Nat.zero_le _)⟩ = 0 := π.node_zero
  rw [TauCeti.Probability.quadraticSumSubTime_eq_sum_sub, hcov, covered, π.nodeSeq_of_le hk,
    π.nodeSeq_of_le (Nat.zero_le _), h0, NNReal.coe_zero, sub_zero]

end TimePartition

/-- One-partition bound for the nonstrict quadratic-variation deviation, from TauCeti's maximal
inequality for the time-centered quadratic sums at the partition nodes
(`IsPreBrownianReal.integral_sq_partialSups_abs_quadraticSumSubTime_le_of_sub_le`) and the gap
between a time and the last completed node (`TimePartition.abs_sub_covered_le_mesh`). -/
private lemma quadraticVariation_measure_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {T : ℝ≥0} (π : TimePartition T) {ε : ℝ} (hε : 0 < ε)
    (hmesh : (π.mesh : ℝ) < ε / 2) :
    μ {ω | ∃ t ≤ T, ε ≤ |π.covariation B B t ω - (t : ℝ)|} ≤
      ENNReal.ofReal (32 * (π.mesh : ℝ) * (T : ℝ) / ε ^ 2) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  let M : Ω → ℝ := partialSups
    (fun j ω ↦ |TauCeti.Probability.quadraticSumSubTime B π.nodeSeq j ω|) π.size
  have hM0 (ω : Ω) : 0 ≤ M ω :=
    (abs_nonneg _).trans (le_partialSups_of_le (fun j ω ↦
      |TauCeti.Probability.quadraticSumSubTime B π.nodeSeq j ω|) (Nat.zero_le π.size) ω)
  have hM2 : ∫ ω, M ω ^ 2 ∂μ ≤ 8 * (π.mesh : ℝ) * (T : ℝ) := by
    have h := hB.integral_sq_partialSups_abs_quadraticSumSubTime_le_of_sub_le π.size
      (π.monotone_nodeSeq.monotoneOn _) (δ := π.mesh) fun i hi ↦ by
        rw [π.nodeSeq_of_le hi, π.nodeSeq_of_le hi.le]
        exact (π.increment_eq_sub ⟨i, hi⟩).symm.trans_le (π.increment_le_mesh ⟨i, hi⟩)
    have hT : (π.nodeSeq π.size : ℝ) - π.nodeSeq 0 = T := by
      rw [π.nodeSeq_of_le le_rfl, π.nodeSeq_of_le (Nat.zero_le _)]
      have hl : π.node ⟨π.size, Nat.lt_succ_self _⟩ = T := π.node_last
      have h0 : π.node ⟨0, Nat.lt_succ_of_le (Nat.zero_le _)⟩ = 0 := π.node_zero
      rw [hl, h0, NNReal.coe_zero, sub_zero]
    rw [hT] at h
    linarith
  have hsub : {ω | ∃ t ≤ T, ε ≤ |π.covariation B B t ω - (t : ℝ)|} ⊆
      {ω | (ε / 2) ^ 2 ≤ M ω ^ 2} := by
    rintro ω ⟨t, ht, hdev⟩
    have hk : |π.covariation B B t ω - π.covered t| ≤ M ω := by
      rw [π.covariation_self_sub_covered]
      exact le_partialSups_of_le (fun j ω ↦
        |TauCeti.Probability.quadraticSumSubTime B π.nodeSeq j ω|)
        (π.completedCount_le_size t) ω
    have hgap : |(π.covered t : ℝ) - t| < ε / 2 :=
      lt_of_le_of_lt (by simpa [abs_sub_comm] using π.abs_sub_covered_le_mesh ht) hmesh
    have htri : |π.covariation B B t ω - t| ≤
        |π.covariation B B t ω - π.covered t| + |(π.covered t : ℝ) - t| :=
      abs_sub_le _ _ _
    have hlt : ε / 2 < M ω := by linarith
    exact pow_le_pow_left₀ (by positivity) hlt.le 2
  have hint : Integrable (fun ω ↦ M ω ^ 2) μ :=
    (hB.memLp_partialSups_abs_quadraticSumSubTime π.nodeSeq π.size).integrable_sq
  have hmark := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω ↦ sq_nonneg (M ω)) hint
    ((ε / 2) ^ 2)
  have hreal : μ.real {ω | (ε / 2) ^ 2 ≤ M ω ^ 2} ≤ 32 * (π.mesh : ℝ) * (T : ℝ) / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hmark, hM2]
  calc μ {ω | ∃ t ≤ T, ε ≤ |π.covariation B B t ω - (t : ℝ)|}
      ≤ μ {ω | (ε / 2) ^ 2 ≤ M ω ^ 2} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {ω | (ε / 2) ^ 2 ≤ M ω ^ 2}) := (ofReal_measureReal).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- **08.7**: uniform-on-compact convergence in probability along deterministic vanishing mesh.
No path continuity assumption is needed for completed-interval quadratic sums. -/
theorem brownian_quadraticVariation_ucp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) {T : ℝ≥0} (π : ℕ → TimePartition T)
    (hmesh : Tendsto (fun n ↦ (π n).mesh) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ μ {ω | ∃ t ≤ T,
      ε < |(π n).covariation B B t ω - (t : ℝ)|}) atTop (𝓝 0) := by
  intro ε hε
  have hmeshR : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0) := NNReal.tendsto_coe.mpr hmesh
  have hev : ∀ᶠ n in atTop, ((π n).mesh : ℝ) < ε / 2 :=
    hmeshR.eventually (Iio_mem_nhds (half_pos hε))
  have hupper : Tendsto (fun n ↦ ENNReal.ofReal
      (32 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2)) atTop (𝓝 0) := by
    have hlin : Tendsto (fun n ↦ 32 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2) atTop (𝓝 0) := by
      have hrewrite : (fun n ↦ 32 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2) =
          fun n ↦ (32 * (T : ℝ) / ε ^ 2) * ((π n).mesh : ℝ) := by
        ext n
        ring
      rw [hrewrite]
      simpa using hmeshR.const_mul (32 * (T : ℝ) / ε ^ 2)
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
    _ ≤ ENNReal.ofReal (32 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2) :=
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
        ENNReal.ofReal (32 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2) + bump n := by
      intro n
      by_cases hn : ((π n).mesh : ℝ) < ε / 2
      · simpa [bad, bump, hn] using quadraticVariation_measure_le hB (π n) hε hn
      · have hprob : μ (bad n) ≤ 1 := by
          calc
            μ (bad n) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        have hnonneg : 0 ≤ ENNReal.ofReal (32 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2) :=
          bot_le
        simpa [bump, hn] using le_trans hprob (by simp)
    have hofReal : ∑' n, ENNReal.ofReal (32 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2) ≠ ∞ := by
      refine Summable.tsum_ofReal_ne_top ?_
      have hrewrite : (fun n ↦ 32 * ((π n).mesh : ℝ) * (T : ℝ) / ε ^ 2) =
          fun n ↦ (32 * (T : ℝ) / ε ^ 2) * ((π n).mesh : ℝ) := by
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
