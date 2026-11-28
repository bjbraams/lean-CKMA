/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.BrownianTheory.Modification
public import CKMA.Probability.BrownianTheory.DyadicPath
public import Mathlib.Topology.MetricSpace.Holder

import CKMA.Probability.BrownianTheory.DyadicLimit

/-!
# Continuous modification along dyadic floors

On the full-measure set `holderGoodSet` of paths whose dyadic increments on each integer
interval are bounded by a constant times a power of the mesh, the values at dyadic floors form a
Cauchy sequence. The limit is continuous, agrees with the original process at each fixed time,
and is locally Hölder for every exponent strictly below one half. Both almost sure inputs, the
good set and the convergence at a fixed time, come from TauCeti's Kolmogorov edge estimate
(`ProbabilityTheory.IsAEKolmogorovProcess.ae_exists_edist_le_mul_pow_rpow`) through
`BrownianTheory.Modification`; the deterministic dyadic chaining is in
`BrownianTheory.DyadicPath` and `BrownianTheory.DyadicLimit`.

## Main definitions

* `CKMA.Brownian.holderPath`: continuous modification constructed as the limit along dyadic
  floors.

## Main results

* `CKMA.Brownian.continuous_holderPath`: every modified path is continuous.
* `CKMA.Brownian.holderPath_isBrownian`: the dyadic-floor limit is a Brownian motion.
* `CKMA.exists_continuous_holder_modification`: a pre-Brownian process has an everywhere
  continuous Hölder modification.
-/

public section

noncomputable section

namespace CKMA

open Finset Filter MeasureTheory Metric ProbabilityTheory Set
open scoped NNReal ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

namespace Brownian

/-- Nonnegative form of the exponent `subHalf k`. -/
private def subHalfNN (k : ℕ) : ℝ≥0 := ⟨subHalf k, (subHalf_pos k).le⟩

/-- Real value of `subHalfNN`. -/
private lemma coe_subHalfNN (k : ℕ) : (subHalfNN k : ℝ) = subHalf k := rfl

/-- `subHalfNN k` is strictly positive. -/
private lemma subHalfNN_pos (k : ℕ) : 0 < subHalfNN k := by
  rw [← NNReal.coe_pos, coe_subHalfNN]
  exact subHalf_pos k

/-- Extension of the measurable version, equal to zero at negative times. -/
private def snap (hB : IsPreBrownianReal B μ) (ω : Ω) (x : ℝ) : ℝ :=
  if hx : 0 ≤ x then preBrownianVersion hB ⟨x, hx⟩ ω else 0

/-- On the nonnegative reals, `snap` is the measurable version. -/
private lemma snap_of_nonneg (hB : IsPreBrownianReal B μ) (ω : Ω) {x : ℝ} (hx : 0 ≤ x) :
    snap hB ω x = preBrownianVersion hB ⟨x, hx⟩ ω := by
  simp [snap, hx]

/-- Dyadic floor of a nonnegative time, as a nonnegative time. -/
@[expose]
def floorTime (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  ⟨dyadicFloorReal n (t : ℝ), dyadicFloorReal_nonneg n t⟩

/-- Real value of a dyadic floor, the defining equation of `floorTime`. -/
lemma coe_floorTime (n : ℕ) (t : ℝ≥0) :
    (floorTime n t : ℝ) = dyadicFloorReal n (t : ℝ) := rfl

/-- Measurable version evaluated at the dyadic floor. -/
@[expose]
def dyadicApprox (hB : IsPreBrownianReal B μ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  preBrownianVersion hB (floorTime n t) ω

/-- Defining equation of `dyadicApprox`. -/
lemma dyadicApprox_apply (hB : IsPreBrownianReal B μ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    dyadicApprox hB n t ω = preBrownianVersion hB (floorTime n t) ω := rfl

/-- Evaluation at a dyadic floor is measurable. -/
private lemma measurable_dyadicApprox (hB : IsPreBrownianReal B μ) (n : ℕ) (t : ℝ≥0) :
    Measurable (dyadicApprox hB n t) :=
  measurable_preBrownianVersion hB _

/-- `snap` at a dyadic floor is the dyadic approximation. -/
private lemma snap_floor (hB : IsPreBrownianReal B μ) (ω : Ω) (n : ℕ) (t : ℝ≥0) :
    snap hB ω (dyadicFloorReal n (t : ℝ)) = dyadicApprox hB n t ω := by
  have hx : 0 ≤ dyadicFloorReal n (t : ℝ) := dyadicFloorReal_nonneg n t
  unfold snap dyadicApprox floorTime
  split_ifs
  exact congrArg (fun u => preBrownianVersion hB u ω) (Subtype.ext rfl)

/-- A nonnegative real is at most one more than its integer floor. -/
private lemma le_natFloor_add_one (t : ℝ≥0) :
    (t : ℝ) ≤ (Nat.floor (t : ℝ) + 1 : ℕ) := by
  have hlt : (t : ℝ) < (Nat.floor (t : ℝ) : ℝ) + 1 := Nat.lt_floor_add_one _
  exact le_of_lt <| by simpa [Nat.cast_add, Nat.cast_one] using hlt

/-- The distance from a time to its dyadic floor is at most one mesh. -/
private lemma abs_floorTime_sub (n : ℕ) (t : ℝ≥0) :
    |(floorTime n t : ℝ) - (t : ℝ)| ≤ 1 / 2 ^ n := by
  have hle : dyadicFloorReal n (t : ℝ) ≤ (t : ℝ) := dyadicFloorReal_le t.2
  have hlt : (t : ℝ) < dyadicFloorReal n (t : ℝ) + 1 / 2 ^ n := lt_dyadicFloorReal_add n t
  rw [coe_floorTime, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hle)]
  exact le_of_lt (by linarith)

/-- At a dyadic time, `snap` is the measurable version. -/
private lemma snap_dyadicPoint (hB : IsPreBrownianReal B μ) (ω : Ω) (j n i : ℕ) :
    snap hB ω ((j : ℝ) + (i : ℝ) / 2 ^ n) = preBrownianVersion hB (dyadicPoint j n i) ω := by
  rw [snap_of_nonneg hB ω (by positivity)]
  exact congrArg (fun u ↦ preBrownianVersion hB u ω) (NNReal.eq (coe_dyadicPoint j n i).symm)

open scoped Classical in
/-- A constant bounding the dyadic increments of a good path on the integer interval starting
at `j`, at exponent `subHalf k`; zero off the good set. -/
private def cellConst (hB : IsPreBrownianReal B μ) (ω : Ω) (k j : ℕ) : ℝ :=
  if hω : ω ∈ holderGoodSet hB then ((hω k j).choose : ℝ) else 0

/-- The cell constant is nonnegative. -/
private lemma cellConst_nonneg (hB : IsPreBrownianReal B μ) (ω : Ω) (k j : ℕ) :
    0 ≤ cellConst hB ω k j := by
  unfold cellConst
  split_ifs <;> positivity

/-- A good path has dyadic Hölder increments on every integer cell. -/
private lemma hasDyadic_snap (hB : IsPreBrownianReal B μ) {ω : Ω} (hω : ω ∈ holderGoodSet hB)
    (k j : ℕ) : HasDyadicIncrements (snap hB ω) (subHalf k) (cellConst hB ω k j) j := by
  intro n i hi
  have hsucc := snap_dyadicPoint hB ω j n (i + 1)
  push_cast at hsucc
  rw [hsucc, snap_dyadicPoint]
  simp only [cellConst, hω, ↓reduceDIte]
  exact (hω k j).choose_spec n i hi

open scoped Classical in
/-- Limit of the dyadic floors, and zero off the good set. -/
@[expose]
def holderPath (hB : IsPreBrownianReal B μ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ holderGoodSet hB then limUnder atTop (fun n => dyadicApprox hB n t ω) else 0

/-- On the good set, `holderPath` is the limit of the dyadic approximations. -/
lemma holderPath_of_mem (hB : IsPreBrownianReal B μ) {ω : Ω} (hω : ω ∈ holderGoodSet hB)
    (t : ℝ≥0) : holderPath hB t ω = limUnder atTop (fun n => dyadicApprox hB n t ω) := by
  simp [holderPath, hω]

/-- Off the good set, `holderPath` is `0`. -/
lemma holderPath_of_notMem (hB : IsPreBrownianReal B μ) {ω : Ω} (hω : ω ∉ holderGoodSet hB)
    (t : ℝ≥0) : holderPath hB t ω = 0 := by
  simp [holderPath, hω]

/-- On a good path the dyadic floors converge to `holderPath`. -/
private lemma tendsto_dyadicApprox_of_mem_holderGoodSet (hB : IsPreBrownianReal B μ) {ω : Ω}
    (hω : ω ∈ holderGoodSet hB) (t : ℝ≥0) : Tendsto (fun n => dyadicApprox hB n t ω) atTop
      (𝓝 (holderPath hB t ω)) := by
  let N : ℕ := Nat.floor (t : ℝ) + 1
  have htN : (t : ℝ) ≤ N := le_natFloor_add_one t
  have hK : ∀ j, j < N → 0 ≤ cellConst hB ω 0 j := fun j _ => cellConst_nonneg hB ω 0 j
  have hinc : ∀ j, j < N →
      HasDyadicIncrements (snap hB ω) (subHalf 0) (cellConst hB ω 0 j) j :=
    fun j _ => hasDyadic_snap hB hω 0 j
  have htend := tendsto_dyadicFloor_limUnder (subHalf_pos 0) hK hinc t.2 htN
  have heq : (fun n => dyadicApprox hB n t ω) =
      fun n => snap hB ω (dyadicFloorReal n (t : ℝ)) := by
    funext n
    exact (snap_floor hB ω n t).symm
  simp only [holderPath, hω, ite_true]
  rw [heq]
  exact htend

open scoped Classical in
/-- The piecewise dyadic approximation is measurable. -/
private lemma measurable_holderPiece (hB : IsPreBrownianReal B μ) (n : ℕ) (t : ℝ≥0) :
    Measurable (fun ω => if ω ∈ holderGoodSet hB then dyadicApprox hB n t ω else (0 : ℝ)) :=
  Measurable.ite (measurableSet_holderGoodSet hB) (measurable_dyadicApprox hB n t) measurable_const

open scoped Classical in
/-- Each time marginal of `holderPath` is a pointwise limit of measurable functions. -/
private lemma tendsto_holderPiece (hB : IsPreBrownianReal B μ) (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n => if ω ∈ holderGoodSet hB then dyadicApprox hB n t ω else (0 : ℝ)) atTop
      (𝓝 (holderPath hB t ω)) := by
  by_cases hω : ω ∈ holderGoodSet hB
  · simpa [holderPath, hω] using tendsto_dyadicApprox_of_mem_holderGoodSet hB hω t
  · simp only [holderPath, hω, ite_false]
    exact tendsto_const_nhds

/-- Each time marginal of the modification is measurable. -/
lemma measurable_holderPath (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    Measurable (holderPath hB t) :=
  measurable_of_tendsto_metrizable (fun n => measurable_holderPiece hB n t)
    (tendsto_pi_nhds.mpr fun ω => tendsto_holderPiece hB t ω)

/-- On a good path, `holderPath` is the limit of `snap` along dyadic floors. -/
private lemma holderPath_eq_lim (hB : IsPreBrownianReal B μ) {ω : Ω} (hω : ω ∈ holderGoodSet hB)
    (t : ℝ≥0) : holderPath hB t ω =
      limUnder atTop (fun n => snap hB ω (dyadicFloorReal n (t : ℝ))) := by
  simp only [holderPath, hω, ite_true]
  apply congrArg (limUnder atTop)
  ext n
  exact (snap_floor hB ω n t).symm

/-- Values of a good path on `[0, N]` obey the dyadic Hölder bound. -/
private lemma abs_sub_holderPath (hB : IsPreBrownianReal B μ) {ω : Ω} (hω : ω ∈ holderGoodSet hB)
    (k N : ℕ) {s t : ℝ≥0} (hs : (s : ℝ) ≤ N) (ht : (t : ℝ) ≤ N) :
    |holderPath hB t ω - holderPath hB s ω| ≤
      dyadicHolderFactor (subHalf k) *
        (∑ j ∈ Finset.range N, cellConst hB ω k j) * |(t : ℝ) - s| ^ subHalf k := by
  have hK : ∀ j, j < N → 0 ≤ cellConst hB ω k j := fun j _ => cellConst_nonneg hB ω k j
  have hinc : ∀ j, j < N →
      HasDyadicIncrements (snap hB ω) (subHalf k) (cellConst hB ω k j) j :=
    fun j _ => hasDyadic_snap hB hω k j
  rw [holderPath_eq_lim hB hω t, holderPath_eq_lim hB hω s, abs_sub_comm (t : ℝ) (s : ℝ)]
  exact abs_sub_dyadicFloor_lim (subHalf_pos k) hK hinc s.2 hs t.2 ht

/-- A good path is Hölder of exponent `subHalf k` on each compact interval. -/
private lemma holderOnWith_subHalf (hB : IsPreBrownianReal B μ) {ω : Ω} (hω : ω ∈ holderGoodSet hB)
    (k : ℕ) (T : ℝ≥0) : ∃ C : ℝ≥0,
      HolderOnWith C (subHalfNN k) (fun t => holderPath hB t ω) (Icc 0 T) := by
  let N : ℕ := Nat.floor (T : ℝ) + 1
  have hTN : (T : ℝ) ≤ N := le_natFloor_add_one T
  let Creal : ℝ :=
    dyadicHolderFactor (subHalf k) * ∑ j ∈ Finset.range N, cellConst hB ω k j
  have hC : 0 ≤ Creal :=
    mul_nonneg (le_of_lt (dyadicHolderFactor_pos (subHalf_pos k)))
      (Finset.sum_nonneg fun j _ => cellConst_nonneg hB ω k j)
  refine ⟨Real.toNNReal Creal, ?_⟩
  intro s hs t ht
  have hsN : (s : ℝ) ≤ N := le_trans (NNReal.coe_le_coe.mpr hs.2) hTN
  have htN : (t : ℝ) ≤ N := le_trans (NNReal.coe_le_coe.mpr ht.2) hTN
  have habs := abs_sub_holderPath hB hω k N hsN htN
  rw [edist_dist, edist_dist, NNReal.dist_eq, Real.dist_eq]
  calc
    ENNReal.ofReal |holderPath hB s ω - holderPath hB t ω| ≤
        ENNReal.ofReal (Creal * |(s : ℝ) - t| ^ subHalf k) := by
      apply ENNReal.ofReal_le_ofReal
      have hflip : |holderPath hB s ω - holderPath hB t ω| =
          |holderPath hB t ω - holderPath hB s ω| := abs_sub_comm _ _
      have htime : |(s : ℝ) - (t : ℝ)| = |(t : ℝ) - (s : ℝ)| := abs_sub_comm _ _
      rw [hflip, htime]
      simpa [Creal, mul_assoc] using habs
    _ = ENNReal.ofReal Creal * ENNReal.ofReal (|(s : ℝ) - t| ^ subHalf k) := by
      rw [ENNReal.ofReal_mul hC]
    _ = ENNReal.ofReal Creal * ENNReal.ofReal |(s : ℝ) - t| ^ subHalf k := by
      rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (subHalf_pos k).le]
    _ = (Real.toNNReal Creal : ℝ≥0∞) *
        ENNReal.ofReal |(s : ℝ) - t| ^ (subHalfNN k : ℝ) := by
      rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal Creal hC, coe_subHalfNN]

/-- Every positive exponent below one half is attained on each compact interval. -/
private lemma holderOnWith_of_le_subHalf (hB : IsPreBrownianReal B μ) {ω : Ω}
    (hω : ω ∈ holderGoodSet hB) {α : ℝ≥0} (hα : (α : ℝ) < 1 / 2) (T : ℝ≥0) :
    ∃ K : ℝ≥0, HolderOnWith K α (fun t => holderPath hB t ω) (Icc 0 T) := by
  obtain ⟨k, hk⟩ := exists_subHalf_ge hα
  obtain ⟨C, hC⟩ := holderOnWith_subHalf hB hω k T
  have hle : α ≤ subHalfNN k := by
    rw [← NNReal.coe_le_coe, coe_subHalfNN]
    exact hk
  by_cases hT : T = 0
  · exact ⟨C, by simp [hT, holderOnWith_singleton]⟩
  · refine ⟨C * T ^ (subHalfNN k - α : ℝ), ?_⟩
    refine HolderOnWith.of_le ?_ hC hle
    intro x hx y hy
    rw [edist_dist, NNReal.dist_eq]
    refine (ENNReal.ofReal_le_ofReal ?_).trans_eq (ENNReal.coe_nnreal_eq T).symm
    have hxT : (x : ℝ) ≤ T := NNReal.coe_le_coe.mpr hx.2
    have hyT : (y : ℝ) ≤ T := NNReal.coe_le_coe.mpr hy.2
    rw [abs_le]
    constructor <;> linarith [NNReal.coe_nonneg x, NNReal.coe_nonneg y]

/-- Every modified path is continuous. -/
lemma continuous_holderPath (hB : IsPreBrownianReal B μ) (ω : Ω) :
    Continuous (fun t => holderPath hB t ω) := by
  by_cases hω : ω ∈ holderGoodSet hB
  · rw [continuous_iff_continuousAt]
    intro t
    obtain ⟨C, hC⟩ := holderOnWith_subHalf hB hω 0 (t + 1)
    have hcont := hC.continuousOn (subHalfNN_pos 0)
    apply hcont.continuousAt
    rw [Metric.mem_nhds_iff]
    refine ⟨1, by norm_num, ?_⟩
    intro s hs
    rw [mem_ball, NNReal.dist_eq] at hs
    have hsle : s ≤ t + 1 := by
      have hlt : (s : ℝ) < (t : ℝ) + 1 := by
        have habs : |(s : ℝ) - t| < 1 := by simpa [Real.dist_eq] using hs
        have hsub : (s : ℝ) - t ≤ |(s : ℝ) - t| := le_abs_self _
        linarith
      exact NNReal.coe_le_coe.mp hlt.le
    exact ⟨bot_le, hsle⟩
  · have hzero : (fun t => holderPath hB t ω) = fun _ => 0 := by
      funext t
      simp [holderPath, hω]
    rw [hzero]
    exact continuous_const

/-- The modification agrees with the measurable version at each fixed time. -/
private lemma holderPath_ae_eq_version (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    holderPath hB t =ᵐ[μ] preBrownianVersion hB t := by
  filter_upwards [ae_mem_holderGoodSet hB,
    ae_tendsto_preBrownianVersion hB (abs_floorTime_sub · t)] with ω hω hlim
  have hpath := tendsto_dyadicApprox_of_mem_holderGoodSet hB hω t
  have hseq : (fun n => dyadicApprox hB n t ω) =
      fun n => preBrownianVersion hB (floorTime n t) ω := rfl
  rw [hseq] at hpath
  have hval := tendsto_nhds_unique hpath hlim
  simpa [holderPath, hω] using hval

/-- The modification agrees with the original process at each fixed time. -/
private lemma holderPath_ae_eq (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    holderPath hB t =ᵐ[μ] B t :=
  (holderPath_ae_eq_version hB t).trans (preBrownianVersion_ae_eq hB t).symm

/-- The dyadic-floor limit is a Brownian motion. -/
lemma holderPath_isBrownian (hB : IsPreBrownianReal B μ) :
    IsBrownianReal (holderPath hB) μ where
  toIsPreBrownianReal := IsPreBrownianReal.congr (preBrownianVersion_isPreBrownian hB)
    fun t => (holderPath_ae_eq_version hB t).symm
  cont := Filter.Eventually.of_forall (continuous_holderPath hB)

end Brownian

open Brownian

/-- A pre-Brownian process has an everywhere continuous Hölder modification. -/
theorem exists_continuous_holder_modification (hB : IsPreBrownianReal B μ) :
    ∃ C : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable (C t)) ∧ (∀ ω, Continuous (fun t => C t ω)) ∧
        IsBrownianReal C μ ∧ (∀ t, C t =ᵐ[μ] B t) ∧
          ∀ᵐ ω ∂μ, ∀ α : ℝ≥0, α < 1 / 2 →
            ∀ T : ℝ≥0, ∃ K : ℝ≥0,
              HolderOnWith K α (fun t => C t ω) (Icc 0 T) := by
  refine ⟨holderPath hB, measurable_holderPath hB, continuous_holderPath hB,
    holderPath_isBrownian hB, holderPath_ae_eq hB, ?_⟩
  filter_upwards [ae_mem_holderGoodSet hB] with ω hω α hα T
  have hα' : (α : ℝ) < 1 / 2 := by exact_mod_cast hα
  exact holderOnWith_of_le_subHalf hB hω hα' T

end CKMA
