/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.BrownianTheory.Modification
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Continuous modification along dyadic floors

On the full-measure set of paths with summable dyadic increments, dyadic floors form a
Cauchy sequence. The limit is continuous, agrees with the original process at each fixed
time, and is locally Hölder for every exponent strictly below one half.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Classical Finset Filter MeasureTheory Metric ProbabilityTheory Set
open scoped NNReal ENNReal Topology

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- Nonnegative form of the exponent `subHalf k`. -/
def subHalfNN (k : ℕ) : ℝ≥0 := ⟨subHalf k, (subHalf_pos k).le⟩

/-- Real value of `subHalfNN`. -/
lemma coe_subHalfNN (k : ℕ) : (subHalfNN k : ℝ) = subHalf k := rfl

/-- `subHalfNN k` is strictly positive. -/
lemma subHalfNN_pos (k : ℕ) : 0 < subHalfNN k := by
  rw [← NNReal.coe_pos, coe_subHalfNN]
  exact subHalf_pos k

/-- Extension of the measurable version, equal to zero at negative times. -/
def snap (hB : IsPreBrownianReal B μ) (ω : Ω) (x : ℝ) : ℝ :=
  if hx : 0 ≤ x then version hB ⟨x, hx⟩ ω else 0

/-- On the nonnegative reals, `snap` is the measurable version. -/
lemma snap_of_nonneg (hB : IsPreBrownianReal B μ) (ω : Ω) {x : ℝ} (hx : 0 ≤ x) :
    snap hB ω x = version hB ⟨x, hx⟩ ω := by
  simp [snap, hx]

/-- Dyadic floor of a nonnegative time, as a nonnegative time. -/
def floorTime (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  ⟨dyadicFloorReal n (t : ℝ), dyadicFloorReal_nonneg t.2⟩

/-- Real value of a dyadic floor. -/
lemma coe_floorTime (n : ℕ) (t : ℝ≥0) : (floorTime n t : ℝ) = dyadicFloorReal n (t : ℝ) := rfl

/-- Measurable version evaluated at the dyadic floor. -/
def approx (hB : IsPreBrownianReal B μ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  version hB (floorTime n t) ω

/-- Evaluation at a dyadic floor is measurable. -/
lemma measurable_approx (hB : IsPreBrownianReal B μ) (n : ℕ) (t : ℝ≥0) :
    Measurable (approx hB n t) :=
  measurable_version hB _

/-- `snap` at a dyadic floor is the dyadic approximation. -/
lemma snap_floor (hB : IsPreBrownianReal B μ) (ω : Ω) (n : ℕ) (t : ℝ≥0) :
    snap hB ω (dyadicFloorReal n (t : ℝ)) = approx hB n t ω := by
  have hx : 0 ≤ dyadicFloorReal n (t : ℝ) := dyadicFloorReal_nonneg t.2
  unfold snap approx floorTime
  split_ifs
  exact congrArg (fun u => version hB u ω) (Subtype.ext rfl)

/-- A nonnegative real is at most one more than its integer floor. -/
lemma le_natFloor_add_one (t : ℝ≥0) :
    (t : ℝ) ≤ (Nat.floor (t : ℝ) + 1 : ℕ) := by
  have hlt : (t : ℝ) < (Nat.floor (t : ℝ) : ℝ) + 1 := Nat.lt_floor_add_one _
  exact le_of_lt <| by simpa [Nat.cast_add, Nat.cast_one] using hlt

/-- The distance from a time to its dyadic floor is at most one mesh. -/
lemma abs_floorTime_sub (n : ℕ) (t : ℝ≥0) :
    |(floorTime n t : ℝ) - (t : ℝ)| ≤ 1 / 2 ^ n := by
  have hle : dyadicFloorReal n (t : ℝ) ≤ (t : ℝ) := dyadicFloorReal_le t.2
  have hlt : (t : ℝ) < dyadicFloorReal n (t : ℝ) + 1 / 2 ^ n := lt_dyadicFloorReal_add t.2
  rw [coe_floorTime, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hle)]
  exact le_of_lt (by linarith)

/-- Threshold `2 ^ (-n / 4)` used for second-moment Borel--Cantelli. -/
def meshRoot (n : ℕ) : ℝ := (2 : ℝ) ^ (-(n : ℝ) / 4)

/-- The second-moment threshold is positive. -/
lemma meshRoot_pos (n : ℕ) : 0 < meshRoot n :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- Squaring the threshold doubles the negative exponent. -/
lemma meshRoot_sq (n : ℕ) : meshRoot n ^ (2 : ℝ) = (2 : ℝ) ^ (-(n : ℝ) / 2) := by
  unfold meshRoot
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- Paths whose dyadic-floor increment exceeds the second-moment threshold. -/
def floorDeviation (hB : IsPreBrownianReal B μ) (t : ℝ≥0) (n : ℕ) : Set Ω :=
  {ω | meshRoot n ≤ |version hB (floorTime n t) ω - version hB t ω|}

/-- One floor increment obeys a summable second-moment bound. -/
lemma measure_floorDeviation_le (hB : IsPreBrownianReal B μ) (t : ℝ≥0) (n : ℕ) :
    μ (floorDeviation hB t n) ≤
      ENNReal.ofReal (gaussianAbsMoment 2 * (2 : ℝ) ^ (-(n : ℝ) / 2)) := by
  have hp : (0 : ℝ) < 2 := by norm_num
  have hδ : 0 < meshRoot n := meshRoot_pos n
  have hint : Integrable (fun ω =>
      |version hB (floorTime n t) ω - version hB t ω| ^ (2 : ℝ)) μ := by
    have hg := integrable_abs_rpow_gaussianReal_var hp
      (nndist (floorTime n t : ℝ) (t : ℝ))
    simpa [Function.comp_def] using
      ((version_isPreBrownian hB).hasLaw_sub (floorTime n t) t).integrable_comp hg
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) (2 : ℝ)) hint
    (meshRoot n ^ (2 : ℝ))
  have hset : {ω | meshRoot n ^ (2 : ℝ) ≤
      |version hB (floorTime n t) ω - version hB t ω| ^ (2 : ℝ)} =
      floorDeviation hB t n := by
    ext ω
    simp only [floorDeviation, mem_ofPred_eq]
    exact Real.rpow_le_rpow_iff (le_of_lt hδ) (abs_nonneg _) hp
  have hmark' : meshRoot n ^ (2 : ℝ) * μ.real (floorDeviation hB t n) ≤
      ∫ ω, |version hB (floorTime n t) ω - version hB t ω| ^ (2 : ℝ) ∂μ := by
    simpa only [hset] using hmark
  have hintle := IsPreBrownianReal.integral_abs_sub_rpow_le (version_isPreBrownian hB) hp
    (floorTime n t) t
  have hdist : |(floorTime n t : ℝ) - (t : ℝ)| ^ ((2 : ℝ) / 2) =
      |(floorTime n t : ℝ) - (t : ℝ)| := by
    rw [div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one]
  have hδ2 : 0 < meshRoot n ^ (2 : ℝ) := Real.rpow_pos_of_pos hδ _
  rw [hdist] at hintle
  have hdiv : μ.real (floorDeviation hB t n) ≤
      gaussianAbsMoment 2 * |(floorTime n t : ℝ) - (t : ℝ)| /
        (meshRoot n ^ (2 : ℝ)) := by
    rw [le_div_iff₀ hδ2, mul_comm]
    exact hmark'.trans hintle
  have hM : 0 ≤ gaussianAbsMoment 2 := gaussianAbsMoment_nonneg hp
  have hmesh : |(floorTime n t : ℝ) - (t : ℝ)| ≤ (2 : ℝ) ^ (-(n : ℝ)) := by
    rw [← one_div_two_pow_eq_rpow]
    exact abs_floorTime_sub n t
  have hnum : gaussianAbsMoment 2 * |(floorTime n t : ℝ) - (t : ℝ)| ≤
      gaussianAbsMoment 2 * (2 : ℝ) ^ (-(n : ℝ)) :=
    mul_le_mul_of_nonneg_left hmesh hM
  have hcancel : (2 : ℝ) ^ (-(n : ℝ)) / (2 : ℝ) ^ (-(n : ℝ) / 2) =
      (2 : ℝ) ^ (-(n : ℝ) / 2) := by
    rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hbound : gaussianAbsMoment 2 * |(floorTime n t : ℝ) - (t : ℝ)| /
      (meshRoot n ^ (2 : ℝ)) ≤
      gaussianAbsMoment 2 * (2 : ℝ) ^ (-(n : ℝ) / 2) := by
    rw [meshRoot_sq]
    calc
      gaussianAbsMoment 2 * |(floorTime n t : ℝ) - (t : ℝ)| /
          (2 : ℝ) ^ (-(n : ℝ) / 2) ≤
          gaussianAbsMoment 2 * (2 : ℝ) ^ (-(n : ℝ)) / (2 : ℝ) ^ (-(n : ℝ) / 2) := by
        gcongr
      _ = gaussianAbsMoment 2 * (2 : ℝ) ^ (-(n : ℝ) / 2) := by
        rw [mul_div_assoc, hcancel]
  have hfin : μ (floorDeviation hB t n) ≠ ⊤ := measure_ne_top _ _
  have hreal : μ.real (floorDeviation hB t n) ≤
      gaussianAbsMoment 2 * (2 : ℝ) ^ (-(n : ℝ) / 2) := hdiv.trans hbound
  have hle : ENNReal.ofReal (μ.real (floorDeviation hB t n)) ≤
      ENNReal.ofReal (gaussianAbsMoment 2 * (2 : ℝ) ^ (-(n : ℝ) / 2)) :=
    ENNReal.ofReal_le_ofReal hreal
  rwa [measureReal_def, ENNReal.ofReal_toReal hfin] at hle

/-- The second-moment floor bounds form a convergent series. -/
lemma summable_floorBound :
    Summable (fun n : ℕ => gaussianAbsMoment 2 * (2 : ℝ) ^ (-(n : ℝ) / 2)) := by
  set r : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / 2)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := by
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) ?_
    rw [neg_div]
    exact neg_lt_zero.2 (by positivity)
  have hpow (n : ℕ) : (2 : ℝ) ^ (-(n : ℝ) / 2) = r ^ n := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have heq : (fun n : ℕ => gaussianAbsMoment 2 * r ^ n) =
      fun n : ℕ => gaussianAbsMoment 2 * (2 : ℝ) ^ (-(n : ℝ) / 2) := by
    funext n
    rw [hpow n]
  rw [← heq]
  exact (summable_geometric_of_lt_one hr0 hr1).mul_left _

/-- Dyadic floors of the measurable version converge almost surely. -/
lemma ae_tendsto_version_floor (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => version hB (floorTime n t) ω) atTop
      (𝓝 (version hB t ω)) := by
  have hle := ENNReal.tsum_le_tsum (fun n => measure_floorDeviation_le hB t n)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n =>
      mul_nonneg (gaussianAbsMoment_nonneg (by norm_num : (0 : ℝ) < 2))
        (Real.rpow_nonneg (by norm_num) _)) summable_floorBound] at hle
  have hsum : ∑' n, μ (floorDeviation hB t n) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hroot : Tendsto meshRoot atTop (𝓝 0) := by
    have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg (by norm_num) _
    have hr1 : (2 : ℝ) ^ (-(1 : ℝ) / 4) < 1 := by
      refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) ?_
      rw [neg_div]
      exact neg_lt_zero.2 (by positivity)
    have hpow : meshRoot = fun n => ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ^ n := by
      funext n
      unfold meshRoot
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    rw [hpow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  rcases Metric.tendsto_atTop.1 hroot ε hε with ⟨N0, hN0⟩
  rcases eventually_atTop.1 hω with ⟨N1, hN1⟩
  refine ⟨max N0 N1, ?_⟩
  intro n hn
  have hnot : ω ∉ floorDeviation hB t n := hN1 n (le_trans (le_max_right _ _) hn)
  have hlt : |version hB (floorTime n t) ω - version hB t ω| < meshRoot n := by
    simp only [floorDeviation, mem_ofPred_eq] at hnot
    exact lt_of_not_ge hnot
  have hrootε : meshRoot n < ε := by
    have hdist := hN0 n (le_trans (le_max_left _ _) hn)
    simpa [Real.dist_eq, abs_of_nonneg (meshRoot_pos n).le, sub_zero] using hdist
  rw [Real.dist_eq]
  exact hlt.trans hrootε

/-- Eventual dyadic increment bound on one integer cell. -/
def incrementTail (hB : IsPreBrownianReal B μ) (ω : Ω) (k j N : ℕ) : Prop :=
  ∀ n, N ≤ n → ∀ i : ℕ, i < 2 ^ n →
    |snap hB ω (↑j + (↑i + 1) / 2 ^ n) - snap hB ω (↑j + (↑i : ℝ) / 2 ^ n)| ≤
      ((1 : ℝ) / 2 ^ n) ^ subHalf k

/-- A good path has some finite increment threshold on each cell. -/
lemma exists_incrementTail (hB : IsPreBrownianReal B μ) {ω : Ω} (hω : ω ∈ good hB)
    (k j : ℕ) : ∃ N, incrementTail hB ω k j N := by
  rcases eventually_atTop.1 (hω k j) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn i hi
  have hnot : ω ∉ badInc hB k j n i := by
    intro hbad
    apply hN n hn
    rw [levelBad]
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨Finset.mem_range.mpr hi, hbad⟩⟩
  have hlt : |version hB (dyadicNN j n (i + 1)) ω -
      version hB (dyadicNN j n i) ω| < ((1 : ℝ) / 2 ^ n) ^ subHalf k := by
    simp only [badInc, mem_ofPred_eq] at hnot
    exact lt_of_not_ge hnot
  have hleft : snap hB ω ((j : ℝ) + ((i : ℝ) + 1) / (2 : ℝ) ^ n) =
      version hB (dyadicNN j n (i + 1)) ω := by
    have hx : (0 : ℝ) ≤ (j : ℝ) + ((i : ℝ) + 1) / (2 : ℝ) ^ n := by positivity
    have hcoe : (j : ℝ) + ((i : ℝ) + 1) / (2 : ℝ) ^ n =
        (dyadicNN j n (i + 1) : ℝ) := by
      rw [coe_dyadicNN, Nat.cast_add, Nat.cast_one]
    rw [snap_of_nonneg hB ω hx]
    exact congrArg (fun u => version hB u ω) (NNReal.eq hcoe)
  have hright : snap hB ω ((j : ℝ) + (i : ℝ) / (2 : ℝ) ^ n) =
      version hB (dyadicNN j n i) ω := by
    have hx : (0 : ℝ) ≤ (j : ℝ) + (i : ℝ) / (2 : ℝ) ^ n := by positivity
    rw [snap_of_nonneg hB ω hx]
    exact congrArg (fun u => version hB u ω) (NNReal.eq ((coe_dyadicNN j n i).symm))
  rw [hleft, hright]
  exact hlt.le

/-- First level after which the dyadic increments of a cell are Hölder. -/
def goodLevel (hB : IsPreBrownianReal B μ) (ω : Ω) (k j : ℕ) : ℕ :=
  if hω : ω ∈ good hB then Nat.find (exists_incrementTail hB hω k j) else 0

/-- The selected level really starts the Hölder tail. -/
lemma incrementTail_goodLevel (hB : IsPreBrownianReal B μ) {ω : Ω} (hω : ω ∈ good hB)
    (k j : ℕ) : incrementTail hB ω k j (goodLevel hB ω k j) := by
  have hlevel : goodLevel hB ω k j = Nat.find (exists_incrementTail hB hω k j) := by
    simp [goodLevel, hω]
  rw [hlevel]
  exact Nat.find_spec (exists_incrementTail hB hω k j)

/-- Hölder constant built from the increments before `goodLevel`. -/
def cellConst (hB : IsPreBrownianReal B μ) (ω : Ω) (k j : ℕ) : ℝ :=
  holderConstFrom (snap hB ω) (subHalf k) j (goodLevel hB ω k j)

/-- The cell constant is nonnegative. -/
lemma cellConst_nonneg (hB : IsPreBrownianReal B μ) (ω : Ω) (k j : ℕ) :
    0 ≤ cellConst hB ω k j :=
  holderConstFrom_nonneg _ _ _ _

/-- A good path has dyadic Hölder increments on every integer cell. -/
lemma hasDyadic_snap (hB : IsPreBrownianReal B μ) {ω : Ω} (hω : ω ∈ good hB)
    (k j : ℕ) : HasDyadicIncrements (snap hB ω) (subHalf k) (cellConst hB ω k j) j := by
  simpa [cellConst, incrementTail] using
    hasDyadicIncrements_of_eventually (subHalf_pos k).le
      (incrementTail_goodLevel hB hω k j)

/-- Limit of the dyadic floors, and zero off the good set. -/
def holderPath (hB : IsPreBrownianReal B μ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ good hB then limUnder atTop (fun n => approx hB n t ω) else 0

/-- On a good path the dyadic floors converge to `holderPath`. -/
lemma tendsto_approx_of_good (hB : IsPreBrownianReal B μ) {ω : Ω} (hω : ω ∈ good hB)
    (t : ℝ≥0) : Tendsto (fun n => approx hB n t ω) atTop
      (𝓝 (holderPath hB t ω)) := by
  let N : ℕ := Nat.floor (t : ℝ) + 1
  have htN : (t : ℝ) ≤ N := le_natFloor_add_one t
  have hK : ∀ j, j < N → 0 ≤ cellConst hB ω 0 j := fun j _ => cellConst_nonneg hB ω 0 j
  have hinc : ∀ j, j < N →
      HasDyadicIncrements (snap hB ω) (subHalf 0) (cellConst hB ω 0 j) j :=
    fun j _ => hasDyadic_snap hB hω 0 j
  have htend := tendsto_dyadicFloor_limUnder (subHalf_pos 0) hK hinc t.2 htN
  have heq : (fun n => approx hB n t ω) =
      fun n => snap hB ω (dyadicFloorReal n (t : ℝ)) := by
    funext n
    exact (snap_floor hB ω n t).symm
  simp only [holderPath, hω, ite_true]
  rw [heq]
  exact htend

/-- The piecewise dyadic approximation is measurable. -/
lemma measurable_holderPiece (hB : IsPreBrownianReal B μ) (n : ℕ) (t : ℝ≥0) :
    Measurable (fun ω => if ω ∈ good hB then approx hB n t ω else (0 : ℝ)) :=
  Measurable.ite (measurableSet_good hB) (measurable_approx hB n t) measurable_const

/-- Each time marginal of `holderPath` is a pointwise limit of measurable functions. -/
lemma tendsto_holderPiece (hB : IsPreBrownianReal B μ) (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n => if ω ∈ good hB then approx hB n t ω else (0 : ℝ)) atTop
      (𝓝 (holderPath hB t ω)) := by
  by_cases hω : ω ∈ good hB
  · simpa [holderPath, hω] using tendsto_approx_of_good hB hω t
  · simp only [holderPath, hω, ite_false]
    exact tendsto_const_nhds

/-- Each time marginal of the modification is measurable. -/
lemma measurable_holderPath (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    Measurable (holderPath hB t) :=
  measurable_of_tendsto_metrizable (fun n => measurable_holderPiece hB n t)
    (tendsto_pi_nhds.mpr fun ω => tendsto_holderPiece hB t ω)

/-- On a good path, `holderPath` is the limit of `snap` along dyadic floors. -/
lemma holderPath_eq_lim (hB : IsPreBrownianReal B μ) {ω : Ω} (hω : ω ∈ good hB)
    (t : ℝ≥0) : holderPath hB t ω =
      limUnder atTop (fun n => snap hB ω (dyadicFloorReal n (t : ℝ))) := by
  simp only [holderPath, hω, ite_true]
  apply congrArg (limUnder atTop)
  ext n
  exact (snap_floor hB ω n t).symm

/-- Values of a good path on `[0, N]` obey the dyadic Hölder bound. -/
lemma abs_sub_holderPath (hB : IsPreBrownianReal B μ) {ω : Ω} (hω : ω ∈ good hB)
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
lemma holderOnWith_subHalf (hB : IsPreBrownianReal B μ) {ω : Ω} (hω : ω ∈ good hB)
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
lemma holderOnWith_of_le_subHalf (hB : IsPreBrownianReal B μ) {ω : Ω}
    (hω : ω ∈ good hB) {α : ℝ≥0} (_hα0 : 0 < α) (hα : (α : ℝ) < 1 / 2) (T : ℝ≥0) :
    ∃ K : ℝ≥0, HolderOnWith K α (fun t => holderPath hB t ω) (Icc 0 T) := by
  obtain ⟨k, hk⟩ := exists_subHalf_ge (NNReal.coe_nonneg α) hα
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
  by_cases hω : ω ∈ good hB
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
lemma holderPath_ae_eq_version (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    holderPath hB t =ᵐ[μ] version hB t := by
  filter_upwards [ae_mem_good hB, ae_tendsto_version_floor hB t] with ω hω hlim
  have hpath := tendsto_approx_of_good hB hω t
  have hseq : (fun n => approx hB n t ω) = fun n => version hB (floorTime n t) ω := rfl
  rw [hseq] at hpath
  have hval := tendsto_nhds_unique hpath hlim
  simpa [holderPath, hω] using hval

/-- The modification agrees with the original process at each fixed time. -/
lemma holderPath_ae_eq (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    holderPath hB t =ᵐ[μ] B t :=
  (holderPath_ae_eq_version hB t).trans (version_ae_eq hB t).symm

/-- The dyadic-floor limit is a Brownian motion. -/
lemma holderPath_isBrownian (hB : IsPreBrownianReal B μ) :
    IsBrownianReal (holderPath hB) μ where
  toIsPreBrownianReal := IsPreBrownianReal.congr (version_isPreBrownian hB)
    fun t => (holderPath_ae_eq_version hB t).symm
  cont := Filter.Eventually.of_forall (continuous_holderPath hB)

/-- A pre-Brownian process has an everywhere continuous Hölder modification. -/
theorem exists_continuous_holder_modification (hB : IsPreBrownianReal B μ) :
    ∃ C : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable (C t)) ∧ (∀ ω, Continuous (fun t => C t ω)) ∧
        IsBrownianReal C μ ∧ (∀ t, C t =ᵐ[μ] B t) ∧
          ∀ᵐ ω ∂μ, ∀ α : ℝ≥0, 0 < α → α < 1 / 2 →
            ∀ T : ℝ≥0, ∃ K : ℝ≥0,
              HolderOnWith K α (fun t => C t ω) (Icc 0 T) := by
  refine ⟨holderPath hB, measurable_holderPath hB, continuous_holderPath hB,
    holderPath_isBrownian hB, holderPath_ae_eq hB, ?_⟩
  filter_upwards [ae_mem_good hB] with ω hω α hα0 hα T
  have hα' : (α : ℝ) < 1 / 2 := by exact_mod_cast hα
  exact holderOnWith_of_le_subHalf hB hω hα0 hα' T

end CKMA
