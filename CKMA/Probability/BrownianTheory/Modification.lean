/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.BrownianTheory.DyadicLimit
public import CKMA.Probability.BrownianTheory.GaussianMoment
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Continuous Hölder modification of a pre-Brownian process

Dyadic increments of a pre-Brownian process satisfy a summable Markov bound at every exponent
strictly below one half. Borel--Cantelli produces one full-measure set on which every such
exponent is locally Hölder, and the dyadic floors converge to a continuous modification.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Classical Finset Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- Exponent `(k + 1) / (2 (k + 2))`, strictly between `0` and `1 / 2`. -/
def subHalf (k : ℕ) : ℝ := ((k + 1 : ℕ) : ℝ) / (2 * ((k + 2 : ℕ) : ℝ))

/-- Moment order `2 (k + 3)`, paired with `subHalf k`. -/
def momentOrder (k : ℕ) : ℝ := 2 * ((k + 3 : ℕ) : ℝ)

/-- `subHalf k` is positive. -/
lemma subHalf_pos (k : ℕ) : 0 < subHalf k := by
  unfold subHalf
  positivity

/-- `subHalf k` is strictly less than one half. -/
lemma subHalf_lt_half (k : ℕ) : subHalf k < 1 / 2 := by
  have hden : (0 : ℝ) < 2 * ((k + 2 : ℕ) : ℝ) := by positivity
  rw [subHalf, div_lt_iff₀ hden]
  have hleft : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  have hright : (1 / 2) * (2 * ((k + 2 : ℕ) : ℝ)) = (k : ℝ) + 2 := by
    have hcast : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
    rw [hcast]
    ring
  rw [hleft, hright]
  linarith

/-- `momentOrder k` is positive. -/
lemma momentOrder_pos (k : ℕ) : 0 < momentOrder k := by
  unfold momentOrder
  positivity

/-- The Kolmogorov gap `p (1 / 2 - α)` equals `(k + 3) / (k + 2)`. -/
lemma moment_gap (k : ℕ) :
    momentOrder k * (1 / 2 - subHalf k) = ((k + 3 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) := by
  unfold momentOrder subHalf
  push_cast
  field_simp
  ring

/-- Every exponent strictly below one half is bounded by some `subHalf k`. -/
lemma exists_subHalf_ge {α : ℝ} (_hα0 : 0 ≤ α) (hα : α < 1 / 2) :
    ∃ k : ℕ, α ≤ subHalf k := by
  by_cases hquart : α ≤ (1 : ℝ) / 4
  · refine ⟨0, ?_⟩
    have hsub : subHalf 0 = (1 : ℝ) / 4 := by
      unfold subHalf
      norm_num
    rwa [hsub]
  · have hden : (0 : ℝ) < 1 - 2 * α := by linarith
    let k : ℕ := Nat.ceil ((4 * α - 1) / (1 - 2 * α))
    refine ⟨k, ?_⟩
    have hk : (4 * α - 1) / (1 - 2 * α) ≤ (k : ℝ) := Nat.le_ceil _
    have hmul : 4 * α - 1 ≤ (k : ℝ) * (1 - 2 * α) :=
      (div_le_iff₀ hden).1 hk
    have hdiv : (0 : ℝ) < 2 * ((k + 2 : ℕ) : ℝ) := by positivity
    rw [subHalf, le_div_iff₀ hdiv]
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
    rw [hcast, hcast2]
    linarith

/-- Measurable version of one time marginal. -/
def version (hB : IsPreBrownianReal B μ) (t : ℝ≥0) : Ω → ℝ :=
  (hB.aemeasurable t).mk (B t)

/-- The measurable version is measurable. -/
lemma measurable_version (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    Measurable (version hB t) :=
  (hB.aemeasurable t).measurable_mk

/-- The measurable version agrees almost everywhere with the original process. -/
lemma version_ae_eq (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    B t =ᵐ[μ] version hB t :=
  (hB.aemeasurable t).ae_eq_mk

/-- The measurable version is pre-Brownian. -/
lemma version_isPreBrownian (hB : IsPreBrownianReal B μ) :
    IsPreBrownianReal (version hB) μ :=
  IsPreBrownianReal.congr hB (version_ae_eq hB)

/-- Dyadic time `j + i / 2 ^ n`. -/
def dyadicNN (j n i : ℕ) : ℝ≥0 :=
  ⟨(j : ℝ) + (i : ℝ) / 2 ^ n, by positivity⟩

/-- Real value of a dyadic time. -/
lemma coe_dyadicNN (j n i : ℕ) :
    (dyadicNN j n i : ℝ) = (j : ℝ) + (i : ℝ) / 2 ^ n := rfl

/-- Consecutive dyadic times differ by one mesh. -/
lemma dyadicNN_sub (j n i : ℕ) :
    (dyadicNN j n (i + 1) : ℝ) - (dyadicNN j n i : ℝ) = 1 / 2 ^ n := by
  rw [coe_dyadicNN, coe_dyadicNN, Nat.cast_add, Nat.cast_one]
  ring

/-- A dyadic increment is too large for the Hölder scale. -/
def badInc (hB : IsPreBrownianReal B μ) (k j n i : ℕ) : Set Ω :=
  {ω | ((1 : ℝ) / 2 ^ n) ^ subHalf k ≤
    |version hB (dyadicNN j n (i + 1)) ω - version hB (dyadicNN j n i) ω|}

/-- Some dyadic increment of level `n` on the interval starting at `j` is too large. -/
def levelBad (hB : IsPreBrownianReal B μ) (k j n : ℕ) : Set Ω :=
  ⋃ i ∈ range (2 ^ n), badInc hB k j n i

/-- Paths whose dyadic increments are eventually Hölder at every scale and location. -/
def good (hB : IsPreBrownianReal B μ) : Set Ω :=
  {ω | ∀ k j : ℕ, ∀ᶠ n in atTop, ω ∉ levelBad hB k j n}

/-- Each bad increment is measurable. -/
lemma measurableSet_badInc (hB : IsPreBrownianReal B μ) (k j n i : ℕ) :
    MeasurableSet (badInc hB k j n i) := by
  have hmeas : Measurable fun ω =>
      |version hB (dyadicNN j n (i + 1)) ω - version hB (dyadicNN j n i) ω| :=
    ((measurable_version hB _).sub (measurable_version hB _)).norm
  exact measurableSet_Ici.preimage hmeas

/-- A bad level is a finite union of measurable sets. -/
lemma measurableSet_levelBad (hB : IsPreBrownianReal B μ) (k j n : ℕ) :
    MeasurableSet (levelBad hB k j n) := by
  refine Finset.measurableSet_biUnion _ fun i _ => measurableSet_badInc hB k j n i

/-- The good set is measurable. -/
lemma measurableSet_good (hB : IsPreBrownianReal B μ) : MeasurableSet (good hB) := by
  have hlim (k j : ℕ) : MeasurableSet (limsup (levelBad hB k j) atTop) :=
    MeasurableSet.measurableSet_limsup (fun n => measurableSet_levelBad hB k j n)
  have hnot (k j : ℕ) : MeasurableSet {ω | ∀ᶠ n in atTop, ω ∉ levelBad hB k j n} := by
    have hcompl : {ω | ∀ᶠ n in atTop, ω ∉ levelBad hB k j n} =
        (limsup (levelBad hB k j) atTop)ᶜ := by
      ext ω
      simp [mem_limsup_iff_frequently_mem, not_frequently]
    rw [hcompl]
    exact (hlim k j).compl
  have hall : good hB = ⋂ k, ⋂ j, {ω | ∀ᶠ n in atTop, ω ∉ levelBad hB k j n} := by
    ext ω
    simp [good]
  rw [hall]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun j => hnot k j

/-- One bad increment has Markov bound `M` times a negative power of the mesh. -/
lemma measureReal_badInc_le (hB : IsPreBrownianReal B μ) (k j n i : ℕ) :
    μ.real (badInc hB k j n i) ≤
      gaussianAbsMoment (momentOrder k) *
        (2 : ℝ) ^ (-(n : ℝ) * momentOrder k * (1 / 2 - subHalf k)) := by
  set p : ℝ := momentOrder k
  set α : ℝ := subHalf k
  set s : ℝ≥0 := dyadicNN j n (i + 1)
  set t : ℝ≥0 := dyadicNN j n i
  have hp : 0 < p := momentOrder_pos k
  have hbase : (0 : ℝ) < 1 / 2 ^ n := by positivity
  set δ : ℝ := ((1 : ℝ) / 2 ^ n) ^ α with hδdef
  have hδ : 0 < δ := Real.rpow_pos_of_pos hbase _
  have hint : Integrable (fun ω => |version hB s ω - version hB t ω| ^ p) μ := by
    have hg := integrable_abs_rpow_gaussianReal_var hp (nndist (s : ℝ) (t : ℝ))
    simpa [Function.comp_def] using
      ((version_isPreBrownian hB).hasLaw_sub s t).integrable_comp hg
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) p) hint (δ ^ p)
  have hset : {ω | δ ^ p ≤ |version hB s ω - version hB t ω| ^ p} =
      badInc hB k j n i := by
    ext ω
    rw [Set.mem_ofPred_eq, badInc, Set.mem_ofPred_eq]
    dsimp [α, s, t]
    rw [← hδdef]
    exact Real.rpow_le_rpow_iff (le_of_lt hδ) (abs_nonneg _) hp
  have hmark' : δ ^ p * μ.real (badInc hB k j n i) ≤
      ∫ ω, |version hB s ω - version hB t ω| ^ p ∂μ := by
    simpa [hset] using hmark
  have hintle :=
    IsPreBrownianReal.integral_abs_sub_rpow_le (version_isPreBrownian hB) hp s t
  have hdist : |(s : ℝ) - t| = 1 / 2 ^ n := by
    have hsub : (s : ℝ) - t = 1 / 2 ^ n := dyadicNN_sub j n i
    rw [abs_of_pos (hsub.symm ▸ hbase), hsub]
  have hδp : 0 < δ ^ p := Real.rpow_pos_of_pos hδ p
  have hdiv : μ.real (badInc hB k j n i) ≤
      (gaussianAbsMoment p * |(s : ℝ) - t| ^ (p / 2)) / δ ^ p := by
    rw [le_div_iff₀ hδp, mul_comm]
    exact hmark'.trans hintle
  have hexp : p / 2 - α * p = p * (1 / 2 - α) := by ring
  calc
    μ.real (badInc hB k j n i) ≤
        (gaussianAbsMoment p * |(s : ℝ) - t| ^ (p / 2)) / δ ^ p := hdiv
    _ = gaussianAbsMoment p * ((1 / 2 ^ n) ^ (p / 2) / (1 / 2 ^ n) ^ (α * p)) := by
      rw [hdist, hδdef, ← Real.rpow_mul (le_of_lt hbase)]
      ring
    _ = gaussianAbsMoment p * (1 / 2 ^ n) ^ (p / 2 - α * p) := by
      rw [← Real.rpow_sub hbase]
    _ = gaussianAbsMoment p * (1 / 2 ^ n) ^ (p * (1 / 2 - α)) := by rw [hexp]
    _ = gaussianAbsMoment p * (2 : ℝ) ^ (-(n : ℝ) * p * (1 / 2 - α)) := by
      rw [one_div_two_pow_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2)]
      congr 1
      ring

/-- Cancelling the grid cardinality against the Gaussian tail leaves one negative power. -/
lemma two_pow_level_mul (k n : ℕ) :
    (2 : ℝ) ^ n *
        (2 : ℝ) ^ (-(n : ℝ) * (momentOrder k * (1 / 2 - subHalf k))) =
      (2 : ℝ) ^ (-(n : ℝ) / ((k + 2 : ℕ) : ℝ)) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [moment_gap, ← Real.rpow_natCast, ← Real.rpow_add h2]
  have hcast3 : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
  have hcast2 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
  rw [hcast3, hcast2]
  field_simp
  ring

/-- A whole dyadic level has measure at most a summable geometric term. -/
lemma measure_levelBad_le (hB : IsPreBrownianReal B μ) (k j n : ℕ) :
    μ (levelBad hB k j n) ≤
      ENNReal.ofReal (gaussianAbsMoment (momentOrder k) *
        (2 : ℝ) ^ (-(n : ℝ) / ((k + 2 : ℕ) : ℝ))) := by
  set c : ℝ := gaussianAbsMoment (momentOrder k) *
    (2 : ℝ) ^ (-(n : ℝ) * momentOrder k * (1 / 2 - subHalf k))
  have hterm (i : ℕ) (_hi : i ∈ range (2 ^ n)) :
      μ (badInc hB k j n i) ≤ ENNReal.ofReal c := by
    have hreal := measureReal_badInc_le hB k j n i
    have hfin : μ (badInc hB k j n i) ≠ ⊤ := measure_ne_top _ _
    have hle : ENNReal.ofReal (μ.real (badInc hB k j n i)) ≤ ENNReal.ofReal c :=
      ENNReal.ofReal_le_ofReal hreal
    rwa [measureReal_def, ENNReal.ofReal_toReal hfin] at hle
  have hunion := measure_biUnion_finset_le (μ := μ) (range (2 ^ n)) (badInc hB k j n)
  have hsum : ∑ i ∈ range (2 ^ n), μ (badInc hB k j n i) ≤
      ∑ _i ∈ range (2 ^ n), ENNReal.ofReal c :=
    Finset.sum_le_sum hterm
  have hconst : ∑ _i ∈ range (2 ^ n), ENNReal.ofReal c =
      (2 ^ n : ℕ) * ENNReal.ofReal c := by
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmul : (2 ^ n : ℕ) * ENNReal.ofReal c =
      ENNReal.ofReal ((2 : ℝ) ^ n * c) := by
    have hnat : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by norm_cast
    have hnat0 : (0 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by positivity
    calc
      (2 ^ n : ℕ) * ENNReal.ofReal c =
          ENNReal.ofReal ((2 ^ n : ℕ) : ℝ) * ENNReal.ofReal c := by
        rw [ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal (((2 ^ n : ℕ) : ℝ) * c) :=
        (ENNReal.ofReal_mul hnat0).symm
      _ = ENNReal.ofReal ((2 : ℝ) ^ n * c) := by rw [hnat]
  have hpow : (2 : ℝ) ^ n * c =
      gaussianAbsMoment (momentOrder k) *
        (2 : ℝ) ^ (-(n : ℝ) / ((k + 2 : ℕ) : ℝ)) := by
    calc
      (2 : ℝ) ^ n * c = gaussianAbsMoment (momentOrder k) *
          ((2 : ℝ) ^ n * (2 : ℝ) ^
            (-(n : ℝ) * (momentOrder k * (1 / 2 - subHalf k)))) := by
        dsimp [c]
        ring
      _ = gaussianAbsMoment (momentOrder k) *
          (2 : ℝ) ^ (-(n : ℝ) / ((k + 2 : ℕ) : ℝ)) := by
        rw [two_pow_level_mul]
  calc
    μ (levelBad hB k j n) ≤ ∑ i ∈ range (2 ^ n), μ (badInc hB k j n i) := hunion
    _ ≤ ∑ _i ∈ range (2 ^ n), ENNReal.ofReal c := hsum
    _ = (2 ^ n : ℕ) * ENNReal.ofReal c := hconst
    _ = ENNReal.ofReal ((2 : ℝ) ^ n * c) := hmul
    _ = ENNReal.ofReal (gaussianAbsMoment (momentOrder k) *
        (2 : ℝ) ^ (-(n : ℝ) / ((k + 2 : ℕ) : ℝ))) := by rw [hpow]

/-- The geometric level bound is a convergent real series. -/
lemma summable_levelBound (k : ℕ) :
    Summable (fun n : ℕ => gaussianAbsMoment (momentOrder k) *
      (2 : ℝ) ^ (-(n : ℝ) / ((k + 2 : ℕ) : ℝ))) := by
  set r : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / ((k + 2 : ℕ) : ℝ))
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := by
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) ?_
    rw [neg_div]
    exact neg_lt_zero.2 (by positivity)
  have hpow (n : ℕ) : (2 : ℝ) ^ (-(n : ℝ) / ((k + 2 : ℕ) : ℝ)) = r ^ n := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2)]
    congr 1
    field_simp
  have heq : (fun n : ℕ => gaussianAbsMoment (momentOrder k) * r ^ n) =
      fun n : ℕ => gaussianAbsMoment (momentOrder k) *
        (2 : ℝ) ^ (-(n : ℝ) / ((k + 2 : ℕ) : ℝ)) := by
    funext n
    rw [hpow n]
  rw [← heq]
  exact (summable_geometric_of_lt_one hr0 hr1).mul_left _

/-- The measures of the bad levels form a finite series. -/
lemma tsum_levelBad_ne_top (hB : IsPreBrownianReal B μ) (k j : ℕ) :
    ∑' n, μ (levelBad hB k j n) ≠ ⊤ := by
  have hle := ENNReal.tsum_le_tsum (fun n => measure_levelBad_le hB k j n)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n =>
      mul_nonneg (gaussianAbsMoment_nonneg (momentOrder_pos k))
        (Real.rpow_nonneg (by norm_num) _)) (summable_levelBound k)] at hle
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/-- Almost every path has eventually Hölder dyadic increments at every scale. -/
lemma ae_mem_good (hB : IsPreBrownianReal B μ) : ∀ᵐ ω ∂μ, ω ∈ good hB := by
  have hkj : ∀ k j, ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ levelBad hB k j n :=
    fun k j => ae_eventually_notMem (tsum_levelBad_ne_top hB k j)
  have hall : ∀ᵐ ω ∂μ, ∀ k j, ∀ᶠ n in atTop, ω ∉ levelBad hB k j n := by
    rw [ae_all_iff]
    intro k
    rw [ae_all_iff]
    exact hkj k
  simpa [good] using hall

end CKMA
