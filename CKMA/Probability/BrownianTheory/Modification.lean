/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import TauCeti.Probability.Process.Kolmogorov
import TauCeti.Probability.Process.Kolmogorov.Edges

/-!
# Dyadic Hölder bounds for a pre-Brownian process

The measurable version of a pre-Brownian process satisfies the even-moment Kolmogorov condition
with exponents `2 m` and `m`. TauCeti's Kolmogorov edge estimate then gives, almost surely, one
random constant bounding all dyadic increments of an integer interval at every exponent
`subHalf k` below one half, and convergence of the process along any sequence of times that
approaches a fixed time geometrically fast. These are the probabilistic inputs to the dyadic
construction of the continuous modification in `BrownianTheory.HolderPath`.

The Kolmogorov condition for Gaussian increments is TauCeti's
`ProbabilityTheory.isKolmogorovProcess_of_hasLaw_sub_gaussianReal`
(`TauCeti.Probability.Process.Kolmogorov`), and the almost sure edge bound is TauCeti's
`ProbabilityTheory.IsAEKolmogorovProcess.ae_exists_edist_le_mul_pow_rpow`
(`TauCeti.Probability.Process.Kolmogorov.Edges`), built on Mathlib's `IsKolmogorovProcess`.

## Main definitions

* `CKMA.Brownian.subHalf`: exponent `(k + 1) / (2 (k + 2))` strictly between `0` and `1 / 2`.
* `CKMA.Brownian.preBrownianVersion`: measurable version of one time marginal of a pre-Brownian
  process.
* `CKMA.Brownian.dyadicPoint`: the dyadic time `j + i / 2 ^ n`.
* `CKMA.Brownian.holderGoodSet`: the paths whose dyadic increments on each integer interval are
  bounded, for every `k`, by a constant times the mesh to the power `subHalf k`.

## Main results

* `CKMA.Brownian.exists_subHalf_ge`: every exponent strictly below `1 / 2` is bounded by some
  `subHalf k`.
* `CKMA.Brownian.isKolmogorovProcess_preBrownianVersion`: the even-moment Kolmogorov condition.
* `CKMA.Brownian.ae_tendsto_preBrownianVersion`: almost sure convergence along times within
  `2 ^ (-n)` of a fixed time.
* `CKMA.Brownian.ae_mem_holderGoodSet`: almost every sample path belongs to `holderGoodSet`.
-/

public section

noncomputable section

namespace CKMA

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology Nat

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

namespace Brownian

/-- Exponent `(k + 1) / (2 (k + 2))`, strictly between `0` and `1 / 2`. -/
@[expose]
def subHalf (k : ℕ) : ℝ := ((k + 1 : ℕ) : ℝ) / (2 * ((k + 2 : ℕ) : ℝ))

/-- Defining equation of `subHalf`. -/
theorem subHalf_def (k : ℕ) : subHalf k = ((k + 1 : ℕ) : ℝ) / (2 * ((k + 2 : ℕ) : ℝ)) := rfl

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

/-- Every exponent strictly below one half is bounded by some `subHalf k`. -/
lemma exists_subHalf_ge {α : ℝ} (hα : α < 1 / 2) :
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
@[expose]
def preBrownianVersion (hB : IsPreBrownianReal B μ) (t : ℝ≥0) : Ω → ℝ :=
  (hB.aemeasurable t).mk (B t)

/-- Defining equation of `preBrownianVersion`. -/
theorem preBrownianVersion_def (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    preBrownianVersion hB t = (hB.aemeasurable t).mk (B t) := rfl

/-- The measurable version is measurable. -/
lemma measurable_preBrownianVersion (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    Measurable (preBrownianVersion hB t) :=
  (hB.aemeasurable t).measurable_mk

/-- The measurable version agrees almost everywhere with the original process. -/
lemma preBrownianVersion_ae_eq (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    B t =ᵐ[μ] preBrownianVersion hB t :=
  (hB.aemeasurable t).ae_eq_mk

/-- The measurable version is pre-Brownian. -/
lemma preBrownianVersion_isPreBrownian (hB : IsPreBrownianReal B μ) :
    IsPreBrownianReal (preBrownianVersion hB) μ :=
  IsPreBrownianReal.congr hB (preBrownianVersion_ae_eq hB)

/-- Dyadic time `j + i / 2 ^ n`. -/
@[expose]
def dyadicPoint (j n i : ℕ) : ℝ≥0 :=
  ⟨(j : ℝ) + (i : ℝ) / 2 ^ n, by positivity⟩

/-- Real value of a dyadic time. -/
lemma coe_dyadicPoint (j n i : ℕ) :
    (dyadicPoint j n i : ℝ) = (j : ℝ) + (i : ℝ) / 2 ^ n := rfl

/-- Consecutive dyadic times differ by one mesh. -/
private lemma dyadicPoint_sub (j n i : ℕ) :
    (dyadicPoint j n (i + 1) : ℝ) - (dyadicPoint j n i : ℝ) = 1 / 2 ^ n := by
  rw [coe_dyadicPoint, coe_dyadicPoint, Nat.cast_add, Nat.cast_one]
  ring

/-- The measurable version satisfies the even-moment Kolmogorov condition with exponents `2 m`
and `m` and constant `(2 m - 1)‼`, for every positive `m`. -/
theorem isKolmogorovProcess_preBrownianVersion (hB : IsPreBrownianReal B μ) {m : ℕ}
    (hm : m ≠ 0) :
    IsKolmogorovProcess (preBrownianVersion hB) μ (2 * m : ℕ) m (2 * m - 1)‼ :=
  isKolmogorovProcess_of_hasLaw_sub_gaussianReal (measurable_preBrownianVersion hB)
    (preBrownianVersion_isPreBrownian hB).hasLaw_sub hm

/-- Edges of length at most `2 ^ (-n)` at level `n`, at most `2 ^ (d n)` of them, have increments
bounded almost surely by one random constant times `2 ^ (-n γ)`, provided `d + 2 m γ < m`. -/
private lemma ae_exists_abs_sub_le (hB : IsPreBrownianReal B μ) {m : ℕ} (hm : m ≠ 0)
    {d γ : ℝ} (hγ₀ : 0 ≤ γ) (hγ : d + (2 * m : ℕ) * γ < m) {c : ℕ → ℕ}
    (hc : ∀ n, (c n : ℝ) ≤ (2 : ℝ) ^ (d * n)) {s t : (n : ℕ) → Fin (c n) → ℝ≥0}
    (hst : ∀ n i, |(s n i : ℝ) - t n i| ≤ 1 / 2 ^ n) :
    ∀ᵐ ω ∂μ, ∃ K : ℕ, ∀ n i, |preBrownianVersion hB (s n i) ω -
      preBrownianVersion hB (t n i) ω| ≤ K * ((1 : ℝ) / 2 ^ n) ^ γ := by
  have hr : (0 : ℝ≥0) < 1 / 2 := by norm_num
  have hr₁ : (1 / 2 : ℝ≥0) < 1 := by norm_num
  have hcard (n : ℕ) : (c n : ℝ≥0) ≤ 1 * ((1 / 2 : ℝ≥0) ^ (-d)) ^ n := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [one_mul, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), one_div,
      Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_mul, neg_neg]
    exact hc n
  have hedge (n : ℕ) (i : Fin (c n)) :
      edist (s n i) (t n i) ≤ ((1 / 2 : ℝ≥0) : ℝ≥0∞) ^ n := by
    rw [edist_dist, NNReal.dist_eq, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow
      (by positivity)]
    refine ENNReal.ofReal_le_ofReal ((hst n i).trans_eq ?_)
    rw [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, one_div_pow]
  filter_upwards [(isKolmogorovProcess_preBrownianVersion hB hm).IsAEKolmogorovProcess
    |>.ae_exists_edist_le_mul_pow_rpow hr hr₁ hcard hedge hγ] with ω ⟨K, hK⟩
  refine ⟨⌈K⌉₊, fun n i ↦ ?_⟩
  have hb : (0 : ℝ) ≤ ((1 : ℝ) / 2 ^ n) ^ γ := by positivity
  have h := hK n i
  rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity) hγ₀,
    ← ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  push_cast at h
  rw [one_div_pow] at h
  exact h.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) hb)

/-- The exponent pair of the Kolmogorov condition of order `2 (k + 3)` reaches `subHalf k` with
one dyadic dimension to spare: `1 + 2 (k + 3) subHalf k < k + 3`. -/
private lemma one_add_mul_subHalf_lt (k : ℕ) :
    1 + ((2 * (k + 3) : ℕ) : ℝ) * subHalf k < ((k + 3 : ℕ) : ℝ) := by
  have h : ((2 * (k + 3) : ℕ) : ℝ) * subHalf k = ((k + 3) * (k + 1)) / (k + 2) := by
    rw [subHalf]
    push_cast
    field_simp
  rw [h, ← sub_pos]
  have hk : (0 : ℝ) < k + 2 := by positivity
  have he : ((k + 3 : ℕ) : ℝ) - (1 + ((k + 3) * (k + 1)) / (k + 2)) = 1 / (k + 2) := by
    push_cast
    field_simp
    ring
  rw [he]
  positivity

/-- If `u n` lies within `2 ^ (-n)` of `t`, then almost surely the measurable version at `u n`
converges to its value at `t`. -/
lemma ae_tendsto_preBrownianVersion (hB : IsPreBrownianReal B μ) {u : ℕ → ℝ≥0} {t : ℝ≥0}
    (hu : ∀ n, |(u n : ℝ) - t| ≤ 1 / 2 ^ n) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ preBrownianVersion hB (u n) ω) atTop
      (𝓝 (preBrownianVersion hB t ω)) := by
  have hγ : (0 : ℝ) + ((2 * 1 : ℕ) : ℝ) * (1 / 4) < ((1 : ℕ) : ℝ) := by norm_num
  filter_upwards [ae_exists_abs_sub_le hB one_ne_zero (by norm_num) hγ (c := fun _ ↦ 1)
    (fun n ↦ by simp) (s := fun n _ ↦ u n) (t := fun _ _ ↦ t) (fun n _ ↦ hu n)] with ω ⟨K, hK⟩
  have hlim : Tendsto (fun n : ℕ ↦ (K : ℝ) * ((1 : ℝ) / 2 ^ n) ^ (1 / 4 : ℝ)) atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 4))).const_mul (K : ℝ)
    simpa [one_div_pow] using h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ hK n 0) hlim

/-- Paths whose dyadic increments on each integer interval are bounded, for every `k`, by a
constant times the mesh to the power `subHalf k`. -/
@[expose]
def holderGoodSet (hB : IsPreBrownianReal B μ) : Set Ω :=
  {ω | ∀ k j : ℕ, ∃ K : ℕ, ∀ n i : ℕ, i < 2 ^ n →
    |preBrownianVersion hB (dyadicPoint j n (i + 1)) ω -
      preBrownianVersion hB (dyadicPoint j n i) ω| ≤ K * ((1 : ℝ) / 2 ^ n) ^ subHalf k}

/-- Membership in `holderGoodSet`. -/
theorem mem_holderGoodSet_iff (hB : IsPreBrownianReal B μ) (ω : Ω) :
    ω ∈ holderGoodSet hB ↔ ∀ k j : ℕ, ∃ K : ℕ, ∀ n i : ℕ, i < 2 ^ n →
      |preBrownianVersion hB (dyadicPoint j n (i + 1)) ω -
        preBrownianVersion hB (dyadicPoint j n i) ω| ≤ K * ((1 : ℝ) / 2 ^ n) ^ subHalf k :=
  Iff.rfl

/-- The good set is measurable. -/
lemma measurableSet_holderGoodSet (hB : IsPreBrownianReal B μ) :
    MeasurableSet (holderGoodSet hB) := by
  refine measurableSet_setOfPred.2 <| .forall fun k ↦ .forall fun j ↦ .exists fun K ↦
    .forall fun n ↦ .forall fun i ↦ .imp measurable_const <| measurableSet_setOfPred.1 <|
      measurableSet_le ?_ measurable_const
  exact ((measurable_preBrownianVersion hB _).sub (measurable_preBrownianVersion hB _)).norm

/-- Almost every path belongs to `holderGoodSet`. -/
lemma ae_mem_holderGoodSet (hB : IsPreBrownianReal B μ) : ∀ᵐ ω ∂μ, ω ∈ holderGoodSet hB := by
  have hkj (k j : ℕ) : ∀ᵐ ω ∂μ, ∃ K : ℕ, ∀ n i : ℕ, i < 2 ^ n →
      |preBrownianVersion hB (dyadicPoint j n (i + 1)) ω -
        preBrownianVersion hB (dyadicPoint j n i) ω| ≤ K * ((1 : ℝ) / 2 ^ n) ^ subHalf k := by
    filter_upwards [ae_exists_abs_sub_le hB (m := k + 3) (by omega) (subHalf_pos k).le
      (one_add_mul_subHalf_lt k) (c := fun n ↦ 2 ^ n) (fun n ↦ by simp)
      (s := fun n i ↦ dyadicPoint j n (i + 1)) (t := fun n i ↦ dyadicPoint j n i)
      (fun n i ↦ by rw [dyadicPoint_sub, abs_of_pos (by positivity)])] with ω ⟨K, hK⟩
    exact ⟨K, fun n i hi ↦ hK n ⟨i, hi⟩⟩
  simp only [mem_holderGoodSet_iff, ae_all_iff]
  exact hkj

end Brownian

end CKMA
