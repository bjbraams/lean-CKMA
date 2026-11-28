/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic

/-!
# Dyadic grid for the reflection principle

The reflection argument uses the uniform mesh `t / 2 ^ n` on `[0, t]` and the largest
consecutive increment on that mesh.

## Main definitions

* `CKMA.Brownian.reflectionGrid`: uniform dyadic grid `t * k / 2 ^ n` on `[0, t]`.
* `CKMA.Brownian.gridOsc`: largest consecutive increment on the dyadic grid of `[0, t]`.
* `CKMA.Brownian.firstGridHitSet`: event that the first grid visit to level `b` occurs at index
  `k`.

## Main results

* `CKMA.Brownian.tendsto_gridOsc`: grid oscillation of a continuous path tends to zero as
  `n → ∞`.
-/

public section

noncomputable section

namespace CKMA

open Finset Filter MeasureTheory Metric ProbabilityTheory Set Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

namespace Brownian

/-- Dyadic time `k * t / 2 ^ n`. -/
@[expose]
def reflectionGrid (t : ℝ≥0) (n k : ℕ) : ℝ≥0 :=
  ⟨(k : ℝ) * (t : ℝ) / 2 ^ n, by positivity⟩

/-- Real value of a grid time, the defining equation of `reflectionGrid`. -/
lemma coe_reflectionGrid (t : ℝ≥0) (n k : ℕ) :
    (reflectionGrid t n k : ℝ) = (k : ℝ) * (t : ℝ) / 2 ^ n := rfl

/-- The first grid time is zero. -/
private lemma reflectionGrid_zero (t : ℝ≥0) (n : ℕ) : reflectionGrid t n 0 = 0 := by
  apply NNReal.eq
  simp [coe_reflectionGrid]

/-- Every grid time is zero when the horizon is zero. -/
private lemma reflectionGrid_of_time_zero (n k : ℕ) : reflectionGrid 0 n k = 0 := by
  apply NNReal.eq
  simp [coe_reflectionGrid]

/-- The last grid time is the horizon. -/
private lemma reflectionGrid_last (t : ℝ≥0) (n : ℕ) : reflectionGrid t n (2 ^ n) = t := by
  apply NNReal.eq
  rw [coe_reflectionGrid, Nat.cast_pow, Nat.cast_ofNat]
  exact mul_div_cancel_left₀ (t : ℝ) (by positivity : (2 : ℝ) ^ n ≠ 0)

/-- Grid times increase with the index. -/
lemma reflectionGrid_mono {t : ℝ≥0} {n k m : ℕ} (hkm : k ≤ m) :
    reflectionGrid t n k ≤ reflectionGrid t n m := by
  rw [← NNReal.coe_le_coe, coe_reflectionGrid, coe_reflectionGrid]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hkm) (NNReal.coe_nonneg t))
    (by positivity)

/-- Grid times up to the last index stay within the horizon. -/
lemma reflectionGrid_le {t : ℝ≥0} {n k : ℕ} (hk : k ≤ 2 ^ n) : reflectionGrid t n k ≤ t := by
  calc
    reflectionGrid t n k ≤ reflectionGrid t n (2 ^ n) := reflectionGrid_mono hk
    _ = t := reflectionGrid_last t n

/-- Consecutive grid times differ by one mesh. -/
private lemma reflectionGrid_sub (t : ℝ≥0) (n k : ℕ) :
    (reflectionGrid t n (k + 1) : ℝ) - reflectionGrid t n k = (t : ℝ) / 2 ^ n := by
  rw [coe_reflectionGrid, coe_reflectionGrid, Nat.cast_add, Nat.cast_one]
  ring

/-- Mesh of the level-`n` grid. -/
@[expose]
def gridMesh (t : ℝ≥0) (n : ℕ) : ℝ := (t : ℝ) / 2 ^ n

/-- Defining equation of `gridMesh`. -/
lemma gridMesh_def (t : ℝ≥0) (n : ℕ) : gridMesh t n = (t : ℝ) / 2 ^ n := rfl

/-- The mesh is nonnegative. -/
private lemma gridMesh_nonneg (t : ℝ≥0) (n : ℕ) : 0 ≤ gridMesh t n := by
  unfold gridMesh
  positivity

/-- The mesh tends to zero. -/
lemma tendsto_gridMesh (t : ℝ≥0) : Tendsto (gridMesh t) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hmul := hpow.const_mul (t : ℝ)
  simp only [mul_zero] at hmul
  refine hmul.congr fun n => ?_
  calc
    (t : ℝ) * ((1 : ℝ) / 2) ^ n = (t : ℝ) * (2 ^ n)⁻¹ := by rw [one_div, inv_pow]
    _ = gridMesh t n := by rw [gridMesh, div_eq_mul_inv]

/-- Every time in the horizon lies within one mesh of some grid time. -/
lemma exists_reflectionGrid_near {t : ℝ≥0} (ht : 0 < t) (n : ℕ) {s : ℝ≥0} (hs : s ≤ t) :
    ∃ k, k ≤ 2 ^ n ∧ |(reflectionGrid t n k : ℝ) - (s : ℝ)| ≤ gridMesh t n := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  set x : ℝ := (s : ℝ) * (2 : ℝ) ^ n / (t : ℝ)
  have hx0 : 0 ≤ x := by positivity
  have hxle : x ≤ (2 ^ n : ℕ) := by
    rw [div_le_iff₀ ht0]
    calc
      (s : ℝ) * (2 : ℝ) ^ n ≤ (t : ℝ) * (2 : ℝ) ^ n := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (by positivity)
      _ = (2 ^ n : ℕ) * (t : ℝ) := by rw [Nat.cast_pow, Nat.cast_ofNat, mul_comm]
  set k := Nat.floor x
  have hk : k ≤ 2 ^ n := Nat.floor_le_of_le hxle
  have hfloor : (k : ℝ) ≤ x := Nat.floor_le hx0
  by_cases hkpow : k = 2 ^ n
  · refine ⟨k, hk, ?_⟩
    have hxeq : x = (2 ^ n : ℕ) := le_antisymm hxle <| by
      simpa [hkpow] using hfloor
    have hsx : (s : ℝ) = t := by
      have hdiv : (s : ℝ) * (2 : ℝ) ^ n / (t : ℝ) = (2 : ℝ) ^ n := by
        simpa [Nat.cast_pow, Nat.cast_ofNat] using hxeq
      have hmul : (s : ℝ) * (2 : ℝ) ^ n = (t : ℝ) * (2 : ℝ) ^ n := by
        rw [div_eq_iff (ne_of_gt ht0)] at hdiv
        simpa [mul_comm] using hdiv
      exact mul_right_cancel₀ (by positivity) hmul
    have hst : s = t := NNReal.eq hsx
    rw [hkpow, reflectionGrid_last, hst, sub_self, abs_zero]
    exact gridMesh_nonneg t n
  · have hklt : k < 2 ^ n := lt_of_le_of_ne hk hkpow
    have hgrid_le : (reflectionGrid t n k : ℝ) ≤ s := by
      rw [coe_reflectionGrid, div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)]
      rw [le_div_iff₀ ht0] at hfloor
      simpa [mul_comm] using hfloor
    have hlt : (s : ℝ) < reflectionGrid t n (k + 1) := by
      rw [coe_reflectionGrid, lt_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)]
      have hxlt : (s : ℝ) * (2 : ℝ) ^ n / (t : ℝ) < (k : ℝ) + 1 := by
        simpa [x] using (Nat.lt_floor_add_one x)
      rw [div_lt_iff₀ ht0] at hxlt
      simpa [Nat.cast_add, Nat.cast_one, mul_comm] using hxlt
    refine ⟨k, hklt.le, ?_⟩
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hgrid_le)]
    have hmesh : (s : ℝ) - reflectionGrid t n k < gridMesh t n := by
      have hsub : (reflectionGrid t n (k + 1) : ℝ) - reflectionGrid t n k = gridMesh t n :=
        reflectionGrid_sub t n k
      linarith
    exact hmesh.le

/-- The level-`n` index range contains `0`. -/
lemma gridRange_nonempty (n : ℕ) : (Finset.range (2 ^ n)).Nonempty :=
  Finset.nonempty_range_iff.mpr (pow_ne_zero n (by decide : (2 : ℕ) ≠ 0))

/-- Largest absolute increment between consecutive grid times. -/
@[expose]
def gridOsc (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (2 ^ n)).sup' (gridRange_nonempty n) fun k =>
    |C (reflectionGrid t n (k + 1)) ω - C (reflectionGrid t n k) ω|

omit [MeasurableSpace Ω] in
/-- Defining equation of `gridOsc`. -/
lemma gridOsc_def (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n : ℕ) (ω : Ω) :
    gridOsc C t n ω = (Finset.range (2 ^ n)).sup' (gridRange_nonempty n) fun k =>
      |C (reflectionGrid t n (k + 1)) ω - C (reflectionGrid t n k) ω| := rfl

omit [MeasurableSpace Ω] in
/-- Grid oscillation is nonnegative. -/
lemma gridOsc_nonneg (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n : ℕ) (ω : Ω) : 0 ≤ gridOsc C t n ω := by
  rw [gridOsc]
  exact (Finset.le_sup'_iff (gridRange_nonempty n)).2
    ⟨0, Finset.mem_range.mpr (pow_pos (by decide : 0 < 2) n), abs_nonneg _⟩

omit [MeasurableSpace Ω] in
/-- At time zero every grid increment vanishes. -/
private lemma gridOsc_eq_zero_of_time (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ht : t = 0) (n : ℕ) (ω : Ω) :
    gridOsc C t n ω = 0 := by
  rw [gridOsc]
  exact Finset.sup'_eq_of_forall (gridRange_nonempty n)
    (fun k => |C (reflectionGrid t n (k + 1)) ω - C (reflectionGrid t n k) ω|)
    (fun k hk => by simp [ht, reflectionGrid_of_time_zero, sub_self, abs_zero])

/-- Each grid oscillation is measurable. -/
lemma measurable_gridOsc {C : ℝ≥0 → Ω → ℝ} (hm : ∀ u, Measurable (C u)) (t : ℝ≥0) (n : ℕ) :
    Measurable (fun ω => gridOsc C t n ω) := by
  unfold gridOsc
  simp_rw [← Finset.sup'_apply (gridRange_nonempty n)
    (fun k ω => |C (reflectionGrid t n (k + 1)) ω - C (reflectionGrid t n k) ω|)]
  exact Finset.measurable_sup' (gridRange_nonempty n) fun k hk =>
    ((hm (reflectionGrid t n (k + 1))).sub (hm (reflectionGrid t n k))).norm

omit [MeasurableSpace Ω] in
/-- Grid oscillation of a continuous path tends to zero. -/
lemma tendsto_gridOsc {C : ℝ≥0 → Ω → ℝ} (hcont : ∀ ω, Continuous (fun u => C u ω))
    (t : ℝ≥0) (ω : Ω) : Tendsto (fun n => gridOsc C t n ω) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_cases ht : t = 0
  · refine ⟨0, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (gridOsc_nonneg C t n ω),
      gridOsc_eq_zero_of_time C t ht n ω]
    exact hε
  have huc := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).uniformContinuousOn_of_continuous
    (hcont ω).continuousOn
  rw [uniformContinuousOn_iff_le] at huc
  obtain ⟨δ, hδ, hclose⟩ := huc (ε / 2) (half_pos hε)
  have hnhds : Iio δ ∈ 𝓝 (0 : ℝ) := by
    rw [Metric.mem_nhds_iff]
    refine ⟨δ, hδ, ?_⟩
    intro y hy
    rw [mem_ball, Real.dist_eq] at hy
    have hy' : y - 0 < δ := (abs_lt.mp hy).2
    simpa [sub_zero] using hy'
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_gridMesh t).eventually hnhds)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (gridOsc_nonneg C t n ω)]
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  rw [gridOsc]
  refine Finset.sup'_le (gridRange_nonempty n) _ fun k hk => ?_
  have hmesh : gridMesh t n < δ := hN n hn
  have hklt : k < 2 ^ n := Finset.mem_range.mp hk
  have hkI : reflectionGrid t n k ∈ Icc 0 t := ⟨bot_le, reflectionGrid_le hklt.le⟩
  have hkI1 : reflectionGrid t n (k + 1) ∈ Icc 0 t :=
    ⟨bot_le, reflectionGrid_le (Nat.succ_le_of_lt hklt)⟩
  have hle : dist (reflectionGrid t n k) (reflectionGrid t n (k + 1)) ≤ δ := by
    rw [NNReal.dist_eq, abs_sub_comm, reflectionGrid_sub, abs_of_nonneg (by positivity), ← gridMesh]
    exact hmesh.le
  have hval := hclose _ hkI _ hkI1 hle
  rw [Real.dist_eq, abs_sub_comm] at hval
  exact hval

/-- Paths whose first visit to level `b` on the dyadic grid of `[0, t]` occurs at index `k`. -/
@[expose]
def firstGridHitSet (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (b : ℝ) (n k : ℕ) : Set Ω :=
  {ω | k ≤ 2 ^ n ∧ b ≤ C (reflectionGrid t n k) ω ∧ ∀ j, j < k → C (reflectionGrid t n j) ω < b}

omit [MeasurableSpace Ω] in
/-- Membership in `firstGridHitSet`. -/
lemma mem_firstGridHitSet_iff {C : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} {b : ℝ} {n k : ℕ} {ω : Ω} :
    ω ∈ firstGridHitSet C t b n k ↔ k ≤ 2 ^ n ∧ b ≤ C (reflectionGrid t n k) ω ∧
      ∀ j, j < k → C (reflectionGrid t n j) ω < b := Iff.rfl

/-- Each first-passage grid event is measurable. -/
lemma measurableSet_firstGridHitSet {C : ℝ≥0 → Ω → ℝ} (hm : ∀ u, Measurable (C u))
    (t : ℝ≥0) (b : ℝ) (n k : ℕ) : MeasurableSet (firstGridHitSet C t b n k) := by
  by_cases hk : k ≤ 2 ^ n
  · have hhit : MeasurableSet {ω | b ≤ C (reflectionGrid t n k) ω} :=
      measurableSet_Ici.preimage (hm _)
    have hprev : MeasurableSet {ω | ∀ j, j < k → C (reflectionGrid t n j) ω < b} := by
      have hfin : MeasurableSet (⋂ j ∈ Finset.range k, {ω | C (reflectionGrid t n j) ω < b}) :=
        MeasurableSet.biInter (Set.to_countable _) fun j hj =>
          measurableSet_Iio.preimage (hm _)
      convert hfin using 1
      ext ω
      simp only [mem_ofPred_eq, mem_iInter, Finset.mem_range]
    have hset : firstGridHitSet C t b n k =
        {ω | b ≤ C (reflectionGrid t n k) ω} ∩
          {ω | ∀ j, j < k → C (reflectionGrid t n j) ω < b} := by
      ext ω
      simp [firstGridHitSet, hk]
    rw [hset]
    exact hhit.inter hprev
  · have hempty : firstGridHitSet C t b n k = ∅ := by
      ext ω
      simp [firstGridHitSet, hk]
    rw [hempty]
    exact MeasurableSet.empty

omit [MeasurableSpace Ω] in
/-- Distinct first-passage indices are disjoint. -/
lemma disjoint_firstGridHitSet {C : ℝ≥0 → Ω → ℝ} (t : ℝ≥0) (b : ℝ) (n : ℕ) {k m : ℕ} (hkm : k ≠ m) :
    Disjoint (firstGridHitSet C t b n k) (firstGridHitSet C t b n m) := by
  rw [Set.disjoint_left]
  intro ω hk hm
  rcases lt_or_gt_of_ne hkm with hlt | hlt
  · exact absurd hk.2.1 (not_le_of_gt (hm.2.2 k hlt))
  · exact absurd hm.2.1 (not_le_of_gt (hk.2.2 m hlt))

omit [MeasurableSpace Ω] in
/-- The first-passage events partition the grid hitting set. -/
lemma iUnion_firstGridHitSet {C : ℝ≥0 → Ω → ℝ} (t : ℝ≥0) (b : ℝ) (n : ℕ) :
    ⋃ k ∈ Finset.range (2 ^ n + 1), firstGridHitSet C t b n k =
      {ω | ∃ k, k ≤ 2 ^ n ∧ b ≤ C (reflectionGrid t n k) ω} := by
  ext ω
  constructor
  · intro hω
    simp only [mem_iUnion] at hω
    rcases hω with ⟨k, hk, htau⟩
    exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), htau.2.1⟩
  · rintro ⟨k, hk, hhit⟩
    have hex : ∃ j, j ≤ 2 ^ n ∧ b ≤ C (reflectionGrid t n j) ω := ⟨k, hk, hhit⟩
    let j := Nat.find hex
    have hj := Nat.find_spec hex
    rw [mem_iUnion₂]
    refine ⟨j, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj.1), hj.1, hj.2, ?_⟩
    intro i hi
    exact lt_of_not_ge fun hle => Nat.find_min hex hi ⟨le_trans hi.le hj.1, hle⟩

omit [IsProbabilityMeasure μ] in
/-- The grid value at time zero misses a positive level almost surely. -/
lemma measure_firstGridHitSet_zero {C : ℝ≥0 → Ω → ℝ} (hC : IsBrownianReal C μ)
    (t : ℝ≥0) {b : ℝ} (hb : 0 < b) (n : ℕ) : μ (firstGridHitSet C t b n 0) = 0 := by
  have hsub : firstGridHitSet C t b n 0 ⊆ {ω | b ≤ C 0 ω} := by
    intro ω hω
    simpa [reflectionGrid_zero] using hω.2.1
  refine measure_mono_null hsub ?_
  have hsub' : {ω | b ≤ C 0 ω} ⊆ {ω | C 0 ω ≠ 0} := by
    intro ω hω hzero
    exact (not_le_of_gt hb) (by simpa [hzero] using hω)
  exact measure_mono_null hsub' (ae_iff.mp hC.eval_zero_ae_eq_zero)

omit [MeasurableSpace Ω] in
/-- The endpoint belongs to the grid hitting set. -/
lemma endpoint_subset_gridHit {C : ℝ≥0 → Ω → ℝ} (t : ℝ≥0) (b : ℝ) (n : ℕ) :
    {ω | b ≤ C t ω} ⊆ {ω | ∃ k, k ≤ 2 ^ n ∧ b ≤ C (reflectionGrid t n k) ω} := by
  intro ω hω
  exact ⟨2 ^ n, le_rfl, by simpa [reflectionGrid_last] using hω⟩

omit [MeasurableSpace Ω] in
/-- A grid hit is a hit of the continuous path on the horizon. -/
lemma gridHit_subset_hit {C : ℝ≥0 → Ω → ℝ} (t : ℝ≥0) (b : ℝ) (n : ℕ) :
    {ω | ∃ k, k ≤ 2 ^ n ∧ b ≤ C (reflectionGrid t n k) ω} ⊆ {ω | ∃ s, s ≤ t ∧ b ≤ C s ω} := by
  intro ω ⟨k, hk, hω⟩
  exact ⟨reflectionGrid t n k, reflectionGrid_le hk, hω⟩

omit [IsProbabilityMeasure μ] in
/-- A centered Gaussian at a positive time has no atom. -/
lemma measure_setOf_eval_eq_eq_zero {C : ℝ≥0 → Ω → ℝ} (hC : IsBrownianReal C μ) {t : ℝ≥0}
    (ht : 0 < t) (b : ℝ) : μ {ω | C t ω = b} = 0 := by
  have hlaw := hC.hasLaw_eval t
  have hnull : NullSingletonClass (gaussianReal (0 : ℝ) t) :=
    nullSingletonClass_gaussianReal (ne_of_gt ht)
  have hp : MeasurableSet {x : ℝ | x = b} := by
    rw [Set.ofPred_eq_eq_singleton]
    exact measurableSet_singleton b
  rw [hlaw.measure_eq hp, Set.ofPred_eq_eq_singleton]
  exact hnull.measure_singleton b

omit [MeasurableSpace Ω] in
/-- On the first grid hit, a small oscillation keeps the overshoot below `2ε`. -/
lemma overshoot_lt {C : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} {b ε : ℝ} {n k : ℕ} {ω : Ω}
    (hk0 : 1 ≤ k) (hk : k ≤ 2 ^ n) (htau : ω ∈ firstGridHitSet C t b n k)
    (hosc : gridOsc C t n ω ≤ ε) (hend : C t ω ≤ 2 * C (reflectionGrid t n k) ω - b) :
    C t ω < b + 2 * ε := by
  have hkpos : 0 < k := Nat.succ_le_iff.mp hk0
  have hprevlt : k - 1 < k := Nat.sub_lt hkpos (by decide : 0 < 1)
  have hprev : C (reflectionGrid t n (k - 1)) ω < b := htau.2.2 (k - 1) hprevlt
  have hmem : k - 1 ∈ Finset.range (2 ^ n) :=
    Finset.mem_range.mpr (lt_of_lt_of_le hprevlt hk)
  have hidx : k - 1 + 1 = k := Nat.sub_add_cancel hk0
  have hinc :
      |C (reflectionGrid t n k) ω - C (reflectionGrid t n (k - 1)) ω| ≤ gridOsc C t n ω := by
    rw [gridOsc]
    have hfun : |C (reflectionGrid t n k) ω - C (reflectionGrid t n (k - 1)) ω| =
        |C (reflectionGrid t n (k - 1 + 1)) ω - C (reflectionGrid t n (k - 1)) ω| := by rw [hidx]
    rw [hfun]
    exact (Finset.le_sup'_iff (gridRange_nonempty n)).2 ⟨k - 1, hmem, le_rfl⟩
  have hstep : C (reflectionGrid t n k) ω < b + ε := by
    have habs := le_abs_self (C (reflectionGrid t n k) ω - C (reflectionGrid t n (k - 1)) ω)
    have hsum : C (reflectionGrid t n (k - 1)) ω + gridOsc C t n ω < b + ε :=
      add_lt_add_of_lt_of_le hprev hosc
    linarith
  linarith

end Brownian

end CKMA
