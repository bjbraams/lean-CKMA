/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.BrownianTheory.HolderPath
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.NNRat.Encodable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Dyadic grid for the reflection principle

Nonnegative rationals are dense, so continuous modifications that agree on them agree at every
time. The reflection argument then uses the uniform mesh `t / 2 ^ n` and the largest consecutive
increment on that mesh.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Classical Finset Filter MeasureTheory Metric ProbabilityTheory Set Topology
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Nonnegative rationals are dense in nonnegative time. -/
lemma denseRange_coe_nnrat : DenseRange (fun q : ℚ≥0 => (q : ℝ≥0)) := by
  intro x
  rw [mem_closure_range_iff]
  intro ε hε
  by_cases hx : x = 0
  · refine ⟨0, ?_⟩
    simpa [hx, dist_self] using hε
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hx
  have hlt : max 0 ((x : ℝ) - ε) < (x : ℝ) := max_lt hx0 (sub_lt_self (x : ℝ) hε)
  obtain ⟨q, hqlo, hqx⟩ := exists_rat_btwn hlt
  have hq0r : (0 : ℝ) ≤ (q : ℝ) :=
    le_trans (le_max_left (0 : ℝ) ((x : ℝ) - ε)) hqlo.le
  have hq0 : 0 ≤ q := by exact_mod_cast hq0r
  refine ⟨q.toNNRat, ?_⟩
  rw [NNReal.dist_eq]
  have hcoe : ((q.toNNRat : ℝ≥0) : ℝ) = (q : ℝ) := by
    change (q.toNNRat : ℝ) = (q : ℝ)
    exact_mod_cast Rat.coe_toNNRat q hq0
  rw [hcoe, abs_of_nonneg (sub_nonneg.2 hqx.le)]
  have hlo : (x : ℝ) - ε < (q : ℝ) :=
    lt_of_le_of_lt (le_max_right (0 : ℝ) ((x : ℝ) - ε)) hqlo
  linarith

/-- Continuous paths that agree almost surely on the nonnegative rationals agree at every time. -/
lemma ae_eq_of_continuous_of_nnrat {B C : ℝ≥0 → Ω → ℝ}
    (hB : ∀ᵐ ω ∂μ, Continuous (fun t => B t ω))
    (hC : ∀ ω, Continuous (fun t => C t ω))
    (hQ : ∀ q : ℚ≥0, C q =ᵐ[μ] B q) :
    ∀ᵐ ω ∂μ, ∀ t, C t ω = B t ω := by
  have hcount : ∀ᵐ ω ∂μ, ∀ q : ℚ≥0, C q ω = B q ω := (ae_all_iff).2 hQ
  filter_upwards [hcount, hB] with ω hω hcontB
  have hfun : (fun t => C t ω) = fun t => B t ω :=
    Continuous.ext_on denseRange_coe_nnrat (hC ω) hcontB <| by
      intro u hu
      rcases hu with ⟨q, rfl⟩
      exact hω q
  intro t
  exact congrFun hfun t

/-- Dyadic time `k * t / 2 ^ n`. -/
def grid (t : ℝ≥0) (n k : ℕ) : ℝ≥0 :=
  ⟨(k : ℝ) * (t : ℝ) / 2 ^ n, by positivity⟩

/-- Real value of a grid time. -/
lemma coe_grid (t : ℝ≥0) (n k : ℕ) : (grid t n k : ℝ) = (k : ℝ) * (t : ℝ) / 2 ^ n := rfl

/-- The first grid time is zero. -/
lemma grid_zero (t : ℝ≥0) (n : ℕ) : grid t n 0 = 0 := by
  apply NNReal.eq
  simp [coe_grid]

/-- Every grid time is zero when the horizon is zero. -/
lemma grid_of_time_zero (n k : ℕ) : grid 0 n k = 0 := by
  apply NNReal.eq
  simp [coe_grid]

/-- The last grid time is the horizon. -/
lemma grid_last (t : ℝ≥0) (n : ℕ) : grid t n (2 ^ n) = t := by
  apply NNReal.eq
  rw [coe_grid, Nat.cast_pow, Nat.cast_ofNat]
  exact mul_div_cancel_left₀ (t : ℝ) (by positivity : (2 : ℝ) ^ n ≠ 0)

/-- Grid times increase with the index. -/
lemma grid_mono {t : ℝ≥0} {n k m : ℕ} (hkm : k ≤ m) : grid t n k ≤ grid t n m := by
  rw [← NNReal.coe_le_coe, coe_grid, coe_grid]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hkm) (NNReal.coe_nonneg t))
    (by positivity)

/-- Grid times up to the last index stay within the horizon. -/
lemma grid_le {t : ℝ≥0} {n k : ℕ} (hk : k ≤ 2 ^ n) : grid t n k ≤ t := by
  calc
    grid t n k ≤ grid t n (2 ^ n) := grid_mono hk
    _ = t := grid_last t n

/-- Consecutive grid times differ by one mesh. -/
lemma grid_sub (t : ℝ≥0) (n k : ℕ) :
    (grid t n (k + 1) : ℝ) - grid t n k = (t : ℝ) / 2 ^ n := by
  rw [coe_grid, coe_grid, Nat.cast_add, Nat.cast_one]
  ring

/-- Mesh of the level-`n` grid. -/
def gridMesh (t : ℝ≥0) (n : ℕ) : ℝ := (t : ℝ) / 2 ^ n

/-- The mesh is nonnegative. -/
lemma gridMesh_nonneg (t : ℝ≥0) (n : ℕ) : 0 ≤ gridMesh t n := by
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
lemma exists_grid_near {t : ℝ≥0} (ht : 0 < t) (n : ℕ) {s : ℝ≥0} (hs : s ≤ t) :
    ∃ k, k ≤ 2 ^ n ∧ |(grid t n k : ℝ) - (s : ℝ)| ≤ gridMesh t n := by
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
    rw [hkpow, grid_last, hst, sub_self, abs_zero]
    exact gridMesh_nonneg t n
  · have hklt : k < 2 ^ n := lt_of_le_of_ne hk hkpow
    have hgrid_le : (grid t n k : ℝ) ≤ s := by
      rw [coe_grid, div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)]
      rw [le_div_iff₀ ht0] at hfloor
      simpa [mul_comm] using hfloor
    have hlt : (s : ℝ) < grid t n (k + 1) := by
      rw [coe_grid, lt_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)]
      have hxlt : (s : ℝ) * (2 : ℝ) ^ n / (t : ℝ) < (k : ℝ) + 1 := by
        simpa [x] using (Nat.lt_floor_add_one x)
      rw [div_lt_iff₀ ht0] at hxlt
      simpa [Nat.cast_add, Nat.cast_one, mul_comm] using hxlt
    refine ⟨k, hklt.le, ?_⟩
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hgrid_le)]
    have hmesh : (s : ℝ) - grid t n k < gridMesh t n := by
      have hsub : (grid t n (k + 1) : ℝ) - grid t n k = gridMesh t n := grid_sub t n k
      linarith
    exact hmesh.le

/-- The level-`n` index range contains `0`. -/
lemma gridRange_nonempty (n : ℕ) : (Finset.range (2 ^ n)).Nonempty :=
  Finset.nonempty_range_iff.mpr (pow_ne_zero n (by decide : (2 : ℕ) ≠ 0))

/-- Largest absolute increment between consecutive grid times. -/
def gridOsc (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (2 ^ n)).sup' (gridRange_nonempty n) fun k =>
    |C (grid t n (k + 1)) ω - C (grid t n k) ω|

/-- Grid oscillation is nonnegative. -/
lemma gridOsc_nonneg (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n : ℕ) (ω : Ω) : 0 ≤ gridOsc C t n ω := by
  rw [gridOsc]
  exact (Finset.le_sup'_iff (gridRange_nonempty n)).2
    ⟨0, Finset.mem_range.mpr (pow_pos (by decide : 0 < 2) n), abs_nonneg _⟩

/-- At time zero every grid increment vanishes. -/
lemma gridOsc_eq_zero_of_time (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ht : t = 0) (n : ℕ) (ω : Ω) :
    gridOsc C t n ω = 0 := by
  rw [gridOsc]
  exact Finset.sup'_eq_of_forall (gridRange_nonempty n)
    (fun k => |C (grid t n (k + 1)) ω - C (grid t n k) ω|)
    (fun k hk => by simp [ht, grid_of_time_zero, sub_self, abs_zero])

/-- Each grid oscillation is measurable. -/
lemma measurable_gridOsc {C : ℝ≥0 → Ω → ℝ} (hm : ∀ u, Measurable (C u)) (t : ℝ≥0) (n : ℕ) :
    Measurable (fun ω => gridOsc C t n ω) := by
  unfold gridOsc
  simp_rw [← Finset.sup'_apply (gridRange_nonempty n)
    (fun k ω => |C (grid t n (k + 1)) ω - C (grid t n k) ω|)]
  exact Finset.measurable_sup' (gridRange_nonempty n) fun k hk =>
    ((hm (grid t n (k + 1))).sub (hm (grid t n k))).norm

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
  have hkI : grid t n k ∈ Icc 0 t := ⟨bot_le, grid_le hklt.le⟩
  have hkI1 : grid t n (k + 1) ∈ Icc 0 t := ⟨bot_le, grid_le (Nat.succ_le_of_lt hklt)⟩
  have hle : dist (grid t n k) (grid t n (k + 1)) ≤ δ := by
    rw [NNReal.dist_eq, abs_sub_comm, grid_sub, abs_of_nonneg (by positivity), ← gridMesh]
    exact hmesh.le
  have hval := hclose _ hkI _ hkI1 hle
  rw [Real.dist_eq, abs_sub_comm] at hval
  exact hval

/-- First grid index at which the path meets level `b`. -/
def isTauSet (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (b : ℝ) (n k : ℕ) : Set Ω :=
  {ω | k ≤ 2 ^ n ∧ b ≤ C (grid t n k) ω ∧ ∀ j, j < k → C (grid t n j) ω < b}

/-- Each first-passage grid event is measurable. -/
lemma measurableSet_isTauSet {C : ℝ≥0 → Ω → ℝ} (hm : ∀ u, Measurable (C u))
    (t : ℝ≥0) (b : ℝ) (n k : ℕ) : MeasurableSet (isTauSet C t b n k) := by
  by_cases hk : k ≤ 2 ^ n
  · have hhit : MeasurableSet {ω | b ≤ C (grid t n k) ω} :=
      measurableSet_Ici.preimage (hm _)
    have hprev : MeasurableSet {ω | ∀ j, j < k → C (grid t n j) ω < b} := by
      have hfin : MeasurableSet (⋂ j ∈ Finset.range k, {ω | C (grid t n j) ω < b}) :=
        MeasurableSet.biInter (Finset.countable_toSet _) fun j hj =>
          measurableSet_Iio.preimage (hm _)
      convert hfin using 1
      ext ω
      simp only [mem_ofPred_eq, mem_iInter, Finset.mem_range]
    have hset : isTauSet C t b n k =
        {ω | b ≤ C (grid t n k) ω} ∩ {ω | ∀ j, j < k → C (grid t n j) ω < b} := by
      ext ω
      simp [isTauSet, hk]
    rw [hset]
    exact hhit.inter hprev
  · have hempty : isTauSet C t b n k = ∅ := by
      ext ω
      simp [isTauSet, hk]
    rw [hempty]
    exact MeasurableSet.empty

/-- Distinct first-passage indices are disjoint. -/
lemma disjoint_isTauSet {C : ℝ≥0 → Ω → ℝ} (t : ℝ≥0) (b : ℝ) (n : ℕ) {k m : ℕ} (hkm : k ≠ m) :
    Disjoint (isTauSet C t b n k) (isTauSet C t b n m) := by
  rw [Set.disjoint_left]
  intro ω hk hm
  rcases lt_or_gt_of_ne hkm with hlt | hlt
  · exact absurd hk.2.1 (not_le_of_gt (hm.2.2 k hlt))
  · exact absurd hm.2.1 (not_le_of_gt (hk.2.2 m hlt))

/-- The first-passage events partition the grid hitting set. -/
lemma iUnion_isTauSet {C : ℝ≥0 → Ω → ℝ} (t : ℝ≥0) (b : ℝ) (n : ℕ) :
    ⋃ k ∈ Finset.range (2 ^ n + 1), isTauSet C t b n k =
      {ω | ∃ k, k ≤ 2 ^ n ∧ b ≤ C (grid t n k) ω} := by
  ext ω
  constructor
  · intro hω
    simp only [mem_iUnion] at hω
    rcases hω with ⟨k, hk, htau⟩
    exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), htau.2.1⟩
  · rintro ⟨k, hk, hhit⟩
    have hex : ∃ j, j ≤ 2 ^ n ∧ b ≤ C (grid t n j) ω := ⟨k, hk, hhit⟩
    let j := Nat.find hex
    have hj := Nat.find_spec hex
    rw [mem_iUnion₂]
    refine ⟨j, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj.1), hj.1, hj.2, ?_⟩
    intro i hi
    exact lt_of_not_ge fun hle => Nat.find_min hex hi ⟨le_trans hi.le hj.1, hle⟩

/-- The grid value at time zero misses a positive level almost surely. -/
lemma measure_isTauSet_zero {C : ℝ≥0 → Ω → ℝ} (hC : IsBrownianReal C μ)
    (t : ℝ≥0) {b : ℝ} (hb : 0 < b) (n : ℕ) : μ (isTauSet C t b n 0) = 0 := by
  have hsub : isTauSet C t b n 0 ⊆ {ω | b ≤ C 0 ω} := by
    intro ω hω
    simpa [grid_zero] using hω.2.1
  refine measure_mono_null hsub ?_
  have hsub' : {ω | b ≤ C 0 ω} ⊆ {ω | C 0 ω ≠ 0} := by
    intro ω hω hzero
    exact (not_le_of_gt hb) (by simpa [hzero] using hω)
  exact measure_mono_null hsub' (ae_iff.mp hC.eval_zero_ae_eq_zero)

/-- The endpoint belongs to the grid hitting set. -/
lemma endpoint_subset_gridHit {C : ℝ≥0 → Ω → ℝ} (t : ℝ≥0) (b : ℝ) (n : ℕ) :
    {ω | b ≤ C t ω} ⊆ {ω | ∃ k, k ≤ 2 ^ n ∧ b ≤ C (grid t n k) ω} := by
  intro ω hω
  exact ⟨2 ^ n, le_rfl, by simpa [grid_last] using hω⟩

/-- A grid hit is a hit of the continuous path on the horizon. -/
lemma gridHit_subset_hit {C : ℝ≥0 → Ω → ℝ} (t : ℝ≥0) (b : ℝ) (n : ℕ) :
    {ω | ∃ k, k ≤ 2 ^ n ∧ b ≤ C (grid t n k) ω} ⊆ {ω | ∃ s, s ≤ t ∧ b ≤ C s ω} := by
  intro ω ⟨k, hk, hω⟩
  exact ⟨grid t n k, grid_le hk, hω⟩

/-- A centered Gaussian at a positive time has no atom. -/
lemma measure_eq_endpoint {C : ℝ≥0 → Ω → ℝ} (hC : IsBrownianReal C μ) {t : ℝ≥0} (ht : 0 < t)
    (b : ℝ) : μ {ω | C t ω = b} = 0 := by
  have hlaw := hC.hasLaw_eval t
  have hnull : NullSingletonClass (gaussianReal (0 : ℝ) t) :=
    nullSingletonClass_gaussianReal (ne_of_gt ht)
  have hp : MeasurableSet {x : ℝ | x = b} := by
    rw [Set.ofPred_eq_eq_singleton]
    exact measurableSet_singleton b
  rw [hlaw.measure_eq hp, Set.ofPred_eq_eq_singleton]
  exact hnull.measure_singleton b

/-- On the first grid hit, a small oscillation keeps the overshoot below `2ε`. -/
lemma overshoot_lt {C : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} {b ε : ℝ} {n k : ℕ} {ω : Ω}
    (hk0 : 1 ≤ k) (hk : k ≤ 2 ^ n) (htau : ω ∈ isTauSet C t b n k)
    (hosc : gridOsc C t n ω ≤ ε) (hend : C t ω ≤ 2 * C (grid t n k) ω - b) :
    C t ω < b + 2 * ε := by
  have hkpos : 0 < k := Nat.succ_le_iff.mp hk0
  have hprevlt : k - 1 < k := Nat.sub_lt hkpos (by decide : 0 < 1)
  have hprev : C (grid t n (k - 1)) ω < b := htau.2.2 (k - 1) hprevlt
  have hmem : k - 1 ∈ Finset.range (2 ^ n) :=
    Finset.mem_range.mpr (lt_of_lt_of_le hprevlt hk)
  have hidx : k - 1 + 1 = k := Nat.sub_add_cancel hk0
  have hinc : |C (grid t n k) ω - C (grid t n (k - 1)) ω| ≤ gridOsc C t n ω := by
    rw [gridOsc]
    have hfun : |C (grid t n k) ω - C (grid t n (k - 1)) ω| =
        |C (grid t n (k - 1 + 1)) ω - C (grid t n (k - 1)) ω| := by rw [hidx]
    rw [hfun]
    exact (Finset.le_sup'_iff (gridRange_nonempty n)).2 ⟨k - 1, hmem, le_rfl⟩
  have hstep : C (grid t n k) ω < b + ε := by
    have habs := le_abs_self (C (grid t n k) ω - C (grid t n (k - 1)) ω)
    have hsum : C (grid t n (k - 1)) ω + gridOsc C t n ω < b + ε :=
      add_lt_add_of_lt_of_le hprev hosc
    linarith
  linarith

end CKMA
