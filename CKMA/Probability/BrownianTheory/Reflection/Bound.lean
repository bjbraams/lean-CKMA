/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.BrownianTheory.Reflection.Past
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Order.OrderClosed

/-!
# Reflection estimates on the dyadic grid

An up-crossing of a positive level is compared with the endpoint by reflecting the first grid
passage. Sending the mesh and the gap above the level to zero removes the overshoot.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Finset MeasureTheory Metric ProbabilityTheory Set Topology
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A finite constant lying under `a + o n` for a null sequence stays under `a`. -/
lemma le_of_forall_le_add_tendsto_zero {c a : ℝ≥0∞} {o : ℕ → ℝ≥0∞} (hc : c ≠ ∞) (ha : a ≠ ∞)
    (ho : ∀ n, o n ≠ ∞) (hle : ∀ n, c ≤ a + o n) (htend : Tendsto o atTop (𝓝 0)) : c ≤ a := by
  have hleR : ∀ n, c.toReal ≤ a.toReal + (o n).toReal := by
    intro n
    have hsum : a + o n ≠ ∞ := ENNReal.add_ne_top.2 ⟨ha, ho n⟩
    rw [← ENNReal.toReal_add ha (ho n)]
    exact (ENNReal.toReal_le_toReal hc hsum).2 (hle n)
  have htendR : Tendsto (fun n => a.toReal + (o n).toReal) atTop (𝓝 a.toReal) := by
    have hoR : Tendsto (fun n => (o n).toReal) atTop (𝓝 0) :=
      (ENNReal.tendsto_toReal_zero_iff ho).2 htend
    simpa [add_zero] using tendsto_const_nhds.add hoR
  have hreal : c.toReal ≤ a.toReal := ge_of_tendsto' htendR hleR
  exact (ENNReal.toReal_le_toReal hc ha).1 hreal

/-- Paths that meet level `b` on the level-`n` grid. -/
def gridHit (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (b : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∃ k, k ≤ 2 ^ n ∧ b ≤ C (grid t n k) ω}

/-- The grid hitting set is the disjoint union of the first-passage events. -/
lemma gridHit_eq_iUnion (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (b : ℝ) (n : ℕ) :
    gridHit C t b n = ⋃ k ∈ Finset.range (2 ^ n + 1), isTauSet C t b n k := by
  simpa [gridHit] using (iUnion_isTauSet (C := C) t b n).symm

/-- Grid hitting sets are measurable. -/
lemma measurableSet_gridHit {C : ℝ≥0 → Ω → ℝ} (hm : ∀ u, Measurable (C u)) (t : ℝ≥0) (b : ℝ)
    (n : ℕ) : MeasurableSet (gridHit C t b n) := by
  rw [gridHit_eq_iUnion]
  exact MeasurableSet.biUnion (Finset.countable_toSet _) fun k _ =>
    measurableSet_isTauSet hm t b n k

/-- Paths that meet level `b` at some time up to the horizon. -/
def hitSet (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (b : ℝ) : Set Ω :=
  {ω | ∃ s : ℝ≥0, s ≤ t ∧ b ≤ C s ω}

/-- Paths that strictly exceed level `b` by the horizon. -/
def strictHit (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (b : ℝ) : Set Ω :=
  {ω | ∃ s : ℝ≥0, s ≤ t ∧ b < C s ω}

/-- The endpoint lies at or above the level. -/
def endpointSet (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (b : ℝ) : Set Ω :=
  {ω | b ≤ C t ω}

/-- The endpoint lies strictly below the level. -/
def belowSet (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (b : ℝ) : Set Ω :=
  {ω | C t ω < b}

/-- The endpoint lies in the half-open band `[b, b + 2ε)`. -/
def bandSet (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (b ε : ℝ) : Set Ω :=
  {ω | b ≤ C t ω ∧ C t ω < b + 2 * ε}

/-- Grid oscillation exceeds `ε`. -/
def oscSet (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ε : ℝ) (n : ℕ) : Set Ω :=
  {ω | ε < gridOsc C t n ω}

/-- The endpoint superlevel is measurable. -/
lemma measurableSet_endpoint {C : ℝ≥0 → Ω → ℝ} (hm : ∀ u, Measurable (C u)) (t : ℝ≥0) (b : ℝ) :
    MeasurableSet (endpointSet C t b) := by
  rw [endpointSet]
  exact measurableSet_Ici.preimage (hm t)

/-- The strict endpoint sublevel is measurable. -/
lemma measurableSet_below {C : ℝ≥0 → Ω → ℝ} (hm : ∀ u, Measurable (C u)) (t : ℝ≥0) (b : ℝ) :
    MeasurableSet (belowSet C t b) := by
  rw [belowSet]
  exact measurableSet_Iio.preimage (hm t)

/-- The endpoint band is measurable. -/
lemma measurableSet_band {C : ℝ≥0 → Ω → ℝ} (hm : ∀ u, Measurable (C u)) (t : ℝ≥0) (b ε : ℝ) :
    MeasurableSet (bandSet C t b ε) := by
  have h1 : MeasurableSet {ω | b ≤ C t ω} := measurableSet_Ici.preimage (hm t)
  have h2 : MeasurableSet {ω | C t ω < b + 2 * ε} := measurableSet_Iio.preimage (hm t)
  have heq : bandSet C t b ε = {ω | b ≤ C t ω} ∩ {ω | C t ω < b + 2 * ε} := by
    ext ω
    simp [bandSet]
  rw [heq]
  exact h1.inter h2

/-- Large grid oscillation is measurable. -/
lemma measurableSet_osc {C : ℝ≥0 → Ω → ℝ} (hm : ∀ u, Measurable (C u)) (t : ℝ≥0) (ε : ℝ)
    (n : ℕ) : MeasurableSet (oscSet C t ε n) := by
  rw [oscSet]
  exact measurableSet_Ioi.preimage (measurable_gridOsc hm t n)

/-- Reaching the level at the horizon is a grid hit. -/
lemma endpoint_subset_gridHit' (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (b : ℝ) (n : ℕ) :
    endpointSet C t b ⊆ gridHit C t b n := by
  simpa [endpointSet, gridHit] using endpoint_subset_gridHit (C := C) t b n

/-- A grid hit is a hit of the path. -/
lemma gridHit_subset_hitSet (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (b : ℝ) (n : ℕ) :
    gridHit C t b n ⊆ hitSet C t b := by
  simpa [gridHit, hitSet] using gridHit_subset_hit (C := C) t b n

/-- Each positive-index passage is at most twice its endpoint piece. -/
lemma measure_isTau_le_two {C : ℝ≥0 → Ω → ℝ} (hC : IsBrownianReal C μ)
    (hm : ∀ u, Measurable (C u)) {t : ℝ≥0} (b : ℝ) {n k : ℕ} (hk : k ≤ 2 ^ n) :
    μ (isTauSet C t b n k) ≤ 2 * μ (isTauSet C t b n k ∩ endpointSet C t b) := by
  let tau := isTauSet C t b n k
  let high := tau ∩ endpointSet C t b
  let low := tau ∩ belowSet C t b
  have hsplit : μ high + μ low = μ tau := by
    have hdiff : tau \ endpointSet C t b = low := by
      ext ω
      simp [tau, low, endpointSet, belowSet, not_le]
    rw [← hdiff]
    simpa [high] using measure_inter_add_sdiff tau (measurableSet_endpoint hm t b)
  have hsub : low ⊆ tau ∩ {ω | C t ω ≤ 2 * C (grid t n k) ω - b} := by
    intro ω hω
    have hlevel : b ≤ C (grid t n k) ω := hω.1.2.1
    have hge : b ≤ 2 * C (grid t n k) ω - b := by linarith
    exact ⟨hω.1, le_trans (le_of_lt hω.2) hge⟩
  have hreflect := measure_isTau_reflect hC hm t b hk
  have hlow : μ low ≤ μ high := by
    calc
      μ low ≤ μ (tau ∩ {ω | C t ω ≤ 2 * C (grid t n k) ω - b}) := measure_mono hsub
      _ = μ high := by simpa [high, endpointSet, tau] using hreflect.symm
  calc
    μ tau = μ high + μ low := hsplit.symm
    _ ≤ μ high + μ high := add_le_add le_rfl hlow
    _ = 2 * μ high := by rw [two_mul]

/-- The grid hitting measure is at most twice the endpoint. -/
lemma measure_gridHit_le {C : ℝ≥0 → Ω → ℝ} (hC : IsBrownianReal C μ)
    (hm : ∀ u, Measurable (C u)) {t : ℝ≥0} {b : ℝ} (n : ℕ) :
    μ (gridHit C t b n) ≤ 2 * μ (endpointSet C t b) := by
  let idx := Finset.range (2 ^ n + 1)
  let tau : ℕ → Set Ω := isTauSet C t b n
  let high : ℕ → Set Ω := fun k => tau k ∩ endpointSet C t b
  have hdisj : PairwiseDisjoint (↑idx) tau := fun k _ m _ hkm => disjoint_isTauSet t b n hkm
  have hmeas : ∀ k ∈ idx, MeasurableSet (tau k) := fun k _ => measurableSet_isTauSet hm t b n k
  have hle : ∀ k ∈ idx, μ (tau k) ≤ 2 * μ (high k) := by
    intro k hk
    have hk' : k ≤ 2 ^ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    simpa [tau, high] using measure_isTau_le_two hC hm b hk'
  have hsumTau : ∑ k ∈ idx, μ (tau k) = μ (gridHit C t b n) := by
    rw [← measure_biUnion_finset hdisj hmeas, ← gridHit_eq_iUnion]
  have hdisjH : PairwiseDisjoint (↑idx) high := hdisj.mono fun _ => inter_subset_left
  have hsumHigh : ∑ k ∈ idx, μ (high k) = μ (endpointSet C t b) := by
    have hunion : ⋃ k ∈ idx, high k = gridHit C t b n ∩ endpointSet C t b := by
      simp_rw [high, tau]
      rw [← iUnion₂_inter, ← gridHit_eq_iUnion]
    rw [← measure_biUnion_finset hdisjH fun k hk =>
      (hmeas k hk).inter (measurableSet_endpoint hm t b), hunion,
      inter_eq_right.2 (endpoint_subset_gridHit' C t b n)]
  calc
    μ (gridHit C t b n) = ∑ k ∈ idx, μ (tau k) := hsumTau.symm
    _ ≤ ∑ k ∈ idx, 2 * μ (high k) := Finset.sum_le_sum hle
    _ = 2 * ∑ k ∈ idx, μ (high k) := by rw [Finset.mul_sum]
    _ = 2 * μ (endpointSet C t b) := by rw [hsumHigh]

/-- Paths whose grid hits persist from stage `N` onward. -/
def gridTail (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (b : ℝ) (N : ℕ) : Set Ω :=
  ⋂ n ∈ Set.Ici N, gridHit C t b n

/-- Later tails contain the earlier ones. -/
lemma monotone_gridTail (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (b : ℝ) : Monotone (gridTail C t b) := by
  intro N M hNM ω hω
  simp only [gridTail, mem_iInter, Set.mem_Ici] at hω ⊢
  intro n hn
  exact hω n (le_trans hNM hn)

/-- A strict hit eventually lies on every fine grid. -/
lemma strictHit_subset_iUnion_tail {C : ℝ≥0 → Ω → ℝ}
    (hcont : ∀ ω, Continuous (fun u => C u ω)) {t : ℝ≥0} (ht : 0 < t) (b : ℝ) :
    strictHit C t b ⊆ ⋃ N, gridTail C t b N := by
  intro ω ⟨s, hs, hlt⟩
  let δ : ℝ := (C s ω - b) / 2
  have hδ : 0 < δ := div_pos (sub_pos.mpr hlt) two_pos
  have hcont_at : ContinuousAt (fun u => C u ω) s := (hcont ω).continuousAt
  obtain ⟨η, hη, hclose⟩ := (Metric.continuousAt_iff.mp hcont_at) δ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_gridMesh t).eventually (Iio_mem_nhds hη))
  refine mem_iUnion.2 ⟨N, ?_⟩
  simp only [gridTail, mem_iInter, Set.mem_Ici]
  intro n hn
  have hmesh : gridMesh t n < η := by simpa [Set.mem_Iio] using hN n hn
  obtain ⟨k, hk, hnear⟩ := exists_grid_near ht n hs
  have hdist : dist (grid t n k) s < η := by
    rw [NNReal.dist_eq]
    exact lt_of_le_of_lt hnear hmesh
  have hval : |C (grid t n k) ω - C s ω| < δ := by
    rw [← Real.dist_eq]
    exact hclose (x := grid t n k) hdist
  have hgt : b < C (grid t n k) ω := by
    have hlow : C s ω - δ < C (grid t n k) ω := by linarith [abs_lt.mp hval]
    have hbase : b < C s ω - δ := by
      unfold δ
      linarith
    linarith
  rw [gridHit]
  exact ⟨k, hk, hgt.le⟩

/-- Strict crossing is at most twice the closed endpoint. -/
lemma measure_strictHit_le {C : ℝ≥0 → Ω → ℝ} (hC : IsBrownianReal C μ)
    (hm : ∀ u, Measurable (C u)) (hcont : ∀ ω, Continuous (fun u => C u ω)) {t : ℝ≥0}
    (ht : 0 < t) {b : ℝ} (_hb : 0 < b) :
    μ (strictHit C t b) ≤ 2 * μ (endpointSet C t b) := by
  have hmono : Monotone (gridTail C t b) := monotone_gridTail C t b
  have hsup : ⨆ N, μ (gridTail C t b N) ≤ 2 * μ (endpointSet C t b) := by
    refine iSup_le fun N => ?_
    have hsub : gridTail C t b N ⊆ gridHit C t b N := by
      intro ω hω
      simp only [gridTail, mem_iInter, Set.mem_Ici] at hω
      exact hω N le_rfl
    exact (measure_mono hsub).trans (measure_gridHit_le hC hm N)
  calc
    μ (strictHit C t b) ≤ μ (⋃ N, gridTail C t b N) :=
      measure_mono (strictHit_subset_iUnion_tail hcont ht b)
    _ = ⨆ N, μ (gridTail C t b N) := hmono.measure_iUnion
    _ ≤ 2 * μ (endpointSet C t b) := hsup

/-- A higher closed level sits inside a lower strict level. -/
lemma hit_subset_strict (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) {b a : ℝ} (hba : b < a) :
    hitSet C t a ⊆ strictHit C t b := by
  intro ω ⟨s, hs, hle⟩
  exact ⟨s, hs, lt_of_lt_of_le hba hle⟩

/-- The closed hitting measure is at most twice the endpoint. -/
lemma measure_hit_le {C : ℝ≥0 → Ω → ℝ} (hC : IsBrownianReal C μ) (hm : ∀ u, Measurable (C u))
    (hcont : ∀ ω, Continuous (fun u => C u ω)) {t : ℝ≥0} (ht : 0 < t) {a : ℝ} (ha : 0 < a) :
    μ (hitSet C t a) ≤ 2 * μ (endpointSet C t a) := by
  let εm : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  let b : ℕ → ℝ := fun m => a - εm m
  have hε : Tendsto εm atTop (𝓝 0) := by
    have hinv : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    simpa [εm, one_div] using hinv
  have hb : Tendsto b atTop (𝓝 a) := by
    simpa [b, sub_zero] using tendsto_const_nhds.sub hε
  have hbmono : Monotone b := by
    intro m₁ m₂ hm
    have hle : ((m₁ : ℝ) + 1)⁻¹ ≥ ((m₂ : ℝ) + 1)⁻¹ :=
      inv_anti₀ (by positivity) (by gcongr)
    simpa [b, εm, one_div] using sub_le_sub_left hle a
  have hanti : Antitone fun m => endpointSet C t (b m) := by
    intro m₁ m₂ hm ω hω
    exact le_trans (hbmono hm) hω
  have hinter : ⋂ m, endpointSet C t (b m) = endpointSet C t a := by
    ext ω
    simp only [endpointSet, mem_iInter, mem_ofPred_eq]
    constructor
    · intro h
      exact le_of_tendsto' hb h
    · intro h m
      exact le_trans (by unfold b εm; linarith [show 0 ≤ εm m from by positivity]) h
  have hbpos : ∀ᶠ m in atTop, 0 < b m := by
    filter_upwards [hε.eventually (Iio_mem_nhds ha)] with m hm
    exact sub_pos.mpr hm
  have hle : ∀ᶠ m in atTop, μ (hitSet C t a) ≤ 2 * μ (endpointSet C t (b m)) := by
    filter_upwards [hbpos] with m hmpos
    have hba : b m < a := sub_lt_self a (by positivity : 0 < εm m)
    exact (measure_mono (hit_subset_strict C t hba)).trans
      (measure_strictHit_le hC hm hcont ht hmpos)
  have hmeas : ∀ m, NullMeasurableSet (endpointSet C t (b m)) μ :=
    fun m => (measurableSet_endpoint hm t (b m)).nullMeasurableSet
  have hlim := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top μ _⟩
  rw [hinter] at hlim
  have hmul := ENNReal.Tendsto.const_mul hlim (Or.inr (by simp : (2 : ℝ≥0∞) ≠ ∞))
  exact ge_of_tendsto hmul hle

/-- One grid still controls the endpoint up to a band and an oscillation event. -/
lemma two_mul_endpoint_le_aux {C : ℝ≥0 → Ω → ℝ} (hC : IsBrownianReal C μ)
    (hm : ∀ u, Measurable (C u)) {t : ℝ≥0} {a : ℝ} (ha : 0 < a) {ε : ℝ} (_hε : 0 < ε)
    (n : ℕ) :
    2 * μ (endpointSet C t a) ≤
      μ (hitSet C t a) + μ (bandSet C t a ε) + μ (oscSet C t ε n) := by
  let idx := Finset.range (2 ^ n + 1)
  let tau : ℕ → Set Ω := isTauSet C t a n
  let high : ℕ → Set Ω := fun k => tau k ∩ endpointSet C t a
  let low : ℕ → Set Ω := fun k => tau k ∩ belowSet C t a
  let refl : ℕ → Set Ω := fun k => tau k ∩ {ω | C t ω ≤ 2 * C (grid t n k) ω - a}
  let good : Set Ω := {ω | gridOsc C t n ω ≤ ε}
  have hmeasTau : ∀ k, MeasurableSet (tau k) := fun k => measurableSet_isTauSet hm t a n k
  have hmeasEnd : MeasurableSet (endpointSet C t a) := measurableSet_endpoint hm t a
  have hmeasGood : MeasurableSet good :=
    measurableSet_Iic.preimage (by simpa [good] using measurable_gridOsc hm t n)
  have hmeasBand : MeasurableSet (bandSet C t a ε) := measurableSet_band hm t a ε
  have hmeasBad : MeasurableSet (oscSet C t ε n) := measurableSet_osc hm t ε n
  have hsplit : ∀ k, μ (high k) + μ (low k) = μ (tau k) := by
    intro k
    have hdiff : tau k \ endpointSet C t a = low k := by
      ext ω
      simp [tau, low, endpointSet, belowSet, not_le]
    rw [← hdiff]
    simpa [high] using measure_inter_add_sdiff (tau k) hmeasEnd
  have hreflect : ∀ k, k ≤ 2 ^ n → μ (high k) = μ (refl k) := by
    intro k hk
    simpa [high, refl, endpointSet, tau] using measure_isTau_reflect hC hm t a hk
  have hpiece : ∀ k, 1 ≤ k → k ≤ 2 ^ n → refl k ∩ good ⊆
      low k ∪ (bandSet C t a ε ∩ tau k) := by
    intro k hk0 hk ω hω
    have hlt := overshoot_lt hk0 hk hω.1.1 hω.2 hω.1.2
    by_cases hbelow : C t ω < a
    · exact Or.inl ⟨hω.1.1, hbelow⟩
    · exact Or.inr ⟨⟨not_lt.mp hbelow, hlt⟩, hω.1.1⟩
  have hspill : ∀ k, refl k \ good ⊆ oscSet C t ε n ∩ tau k := by
    intro k ω hω
    have hmem : ω ∈ refl k ∧ ω ∉ good := by simpa [Set.mem_sdiff] using hω
    have hgt : ε < gridOsc C t n ω :=
      not_le.mp (by simpa [good, mem_ofPred_eq] using hmem.2)
    exact ⟨by simpa [oscSet, mem_ofPred_eq] using hgt, hmem.1.1⟩
  have hineq : ∀ k, 1 ≤ k → k ≤ 2 ^ n → μ (high k) ≤
      μ (low k) + μ (bandSet C t a ε ∩ tau k) + μ (oscSet C t ε n ∩ tau k) := by
    intro k hk0 hk
    have h1 : μ (refl k ∩ good) ≤ μ (low k ∪ (bandSet C t a ε ∩ tau k)) :=
      measure_mono (hpiece k hk0 hk)
    have h2 : μ (refl k \ good) ≤ μ (oscSet C t ε n ∩ tau k) := measure_mono (hspill k)
    have h3 : μ (low k ∪ (bandSet C t a ε ∩ tau k)) ≤
        μ (low k) + μ (bandSet C t a ε ∩ tau k) :=
      measure_union_le (low k) (bandSet C t a ε ∩ tau k)
    calc
      μ (high k) = μ (refl k) := hreflect k hk
      _ = μ (refl k ∩ good) + μ (refl k \ good) :=
        (measure_inter_add_sdiff (refl k) hmeasGood).symm
      _ ≤ μ (low k ∪ (bandSet C t a ε ∩ tau k)) + μ (oscSet C t ε n ∩ tau k) :=
        add_le_add h1 h2
      _ ≤ μ (low k) + μ (bandSet C t a ε ∩ tau k) + μ (oscSet C t ε n ∩ tau k) :=
        add_le_add_left h3 _
  have hterm : ∀ k ∈ idx, μ (high k) ≤
      μ (low k) + μ (bandSet C t a ε ∩ tau k) + μ (oscSet C t ε n ∩ tau k) := by
    intro k hk
    have hk' : k ≤ 2 ^ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    by_cases hk0 : 1 ≤ k
    · exact hineq k hk0 hk'
    · have hkzero : k = 0 := Nat.lt_one_iff.mp (lt_of_not_ge hk0)
      have hzero : μ (tau 0) = 0 := measure_isTauSet_zero hC t ha n
      have hhigh0 : μ (high k) = 0 := by
        rw [hkzero]
        exact measure_mono_null inter_subset_left hzero
      simp [hhigh0]
  have hsum : ∑ k ∈ idx, μ (high k) ≤ ∑ k ∈ idx, μ (low k) +
      ∑ k ∈ idx, μ (bandSet C t a ε ∩ tau k) +
      ∑ k ∈ idx, μ (oscSet C t ε n ∩ tau k) := by
    calc
      ∑ k ∈ idx, μ (high k) ≤ ∑ k ∈ idx, (μ (low k) + μ (bandSet C t a ε ∩ tau k) +
          μ (oscSet C t ε n ∩ tau k)) := Finset.sum_le_sum hterm
      _ = ∑ k ∈ idx, μ (low k) + ∑ k ∈ idx, μ (bandSet C t a ε ∩ tau k) +
          ∑ k ∈ idx, μ (oscSet C t ε n ∩ tau k) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hdisj : PairwiseDisjoint (↑idx) tau := fun _ _ _ _ hkm => disjoint_isTauSet t a n hkm
  have hsumTau : ∑ k ∈ idx, μ (tau k) = μ (gridHit C t a n) := by
    rw [← measure_biUnion_finset hdisj fun k _ => hmeasTau k, ← gridHit_eq_iUnion]
  have hsumHL : ∑ k ∈ idx, μ (high k) + ∑ k ∈ idx, μ (low k) = μ (gridHit C t a n) := by
    rw [← Finset.sum_add_distrib]
    have hsumEq : ∑ k ∈ idx, (μ (high k) + μ (low k)) = ∑ k ∈ idx, μ (tau k) :=
      Finset.sum_congr rfl fun k _ => hsplit k
    rw [hsumEq, hsumTau]
  have hdisjBand : PairwiseDisjoint (↑idx) (fun k => bandSet C t a ε ∩ tau k) :=
    hdisj.mono fun _ => inter_subset_right
  have hsumBand : ∑ k ∈ idx, μ (bandSet C t a ε ∩ tau k) ≤ μ (bandSet C t a ε) := by
    rw [← measure_biUnion_finset hdisjBand fun k _ => hmeasBand.inter (hmeasTau k)]
    exact measure_mono (iUnion₂_subset fun _ _ => inter_subset_left)
  have hdisjBad : PairwiseDisjoint (↑idx) (fun k => oscSet C t ε n ∩ tau k) :=
    hdisj.mono fun _ => inter_subset_right
  have hsumBad : ∑ k ∈ idx, μ (oscSet C t ε n ∩ tau k) ≤ μ (oscSet C t ε n) := by
    rw [← measure_biUnion_finset hdisjBad fun k _ => hmeasBad.inter (hmeasTau k)]
    exact measure_mono (iUnion₂_subset fun _ _ => inter_subset_left)
  have hdisjH : PairwiseDisjoint (↑idx) high := hdisj.mono fun _ => inter_subset_left
  have hsumHigh : ∑ k ∈ idx, μ (high k) = μ (endpointSet C t a) := by
    have hunion : ⋃ k ∈ idx, high k = gridHit C t a n ∩ endpointSet C t a := by
      simp_rw [high, tau]
      rw [← iUnion₂_inter, ← gridHit_eq_iUnion]
    rw [← measure_biUnion_finset hdisjH fun k _ => (hmeasTau k).inter hmeasEnd, hunion,
      inter_eq_right.2 (endpoint_subset_gridHit' C t a n)]
  have hrest : ∑ k ∈ idx, μ (high k) ≤ ∑ k ∈ idx, μ (low k) + μ (bandSet C t a ε) +
      μ (oscSet C t ε n) := by
    calc
      ∑ k ∈ idx, μ (high k) ≤ ∑ k ∈ idx, μ (low k) +
          ∑ k ∈ idx, μ (bandSet C t a ε ∩ tau k) +
          ∑ k ∈ idx, μ (oscSet C t ε n ∩ tau k) := hsum
      _ ≤ ∑ k ∈ idx, μ (low k) + μ (bandSet C t a ε) + μ (oscSet C t ε n) :=
        add_le_add (add_le_add le_rfl hsumBand) hsumBad
  let H := ∑ k ∈ idx, μ (high k)
  let L := ∑ k ∈ idx, μ (low k)
  have hHL : H + L = μ (gridHit C t a n) := by simpa [H, L] using hsumHL
  have hH : H ≤ L + μ (bandSet C t a ε) + μ (oscSet C t ε n) := by simpa [H, L] using hrest
  have htwo : 2 * H ≤ μ (gridHit C t a n) + μ (bandSet C t a ε) + μ (oscSet C t ε n) := by
    calc
      2 * H = H + H := by rw [two_mul]
      _ ≤ H + (L + μ (bandSet C t a ε) + μ (oscSet C t ε n)) := add_le_add le_rfl hH
      _ = H + L + μ (bandSet C t a ε) + μ (oscSet C t ε n) := by rw [← add_assoc, ← add_assoc]
      _ = μ (gridHit C t a n) + μ (bandSet C t a ε) + μ (oscSet C t ε n) := by rw [hHL]
  calc
    2 * μ (endpointSet C t a) = 2 * H := by simp [H, hsumHigh]
    _ ≤ μ (gridHit C t a n) + μ (bandSet C t a ε) + μ (oscSet C t ε n) := htwo
    _ ≤ μ (hitSet C t a) + μ (bandSet C t a ε) + μ (oscSet C t ε n) :=
      add_le_add (add_le_add (measure_mono (gridHit_subset_hitSet C t a n)) le_rfl) le_rfl

/-- Grid oscillation of a continuous modification has measures tending to zero. -/
lemma tendsto_measure_oscSet {C : ℝ≥0 → Ω → ℝ} (hm : ∀ u, Measurable (C u))
    (hcont : ∀ ω, Continuous (fun u => C u ω)) (t : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => μ (oscSet C t ε n)) atTop (𝓝 0) := by
  let tail : ℕ → Set Ω := fun N => ⋃ n ∈ Set.Ici N, oscSet C t ε n
  have hanti : Antitone tail := by
    intro N M hNM ω hω
    simp only [tail, mem_iUnion, Set.mem_Ici] at hω ⊢
    obtain ⟨n, hn, hω⟩ := hω
    exact ⟨n, le_trans hNM hn, hω⟩
  have hempty : ⋂ N, tail N = ∅ := by
    ext ω
    simp only [mem_iInter, mem_empty_iff_false, iff_false]
    intro h
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (tendsto_gridOsc hcont t ω)) ε hε
    have htail := h N
    simp only [tail, mem_iUnion, Set.mem_Ici] at htail
    obtain ⟨n, hn, hbad⟩ := htail
    have hdist := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (gridOsc_nonneg C t n ω)] at hdist
    exact absurd (by simpa [oscSet] using hbad) (not_lt_of_gt hdist)
  have hmeas : ∀ N, NullMeasurableSet (tail N) μ := by
    intro N
    have hcount : (Set.Ici N).Countable :=
      Set.Countable.mono (subset_univ _) Set.countable_univ
    exact (MeasurableSet.biUnion hcount fun _ _ => measurableSet_osc hm t ε _).nullMeasurableSet
  have hlim := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top μ _⟩
  rw [hempty, measure_empty] at hlim
  have hmono : ∀ n, μ (oscSet C t ε n) ≤ μ (tail n) := by
    intro n
    refine measure_mono fun ω hω => ?_
    simp only [tail, mem_iUnion, Set.mem_Ici]
    exact ⟨n, le_rfl, hω⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hmono

/-- The endpoint is at most half the hitting measure. -/
lemma two_mul_endpoint_le_hit {C : ℝ≥0 → Ω → ℝ} (hC : IsBrownianReal C μ)
    (hm : ∀ u, Measurable (C u)) (hcont : ∀ ω, Continuous (fun u => C u ω)) {t : ℝ≥0}
    (ht : 0 < t) {a : ℝ} (ha : 0 < a) :
    2 * μ (endpointSet C t a) ≤ μ (hitSet C t a) := by
  have hstep : ∀ ε, 0 < ε → 2 * μ (endpointSet C t a) ≤
      μ (hitSet C t a) + μ (bandSet C t a ε) := by
    intro ε hε
    have hosc : Tendsto (fun n => μ (oscSet C t ε n)) atTop (𝓝 0) :=
      tendsto_measure_oscSet hm hcont t hε
    exact le_of_forall_le_add_tendsto_zero
      (ENNReal.mul_ne_top (by simp) (measure_ne_top μ _))
      (ENNReal.add_ne_top.2 ⟨measure_ne_top μ _, measure_ne_top μ _⟩)
      (fun _ => measure_ne_top μ _)
      (fun n => two_mul_endpoint_le_aux hC hm ha hε n) hosc
  let εm : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hεtend : Tendsto εm atTop (𝓝 0) := by
    have hinv : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    simpa [εm, one_div] using hinv
  have hpos : ∀ m, 0 < εm m := fun _ => by positivity
  have hanti : Antitone fun m => bandSet C t a (εm m) := by
    intro m₁ m₂ hm ω hω
    have hεle : εm m₂ ≤ εm m₁ := by
      simpa [εm, one_div] using
        (inv_anti₀ (by positivity) (by gcongr : (m₁ : ℝ) + 1 ≤ (m₂ : ℝ) + 1))
    refine ⟨hω.1, lt_of_lt_of_le hω.2 ?_⟩
    linarith
  have hinter : ⋂ m, bandSet C t a (εm m) = {ω | C t ω = a} := by
    ext ω
    simp only [bandSet, mem_iInter, mem_ofPred_eq]
    constructor
    · intro h
      have hlower : a ≤ C t ω := (h 0).1
      have hupper : ∀ m, C t ω < a + 2 * εm m := fun m => (h m).2
      have htop : Tendsto (fun m => a + 2 * εm m) atTop (𝓝 a) := by
        simpa [mul_zero, add_zero] using tendsto_const_nhds.add (hεtend.const_mul 2)
      exact le_antisymm (ge_of_tendsto' htop fun m => (hupper m).le) hlower
    · intro h m
      refine ⟨by simp [h], ?_⟩
      have hlt : a < a + 2 * εm m := by linarith [hpos m]
      simpa [h] using hlt
  have hmeas : ∀ m, NullMeasurableSet (bandSet C t a (εm m)) μ :=
    fun m => (measurableSet_band hm t a (εm m)).nullMeasurableSet
  have hlim := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top μ _⟩
  rw [hinter, measure_eq_endpoint hC ht a] at hlim
  exact le_of_forall_le_add_tendsto_zero
    (ENNReal.mul_ne_top (by simp) (measure_ne_top μ _))
    (measure_ne_top μ _)
    (fun _ => measure_ne_top μ _)
    (fun m => hstep (εm m) (hpos m)) hlim

/-- At time zero both sides of the reflection identity vanish. -/
lemma reflection_zero {C : ℝ≥0 → Ω → ℝ} (hC : IsBrownianReal C μ) {a : ℝ} (ha : 0 < a)
    {t : ℝ≥0} (ht : t = 0) : μ (hitSet C t a) = 2 * μ (endpointSet C t a) := by
  have hnull : μ {ω | C 0 ω ≠ 0} = 0 := ae_iff.mp hC.eval_zero_ae_eq_zero
  have hleft : μ (hitSet C t a) = 0 := by
    refine measure_mono_null ?_ hnull
    intro ω ⟨s, hs, hle⟩
    have hs0 : s = 0 := le_antisymm (by simpa [ht] using hs) bot_le
    intro hzero
    have : a ≤ 0 := by simpa [hs0, hzero] using hle
    exact (not_le_of_gt ha) this
  have hright : μ (endpointSet C t a) = 0 := by
    refine measure_mono_null ?_ hnull
    intro ω hω hzero
    have : a ≤ 0 := by simpa [endpointSet, ht, hzero] using hω
    exact (not_le_of_gt ha) this
  simp [hleft, hright]

/-- Reflection for an everywhere continuous measurable Brownian motion. -/
lemma reflection_continuous {C : ℝ≥0 → Ω → ℝ} (hC : IsBrownianReal C μ)
    (hm : ∀ u, Measurable (C u)) (hcont : ∀ ω, Continuous (fun u => C u ω)) {a : ℝ}
    (ha : 0 < a) (t : ℝ≥0) : μ (hitSet C t a) = 2 * μ (endpointSet C t a) := by
  by_cases ht : t = 0
  · exact reflection_zero hC ha ht
  · exact le_antisymm (measure_hit_le hC hm hcont (pos_iff_ne_zero.mpr ht) ha)
      (two_mul_endpoint_le_hit hC hm hcont (pos_iff_ne_zero.mpr ht) ha)

/-- **08.4**: the reflection principle for a real Brownian motion. -/
theorem reflection_principle {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) {a : ℝ} (ha : 0 < a)
    (t : ℝ≥0) :
    μ {ω | ∃ s : ℝ≥0, s ≤ t ∧ a ≤ B s ω} = 2 * μ {ω | a ≤ B t ω} := by
  obtain ⟨C, hm, hcont, hBr, hmod, _⟩ :=
    exists_continuous_holder_modification hB.toIsPreBrownianReal
  have hident := reflection_continuous hBr hm hcont ha t
  have hpath := ae_eq_of_continuous_of_nnrat hB.cont hcont fun q => hmod q
  have hhit : hitSet B t a =ᵐ[μ] hitSet C t a := by
    refine Eventually.set_eq ?_
    filter_upwards [hpath] with ω hω
    constructor
    · rintro ⟨s, hs, hle⟩
      exact ⟨s, hs, by simpa [hω s] using hle⟩
    · rintro ⟨s, hs, hle⟩
      exact ⟨s, hs, by simpa [← hω s] using hle⟩
  have hend : endpointSet B t a =ᵐ[μ] endpointSet C t a := by
    refine Eventually.set_eq ?_
    filter_upwards [hmod t] with ω hω
    simp [endpointSet, hω]
  have hgoal : μ (hitSet B t a) = 2 * μ (endpointSet B t a) := by
    calc
      μ (hitSet B t a) = μ (hitSet C t a) := measure_congr hhit
      _ = 2 * μ (endpointSet C t a) := hident
      _ = 2 * μ (endpointSet B t a) := by rw [measure_congr hend.symm]
  simpa [hitSet, endpointSet] using hgoal

end CKMA
