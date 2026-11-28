/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Ergodic.Recurrence.Combinatorics
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

/-!
# Multiple recurrence from progression counts

An initial orbit segment that meets a positive-measure set in positive density contains
many arithmetic progressions, once a Szemerédi count is available. Integrating those
progressions bounds the Cesàro means of the corresponding return intersections from below.

Roth's theorem supplies the quadratic count for progressions of length three. The same
averaging applies to every longer progression.

## Main definitions

* `CKMA.apParams`: Pairs `(a, d)` indexing a nontrivial `L`-term progression in `{0, …, N - 1}`
  (re-exported from `Combinatorics`).
* `CKMA.progressionCount`: Number of nontrivial `L`-term progressions in `S ∩ {0, …, N - 1}`
  (re-exported from `Combinatorics`).

## Main results

* `CKMA.liminf_pos_of_progressionCount_ge`: a quadratic lower bound on progression counts in
  dense sets yields a positive liminf of the `L`-fold return averages of a positive-measure set.
-/

public section

noncomputable section

namespace CKMA

open Finset MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators

attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {T : Ω → Ω} {A : Set Ω}

/-- Times in `{0, …, N - 1}` at which the orbit of `x` meets `A`. -/
private def orbitVisits (T : Ω → Ω) (A : Set Ω) (N : ℕ) (x : Ω) : Finset ℕ :=
  (range N).filter fun m => T^[m] x ∈ A

/-- Points whose first `N` iterates meet `A` with density at least `θ`. -/
private def denseVisits (T : Ω → Ω) (A : Set Ω) (θ : ℝ) (N : ℕ) : Set Ω :=
  {x | θ * (N : ℝ) ≤ ((orbitVisits T A N x).card : ℝ)}

omit [MeasurableSpace Ω] in
/-- The visit count is the sum of the indicators of the first `N` preimages. -/
private lemma orbitVisits_card_eq (T : Ω → Ω) (A : Set Ω) (N : ℕ) (x : Ω) :
    ((orbitVisits T A N x).card : ℝ≥0∞) =
      ∑ m ∈ range N, Set.indicator ((T^[m]) ⁻¹' A) (fun _ => (1 : ℝ≥0∞)) x := by
  rw [orbitVisits, card_filter, Nat.cast_sum]
  refine sum_congr rfl fun m _ => ?_
  by_cases hx : T^[m] x ∈ A
  · have hmem : x ∈ (T^[m]) ⁻¹' A := hx
    simp [ite_eq_left hx, Set.indicator_of_mem hmem]
  · have hnmem : x ∉ (T^[m]) ⁻¹' A := hx
    simp [ite_eq_right hx, Set.indicator_of_notMem hnmem]

/-- Integrating visit counts recovers `N` times the measure of `A`. -/
private lemma lintegral_orbitVisits (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A)
    (N : ℕ) :
    ∫⁻ x, ((orbitVisits T A N x).card : ℝ≥0∞) ∂μ = (N : ℝ≥0∞) * μ A := by
  rw [lintegral_congr fun x => orbitVisits_card_eq T A N x]
  have hnull : ∀ m, NullMeasurableSet ((T^[m]) ⁻¹' A) μ :=
    fun m => (hT.iterate m).aemeasurable.nullMeasurableSet_preimage hA
  rw [lintegral_finsetSum' (range N) fun m _ => aemeasurable_const.indicator₀ (hnull m)]
  have hterm : ∀ m ∈ range N,
      ∫⁻ a, ((T^[m]) ⁻¹' A).indicator (fun _ => (1 : ℝ≥0∞)) a ∂μ = μ A := by
    intro m _
    rw [lintegral_indicator_const₀ (hnull m) 1, one_mul]
    exact (hT.iterate m).measure_preimage hA.nullMeasurableSet
  rw [sum_congr rfl hterm, sum_const, card_range, nsmul_eq_mul]

/-- The visit-count function is almost everywhere measurable. -/
private lemma aemeasurable_orbitCard (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A)
    (N : ℕ) : AEMeasurable (fun x => ((orbitVisits T A N x).card : ℝ≥0∞)) μ := by
  have hsum : AEMeasurable (fun x => ∑ m ∈ range N,
      Set.indicator ((T^[m]) ⁻¹' A) (fun _ => (1 : ℝ≥0∞)) x) μ :=
    (range N).aemeasurable_fun_sum fun m _ =>
      aemeasurable_const.indicator₀
        ((hT.iterate m).aemeasurable.nullMeasurableSet_preimage hA)
  exact hsum.congr (ae_of_all μ fun x => (orbitVisits_card_eq T A N x).symm)

/-- The set of densely visiting points is null measurable. -/
private lemma nullMeasurable_denseVisits (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A)
    (θ : ℝ) (N : ℕ) : NullMeasurableSet (denseVisits T A θ N) μ := by
  have hset : denseVisits T A θ N =
      (fun x => ((orbitVisits T A N x).card : ℝ≥0∞)) ⁻¹'
        Set.Ici (ENNReal.ofReal (θ * (N : ℝ))) := by
    ext x
    rw [denseVisits, Set.mem_ofPred, Set.mem_preimage, Set.mem_Ici]
    simp
  rw [hset]
  exact (aemeasurable_orbitCard hT hA N).nullMeasurableSet_preimage measurableSet_Ici

/-- A positive-measure set forces a uniformly positive mass of dense orbit segments. -/
private lemma denseVisits_measure_ge [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    (hA : MeasurableSet A) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {N : ℕ} (hN : 0 < N) :
    ENNReal.ofReal (((μ A).toReal - θ) / (1 - θ)) ≤ μ (denseVisits T A θ N) := by
  let f : Ω → ℝ≥0∞ := fun x => ((orbitVisits T A N x).card : ℝ≥0∞)
  let G := denseVisits T A θ N
  have hG : NullMeasurableSet G μ := nullMeasurable_denseVisits hT hA θ N
  have hint : ∫⁻ x, f x ∂μ = (N : ℝ≥0∞) * μ A := lintegral_orbitVisits hT hA N
  have hsplit : ∫⁻ x in G, f x ∂μ + ∫⁻ x in Gᶜ, f x ∂μ = ∫⁻ x, f x ∂μ :=
    lintegral_add_compl₀ f hG
  have hleG : ∫⁻ x in G, f x ∂μ ≤ (N : ℝ≥0∞) * μ G := by
    calc
      ∫⁻ x in G, f x ∂μ ≤ ∫⁻ _ in G, (N : ℝ≥0∞) ∂μ := by
        refine setLIntegral_mono measurable_const fun x _ => ?_
        dsimp only [f]
        refine Nat.cast_le.mpr ?_
        rw [orbitVisits]
        exact (card_filter_le (range N) fun m => T^[m] x ∈ A).trans (le_of_eq (card_range N))
      _ = (N : ℝ≥0∞) * μ G := setLIntegral_const G _
  have hleGc : ∫⁻ x in Gᶜ, f x ∂μ ≤ ENNReal.ofReal (θ * (N : ℝ)) * μ Gᶜ := by
    calc
      ∫⁻ x in Gᶜ, f x ∂μ ≤ ∫⁻ _ in Gᶜ, ENNReal.ofReal (θ * (N : ℝ)) ∂μ := by
        refine setLIntegral_mono measurable_const fun x hx => ?_
        have hnot : ¬ θ * (N : ℝ) ≤ ((orbitVisits T A N x).card : ℝ) := by
          simpa [G, denseVisits, Set.mem_ofPred] using hx
        dsimp only [f]
        rw [← ENNReal.ofReal_natCast (orbitVisits T A N x).card]
        exact ENNReal.ofReal_le_ofReal (lt_of_not_ge hnot).le
      _ = ENNReal.ofReal (θ * (N : ℝ)) * μ Gᶜ := setLIntegral_const Gᶜ _
  have hθN : ENNReal.ofReal (θ * (N : ℝ)) = ENNReal.ofReal θ * (N : ℝ≥0∞) := by
    rw [ENNReal.ofReal_mul hθ0, ENNReal.ofReal_natCast]
  have hsum : (N : ℝ≥0∞) * μ A ≤
      (N : ℝ≥0∞) * (μ G + ENNReal.ofReal θ * μ Gᶜ) := by
    calc
      (N : ℝ≥0∞) * μ A = ∫⁻ x in G, f x ∂μ + ∫⁻ x in Gᶜ, f x ∂μ := by
        rw [← hint, ← hsplit]
      _ ≤ (N : ℝ≥0∞) * μ G + ENNReal.ofReal (θ * (N : ℝ)) * μ Gᶜ := add_le_add hleG hleGc
      _ = (N : ℝ≥0∞) * μ G + (ENNReal.ofReal θ * (N : ℝ≥0∞)) * μ Gᶜ := by rw [hθN]
      _ = (N : ℝ≥0∞) * μ G + (N : ℝ≥0∞) * (ENNReal.ofReal θ * μ Gᶜ) := by
        rw [mul_comm (ENNReal.ofReal θ) (N : ℝ≥0∞), mul_assoc]
      _ = (N : ℝ≥0∞) * (μ G + ENNReal.ofReal θ * μ Gᶜ) := by rw [mul_add]
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
  have hcancel : μ A ≤ μ G + ENNReal.ofReal θ * μ Gᶜ :=
    (ENNReal.mul_le_mul_iff_right hN0 (ENNReal.natCast_ne_top N)).mp hsum
  have hGfin : μ G ≠ ∞ := measure_ne_top μ G
  have hGcfin : μ Gᶜ ≠ ∞ := measure_ne_top μ Gᶜ
  have hprod : ENNReal.ofReal θ * μ Gᶜ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGcfin
  have hto : (μ A).toReal ≤ (μ G).toReal + θ * (μ Gᶜ).toReal := by
    have hmono := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hGfin, hprod⟩) hcancel
    rw [ENNReal.toReal_add hGfin hprod, ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ0] at hmono
    exact hmono
  have hcompl : (μ Gᶜ).toReal = 1 - (μ G).toReal := by
    rw [prob_compl_eq_one_sub₀ hG, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
  have hden : 0 < 1 - θ := sub_pos.mpr hθ1
  have hdiv : ((μ A).toReal - θ) / (1 - θ) ≤ (μ G).toReal := by
    rw [div_le_iff₀ hden]
    have hlin : (μ A).toReal ≤ (μ G).toReal * (1 - θ) + θ := by
      have hrewrite : (μ G).toReal + θ * (1 - (μ G).toReal) =
          (μ G).toReal * (1 - θ) + θ := by ring
      rw [hcompl] at hto
      linarith
    linarith
  exact (ENNReal.ofReal_le_iff_le_toReal hGfin).mpr hdiv

/-- Points whose orbit meets `A` along the progression with start `p.1` and gap `p.2`. -/
private def progressionHit (T : Ω → Ω) (A : Set Ω) (L : ℕ) (p : ℕ × ℕ) : Set Ω :=
  {x | ∀ j ∈ range L, T^[p.1 + j * p.2] x ∈ A}

omit [MeasurableSpace Ω] in
/-- A progression hit is the intersection of the corresponding preimages. -/
private lemma progressionHit_eq (T : Ω → Ω) (A : Set Ω) (L : ℕ) (p : ℕ × ℕ) :
    progressionHit T A L p = ⋂ j ∈ range L, (T^[p.1 + j * p.2]) ⁻¹' A := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iInter₂.mpr fun j hj => ?_
    rw [Set.mem_preimage]
    exact hx j (mem_coe.mp hj)
  · intro hx j hj
    have hxj := Set.mem_iInter₂.mp hx j (mem_coe.mpr hj)
    rw [Set.mem_preimage] at hxj
    exact hxj

/-- Each progression hit is null measurable. -/
private lemma progressionHit_nullMeasurable (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A)
    (L : ℕ) (p : ℕ × ℕ) : NullMeasurableSet (progressionHit T A L p) μ := by
  rw [progressionHit_eq]
  exact NullMeasurableSet.biInter (Finset.countable_toSet (range L)) fun j _ =>
    (hT.iterate (p.1 + j * p.2)).aemeasurable.nullMeasurableSet_preimage hA

/-- Every term of a progression indexed by `apParams` lies in `{0, …, N - 1}`. -/
private lemma progression_index_lt {L N : ℕ} {p : ℕ × ℕ} (hp : p ∈ apParams L N) {j : ℕ}
    (hj : j ∈ range L) : p.1 + j * p.2 < N := by
  have hlast : p.1 + (L - 1) * p.2 < N := (mem_filter.mp hp).2.2
  have hjle : j ≤ L - 1 := by
    have hjlt : j < L := mem_range.mp hj
    omega
  exact Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_right p.2 hjle) _) hlast

omit [MeasurableSpace Ω] in
/-- Membership in a progression hit is membership of its times in the visit set. -/
private lemma mem_progressionHit_iff (T : Ω → Ω) (A : Set Ω) {L N : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ apParams L N) (x : Ω) :
    x ∈ progressionHit T A L p ↔
      ∀ j ∈ range L, p.1 + j * p.2 ∈ orbitVisits T A N x := by
  constructor
  · intro hx j hj
    rw [orbitVisits, mem_filter, mem_range]
    exact ⟨progression_index_lt hp hj, hx j hj⟩
  · intro hx j hj
    exact (mem_filter.mp (hx j hj)).2

omit [MeasurableSpace Ω] in
/-- The progression count is the sum of the indicators of the progression hits. -/
private lemma progressionCount_indicator (T : Ω → Ω) (A : Set Ω) (L N : ℕ) (x : Ω) :
    (progressionCount L N (orbitVisits T A N x) : ℝ≥0∞) =
      ∑ p ∈ apParams L N,
        Set.indicator (progressionHit T A L p) (fun _ => (1 : ℝ≥0∞)) x := by
  rw [progressionCount, card_filter, Nat.cast_sum]
  refine sum_congr rfl fun p hp => ?_
  by_cases hx : x ∈ progressionHit T A L p
  · have hvisit : ∀ j ∈ range L, p.1 + j * p.2 ∈ orbitVisits T A N x :=
      (mem_progressionHit_iff T A hp x).1 hx
    rw [ite_eq_left (hc := hvisit), Nat.cast_one, Set.indicator_of_mem hx]
  · have hnot : ¬ ∀ j ∈ range L, p.1 + j * p.2 ∈ orbitVisits T A N x :=
      fun h => hx ((mem_progressionHit_iff T A hp x).2 h)
    rw [ite_eq_right (hnc := hnot), Nat.cast_zero, Set.indicator_of_notMem hx]

omit [MeasurableSpace Ω] in
/-- Shifting a progression hit by its start is one application of `T`. -/
private lemma progressionHit_shift (T : Ω → Ω) (A : Set Ω) (L a d : ℕ) :
    progressionHit T A L (a, d) = (T^[a]) ⁻¹' progressionHit T A L (0, d) := by
  ext x
  simp only [progressionHit, Set.mem_ofPred, Set.mem_preimage]
  constructor
  · intro hx j hj
    have h := hx j hj
    rw [Nat.add_comm a (j * d), iterate_add_apply] at h
    simpa [Nat.zero_add] using h
  · intro hx j hj
    have h := hx j hj
    rw [Nat.zero_add] at h
    rw [Nat.add_comm a (j * d), iterate_add_apply]
    exact h

/-- A measure-preserving map leaves the measure of a progression hit unchanged. -/
private lemma measure_progressionHit_shift (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A)
    (L a d : ℕ) :
    μ (progressionHit T A L (a, d)) = μ (progressionHit T A L (0, d)) := by
  rw [progressionHit_shift]
  exact (hT.iterate a).measure_preimage (progressionHit_nullMeasurable hT hA L (0, d))

/-- The integrated progression count is the sum of the measures of the hits. -/
private lemma lintegral_progressionCount (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A)
    (L N : ℕ) :
    ∫⁻ x, (progressionCount L N (orbitVisits T A N x) : ℝ≥0∞) ∂μ =
      ∑ p ∈ apParams L N, μ (progressionHit T A L p) := by
  rw [lintegral_congr fun x => progressionCount_indicator T A L N x]
  have hnull : ∀ p ∈ apParams L N, NullMeasurableSet (progressionHit T A L p) μ :=
    fun p _ => progressionHit_nullMeasurable hT hA L p
  rw [lintegral_finsetSum' (apParams L N) fun p hp => aemeasurable_const.indicator₀ (hnull p hp)]
  refine sum_congr rfl fun p hp => ?_
  rw [lintegral_indicator_const₀ (hnull p hp) 1, one_mul]

/-- Gaps of indexed progressions lie in `{1, …, N}`. -/
private lemma apParams_snd_mem_Icc {L N : ℕ} (hL : 3 ≤ L) {p : ℕ × ℕ} (hp : p ∈ apParams L N) :
    p.2 ∈ Icc 1 N := by
  have hp' := mem_filter.mp hp
  have hlast : p.1 + (L - 1) * p.2 < N := hp'.2.2
  have hL1 : 0 < L - 1 := by omega
  have hdlt : p.2 < N := by
    have hdmul : p.2 ≤ (L - 1) * p.2 := Nat.le_mul_of_pos_left p.2 hL1
    exact Nat.lt_of_le_of_lt (hdmul.trans (Nat.le_add_left _ p.1)) hlast
  rw [mem_Icc]
  exact ⟨Nat.succ_le_of_lt hp'.2.1, le_of_lt hdlt⟩

/-- At most `N` indexed progressions share a fixed positive gap. -/
private lemma fiber_card_le (L N d : ℕ) : #{p ∈ apParams L N | p.2 = d} ≤ N := by
  refine (card_le_card_of_injOn (s := (apParams L N).filter fun p => p.2 = d) (t := range N)
      Prod.fst ?_ ?_).trans (le_of_eq (card_range N))
  · intro p hp
    rw [mem_coe, mem_filter] at hp
    rw [mem_coe, mem_range]
    have hlast : p.1 + (L - 1) * p.2 < N := (mem_filter.mp hp.1).2.2
    exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hlast
  · intro p hp q hq hfst
    rw [mem_coe, mem_filter] at hp hq
    exact Prod.ext hfst (hp.2.trans hq.2.symm)

/-- Summing hit measures by gap costs at most a factor `N`. -/
private lemma sum_progressionHit_le (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A)
    {L N : ℕ} (hL : 3 ≤ L) :
    ∑ p ∈ apParams L N, μ (progressionHit T A L p) ≤
      (N : ℝ≥0∞) * ∑ d ∈ Icc 1 N, μ (progressionHit T A L (0, d)) := by
  have hmaps : ∀ p ∈ apParams L N, p.2 ∈ Icc 1 N := fun p hp => apParams_snd_mem_Icc hL hp
  have hfib := sum_fiberwise_of_maps_to' (s := apParams L N) (t := Icc 1 N) (g := Prod.snd)
    hmaps fun d => μ (progressionHit T A L (0, d))
  have hshift : ∑ p ∈ apParams L N, μ (progressionHit T A L (0, p.2)) =
      ∑ p ∈ apParams L N, μ (progressionHit T A L p) := by
    refine sum_congr rfl fun p _ => (measure_progressionHit_shift hT hA L p.1 p.2).symm
  have hcardμ : ∑ d ∈ Icc 1 N,
      ∑ p ∈ apParams L N with p.2 = d, μ (progressionHit T A L (0, d)) =
      ∑ d ∈ Icc 1 N, (#{p ∈ apParams L N | p.2 = d} : ℝ≥0∞) *
        μ (progressionHit T A L (0, d)) := by
    refine sum_congr rfl fun _ _ => ?_
    rw [sum_const, nsmul_eq_mul]
  rw [← hshift, ← hfib, hcardμ]
  calc
    ∑ d ∈ Icc 1 N, (#{p ∈ apParams L N | p.2 = d} : ℝ≥0∞) *
        μ (progressionHit T A L (0, d))
      ≤ ∑ d ∈ Icc 1 N, (N : ℝ≥0∞) * μ (progressionHit T A L (0, d)) := by
        refine sum_le_sum fun d _ => ?_
        exact mul_le_mul' (Nat.cast_le.mpr (fiber_card_le L N d)) le_rfl
    _ = (N : ℝ≥0∞) * ∑ d ∈ Icc 1 N, μ (progressionHit T A L (0, d)) := by
        rw [mul_sum]

/-- Cesàro means of the `L`-fold return intersections along positive gaps. -/
private def progressionReturnAverage (μ : Measure Ω) (T : Ω → Ω) (A : Set Ω) (L N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ range N,
    (μ (⋂ j ∈ range L, (T^[j * (n + 1)]) ⁻¹' A)).toReal

/-- Each return average is at most one. -/
private lemma progressionReturnAverage_le_one [IsProbabilityMeasure μ] (T : Ω → Ω) (A : Set Ω)
    (L N : ℕ) : progressionReturnAverage μ T A L N ≤ 1 := by
  by_cases hN : N = 0
  · simp [progressionReturnAverage, hN, range_zero, sum_empty, inv_zero]
  · have hpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have hsum : ∑ n ∈ range N,
        (μ (⋂ j ∈ range L, (T^[j * (n + 1)]) ⁻¹' A)).toReal ≤ (N : ℝ) := by
      calc
        ∑ n ∈ range N, (μ (⋂ j ∈ range L, (T^[j * (n + 1)]) ⁻¹' A)).toReal
          ≤ ∑ n ∈ range N, (1 : ℝ) := sum_le_sum fun _ _ => measureReal_le_one
        _ = (N : ℝ) := by rw [sum_const, card_range, nsmul_eq_mul, mul_one]
    rw [progressionReturnAverage, inv_mul_le_iff₀ hpos, mul_one]
    exact hsum

/-- A quadratic progression count yields a uniform positive lower bound on return averages. -/
private lemma progressionReturnAverage_ge [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    (hA : MeasurableSet A) {L : ℕ} (hL : 3 ≤ L) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hθδ : θ ≤ (μ A).toReal) {c : ℝ} (hc : 0 < c) {N0 : ℕ}
    (hcount : ∀ N, N0 ≤ N → ∀ S : Finset ℕ, S ⊆ range N → θ * (N : ℝ) ≤ (S.card : ℝ) →
      c * (N : ℝ) ^ 2 ≤ (progressionCount L N S : ℝ))
    {N : ℕ} (hN : max N0 1 ≤ N) :
    c * (((μ A).toReal - θ) / (1 - θ)) ≤ progressionReturnAverage μ T A L N := by
  have hNpos : 0 < N := Nat.succ_le_iff.mp (le_trans (Nat.le_max_right _ _) hN)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  set γ : ℝ := ((μ A).toReal - θ) / (1 - θ)
  have hden : 0 < 1 - θ := sub_pos.mpr hθ1
  have hγ0 : 0 ≤ γ := div_nonneg (sub_nonneg.mpr hθδ) hden.le
  let G := denseVisits T A θ N
  have hG : NullMeasurableSet G μ := nullMeasurable_denseVisits hT hA θ N
  have hμG : ENNReal.ofReal γ ≤ μ G := denseVisits_measure_ge hT hA hθ0.le hθ1 hNpos
  let cN : ℝ≥0∞ := ENNReal.ofReal (c * (N : ℝ) ^ 2)
  have hpoint : G.indicator (fun _ => cN) ≤
      fun x => (progressionCount L N (orbitVisits T A N x) : ℝ≥0∞) := by
    intro x
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx]
      have hsub : orbitVisits T A N x ⊆ range N := by
        rw [orbitVisits]
        exact filter_subset (fun m => T^[m] x ∈ A) (range N)
      have hdense : θ * (N : ℝ) ≤ ((orbitVisits T A N x).card : ℝ) := by
        simpa [G, denseVisits, Set.mem_ofPred] using hx
      have hnum := hcount N (le_trans (Nat.le_max_left _ _) hN) _ hsub hdense
      change ENNReal.ofReal (c * (N : ℝ) ^ 2) ≤
        (progressionCount L N (orbitVisits T A N x) : ℝ≥0∞)
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hnum
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  have hint := lintegral_mono (μ := μ) hpoint
  rw [lintegral_indicator_const₀ hG cN] at hint
  have hmul : cN * ENNReal.ofReal γ ≤ cN * μ G := mul_le_mul' le_rfl hμG
  have hcN : 0 ≤ c * (N : ℝ) ^ 2 := mul_nonneg hc.le (pow_nonneg (Nat.cast_nonneg _) _)
  have hprod : cN * ENNReal.ofReal γ = ENNReal.ofReal (c * (N : ℝ) ^ 2 * γ) := by
    unfold cN
    rw [← ENNReal.ofReal_mul hcN]
  have hintW := lintegral_progressionCount hT hA L N
  have hWle := sum_progressionHit_le hT hA hL (N := N)
  have hlow : ENNReal.ofReal (c * (N : ℝ) ^ 2 * γ) ≤
      (N : ℝ≥0∞) * ∑ d ∈ Icc 1 N, μ (progressionHit T A L (0, d)) := by
    calc
      ENNReal.ofReal (c * (N : ℝ) ^ 2 * γ) = cN * ENNReal.ofReal γ := hprod.symm
      _ ≤ cN * μ G := hmul
      _ ≤ ∫⁻ x, (progressionCount L N (orbitVisits T A N x) : ℝ≥0∞) ∂μ := hint
      _ = ∑ p ∈ apParams L N, μ (progressionHit T A L p) := hintW
      _ ≤ (N : ℝ≥0∞) * ∑ d ∈ Icc 1 N, μ (progressionHit T A L (0, d)) := hWle
  set S : ℝ≥0∞ := ∑ d ∈ Icc 1 N, μ (progressionHit T A L (0, d)) with hSdef
  have hSfin : S ≠ ∞ := ENNReal.sum_ne_top.mpr fun _ _ => measure_ne_top μ _
  have hNSfin : (N : ℝ≥0∞) * S ≠ ∞ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) hSfin
  have hnn : 0 ≤ c * (N : ℝ) ^ 2 * γ := mul_nonneg hcN hγ0
  have hreal : c * (N : ℝ) ^ 2 * γ ≤ (N : ℝ) * S.toReal := by
    have hmono := ENNReal.toReal_mono hNSfin hlow
    rw [ENNReal.toReal_ofReal hnn, ENNReal.toReal_mul, ENNReal.toReal_natCast] at hmono
    exact hmono
  have hsq : c * (N : ℝ) ^ 2 * γ = c * γ * N * N := by ring
  have hcancel : c * γ * N ≤ S.toReal := by
    rw [hsq, mul_comm (N : ℝ) S.toReal] at hreal
    exact (mul_le_mul_iff_left₀ hNreal).mp hreal
  have hIcc : ∑ d ∈ Icc 1 N, (μ (progressionHit T A L (0, d))).toReal =
      ∑ n ∈ range N, (μ (⋂ j ∈ range L, (T^[j * (n + 1)]) ⁻¹' A)).toReal := by
    refine (sum_nbij' (fun n => n + 1) (fun d => d - 1)
      (fun n hn => ?_) (fun d hd => ?_) (fun n _ => ?_) (fun d hd => ?_)
      (fun n _ => ?_)).symm
    · rw [mem_range] at hn
      rw [mem_Icc]
      omega
    · rw [mem_Icc] at hd
      rw [mem_range]
      omega
    · exact Nat.add_sub_cancel n 1
    · rw [mem_Icc] at hd
      exact Nat.sub_add_cancel hd.1
    · have hhit := progressionHit_eq T A L (0, n + 1)
      simp only [Nat.zero_add] at hhit
      exact (congrArg (fun s => (μ s).toReal) hhit).symm
  have hSreal : S.toReal = ∑ n ∈ range N,
      (μ (⋂ j ∈ range L, (T^[j * (n + 1)]) ⁻¹' A)).toReal := by
    rw [hSdef, ENNReal.toReal_sum fun _ _ => measure_ne_top μ _, hIcc]
  have hdiv : c * γ ≤ progressionReturnAverage μ T A L N := by
    rw [progressionReturnAverage, ← hSreal, inv_mul_eq_div, le_div_iff₀ hNreal]
    exact hcancel
  exact hdiv

/-- If, for every density `δ > 0`, every `δ`-dense subset of a long interval `{0, …, N - 1}`
contains at least `c N²` nontrivial `L`-term progressions for some `c > 0`, then a set of
positive measure has a positive liminf of its `L`-fold return averages along progressions. -/
theorem liminf_pos_of_progressionCount_ge [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    (hA : MeasurableSet A) (hpos : 0 < μ A) {L : ℕ} (hL : 3 ≤ L)
    (hnum : ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ S : Finset ℕ,
      S ⊆ range N → δ * (N : ℝ) ≤ (S.card : ℝ) →
      c * (N : ℝ) ^ 2 ≤ (progressionCount L N S : ℝ)) :
    0 < liminf (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ range N,
      (μ (⋂ j ∈ range L, (T^[j * (n + 1)]) ⁻¹' A)).toReal) atTop := by
  set δ : ℝ := (μ A).toReal
  have hδ : 0 < δ := ENNReal.toReal_pos hpos.ne' (measure_ne_top μ A)
  have hδ1 : δ ≤ 1 := by
    have hle : μ A ≤ ENNReal.ofReal 1 := by simpa [ENNReal.ofReal_one] using (prob_le_one : μ A ≤ 1)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one hle
  set θ : ℝ := δ / 2 with hθdef
  have hθ : 0 < θ := by rw [hθdef]; exact half_pos hδ
  have hθ1 : θ < 1 := by rw [hθdef]; linarith
  have hθδ : θ ≤ δ := by rw [hθdef]; exact half_le_self hδ.le
  obtain ⟨c, hc, N0, hcount⟩ := hnum θ hθ
  have hden : 0 < 1 - θ := sub_pos.mpr hθ1
  have hratio : (δ - θ) / (1 - θ) = θ / (1 - θ) := by rw [hθdef]; ring
  have hκ : 0 < c * (θ / (1 - θ)) := mul_pos hc (div_pos hθ hden)
  have hev : ∀ᶠ N in atTop, c * (θ / (1 - θ)) ≤ progressionReturnAverage μ T A L N := by
    filter_upwards [eventually_ge_atTop (max N0 1)] with N hN
    have havg := progressionReturnAverage_ge hT hA hL hθ hθ1 hθδ hc hcount hN
    rw [hratio] at havg
    exact havg
  have hcob : IsCoboundedUnder (· ≥ ·) atTop (progressionReturnAverage μ T A L) :=
    isCoboundedUnder_ge_of_eventually_le atTop
      (Eventually.of_forall fun N => progressionReturnAverage_le_one T A L N)
  have hlim : c * (θ / (1 - θ)) ≤ liminf (progressionReturnAverage μ T A L) atTop :=
    le_liminf_of_le hcob hev
  unfold progressionReturnAverage at hlim
  exact lt_of_lt_of_le hκ hlim

end CKMA
