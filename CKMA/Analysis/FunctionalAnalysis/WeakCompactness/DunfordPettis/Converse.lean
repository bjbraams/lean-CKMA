/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.FunctionalAnalysis.WeakCompactness.DunfordPettis
public import CKMA.Analysis.FunctionalAnalysis.WeakCompactness.EberleinSmulian
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Range
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.Order.OrderClosed

import Mathlib.Tactic.Choose
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Dunford–Pettis, converse

On a finite measure space, a relatively weakly compact subset of scalar `L¹` is uniformly
integrable. The space of measurable sets, with distance `μ (s ∆ t)`, is a complete pseudometric
space. Set integrals of a weakly convergent sequence are continuous for that distance, so the
Vitali–Hahn–Saks argument and the Baire property give uniform absolute continuity of the signed
integrals. A decomposition into sign sets of the real and imaginary parts upgrades the estimate to
the integral of the norm. Eberlein–Šmulian extracts a weakly convergent subsequence from any
sequence in a relatively weakly compact set.
-/

@[expose] public section

noncomputable section

open Bornology Filter Function Metric MeasureTheory Set Topology
open scoped ENNReal NNReal symmDiff

namespace CKMA.WeakCompactness

variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X]

/-- Failure of equivalence of membership puts the point in the symmetric difference. -/
theorem mem_symmDiff_of_not_iff {s t : Set X} {x : X} (h : ¬ (x ∈ s ↔ x ∈ t)) : x ∈ s ∆ t := by
  rw [mem_symmDiff]
  by_cases hx : x ∈ s
  · refine Or.inl ⟨hx, ?_⟩
    intro ht
    exact h ⟨fun _ ↦ ht, fun _ ↦ hx⟩
  · refine Or.inr ⟨?_, hx⟩
    by_contra hnot
    exact h (iff_of_false hx hnot)

/-- A change of membership between two indices occurs at a consecutive symmetric difference. -/
theorem exists_mem_symmDiff_succ {A : ℕ → Set X} {x : X} {n N : ℕ} (hn : n ≤ N)
    (hne : ¬ (x ∈ A n ↔ x ∈ A N)) : ∃ k, n ≤ k ∧ k < N ∧ x ∈ A k ∆ A (k + 1) := by
  induction N generalizing n with
  | zero =>
    obtain rfl : n = 0 := Nat.eq_zero_of_le_zero hn
    exact (hne Iff.rfl).elim
  | succ N ih =>
    have hnle : n ≤ N := by
      by_contra hlt
      have hnEq : n = N + 1 := by omega
      subst hnEq
      exact hne Iff.rfl
    by_cases hstep : x ∈ A N ↔ x ∈ A (N + 1)
    · have hne' : ¬ (x ∈ A n ↔ x ∈ A N) := by
        intro h
        exact hne (h.trans hstep)
      obtain ⟨k, hk, hkN, hx⟩ := ih hnle hne'
      exact ⟨k, hk, Nat.lt_succ_of_lt hkN, hx⟩
    · refine ⟨N, hnle, Nat.lt_succ_self N, mem_symmDiff_of_not_iff hstep⟩

/-- Membership in the liminf means membership in every sufficiently late set. -/
theorem mem_iUnion_iInter_add {A : ℕ → Set X} {x : X} :
    x ∈ ⋃ N, ⋂ k, A (k + N) ↔ ∃ N, ∀ k ≥ N, x ∈ A k := by
  constructor
  · intro hx
    simp only [mem_iUnion, mem_iInter] at hx
    obtain ⟨N, hN⟩ := hx
    refine ⟨N, fun k hk ↦ ?_⟩
    have hkEq : k = (k - N) + N := by omega
    rw [hkEq]
    exact hN (k - N)
  · rintro ⟨N, hN⟩
    simp only [mem_iUnion, mem_iInter]
    exact ⟨N, fun k ↦ hN (k + N) (Nat.le_add_left _ _)⟩

/-- Avoiding consecutive symmetric differences freezes membership. -/
theorem forall_mem_iff_base_of_not_mem_succDiff {A : ℕ → Set X} {x : X} {N : ℕ}
    (h : ∀ j, x ∉ A (j + N) ∆ A (j + N + 1)) {k : ℕ} (hk : N ≤ k) :
    x ∈ A k ↔ x ∈ A N := by
  have hiff : ∀ j, x ∈ A (j + N) ↔ x ∈ A (j + N + 1) := by
    intro j
    by_contra hne
    exact h j (mem_symmDiff_of_not_iff hne)
  have hbase : ∀ m, x ∈ A (m + N) ↔ x ∈ A N := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hidx : (m + 1) + N = m + N + 1 := by omega
      rw [hidx]
      exact (hiff m).symm.trans ih
  have hkEq : k = (k - N) + N := by omega
  rw [hkEq]
  exact hbase (k - N)

/-- The symmetric difference of a set with the liminf is covered by later consecutive
differences, up to the limsup of those differences. -/
theorem symmDiff_liminf_subset_flip_union_limsup {A : ℕ → Set X} (n : ℕ) :
    A n ∆ (⋃ N, ⋂ k, A (k + N)) ⊆
      (⋃ k, A (k + n) ∆ A (k + n + 1)) ∪
        (⋂ N, ⋃ k, A (k + N) ∆ A (k + N + 1)) := by
  intro x hx
  by_cases hxZ : x ∈ ⋂ N, ⋃ k, A (k + N) ∆ A (k + N + 1)
  · exact Or.inr hxZ
  · have hxZ' : ∃ N, x ∉ ⋃ k, A (k + N) ∆ A (k + N + 1) := by
      simpa [mem_iInter] using hxZ
    obtain ⟨N0, hN0⟩ := hxZ'
    have hN0' : ∀ j, x ∉ A (j + N0) ∆ A (j + N0 + 1) := by
      simpa [mem_iUnion] using hN0
    have hconst {k : ℕ} (hk : N0 ≤ k) : x ∈ A k ↔ x ∈ A N0 :=
      forall_mem_iff_base_of_not_mem_succDiff hN0' hk
    have hxL : x ∈ ⋃ N, ⋂ k, A (k + N) ↔ x ∈ A N0 := by
      rw [mem_iUnion_iInter_add]
      constructor
      · intro ⟨N, hN⟩
        exact (hconst (le_max_right N N0)).1 (hN _ (le_max_left N N0))
      · intro hxN
        exact ⟨N0, fun k hk ↦ (hconst hk).2 hxN⟩
    have hne : ¬ (x ∈ A n ↔ x ∈ ⋃ N, ⋂ k, A (k + N)) := by
      rw [mem_symmDiff] at hx
      rcases hx with ⟨hxA, hxLnot⟩ | ⟨hxLmem, hxAnot⟩
      · intro h
        exact hxLnot (h.1 hxA)
      · intro h
        exact hxAnot (h.2 hxLmem)
    have hne' : ¬ (x ∈ A n ↔ x ∈ A N0) := by
      intro h
      exact hne (h.trans hxL.symm)
    have hnle : n ≤ N0 := by
      by_contra hlt
      exact hne' (hconst (le_of_not_ge hlt))
    obtain ⟨k, hk, hklt, hxk⟩ := exists_mem_symmDiff_succ hnle hne'
    refine Or.inl (mem_iUnion.mpr ⟨k - n, ?_⟩)
    rw [show (k - n) + n = k by omega]
    exact hxk

/-- A Cauchy sequence with a convergent subsequence converges. -/
theorem tendsto_of_cauchySeq_of_tendsto_comp {α : Type*} [PseudoMetricSpace α] {u : ℕ → α}
    (hu : CauchySeq u) {φ : ℕ → ℕ} (hφ : StrictMono φ) {a : α}
    (hsub : Tendsto (u ∘ φ) atTop (𝓝 a)) : Tendsto u atTop (𝓝 a) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N0, hN0⟩ := (Metric.cauchySeq_iff.mp hu) (ε / 2) (half_pos hε)
  rw [Metric.tendsto_atTop] at hsub
  obtain ⟨N1, hN1⟩ := hsub (ε / 2) (half_pos hε)
  refine ⟨N0, fun n hn ↦ ?_⟩
  let k := max N1 n
  have hkφ : N0 ≤ φ k := le_trans (le_trans hn (le_max_right N1 n)) (hφ.id_le k)
  calc dist (u n) a ≤ dist (u n) (u (φ k)) + dist (u (φ k)) a := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hN0 n hn (φ k) hkφ) (hN1 k (le_max_left _ _))
    _ = ε := by ring

/-- The tail of a geometric series of ratio one half. -/
theorem tsum_geometric_half_shift (N : ℕ) :
    ∑' k : ℕ, (1 / 2 : ℝ) ^ (k + N) = 2 * (1 / 2 : ℝ) ^ N := by
  have hs : Summable fun k : ℕ ↦ (1 / 2 : ℝ) ^ k := summable_geometric_two
  simp_rw [pow_add]
  rw [hs.tsum_mul_right, tsum_geometric_two]

variable {μ : Measure X}

/-- The empty set is a point of the space of measurable sets. -/
instance : Nonempty (MeasuredSets μ) := ⟨⟨∅, MeasurableSet.empty⟩⟩

/-- Measurable sets, at finite distance `μ (s ∆ t)`, form a complete pseudometric space. -/
instance [IsFiniteMeasure μ] : CompleteSpace (MeasuredSets μ) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  have hpos : ∀ n, 0 < (1 / 2 : ℝ) ^ n := fun _ ↦ by positivity
  let modulus : ℕ → ℕ := fun n ↦
    Classical.choose ((Metric.cauchySeq_iff.mp hu) ((1 / 2 : ℝ) ^ n) (hpos n))
  have hmod (n : ℕ) : ∀ m ≥ modulus n, ∀ k ≥ modulus n,
      dist (u m) (u k) < (1 / 2 : ℝ) ^ n :=
    Classical.choose_spec ((Metric.cauchySeq_iff.mp hu) ((1 / 2 : ℝ) ^ n) (hpos n))
  let φ : ℕ → ℕ := fun n ↦ (Finset.range (n + 1)).sup modulus + n
  have hφge (n : ℕ) : modulus n ≤ φ n := by
    have hmem : n ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_self n)
    have := Finset.le_sup (f := modulus) hmem
    dsimp [φ]
    omega
  have hφge' (n : ℕ) : modulus n ≤ φ (n + 1) := by
    have hmem : n ∈ Finset.range (n + 1 + 1) := Finset.mem_range.mpr (by omega)
    have := Finset.le_sup (f := modulus) hmem
    dsimp [φ]
    omega
  have hφsucc (n : ℕ) : φ n < φ (n + 1) := by
    have hsub : Finset.range (n + 1) ⊆ Finset.range (n + 1 + 1) :=
      Finset.range_mono (Nat.le_succ _)
    have hsup := Finset.sup_mono (f := modulus) hsub
    rw [Nat.lt_iff_add_one_le]
    dsimp [φ]
    calc (Finset.range (n + 1)).sup modulus + n + 1
        ≤ (Finset.range (n + 1 + 1)).sup modulus + n + 1 := by gcongr
      _ = (Finset.range (n + 1 + 1)).sup modulus + (n + 1) := by omega
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ hφsucc
  let A : ℕ → Set X := fun n ↦ (u (φ n) : Set X)
  have hA (n : ℕ) : MeasurableSet (A n) := (u (φ n)).2
  have hstep (k : ℕ) : μ.real (A k ∆ A (k + 1)) ≤ (1 / 2 : ℝ) ^ k := by
    have hlt := hmod k (φ k) (hφge k) (φ (k + 1)) (hφge' k)
    rw [MeasuredSets.dist_def] at hlt
    exact hlt.le
  let B : ℕ → Set X := fun N ↦ ⋃ k, A (k + N) ∆ A (k + N + 1)
  have hBmeas (N : ℕ) : MeasurableSet (B N) :=
    MeasurableSet.iUnion fun k ↦ (hA (k + N)).symmDiff (hA (k + N + 1))
  have hBreal (N : ℕ) : μ.real (B N) ≤ 2 * (1 / 2 : ℝ) ^ N := by
    have hμ : μ (B N) ≤ ∑' k, μ (A (k + N) ∆ A (k + N + 1)) := measure_iUnion_le _
    have hterm (k : ℕ) : μ (A (k + N) ∆ A (k + N + 1)) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + N)) := by
      rw [← ofReal_measureReal (μ := μ) (s := A (k + N) ∆ A (k + N + 1))]
      exact ENNReal.ofReal_le_ofReal (hstep (k + N))
    have hsumle : ∑' k, μ (A (k + N) ∆ A (k + N + 1)) ≤
        ∑' k, ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + N)) :=
      ENNReal.tsum_le_tsum hterm
    have hsumm : Summable fun k : ℕ ↦ (1 / 2 : ℝ) ^ (k + N) := by
      simp_rw [pow_add]
      exact summable_geometric_two.mul_right ((1 / 2 : ℝ) ^ N)
    have hne : ∑' k, ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + N)) ≠ ∞ :=
      Summable.tsum_ofReal_ne_top hsumm
    have hto : (μ (B N)).toReal ≤
        (∑' k, ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + N))).toReal :=
      ENNReal.toReal_mono hne (hμ.trans hsumle)
    have htsum : (∑' k, ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + N))).toReal =
        ∑' k, (1 / 2 : ℝ) ^ (k + N) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hsumm,
        ENNReal.toReal_ofReal (tsum_nonneg fun _ ↦ by positivity)]
    rw [← measureReal_def, htsum, tsum_geometric_half_shift] at hto
    exact hto
  have hanti : Antitone B := by
    intro N M hNM x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨k + (M - N), ?_⟩
    have h1 : k + (M - N) + N = k + M := by omega
    have h2 : k + (M - N) + N + 1 = k + M + 1 := by omega
    simpa [h1, h2] using hk
  let Z : Set X := ⋂ N, B N
  have hZ : μ Z = 0 := by
    have htend := tendsto_measure_iInter_atTop (s := B)
      (fun N ↦ (hBmeas N).nullMeasurableSet) hanti ⟨0, measure_ne_top μ (B 0)⟩
    have hreal : Tendsto (fun N ↦ μ.real (B N)) atTop (𝓝 0) := by
      refine squeeze_zero (fun _ ↦ measureReal_nonneg) hBreal ?_
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ))
        (by positivity) (by norm_num)).const_mul 2
    have hzero : Tendsto (fun N ↦ μ (B N)) atTop (𝓝 0) := by
      refine (tendsto_congr fun N ↦ (ofReal_measureReal (μ := μ) (s := B N)).symm).mpr ?_
      have hcomp :
          Tendsto (ENNReal.ofReal ∘ fun N ↦ μ.real (B N)) atTop (𝓝 (ENNReal.ofReal 0)) :=
        (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
      rw [ENNReal.ofReal_zero] at hcomp
      exact hcomp
    exact tendsto_nhds_unique htend hzero
  have hZreal : μ.real Z = 0 := by simp [Measure.real, hZ]
  let L : Set X := ⋃ N, ⋂ k, A (k + N)
  have hL : MeasurableSet L := MeasurableSet.iUnion fun N ↦ MeasurableSet.iInter fun k ↦ hA _
  have hsub (n : ℕ) : A n ∆ L ⊆ B n ∪ Z := by
    simpa [A, B, L, Z] using symmDiff_liminf_subset_flip_union_limsup (A := A) n
  let Lms : MeasuredSets μ := ⟨L, hL⟩
  have hsubseq : Tendsto (fun n ↦ u (φ n)) atTop (𝓝 Lms) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ))
      (by positivity) (by norm_num)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hpow.const_mul 2) ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [MeasuredSets.dist_def]
    have hlt : 2 * (1 / 2 : ℝ) ^ n < ε := by
      have hdist := hN n hn
      rw [Real.dist_eq, mul_zero, sub_zero] at hdist
      exact (abs_lt.mp hdist).2
    calc μ.real (A n ∆ L) ≤ μ.real (B n ∪ Z) := measureReal_mono (hsub n)
      _ ≤ μ.real (B n) + μ.real Z := measureReal_union_le _ _
      _ = μ.real (B n) := by simp [hZreal]
      _ ≤ 2 * (1 / 2 : ℝ) ^ n := hBreal n
      _ < ε := hlt
  exact ⟨Lms, tendsto_of_cauchySeq_of_tendsto_comp hu hφ hsubseq⟩

/-- The set integrals of an integrable function differ by at most the integral of the norm over
the symmetric difference. -/
theorem norm_setIntegral_sub_le {f : X → 𝕜} (hf : Integrable f μ) {s t : Set X}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ‖∫ x in s, f x ∂μ - ∫ x in t, f x ∂μ‖ ≤ ∫ x in s ∆ t, ‖f x‖ ∂μ := by
  have hs' : ∫ x in s, f x ∂μ = ∫ x in s ∩ t, f x ∂μ + ∫ x in s \ t, f x ∂μ :=
    (integral_inter_add_sdiff ht hf.integrableOn).symm
  have ht' : ∫ x in t, f x ∂μ = ∫ x in t ∩ s, f x ∂μ + ∫ x in t \ s, f x ∂μ :=
    (integral_inter_add_sdiff hs hf.integrableOn).symm
  have hsub : ∫ x in s, f x ∂μ - ∫ x in t, f x ∂μ =
      ∫ x in s \ t, f x ∂μ - ∫ x in t \ s, f x ∂μ := by
    rw [hs', ht', inter_comm]
    ring
  rw [hsub]
  refine le_trans (norm_sub_le _ _) ?_
  have hst : ‖∫ x in s \ t, f x ∂μ‖ ≤ ∫ x in s \ t, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
  have hts : ‖∫ x in t \ s, f x ∂μ‖ ≤ ∫ x in t \ s, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
  refine le_trans (add_le_add hst hts) ?_
  have hun : (s \ t) ∪ (t \ s) = s ∆ t := by rw [Set.symmDiff_def]
  rw [← hun]
  exact (setIntegral_union disjoint_sdiff_sdiff (ht.diff hs) hf.norm.integrableOn
    hf.norm.integrableOn).symm.le

/-- Set integration against an integrable scalar function is continuous on measurable sets. -/
theorem continuous_setIntegral [IsFiniteMeasure μ] {f : X → 𝕜} (hf : Integrable f μ) :
    Continuous (fun s : MeasuredSets μ ↦ ∫ x in (s : Set X), f x ∂μ) := by
  rw [Metric.continuous_iff]
  intro s ε hε
  obtain ⟨δ, hδ, hδf⟩ := (memLp_one_iff_integrable.mpr hf).eLpNorm_indicator_le (p := 1)
    le_rfl ENNReal.one_ne_top (ENNReal.ofReal_pos.mpr (half_pos hε))
  let δR : ℝ := if δ = ⊤ then 1 else δ.toReal
  have hδR : 0 < δR := by
    by_cases htop : δ = ⊤
    · simp [δR, htop]
    · simpa [δR, htop] using ENNReal.toReal_pos hδ.ne' htop
  refine ⟨δR, hδR, fun t ht ↦ ?_⟩
  rw [dist_eq_norm]
  let sym : Set X := (t : Set X) ∆ (s : Set X)
  have hsym : MeasurableSet sym := t.2.symmDiff s.2
  have hμ : μ sym ≤ δ := by
    by_cases htop : δ = ⊤
    · simp [htop]
    · rw [← ofReal_measureReal (μ := μ) (s := sym)]
      refine (ENNReal.ofReal_le_ofReal ?_).trans_eq (ENNReal.ofReal_toReal htop)
      have hdist : μ.real sym < δ.toReal := by
        simpa [MeasuredSets.dist_def, δR, htop] using ht
      exact hdist.le
  have hindic : eLpNorm (sym.indicator f) 1 μ ≤ ENNReal.ofReal (ε / 2) :=
    hδf sym hsym.nullMeasurableSet hμ
  have hint : ∫ x in sym, ‖f x‖ ∂μ ≤ ε / 2 := by
    have hnorm : ∀ x, ‖sym.indicator f x‖ = sym.indicator (fun y ↦ ‖f y‖) x := by
      intro x
      by_cases hx : x ∈ sym <;> simp [hx]
    rw [← integral_indicator hsym, ← funext hnorm]
    have hfInd : AEStronglyMeasurable (sym.indicator f) μ :=
      hf.aestronglyMeasurable.indicator hsym
    rw [integral_norm_eq_lintegral_enorm hfInd]
    have hto := ENNReal.toReal_mono ENNReal.ofReal_ne_top hindic
    rw [eLpNorm_one_eq_lintegral_enorm hfInd,
      ENNReal.toReal_ofReal (half_pos hε).le] at hto
    exact hto
  exact lt_of_le_of_lt ((norm_setIntegral_sub_le hf t.2 s.2).trans hint) (by linarith)

/-- Integration over a fixed measurable set, as a continuous linear functional on `L¹`. -/
def setIntegralCLM {μ : Measure X} {s : Set X} (hs : MeasurableSet s) :
    Lp 𝕜 1 μ →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ∫ x in s, (f : X → 𝕜) x ∂μ
      map_add' := fun f g ↦ by
        have hf : Integrable (f : X → 𝕜) μ := memLp_one_iff_integrable.mp (Lp.memLp f)
        have hg : Integrable (g : X → 𝕜) μ := memLp_one_iff_integrable.mp (Lp.memLp g)
        rw [setIntegral_congr_ae hs ((Lp.coeFn_add f g).mono fun _ hx _ ↦ hx)]
        exact integral_add hf.integrableOn hg.integrableOn
      map_smul' := fun c f ↦ by
        rw [setIntegral_congr_ae hs ((Lp.coeFn_smul c f).mono fun _ hx _ ↦ hx)]
        simpa using (integral_smul (μ := μ.restrict s) c (f : X → 𝕜)) }
    1
    (fun f ↦ by
      have hf : Integrable (f : X → 𝕜) μ := memLp_one_iff_integrable.mp (Lp.memLp f)
      rw [one_mul]
      calc ‖∫ x in s, (f : X → 𝕜) x ∂μ‖
          ≤ ∫ x in s, ‖(f : X → 𝕜) x‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ ∫ x, ‖(f : X → 𝕜) x‖ ∂μ :=
          setIntegral_le_integral hf.norm (Eventually.of_forall fun _ ↦ norm_nonneg _)
        _ = ‖f‖ := by
          rw [integral_norm_eq_lintegral_enorm (Lp.memLp f).aestronglyMeasurable, Lp.norm_def,
            eLpNorm_one_eq_lintegral_enorm (Lp.memLp f).aestronglyMeasurable])

/-- The scalar norm is at most the sum of the absolute real and imaginary parts. -/
theorem norm_le_abs_re_add_abs_im (z : 𝕜) : ‖z‖ ≤ |RCLike.re z| + |RCLike.im z| := by
  have hsq : ‖z‖ ^ 2 ≤ (|RCLike.re z| + |RCLike.im z|) ^ 2 := by
    rw [RCLike.norm_sq_eq_def]
    nlinarith [sq_abs (RCLike.re z), sq_abs (RCLike.im z), abs_nonneg (RCLike.re z),
      abs_nonneg (RCLike.im z)]
  exact le_of_sq_le_sq hsq (by positivity)

/-- The integral of the norm is controlled by signed integrals over measurable subsets. -/
theorem integral_norm_le_four_of_subset_bound {f : X → 𝕜} (hf : Integrable f μ) {E : Set X}
    (hE : MeasurableSet E) {η : ℝ}
    (hη : ∀ F, MeasurableSet F → F ⊆ E → ‖∫ x in F, f x ∂μ‖ ≤ η) :
    ∫ x in E, ‖f x‖ ∂μ ≤ 4 * η := by
  let g : X → 𝕜 := hf.aestronglyMeasurable.mk f
  have hg_sm : StronglyMeasurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk
  have hg_ae : f =ᵐ[μ] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg_int : Integrable g μ := (integrable_congr hg_ae).1 hf
  have hre_meas : Measurable fun x ↦ RCLike.re (g x) :=
    (RCLike.continuous_re.comp_stronglyMeasurable hg_sm).measurable
  have him_meas : Measurable fun x ↦ RCLike.im (g x) :=
    (RCLike.continuous_im.comp_stronglyMeasurable hg_sm).measurable
  let posRe : Set X := {x | 0 ≤ RCLike.re (g x)}
  let posIm : Set X := {x | 0 ≤ RCLike.im (g x)}
  have hposRe : MeasurableSet posRe := measurableSet_le measurable_const hre_meas
  have hposIm : MeasurableSet posIm := measurableSet_le measurable_const him_meas
  have hre_abs : Integrable (fun x ↦ |RCLike.re (g x)|) μ := by
    simpa [Real.norm_eq_abs] using (Integrable.re hg_int).norm
  have him_abs : Integrable (fun x ↦ |RCLike.im (g x)|) μ := by
    simpa [Real.norm_eq_abs] using (Integrable.im hg_int).norm
  have hpiece {φ : X → ℝ} (hφ : Measurable φ) (habs : Integrable (fun x ↦ |φ x|) μ)
      (hφint : Integrable φ μ) {pos : Set X} (hpos : MeasurableSet pos)
      (hpos_def : pos = {x | 0 ≤ φ x})
      (hbound : ∀ F, MeasurableSet F → F ⊆ E →
        |∫ x in F, φ x ∂μ| ≤ η) :
      ∫ x in E, |φ x| ∂μ ≤ 2 * η := by
    have hun : (E ∩ pos) ∪ (E ∩ posᶜ) = E := by simp [inter_union_compl]
    have hdis : Disjoint (E ∩ pos) (E ∩ posᶜ) := by
      rw [Set.disjoint_iff]
      intro x hx
      exact hx.2.2 hx.1.2
    have hsplit : ∫ x in E, |φ x| ∂μ =
        ∫ x in E ∩ pos, |φ x| ∂μ + ∫ x in E ∩ posᶜ, |φ x| ∂μ := by
      have hU := setIntegral_union hdis (hE.inter hpos.compl)
        habs.integrableOn habs.integrableOn
      rwa [hun] at hU
    have hpos_eq : ∫ x in E ∩ pos, |φ x| ∂μ = ∫ x in E ∩ pos, φ x ∂μ :=
      setIntegral_congr_fun (hE.inter hpos) fun x hx ↦ by
        have hx0 : 0 ≤ φ x := by simpa [hpos_def] using hx.2
        exact abs_of_nonneg hx0
    have hneg_eq : ∫ x in E ∩ posᶜ, |φ x| ∂μ = ∫ x in E ∩ posᶜ, -φ x ∂μ :=
      setIntegral_congr_fun (hE.inter hpos.compl) fun x hx ↦ by
        have hlt : φ x < 0 := by
          have hnot : ¬ 0 ≤ φ x := by simpa [hpos_def, mem_compl_iff] using hx.2
          exact lt_of_not_ge hnot
        exact abs_of_neg hlt
    have hpos_le : ∫ x in E ∩ pos, φ x ∂μ ≤ η := by
      have habs' : |∫ x in E ∩ pos, φ x ∂μ| ≤ η :=
        hbound _ (hE.inter hpos) inter_subset_left
      exact le_trans (le_abs_self _) habs'
    have hneg_le : ∫ x in E ∩ posᶜ, -φ x ∂μ ≤ η := by
      rw [integral_neg]
      have habs' : |∫ x in E ∩ posᶜ, φ x ∂μ| ≤ η :=
        hbound _ (hE.inter hpos.compl) inter_subset_left
      exact le_trans (neg_le_abs _) habs'
    calc ∫ x in E, |φ x| ∂μ
        = ∫ x in E ∩ pos, φ x ∂μ + ∫ x in E ∩ posᶜ, -φ x ∂μ := by rw [hsplit, hpos_eq, hneg_eq]
      _ ≤ η + η := add_le_add hpos_le hneg_le
      _ = 2 * η := by ring
  have hre_bound : ∀ F, MeasurableSet F → F ⊆ E →
      |∫ x in F, RCLike.re (g x) ∂μ| ≤ η := by
    intro F hF hFE
    rw [integral_re (μ := μ.restrict F) hg_int.integrableOn]
    have hint : ∫ x in F, g x ∂μ = ∫ x in F, f x ∂μ :=
      setIntegral_congr_ae hF (hg_ae.mono fun _ hx _ ↦ hx.symm)
    rw [hint]
    exact (RCLike.abs_re_le_norm _).trans (hη F hF hFE)
  have him_bound : ∀ F, MeasurableSet F → F ⊆ E →
      |∫ x in F, RCLike.im (g x) ∂μ| ≤ η := by
    intro F hF hFE
    rw [integral_im (μ := μ.restrict F) hg_int.integrableOn]
    have hint : ∫ x in F, g x ∂μ = ∫ x in F, f x ∂μ :=
      setIntegral_congr_ae hF (hg_ae.mono fun _ hx _ ↦ hx.symm)
    rw [hint]
    exact (RCLike.abs_im_le_norm _).trans (hη F hF hFE)
  have hre_le := hpiece hre_meas hre_abs (Integrable.re hg_int) hposRe rfl hre_bound
  have him_le := hpiece him_meas him_abs (Integrable.im hg_int) hposIm rfl him_bound
  have hnorm_eq : ∫ x in E, ‖f x‖ ∂μ = ∫ x in E, ‖g x‖ ∂μ :=
    setIntegral_congr_ae hE (hg_ae.mono fun _ hx _ ↦ congrArg norm hx)
  have hsum_int : Integrable (fun x ↦ |RCLike.re (g x)| + |RCLike.im (g x)|) μ :=
    hre_abs.add him_abs
  rw [hnorm_eq]
  calc ∫ x in E, ‖g x‖ ∂μ
      ≤ ∫ x in E, |RCLike.re (g x)| + |RCLike.im (g x)| ∂μ :=
        setIntegral_mono_on hg_int.norm.integrableOn hsum_int.integrableOn hE
          fun x _ ↦ norm_le_abs_re_add_abs_im (g x)
    _ = ∫ x in E, |RCLike.re (g x)| ∂μ + ∫ x in E, |RCLike.im (g x)| ∂μ :=
      integral_add hre_abs.integrableOn him_abs.integrableOn
    _ ≤ 2 * η + 2 * η := add_le_add hre_le him_le
    _ = 4 * η := by ring

/-- A weakly convergent sequence in scalar `L¹` has uniformly absolutely continuous integrals of
the norm. -/
theorem exists_forall_integral_norm_le_of_tendsto_toWeakSpace [IsFiniteMeasure μ]
    {u : ℕ → Lp 𝕜 1 μ} {x : Lp 𝕜 1 μ}
    (hu : Tendsto (fun n ↦ toWeakSpace 𝕜 (Lp 𝕜 1 μ) (u n)) atTop
      (𝓝 (toWeakSpace 𝕜 (Lp 𝕜 1 μ) x)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ n, ∀ E, MeasurableSet E → μ.real E < δ →
      ∫ a in E, ‖(u n : X → 𝕜) a‖ ∂μ ≤ ε := by
  let θ : ℝ := ε / 12
  have hθ : 0 < θ := by positivity
  let g : ℕ → MeasuredSets μ → 𝕜 := fun n t ↦ ∫ a in (t : Set X), (u n : X → 𝕜) a ∂μ
  have hg (n : ℕ) : Continuous (g n) :=
    continuous_setIntegral (memLp_one_iff_integrable.mp (Lp.memLp (u n)))
  let F : ℕ → Set (MeasuredSets μ) :=
    fun N ↦ {t | ∀ m ≥ N, ∀ n ≥ N, ‖g m t - g n t‖ ≤ θ}
  have hFclosed (N : ℕ) : IsClosed (F N) := by
    have hEq : F N = ⋂ p : {p : ℕ × ℕ // N ≤ p.1 ∧ N ≤ p.2},
        {t | ‖g p.1.1 t - g p.1.2 t‖ ≤ θ} := by
      ext t
      simp only [F, mem_iInter, mem_ofPred_eq]
      constructor
      · intro h p
        exact h p.1.1 p.2.1 p.1.2 p.2.2
      · intro h m hm n hn
        exact h ⟨(m, n), hm, hn⟩
    rw [hEq]
    refine isClosed_iInter fun p ↦ ?_
    exact isClosed_le (continuous_norm.comp ((hg p.1.1).sub (hg p.1.2))) continuous_const
  have hcover : ⋃ N, F N = univ := by
    ext t
    simp only [mem_iUnion, mem_univ, iff_true]
    have htend := EberleinSmulian.tendsto_eval_of_tendsto_toWeakSpace hu
      (setIntegralCLM (μ := μ) t.2)
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp htend.cauchySeq) θ hθ
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    rw [← dist_eq_norm]
    exact (hN m hm n hn).le
  obtain ⟨N, hNint⟩ := nonempty_interior_of_iUnion_of_closed hFclosed hcover
  obtain ⟨A, hA⟩ := hNint
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hA)
  have hcauchy {E : Set X} (hE : MeasurableSet E) (hμE : μ.real E < δ) {m n : ℕ}
      (hm : N ≤ m) (hn : N ≤ n) :
      ‖∫ a in E, (u m : X → 𝕜) a ∂μ - ∫ a in E, (u n : X → 𝕜) a ∂μ‖ ≤ 2 * θ := by
    let Bms : MeasuredSets μ := ⟨(A : Set X) ∪ E, A.2.union hE⟩
    let Cms : MeasuredSets μ := ⟨(A : Set X) \ E, A.2.diff hE⟩
    have hBdist : dist Bms A < δ := by
      rw [MeasuredSets.dist_def]
      have hEq : ((Bms : Set X) ∆ (A : Set X)) = E \ (A : Set X) := by
        ext y
        simp only [Bms, mem_symmDiff, Set.mem_sdiff]
        constructor
        · rintro (⟨hyB, hyA⟩ | ⟨hyA, hyB⟩)
          · rcases hyB with hyA' | hyE
            · exact absurd hyA' hyA
            · exact ⟨hyE, hyA⟩
          · exact absurd (Or.inl hyA) hyB
        · rintro ⟨hyE, hyA⟩
          exact Or.inl ⟨Or.inr hyE, hyA⟩
      rw [hEq]
      exact lt_of_le_of_lt (measureReal_mono (sdiff_subset : E \ (A : Set X) ⊆ E)) hμE
    have hCdist : dist Cms A < δ := by
      rw [MeasuredSets.dist_def]
      have hEq : ((Cms : Set X) ∆ (A : Set X)) = (A : Set X) ∩ E := by
        ext y
        simp only [Cms, mem_symmDiff, mem_inter_iff]
        constructor
        · rintro (⟨⟨hyA, hyEnot⟩, hyA'⟩ | ⟨hyA, hyC⟩)
          · exact absurd hyA hyA'
          · refine ⟨hyA, ?_⟩
            by_contra hyEnot
            exact hyC ⟨hyA, hyEnot⟩
        · rintro ⟨hyA, hyE⟩
          exact Or.inr ⟨hyA, fun h ↦ h.2 hyE⟩
      rw [hEq]
      exact lt_of_le_of_lt (measureReal_mono (inter_subset_right : (A : Set X) ∩ E ⊆ E)) hμE
    have hBmem : Bms ∈ F N := hball (mem_ball.mpr hBdist)
    have hCmem : Cms ∈ F N := hball (mem_ball.mpr hCdist)
    have hsplit (f : X → 𝕜) (hf : Integrable f μ) :
        ∫ a in (Bms : Set X), f a ∂μ - ∫ a in (Cms : Set X), f a ∂μ = ∫ a in E, f a ∂μ := by
      have hun : (Cms : Set X) ∪ E = (Bms : Set X) := by
        ext y
        simp only [Cms, Bms, mem_union]
        constructor
        · rintro (⟨hyA, _⟩ | hyE)
          · exact Or.inl hyA
          · exact Or.inr hyE
        · rintro (hyA | hyE)
          · by_cases hy : y ∈ E
            · exact Or.inr hy
            · exact Or.inl ⟨hyA, hy⟩
          · exact Or.inr hyE
      have hEq : ∫ a in (Bms : Set X), f a ∂μ =
          ∫ a in (Cms : Set X), f a ∂μ + ∫ a in E, f a ∂μ := by
        rw [← hun]
        exact setIntegral_union disjoint_sdiff_left hE hf.integrableOn hf.integrableOn
      rw [hEq]
      ring
    have hint (k : ℕ) : Integrable (u k : X → 𝕜) μ :=
      memLp_one_iff_integrable.mp (Lp.memLp (u k))
    have hsub : ∫ a in E, (u m : X → 𝕜) a ∂μ - ∫ a in E, (u n : X → 𝕜) a ∂μ =
        (g m Bms - g n Bms) - (g m Cms - g n Cms) := by
      have hm := hsplit (u m : X → 𝕜) (hint m)
      have hn' := hsplit (u n : X → 𝕜) (hint n)
      rw [← hm, ← hn']
      ring
    rw [hsub]
    calc ‖(g m Bms - g n Bms) - (g m Cms - g n Cms)‖
        ≤ ‖g m Bms - g n Bms‖ + ‖g m Cms - g n Cms‖ := norm_sub_le _ _
      _ ≤ θ + θ := add_le_add (hBmem m hm n hn) (hCmem m hm n hn)
      _ = 2 * θ := by ring
  let v : Fin (N + 1) → X → 𝕜 := fun i ↦ (u i.1 : X → 𝕜)
  have hv (i : Fin (N + 1)) : MemLp (v i) 1 μ := Lp.memLp (u i.1)
  have hfin := unifIntegrable_finite (p := (1 : ℝ≥0∞)) (μ := μ) le_rfl ENNReal.one_ne_top hv
  obtain ⟨δE, hδE, hδEi⟩ := (unifIntegrable_iff'.mp hfin) (ENNReal.ofReal θ)
    (ENNReal.ofReal_pos.mpr hθ)
  let δR : ℝ := min δ (if δE = ⊤ then δ else δE.toReal)
  have hδR : 0 < δR := by
    by_cases htop : δE = ⊤
    · simp [δR, htop, hδ]
    · have hto : 0 < δE.toReal := ENNReal.toReal_pos hδE.ne' htop
      have hmin : 0 < min δ δE.toReal := lt_min hδ hto
      simpa [δR, htop] using hmin
  refine ⟨δR, hδR, fun n E hE hμE ↦ ?_⟩
  have hballμ : μ.real E < δ := lt_of_lt_of_le hμE (min_le_left _ _)
  have hennF (F : Set X) (hFE : F ⊆ E) : μ F ≤ δE := by
    by_cases htop : δE = ⊤
    · simp [htop]
    · rw [← ofReal_measureReal (μ := μ) (s := F)]
      refine (ENNReal.ofReal_le_ofReal ?_).trans_eq (ENNReal.ofReal_toReal htop)
      have hmin : δR ≤ δE.toReal := by simp [δR, htop]
      exact (lt_of_le_of_lt (measureReal_mono hFE) hμE).le.trans hmin
  have hsigned (F : Set X) (hF : MeasurableSet F) (hFE : F ⊆ E) :
      ‖∫ a in F, (u n : X → 𝕜) a ∂μ‖ ≤ 3 * θ := by
    have hsmall : μ.real F < δ :=
      lt_of_le_of_lt (measureReal_mono hFE) hballμ
    by_cases hn : n ≤ N
    · have hlp := hδEi ⟨n, Nat.lt_succ_of_le hn⟩ F hF (hennF F hFE)
      have hint_eq : ∫ a in F, ‖(u n : X → 𝕜) a‖ ∂μ =
          (eLpNorm (u n : X → 𝕜) 1 (μ.restrict F)).toReal := by
        rw [integral_norm_eq_lintegral_enorm
            (Lp.memLp (u n)).aestronglyMeasurable.restrict,
          eLpNorm_one_eq_lintegral_enorm
            (Lp.memLp (u n)).aestronglyMeasurable.restrict]
      have hto : (eLpNorm (u n : X → 𝕜) 1 (μ.restrict F)).toReal ≤ θ :=
        (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlp).trans_eq
          (ENNReal.toReal_ofReal hθ.le)
      calc ‖∫ a in F, (u n : X → 𝕜) a ∂μ‖
          ≤ ∫ a in F, ‖(u n : X → 𝕜) a‖ ∂μ := norm_integral_le_integral_norm _
        _ = (eLpNorm (u n : X → 𝕜) 1 (μ.restrict F)).toReal := hint_eq
        _ ≤ θ := hto
        _ ≤ 3 * θ := by nlinarith [hθ]
    · have hdiff := hcauchy hF hsmall (le_of_not_ge hn) (le_refl N)
      have hanchor : ‖∫ a in F, (u N : X → 𝕜) a ∂μ‖ ≤ θ := by
        have hlp := hδEi ⟨N, Nat.lt_succ_self N⟩ F hF (hennF F hFE)
        have hint_eq : ∫ a in F, ‖(u N : X → 𝕜) a‖ ∂μ =
            (eLpNorm (u N : X → 𝕜) 1 (μ.restrict F)).toReal := by
          rw [integral_norm_eq_lintegral_enorm
              (Lp.memLp (u N)).aestronglyMeasurable.restrict,
            eLpNorm_one_eq_lintegral_enorm
              (Lp.memLp (u N)).aestronglyMeasurable.restrict]
        have hto : (eLpNorm (u N : X → 𝕜) 1 (μ.restrict F)).toReal ≤ θ :=
          (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlp).trans_eq
            (ENNReal.toReal_ofReal hθ.le)
        exact (norm_integral_le_integral_norm _).trans (hint_eq.trans_le hto)
      calc ‖∫ a in F, (u n : X → 𝕜) a ∂μ‖
          = ‖(∫ a in F, (u n : X → 𝕜) a ∂μ -
                ∫ a in F, (u N : X → 𝕜) a ∂μ) +
                ∫ a in F, (u N : X → 𝕜) a ∂μ‖ := by rw [sub_add_cancel]
        _ ≤ ‖∫ a in F, (u n : X → 𝕜) a ∂μ -
              ∫ a in F, (u N : X → 𝕜) a ∂μ‖ +
            ‖∫ a in F, (u N : X → 𝕜) a ∂μ‖ := norm_add_le _ _
        _ ≤ 2 * θ + θ := add_le_add hdiff hanchor
        _ = 3 * θ := by ring
  have hfour := integral_norm_le_four_of_subset_bound
    (memLp_one_iff_integrable.mp (Lp.memLp (u n))) hE hsigned
  have hconst : 4 * (3 * θ) = ε := by
    dsimp [θ]
    ring
  simpa [hconst] using hfour

/-- Relative weak compactness in scalar `L¹` on a finite measure space yields uniform
integrability, including the uniform `L¹` bound. -/
theorem uniformIntegrable_of_isCompact_closure_toWeakSpace [IsFiniteMeasure μ]
    {s : Set (Lp 𝕜 1 μ)} (hs : IsCompact (closure (toWeakSpace 𝕜 (Lp 𝕜 1 μ) '' s))) :
    UniformIntegrable (fun f : s ↦ (f.1 : X → 𝕜)) 1 μ := by
  constructor
  · rw [unifIntegrable_iff']
    intro ε hε
    by_cases htop : ε = ⊤
    · exact ⟨1, zero_lt_one, fun _ _ _ _ ↦ by simp [htop]⟩
    have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
    by_contra hfail
    push Not at hfail
    have hseq : ∀ n : ℕ, ∃ i : s, ∃ t : Set X,
        MeasurableSet t ∧ μ t ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) ∧
          ε < eLpNorm (i.1 : X → 𝕜) 1 (μ.restrict t) :=
      fun n ↦ hfail (ENNReal.ofReal ((1 / 2 : ℝ) ^ n))
        (ENNReal.ofReal_pos.mpr (by positivity))
    choose idx t hspec using hseq
    let w : ℕ → Lp 𝕜 1 μ := fun n ↦ (idx n).1
    have hw : ∀ n, w n ∈ s := fun n ↦ (idx n).2
    obtain ⟨r, hr, x, hx⟩ :=
      EberleinSmulian.exists_subseq_of_isCompact_closure s hs w hw
    obtain ⟨δ, hδ, hctrl⟩ :=
      exists_forall_integral_norm_le_of_tendsto_toWeakSpace hx hεr
    obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ))
        (by positivity) (by norm_num)) δ hδ
    have hhalf : (1 / 2 : ℝ) ^ N0 < δ := by
      simpa [Real.dist_eq, sub_zero,
        abs_of_nonneg (pow_nonneg (by positivity) _)] using hN0 N0 le_rfl
    have hpow : (1 / 2 : ℝ) ^ (r N0) ≤ (1 / 2 : ℝ) ^ N0 :=
      pow_le_pow_of_le_one (by positivity) (by norm_num) (hr.id_le N0)
    have hμle : μ.real (t (r N0)) ≤ (1 / 2 : ℝ) ^ (r N0) := by
      have hmono :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hspec (r N0)).2.1
      simpa [Measure.real,
        ENNReal.toReal_ofReal (pow_nonneg (by positivity) _)] using hmono
    have hμlt : μ.real (t (r N0)) < δ := lt_of_le_of_lt (hμle.trans hpow) hhalf
    have hint := hctrl N0 (t (r N0)) (hspec (r N0)).1 hμlt
    have hf : Integrable (w (r N0) : X → 𝕜) (μ.restrict (t (r N0))) :=
      (memLp_one_iff_integrable.mp (Lp.memLp (w (r N0)))).integrableOn
    have hsm : AEStronglyMeasurable (w (r N0) : X → 𝕜)
        (μ.restrict (t (r N0))) :=
      (Lp.memLp (w (r N0))).aestronglyMeasurable.restrict
    have heq : eLpNorm (w (r N0) : X → 𝕜) 1 (μ.restrict (t (r N0))) =
        ENNReal.ofReal
          (∫ a in t (r N0), ‖(w (r N0) : X → 𝕜) a‖ ∂μ) := by
      rw [eLpNorm_one_eq_lintegral_enorm hsm,
        ← ofReal_integral_norm_eq_lintegral_enorm hf]
    have hle : eLpNorm (w (r N0) : X → 𝕜) 1 (μ.restrict (t (r N0))) ≤ ε := by
      rw [heq]
      exact (ENNReal.ofReal_le_ofReal hint).trans_eq (ENNReal.ofReal_toReal htop)
    exact (hspec (r N0)).2.2.not_ge hle
  · obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le).1
      (isBounded_of_isCompact_closure_toWeakSpace hs)
    refine ⟨Real.toNNReal C, fun i ↦ ?_⟩
    have hle : ‖i.1‖ ≤ C := hC i.1 i.2
    have hC0 : 0 ≤ C := (norm_nonneg _).trans hle
    have hcoe : (Real.toNNReal C : ℝ≥0∞) = ENNReal.ofReal C := by
      simp [hC0, Real.toNNReal_of_nonneg, ENNReal.ofReal_eq_coe_nnreal]
    rw [hcoe]
    exact (ENNReal.le_ofReal_iff_toReal_le (Lp.eLpNorm_ne_top i.1) hC0).2
      (by simpa [Lp.norm_def] using hle)

/-- **17.23**, Dunford–Pettis: on a finite measure space, relative weak compactness in scalar
`L¹` is uniform integrability, including the uniform `L¹` bound. -/
theorem dunford_pettis [IsFiniteMeasure μ] (s : Set (Lp 𝕜 1 μ)) :
    IsCompact (closure (toWeakSpace 𝕜 (Lp 𝕜 1 μ) '' s)) ↔
      UniformIntegrable (fun f : s ↦ (f.1 : X → 𝕜)) 1 μ := by
  constructor
  · exact fun hs ↦ uniformIntegrable_of_isCompact_closure_toWeakSpace hs
  · exact fun hUI ↦ isCompact_closure_toWeakSpace_of_uniformIntegrable hUI

end CKMA.WeakCompactness
