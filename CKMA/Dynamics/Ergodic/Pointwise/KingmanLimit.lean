/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Ergodic.Pointwise.KingmanAE

import CKMA.Dynamics.Ergodic.Pointwise.KingmanOrbit
import CKMA.Dynamics.Ergodic.Pointwise.Kingman
import CKMA.Dynamics.Ergodic.Pointwise.Maximal
import Mathlib.MeasureTheory.Integral.DominatedConvergence

import Mathlib.Tactic

/-!
# Integral of the Kingman liminf

Under a linear pointwise lower bound, the Avila–Bochi comparison integrates to the Fekete
infimum, so the integrable liminf has that mean.

## Main definitions

* `CKMA.HasKingmanExcursion`: predicate that a site has an excursion below the slope on `1, …, k`.
* `CKMA.kingmanCompare`: comparison value (the slope on an excursion, and one step otherwise).
* `CKMA.kingmanMajor`: tail majorant of the comparison value and the one-step increment.

## Main results

* `CKMA.kingmanLiminfReal_integral_eq`: the liminf has integral equal to the Fekete infimum.
-/

public section

noncomputable section

namespace CKMA

open Set MeasureTheory Filter Topology Finset
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

attribute [local instance] Classical.propDecidable

/-- A site has an excursion when some positive length at most `k` lies below the slope. -/
@[expose]
def HasKingmanExcursion (f : ℕ → Ω → ℝ) (slope : Ω → ℝ) (k : ℕ) (ω : Ω) : Prop :=
  ∃ j, 0 < j ∧ j ≤ k ∧ f j ω < (j : ℝ) * slope ω

@[deprecated (since := "2026-11-15")] alias kingmanExcursion := HasKingmanExcursion

/-- Comparison value: the slope on an excursion, and one step otherwise. -/
@[expose]
def kingmanCompare (f : ℕ → Ω → ℝ) (slope : Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if HasKingmanExcursion f slope k ω then slope ω else f 1 ω

/-- Tail majorant of the comparison value and the one-step increment. -/
@[expose]
def kingmanMajor (f : ℕ → Ω → ℝ) (slope : Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  max (kingmanCompare f slope k ω) (f 1 ω)

/-- Excursion sets of a measurable cocycle and a measurable slope are measurable. -/
lemma measurableSet_hasKingmanExcursion {f : ℕ → Ω → ℝ} {slope : Ω → ℝ} {k : ℕ}
    (hf : ∀ j : ℕ, 0 < j → Measurable (f j)) (hs : Measurable slope) :
    MeasurableSet {ω | HasKingmanExcursion f slope k ω} := by
  have hunion : {ω | HasKingmanExcursion f slope k ω} =
      ⋃ j : ℕ, {ω | 0 < j ∧ j ≤ k ∧ f j ω < (j : ℝ) * slope ω} := by
    ext ω
    simp [HasKingmanExcursion]
  rw [hunion]
  refine MeasurableSet.iUnion fun j => ?_
  by_cases hj : 0 < j ∧ j ≤ k
  · simp only [hj, true_and]
    exact measurableSet_lt (hf j hj.1) (hs.const_mul (j : ℝ))
  · have hempty : {ω | 0 < j ∧ j ≤ k ∧ f j ω < (j : ℝ) * slope ω} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hj0, hjk, -⟩
      exact hj ⟨hj0, hjk⟩
    rw [hempty]
    exact MeasurableSet.empty

@[deprecated (since := "2026-11-15")]
alias measurableSet_kingmanExcursion := measurableSet_hasKingmanExcursion

/-- The comparison function is measurable. -/
private lemma measurable_kingmanCompare {f : ℕ → Ω → ℝ} {slope : Ω → ℝ} {k : ℕ}
    (hf : ∀ j : ℕ, 0 < j → Measurable (f j)) (hs : Measurable slope) :
    Measurable (kingmanCompare f slope k) := by
  unfold kingmanCompare
  exact Measurable.ite (measurableSet_hasKingmanExcursion hf hs) hs (hf 1 Nat.one_pos)

/-- The tail majorant is measurable. -/
private lemma measurable_kingmanMajor {f : ℕ → Ω → ℝ} {slope : Ω → ℝ} {k : ℕ}
    (hf : ∀ j : ℕ, 0 < j → Measurable (f j)) (hs : Measurable slope) :
    Measurable (kingmanMajor f slope k) := by
  unfold kingmanMajor
  have hpair : Measurable fun ω => (kingmanCompare f slope k ω, f 1 ω) :=
    (measurable_kingmanCompare hf hs).prodMk (hf 1 Nat.one_pos)
  exact continuous_max.measurable.comp hpair

omit [MeasurableSpace Ω] in
/-- A constant slope along one orbit reproduces the deterministic window bound. -/
private lemma kingman_orbit_compare_le {f : ℕ → Ω → ℝ} {slope : ℝ} {k n : ℕ} {ω : Ω}
    (hsub : ∀ i a b : ℕ, 0 < a → 0 < b →
      f (a + b) ((T^[i]) ω) ≤ f a ((T^[i]) ω) + f b ((T^[i + a]) ω))
    (hk : 0 < k) (hn : k ≤ n) :
    f n ω ≤
      ∑ i ∈ range (n - k), kingmanCompare f (fun _ : Ω => slope) k ((T^[i]) ω) +
        ∑ i ∈ Ico (n - k) n, kingmanMajor f (fun _ : Ω => slope) k ((T^[i]) ω) := by
  let u : ℕ → ℕ → ℝ := fun i t => f t ((T^[i]) ω)
  have hsubu : ∀ i a b, 0 < a → 0 < b → u i (a + b) ≤ u i a + u (i + a) b := by
    intro i a b ha hb
    have hiter : (T^[a]) ((T^[i]) ω) = (T^[i + a]) ω := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    simpa [u, hiter] using hsub i a b ha hb
  have hbound := kingman_orbit_bound hsubu hk slope n 0 hn
  have hpsi : ∀ i, kingmanPsi u slope k i =
      kingmanCompare f (fun _ : Ω => slope) k ((T^[i]) ω) := by
    intro i
    unfold kingmanPsi kingmanCompare
    have hiff : IsKingmanWindow u slope k i ↔
        HasKingmanExcursion f (fun _ : Ω => slope) k ((T^[i]) ω) := by
      simp [IsKingmanWindow, HasKingmanExcursion, u]
    by_cases hwin : IsKingmanWindow u slope k i
    · have hexc : HasKingmanExcursion f (fun _ : Ω => slope) k ((T^[i]) ω) := hiff.mp hwin
      rw [ite_eq_left hwin, ite_eq_left hexc]
    · have hexc : ¬ HasKingmanExcursion f (fun _ : Ω => slope) k ((T^[i]) ω) :=
        fun h => hwin (hiff.mpr h)
      rw [ite_eq_right hwin, ite_eq_right hexc]
  have hmx : ∀ i, kingmanMx u slope k i =
      kingmanMajor f (fun _ : Ω => slope) k ((T^[i]) ω) := by
    intro i
    simp [kingmanMx, kingmanMajor, hpsi, u]
  have hleft : u 0 n = f n ω := by simp [u, Function.iterate_zero_apply]
  rw [hleft] at hbound
  have hsum1 : ∑ i ∈ range (n - k), kingmanPsi u slope k (0 + i) =
      ∑ i ∈ range (n - k), kingmanCompare f (fun _ : Ω => slope) k ((T^[i]) ω) := by
    refine sum_congr rfl fun i _ => ?_
    simpa [Nat.zero_add] using hpsi i
  have hsum2 : ∑ i ∈ Ico (n - k) n, kingmanMx u slope k (0 + i) =
      ∑ i ∈ Ico (n - k) n, kingmanMajor f (fun _ : Ω => slope) k ((T^[i]) ω) := by
    refine sum_congr rfl fun i _ => ?_
    simpa [Nat.zero_add] using hmx i
  rw [hsum1, hsum2] at hbound
  exact hbound

/-- Invariance propagates along almost every forward orbit. -/
private lemma kingmanLiminfReal_ae_const_orbit [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} {C : ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) :
    ∀ᵐ ω ∂μ, ∀ i, kingmanLiminfReal f ((T^[i]) ω) = kingmanLiminfReal f ω := by
  have hinv := kingmanLiminfReal_ae_invariant hT hf hf_meas hsub hC
  filter_upwards [ae_forall_iterate hT hinv] with ω hω
  intro i
  induction i with
  | zero => simp [Function.iterate_zero_apply]
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (hω i).trans ih

omit [MeasurableSpace Ω] in
/-- The comparison value is bounded by the slope plus the one-step increment. -/
private lemma abs_kingmanCompare_le (f : ℕ → Ω → ℝ) (slope : Ω → ℝ) (k : ℕ) (ω : Ω) :
    |kingmanCompare f slope k ω| ≤ |slope ω| + |f 1 ω| := by
  unfold kingmanCompare
  split_ifs
  · exact le_add_of_nonneg_right (abs_nonneg _)
  · exact le_add_of_nonneg_left (abs_nonneg _)

omit [MeasurableSpace Ω] in
/-- The tail majorant is bounded by the slope plus the one-step increment. -/
private lemma abs_kingmanMajor_le (f : ℕ → Ω → ℝ) (slope : Ω → ℝ) (k : ℕ) (ω : Ω) :
    |kingmanMajor f slope k ω| ≤ |slope ω| + |f 1 ω| :=
  abs_max_le_max_abs_abs.trans
    (max_le (abs_kingmanCompare_le f slope k ω) (le_add_of_nonneg_left (abs_nonneg _)))

/-- Under an integrable measurable slope, each comparison value is integrable. -/
private lemma integrable_kingmanCompare {f : ℕ → Ω → ℝ} {slope : Ω → ℝ}
    (hf1 : Integrable (f 1) μ) (hf_meas : ∀ j : ℕ, 0 < j → Measurable (f j))
    (hs : Integrable slope μ) (hs_meas : Measurable slope) (k : ℕ) :
    Integrable (kingmanCompare f slope k) μ := by
  have hdom : Integrable (fun ω => |slope ω| + |f 1 ω|) μ := hs.abs.add hf1.abs
  refine hdom.mono (measurable_kingmanCompare hf_meas hs_meas).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact (abs_kingmanCompare_le f slope k ω).trans (le_abs_self _)

/-- Under an integrable measurable slope, each tail majorant is integrable. -/
private lemma integrable_kingmanMajor {f : ℕ → Ω → ℝ} {slope : Ω → ℝ}
    (hf1 : Integrable (f 1) μ) (hf_meas : ∀ j : ℕ, 0 < j → Measurable (f j))
    (hs : Integrable slope μ) (hs_meas : Measurable slope) (k : ℕ) :
    Integrable (kingmanMajor f slope k) μ := by
  have hdom : Integrable (fun ω => |slope ω| + |f 1 ω|) μ := hs.abs.add hf1.abs
  refine hdom.mono (measurable_kingmanMajor hf_meas hs_meas).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact (abs_kingmanMajor_le f slope k ω).trans (le_abs_self _)

omit [MeasurableSpace Ω] in
/-- The comparison value at a site depends on the slope only through its value there. -/
private lemma kingmanCompare_congr_slope {f : ℕ → Ω → ℝ} {s s' : Ω → ℝ} {k : ℕ} {ω : Ω}
    (h : s ω = s' ω) : kingmanCompare f s k ω = kingmanCompare f s' k ω := by
  unfold kingmanCompare HasKingmanExcursion
  rw [h]

omit [MeasurableSpace Ω] in
/-- The tail majorant at a site depends on the slope only through its value there. -/
private lemma kingmanMajor_congr_slope {f : ℕ → Ω → ℝ} {s s' : Ω → ℝ} {k : ℕ} {ω : Ω}
    (h : s ω = s' ω) : kingmanMajor f s k ω = kingmanMajor f s' k ω := by
  unfold kingmanMajor
  rw [kingmanCompare_congr_slope h]

omit [MeasurableSpace Ω] in
/-- Where the extended liminf is the real liminf, some positive length lies strictly below
`ε` above the liminf slope. -/
private lemma exists_lt_mul_kingmanLiminfReal_add {f : ℕ → Ω → ℝ} {ω : Ω}
    (hω : kingmanLiminf f ω = (kingmanLiminfReal f ω : EReal)) {ε : ℝ} (hε : 0 < ε) :
    ∃ j, 0 < j ∧ f j ω < (j : ℝ) * (kingmanLiminfReal f ω + ε) := by
  have hlt : kingmanLiminf f ω < (kingmanLiminfReal f ω + ε : EReal) := by
    rw [hω]
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  have hfreq := frequently_lt_of_liminf_lt (f := atTop)
    (u := fun n => (kingmanRatio f n ω : EReal))
    (by
      unfold Filter.IsCoboundedUnder
      exact isCobounded_ge_of_top)
    (by simpa [kingmanLiminf] using hlt)
  obtain ⟨n, hn⟩ := hfreq.exists
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  have hreal : kingmanRatio f n ω < kingmanLiminfReal f ω + ε :=
    EReal.coe_lt_coe_iff.mp hn
  unfold kingmanRatio at hreal
  have hpos : (0 : ℝ) < n + 1 := by positivity
  have hmul := mul_lt_mul_of_pos_left hreal hpos
  have hnz : (n + 1 : ℝ) ≠ 0 := by positivity
  rw [mul_inv_cancel_left₀ hnz] at hmul
  have hcast : (n + 1 : ℝ) = ((n + 1 : ℕ) : ℝ) := by simp [Nat.cast_succ]
  rw [hcast] at hmul
  exact hmul

omit [MeasurableSpace Ω] in
/-- Along an orbit on which a slope is constant, the cocycle is bounded by the comparison
sums with that slope. -/
private lemma kingman_le_sum_compare_of_orbit {f : ℕ → Ω → ℝ} {slope : Ω → ℝ} {k n : ℕ}
    {ω : Ω} (hconst : ∀ i, slope ((T^[i]) ω) = slope ω)
    (hsub : ∀ i a b : ℕ, 0 < a → 0 < b →
      f (a + b) ((T^[i]) ω) ≤ f a ((T^[i]) ω) + f b ((T^[a]) ((T^[i]) ω)))
    (hk : 0 < k) (hn : k ≤ n) :
    f n ω ≤ ∑ i ∈ range (n - k), kingmanCompare f slope k ((T^[i]) ω) +
      ∑ i ∈ Finset.Ico (n - k) n, kingmanMajor f slope k ((T^[i]) ω) := by
  have hsub' : ∀ i a b : ℕ, 0 < a → 0 < b →
      f (a + b) ((T^[i]) ω) ≤ f a ((T^[i]) ω) + f b ((T^[i + a]) ω) :=
    fun i a b ha hb => by
      have hiter : (T^[a]) ((T^[i]) ω) = (T^[i + a]) ω := by
        simpa [Nat.add_comm] using (Function.iterate_add_apply T a i ω).symm
      simpa [hiter] using hsub i a b ha hb
  have horb := kingman_orbit_compare_le (ω := ω) (slope := slope ω) hsub' hk hn
  have h1 : ∀ i ∈ range (n - k), kingmanCompare f (fun _ : Ω => slope ω) k ((T^[i]) ω) =
      kingmanCompare f slope k ((T^[i]) ω) :=
    fun i _ => kingmanCompare_congr_slope (hconst i).symm
  have h2 : ∀ i ∈ Finset.Ico (n - k) n, kingmanMajor f (fun _ : Ω => slope ω) k ((T^[i]) ω) =
      kingmanMajor f slope k ((T^[i]) ω) :=
    fun i _ => kingmanMajor_congr_slope (hconst i).symm
  rwa [sum_congr rfl h1, sum_congr rfl h2] at horb

/-- Integrating an orbit comparison: if `g` is a.e. bounded by `n - k` iterates of `ψ` plus
the last `k` iterates of `m`, then its integral is at most `(n - k) ∫ ψ + k ∫ m`. -/
private lemma integral_le_of_le_sum_iterates (hT : MeasurePreserving T μ μ)
    {g ψ m : Ω → ℝ} {n k : ℕ} (hg : Integrable g μ) (hψ : Integrable ψ μ)
    (hm : Integrable m μ) (hn : k ≤ n)
    (hle : ∀ᵐ ω ∂μ, g ω ≤
      ∑ i ∈ range (n - k), ψ ((T^[i]) ω) + ∑ i ∈ Ico (n - k) n, m ((T^[i]) ω)) :
    ∫ ω, g ω ∂μ ≤ ((n - k : ℕ) : ℝ) * ∫ ω, ψ ω ∂μ + (k : ℝ) * ∫ ω, m ω ∂μ := by
  have hψi : ∀ i, Integrable (fun ω => ψ ((T^[i]) ω)) μ := fun i => by
    simpa [Function.comp_def] using (hT.iterate i).integrable_comp_of_integrable hψ
  have hmi : ∀ i, Integrable (fun ω => m ((T^[i]) ω)) μ := fun i => by
    simpa [Function.comp_def] using (hT.iterate i).integrable_comp_of_integrable hm
  have hψs : Integrable (fun ω => ∑ i ∈ range (n - k), ψ ((T^[i]) ω)) μ :=
    integrable_finsetSum _ fun i _ => hψi i
  have hms : Integrable (fun ω => ∑ i ∈ Ico (n - k) n, m ((T^[i]) ω)) μ :=
    integrable_finsetSum _ fun i _ => hmi i
  have hle' : g ≤ᵐ[μ] (fun ω => ∑ i ∈ range (n - k), ψ ((T^[i]) ω)) +
      fun ω => ∑ i ∈ Ico (n - k) n, m ((T^[i]) ω) := by
    filter_upwards [hle] with ω hω
    simpa [Pi.add_apply] using hω
  have hint := integral_mono_ae hg (hψs.add hms) hle'
  have hψint : ∫ ω, ∑ i ∈ range (n - k), ψ ((T^[i]) ω) ∂μ =
      ((n - k : ℕ) : ℝ) * ∫ ω, ψ ω ∂μ := by
    rw [integral_finsetSum _ fun i _ => hψi i]
    have hterm : ∀ i ∈ range (n - k), ∫ ω, ψ ((T^[i]) ω) ∂μ = ∫ ω, ψ ω ∂μ :=
      fun i _ => integral_comp_measurePreserving (hT.iterate i) hψ
    rw [sum_congr rfl hterm, sum_const, card_range, nsmul_eq_mul]
  have hmint : ∫ ω, ∑ i ∈ Ico (n - k) n, m ((T^[i]) ω) ∂μ = (k : ℝ) * ∫ ω, m ω ∂μ := by
    rw [integral_finsetSum _ fun i _ => hmi i]
    have hcard : (Finset.Ico (n - k) n).card = k := by
      rw [Nat.card_Ico]
      omega
    have hterm : ∀ i ∈ Finset.Ico (n - k) n, ∫ ω, m ((T^[i]) ω) ∂μ = ∫ ω, m ω ∂μ :=
      fun i _ => integral_comp_measurePreserving (hT.iterate i) hm
    rw [sum_congr rfl hterm, sum_const, hcard, nsmul_eq_mul]
  rw [integral_add' hψs hms, hψint, hmint] at hint
  exact hint

/-- The tail weight `k / (N + 1)` tends to zero. -/
private lemma tendsto_natCast_div_add_one_atTop (k : ℕ) :
    Tendsto (fun N : ℕ => (k : ℝ) / (N + 1 : ℝ)) atTop (𝓝 0) := by
  simpa [Function.comp_def] using
    (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ)).comp (tendsto_add_atTop_nat 1)

/-- The window weight `(N + 1 - k) / (N + 1)` tends to one. -/
private lemma tendsto_natSub_div_add_one_atTop (k : ℕ) :
    Tendsto (fun N : ℕ => ((N + 1 - k : ℕ) : ℝ) / (N + 1 : ℝ)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun N : ℕ => 1 - (k : ℝ) / (N + 1 : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_natCast_div_add_one_atTop k)
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop k] with N hN
  have hnz : (N + 1 : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one, sub_div, div_self hnz]

/-- With a slope that is almost surely constant along orbits, the Fekete infimum is at most
the integral of each comparison value of positive window length. -/
private lemma sInf_le_integral_kingmanCompare [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) {f : ℕ → Ω → ℝ} {C : ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω)
    {slope : Ω → ℝ} (hs : Integrable slope μ) (hs_meas : Measurable slope)
    (hconst : ∀ᵐ ω ∂μ, ∀ i, slope ((T^[i]) ω) = slope ω) {k : ℕ} (hk : 0 < k) :
    sInf {a : ℝ | ∃ n : ℕ, 0 < n ∧ a = (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ} ≤
      ∫ ω, kingmanCompare f slope k ω ∂μ := by
  have hsuborb := ae_forall_iterate hT (kingman_ae_subadditive hsub)
  have hbound : ∀ n, k ≤ n → ∫ ω, f n ω ∂μ ≤
      ((n - k : ℕ) : ℝ) * ∫ ω, kingmanCompare f slope k ω ∂μ +
        (k : ℝ) * ∫ ω, kingmanMajor f slope k ω ∂μ := by
    intro n hn
    refine integral_le_of_le_sum_iterates hT (hf n (hk.trans_le hn))
      (integrable_kingmanCompare (hf 1 Nat.one_pos) hf_meas hs hs_meas k)
      (integrable_kingmanMajor (hf 1 Nat.one_pos) hf_meas hs hs_meas k) hn ?_
    filter_upwards [hconst, hsuborb] with ω hcω hsω
    exact kingman_le_sum_compare_of_orbit hcω hsω hk hn
  have hLHS := tendsto_kingmanIntegral_div hT hf hsub
    ⟨-C, fun n hn => kingman_integral_ge_of_pointwise hf hC hn⟩
  have hRHS : Tendsto (fun N : ℕ =>
      (((N + 1 - k : ℕ) : ℝ) / (N + 1 : ℝ)) * ∫ ω, kingmanCompare f slope k ω ∂μ +
        ((k : ℝ) / (N + 1 : ℝ)) * ∫ ω, kingmanMajor f slope k ω ∂μ) atTop
      (𝓝 (∫ ω, kingmanCompare f slope k ω ∂μ)) := by
    simpa using ((tendsto_natSub_div_add_one_atTop k).mul_const _).add
      ((tendsto_natCast_div_add_one_atTop k).mul_const _)
  refine le_of_tendsto_of_tendsto hLHS hRHS ?_
  filter_upwards [eventually_ge_atTop k] with N hN
  have hmul := mul_le_mul_of_nonneg_left (hbound (N + 1) (by omega))
    (by positivity : (0 : ℝ) ≤ (N + 1 : ℝ)⁻¹)
  calc _ ≤ _ := hmul
    _ = _ := by ring

/-- The liminf is integrable of mean equal to the Fekete infimum. -/
lemma kingmanLiminfReal_integral_eq [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} {C : ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) :
    ∫ ω, kingmanLiminfReal f ω ∂μ =
      sInf {a : ℝ | ∃ n : ℕ, 0 < n ∧ a = (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ} := by
  obtain ⟨hg_int, hle, hne, -⟩ := kingmanLiminfReal_integrable_le hT hf hf_meas hsub hC
  have hg_meas : Measurable (kingmanLiminfReal f) :=
    (measurable_kingmanLiminf hf_meas).ereal_toReal
  have hconst := kingmanLiminfReal_ae_const_orbit hT hf hf_meas hsub hC
  refine le_antisymm hle (le_of_forall_pos_le_add fun ε hε => ?_)
  -- Compare with the slope `liminf + ε`, which is constant along almost every orbit.
  let slope : Ω → ℝ := fun ω => kingmanLiminfReal f ω + ε
  have hs_int : Integrable slope μ := hg_int.add (integrable_const ε)
  have hs_meas : Measurable slope := hg_meas.add measurable_const
  have hsconst : ∀ᵐ ω ∂μ, ∀ i, slope ((T^[i]) ω) = slope ω := by
    filter_upwards [hconst] with ω hω i
    simp only [slope, hω i]
  -- As the window grows, almost every site has an excursion, so the comparison values
  -- converge to the slope.
  have hψ_lim : Tendsto (fun k => ∫ ω, kingmanCompare f slope k ω ∂μ) atTop
      (𝓝 (∫ ω, slope ω ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => |slope ω| + |f 1 ω|)
      (fun k => (measurable_kingmanCompare hf_meas hs_meas).aestronglyMeasurable)
      (hs_int.abs.add (hf 1 Nat.one_pos).abs)
      (fun k => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        exact abs_kingmanCompare_le f slope k ω) ?_
    filter_upwards [hne] with ω htop
    obtain ⟨j, hj0, hjlt⟩ := exists_lt_mul_kingmanLiminfReal_add (ω := ω)
      (EReal.coe_toReal htop (kingmanLiminf_ne_bot hC ω)).symm hε
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop j] with k hk
    have hex : HasKingmanExcursion f slope k ω := ⟨j, hj0, hk, hjlt⟩
    rw [kingmanCompare, ite_eq_left hex]
  have hint_slope : ∫ ω, slope ω ∂μ = ∫ ω, kingmanLiminfReal f ω ∂μ + ε := by
    simp only [slope]
    rw [integral_add hg_int (integrable_const ε), integral_const]
    simp [measureReal_def, IsProbabilityMeasure.measure_univ]
  rw [← hint_slope]
  refine le_of_tendsto_of_tendsto tendsto_const_nhds hψ_lim ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  exact sInf_le_integral_kingmanCompare hT hf hf_meas hsub hC hs_int hs_meas hsconst hk

end CKMA
