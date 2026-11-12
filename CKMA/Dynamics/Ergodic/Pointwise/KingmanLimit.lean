/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Ergodic.Pointwise.KingmanAE

import Mathlib.Tactic

/-!
# Integral of the Kingman liminf

Under a linear pointwise lower bound, the Avila–Bochi comparison integrates to the Fekete
infimum, so the integrable liminf has that mean.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Set MeasureTheory Filter Topology Finset
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

attribute [local instance] Classical.propDecidable

/-- A site has an excursion when some positive length at most `k` lies below the slope. -/
def kingmanExcursion (f : ℕ → Ω → ℝ) (slope : Ω → ℝ) (k : ℕ) (ω : Ω) : Prop :=
  ∃ j, 0 < j ∧ j ≤ k ∧ f j ω < (j : ℝ) * slope ω

/-- Comparison value: the slope on an excursion, and one step otherwise. -/
def kingmanCompare (f : ℕ → Ω → ℝ) (slope : Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if kingmanExcursion f slope k ω then slope ω else f 1 ω

/-- Tail majorant of the comparison value and the one-step increment. -/
def kingmanMajor (f : ℕ → Ω → ℝ) (slope : Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  max (kingmanCompare f slope k ω) (f 1 ω)

/-- Excursion sets of a measurable cocycle and a measurable slope are measurable. -/
lemma measurableSet_kingmanExcursion {f : ℕ → Ω → ℝ} {slope : Ω → ℝ} {k : ℕ}
    (hf : ∀ j : ℕ, 0 < j → Measurable (f j)) (hs : Measurable slope) :
    MeasurableSet {ω | kingmanExcursion f slope k ω} := by
  have hunion : {ω | kingmanExcursion f slope k ω} =
      ⋃ j : ℕ, {ω | 0 < j ∧ j ≤ k ∧ f j ω < (j : ℝ) * slope ω} := by
    ext ω
    simp [kingmanExcursion]
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

/-- The comparison function is measurable. -/
lemma measurable_kingmanCompare {f : ℕ → Ω → ℝ} {slope : Ω → ℝ} {k : ℕ}
    (hf : ∀ j : ℕ, 0 < j → Measurable (f j)) (hs : Measurable slope) :
    Measurable (kingmanCompare f slope k) := by
  unfold kingmanCompare
  exact Measurable.ite (measurableSet_kingmanExcursion hf hs) hs (hf 1 Nat.one_pos)

/-- The tail majorant is measurable. -/
lemma measurable_kingmanMajor {f : ℕ → Ω → ℝ} {slope : Ω → ℝ} {k : ℕ}
    (hf : ∀ j : ℕ, 0 < j → Measurable (f j)) (hs : Measurable slope) :
    Measurable (kingmanMajor f slope k) := by
  unfold kingmanMajor
  have hpair : Measurable fun ω => (kingmanCompare f slope k ω, f 1 ω) :=
    (measurable_kingmanCompare hf hs).prodMk (hf 1 Nat.one_pos)
  exact continuous_max.measurable.comp hpair

omit [MeasurableSpace Ω] in
/-- A constant slope along one orbit reproduces the deterministic window bound. -/
lemma kingman_orbit_compare_le {f : ℕ → Ω → ℝ} {slope : ℝ} {k n : ℕ} {ω : Ω}
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
    have hiff : kingmanWindow u slope k i ↔
        kingmanExcursion f (fun _ : Ω => slope) k ((T^[i]) ω) := by
      simp [kingmanWindow, kingmanExcursion, u]
    by_cases hwin : kingmanWindow u slope k i
    · have hexc : kingmanExcursion f (fun _ : Ω => slope) k ((T^[i]) ω) := hiff.mp hwin
      rw [ite_eq_left hwin, ite_eq_left hexc]
    · have hexc : ¬ kingmanExcursion f (fun _ : Ω => slope) k ((T^[i]) ω) :=
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
lemma kingmanLiminfReal_ae_const_orbit [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
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

/-- The liminf is integrable of mean equal to the Fekete infimum. -/
lemma kingmanLiminfReal_integral_eq [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} {C : ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) :
    ∫ ω, kingmanLiminfReal f ω ∂μ =
      sInf {a : ℝ | ∃ n : ℕ, 0 < n ∧ a = (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ} := by
  set L : ℝ := sInf {a : ℝ | ∃ n : ℕ, 0 < n ∧ a = (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ}
  obtain ⟨hg_int, hle, hne, -⟩ := kingmanLiminfReal_integrable_le hT hf hf_meas hsub hC
  have hg_meas : Measurable (kingmanLiminfReal f) :=
    (measurable_kingmanLiminf hf_meas).ereal_toReal
  have hconst := kingmanLiminfReal_ae_const_orbit hT hf hf_meas hsub hC
  have hsuborb := ae_forall_iterate hT (kingman_ae_subadditive hsub)
  have hcoe : ∀ᵐ ω ∂μ, kingmanLiminf f ω = (kingmanLiminfReal f ω : EReal) := by
    filter_upwards [hne] with ω htop
    exact (EReal.coe_toReal htop (kingmanLiminf_ne_bot hC ω)).symm
  suffices hge : L ≤ ∫ ω, kingmanLiminfReal f ω ∂μ by
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  let slope : Ω → ℝ := fun ω => kingmanLiminfReal f ω + ε
  let ψ : ℕ → Ω → ℝ := fun k => kingmanCompare f slope k
  let mx : ℕ → Ω → ℝ := fun k => kingmanMajor f slope k
  have hslope_meas : Measurable slope := hg_meas.add measurable_const
  have hψ_meas : ∀ k, Measurable (ψ k) := fun k =>
    measurable_kingmanCompare hf_meas hslope_meas
  have hmx_meas : ∀ k, Measurable (mx k) := fun k =>
    measurable_kingmanMajor hf_meas hslope_meas
  have hdom_int : Integrable (fun ω => |slope ω| + |f 1 ω|) μ :=
    (hg_int.add (integrable_const ε)).abs.add (hf 1 Nat.one_pos).abs
  have habsψ : ∀ k ω, |ψ k ω| ≤ |slope ω| + |f 1 ω| := by
    intro k ω
    by_cases hex : kingmanExcursion f slope k ω
    · unfold ψ
      rw [kingmanCompare, ite_eq_left hex]
      exact le_add_of_nonneg_right (abs_nonneg _)
    · unfold ψ
      rw [kingmanCompare, ite_eq_right hex]
      exact le_add_of_nonneg_left (abs_nonneg _)
  have habsmx : ∀ k ω, |mx k ω| ≤ |slope ω| + |f 1 ω| := by
    intro k ω
    by_cases hex : kingmanExcursion f slope k ω
    · unfold mx
      rw [kingmanMajor]
      have hcmp : kingmanCompare f slope k ω = slope ω := by
        unfold kingmanCompare
        rw [ite_eq_left hex]
      rw [hcmp]
      refine abs_le.mpr ⟨?_, ?_⟩
      · exact le_trans (neg_le_neg (le_add_of_nonneg_right (abs_nonneg (f 1 ω))))
          (le_trans (neg_abs_le (slope ω)) (le_max_left _ _))
      · exact max_le
          (le_trans (le_abs_self _) (le_add_of_nonneg_right (abs_nonneg _)))
          (le_trans (le_abs_self _) (le_add_of_nonneg_left (abs_nonneg _)))
    · unfold mx
      rw [kingmanMajor]
      have hcmp : kingmanCompare f slope k ω = f 1 ω := by
        unfold kingmanCompare
        rw [ite_eq_right hex]
      rw [hcmp, max_self]
      exact le_add_of_nonneg_left (abs_nonneg _)
  have hψ_int : ∀ k, Integrable (ψ k) μ := by
    intro k
    refine hdom_int.mono (hψ_meas k).aestronglyMeasurable ?_
    refine Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (habsψ k ω).trans (le_abs_self _)
  have hmx_int : ∀ k, Integrable (mx k) μ := by
    intro k
    refine hdom_int.mono (hmx_meas k).aestronglyMeasurable ?_
    refine Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (habsmx k ω).trans (le_abs_self _)
  have hcatch : ∀ᵐ ω ∂μ, ∃ j, 0 < j ∧
      f j ω < (j : ℝ) * (kingmanLiminfReal f ω + ε) := by
    filter_upwards [hcoe] with ω hω
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
  have hLk : ∀ k, 0 < k → L ≤ ∫ ω, ψ k ω ∂μ := by
    intro k hk
    have hineq_ae : ∀ n, k ≤ n → ∀ᵐ ω ∂μ, f n ω ≤
        ∑ i ∈ range (n - k), ψ k ((T^[i]) ω) +
          ∑ i ∈ Ico (n - k) n, mx k ((T^[i]) ω) := by
      intro n hn
      filter_upwards [hconst, hsuborb] with ω hconstω hsubω
      have hsub' : ∀ i a b : ℕ, 0 < a → 0 < b →
          f (a + b) ((T^[i]) ω) ≤ f a ((T^[i]) ω) + f b ((T^[i + a]) ω) :=
        fun i a b ha hb => by
          have hiter : (T^[a]) ((T^[i]) ω) = (T^[i + a]) ω := by
            simpa [Nat.add_comm] using (Function.iterate_add_apply T a i ω).symm
          simpa [hiter] using hsubω i a b ha hb
      have horb := kingman_orbit_compare_le (ω := ω) (slope := kingmanLiminfReal f ω + ε)
        hsub' hk hn
      have hterm : ∀ i, kingmanCompare f (fun _ : Ω => kingmanLiminfReal f ω + ε) k
          ((T^[i]) ω) = ψ k ((T^[i]) ω) := by
        intro i
        have hgs : kingmanLiminfReal f ((T^[i]) ω) = kingmanLiminfReal f ω := hconstω i
        unfold ψ kingmanCompare slope
        by_cases hex : kingmanExcursion f (fun _ : Ω => kingmanLiminfReal f ω + ε) k
            ((T^[i]) ω)
        · have hex' : kingmanExcursion f slope k ((T^[i]) ω) := by
            obtain ⟨j, hj0, hjk, hjlt⟩ := hex
            refine ⟨j, hj0, hjk, ?_⟩
            change f j ((T^[i]) ω) < (j : ℝ) * (kingmanLiminfReal f ((T^[i]) ω) + ε)
            rw [hgs]
            exact hjlt
          rw [ite_eq_left hex, ite_eq_left hex']
          rw [hgs]
        · have hex' : ¬ kingmanExcursion f slope k ((T^[i]) ω) := by
            intro hexv
            apply hex
            obtain ⟨j, hj0, hjk, hjlt⟩ := hexv
            refine ⟨j, hj0, hjk, ?_⟩
            change f j ((T^[i]) ω) <
              (j : ℝ) * (kingmanLiminfReal f ((T^[i]) ω) + ε) at hjlt
            rw [hgs] at hjlt
            exact hjlt
          rw [ite_eq_right hex, ite_eq_right hex']
      have hmaj : ∀ i, kingmanMajor f (fun _ : Ω => kingmanLiminfReal f ω + ε) k
          ((T^[i]) ω) = mx k ((T^[i]) ω) := by
        intro i
        have hcmp := hterm i
        unfold ψ at hcmp
        simp only [kingmanMajor, mx, hcmp]
      have hsum1 : ∑ i ∈ range (n - k),
          kingmanCompare f (fun _ : Ω => kingmanLiminfReal f ω + ε) k ((T^[i]) ω) =
          ∑ i ∈ range (n - k), ψ k ((T^[i]) ω) := by
        refine sum_congr rfl fun i _ => hterm i
      have hsum2 : ∑ i ∈ Ico (n - k) n,
          kingmanMajor f (fun _ : Ω => kingmanLiminfReal f ω + ε) k ((T^[i]) ω) =
          ∑ i ∈ Ico (n - k) n, mx k ((T^[i]) ω) := by
        refine sum_congr rfl fun i _ => hmaj i
      rw [hsum1, hsum2] at horb
      exact horb
    have hbound_n : ∀ n, k ≤ n → ∫ ω, f n ω ∂μ ≤
        ((n - k : ℕ) : ℝ) * ∫ ω, ψ k ω ∂μ + (k : ℝ) * ∫ ω, mx k ω ∂μ := by
      intro n hn
      have hnpos : 0 < n := lt_of_lt_of_le hk hn
      have hψi : ∀ i, Integrable (fun ω => ψ k ((T^[i]) ω)) μ := fun i => by
        simpa [Function.comp_def] using
          (hT.iterate i).integrable_comp_of_integrable (hψ_int k)
      have hmxi : ∀ i, Integrable (fun ω => mx k ((T^[i]) ω)) μ := fun i => by
        simpa [Function.comp_def] using
          (hT.iterate i).integrable_comp_of_integrable (hmx_int k)
      have hψs : Integrable (fun ω => ∑ i ∈ range (n - k), ψ k ((T^[i]) ω)) μ :=
        integrable_finsetSum _ fun i _ => hψi i
      have hmxs : Integrable (fun ω => ∑ i ∈ Ico (n - k) n, mx k ((T^[i]) ω)) μ :=
        integrable_finsetSum _ fun i _ => hmxi i
      have hright := hψs.add hmxs
      have hle : (fun ω => f n ω) ≤ᵐ[μ]
          (fun ω => ∑ i ∈ range (n - k), ψ k ((T^[i]) ω)) +
            fun ω => ∑ i ∈ Ico (n - k) n, mx k ((T^[i]) ω) := by
        filter_upwards [hineq_ae n hn] with ω hω
        simpa [Pi.add_apply] using hω
      have hint := integral_mono_ae (hf n hnpos) hright hle
      have hψint : ∫ ω, ∑ i ∈ range (n - k), ψ k ((T^[i]) ω) ∂μ =
          ((n - k : ℕ) : ℝ) * ∫ ω, ψ k ω ∂μ := by
        rw [integral_finsetSum _ fun i _ => hψi i]
        have hterm : ∀ i ∈ range (n - k),
            ∫ ω, ψ k ((T^[i]) ω) ∂μ = ∫ ω, ψ k ω ∂μ :=
          fun i _ => integral_comp_measurePreserving (hT.iterate i) (hψ_int k)
        rw [sum_congr rfl hterm, sum_const, card_range, nsmul_eq_mul]
      have hmxint : ∫ ω, ∑ i ∈ Ico (n - k) n, mx k ((T^[i]) ω) ∂μ =
          (k : ℝ) * ∫ ω, mx k ω ∂μ := by
        rw [integral_finsetSum _ fun i _ => hmxi i]
        have hcard : (Finset.Ico (n - k) n).card = k := by
          rw [Nat.card_Ico]
          omega
        have hterm : ∀ i ∈ Finset.Ico (n - k) n,
            ∫ ω, mx k ((T^[i]) ω) ∂μ = ∫ ω, mx k ω ∂μ :=
          fun i _ => integral_comp_measurePreserving (hT.iterate i) (hmx_int k)
        rw [sum_congr rfl hterm, sum_const, hcard, nsmul_eq_mul]
      rw [integral_add' hψs hmxs, hψint, hmxint] at hint
      exact hint
    have hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ :=
      ⟨-C, fun n hn => kingman_integral_ge_of_pointwise hf hC hn⟩
    have hLHS := tendsto_kingmanIntegral_div hT hf hsub hlower
    have hcoeff : Tendsto (fun N : ℕ => ((N + 1 - k : ℕ) : ℝ) / (N + 1 : ℝ)) atTop (𝓝 1) := by
      have hden : Tendsto (fun N : ℕ => (N + 1 : ℝ)) atTop atTop := by
        have heq : (fun N : ℕ => (N + 1 : ℝ)) = fun N => ((N + 1 : ℕ) : ℝ) := by
          ext N
          simp
        rw [heq]
        exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
      have hinv : Tendsto (fun N : ℕ => (N + 1 : ℝ)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hden
      have hsubtr : Tendsto (fun N : ℕ => (k : ℝ) * (N + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
        simpa using hinv.const_mul (k : ℝ)
      have hform : ∀ N, k ≤ N + 1 → ((N + 1 - k : ℕ) : ℝ) / (N + 1 : ℝ) =
          1 - (k : ℝ) * (N + 1 : ℝ)⁻¹ := by
        intro N hNk
        have hcast : ((N + 1 - k : ℕ) : ℝ) = (N + 1 : ℝ) - (k : ℝ) := by
          rw [Nat.cast_sub hNk]
          simp [Nat.cast_succ]
        have hnz : (N + 1 : ℝ) ≠ 0 := by positivity
        calc
          ((N + 1 - k : ℕ) : ℝ) / (N + 1 : ℝ)
              = ((N + 1 : ℝ) - (k : ℝ)) * (N + 1 : ℝ)⁻¹ := by
                rw [hcast, div_eq_mul_inv]
          _ = (N + 1 : ℝ) * (N + 1 : ℝ)⁻¹ - (k : ℝ) * (N + 1 : ℝ)⁻¹ := by
                rw [sub_mul]
          _ = 1 - (k : ℝ) * (N + 1 : ℝ)⁻¹ := by
                rw [mul_inv_cancel₀ hnz]
      have htend : Tendsto (fun N : ℕ => 1 - (k : ℝ) * (N + 1 : ℝ)⁻¹) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.sub hsubtr
      refine htend.congr' ?_
      filter_upwards [eventually_ge_atTop k] with N hN
      exact (hform N (by omega)).symm
    have htail : Tendsto (fun N : ℕ => (k : ℝ) / (N + 1 : ℝ)) atTop (𝓝 0) := by
      have hden : Tendsto (fun N : ℕ => (N + 1 : ℝ)) atTop atTop := by
        have heq : (fun N : ℕ => (N + 1 : ℝ)) = fun N => ((N + 1 : ℕ) : ℝ) := by
          ext N
          simp
        rw [heq]
        exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
      simpa [div_eq_mul_inv] using
        (tendsto_inv_atTop_zero.comp hden).const_mul (k : ℝ)
    have hRHSgoal : Tendsto (fun N : ℕ =>
        (((N + 1 - k : ℕ) : ℝ) / (N + 1 : ℝ)) * ∫ ω, ψ k ω ∂μ +
          ((k : ℝ) / (N + 1 : ℝ)) * ∫ ω, mx k ω ∂μ) atTop
        (𝓝 (∫ ω, ψ k ω ∂μ)) := by
      have hmul1 := hcoeff.mul (tendsto_const_nhds (x := ∫ ω, ψ k ω ∂μ))
      have hmul2 := htail.mul (tendsto_const_nhds (x := ∫ ω, mx k ω ∂μ))
      simpa [one_mul, zero_mul, add_zero] using hmul1.add hmul2
    refine le_of_tendsto_of_tendsto (by simpa [L] using hLHS) hRHSgoal ?_
    filter_upwards [eventually_ge_atTop k] with N hN
    have hn : k ≤ N + 1 := by omega
    have hdiv := hbound_n (N + 1) hn
    have hpos : (0 : ℝ) ≤ (N + 1 : ℝ)⁻¹ := by positivity
    have hmul := mul_le_mul_of_nonneg_left hdiv hpos
    have hleft : (N + 1 : ℝ)⁻¹ *
        (((N + 1 - k : ℕ) : ℝ) * ∫ ω, ψ k ω ∂μ + (k : ℝ) * ∫ ω, mx k ω ∂μ) =
        (((N + 1 - k : ℕ) : ℝ) / (N + 1 : ℝ)) * ∫ ω, ψ k ω ∂μ +
          ((k : ℝ) / (N + 1 : ℝ)) * ∫ ω, mx k ω ∂μ := by
      have ha : ((N + 1 - k : ℕ) : ℝ) / (N + 1 : ℝ) =
          (N + 1 : ℝ)⁻¹ * ((N + 1 - k : ℕ) : ℝ) := by
        rw [div_eq_mul_inv, mul_comm]
      have hb : (k : ℝ) / (N + 1 : ℝ) = (N + 1 : ℝ)⁻¹ * (k : ℝ) := by
        rw [div_eq_mul_inv, mul_comm]
      rw [ha, hb, mul_add, ← mul_assoc, ← mul_assoc]
    rw [hleft] at hmul
    exact hmul
  have hψ_lim : Tendsto (fun k => ∫ ω, ψ k ω ∂μ) atTop
      (𝓝 (∫ ω, kingmanLiminfReal f ω + ε ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => |slope ω| + |f 1 ω|)
      (fun k => (hψ_meas k).aestronglyMeasurable) hdom_int (fun k => Eventually.of_forall
        fun ω => by
          rw [Real.norm_eq_abs]
          exact habsψ k ω) ?_
    filter_upwards [hcatch] with ω ⟨j, hj0, hjlt⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop j] with k hk
    have hex : kingmanExcursion f slope k ω := by
      refine ⟨j, hj0, hk, ?_⟩
      simpa only [slope] using hjlt
    unfold ψ
    rw [kingmanCompare, ite_eq_left hex]
  have hint_add : ∫ ω, kingmanLiminfReal f ω + ε ∂μ =
      ∫ ω, kingmanLiminfReal f ω ∂μ + ε := by
    rw [integral_add hg_int (integrable_const ε), integral_const]
    simp [measureReal_def, IsProbabilityMeasure.measure_univ]
  have hlim : L ≤ ∫ ω, kingmanLiminfReal f ω + ε ∂μ := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hψ_lim ?_
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact hLk k hk
  simpa [hint_add] using hlim

end CKMA
