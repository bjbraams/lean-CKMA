/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Ergodic.Pointwise.Kingman
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Topology.Order.LiminfLimsup

import Mathlib.Tactic

/-!
# Almost-everywhere convergence in Kingman's theorem

Integrable cocycles are negligible along orbits. Under a linear pointwise lower bound the
Avila–Bochi estimate identifies the liminf, and Birkhoff's theorem along multiples controls the
limsup.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Set MeasureTheory Filter Topology Finset
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

attribute [local instance] Classical.propDecidable

/-- Positive-length normalized values, in the indexing of the subadditive theorem. -/
def kingmanRatio (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (n + 1 : ℝ)⁻¹ * f (n + 1) ω

/-- The extended liminf of the normalized subadditive process. -/
def kingmanLiminf (f : ℕ → Ω → ℝ) (ω : Ω) : EReal :=
  liminf (fun n => (kingmanRatio f n ω : EReal)) atTop

/-- The extended limsup of the normalized subadditive process. -/
def kingmanLimsup (f : ℕ → Ω → ℝ) (ω : Ω) : EReal :=
  limsup (fun n => (kingmanRatio f n ω : EReal)) atTop

/-- Tail measures of an integrable nonnegative function are summable. -/
lemma tsum_meas_ge_lt_top [IsProbabilityMeasure μ] {g : Ω → ℝ} (hg : Integrable g μ)
    (hg0 : ∀ ω, 0 ≤ g ω) (hg_meas : Measurable g) :
    (∑' n : ℕ, μ {ω | (n : ℝ) ≤ g ω}) < ⊤ := by
  let φ : ℝ → ℝ := fun t => μ.real {ω | t ≤ g ω}
  have hanti : Antitone φ := by
    intro s t hst
    exact ENNReal.toReal_mono (measure_ne_top μ _)
      (measure_mono fun ω hω => le_trans hst hω)
  have hcake := lintegral_eq_lintegral_meas_le (μ := μ) (f := g)
    (Eventually.of_forall hg0) hg_meas.aemeasurable
  have hfin : ∫⁻ ω, ENNReal.ofReal (g ω) ∂μ < ⊤ := by
    have hnorm : (fun ω => ENNReal.ofReal (g ω)) = fun ω => ‖g ω‖ₑ := by
      ext ω
      exact (Real.enorm_of_nonneg (hg0 ω)).symm
    rw [hnorm]
    exact hg.hasFiniteIntegral
  have hset : ∫⁻ t in Ioi (0 : ℝ), μ {ω | t ≤ g ω} < ⊤ := by
    rw [← hcake]
    exact hfin
  have hφ_int : IntegrableOn φ (Ioi 0) := by
    refine ⟨hanti.measurable.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt (lintegral_mono fun t => ?_) hset
    have hφt : φ t = ENNReal.toReal (μ {ω | t ≤ g ω}) := by
      simp [φ, measureReal_def]
    rw [hφt, Real.enorm_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (measure_ne_top μ _)]
  have hsummable : Summable fun n : ℕ => φ n := by
    refine AntitoneOn.summable_of_integrableOn_Ioi (N := 0)
      (fun s _ t _ hst => hanti hst) ?_ (fun _ _ => ENNReal.toReal_nonneg)
    simpa using hφ_int
  have hreal : (∑' n : ℕ, μ {ω | (n : ℝ) ≤ g ω}) =
      ∑' n : ℕ, ENNReal.ofReal (φ n) := by
    refine tsum_congr fun n => ?_
    simp [φ, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
  have htop : ∑' n : ℕ, ENNReal.ofReal (φ n) = ENNReal.ofReal (∑' n : ℕ, φ n) :=
    (ENNReal.ofReal_tsum_of_nonneg (fun _ => ENNReal.toReal_nonneg) hsummable).symm
  rw [hreal, htop]
  exact ENNReal.ofReal_lt_top

/-- An integrable observable is negligible along the orbit, after division by the time. -/
lemma tendsto_comp_iterate_div [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {g : Ω → ℝ} (hg : Integrable g μ) (hg_meas : Measurable g) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => g ((T^[n]) ω) / (n : ℝ)) atTop (𝓝 0) := by
  have htail : ∀ k : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      |g ((T^[n]) ω)| < (1 / (k + 1 : ℝ)) * n := by
    intro k
    let ε : ℝ := 1 / (k + 1 : ℝ)
    have hε : 0 < ε := by positivity
    let X : Ω → ℝ := fun ω => |g ω| / ε
    have hX0 : ∀ ω, 0 ≤ X ω := fun ω => div_nonneg (abs_nonneg _) hε.le
    have hX_int : Integrable X μ := hg.abs.div_const ε
    have hX_meas : Measurable X := (continuous_abs.measurable.comp hg_meas).div_const ε
    have hsum := tsum_meas_ge_lt_top hX_int hX0 hX_meas
    let s : ℕ → Set Ω := fun n => {ω | ε * (n : ℝ) ≤ |g ((T^[n]) ω)|}
    have hmeas_base : ∀ n : ℕ, MeasurableSet {ω | (n : ℝ) ≤ X ω} :=
      fun n => measurableSet_le measurable_const hX_meas
    have hpre : ∀ n : ℕ, μ (s n) = μ {ω | (n : ℝ) ≤ X ω} := by
      intro n
      have hset : s n = (T^[n]) ⁻¹' {ω | (n : ℝ) ≤ X ω} := by
        ext ω
        simp only [s, X, Set.mem_preimage, Set.mem_ofPred_eq]
        rw [mul_comm, le_div_iff₀ hε]
      rw [hset]
      exact (hT.iterate n).measure_preimage (hmeas_base n).nullMeasurableSet
    have htsum : (∑' n, μ (s n)) < ⊤ := by
      have heq : (fun n : ℕ => μ (s n)) = fun n : ℕ => μ {ω | (n : ℝ) ≤ X ω} := by
        funext n
        exact hpre n
      rw [heq]
      exact hsum
    filter_upwards [ae_eventually_notMem htsum.ne] with ω hω
    filter_upwards [hω, eventually_gt_atTop 0] with n hn npos
    have hnot : ¬ ε * (n : ℝ) ≤ |g ((T^[n]) ω)| := hn
    have hlt : |g ((T^[n]) ω)| < ε * n := lt_of_not_ge hnot
    simpa [ε] using hlt
  filter_upwards [ae_all_iff.2 htail] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  rcases eventually_atTop.1 (hω k) with ⟨N, hN⟩
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnpos : 0 < n := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right N 1) hn)
  have hlt := hN n (le_trans (le_max_left N 1) hn)
  rw [Real.dist_eq, sub_zero, abs_div, Nat.abs_cast]
  exact ((div_lt_iff₀ (Nat.cast_pos.mpr hnpos)).2 hlt).trans hk

/-- A null-set property holds along almost every forward orbit. -/
lemma ae_forall_iterate (hT : MeasurePreserving T μ μ) {p : Ω → Prop}
    (hp : ∀ᵐ ω ∂μ, p ω) : ∀ᵐ ω ∂μ, ∀ i : ℕ, p ((T^[i]) ω) :=
  ae_all_iff.2 fun i => (hT.iterate i).quasiMeasurePreserving.ae hp

/-- Subadditive blocks of equal length are at most the sum of the block values. -/
lemma kingmanCocycle_le_sum_blocks {u : ℕ → ℕ → ℝ}
    (hsub : ∀ i n m, 0 < n → 0 < m → u i (n + m) ≤ u i n + u (i + n) m)
    {m : ℕ} (hm : 0 < m) {q : ℕ} (hq : 0 < q) :
    u 0 (q * m) ≤ ∑ j ∈ range q, u (j * m) m := by
  induction q with
  | zero =>
    omega
  | succ q ih =>
    cases q with
    | zero =>
      simp
    | succ q =>
      have hq0 : 0 < q + 1 := Nat.succ_pos q
      have hlen : 0 < (q + 1) * m := Nat.mul_pos hq0 hm
      have hstep := hsub 0 ((q + 1) * m) m hlen hm
      have hadd : (q + 1) * m + m = (q + 1 + 1) * m := by
        have hmul : (q + 1) * m + 1 * m = ((q + 1) + 1) * m :=
          (Nat.add_mul (q + 1) 1 m).symm
        simpa [one_mul] using hmul
      rw [hadd] at hstep
      have hIH := ih hq0
      rw [sum_range_succ]
      simp only [Nat.zero_add] at hstep
      linarith

/-- Every pair of positive lengths satisfies the subadditive inequality simultaneously. -/
lemma kingman_ae_subadditive {f : ℕ → Ω → ℝ}
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω)) :
    ∀ᵐ ω ∂μ, ∀ n m : ℕ, 0 < n → 0 < m →
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω) := by
  refine ae_all_iff.2 fun n => ae_all_iff.2 fun m => ?_
  by_cases hn : 0 < n
  · by_cases hm : 0 < m
    · exact (hsub n m hn hm).mono fun _ h _ _ => h
    · exact Eventually.of_forall fun _ _ hm' => (hm hm').elim
  · exact Eventually.of_forall fun _ hn' => (hn hn').elim

omit [MeasurableSpace Ω] in
/-- Normalized lengths stay above the linear lower bound. -/
lemma kingmanRatio_ge {f : ℕ → Ω → ℝ} {C : ℝ}
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) (n : ℕ) (ω : Ω) :
    -C ≤ kingmanRatio f n ω := by
  have hpos : 0 < n + 1 := Nat.succ_pos n
  have hle := hC (n + 1) hpos ω
  unfold kingmanRatio
  have hcast : (n + 1 : ℝ) = ((n + 1 : ℕ) : ℝ) := by simp [Nat.cast_succ]
  rw [hcast]
  have hinv : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_left hle hinv
  have hcancel : ((n + 1 : ℕ) : ℝ)⁻¹ * (-C * ((n + 1 : ℕ) : ℝ)) = -C := by
    have hn0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hn0]
  rwa [hcancel] at hmul

/-- Each normalized length is measurable when the cocycle is. -/
lemma measurable_kingmanRatio {f : ℕ → Ω → ℝ} {n : ℕ} (hf : Measurable (f (n + 1))) :
    Measurable (kingmanRatio f n) := by
  unfold kingmanRatio
  exact measurable_const.mul hf

/-- The extended liminf is measurable for a measurable cocycle. -/
lemma measurable_kingmanLiminf {f : ℕ → Ω → ℝ}
    (hf : ∀ n : ℕ, 0 < n → Measurable (f n)) : Measurable (kingmanLiminf f) := by
  unfold kingmanLiminf
  refine Measurable.liminf fun n => ?_
  exact (measurable_kingmanRatio (hf (n + 1) (Nat.succ_pos n))).coe_real_ereal

/-- Along almost every orbit the liminf does not increase under `T`. -/
lemma kingmanLiminf_le_comp {f : ℕ → Ω → ℝ} {C : ℝ}
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) :
    ∀ᵐ ω ∂μ, kingmanLiminf f ω ≤ kingmanLiminf f (T ω) := by
  have hc : Tendsto (fun n : ℕ => (n + 1 : ℝ) / (n + 2)) atTop (𝓝 1) := by
    have hreal : Tendsto (fun n : ℕ => (n + 2 : ℝ)) atTop atTop := by
      have heq : (fun n : ℕ => (n + 2 : ℝ)) = fun n => ((n + 2 : ℕ) : ℝ) := by
        ext n
        simp
      rw [heq]
      exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
    have hinv : Tendsto (fun n : ℕ => (n + 2 : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hreal
    have hform : (fun n : ℕ => (n + 1 : ℝ) / (n + 2)) =
        fun n : ℕ => 1 - (n + 2 : ℝ)⁻¹ := by
      ext n
      have hn : (n + 2 : ℝ) ≠ 0 := by positivity
      field_simp [hn]
      ring
    rw [hform]
    simpa using tendsto_const_nhds.sub hinv
  filter_upwards [kingman_ae_subadditive hsub] with ω hsubω
  let c : ℕ → ℝ := fun n => (n + 1 : ℝ) / (n + 2)
  let z : ℕ → ℝ := fun n => kingmanRatio f n (T ω)
  have hstep : ∀ n, kingmanRatio f (n + 1) ω ≤
      f 1 ω / (n + 2 : ℝ) + c n * z n := by
    intro n
    have hineq := hsubω 1 (n + 1) Nat.one_pos (Nat.succ_pos n)
    have hlen : 1 + (n + 1) = n + 2 := by omega
    have hiter : T^[1] = T := Function.iterate_one _
    rw [hlen, hiter] at hineq
    have hpos : (0 : ℝ) < n + 2 := by positivity
    have hdiv := div_le_div_of_nonneg_right hineq hpos.le
    have hsplit : (f 1 ω + f (n + 1) (T ω)) / (n + 2) =
        f 1 ω / (n + 2) + f (n + 1) (T ω) / (n + 2) := by
      ring
    have hratio : f (n + 1) (T ω) / (n + 2) = c n * z n := by
      have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
      unfold c z kingmanRatio
      field_simp [hn1]
    have hleft : kingmanRatio f (n + 1) ω = f (n + 2) ω / (n + 2) := by
      unfold kingmanRatio
      rw [show n + 1 + 1 = n + 2 by omega]
      have hcast : ((n + 1 : ℕ) : ℝ) + 1 = n + 2 := by
        rw [Nat.cast_succ]
        ring
      rw [hcast, div_eq_mul_inv, mul_comm]
    linarith
  have hα : Tendsto (fun n : ℕ => f 1 ω / (n + 2 : ℝ)) atTop (𝓝 0) := by
    have hreal : Tendsto (fun n : ℕ => (n + 2 : ℝ)) atTop atTop := by
      have heq : (fun n : ℕ => (n + 2 : ℝ)) = fun n => ((n + 2 : ℕ) : ℝ) := by
        ext n
        simp
      rw [heq]
      exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
    have hmul := (tendsto_const_nhds (x := f 1 ω)).mul (tendsto_inv_atTop_zero.comp hreal)
    have hfun : (fun n : ℕ => f 1 ω * (n + 2 : ℝ)⁻¹) =
        fun n : ℕ => f 1 ω / (n + 2) := by
      ext n
      rw [div_eq_mul_inv]
    simpa [hfun] using hmul
  have hle : liminf (fun n => ((kingmanRatio f (n + 1) ω : ℝ) : EReal)) atTop ≤
      liminf (fun n => ((f 1 ω / (n + 2) + c n * z n : ℝ) : EReal)) atTop := by
    refine liminf_le_liminf ?_
    filter_upwards with n
    exact EReal.coe_le_coe_iff.mpr (hstep n)
  have hadd := liminf_add_tendsto (u := fun n => ((c n * z n : ℝ) : EReal)) hα
  have hfun : (fun n => ((c n * z n : ℝ) : EReal) + ((f 1 ω / (n + 2) : ℝ) : EReal)) =
      fun n => ((f 1 ω / (n + 2) + c n * z n : ℝ) : EReal) := by
    ext n
    rw [add_comm, ← EReal.coe_add]
  rw [hfun] at hadd
  have hprod : liminf (fun n => ((c n * z n : ℝ) : EReal)) atTop =
      liminf (fun n => (z n : EReal)) atTop := by
    refine liminf_mul_tendsto_one_ge (M := |C|) (fun n => ?_) hc
      (Eventually.of_forall fun n => by positivity)
    have hge := kingmanRatio_ge hC n (T ω)
    linarith [neg_le_neg (le_abs_self C), hge]
  have hshift : liminf (fun n => ((kingmanRatio f (n + 1) ω : ℝ) : EReal)) atTop =
      kingmanLiminf f ω := by
    simpa [kingmanLiminf] using
      (liminf_add_one (u := fun n => (kingmanRatio f n ω : EReal)))
  have hzero : liminf (fun n => ((c n * z n : ℝ) : EReal)) atTop + (0 : EReal) =
      liminf (fun n => ((c n * z n : ℝ) : EReal)) atTop := by simp
  calc kingmanLiminf f ω
      = liminf (fun n => ((kingmanRatio f (n + 1) ω : ℝ) : EReal)) atTop := hshift.symm
    _ ≤ liminf (fun n => ((f 1 ω / (n + 2) + c n * z n : ℝ) : EReal)) atTop := hle
    _ = liminf (fun n => ((c n * z n : ℝ) : EReal)) atTop + (0 : EReal) := hadd
    _ = liminf (fun n => ((c n * z n : ℝ) : EReal)) atTop := hzero
    _ = liminf (fun n => (z n : EReal)) atTop := hprod
    _ = kingmanLiminf f (T ω) := by simp [kingmanLiminf, z]

/-- The linear lower bound passes to the extended liminf. -/
lemma kingmanLiminf_ge {f : ℕ → Ω → ℝ} {C : ℝ}
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) (ω : Ω) :
    (-C : EReal) ≤ kingmanLiminf f ω := by
  unfold kingmanLiminf
  refine le_liminf_of_le (h := Eventually.of_forall fun n => ?_)
  exact EReal.coe_le_coe_iff.mpr (kingmanRatio_ge hC n ω)

/-- The extended liminf is never `⊥` under a real linear lower bound. -/
lemma kingmanLiminf_ne_bot {f : ℕ → Ω → ℝ} {C : ℝ}
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) (ω : Ω) :
    kingmanLiminf f ω ≠ ⊥ := by
  intro hbot
  have hle := kingmanLiminf_ge hC ω
  rw [hbot] at hle
  exact not_le_of_gt (EReal.bot_lt_coe (-C)) hle

/-- Each normalized length is integrable. -/
lemma integrable_kingmanRatio {f : ℕ → Ω → ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ) (n : ℕ) :
    Integrable (kingmanRatio f n) μ := by
  unfold kingmanRatio
  exact (hf (n + 1) (Nat.succ_pos n)).const_mul ((n + 1 : ℝ)⁻¹)

/-- A pointwise linear bound yields the same bound for normalized integrals. -/
lemma kingman_integral_ge_of_pointwise [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} {C : ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) {n : ℕ} (hn : 0 < n) :
    -C ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ := by
  have hconst_int : Integrable (fun _ : Ω => -C * (n : ℝ)) μ := integrable_const _
  have hge : ∫ ω, -C * (n : ℝ) ∂μ ≤ ∫ ω, f n ω ∂μ :=
    integral_mono hconst_int (hf n hn) fun ω => hC n hn ω
  have hconst : ∫ ω, -C * (n : ℝ) ∂μ = -C * (n : ℝ) := by
    rw [integral_const]
    simp [measureReal_def, IsProbabilityMeasure.measure_univ]
  have hinv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_left hge hinv
  rw [hconst] at hmul
  have hcancel : (n : ℝ)⁻¹ * (-C * (n : ℝ)) = -C := by
    field_simp
  rwa [hcancel] at hmul

/-- Shifted normalized integrals converge to the mean rate plus the shift. -/
lemma tendsto_integral_kingmanShift [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} {C : ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) :
    Tendsto (fun n : ℕ => ∫ ω, kingmanRatio f n ω + C ∂μ) atTop
      (𝓝 (sInf {a : ℝ | ∃ n : ℕ, 0 < n ∧ a = (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ} + C)) := by
  have hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ :=
    ⟨-C, fun n hn => kingman_integral_ge_of_pointwise hf hC hn⟩
  have hdiv := tendsto_kingmanIntegral_div hT hf hsub hlower
  have hint : ∀ n, ∫ ω, kingmanRatio f n ω + C ∂μ =
      (n + 1 : ℝ)⁻¹ * ∫ ω, f (n + 1) ω ∂μ + C := by
    intro n
    unfold kingmanRatio
    rw [integral_add ((hf (n + 1) (Nat.succ_pos n)).const_mul _) (integrable_const _),
      integral_const_mul, integral_const]
    simp [measureReal_def, IsProbabilityMeasure.measure_univ]
  exact (hdiv.add tendsto_const_nhds).congr fun n => (hint n).symm

/-- `ENNReal.ofReal` preserves a constant shift of an extended liminf. -/
lemma liminf_ofReal_add_const {z : ℕ → ℝ} {C : ℝ} :
    liminf (fun n => ENNReal.ofReal (z n + C)) atTop =
      (liminf (fun n => (z n : EReal)) atTop + (C : EReal)).toENNReal := by
  have hadd := liminf_add_tendsto (u := fun n => (z n : EReal))
    (v := fun _ : ℕ => C) tendsto_const_nhds
  have hfun : (fun n => (z n : EReal) + (C : EReal)) =
      fun n => ((z n + C : ℝ) : EReal) := by
    ext n
    simp [EReal.coe_add]
  rw [hfun] at hadd
  have hmono : Monotone EReal.toENNReal := fun _ _ hxy => EReal.toENNReal_le_toENNReal hxy
  have hmap := hmono.map_liminf_of_continuousAt (F := atTop)
    (a := fun n => ((z n + C : ℝ) : EReal)) EReal.continuous_toENNReal.continuousAt
    (cobdd := by
      unfold Filter.IsCoboundedUnder
      exact isCobounded_ge_of_top)
    (bdd_below := ereal_isBoundedUnder_ge atTop _)
  have hcomp : EReal.toENNReal ∘ (fun n => ((z n + C : ℝ) : EReal)) =
      fun n => ENNReal.ofReal (z n + C) := by
    ext n
    rw [Function.comp_apply]
    exact EReal.real_coe_toENNReal (z n + C)
  rw [hcomp, hadd] at hmap
  exact hmap.symm

/-- The real representative of the extended liminf. Infinities are sent to zero. -/
def kingmanLiminfReal (f : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  (kingmanLiminf f ω).toReal

/-- Under a pointwise linear bound, Fatou makes the liminf integrable with mean at most
the Fekete infimum. The value is finite almost everywhere and stays above `-C`. -/
lemma kingmanLiminfReal_integrable_le [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} {C : ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) :
    Integrable (kingmanLiminfReal f) μ ∧
      ∫ ω, kingmanLiminfReal f ω ∂μ ≤
        sInf {a : ℝ | ∃ n : ℕ, 0 < n ∧ a = (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ} ∧
      (∀ᵐ ω ∂μ, kingmanLiminf f ω ≠ ⊤) ∧
      (∀ᵐ ω ∂μ, -C ≤ kingmanLiminfReal f ω) := by
  set L : ℝ := sInf {a : ℝ | ∃ n : ℕ, 0 < n ∧ a = (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ}
  have hL : -C ≤ L := by
    refine le_csInf ⟨((1 : ℕ) : ℝ)⁻¹ * ∫ ω, f 1 ω ∂μ, ⟨1, Nat.one_pos, rfl⟩⟩ ?_
    intro a ⟨n, hn, ha⟩
    rw [ha]
    exact kingman_integral_ge_of_pointwise hf hC hn
  have hshift := tendsto_integral_kingmanShift hT hf hsub hC
  have hnn : ∀ n ω, 0 ≤ kingmanRatio f n ω + C := by
    intro n ω
    linarith [kingmanRatio_ge hC n ω]
  have hmeas_n : ∀ n, Measurable fun ω => ENNReal.ofReal (kingmanRatio f n ω + C) := by
    intro n
    exact ENNReal.continuous_ofReal.measurable.comp
      ((measurable_kingmanRatio (hf_meas (n + 1) (Nat.succ_pos n))).add measurable_const)
  have hlint : ∀ n, ∫⁻ ω, ENNReal.ofReal (kingmanRatio f n ω + C) ∂μ =
      ENNReal.ofReal (∫ ω, kingmanRatio f n ω + C ∂μ) := by
    intro n
    have hint : Integrable (fun ω => kingmanRatio f n ω + C) μ :=
      (integrable_kingmanRatio hf n).add (integrable_const _)
    exact (ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun ω => hnn n ω)).symm
  have htend : Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (kingmanRatio f n ω + C) ∂μ) atTop
      (𝓝 (ENNReal.ofReal (L + C))) := by
    have hreal := ENNReal.tendsto_ofReal (by simpa [L] using hshift)
    refine hreal.congr fun n => ?_
    exact (hlint n).symm
  have hfatou := lintegral_liminf_le (μ := μ) (u := atTop)
    (f := fun n ω => ENNReal.ofReal (kingmanRatio f n ω + C)) hmeas_n
  have hpoint : (fun ω => liminf (fun n => ENNReal.ofReal (kingmanRatio f n ω + C)) atTop) =
      fun ω => (kingmanLiminf f ω + (C : EReal)).toENNReal := by
    ext ω
    simpa [kingmanLiminf] using
      liminf_ofReal_add_const (z := fun n => kingmanRatio f n ω) (C := C)
  have hineq : ∫⁻ ω, (kingmanLiminf f ω + (C : EReal)).toENNReal ∂μ ≤
      ENNReal.ofReal (L + C) := by
    rw [← hpoint]
    calc
      ∫⁻ ω, liminf (fun n => ENNReal.ofReal (kingmanRatio f n ω + C)) atTop ∂μ
          ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (kingmanRatio f n ω + C) ∂μ) atTop := hfatou
      _ = ENNReal.ofReal (L + C) := htend.liminf_eq
  have hlimmeas : Measurable fun ω =>
      liminf (fun n => ENNReal.ofReal (kingmanRatio f n ω + C)) atTop :=
    Measurable.liminf hmeas_n
  have hne : ∀ᵐ ω ∂μ, kingmanLiminf f ω ≠ ⊤ := by
    have hlin_fin : ∫⁻ ω, liminf (fun n => ENNReal.ofReal (kingmanRatio f n ω + C)) atTop ∂μ ≤
        ENNReal.ofReal (L + C) := by
      rw [hpoint]
      exact hineq
    have hfin : ∫⁻ ω, liminf (fun n => ENNReal.ofReal (kingmanRatio f n ω + C)) atTop ∂μ ≠ ⊤ :=
      ne_of_lt (hlin_fin.trans_lt ENNReal.ofReal_lt_top)
    filter_upwards [ae_lt_top hlimmeas hfin] with ω hω
    have htop : (kingmanLiminf f ω + (C : EReal)).toENNReal ≠ ⊤ := by
      have hval : liminf (fun n => ENNReal.ofReal (kingmanRatio f n ω + C)) atTop =
          (kingmanLiminf f ω + (C : EReal)).toENNReal := congr_fun hpoint ω
      exact hval ▸ hω.ne
    intro hinf
    apply htop
    rw [hinf, EReal.top_add_coe, EReal.toENNReal_top]
  have hge_ae : ∀ᵐ ω ∂μ, -C ≤ kingmanLiminfReal f ω := by
    filter_upwards [hne] with ω htop
    have hle := EReal.toReal_le_toReal (kingmanLiminf_ge hC ω) (EReal.coe_ne_bot (-C)) htop
    simpa [kingmanLiminfReal, EReal.toReal_coe] using hle
  have hnn_g : ∀ᵐ ω ∂μ, 0 ≤ kingmanLiminfReal f ω + C := by
    filter_upwards [hge_ae] with ω hω
    linarith
  have hfun_ae : (fun ω => ENNReal.ofReal (kingmanLiminfReal f ω + C)) =ᵐ[μ]
      fun ω => (kingmanLiminf f ω + (C : EReal)).toENNReal := by
    filter_upwards [hne] with ω htop
    have hbot := kingmanLiminf_ne_bot hC ω
    have hsum : (kingmanLiminf f ω + (C : EReal)).toReal = kingmanLiminfReal f ω + C := by
      rw [EReal.toReal_add htop hbot (EReal.coe_ne_top C) (EReal.coe_ne_bot C)]
      simp [kingmanLiminfReal]
    have hfinite : kingmanLiminf f ω + (C : EReal) ≠ ⊤ :=
      (EReal.add_ne_top_iff_ne_top_left (EReal.coe_ne_bot C) (EReal.coe_ne_top C)).mpr htop
    rw [EReal.toENNReal_of_ne_top hfinite, hsum]
  have hlin_real : ∫⁻ ω, ENNReal.ofReal (kingmanLiminfReal f ω + C) ∂μ ≤
      ENNReal.ofReal (L + C) := by
    calc
      ∫⁻ ω, ENNReal.ofReal (kingmanLiminfReal f ω + C) ∂μ
          = ∫⁻ ω, (kingmanLiminf f ω + (C : EReal)).toENNReal ∂μ := lintegral_congr_ae hfun_ae
      _ ≤ ENNReal.ofReal (L + C) := hineq
  have hgC_meas : Measurable fun ω => kingmanLiminfReal f ω + C :=
    ((measurable_kingmanLiminf hf_meas).ereal_toReal).add measurable_const
  have hgC_int : Integrable (fun ω => kingmanLiminfReal f ω + C) μ := by
    refine ⟨hgC_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn_g]
    exact hlin_real.trans_lt ENNReal.ofReal_lt_top
  have hg_int : Integrable (kingmanLiminfReal f) μ := by
    have hsub_fun : kingmanLiminfReal f = fun ω => (kingmanLiminfReal f ω + C) - C := by
      ext ω
      ring
    rw [hsub_fun]
    exact hgC_int.sub (integrable_const C)
  have hsplit : ∫ ω, kingmanLiminfReal f ω + C ∂μ =
      ∫ ω, kingmanLiminfReal f ω ∂μ + C := by
    rw [integral_add hg_int (integrable_const C), integral_const]
    simp [measureReal_def, IsProbabilityMeasure.measure_univ]
  have hint_le : ∫ ω, kingmanLiminfReal f ω + C ∂μ ≤ L + C := by
    have hLC : 0 ≤ L + C := by linarith
    rw [← ENNReal.ofReal_le_ofReal_iff hLC,
      ofReal_integral_eq_lintegral_ofReal hgC_int hnn_g]
    exact hlin_real
  refine ⟨hg_int, ?_, hne, hge_ae⟩
  linarith

/-- The real liminf does not increase along almost every orbit, hence is invariant. -/
lemma kingmanLiminfReal_ae_invariant [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} {C : ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) :
    kingmanLiminfReal f ∘ T =ᵐ[μ] kingmanLiminfReal f := by
  obtain ⟨hg_int, -, hne, -⟩ := kingmanLiminfReal_integrable_le hT hf hf_meas hsub hC
  have hcomp := kingmanLiminf_le_comp hsub hC
  have hneT : ∀ᵐ ω ∂μ, kingmanLiminf f (T ω) ≠ ⊤ := hT.quasiMeasurePreserving.ae hne
  have hge : ∀ᵐ ω ∂μ, kingmanLiminfReal f ω ≤ kingmanLiminfReal f (T ω) := by
    filter_upwards [hcomp, hne, hneT] with ω hle htop htopT
    have hreal := EReal.toReal_le_toReal hle (kingmanLiminf_ne_bot hC ω) htopT
    simpa [kingmanLiminfReal] using hreal
  have hTg : Integrable (fun ω => kingmanLiminfReal f (T ω)) μ := by
    simpa [Function.comp_def] using hT.integrable_comp_of_integrable hg_int
  have hdiff_int : Integrable (fun ω => kingmanLiminfReal f (T ω) - kingmanLiminfReal f ω) μ :=
    hTg.sub hg_int
  have hint : ∫ ω, kingmanLiminfReal f (T ω) - kingmanLiminfReal f ω ∂μ = 0 := by
    rw [integral_sub hTg hg_int, integral_comp_measurePreserving hT hg_int, sub_self]
  have hnn : 0 ≤ᵐ[μ] fun ω => kingmanLiminfReal f (T ω) - kingmanLiminfReal f ω := by
    filter_upwards [hge] with ω hω
    have : 0 ≤ kingmanLiminfReal f (T ω) - kingmanLiminfReal f ω := by linarith
    simpa using this
  have heq0 := (integral_eq_zero_iff_of_nonneg_ae hnn hdiff_int).1 hint
  filter_upwards [heq0] with ω hω
  exact sub_eq_zero.mp hω

end CKMA
