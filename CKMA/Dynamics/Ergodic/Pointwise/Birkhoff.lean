/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Ergodic.Pointwise.BirkhoffLimit
public import Mathlib.Dynamics.Ergodic.Function
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

import Mathlib.Tactic

/-!
# Birkhoff's pointwise ergodic theorem

The almost-everywhere limit of the Birkhoff averages is the conditional expectation on the
invariant σ-algebra. Bounded observables are identified by dominated convergence, and the
integrable case follows by truncation.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Set MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω} {f : Ω → ℝ}

/-- Truncation of a real observable to `[-M, M]`. -/
def birkhoffTruncate (M : ℝ) (f : Ω → ℝ) : Ω → ℝ :=
  fun ω => max (-M) (min (f ω) M)

/-- Truncation preserves measurability. -/
lemma measurable_birkhoffTruncate {M : ℝ} (hf : Measurable f) :
    Measurable (birkhoffTruncate M f) := by
  unfold birkhoffTruncate
  exact (measurable_const : Measurable fun _ : Ω => (-M : ℝ)).max
    (hf.min (measurable_const : Measurable fun _ : Ω => M))

section

omit [MeasurableSpace Ω]

/-- A nonnegative truncation radius bounds the truncated observable. -/
lemma abs_birkhoffTruncate_le {M : ℝ} (hM : 0 ≤ M) (ω : Ω) :
    |birkhoffTruncate M f ω| ≤ M := by
  unfold birkhoffTruncate
  set x := f ω
  refine abs_le.mpr ⟨le_max_left _ _, ?_⟩
  refine max_le (by linarith) (min_le_right _ _)

/-- Distance to the truncation is at most the distance to zero. -/
lemma abs_sub_birkhoffTruncate_le {M : ℝ} (hM : 0 ≤ M) (ω : Ω) :
    |f ω - birkhoffTruncate M f ω| ≤ |f ω| := by
  unfold birkhoffTruncate
  set x := f ω
  rcases le_or_gt x M with hxm | hxm
  · rcases le_or_gt x (-M) with hx | hx
    · have htr : max (-M) (min x M) = -M := by
        rw [min_eq_left (hx.trans (by linarith)), max_eq_left hx]
      rw [htr, sub_neg_eq_add, abs_of_nonpos (by linarith : x ≤ 0),
        abs_of_nonpos (by linarith : x + M ≤ 0)]
      linarith
    · have htr : max (-M) (min x M) = x := by
        rw [min_eq_left hxm, max_eq_right hx.le]
      rw [htr]
      simp
  · have htr : max (-M) (min x M) = M := by
      rw [min_eq_right hxm.le, max_eq_right (by linarith)]
    rw [htr, abs_of_pos (by linarith : 0 < x - M), abs_of_nonneg (by linarith : 0 ≤ x)]
    linarith

/-- Integer truncations converge pointwise to the original observable. -/
lemma tendsto_birkhoffTruncate (ω : Ω) :
    Tendsto (fun M : ℕ => birkhoffTruncate (M : ℝ) f ω) atTop (𝓝 (f ω)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt |f ω|
  refine ⟨N, fun M hM => ?_⟩
  have hle : |f ω| ≤ (M : ℝ) := hN.le.trans (Nat.cast_le.mpr hM)
  have heq : birkhoffTruncate (M : ℝ) f ω = f ω := by
    unfold birkhoffTruncate
    rw [min_eq_left ((le_abs_self _).trans hle), max_eq_right (neg_le_of_abs_le hle)]
  simp [heq, dist_self, hε]

end

section

omit [MeasurableSpace Ω]

/-- A nonnegative observable has nonnegative Birkhoff averages. -/
lemma birkhoffAverage_nonneg {T : Ω → Ω} {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) (n : ℕ) (ω : Ω) :
    0 ≤ birkhoffAverage ℝ T f n ω := by
  unfold birkhoffAverage birkhoffSum
  rw [smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (by positivity)) (Finset.sum_nonneg fun _ _ => hf _)

end

/-- Integrating a Birkhoff sum counts the integral once for each summand. -/
lemma integral_birkhoffSum (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (n : ℕ) :
    ∫ ω, birkhoffSum T f n ω ∂μ = (n : ℝ) * ∫ ω, f ω ∂μ := by
  induction n with
  | zero =>
    simp [birkhoffSum_zero, integral_zero]
  | succ n ih =>
    have hsum : Integrable (birkhoffSum T f n) μ := integrable_birkhoffSum hT hf n
    have hcomp : Integrable (birkhoffSum T f n ∘ T) μ :=
      hT.integrable_comp_of_integrable hsum
    rw [birkhoffSum_succ', integral_add' hf hcomp]
    have hshift : ∫ a, (birkhoffSum T f n ∘ T) a ∂μ = ∫ a, birkhoffSum T f n a ∂μ := by
      change ∫ a, birkhoffSum T f n (T a) ∂μ = _
      exact integral_comp_measurePreserving hT hsum
    rw [hshift, ih]
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
      simp [Nat.cast_add, Nat.cast_one]
    rw [hcast, add_mul, one_mul, add_comm]

/-- A positive-length Birkhoff average has the same integral as the observable. -/
lemma integral_birkhoffAverage (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    {n : ℕ} (hn : 0 < n) :
    ∫ ω, birkhoffAverage ℝ T f n ω ∂μ = ∫ ω, f ω ∂μ := by
  unfold birkhoffAverage
  rw [integral_smul, integral_birkhoffSum hT hf n, smul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← mul_assoc, inv_mul_cancel₀ hn0, one_mul]

section

omit [MeasurableSpace Ω]

/-- On a strictly invariant set, averaging commutes with the indicator. -/
lemma birkhoffAverage_indicator_invariant {E : Set Ω} (hinv : T ⁻¹' E = E) (n : ℕ) (ω : Ω) :
    birkhoffAverage ℝ T (E.indicator f) n ω =
      E.indicator (fun ω => birkhoffAverage ℝ T f n ω) ω := by
  unfold birkhoffAverage
  rw [birkhoffSum_indicator_invariant hinv f n ω]
  by_cases hω : ω ∈ E
  · simp [indicator_of_mem hω, smul_eq_mul]
  · simp [indicator_of_notMem hω, smul_eq_mul]

end

/-- Invariant sets do not change the integral of a positive-length average. -/
lemma setIntegral_birkhoffAverage_of_invariant (hT : MeasurePreserving T μ μ)
    (hf : Integrable f μ) {E : Set Ω} (hE : MeasurableSet E) (hinv : T ⁻¹' E = E)
    {n : ℕ} (hn : 0 < n) :
    ∫ ω in E, birkhoffAverage ℝ T f n ω ∂μ = ∫ ω in E, f ω ∂μ := by
  have hfun : E.indicator (fun ω => birkhoffAverage ℝ T f n ω) =
      birkhoffAverage ℝ T (E.indicator f) n := by
    ext ω
    exact (birkhoffAverage_indicator_invariant (f := f) hinv n ω).symm
  rw [← integral_indicator hE, hfun,
    integral_birkhoffAverage hT (hf.indicator hE) hn, integral_indicator hE]

section

omit [MeasurableSpace Ω]

/-- A uniform bound passes to the finite Birkhoff limit. -/
lemma abs_birkhoffLimit_le_of_abs_le {M : ℝ} (hM : 0 ≤ M) (hf : ∀ ω, |f ω| ≤ M) (ω : Ω) :
    |birkhoffLimit T f ω| ≤ M := by
  have hupper : birkhoffLimsup T f ω ≤ (M : EReal) := by
    unfold birkhoffLimsup
    rw [limsup_le_iff]
    intro y hy
    cases y with
    | bot => exact (not_lt_bot hy).elim
    | top =>
      filter_upwards with _
      exact EReal.coe_lt_top _
    | coe q =>
      have hMq : M < q := EReal.coe_lt_coe_iff.mp hy
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hAn : birkhoffAverage ℝ T f n ω ≤ M :=
        (abs_le.mp (abs_birkhoffAverage_le_of_abs_le hM hf n ω)).2
      exact EReal.coe_lt_coe (hAn.trans_lt hMq)
  have hlower : (-M : EReal) ≤ birkhoffLimsup T f ω := by
    have hinf : (-M : EReal) ≤ birkhoffLiminf T f ω := by
      unfold birkhoffLiminf
      rw [le_liminf_iff]
      intro y hy
      cases y with
      | top => exact (not_top_lt hy).elim
      | bot =>
        filter_upwards with _
        exact EReal.bot_lt_coe _
      | coe q =>
        have hqM : q < -M := EReal.coe_lt_coe_iff.mp hy
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hAn : -M ≤ birkhoffAverage ℝ T f n ω :=
          (abs_le.mp (abs_birkhoffAverage_le_of_abs_le hM hf n ω)).1
        exact EReal.coe_lt_coe (hqM.trans_le hAn)
    exact hinf.trans (by
      simpa [birkhoffLiminf, birkhoffLimsup] using
        liminf_le_limsup (f := atTop)
          (u := fun n => Real.toEReal (birkhoffAverage ℝ T f n ω))
          (ereal_isBoundedUnder_le _ _) (ereal_isBoundedUnder_ge _ _))
  have htop : birkhoffLimsup T f ω ≠ ⊤ := fun h => by
    have : (M : EReal) < ⊤ := EReal.coe_lt_top M
    rw [← h] at this
    exact not_le_of_gt this hupper
  have hbot : birkhoffLimsup T f ω ≠ ⊥ := fun h => by
    have : (⊥ : EReal) < (-M : EReal) := EReal.bot_lt_coe (-M)
    rw [← h] at this
    exact not_le_of_gt this hlower
  have hcoe : ((birkhoffLimit T f ω : ℝ) : EReal) = birkhoffLimsup T f ω := by
    rw [birkhoffLimit, EReal.coe_toReal htop hbot]
  rw [← hcoe] at hupper hlower
  exact abs_le.mpr ⟨EReal.coe_le_coe_iff.mp hlower, EReal.coe_le_coe_iff.mp hupper⟩

end

/-- For a bounded measurable observable the Birkhoff limit is the conditional expectation. -/
lemma birkhoffLimit_ae_eq_condExp_of_bounded [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (hf_meas : Measurable f)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ ω, |f ω| ≤ M) :
    birkhoffLimit T f =ᵐ[μ] μ[f | MeasurableSpace.invariants T] := by
  have hφ_meas : Measurable (birkhoffLimit T f) :=
    measurable_birkhoffLimit hT.measurable hf_meas
  have hφ_int : Integrable (birkhoffLimit T f) μ :=
    (integrable_const M).mono' hφ_meas.aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using abs_birkhoffLimit_le_of_abs_le hM hbound ω)
  have hset : ∀ s : Set Ω, MeasurableSet[MeasurableSpace.invariants T] s → μ s < ⊤ →
      ∫ ω in s, birkhoffLimit T f ω ∂μ = ∫ ω in s, f ω ∂μ := by
    intro s hs _
    rw [MeasurableSpace.measurableSet_invariants] at hs
    have hconv := birkhoffAverage_ae_tendsto_birkhoffLimit hT hf hf_meas
    have htend : Tendsto (fun n => ∫ ω in s, birkhoffAverage ℝ T f n ω ∂μ) atTop
        (𝓝 (∫ ω in s, birkhoffLimit T f ω ∂μ)) := by
      have hdom := tendsto_integral_of_dominated_convergence (μ := μ)
        (F := fun n => s.indicator (fun ω => birkhoffAverage ℝ T f n ω))
        (f := s.indicator (birkhoffLimit T f)) (bound := fun _ => M)
        (fun n => ((measurable_birkhoffAverage hT.measurable hf_meas n).indicator
          hs.1).aestronglyMeasurable)
        (integrable_const M)
        (fun n => Eventually.of_forall fun ω => by
          by_cases hω : ω ∈ s
          · simpa [indicator_of_mem hω, Real.norm_eq_abs] using
              abs_birkhoffAverage_le_of_abs_le hM hbound n ω
          · simp [indicator_of_notMem hω, hM])
        (by
          filter_upwards [hconv] with ω hω
          by_cases hmem : ω ∈ s
          · simpa [indicator_of_mem hmem] using hω
          · simp [indicator_of_notMem hmem])
      have hright : ∫ ω, s.indicator (birkhoffLimit T f) ω ∂μ =
          ∫ ω in s, birkhoffLimit T f ω ∂μ :=
        integral_indicator (f := birkhoffLimit T f) hs.1
      rw [hright] at hdom
      refine Tendsto.congr' ?_ hdom
      filter_upwards with n
      exact integral_indicator (f := fun ω => birkhoffAverage ℝ T f n ω) hs.1
    have hconst : Tendsto (fun n => ∫ ω in s, birkhoffAverage ℝ T f n ω ∂μ) atTop
        (𝓝 (∫ ω in s, f ω ∂μ)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      exact (setIntegral_birkhoffAverage_of_invariant hT hf hs.1 hs.2 hn).symm
    exact tendsto_nhds_unique htend hconst
  have hm : MeasurableSpace.invariants T ≤ ‹MeasurableSpace Ω› :=
    MeasurableSpace.invariants_le T
  have hσ : SigmaFinite (μ.trim hm) := by infer_instance
  exact ae_eq_condExp_of_forall_setIntegral_eq hm hf (fun s _ _ => hφ_int.integrableOn) hset
    ((measurable_invariants_birkhoffLimit hT.measurable hf_meas).stronglyMeasurable
      |>.aestronglyMeasurable)

/-- A nonnegative Birkhoff limit is integrable, and its integral is at most that of `f`. -/
lemma birkhoffLimit_integrable_le_of_nonneg [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (hf_meas : Measurable f)
    (hf0 : ∀ ω, 0 ≤ f ω) :
    Integrable (birkhoffLimit T f) μ ∧
      ∫ ω, birkhoffLimit T f ω ∂μ ≤ ∫ ω, f ω ∂μ := by
  have hφ_meas : Measurable (birkhoffLimit T f) :=
    measurable_birkhoffLimit hT.measurable hf_meas
  have hφ0 : ∀ ω, 0 ≤ birkhoffLimit T f ω := by
    intro ω
    have hlow : (0 : EReal) ≤ birkhoffLimsup T f ω := by
      have hinf : (0 : EReal) ≤ birkhoffLiminf T f ω := by
        unfold birkhoffLiminf
        rw [le_liminf_iff]
        intro y hy
        cases y with
        | top => exact (not_top_lt hy).elim
        | bot =>
          filter_upwards with _
          exact EReal.bot_lt_coe _
        | coe q =>
          have hq : q < 0 := EReal.coe_lt_coe_iff.mp hy
          filter_upwards [eventually_ge_atTop 0] with n _
          exact EReal.coe_lt_coe (hq.trans_le (birkhoffAverage_nonneg hf0 n ω))
      exact hinf.trans (by
        simpa [birkhoffLiminf, birkhoffLimsup] using
          liminf_le_limsup (f := atTop)
            (u := fun n => Real.toEReal (birkhoffAverage ℝ T f n ω))
            (ereal_isBoundedUnder_le _ _) (ereal_isBoundedUnder_ge _ _))
    unfold birkhoffLimit
    exact EReal.toReal_nonneg hlow
  have hconv := birkhoffAverage_ae_tendsto_birkhoffLimit hT hf hf_meas
  have hlim :
      (fun ω => liminf (fun n => ENNReal.ofReal (birkhoffAverage ℝ T f n ω)) atTop) =ᵐ[μ]
        fun ω => ENNReal.ofReal (birkhoffLimit T f ω) := by
    filter_upwards [hconv] with ω hω
    exact (ENNReal.tendsto_ofReal hω).liminf_eq
  have hfatou := lintegral_liminf_le (μ := μ) (u := atTop)
    (f := fun n ω => ENNReal.ofReal (birkhoffAverage ℝ T f n ω))
    (fun n => ENNReal.continuous_ofReal.measurable.comp
      (measurable_birkhoffAverage hT.measurable hf_meas n))
  have hI : ∀ n, 0 < n →
      ∫⁻ ω, ENNReal.ofReal (birkhoffAverage ℝ T f n ω) ∂μ =
        ENNReal.ofReal (∫ ω, f ω ∂μ) := by
    intro n hn
    have hint : Integrable (birkhoffAverage ℝ T f n) μ :=
      (integrable_birkhoffSum hT hf n).smul ((n : ℝ)⁻¹)
    rw [← ofReal_integral_eq_lintegral_ofReal hint
        (Eventually.of_forall (birkhoffAverage_nonneg hf0 n)),
      integral_birkhoffAverage hT hf hn]
  have hconst :
      (fun n => ∫⁻ ω, ENNReal.ofReal (birkhoffAverage ℝ T f n ω) ∂μ) =ᶠ[atTop]
        fun _ => ENNReal.ofReal (∫ ω, f ω ∂μ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact hI n hn
  have hlin : ∫⁻ ω, ENNReal.ofReal (birkhoffLimit T f ω) ∂μ ≤
      ENNReal.ofReal (∫ ω, f ω ∂μ) := by
    calc
      ∫⁻ ω, ENNReal.ofReal (birkhoffLimit T f ω) ∂μ
          = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (birkhoffAverage ℝ T f n ω)) atTop ∂μ :=
            lintegral_congr_ae hlim.symm
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (birkhoffAverage ℝ T f n ω) ∂μ) atTop :=
            hfatou
      _ = ENNReal.ofReal (∫ ω, f ω ∂μ) :=
            (tendsto_const_nhds.congr' hconst.symm).liminf_eq
  have hfi : HasFiniteIntegral (birkhoffLimit T f) μ := by
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hφ0)]
    exact hlin.trans_lt ENNReal.ofReal_lt_top
  have hφ_int : Integrable (birkhoffLimit T f) μ := ⟨hφ_meas.aestronglyMeasurable, hfi⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hφ_int (Eventually.of_forall hφ0)] at hlin
  exact ⟨hφ_int, (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hf0)).1 hlin⟩

/-- The distance between Birkhoff limits is controlled by the limit of the absolute difference. -/
lemma abs_birkhoffLimit_sub_le_ae [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (hf_meas : Measurable f)
    (hg_meas : Measurable g) :
    (fun ω => |birkhoffLimit T f ω - birkhoffLimit T g ω|) ≤ᵐ[μ]
      birkhoffLimit T (fun ω => |f ω - g ω|) := by
  have hdiff_meas : Measurable (fun ω => |f ω - g ω|) :=
    continuous_abs.measurable.comp (hf_meas.sub hg_meas)
  have hdiff_int : Integrable (fun ω => |f ω - g ω|) μ := (hf.sub hg).abs
  filter_upwards [birkhoffAverage_ae_tendsto_birkhoffLimit hT hf hf_meas,
      birkhoffAverage_ae_tendsto_birkhoffLimit hT hg hg_meas,
      birkhoffAverage_ae_tendsto_birkhoffLimit hT hdiff_int hdiff_meas] with ω hωf hωg hωa
  refine le_of_tendsto_of_tendsto' ((hωf.sub hωg).abs) hωa fun n => ?_
  have hsub : birkhoffAverage ℝ T (f - g) n ω =
      birkhoffAverage ℝ T f n ω - birkhoffAverage ℝ T g n ω :=
    birkhoffAverage_sub_apply n ω
  calc
    |birkhoffAverage ℝ T f n ω - birkhoffAverage ℝ T g n ω|
        = |birkhoffAverage ℝ T (f - g) n ω| := by rw [hsub]
    _ ≤ birkhoffAverage ℝ T (fun ω => |(f - g) ω|) n ω :=
        abs_birkhoffAverage_le (f := f - g) n ω
    _ = birkhoffAverage ℝ T (fun ω => |f ω - g ω|) n ω := by
        simp [Pi.sub_apply]

/-- Integrals of distances between Birkhoff limits contract like the observables. -/
lemma integral_abs_birkhoffLimit_sub_le [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (hf_meas : Measurable f)
    (hg_meas : Measurable g) :
    ∫ ω, |birkhoffLimit T f ω - birkhoffLimit T g ω| ∂μ ≤ ∫ ω, |f ω - g ω| ∂μ := by
  have hdiff_meas : Measurable (fun ω => |f ω - g ω|) :=
    continuous_abs.measurable.comp (hf_meas.sub hg_meas)
  have hdiff_int : Integrable (fun ω => |f ω - g ω|) μ := (hf.sub hg).abs
  have hφ := birkhoffLimit_integrable_le_of_nonneg hT hdiff_int hdiff_meas
    (fun ω => abs_nonneg _)
  have hleft_meas : Measurable (fun ω => |birkhoffLimit T f ω - birkhoffLimit T g ω|) :=
    continuous_abs.measurable.comp ((measurable_birkhoffLimit hT.measurable hf_meas).sub
      (measurable_birkhoffLimit hT.measurable hg_meas))
  have hle := abs_birkhoffLimit_sub_le_ae hT hf hg hf_meas hg_meas
  have hleft : Integrable (fun ω => |birkhoffLimit T f ω - birkhoffLimit T g ω|) μ :=
    hφ.1.mono' hleft_meas.aestronglyMeasurable
      (hle.mono fun ω hω => by simpa [Real.norm_eq_abs] using hω)
  exact (integral_mono_ae hleft hφ.1 hle).trans hφ.2

/-- Integer truncations converge to the observable in L¹. -/
lemma tendsto_integral_abs_sub_birkhoffTruncate (hf : Integrable f μ) (hf_meas : Measurable f) :
    Tendsto (fun M : ℕ => ∫ ω, |f ω - birkhoffTruncate (M : ℝ) f ω| ∂μ) atTop (𝓝 0) := by
  have hmeas : ∀ M : ℕ, AEStronglyMeasurable
      (fun ω => |f ω - birkhoffTruncate (M : ℝ) f ω|) μ := fun M =>
    (continuous_abs.measurable.comp
      (hf_meas.sub (measurable_birkhoffTruncate hf_meas))).aestronglyMeasurable
  have hdom := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun M ω => |f ω - birkhoffTruncate (M : ℝ) f ω|)
    (f := fun _ => (0 : ℝ)) (bound := fun ω => |f ω|) hmeas hf.abs
    (fun M => Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using
        abs_sub_birkhoffTruncate_le (Nat.cast_nonneg M) ω)
    (Eventually.of_forall fun ω => by
      have hsub : Tendsto (fun M : ℕ => f ω - birkhoffTruncate (M : ℝ) f ω) atTop
          (𝓝 (f ω - f ω)) :=
        (tendsto_const_nhds (x := f ω)).sub (tendsto_birkhoffTruncate (f := f) ω)
      rw [sub_self (f ω)] at hsub
      have habs := (continuous_abs.tendsto (0 : ℝ)).comp hsub
      rw [abs_zero] at habs
      refine Tendsto.congr ?_ habs
      intro M
      simp [Function.comp_apply])
  simpa [integral_zero] using hdom

/-- For a measurable integrable observable the Birkhoff limit is the conditional expectation. -/
lemma birkhoffLimit_ae_eq_condExp_of_measurable [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (hf_meas : Measurable f) :
    birkhoffLimit T f =ᵐ[μ] μ[f | MeasurableSpace.invariants T] := by
  let fM : ℕ → Ω → ℝ := fun M => birkhoffTruncate (M : ℝ) f
  have hM_meas : ∀ M, Measurable (fM M) := fun _ => measurable_birkhoffTruncate hf_meas
  have hM_int : ∀ M, Integrable (fM M) μ := fun M =>
    (integrable_const (M : ℝ)).mono' (hM_meas M).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using abs_birkhoffTruncate_le (Nat.cast_nonneg M) ω)
  have hM_eq : ∀ M, birkhoffLimit T (fM M) =ᵐ[μ]
      μ[fM M | MeasurableSpace.invariants T] := fun M =>
    birkhoffLimit_ae_eq_condExp_of_bounded hT (hM_int M) (hM_meas M) (Nat.cast_nonneg M)
      (fun ω => abs_birkhoffTruncate_le (Nat.cast_nonneg M) ω)
  have habs_meas : Measurable (fun ω => |f ω|) := continuous_abs.measurable.comp hf_meas
  have hφ_int : Integrable (birkhoffLimit T f) μ := by
    let z : Ω → ℝ := fun _ => 0
    have hzero : ∀ ω, birkhoffLimit T z ω = 0 := fun ω => by
      have hbound : ∀ η, |z η| ≤ (0 : ℝ) := fun _ => by rw [abs_zero]
      have hle := abs_birkhoffLimit_le_of_abs_le (T := T) (f := z) le_rfl hbound ω
      exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
    have hz_int : Integrable z μ := integrable_zero Ω ℝ μ
    have hle := abs_birkhoffLimit_sub_le_ae hT hf hz_int hf_meas measurable_const
    have hbound := (birkhoffLimit_integrable_le_of_nonneg hT hf.abs habs_meas
      (fun _ => abs_nonneg _)).1
    refine hbound.mono' (measurable_birkhoffLimit hT.measurable hf_meas).aestronglyMeasurable ?_
    filter_upwards [hle] with ω hω
    have hnorm : ‖birkhoffLimit T f ω‖ = |birkhoffLimit T f ω - birkhoffLimit T z ω| := by
      rw [hzero ω, sub_zero, Real.norm_eq_abs]
    have hfun : birkhoffLimit T (fun η => |f η - z η|) ω =
        birkhoffLimit T (fun η => |f η|) ω := by
      congr 1
      funext η
      simp [z, sub_zero]
    exact le_of_eq_of_le hnorm (hω.trans_eq hfun)
  let φ : Ω → ℝ := birkhoffLimit T f
  let cexp : Ω → ℝ := μ[f | MeasurableSpace.invariants T]
  have hint : Integrable (fun ω => |φ ω - cexp ω|) μ := (hφ_int.sub integrable_condExp).abs
  have ha_nonneg : 0 ≤ ∫ ω, |φ ω - cexp ω| ∂μ := integral_nonneg fun _ => abs_nonneg _
  have ha_le : ∀ M : ℕ, ∫ ω, |φ ω - cexp ω| ∂μ ≤
      2 * ∫ ω, |f ω - fM M ω| ∂μ := by
    intro M
    have h1 : ∫ ω, |φ ω - birkhoffLimit T (fM M) ω| ∂μ ≤ ∫ ω, |f ω - fM M ω| ∂μ :=
      integral_abs_birkhoffLimit_sub_le hT hf (hM_int M) hf_meas (hM_meas M)
    have hb_int : Integrable (birkhoffLimit T (fM M)) μ :=
      (integrable_const (M : ℝ)).mono'
        (measurable_birkhoffLimit hT.measurable (hM_meas M)).aestronglyMeasurable
        (Eventually.of_forall fun ω => by
          simpa [Real.norm_eq_abs] using abs_birkhoffLimit_le_of_abs_le (Nat.cast_nonneg M)
            (fun ω => abs_birkhoffTruncate_le (Nat.cast_nonneg M) ω) ω)
    let d : Ω → ℝ := μ[fM M | MeasurableSpace.invariants T]
    have hmid_int : Integrable (fun ω => |birkhoffLimit T (fM M) ω - d ω|) μ :=
      (hb_int.sub integrable_condExp).abs
    have hmid : ∫ ω, |birkhoffLimit T (fM M) ω - d ω| ∂μ = 0 :=
      (integral_eq_zero_iff_of_nonneg (fun _ => abs_nonneg _) hmid_int).2
        (by
          filter_upwards [hM_eq M] with ω hω
          simp [hω, d])
    have hsub := condExp_sub (hM_int M) hf (MeasurableSpace.invariants T)
    have hcond : ∫ ω, |d ω - cexp ω| ∂μ ≤ ∫ ω, |f ω - fM M ω| ∂μ := by
      have hcongr : (fun ω => |d ω - cexp ω|) =ᵐ[μ]
          fun ω => |(μ[fM M - f | MeasurableSpace.invariants T]) ω| := by
        filter_upwards [hsub] with ω hω
        dsimp [d, cexp]
        rw [hω, Pi.sub_apply]
      have hcomm : ∫ ω, |fM M ω - f ω| ∂μ = ∫ ω, |f ω - fM M ω| ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp [abs_sub_comm]
      calc
        ∫ ω, |d ω - cexp ω| ∂μ
            = ∫ ω, |(μ[fM M - f | MeasurableSpace.invariants T]) ω| ∂μ :=
              integral_congr_ae hcongr
        _ ≤ ∫ ω, |fM M ω - f ω| ∂μ := by
              simpa [Pi.sub_apply] using integral_abs_condExp_le (μ := μ)
                (m := MeasurableSpace.invariants T) (fM M - f)
        _ = ∫ ω, |f ω - fM M ω| ∂μ := hcomm
    have hab : Integrable (fun ω => |φ ω - birkhoffLimit T (fM M) ω|) μ :=
      (hφ_int.sub hb_int).abs
    have hcd : Integrable (fun ω => |d ω - cexp ω|) μ :=
      (integrable_condExp.sub integrable_condExp).abs
    have hsum_int : Integrable (fun ω => |φ ω - birkhoffLimit T (fM M) ω| +
        |birkhoffLimit T (fM M) ω - d ω| + |d ω - cexp ω|) μ :=
      (hab.add hmid_int).add hcd
    have hpt : ∀ ω, |φ ω - cexp ω| ≤ |φ ω - birkhoffLimit T (fM M) ω| +
        |birkhoffLimit T (fM M) ω - d ω| + |d ω - cexp ω| := by
      intro ω
      linarith [abs_sub_le (φ ω) (birkhoffLimit T (fM M) ω) (cexp ω),
        abs_sub_le (birkhoffLimit T (fM M) ω) (d ω) (cexp ω)]
    have hsplit := integral_mono hint hsum_int hpt
    have hsum_eq : ∫ ω, |φ ω - birkhoffLimit T (fM M) ω| +
          |birkhoffLimit T (fM M) ω - d ω| + |d ω - cexp ω| ∂μ =
        ∫ ω, |φ ω - birkhoffLimit T (fM M) ω| ∂μ +
          ∫ ω, |birkhoffLimit T (fM M) ω - d ω| ∂μ +
          ∫ ω, |d ω - cexp ω| ∂μ := by
      have hinner : (fun ω => |φ ω - birkhoffLimit T (fM M) ω| +
            |birkhoffLimit T (fM M) ω - d ω|) =
          (fun ω => |φ ω - birkhoffLimit T (fM M) ω|) +
            fun ω => |birkhoffLimit T (fM M) ω - d ω| := by
        funext ω
        simp [Pi.add_apply]
      have hpair : (fun ω => |φ ω - birkhoffLimit T (fM M) ω| +
            |birkhoffLimit T (fM M) ω - d ω| + |d ω - cexp ω|) =
          (fun ω => |φ ω - birkhoffLimit T (fM M) ω| +
            |birkhoffLimit T (fM M) ω - d ω|) +
            fun ω => |d ω - cexp ω| := by
        funext ω
        simp [Pi.add_apply, add_assoc]
      rw [hpair, hinner, integral_add' (hab.add hmid_int) hcd, integral_add' hab hmid_int]
    linarith [h1, hcond, hsplit, hsum_eq, hmid]
  have ha0 : ∫ ω, |φ ω - cexp ω| ∂μ ≤ 0 := by
    have hb : Tendsto (fun M : ℕ => 2 * ∫ ω, |f ω - fM M ω| ∂μ) atTop (𝓝 0) := by
      simpa [mul_zero] using
        (tendsto_integral_abs_sub_birkhoffTruncate hf hf_meas).const_mul 2
    exact le_of_tendsto_of_tendsto'
      (tendsto_const_nhds (x := ∫ ω, |φ ω - cexp ω| ∂μ)) hb ha_le
  have ha_zero : ∫ ω, |φ ω - cexp ω| ∂μ = 0 := le_antisymm ha0 ha_nonneg
  have hzero_ae : (fun ω => |φ ω - cexp ω|) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => abs_nonneg _) hint).1 ha_zero
  filter_upwards [hzero_ae] with ω hω
  exact sub_eq_zero.mp (abs_eq_zero.mp hω)

/-- Birkhoff averages converge almost everywhere to the invariant conditional expectation. -/
lemma birkhoffAverage_ae_tendsto_condExp [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => birkhoffAverage ℝ T f n ω) atTop
      (𝓝 ((μ[f | MeasurableSpace.invariants T]) ω)) := by
  set g : Ω → ℝ := hf.aestronglyMeasurable.mk f with hg_def
  have hfg : f =ᵐ[μ] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg_meas : Measurable g := hf.aestronglyMeasurable.measurable_mk
  have hg_int : Integrable g μ := hf.congr hfg
  have hlim := birkhoffAverage_ae_tendsto_birkhoffLimit hT hg_int hg_meas
  have heq := birkhoffLimit_ae_eq_condExp_of_measurable hT hg_int hg_meas
  have hcond := (condExp_congr_ae (m := MeasurableSpace.invariants T) hfg).symm
  have havg : ∀ᵐ ω ∂μ, ∀ n, birkhoffAverage ℝ T f n ω = birkhoffAverage ℝ T g n ω :=
    (ae_all_iff).2 fun n =>
      hT.quasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ hfg n
  filter_upwards [havg, hlim, heq, hcond] with ω havgω hlimω heqω hcondω
  have htend := hlimω.congr fun n => (havgω n).symm
  rw [heqω, hcondω] at htend
  exact htend

/-- In an ergodic system the conditional expectation is almost everywhere the scalar mean. -/
lemma birkhoffAverage_ae_tendsto_integral_of_ergodic [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => birkhoffAverage ℝ T f n ω) atTop
      (𝓝 (∫ ω, f ω ∂μ)) := by
  have hconv := birkhoffAverage_ae_tendsto_condExp hT.toMeasurePreserving hf
  let cexp : Ω → ℝ := μ[f | MeasurableSpace.invariants T]
  have hmeas : Measurable[MeasurableSpace.invariants T] cexp :=
    stronglyMeasurable_condExp.measurable
  have hmeas0 : Measurable cexp := hmeas.mono (MeasurableSpace.invariants_le T) le_rfl
  have hinv : cexp ∘ T = cexp :=
    MeasurableSpace.comp_eq_of_measurable_invariants hmeas
  obtain ⟨c, hc⟩ := hT.ae_eq_const_of_ae_eq_comp₀ hmeas0.aemeasurable.nullMeasurable
    (EventuallyEq.of_eq hinv)
  have : SigmaFinite (μ.trim (MeasurableSpace.invariants_le T)) := inferInstance
  have hint : ∫ ω, cexp ω ∂μ = ∫ ω, f ω ∂μ :=
    integral_condExp (MeasurableSpace.invariants_le T)
  have hconst : ∫ ω, cexp ω ∂μ = c := by
    have heq : cexp =ᵐ[μ] fun _ : Ω => c := hc.mono fun _ hω => by
      simpa [Function.const_apply] using hω
    rw [integral_congr_ae heq, integral_const]
    simp [measureReal_def, IsProbabilityMeasure.measure_univ]
  filter_upwards [hconv, hc] with ω hω hcω
  have hval : (μ[f | MeasurableSpace.invariants T]) ω = ∫ η, f η ∂μ := by
    have hcval : (μ[f | MeasurableSpace.invariants T]) ω = c := by
      simpa [cexp, Function.const_apply] using hcω
    rw [hcval, ← hint, hconst]
  simpa [hval] using hω

end CKMA

