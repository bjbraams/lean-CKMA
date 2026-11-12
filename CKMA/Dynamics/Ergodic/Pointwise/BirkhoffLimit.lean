/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Ergodic.Pointwise.Maximal
public import CKMA.Dynamics.Ergodic.Pointwise.BirkhoffShift
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants

import Mathlib.Tactic

/-!
# Almost-everywhere convergence of Birkhoff averages

Strict invariance of the extended limsup, the maximal ergodic inequality, and a countable
rational upcrossing argument show that the averages converge almost everywhere to a finite
invariant limit.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Set MeasureTheory Filter Topology

variable {Ω : Type*}

section Averages

variable {T : Ω → Ω} {f : Ω → ℝ}

/-- A positive-length Birkhoff average of a constant function is that constant. -/
lemma birkhoffAverage_const (n : ℕ) (hn : n ≠ 0) (c : ℝ) (ω : Ω) :
    birkhoffAverage ℝ T (fun _ : Ω => c) n ω = c := by
  unfold birkhoffAverage birkhoffSum
  simp only [smul_eq_mul, Finset.sum_const, Finset.card_range]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]

/-- Subtracting a constant subtracts that constant from a positive-length average. -/
lemma birkhoffAverage_sub_const {f : Ω → ℝ} (n : ℕ) (hn : n ≠ 0) (c : ℝ) (ω : Ω) :
    birkhoffAverage ℝ T (fun ω => f ω - c) n ω = birkhoffAverage ℝ T f n ω - c := by
  have hfun : (fun ω => f ω - c) = f - fun _ => c := by
    funext ω
    rfl
  rw [hfun, birkhoffAverage_sub_apply, birkhoffAverage_const n hn c ω]

/-- The absolute value of an average is at most the average of the absolute value. -/
lemma abs_birkhoffAverage_le (n : ℕ) (ω : Ω) :
    |birkhoffAverage ℝ T f n ω| ≤ birkhoffAverage ℝ T (fun ω => |f ω|) n ω := by
  cases n with
  | zero => simp [birkhoffAverage_zero_apply]
  | succ n =>
    unfold birkhoffAverage
    rw [smul_eq_mul, smul_eq_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    unfold birkhoffSum
    simpa using Finset.abs_sum_le_sum_abs (fun k => f (T^[k] ω)) (Finset.range (n + 1))

/-- A uniform bound on the observable bounds every Birkhoff average. -/
lemma abs_birkhoffAverage_le_of_abs_le {M : ℝ} (hM : 0 ≤ M) (hf : ∀ ω, |f ω| ≤ M)
    (n : ℕ) (ω : Ω) : |birkhoffAverage ℝ T f n ω| ≤ M := by
  cases n with
  | zero =>
    rw [birkhoffAverage_zero_apply, abs_zero]
    exact hM
  | succ n =>
    refine le_trans (abs_birkhoffAverage_le (n + 1) ω) ?_
    have hle : birkhoffAverage ℝ T (fun ω => |f ω|) (n + 1) ω ≤
        birkhoffAverage ℝ T (fun _ : Ω => M) (n + 1) ω := by
      unfold birkhoffAverage
      rw [smul_eq_mul, smul_eq_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      unfold birkhoffSum
      exact Finset.sum_le_sum fun k _ => hf _
    rwa [birkhoffAverage_const (n + 1) (by positivity) M ω] at hle

/-- A strict limsup forces some positive-length sum of `f - α` to be positive. -/
lemma subset_positive_of_birkhoffLimsup_gt {α : ℝ} {E : Set Ω}
    (hsub : E ⊆ {ω | (α : EReal) < birkhoffLimsup T f ω}) :
    E ⊆ {ω | ∃ n, 0 < n ∧ 0 < birkhoffSum T (fun ω => f ω - α) n ω} := by
  intro ω hω
  have hlt : (α : EReal) <
      limsup (fun n => Real.toEReal (birkhoffAverage ℝ T f n ω)) atTop := by
    simpa [birkhoffLimsup] using hsub hω
  have hfreq : ∃ᶠ n in atTop, (α : EReal) < Real.toEReal (birkhoffAverage ℝ T f n ω) :=
    frequently_lt_of_lt_limsup (hu := ereal_isCoboundedUnder_le _ _) hlt
  rw [frequently_atTop] at hfreq
  obtain ⟨n, hn, hltn⟩ := hfreq 1
  have hn0 : 0 < n := by omega
  have hreal : α < birkhoffAverage ℝ T f n ω := EReal.coe_lt_coe_iff.mp hltn
  refine ⟨n, hn0, ?_⟩
  have havg : 0 < birkhoffAverage ℝ T (fun ω => f ω - α) n ω := by
    rw [birkhoffAverage_sub_const n hn0.ne' α ω]
    linarith
  unfold birkhoffAverage at havg
  rw [smul_eq_mul] at havg
  exact (mul_pos_iff_of_pos_left (by positivity)).mp havg

/-- A strict inequality for the liminf is a strict limsup inequality for `-f`. -/
lemma birkhoffLiminf_lt_coe_iff (ω : Ω) (α : ℝ) :
    birkhoffLiminf T f ω < α ↔ (-α : EReal) < birkhoffLimsup T (-f) ω := by
  rw [birkhoffLiminf_neg]
  cases hL : birkhoffLimsup T (-f) ω with
  | bot => simp [EReal.neg_bot]
  | top =>
    rw [EReal.neg_top]
    refine ⟨fun _ => ?_, fun _ => EReal.bot_lt_coe α⟩
    simpa [EReal.coe_neg] using EReal.coe_lt_top (-α)
  | coe r =>
    rw [← EReal.coe_neg, ← EReal.coe_neg, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff]
    exact ⟨fun h => by linarith, fun h => by linarith⟩

end Averages

section Measurable

variable [MeasurableSpace Ω] {T : Ω → Ω} {f : Ω → ℝ}

/-- Each Birkhoff average of a measurable observable is measurable. -/
lemma measurable_birkhoffAverage (hT : Measurable T) (hf : Measurable f) (n : ℕ) :
    Measurable (birkhoffAverage ℝ T f n) := by
  unfold birkhoffAverage
  simp only [smul_eq_mul]
  exact ((measurable_const : Measurable fun (_ : Ω) => (n : ℝ)⁻¹).mul
    (measurable_birkhoffSum hT hf n))

/-- The extended limsup of the averages is measurable. -/
lemma measurable_birkhoffLimsup (hT : Measurable T) (hf : Measurable f) :
    Measurable (birkhoffLimsup T f) := by
  unfold birkhoffLimsup
  refine Measurable.limsup fun n => ?_
  exact continuous_coe_real_ereal.measurable.comp (measurable_birkhoffAverage hT hf n)

/-- The extended liminf of the averages is measurable. -/
lemma measurable_birkhoffLiminf (hT : Measurable T) (hf : Measurable f) :
    Measurable (birkhoffLiminf T f) := by
  unfold birkhoffLiminf
  refine Measurable.liminf fun n => ?_
  exact continuous_coe_real_ereal.measurable.comp (measurable_birkhoffAverage hT hf n)

/-- Real part of an extended real, sending both infinities to zero. -/
lemma measurable_ereal_toReal : Measurable EReal.toReal := by
  have hs : (({⊥, ⊤}ᶜ : Set EReal)ᶜ).Countable := by
    rw [compl_compl]
    exact (countable_singleton (⊤ : EReal)).insert ⊥
  exact EReal.continuousOn_toReal.measurable_of_countable_compl hs

/-- Pointwise finite part of the extended limsup of the averages. -/
def birkhoffLimit (T : Ω → Ω) (f : Ω → ℝ) (ω : Ω) : ℝ :=
  (birkhoffLimsup T f ω).toReal

/-- The finite part of the limsup is measurable. -/
lemma measurable_birkhoffLimit (hT : Measurable T) (hf : Measurable f) :
    Measurable (birkhoffLimit T f) :=
  measurable_ereal_toReal.comp (measurable_birkhoffLimsup hT hf)

section InvariantLimit

omit [MeasurableSpace Ω]

/-- The finite part of the limsup is strictly invariant. -/
lemma birkhoffLimit_comp (ω : Ω) : birkhoffLimit T f (T ω) = birkhoffLimit T f ω := by
  unfold birkhoffLimit
  rw [birkhoffLimsup_comp]

end InvariantLimit

/-- A measurable strictly invariant real function is measurable on the invariant σ-algebra. -/
lemma measurable_invariants_of_comp_eq {g : Ω → ℝ} (hg : Measurable g) (hcomp : g ∘ T = g) :
    Measurable[MeasurableSpace.invariants T] g := by
  rw [MeasurableSpace.measurable_invariants_dom]
  exact ⟨hg, fun s _ => by rw [hcomp]⟩

/-- The Birkhoff limit is measurable on the invariant σ-algebra. -/
lemma measurable_invariants_birkhoffLimit (hT : Measurable T) (hf : Measurable f) :
    Measurable[MeasurableSpace.invariants T] (birkhoffLimit T f) :=
  measurable_invariants_of_comp_eq (measurable_birkhoffLimit hT hf) <|
    funext fun ω => birkhoffLimit_comp (T := T) (f := f) ω

/-- Upcrossing set where the liminf lies below `p` and the limsup lies above `q`. -/
def birkhoffSeparated (T : Ω → Ω) (f : Ω → ℝ) (p q : ℝ) : Set Ω :=
  {ω | birkhoffLiminf T f ω < p ∧ (q : EReal) < birkhoffLimsup T f ω}

/-- An upcrossing set is measurable. -/
lemma measurableSet_birkhoffSeparated (hT : Measurable T) (hf : Measurable f) (p q : ℝ) :
    MeasurableSet (birkhoffSeparated T f p q) := by
  unfold birkhoffSeparated
  rw [Set.ofPred_and]
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_lt (measurable_birkhoffLiminf hT hf)
      (measurable_const : Measurable fun (_ : Ω) => (p : EReal))
  · exact measurableSet_lt
      (measurable_const : Measurable fun (_ : Ω) => (q : EReal))
      (measurable_birkhoffLimsup hT hf)

/-- The set where the limsup is infinite is measurable. -/
lemma measurableSet_birkhoffLimsup_top (hT : Measurable T) (hf : Measurable f) :
    MeasurableSet {ω | birkhoffLimsup T f ω = ⊤} :=
  measurableSet_eq_fun (measurable_birkhoffLimsup hT hf) measurable_const

section InvariantSets

omit [MeasurableSpace Ω]

/-- An upcrossing set is strictly invariant. -/
lemma preimage_birkhoffSeparated (p q : ℝ) :
    T ⁻¹' birkhoffSeparated T f p q = birkhoffSeparated T f p q := by
  ext ω
  change birkhoffLiminf T f (T ω) < (p : EReal) ∧
      (q : EReal) < birkhoffLimsup T f (T ω) ↔
      birkhoffLiminf T f ω < (p : EReal) ∧ (q : EReal) < birkhoffLimsup T f ω
  rw [birkhoffLiminf_comp, birkhoffLimsup_comp]

/-- The infinite limsup set is strictly invariant. -/
lemma preimage_birkhoffLimsup_top :
    T ⁻¹' {ω | birkhoffLimsup T f ω = ⊤} = {ω | birkhoffLimsup T f ω = ⊤} := by
  ext ω
  change birkhoffLimsup T f (T ω) = ⊤ ↔ birkhoffLimsup T f ω = ⊤
  rw [birkhoffLimsup_comp]

end InvariantSets

end Measurable

section Null

variable [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω} {f : Ω → ℝ}

/-- Separated finite liminf and limsup occur only on a null set. -/
lemma measure_birkhoffSeparated_eq_zero [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ) (hf_meas : Measurable f)
    {p q : ℝ} (hpq : p < q) : μ (birkhoffSeparated T f p q) = 0 := by
  set E := birkhoffSeparated T f p q
  have hE : MeasurableSet E := measurableSet_birkhoffSeparated hT.measurable hf_meas p q
  have hinv : T ⁻¹' E = E := preimage_birkhoffSeparated (T := T) (f := f) p q
  have hsup : E ⊆ {ω | ∃ n, 0 < n ∧ 0 < birkhoffSum T (fun ω => f ω - q) n ω} := by
    refine subset_positive_of_birkhoffLimsup_gt fun ω hω => ?_
    exact hω.2
  have hinf : E ⊆ {ω | ( -p : EReal) < birkhoffLimsup T (-f) ω} := by
    intro ω hω
    exact (birkhoffLiminf_lt_coe_iff (T := T) (f := f) ω p).mp hω.1
  have hneg : E ⊆ {ω | ∃ n, 0 < n ∧ 0 < birkhoffSum T (fun ω => -f ω - (-p)) n ω} :=
    subset_positive_of_birkhoffLimsup_gt (T := T) (f := -f) (α := -p) hinf
  have hge := setIntegral_ge_const_of_invariant_subset_positive hT hf hf_meas hE hinv hsup
  have hle := setIntegral_ge_const_of_invariant_subset_positive hT hf.neg hf_meas.neg hE hinv hneg
  have hupper : ∫ ω in E, f ω ∂μ ≤ p * μ.real E := by
    have hnegint : ∫ ω in E, (-f) ω ∂μ = -∫ ω in E, f ω ∂μ := by
      simpa [Pi.neg_apply] using (integral_neg (μ := μ.restrict E) f)
    rw [hnegint] at hle
    linarith
  have hmul : (q - p) * μ.real E ≤ 0 := by linarith
  have hμ : μ.real E ≤ 0 := by nlinarith [hpq]
  have hzero : μ.real E = 0 := le_antisymm hμ measureReal_nonneg
  exact (measureReal_eq_zero_iff).mp hzero

/-- The set where the limsup is infinite is null. -/
lemma measure_birkhoffLimsup_top_eq_zero [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ) (hf_meas : Measurable f) :
    μ {ω | birkhoffLimsup T f ω = ⊤} = 0 := by
  set S := {ω | birkhoffLimsup T f ω = ⊤}
  have habs : Integrable (fun ω => |f ω|) μ := hf.norm
  have hbound : ∀ N : ℕ, 0 < N → (N : ℝ) * μ.real S ≤ ∫ ω, |f ω| ∂μ := by
    intro N hN
    set E := {ω | (N : ℝ) < birkhoffLimsup T f ω}
    have hE : MeasurableSet E :=
      measurableSet_lt measurable_const (measurable_birkhoffLimsup hT.measurable hf_meas)
    have hinv : T ⁻¹' E = E := by
      ext ω
      change ((N : ℝ) : EReal) < birkhoffLimsup T f (T ω) ↔
        ((N : ℝ) : EReal) < birkhoffLimsup T f ω
      rw [birkhoffLimsup_comp]
    have hSE : S ⊆ E := by
      intro ω hω
      change birkhoffLimsup T f ω = ⊤ at hω
      change ((N : ℝ) : EReal) < birkhoffLimsup T f ω
      rw [hω]
      exact EReal.coe_lt_top _
    have hsub : E ⊆ {ω | ∃ n, 0 < n ∧ 0 < birkhoffSum T (fun ω => f ω - N) n ω} :=
      subset_positive_of_birkhoffLimsup_gt fun ω hω => hω
    have hge :=
      setIntegral_ge_const_of_invariant_subset_positive hT hf hf_meas hE hinv hsub
    have hSle : μ.real S ≤ μ.real E := measureReal_mono hSE
    have hNS : (N : ℝ) * μ.real S ≤ ∫ ω in E, f ω ∂μ := by nlinarith
    have hle_abs : ∫ ω in E, f ω ∂μ ≤ ∫ ω in E, |f ω| ∂μ :=
      integral_mono hf.integrableOn habs.integrableOn fun ω => le_abs_self _
    have habs_le : ∫ ω in E, |f ω| ∂μ ≤ ∫ ω, |f ω| ∂μ :=
      setIntegral_le_integral habs (Eventually.of_forall fun ω => abs_nonneg _)
    linarith
  have hdiv : Tendsto (fun N : ℕ => (∫ ω, |f ω| ∂μ) / (N : ℝ)) atTop (𝓝 0) := by
    have hnat : Tendsto (fun N : ℕ => ((N : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds (x := ∫ ω, |f ω| ∂μ)).mul (tendsto_inv_atTop_zero.comp hnat)
  have hsmall : ∀ᶠ N : ℕ in atTop, μ.real S ≤ (∫ ω, |f ω| ∂μ) / (N : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    rw [le_div_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N), mul_comm]
    exact hbound N hN
  have hnonpos : μ.real S ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hdiv hsmall
  exact (measureReal_eq_zero_iff).mp (le_antisymm hnonpos measureReal_nonneg)

/-- The set where the liminf is infinite is null. -/
lemma measure_birkhoffLiminf_bot_eq_zero [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ) (hf_meas : Measurable f) :
    μ {ω | birkhoffLiminf T f ω = ⊥} = 0 := by
  have hset : {ω | birkhoffLiminf T f ω = ⊥} = {ω | birkhoffLimsup T (-f) ω = ⊤} := by
    ext ω
    change birkhoffLiminf T f ω = ⊥ ↔ birkhoffLimsup T (-f) ω = ⊤
    rw [birkhoffLiminf_neg]
    cases hL : birkhoffLimsup T (-f) ω with
    | bot => simp [EReal.neg_bot]
    | top => simp [EReal.neg_top]
    | coe _ => simp
  rw [hset]
  exact measure_birkhoffLimsup_top_eq_zero hT hf.neg hf_meas.neg

/-- Outside a null set the averages converge to the finite invariant limit. -/
lemma birkhoffAverage_ae_tendsto_birkhoffLimit [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ) (hf_meas : Measurable f) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n ω) atTop (𝓝 (birkhoffLimit T f ω)) := by
  let bad : Set Ω := ⋃ r : {r : ℚ × ℚ // (r.1 : ℝ) < r.2},
    birkhoffSeparated T f r.1.1 r.1.2
  have hbad : μ bad = 0 := by
    refine measure_iUnion_null fun r => ?_
    exact measure_birkhoffSeparated_eq_zero hT hf hf_meas r.2
  have htop := measure_birkhoffLimsup_top_eq_zero hT hf hf_meas
  have hbot := measure_birkhoffLiminf_bot_eq_zero hT hf hf_meas
  have hnotbad : ∀ᵐ ω ∂μ, ω ∉ bad := by
    rw [ae_iff]
    simpa using hbad
  have hnottop : ∀ᵐ ω ∂μ, birkhoffLimsup T f ω ≠ ⊤ := by
    rw [ae_iff]
    simpa using htop
  have hnotbot : ∀ᵐ ω ∂μ, birkhoffLiminf T f ω ≠ ⊥ := by
    rw [ae_iff]
    simpa using hbot
  filter_upwards [hnotbad, hnottop, hnotbot] with ω hω htop' hbot'
  have hosc : ∀ p q : ℚ, (p : ℝ) < q →
      ¬ (birkhoffLiminf T f ω < (p : ℝ) ∧
        ((q : ℝ) : EReal) < birkhoffLimsup T f ω) := by
    intro p q hpq hmem
    have : ω ∈ bad := by
      refine mem_iUnion.2 ⟨⟨(p, q), hpq⟩, ?_⟩
      simpa [birkhoffSeparated] using hmem
    exact hω this
  have hle : birkhoffLiminf T f ω ≤ birkhoffLimsup T f ω := by
    simpa [birkhoffLiminf, birkhoffLimsup] using
      liminf_le_limsup (f := atTop)
        (u := fun n => Real.toEReal (birkhoffAverage ℝ T f n ω))
        (ereal_isBoundedUnder_le _ _) (ereal_isBoundedUnder_ge _ _)
  have heq : birkhoffLiminf T f ω = birkhoffLimsup T f ω := by
    refine le_antisymm hle ?_
    by_contra hlt
    have hlt' : birkhoffLiminf T f ω < birkhoffLimsup T f ω := lt_of_not_ge hlt
    cases hL : birkhoffLiminf T f ω with
    | bot => exact (hbot' hL).elim
    | top => exact (not_top_lt (hL ▸ hlt')).elim
    | coe x =>
      cases hS : birkhoffLimsup T f ω with
      | bot => exact (not_lt_bot (hS ▸ hlt')).elim
      | top => exact (htop' hS).elim
      | coe y =>
        have hxy : x < y :=
          EReal.coe_lt_coe_iff.mp (by simpa [hL, hS] using hlt')
        obtain ⟨p, hpx, hpy⟩ := exists_rat_btwn hxy
        obtain ⟨q, hpq, hqy⟩ := exists_rat_btwn hpy
        exact (hosc p q hpq ⟨by simpa [hL] using (EReal.coe_lt_coe hpx),
          by simpa [hS] using (EReal.coe_lt_coe hqy)⟩).elim
  have hsup_bot : birkhoffLimsup T f ω ≠ ⊥ := fun h => hbot' (heq.trans h)
  have hcoe : ((birkhoffLimit T f ω : ℝ) : EReal) = birkhoffLimsup T f ω := by
    rw [birkhoffLimit, EReal.coe_toReal htop' hsup_bot]
  have hinf : liminf (fun n => Real.toEReal (birkhoffAverage ℝ T f n ω)) atTop =
      (birkhoffLimit T f ω : EReal) := by
    unfold birkhoffLiminf at heq
    rw [heq, hcoe]
  have hsup : limsup (fun n => Real.toEReal (birkhoffAverage ℝ T f n ω)) atTop =
      (birkhoffLimit T f ω : EReal) := by
    unfold birkhoffLimsup at hcoe
    rw [hcoe]
  have htend := tendsto_of_liminf_eq_limsup hinf hsup
    (ereal_isBoundedUnder_le _ _) (ereal_isBoundedUnder_ge _ _)
  exact (EReal.tendsto_coe).1 htend

end Null

end CKMA
