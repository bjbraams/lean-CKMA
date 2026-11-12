/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Semicontinuity.Basic

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Full large deviation bounds and bounded Varadhan (06.62)

`HasLargeDeviationPrinciple` combines lower bounds on open sets and upper bounds on
closed sets at speed `n + 1`. `logProbabilityRate` uses an extended logarithm so that
zero probabilities retain value minus infinity. `IsGoodRateFunction` separately records
lower semicontinuity and compact finite sublevels.

`varadhan` states the Laplace principle for bounded continuous test functions under the
full LDP. Goodness is not required for this bounded form. Both the rate function and
the variational supremum retain their extended values.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped NNReal ENNReal


open MeasureTheory Filter Topology Set Finset

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- A good rate function has compact finite sublevels and is lower semicontinuous. -/
def IsGoodRateFunction (I : X → ℝ≥0∞) : Prop :=
  LowerSemicontinuous I ∧ ∀ a : ℝ≥0, IsCompact {x | I x ≤ a}

/-- Logarithmic probability at speed `n + 1`. Extended logarithms retain zero probabilities. -/
def logProbabilityRate (P : ℕ → Measure X) (s : Set X) (n : ℕ) : EReal :=
  (((n + 1 : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (P n s)

/-- The open lower and closed upper bounds of a large deviation principle at speed `n + 1`. -/
def HasLargeDeviationPrinciple (P : ℕ → Measure X) (I : X → ℝ≥0∞) : Prop :=
  (∀ s, IsOpen s → -(⨅ x ∈ s, (I x : EReal)) ≤
    liminf (logProbabilityRate P s) atTop) ∧
  (∀ s, IsClosed s → limsup (logProbabilityRate P s) atTop ≤
    -(⨅ x ∈ s, (I x : EReal)))

/-- Normalized real logarithm of the Laplace integral at speed `n + 1`. -/
private noncomputable def laplaceRate (P : ℕ → Measure X) (f : X → ℝ) (n : ℕ) : ℝ :=
  (n + 1 : ℝ)⁻¹ * Real.log (∫ x, Real.exp ((n + 1 : ℝ) * f x) ∂P n)

/-- The bounded continuous Laplace integrand is integrable, and its integral is positive. -/
private lemma laplaceIntegral_pos [BorelSpace X] (P : Measure X) [IsProbabilityMeasure P]
    {f : X → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) (n : ℕ) :
    Integrable (fun x ↦ Real.exp ((n + 1 : ℝ) * f x)) P ∧
      0 < ∫ x, Real.exp ((n + 1 : ℝ) * f x) ∂P := by
  let g : X → ℝ := fun x ↦ Real.exp ((n + 1 : ℝ) * f x)
  have hgcont : Continuous g := Real.continuous_exp.comp (continuous_const.mul hf)
  have hgint : Integrable g P := by
    refine Integrable.of_bound hgcont.aestronglyMeasurable (Real.exp ((n + 1 : ℝ) * M)) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr <|
      mul_le_mul_of_nonneg_left (abs_le.mp (hM x)).2 (by positivity : 0 ≤ (n + 1 : ℝ))
  have hlow : ∀ x, Real.exp ((n + 1 : ℝ) * (-M)) ≤ g x := by
    intro x
    exact Real.exp_le_exp.mpr <|
      mul_le_mul_of_nonneg_left (abs_le.mp (hM x)).1 (by positivity : 0 ≤ (n + 1 : ℝ))
  have hint_const : ∫ _ : X, Real.exp ((n + 1 : ℝ) * (-M)) ∂P =
      Real.exp ((n + 1 : ℝ) * (-M)) := by
    rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  refine ⟨hgint, ?_⟩
  have hge : Real.exp ((n + 1 : ℝ) * (-M)) ≤ ∫ x, g x ∂P := by
    rw [← hint_const]
    exact integral_mono (integrable_const _) hgint hlow
  exact (Real.exp_pos _).trans_le hge

omit [TopologicalSpace X] in
/-- A vanishing probability has logarithmic rate bottom. -/
private lemma logProbabilityRate_of_real_eq_zero {P : ℕ → Measure X}
    [∀ n, IsProbabilityMeasure (P n)] {s : Set X} {n : ℕ} (hs : (P n).real s = 0) :
    logProbabilityRate P s n = ⊥ := by
  have hμ : P n s = 0 := (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hs
  rw [logProbabilityRate, hμ, ENNReal.log_zero]
  exact EReal.coe_mul_bot_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < (n + 1 : ℝ)))

omit [TopologicalSpace X] in
/-- A positive probability has logarithmic rate equal to the normalized real logarithm. -/
private lemma logProbabilityRate_of_real_ne_zero {P : ℕ → Measure X}
    [∀ n, IsProbabilityMeasure (P n)] {s : Set X} {n : ℕ} (hs : (P n).real s ≠ 0) :
    logProbabilityRate P s n =
      ↑((n + 1 : ℝ)⁻¹ * Real.log ((P n).real s)) := by
  have hμ : P n s ≠ 0 := (measureReal_ne_zero_iff (measure_ne_top _ _)).1 hs
  rw [logProbabilityRate, ENNReal.log_pos_real hμ (measure_ne_top _ _), measureReal_def,
    ← EReal.coe_mul]

/-- Adding a real commutes with subtraction of an extended nonnegative value. -/
private lemma add_real_sub_ennreal (a δ : ℝ) (b : ℝ≥0∞) :
    ((a : EReal) + δ) - (b : EReal) = ((a : EReal) - (b : EReal)) + δ := by
  by_cases hb : b = ∞
  · simp [hb, EReal.sub_top, EReal.bot_add]
  · rw [(EReal.coe_ennreal_toReal hb).symm]
    simp only [← EReal.coe_add, ← EReal.coe_sub]
    norm_cast
    ring

/-- The limsup of a finset supremum is at most a common upper bound of the limsups. -/
private lemma limsup_finset_sup_le {ι : Type*} (K : Finset ι) (φ : ι → ℕ → EReal) {b : EReal}
    (h : ∀ j ∈ K, limsup (φ j) atTop ≤ b) :
    limsup (fun n ↦ K.sup (fun j ↦ φ j n)) atTop ≤ b := by
  rw [limsup_le_iff]
  intro y hy
  have hybot : (⊥ : EReal) < y := bot_le.trans_lt hy
  have hEv : ∀ j ∈ K, ∀ᶠ n in atTop, φ j n < y := fun j hj ↦
    eventually_lt_of_limsup_lt ((h j hj).trans_lt hy)
  filter_upwards [(eventually_all_finset K).2 hEv] with n hn
  exact (Finset.sup_lt_iff hybot).2 hn

/-- Each value `f x - I x` lies under the liminf of the Laplace rate. -/
private lemma sub_le_liminf_laplaceRate [BorelSpace X] (P : ℕ → Measure X)
    [∀ n, IsProbabilityMeasure (P n)] {I : X → ℝ≥0∞}
    (hP : HasLargeDeviationPrinciple P I) {f : X → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ x, |f x| ≤ M) (x : X) :
    (f x : EReal) - (I x : EReal) ≤
      liminf (fun n ↦ (laplaceRate P f n : EReal)) atTop := by
  by_cases hI : I x = ∞
  · rw [hI, EReal.coe_ennreal_top, EReal.sub_top]
    exact bot_le
  have hIx : (I x : EReal) = ↑(I x).toReal := (EReal.coe_ennreal_toReal hI).symm
  let L : EReal := liminf (fun n ↦ (laplaceRate P f n : EReal)) atTop
  suffices hε : ∀ ε : ℝ, 0 < ε → ↑(f x - ε - (I x).toReal) ≤ L by
    refine (EReal.ge_of_forall_gt_iff_ge).1 fun z hz ↦ ?_
    have hzR : z < f x - (I x).toReal := by
      rw [hIx, ← EReal.coe_sub] at hz
      exact EReal.coe_lt_coe_iff.mp hz
    have hpos : 0 < f x - (I x).toReal - z := sub_pos.mpr hzR
    convert hε _ hpos using 1
    norm_cast
    ring
  intro ε hε
  let a : ℝ := f x - ε
  let U : Set X := {y | a < f y}
  have hUopen : IsOpen U := isOpen_lt continuous_const hf
  have hxU : x ∈ U := by
    change a < f x
    simpa [a] using sub_lt_self (f x) hε
  have hg : ∀ n : ℕ, Integrable (fun y ↦ Real.exp ((n + 1 : ℝ) * f y)) (P n) ∧
      0 < ∫ y, Real.exp ((n + 1 : ℝ) * f y) ∂P n :=
    fun n ↦ laplaceIntegral_pos (P n) hf hM n
  have hstep : ∀ n, (a : EReal) + logProbabilityRate P U n ≤ (laplaceRate P f n : EReal) := by
    intro n
    by_cases hμ : (P n).real U = 0
    · rw [logProbabilityRate_of_real_eq_zero hμ, EReal.add_bot]
      exact bot_le
    · have hμpos : 0 < (P n).real U :=
        lt_of_le_of_ne measureReal_nonneg (Ne.symm hμ)
      let g : X → ℝ := fun y ↦ Real.exp ((n + 1 : ℝ) * f y)
      have hUg : ∀ y ∈ U, Real.exp ((n + 1 : ℝ) * a) ≤ g y := by
        intro y hy
        exact Real.exp_le_exp.mpr <|
          mul_le_mul_of_nonneg_left (le_of_lt hy) (by positivity : 0 ≤ (n + 1 : ℝ))
      have hset : Real.exp ((n + 1 : ℝ) * a) * (P n).real U ≤ ∫ y in U, g y ∂P n :=
        setIntegral_ge_of_const_le_real hUopen.measurableSet (measure_ne_top _ _) hUg
          (hg n).1.integrableOn
      have hint : ∫ y in U, g y ∂P n ≤ ∫ y, g y ∂P n :=
        setIntegral_le_integral (hg n).1 (Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)
      have hbase : Real.exp ((n + 1 : ℝ) * a) * (P n).real U ≤ ∫ y, g y ∂P n :=
        hset.trans hint
      have hbasepos : 0 < Real.exp ((n + 1 : ℝ) * a) * (P n).real U :=
        mul_pos (Real.exp_pos _) hμpos
      have hlog : Real.log (Real.exp ((n + 1 : ℝ) * a) * (P n).real U) ≤
          Real.log (∫ y, g y ∂P n) :=
        Real.log_le_log hbasepos hbase
      have hmul : (n + 1 : ℝ)⁻¹ *
          Real.log (Real.exp ((n + 1 : ℝ) * a) * (P n).real U) ≤ laplaceRate P f n :=
        mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr (by positivity))
      have hrewrite : (n + 1 : ℝ)⁻¹ *
          Real.log (Real.exp ((n + 1 : ℝ) * a) * (P n).real U) =
          a + (n + 1 : ℝ)⁻¹ * Real.log ((P n).real U) := by
        rw [Real.log_mul (Real.exp_pos _).ne' hμpos.ne', Real.log_exp, mul_add,
          ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
      rw [hrewrite] at hmul
      rw [logProbabilityRate_of_real_ne_zero hμ, ← EReal.coe_add]
      exact_mod_cast hmul
  have hliminf : (a : EReal) + liminf (logProbabilityRate P U) atTop ≤ L := by
    have hadd := EReal.le_liminf_add (f := atTop)
      (u := fun _ : ℕ ↦ (a : EReal)) (v := logProbabilityRate P U)
    have hconst : liminf (fun _ : ℕ ↦ (a : EReal)) atTop = a := liminf_const _
    rw [hconst] at hadd
    exact hadd.trans <| liminf_le_liminf (Eventually.of_forall hstep)
  have hopen : (a : EReal) - ⨅ y ∈ U, (I y : EReal) ≤ L := by
    have hLDP := hP.1 U hUopen
    have : (a : EReal) + (- ⨅ y ∈ U, (I y : EReal)) ≤
        (a : EReal) + liminf (logProbabilityRate P U) atTop :=
      add_le_add_right hLDP (a : EReal)
    simpa [sub_eq_add_neg, L] using this.trans hliminf
  have hIxU : ⨅ y ∈ U, (I y : EReal) ≤ (I x : EReal) := iInf₂_le x hxU
  have : (a : EReal) - (I x : EReal) ≤ L :=
    (EReal.sub_le_sub le_rfl hIxU).trans hopen
  unfold a at this
  rw [hIx, ← EReal.coe_sub] at this
  exact this

/-- The Laplace rate has limsup at most the variational supremum. -/
private lemma limsup_laplaceRate_le [BorelSpace X] (P : ℕ → Measure X)
    [∀ n, IsProbabilityMeasure (P n)] {I : X → ℝ≥0∞}
    (hP : HasLargeDeviationPrinciple P I) {f : X → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    limsup (fun n ↦ (laplaceRate P f n : EReal)) atTop ≤
      ⨆ x, (f x : EReal) - (I x : EReal) := by
  set α : EReal := ⨆ x, (f x : EReal) - (I x : EReal)
  have hδ : ∀ δ : ℝ, 0 < δ →
      limsup (fun n ↦ (laplaceRate P f n : EReal)) atTop ≤ α + δ := by
    intro δ hδ
    obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure (P 0)
    have hM0 : 0 ≤ M := (abs_nonneg (f x0)).trans (hM x0)
    let j0 : ℤ := ⌊-M / δ⌋ + 1
    let j1 : ℤ := ⌊M / δ⌋ + 1
    have hj01 : j0 ≤ j1 := by
      have hdiv : -M / δ ≤ M / δ := by
        rw [div_le_div_iff_of_pos_right hδ]
        linarith
      exact add_le_add_left (Int.floor_le_floor hdiv) 1
    let K : Finset ℤ := Icc j0 j1
    have hK : K.Nonempty := ⟨j0, mem_Icc.mpr ⟨le_rfl, hj01⟩⟩
    let A : ℤ → Set X := fun j ↦ {x | ((j - 1 : ℤ) : ℝ) * δ ≤ f x ∧ f x < (j : ℝ) * δ}
    let F : ℤ → Set X := fun j ↦ {x | ((j - 1 : ℤ) : ℝ) * δ ≤ f x}
    have hAmeas : ∀ j, MeasurableSet (A j) := by
      intro j
      exact (isClosed_le continuous_const hf).measurableSet.inter
        (isOpen_lt hf continuous_const).measurableSet
    have hFclosed : ∀ j, IsClosed (F j) := fun j ↦ isClosed_le continuous_const hf
    have hAF : ∀ j, A j ⊆ F j := fun j x hx ↦ hx.1
    have hpair : Pairwise (fun j k ↦ Disjoint (A j) (A k)) := by
      intro j k hjk
      rcases lt_or_gt_of_ne hjk with hlt | hlt
      · refine disjoint_left.2 fun x hxj hxk ↦ ?_
        have hjk' : (j : ℝ) ≤ (k : ℝ) - 1 := by
          exact_mod_cast (Int.le_sub_one_iff.mpr hlt)
        have hmul : (j : ℝ) * δ ≤ ((k : ℝ) - 1) * δ :=
          mul_le_mul_of_nonneg_right hjk' hδ.le
        have hfk : ((k - 1 : ℤ) : ℝ) * δ ≤ f x := hxk.1
        have hfj : f x < (j : ℝ) * δ := hxj.2
        have hcast : ((k - 1 : ℤ) : ℝ) = (k : ℝ) - 1 := by push_cast; ring
        have hltx : f x < f x := by
          calc
            f x < (j : ℝ) * δ := hfj
            _ ≤ ((k : ℝ) - 1) * δ := hmul
            _ = ((k - 1 : ℤ) : ℝ) * δ := by rw [hcast]
            _ ≤ f x := hfk
        exact lt_irrefl _ hltx
      · refine disjoint_left.2 fun x hxj hxk ↦ ?_
        have hjk' : (k : ℝ) ≤ (j : ℝ) - 1 := by
          exact_mod_cast (Int.le_sub_one_iff.mpr hlt)
        have hmul : (k : ℝ) * δ ≤ ((j : ℝ) - 1) * δ :=
          mul_le_mul_of_nonneg_right hjk' hδ.le
        have hfj : ((j - 1 : ℤ) : ℝ) * δ ≤ f x := hxj.1
        have hfk : f x < (k : ℝ) * δ := hxk.2
        have hcast : ((j - 1 : ℤ) : ℝ) = (j : ℝ) - 1 := by push_cast; ring
        have hltx : f x < f x := by
          calc
            f x < (k : ℝ) * δ := hfk
            _ ≤ ((j : ℝ) - 1) * δ := hmul
            _ = ((j - 1 : ℤ) : ℝ) * δ := by rw [hcast]
            _ ≤ f x := hfj
        exact lt_irrefl _ hltx
    have hcover : ⋃ j ∈ K, A j = Set.univ := by
      ext x
      refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
      have hfx := abs_le.mp (hM x)
      let t : ℝ := f x / δ
      let j : ℤ := ⌊t⌋ + 1
      have hjmem : j ∈ K := by
        have hlo : -M / δ ≤ t := by
          change -M / δ ≤ f x / δ
          exact (div_le_div_iff_of_pos_right hδ).2 hfx.1
        have hhi : t ≤ M / δ := by
          change f x / δ ≤ M / δ
          exact (div_le_div_iff_of_pos_right hδ).2 hfx.2
        refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
        · exact add_le_add_left (Int.floor_le_floor hlo) 1
        · exact add_le_add_left (Int.floor_le_floor hhi) 1
      have hfloor : (⌊t⌋ : ℝ) ≤ t := Int.floor_le t
      have hfloor' : t < (⌊t⌋ : ℝ) + 1 := Int.lt_floor_add_one t
      have hmul1 : (⌊t⌋ : ℝ) * δ ≤ f x := by
        have := mul_le_mul_of_nonneg_right hfloor hδ.le
        simpa [t, div_mul_cancel₀ _ hδ.ne'] using this
      have hmul2 : f x < ((⌊t⌋ : ℝ) + 1) * δ := by
        have := mul_lt_mul_of_pos_right hfloor' hδ
        simpa [t, div_mul_cancel₀ _ hδ.ne'] using this
      refine mem_iUnion₂.mpr ⟨j, hjmem, ?_, ?_⟩
      · simpa [j, Int.cast_sub, Int.cast_one] using hmul1
      · simpa [j] using hmul2
    have hg (n : ℕ) : Integrable (fun x ↦ Real.exp ((n + 1 : ℝ) * f x)) (P n) ∧
        0 < ∫ x, Real.exp ((n + 1 : ℝ) * f x) ∂P n :=
      laplaceIntegral_pos (P n) hf hM n
    have hpoint : ∀ j, ∀ x ∈ F j,
        ↑((j : ℝ) * δ) - (I x : EReal) ≤ α + δ := by
      intro j x hxF
      have hfx : (j : ℝ) * δ ≤ f x + δ := by
        have hge : ((j - 1 : ℤ) : ℝ) * δ ≤ f x := hxF
        have hsum : ((j - 1 : ℤ) : ℝ) * δ + δ = (j : ℝ) * δ := by push_cast; ring
        linarith
      have hsub : ↑((j : ℝ) * δ) - (I x : EReal) ≤
          ((f x : EReal) + δ) - (I x : EReal) :=
        EReal.sub_le_sub (by exact_mod_cast hfx) le_rfl
      rw [add_real_sub_ennreal] at hsub
      exact hsub.trans <| add_le_add_left
        (le_iSup (fun y ↦ (f y : EReal) - (I y : EReal)) x) δ
    have hterm : ∀ j, limsup (fun n ↦ ↑((j : ℝ) * δ) + logProbabilityRate P (F j) n) atTop ≤
        α + δ := by
      intro j
      let β : EReal := ⨅ x ∈ F j, (I x : EReal)
      have hLDP : limsup (logProbabilityRate P (F j)) atTop ≤ -β := hP.2 (F j) (hFclosed j)
      have hadd : limsup (fun n ↦ ↑((j : ℝ) * δ) + logProbabilityRate P (F j) n) atTop ≤
          ↑((j : ℝ) * δ) + limsup (logProbabilityRate P (F j)) atTop := by
        let u : ℕ → EReal := fun _ ↦ ↑((j : ℝ) * δ)
        let v : ℕ → EReal := logProbabilityRate P (F j)
        have hconst : limsup u atTop = ↑((j : ℝ) * δ) := limsup_const _
        have hsum : limsup (u + v) atTop ≤ limsup u atTop + limsup v atTop :=
          EReal.limsup_add_le
            (Or.inl <| by
              rw [hconst]
              exact EReal.coe_ne_bot _)
            (Or.inl <| by
              rw [hconst]
              exact EReal.coe_ne_top _)
        have hfun : u + v = fun n ↦ u n + v n := by
          funext n
          rfl
        rw [hfun, hconst] at hsum
        simpa [u, v] using hsum
      have : ↑((j : ℝ) * δ) + limsup (logProbabilityRate P (F j)) atTop ≤
          ↑((j : ℝ) * δ) - β := by
        rw [sub_eq_add_neg]
        exact add_le_add_right hLDP ↑((j : ℝ) * δ)
      refine (hadd.trans this).trans ?_
      by_cases hβ : β = ⊤
      · simp [hβ, EReal.sub_top, bot_le]
      · have hβbot : β ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0)
          (le_iInf₂ fun x _ ↦ EReal.coe_ennreal_nonneg (I x))
        let r : ℝ := β.toReal
        have hr : β = ↑r := (EReal.coe_toReal hβ hβbot).symm
        refine (EReal.ge_of_forall_gt_iff_ge).1 ?_
        intro z hz
        rw [hr, ← EReal.coe_sub] at hz
        have hzl : z < (j : ℝ) * δ - r := EReal.coe_lt_coe_iff.mp hz
        let η : ℝ := (j : ℝ) * δ - r - z
        have hη : 0 < η := sub_pos.mpr hzl
        have hfind : ∃ x, x ∈ F j ∧ (I x : EReal) < ↑(r + η) := by
          have hlt : β < ↑(r + η) := by
            rw [hr]
            exact_mod_cast lt_add_of_pos_right r hη
          simpa only [β, iInf_lt_iff, exists_prop] using hlt
        obtain ⟨x, hxF, hxI⟩ := hfind
        have hne : I x ≠ ∞ := by
          intro htop
          rw [htop, EReal.coe_ennreal_top] at hxI
          exact (lt_irrefl ⊤) (hxI.trans_le le_top)
        have hto : (I x).toReal < r + η := by
          rw [← EReal.coe_lt_coe_iff, EReal.coe_ennreal_toReal hne]
          exact hxI
        have hzlt : z < (j : ℝ) * δ - (I x).toReal := by
          have hsum : r + η = (j : ℝ) * δ - z := by
            simp only [η]
            ring
          linarith
        have hzE : (z : EReal) < ↑((j : ℝ) * δ) - (I x : EReal) := by
          rw [← EReal.coe_ennreal_toReal hne, ← EReal.coe_sub]
          exact_mod_cast hzlt
        exact (hzE.trans_le (hpoint j x hxF)).le
    let φ : ℤ → ℕ → EReal := fun j n ↦ ↑((j : ℝ) * δ) + logProbabilityRate P (F j) n
    have hsup : limsup (fun n ↦ K.sup (fun j ↦ φ j n)) atTop ≤ α + δ :=
      limsup_finset_sup_le K φ fun j hj ↦ hterm j
    let ε : ℕ → ℝ := fun n ↦ (n + 1 : ℝ)⁻¹ * Real.log (K.card : ℝ)
    have hε : Tendsto (fun n ↦ (ε n : EReal)) atTop (𝓝 (0 : EReal)) := by
      refine (EReal.tendsto_coe).2 ?_
      have hinv : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
        have hsum : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
          simpa [Nat.cast_add] using
            tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
        exact hsum.inv_tendsto_atTop
      simpa [ε] using hinv.mul_const (Real.log (K.card : ℝ))
    have hle : ∀ n, (laplaceRate P f n : EReal) ≤
        ↑(ε n) + K.sup (fun j ↦ φ j n) := by
      intro n
      let g : X → ℝ := fun x ↦ Real.exp ((n + 1 : ℝ) * f x)
      have hint_sum : ∫ x, g x ∂P n = ∑ j ∈ K, ∫ x in A j, g x ∂P n := by
        rw [← integral_biUnion_finset K (fun j _ ↦ hAmeas j)
          (fun j hj k hk hjk ↦ hpair hjk) (fun j _ ↦ (hg n).1.integrableOn), hcover,
          setIntegral_univ]
      have hpiece : ∀ j ∈ K, ∫ x in A j, g x ∂P n ≤
          Real.exp ((n + 1 : ℝ) * (j : ℝ) * δ) * (P n).real (F j) := by
        intro j hj
        have hconst : IntegrableOn (fun _ : X ↦ Real.exp ((n + 1 : ℝ) * (j : ℝ) * δ)) (A j)
            (P n) := integrableOn_const (measure_ne_top _ _)
        have hmono : ∫ x in A j, g x ∂P n ≤
            ∫ _ in A j, Real.exp ((n + 1 : ℝ) * (j : ℝ) * δ) ∂P n := by
          refine setIntegral_mono_on (hg n).1.integrableOn hconst (hAmeas j) ?_
          intro x hx
          refine Real.exp_le_exp.mpr ?_
          calc
            (n + 1 : ℝ) * f x ≤ (n + 1 : ℝ) * ((j : ℝ) * δ) :=
              mul_le_mul_of_nonneg_left (le_of_lt hx.2) (by positivity)
            _ = (n + 1 : ℝ) * (j : ℝ) * δ := by ring
        refine hmono.trans ?_
        rw [setIntegral_const, smul_eq_mul, mul_comm]
        exact mul_le_mul_of_nonneg_left
          (measureReal_mono (hAF j) (measure_ne_top _ _)) (Real.exp_pos _).le
      let term : ℤ → ℝ := fun j ↦ Real.exp ((n + 1 : ℝ) * (j : ℝ) * δ) * (P n).real (F j)
      have hsumle : ∫ x, g x ∂P n ≤ ∑ j ∈ K, term j := by
        rw [hint_sum]
        exact Finset.sum_le_sum hpiece
      have hintpos : 0 < ∫ x, g x ∂P n := (hg n).2
      have hSpos : 0 < ∑ j ∈ K, term j := hintpos.trans_le hsumle
      let m : ℝ := K.sup' hK term
      have hmbound : ∀ j ∈ K, term j ≤ m := (sup'_le_iff hK term).1 le_rfl
      have hSm : ∑ j ∈ K, term j ≤ (K.card : ℝ) * m := by
        calc
          ∑ j ∈ K, term j ≤ ∑ _j ∈ K, m := Finset.sum_le_sum hmbound
          _ = (K.card : ℝ) * m := by simp [sum_const, nsmul_eq_mul]
      have hmpos : 0 < m := by
        have hcard : 0 < (K.card : ℝ) := by exact_mod_cast hK.card_pos
        exact (mul_pos_iff_of_pos_left hcard).1 (hSpos.trans_le hSm)
      obtain ⟨j, hj, hjm⟩ := exists_mem_eq_sup' hK term
      have hm_eq : m = term j := by
        simpa [m] using hjm
      have hμpos : 0 < (P n).real (F j) := by
        have : 0 < term j := hm_eq ▸ hmpos
        exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).1 this
      have hlogS : Real.log (∫ x, g x ∂P n) ≤
          Real.log ((K.card : ℝ) * m) :=
        Real.log_le_log hintpos (hsumle.trans hSm)
      have hΛ : laplaceRate P f n ≤
          (n + 1 : ℝ)⁻¹ * Real.log ((K.card : ℝ) * m) :=
        mul_le_mul_of_nonneg_left hlogS (inv_nonneg.mpr (by positivity))
      have hsplit : (n + 1 : ℝ)⁻¹ * Real.log ((K.card : ℝ) * m) =
          ε n + (n + 1 : ℝ)⁻¹ * Real.log m := by
        rw [Real.log_mul (Nat.cast_ne_zero.mpr hK.card_pos.ne') hmpos.ne', mul_add]
      have hmlog : (n + 1 : ℝ)⁻¹ * Real.log m =
          (j : ℝ) * δ + (n + 1 : ℝ)⁻¹ * Real.log ((P n).real (F j)) := by
        rw [hm_eq, Real.log_mul (Real.exp_pos _).ne' hμpos.ne', Real.log_exp, mul_add]
        congr 1
        calc
          (n + 1 : ℝ)⁻¹ * ((n + 1) * (j : ℝ) * δ) =
              (n + 1 : ℝ)⁻¹ * ((n + 1) * ((j : ℝ) * δ)) := by ring
          _ = (j : ℝ) * δ := by
            rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
      have hφ : ↑((n + 1 : ℝ)⁻¹ * Real.log m) = φ j n := by
        rw [hmlog]
        unfold φ
        rw [EReal.coe_add, logProbabilityRate_of_real_ne_zero hμpos.ne']
      rw [hsplit] at hΛ
      have : (laplaceRate P f n : EReal) ≤ ↑(ε n) + ↑((n + 1 : ℝ)⁻¹ * Real.log m) := by
        rw [← EReal.coe_add]
        exact_mod_cast hΛ
      have hsecond : ↑((n + 1 : ℝ)⁻¹ * Real.log m) ≤ K.sup (fun i ↦ φ i n) := by
        rw [hφ]
        exact Finset.le_sup (f := fun i ↦ φ i n) hj
      exact this.trans (add_le_add_right hsecond ↑(ε n))
    have hlim : limsup (fun n ↦ ↑(ε n) + K.sup (fun j ↦ φ j n)) atTop ≤
        limsup (fun n ↦ (ε n : EReal)) atTop +
          limsup (fun n ↦ K.sup (fun j ↦ φ j n)) atTop := by
      let u : ℕ → EReal := fun n ↦ (ε n : EReal)
      let v : ℕ → EReal := fun n ↦ K.sup (fun j ↦ φ j n)
      have hsum : limsup (u + v) atTop ≤ limsup u atTop + limsup v atTop :=
        EReal.limsup_add_le
          (Or.inl <| by
            rw [Tendsto.limsup_eq hε]
            exact EReal.coe_ne_bot 0)
          (Or.inl <| by
            rw [Tendsto.limsup_eq hε]
            exact EReal.coe_ne_top 0)
      have hfun : u + v = fun n ↦ u n + v n := by
        funext n
        rfl
      rw [hfun] at hsum
      simpa [u, v] using hsum
    have : limsup (fun n ↦ (laplaceRate P f n : EReal)) atTop ≤
        limsup (fun n ↦ ↑(ε n) + K.sup (fun j ↦ φ j n)) atTop :=
      limsup_le_limsup (Eventually.of_forall hle)
    refine this.trans (hlim.trans ?_)
    rw [Tendsto.limsup_eq hε, zero_add]
    exact hsup
  refine (EReal.le_of_forall_lt_iff_le).1 ?_
  intro z hz
  have hαtop : α ≠ ⊤ := (hz.trans (EReal.coe_lt_top z)).ne
  by_cases hαbot : α = ⊥
  · have hbot : limsup (fun n ↦ (laplaceRate P f n : EReal)) atTop ≤ ⊥ := by
      simpa [hαbot, EReal.bot_add] using hδ 1 one_pos
    exact hbot.trans bot_le
  · have ha : α = ↑α.toReal := (EReal.coe_toReal hαtop hαbot).symm
    rw [ha] at hz
    generalize hδeq : z - α.toReal = δ
    have hδpos : 0 < δ := by
      rw [← hδeq]
      exact sub_pos.mpr (EReal.coe_lt_coe_iff.mp hz)
    have hle := hδ δ hδpos
    have hcancel : α.toReal + δ = z := by
      rw [← hδeq]
      ring
    rw [ha, ← EReal.coe_add, hcancel] at hle
    exact hle

/-- **06.62**: Varadhan's integral lemma for bounded continuous functions.
The real logarithm on the left is legitimate because each integral is strictly positive.
The extended supremum on the right includes points where `I = ∞`. -/
theorem varadhan [BorelSpace X] (P : ℕ → Measure X)
    [∀ n, IsProbabilityMeasure (P n)] {I : X → ℝ≥0∞}
    (hP : HasLargeDeviationPrinciple P I)
    {f : X → ℝ} (hf : Continuous f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    Tendsto (fun n : ℕ ↦ (((n + 1 : ℝ)⁻¹ *
      Real.log (∫ x, Real.exp ((n + 1 : ℝ) * f x) ∂P n) : ℝ) : EReal))
      atTop (𝓝 (⨆ x, (f x : EReal) - (I x : EReal))) := by
  obtain ⟨M, hM⟩ := hb
  have hlow : ⨆ x, (f x : EReal) - (I x : EReal) ≤
      liminf (fun n ↦ (laplaceRate P f n : EReal)) atTop :=
    iSup_le fun x ↦ sub_le_liminf_laplaceRate P hP hf hM x
  have hup := limsup_laplaceRate_le P hP hf hM
  simpa [laplaceRate] using tendsto_of_le_liminf_of_limsup_le hlow hup

end CKMA
