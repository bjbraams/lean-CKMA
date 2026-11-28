/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.LargeDeviations.Basic

import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Varadhan's lemma for bounded continuous functions (06.62)

`varadhan` states the Laplace principle for bounded continuous test functions under the two
bounds of `CKMA.HasLargeDeviationBounds`. Neither goodness nor lower semicontinuity of the rate is
required for this bounded form. Both the rate function and the variational supremum retain their
extended values. A TauCeti large deviation principle `h` at speed `(n + 1)⁻¹` supplies the
hypothesis as `hasLargeDeviationBounds_of_hasLDP h`.

## Main results

* `CKMA.varadhan`: Varadhan's integral lemma for bounded continuous functions (**06.62**).
-/

public section

noncomputable section

namespace CKMA

open scoped NNReal ENNReal

open MeasureTheory Filter Topology Set Finset

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- Normalized real logarithm of the Laplace integral at speed `n + 1`. -/
private noncomputable def laplaceRate (P : ℕ → Measure X) (f : X → ℝ) (n : ℕ) : ℝ :=
  (n + 1 : ℝ)⁻¹ * Real.log (∫ x, Real.exp ((n + 1 : ℝ) * f x) ∂P n)

/-- The bounded continuous Laplace integrand is integrable, and its integral is positive. -/
private lemma laplaceIntegral_pos [OpensMeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
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
private lemma sub_le_liminf_laplaceRate [OpensMeasurableSpace X] (P : ℕ → Measure X)
    [∀ n, IsProbabilityMeasure (P n)] {I : X → ℝ≥0∞}
    (hP : HasLargeDeviationBounds P I) {f : X → ℝ} (hf : Continuous f)
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

/-- Adding a sequence that converges to a real number raises the limsup by at most that
number. -/
private lemma limsup_add_le_of_tendsto {u v : ℕ → EReal} {r : ℝ}
    (hu : Tendsto u atTop (𝓝 (r : EReal))) :
    limsup (fun n ↦ u n + v n) atTop ≤ r + limsup v atTop := by
  have hsum : limsup (u + v) atTop ≤ limsup u atTop + limsup v atTop :=
    EReal.limsup_add_le
      (Or.inl <| by
        rw [hu.limsup_eq]
        exact EReal.coe_ne_bot r)
      (Or.inl <| by
        rw [hu.limsup_eq]
        exact EReal.coe_ne_top r)
  rw [hu.limsup_eq] at hsum
  exact hsum

omit [TopologicalSpace X] [MeasurableSpace X] in
/-- A real number minus the infimum of `I` over a set is at most every common upper bound of
the differences with the values of `I` on that set. -/
private lemma coe_sub_iInf₂_le {s : Set X} {I : X → ℝ≥0∞} {c : ℝ} {B : EReal}
    (h : ∀ x ∈ s, (c : EReal) - (I x : EReal) ≤ B) :
    (c : EReal) - ⨅ x ∈ s, (I x : EReal) ≤ B := by
  set β : EReal := ⨅ x ∈ s, (I x : EReal) with hβdef
  by_cases hβ : β = ⊤
  · simp [hβ, EReal.sub_top, bot_le]
  have hβbot : β ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0)
    (le_iInf₂ fun x _ ↦ EReal.coe_ennreal_nonneg (I x))
  set r : ℝ := β.toReal
  have hr : β = ↑r := (EReal.coe_toReal hβ hβbot).symm
  refine (EReal.ge_of_forall_gt_iff_ge).1 fun z hz ↦ ?_
  rw [hr, ← EReal.coe_sub] at hz
  have hzl : z < c - r := EReal.coe_lt_coe_iff.mp hz
  have hη : 0 < c - r - z := sub_pos.mpr hzl
  obtain ⟨x, hxs, hxI⟩ : ∃ x ∈ s, (I x : EReal) < ↑(r + (c - r - z)) := by
    have hlt : β < ↑(r + (c - r - z)) := by
      rw [hr]
      exact_mod_cast lt_add_of_pos_right r hη
    simpa only [hβdef, iInf_lt_iff, exists_prop] using hlt
  have hne : I x ≠ ∞ := by
    intro htop
    rw [htop, EReal.coe_ennreal_top] at hxI
    exact (lt_irrefl ⊤) (hxI.trans_le le_top)
  have hto : (I x).toReal < r + (c - r - z) := by
    rw [← EReal.coe_lt_coe_iff, EReal.coe_ennreal_toReal hne]
    exact hxI
  have hzE : (z : EReal) < ↑c - (I x : EReal) := by
    rw [← EReal.coe_ennreal_toReal hne, ← EReal.coe_sub]
    exact_mod_cast (by linarith : z < c - (I x).toReal)
  exact (hzE.trans_le (h x hxs)).le

omit [TopologicalSpace X] [MeasurableSpace X] in
/-- The bands `{(j - 1) δ ≤ f < j δ}` with distinct indices are disjoint. -/
private lemma pairwise_disjoint_bands {f : X → ℝ} {δ : ℝ} (hδ : 0 < δ) :
    Pairwise fun j k : ℤ ↦ Disjoint {x | ((j - 1 : ℤ) : ℝ) * δ ≤ f x ∧ f x < (j : ℝ) * δ}
      {x | ((k - 1 : ℤ) : ℝ) * δ ≤ f x ∧ f x < (k : ℝ) * δ} := by
  have key (j k : ℤ) (hlt : j < k) :
      Disjoint {x | ((j - 1 : ℤ) : ℝ) * δ ≤ f x ∧ f x < (j : ℝ) * δ}
        {x | ((k - 1 : ℤ) : ℝ) * δ ≤ f x ∧ f x < (k : ℝ) * δ} := by
    refine disjoint_left.2 fun x hxj hxk ↦ ?_
    have hjk : (j : ℝ) ≤ ((k - 1 : ℤ) : ℝ) := by exact_mod_cast Int.le_sub_one_iff.mpr hlt
    exact lt_irrefl _
      (hxj.2.trans_le ((mul_le_mul_of_nonneg_right hjk hδ.le).trans hxk.1))
  intro j k hjk
  rcases lt_or_gt_of_ne hjk with hlt | hlt
  · exact key j k hlt
  · exact (key k j hlt).symm

omit [TopologicalSpace X] [MeasurableSpace X] in
/-- When `|f| ≤ M`, the bands of width `δ` with indices from `⌊-M / δ⌋ + 1` to `⌊M / δ⌋ + 1`
cover the space. -/
private lemma iUnion_bands_eq_univ {f : X → ℝ} {M δ : ℝ} (hδ : 0 < δ) (hM : ∀ x, |f x| ≤ M) :
    ⋃ j ∈ Finset.Icc (⌊-M / δ⌋ + 1) (⌊M / δ⌋ + 1),
      {x | ((j - 1 : ℤ) : ℝ) * δ ≤ f x ∧ f x < (j : ℝ) * δ} = Set.univ := by
  ext x
  refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
  have hfx := abs_le.mp (hM x)
  let t : ℝ := f x / δ
  have hlo : -M / δ ≤ t := (div_le_div_iff_of_pos_right hδ).2 hfx.1
  have hhi : t ≤ M / δ := (div_le_div_iff_of_pos_right hδ).2 hfx.2
  have hmul1 : (⌊t⌋ : ℝ) * δ ≤ f x := by
    have := mul_le_mul_of_nonneg_right (Int.floor_le t) hδ.le
    simpa [t, div_mul_cancel₀ _ hδ.ne'] using this
  have hmul2 : f x < ((⌊t⌋ : ℝ) + 1) * δ := by
    have := mul_lt_mul_of_pos_right (Int.lt_floor_add_one t) hδ
    simpa [t, div_mul_cancel₀ _ hδ.ne'] using this
  refine mem_iUnion₂.mpr ⟨⌊t⌋ + 1, Finset.mem_Icc.mpr
    ⟨add_le_add_left (Int.floor_le_floor hlo) 1, add_le_add_left (Int.floor_le_floor hhi) 1⟩,
    ?_, ?_⟩
  · simpa [Int.cast_sub, Int.cast_one] using hmul1
  · simpa using hmul2

/-- Splitting the Laplace integral over finitely many disjoint bands `A j` covering the space,
on which `f < j δ`, bounds the Laplace rate by `log (card K) / (n + 1)` plus the largest
band contribution `j δ + logProbabilityRate P (F j) n`, for any sets `F j ⊇ A j`. -/
private lemma laplaceRate_le_add_finset_sup [OpensMeasurableSpace X] (P : ℕ → Measure X)
    [∀ n, IsProbabilityMeasure (P n)] {f : X → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) {δ : ℝ} {K : Finset ℤ} (hK : K.Nonempty) {A F : ℤ → Set X}
    (hAmeas : ∀ j, MeasurableSet (A j)) (hpair : Pairwise fun j k ↦ Disjoint (A j) (A k))
    (hcover : ⋃ j ∈ K, A j = Set.univ) (hAF : ∀ j, A j ⊆ F j)
    (hAf : ∀ j, ∀ x ∈ A j, f x < (j : ℝ) * δ) (n : ℕ) :
    (laplaceRate P f n : EReal) ≤ ↑((n + 1 : ℝ)⁻¹ * Real.log (K.card : ℝ)) +
      K.sup fun j ↦ ↑((j : ℝ) * δ) + logProbabilityRate P (F j) n := by
  have hg := laplaceIntegral_pos (P n) hf hM n
  let g : X → ℝ := fun x ↦ Real.exp ((n + 1 : ℝ) * f x)
  have hint_sum : ∫ x, g x ∂P n = ∑ j ∈ K, ∫ x in A j, g x ∂P n := by
    rw [← integral_biUnion_finset K (fun j _ ↦ hAmeas j)
      (fun j hj k hk hjk ↦ hpair hjk) (fun j _ ↦ hg.1.integrableOn), hcover,
      setIntegral_univ]
  have hpiece : ∀ j ∈ K, ∫ x in A j, g x ∂P n ≤
      Real.exp ((n + 1 : ℝ) * (j : ℝ) * δ) * (P n).real (F j) := by
    intro j hj
    have hconst : IntegrableOn (fun _ : X ↦ Real.exp ((n + 1 : ℝ) * (j : ℝ) * δ)) (A j)
        (P n) := integrableOn_const (measure_ne_top _ _)
    have hmono : ∫ x in A j, g x ∂P n ≤
        ∫ _ in A j, Real.exp ((n + 1 : ℝ) * (j : ℝ) * δ) ∂P n := by
      refine setIntegral_mono_on hg.1.integrableOn hconst (hAmeas j) ?_
      intro x hx
      refine Real.exp_le_exp.mpr ?_
      calc
        (n + 1 : ℝ) * f x ≤ (n + 1 : ℝ) * ((j : ℝ) * δ) :=
          mul_le_mul_of_nonneg_left (le_of_lt (hAf j x hx)) (by positivity)
        _ = (n + 1 : ℝ) * (j : ℝ) * δ := by ring
    refine hmono.trans ?_
    rw [setIntegral_const, smul_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left
      (measureReal_mono (hAF j) (measure_ne_top _ _)) (Real.exp_pos _).le
  let term : ℤ → ℝ := fun j ↦ Real.exp ((n + 1 : ℝ) * (j : ℝ) * δ) * (P n).real (F j)
  have hsumle : ∫ x, g x ∂P n ≤ ∑ j ∈ K, term j := by
    rw [hint_sum]
    exact Finset.sum_le_sum hpiece
  have hintpos : 0 < ∫ x, g x ∂P n := hg.2
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
  have hlogS : Real.log (∫ x, g x ∂P n) ≤ Real.log ((K.card : ℝ) * m) :=
    Real.log_le_log hintpos (hsumle.trans hSm)
  have hΛ : laplaceRate P f n ≤ (n + 1 : ℝ)⁻¹ * Real.log ((K.card : ℝ) * m) :=
    mul_le_mul_of_nonneg_left hlogS (inv_nonneg.mpr (by positivity))
  have hsplit : (n + 1 : ℝ)⁻¹ * Real.log ((K.card : ℝ) * m) =
      (n + 1 : ℝ)⁻¹ * Real.log (K.card : ℝ) + (n + 1 : ℝ)⁻¹ * Real.log m := by
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
  have hφ : ↑((n + 1 : ℝ)⁻¹ * Real.log m) =
      ↑((j : ℝ) * δ) + logProbabilityRate P (F j) n := by
    rw [hmlog, EReal.coe_add, logProbabilityRate_of_real_ne_zero hμpos.ne']
  rw [hsplit] at hΛ
  have : (laplaceRate P f n : EReal) ≤
      ↑((n + 1 : ℝ)⁻¹ * Real.log (K.card : ℝ)) + ↑((n + 1 : ℝ)⁻¹ * Real.log m) := by
    rw [← EReal.coe_add]
    exact_mod_cast hΛ
  have hsecond : ↑((n + 1 : ℝ)⁻¹ * Real.log m) ≤
      K.sup fun i ↦ ↑((i : ℝ) * δ) + logProbabilityRate P (F i) n := by
    rw [hφ]
    exact Finset.le_sup (f := fun i ↦ ↑((i : ℝ) * δ) + logProbabilityRate P (F i) n) hj
  exact this.trans (add_le_add_right hsecond _)

/-- On the closed set `{(j - 1) δ ≤ f}`, the contribution of the band with index `j` has
limsup at most the variational supremum plus `δ`. -/
private lemma limsup_band_le (P : ℕ → Measure X) {I : X → ℝ≥0∞}
    (hP : HasLargeDeviationBounds P I) {f : X → ℝ} (hf : Continuous f) (δ : ℝ) (j : ℤ) :
    limsup (fun n ↦ ↑((j : ℝ) * δ) +
        logProbabilityRate P {x | ((j - 1 : ℤ) : ℝ) * δ ≤ f x} n) atTop ≤
      (⨆ x, (f x : EReal) - (I x : EReal)) + δ := by
  refine (limsup_add_le_of_tendsto (u := fun _ ↦ (((j : ℝ) * δ : ℝ) : EReal))
    tendsto_const_nhds).trans ?_
  refine (add_le_add_right
    (hP.2 {x | ((j - 1 : ℤ) : ℝ) * δ ≤ f x} (isClosed_le continuous_const hf)) _).trans ?_
  rw [← sub_eq_add_neg]
  refine coe_sub_iInf₂_le fun x hxF ↦ ?_
  have hfx : (j : ℝ) * δ ≤ f x + δ := by
    have hge : ((j - 1 : ℤ) : ℝ) * δ ≤ f x := hxF
    have hsum : ((j - 1 : ℤ) : ℝ) * δ + δ = (j : ℝ) * δ := by push_cast; ring
    linarith
  have hsub : ↑((j : ℝ) * δ) - (I x : EReal) ≤ ((f x : EReal) + δ) - (I x : EReal) :=
    EReal.sub_le_sub (by exact_mod_cast hfx) le_rfl
  rw [add_real_sub_ennreal] at hsub
  exact hsub.trans <| add_le_add_left
    (le_iSup (fun y ↦ (f y : EReal) - (I y : EReal)) x) δ

/-- For every `δ > 0`, the Laplace rate has limsup at most the variational supremum plus `δ`.
The proof splits the range of `f` into finitely many bands of width `δ`. -/
private lemma limsup_laplaceRate_le_add [OpensMeasurableSpace X] (P : ℕ → Measure X)
    [∀ n, IsProbabilityMeasure (P n)] {I : X → ℝ≥0∞}
    (hP : HasLargeDeviationBounds P I) {f : X → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ x, |f x| ≤ M) {δ : ℝ} (hδ : 0 < δ) :
    limsup (fun n ↦ (laplaceRate P f n : EReal)) atTop ≤
      (⨆ x, (f x : EReal) - (I x : EReal)) + δ := by
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure (P 0)
  have hM0 : 0 ≤ M := (abs_nonneg (f x0)).trans (hM x0)
  let K : Finset ℤ := Finset.Icc (⌊-M / δ⌋ + 1) (⌊M / δ⌋ + 1)
  have hK : K.Nonempty := by
    refine Finset.nonempty_Icc.2 (add_le_add_left (Int.floor_le_floor ?_) 1)
    rw [div_le_div_iff_of_pos_right hδ]
    linarith
  let A : ℤ → Set X := fun j ↦ {x | ((j - 1 : ℤ) : ℝ) * δ ≤ f x ∧ f x < (j : ℝ) * δ}
  let F : ℤ → Set X := fun j ↦ {x | ((j - 1 : ℤ) : ℝ) * δ ≤ f x}
  have hAmeas (j : ℤ) : MeasurableSet (A j) :=
    (isClosed_le continuous_const hf).measurableSet.inter
      (isOpen_lt hf continuous_const).measurableSet
  have hle (n : ℕ) := laplaceRate_le_add_finset_sup P hf hM hK hAmeas
    (pairwise_disjoint_bands hδ) (iUnion_bands_eq_univ hδ hM) (F := F) (fun _ _ hx ↦ hx.1)
    (fun _ _ hx ↦ hx.2) n
  -- Stated without a type ascription: elaborating against the expected type times out.
  have hsup := limsup_finset_sup_le K
    (fun j n ↦ (((j : ℝ) * δ : ℝ) : EReal) + logProbabilityRate P (F j) n)
    (fun j _ ↦ limsup_band_le P hP hf δ j)
  have hε : Tendsto (fun n : ℕ ↦ (((n + 1 : ℝ)⁻¹ * Real.log (K.card : ℝ) : ℝ) : EReal))
      atTop (𝓝 ((0 : ℝ) : EReal)) := by
    refine (EReal.tendsto_coe).2 ?_
    have hinv : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using hinv.mul_const (Real.log (K.card : ℝ))
  refine (limsup_le_limsup (Eventually.of_forall hle)).trans
    ((limsup_add_le_of_tendsto hε).trans ?_)
  rw [EReal.coe_zero, zero_add]
  exact hsup

/-- The Laplace rate has limsup at most the variational supremum. -/
private lemma limsup_laplaceRate_le [OpensMeasurableSpace X] (P : ℕ → Measure X)
    [∀ n, IsProbabilityMeasure (P n)] {I : X → ℝ≥0∞}
    (hP : HasLargeDeviationBounds P I) {f : X → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    limsup (fun n ↦ (laplaceRate P f n : EReal)) atTop ≤
      ⨆ x, (f x : EReal) - (I x : EReal) := by
  set α : EReal := ⨆ x, (f x : EReal) - (I x : EReal)
  have hδ : ∀ δ : ℝ, 0 < δ →
      limsup (fun n ↦ (laplaceRate P f n : EReal)) atTop ≤ α + δ :=
    fun δ hδ ↦ limsup_laplaceRate_le_add P hP hf hM hδ
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
The extended supremum on the right includes points where `I = ∞`. A TauCeti large deviation
principle `h` at speed `(n + 1)⁻¹` supplies the hypothesis as `hasLargeDeviationBounds_of_hasLDP h`. -/
theorem varadhan [OpensMeasurableSpace X] (P : ℕ → Measure X)
    [∀ n, IsProbabilityMeasure (P n)] {I : X → ℝ≥0∞}
    (hP : HasLargeDeviationBounds P I)
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
