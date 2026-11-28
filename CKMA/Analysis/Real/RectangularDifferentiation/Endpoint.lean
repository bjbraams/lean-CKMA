/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.RectangularDifferentiation.Iteration

/-!
# Truncated slice bounds for the strong maximal operator

Distribution estimates for the slice strong maximal function `CKMA.partialStrongMax` in
dimension `n + 1`. Under the weak `L(log⁺L)^{n-1}` bound in dimension `n`, Fubini bounds the
distribution of the slice maximal function, and discarding the values of `f` at most half the
height keeps high superlevels. Truncating the slice maximal function below half the height, the
one-dimensional weak-type bound in the last coordinate gives
`|{M f > a}| ≤ (10 / a) ∫ truncatedPartial f a`.

## Main definitions

* `CKMA.HasStrongMaximalOrliczBound`: the weak `L(log⁺L)^{n-1}` bound for the strong maximal
  operator in dimension `n` with a given constant.
* `CKMA.StrongMaximal.halfLevelTrunc`: truncation discarding values of absolute value at most
  `t / 2`.
* `CKMA.StrongMaximal.truncatedPartial`: the partial strong maximal function
  `CKMA.partialStrongMax`, set to zero on and below the half-height threshold.

## Main results

* `CKMA.measurable_partialStrongMax`: measurability of the slice strong maximal function.
* `CKMA.volume_partialStrongMax_gt_le`, `CKMA.volume_partialStrongMax_gt_le_trunc`: the
  distribution of the slice maximal function, without and with truncation of `f`.
* `CKMA.strongMaximal_volume_le_truncIntegral`: the distribution of the strong maximal function is
  at most `10 / a` times the integral of the truncated partial maximal function.

## Implementation notes

The proof of `CKMA.strongMaximal_volume_le_truncIntegral` places the strong maximal superlevel,
up to the coordinate equivalence, inside a countable union of products of rational intervals
with one-dimensional superlevels of the truncated partial maximal function.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Set StrongMaximal
open scoped ENNReal

/-- The weak `L(log⁺L)^{n-1}` bound for the strong maximal operator in dimension `n` with
constant `C`: `|{M g > b}| ≤ C ∫ Φₙ(|g| / b)` for every measurable `g` and `b > 0`. -/
@[expose]
def HasStrongMaximalOrliczBound (n : ℕ) (C : ℝ) : Prop :=
  ∀ (g : (Fin n → ℝ) → ℝ), Measurable g → ∀ b : ℝ, 0 < b →
    volume {z | ENNReal.ofReal b < strongMaximalFunction g z} ≤
      ENNReal.ofReal C * ∫⁻ z, ENNReal.ofReal (strongMaximalGrowth n (|g z| / b))

/-- Unfolding of `CKMA.HasStrongMaximalOrliczBound`. -/
theorem hasStrongMaximalOrliczBound_iff {n : ℕ} {C : ℝ} :
    HasStrongMaximalOrliczBound n C ↔ ∀ (g : (Fin n → ℝ) → ℝ), Measurable g → ∀ b : ℝ, 0 < b →
      volume {z | ENNReal.ofReal b < strongMaximalFunction g z} ≤
        ENNReal.ofReal C * ∫⁻ z, ENNReal.ofReal (strongMaximalGrowth n (|g z| / b)) :=
  Iff.rfl

/-- A strict partial-maximal inequality is a countable union of rational slice averages. -/
private theorem partialStrongMax_gt_eq {n : ℕ} (hn : 0 < n) (f : (Fin (n + 1) → ℝ) → ℝ)
    (c : ℝ≥0∞) :
    {p : ℝ × (Fin n → ℝ) | c < partialStrongMax f p.1 p.2} =
      ⋃ J : RatRectangle n,
        {y | c < sliceRatAverage f y J} ×ˢ J.carrier := by
  ext ⟨y, z⟩
  simp only [mem_ofPred_eq, mem_iUnion, mem_prod]
  rw [partialStrongMax_eq_ratSup hn f y z, lt_iSup_iff]
  constructor
  · rintro ⟨J, hJ⟩
    rw [lt_iSup_iff] at hJ
    obtain ⟨hz, havg⟩ := hJ
    exact ⟨J, havg, hz⟩
  · rintro ⟨J, havg, hz⟩
    exact ⟨J, lt_iSup_iff.2 ⟨hz, havg⟩⟩

/-- Superlevel sets of the partial maximal function are measurable. -/
private theorem measurableSet_partialStrongMax_gt {n : ℕ} (hn : 0 < n)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) (c : ℝ≥0∞) :
    MeasurableSet {p : ℝ × (Fin n → ℝ) | c < partialStrongMax f p.1 p.2} := by
  rw [partialStrongMax_gt_eq hn f c]
  refine MeasurableSet.iUnion fun J ↦ MeasurableSet.prod ?_ ?_
  · exact measurableSet_lt measurable_const (measurable_sliceRatAverage hf J)
  · rw [← J.carrier_toOpen]
    exact J.toOpen.measurableSet_carrier

/-- The partial maximal function is measurable on the product of the last coordinate and the
initial segment. -/
theorem measurable_partialStrongMax {n : ℕ} (hn : 0 < n)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) :
    Measurable (fun p : ℝ × (Fin n → ℝ) ↦ partialStrongMax f p.1 p.2) :=
  measurable_of_Ioi fun c ↦ measurableSet_partialStrongMax_gt hn hf c

/-- Integrating the inductive distribution bound of the slices recovers the full integral. -/
theorem volume_partialStrongMax_gt_le {n : ℕ} (hn : 1 ≤ n) {C : ℝ}
    (hIH : HasStrongMaximalOrliczBound n C)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) {b : ℝ} (hb : 0 < b) :
    volume {p : ℝ × (Fin n → ℝ) | ENNReal.ofReal b < partialStrongMax f p.1 p.2} ≤
      ENNReal.ofReal C *
        ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth n (|f x| / b)) := by
  have hn0 : 0 < n := by omega
  set S := {p : ℝ × (Fin n → ℝ) | ENNReal.ofReal b < partialStrongMax f p.1 p.2}
  have hS : MeasurableSet S := measurableSet_partialStrongMax_gt hn0 hf _
  rw [Measure.volume_eq_prod, Measure.prod_apply hS]
  have hgrow : Measurable fun p : ℝ × (Fin n → ℝ) ↦
      ENNReal.ofReal (strongMaximalGrowth n (|f ((lastCoordEquiv n).symm p)| / b)) := by
    refine ENNReal.measurable_ofReal.comp ((measurable_strongMaximalGrowth n).comp ?_)
    exact (continuous_abs.measurable.comp
      (hf.comp (lastCoordEquiv n).symm.measurable)).div_const b
  have hpoint : ∀ y, volume (Prod.mk y ⁻¹' S) ≤
      ENNReal.ofReal C *
        ∫⁻ z, ENNReal.ofReal (strongMaximalGrowth n (|lastCoordSlice f y z| / b)) := by
    intro y
    have hset : Prod.mk y ⁻¹' S =
        {z | ENNReal.ofReal b < strongMaximalFunction (lastCoordSlice f y) z} := by
      ext z
      simp only [mem_preimage, S, mem_ofPred_eq, partialStrongMax]
    rw [hset]
    exact hIH (lastCoordSlice f y) (measurable_lastCoordSlice hf y) b hb
  calc
    ∫⁻ y, volume (Prod.mk y ⁻¹' S) ≤
        ∫⁻ y, ENNReal.ofReal C *
          ∫⁻ z, ENNReal.ofReal (strongMaximalGrowth n (|lastCoordSlice f y z| / b)) :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal C * ∫⁻ y, ∫⁻ z,
          ENNReal.ofReal (strongMaximalGrowth n (|lastCoordSlice f y z| / b)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal C *
          ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth n (|f x| / b)) := by
      congr 1
      have hev : MeasurePreserving (⇑(lastCoordEquiv n).symm) volume volume :=
        (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)).symm
      rw [← hev.lintegral_comp_emb (lastCoordEquiv n).symm.measurableEmbedding
        (fun x ↦ ENNReal.ofReal (strongMaximalGrowth n (|f x| / b)))]
      exact (lintegral_prod _ hgrow.aemeasurable).symm

namespace StrongMaximal

/-- The truncation that discards values at most half the height. -/
@[expose]
def halfLevelTrunc {α : Type*} (t : ℝ) (f : α → ℝ) (x : α) : ℝ :=
  if t / 2 < |f x| then f x else 0

/-- Unfolding of `CKMA.StrongMaximal.halfLevelTrunc`. -/
theorem halfLevelTrunc_def {α : Type*} (t : ℝ) (f : α → ℝ) (x : α) :
    halfLevelTrunc t f x = if t / 2 < |f x| then f x else 0 :=
  rfl

/-- Truncation preserves measurability. -/
private theorem measurable_halfLevelTrunc {α : Type*} [MeasurableSpace α] {t : ℝ} {f : α → ℝ}
    (hf : Measurable f) : Measurable (halfLevelTrunc t f) := by
  have hs : MeasurableSet {x | t / 2 < |f x|} := by
    simpa [Real.norm_eq_abs] using measurableSet_lt measurable_const hf.norm
  unfold halfLevelTrunc
  exact hf.ite hs measurable_const

end StrongMaximal

/-- The distribution of a high superlevel is controlled by the truncated slices. -/
theorem volume_partialStrongMax_gt_le_trunc {n : ℕ} (hn : 1 ≤ n) {C : ℝ}
    (hIH : HasStrongMaximalOrliczBound n C)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) {t : ℝ} (ht : 0 < t) :
    volume {p : ℝ × (Fin n → ℝ) | ENNReal.ofReal t < partialStrongMax f p.1 p.2} ≤
      ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth n
        (|(halfLevelTrunc t f) x| / (t / 2))) := by
  have hsub : {p : ℝ × (Fin n → ℝ) | ENNReal.ofReal t < partialStrongMax f p.1 p.2} ⊆
      {p : ℝ × (Fin n → ℝ) | ENNReal.ofReal (t / 2) <
        partialStrongMax (halfLevelTrunc t f) p.1 p.2} := by
    intro p hp
    simp only [mem_ofPred_eq] at hp ⊢
    have htrunc := strongMaximal_lt_trunc ht (measurable_lastCoordSlice hf p.1) hp
    have hfun : lastCoordSlice (halfLevelTrunc t f) p.1 =
        fun y ↦ if t / 2 < |lastCoordSlice f p.1 y| then lastCoordSlice f p.1 y else 0 := by
      funext y
      rfl
    rw [partialStrongMax, hfun]
    exact htrunc
  refine le_trans (measure_mono hsub) ?_
  exact volume_partialStrongMax_gt_le hn hIH (measurable_halfLevelTrunc hf)
    (div_pos ht (by norm_num))

/-- Discarding the half-height part of an integrand preserves a strict one-dimensional
maximal inequality. -/
private theorem intervalMaximalFunction_trunc_gt {φ : ℝ → ℝ≥0∞} {a : ℝ}
    (ha : 0 < a) {x : ℝ} (hx : ENNReal.ofReal a < intervalMaximalFunction φ x) :
    ENNReal.ofReal (a / 2) <
      intervalMaximalFunction (fun y ↦ if ENNReal.ofReal (a / 2) < φ y then φ y else 0) x := by
  obtain ⟨I, hxI, havg⟩ := lt_intervalMaximalFunction_iff.1 hx
  set ψ : ℝ → ℝ≥0∞ := fun y ↦ if ENNReal.ofReal (a / 2) < φ y then φ y else 0
  set b := ENNReal.ofReal (a / 2)
  have hb : ENNReal.ofReal a = b + b := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]
  have hvolI : volume I.carrier = ENNReal.ofReal I.length := by
    simp [OpenInterval.carrier, OpenInterval.length, Real.volume_Ioo]
  have hne : ENNReal.ofReal I.length ≠ 0 := (ENNReal.ofReal_pos.2 I.length_pos).ne'
  have hL : ENNReal.ofReal a * ENNReal.ofReal I.length < ∫⁻ y in I.carrier, φ y :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl hne) (Or.inl ENNReal.ofReal_ne_top)).1 havg
  have hφψ : ∫⁻ y in I.carrier, φ y ≤ (∫⁻ y in I.carrier, ψ y) + b * ENNReal.ofReal I.length := by
    rw [← hvolI, ← setLIntegral_const, ← lintegral_add_right _ measurable_const]
    refine lintegral_mono fun y ↦ ?_
    simp only [ψ]
    split_ifs with h
    · exact le_self_add
    · exact (not_lt.1 h).trans (by rw [zero_add])
  have hlt : b * ENNReal.ofReal I.length < ∫⁻ y in I.carrier, ψ y := by
    rw [hb, add_mul] at hL
    exact (ENNReal.add_lt_add_iff_right (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top)).1 (hL.trans_le hφψ)
  exact lt_intervalMaximalFunction_iff.2 ⟨I, hxI,
    (ENNReal.lt_div_iff_mul_lt (Or.inl hne) (Or.inl ENNReal.ofReal_ne_top)).2 hlt⟩

namespace StrongMaximal

/-- The partial maximal function, set to zero on and below the half-height threshold. -/
@[expose]
def truncatedPartial {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (a : ℝ) (y : ℝ)
    (z : Fin n → ℝ) : ℝ≥0∞ :=
  if ENNReal.ofReal (a / 2) < partialStrongMax f y z then partialStrongMax f y z else 0

/-- Unfolding of `CKMA.StrongMaximal.truncatedPartial`. -/
theorem truncatedPartial_def {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (a y : ℝ) (z : Fin n → ℝ) :
    truncatedPartial f a y z =
      if ENNReal.ofReal (a / 2) < partialStrongMax f y z then partialStrongMax f y z else 0 :=
  rfl

/-- The truncated partial maximal function is measurable. -/
private theorem measurable_truncatedPartial {n : ℕ} (hn : 0 < n)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) (a : ℝ) :
    Measurable (fun p : ℝ × (Fin n → ℝ) ↦ truncatedPartial f a p.1 p.2) := by
  have hT : Measurable fun p : ℝ × (Fin n → ℝ) ↦ partialStrongMax f p.1 p.2 :=
    measurable_partialStrongMax hn hf
  have hs : MeasurableSet {p : ℝ × (Fin n → ℝ) |
      ENNReal.ofReal (a / 2) < partialStrongMax f p.1 p.2} :=
    measurableSet_lt measurable_const hT
  unfold truncatedPartial
  exact hT.ite hs measurable_const

end StrongMaximal

/-- Rational one-dimensional averages of the truncated partial maximal function are measurable
in the slice coordinate. -/
private theorem measurable_truncRatAverage {n : ℕ} (hn : 0 < n)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) (a : ℝ) (J : RatInterval) :
    Measurable fun z : Fin n → ℝ ↦
      ratIntervalAverage (fun y ↦ truncatedPartial f a y z) J := by
  set phi : ℝ × (Fin n → ℝ) → ℝ≥0∞ := fun p ↦ truncatedPartial f a p.1 p.2
  have hphi : Measurable phi := measurable_truncatedPartial hn hf a
  have hs : MeasurableSet J.carrier := measurableSet_Ioo
  simp_rw [ratIntervalAverage, intervalAverage, div_eq_mul_inv, RatInterval.length_toOpen,
    RatInterval.carrier_toOpen]
  have hfun : (fun z ↦
      (∫⁻ y in J.carrier, truncatedPartial f a y z) * (ENNReal.ofReal J.length)⁻¹) =
      fun z ↦ (∫⁻ y, (Prod.fst ⁻¹' J.carrier).indicator phi (y, z)) *
        (ENNReal.ofReal J.length)⁻¹ := by
    funext z
    refine congrArg (fun t ↦ t * (ENNReal.ofReal J.length)⁻¹) ?_
    rw [← lintegral_indicator hs]
    refine lintegral_congr fun y ↦ ?_
    by_cases hy : y ∈ J.carrier
    · simp [phi, hy, Set.indicator]
    · simp [phi, hy, Set.indicator]
  rw [hfun]
  exact (hphi.indicator (hs.preimage measurable_fst)).lintegral_prod_left'.mul_const _

/-- The strong maximal superlevel sits inside the one-dimensional superlevel of the truncated
partial maximal function, up to the coordinate equivalence. -/
private theorem strongMaximal_subset_truncRat {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : Measurable f) {a : ℝ} (ha : 0 < a) :
    {x | ENNReal.ofReal a < strongMaximalFunction f x} ⊆
      lastCoordEquiv n ⁻¹'
        (⋃ J : RatInterval, J.carrier ×ˢ
          {z | ENNReal.ofReal (a / 2) <
            ratIntervalAverage (fun y ↦ truncatedPartial f a y z) J}) := by
  intro x hx
  let y : ℝ := x (Fin.last n)
  let z : Fin n → ℝ := Fin.init x
  have hyM : ENNReal.ofReal a <
      intervalMaximalFunction (fun t ↦ partialStrongMax f t z) y :=
    lt_of_lt_of_le hx (strongMaximal_le_partial hf x)
  have htrunc := intervalMaximalFunction_trunc_gt ha hyM
  rw [intervalMaximalFunction, lt_iSup_iff] at htrunc
  obtain ⟨I, hI⟩ := htrunc
  rw [lt_iSup_iff] at hI
  obtain ⟨hyI, havg⟩ := hI
  have hψ : (fun t ↦ if ENNReal.ofReal (a / 2) < partialStrongMax f t z then
      partialStrongMax f t z else 0) = fun t ↦ truncatedPartial f a t z := by
    funext t
    rfl
  rw [hψ] at havg
  obtain ⟨J, hsub, hJ⟩ := exists_ratInterval_of_average_gt
    (fun t ↦ truncatedPartial f a t z) I (div_pos ha (by norm_num)) havg
  have hyJ : y ∈ J.carrier := hsub hyI
  have hcoord : lastCoordEquiv n x = (y, z) := by
    simpa [y, z] using lastCoordEquiv_apply n x
  rw [mem_preimage, hcoord]
  refine mem_iUnion.2 ⟨J, ?_⟩
  exact mem_prod.2 ⟨hyJ, hJ⟩

/-- The distribution of the strong maximal function is at most a constant multiple of the
integral of the truncated partial maximal function. -/
theorem strongMaximal_volume_le_truncIntegral {n : ℕ} (hn : 1 ≤ n)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) {a : ℝ} (ha : 0 < a) :
    volume {x | ENNReal.ofReal a < strongMaximalFunction f x} ≤
      ENNReal.ofReal (10 / a) * ∫⁻ p : ℝ × (Fin n → ℝ), truncatedPartial f a p.1 p.2 := by
  have hn0 : 0 < n := by omega
  let S : Set (ℝ × (Fin n → ℝ)) :=
    ⋃ J : RatInterval, J.carrier ×ˢ
      {z | ENNReal.ofReal (a / 2) <
        ratIntervalAverage (fun y ↦ truncatedPartial f a y z) J}
  have hS : MeasurableSet S := by
    refine MeasurableSet.iUnion fun J ↦ MeasurableSet.prod measurableSet_Ioo ?_
    exact measurableSet_lt measurable_const (measurable_truncRatAverage hn0 hf a J)
  have hsub := strongMaximal_subset_truncRat hf ha
  have hev : MeasurePreserving (lastCoordEquiv n) volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)
  have hpre : volume {x | ENNReal.ofReal a < strongMaximalFunction f x} ≤ volume S := by
    rw [← hev.measure_preimage_equiv S]
    exact measure_mono hsub
  have hconst : ENNReal.ofReal 5 / ENNReal.ofReal (a / 2) = ENNReal.ofReal (10 / a) := by
    have hdiv : (5 : ℝ) / (a / 2) = 10 / a := by
      field_simp [ha.ne']
      ring
    rw [← ENNReal.ofReal_div_of_pos (div_pos ha (by norm_num : (0 : ℝ) < 2)), hdiv]
  have hhalf : 0 < a / 2 := div_pos ha (by norm_num)
  have hslice : ∀ z, volume {y | (y, z) ∈ S} ≤
      (ENNReal.ofReal 5 *
        ∫⁻ y, truncatedPartial f a y z) / ENNReal.ofReal (a / 2) := by
    intro z
    refine le_trans (measure_mono ?_) (intervalMaximalFunction_weakType
      (fun y ↦ truncatedPartial f a y z) hhalf)
    intro y hy
    obtain ⟨J, hJ⟩ := mem_iUnion.1 hy
    obtain ⟨hyJ, havg⟩ := mem_prod.1 hJ
    have hmem : y ∈ J.toOpen.carrier := by
      simpa [RatInterval.carrier_toOpen] using hyJ
    have havg' : intervalAverage (fun t ↦ truncatedPartial f a t z) J.toOpen =
        ratIntervalAverage (fun t ↦ truncatedPartial f a t z) J := by
      simp [ratIntervalAverage]
    have hlt : ENNReal.ofReal (a / 2) <
        intervalAverage (fun t ↦ truncatedPartial f a t z) J.toOpen := by
      simpa [havg'] using havg
    unfold intervalMaximalFunction
    exact lt_of_lt_of_le hlt
      ((le_iSup (fun _ : y ∈ J.toOpen.carrier ↦
        intervalAverage (fun t ↦ truncatedPartial f a t z) J.toOpen) hmem).trans
        (le_iSup (fun I : OpenInterval ↦ ⨆ _ : y ∈ I.carrier,
          intervalAverage (fun t ↦ truncatedPartial f a t z) I) J.toOpen))
  have hvolS : volume S ≤ ENNReal.ofReal (10 / a) *
      ∫⁻ p : ℝ × (Fin n → ℝ), truncatedPartial f a p.1 p.2 := by
    rw [Measure.volume_eq_prod, Measure.prod_apply_symm hS]
    refine le_trans (lintegral_mono hslice) ?_
    have hrew : ∀ t : ℝ≥0∞,
        (ENNReal.ofReal 5 * t) / ENNReal.ofReal (a / 2) =
          ENNReal.ofReal (10 / a) * t := by
      intro t
      calc
        (ENNReal.ofReal 5 * t) / ENNReal.ofReal (a / 2) =
            ENNReal.ofReal 5 * t * (ENNReal.ofReal (a / 2))⁻¹ := by
          rw [div_eq_mul_inv]
        _ = ENNReal.ofReal 5 * (ENNReal.ofReal (a / 2))⁻¹ * t := by
          rw [mul_assoc, mul_comm t, ← mul_assoc]
        _ = (ENNReal.ofReal 5 / ENNReal.ofReal (a / 2)) * t := by
          rw [div_eq_mul_inv (a := ENNReal.ofReal 5)
            (b := ENNReal.ofReal (a / 2))]
        _ = ENNReal.ofReal (10 / a) * t := by rw [hconst]
    simp_rw [hrew]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hpsi : Measurable fun p : ℝ × (Fin n → ℝ) ↦ truncatedPartial f a p.1 p.2 :=
      measurable_truncatedPartial hn0 hf a
    rw [lintegral_prod_symm _ hpsi.aemeasurable]
  exact hpre.trans hvolS

end CKMA
