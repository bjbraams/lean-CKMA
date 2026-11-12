/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.RectangularDifferentiation.Iteration
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Endpoint bound for the strong maximal operator

The strong maximal function in dimension `n + 1` is controlled by the uncentered
one-dimensional maximal function, taken in the last coordinate, of the strong maximal
function of the slices. Fubini, the one-dimensional weak-type bound, and one application
of the logarithmic iteration kernel raise the Orlicz exponent by one.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Set
open scoped ENNReal

/-- A strict partial-maximal inequality is a countable union of rational slice averages. -/
theorem partialStrongMax_gt_eq {n : ℕ} (hn : 0 < n) (f : (Fin (n + 1) → ℝ) → ℝ)
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
theorem measurableSet_partialStrongMax_gt {n : ℕ} (hn : 0 < n)
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
theorem partial_distribution {n : ℕ} (hn : 1 ≤ n) {C : ℝ}
    (hIH : ∀ (g : (Fin n → ℝ) → ℝ), Measurable g → ∀ b : ℝ, 0 < b →
      volume {z | ENNReal.ofReal b < strongMaximalFunction g z} ≤
        ENNReal.ofReal C *
          ∫⁻ z, ENNReal.ofReal (strongMaximalGrowth n (|g z| / b)))
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) {b : ℝ} (hb : 0 < b) :
    volume {p : ℝ × (Fin n → ℝ) | ENNReal.ofReal b < partialStrongMax f p.1 p.2} ≤
      ENNReal.ofReal C *
        ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth n (|f x| / b)) := by
  have hn0 : 0 < n := by omega
  set S := {p : ℝ × (Fin n → ℝ) | ENNReal.ofReal b < partialStrongMax f p.1 p.2}
  have hS : MeasurableSet S := measurableSet_partialStrongMax_gt hn0 hf _
  rw [Measure.volume_eq_prod, Measure.prod_apply hS]
  have hgrow : Measurable fun p : ℝ × (Fin n → ℝ) ↦
      ENNReal.ofReal (strongMaximalGrowth n (|f ((coordEquiv n).symm p)| / b)) := by
    refine ENNReal.measurable_ofReal.comp ((measurable_strongMaximalGrowth n).comp ?_)
    exact (continuous_abs.measurable.comp
      (hf.comp (coordEquiv n).symm.measurable)).div_const b
  have hpoint : ∀ y, volume (Prod.mk y ⁻¹' S) ≤
      ENNReal.ofReal C *
        ∫⁻ z, ENNReal.ofReal (strongMaximalGrowth n (|sliceFunction f y z| / b)) := by
    intro y
    have hset : Prod.mk y ⁻¹' S =
        {z | ENNReal.ofReal b < strongMaximalFunction (sliceFunction f y) z} := by
      ext z
      simp only [mem_preimage, S, mem_ofPred_eq, partialStrongMax]
    rw [hset]
    exact hIH (sliceFunction f y) (sliceFunction_measurable hf y) b hb
  calc
    ∫⁻ y, volume (Prod.mk y ⁻¹' S) ≤
        ∫⁻ y, ENNReal.ofReal C *
          ∫⁻ z, ENNReal.ofReal (strongMaximalGrowth n (|sliceFunction f y z| / b)) :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal C * ∫⁻ y, ∫⁻ z,
          ENNReal.ofReal (strongMaximalGrowth n (|sliceFunction f y z| / b)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal C *
          ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth n (|f x| / b)) := by
      congr 1
      have hev : MeasurePreserving (⇑(coordEquiv n).symm) volume volume :=
        (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)).symm
      rw [← hev.lintegral_comp_emb (coordEquiv n).symm.measurableEmbedding
        (fun x ↦ ENNReal.ofReal (strongMaximalGrowth n (|f x| / b)))]
      exact (lintegral_prod _ hgrow.aemeasurable).symm

/-- The truncation that discards values at most half the height. -/
def truncAt {α : Type*} (t : ℝ) (f : α → ℝ) (x : α) : ℝ :=
  if t / 2 < |f x| then f x else 0

/-- Truncation preserves measurability. -/
theorem measurable_truncAt {α : Type*} [MeasurableSpace α] {t : ℝ} {f : α → ℝ}
    (hf : Measurable f) : Measurable (truncAt t f) := by
  have hs : MeasurableSet {x | t / 2 < |f x|} := by
    simpa [Real.norm_eq_abs] using measurableSet_lt measurable_const hf.norm
  unfold truncAt
  exact hf.ite hs measurable_const

/-- The distribution of a high superlevel is controlled by the truncated slices. -/
theorem partial_distribution_trunc {n : ℕ} (hn : 1 ≤ n) {C : ℝ}
    (hIH : ∀ (g : (Fin n → ℝ) → ℝ), Measurable g → ∀ b : ℝ, 0 < b →
      volume {z | ENNReal.ofReal b < strongMaximalFunction g z} ≤
        ENNReal.ofReal C *
          ∫⁻ z, ENNReal.ofReal (strongMaximalGrowth n (|g z| / b)))
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) {t : ℝ} (ht : 0 < t) :
    volume {p : ℝ × (Fin n → ℝ) | ENNReal.ofReal t < partialStrongMax f p.1 p.2} ≤
      ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth n
        (|(truncAt t f) x| / (t / 2))) := by
  have hsub : {p : ℝ × (Fin n → ℝ) | ENNReal.ofReal t < partialStrongMax f p.1 p.2} ⊆
      {p : ℝ × (Fin n → ℝ) | ENNReal.ofReal (t / 2) <
        partialStrongMax (truncAt t f) p.1 p.2} := by
    intro p hp
    simp only [mem_ofPred_eq] at hp ⊢
    have htrunc := strongMaximal_lt_trunc ht (sliceFunction_measurable hf p.1) hp
    have hfun : sliceFunction (truncAt t f) p.1 =
        fun y ↦ if t / 2 < |sliceFunction f p.1 y| then sliceFunction f p.1 y else 0 := by
      funext y
      rfl
    rw [partialStrongMax, hfun]
    exact htrunc
  refine le_trans (measure_mono hsub) ?_
  exact partial_distribution hn hIH (measurable_truncAt hf) (div_pos ht (by norm_num))

/-- Discarding the half-height part of an integrand preserves a strict one-dimensional
maximal inequality. -/
theorem oneDimMaximalENN_trunc_gt {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) {a : ℝ} (ha : 0 < a)
    {x : ℝ} (hx : ENNReal.ofReal a < oneDimMaximalENN φ x) :
    ENNReal.ofReal (a / 2) <
      oneDimMaximalENN (fun y ↦ if ENNReal.ofReal (a / 2) < φ y then φ y else 0) x := by
  rw [oneDimMaximalENN, lt_iSup_iff] at hx
  obtain ⟨I, hI⟩ := hx
  rw [lt_iSup_iff] at hI
  obtain ⟨hxI, havg⟩ := hI
  set ψ : ℝ → ℝ≥0∞ := fun y ↦ if ENNReal.ofReal (a / 2) < φ y then φ y else 0
  set G : Set ℝ := {y | ENNReal.ofReal (a / 2) < φ y}
  have hG : MeasurableSet G := measurableSet_lt measurable_const hφ
  have hImeas : MeasurableSet I.carrier := by simp [OpenInterval.carrier]
  have hLpos : 0 < I.length := I.length_pos
  have hhalf_nn : 0 ≤ a / 2 := div_nonneg ha.le (by norm_num)
  have hL : ENNReal.ofReal a * ENNReal.ofReal I.length < ∫⁻ y in I.carrier, φ y := by
    refine (ENNReal.lt_div_iff_mul_lt ?_ ?_).1 ?_
    · exact Or.inl (ne_of_gt (ENNReal.ofReal_pos.2 hLpos))
    · exact Or.inl ENNReal.ofReal_ne_top
    simpa [intervalAverage] using havg
  have hsplit : ∫⁻ y in I.carrier, φ y =
      (∫⁻ y in I.carrier ∩ G, φ y) + (∫⁻ y in I.carrier \ G, φ y) :=
    (lintegral_inter_add_sdiff (μ := volume) φ I.carrier hG).symm
  have hvolI : volume I.carrier = ENNReal.ofReal I.length := by
    simp [OpenInterval.carrier, OpenInterval.length, Real.volume_Ioo]
  have hG2 : ∫⁻ y in I.carrier \ G, φ y ≤
      ENNReal.ofReal (a / 2) * ENNReal.ofReal I.length := by
    have hle : ∫⁻ y in I.carrier \ G, φ y ≤
        ∫⁻ y in I.carrier \ G, ENNReal.ofReal (a / 2) :=
      setLIntegral_mono' (μ := (volume : Measure ℝ)) (hImeas.diff hG) fun _ hy ↦
        le_of_not_gt hy.2
    calc
      ∫⁻ y in I.carrier \ G, φ y ≤
          ∫⁻ y in I.carrier \ G, ENNReal.ofReal (a / 2) := hle
      _ = ENNReal.ofReal (a / 2) * volume (I.carrier \ G) :=
        setLIntegral_const (I.carrier \ G) _
      _ ≤ ENNReal.ofReal (a / 2) * volume I.carrier :=
        mul_le_mul' le_rfl (measure_mono (sdiff_subset (s := I.carrier) (t := G)))
      _ = ENNReal.ofReal (a / 2) * ENNReal.ofReal I.length := by rw [hvolI]
  have hψ : ∫⁻ y in I.carrier, ψ y = ∫⁻ y in I.carrier ∩ G, φ y := by
    have hsplitψ : ∫⁻ y in I.carrier, ψ y =
        (∫⁻ y in I.carrier ∩ G, ψ y) + (∫⁻ y in I.carrier \ G, ψ y) :=
      (lintegral_inter_add_sdiff (μ := volume) ψ I.carrier hG).symm
    have hagree : ∫⁻ y in I.carrier ∩ G, ψ y = ∫⁻ y in I.carrier ∩ G, φ y :=
      setLIntegral_congr_fun (μ := volume) (hImeas.inter hG) fun y hy ↦ by
        have hyG : ENNReal.ofReal (a / 2) < φ y := by
          simpa [G, mem_ofPred_eq] using (mem_inter_iff y I.carrier G).mp hy |>.2
        simp only [ψ]
        split_ifs
        rfl
    have hzero : ∫⁻ y in I.carrier \ G, ψ y = 0 :=
      setLIntegral_eq_zero (μ := volume) (hImeas.diff hG) fun y hy ↦ by
        have hyG : ¬ ENNReal.ofReal (a / 2) < φ y := by
          simpa [G, mem_ofPred_eq] using hy.2
        simp only [ψ]
        split_ifs
        rfl
    rw [hsplitψ, hagree, hzero, add_zero]
  have hlt : ENNReal.ofReal (a / 2) * ENNReal.ofReal I.length <
      ∫⁻ y in I.carrier, ψ y := by
    by_contra hle
    have hle' : ∫⁻ y in I.carrier, ψ y ≤
        ENNReal.ofReal (a / 2) * ENNReal.ofReal I.length := not_lt.mp hle
    have hsum : ∫⁻ y in I.carrier, φ y ≤
        ENNReal.ofReal a * ENNReal.ofReal I.length := by
      calc
        ∫⁻ y in I.carrier, φ y =
            (∫⁻ y in I.carrier, ψ y) + (∫⁻ y in I.carrier \ G, φ y) := by rw [hsplit, hψ]
        _ ≤ ENNReal.ofReal (a / 2) * ENNReal.ofReal I.length +
            ENNReal.ofReal (a / 2) * ENNReal.ofReal I.length := add_le_add hle' hG2
        _ = (ENNReal.ofReal (a / 2) + ENNReal.ofReal (a / 2)) * ENNReal.ofReal I.length := by
          rw [add_mul]
        _ = ENNReal.ofReal a * ENNReal.ofReal I.length := by
          have hsum_real : a / 2 + a / 2 = a := by ring
          rw [← ENNReal.ofReal_add hhalf_nn hhalf_nn, hsum_real]
    exact not_le_of_gt hL hsum
  have havgψ : ENNReal.ofReal (a / 2) < intervalAverage ψ I := by
    refine (ENNReal.lt_div_iff_mul_lt ?_ ?_).2 hlt
    · exact Or.inl (ne_of_gt (ENNReal.ofReal_pos.2 hLpos))
    · exact Or.inl ENNReal.ofReal_ne_top
  unfold oneDimMaximalENN
  exact lt_of_lt_of_le havgψ
    ((le_iSup (fun _ : x ∈ I.carrier ↦ intervalAverage ψ I) hxI).trans
      (le_iSup (fun J : OpenInterval ↦
        ⨆ _ : x ∈ J.carrier, intervalAverage ψ J) I))

/-- A strict interval average is witnessed by a rational interval, whether or not the integrand
is globally integrable. -/
theorem exists_ratInterval_of_average_gt_local (g : ℝ → ℝ≥0∞) (I : OpenInterval) {α : ℝ}
    (hα : 0 < α) (havg : ENNReal.ofReal α < intervalAverage g I) :
    ∃ J : RatInterval, I.carrier ⊆ J.carrier ∧
      ENNReal.ofReal α < ratIntervalAverage g J := by
  by_cases hfin : ∫⁻ t in I.carrier, g t = ∞
  · obtain ⟨p, _, hp2⟩ := exists_rat_btwn (show I.left - 1 < I.left by linarith)
    obtain ⟨q, hq1, _⟩ := exists_rat_btwn (show I.right < I.right + 1 by linarith)
    have hpq : (p : ℝ) < (q : ℝ) := by linarith [I.left_lt_right]
    let J : RatInterval := ⟨p, q, by exact_mod_cast hpq⟩
    have hsub : I.carrier ⊆ J.carrier := by
      intro t ht
      exact ⟨lt_trans hp2 ht.1, lt_trans ht.2 hq1⟩
    have hint : ∫⁻ t in J.carrier, g t = ∞ :=
      top_unique <| (hfin ▸ lintegral_mono_set hsub : ∞ ≤ _)
    have havgJ : ratIntervalAverage g J = ∞ := by
      rw [ratIntervalAverage, intervalAverage, ENNReal.div_eq_top]
      exact Or.inr ⟨hint, ENNReal.ofReal_ne_top⟩
    exact ⟨J, hsub, by simp [havgJ, ENNReal.ofReal_lt_top]⟩
  · let gI : ℝ → ℝ≥0∞ := I.carrier.indicator g
    have hImeas : MeasurableSet I.carrier := by simp [OpenInterval.carrier]
    have hfinI : ∫⁻ t, gI t ≠ ∞ := by
      rw [lintegral_indicator hImeas]
      exact hfin
    have havgI : intervalAverage gI I = intervalAverage g I := by
      simp only [intervalAverage]
      refine congrArg (fun s ↦ s / ENNReal.ofReal I.length) ?_
      refine setLIntegral_congr_fun hImeas fun t ht ↦ ?_
      simp [gI, ht]
    obtain ⟨J, hsub, hJ⟩ :=
      exists_ratInterval_of_average_gt gI hfinI I hα (by simpa [havgI] using havg)
    have hnum : ∫⁻ t in J.carrier, gI t ≤ ∫⁻ t in J.carrier, g t := by
      have hs : MeasurableSet J.carrier := measurableSet_Ioo
      rw [← lintegral_indicator hs, ← lintegral_indicator hs]
      refine lintegral_mono fun t ↦ ?_
      by_cases htJ : t ∈ J.carrier
      · by_cases htI : t ∈ I.carrier
        · simp [gI, htJ, htI, Set.indicator]
        · simp [gI, htJ, htI, Set.indicator]
      · simp [gI, htJ, Set.indicator]
    have hle : ratIntervalAverage gI J ≤ ratIntervalAverage g J := by
      simp only [ratIntervalAverage, intervalAverage]
      exact ENNReal.div_le_div_right hnum _
    exact ⟨J, hsub, lt_of_lt_of_le hJ hle⟩

/-- The partial maximal function, set to zero on and below the half-height threshold. -/
def truncatedPartial {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (a : ℝ) (y : ℝ)
    (z : Fin n → ℝ) : ℝ≥0∞ :=
  if ENNReal.ofReal (a / 2) < partialStrongMax f y z then partialStrongMax f y z else 0

/-- The truncated partial maximal function is measurable. -/
theorem measurable_truncatedPartial {n : ℕ} (hn : 0 < n)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) (a : ℝ) :
    Measurable (fun p : ℝ × (Fin n → ℝ) ↦ truncatedPartial f a p.1 p.2) := by
  have hT : Measurable fun p : ℝ × (Fin n → ℝ) ↦ partialStrongMax f p.1 p.2 :=
    measurable_partialStrongMax hn hf
  have hs : MeasurableSet {p : ℝ × (Fin n → ℝ) |
      ENNReal.ofReal (a / 2) < partialStrongMax f p.1 p.2} :=
    measurableSet_lt measurable_const hT
  unfold truncatedPartial
  exact hT.ite hs measurable_const

/-- Rational one-dimensional averages of the truncated partial maximal function are measurable
in the slice coordinate. -/
theorem measurable_truncRatAverage {n : ℕ} (hn : 0 < n)
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
theorem strongMaximal_subset_truncRat {n : ℕ} (hn : 1 ≤ n)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) {a : ℝ} (ha : 0 < a) :
    {x | ENNReal.ofReal a < strongMaximalFunction f x} ⊆
      coordEquiv n ⁻¹'
        (⋃ J : RatInterval, J.carrier ×ˢ
          {z | ENNReal.ofReal (a / 2) <
            ratIntervalAverage (fun y ↦ truncatedPartial f a y z) J}) := by
  have hn0 : 0 < n := by omega
  intro x hx
  let y : ℝ := x (Fin.last n)
  let z : Fin n → ℝ := Fin.init x
  have hslice : Measurable fun t ↦ partialStrongMax f t z :=
    (measurable_partialStrongMax hn0 hf).comp (measurable_id.prodMk measurable_const)
  have hyM : ENNReal.ofReal a <
      oneDimMaximalENN (fun t ↦ partialStrongMax f t z) y :=
    lt_of_lt_of_le hx (strongMaximal_le_partial hf x)
  have htrunc := oneDimMaximalENN_trunc_gt hslice ha hyM
  rw [oneDimMaximalENN, lt_iSup_iff] at htrunc
  obtain ⟨I, hI⟩ := htrunc
  rw [lt_iSup_iff] at hI
  obtain ⟨hyI, havg⟩ := hI
  have hψ : (fun t ↦ if ENNReal.ofReal (a / 2) < partialStrongMax f t z then
      partialStrongMax f t z else 0) = fun t ↦ truncatedPartial f a t z := by
    funext t
    rfl
  rw [hψ] at havg
  obtain ⟨J, hsub, hJ⟩ := exists_ratInterval_of_average_gt_local
    (fun t ↦ truncatedPartial f a t z) I (div_pos ha (by norm_num)) havg
  have hyJ : y ∈ J.carrier := hsub hyI
  have hcoord : coordEquiv n x = (y, z) := by
    simpa [y, z] using coordEquiv_apply n x
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
  have hsub := strongMaximal_subset_truncRat hn hf ha
  have hev : MeasurePreserving (coordEquiv n) volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)
  have hpre : volume {x | ENNReal.ofReal a < strongMaximalFunction f x} ≤ volume S := by
    rw [← hev.measure_preimage_equiv S]
    exact measure_mono hsub
  have hconst : ENNReal.ofReal oneDimWeakConstant / ENNReal.ofReal (a / 2) =
      ENNReal.ofReal (10 / a) := by
    have h5 : oneDimWeakConstant = 5 := by simp [oneDimWeakConstant]
    have hdiv : (5 : ℝ) / (a / 2) = 10 / a := by
      field_simp [ha.ne']
      ring
    rw [h5, ← ENNReal.ofReal_div_of_pos (div_pos ha (by norm_num : (0 : ℝ) < 2)), hdiv]
  have hhalf : 0 < a / 2 := div_pos ha (by norm_num)
  have hslice : ∀ z, volume {y | (y, z) ∈ S} ≤
      (ENNReal.ofReal oneDimWeakConstant *
        ∫⁻ y, truncatedPartial f a y z) / ENNReal.ofReal (a / 2) := by
    intro z
    refine le_trans (measure_mono ?_) (oneDimMaximalENN_weakType
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
    unfold oneDimMaximalENN
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
        (ENNReal.ofReal oneDimWeakConstant * t) / ENNReal.ofReal (a / 2) =
          ENNReal.ofReal (10 / a) * t := by
      intro t
      calc
        (ENNReal.ofReal oneDimWeakConstant * t) / ENNReal.ofReal (a / 2) =
            ENNReal.ofReal oneDimWeakConstant * t * (ENNReal.ofReal (a / 2))⁻¹ := by
          rw [div_eq_mul_inv]
        _ = ENNReal.ofReal oneDimWeakConstant * (ENNReal.ofReal (a / 2))⁻¹ * t := by
          rw [mul_assoc, mul_comm t, ← mul_assoc]
        _ = (ENNReal.ofReal oneDimWeakConstant / ENNReal.ofReal (a / 2)) * t := by
          rw [div_eq_mul_inv (a := ENNReal.ofReal oneDimWeakConstant)
            (b := ENNReal.ofReal (a / 2))]
        _ = ENNReal.ofReal (10 / a) * t := by rw [hconst]
    simp_rw [hrew]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hpsi : Measurable fun p : ℝ × (Fin n → ℝ) ↦ truncatedPartial f a p.1 p.2 :=
      measurable_truncatedPartial hn0 hf a
    rw [lintegral_prod_symm _ hpsi.aemeasurable]
  exact hpre.trans hvolS

end CKMA
