/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.RectangularDifferentiation.Base
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Iteration of the strong maximal operator

The strong maximal function in dimension `n + 1` is at most the uncentered one-dimensional
maximal function, in the last coordinate, of the strong maximal function of the slices. The
resulting distribution function is estimated by Fubini, the one-dimensional weak-type bound,
and one application of the logarithmic iteration kernel.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Set
open scoped BigOperators ENNReal intervalIntegral

/-- Measurable splitting of a tuple into its last coordinate and its initial segment. -/
def coordEquiv (n : ℕ) : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)

/-- The equivalence reads the last coordinate and the initial segment. -/
theorem coordEquiv_apply (n : ℕ) (x : Fin (n + 1) → ℝ) :
    coordEquiv n x = (x (Fin.last n), Fin.init x) := by
  simp [coordEquiv, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv_last,
    Fin.snocEquiv_symm_apply]

/-- The inverse equivalence appends the last coordinate. -/
theorem coordEquiv_symm_apply (n : ℕ) (y : ℝ) (z : Fin n → ℝ) :
    (coordEquiv n).symm (y, z) = Fin.snoc z y := by
  simp [coordEquiv, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv_last,
    Fin.snocEquiv_apply]

/-- The slice of a function at a fixed last coordinate. -/
def sliceFunction {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (y : ℝ) (z : Fin n → ℝ) : ℝ :=
  f ((coordEquiv n).symm (y, z))

/-- The strong maximal function of one slice. -/
def partialStrongMax {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (y : ℝ) (z : Fin n → ℝ) : ℝ≥0∞ :=
  strongMaximalFunction (sliceFunction f y) z

/-- Slices of a measurable function are measurable. -/
theorem sliceFunction_measurable {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f)
    (y : ℝ) : Measurable (sliceFunction f y) :=
  hf.comp ((coordEquiv n).symm.measurable.comp measurable_prodMk_left)

namespace OpenRectangle

/-- The rectangle obtained by dropping the last side. -/
def initial {n : ℕ} (R : OpenRectangle (n + 1)) : OpenRectangle n where
  lower := Fin.init R.lower
  upper := Fin.init R.upper
  lower_lt_upper := fun j ↦ R.lower_lt_upper j.castSucc

/-- The last side of a rectangle. -/
def lastSide {n : ℕ} (R : OpenRectangle (n + 1)) : OpenInterval where
  left := R.lower (Fin.last n)
  right := R.upper (Fin.last n)
  left_lt_right := R.lower_lt_upper (Fin.last n)

/-- A point lies in the rectangle exactly when its factors lie in the sides. -/
theorem carrier_eq_preimage {n : ℕ} (R : OpenRectangle (n + 1)) :
    R.carrier = coordEquiv n ⁻¹' (R.lastSide.carrier ×ˢ R.initial.carrier) := by
  ext x
  simp only [mem_preimage, coordEquiv_apply, mem_prod]
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · simpa [lastSide, OpenInterval.carrier, mem_Ioo] using hx (Fin.last n)
    · intro j
      simpa [initial, carrier, Fin.init] using hx j.castSucc
  · intro hx j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · simpa [initial, carrier, Fin.init] using hx.2 i
    · simpa [lastSide, OpenInterval.carrier, mem_Ioo] using hx.1

/-- The volume of a rectangle is the product of the volumes of its factors. -/
theorem volume_carrier_prod {n : ℕ} (R : OpenRectangle (n + 1)) :
    volume R.carrier = volume R.lastSide.carrier * volume R.initial.carrier := by
  have hev : MeasurePreserving (coordEquiv n) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)
  rw [R.carrier_eq_preimage, hev.measure_preimage_equiv, Measure.volume_eq_prod,
    Measure.prod_prod]

/-- The last side has volume equal to its length. -/
theorem volume_lastSide {n : ℕ} (R : OpenRectangle (n + 1)) :
    volume R.lastSide.carrier = ENNReal.ofReal R.lastSide.length := by
  simp [lastSide, OpenInterval.carrier, OpenInterval.length, Real.volume_Ioo]

end OpenRectangle

/-- The volume of a rectangle is positive. -/
theorem OpenRectangle.volume_carrier_pos {d : ℕ} (R : OpenRectangle d) :
    0 < volume R.carrier := by
  rw [R.volume_carrier]
  refine Finset.prod_induction _ (fun t ↦ 0 < t) ?_ ?_ ?_
  · intro a b ha hb
    exact ENNReal.mul_pos ha.ne' hb.ne'
  · exact zero_lt_one
  · intro j _
    exact ENNReal.ofReal_pos.2 (sub_pos.2 (R.lower_lt_upper j))

/-- The volume of a rectangle is finite. -/
theorem OpenRectangle.volume_carrier_lt_top {d : ℕ} (R : OpenRectangle d) :
    volume R.carrier < ∞ := by
  rw [R.volume_carrier]
  exact ENNReal.prod_lt_top fun j _ ↦ ENNReal.ofReal_lt_top

/-- A nonnegative integrand splits as an iterated integral over the sides. -/
theorem lintegral_rectangle_slice {n : ℕ} {g : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hg : Measurable g)
    (R : OpenRectangle (n + 1)) :
    ∫⁻ x in R.carrier, g x =
      ∫⁻ y in R.lastSide.carrier,
        ∫⁻ z in R.initial.carrier, g ((coordEquiv n).symm (y, z)) := by
  have hev : MeasurePreserving (⇑(coordEquiv n).symm) volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)).symm
  have hpre : (coordEquiv n).symm ⁻¹' R.carrier =
      R.lastSide.carrier ×ˢ R.initial.carrier := by
    rw [R.carrier_eq_preimage]
    ext p
    simp
  rw [← hev.setLIntegral_comp_preimage_emb (coordEquiv n).symm.measurableEmbedding g R.carrier,
    hpre]
  refine setLIntegral_prod (fun p ↦ g ((coordEquiv n).symm p)) ?_
  exact (hg.comp (coordEquiv n).symm.measurable).aemeasurable.restrict

/-- The strong maximal function is at most the one-dimensional maximal function of its slices. -/
theorem strongMaximal_le_partial {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f)
    (x : Fin (n + 1) → ℝ) :
    strongMaximalFunction f x ≤
      oneDimMaximalENN (fun y ↦ partialStrongMax f y (Fin.init x)) (x (Fin.last n)) := by
  refine iSup_le fun R ↦ iSup_le fun hxR ↦ ?_
  let g : (Fin (n + 1) → ℝ) → ℝ≥0∞ := fun w ↦ ENNReal.ofReal |f w|
  have hg : Measurable g := by
    simpa [g, Real.norm_eq_abs] using hf.norm.ennreal_ofReal
  let V : ℝ≥0∞ := volume R.initial.carrier
  let L : ℝ≥0∞ := volume R.lastSide.carrier
  have hV0 : V ≠ 0 := (R.initial.volume_carrier_pos).ne'
  have hVtop : V ≠ ∞ := R.initial.volume_carrier_lt_top.ne
  have hL : L = ENNReal.ofReal R.lastSide.length := R.volume_lastSide
  have hint := lintegral_rectangle_slice hg R
  have hvol := R.volume_carrier_prod
  have hz : Fin.init x ∈ R.initial.carrier := by
    intro j
    simpa [OpenRectangle.initial, OpenRectangle.carrier, Fin.init] using hxR j.castSucc
  have hy : x (Fin.last n) ∈ R.lastSide.carrier := by
    simpa [OpenRectangle.lastSide, OpenInterval.carrier, mem_Ioo] using hxR (Fin.last n)
  let φ : ℝ → ℝ≥0∞ := fun y ↦
    ∫⁻ z in R.initial.carrier, g ((coordEquiv n).symm (y, z))
  have hslice : ∀ y, φ y / V ≤ partialStrongMax f y (Fin.init x) := by
    intro y
    have havg : φ y / V =
        (∫⁻ w in R.initial.carrier, ENNReal.ofReal |sliceFunction f y w|) / V := by
      simp [φ, g, sliceFunction]
    rw [havg]
    unfold partialStrongMax strongMaximalFunction
    exact (le_iSup (fun h : Fin.init x ∈ R.initial.carrier ↦
        (∫⁻ w in R.initial.carrier, ENNReal.ofReal |sliceFunction f y w|) /
          volume R.initial.carrier) hz).trans
      (le_iSup (fun S : OpenRectangle n ↦ ⨆ h : Fin.init x ∈ S.carrier,
        (∫⁻ w in S.carrier, ENNReal.ofReal |sliceFunction f y w|) / volume S.carrier)
        R.initial)
  have hφle : ∀ y, φ y ≤ partialStrongMax f y (Fin.init x) * V :=
    fun y ↦ (ENNReal.div_le_iff_le_mul (Or.inl hV0) (Or.inl hVtop)).1 (hslice y)
  have hnum : ∫⁻ y in R.lastSide.carrier, φ y ≤
      V * ∫⁻ y in R.lastSide.carrier, partialStrongMax f y (Fin.init x) := by
    have hs : MeasurableSet R.lastSide.carrier := by
      simp [OpenRectangle.lastSide, OpenInterval.carrier]
    have hle := setLIntegral_mono' (μ := (volume : Measure ℝ)) hs fun y _ ↦
      (hφle y).trans (by rw [mul_comm])
    have hmul := lintegral_const_mul' (μ := volume.restrict R.lastSide.carrier) V
      (fun y ↦ partialStrongMax f y (Fin.init x)) hVtop
    exact hle.trans_eq hmul
  have hI : (∫⁻ y in R.lastSide.carrier, partialStrongMax f y (Fin.init x)) / L =
      intervalAverage (fun y ↦ partialStrongMax f y (Fin.init x)) R.lastSide := by
    simp [intervalAverage, OpenInterval.carrier, hL]
  calc
    (∫⁻ w in R.carrier, g w) / volume R.carrier
        = (∫⁻ y in R.lastSide.carrier, φ y) / (L * V) := by rw [hint, hvol]
    _ ≤ (V * ∫⁻ y in R.lastSide.carrier, partialStrongMax f y (Fin.init x)) / (L * V) :=
        ENNReal.div_le_div_right hnum _
    _ = (∫⁻ y in R.lastSide.carrier, partialStrongMax f y (Fin.init x)) / L := by
        rw [mul_comm L V, ENNReal.mul_div_mul_left _ _ hV0 hVtop]
    _ = intervalAverage (fun y ↦ partialStrongMax f y (Fin.init x)) R.lastSide := hI
    _ ≤ oneDimMaximalENN (fun y ↦ partialStrongMax f y (Fin.init x)) (x (Fin.last n)) := by
        unfold oneDimMaximalENN
        exact (le_iSup (fun h : x (Fin.last n) ∈ R.lastSide.carrier ↦
            intervalAverage (fun y ↦ partialStrongMax f y (Fin.init x)) R.lastSide) hy).trans
          (le_iSup (fun I : OpenInterval ↦ ⨆ h : x (Fin.last n) ∈ I.carrier,
            intervalAverage (fun y ↦ partialStrongMax f y (Fin.init x)) I) R.lastSide)

/-- The carrier of a rectangle is measurable. -/
theorem OpenRectangle.measurableSet_carrier {d : ℕ} (R : OpenRectangle d) :
    MeasurableSet R.carrier := by
  rw [R.carrier_eq_pi]
  exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo

/-- The strong maximal function increases when absolute values increase. -/
theorem strongMaximalFunction_mono {d : ℕ} {f g : (Fin d → ℝ) → ℝ}
    (hfg : ∀ x, |f x| ≤ |g x|) (x : Fin d → ℝ) :
    strongMaximalFunction f x ≤ strongMaximalFunction g x := by
  refine iSup_le fun R ↦ iSup_le fun hx ↦ ?_
  have hnum : ∫⁻ y in R.carrier, ENNReal.ofReal |f y| ≤
      ∫⁻ y in R.carrier, ENNReal.ofReal |g y| :=
    setLIntegral_mono' (μ := (volume : Measure (Fin d → ℝ))) R.measurableSet_carrier
      fun y _ ↦ ENNReal.ofReal_le_ofReal (hfg y)
  exact (ENNReal.div_le_div_right hnum _).trans
    ((le_iSup (fun h : x ∈ R.carrier ↦
      (∫⁻ y in R.carrier, ENNReal.ofReal |g y|) / volume R.carrier) hx).trans
      (le_iSup (fun S : OpenRectangle d ↦ ⨆ h : x ∈ S.carrier,
        (∫⁻ y in S.carrier, ENNReal.ofReal |g y|) / volume S.carrier) R))

/-- A pointwise bound by a constant bounds the strong maximal function. -/
theorem strongMaximalFunction_le_ofReal {d : ℕ} {f : (Fin d → ℝ) → ℝ} {c : ℝ}
    (_hc : 0 ≤ c) (hf : ∀ x, |f x| ≤ c) (x : Fin d → ℝ) :
    strongMaximalFunction f x ≤ ENNReal.ofReal c := by
  refine iSup_le fun R ↦ iSup_le fun _ ↦ ?_
  have hnum : ∫⁻ y in R.carrier, ENNReal.ofReal |f y| ≤
      ENNReal.ofReal c * volume R.carrier := by
    calc
      ∫⁻ y in R.carrier, ENNReal.ofReal |f y| ≤ ∫⁻ y in R.carrier, ENNReal.ofReal c :=
        setLIntegral_mono' (μ := (volume : Measure (Fin d → ℝ))) R.measurableSet_carrier
          fun y _ ↦ ENNReal.ofReal_le_ofReal (hf y)
      _ = ENNReal.ofReal c * volume R.carrier := by
        rw [setLIntegral_const]
  exact ENNReal.div_le_of_le_mul hnum

/-- The maximal function of a sum is at most the sum of the maximal functions. -/
theorem strongMaximalFunction_le_add {d : ℕ} {f g h : (Fin d → ℝ) → ℝ}
    (hg : Measurable g) (hle : ∀ y, |f y| ≤ |g y| + |h y|)
    (x : Fin d → ℝ) :
    strongMaximalFunction f x ≤ strongMaximalFunction g x + strongMaximalFunction h x := by
  refine iSup_le fun R ↦ iSup_le fun hx ↦ ?_
  have hgabs : Measurable fun y ↦ ENNReal.ofReal |g y| := by
    simpa [Real.norm_eq_abs] using hg.norm.ennreal_ofReal
  have hpoint : ∀ y, ENNReal.ofReal |f y| ≤ ENNReal.ofReal |g y| + ENNReal.ofReal |h y| := by
    intro y
    calc
      ENNReal.ofReal |f y| ≤ ENNReal.ofReal (|g y| + |h y|) :=
        ENNReal.ofReal_le_ofReal (hle y)
      _ = ENNReal.ofReal |g y| + ENNReal.ofReal |h y| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
  have hnum : ∫⁻ y in R.carrier, ENNReal.ofReal |f y| ≤
      (∫⁻ y in R.carrier, ENNReal.ofReal |g y|) +
        (∫⁻ y in R.carrier, ENNReal.ofReal |h y|) := by
    calc
      ∫⁻ y in R.carrier, ENNReal.ofReal |f y| ≤
          ∫⁻ y in R.carrier, (ENNReal.ofReal |g y| + ENNReal.ofReal |h y|) :=
        setLIntegral_mono' (μ := (volume : Measure (Fin d → ℝ))) R.measurableSet_carrier
          fun y _ ↦ hpoint y
      _ = (∫⁻ y in R.carrier, ENNReal.ofReal |g y|) +
          (∫⁻ y in R.carrier, ENNReal.ofReal |h y|) :=
        lintegral_add_left (μ := volume.restrict R.carrier) hgabs _
  have hdiv : (∫⁻ y in R.carrier, ENNReal.ofReal |f y|) / volume R.carrier ≤
      (∫⁻ y in R.carrier, ENNReal.ofReal |g y|) / volume R.carrier +
        (∫⁻ y in R.carrier, ENNReal.ofReal |h y|) / volume R.carrier := by
    calc
      (∫⁻ y in R.carrier, ENNReal.ofReal |f y|) / volume R.carrier ≤
          ((∫⁻ y in R.carrier, ENNReal.ofReal |g y|) +
            (∫⁻ y in R.carrier, ENNReal.ofReal |h y|)) / volume R.carrier :=
        ENNReal.div_le_div_right hnum _
      _ = (∫⁻ y in R.carrier, ENNReal.ofReal |g y|) / volume R.carrier +
          (∫⁻ y in R.carrier, ENNReal.ofReal |h y|) / volume R.carrier :=
        ENNReal.add_div
  -- The two summands are rectangle averages, hence at most the maximal functions.
  have havg : (∫⁻ y in R.carrier, ENNReal.ofReal |g y|) / volume R.carrier +
      (∫⁻ y in R.carrier, ENNReal.ofReal |h y|) / volume R.carrier ≤
      strongMaximalFunction g x + strongMaximalFunction h x := by
    gcongr
    · exact (le_iSup (fun hmem : x ∈ R.carrier ↦
          (∫⁻ y in R.carrier, ENNReal.ofReal |g y|) / volume R.carrier) hx).trans
        (le_iSup (fun S : OpenRectangle d ↦ ⨆ hmem : x ∈ S.carrier,
          (∫⁻ y in S.carrier, ENNReal.ofReal |g y|) / volume S.carrier) R)
    · exact (le_iSup (fun hmem : x ∈ R.carrier ↦
          (∫⁻ y in R.carrier, ENNReal.ofReal |h y|) / volume R.carrier) hx).trans
        (le_iSup (fun S : OpenRectangle d ↦ ⨆ hmem : x ∈ S.carrier,
          (∫⁻ y in S.carrier, ENNReal.ofReal |h y|) / volume S.carrier) R)
  exact hdiv.trans havg

/-- Values at most `t / 2` do not contribute to the strict superlevel set of height `t`. -/
theorem strongMaximal_lt_trunc {d : ℕ} {t : ℝ} (ht : 0 < t) {f : (Fin d → ℝ) → ℝ}
    (hf : Measurable f) {x : Fin d → ℝ}
    (hx : ENNReal.ofReal t < strongMaximalFunction f x) :
    ENNReal.ofReal (t / 2) <
      strongMaximalFunction (fun y ↦ if t / 2 < |f y| then f y else 0) x := by
  let big : (Fin d → ℝ) → ℝ := fun y ↦ if t / 2 < |f y| then f y else 0
  let small : (Fin d → ℝ) → ℝ := fun y ↦ if t / 2 < |f y| then 0 else f y
  have hset : MeasurableSet {y | t / 2 < |f y|} := by
    simpa [Real.norm_eq_abs] using measurableSet_lt measurable_const hf.norm
  have hbig : Measurable big := hf.piecewise hset measurable_const
  have hsplit : ∀ y, |f y| ≤ |big y| + |small y| := by
    intro y
    by_cases hy : t / 2 < |f y|
    · simp [big, small, hy]
    · simp [big, small, hy]
  have hsmall_le : ∀ y, |small y| ≤ t / 2 := by
    intro y
    by_cases hy : t / 2 < |f y|
    · simp only [small, hy, ite_true, abs_zero]
      exact div_nonneg ht.le (by norm_num : (0 : ℝ) ≤ 2)
    · simpa [small, hy] using le_of_not_gt hy
  have hle := strongMaximalFunction_le_add hbig hsplit x
  have hconst := strongMaximalFunction_le_ofReal (div_nonneg ht.le (by norm_num : (0 : ℝ) ≤ 2))
    hsmall_le x
  by_contra hnot
  have hbig_le : strongMaximalFunction big x ≤ ENNReal.ofReal (t / 2) := not_lt.mp hnot
  have : strongMaximalFunction f x ≤ ENNReal.ofReal t := by
    calc
      strongMaximalFunction f x ≤ strongMaximalFunction big x + strongMaximalFunction small x :=
        hle
      _ ≤ ENNReal.ofReal (t / 2) + ENNReal.ofReal (t / 2) := add_le_add hbig_le hconst
      _ = ENNReal.ofReal t := by
        rw [← ENNReal.ofReal_add (div_nonneg ht.le (by norm_num)) (div_nonneg ht.le (by norm_num))]
        congr 1
        ring
  exact not_lt.mpr this hx

/-- The scaled kernel, written at an arbitrary positive height. -/
theorem strongMaximal_iteration_scale {n : ℕ} (hn : 1 ≤ n) {a v : ℝ} (ha : 0 < a) (hv : 0 ≤ v) :
    (a / 2) * strongMaximalGrowth n (2 * v / a) +
      (if v ≤ a / 4 then (0 : ℝ) else
        ∫ t in (a / 2)..(2 * v), strongMaximalGrowth n (2 * v / t)) ≤
      a * strongMaximalIterationFactor n * strongMaximalGrowth (n + 1) (v / a) := by
  set u : ℝ := v / a
  have hu : 0 ≤ u := div_nonneg hv ha.le
  have hker := strongMaximalGrowth_scaled_kernel hn hu
  have hmul := mul_le_mul_of_nonneg_left hker ha.le
  have hhalf : a * ((1 / 2) * strongMaximalGrowth n (2 * u)) =
      (a / 2) * strongMaximalGrowth n (2 * v / a) := by
    rw [show 2 * u = 2 * v / a by unfold u; field_simp [ha.ne']]
    ring
  by_cases hv4 : v ≤ a / 4
  · have hu4 : u ≤ 1 / 4 := by
      unfold u
      rw [div_le_iff₀ ha]
      linarith
    simp only [hv4, hu4, ite_true, add_zero] at hmul ⊢
    rw [← hhalf]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  · have hu4 : ¬ u ≤ 1 / 4 := by
      intro hu4
      apply hv4
      unfold u at hu4
      rw [div_le_iff₀ ha] at hu4
      linarith
    simp only [hv4, hu4, ite_false] at hmul ⊢
    have hsub : a * (∫ s in (1 / 2 : ℝ)..(2 * u), strongMaximalGrowth n (2 * u / s)) =
        ∫ t in (a / 2)..(2 * v), strongMaximalGrowth n (2 * v / t) := by
      have hchange := intervalIntegral.smul_integral_comp_mul_left (a := (1 / 2 : ℝ))
        (b := 2 * u) (f := fun t ↦ strongMaximalGrowth n (2 * v / t)) a
      have hfun : ∀ s, strongMaximalGrowth n (2 * v / (a * s)) =
          strongMaximalGrowth n (2 * u / s) := by
        intro s
        congr 1
        unfold u
        field_simp [ha.ne']
      simp_rw [hfun, smul_eq_mul] at hchange
      rw [show a * (1 / 2 : ℝ) = a / 2 by ring] at hchange
      rw [show a * (2 * u) = 2 * v by unfold u; field_simp [ha.ne']] at hchange
      exact hchange
    rw [← hhalf, ← hsub]
    have hfactor : a * ((1 / 2) * strongMaximalGrowth n (2 * u) +
        ∫ s in (1 / 2 : ℝ)..(2 * u), strongMaximalGrowth n (2 * u / s)) =
        a * ((1 / 2) * strongMaximalGrowth n (2 * u)) +
          a * ∫ s in (1 / 2 : ℝ)..(2 * u), strongMaximalGrowth n (2 * u / s) := by ring
    rw [← hfactor]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Scaling the argument of the endpoint growth costs only a constant factor. -/
theorem strongMaximalGrowth_smul_le {n : ℕ} {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) :
    strongMaximalGrowth n (c * u) ≤
      c * (1 + |Real.log c|) ^ (n - 1) * strongMaximalGrowth (n + 1) u := by
  by_cases hu0 : u = 0
  · simp [strongMaximalGrowth, hu0, Real.log_zero]
  · have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
    have hlogle : 1 + max 0 (Real.log (c * u)) ≤
        (1 + |Real.log c|) * (1 + max 0 (Real.log u)) := by
      by_cases hcu : c * u ≤ 1
      · have hlog : Real.log (c * u) ≤ 0 := Real.log_nonpos (mul_nonneg hc.le hu) hcu
        simp only [max_eq_left hlog, add_zero]
        nlinarith [abs_nonneg (Real.log c), le_max_left (0 : ℝ) (Real.log u)]
      · have hcu' : 1 < c * u := lt_of_not_ge hcu
        have hlogeq : Real.log (c * u) = Real.log c + Real.log u :=
          Real.log_mul hc.ne' hu'.ne'
        have hposlog : 0 ≤ Real.log (c * u) := Real.log_nonneg hcu'.le
        rw [hlogeq, max_eq_right (hlogeq ▸ hposlog)]
        by_cases hlu : Real.log u ≤ 0
        · rw [max_eq_left hlu, add_zero, mul_one]
          linarith [le_abs_self (Real.log c)]
        · rw [max_eq_right (le_of_not_ge hlu)]
          have habs : Real.log c ≤ |Real.log c| := le_abs_self _
          have hposu : 0 ≤ Real.log u := le_of_not_ge hlu
          have hnonneg : 0 ≤ |Real.log c| * Real.log u :=
            mul_nonneg (abs_nonneg _) hposu
          calc
            1 + (Real.log c + Real.log u) ≤ 1 + (|Real.log c| + Real.log u) := by
              linarith [habs]
            _ = 1 + |Real.log c| + Real.log u := by ring
            _ ≤ 1 + |Real.log c| + Real.log u + |Real.log c| * Real.log u := by
              linarith [hnonneg]
            _ = (1 + |Real.log c|) * (1 + Real.log u) := by ring
    have hbase : 0 ≤ 1 + max 0 (Real.log (c * u)) := by
      linarith [le_max_left (0 : ℝ) (Real.log (c * u))]
    have hpow := pow_le_pow_left₀ hbase hlogle (n - 1)
    have hone : (1 : ℝ) ≤ 1 + max 0 (Real.log u) := by
      linarith [le_max_left (0 : ℝ) (Real.log u)]
    simp only [strongMaximalGrowth, Nat.add_sub_cancel]
    calc
      c * u * (1 + max 0 (Real.log (c * u))) ^ (n - 1) ≤
          c * u * ((1 + |Real.log c|) * (1 + max 0 (Real.log u))) ^ (n - 1) := by
        gcongr
      _ = c * (1 + |Real.log c|) ^ (n - 1) *
          (u * (1 + max 0 (Real.log u)) ^ (n - 1)) := by
        rw [mul_pow]
        ring
      _ ≤ c * (1 + |Real.log c|) ^ (n - 1) *
          (u * (1 + max 0 (Real.log u)) ^ n) := by
        gcongr
        exact Nat.sub_le n 1

/-- The endpoint growth is a measurable function of its argument. -/
theorem measurable_strongMaximalGrowth (n : ℕ) : Measurable (strongMaximalGrowth n) := by
  unfold strongMaximalGrowth
  exact (measurable_id.mul ((measurable_const.add
    ((measurable_const.max Real.measurable_log))).pow_const (n - 1)))

/-- An open axis-parallel rectangle with rational endpoints. -/
structure RatRectangle (d : ℕ) where
  /-- Lower rational coordinates. -/
  lower : Fin d → ℚ
  /-- Upper rational coordinates. -/
  upper : Fin d → ℚ
  /-- Every side has positive rational length. -/
  lower_lt_upper : ∀ j, lower j < upper j

namespace RatRectangle

/-- The underlying open set. -/
def carrier {d : ℕ} (J : RatRectangle d) : Set (Fin d → ℝ) :=
  {x | ∀ j, (J.lower j : ℝ) < x j ∧ x j < J.upper j}

/-- A rational rectangle viewed as an open rectangle. -/
def toOpen {d : ℕ} (J : RatRectangle d) : OpenRectangle d where
  lower := fun j ↦ J.lower j
  upper := fun j ↦ J.upper j
  lower_lt_upper := fun j ↦ by exact_mod_cast J.lower_lt_upper j

/-- The carrier agrees with the underlying open rectangle. -/
theorem carrier_toOpen {d : ℕ} (J : RatRectangle d) : J.toOpen.carrier = J.carrier := by
  ext x
  simp [toOpen, carrier, OpenRectangle.carrier]

/-- Rational rectangles form a countable family. -/
instance {d : ℕ} : Countable (RatRectangle d) :=
  Function.Injective.countable (f := fun J : RatRectangle d ↦ (J.lower, J.upper))
    (fun I J h ↦ by cases I; cases J; aesop)

/-- Extended average of a nonnegative integrand. -/
def average {d : ℕ} (g : (Fin d → ℝ) → ℝ≥0∞) (J : RatRectangle d) : ℝ≥0∞ :=
  (∫⁻ x in J.carrier, g x) / volume J.carrier

end RatRectangle

/-- An infinite rectangular integral stays infinite on a rational enlargement. -/
theorem exists_ratRectangle_enlargement_top {d : ℕ} (_hd : 0 < d)
    (g : (Fin d → ℝ) → ℝ≥0∞) (R : OpenRectangle d)
    (hinf : ∫⁻ x in R.carrier, g x = ∞) :
    ∃ J : RatRectangle d, R.carrier ⊆ J.carrier ∧ ∫⁻ x in J.carrier, g x = ∞ := by
  have hlo : ∀ j : Fin d, ∃ q : ℚ, R.lower j - 1 < (q : ℝ) ∧ (q : ℝ) < R.lower j :=
    fun j ↦ exists_rat_btwn (by linarith)
  choose lo hlo1 hlo2 using hlo
  have hhi : ∀ j : Fin d, ∃ q : ℚ, R.upper j < (q : ℝ) ∧ (q : ℝ) < R.upper j + 1 :=
    fun j ↦ exists_rat_btwn (by linarith)
  choose hi hhi1 hhi2 using hhi
  have hlt : ∀ j, lo j < hi j := by
    intro j
    exact_mod_cast lt_trans (hlo2 j) (lt_trans (R.lower_lt_upper j) (hhi1 j))
  let J : RatRectangle d := ⟨lo, hi, hlt⟩
  have hsub : R.carrier ⊆ J.carrier := by
    intro x hx j
    exact ⟨lt_trans (hlo2 j) (hx j).1, lt_trans (hx j).2 (hhi1 j)⟩
  refine ⟨J, hsub, ?_⟩
  exact eq_top_iff.2 <| hinf ▸ lintegral_mono_set hsub

/-- A finite strict rectangular average survives a small outward rational perturbation. -/
theorem exists_ratRectangle_of_average_gt_finite {d : ℕ} (hd : 0 < d)
    (g : (Fin d → ℝ) → ℝ≥0∞) (R : OpenRectangle d) {α : ℝ} (hα : 0 < α)
    (havg : ENNReal.ofReal α < (∫⁻ x in R.carrier, g x) / volume R.carrier)
    (hfin : ∫⁻ x in R.carrier, g x ≠ ∞) :
    ∃ J : RatRectangle d, R.carrier ⊆ J.carrier ∧
      ENNReal.ofReal α < RatRectangle.average g J := by
  let s : Fin d → ℝ := fun j ↦ R.upper j - R.lower j
  have hs : ∀ j, 0 < s j := fun j ↦ sub_pos.2 (R.lower_lt_upper j)
  let P : ℝ := ∏ j, s j
  have hP : 0 < P := Finset.prod_pos fun j _ ↦ hs j
  have hvol : volume R.carrier = ENNReal.ofReal P := by
    rw [R.volume_carrier]
    exact (ENNReal.ofReal_prod_of_nonneg fun j _ ↦ (hs j).le).symm
  have hmul : ENNReal.ofReal α * volume R.carrier < ∫⁻ x in R.carrier, g x := by
    refine (ENNReal.lt_div_iff_mul_lt ?_ ?_).1 havg
    · exact Or.inl R.volume_carrier_pos.ne'
    · exact Or.inl R.volume_carrier_lt_top.ne
  have hprod : ENNReal.ofReal (α * P) < ∫⁻ x in R.carrier, g x := by
    simpa [hvol, ENNReal.ofReal_mul hα.le] using hmul
  set I : ℝ := (∫⁻ x in R.carrier, g x).toReal
  have hIpos : 0 < I := ENNReal.toReal_pos ((ENNReal.ofReal_pos.2 (mul_pos hα hP)).trans hprod).ne'
    hfin
  have hAP : α * P < I := by
    rw [← ENNReal.ofReal_lt_ofReal_iff hIpos, ENNReal.ofReal_toReal hfin]
    exact hprod
  set ratio : ℝ := I / (α * P)
  have hratio : 1 < ratio := (one_lt_div (mul_pos hα hP)).2 hAP
  set η : ℝ := (1 + ratio) / 2
  have hη1 : 1 < η := by unfold η; linarith
  have hηr : η < ratio := by unfold η; linarith
  have hηpos : 0 < η := lt_trans zero_lt_one hη1
  set ρ : ℝ := η ^ (1 / (d : ℝ))
  have hρ : 1 < ρ := Real.one_lt_rpow hη1 (one_div_pos.2 (Nat.cast_pos.2 hd))
  have hρd : ρ ^ d = η := by
    rw [← Real.rpow_natCast]
    unfold ρ
    rw [← Real.rpow_mul hηpos.le, one_div, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hd.ne'),
      Real.rpow_one]
  let δ : Fin d → ℝ := fun j ↦ s j * (ρ - 1) / 2
  have hδpos : ∀ j, 0 < δ j := fun j ↦ by
    unfold δ
    exact div_pos (mul_pos (hs j) (sub_pos.2 hρ)) (by norm_num)
  have hlo : ∀ j, ∃ q : ℚ, R.lower j - δ j < (q : ℝ) ∧ (q : ℝ) < R.lower j :=
    fun j ↦ exists_rat_btwn (sub_lt_self _ (hδpos j))
  choose lo hlo1 hlo2 using hlo
  have hhi : ∀ j, ∃ q : ℚ, R.upper j < (q : ℝ) ∧ (q : ℝ) < R.upper j + δ j :=
    fun j ↦ exists_rat_btwn (lt_add_of_pos_right _ (hδpos j))
  choose hi hhi1 hhi2 using hhi
  have hord : ∀ j, lo j < hi j := by
    intro j
    exact_mod_cast lt_trans (hlo2 j) (lt_trans (R.lower_lt_upper j) (hhi1 j))
  let J : RatRectangle d := ⟨lo, hi, hord⟩
  have hsub : R.carrier ⊆ J.carrier := by
    intro x hx j
    exact ⟨lt_trans (hlo2 j) (hx j).1, lt_trans (hx j).2 (hhi1 j)⟩
  let t : Fin d → ℝ := fun j ↦ (hi j : ℝ) - lo j
  have htlt : ∀ j, t j < s j * ρ := by
    intro j
    calc
      t j = (hi j : ℝ) - lo j := rfl
      _ < R.upper j + δ j - lo j := by linarith [hhi2 j]
      _ < R.upper j + δ j - (R.lower j - δ j) := by linarith [hlo1 j]
      _ = s j + 2 * δ j := by unfold s; ring
      _ = s j * ρ := by unfold δ; ring
  have htpos : ∀ j, 0 < t j := fun j ↦ sub_pos.2 (by exact_mod_cast hord j)
  have hQ : ∏ j, t j < ∏ j, (s j * ρ) := by
    have hden : 0 < ∏ j, (s j * ρ) :=
      Finset.prod_pos fun j _ ↦ mul_pos (hs j) (lt_trans zero_lt_one hρ)
    rw [← div_lt_one hden, ← Finset.prod_div_distrib]
    let f : Fin d → ℝ := fun j ↦ t j / (s j * ρ)
    have hterm_pos : ∀ j, 0 < f j := fun j ↦
      div_pos (htpos j) (mul_pos (hs j) (lt_trans zero_lt_one hρ))
    have hterm_lt : ∀ j, f j < 1 := fun j ↦ by
      unfold f
      rw [div_lt_one (mul_pos (hs j) (lt_trans zero_lt_one hρ))]
      exact htlt j
    have hprod_lt : ∀ u : Finset (Fin d), u.Nonempty → ∏ j ∈ u, f j < 1 := by
      intro u
      induction u using Finset.induction with
      | empty => intro hne; exact absurd hne (by simp)
      | insert a s ha ih =>
        intro _hne
        rw [Finset.prod_insert ha]
        by_cases hsne : s.Nonempty
        · have hps : ∏ j ∈ s, f j < 1 := ih hsne
          have hps0 : 0 < ∏ j ∈ s, f j :=
            Finset.prod_pos fun j hj ↦ hterm_pos j
          calc
            f a * ∏ j ∈ s, f j < 1 * ∏ j ∈ s, f j :=
              mul_lt_mul_of_pos_right (hterm_lt a) hps0
            _ = ∏ j ∈ s, f j := one_mul _
            _ < 1 := hps
        · rw [Finset.not_nonempty_iff_eq_empty.1 hsne, Finset.prod_empty, mul_one]
          exact hterm_lt a
    exact hprod_lt Finset.univ ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  have hprodρ : ∏ j, (s j * ρ) = P * η := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hρd]
  have hQη : ∏ j, t j < P * η := hQ.trans_eq hprodρ
  have hαQ : α * ∏ j, t j < I := by
    have hleft : α * ∏ j, t j < α * (P * η) := mul_lt_mul_of_pos_left hQη hα
    have hmid : α * (P * η) = α * P * η := by ring
    have hright : α * P * η < α * P * ratio :=
      mul_lt_mul_of_pos_left hηr (mul_pos hα hP)
    have hratioI : α * P * ratio = I := by
      unfold ratio
      field_simp [hα.ne', hP.ne']
    linarith
  have hvolJ : volume J.carrier = ENNReal.ofReal (∏ j, t j) := by
    rw [← J.carrier_toOpen, J.toOpen.volume_carrier]
    have hside : ∀ j, J.toOpen.upper j - J.toOpen.lower j = t j := fun j ↦ by
      simp [RatRectangle.toOpen, J, t]
    simp_rw [hside]
    exact (ENNReal.ofReal_prod_of_nonneg fun j _ ↦ (htpos j).le).symm
  have hintJ : ∫⁻ x in R.carrier, g x ≤ ∫⁻ x in J.carrier, g x :=
    lintegral_mono_set hsub
  have hstrict : ENNReal.ofReal (α * ∏ j, t j) < ∫⁻ x in J.carrier, g x := by
    refine lt_of_lt_of_le ?_ hintJ
    rw [← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff hIpos).2 hαQ
  have hdiv : ENNReal.ofReal α < RatRectangle.average g J := by
    refine (ENNReal.lt_div_iff_mul_lt ?_ ?_).2 ?_
    · exact Or.inl <| by
        rw [hvolJ]
        exact (ENNReal.ofReal_pos.2 (Finset.prod_pos fun j _ ↦ htpos j)).ne'
    · exact Or.inl <| by rw [hvolJ]; exact ENNReal.ofReal_ne_top
    simpa [RatRectangle.average, hvolJ, ENNReal.ofReal_mul hα.le] using hstrict
  exact ⟨J, hsub, hdiv⟩

/-- A strict rectangular average survives an outward rational perturbation. -/
theorem exists_ratRectangle_of_average_gt {d : ℕ} (hd : 0 < d)
    (g : (Fin d → ℝ) → ℝ≥0∞) (R : OpenRectangle d) {α : ℝ} (hα : 0 < α)
    (havg : ENNReal.ofReal α < (∫⁻ x in R.carrier, g x) / volume R.carrier) :
    ∃ J : RatRectangle d, R.carrier ⊆ J.carrier ∧
      ENNReal.ofReal α < RatRectangle.average g J := by
  by_cases hfin : ∫⁻ x in R.carrier, g x = ∞
  · obtain ⟨J, hsub, hJ⟩ := exists_ratRectangle_enlargement_top hd g R hfin
    have hvol_ne : volume J.carrier ≠ ∞ := J.toOpen.volume_carrier_lt_top.ne
    have havgJ : RatRectangle.average g J = ∞ := by
      unfold RatRectangle.average
      rw [hJ, ENNReal.div_eq_top]
      exact Or.inr ⟨by simp, hvol_ne⟩
    exact ⟨J, hsub, by simp [havgJ, ENNReal.ofReal_lt_top]⟩
  · exact exists_ratRectangle_of_average_gt_finite hd g R hα havg hfin

/-- A strict strong-maximal inequality is witnessed by a rational rectangle. -/
theorem exists_ratRectangle_of_strongMaximal_gt {d : ℕ} (hd : 0 < d)
    (f : (Fin d → ℝ) → ℝ) {x : Fin d → ℝ} {α : ℝ} (hα : 0 < α)
    (hx : ENNReal.ofReal α < strongMaximalFunction f x) :
    ∃ J : RatRectangle d, x ∈ J.carrier ∧ ENNReal.ofReal α <
      RatRectangle.average (fun y ↦ ENNReal.ofReal |f y|) J := by
  rw [strongMaximalFunction, lt_iSup_iff] at hx
  obtain ⟨R, hxR⟩ := hx
  obtain ⟨hxmem, havg⟩ := lt_iSup_iff.mp hxR
  obtain ⟨J, hsub, hJ⟩ := exists_ratRectangle_of_average_gt hd
    (fun y ↦ ENNReal.ofReal |f y|) R hα havg
  exact ⟨J, hsub hxmem, hJ⟩

/-- The positive part of the logarithm is monotone on the nonnegative reals. -/
theorem logPlus_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    max 0 (Real.log u) ≤ max 0 (Real.log v) := by
  by_cases hu1 : u ≤ 1
  · have hlog : Real.log u ≤ 0 := Real.log_nonpos hu hu1
    simp only [max_eq_left hlog, le_max_left]
  · have hu1' : 1 < u := lt_of_not_ge hu1
    have hv1 : 1 < v := lt_of_lt_of_le hu1' huv
    rw [max_eq_right (Real.log_nonneg hu1'.le), max_eq_right (Real.log_nonneg hv1.le)]
    exact Real.log_le_log (zero_lt_one.trans hu1') huv

/-- Dividing the argument by an integer multiplies the growth by at most `1 / k`. -/
theorem strongMaximalGrowth_div_le {n k : ℕ} (hk : 1 ≤ k) {v : ℝ} (hv : 0 ≤ v) :
    strongMaximalGrowth n (v / k) ≤ (1 / (k : ℝ)) * strongMaximalGrowth n v := by
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 (by omega)
  have hlog : max 0 (Real.log (v / k)) ≤ max 0 (Real.log v) := by
    by_cases hv0 : v = 0
    · simp [hv0, Real.log_zero]
    · exact logPlus_mono (div_nonneg hv hk0.le) (by
        rw [div_le_iff₀ hk0]
        nlinarith [show (1 : ℝ) ≤ k by exact_mod_cast hk])
  simp only [strongMaximalGrowth]
  have hpow := pow_le_pow_left₀ (by linarith [le_max_left (0 : ℝ) (Real.log (v / k))]) hlog (n - 1)
  have hdiv : v / k * (1 + max 0 (Real.log v)) ^ (n - 1) =
      (1 / (k : ℝ)) * (v * (1 + max 0 (Real.log v)) ^ (n - 1)) := by
    field_simp [hk0.ne']
  calc
    v / k * (1 + max 0 (Real.log (v / k))) ^ (n - 1) ≤
        v / k * (1 + max 0 (Real.log v)) ^ (n - 1) := by gcongr
    _ = (1 / (k : ℝ)) * (v * (1 + max 0 (Real.log v)) ^ (n - 1)) := hdiv

/-- Extended average of one slice over a rational rectangle. -/
def sliceRatAverage {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (y : ℝ) (J : RatRectangle n) : ℝ≥0∞ :=
  RatRectangle.average (fun z ↦ ENNReal.ofReal |f ((coordEquiv n).symm (y, z))|) J

/-- Slice averages over a fixed rational rectangle are measurable in the last coordinate. -/
theorem measurable_sliceRatAverage {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f)
    (J : RatRectangle n) : Measurable (sliceRatAverage f · J) := by
  set phi : ℝ × (Fin n → ℝ) → ℝ≥0∞ :=
    fun p ↦ ENNReal.ofReal |f ((coordEquiv n).symm p)|
  have hphi : Measurable phi :=
    ENNReal.measurable_ofReal.comp
      (continuous_abs.measurable.comp (hf.comp (coordEquiv n).symm.measurable))
  have hs : MeasurableSet J.carrier := by
    rw [← J.carrier_toOpen]
    exact J.toOpen.measurableSet_carrier
  unfold sliceRatAverage RatRectangle.average
  simp_rw [div_eq_mul_inv]
  have hfun : (fun y ↦
      (∫⁻ z in J.carrier, ENNReal.ofReal |f ((coordEquiv n).symm (y, z))|) *
        (volume J.carrier)⁻¹) =
      fun y ↦ (∫⁻ z, (Prod.snd ⁻¹' J.carrier).indicator phi (y, z)) *
        (volume J.carrier)⁻¹ := by
    funext y
    refine congrArg (fun t ↦ t * (volume J.carrier)⁻¹) ?_
    rw [← lintegral_indicator hs]
    refine lintegral_congr fun z ↦ ?_
    by_cases hz : z ∈ J.carrier
    · simp [phi, hz, Set.indicator]
    · simp [phi, hz, Set.indicator]
  rw [hfun]
  exact (hphi.indicator (hs.preimage measurable_snd)).lintegral_prod_right'.mul_const _

/-- The partial maximal function is the supremum of its rational-rectangle averages. -/
theorem partialStrongMax_eq_ratSup {n : ℕ} (hn : 0 < n) (f : (Fin (n + 1) → ℝ) → ℝ)
    (y : ℝ) (z : Fin n → ℝ) :
    partialStrongMax f y z =
      ⨆ J : RatRectangle n, ⨆ (_ : z ∈ J.carrier), sliceRatAverage f y J := by
  apply le_antisymm
  · refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
    by_cases hc0 : c = 0
    · simp [hc0]
    · have hct : c ≠ ∞ := ne_top_of_lt hc
      have hto : 0 < c.toReal := ENNReal.toReal_pos hc0 hct
      have hc' : ENNReal.ofReal c.toReal < partialStrongMax f y z := by
        simpa [ENNReal.ofReal_toReal hct] using hc
      obtain ⟨J, hz, hJ⟩ :=
        exists_ratRectangle_of_strongMaximal_gt hn (sliceFunction f y) hto hc'
      have hzJ : z ∈ J.carrier := by simpa [sliceFunction] using hz
      have hJ' : ENNReal.ofReal c.toReal < sliceRatAverage f y J := by
        simpa [sliceRatAverage, sliceFunction] using hJ
      have hle : sliceRatAverage f y J ≤
          ⨆ K : RatRectangle n, ⨆ (_ : z ∈ K.carrier), sliceRatAverage f y K :=
        (le_iSup (fun _ : z ∈ J.carrier ↦ sliceRatAverage f y J) hzJ).trans
          (le_iSup (fun K : RatRectangle n ↦
            ⨆ (_ : z ∈ K.carrier), sliceRatAverage f y K) J)
      simpa [ENNReal.ofReal_toReal hct] using (hJ'.trans_le hle).le
  · refine iSup_le fun J ↦ iSup_le fun hz ↦ ?_
    have havg : sliceRatAverage f y J =
        (∫⁻ w in J.toOpen.carrier, ENNReal.ofReal |sliceFunction f y w|) /
          volume J.toOpen.carrier := by
      simp [sliceRatAverage, RatRectangle.average, sliceFunction, ← J.carrier_toOpen]
    rw [havg]
    exact (le_iSup (fun h : z ∈ J.toOpen.carrier ↦
        (∫⁻ w in J.toOpen.carrier, ENNReal.ofReal |sliceFunction f y w|) /
          volume J.toOpen.carrier) (by simpa [RatRectangle.carrier_toOpen] using hz)).trans
      (le_iSup (fun S : OpenRectangle n ↦ ⨆ h : z ∈ S.carrier,
        (∫⁻ w in S.carrier, ENNReal.ofReal |sliceFunction f y w|) / volume S.carrier) J.toOpen)

end CKMA




