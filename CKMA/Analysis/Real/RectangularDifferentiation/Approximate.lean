/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.RectangularDifferentiation.Step
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Metrizable.Uniformity

/-!
# Rectangular differentiation of the global endpoint class

Continuous compactly supported functions are differentiated by every axis-parallel rectangle.
The strong maximal inequality then passes to the global class `L(log⁺L)^{d-1}` by truncating in
height and approximating in `L¹`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology

/-- The endpoint growth vanishes at zero. -/
theorem strongMaximalGrowth_zero (d : ℕ) : strongMaximalGrowth d 0 = 0 := by
  simp [strongMaximalGrowth, Real.log_zero]

/-- The endpoint growth is monotone on the nonnegative reals. -/
theorem strongMaximalGrowth_mono {d : ℕ} {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    strongMaximalGrowth d u ≤ strongMaximalGrowth d v := by
  have hv : 0 ≤ v := le_trans hu huv
  have hlog := logPlus_mono hu huv
  have hbase : 0 ≤ 1 + max 0 (Real.log u) := by
    linarith [le_max_left (0 : ℝ) (Real.log u)]
  unfold strongMaximalGrowth
  calc
    u * (1 + max 0 (Real.log u)) ^ (d - 1) ≤
        v * (1 + max 0 (Real.log u)) ^ (d - 1) :=
      mul_le_mul_of_nonneg_right huv (pow_nonneg hbase _)
    _ ≤ v * (1 + max 0 (Real.log v)) ^ (d - 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase (by linarith) _) hv

/-- A bound on the argument gives a linear bound of the same growth order. -/
theorem strongMaximalGrowth_le_mul_of_le {d : ℕ} {u M : ℝ} (hu : 0 ≤ u) (huM : u ≤ M) :
    strongMaximalGrowth d u ≤ (1 + max 0 (Real.log M)) ^ (d - 1) * u := by
  have hlog := logPlus_mono hu huM
  have hbase : 0 ≤ 1 + max 0 (Real.log u) := by
    linarith [le_max_left (0 : ℝ) (Real.log u)]
  unfold strongMaximalGrowth
  calc
    u * (1 + max 0 (Real.log u)) ^ (d - 1) ≤
        u * (1 + max 0 (Real.log M)) ^ (d - 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase (by linarith) _) hu
    _ = (1 + max 0 (Real.log M)) ^ (d - 1) * u := by ring

/-- Scaling the argument of the endpoint growth preserves the order. -/
theorem strongMaximalGrowth_mul_le {d : ℕ} {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) :
    strongMaximalGrowth d (c * u) ≤
      c * (1 + |Real.log c|) ^ (d - 1) * strongMaximalGrowth d u := by
  by_cases hu0 : u = 0
  · simp [hu0, strongMaximalGrowth_zero]
  · have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
    have hlogle : max 0 (Real.log (c * u)) ≤ |Real.log c| + max 0 (Real.log u) := by
      rw [Real.log_mul hc.ne' hu'.ne']
      exact max_le (add_nonneg (abs_nonneg _) (le_max_left _ _))
        (add_le_add (le_abs_self _) (le_max_right (0 : ℝ) (Real.log u)))
    have hprod : 1 + max 0 (Real.log (c * u)) ≤
        (1 + |Real.log c|) * (1 + max 0 (Real.log u)) := by
      have hA : 0 ≤ |Real.log c| := abs_nonneg _
      have hB : 0 ≤ max 0 (Real.log u) := le_max_left _ _
      calc
        1 + max 0 (Real.log (c * u)) ≤ 1 + |Real.log c| + max 0 (Real.log u) := by
          linarith [hlogle]
        _ ≤ 1 + |Real.log c| + max 0 (Real.log u) + |Real.log c| * max 0 (Real.log u) := by
          linarith [mul_nonneg hA hB]
        _ = (1 + |Real.log c|) * (1 + max 0 (Real.log u)) := by ring
    have hbase : 0 ≤ 1 + max 0 (Real.log (c * u)) := by
      linarith [le_max_left (0 : ℝ) (Real.log (c * u))]
    have hcu : 0 ≤ c * u := mul_nonneg hc.le hu
    unfold strongMaximalGrowth
    calc
      c * u * (1 + max 0 (Real.log (c * u))) ^ (d - 1) ≤
          c * u * ((1 + |Real.log c|) * (1 + max 0 (Real.log u))) ^ (d - 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase hprod _) hcu
      _ = c * (1 + |Real.log c|) ^ (d - 1) *
          (u * (1 + max 0 (Real.log u)) ^ (d - 1)) := by
        rw [mul_pow]
        ring

/-- Dividing by a positive constant preserves the growth order. -/
theorem strongMaximalGrowth_div_const_le {d : ℕ} {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    strongMaximalGrowth d (u / a) ≤
      a⁻¹ * (1 + |Real.log a|) ^ (d - 1) * strongMaximalGrowth d u := by
  have h := strongMaximalGrowth_mul_le (d := d) (inv_pos.2 ha) hu
  have hlog : |Real.log a⁻¹| = |Real.log a| := by rw [Real.log_inv, abs_neg]
  have hc : a⁻¹ * u = u / a := by rw [div_eq_mul_inv, mul_comm]
  rw [hlog, hc] at h
  exact h

/-- The coefficient comparing a maximal height `a` with the unscaled growth. -/
def strongMaximalScale (d : ℕ) (C a : ℝ) : ℝ :=
  C * a⁻¹ * (1 + |Real.log a|) ^ (d - 1)

/-- The scale coefficient is positive for a positive height and a positive constant. -/
theorem strongMaximalScale_pos {d : ℕ} {C a : ℝ} (hC : 0 < C) (ha : 0 < a) :
    0 < strongMaximalScale d C a := by
  unfold strongMaximalScale
  positivity

/-- Two points of a rectangle are closer than its total width in the supremum metric. -/
theorem OpenRectangle.dist_lt_totalWidth {d : ℕ} (hd : 0 < d) (R : OpenRectangle d)
    {x y : Fin d → ℝ} (hx : x ∈ R.carrier) (hy : y ∈ R.carrier) :
    dist y x < R.totalWidth := by
  have hside : ∀ j, |y j - x j| < R.upper j - R.lower j := by
    intro j
    rcases hx j with ⟨hxlo, hxhi⟩
    rcases hy j with ⟨hylo, hyhi⟩
    rw [abs_lt]
    constructor <;> linarith
  have hle : ∀ j, R.upper j - R.lower j ≤ R.totalWidth := by
    intro j
    unfold OpenRectangle.totalWidth
    exact Finset.single_le_sum
      (fun i _ ↦ sub_nonneg.2 (R.lower_lt_upper i).le) (Finset.mem_univ j)
  have hpos : 0 < R.totalWidth := by
    unfold OpenRectangle.totalWidth
    exact Finset.sum_pos (fun j _ ↦ sub_pos.2 (R.lower_lt_upper j))
      ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  rw [dist_pi_lt_iff hpos]
  intro j
  rw [Real.dist_eq]
  exact (hside j).trans_le (hle j)

/-- The absolute value of a signed average is at most the average of the absolute value. -/
theorem OpenRectangle.abs_average_le {d : ℕ} (R : OpenRectangle d)
    (g : (Fin d → ℝ) → ℝ) :
    |R.average g| ≤ R.average (fun y ↦ |g y|) := by
  unfold OpenRectangle.average
  have hv : 0 ≤ (volume R.carrier).toReal⁻¹ := inv_nonneg.2 ENNReal.toReal_nonneg
  rw [abs_mul, abs_of_nonneg hv]
  exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hv

/-- A uniform oscillation bound passes to the average. -/
theorem OpenRectangle.abs_average_sub_le {d : ℕ} (R : OpenRectangle d)
    {g : (Fin d → ℝ) → ℝ} {c η : ℝ} (hg : IntegrableOn g R.carrier)
    (hbound : ∀ y ∈ R.carrier, |g y - c| ≤ η) : |R.average g - c| ≤ η := by
  have hvpos : 0 < volume.real R.carrier :=
    ENNReal.toReal_pos R.volume_carrier_pos.ne' R.volume_carrier_lt_top.ne
  have hc : IntegrableOn (fun _ : Fin d → ℝ ↦ c) R.carrier :=
    integrableOn_const R.volume_carrier_lt_top.ne
  have hsub : IntegrableOn (fun y ↦ g y - c) R.carrier := hg.sub hc
  have habs : IntegrableOn (fun y ↦ |g y - c|) R.carrier := hsub.abs
  have hconst : IntegrableOn (fun _ : Fin d → ℝ ↦ η) R.carrier :=
    integrableOn_const R.volume_carrier_lt_top.ne
  have hint : ∫ y in R.carrier, (g y - c) =
      (∫ y in R.carrier, g y) - volume.real R.carrier * c := by
    rw [integral_sub hg hc, setIntegral_const, smul_eq_mul]
  have hmono : ∫ y in R.carrier, |g y - c| ≤ ∫ y in R.carrier, η :=
    setIntegral_mono_on habs hconst R.measurableSet_carrier hbound
  unfold OpenRectangle.average
  rw [← measureReal_def]
  have hrew : ((volume.real R.carrier)⁻¹ * ∫ y in R.carrier, g y) - c =
      (volume.real R.carrier)⁻¹ * ∫ y in R.carrier, (g y - c) := by
    rw [hint, mul_sub, ← mul_assoc, inv_mul_cancel₀ hvpos.ne', one_mul]
  calc
    |((volume.real R.carrier)⁻¹ * ∫ y in R.carrier, g y) - c|
        = |(volume.real R.carrier)⁻¹ * ∫ y in R.carrier, (g y - c)| := by rw [hrew]
    _ = (volume.real R.carrier)⁻¹ * |∫ y in R.carrier, (g y - c)| := by
        rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hvpos.le)]
    _ ≤ (volume.real R.carrier)⁻¹ * ∫ y in R.carrier, |g y - c| :=
        mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (inv_nonneg.2 hvpos.le)
    _ ≤ (volume.real R.carrier)⁻¹ * ∫ y in R.carrier, η :=
        mul_le_mul_of_nonneg_left hmono (inv_nonneg.2 hvpos.le)
    _ = (volume.real R.carrier)⁻¹ * (volume.real R.carrier * η) := by
        rw [setIntegral_const, smul_eq_mul]
    _ = η := by rw [← mul_assoc, inv_mul_cancel₀ hvpos.ne', one_mul]

/-- An integrable absolute average is a strong-maximal average. -/
theorem OpenRectangle.ofReal_average_abs_le_strongMaximal {d : ℕ} (R : OpenRectangle d)
    {g : (Fin d → ℝ) → ℝ} (hg : IntegrableOn (fun y ↦ |g y|) R.carrier)
    {x : Fin d → ℝ} (hx : x ∈ R.carrier) :
    ENNReal.ofReal (R.average (fun y ↦ |g y|)) ≤ strongMaximalFunction g x := by
  have hv : 0 < (volume R.carrier).toReal :=
    ENNReal.toReal_pos R.volume_carrier_pos.ne' R.volume_carrier_lt_top.ne
  have hnn : 0 ≤ᵐ[volume.restrict R.carrier] fun y ↦ |g y| :=
    ae_of_all _ fun _ ↦ abs_nonneg _
  have hI := ofReal_integral_eq_lintegral_ofReal hg hnn
  have hinv : 0 ≤ (volume R.carrier).toReal⁻¹ := inv_nonneg.2 ENNReal.toReal_nonneg
  unfold OpenRectangle.average
  rw [ENNReal.ofReal_mul hinv, ENNReal.ofReal_inv_of_pos hv,
    ENNReal.ofReal_toReal R.volume_carrier_lt_top.ne, hI, mul_comm, ← div_eq_mul_inv]
  exact (le_iSup (fun h : x ∈ R.carrier ↦
      (∫⁻ y in R.carrier, ENNReal.ofReal |g y|) / volume R.carrier) hx).trans
    (le_iSup (fun S : OpenRectangle d ↦ ⨆ h : x ∈ S.carrier,
      (∫⁻ y in S.carrier, ENNReal.ofReal |g y|) / volume S.carrier) R)

/-- Truncation of a real number to the interval `[-N, N]`. -/
def heightClamp (N t : ℝ) : ℝ := max (-N) (min t N)

/-- Truncation to a symmetric interval is 1-Lipschitz. -/
theorem heightClamp_lipschitz (N : ℝ) : LipschitzWith 1 (heightClamp N) := by
  unfold heightClamp
  exact (LipschitzWith.id.min_const N).const_max (-N)

/-- Truncation does not increase distances. -/
theorem abs_heightClamp_sub_le (N s t : ℝ) :
    |heightClamp N s - heightClamp N t| ≤ |s - t| := by
  have h := (heightClamp_lipschitz N).dist_le_mul s t
  simpa [Real.dist_eq, NNReal.coe_one, one_mul] using h

/-- Truncation fixes zero when the height is nonnegative. -/
theorem heightClamp_zero {N : ℝ} (hN : 0 ≤ N) : heightClamp N 0 = 0 := by
  unfold heightClamp
  rw [min_eq_left hN, max_eq_right (neg_nonpos.2 hN)]

/-- Truncation fixes every point of the interval `[-N, N]`. -/
theorem heightClamp_eq_self {N t : ℝ} (ht : |t| ≤ N) : heightClamp N t = t := by
  rw [abs_le] at ht
  unfold heightClamp
  rw [min_eq_left ht.2, max_eq_right ht.1]

/-- Truncation does not increase the absolute value. -/
theorem abs_heightClamp_le {N t : ℝ} (hN : 0 ≤ N) : |heightClamp N t| ≤ |t| := by
  simpa [heightClamp_zero hN, sub_zero] using abs_heightClamp_sub_le N t 0

/-- A truncated value stays inside the truncation window. -/
theorem abs_heightClamp_le_height {N t : ℝ} (hN : 0 ≤ N) : |heightClamp N t| ≤ N := by
  unfold heightClamp
  exact abs_le.2 ⟨le_max_left _ _, max_le (neg_le_self hN) (min_le_right _ _)⟩

/-- The distance from a real number to its truncation is at most its absolute value. -/
theorem abs_sub_heightClamp_le {N t : ℝ} (hN : 0 ≤ N) : |t - heightClamp N t| ≤ |t| := by
  by_cases hhi : N < t
  · have hclamp : heightClamp N t = N := by
      unfold heightClamp
      rw [min_eq_right hhi.le, max_eq_right (neg_le_self hN)]
    have ht : 0 ≤ t := le_trans hN hhi.le
    rw [hclamp, abs_of_nonneg (sub_nonneg.2 hhi.le), abs_of_nonneg ht]
    linarith
  · by_cases hlo : t < -N
    · have hclamp : heightClamp N t = -N := by
        unfold heightClamp
        have htN : t ≤ N := le_trans hlo.le (neg_le_self hN)
        rw [min_eq_left htN, max_eq_left hlo.le]
      have hsub : t + N < 0 := by linarith
      have ht : t < 0 := lt_of_lt_of_le hlo (neg_nonpos.2 hN)
      rw [hclamp, sub_neg_eq_add, abs_of_neg hsub, abs_of_neg ht]
      linarith
    · have ht : |t| ≤ N := abs_le.mpr ⟨not_lt.mp hlo, not_lt.mp hhi⟩
      simp [heightClamp_eq_self ht, abs_nonneg]

/-- Truncation is continuous. -/
theorem continuous_heightClamp (N : ℝ) : Continuous (heightClamp N) :=
  (heightClamp_lipschitz N).continuous

/-- Truncation preserves compact support. -/
theorem HasCompactSupport.heightClamp {X : Type*} [TopologicalSpace X] {N : ℝ} (hN : 0 ≤ N)
    {f : X → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun x ↦ heightClamp N (f x)) :=
  hf.comp_left (heightClamp_zero hN)

/-- Continuous compactly supported functions are differentiated at every point. -/
theorem rectanglesDifferentiateAt_of_hasCompactSupport {d : ℕ} (hd : 0 < d)
    {h : (Fin d → ℝ) → ℝ} (hh : Continuous h) (hs : HasCompactSupport h) (x : Fin d → ℝ) :
    RectanglesDifferentiateAt h x := by
  intro ε hε
  have hx : ContinuousAt h x := hh.continuousAt
  rw [continuousAt_iff] at hx
  obtain ⟨δ, hδ, hdist⟩ := hx (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun R hxR hwidth ↦ ?_⟩
  have hint : IntegrableOn h R.carrier :=
    (hh.integrable_of_hasCompactSupport hs).integrableOn
  have hclose : ∀ y ∈ R.carrier, |h y - h x| ≤ ε / 2 := by
    intro y hy
    have hdy : dist (h y) (h x) < ε / 2 :=
      hdist ((R.dist_lt_totalWidth hd hxR hy).trans hwidth)
    rw [Real.dist_eq] at hdy
    exact hdy.le
  exact (R.abs_average_sub_le hint hclose).trans_lt (half_lt_self hε)

/-- Global integrability of the endpoint growth implies ordinary integrability. -/
theorem integrable_of_strongMaximalGrowth {d : ℕ} {f : (Fin d → ℝ) → ℝ} (hm : Measurable f)
    (hG : Integrable (fun x ↦ strongMaximalGrowth d |f x|)) : Integrable f := by
  refine hG.mono' hm.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  exact strongMaximalGrowth_ge_self (abs_nonneg _)

/-- Raising the truncation height sends the endpoint integral of the error to zero. -/
theorem tendsto_integral_growth_heightClamp {d : ℕ} {f : (Fin d → ℝ) → ℝ} (hm : Measurable f)
    (hG : Integrable (fun x ↦ strongMaximalGrowth d |f x|)) :
    Tendsto (fun n : ℕ ↦ ∫ x, strongMaximalGrowth d |f x - heightClamp (n : ℝ) (f x)|)
      atTop (𝓝 0) := by
  let F : ℕ → (Fin d → ℝ) → ℝ :=
    fun n x ↦ strongMaximalGrowth d |f x - heightClamp (n : ℝ) (f x)|
  have hmeas : ∀ n, AEStronglyMeasurable (F n) volume := by
    intro n
    have hmF : Measurable fun x ↦ |f x - heightClamp (n : ℝ) (f x)| := by
      simpa [Real.norm_eq_abs] using
        (hm.sub ((continuous_heightClamp (n : ℝ)).measurable.comp hm)).norm
    exact ((measurable_strongMaximalGrowth d).comp hmF).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ x ∂volume, ‖F n x‖ ≤ strongMaximalGrowth d |f x| := by
    intro n
    refine ae_of_all _ fun x ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (strongMaximalGrowth_nonneg (abs_nonneg _))]
    exact strongMaximalGrowth_mono (abs_nonneg _)
      (abs_sub_heightClamp_le (Nat.cast_nonneg n))
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun n ↦ F n x) atTop (𝓝 (0 : ℝ)) := by
    refine ae_of_all _ fun x ↦ ?_
    obtain ⟨N, hN⟩ := exists_nat_gt |f x|
    refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn ↦ ?_
    have hle : |f x| ≤ (n : ℝ) := le_trans hN.le (Nat.cast_le.mpr hn)
    simp [F, heightClamp_eq_self hle, strongMaximalGrowth_zero]
  have hconv := tendsto_integral_of_dominated_convergence
    (fun x ↦ strongMaximalGrowth d |f x|) hmeas hG hbound hlim
  simpa [F, integral_zero] using hconv

/-- A measurable function bounded by `N` can be replaced by a continuous compactly supported
function with a small endpoint integral. -/
theorem exists_continuous_growth_small {d : ℕ} {N : ℝ} (hN : 0 ≤ N)
    {f : (Fin d → ℝ) → ℝ} (hm : Measurable f) (hf : Integrable f)
    (hbound : ∀ x, |f x| ≤ N) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h : (Fin d → ℝ) → ℝ, Continuous h ∧ HasCompactSupport h ∧
      Integrable (fun x ↦ strongMaximalGrowth d |f x - h x|) ∧
      (∫ x, strongMaximalGrowth d |f x - h x|) ≤ δ := by
  set growthCoeff : ℝ := (1 + max 0 (Real.log (2 * N))) ^ (d - 1)
  have hcoeff : 0 < growthCoeff := by
    have hone : (0 : ℝ) < 1 + max 0 (Real.log (2 * N)) := by
      linarith [le_max_left (0 : ℝ) (Real.log (2 * N))]
    exact pow_pos hone _
  obtain ⟨g, hgsupp, hgL1, hgcont, hgint⟩ :=
    hf.exists_hasCompactSupport_integral_sub_le (div_pos hδ hcoeff)
  let h : (Fin d → ℝ) → ℝ := fun x ↦ heightClamp N (g x)
  have hh : Continuous h := (continuous_heightClamp N).comp hgcont
  have hhs : HasCompactSupport h := HasCompactSupport.heightClamp hN hgsupp
  have hlip : ∀ x, |f x - h x| ≤ |f x - g x| := by
    intro x
    have hfix : heightClamp N (f x) = f x := heightClamp_eq_self (hbound x)
    simpa [h, hfix] using abs_heightClamp_sub_le N (f x) (g x)
  have htwo : ∀ x, |f x - h x| ≤ 2 * N := by
    intro x
    have hfN : |f x| ≤ N := hbound x
    have hhN : |h x| ≤ N := abs_heightClamp_le_height hN
    have hsum : |f x - h x| ≤ |f x| + |h x| := by
      simpa [Real.norm_eq_abs] using norm_sub_le (f x) (h x)
    linarith
  have hgrow : ∀ x, strongMaximalGrowth d |f x - h x| ≤ growthCoeff * |f x - g x| := by
    intro x
    calc
      strongMaximalGrowth d |f x - h x| ≤ growthCoeff * |f x - h x| :=
        strongMaximalGrowth_le_mul_of_le (abs_nonneg _) (htwo x)
      _ ≤ growthCoeff * |f x - g x| :=
        mul_le_mul_of_nonneg_left (hlip x) hcoeff.le
  have hdom : Integrable (fun x ↦ growthCoeff * |f x - g x|) :=
    (hf.sub hgint).abs.const_mul growthCoeff
  have hint : ∫ x, strongMaximalGrowth d |f x - h x| ≤
      ∫ x, growthCoeff * |f x - g x| :=
    integral_mono_of_nonneg
      (ae_of_all _ fun _ ↦ strongMaximalGrowth_nonneg (abs_nonneg _)) hdom
      (ae_of_all _ hgrow)
  have hL1 : ∫ x, |f x - g x| ≤ δ / growthCoeff := by
    simpa [Real.norm_eq_abs] using hgL1
  have hsmall : ∫ x, strongMaximalGrowth d |f x - h x| ≤ δ := by
    calc
      ∫ x, strongMaximalGrowth d |f x - h x| ≤
          growthCoeff * ∫ x, |f x - g x| := by
        rw [integral_const_mul] at hint
        exact hint
      _ ≤ growthCoeff * (δ / growthCoeff) :=
        mul_le_mul_of_nonneg_left hL1 hcoeff.le
      _ = δ := by field_simp [hcoeff.ne']
  have hm_diff : Measurable fun x ↦ |f x - h x| := by
    simpa [h, Real.norm_eq_abs] using (hm.sub hh.measurable).norm
  have hGi : Integrable (fun x ↦ strongMaximalGrowth d |f x - h x|) :=
    hdom.mono' ((measurable_strongMaximalGrowth d).comp hm_diff).aestronglyMeasurable
      (ae_of_all _ fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (strongMaximalGrowth_nonneg (abs_nonneg _))]
        exact hgrow x)
  exact ⟨h, hh, hhs, hGi, hsmall⟩

/-- The distribution of the strong maximal function is an integral of the same-order growth. -/
theorem strongMaximal_distribution_le {d : ℕ} {g : (Fin d → ℝ) → ℝ}
    (hG : Integrable (fun x ↦ strongMaximalGrowth d |g x|)) {a C : ℝ} (ha : 0 < a)
    (hC : 0 < C)
    (hmax : volume {x | ENNReal.ofReal a < strongMaximalFunction g x} ≤
      ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth d (|g x| / a))) :
    volume {x | ENNReal.ofReal a < strongMaximalFunction g x} ≤
      ENNReal.ofReal (strongMaximalScale d C a * ∫ x, strongMaximalGrowth d |g x|) := by
  set κ : ℝ := a⁻¹ * (1 + |Real.log a|) ^ (d - 1)
  have hκ : 0 ≤ κ := by
    have hpos : 0 < κ := by
      unfold κ
      positivity
    exact hpos.le
  set I : ℝ := ∫ x, strongMaximalGrowth d |g x|
  have hpt : ∀ x, strongMaximalGrowth d (|g x| / a) ≤
      κ * strongMaximalGrowth d |g x| := by
    intro x
    simpa [κ] using strongMaximalGrowth_div_const_le ha (abs_nonneg (g x))
  have hconst : ∫⁻ x, ENNReal.ofReal (κ * strongMaximalGrowth d |g x|) =
      ENNReal.ofReal κ * ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth d |g x|) := by
    rw [lintegral_congr fun x ↦ ENNReal.ofReal_mul hκ,
      lintegral_const_mul' (ENNReal.ofReal κ) _ ENNReal.ofReal_ne_top]
  have hboch : ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth d |g x|) = ENNReal.ofReal I :=
    (ofReal_integral_eq_lintegral_ofReal hG
      (ae_of_all _ fun _ ↦ strongMaximalGrowth_nonneg (abs_nonneg _))).symm
  have hle : ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth d (|g x| / a)) ≤
      ENNReal.ofReal κ * ENNReal.ofReal I := by
    refine (lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (hpt x)).trans ?_
    rw [hconst, hboch]
  have hbound : ENNReal.ofReal C *
      ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth d (|g x| / a)) ≤
      ENNReal.ofReal C * (ENNReal.ofReal κ * ENNReal.ofReal I) :=
    mul_le_mul' le_rfl hle
  have hrew : ENNReal.ofReal C * (ENNReal.ofReal κ * ENNReal.ofReal I) =
      ENNReal.ofReal (C * κ * I) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul hC.le, ← ENNReal.ofReal_mul (mul_nonneg hC.le hκ)]
  have hscale : C * κ = strongMaximalScale d C a := by
    unfold strongMaximalScale κ
    ring
  refine hmax.trans ?_
  exact hbound.trans_eq (by rw [hrew, hscale])

/-- Markov's inequality for the endpoint growth, which dominates the absolute value. -/
theorem volume_growth_ge_le {d : ℕ} {g : (Fin d → ℝ) → ℝ} (hg : Measurable g)
    (hG : Integrable (fun x ↦ strongMaximalGrowth d |g x|)) {a : ℝ} (ha : 0 < a) :
    volume {x | a ≤ |g x|} ≤
      ENNReal.ofReal ((∫ x, strongMaximalGrowth d |g x|) / a) := by
  have hsub : {x | a ≤ |g x|} ⊆
      {x | ENNReal.ofReal a ≤ ENNReal.ofReal (strongMaximalGrowth d |g x|)} := by
    intro x hx
    exact ENNReal.ofReal_le_ofReal (le_trans hx (strongMaximalGrowth_ge_self (abs_nonneg _)))
  have hf : AEMeasurable (fun x ↦ ENNReal.ofReal (strongMaximalGrowth d |g x|)) volume :=
    ((measurable_strongMaximalGrowth d).comp hg.norm).ennreal_ofReal.aemeasurable
  have hmark := meas_ge_le_lintegral_div hf (ENNReal.ofReal_pos.2 ha).ne' ENNReal.ofReal_ne_top
  have hI : ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth d |g x|) =
      ENNReal.ofReal (∫ x, strongMaximalGrowth d |g x|) :=
    (ofReal_integral_eq_lintegral_ofReal hG
      (ae_of_all _ fun _ ↦ strongMaximalGrowth_nonneg (abs_nonneg _))).symm
  refine (measure_mono hsub).trans ?_
  exact hmark.trans (by rw [hI, ENNReal.ofReal_div_of_pos ha])

/-- Height truncation followed by a continuous compactly supported correction splits off two
small endpoint errors. -/
theorem exists_split_growth_small {d : ℕ} {f : (Fin d → ℝ) → ℝ} (hm : Measurable f)
    (hG : Integrable (fun x ↦ strongMaximalGrowth d |f x|)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g1 g2 h : (Fin d → ℝ) → ℝ,
      Measurable g1 ∧ Measurable g2 ∧ Continuous h ∧ HasCompactSupport h ∧
      Integrable g1 ∧ Integrable g2 ∧
      Integrable (fun x ↦ strongMaximalGrowth d |g1 x|) ∧
      Integrable (fun x ↦ strongMaximalGrowth d |g2 x|) ∧
      (∫ x, strongMaximalGrowth d |g1 x|) ≤ δ ∧
      (∫ x, strongMaximalGrowth d |g2 x|) ≤ δ ∧
      ∀ x, f x = g1 x + g2 x + h x := by
  have htend := tendsto_integral_growth_heightClamp hm hG
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N, hN⟩ := htend δ hδ
  have hdist := hN N le_rfl
  have hnn : 0 ≤ ∫ x, strongMaximalGrowth d |f x - heightClamp (N : ℝ) (f x)| :=
    integral_nonneg fun x ↦ strongMaximalGrowth_nonneg (abs_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hdist
  let fN : (Fin d → ℝ) → ℝ := fun x ↦ heightClamp (N : ℝ) (f x)
  have hmN : Measurable fN := (continuous_heightClamp (N : ℝ)).measurable.comp hm
  have hfN_int : Integrable fN := by
    refine hG.mono' hmN.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact le_trans (abs_heightClamp_le (Nat.cast_nonneg N))
      (strongMaximalGrowth_ge_self (abs_nonneg _))
  have hbound : ∀ x, |fN x| ≤ (N : ℝ) := fun _ ↦ abs_heightClamp_le_height (Nat.cast_nonneg N)
  obtain ⟨h, hh, hhs, hg2i, hg2int⟩ :=
    exists_continuous_growth_small (Nat.cast_nonneg N) hmN hfN_int hbound hδ
  let g1 : (Fin d → ℝ) → ℝ := fun x ↦ f x - fN x
  let g2 : (Fin d → ℝ) → ℝ := fun x ↦ fN x - h x
  have hg1m : Measurable g1 := hm.sub hmN
  have hg2m : Measurable g2 := hmN.sub hh.measurable
  have hg1_int : Integrable g1 := (integrable_of_strongMaximalGrowth hm hG).sub hfN_int
  have hg2_int : Integrable g2 := hfN_int.sub (hh.integrable_of_hasCompactSupport hhs)
  have hg1i : Integrable (fun x ↦ strongMaximalGrowth d |g1 x|) := by
    have hmabs : Measurable fun x ↦ |g1 x| := by
      simpa [g1, Real.norm_eq_abs] using hg1m.norm
    refine hG.mono' ((measurable_strongMaximalGrowth d).comp hmabs).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (strongMaximalGrowth_nonneg (abs_nonneg _))]
    exact strongMaximalGrowth_mono (abs_nonneg _)
      (by simpa [g1, fN] using
        abs_sub_heightClamp_le (t := f x) (Nat.cast_nonneg N))
  have hg1le : ∫ x, strongMaximalGrowth d |g1 x| ≤ δ := by
    simpa [g1, fN] using hdist.le
  have hsum : ∀ x, f x = g1 x + g2 x + h x := by
    intro x
    simp [g1, g2, fN]
  exact ⟨g1, g2, h, hg1m, hg2m, hh, hhs, hg1_int, hg2_int, hg1i, hg2i, hg1le, hg2int, hsum⟩

/-- Outside a small set, a split into two small errors and one continuous function has small
rectangular oscillation. -/
theorem exists_rectangle_width {d : ℕ} (hd : 0 < d) {g1 g2 h : (Fin d → ℝ) → ℝ}
    {x : Fin d → ℝ} {ε : ℝ} (hg1 : Integrable g1) (hg2 : Integrable g2) (hh : Continuous h)
    (hs : HasCompactSupport h)
    (hM1 : strongMaximalFunction g1 x ≤ ENNReal.ofReal (ε / 5))
    (hM2 : strongMaximalFunction g2 x ≤ ENNReal.ofReal (ε / 5))
    (hp1 : |g1 x| < ε / 5) (hp2 : |g2 x| < ε / 5) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : OpenRectangle d, x ∈ R.carrier → R.totalWidth < δ →
      |R.average (fun y ↦ g1 y + g2 y + h y) - (g1 x + g2 x + h x)| < ε := by
  set a : ℝ := ε / 5
  have ha : 0 < a := by
    unfold a
    positivity
  obtain ⟨δ, hδ, hδh⟩ := rectanglesDifferentiateAt_of_hasCompactSupport hd hh hs x a ha
  refine ⟨δ, hδ, fun R hxR hwidth ↦ ?_⟩
  have hhint : Integrable h := hh.integrable_of_hasCompactSupport hs
  have hsumavg : R.average (fun y ↦ g1 y + g2 y + h y) =
      R.average g1 + R.average g2 + R.average h := by
    unfold OpenRectangle.average
    have hadd1 : ∫ y in R.carrier, (g1 y + g2 y + h y) =
        (∫ y in R.carrier, (g1 y + g2 y)) + ∫ y in R.carrier, h y :=
      integral_add ((hg1.add hg2).integrableOn) hhint.integrableOn
    have hadd2 : ∫ y in R.carrier, (g1 y + g2 y) =
        (∫ y in R.carrier, g1 y) + ∫ y in R.carrier, g2 y :=
      integral_add hg1.integrableOn hg2.integrableOn
    rw [hadd1, hadd2, mul_add, mul_add]
  have hpiece : |R.average g1 - g1 x| < 2 * a ∧ |R.average g2 - g2 x| < 2 * a := by
    constructor
    · have hint1 : IntegrableOn (fun y ↦ |g1 y|) R.carrier := hg1.abs.integrableOn
      have hreal : R.average (fun y ↦ |g1 y|) ≤ a :=
        (ENNReal.ofReal_le_ofReal_iff ha.le).1
          ((R.ofReal_average_abs_le_strongMaximal hint1 hxR).trans hM1)
      have havg : |R.average g1| ≤ a := (R.abs_average_le g1).trans hreal
      have hstep : |R.average g1 - g1 x| ≤ |R.average g1| + |g1 x| := by
        simpa [Real.norm_eq_abs] using norm_sub_le (R.average g1) (g1 x)
      linarith
    · have hint2 : IntegrableOn (fun y ↦ |g2 y|) R.carrier := hg2.abs.integrableOn
      have hreal : R.average (fun y ↦ |g2 y|) ≤ a :=
        (ENNReal.ofReal_le_ofReal_iff ha.le).1
          ((R.ofReal_average_abs_le_strongMaximal hint2 hxR).trans hM2)
      have havg : |R.average g2| ≤ a := (R.abs_average_le g2).trans hreal
      have hstep : |R.average g2 - g2 x| ≤ |R.average g2| + |g2 x| := by
        simpa [Real.norm_eq_abs] using norm_sub_le (R.average g2) (g2 x)
      linarith
  have hhsmall : |R.average h - h x| < a := hδh R hxR hwidth
  have htri : |R.average (fun y ↦ g1 y + g2 y + h y) - (g1 x + g2 x + h x)| ≤
      |R.average g1 - g1 x| + |R.average g2 - g2 x| + |R.average h - h x| := by
    rw [hsumavg]
    have hrewrite : (R.average g1 + R.average g2 + R.average h) - (g1 x + g2 x + h x) =
        (R.average g1 - g1 x) + ((R.average g2 - g2 x) + (R.average h - h x)) := by ring
    rw [hrewrite]
    have hleft := norm_add_le (R.average g1 - g1 x)
      ((R.average g2 - g2 x) + (R.average h - h x))
    have hright := norm_add_le (R.average g2 - g2 x) (R.average h - h x)
    simp only [Real.norm_eq_abs] at hleft hright
    calc
      _ ≤ |R.average g1 - g1 x| + |(R.average g2 - g2 x) + (R.average h - h x)| := hleft
      _ ≤ |R.average g1 - g1 x| + (|R.average g2 - g2 x| + |R.average h - h x|) :=
        add_le_add le_rfl hright
      _ = |R.average g1 - g1 x| + |R.average g2 - g2 x| + |R.average h - h x| := by
        rw [← add_assoc]
  have haε : 5 * a = ε := by
    unfold a
    field_simp
  linarith

/-- Points where every scale of rectangle misses the value by a fixed amount. -/
def rectangleOscillation {d : ℕ} (f : (Fin d → ℝ) → ℝ) (ε : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ δ : ℝ, 0 < δ → ∃ R : OpenRectangle d, x ∈ R.carrier ∧ R.totalWidth < δ ∧
    ε ≤ |R.average f - f x|}

/-- The strong maximal inequality makes the rectangular oscillation of a globally integrable
endpoint function a null set. -/
theorem volume_rectangleOscillation_eq_zero {d : ℕ} (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ}
    (hm : Measurable f) (hG : Integrable (fun x ↦ strongMaximalGrowth d |f x|)) {ε : ℝ}
    (hε : 0 < ε) : volume (rectangleOscillation f ε) = 0 := by
  refine eq_zero_of_forall_le_ofReal fun η hη ↦ ?_
  obtain ⟨C, hC, hmax⟩ := strongMaximal_orlicz hd
  set a : ℝ := ε / 5
  have ha : 0 < a := by
    unfold a
    positivity
  set scale : ℝ := strongMaximalScale d C a
  have hscale : 0 < scale := strongMaximalScale_pos hC ha
  set δ : ℝ := min ((η / 4) / scale) (a * (η / 4))
  have hδ : 0 < δ := lt_min (div_pos (div_pos hη (by norm_num)) hscale)
    (mul_pos ha (div_pos hη (by norm_num)))
  obtain ⟨g1, g2, h, hg1m, hg2m, hh, hhs, hg1, hg2, hg1G, hg2G, hg1int, hg2int, hsum⟩ :=
    exists_split_growth_small hm hG hδ
  have hdist1 := strongMaximal_distribution_le hg1G ha hC (hmax g1 hg1m a ha)
  have hdist2 := strongMaximal_distribution_le hg2G ha hC (hmax g2 hg2m a ha)
  have hlevel1 := volume_growth_ge_le hg1m hg1G ha
  have hlevel2 := volume_growth_ge_le hg2m hg2G ha
  have hscale_le : scale * ∫ x, strongMaximalGrowth d |g1 x| ≤ η / 4 := by
    have hI : ∫ x, strongMaximalGrowth d |g1 x| ≤ (η / 4) / scale :=
      le_trans hg1int (min_le_left _ _)
    calc
      scale * ∫ x, strongMaximalGrowth d |g1 x| ≤ scale * ((η / 4) / scale) :=
        mul_le_mul_of_nonneg_left hI hscale.le
      _ = η / 4 := by field_simp [hscale.ne']
  have hscale_le2 : scale * ∫ x, strongMaximalGrowth d |g2 x| ≤ η / 4 := by
    have hI : ∫ x, strongMaximalGrowth d |g2 x| ≤ (η / 4) / scale :=
      le_trans hg2int (min_le_left _ _)
    calc
      scale * ∫ x, strongMaximalGrowth d |g2 x| ≤ scale * ((η / 4) / scale) :=
        mul_le_mul_of_nonneg_left hI hscale.le
      _ = η / 4 := by field_simp [hscale.ne']
  have hdiv1 : (∫ x, strongMaximalGrowth d |g1 x|) / a ≤ η / 4 := by
    rw [div_le_iff₀ ha]
    exact (le_trans hg1int (min_le_right _ _)).trans_eq (by ring)
  have hdiv2 : (∫ x, strongMaximalGrowth d |g2 x|) / a ≤ η / 4 := by
    rw [div_le_iff₀ ha]
    exact (le_trans hg2int (min_le_right _ _)).trans_eq (by ring)
  set E1 : Set (Fin d → ℝ) := {x | ENNReal.ofReal a < strongMaximalFunction g1 x}
  set E2 : Set (Fin d → ℝ) := {x | ENNReal.ofReal a < strongMaximalFunction g2 x}
  set F1 : Set (Fin d → ℝ) := {x | a ≤ |g1 x|}
  set F2 : Set (Fin d → ℝ) := {x | a ≤ |g2 x|}
  have hE1 : volume E1 ≤ ENNReal.ofReal (η / 4) := by
    refine hdist1.trans (ENNReal.ofReal_le_ofReal ?_)
    simpa [scale] using hscale_le
  have hE2 : volume E2 ≤ ENNReal.ofReal (η / 4) := by
    refine hdist2.trans (ENNReal.ofReal_le_ofReal ?_)
    simpa [scale] using hscale_le2
  have hF1 : volume F1 ≤ ENNReal.ofReal (η / 4) :=
    hlevel1.trans (ENNReal.ofReal_le_ofReal hdiv1)
  have hF2 : volume F2 ≤ ENNReal.ofReal (η / 4) :=
    hlevel2.trans (ENNReal.ofReal_le_ofReal hdiv2)
  have hunion : volume (E1 ∪ E2 ∪ F1 ∪ F2) ≤ ENNReal.ofReal η := by
    have hsumv : volume E1 + volume E2 + volume F1 + volume F2 ≤
        ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) +
          ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) :=
      add_le_add (add_le_add (add_le_add hE1 hE2) hF1) hF2
    have hfour : ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) +
        ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    have hle : volume (E1 ∪ E2 ∪ F1 ∪ F2) ≤
        volume E1 + volume E2 + volume F1 + volume F2 := by
      have h12 : volume (E1 ∪ E2) ≤ volume E1 + volume E2 := measure_union_le _ _
      have h123 : volume (E1 ∪ E2 ∪ F1) ≤ volume (E1 ∪ E2) + volume F1 :=
        measure_union_le _ _
      calc
        volume (E1 ∪ E2 ∪ F1 ∪ F2) ≤ volume (E1 ∪ E2 ∪ F1) + volume F2 :=
          measure_union_le _ _
        _ ≤ volume (E1 ∪ E2) + volume F1 + volume F2 := add_le_add_left h123 _
        _ ≤ volume E1 + volume E2 + volume F1 + volume F2 :=
          add_le_add_left (add_le_add_left h12 _) _
    exact hle.trans (hsumv.trans_eq hfour)
  have hd0 : 0 < d := by omega
  have hinc : rectangleOscillation f ε ⊆ E1 ∪ E2 ∪ F1 ∪ F2 := by
    intro x hxOsc
    by_cases h1 : ENNReal.ofReal a < strongMaximalFunction g1 x
    · exact Or.inl (Or.inl (Or.inl h1))
    · by_cases h2 : ENNReal.ofReal a < strongMaximalFunction g2 x
      · exact Or.inl (Or.inl (Or.inr h2))
      · by_cases h3 : a ≤ |g1 x|
        · exact Or.inl (Or.inr h3)
        · by_cases h4 : a ≤ |g2 x|
          · exact Or.inr h4
          · exfalso
            obtain ⟨ρ, hρ, hρR⟩ := exists_rectangle_width hd0 hg1 hg2 hh hhs
              (not_lt.mp h1) (not_lt.mp h2) (not_le.mp h3) (not_le.mp h4) hε
            obtain ⟨R, hxR, hwidth, hge⟩ := hxOsc ρ hρ
            have hfun : R.average f = R.average (fun y ↦ g1 y + g2 y + h y) := by
              unfold OpenRectangle.average
              congr 1
              exact setIntegral_congr_fun R.measurableSet_carrier fun y _ ↦ hsum y
            have hval : f x = g1 x + g2 x + h x := hsum x
            rw [hfun, hval] at hge
            exact not_lt_of_ge hge (hρR R hxR hwidth)
  exact (measure_mono hinc).trans hunion

/-- A measurable function with globally integrable endpoint growth is rectangularly differentiated
almost everywhere. -/
theorem ae_rectanglesDifferentiateAt_of_integrable_growth {d : ℕ} (hd : 1 ≤ d)
    {f : (Fin d → ℝ) → ℝ} (hm : Measurable f)
    (hG : Integrable (fun x ↦ strongMaximalGrowth d |f x|)) :
    ∀ᵐ x ∂volume, RectanglesDifferentiateAt f x := by
  rw [ae_iff]
  have hosc : ∀ n : ℕ, volume (rectangleOscillation f (1 / (n + 1 : ℝ))) = 0 := by
    intro n
    exact volume_rectangleOscillation_eq_zero hd hm hG (by positivity)
  have hsub : {x | ¬ RectanglesDifferentiateAt f x} ⊆
      ⋃ n : ℕ, rectangleOscillation f (1 / (n + 1 : ℝ)) := by
    intro x hx
    unfold RectanglesDifferentiateAt at hx
    push Not at hx
    obtain ⟨ε, hε, hx⟩ := hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine mem_iUnion.2 ⟨n, ?_⟩
    intro δ hδ
    obtain ⟨R, hxR, hwidth, hbig⟩ := hx δ hδ
    exact ⟨R, hxR, hwidth, hn.le.trans hbig⟩
  refine measure_mono_null hsub ?_
  suffices hzero :
      ∑' n : ℕ, volume (rectangleOscillation f (1 / (n + 1 : ℝ))) = 0 by
    exact le_antisymm ((measure_iUnion_le _).trans hzero.le) bot_le
  rw [ENNReal.tsum_eq_zero]
  intro n
  exact hosc n

end CKMA
