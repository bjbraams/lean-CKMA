/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.RectangularDifferentiation.Differentiate
public import Mathlib.NumberTheory.Harmonic.Bounds

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# An integrable function not differentiated by rectangles

Each stage of the Saks picture is a harmonic family of axis-aligned strips in a scaled square.
The packing of translates, the higher-dimensional product, and the integrable spike sum are in
`CounterexampleCover`.
-/

@[expose] public section

noncomputable section

open Classical MeasureTheory Set Filter Finset
open scoped ENNReal NNReal BigOperators

namespace CKMA.Bohr

/-- The target average at stage `k`. -/
def stageHeight (k : ℕ) : ℝ := k + 1

/-- Dyadic length producing a harmonic sum at least half this integer. -/
def stageLog (k : ℕ) : ℕ := (k + 1) * 2 ^ (k + 4)

/-- Number of strips in the Bohr picture at stage `k`. -/
def stageCount (k : ℕ) : ℕ := 2 ^ stageLog k

/-- Linear scale that makes every witnessing rectangle narrower than `2 ^ (-(k + 1))`. -/
def stageScale (k : ℕ) : ℝ :=
  1 / ((2 ^ (k + 2) : ℕ) * (stageCount k + 1) : ℝ)

/-- Side length of the bounding square of one scaled picture. -/
def boxSide (k : ℕ) : ℝ := stageScale k * stageCount k

/-- `k + 1` is at most a power of two. -/
lemma nat_succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    calc
      k + 1 + 1 ≤ 2 ^ (k + 1) + 2 ^ (k + 1) := by
        have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
        omega
      _ = 2 ^ (k + 2) := by rw [← two_mul, ← pow_succ']

/-- `n + 1 ≤ 2 ^ n`. -/
lemma succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    calc
      n + 1 + 1 ≤ 2 ^ n + 1 := by omega
      _ ≤ 2 ^ n + 2 ^ n := by
        have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        omega
      _ = 2 ^ (n + 1) := by rw [← two_mul, ← pow_succ']

/-- The scale is positive. -/
lemma stageScale_pos (k : ℕ) : 0 < stageScale k := by
  unfold stageScale
  positivity

/-- The bounding side equals `N / (2 ^ (k + 2) · (N + 1))`. -/
lemma boxSide_eq (k : ℕ) :
    boxSide k =
      (stageCount k : ℝ) / ((2 ^ (k + 2) : ℕ) * (stageCount k + 1) : ℝ) := by
  unfold boxSide stageScale
  rw [div_mul_eq_mul_div, one_mul]

/-- The bounding side is strictly shorter than one quarter. -/
lemma boxSide_lt_quarter (k : ℕ) : boxSide k < (4 : ℝ)⁻¹ := by
  rw [boxSide_eq, ← one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
  have h4 : (4 : ℕ) ≤ 2 ^ (k + 2) := by
    calc
      (4 : ℕ) = 2 ^ 2 := by decide
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have h4R : (4 : ℝ) ≤ (2 ^ (k + 2) : ℕ) := by exact_mod_cast h4
  have hNnonneg : (0 : ℝ) ≤ stageCount k := Nat.cast_nonneg _
  have hstep : (stageCount k : ℝ) * 4 ≤ (2 ^ (k + 2) : ℕ) * stageCount k := by
    calc
      (stageCount k : ℝ) * 4 = 4 * stageCount k := by ring
      _ ≤ (2 ^ (k + 2) : ℕ) * stageCount k :=
        mul_le_mul_of_nonneg_right h4R hNnonneg
  have hstrict : (2 ^ (k + 2) : ℕ) * (stageCount k : ℝ) <
      (2 ^ (k + 2) : ℕ) * (stageCount k + 1) :=
    mul_lt_mul_of_pos_left (by linarith) (by positivity)
  have hright : ((2 ^ (k + 2) : ℕ) : ℝ) * ((stageCount k : ℝ) + 1) =
      1 * (((2 ^ (k + 2) : ℕ) : ℝ) * ((stageCount k : ℝ) + 1)) := by ring
  exact (hstep.trans_lt hstrict).trans_eq hright

/-- The bounding side is positive and leaves room in the unit interval. -/
lemma boxSide_mem_Ioo (k : ℕ) : 0 < boxSide k ∧ boxSide k < 1 := by
  refine ⟨mul_pos (stageScale_pos k) (by unfold stageCount; positivity), ?_⟩
  exact (boxSide_lt_quarter k).trans (by norm_num)

/-- Removing the first term splits the harmonic sum. -/
lemma tail_harmonic (n : ℕ) (hn : 2 ≤ n) :
    ∑ j ∈ Finset.Icc 2 n, (1 / (j : ℝ)) = (harmonic n : ℝ) - 1 := by
  have hmem : 1 ∈ Finset.Icc 1 n := Finset.left_mem_Icc.mpr (by omega)
  have hcast : (harmonic n : ℝ) = ∑ i ∈ Finset.Icc 1 n, (1 / (i : ℝ)) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Rat.cast_inv, Rat.cast_natCast, one_div]
  rw [hcast, ← Finset.sum_erase_add (Finset.Icc 1 n) (fun j : ℕ => 1 / (j : ℝ)) hmem]
  have herase : (Finset.Icc 1 n).erase 1 = Finset.Icc 2 n := by
    ext j
    simp [Finset.mem_Icc]
    omega
  rw [herase]
  simp [one_div]

/-- The stage logarithm is at least sixteen. -/
lemma stageLog_ge_sixteen (k : ℕ) : 16 ≤ stageLog k := by
  unfold stageLog
  have hpow : 2 ^ 4 ≤ 2 ^ (k + 4) := Nat.pow_le_pow_right (by decide) (by omega)
  have hone : 1 ≤ k + 1 := by omega
  calc
    16 = 1 * 2 ^ 4 := by decide
    _ ≤ (k + 1) * 2 ^ (k + 4) := Nat.mul_le_mul hone hpow

/-- Half the stage logarithm is a lower bound for the harmonic tail. -/
lemma stage_harmonic_lower (k : ℕ) :
    (stageLog k : ℝ) / 2 ≤ ∑ j ∈ Finset.Icc 2 (stageCount k), (1 / (j : ℝ)) := by
  have hm : (16 : ℝ) ≤ stageLog k := by exact_mod_cast stageLog_ge_sixteen k
  have hN : 2 ≤ stageCount k := by
    unfold stageCount
    calc
      2 = 2 ^ 1 := by decide
      _ ≤ 2 ^ stageLog k :=
        Nat.pow_le_pow_right (by decide) (le_trans (by decide) (stageLog_ge_sixteen k))
  rw [tail_harmonic (stageCount k) hN]
  have hlog : Real.log (stageCount k) = stageLog k * Real.log 2 := by
    rw [stageCount, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  have hgap : (1 : ℝ) ≤ (stageLog k) * (Real.log 2 - 1 / 2) := by
    have hlt : (1 / 16 : ℝ) < Real.log 2 - 1 / 2 := by linarith [Real.log_two_gt_d9]
    nlinarith
  have hhalf : (stageLog k : ℝ) / 2 ≤ Real.log (stageCount k) - 1 := by
    rw [hlog]
    linarith
  have hmono : Real.log (stageCount k) ≤ Real.log (↑(stageCount k) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hH : Real.log (↑(stageCount k) + 1) ≤ harmonic (stageCount k) := by
    simpa [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic (stageCount k)
  linarith

/-- Lower bound on the area of one scaled Bohr union of strips. -/
def areaLower (k : ℕ) : ℝ :=
  stageScale k ^ 2 * stageCount k * (stageLog k / 2)

/-- `areaLower` is positive. -/
lemma areaLower_pos (k : ℕ) : 0 < areaLower k := by
  unfold areaLower
  refine mul_pos (mul_pos (pow_pos (stageScale_pos k) 2) ?_) ?_
  · exact_mod_cast (Nat.two_pow_pos (stageLog k) : 0 < stageCount k)
  · exact div_pos (by exact_mod_cast (show 0 < stageLog k by
      unfold stageLog; positivity)) (by norm_num)

/-- The open square in which translates of one picture are allowed to sit. -/
def domain (k : ℕ) : Set (Fin 2 → ℝ) :=
  univ.pi fun _ => Ioo 0 (1 - boxSide k)

/-- The domain is an open rectangle of side `1 - boxSide`. -/
def domainRect (k : ℕ) : OpenRectangle 2 where
  lower := fun _ => 0
  upper := fun _ => 1 - boxSide k
  lower_lt_upper := fun _ => by
    have h := boxSide_mem_Ioo k
    linarith

/-- The domain coincides with the carrier of `domainRect`. -/
lemma domain_eq_carrier (k : ℕ) : domain k = (domainRect k).carrier := by
  rw [domain, OpenRectangle.carrier_eq_pi]
  simp [domainRect]

/-- Real area of the translate domain. -/
lemma volume_real_domain (k : ℕ) :
    volume.real (domain k) = (1 - boxSide k) ^ 2 := by
  have hside : ∀ j, 0 ≤ (domainRect k).upper j - (domainRect k).lower j := by
    intro j
    have h := boxSide_mem_Ioo k
    simp [domainRect]
    linarith
  rw [domain_eq_carrier, measureReal_def, (domainRect k).volume_carrier,
    ← ENNReal.ofReal_prod_of_nonneg (fun j _ => hside j),
    ENNReal.toReal_ofReal (Finset.prod_nonneg (fun j _ => hside j))]
  rw [Fin.prod_univ_two]
  simp [domainRect, sub_zero, pow_two]

/-- The domain has positive finite area. -/
lemma volume_domain_pos_lt_top (k : ℕ) :
    0 < volume (domain k) ∧ volume (domain k) < ∞ := by
  have hreal : 0 < volume.real (domain k) := by
    rw [volume_real_domain]
    have h := boxSide_mem_Ioo k
    exact pow_pos (by linarith [h.1, h.2]) 2
  refine ⟨?_, ?_⟩
  · rw [measureReal_def] at hreal
    exact ENNReal.toReal_pos_iff.mp hreal |>.1
  · rw [domain_eq_carrier]
    exact (domainRect k).volume_carrier_lt_top

/-- A plane strip of the scaled Bohr picture, for an index `j ≥ 2`. -/
def stripRect (k j : ℕ) (hj : 2 ≤ j) : OpenRectangle 2 where
  lower := fun i => if i = 0 then stageScale k * (j - 1) else 0
  upper := fun i =>
    if i = 0 then stageScale k * j else stageScale k * stageCount k / j
  lower_lt_upper := by
    intro i
    fin_cases i <;> simp
    · have hjR : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
      have hτ : 0 < stageScale k := stageScale_pos k
      nlinarith
    · have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
      have hτ : 0 < stageScale k := stageScale_pos k
      exact div_pos (mul_pos hτ (by
        unfold stageCount
        exact_mod_cast Nat.two_pow_pos (stageLog k))) hjR

/-- Horizontal side of a strip. -/
lemma strip_width_x (k j : ℕ) (hj : 2 ≤ j) :
    (stripRect k j hj).upper 0 - (stripRect k j hj).lower 0 = stageScale k := by
  simp only [stripRect]
  rw [ite_eq_left trivial, ite_eq_left trivial]
  ring

/-- Vertical side of a strip. -/
lemma strip_width_y (k j : ℕ) (hj : 2 ≤ j) :
    (stripRect k j hj).upper 1 - (stripRect k j hj).lower 1 =
      stageScale k * (stageCount k : ℝ) / j := by
  simp only [stripRect]
  rw [ite_eq_right (show (1 : Fin 2) ≠ 0 by decide),
    ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)]
  field_simp
  ring

/-- The `j`-th strip when `j` lies in the harmonic range, and the empty set otherwise. -/
def stripCarrier (k j : ℕ) : Set (Fin 2 → ℝ) :=
  if h : 2 ≤ j ∧ j ≤ stageCount k then (stripRect k j h.1).carrier else ∅

/-- On the harmonic range the carrier is the rectangle. -/
lemma stripCarrier_of_mem (k j : ℕ) (hj : j ∈ Finset.Icc 2 (stageCount k)) :
    stripCarrier k j =
      (stripRect k j (Finset.mem_Icc.mp hj).1).carrier := by
  have h2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
  have hN : j ≤ stageCount k := (Finset.mem_Icc.mp hj).2
  simp [stripCarrier, h2, hN]

/-- Volume of one strip. -/
lemma volume_stripCarrier (k j : ℕ) (hj : j ∈ Finset.Icc 2 (stageCount k)) :
    volume (stripCarrier k j) =
      ENNReal.ofReal (stageScale k ^ 2 * (stageCount k : ℝ) / j) := by
  rw [stripCarrier_of_mem k j hj]
  have h2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
  rw [(stripRect k j h2).volume_carrier, Fin.prod_univ_two, strip_width_x k j h2,
    strip_width_y k j h2]
  have hτ : 0 ≤ stageScale k := (stageScale_pos k).le
  rw [← ENNReal.ofReal_mul hτ]
  congr 1
  ring

/-- Distinct strips meet in an empty set. -/
lemma pairwise_stripCarrier (k : ℕ) :
    PairwiseDisjoint (↑(Finset.Icc 2 (stageCount k))) (stripCarrier k) := by
  intro a ha b hb hab
  change Disjoint (stripCarrier k a) (stripCarrier k b)
  rw [stripCarrier_of_mem k a ha, stripCarrier_of_mem k b hb]
  have haI := Finset.mem_Icc.mp ha
  have hbI := Finset.mem_Icc.mp hb
  rcases hab.lt_or_gt with hlt | hlt
  · rw [Set.disjoint_left]
    intro x hx hx'
    have hxa : x 0 < stageScale k * a := by
      have hmem := hx 0
      simp only [stripRect] at hmem
      exact hmem.2
    have hxb : stageScale k * (b - 1) < x 0 := by
      have hmem := hx' 0
      simp only [stripRect] at hmem
      exact hmem.1
    have hτ : 0 ≤ stageScale k := (stageScale_pos k).le
    have hab1 : a + 1 ≤ b := by omega
    have habR : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hab1
    have hineq : (a : ℝ) ≤ (b : ℝ) - 1 := by linarith
    linarith [mul_le_mul_of_nonneg_left hineq hτ]
  · rw [Set.disjoint_left]
    intro x hx hx'
    have hxb : x 0 < stageScale k * b := by
      have hmem := hx' 0
      simp only [stripRect] at hmem
      exact hmem.2
    have hxa : stageScale k * (a - 1) < x 0 := by
      have hmem := hx 0
      simp only [stripRect] at hmem
      exact hmem.1
    have hτ : 0 ≤ stageScale k := (stageScale_pos k).le
    have hab1 : b + 1 ≤ a := by omega
    have habR : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hab1
    have hineq : (b : ℝ) ≤ (a : ℝ) - 1 := by linarith
    linarith [mul_le_mul_of_nonneg_left hineq hτ]

/-- Union of the harmonic strips in one scaled picture. -/
def badPlane (k : ℕ) : Set (Fin 2 → ℝ) :=
  ⋃ j ∈ Finset.Icc 2 (stageCount k), stripCarrier k j

/-- The strip union is measurable. -/
lemma measurableSet_badPlane (k : ℕ) : MeasurableSet (badPlane k) := by
  rw [badPlane]
  exact Finset.measurableSet_biUnion _ fun j hj => by
    rw [stripCarrier_of_mem k j hj]
    exact (stripRect k j (Finset.mem_Icc.mp hj).1).measurableSet_carrier

/-- The strip union has area at least `areaLower`. -/
lemma areaLower_le_volume_badPlane (k : ℕ) :
    ENNReal.ofReal (areaLower k) ≤ volume (badPlane k) := by
  have hm : ∀ j ∈ Finset.Icc 2 (stageCount k), MeasurableSet (stripCarrier k j) := by
    intro j hj
    rw [stripCarrier_of_mem k j hj]
    exact (stripRect k j (Finset.mem_Icc.mp hj).1).measurableSet_carrier
  rw [badPlane, measure_biUnion_finset (pairwise_stripCarrier k) hm]
  have hsum : ∑ j ∈ Finset.Icc 2 (stageCount k), volume (stripCarrier k j) =
      ENNReal.ofReal (stageScale k ^ 2 * (stageCount k : ℝ) *
        ∑ j ∈ Finset.Icc 2 (stageCount k), (1 / (j : ℝ))) := by
    rw [Finset.sum_congr rfl fun j hj => volume_stripCarrier k j hj,
      ← ENNReal.ofReal_sum_of_nonneg (fun j hj => by positivity)]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by
      have := (Finset.mem_Icc.mp hj).1
      omega)
    field_simp
  rw [hsum]
  apply ENNReal.ofReal_le_ofReal
  rw [areaLower]
  exact mul_le_mul_of_nonneg_left (stage_harmonic_lower k) (by positivity)

/-- Length of each extra side of a witnessing window. -/
def margin (d k : ℕ) : ℝ :=
  if d ≤ 2 then 0 else 1 / ((2 ^ (k + 2) * (d - 2) : ℕ) : ℝ)

/-- The window length is at most one quarter. -/
lemma margin_le_inv_four (d k : ℕ) : margin d k ≤ (4 : ℝ)⁻¹ := by
  unfold margin
  split_ifs with hd
  · norm_num
  · have h4 : (4 : ℝ) ≤ (2 ^ (k + 2) : ℕ) := by
      exact_mod_cast (show (4 : ℕ) ≤ 2 ^ (k + 2) by
        calc
          (4 : ℕ) = 2 ^ 2 := by decide
          _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by decide) (by omega))
    have hd2 : (1 : ℝ) ≤ (d - 2 : ℕ) := by
      exact_mod_cast (show 1 ≤ d - 2 by omega)
    have hden : (4 : ℝ) ≤ (2 ^ (k + 2) : ℕ) * (d - 2 : ℕ) := by
      have h1 : (4 : ℝ) ≤ 4 * (d - 2 : ℕ) := by nlinarith
      exact h1.trans (mul_le_mul_of_nonneg_right h4 (by positivity))
    have hcast : ((2 ^ (k + 2) * (d - 2) : ℕ) : ℝ) =
        (2 ^ (k + 2) : ℕ) * (d - 2 : ℕ) := Nat.cast_mul _ _
    rw [one_div, hcast]
    exact (inv_le_inv₀ (by positivity) (by norm_num)).mpr hden

/-- The extra sides contribute total width `2 ^ (-(k + 2))`. -/
lemma extraWidth (d k : ℕ) (hd : 2 < d) :
    ((d - 2 : ℕ) : ℝ) * margin d k = (2 ^ (k + 2) : ℝ)⁻¹ := by
  have hnot : ¬ d ≤ 2 := by omega
  simp only [margin, hnot, ite_false]
  rw [one_div, Nat.cast_mul, mul_inv, Nat.cast_pow, Nat.cast_ofNat]
  have hd0 : ((d - 2 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show d - 2 ≠ 0 by omega)
  rw [mul_left_comm, mul_inv_cancel₀ hd0, mul_one]

/-- Lower corner of the inner rectangle. -/
def innerLower (d k : ℕ) (i : Fin d) : ℝ :=
  if i.val ≤ 1 then boxSide k else margin d k / 2

/-- Upper corner of the inner rectangle. -/
def innerUpper (d k : ℕ) (i : Fin d) : ℝ :=
  if i.val ≤ 1 then 1 - boxSide k else 1 - margin d k / 2

/-- The inner rectangle, where translates still see a full strip. -/
def innerRect (d k : ℕ) (_hd : 2 ≤ d) : OpenRectangle d where
  lower := innerLower d k
  upper := innerUpper d k
  lower_lt_upper := by
    intro i
    by_cases hi : i.val ≤ 1
    · simp only [innerLower, innerUpper, hi, ite_true]
      have h := boxSide_lt_quarter k
      linarith
    · simp only [innerLower, innerUpper, hi, ite_false]
      have hm : margin d k ≤ (4 : ℝ)⁻¹ := margin_le_inv_four d k
      have hm0 : 0 ≤ margin d k := by
        unfold margin
        split_ifs with hd2
        · rfl
        · exact (div_pos one_pos (by
            exact_mod_cast (Nat.mul_pos (Nat.two_pow_pos _)
              (show 0 < d - 2 by omega)))).le
      linarith

/-- Carrier of the inner rectangle. -/
def inner (d k : ℕ) (hd : 2 ≤ d) : Set (Fin d → ℝ) := (innerRect d k hd).carrier

/-- Side lengths of the inner rectangle. -/
lemma inner_side (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    (innerRect d k hd).upper i - (innerRect d k hd).lower i =
      if i.val ≤ 1 then 1 - 2 * boxSide k else 1 - margin d k := by
  by_cases hi : i.val ≤ 1
  · simp only [innerRect, innerLower, innerUpper, hi, ite_true]
    ring
  · simp only [innerRect, innerLower, innerUpper, hi, ite_false]
    ring

/-- Two coordinates carry the Bohr picture. -/
lemma card_plane (d : ℕ) (hd : 2 ≤ d) :
    (Finset.univ.filter (fun i : Fin d => i.val ≤ 1)).card = 2 := by
  classical
  let z : Fin d := ⟨0, by omega⟩
  let o : Fin d := ⟨1, by omega⟩
  have hne : z ≠ o := by
    intro h
    have := congrArg Fin.val h
    simp [z, o] at this
  have hset : Finset.univ.filter (fun i : Fin d => i.val ≤ 1) = {z, o} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hi
      have hval : i.val = 0 ∨ i.val = 1 := by omega
      rcases hval with h0 | h1
      · left
        ext
        simp [z, h0]
      · right
        ext
        simp [o, h1]
    · intro h
      rcases h with rfl | rfl
      · simp [z]
      · simp [o]
  rw [hset]
  exact (Finset.card_pair_eq_two_iff).mpr hne

/-- The remaining coordinates form a face of dimension `d - 2`. -/
lemma card_extra (d : ℕ) (hd : 2 ≤ d) :
    (Finset.univ.filter (fun i : Fin d => ¬ i.val ≤ 1)).card = d - 2 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin d))) (fun i : Fin d => i.val ≤ 1)
  rw [card_plane d hd, Finset.card_univ, Fintype.card_fin] at h
  omega

/-- Real volume of the inner rectangle. -/
lemma volume_real_inner (d k : ℕ) (hd : 2 ≤ d) :
    volume.real (inner d k hd) =
      (1 - 2 * boxSide k) ^ 2 * (1 - margin d k) ^ (d - 2) := by
  have hside : ∀ i, 0 ≤ (innerRect d k hd).upper i - (innerRect d k hd).lower i := by
    intro i
    rw [inner_side d k hd i]
    by_cases hi : i.val ≤ 1
    · simp only [hi, ite_true]
      have h := boxSide_lt_quarter k
      linarith
    · simp only [hi, ite_false]
      linarith [margin_le_inv_four d k]
  rw [inner, measureReal_def, (innerRect d k hd).volume_carrier,
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => hside i),
    ENNReal.toReal_ofReal (Finset.prod_nonneg (fun i _ => hside i))]
  let p : Fin d → Prop := fun i => i.val ≤ 1
  have hsplit := Finset.prod_filter_mul_prod_filter_not Finset.univ p
    (fun i => (innerRect d k hd).upper i - (innerRect d k hd).lower i)
  rw [← hsplit]
  have hplane : ∏ i ∈ Finset.univ.filter p,
      ((innerRect d k hd).upper i - (innerRect d k hd).lower i) =
      (1 - 2 * boxSide k) ^ 2 := by
    calc
      _ = ∏ i ∈ Finset.univ.filter p, (1 - 2 * boxSide k) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have hi' : p i := (Finset.mem_filter.mp hi).2
        simp [inner_side d k hd i, hi', p]
      _ = (1 - 2 * boxSide k) ^ (Finset.univ.filter p).card := by
        simp [Finset.prod_const]
      _ = (1 - 2 * boxSide k) ^ 2 := by rw [card_plane d hd]
  have hextra : ∏ i ∈ Finset.univ.filter (fun i => ¬ p i),
      ((innerRect d k hd).upper i - (innerRect d k hd).lower i) =
      (1 - margin d k) ^ (d - 2) := by
    calc
      _ = ∏ i ∈ Finset.univ.filter (fun i => ¬ p i), (1 - margin d k) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have hi' : ¬ p i := (Finset.mem_filter.mp hi).2
        simp [inner_side d k hd i, hi', p]
      _ = (1 - margin d k) ^ (Finset.univ.filter (fun i => ¬ p i)).card := by
        simp [Finset.prod_const]
      _ = (1 - margin d k) ^ (d - 2) := by rw [card_extra d hd]
  rw [hplane, hextra]

/-- The squared plane factor exceeds one quarter. -/
lemma planeFactor_gt (k : ℕ) : (1 / 4 : ℝ) < (1 - 2 * boxSide k) ^ 2 := by
  have hhalf : (1 / 2 : ℝ) < 1 - 2 * boxSide k := by
    linarith [boxSide_lt_quarter k]
  have hsq : (1 / 2 : ℝ) ^ 2 < (1 - 2 * boxSide k) ^ 2 :=
    pow_lt_pow_left₀ hhalf (by norm_num) (by decide)
  have hnum : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
  linarith

/-- Bernoulli gives a uniform lower bound on the extra factor. -/
lemma extraFactor_ge (d k : ℕ) (hd : 2 ≤ d) :
    (3 / 4 : ℝ) ≤ (1 - margin d k) ^ (d - 2) := by
  have hneg : (-2 : ℝ) ≤ -margin d k := by linarith [margin_le_inv_four d k]
  have hB := one_add_mul_le_pow hneg (d - 2)
  have hsub : (1 : ℝ) - ((d - 2 : ℕ) : ℝ) * margin d k ≤
      (1 - margin d k) ^ (d - 2) := by
    simpa [sub_eq_add_neg] using hB
  have hbase : (3 / 4 : ℝ) ≤ 1 - ((d - 2 : ℕ) : ℝ) * margin d k := by
    by_cases hd2 : d ≤ 2
    · have hdEq : d = 2 := by omega
      simp [hdEq, margin]
      norm_num
    · have hd' : 2 < d := by omega
      rw [extraWidth d k hd']
      have h4 : (4 : ℝ) ≤ 2 ^ (k + 2) := by
        exact_mod_cast (show (4 : ℕ) ≤ 2 ^ (k + 2) by
          calc
            (4 : ℕ) = 2 ^ 2 := by decide
            _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by decide) (by omega))
      have hinv : (2 ^ (k + 2) : ℝ)⁻¹ ≤ (4 : ℝ)⁻¹ :=
        (inv_le_inv₀ (by positivity) (by norm_num)).mpr h4
      linarith
  linarith

/-- The inner rectangle occupies more than `3 / 16` of the unit cube. -/
lemma volume_real_inner_gt (d k : ℕ) (hd : 2 ≤ d) :
    (3 / 16 : ℝ) < volume.real (inner d k hd) := by
  rw [volume_real_inner d k hd]
  have hplane := planeFactor_gt k
  have hextra := extraFactor_ge d k hd
  have hpos : (0 : ℝ) ≤ (3 / 4 : ℝ) := by norm_num
  have hmul : (1 / 4 : ℝ) * (3 / 4) <
      (1 - 2 * boxSide k) ^ 2 * (3 / 4) :=
    mul_lt_mul_of_pos_right hplane (by norm_num)
  have hmul' : (1 - 2 * boxSide k) ^ 2 * (3 / 4) ≤
      (1 - 2 * boxSide k) ^ 2 * (1 - margin d k) ^ (d - 2) :=
    mul_le_mul_of_nonneg_left hextra (by linarith [planeFactor_gt k])
  linarith [show (1 / 4 : ℝ) * (3 / 4) = 3 / 16 by norm_num]

/-- Fraction of the translate domain removed by one picture. -/
def removalRatio (k : ℕ) : ℝ := areaLower k / volume.real (domain k)

/-- The removal ratio lies in the unit interval. -/
lemma removalRatio_mem_Ioo (k : ℕ) : 0 < removalRatio k ∧ removalRatio k < 1 := by
  have hdom : 0 < volume.real (domain k) := by
    rw [volume_real_domain]
    exact pow_pos (by linarith [boxSide_mem_Ioo k]) 2
  refine ⟨div_pos (areaLower_pos k) hdom, ?_⟩
  rw [removalRatio, div_lt_one hdom]
  have hhalf : (stageLog k : ℝ) / 2 < stageCount k := by
    have hlt : stageLog k < 2 * stageCount k := by
      have hpow : stageLog k ≤ 2 ^ stageLog k := by
        have hsucc := succ_le_two_pow (stageLog k)
        omega
      have htwo : 2 ^ stageLog k < 2 * 2 ^ stageLog k := by
        have hone : 1 ≤ 2 ^ stageLog k := Nat.one_le_two_pow
        omega
      unfold stageCount
      omega
    have hR : (stageLog k : ℝ) < 2 * (stageCount k : ℝ) := by exact_mod_cast hlt
    linarith
  have harea : areaLower k < boxSide k ^ 2 := by
    rw [areaLower, boxSide]
    have hpos : 0 < stageScale k ^ 2 * stageCount k := by
      exact mul_pos (pow_pos (stageScale_pos k) 2)
        (by exact_mod_cast (Nat.two_pow_pos (stageLog k) : 0 < stageCount k))
    calc
      stageScale k ^ 2 * stageCount k * (stageLog k / 2)
          < stageScale k ^ 2 * stageCount k * stageCount k := by
            exact mul_lt_mul_of_pos_left hhalf hpos
      _ = (stageScale k * stageCount k) ^ 2 := by ring
  have hbox : boxSide k < 1 - boxSide k := by linarith [boxSide_lt_quarter k]
  have hsq : boxSide k ^ 2 < (1 - boxSide k) ^ 2 := by
    have h0 : 0 ≤ boxSide k := (boxSide_mem_Ioo k).1.le
    exact pow_lt_pow_left₀ hbox h0 (by decide)
  rw [volume_real_domain]
  linarith

/-- Number of translates used at stage `k`. -/
def copyCount (k : ℕ) : ℕ := Nat.floor (1 / removalRatio k) + 1

/-- The copies multiply the removal ratio to at least one. -/
lemma copyCount_ratio_ge_one (k : ℕ) :
    (1 : ℝ) ≤ (copyCount k : ℝ) * removalRatio k := by
  have hr := (removalRatio_mem_Ioo k).1
  have hlt : 1 / removalRatio k < (copyCount k : ℝ) := by
    unfold copyCount
    rw [Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one (1 / removalRatio k)
  rw [div_lt_iff₀ hr] at hlt
  exact hlt.le

/-- There are at most one more copies than the reciprocal of the ratio. -/
lemma copyCount_le (k : ℕ) :
    (copyCount k : ℝ) ≤ 1 / removalRatio k + 1 := by
  unfold copyCount
  have hr : 0 ≤ 1 / removalRatio k := by
    exact le_of_lt (div_pos one_pos (removalRatio_mem_Ioo k).1)
  have hfl : ((Nat.floor (1 / removalRatio k) : ℕ) : ℝ) ≤ 1 / removalRatio k :=
    Nat.floor_le hr
  rw [Nat.cast_add, Nat.cast_one]
  exact add_le_add_left hfl 1

/-- One point of the translate domain. -/
lemma domain_nonempty (k : ℕ) : ∃ v : Fin 2 → ℝ, v ∈ domain k := by
  refine ⟨fun _ => (1 - boxSide k) / 2, ?_⟩
  rw [domain]
  intro i _
  have h := boxSide_mem_Ioo k
  constructor <;> linarith

/-- The translate domain is measurable. -/
lemma measurableSet_domain (k : ℕ) : MeasurableSet (domain k) := by
  rw [domain_eq_carrier]
  exact (domainRect k).measurableSet_carrier

/-- The open square in the plane where a witness still fits. -/
def innerPlane (k : ℕ) : Set (Fin 2 → ℝ) := inner 2 k le_rfl

/-- Real area of the plane inner square. -/
lemma volume_real_innerPlane (k : ℕ) :
    volume.real (innerPlane k) = (1 - 2 * boxSide k) ^ 2 := by
  rw [innerPlane, volume_real_inner, pow_zero, mul_one]

/-- The plane inner square has positive finite area. -/
lemma volume_innerPlane_pos_lt_top (k : ℕ) :
    0 < volume (innerPlane k) ∧ volume (innerPlane k) < ∞ := by
  have hreal : 0 < volume.real (innerPlane k) := by
    rw [volume_real_innerPlane]
    exact lt_trans (by norm_num : (0 : ℝ) < 1 / 4) (planeFactor_gt k)
  refine ⟨?_, ?_⟩
  · rw [measureReal_def] at hreal
    exact (ENNReal.toReal_pos_iff.mp hreal).1
  · rw [innerPlane, inner]
    exact (innerRect 2 k le_rfl).volume_carrier_lt_top

/-- The strips lie in the scaled open square. -/
lemma badPlane_subset_box (k : ℕ) :
    badPlane k ⊆ univ.pi fun _ : Fin 2 => Ioo 0 (boxSide k) := by
  intro x hx
  rw [badPlane] at hx
  simp only [mem_iUnion] at hx
  obtain ⟨j, hj, hxj⟩ := hx
  rw [stripCarrier_of_mem k j hj] at hxj
  have hj2 : (2 : ℕ) ≤ j := (Finset.mem_Icc.mp hj).1
  have hjN : (j : ℝ) ≤ stageCount k := by exact_mod_cast (Finset.mem_Icc.mp hj).2
  have hτ : 0 < stageScale k := stageScale_pos k
  have hx0 := hxj 0
  have hx1 := hxj 1
  simp only [stripRect] at hx0 hx1
  rw [ite_eq_left trivial, ite_eq_left trivial] at hx0
  rw [ite_eq_right (show (1 : Fin 2) ≠ 0 by decide),
    ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)] at hx1
  rw [Set.mem_univ_pi]
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · rw [Set.mem_Ioo]
    refine ⟨?_, ?_⟩
    · have hlow : 0 ≤ stageScale k * ((j : ℝ) - 1) := by
        have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
        nlinarith
      exact lt_of_le_of_lt hlow hx0.1
    · have hup : stageScale k * (j : ℝ) ≤ boxSide k := by
        rw [boxSide]
        exact mul_le_mul_of_nonneg_left hjN hτ.le
      exact lt_of_lt_of_le hx0.2 hup
  · rw [Set.mem_Ioo]
    refine ⟨hx1.1, ?_⟩
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hj1 : (1 : ℝ) < j := by exact_mod_cast (show 1 < j by omega)
    have hN : (0 : ℝ) < stageCount k := by
      unfold stageCount
      exact_mod_cast Nat.two_pow_pos (stageLog k)
    have hlt : stageScale k * stageCount k / j < boxSide k := by
      have hpos : 0 < stageScale k * (stageCount k : ℝ) := mul_pos hτ hN
      rw [boxSide, div_lt_iff₀ hj0]
      have hmul := mul_lt_mul_of_pos_left hj1 hpos
      rwa [mul_one] at hmul
    exact lt_trans hx1.2 hlt

/-- Reflecting a strip through an inner point stays inside the translate domain. -/
lemma sub_badPlane_subset_domain (k : ℕ) {x : Fin 2 → ℝ} (hx : x ∈ innerPlane k) :
    (fun v => x - v) ⁻¹' badPlane k ⊆ domain k := by
  intro v hv
  have hbox := badPlane_subset_box k hv
  rw [Set.mem_univ_pi] at hbox
  rw [domain, Set.mem_univ_pi]
  intro i
  have hi : i.val ≤ 1 := by have hlt := i.isLt; omega
  have hsi := hbox i
  have hxi := hx i
  simp only [innerRect, innerLower, innerUpper, hi, ite_true] at hxi
  rw [Set.mem_Ioo] at hsi ⊢
  have hvx : v i = x i - (x - v) i := by simp
  rw [hvx]
  constructor <;> linarith

/-- Each inner point sees a reflected copy of the whole strip union. -/
lemma volume_fiber_ge (k : ℕ) {x : Fin 2 → ℝ} (hx : x ∈ innerPlane k) :
    ENNReal.ofReal (areaLower k) ≤
      volume {v | v ∈ domain k ∧ x - v ∈ badPlane k} := by
  have hpre : volume ((fun v => x - v) ⁻¹' badPlane k) = volume (badPlane k) :=
    (volume.measurePreserving_sub_left x).measure_preimage
      (measurableSet_badPlane k).nullMeasurableSet
  have heq : {v | v ∈ domain k ∧ x - v ∈ badPlane k} =
      (fun v => x - v) ⁻¹' badPlane k := by
    ext v
    constructor
    · intro hv
      exact hv.2
    · intro hv
      exact ⟨sub_badPlane_subset_domain k hx hv, hv⟩
  rw [heq, hpre]
  exact areaLower_le_volume_badPlane k

/-- Pairs `(v, x)` for which the translate of `v` meets `U` in the strip union. -/
def hitSet (k : ℕ) (U : Set (Fin 2 → ℝ)) : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ)) :=
  {p | p.1 ∈ domain k ∧ p.2 ∈ U ∧ p.2 - p.1 ∈ badPlane k}

/-- The hitting set is measurable. -/
lemma measurableSet_hitSet (k : ℕ) {U : Set (Fin 2 → ℝ)} (hU : MeasurableSet U) :
    MeasurableSet (hitSet k U) := by
  have hsub : Measurable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => p.2 - p.1) := by
    fun_prop
  have hdom : MeasurableSet (Prod.fst ⁻¹' domain k) :=
    measurable_fst (β := Fin 2 → ℝ) (measurableSet_domain k)
  have hUset : MeasurableSet (Prod.snd ⁻¹' U) :=
    measurable_snd (α := Fin 2 → ℝ) hU
  have hbad : MeasurableSet ((fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => p.2 - p.1) ⁻¹'
      badPlane k) :=
    hsub (measurableSet_badPlane k)
  convert hdom.inter (hUset.inter hbad) using 1
  ext p
  simp [hitSet]

/-- One ratio of the domain has the same mass as the strip union. -/
lemma removalRatio_mul_volume (k : ℕ) :
    ENNReal.ofReal (removalRatio k) * volume (domain k) =
      ENNReal.ofReal (areaLower k) := by
  have hvolD : volume (domain k) = ENNReal.ofReal (volume.real (domain k)) := by
    rw [measureReal_def]
    exact (ENNReal.ofReal_toReal (volume_domain_pos_lt_top k).2.ne).symm
  rw [hvolD, ← ENNReal.ofReal_mul (removalRatio_mem_Ioo k).1.le]
  congr 1
  unfold removalRatio
  field_simp [show volume.real (domain k) ≠ 0 by
    rw [volume_real_domain]
    exact ne_of_gt (pow_pos (by linarith [boxSide_mem_Ioo k]) 2)]

/-- One translate meets any positive subset of the inner square in a definite fraction. -/
lemma exists_heavy_translate (k : ℕ) {U : Set (Fin 2 → ℝ)}
    (hU : MeasurableSet U) (hUs : U ⊆ innerPlane k) :
    ∃ v : Fin 2 → ℝ, v ∈ domain k ∧
      ENNReal.ofReal (removalRatio k) * volume U ≤
        volume (U ∩ {x | x - v ∈ badPlane k}) := by
  obtain ⟨v0, hv0⟩ := domain_nonempty k
  by_cases hU0 : volume U = 0
  · exact ⟨v0, hv0, by simp [hU0]⟩
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  have hS : MeasurableSet (hitSet k U) := measurableSet_hitSet k hU
  have hvint : (volume.prod volume) (hitSet k U) =
      ∫⁻ v, volume (Prod.mk v ⁻¹' hitSet k U) ∂volume :=
    Measure.prod_apply (μ := volume) (ν := volume) hS
  have hxint : (volume.prod volume) (hitSet k U) =
      ∫⁻ x, volume ((fun v => (v, x)) ⁻¹' hitSet k U) ∂volume :=
    Measure.prod_apply_symm (μ := volume) (ν := volume) hS
  have hsec_in : ∀ v ∈ domain k,
      Prod.mk v ⁻¹' hitSet k U = U ∩ {x | x - v ∈ badPlane k} := by
    intro v hv
    ext x
    constructor
    · intro hx
      exact ⟨hx.2.1, hx.2.2⟩
    · intro hx
      exact ⟨hv, hx.1, hx.2⟩
  have hsec_out : ∀ v, v ∉ domain k → Prod.mk v ⁻¹' hitSet k U = ∅ := by
    intro v hv
    ext x
    constructor
    · intro hx
      exact hv hx.1
    · intro hx
      simp at hx
  have hint_eq : ∫⁻ v, volume (Prod.mk v ⁻¹' hitSet k U) ∂volume =
      ∫⁻ v in domain k, volume (U ∩ {x | x - v ∈ badPlane k}) ∂volume := by
    rw [← lintegral_indicator (measurableSet_domain k)]
    refine lintegral_congr fun v => ?_
    by_cases hv : v ∈ domain k
    · rw [indicator_of_mem hv, hsec_in v hv]
    · rw [indicator_of_notMem hv, hsec_out v hv, measure_empty]
  have hfiber : ∀ x, ENNReal.ofReal (areaLower k) *
      U.indicator (fun _ => (1 : ℝ≥0∞)) x ≤
        volume ((fun v => (v, x)) ⁻¹' hitSet k U) := by
    intro x
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx, mul_one]
      have heq : (fun v => (v, x)) ⁻¹' hitSet k U =
          {v | v ∈ domain k ∧ x - v ∈ badPlane k} := by
        ext v
        constructor
        · intro hv
          exact ⟨hv.1, hv.2.2⟩
        · intro hv
          exact ⟨hv.1, hx, hv.2⟩
      rw [heq]
      exact volume_fiber_ge k (hUs hx)
    · rw [indicator_of_notMem hx, mul_zero]
      exact zero_le
  have hge : ENNReal.ofReal (areaLower k) * volume U ≤
      ∫⁻ v, volume (Prod.mk v ⁻¹' hitSet k U) ∂volume := by
    rw [← hvint, hxint]
    calc
      ENNReal.ofReal (areaLower k) * volume U =
          ∫⁻ x, ENNReal.ofReal (areaLower k) *
            U.indicator (fun _ => (1 : ℝ≥0∞)) x ∂volume := by
        rw [lintegral_const_mul _ (measurable_const.indicator hU),
          lintegral_indicator hU, setLIntegral_const, one_mul]
      _ ≤ ∫⁻ x, volume ((fun v => (v, x)) ⁻¹' hitSet k U) ∂volume :=
        lintegral_mono hfiber
  let c : ℝ≥0∞ := ENNReal.ofReal (removalRatio k) * volume U
  have hc_lt : c < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_of_le_of_lt (measure_mono hUs) (volume_innerPlane_pos_lt_top k).2)
  have hfin : ∫⁻ v in domain k, volume (U ∩ {x | x - v ∈ badPlane k}) ∂volume ≠ ∞ := by
    refine ne_of_lt ?_
    calc
      ∫⁻ v in domain k, volume (U ∩ {x | x - v ∈ badPlane k}) ∂volume
          ≤ ∫⁻ v in domain k, c ∂volume :=
        setLIntegral_mono' (measurableSet_domain k) fun v hv => (h v hv).le
      _ = c * volume (domain k) := setLIntegral_const _ _
      _ < ∞ := ENNReal.mul_lt_top hc_lt (volume_domain_pos_lt_top k).2
  have hstrict : ∫⁻ v in domain k, volume (U ∩ {x | x - v ∈ badPlane k}) ∂volume <
      ∫⁻ v in domain k, c ∂volume :=
    setLIntegral_strict_mono (measurableSet_domain k) (volume_domain_pos_lt_top k).1.ne'
      measurable_const hfin (ae_of_all _ fun v hv => h v hv)
  rw [setLIntegral_const] at hstrict
  have hident : c * volume (domain k) = ENNReal.ofReal (areaLower k) * volume U := by
    calc
      c * volume (domain k) =
          ENNReal.ofReal (removalRatio k) * volume U * volume (domain k) := rfl
      _ = volume U * (ENNReal.ofReal (removalRatio k) * volume (domain k)) := by
        rw [mul_assoc, mul_left_comm]
      _ = volume U * ENNReal.ofReal (areaLower k) := by rw [removalRatio_mul_volume]
      _ = ENNReal.ofReal (areaLower k) * volume U := mul_comm _ _
  rw [hident, ← hint_eq] at hstrict
  exact (not_lt_of_ge hge) hstrict

end CKMA.Bohr
