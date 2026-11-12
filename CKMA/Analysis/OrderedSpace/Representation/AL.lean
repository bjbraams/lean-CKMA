/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.OrderedSpace.Bands
public import CKMA.Analysis.OrderedSpace.Representation.AM
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.Sum
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Kakutani representation of an AL-space

An AL-space is Archimedean and sequentially order complete. The principal ideal of a positive
vector, renormed by the order-unit gauge, is a complete AM-space with that vector as unit, so
the AM representation supplies a compact carrier. The Riesz–Markov measure of the AL-norm
functional makes evaluation into `L¹` an isometry for the original norm, and a weak unit makes
the ideal dense. A maximal disjoint family reduces the general case to weak units of the
closed principal bands, glued by the sum of the pushed-forward measures.
Sources: GAPS 19.29; Aliprantis–Burkinshaw, Theorem 4.27; Schaefer, Theorem II.8.5.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open Set Metric Filter Topology MeasureTheory
open scoped CompactlySupported

namespace CKMA

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E]
  [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]

/-- A normed Riesz space satisfies the Archimedean axiom. -/
theorem archimedean_of_norm {x y : E} (h : ∀ n : ℕ, (n : ℝ) • x ≤ y) : x ≤ 0 := by
  have hpos : ∀ n : ℕ, (n : ℝ) • x⁺ ≤ y⁺ := by
    intro n
    rw [← posPart_smul_of_nonneg (Nat.cast_nonneg n)]
    exact sup_le_sup_right (h n) 0
  have hnorm : ∀ n : ℕ, (n : ℝ) * ‖x⁺‖ ≤ ‖y⁺‖ := by
    intro n
    have habs : |(n : ℝ) • x⁺| ≤ |y⁺| := by
      rw [abs_of_nonneg (smul_nonneg (Nat.cast_nonneg n) (posPart_nonneg x)),
        abs_of_nonneg (posPart_nonneg y)]
      exact hpos n
    have hle := norm_le_norm_of_abs_le_abs habs
    rwa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)] at hle
  have hz : ‖x⁺‖ = 0 := by
    by_contra hne
    have hpos' : 0 < ‖x⁺‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    obtain ⟨n, hn⟩ := exists_nat_gt (‖y⁺‖ / ‖x⁺‖)
    have hlt : ‖y⁺‖ < (n : ℝ) * ‖x⁺‖ := by
      rwa [div_lt_iff₀ hpos'] at hn
    exact not_lt.mpr (hnorm n) hlt
  rw [norm_eq_zero] at hz
  exact posPart_eq_zero.mp hz

/-- Sequential monotone completeness of an AL-space. -/
theorem al_isKB (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {x : ℕ → E} (hx : Monotone x) (hpos : ∀ n, 0 ≤ x n)
    (hbound : ∃ M : ℝ, ∀ n, ‖x n‖ ≤ M) : ∃ y : E, Tendsto x atTop (𝓝 y) := by
  have hsub : ∀ n m, n ≤ m → ‖x m - x n‖ = ‖x m‖ - ‖x n‖ := by
    intro n m hnm
    have h := hE (x n) (x m - x n) (hpos n) (sub_nonneg.mpr (hx hnm))
    rw [add_sub_cancel] at h
    linarith
  have hn : Monotone (fun n => ‖x n‖) := by
    intro n m hnm
    have h := hsub n m hnm
    linarith [norm_nonneg (x m - x n)]
  have hb : BddAbove (range fun n => ‖x n‖) := by
    rcases hbound with ⟨M, hM⟩
    exact ⟨M, by rintro _ ⟨n, rfl⟩; exact hM n⟩
  have hcnorm := (tendsto_atTop_ciSup hn hb).cauchySeq
  apply cauchySeq_tendsto_of_complete
  refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
  rcases Metric.cauchySeq_iff'.1 hcnorm ε hε with ⟨N, hN⟩
  refine ⟨N, fun n hNn => ?_⟩
  have heq : dist (x n) (x N) = dist ‖x n‖ ‖x N‖ := by
    rw [dist_eq_norm, hsub N n hNn, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr (hn hNn))]
  rw [heq]
  exact hN n hNn

/-- The additive norm of an AL-space, extended from the positive cone. -/
def alNormFunctional (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖) :
    E →ₗ[ℝ] ℝ :=
  coneAdditiveLinearMap (fun x => ‖x‖)
    (fun x y hx hy => hE x y hx hy)
    (fun c x hc _hx => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, smul_eq_mul])

/-- On the positive cone the AL-norm functional is the ambient norm. -/
theorem alNormFunctional_apply_nonneg
    (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    {x : E} (hx : 0 ≤ x) : alNormFunctional hE x = ‖x‖ :=
  coneAdditiveLinearMap_apply_of_nonneg _ _ _ hx

/-- The AL-norm functional reproduces the norm on absolute values. -/
theorem alNormFunctional_abs
    (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖) (x : E) :
    alNormFunctional hE |x| = ‖x‖ := by
  rw [alNormFunctional_apply_nonneg hE (abs_nonneg x), norm_abs_eq_norm]

/-- The AL-norm functional is monotone. -/
theorem alNormFunctional_mono
    (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖) :
    Monotone (alNormFunctional hE) := by
  intro a b hab
  have hdiff : 0 ≤ b - a := sub_nonneg.mpr hab
  have hsub : alNormFunctional hE b - alNormFunctional hE a =
      alNormFunctional hE (b - a) := by
    rw [← map_sub]
  rw [← sub_nonneg, hsub, alNormFunctional_apply_nonneg hE hdiff]
  exact norm_nonneg _

/-- Positive parts of disjoint vectors remain disjoint. -/
theorem posPart_inf_posPart_eq_zero_of_disjoint {x y : E} (h : LatticeDisjoint x y) :
    x⁺ ⊓ y⁺ = 0 := by
  apply le_antisymm
  · calc x⁺ ⊓ y⁺ ≤ |x| ⊓ |y| :=
        inf_le_inf (sup_le (le_abs_self x) (abs_nonneg x))
          (sup_le (le_abs_self y) (abs_nonneg y))
    _ = 0 := h
  · exact le_inf (posPart_nonneg x) (posPart_nonneg y)

/-- Absolute values add when the vectors are lattice disjoint. -/
theorem abs_add_of_latticeDisjoint {x y : E} (h : LatticeDisjoint x y) :
    |x + y| = |x| + |y| := by
  have hparts : x⁺ ⊓ y⁺ = 0 ∧ x⁺ ⊓ y⁻ = 0 ∧ x⁻ ⊓ y⁺ = 0 ∧ x⁻ ⊓ y⁻ = 0 := by
    refine ⟨posPart_inf_posPart_eq_zero_of_disjoint h, ?_, ?_, ?_⟩
    · have hy : LatticeDisjoint x (-y) := by
        simpa [LatticeDisjoint, abs_neg] using h
      simpa [negPart_def] using posPart_inf_posPart_eq_zero_of_disjoint hy
    · have hx : LatticeDisjoint (-x) y := by
        simpa [LatticeDisjoint, abs_neg] using h
      simpa [negPart_def] using posPart_inf_posPart_eq_zero_of_disjoint hx
    · have hxy : LatticeDisjoint (-x) (-y) := by
        simpa [LatticeDisjoint, abs_neg] using h
      simpa [negPart_def] using posPart_inf_posPart_eq_zero_of_disjoint hxy
  have hcross : (x⁺ + y⁺) ⊓ (x⁻ + y⁻) = 0 := by
    have ha : 0 ≤ x⁺ := posPart_nonneg x
    have hb : 0 ≤ y⁺ := posPart_nonneg y
    have hc : 0 ≤ x⁻ := negPart_nonneg x
    have hd : 0 ≤ y⁻ := negPart_nonneg y
    apply le_antisymm
    · have h1 : (x⁺ + y⁺) ⊓ x⁻ ≤ x⁺ ⊓ x⁻ + y⁺ ⊓ x⁻ := by
        calc (x⁺ + y⁺) ⊓ x⁻ = x⁻ ⊓ (x⁺ + y⁺) := inf_comm _ _
          _ ≤ x⁻ ⊓ x⁺ + x⁻ ⊓ y⁺ := inf_add_le_add_inf hc ha hb
          _ = x⁺ ⊓ x⁻ + y⁺ ⊓ x⁻ := by rw [inf_comm x⁻, inf_comm x⁻]
      have h2 : (x⁺ + y⁺) ⊓ y⁻ ≤ x⁺ ⊓ y⁻ + y⁺ ⊓ y⁻ := by
        calc (x⁺ + y⁺) ⊓ y⁻ = y⁻ ⊓ (x⁺ + y⁺) := inf_comm _ _
          _ ≤ y⁻ ⊓ x⁺ + y⁻ ⊓ y⁺ := inf_add_le_add_inf hd ha hb
          _ = x⁺ ⊓ y⁻ + y⁺ ⊓ y⁻ := by rw [inf_comm y⁻, inf_comm y⁻]
      calc (x⁺ + y⁺) ⊓ (x⁻ + y⁻)
          ≤ (x⁺ + y⁺) ⊓ x⁻ + (x⁺ + y⁺) ⊓ y⁻ :=
            inf_add_le_add_inf (add_nonneg ha hb) hc hd
        _ ≤ (x⁺ ⊓ x⁻ + y⁺ ⊓ x⁻) + (x⁺ ⊓ y⁻ + y⁺ ⊓ y⁻) := add_le_add h1 h2
        _ = 0 := by
            rw [posPart_inf_negPart_eq_zero, inf_comm y⁺, hparts.2.2.1, hparts.2.1,
              posPart_inf_negPart_eq_zero]
            abel
    · exact le_inf (add_nonneg ha hb) (add_nonneg hc hd)
  have hdiff : x + y = (x⁺ + y⁺) - (x⁻ + y⁻) := by
    nth_rw 1 [← posPart_sub_negPart x]
    nth_rw 1 [← posPart_sub_negPart y]
    abel
  have hsplit := eq_posPart_negPart_of_inf_eq_zero
      (add_nonneg (posPart_nonneg x) (posPart_nonneg y))
      (add_nonneg (negPart_nonneg x) (negPart_nonneg y)) hcross hdiff
  calc |x + y| = (x + y)⁺ + (x + y)⁻ := by rw [← posPart_add_negPart]
    _ = (x⁺ + y⁺) + (x⁻ + y⁻) := by rw [hsplit.1, hsplit.2]
    _ = (x⁺ + x⁻) + (y⁺ + y⁻) := by abel
    _ = |x| + |y| := by rw [posPart_add_negPart, posPart_add_negPart]

/-- A vector disjoint from each summand is disjoint from the sum. -/
theorem latticeDisjoint_sum {ι : Type*} {s : Finset ι} {a : E} {x : ι → E}
    (ha : ∀ i ∈ s, LatticeDisjoint a (x i)) : LatticeDisjoint a (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp [LatticeDisjoint]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, LatticeDisjoint]
    have haj : |a| ⊓ |x j| = 0 := by
      simpa [LatticeDisjoint] using ha j (Finset.mem_insert_self j s)
    have hrest : |a| ⊓ |∑ i ∈ s, x i| = 0 := by
      have hsub : ∀ i ∈ s, LatticeDisjoint a (x i) :=
        fun i hi => ha i (Finset.mem_insert_of_mem hi)
      simpa [LatticeDisjoint] using ih hsub
    apply le_antisymm
    · calc |a| ⊓ |x j + ∑ i ∈ s, x i| ≤ |a| ⊓ (|x j| + |∑ i ∈ s, x i|) :=
          inf_le_inf_left _ (abs_add_le _ _)
      _ ≤ |a| ⊓ |x j| + |a| ⊓ |∑ i ∈ s, x i| :=
          inf_add_le_add_inf (abs_nonneg a) (abs_nonneg _) (abs_nonneg _)
      _ = 0 := by simp [haj, hrest]
    · exact le_inf (abs_nonneg _) (abs_nonneg _)

/-- The norm is additive on finite sums of pairwise lattice-disjoint vectors. -/
theorem norm_sum_of_pairwise_latticeDisjoint
    (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    {ι : Type*} {s : Finset ι} {x : ι → E}
    (hdisj : (s : Set ι).Pairwise fun i j => LatticeDisjoint (x i) (x j)) :
    ‖∑ i ∈ s, x i‖ = ∑ i ∈ s, ‖x i‖ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hterm : ∀ i ∈ s, LatticeDisjoint (x a) (x i) := by
      intro i hi
      exact hdisj (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
        (by rintro rfl; exact ha hi)
    have hrest := latticeDisjoint_sum hterm
    rw [← norm_abs_eq_norm (x a + ∑ i ∈ s, x i), abs_add_of_latticeDisjoint hrest,
      hE _ _ (abs_nonneg _) (abs_nonneg _), norm_abs_eq_norm, norm_abs_eq_norm]
    have hdisj' : (s : Set ι).Pairwise fun i j => LatticeDisjoint (x i) (x j) :=
      fun i hi j hj hij => hdisj (Finset.mem_insert_of_mem hi)
        (Finset.mem_insert_of_mem hj) hij
    rw [ih hdisj']

/-- Scalar truncation of the remainder meets the unit in a vector dominated by `x`. -/
theorem trunc_smul_le {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) (n : ℕ) :
    (n : ℝ) • ((x - x ⊓ ((n : ℝ) • u)) ⊓ u) ≤ x := by
  induction n with
  | zero => simp [hx]
  | succ n ih =>
    set w : E := (x - x ⊓ (((n + 1 : ℕ) : ℝ) • u)) ⊓ u
    have hwpos : 0 ≤ w := le_inf (sub_nonneg.mpr inf_le_left) hu
    have hw_u : w ≤ u := inf_le_right
    have hw_rem : w ≤ x - x ⊓ (((n + 1 : ℕ) : ℝ) • u) := inf_le_left
    have hmono : (n : ℝ) • u ≤ ((n + 1 : ℕ) : ℝ) • u := by
      apply smul_le_smul_of_nonneg_right _ hu
      exact_mod_cast Nat.le_succ n
    have hrem : w ≤ (x - x ⊓ ((n : ℝ) • u)) ⊓ u := by
      refine le_inf ?_ hw_u
      have hinf : x ⊓ ((n : ℝ) • u) ≤ x ⊓ (((n + 1 : ℕ) : ℝ) • u) :=
        inf_le_inf_left x hmono
      exact hw_rem.trans (sub_le_sub_left hinf x)
    have hnwn : (n : ℝ) • w ≤ x := by
      have hwsm : (n : ℝ) • w ≤ (n : ℝ) • ((x - x ⊓ ((n : ℝ) • u)) ⊓ u) :=
        smul_le_smul_of_nonneg_left hrem (Nat.cast_nonneg n)
      exact hwsm.trans (ih)
    have hnu : (n : ℝ) • w ≤ ((n + 1 : ℕ) : ℝ) • u := by
      have h1 : (n : ℝ) • w ≤ (n : ℝ) • u :=
        smul_le_smul_of_nonneg_left hw_u (Nat.cast_nonneg n)
      exact h1.trans hmono
    have hna : (n : ℝ) • w ≤ x ⊓ (((n + 1 : ℕ) : ℝ) • u) := le_inf hnwn hnu
    have hsum : ((n + 1 : ℕ) : ℝ) • w = (n : ℝ) • w + w := by
      rw [Nat.cast_add_one, add_smul, one_smul]
    change ((n + 1 : ℕ) : ℝ) • w ≤ x
    rw [hsum]
    refine (add_le_add_left hna w).trans ?_
    rw [add_comm]
    exact (le_sub_iff_add_le).mp hw_rem

/-- The part of a truncation remainder carried by the unit is norm-small. -/
theorem norm_trunc_remainder_le {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) {n : ℕ} (hn : 1 ≤ n) :
    ‖(x - x ⊓ ((n : ℝ) • u)) ⊓ u‖ ≤ ‖x‖ / n := by
  set v : E := (x - x ⊓ ((n : ℝ) • u)) ⊓ u
  have hv : (n : ℝ) • v ≤ x := trunc_smul_le hu hx n
  have hv0 : 0 ≤ v := le_inf (sub_nonneg.mpr inf_le_left) hu
  have hnv0 : 0 ≤ (n : ℝ) • v := smul_nonneg (Nat.cast_nonneg n) hv0
  have hnorm : ‖(n : ℝ) • v‖ ≤ ‖x‖ := by
    apply norm_le_norm_of_abs_le_abs
    rw [abs_of_nonneg hnv0, abs_of_nonneg hx]
    exact hv
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)] at hnorm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.succ_le_iff.mp hn)
  rwa [le_div_iff₀ hn0, mul_comm]

/-- The set of admissible gauge scalars. -/
def gaugeSet (u x : E) : Set ℝ := {c : ℝ | 0 ≤ c ∧ |x| ≤ c • u}

/-- The gauge set of an ideal element is nonempty and bounded below by zero. -/
theorem gaugeSet_nonempty {u x : E} (hx : x ∈ principalOrderIdeal u) :
    (gaugeSet u x).Nonempty := by
  obtain ⟨c, hc, hx⟩ := hx
  exact ⟨c, hc, hx⟩

/-- Every gauge scalar is nonnegative. -/
theorem bddBelow_gaugeSet (u x : E) : BddBelow (gaugeSet u x) :=
  ⟨0, fun _ hc => hc.1⟩

/-- The order-unit gauge of an ideal element is nonnegative. -/
theorem gauge_nonneg {u x : E} (hx : x ∈ principalOrderIdeal u) :
    0 ≤ orderUnitGauge u x := by
  unfold orderUnitGauge
  exact le_csInf (gaugeSet_nonempty hx) fun _ hc => hc.1

/-- An admissible scalar dominates the gauge. -/
theorem gauge_le_of_mem {u x : E} {c : ℝ} (hc : c ∈ gaugeSet u x) :
    orderUnitGauge u x ≤ c := by
  unfold orderUnitGauge
  exact csInf_le (bddBelow_gaugeSet u x) hc

/-- Archimedean attainment: the absolute value is bounded by the gauge multiple. -/
theorem abs_le_gauge_smul {u x : E} (hu : 0 ≤ u) (hx : x ∈ principalOrderIdeal u) :
    |x| ≤ orderUnitGauge u x • u := by
  set p : ℝ := orderUnitGauge u x
  have hp : 0 ≤ p := gauge_nonneg hx
  let z : E := (|x| - p • u)⁺
  have hz0 : 0 ≤ z := posPart_nonneg _
  have hzε : ∀ ε : ℝ, 0 < ε → z ≤ ε • u := by
    intro ε hε
    have hnot : ¬ ∀ c ∈ gaugeSet u x, p + ε ≤ c := by
      intro hall
      have hle : p + ε ≤ p := le_csInf (gaugeSet_nonempty hx) hall
      linarith
    push Not at hnot
    obtain ⟨c, hc, hclt⟩ := hnot
    have habs : |x| ≤ c • u := hc.2
    have hcε : c • u ≤ (p + ε) • u :=
      smul_le_smul_of_nonneg_right (le_of_lt hclt) hu
    have hdiff : |x| - p • u ≤ ε • u := by
      have hsum : c • u ≤ p • u + ε • u := by
        rw [← add_smul]
        exact hcε
      exact (sub_le_sub_right (habs.trans hsum) (p • u)).trans_eq (by abel)
    have hpos : (|x| - p • u)⁺ ≤ ε • u := by
      exact sup_le hdiff (smul_nonneg hε.le hu)
    simpa [z] using hpos
  have harch : ∀ n : ℕ, (n : ℝ) • z ≤ u := by
    intro n
    cases n with
    | zero => simp [hu]
    | succ n =>
      have hε : (0 : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) :=
        one_div_pos.mpr (by exact_mod_cast Nat.succ_pos n)
      have hz := hzε _ hε
      have hmul := smul_le_smul_of_nonneg_left hz
        (Nat.cast_nonneg (α := ℝ) (n + 1))
      have hcoe : ((n + 1 : ℕ) : ℝ) * (1 / ((n + 1 : ℕ) : ℝ)) = 1 := by
        rw [mul_one_div]
        exact div_self (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
      rw [smul_smul, hcoe, one_smul] at hmul
      exact hmul
  have hzle : z ≤ 0 := archimedean_of_norm harch
  have hz : z = 0 := le_antisymm hzle hz0
  exact sub_nonpos.mp (posPart_eq_zero.mp (by simpa [z] using hz))

/-- Membership in the gauge set is equivalent to dominating the gauge, for ideal elements. -/
theorem gauge_le_iff {u x : E} (hu : 0 ≤ u) (hx : x ∈ principalOrderIdeal u) {c : ℝ}
    (hc : 0 ≤ c) : orderUnitGauge u x ≤ c ↔ |x| ≤ c • u := by
  constructor
  · intro hle
    exact (abs_le_gauge_smul hu hx).trans (smul_le_smul_of_nonneg_right hle hu)
  · intro habs
    exact gauge_le_of_mem ⟨hc, habs⟩

/-- The gauge is absolutely homogeneous on the principal ideal. -/
theorem gauge_smul {u x : E} (hu : 0 ≤ u) (hx : x ∈ principalOrderIdeal u) (c : ℝ) :
    orderUnitGauge u (c • x) = |c| * orderUnitGauge u x := by
  have hx' : c • x ∈ principalOrderIdeal u := by
    obtain ⟨d, hd, hxd⟩ := hx
    refine ⟨|c| * d, mul_nonneg (abs_nonneg c) hd, ?_⟩
    calc |c • x| = |c| • |x| := abs_smul c x
      _ ≤ |c| • (d • u) := smul_le_smul_of_nonneg_left hxd (abs_nonneg c)
      _ = (|c| * d) • u := by rw [mul_smul]
  have hp : 0 ≤ orderUnitGauge u x := gauge_nonneg hx
  have hq : 0 ≤ orderUnitGauge u (c • x) := gauge_nonneg hx'
  apply le_antisymm
  · have habs : |c • x| ≤ (|c| * orderUnitGauge u x) • u := by
      calc |c • x| = |c| • |x| := abs_smul c x
        _ ≤ |c| • (orderUnitGauge u x • u) :=
            smul_le_smul_of_nonneg_left (abs_le_gauge_smul hu hx) (abs_nonneg c)
        _ = (|c| * orderUnitGauge u x) • u := by rw [mul_smul]
    exact (gauge_le_iff hu hx' (mul_nonneg (abs_nonneg c) hp)).2 habs
  · rcases eq_or_ne c 0 with rfl | hc
    · simpa using hq
    · have habs : |x| ≤ (|c|⁻¹ * orderUnitGauge u (c • x)) • u := by
        have hback : x = c⁻¹ • c • x := by
          rw [← mul_smul, inv_mul_cancel₀ hc, one_smul]
        calc |x| = |c⁻¹ • c • x| := by rw [← hback]
          _ = |c|⁻¹ • |c • x| := by rw [abs_smul, abs_inv]
          _ ≤ |c|⁻¹ • (orderUnitGauge u (c • x) • u) :=
              smul_le_smul_of_nonneg_left (abs_le_gauge_smul hu hx') (inv_nonneg.mpr (abs_nonneg c))
          _ = (|c|⁻¹ * orderUnitGauge u (c • x)) • u := by rw [mul_smul]
      have hp' : orderUnitGauge u x ≤ |c|⁻¹ * orderUnitGauge u (c • x) :=
        (gauge_le_iff hu hx (mul_nonneg (inv_nonneg.mpr (abs_nonneg c)) hq)).2 habs
      have hmul := mul_le_mul_of_nonneg_left hp' (abs_nonneg c)
      rwa [← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hc), one_mul] at hmul

/-- The gauge is subadditive on the principal ideal. -/
theorem gauge_add {u x y : E} (hu : 0 ≤ u) (hx : x ∈ principalOrderIdeal u)
    (hy : y ∈ principalOrderIdeal u) :
    orderUnitGauge u (x + y) ≤ orderUnitGauge u x + orderUnitGauge u y := by
  have hxy : x + y ∈ principalOrderIdeal u := by
    obtain ⟨c, hc, hxc⟩ := hx
    obtain ⟨d, hd, hyd⟩ := hy
    refine ⟨c + d, add_nonneg hc hd, ?_⟩
    calc |x + y| ≤ |x| + |y| := abs_add_le x y
      _ ≤ c • u + d • u := add_le_add hxc hyd
      _ = (c + d) • u := by rw [add_smul]
  have habs : |x + y| ≤ (orderUnitGauge u x + orderUnitGauge u y) • u := by
    calc |x + y| ≤ |x| + |y| := abs_add_le x y
      _ ≤ orderUnitGauge u x • u + orderUnitGauge u y • u :=
          add_le_add (abs_le_gauge_smul hu hx) (abs_le_gauge_smul hu hy)
      _ = (orderUnitGauge u x + orderUnitGauge u y) • u := by rw [add_smul]
  exact (gauge_le_iff hu hxy (add_nonneg (gauge_nonneg hx) (gauge_nonneg hy))).2 habs

/-- The absolute value of a supremum is dominated by the supremum of the absolute values. -/
theorem abs_sup_le_sup_abs (x y : E) : |x ⊔ y| ≤ |x| ⊔ |y| := by
  refine sup_le ?_ ?_
  · exact sup_le_sup (le_abs_self x) (le_abs_self y)
  · rw [neg_sup]
    exact inf_le_left.trans ((neg_le_abs x).trans le_sup_left)

/-- The absolute value of an infimum is dominated by the supremum of the absolute values. -/
theorem abs_inf_le_sup_abs (x y : E) : |x ⊓ y| ≤ |x| ⊔ |y| := by
  rw [show x ⊓ y = -(-x ⊔ -y) by rw [← neg_inf, neg_neg], abs_neg]
  exact (abs_sup_le_sup_abs (-x) (-y)).trans (by simp [abs_neg])

/-- Nonnegative scaling preserves a principal ideal. -/
theorem principalOrderIdeal_smul {u : E} {c : ℝ} {x : E} (hx : x ∈ principalOrderIdeal u) :
    c • x ∈ principalOrderIdeal u := by
  obtain ⟨d, hd, hxd⟩ := hx
  refine ⟨|c| * d, mul_nonneg (abs_nonneg c) hd, ?_⟩
  calc |c • x| = |c| • |x| := abs_smul c x
    _ ≤ |c| • (d • u) := smul_le_smul_of_nonneg_left hxd (abs_nonneg c)
    _ = (|c| * d) • u := by rw [mul_smul]

/-- Negation preserves a principal ideal. -/
theorem principalOrderIdeal_neg {u x : E} (hx : x ∈ principalOrderIdeal u) :
    -x ∈ principalOrderIdeal u := by
  obtain ⟨c, hc, hxc⟩ := hx
  exact ⟨c, hc, by simpa [abs_neg] using hxc⟩

/-- Addition preserves a principal ideal. -/
theorem principalOrderIdeal_add {u x y : E} (hx : x ∈ principalOrderIdeal u)
    (hy : y ∈ principalOrderIdeal u) : x + y ∈ principalOrderIdeal u := by
  obtain ⟨c, hc, hxc⟩ := hx
  obtain ⟨d, hd, hyd⟩ := hy
  refine ⟨c + d, add_nonneg hc hd, ?_⟩
  calc |x + y| ≤ |x| + |y| := abs_add_le x y
    _ ≤ c • u + d • u := add_le_add hxc hyd
    _ = (c + d) • u := by rw [add_smul]

/-- Subtraction preserves a principal ideal. -/
theorem principalOrderIdeal_sub {u x y : E} (hx : x ∈ principalOrderIdeal u)
    (hy : y ∈ principalOrderIdeal u) : x - y ∈ principalOrderIdeal u := by
  simpa [sub_eq_add_neg] using principalOrderIdeal_add hx (principalOrderIdeal_neg hy)

/-- Natural scaling preserves a principal ideal. -/
theorem principalOrderIdeal_nsmul {u : E} {n : ℕ} {x : E} (hx : x ∈ principalOrderIdeal u) :
    n • x ∈ principalOrderIdeal u := by
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  exact principalOrderIdeal_smul hx

/-- Integer scaling preserves a principal ideal. -/
theorem principalOrderIdeal_zsmul {u : E} {n : ℤ} {x : E} (hx : x ∈ principalOrderIdeal u) :
    n • x ∈ principalOrderIdeal u := by
  rw [← Int.cast_smul_eq_zsmul ℝ]
  exact principalOrderIdeal_smul hx

/-- A principal ideal is closed under binary suprema. -/
theorem principalOrderIdeal_sup {u x y : E} (hx : x ∈ principalOrderIdeal u)
    (hy : y ∈ principalOrderIdeal u) : x ⊔ y ∈ principalOrderIdeal u := by
  obtain ⟨c, hc, hxc⟩ := hx
  obtain ⟨d, hd, hyd⟩ := hy
  refine ⟨c + d, add_nonneg hc hd, ?_⟩
  calc |x ⊔ y| ≤ |x| ⊔ |y| := abs_sup_le_sup_abs x y
    _ ≤ |x| + |y| :=
        sup_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
    _ ≤ c • u + d • u := add_le_add hxc hyd
    _ = (c + d) • u := by rw [add_smul]

/-- A principal ideal is closed under binary infima. -/
theorem principalOrderIdeal_inf {u x y : E} (hx : x ∈ principalOrderIdeal u)
    (hy : y ∈ principalOrderIdeal u) : x ⊓ y ∈ principalOrderIdeal u := by
  obtain ⟨c, hc, hxc⟩ := hx
  obtain ⟨d, hd, hyd⟩ := hy
  refine ⟨c + d, add_nonneg hc hd, ?_⟩
  calc |x ⊓ y| ≤ |x| ⊔ |y| := abs_inf_le_sup_abs x y
    _ ≤ |x| + |y| :=
        sup_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
    _ ≤ c • u + d • u := add_le_add hxc hyd
    _ = (c + d) • u := by rw [add_smul]

/-- Truncations of a positive vector by a weak unit converge to the vector. -/
theorem tendsto_trunc_of_weakUnit
    (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖) [CompleteSpace E]
    {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) (hweak : latticeDisjointComplement {u} ⊆ {0}) :
    Tendsto (fun n : ℕ => x ⊓ ((n : ℝ) • u)) atTop (𝓝 x) := by
  have hmono : Monotone fun n : ℕ => x ⊓ ((n : ℝ) • u) := by
    intro n m hnm
    exact inf_le_inf_left x (smul_le_smul_of_nonneg_right (by exact_mod_cast hnm) hu)
  have hpos : ∀ n : ℕ, 0 ≤ x ⊓ ((n : ℝ) • u) :=
    fun n => le_inf hx (smul_nonneg (Nat.cast_nonneg n) hu)
  have hbound : ∃ M : ℝ, ∀ n : ℕ, ‖x ⊓ ((n : ℝ) • u)‖ ≤ M := by
    refine ⟨‖x‖, fun n => ?_⟩
    apply norm_le_norm_of_abs_le_abs
    rw [abs_of_nonneg (hpos n), abs_of_nonneg hx]
    exact inf_le_left
  obtain ⟨y, hy⟩ := al_isKB hE hmono hpos hbound
  have hyx : y ≤ x :=
    (isClosed_Icc.mem_of_tendsto hy (Eventually.of_forall fun n => ⟨hpos n, inf_le_left⟩)).2
  have hzero : Tendsto (fun n : ℕ => (x - x ⊓ ((n : ℝ) • u)) ⊓ u) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (‖x‖ / ε)
    refine ⟨max N 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
    have hle := norm_trunc_remainder_le hu hx hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.succ_le_iff.mp hn1)
    have hnbig : ‖x‖ / ε < (n : ℝ) :=
      (hN.trans_le (by exact_mod_cast (le_max_left N 1).trans hn))
    have hlt : ‖x‖ / n < ε := by
      rw [div_lt_iff₀ hn0]
      rw [div_lt_iff₀ hε, mul_comm] at hnbig
      exact hnbig
    rw [dist_eq_norm, sub_zero]
    exact hle.trans_lt hlt
  have hrem : Tendsto (fun n : ℕ => (x - x ⊓ ((n : ℝ) • u)) ⊓ u) atTop (𝓝 ((x - y) ⊓ u)) := by
    have hpair : Tendsto (fun n : ℕ => (x - x ⊓ ((n : ℝ) • u), u)) atTop (𝓝 (x - y, u)) := by
      rw [nhds_prod_eq]
      have hxconst : Tendsto (fun _ : ℕ => x) atTop (𝓝 x) := tendsto_const_nhds
      have huconst : Tendsto (fun _ : ℕ => u) atTop (𝓝 u) := tendsto_const_nhds
      exact (hxconst.sub hy).prodMk huconst
    exact (continuous_inf.tendsto (x - y, u)).comp hpair
  have hinf : (x - y) ⊓ u = 0 := tendsto_nhds_unique hrem hzero
  have hdisj : x - y ∈ latticeDisjointComplement {u} := by
    intro v hv
    obtain rfl : v = u := by simpa using hv
    rw [LatticeDisjoint, abs_of_nonneg (sub_nonneg.mpr hyx), abs_of_nonneg hu, hinf]
  have hz : x - y = 0 := by simpa using hweak hdisj
  simpa [sub_eq_zero.mp hz] using hy

/-- The principal ideal of `u`, as a fresh type carrying the order-unit gauge norm. -/
@[ext]
structure OrderUnitSpace (u : E) where
  /-- Underlying vector of the ideal element. -/
  toVec : E
  /-- Witness that the vector lies in the principal ideal. -/
  mem_ideal : toVec ∈ principalOrderIdeal u

namespace OrderUnitSpace

variable {u : E}

/-- The underlying-vector map is injective. -/
theorem toVec_injective : Function.Injective (toVec : OrderUnitSpace u → E) :=
  fun _ _ h => OrderUnitSpace.ext h

instance : Zero (OrderUnitSpace u) where
  zero := ⟨0, ⟨0, le_rfl, by simp⟩⟩

instance : Add (OrderUnitSpace u) where
  add x y := ⟨x.toVec + y.toVec, principalOrderIdeal_add x.mem_ideal y.mem_ideal⟩

instance : Neg (OrderUnitSpace u) where
  neg x := ⟨-x.toVec, principalOrderIdeal_neg x.mem_ideal⟩

instance : Sub (OrderUnitSpace u) where
  sub x y := ⟨x.toVec - y.toVec, principalOrderIdeal_sub x.mem_ideal y.mem_ideal⟩

instance : SMul ℕ (OrderUnitSpace u) where
  smul n x := ⟨n • x.toVec, principalOrderIdeal_nsmul x.mem_ideal⟩

instance : SMul ℤ (OrderUnitSpace u) where
  smul n x := ⟨n • x.toVec, principalOrderIdeal_zsmul x.mem_ideal⟩

instance : SMul ℝ (OrderUnitSpace u) where
  smul c x := ⟨c • x.toVec, principalOrderIdeal_smul x.mem_ideal⟩

@[simp] theorem toVec_zero : (0 : OrderUnitSpace u).toVec = 0 := rfl

@[simp] theorem toVec_add (x y : OrderUnitSpace u) : (x + y).toVec = x.toVec + y.toVec := rfl

@[simp] theorem toVec_neg (x : OrderUnitSpace u) : (-x).toVec = -x.toVec := rfl

@[simp] theorem toVec_sub (x y : OrderUnitSpace u) : (x - y).toVec = x.toVec - y.toVec := rfl

@[simp] theorem toVec_nsmul (n : ℕ) (x : OrderUnitSpace u) : (n • x).toVec = n • x.toVec := rfl

@[simp] theorem toVec_zsmul (n : ℤ) (x : OrderUnitSpace u) : (n • x).toVec = n • x.toVec := rfl

@[simp] theorem toVec_smul (c : ℝ) (x : OrderUnitSpace u) : (c • x).toVec = c • x.toVec := rfl

instance : AddCommGroup (OrderUnitSpace u) :=
  Function.Injective.addCommGroup toVec toVec_injective rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- The underlying vector, as an additive monoid homomorphism. -/
def toVecAddMonoidHom : OrderUnitSpace u →+ E where
  toFun := toVec
  map_zero' := rfl
  map_add' := fun _ _ => rfl

instance : Module ℝ (OrderUnitSpace u) :=
  Function.Injective.module ℝ toVecAddMonoidHom toVec_injective fun _ _ => rfl

/-- Inclusion of the principal ideal into the ambient space. -/
def toVecₗ : OrderUnitSpace u →ₗ[ℝ] E where
  toFun := toVec
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

@[simp] theorem toVecₗ_apply (x : OrderUnitSpace u) : toVecₗ x = x.toVec := rfl

instance : PartialOrder (OrderUnitSpace u) where
  le x y := x.toVec ≤ y.toVec
  le_refl := fun _ => le_rfl
  le_trans := fun _ _ _ => le_trans
  le_antisymm := fun _ _ hxy hyx => OrderUnitSpace.ext (le_antisymm hxy hyx)

instance : Lattice (OrderUnitSpace u) where
  sup x y := ⟨x.toVec ⊔ y.toVec, principalOrderIdeal_sup x.mem_ideal y.mem_ideal⟩
  le_sup_left := fun _ _ => le_sup_left
  le_sup_right := fun _ _ => le_sup_right
  sup_le := fun _ _ _ hxz hyz => sup_le hxz hyz
  inf x y := ⟨x.toVec ⊓ y.toVec, principalOrderIdeal_inf x.mem_ideal y.mem_ideal⟩
  inf_le_left := fun _ _ => inf_le_left
  inf_le_right := fun _ _ => inf_le_right
  le_inf := fun _ _ _ hxy hxz => le_inf hxy hxz

@[simp] theorem toVec_sup (x y : OrderUnitSpace u) : (x ⊔ y).toVec = x.toVec ⊔ y.toVec := rfl

@[simp] theorem toVec_inf (x y : OrderUnitSpace u) : (x ⊓ y).toVec = x.toVec ⊓ y.toVec := rfl

@[simp] theorem toVec_abs (x : OrderUnitSpace u) : |x|.toVec = |x.toVec| := by
  simp [abs]

instance : IsOrderedAddMonoid (OrderUnitSpace u) where
  add_le_add_left a b hab c := by
    change (a + c).toVec ≤ (b + c).toVec
    rw [toVec_add, toVec_add]
    exact add_le_add_left (show a.toVec ≤ b.toVec from hab) c.toVec

instance : IsOrderedModule ℝ (OrderUnitSpace u) where
  smul_le_smul_of_nonneg_left a ha b₁ b₂ hb := by
    change (a • b₁).toVec ≤ (a • b₂).toVec
    rw [toVec_smul, toVec_smul]
    exact smul_le_smul_of_nonneg_left (show b₁.toVec ≤ b₂.toVec from hb) ha
  smul_le_smul_of_nonneg_right b hb a₁ a₂ ha := by
    change (a₁ • b).toVec ≤ (a₂ • b).toVec
    rw [toVec_smul, toVec_smul]
    exact smul_le_smul_of_nonneg_right (show a₁ ≤ a₂ from ha)
      (show (0 : E) ≤ b.toVec from hb)

variable [Fact (0 ≤ u)]

/-- The order unit, as an element of its principal ideal. -/
def unit : OrderUnitSpace u :=
  ⟨u, ⟨1, zero_le_one, by rw [abs_of_nonneg (Fact.out : 0 ≤ u), one_smul]⟩⟩

@[simp] theorem toVec_unit : (unit : OrderUnitSpace u).toVec = u := rfl

instance : Norm (OrderUnitSpace u) where
  norm x := orderUnitGauge u x.toVec

/-- The gauge satisfies the normed-space axioms on the principal ideal. -/
theorem core : NormedSpace.Core ℝ (OrderUnitSpace u) where
  norm_nonneg x := gauge_nonneg x.mem_ideal
  norm_smul c x := by
    simpa [norm, Real.norm_eq_abs] using gauge_smul (Fact.out : 0 ≤ u) x.mem_ideal c
  norm_triangle x y := gauge_add (Fact.out : 0 ≤ u) x.mem_ideal y.mem_ideal
  norm_eq_zero_iff x := by
    constructor
    · intro h
      have hgauge := abs_le_gauge_smul (Fact.out : 0 ≤ u) x.mem_ideal
      rw [show orderUnitGauge u x.toVec = ‖x‖ by rfl, h, zero_smul] at hgauge
      have hz : |x.toVec| = 0 := le_antisymm hgauge (abs_nonneg _)
      have hle : x.toVec ≤ 0 := by
        rw [← hz, abs]
        exact le_sup_left
      have hge : 0 ≤ x.toVec := by
        have hneg : -x.toVec ≤ 0 := by
          rw [← hz, abs]
          exact le_sup_right
        exact neg_nonpos.mp hneg
      exact OrderUnitSpace.ext (le_antisymm hle hge)
    · rintro rfl
      apply le_antisymm
      · exact gauge_le_of_mem ⟨le_rfl, by simp⟩
      · exact gauge_nonneg ⟨0, le_rfl, by simp⟩

instance : NormedAddCommGroup (OrderUnitSpace u) := NormedAddCommGroup.ofCore core

instance : NormedSpace ℝ (OrderUnitSpace u) := NormedSpace.ofCore core

instance : HasSolidNorm (OrderUnitSpace u) where
  solid x y hxy := by
    have hxy' : |x.toVec| ≤ |y.toVec| := by
      change |x|.toVec ≤ |y|.toVec at hxy
      simpa [toVec_abs] using hxy
    exact (gauge_le_iff (Fact.out : 0 ≤ u) x.mem_ideal (gauge_nonneg y.mem_ideal)).2
      (hxy'.trans (abs_le_gauge_smul (Fact.out : 0 ≤ u) y.mem_ideal))

/-- The gauge metric on a principal ideal of a Banach lattice is complete. -/
instance [CompleteSpace E] : CompleteSpace (OrderUnitSpace u) := by
  refine complete_of_cauchySeq_tendsto fun s hs => ?_
  have hu : 0 ≤ u := Fact.out
  have hmul : ∀ z : OrderUnitSpace u, ‖z.toVec‖ ≤ ‖z‖ * ‖u‖ := by
    intro z
    have hle : ‖z.toVec‖ ≤ ‖‖z‖ • u‖ := by
      apply norm_le_norm_of_abs_le_abs
      rw [abs_of_nonneg (smul_nonneg (norm_nonneg _) hu)]
      simpa [norm] using abs_le_gauge_smul hu z.mem_ideal
    rwa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hle
  have hE : CauchySeq fun n => (s n).toVec := by
    rw [Metric.cauchySeq_iff] at hs ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hs (ε / (‖u‖ + 1)) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hdist : dist (s m) (s n) < ε / (‖u‖ + 1) := hN m hm n hn
    have hle : dist (s m).toVec (s n).toVec ≤ dist (s m) (s n) * ‖u‖ := by
      rw [dist_eq_norm, dist_eq_norm]
      exact hmul (s m - s n)
    have hcmp : (ε / (‖u‖ + 1)) * ‖u‖ ≤ ε := by
      calc (ε / (‖u‖ + 1)) * ‖u‖ ≤ (ε / (‖u‖ + 1)) * (‖u‖ + 1) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (by positivity)
        _ = ε := by rw [div_mul_cancel₀ _ (by positivity)]
    by_cases hu0 : ‖u‖ = 0
    · have hzero : dist (s m).toVec (s n).toVec ≤ 0 := by simpa [hu0] using hle
      exact (le_antisymm hzero (dist_nonneg)).trans_lt hε
    · exact (hle.trans_lt (mul_lt_mul_of_pos_right hdist
        (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu0)))).trans_le hcmp
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hE
  rw [Metric.cauchySeq_iff] at hs
  have hclose : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m, N ≤ m → |(s m).toVec - y| ≤ ε • u := by
    intro ε hε
    obtain ⟨N, hN⟩ := hs ε hε
    refine ⟨N, fun m hm => ?_⟩
    have htail : ∀ n, N ≤ n → (s n).toVec ∈ Icc ((s m).toVec - ε • u) ((s m).toVec + ε • u) := by
      intro n hn
      have hdist : dist (s m) (s n) < ε := hN m hm n hn
      have hgauge : ‖s m - s n‖ < ε := by rwa [dist_eq_norm] at hdist
      have habs : |(s m).toVec - (s n).toVec| ≤ ‖s m - s n‖ • u :=
        abs_le_gauge_smul hu (s m - s n).mem_ideal
      have hle : |(s m).toVec - (s n).toVec| ≤ ε • u :=
        habs.trans (smul_le_smul_of_nonneg_right (le_of_lt hgauge) hu)
      rw [abs_le'] at hle
      constructor
      · rw [sub_le_iff_le_add]
        exact (sub_le_iff_le_add').mp hle.1
      · simp only [neg_sub] at hle
        exact (sub_le_iff_le_add').mp hle.2
    have hyI := isClosed_Icc.mem_of_tendsto hy
      (eventually_atTop.2 ⟨N, fun n hn => htail n hn⟩)
    rw [mem_Icc] at hyI
    rw [abs_le']
    constructor
    · rw [sub_le_iff_le_add']
      exact (sub_le_iff_le_add).mp hyI.1
    · simp only [neg_sub]
      rw [sub_le_iff_le_add']
      exact hyI.2
  have hyideal : y ∈ principalOrderIdeal u := by
    obtain ⟨N, hN⟩ := hclose 1 zero_lt_one
    have hdiff : (s N).toVec - y ∈ principalOrderIdeal u :=
      ⟨1, zero_le_one, by simpa [one_smul] using hN N le_rfl⟩
    have hyeq : y = (s N).toVec - ((s N).toVec - y) := by abel
    rw [hyeq]
    exact principalOrderIdeal_sub (s N).mem_ideal hdiff
  refine ⟨⟨y, hyideal⟩, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hclose (ε / 2) (half_pos hε)
  refine ⟨N, fun m hm => ?_⟩
  rw [dist_eq_norm]
  have hgauge : orderUnitGauge u ((s m).toVec - y) ≤ ε / 2 :=
    (gauge_le_iff hu (principalOrderIdeal_sub (s m).mem_ideal hyideal) (half_pos hε).le).2
      (hN m hm)
  change orderUnitGauge u ((s m - ⟨y, hyideal⟩).toVec) < ε
  exact hgauge.trans_lt (half_lt_self hε)

/-- The closed gauge ball is the order interval of the unit. -/
theorem ball_eq_Icc : closedBall (0 : OrderUnitSpace u) 1 = Icc (-unit) unit := by
  ext x
  rw [mem_closedBall_iff_norm, sub_zero]
  change orderUnitGauge u x.toVec ≤ 1 ↔ -unit ≤ x ∧ x ≤ unit
  rw [gauge_le_iff (Fact.out : 0 ≤ u) x.mem_ideal zero_le_one, one_smul, abs_le']
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · change (-unit).toVec ≤ x.toVec
      rw [toVec_neg, toVec_unit]
      exact (neg_le_neg h.2).trans_eq (by simp)
    · change x.toVec ≤ unit.toVec
      rw [toVec_unit]
      exact h.1
  · intro h
    refine ⟨?_, ?_⟩
    · have hx : x.toVec ≤ unit.toVec := h.2
      rwa [toVec_unit] at hx
    · change -x.toVec ≤ u
      have hx : (-unit).toVec ≤ x.toVec := h.1
      rw [toVec_neg, toVec_unit] at hx
      exact (neg_le_neg hx).trans_eq (by simp)

/-- The order unit is positive. -/
theorem unit_nonneg : 0 ≤ (unit : OrderUnitSpace u) := by
  change (0 : OrderUnitSpace u).toVec ≤ unit.toVec
  rw [toVec_zero, toVec_unit]
  exact Fact.out

end OrderUnitSpace

/-- A weak unit's principal ideal is dense for the ambient norm. -/
theorem denseRange_orderUnit
    (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖) [CompleteSpace E] {u : E}
    (hu : 0 ≤ u) (hweak : latticeDisjointComplement {u} ⊆ {0}) :
    DenseRange (OrderUnitSpace.toVecₗ (u := u)) := by
  let : Fact (0 ≤ u) := ⟨hu⟩
  intro x
  have hpos := tendsto_trunc_of_weakUnit hE hu (posPart_nonneg x) hweak
  have hneg := tendsto_trunc_of_weakUnit hE hu (negPart_nonneg x) hweak
  let s : ℕ → OrderUnitSpace u := fun n =>
    ⟨x⁺ ⊓ ((n : ℝ) • u) - (x⁻ ⊓ ((n : ℝ) • u)), by
      apply principalOrderIdeal_sub
      · refine ⟨(n : ℝ), Nat.cast_nonneg n, ?_⟩
        rw [abs_of_nonneg (le_inf (posPart_nonneg x) (smul_nonneg (Nat.cast_nonneg n) hu))]
        exact inf_le_right
      · refine ⟨(n : ℝ), Nat.cast_nonneg n, ?_⟩
        rw [abs_of_nonneg (le_inf (negPart_nonneg x) (smul_nonneg (Nat.cast_nonneg n) hu))]
        exact inf_le_right⟩
  have hlim : Tendsto (fun n => (s n).toVec) atTop (𝓝 x) := by
    have hsub := hpos.sub hneg
    rw [posPart_sub_negPart] at hsub
    simpa [s] using hsub
  exact mem_closure_of_tendsto hlim
    (Eventually.of_forall fun n => ⟨s n, by simp [OrderUnitSpace.toVecₗ]⟩)

/-- An AL-space with a weak unit is lattice isometric to a real L¹ space. -/
theorem exists_al_representation_of_weakUnit
    (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖) [CompleteSpace E] {u : E}
    (hu : 0 ≤ u) (hweak : latticeDisjointComplement {u} ⊆ {0}) :
    ∃ (X : Type u) (_ : MeasurableSpace X) (μ : Measure X) (U : E ≃ₗᵢ[ℝ] Lp ℝ 1 μ),
      ∀ x y, U (x ⊔ y) = U x ⊔ U y := by
  classical
  let : Fact (0 ≤ u) := ⟨hu⟩
  let F := OrderUnitSpace u
  let e0 : F := OrderUnitSpace.unit
  have he0 : 0 ≤ e0 := OrderUnitSpace.unit_nonneg
  have hball : closedBall (0 : F) 1 = Icc (-e0) e0 := OrderUnitSpace.ball_eq_Icc
  obtain ⟨K, V, -, hsup⟩ := exists_am_representation (E := F) he0 hball
  borelize (K : Type u)
  let ι : F →ₗ[ℝ] E := OrderUnitSpace.toVecₗ
  let lev : C(K, ℝ) →ₗ[ℝ] ℝ :=
    (alNormFunctional hE).comp (ι.comp V.symm.toLinearEquiv.toLinearMap)
  let cc : C_c(K, ℝ) →ₗ[ℝ] C(K, ℝ) :=
    { toFun := fun f => f.toContinuousMap
      map_add' := fun _ _ => by ext; simp
      map_smul' := fun _ _ => by ext; simp [smul_eq_mul] }
  have hlev_nonneg : ∀ g : C(K, ℝ), 0 ≤ g → 0 ≤ lev g := by
    intro g hg
    let y : F := V.symm g
    have hy : 0 ≤ y := by
      have hy0 : y ⊔ 0 = y := by
        apply V.injective
        rw [hsup, map_zero, V.apply_symm_apply]
        exact sup_eq_left.mpr hg
      rw [sup_comm] at hy0
      exact sup_eq_right.mp hy0
    have hpos : 0 ≤ ι y := by
      change (0 : F).toVec ≤ y.toVec at hy
      change 0 ≤ y.toVec
      rw [OrderUnitSpace.toVec_zero] at hy
      exact hy
    rw [show lev g = alNormFunctional hE (ι y) by rfl]
    rw [alNormFunctional_apply_nonneg hE hpos]
    exact norm_nonneg _
  let Λ : C_c(K, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ (lev.comp cc) fun g hg => by
    apply hlev_nonneg
    rw [ContinuousMap.le_def]
    intro t
    exact hg t
  let μ : Measure K := RealRMK.rieszMeasure Λ
  let : Fact (1 ≤ (1 : ENNReal)) := ⟨le_rfl⟩
  have hintegral : ∀ g : C(K, ℝ), ∫ t, g t ∂μ = lev g := by
    intro g
    have hri := RealRMK.integral_rieszMeasure (Λ := Λ)
      (CompactlySupportedContinuousMap.continuousMapEquiv g)
    have hcoe : (fun t => (CompactlySupportedContinuousMap.continuousMapEquiv g) t) =
        fun t => g t := by
      ext t
      simp [CompactlySupportedContinuousMap.continuousMapEquiv]
    have hΛ : Λ (CompactlySupportedContinuousMap.continuousMapEquiv g) = lev g := by
      change lev (cc (CompactlySupportedContinuousMap.continuousMapEquiv g)) = lev g
      congr 1
    simpa [μ, hcoe] using hri.trans hΛ
  let fLp : F →ₗ[ℝ] Lp ℝ 1 μ :=
    (ContinuousMap.toLp (E := ℝ) (1 : ENNReal) μ ℝ).toLinearMap.comp V.toLinearEquiv.toLinearMap
  have hnorm : ∀ x : F, ‖fLp x‖ = ‖ι x‖ := by
    intro x
    have hmeas : AEStronglyMeasurable (fun t => (V x) t) μ :=
      (V x).continuous.aestronglyMeasurable
    rw [show fLp x = ContinuousMap.toLp (1 : ENNReal) μ ℝ (V x) by rfl, Lp.norm_def,
      eLpNorm_congr_ae (ContinuousMap.coeFn_toLp (p := (1 : ENNReal)) (μ := μ) (𝕜 := ℝ) (V x)),
      eLpNorm_one_eq_lintegral_enorm hmeas, ← integral_norm_eq_lintegral_enorm hmeas]
    have habsV : |V x| = V |x| := by
      simpa [abs, map_neg] using (hsup x (-x)).symm
    have hint : ∫ t, ‖(V x) t‖ ∂μ = alNormFunctional hE (ι |x|) := by
      have hfun : (fun t => ‖(V x) t‖) = fun t => (|V x|) t := by
        ext t
        rw [Real.norm_eq_abs]
        simp [abs, ContinuousMap.sup_apply]
      rw [hfun, habsV, hintegral]
      change (alNormFunctional hE) (ι (V.symm (V |x|))) = (alNormFunctional hE) (ι |x|)
      rw [V.symm_apply_apply]
    rw [hint]
    change (alNormFunctional hE) |x.toVec| = ‖x.toVec‖
    exact alNormFunctional_abs hE x.toVec
  have hdense : DenseRange ι := denseRange_orderUnit hE hu hweak
  let T := fLp.extendOfIsometry (e := ι) hdense hnorm
  have hclosed : IsClosed (Set.range (⇑T)) :=
    T.antilipschitzWith.isClosed_range T.lipschitzWith.uniformContinuous
  have htoLp_dense : DenseRange (ContinuousMap.toLp (E := ℝ) (1 : ENNReal) μ ℝ) :=
    ContinuousMap.toLp_denseRange ℝ μ ℝ ENNReal.one_ne_top
  have hsub : Set.range (ContinuousMap.toLp (E := ℝ) (1 : ENNReal) μ ℝ) ⊆ Set.range (⇑T) := by
    intro z hz
    rcases hz with ⟨g, rfl⟩
    obtain ⟨x, rfl⟩ := V.surjective g
    exact ⟨ι x, by rw [LinearMap.extendOfIsometry_eq]; rfl⟩
  have hpres : ∀ a b : F, fLp (a ⊔ b) = fLp a ⊔ fLp b := by
    intro a b
    apply Lp.ext
    filter_upwards [ContinuousMap.coeFn_toLp (p := (1 : ENNReal)) (μ := μ) (𝕜 := ℝ) (V (a ⊔ b)),
      ContinuousMap.coeFn_toLp (p := (1 : ENNReal)) (μ := μ) (𝕜 := ℝ) (V a),
      ContinuousMap.coeFn_toLp (p := (1 : ENNReal)) (μ := μ) (𝕜 := ℝ) (V b),
      Lp.coeFn_sup (fLp a) (fLp b)] with t h1 h2 h3 h4
    have hfa : fLp (a ⊔ b) = ContinuousMap.toLp (1 : ENNReal) μ ℝ (V (a ⊔ b)) := by
      simp [fLp, LinearMap.comp_apply]
    have hfb : fLp a = ContinuousMap.toLp (1 : ENNReal) μ ℝ (V a) := by
      simp [fLp, LinearMap.comp_apply]
    have hfc : fLp b = ContinuousMap.toLp (1 : ENNReal) μ ℝ (V b) := by
      simp [fLp, LinearMap.comp_apply]
    rw [hfa, h1, h4, hfb, hfc, Pi.sup_apply, h2, h3, hsup, ContinuousMap.sup_apply]
  have hsurj : Function.Surjective (⇑T) := by
    intro z
    have hz : z ∈ closure (Set.range (ContinuousMap.toLp (E := ℝ) (1 : ENNReal) μ ℝ)) :=
      htoLp_dense z
    simpa [Set.mem_range] using closure_minimal hsub hclosed hz
  have hTsup : ∀ a b : E, T (a ⊔ b) = T a ⊔ T b := by
    intro a b
    obtain ⟨fa, hfa, hlima⟩ := mem_closure_iff_seq_limit.mp (hdense a)
    obtain ⟨fb, hfb, hlimb⟩ := mem_closure_iff_seq_limit.mp (hdense b)
    choose ga hga using fun n => hfa n
    choose gb hgb using fun n => hfb n
    have hlimga : Tendsto (fun n => ι (ga n)) atTop (𝓝 a) := by simpa [hga] using hlima
    have hlimgb : Tendsto (fun n => ι (gb n)) atTop (𝓝 b) := by simpa [hgb] using hlimb
    have hsuplim : Tendsto (fun n => ι (ga n) ⊔ ι (gb n)) atTop (𝓝 (a ⊔ b)) := by
      have hpairι : Tendsto (fun n => (ι (ga n), ι (gb n))) atTop (𝓝 (a, b)) := by
        rw [nhds_prod_eq]
        exact hlimga.prodMk hlimgb
      exact (continuous_sup.tendsto (a, b)).comp hpairι
    have heq : ∀ n, ι (ga n) ⊔ ι (gb n) = ι (ga n ⊔ gb n) := by
      intro n
      change (ga n).toVec ⊔ (gb n).toVec = (ga n ⊔ gb n).toVec
      exact (OrderUnitSpace.toVec_sup (ga n) (gb n)).symm
    have hTeq : ∀ n, T (ι (ga n) ⊔ ι (gb n)) = T (ι (ga n)) ⊔ T (ι (gb n)) := by
      intro n
      rw [heq, LinearMap.extendOfIsometry_eq, LinearMap.extendOfIsometry_eq,
        LinearMap.extendOfIsometry_eq, hpres]
    have hTlim : Tendsto (fun n => T (ι (ga n) ⊔ ι (gb n))) atTop (𝓝 (T (a ⊔ b))) :=
      (T.continuous.tendsto (a ⊔ b)).comp hsuplim
    have hpair : Tendsto (fun n => (T (ι (ga n)), T (ι (gb n)))) atTop (𝓝 (T a, T b)) := by
      rw [nhds_prod_eq]
      exact ((T.continuous.tendsto a).comp hlimga).prodMk ((T.continuous.tendsto b).comp hlimgb)
    have hTsuplim : Tendsto (fun n => T (ι (ga n)) ⊔ T (ι (gb n))) atTop (𝓝 (T a ⊔ T b)) :=
      (continuous_sup.tendsto (T a, T b)).comp hpair
    exact tendsto_nhds_unique (hTlim.congr fun n => hTeq n) hTsuplim
  refine ⟨(K : Type u), inferInstance, μ, LinearIsometryEquiv.ofSurjective T hsurj, ?_⟩
  intro a b
  simpa [LinearIsometryEquiv.coe_ofSurjective] using hTsup a b

end CKMA
