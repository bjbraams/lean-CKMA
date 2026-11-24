/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.OrderedSpace.Representation.AL.OrderUnit
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import CKMA.Analysis.OrderedSpace.Representation.AM
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Kakutani representation of an AL-space with a weak unit

An AL-space has additive norm on the positive cone. The AL-norm functional extends that norm.
Truncations by a weak unit converge, and the principal ideal of a weak unit is dense.
That ideal, renormed by the order-unit gauge, is built in
`CKMA.Analysis.OrderedSpace.Representation.AL.OrderUnit` and is an AM-space with the weak unit
as order unit. The Riesz–Markov measure of the AL-norm functional makes the inclusion of the
ideal into `L¹` an isometry for the original norm.
Sources: GAPS 19.29; Aliprantis–Burkinshaw, Theorem 4.27; Schaefer, Theorem II.8.5.

## Main definitions

* `CKMA.alNormFunctional`: linear functional extending the norm on the positive cone of an
  AL-space.

## Main results

* `CKMA.exists_tendsto_of_monotone_of_norm_add_eq`: monotone completeness from the AL identity.
* `CKMA.norm_sum_of_pairwise_latticeDisjoint`: the norm adds on pairwise disjoint finite sums.
* `CKMA.tendsto_trunc_of_weakUnit`: truncations against a weak unit converge in norm.
* `CKMA.denseRange_orderUnit`: the principal ideal of a weak unit is norm-dense.
* `CKMA.exists_al_representation_of_weakUnit`: an AL-space with a weak unit is lattice isometric
  to a real `L¹` space.
-/

public section

noncomputable section

open Set Metric Filter Topology MeasureTheory
open scoped CompactlySupported

namespace CKMA

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E]
  [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]

omit [NormedSpace ℝ E] [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- Sequential monotone completeness of an AL-space: in a complete normed lattice whose norm
is additive on the positive cone, a monotone, nonnegative, norm-bounded sequence converges. -/
theorem exists_tendsto_of_monotone_of_norm_add_eq
    (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
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


@[deprecated (since := "2026-11-15")]
alias al_isKB := exists_tendsto_of_monotone_of_norm_add_eq

/-- The additive norm of an AL-space, extended from the positive cone. -/
@[expose]
def alNormFunctional (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖) :
    E →ₗ[ℝ] ℝ :=
  coneAdditiveLinearMap (fun x => ‖x‖)
    (fun x y hx hy => hE x y hx hy)
    (fun c x hc _hx => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, smul_eq_mul])

omit [HasSolidNorm E] in
/-- On the positive cone the AL-norm functional is the ambient norm. -/
private theorem alNormFunctional_apply_nonneg
    (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    {x : E} (hx : 0 ≤ x) : alNormFunctional hE x = ‖x‖ :=
  coneAdditiveLinearMap_apply_of_nonneg _ _ _ hx

/-- The AL-norm functional reproduces the norm on absolute values. -/
private theorem alNormFunctional_abs
    (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖) (x : E) :
    alNormFunctional hE |x| = ‖x‖ := by
  rw [alNormFunctional_apply_nonneg hE (abs_nonneg x), norm_abs_eq_norm]

omit [HasSolidNorm E] in
/-- The AL-norm functional is monotone. -/
private theorem alNormFunctional_mono
    (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖) :
    Monotone (alNormFunctional hE) := by
  intro a b hab
  have hdiff : 0 ≤ b - a := sub_nonneg.mpr hab
  have hsub : alNormFunctional hE b - alNormFunctional hE a =
      alNormFunctional hE (b - a) := by
    rw [← map_sub]
  rw [← sub_nonneg, hsub, alNormFunctional_apply_nonneg hE hdiff]
  exact norm_nonneg _

omit [NormedSpace ℝ E] [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- Positive parts of disjoint vectors remain disjoint. -/
private theorem posPart_inf_posPart_eq_zero_of_disjoint {x y : E} (h : LatticeDisjoint x y) :
    x⁺ ⊓ y⁺ = 0 := by
  apply le_antisymm
  · calc x⁺ ⊓ y⁺ ≤ |x| ⊓ |y| :=
        inf_le_inf (sup_le (le_abs_self x) (abs_nonneg x))
          (sup_le (le_abs_self y) (abs_nonneg y))
    _ = 0 := h
  · exact le_inf (posPart_nonneg x) (posPart_nonneg y)

omit [NormedSpace ℝ E] [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- Absolute values add when the vectors are lattice disjoint. -/
private theorem abs_add_of_latticeDisjoint {x y : E} (h : LatticeDisjoint x y) :
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
  have hsplit := eq_posPart_negPart_of_inf_eq_zero hcross hdiff
  calc |x + y| = (x + y)⁺ + (x + y)⁻ := by rw [← posPart_add_negPart]
    _ = (x⁺ + y⁺) + (x⁻ + y⁻) := by rw [hsplit.1, hsplit.2]
    _ = (x⁺ + x⁻) + (y⁺ + y⁻) := by abel
    _ = |x| + |y| := by rw [posPart_add_negPart, posPart_add_negPart]

omit [NormedSpace ℝ E] [IsOrderedModule ℝ E] [HasSolidNorm E] in
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

omit [NormedSpace ℝ E] [IsOrderedModule ℝ E] in
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

omit [HasSolidNorm E] in
/-- Scalar truncation of the remainder meets the unit in a vector dominated by `x`. -/
private theorem trunc_smul_le {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) (n : ℕ) :
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
  obtain ⟨y, hy⟩ := exists_tendsto_of_monotone_of_norm_add_eq hE hmono hpos hbound
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
