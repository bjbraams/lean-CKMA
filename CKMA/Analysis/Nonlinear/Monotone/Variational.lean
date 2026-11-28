/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Topology.Bornology.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.Map
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Sequences
import CKMA.Analysis.Nonlinear.FixedPoint
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact

/-!
# Variational inequalities for monotone dual maps

Browder–Minty surjectivity and variational inequalities for a monotone, hemicontinuous operator
`A : E → E*` on a real Banach space that sends bounded sets to bounded sets. Monotonicity,
hemicontinuity, boundedness on bounded sets and coercivity are expressed in the dual pairing.
Reflexivity is surjectivity of the canonical bidual inclusion; it implies completeness
(`TauCeti.completeSpace_of_surjective_inclusionInDoubleDual`), so no completeness hypothesis is
taken. Finite-dimensional approximations use the Brouwer simplex lemma
`CKMA.exists_forall_nonneg_of_sum_mul_nonneg`. The limit uses weak compactness of closed bounded
convex sets, `TauCeti.isCompact_toWeakSpace_of_isClosed_of_convex_of_isBounded`, and Minty's trick.
Sources: GAPS 35.40 and 35.45.

## Main definitions

* `CKMA.IsMonotoneDualMap`: Monotonicity for a map into the continuous dual.
* `CKMA.IsStrictlyMonotoneDualMap`: Strict monotonicity in the dual pairing.
* `CKMA.IsHemicontinuousDualMap`: Hemicontinuity along line segments.
* `CKMA.MapsBoundedSetsToBoundedSets`: Boundedness on bounded sets.
* `CKMA.IsCoerciveDualMap`: Coercivity in the dual pairing at infinity.
* `CKMA.SolvesVariationalInequality`: Solution predicate for a variational inequality on `C`.
* `CKMA.IsCoerciveOnAt`: Coercivity relative to a feasible point of a constraint set.

## Main results

* `CKMA.IsStrictlyMonotoneDualMap.injective`: Injectivity of strictly monotone dual maps.
* `CKMA.exists_solution_variationalInequality`: Bounded-domain variational inequality existence
  (**35.45**).
* `CKMA.exists_solution_variationalInequality_of_coercive`: Unbounded-domain coercive variational
  inequality existence.
* `CKMA.IsMonotoneDualMap.surjective`: Browder–Minty surjectivity for monotone operators on
  reflexive Banach spaces (**35.40**).
-/

public section

noncomputable section

namespace CKMA

open Bornology Filter Function Metric Set Submodule Topology

section Banach

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Monotonicity for a map taking values in the continuous dual. -/
@[expose]
def IsMonotoneDualMap (A : E → StrongDual ℝ E) : Prop :=
  ∀ x y, 0 ≤ (A x - A y) (x - y)

/-- Strict monotonicity in the dual pairing. -/
@[expose]
def IsStrictlyMonotoneDualMap (A : E → StrongDual ℝ E) : Prop :=
  ∀ x y, x ≠ y → 0 < (A x - A y) (x - y)

/-- Hemicontinuity means continuity of every dual evaluation along each line segment. -/
@[expose]
def IsHemicontinuousDualMap (A : E → StrongDual ℝ E) : Prop :=
  ∀ x y z, ContinuousOn (fun t : ℝ ↦ A (x + t • y) z) (Set.Icc 0 1)

/-- Boundedness on bounded sets, without assuming global boundedness. -/
@[expose]
def MapsBoundedSetsToBoundedSets (A : E → StrongDual ℝ E) : Prop :=
  ∀ C : Set E, Bornology.IsBounded C → Bornology.IsBounded (A '' C)

/-- Coercivity in the dual pairing as the norm tends to infinity, along `cobounded E`.
The ratio is totalized at zero, which does not affect this filter. -/
@[expose]
def IsCoerciveDualMap (A : E → StrongDual ℝ E) : Prop :=
  Tendsto (fun x ↦ A x x / ‖x‖) (cobounded E) atTop

/-- A variational inequality on `C` at forcing `f`. -/
@[expose]
def SolvesVariationalInequality (A : E → StrongDual ℝ E) (C : Set E)
    (f : StrongDual ℝ E) (u : E) : Prop :=
  u ∈ C ∧ ∀ v ∈ C, 0 ≤ (A u - f) (v - u)

/-- Coercivity relative to a point of an unbounded constraint set. -/
@[expose]
def IsCoerciveOnAt (A : E → StrongDual ℝ E) (C : Set E)
    (f : StrongDual ℝ E) (u₀ : E) : Prop :=
  Tendsto (fun u ↦ (A u - f) (u - u₀) / ‖u‖) (cobounded E ⊓ 𝓟 C) atTop

/-- Defining property of `IsMonotoneDualMap`. -/
theorem isMonotoneDualMap_iff {A : E → StrongDual ℝ E} :
    IsMonotoneDualMap A ↔ ∀ x y, 0 ≤ (A x - A y) (x - y) := Iff.rfl

/-- Defining property of `IsStrictlyMonotoneDualMap`. -/
theorem isStrictlyMonotoneDualMap_iff {A : E → StrongDual ℝ E} :
    IsStrictlyMonotoneDualMap A ↔ ∀ x y, x ≠ y → 0 < (A x - A y) (x - y) := Iff.rfl

/-- A strictly monotone dual map is monotone. -/
theorem IsStrictlyMonotoneDualMap.isMonotoneDualMap {A : E → StrongDual ℝ E}
    (hA : IsStrictlyMonotoneDualMap A) : IsMonotoneDualMap A := by
  intro x y
  rcases eq_or_ne x y with rfl | hxy
  · simp
  · exact (hA x y hxy).le

/-- Defining property of `IsHemicontinuousDualMap`. -/
theorem isHemicontinuousDualMap_iff {A : E → StrongDual ℝ E} :
    IsHemicontinuousDualMap A ↔
      ∀ x y z, ContinuousOn (fun t : ℝ ↦ A (x + t • y) z) (Set.Icc 0 1) := Iff.rfl

/-- Defining property of `MapsBoundedSetsToBoundedSets`. -/
theorem mapsBoundedSetsToBoundedSets_iff {A : E → StrongDual ℝ E} :
    MapsBoundedSetsToBoundedSets A ↔
      ∀ C : Set E, Bornology.IsBounded C → Bornology.IsBounded (A '' C) := Iff.rfl

/-- Defining property of `IsCoerciveDualMap`. -/
theorem isCoerciveDualMap_iff {A : E → StrongDual ℝ E} :
    IsCoerciveDualMap A ↔ Tendsto (fun x ↦ A x x / ‖x‖) (cobounded E) atTop := Iff.rfl

/-- Defining property of `SolvesVariationalInequality`. -/
theorem solvesVariationalInequality_iff {A : E → StrongDual ℝ E} {C : Set E}
    {f : StrongDual ℝ E} {u : E} :
    SolvesVariationalInequality A C f u ↔ u ∈ C ∧ ∀ v ∈ C, 0 ≤ (A u - f) (v - u) := Iff.rfl

/-- Defining property of `IsCoerciveOnAt`. -/
theorem isCoerciveOnAt_iff {A : E → StrongDual ℝ E} {C : Set E}
    {f : StrongDual ℝ E} {u₀ : E} :
    IsCoerciveOnAt A C f u₀ ↔
      Tendsto (fun u ↦ (A u - f) (u - u₀) / ‖u‖) (cobounded E ⊓ 𝓟 C) atTop := Iff.rfl

/-- A strictly monotone dual map is injective. -/
theorem IsStrictlyMonotoneDualMap.injective {A : E → StrongDual ℝ E}
    (hA : IsStrictlyMonotoneDualMap A) : Function.Injective A := by
  intro x y hxy
  by_contra hne
  have h := hA x y hne
  simp [hxy] at h

/-- A coercive ratio eventually dominates any linear lower bound outside a ball. -/
private theorem IsCoerciveDualMap.exists_radius {A : E → StrongDual ℝ E}
    (hc : IsCoerciveDualMap A) (M : ℝ) :
    ∃ R, 0 < R ∧ ∀ x, R ≤ ‖x‖ → M * ‖x‖ ≤ A x x := by
  rw [IsCoerciveDualMap, ← comap_norm_atTop, Filter.tendsto_atTop] at hc
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp (eventually_comap.mp (hc M))
  refine ⟨max R0 1, lt_max_of_lt_right zero_lt_one, fun x hx ↦ ?_⟩
  have hxpos : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hx)
  have hdiv : M ≤ A x x / ‖x‖ := hR0 ‖x‖ ((le_max_left _ _).trans hx) x rfl
  exact (le_div_iff₀ hxpos).mp hdiv

/-- Coercivity on `C` dominates any linear bound for all large feasible points. -/
private theorem IsCoerciveOnAt.exists_radius {A : E → StrongDual ℝ E} {C : Set E}
    {f : StrongDual ℝ E} {u₀ : E} (hc : IsCoerciveOnAt A C f u₀) (M : ℝ) :
    ∃ R, 0 < R ∧ ∀ u ∈ C, R ≤ ‖u‖ → M * ‖u‖ ≤ (A u - f) (u - u₀) := by
  rw [IsCoerciveOnAt, ← comap_norm_atTop, Filter.tendsto_atTop] at hc
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp
    (eventually_comap.mp (eventually_inf_principal.mp (hc M)))
  refine ⟨max R0 1, lt_max_of_lt_right zero_lt_one, fun u hu hnorm ↦ ?_⟩
  have hpos : 0 < ‖u‖ := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hnorm)
  have hdiv : M ≤ (A u - f) (u - u₀) / ‖u‖ :=
    hR0 ‖u‖ ((le_max_left _ _).trans hnorm) u rfl hu
  exact (le_div_iff₀ hpos).mp hdiv

/-- Parameter in `(0, 1]` tending to zero along the naturals. -/
private def segmentParam (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- Each segment parameter is positive. -/
private theorem segmentParam_pos (n : ℕ) : 0 < segmentParam n := by
  unfold segmentParam
  exact div_pos zero_lt_one (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one)

/-- Each segment parameter is at most one. -/
private theorem segmentParam_le_one (n : ℕ) : segmentParam n ≤ 1 := by
  unfold segmentParam
  rw [div_le_one (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one)]
  linarith

/-- Each segment parameter lies in the half-open unit interval. -/
private theorem segmentParam_mem_Ioc (n : ℕ) : segmentParam n ∈ Ioc 0 1 :=
  ⟨segmentParam_pos n, segmentParam_le_one n⟩

/-- The segment parameters tend to zero. -/
private theorem tendsto_segmentParam_zero : Tendsto segmentParam atTop (𝓝 0) := by
  unfold segmentParam
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Hemicontinuity passes scalar pairings to the base point of a segment. -/
private theorem IsHemicontinuousDualMap.tendsto_segmentParam
    {A : E → StrongDual ℝ E} (hh : IsHemicontinuousDualMap A) (x y z : E) :
    Tendsto (fun n ↦ A (x + segmentParam n • y) z) atTop (𝓝 (A x z)) := by
  have hcont := (hh x y z 0 ⟨le_rfl, zero_le_one⟩).tendsto
  have hseg : Tendsto segmentParam atTop (𝓝[Icc 0 1] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_segmentParam_zero,
      Eventually.of_forall fun n ↦ Ioc_subset_Icc_self (segmentParam_mem_Ioc n)⟩
  simpa [zero_smul, add_zero, Function.comp_def] using hcont.comp hseg

/-- An affine combination, rewritten from its first endpoint. -/
private theorem segment_eq (u v : E) (t : ℝ) : (1 - t) • u + t • v = u + t • (v - u) := by
  rw [← AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module']
  abel

/-- Displacement along a segment is the scaled direction. -/
private theorem segment_sub (u v : E) (t : ℝ) :
    ((1 - t) • u + t • v) - u = t • (v - u) := by
  rw [segment_eq, add_sub_cancel_left]

/-- Minty's inequality and hemicontinuity give the variational inequality. -/
private theorem SolvesVariationalInequality.of_minty {A : E → StrongDual ℝ E}
    (hh : IsHemicontinuousDualMap A) {C : Set E} (hC : Convex ℝ C)
    {f : StrongDual ℝ E} {u : E} (hu : u ∈ C)
    (hminty : ∀ v ∈ C, 0 ≤ (A v - f) (v - u)) :
    SolvesVariationalInequality A C f u := by
  refine ⟨hu, fun w hw ↦ ?_⟩
  have hmem : ∀ n, (1 - segmentParam n) • u + segmentParam n • w ∈ C := by
    intro n
    apply (convex_iff_add_mem.mp hC) hu hw
    · exact sub_nonneg.mpr (segmentParam_le_one n)
    · exact (segmentParam_pos n).le
    · exact sub_add_cancel 1 (segmentParam n)
  have hgap : ∀ n, 0 ≤
      (A ((1 - segmentParam n) • u + segmentParam n • w) - f) (w - u) := by
    intro n
    let v := (1 - segmentParam n) • u + segmentParam n • w
    have hpair : 0 ≤ (A v - f) (v - u) := hminty v (hmem n)
    rw [segment_sub, map_smul, smul_eq_mul] at hpair
    exact nonneg_of_mul_nonneg_right hpair (segmentParam_pos n)
  have hlim : Tendsto (fun n ↦
      A (u + segmentParam n • (w - u)) (w - u) - f (w - u)) atTop
      (𝓝 (A u (w - u) - f (w - u))) :=
    (hh.tendsto_segmentParam u (w - u) (w - u)).sub tendsto_const_nhds
  have hlim' : Tendsto (fun n ↦
      (A ((1 - segmentParam n) • u + segmentParam n • w) - f) (w - u)) atTop
      (𝓝 ((A u - f) (w - u))) := by
    simp_rw [segment_eq, sub_apply] at hlim ⊢
    exact hlim
  have hnn := le_of_tendsto hlim'.neg
    (Eventually.of_forall fun n ↦ neg_nonpos.mpr (hgap n))
  exact neg_nonpos.mp hnn

/-- The two subspace pairings through `subtypeL` agree on differences. -/
private theorem sub_comp_subtypeL_apply {V : Submodule ℝ E} (B C : StrongDual ℝ E) (x y : V) :
    (B.comp V.subtypeL - C.comp V.subtypeL) (x - y) = (B - C) ((x : E) - (y : E)) := by
  rw [sub_apply, sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    subtypeL_apply, Submodule.coe_sub]

/-- A Minty inequality against every subspace vector identifies the dual functional. -/
private theorem eq_comp_subtypeL_of_minty {A : E → StrongDual ℝ E}
    (hh : IsHemicontinuousDualMap A) {V : Submodule ℝ E} {x : V} {χ : StrongDual ℝ V}
    (hχ : ∀ y : V, 0 ≤ ((A (y : E)).comp V.subtypeL - χ) (y - x)) :
    χ = (A (x : E)).comp V.subtypeL := by
  have hle : ∀ z : V, χ z ≤ A (x : E) (z : E) := by
    intro z
    have hstep : ∀ n, χ z ≤ A ((x + segmentParam n • z : V) : E) (z : E) := by
      intro n
      have hy := hχ (x + segmentParam n • z)
      have hsub : (x + segmentParam n • z) - x = segmentParam n • z := by
        simp [add_sub_cancel_left]
      rw [hsub, map_smul, sub_apply, ContinuousLinearMap.comp_apply, subtypeL_apply,
        smul_eq_mul] at hy
      linarith [nonneg_of_mul_nonneg_right hy (segmentParam_pos n)]
    have htend := hh.tendsto_segmentParam (x : E) (z : E) (z : E)
    have hstep' : ∀ n, χ z ≤ A ((x : E) + segmentParam n • (z : E)) (z : E) := by
      intro n
      simpa [Submodule.coe_add, Submodule.coe_smul] using hstep n
    have hdiff : Tendsto
        (fun n ↦ χ z - A ((x : E) + segmentParam n • (z : E)) (z : E)) atTop
        (𝓝 (χ z - A (x : E) (z : E))) :=
      tendsto_const_nhds.sub htend
    have := le_of_tendsto hdiff (Eventually.of_forall fun n ↦ sub_nonpos.mpr (hstep' n))
    linarith
  ext z
  rw [ContinuousLinearMap.comp_apply, subtypeL_apply]
  refine le_antisymm (hle z) ?_
  have hneg := hle (-z)
  rw [map_neg, Submodule.coe_neg, map_neg] at hneg
  linarith

/-- On a finite-dimensional subspace, bounded monotone hemicontinuous maps are continuous. -/
private theorem IsMonotoneDualMap.continuous_comp_subtypeL {A : E → StrongDual ℝ E}
    (hm : IsMonotoneDualMap A) (hh : IsHemicontinuousDualMap A)
    (hb : MapsBoundedSetsToBoundedSets A) {V : Submodule ℝ E} [FiniteDimensional ℝ V] :
    Continuous (fun x : V ↦ (A (x : E)).comp V.subtypeL) := by
  rw [continuous_iff_seqContinuous]
  intro xseq x hx
  let φ : V → StrongDual ℝ V := fun y ↦ (A (y : E)).comp V.subtypeL
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨R, hR⟩ := (isBounded_range_of_tendsto xseq hx).subset_closedBall (0 : V)
  have hxn (n : ℕ) : ‖xseq n‖ ≤ R := by
    have hn := hR ⟨n, rfl⟩
    rwa [mem_closedBall_iff_norm, sub_zero] at hn
  have hE : IsBounded (range fun n ↦ (xseq n : E)) := by
    refine (isBounded_closedBall (x := (0 : E)) (r := ‖V.subtypeL‖ * R)).subset ?_
    rintro _ ⟨n, rfl⟩
    rw [mem_closedBall_iff_norm, sub_zero]
    calc ‖(xseq n : E)‖ = ‖V.subtypeL (xseq n)‖ := by rw [subtypeL_apply]
      _ ≤ ‖V.subtypeL‖ * ‖xseq n‖ := V.subtypeL.le_opNorm _
      _ ≤ ‖V.subtypeL‖ * R :=
          mul_le_mul_of_nonneg_left (hxn n) (ContinuousLinearMap.opNorm_nonneg _)
  obtain ⟨M, hM⟩ := (hb _ hE).subset_closedBall (0 : StrongDual ℝ E)
  have hAn (n : ℕ) : ‖A (xseq n : E)‖ ≤ M := by
    have hn := hM ⟨(xseq n : E), ⟨n, rfl⟩, rfl⟩
    rwa [mem_closedBall_iff_norm, sub_zero] at hn
  have hφnorm (k : ℕ) : ‖φ (xseq (ns k))‖ ≤ M * ‖V.subtypeL‖ := by
    calc ‖φ (xseq (ns k))‖ ≤ ‖A (xseq (ns k) : E)‖ * ‖V.subtypeL‖ :=
          (A (xseq (ns k) : E)).opNorm_comp_le V.subtypeL
      _ ≤ M * ‖V.subtypeL‖ :=
          mul_le_mul_of_nonneg_right (hAn (ns k)) (ContinuousLinearMap.opNorm_nonneg _)
  have hsub : ∃ χ : StrongDual ℝ V, ∃ ms : ℕ → ℕ, StrictMono ms ∧
      Tendsto (fun k ↦ φ (xseq (ns (ms k)))) atTop (𝓝 χ) := by
    let _ : NormedAddCommGroup (StrongDual ℝ V) :=
      ContinuousLinearMap.toNormedAddCommGroup (E := V) (F := ℝ)
    have : ProperSpace (StrongDual ℝ V) := FiniteDimensional.proper_real _
    have hψ (k : ℕ) : φ (xseq (ns k)) ∈ closedBall 0 (M * ‖V.subtypeL‖) := by
      rw [mem_closedBall, dist_eq_norm, sub_zero]
      exact hφnorm k
    obtain ⟨χ, _, ms, hms, hχ⟩ :=
      (isCompact_closedBall (0 : StrongDual ℝ V) (M * ‖V.subtypeL‖)).tendsto_subseq hψ
    exact ⟨χ, ms, hms, hχ⟩
  obtain ⟨χ, ms, hms, hχ⟩ := hsub
  have hχeq : χ = φ x := by
    apply eq_comp_subtypeL_of_minty hh
    intro y
    let a : ℕ → V := fun k ↦ xseq (ns (ms k))
    have ha : Tendsto a atTop (𝓝 x) := hx.comp (hns.comp hms.tendsto_atTop)
    have hφa : Tendsto (fun k ↦ φ (a k)) atTop (𝓝 χ) := hχ
    have hge : ∀ k, 0 ≤ (φ (a k) - φ y) (a k - y) := by
      intro k
      rw [sub_comp_subtypeL_apply]
      exact hm (a k : E) (y : E)
    have hpair : Tendsto (fun k ↦ (φ (a k) - φ y) (a k - y)) atTop
        (𝓝 ((χ - φ y) (x - y))) := by
      let applyPair : (StrongDual ℝ V × V) → ℝ := fun p ↦ p.1 p.2
      have happly : Continuous applyPair :=
        (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := V) (F := ℝ)).continuous
      have hsubφ : Tendsto (fun k ↦ φ (a k) - φ y) atTop (𝓝 (χ - φ y)) :=
        hφa.sub (tendsto_const_nhds (x := φ y))
      have hsubv : Tendsto (fun k ↦ a k - y) atTop (𝓝 (x - y)) :=
        ha.sub (tendsto_const_nhds (x := y))
      have hprod : Tendsto (fun k ↦ (φ (a k) - φ y, a k - y)) atTop
          (𝓝 (χ - φ y, x - y)) := by
        rw [nhds_prod_eq]
        exact hsubφ.prodMk hsubv
      simpa [applyPair, Function.comp_def] using happly.tendsto (χ - φ y, x - y) |>.comp hprod
    have hL : 0 ≤ (χ - φ y) (x - y) :=
      neg_nonpos.mp <| le_of_tendsto hpair.neg <|
        Eventually.of_forall fun k ↦ neg_nonpos.mpr (hge k)
    have hswap : (φ y - χ) (y - x) = (χ - φ y) (x - y) := by
      rw [← neg_sub x y, map_neg, ← neg_apply, neg_sub]
    rw [hswap]
    exact hL
  refine ⟨ms, ?_⟩
  rw [hχeq] at hχ
  exact hχ

/-- A convex combination cancels in the dual pairing against its own barycenter. -/
private theorem sum_weight_gap_eq_zero (A : E → StrongDual ℝ E) (f : StrongDual ℝ E)
    {ι : Type*} [Fintype ι] (v : ι → E) (w : ι → ℝ) (hw : ∑ i, w i = 1) :
    ∑ i, w i * (A (∑ j, w j • v j) - f) (v i - ∑ j, w j • v j) = 0 := by
  set b := ∑ j, w j • v j
  have hvec : ∑ i, w i • (v i - b) = 0 := by
    simp_rw [smul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, hw, one_smul, sub_eq_zero]
  have hlin : ∑ i, w i * (A b - f) (v i - b) = (A b - f) (∑ i, w i • (v i - b)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, smul_eq_mul]
  rw [hlin, hvec, map_zero]

/-- On the convex hull of a nonempty finite set, some point has nonnegative gaps on the vertices. -/
private theorem exists_nonneg_on_finset {A : E → StrongDual ℝ E} (hm : IsMonotoneDualMap A)
    (hh : IsHemicontinuousDualMap A) (hb : MapsBoundedSetsToBoundedSets A) {s : Finset E}
    (hne : s.Nonempty) (f : StrongDual ℝ E) :
    ∃ u ∈ convexHull ℝ (s : Set E), ∀ v ∈ s, 0 ≤ (A u - f) (v - u) := by
  obtain ⟨x0, hx0⟩ := hne
  let ι := {x // x ∈ s}
  have : Nonempty ι := ⟨⟨x0, hx0⟩⟩
  let V : Submodule ℝ E := span ℝ (s : Set E)
  have : FiniteDimensional ℝ V := by
    simpa [V] using (inferInstance : FiniteDimensional ℝ (span ℝ (s : Set E)))
  let point : ι → V := fun i ↦ ⟨i, subset_span i.2⟩
  let bary : (ι → ℝ) → V := fun w ↦ ∑ i, w i • point i
  have hbary : Continuous bary :=
    continuous_finsetSum Finset.univ fun i _ ↦ (continuous_apply i).smul continuous_const
  have hbaryE (w : ι → ℝ) : (bary w : E) = ∑ i, w i • (i : E) := by
    simp [bary, point]
  let φ : V → StrongDual ℝ V := fun x ↦ (A (x : E)).comp V.subtypeL
  have hφ : Continuous φ := hm.continuous_comp_subtypeL hh hb
  -- The gap `(A b - f) (v - b)` at the barycenter `b`, written through `φ` for continuity.
  let gap : (ι → ℝ) → ι → ℝ := fun w i ↦
    (φ (bary w)) (point i - bary w) - f (i : E) + f (bary w : E)
  have hgap_eq (w : ι → ℝ) (i : ι) :
      (A (bary w : E) - f) ((i : E) - (bary w : E)) = gap w i := by
    simp only [gap, φ, sub_apply, map_sub, ContinuousLinearMap.comp_apply, subtypeL_apply]
    ring
  have hgap : Continuous gap := continuous_pi fun i ↦
    (((hφ.comp hbary).clm_apply (continuous_const.sub hbary)).sub continuous_const).add
      (f.continuous.comp (V.subtypeL.continuous.comp hbary))
  obtain ⟨w, hw0, hw1, hw⟩ := exists_forall_nonneg_of_sum_mul_nonneg hgap fun w _ hw1 ↦ by
    simp_rw [← hgap_eq, hbaryE]
    exact (sum_weight_gap_eq_zero A f (fun i : ι ↦ (i : E)) w hw1).ge
  refine ⟨(bary w : E), ?_, fun x hx ↦ ?_⟩
  · exact mem_convexHull_of_exists_fintype w (fun i : ι ↦ (i : E)) hw0 hw1 (fun i ↦ i.2)
      (hbaryE w).symm
  · have hx' := hw ⟨x, hx⟩
    rwa [← hgap_eq] at hx'

/-- **35.45**: bounded-domain variational-inequality existence in a reflexive space (reflexivity,
as surjectivity of the bidual inclusion, implies completeness). -/
theorem exists_solution_variationalInequality
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    {A : E → StrongDual ℝ E} (hm : IsMonotoneDualMap A)
    (hh : IsHemicontinuousDualMap A) (hb : MapsBoundedSetsToBoundedSets A)
    {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hc : Convex ℝ C) (f : StrongDual ℝ E) :
    ∃ u, SolvesVariationalInequality A C f u := by
  let sW := toWeakSpace ℝ E '' C
  have hsW : IsCompact sW :=
    TauCeti.isCompact_toWeakSpace_of_isClosed_of_convex_of_isBounded hreflexive hclosed hc hbounded
  let half : E → Set E := fun v ↦ {u | 0 ≤ (A v - f) (v - u)}
  let t : C → Set (WeakSpace ℝ E) := fun v ↦ toWeakSpace ℝ E '' (C ∩ half (v : E))
  have htclosed : ∀ v : C, IsClosed (t v) := by
    intro v
    let K := C ∩ half (v : E)
    have hKclosed : IsClosed K := by
      refine hclosed.inter ?_
      exact isClosed_le continuous_const
        ((A (v : E) - f).continuous.comp (continuous_const.sub continuous_id))
    have hKconv : Convex ℝ K := by
      refine hc.inter ?_
      rw [convex_iff_add_mem]
      intro x hx y hy a b ha hb hab
      have hlin : (v : E) - (a • x + b • y) = a • ((v : E) - x) + b • ((v : E) - y) := by
        calc (v : E) - (a • x + b • y)
            = (a + b) • (v : E) - (a • x + b • y) := by rw [hab, one_smul]
          _ = (a • (v : E) + b • (v : E)) - (a • x + b • y) := by rw [add_smul]
          _ = (a • (v : E) - a • x) + (b • (v : E) - b • y) := by rw [add_sub_add_comm]
          _ = a • ((v : E) - x) + b • ((v : E) - y) := by rw [← smul_sub, ← smul_sub]
      dsimp [half]
      rw [hlin, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
    have himage : t v = toWeakSpace ℝ E '' K := rfl
    rw [himage, ← hKclosed.closure_eq, hKconv.toWeakSpace_closure ℝ]
    exact isClosed_closure
  have hst : ∀ u : Finset C, (sW ∩ ⋂ i ∈ u, t i).Nonempty := by
    intro u
    obtain rfl | hufin := u.eq_empty_or_nonempty
    · obtain ⟨x, hx⟩ := hne
      refine ⟨toWeakSpace ℝ E x, ⟨x, hx, rfl⟩, mem_iInter₂.mpr ?_⟩
      intro i hi
      exact absurd hi (Finset.notMem_empty i)
    · let sE : Finset E := u.map (Embedding.subtype (· ∈ C))
      have hsE : sE.Nonempty := by
        obtain ⟨v, hv⟩ := hufin
        exact ⟨v.1, Finset.mem_map.mpr ⟨v, hv, rfl⟩⟩
      obtain ⟨y, hyhull, hygap⟩ := exists_nonneg_on_finset hm hh hb hsE f
      have hyC : y ∈ C := by
        refine convexHull_min ?_ hc hyhull
        intro z hz
        obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hz
        exact v.2
      refine ⟨toWeakSpace ℝ E y, ⟨y, hyC, rfl⟩, mem_iInter₂.mpr ?_⟩
      intro v hv
      dsimp [t]
      refine ⟨y, ⟨hyC, ?_⟩, rfl⟩
      dsimp [half]
      have hvi : (v : E) ∈ sE := Finset.mem_map.mpr ⟨v, hv, rfl⟩
      have hadd : (A (v : E) - A y) + (A y - f) = A (v : E) - f := by
        rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc, ← add_assoc (-(A y)) (A y) (-f),
          neg_add_cancel, zero_add, ← sub_eq_add_neg]
      rw [← hadd, add_apply]
      exact add_nonneg (hm (v : E) y) (hygap (v : E) hvi)
  obtain ⟨z, hzW, hzI⟩ := hsW.inter_iInter_nonempty t htclosed hst
  obtain ⟨u, huC, rfl⟩ := hzW
  have hminty : ∀ v ∈ C, 0 ≤ (A v - f) (v - u) := by
    intro v hv
    have hzv : toWeakSpace ℝ E u ∈ t ⟨v, hv⟩ := (mem_iInter.mp hzI) ⟨v, hv⟩
    obtain ⟨u', hu', hu'eq⟩ := hzv
    have hsame : u' = u := (toWeakSpace ℝ E).injective hu'eq
    rw [hsame] at hu'
    exact hu'.2
  exact ⟨u, SolvesVariationalInequality.of_minty hh hc huC hminty⟩

/-- The unbounded-domain version uses coercivity relative to one feasible point. -/
theorem exists_solution_variationalInequality_of_coercive
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    {A : E → StrongDual ℝ E} (hm : IsMonotoneDualMap A)
    (hh : IsHemicontinuousDualMap A) (hb : MapsBoundedSetsToBoundedSets A)
    {C : Set E} (hclosed : IsClosed C) (hc : Convex ℝ C)
    (f : StrongDual ℝ E) {u₀ : E} (hu₀ : u₀ ∈ C) (hcoercive : IsCoerciveOnAt A C f u₀) :
    ∃ u, SolvesVariationalInequality A C f u := by
  obtain ⟨R0, _, hR0⟩ := hcoercive.exists_radius 1
  let R := max R0 (‖u₀‖ + 1)
  let K := C ∩ closedBall (0 : E) R
  have hKne : K.Nonempty := by
    refine ⟨u₀, hu₀, ?_⟩
    rw [mem_closedBall_iff_norm, sub_zero]
    exact (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1)).trans (le_max_right _ _)
  obtain ⟨u, huK, hVI⟩ := exists_solution_variationalInequality hreflexive hm hh hb hKne
    (hclosed.inter isClosed_closedBall) (isBounded_closedBall.subset inter_subset_right)
    (hc.inter (convex_closedBall 0 R)) f
  have huC : u ∈ C := huK.1
  have huR : ‖u‖ ≤ R := by
    have := huK.2
    rwa [mem_closedBall_iff_norm, sub_zero] at this
  have hult : ‖u‖ < R := by
    by_contra hge
    have hueq : ‖u‖ = R := le_antisymm huR (not_lt.mp hge)
    have hco : 1 * ‖u‖ ≤ (A u - f) (u - u₀) := hR0 u huC ((le_max_left _ _).trans hueq.ge)
    have hu₀K : u₀ ∈ K := by
      refine ⟨hu₀, ?_⟩
      rw [mem_closedBall_iff_norm, sub_zero]
      exact (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1)).trans (le_max_right _ _)
    have htest : 0 ≤ (A u - f) (u₀ - u) := hVI u₀ hu₀K
    rw [← neg_sub u u₀, map_neg] at htest
    have hpos : 0 < ‖u‖ := by
      calc (0 : ℝ) < ‖u₀‖ + 1 := by positivity
        _ ≤ R := le_max_right _ _
        _ = ‖u‖ := hueq.symm
    linarith
  refine ⟨u, huC, fun v hv ↦ ?_⟩
  let δ := R - ‖u‖
  have hδ : 0 < δ := sub_pos.mpr hult
  let t := min (1 : ℝ) (δ / (‖v - u‖ + 1))
  have hden : 0 < ‖v - u‖ + 1 := by linarith [norm_nonneg (v - u)]
  have htpos : 0 < t := lt_min zero_lt_one (div_pos hδ hden)
  have htle : t ≤ 1 := min_le_left _ _
  have htnorm : t * ‖v - u‖ ≤ δ := by
    have htd : t * (‖v - u‖ + 1) ≤ δ := by
      calc t * (‖v - u‖ + 1)
          ≤ (δ / (‖v - u‖ + 1)) * (‖v - u‖ + 1) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hden.le
        _ = δ := by rw [div_mul_cancel₀ _ hden.ne']
    calc t * ‖v - u‖ ≤ t * (‖v - u‖ + 1) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) htpos.le
      _ ≤ δ := htd
  let w := (1 - t) • u + t • v
  have hwK : w ∈ K := by
    have hwC : w ∈ C := by
      apply (convex_iff_add_mem.mp hc) huC hv
      · exact sub_nonneg.mpr htle
      · exact htpos.le
      · exact sub_add_cancel 1 t
    have hwnorm : ‖w‖ ≤ R := by
      have hwEq : w = u + t • (v - u) := by
        dsimp [w]
        exact segment_eq u v t
      rw [hwEq]
      calc ‖u + t • (v - u)‖ ≤ ‖u‖ + ‖t • (v - u)‖ := norm_add_le _ _
        _ = ‖u‖ + t * ‖v - u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
        _ ≤ ‖u‖ + δ := add_le_add_right htnorm ‖u‖
        _ = R := by dsimp [δ]; linarith
    exact ⟨hwC, by rwa [mem_closedBall_iff_norm, sub_zero]⟩
  have htest : 0 ≤ (A u - f) (w - u) := hVI w hwK
  rw [segment_sub, map_smul, smul_eq_mul] at htest
  exact nonneg_of_mul_nonneg_right htest htpos

/-- **35.40**: Browder–Minty surjectivity for an everywhere-defined monotone, hemicontinuous,
coercive operator on a reflexive space, bounded on bounded sets. Reflexivity is surjectivity of
the bidual inclusion, as in TauCeti's weak compactness API; it implies completeness. -/
theorem IsMonotoneDualMap.surjective
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    {A : E → StrongDual ℝ E} (hm : IsMonotoneDualMap A)
    (hh : IsHemicontinuousDualMap A) (hb : MapsBoundedSetsToBoundedSets A)
    (hc : IsCoerciveDualMap A) : Function.Surjective A := by
  intro f
  obtain ⟨R0, _, hR0⟩ := hc.exists_radius (‖f‖ + 1)
  let R := max R0 1
  have hRnonneg : 0 ≤ R := zero_le_one.trans (le_max_right _ _)
  obtain ⟨u, huBall, hVI⟩ := exists_solution_variationalInequality hreflexive hm hh hb
    (⟨0, mem_closedBall_self hRnonneg⟩ : (closedBall (0 : E) R).Nonempty)
    isClosed_closedBall isBounded_closedBall (convex_closedBall (0 : E) R) f
  have huR : ‖u‖ ≤ R := by rwa [mem_closedBall_iff_norm, sub_zero] at huBall
  have hult : ‖u‖ < R := by
    by_contra hge
    have hueq : ‖u‖ = R := le_antisymm huR (not_lt.mp hge)
    have hco : (‖f‖ + 1) * ‖u‖ ≤ A u u := hR0 u ((le_max_left _ _).trans hueq.ge)
    have htest : 0 ≤ (A u - f) (0 - u) := hVI 0 (mem_closedBall_self hRnonneg)
    rw [zero_sub, map_neg, sub_apply] at htest
    have hAu : A u u ≤ f u := by linarith
    have hfu : f u ≤ ‖f‖ * ‖u‖ := by
      calc f u ≤ |f u| := le_abs_self _
        _ = ‖f u‖ := (Real.norm_eq_abs (f u)).symm
        _ ≤ ‖f‖ * ‖u‖ := f.le_opNorm u
    have hpos : 0 < ‖u‖ := by
      calc (0 : ℝ) < 1 := zero_lt_one
        _ ≤ R := le_max_right _ _
        _ = ‖u‖ := hueq.symm
    linarith [hco, hAu, hfu, hpos]
  refine ⟨u, ?_⟩
  ext w
  rw [← sub_eq_zero, ← sub_apply]
  by_cases hw : w = 0
  · simp [hw, map_zero]
  · have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    let t := (R - ‖u‖) / (2 * ‖w‖)
    have hδ : 0 < R - ‖u‖ := sub_pos.mpr hult
    have htpos : 0 < t := div_pos hδ (by linarith)
    have htnorm : t * ‖w‖ = (R - ‖u‖) / 2 := by
      calc t * ‖w‖ = (R - ‖u‖) / (2 * ‖w‖) * ‖w‖ := rfl
        _ = (R - ‖u‖) * ‖w‖ / (2 * ‖w‖) := by rw [div_mul_eq_mul_div]
        _ = (R - ‖u‖) / 2 := by rw [mul_div_mul_right _ _ (norm_ne_zero_iff.mpr hw)]
    have hmem (ε : ℝ) (hε : |ε| * ‖w‖ ≤ (R - ‖u‖) / 2) :
        u + ε • w ∈ closedBall (0 : E) R := by
      rw [mem_closedBall_iff_norm, sub_zero]
      calc ‖u + ε • w‖ ≤ ‖u‖ + ‖ε • w‖ := norm_add_le _ _
        _ = ‖u‖ + |ε| * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ ‖u‖ + (R - ‖u‖) / 2 := add_le_add_right hε ‖u‖
        _ ≤ R := by linarith [huR]
    have hpos_ball := hmem t (by rw [abs_of_pos htpos, htnorm])
    have hneg_ball := hmem (-t) (by rw [abs_neg, abs_of_pos htpos, htnorm])
    have h1 : 0 ≤ (A u - f) ((u + t • w) - u) := hVI _ hpos_ball
    have h2 : 0 ≤ (A u - f) ((u + (-t) • w) - u) := hVI _ hneg_ball
    have h1' : 0 ≤ t * (A u - f) w := by
      simpa [add_sub_cancel_left, map_smul, smul_eq_mul] using h1
    have h2' : 0 ≤ t * -((A u - f) w) := by
      have h2raw : 0 ≤ (A u - f) ((-t) • w) := by
        simpa [add_sub_cancel_left] using h2
      rw [map_smul, smul_eq_mul, neg_mul_comm] at h2raw
      exact h2raw
    have hg1 : 0 ≤ (A u - f) w := nonneg_of_mul_nonneg_right h1' htpos
    have hg2 : 0 ≤ -((A u - f) w) := nonneg_of_mul_nonneg_right h2' htpos
    linarith

end Banach

end CKMA
