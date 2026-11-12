/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.OrderedSpace.Representation.AL
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
public import Mathlib.MeasureTheory.Function.SimpleFunc
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.Order.Zorn
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Gluing of AL representations along a maximal disjoint family

A maximal pairwise lattice-disjoint family of strictly positive vectors splits an AL-space into
the ℓ¹-sum of the closed principal bands those vectors generate. Each band carries its generator
as a weak unit, so the weak-unit representation supplies an L¹ space. The disjoint union of those
carriers, with the sum of the pushed-forward measures, represents the original space. No
σ-finiteness restriction is imposed: an uncountable disjoint family is allowed, and each vector
meets only countably many bands.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open Metric Set Filter Topology MeasureTheory
open scoped ENNReal

namespace CKMA

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E]
  [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]

/-- A pairwise lattice-disjoint family of strictly positive vectors. -/
def IsPositiveDisjointFamily (S : Set E) : Prop :=
  (∀ x ∈ S, 0 < x) ∧ S.Pairwise (fun a b => LatticeDisjoint a b)

/-- Pairwise disjoint positive families are inductive, so a maximal one exists. -/
theorem exists_maximal_positiveDisjointFamily :
    ∃ M : Set E, IsPositiveDisjointFamily M ∧ Maximal IsPositiveDisjointFamily M := by
  have hchain : ∀ c ⊆ {S : Set E | IsPositiveDisjointFamily S}, IsChain (· ⊆ ·) c →
      ∃ ub ∈ {S : Set E | IsPositiveDisjointFamily S}, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hchain
    refine ⟨⋃₀ c, ?_, fun s hs => subset_sUnion_of_mem hs⟩
    constructor
    · intro x hx
      rcases hx with ⟨s, hs, hx⟩
      exact (hc hs).1 x hx
    · intro x hx y hy hxy
      rcases hx with ⟨s, hs, hx⟩
      rcases hy with ⟨t, ht, hy⟩
      by_cases hst : s = t
      · subst hst
        exact (hc hs).2 hx hy hxy
      · rcases hchain hs ht hst with hsub | hsub
        · exact (hc ht).2 (hsub hx) hy hxy
        · exact (hc hs).2 hx (hsub hy) hxy
  obtain ⟨M, hM⟩ :=
    zorn_subset (α := E) {S : Set E | IsPositiveDisjointFamily S} hchain
  rw [maximal_subset_iff] at hM
  refine ⟨M, by simpa using hM.1, maximal_subset_iff.mpr ⟨?_, ?_⟩⟩
  · simpa using hM.1
  · intro t ht hsub
    exact hM.2 (by simpa using ht) hsub

/-- A chosen maximal pairwise disjoint family of strictly positive vectors. -/
noncomputable def maximalPositiveDisjointFamily : Set E :=
  Classical.choose (exists_maximal_positiveDisjointFamily (E := E))

/-- The chosen family is a maximal positive disjoint family. -/
theorem maximalPositiveDisjointFamily_spec :
    IsPositiveDisjointFamily (E := E) maximalPositiveDisjointFamily ∧
      Maximal (fun S : Set E => IsPositiveDisjointFamily (E := E) S)
        maximalPositiveDisjointFamily :=
  Classical.choose_spec (exists_maximal_positiveDisjointFamily (E := E))

/-- Index of the chosen maximal disjoint family. -/
structure bandIndex where
  /-- Vector belonging to the family. -/
  vec : E
  /-- Proof that the vector lies in the chosen family. -/
  mem_family : vec ∈ maximalPositiveDisjointFamily

/-- Each index vector is strictly positive. -/
theorem bandIndex_pos (i : bandIndex) : (0 : E) < i.vec :=
  (maximalPositiveDisjointFamily_spec (E := E)).1.1 i.vec i.mem_family

/-- Each index vector is nonnegative. -/
theorem bandIndex_nonneg (i : bandIndex) : (0 : E) ≤ i.vec :=
  le_of_lt (bandIndex_pos i)

/-- Distinct index vectors are lattice disjoint. -/
theorem bandIndex_disjoint {i j : bandIndex} (hij : i ≠ j) :
    LatticeDisjoint (E := E) i.vec j.vec := by
  have hne : i.vec ≠ j.vec := by
    intro h
    apply hij
    cases i
    cases j
    cases h
    rfl
  exact (maximalPositiveDisjointFamily_spec (E := E)).1.2 i.mem_family j.mem_family hne

/-- The order truncation of a positive vector by successive multiples of `u`. -/
def trunc (u x : E) (n : ℕ) : E := x ⊓ ((n : ℝ) • u)

/-- Canonical limit of the truncations, whether or not the sequence converges. -/
noncomputable def posBandPart (u x : E) : E :=
  limUnder atTop (fun n : ℕ => trunc u x n)

/-- Truncations by a nonnegative vector increase. -/
theorem trunc_mono {u x : E} (hu : 0 ≤ u) (_hx : 0 ≤ x) : Monotone (trunc u x) := by
  intro n m hnm
  exact inf_le_inf_left x (smul_le_smul_of_nonneg_right (by exact_mod_cast hnm) hu)

/-- Truncations of a positive vector are positive. -/
theorem trunc_nonneg {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) (n : ℕ) : 0 ≤ trunc u x n :=
  le_inf hx (smul_nonneg (Nat.cast_nonneg n) hu)

/-- Truncations are bounded in norm by the vector. -/
theorem trunc_norm_le {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) (n : ℕ) :
    ‖trunc u x n‖ ≤ ‖x‖ := by
  apply norm_le_norm_of_abs_le_abs
  rw [abs_of_nonneg (trunc_nonneg hu hx n), abs_of_nonneg hx]
  exact inf_le_left

/-- In an AL-space the truncations converge, and the limit is `posBandPart`. -/
theorem posBandPart_tendsto (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) :
    Tendsto (trunc u x) atTop (𝓝 (posBandPart u x)) := by
  apply tendsto_nhds_limUnder
  refine al_isKB hE (trunc_mono hu hx) (trunc_nonneg hu hx) ⟨‖x‖, trunc_norm_le hu hx⟩

/-- The band part of a positive vector lies between zero and the vector. -/
theorem posBandPart_mem_Icc (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) :
    posBandPart u x ∈ Icc 0 x := by
  exact isClosed_Icc.mem_of_tendsto (posBandPart_tendsto hE hu hx)
    (Eventually.of_forall fun n => ⟨trunc_nonneg hu hx n, inf_le_left⟩)

/-- The band part of a positive vector is nonnegative. -/
theorem posBandPart_nonneg (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) : 0 ≤ posBandPart u x :=
  (posBandPart_mem_Icc hE hu hx).1

/-- The band part of a positive vector is at most the vector. -/
theorem posBandPart_le (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) : posBandPart u x ≤ x :=
  (posBandPart_mem_Icc hE hu hx).2

/-- The band part of zero is zero. -/
theorem posBandPart_zero (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u : E} (hu : 0 ≤ u) : posBandPart u 0 = 0 := by
  apply tendsto_nhds_unique (posBandPart_tendsto hE hu le_rfl)
  have h0 : trunc u 0 = fun _ => (0 : E) := by
    ext n
    simp only [trunc]
    exact inf_eq_left.mpr (smul_nonneg (Nat.cast_nonneg n) hu)
  rw [h0]
  exact tendsto_const_nhds

/-- Reindexing the truncations along a cofinal sequence does not change the limit. -/
theorem tendsto_trunc_comp (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) :
    Tendsto (fun n => trunc u x (φ n)) atTop (𝓝 (posBandPart u x)) :=
  (posBandPart_tendsto hE hu hx).comp hφ

/-- A vector squeezed in norm between two sequences with the same limit converges to it. -/
theorem tendsto_of_norm_squeeze {a b c : ℕ → E} {L : E} (hb : Tendsto b atTop (𝓝 L))
    (hc : Tendsto c atTop (𝓝 L)) (hbc : ∀ n, b n ≤ a n) (hac : ∀ n, a n ≤ c n) :
    Tendsto a atTop (𝓝 L) := by
  have hgap : ∀ n, ‖a n - b n‖ ≤ ‖c n - b n‖ := by
    intro n
    apply norm_le_norm_of_abs_le_abs
    have h0 : 0 ≤ a n - b n := sub_nonneg.mpr (hbc n)
    have h1 : a n - b n ≤ c n - b n := sub_le_sub_right (hac n) _
    rw [abs_of_nonneg h0, abs_of_nonneg (h0.trans h1)]
    exact h1
  have hzero : Tendsto (fun n => ‖a n - b n‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) hgap <| by
      simpa using (hc.sub hb).norm
  have hsum := hb.add (tendsto_zero_iff_norm_tendsto_zero.mpr hzero)
  simpa using hsum

/-- Doubling the truncation index remains cofinal. -/
theorem tendsto_double_atTop : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro N
  refine ⟨N, fun n hn => ?_⟩
  exact hn.trans (by omega)

/-- Band parts are additive on the positive cone. -/
theorem posBandPart_add (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u x y : E} (hu : 0 ≤ u) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    posBandPart u (x + y) = posBandPart u x + posBandPart u y := by
  let a : ℕ → E := fun n => trunc u x n + trunc u y n
  let b : ℕ → E := trunc u (x + y)
  let c : ℕ → E := fun n => trunc u (x + y) (2 * n)
  have hxy : 0 ≤ x + y := add_nonneg hx hy
  have hba : ∀ n, b n ≤ a n := by
    intro n
    simpa [b, a, trunc, inf_comm] using
      inf_add_le_add_inf (smul_nonneg (Nat.cast_nonneg n) hu) hx hy
  have hac : ∀ n, a n ≤ c n := by
    intro n
    refine le_inf (add_le_add inf_le_left inf_le_left) ?_
    have hsum : trunc u x n + trunc u y n ≤ ((2 * n : ℕ) : ℝ) • u := by
      calc
        trunc u x n + trunc u y n ≤ (n : ℝ) • u + (n : ℝ) • u :=
          add_le_add inf_le_right inf_le_right
        _ = ((2 * n : ℕ) : ℝ) • u := by
          rw [← add_smul, ← Nat.cast_add, ← two_mul]
    exact hsum
  have hb := posBandPart_tendsto hE hu hxy
  have hc : Tendsto c atTop (𝓝 (posBandPart u (x + y))) :=
    tendsto_trunc_comp hE hu hxy tendsto_double_atTop
  have ha : Tendsto a atTop (𝓝 (posBandPart u (x + y))) :=
    tendsto_of_norm_squeeze hb hc hba hac
  have ha' : Tendsto a atTop (𝓝 (posBandPart u x + posBandPart u y)) :=
    (posBandPart_tendsto hE hu hx).add (posBandPart_tendsto hE hu hy)
  exact tendsto_nhds_unique ha ha'

/-- Scalar multiples of a cofinal truncation still recover the band part. -/
theorem tendsto_trunc_real (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : Tendsto t atTop atTop) :
    Tendsto (fun n => x ⊓ (t n • u)) atTop (𝓝 (posBandPart u x)) := by
  let m : ℕ → ℕ := fun n => Nat.floor (t n)
  have hm : Tendsto m atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    rcases (tendsto_atTop_atTop.mp ht) N with ⟨N0, hN0⟩
    exact ⟨N0, fun n hn => Nat.le_floor (by exact_mod_cast hN0 n hn)⟩
  have hm1 : Tendsto (fun n => m n + 1) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    rcases (tendsto_atTop_atTop.mp hm) N with ⟨N0, hN0⟩
    exact ⟨N0, fun n hn => (hN0 n hn).trans (Nat.le_succ _)⟩
  have hlow := tendsto_trunc_comp hE hu hx hm
  have hhigh := tendsto_trunc_comp hE hu hx hm1
  have hlo : ∀ n, trunc u x (m n) ≤ x ⊓ (t n • u) := by
    intro n
    exact inf_le_inf_left x <| smul_le_smul_of_nonneg_right (Nat.floor_le (ht0 n)) hu
  have hhi : ∀ n, x ⊓ (t n • u) ≤ trunc u x (m n + 1) := by
    intro n
    exact inf_le_inf_left x <| smul_le_smul_of_nonneg_right
      (le_of_lt (by simpa [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (t n))) hu
  exact tendsto_of_norm_squeeze hlow hhigh hlo hhi

/-- Band parts are homogeneous for nonnegative scalars. -/
theorem posBandPart_smul (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) {c : ℝ} (hc : 0 ≤ c) :
    posBandPart u (c • x) = c • posBandPart u x := by
  rcases eq_or_lt_of_le hc with rfl | hc0
  · simp [posBandPart_zero hE hu]
  · apply tendsto_nhds_unique (posBandPart_tendsto hE hu (smul_nonneg hc hx))
    have ht : Tendsto (fun n : ℕ => (n : ℝ) / c) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨Nat.ceil (c * (b + 1)), fun n hn => ?_⟩
      have hceil : c * (b + 1) ≤ (n : ℝ) := Nat.ceil_le.mp hn
      rw [le_div_iff₀ hc0]
      linarith
    have hinner := tendsto_trunc_real hE hu hx
      (fun n => div_nonneg (Nat.cast_nonneg n) hc) ht
    refine (hinner.const_smul c).congr fun n => ?_
    symm
    calc
      trunc u (c • x) n = c • x ⊓ ((n : ℝ) • u) := rfl
      _ = c • x ⊓ (c * ((n : ℝ) / c)) • u := by
        rw [mul_comm, div_mul_cancel₀ _ hc0.ne']
      _ = c • x ⊓ c • (((n : ℝ) / c) • u) := by rw [← smul_smul]
      _ = c • (x ⊓ (((n : ℝ) / c) • u)) := (smul_inf_of_nonneg hc x _).symm

/-- A positive vector dominated by a multiple of `u` is its own band part. -/
theorem posBandPart_of_le_smul (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) {c : ℝ} (_hc : 0 ≤ c)
    (hxu : x ≤ c • u) : posBandPart u x = x := by
  obtain ⟨N, hN⟩ := exists_nat_ge c
  apply tendsto_nhds_unique (posBandPart_tendsto hE hu hx)
  refine tendsto_atTop_of_eventually_const (i₀ := N) ?_
  intro n hn
  have hnu : c • u ≤ (n : ℝ) • u :=
    smul_le_smul_of_nonneg_right (hN.trans (by exact_mod_cast hn)) hu
  simp [trunc, inf_eq_left.mpr (hxu.trans hnu)]

/-- A positive vector disjoint from `u` has band part zero. -/
theorem posBandPart_eq_zero_of_disjoint (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) (hdisj : x ⊓ u = 0) :
    posBandPart u x = 0 := by
  apply tendsto_nhds_unique (posBandPart_tendsto hE hu hx)
  have h0 : ∀ n, trunc u x n = 0 := by
    intro n
    simpa [trunc, inf_comm] using
      inf_smul_eq_zero (Nat.cast_nonneg n) hu hx (by simpa [inf_comm] using hdisj)
  have hfun : trunc u x = fun _ => (0 : E) := by
    ext n
    exact h0 n
  rw [hfun]
  exact tendsto_const_nhds

/-- The remainder after removing the band part is disjoint from `u`. -/
theorem posBandPart_disjoint_remainder (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) :
    (x - posBandPart u x) ⊓ u = 0 := by
  have hzero : Tendsto (fun n : ℕ => (x - trunc u x n) ⊓ u) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (‖x‖ / ε)
    refine ⟨max N 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
    have hle := norm_trunc_remainder_le hu hx hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.succ_le_iff.mp hn1)
    have hnbig : ‖x‖ / ε < (n : ℝ) :=
      hN.trans_le (by exact_mod_cast (le_max_left N 1).trans hn)
    have hlt : ‖x‖ / n < ε := by
      rw [div_lt_iff₀ hn0]
      rw [div_lt_iff₀ hε, mul_comm] at hnbig
      exact hnbig
    rw [dist_eq_norm, sub_zero]
    exact hle.trans_lt hlt
  have hrem : Tendsto (fun n : ℕ => (x - trunc u x n) ⊓ u) atTop
      (𝓝 ((x - posBandPart u x) ⊓ u)) := by
    have hpair : Tendsto (fun n : ℕ => (x - trunc u x n, u)) atTop
        (𝓝 (x - posBandPart u x, u)) := by
      rw [nhds_prod_eq]
      exact ((tendsto_const_nhds.sub (posBandPart_tendsto hE hu hx))).prodMk tendsto_const_nhds
    exact (continuous_inf.tendsto _).comp hpair
  exact tendsto_nhds_unique hrem hzero

/-- Disjoint positive generators have disjoint band parts. -/
theorem posBandPart_disjoint_of_disjoint (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u v x : E} (hu : 0 ≤ u) (hv : 0 ≤ v) (hx : 0 ≤ x)
    (huv : u ⊓ v = 0) : posBandPart u x ⊓ posBandPart v x = 0 := by
  have htrunc : ∀ n, trunc u x n ⊓ trunc v x n = 0 := by
    intro n
    refine le_antisymm ?_ (le_inf (trunc_nonneg hu hx n) (trunc_nonneg hv hx n))
    calc
      trunc u x n ⊓ trunc v x n ≤ ((n : ℝ) • u) ⊓ ((n : ℝ) • v) :=
        inf_le_inf inf_le_right inf_le_right
      _ = 0 := by
        have hvu : v ⊓ ((n : ℝ) • u) = 0 := by
          simpa [inf_comm] using inf_smul_eq_zero (Nat.cast_nonneg n) hu hv huv
        simpa [inf_comm] using inf_smul_eq_zero (Nat.cast_nonneg n) hv
          (smul_nonneg (Nat.cast_nonneg n) hu) hvu
  have hlim : Tendsto (fun n => trunc u x n ⊓ trunc v x n) atTop
      (𝓝 (posBandPart u x ⊓ posBandPart v x)) := by
    have hpair : Tendsto (fun n => (trunc u x n, trunc v x n)) atTop
        (𝓝 (posBandPart u x, posBandPart v x)) := by
      rw [nhds_prod_eq]
      exact (posBandPart_tendsto hE hu hx).prodMk (posBandPart_tendsto hE hv hx)
    exact (continuous_inf.tendsto _).comp hpair
  have hzero : Tendsto (fun n => trunc u x n ⊓ trunc v x n) atTop (𝓝 0) := by
    exact tendsto_const_nhds.congr fun n => (htrunc n).symm
  exact tendsto_nhds_unique hlim hzero

/-- Truncations lie in the principal ideal. -/
theorem trunc_mem_ideal {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) (n : ℕ) :
    trunc u x n ∈ principalOrderIdeal u := by
  refine ⟨(n : ℝ), Nat.cast_nonneg n, ?_⟩
  rw [abs_of_nonneg (trunc_nonneg hu hx n)]
  exact inf_le_right

/-- The band part lies in the closure of the principal ideal. -/
theorem posBandPart_mem_closure (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) :
    posBandPart u x ∈ closure (principalOrderIdeal u) :=
  mem_closure_of_tendsto (posBandPart_tendsto hE hu hx)
    (Eventually.of_forall (trunc_mem_ideal hu hx))

/-- The closure of a principal ideal is an additive subgroup. -/
theorem principalBand_zero_mem (u : E) : (0 : E) ∈ closure (principalOrderIdeal u) :=
  subset_closure ⟨0, le_rfl, by simp⟩

/-- Addition preserves the closure of a principal ideal. -/
theorem principalBand_add_mem {u x y : E} (hx : x ∈ closure (principalOrderIdeal u))
    (hy : y ∈ closure (principalOrderIdeal u)) :
    x + y ∈ closure (principalOrderIdeal u) := by
  obtain ⟨sx, hsx, xlim⟩ := mem_closure_iff_seq_limit.mp hx
  obtain ⟨sy, hsy, ylim⟩ := mem_closure_iff_seq_limit.mp hy
  exact mem_closure_of_tendsto (xlim.add ylim)
    (Eventually.of_forall fun n => principalOrderIdeal_add (hsx n) (hsy n))

/-- Negation preserves the closure of a principal ideal. -/
theorem principalBand_neg_mem {u x : E} (hx : x ∈ closure (principalOrderIdeal u)) :
    -x ∈ closure (principalOrderIdeal u) := by
  obtain ⟨sx, hsx, xlim⟩ := mem_closure_iff_seq_limit.mp hx
  exact mem_closure_of_tendsto xlim.neg
    (Eventually.of_forall fun n => principalOrderIdeal_neg (hsx n))

/-- Subtraction preserves the closure of a principal ideal. -/
theorem principalBand_sub_mem {u x y : E} (hx : x ∈ closure (principalOrderIdeal u))
    (hy : y ∈ closure (principalOrderIdeal u)) :
    x - y ∈ closure (principalOrderIdeal u) := by
  simpa [sub_eq_add_neg] using principalBand_add_mem hx (principalBand_neg_mem hy)

/-- Scaling preserves the closure of a principal ideal. -/
theorem principalBand_smul_mem {u x : E} (c : ℝ) (hx : x ∈ closure (principalOrderIdeal u)) :
    c • x ∈ closure (principalOrderIdeal u) := by
  obtain ⟨sx, hsx, xlim⟩ := mem_closure_iff_seq_limit.mp hx
  exact mem_closure_of_tendsto (xlim.const_smul c)
    (Eventually.of_forall fun n => principalOrderIdeal_smul (hsx n))

/-- Suprema preserve the closure of a principal ideal. -/
theorem principalBand_sup_mem {u x y : E} (hx : x ∈ closure (principalOrderIdeal u))
    (hy : y ∈ closure (principalOrderIdeal u)) :
    x ⊔ y ∈ closure (principalOrderIdeal u) := by
  obtain ⟨sx, hsx, xlim⟩ := mem_closure_iff_seq_limit.mp hx
  obtain ⟨sy, hsy, ylim⟩ := mem_closure_iff_seq_limit.mp hy
  have hpair : Tendsto (fun n => (sx n, sy n)) atTop (𝓝 (x, y)) := by
    rw [nhds_prod_eq]
    exact xlim.prodMk ylim
  exact mem_closure_of_tendsto ((continuous_sup.tendsto (x, y)).comp hpair)
    (Eventually.of_forall fun n => principalOrderIdeal_sup (hsx n) (hsy n))

/-- Infima preserve the closure of a principal ideal. -/
theorem principalBand_inf_mem {u x y : E} (hx : x ∈ closure (principalOrderIdeal u))
    (hy : y ∈ closure (principalOrderIdeal u)) :
    x ⊓ y ∈ closure (principalOrderIdeal u) := by
  obtain ⟨sx, hsx, xlim⟩ := mem_closure_iff_seq_limit.mp hx
  obtain ⟨sy, hsy, ylim⟩ := mem_closure_iff_seq_limit.mp hy
  have hpair : Tendsto (fun n => (sx n, sy n)) atTop (𝓝 (x, y)) := by
    rw [nhds_prod_eq]
    exact xlim.prodMk ylim
  exact mem_closure_of_tendsto ((continuous_inf.tendsto (x, y)).comp hpair)
    (Eventually.of_forall fun n => principalOrderIdeal_inf (hsx n) (hsy n))

/-- Absolute value preserves the closure of a principal ideal. -/
theorem principalBand_abs_mem {u x : E} (hx : x ∈ closure (principalOrderIdeal u)) :
    |x| ∈ closure (principalOrderIdeal u) := by
  simpa [abs] using principalBand_sup_mem hx (principalBand_neg_mem hx)

/-- The closed principal band generated by `u`, with the ambient norm. -/
@[ext]
structure ClosedPrincipalBand (u : E) where
  /-- Underlying vector. -/
  toVec : E
  /-- Membership in the norm closure of the principal ideal. -/
  mem_band : toVec ∈ closure (principalOrderIdeal u)

namespace ClosedPrincipalBand

variable {u : E}

/-- The underlying vector map is injective. -/
theorem toVec_injective : Function.Injective (toVec : ClosedPrincipalBand u → E) :=
  fun _ _ h => ClosedPrincipalBand.ext h

instance : Zero (ClosedPrincipalBand u) where
  zero := ⟨0, principalBand_zero_mem u⟩

instance : Add (ClosedPrincipalBand u) where
  add x y := ⟨x.toVec + y.toVec, principalBand_add_mem x.mem_band y.mem_band⟩

instance : Neg (ClosedPrincipalBand u) where
  neg x := ⟨-x.toVec, principalBand_neg_mem x.mem_band⟩

instance : Sub (ClosedPrincipalBand u) where
  sub x y := ⟨x.toVec - y.toVec, principalBand_sub_mem x.mem_band y.mem_band⟩

instance : SMul ℕ (ClosedPrincipalBand u) where
  smul n x := ⟨n • x.toVec, by
    rw [← Nat.cast_smul_eq_nsmul ℝ]
    exact principalBand_smul_mem (n : ℝ) x.mem_band⟩

instance : SMul ℤ (ClosedPrincipalBand u) where
  smul n x := ⟨n • x.toVec, by
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact principalBand_smul_mem (n : ℤ) x.mem_band⟩

instance : SMul ℝ (ClosedPrincipalBand u) where
  smul c x := ⟨c • x.toVec, principalBand_smul_mem c x.mem_band⟩

@[simp] theorem toVec_zero : (0 : ClosedPrincipalBand u).toVec = 0 := rfl

@[simp] theorem toVec_add (x y : ClosedPrincipalBand u) :
    (x + y).toVec = x.toVec + y.toVec := rfl

@[simp] theorem toVec_neg (x : ClosedPrincipalBand u) : (-x).toVec = -x.toVec := rfl

@[simp] theorem toVec_sub (x y : ClosedPrincipalBand u) :
    (x - y).toVec = x.toVec - y.toVec := rfl

@[simp] theorem toVec_nsmul (n : ℕ) (x : ClosedPrincipalBand u) :
    (n • x).toVec = n • x.toVec := rfl

@[simp] theorem toVec_zsmul (n : ℤ) (x : ClosedPrincipalBand u) :
    (n • x).toVec = n • x.toVec := rfl

@[simp] theorem toVec_smul (c : ℝ) (x : ClosedPrincipalBand u) :
    (c • x).toVec = c • x.toVec := rfl

instance : AddCommGroup (ClosedPrincipalBand u) :=
  Function.Injective.addCommGroup toVec toVec_injective rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- Inclusion of the closed band, as an additive homomorphism. -/
def toVecAddMonoidHom : ClosedPrincipalBand u →+ E where
  toFun := toVec
  map_zero' := rfl
  map_add' := fun _ _ => rfl

instance : Module ℝ (ClosedPrincipalBand u) :=
  Function.Injective.module ℝ toVecAddMonoidHom toVec_injective fun _ _ => rfl

/-- Inclusion of the closed principal band into the ambient space. -/
def toVecₗ : ClosedPrincipalBand u →ₗ[ℝ] E where
  toFun := toVec
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

@[simp] theorem toVecₗ_apply (x : ClosedPrincipalBand u) : toVecₗ x = x.toVec := rfl

instance : PartialOrder (ClosedPrincipalBand u) where
  le x y := x.toVec ≤ y.toVec
  le_refl := fun _ => le_rfl
  le_trans := fun _ _ _ => le_trans
  le_antisymm := fun _ _ hxy hyx => ClosedPrincipalBand.ext (le_antisymm hxy hyx)

instance : Lattice (ClosedPrincipalBand u) where
  sup x y := ⟨x.toVec ⊔ y.toVec, principalBand_sup_mem x.mem_band y.mem_band⟩
  le_sup_left := fun _ _ => le_sup_left
  le_sup_right := fun _ _ => le_sup_right
  sup_le := fun _ _ _ hxz hyz => sup_le hxz hyz
  inf x y := ⟨x.toVec ⊓ y.toVec, principalBand_inf_mem x.mem_band y.mem_band⟩
  inf_le_left := fun _ _ => inf_le_left
  inf_le_right := fun _ _ => inf_le_right
  le_inf := fun _ _ _ hxy hxz => le_inf hxy hxz

@[simp] theorem toVec_sup (x y : ClosedPrincipalBand u) :
    (x ⊔ y).toVec = x.toVec ⊔ y.toVec := rfl

@[simp] theorem toVec_inf (x y : ClosedPrincipalBand u) :
    (x ⊓ y).toVec = x.toVec ⊓ y.toVec := rfl

@[simp] theorem toVec_abs (x : ClosedPrincipalBand u) : |x|.toVec = |x.toVec| := by
  simp [abs]

instance : IsOrderedAddMonoid (ClosedPrincipalBand u) where
  add_le_add_left a b hab c := by
    change (a + c).toVec ≤ (b + c).toVec
    rw [toVec_add, toVec_add]
    exact add_le_add_left (show a.toVec ≤ b.toVec from hab) c.toVec

instance : IsOrderedModule ℝ (ClosedPrincipalBand u) where
  smul_le_smul_of_nonneg_left a ha b₁ b₂ hb := by
    change (a • b₁).toVec ≤ (a • b₂).toVec
    rw [toVec_smul, toVec_smul]
    exact smul_le_smul_of_nonneg_left (show b₁.toVec ≤ b₂.toVec from hb) ha
  smul_le_smul_of_nonneg_right b hb a₁ a₂ ha := by
    change (a₁ • b).toVec ≤ (a₂ • b).toVec
    rw [toVec_smul, toVec_smul]
    exact smul_le_smul_of_nonneg_right (show a₁ ≤ a₂ from ha)
      (show (0 : E) ≤ b.toVec from hb)

instance : Norm (ClosedPrincipalBand u) where
  norm x := ‖x.toVec‖

/-- The ambient norm satisfies the normed-space axioms on the closed band. -/
theorem core : NormedSpace.Core ℝ (ClosedPrincipalBand u) where
  norm_nonneg x := by
    change 0 ≤ ‖x.toVec‖
    exact norm_nonneg _
  norm_smul c x := by
    change ‖c • x.toVec‖ = ‖c‖ * ‖x.toVec‖
    exact norm_smul c x.toVec
  norm_triangle x y := by
    change ‖x.toVec + y.toVec‖ ≤ ‖x.toVec‖ + ‖y.toVec‖
    exact norm_add_le _ _
  norm_eq_zero_iff x := by
    constructor
    · intro h
      apply ClosedPrincipalBand.ext
      change ‖x.toVec‖ = 0 at h
      exact norm_eq_zero.mp h
    · rintro rfl
      change ‖(0 : E)‖ = 0
      simp

instance : NormedAddCommGroup (ClosedPrincipalBand u) := NormedAddCommGroup.ofCore core

instance : NormedSpace ℝ (ClosedPrincipalBand u) := NormedSpace.ofCore core

instance : HasSolidNorm (ClosedPrincipalBand u) where
  solid x y hxy := by
    have hxy' : |x.toVec| ≤ |y.toVec| := by
      change |x|.toVec ≤ |y|.toVec at hxy
      simpa [toVec_abs] using hxy
    change ‖x.toVec‖ ≤ ‖y.toVec‖
    exact norm_le_norm_of_abs_le_abs hxy'

/-- A closed band in a Banach lattice is complete. -/
instance [CompleteSpace E] : CompleteSpace (ClosedPrincipalBand u) := by
  refine complete_of_cauchySeq_tendsto fun s hs => ?_
  have hE : CauchySeq fun n => (s n).toVec := by
    rw [Metric.cauchySeq_iff] at hs ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hs ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have hdist : dist (s m) (s n) < ε := hN m hm n hn
    rw [dist_eq_norm] at hdist ⊢
    change ‖(s m - s n).toVec‖ < ε at hdist
    simpa [toVec_sub] using hdist
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hE
  have hyband : y ∈ closure (principalOrderIdeal u) :=
    isClosed_closure.mem_of_tendsto hy (Eventually.of_forall fun n => (s n).mem_band)
  refine ⟨⟨y, hyband⟩, ?_⟩
  rw [Metric.tendsto_atTop] at hy ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hy ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hdist : dist (s n).toVec y < ε := hN n hn
  rw [dist_eq_norm] at hdist ⊢
  change ‖(s n - ⟨y, hyband⟩).toVec‖ < ε
  simpa [toVec_sub] using hdist

/-- The closed band of an AL-space is an AL-space. -/
theorem isAL (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖) :
    ∀ x y : ClosedPrincipalBand u, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖ := by
  intro x y hx hy
  have hx' : (0 : E) ≤ x.toVec := by
    change (0 : ClosedPrincipalBand u).toVec ≤ x.toVec at hx
    simpa [toVec_zero] using hx
  have hy' : (0 : E) ≤ y.toVec := by
    change (0 : ClosedPrincipalBand u).toVec ≤ y.toVec at hy
    simpa [toVec_zero] using hy
  change ‖x.toVec + y.toVec‖ = ‖x.toVec‖ + ‖y.toVec‖
  exact hE x.toVec y.toVec hx' hy'

variable [Fact (0 ≤ u)]

/-- The generator, viewed in its closed principal band. -/
def unit : ClosedPrincipalBand u :=
  ⟨u, subset_closure ⟨1, zero_le_one, by rw [abs_of_nonneg (Fact.out : 0 ≤ u), one_smul]⟩⟩

@[simp] theorem toVec_unit : (unit : ClosedPrincipalBand u).toVec = u := rfl

/-- The generator is nonnegative in the band. -/
theorem unit_nonneg : 0 ≤ (unit : ClosedPrincipalBand u) := by
  change (0 : ClosedPrincipalBand u).toVec ≤ unit.toVec
  rw [toVec_zero, toVec_unit]
  exact Fact.out

end ClosedPrincipalBand

/-- Linear projection onto the closed principal band, extended from the positive cone. -/
noncomputable def bandProjection (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u : E} (hu : 0 ≤ u) : E →ₗ[ℝ] E :=
  coneAdditiveLinearMap (fun x => posBandPart u x)
    (fun x y hx hy => posBandPart_add (x := x) (y := y) hE hu hx hy)
    (fun c x hc hx => posBandPart_smul (c := c) (x := x) hE hu hx hc)

/-- On the positive cone the projection is the truncation limit. -/
theorem bandProjection_apply_nonneg (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) :
    bandProjection hE hu x = posBandPart u x :=
  coneAdditiveLinearMap_apply_of_nonneg _ _ _ hx

/-- The projection is positive and contractive on the positive cone. -/
theorem bandProjection_contractive (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) :
    0 ≤ bandProjection hE hu x ∧ bandProjection hE hu x ≤ x := by
  rw [bandProjection_apply_nonneg hE hu hx]
  exact ⟨posBandPart_nonneg hE hu hx, posBandPart_le hE hu hx⟩

/-- The projection fixes its own positive values. -/
theorem posBandPart_idem (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) :
    posBandPart u (posBandPart u x) = posBandPart u x := by
  have hcut : ∀ n : ℕ, posBandPart u x ⊓ ((n : ℝ) • u) = trunc u x n := by
    intro n
    have hlim : Tendsto (fun k : ℕ => trunc u x k ⊓ ((n : ℝ) • u)) atTop
        (𝓝 (posBandPart u x ⊓ ((n : ℝ) • u))) := by
      have hpair : Tendsto (fun k : ℕ => (trunc u x k, (n : ℝ) • u)) atTop
          (𝓝 (posBandPart u x, (n : ℝ) • u)) := by
        rw [nhds_prod_eq]
        exact (posBandPart_tendsto hE hu hx).prodMk tendsto_const_nhds
      exact (continuous_inf.tendsto _).comp hpair
    have hconst : Tendsto (fun k : ℕ => trunc u x k ⊓ ((n : ℝ) • u)) atTop
        (𝓝 (trunc u x n)) := by
      refine tendsto_atTop_of_eventually_const (i₀ := n) ?_
      intro k hk
      have hmono : (n : ℝ) • u ≤ (k : ℝ) • u :=
        smul_le_smul_of_nonneg_right (by exact_mod_cast hk) hu
      rw [trunc, trunc, inf_assoc, inf_eq_right.mpr hmono]
    exact tendsto_nhds_unique hlim hconst
  apply tendsto_nhds_unique (posBandPart_tendsto hE hu (posBandPart_nonneg hE hu hx))
  exact (posBandPart_tendsto hE hu hx).congr fun n => by
    simpa [trunc] using (hcut n).symm

/-- The linear projection is idempotent. -/
theorem bandProjection_idem (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u : E} (hu : 0 ≤ u) (x : E) :
    bandProjection hE hu (bandProjection hE hu x) = bandProjection hE hu x := by
  have hpos : ∀ z : E, 0 ≤ z →
      bandProjection hE hu (bandProjection hE hu z) = bandProjection hE hu z := by
    intro z hz
    rw [bandProjection_apply_nonneg hE hu hz, bandProjection_apply_nonneg hE hu
      (posBandPart_nonneg hE hu hz), posBandPart_idem hE hu hz]
  have hx : bandProjection hE hu x =
      bandProjection hE hu x⁺ - bandProjection hE hu x⁻ := by
    have hsub := map_sub (bandProjection hE hu) x⁺ x⁻
    rwa [posPart_sub_negPart x] at hsub
  calc
    bandProjection hE hu (bandProjection hE hu x) =
        bandProjection hE hu (bandProjection hE hu x⁺) -
          bandProjection hE hu (bandProjection hE hu x⁻) := by
      have hsub := map_sub (bandProjection hE hu) (bandProjection hE hu x⁺)
        (bandProjection hE hu x⁻)
      rwa [← hx] at hsub
    _ = bandProjection hE hu x⁺ - bandProjection hE hu x⁻ := by
      rw [hpos _ (posPart_nonneg x), hpos _ (negPart_nonneg x)]
    _ = bandProjection hE hu x := hx.symm

/-- Absolute value passes inside the band projection. -/
theorem bandProjection_abs (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u : E} (hu : 0 ≤ u) (x : E) :
    |bandProjection hE hu x| = bandProjection hE hu |x| :=
  contractiveProjection_abs (fun y => bandProjection_idem hE hu y)
    (fun y hy => bandProjection_contractive (x := y) hE hu hy) x

/-- The band projection preserves binary suprema. -/
theorem bandProjection_sup (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u : E} (hu : 0 ≤ u) (x y : E) :
    bandProjection hE hu (x ⊔ y) = bandProjection hE hu x ⊔ bandProjection hE hu y := by
  have htwo : (2 : ℝ) • (bandProjection hE hu (x ⊔ y)) =
      (2 : ℝ) • (bandProjection hE hu x ⊔ bandProjection hE hu y) := by
    calc
      (2 : ℝ) • (bandProjection hE hu (x ⊔ y)) =
          bandProjection hE hu ((2 : ℝ) • (x ⊔ y)) :=
        (map_smul (bandProjection hE hu) (2 : ℝ) (x ⊔ y)).symm
      _ = bandProjection hE hu ((2 : ℕ) • (x ⊔ y)) := by
        congr 1
        exact Nat.cast_smul_eq_nsmul ℝ 2 (x ⊔ y)
      _ = bandProjection hE hu (x + y + |y - x|) := by
        rw [two_nsmul_sup_eq_add_add_abs_sub]
      _ = bandProjection hE hu x + bandProjection hE hu y +
          bandProjection hE hu |y - x| := by rw [map_add, map_add]
      _ = bandProjection hE hu x + bandProjection hE hu y +
          |bandProjection hE hu (y - x)| := by
        rw [← bandProjection_abs hE hu (y - x)]
      _ = bandProjection hE hu x + bandProjection hE hu y +
          |bandProjection hE hu y - bandProjection hE hu x| := by rw [map_sub]
      _ = (2 : ℕ) • (bandProjection hE hu x ⊔ bandProjection hE hu y) := by
        rw [two_nsmul_sup_eq_add_add_abs_sub]
      _ = (2 : ℝ) • (bandProjection hE hu x ⊔ bandProjection hE hu y) :=
        (Nat.cast_smul_eq_nsmul ℝ 2 _).symm
  have hcancel := congrArg (fun z : E => (2 : ℝ)⁻¹ • z) htwo
  rw [smul_smul, smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), one_smul, one_smul]
    at hcancel
  exact hcancel

/-- The projection is norm-contractive. -/
theorem bandProjection_norm_le (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u : E} (hu : 0 ≤ u) (x : E) : ‖bandProjection hE hu x‖ ≤ ‖x‖ := by
  apply norm_le_norm_of_abs_le_abs
  rw [bandProjection_abs hE hu x]
  exact (bandProjection_contractive hE hu (abs_nonneg x)).2

/-- The band projection as a continuous linear map. -/
noncomputable def bandProjectionCLM (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u : E} (hu : 0 ≤ u) : E →L[ℝ] E :=
  (bandProjection hE hu).mkContinuous 1 fun x => by
    simpa using bandProjection_norm_le hE hu x

/-- The projection lands in the closed principal band. -/
theorem bandProjection_mem_closure (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u : E} (hu : 0 ≤ u) (x : E) :
    bandProjection hE hu x ∈ closure (principalOrderIdeal u) := by
  have hdecomp : bandProjection hE hu x = posBandPart u x⁺ - posBandPart u x⁻ := by
    nth_rw 1 [← posPart_sub_negPart x]
    rw [map_sub, bandProjection_apply_nonneg hE hu (posPart_nonneg x),
      bandProjection_apply_nonneg hE hu (negPart_nonneg x)]
  rw [hdecomp]
  exact principalBand_sub_mem
    (posBandPart_mem_closure hE hu (posPart_nonneg x))
    (posBandPart_mem_closure hE hu (negPart_nonneg x))

/-- Every ideal element is fixed by the band projection. -/
theorem bandProjection_eq_of_mem_ideal (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u x : E} (hu : 0 ≤ u) (hx : x ∈ principalOrderIdeal u) :
    bandProjection hE hu x = x := by
  obtain ⟨c, hc, hxc⟩ := hx
  have hpos : posBandPart u x⁺ = x⁺ := by
    apply posBandPart_of_le_smul hE hu (posPart_nonneg x) hc
    have hle : x⁺ ≤ |x| := by
      rw [← posPart_add_negPart x]
      exact le_add_of_nonneg_right (negPart_nonneg x)
    exact hle.trans hxc
  have hneg : posBandPart u x⁻ = x⁻ := by
    apply posBandPart_of_le_smul hE hu (negPart_nonneg x) hc
    have hle : x⁻ ≤ |x| := by
      rw [← posPart_add_negPart x]
      exact le_add_of_nonneg_left (posPart_nonneg x)
    exact hle.trans hxc
  have hx' : bandProjection hE hu x =
      bandProjection hE hu x⁺ - bandProjection hE hu x⁻ := by
    have hsub := map_sub (bandProjection hE hu) x⁺ x⁻
    rwa [posPart_sub_negPart x] at hsub
  rw [hx', bandProjection_apply_nonneg hE hu (posPart_nonneg x),
    bandProjection_apply_nonneg hE hu (negPart_nonneg x), hpos, hneg, posPart_sub_negPart]

/-- Every vector of the closed band is fixed by the projection. -/
theorem bandProjection_eq_of_mem_closure (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u x : E} (hu : 0 ≤ u) (hx : x ∈ closure (principalOrderIdeal u)) :
    bandProjection hE hu x = x := by
  obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.mp hx
  have hfix : ∀ n, bandProjection hE hu (s n) = s n :=
    fun n => bandProjection_eq_of_mem_ideal hE hu (hs n)
  have hP : Tendsto (fun n => bandProjection hE hu (s n)) atTop
      (𝓝 (bandProjection hE hu x)) :=
    ((bandProjectionCLM hE hu).continuous.tendsto x).comp hlim
  exact tendsto_nhds_unique hP (by simpa [hfix] using hlim)

/-- The generator is a weak unit of its closed principal band. -/
theorem closedPrincipalBand_weakUnit (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u : E} [Fact (0 ≤ u)] :
    latticeDisjointComplement {(ClosedPrincipalBand.unit : ClosedPrincipalBand u)} ⊆ {0} := by
  have hu : 0 ≤ u := Fact.out
  intro x hx
  have hdisj : |x.toVec| ⊓ u = 0 := by
    have h := hx ClosedPrincipalBand.unit (Set.mem_singleton _)
    have h' : (|x| ⊓ |ClosedPrincipalBand.unit|).toVec = 0 := by
      simpa [LatticeDisjoint, ClosedPrincipalBand.toVec_zero] using
        congrArg ClosedPrincipalBand.toVec h
    simpa [ClosedPrincipalBand.toVec_inf, ClosedPrincipalBand.toVec_abs,
      ClosedPrincipalBand.toVec_unit, abs_of_nonneg hu] using h'
  have hzero : |x.toVec| = 0 := by
    have hfix := bandProjection_eq_of_mem_closure hE hu
      (principalBand_abs_mem x.mem_band)
    have hP : bandProjection hE hu |x.toVec| = 0 := by
      rw [bandProjection_apply_nonneg hE hu (abs_nonneg _)]
      exact posBandPart_eq_zero_of_disjoint hE hu (abs_nonneg _) hdisj
    exact hfix.symm.trans hP
  have hx0 : x.toVec = 0 := by
    apply le_antisymm
    · rw [← hzero, abs]; exact le_sup_left
    · have hneg : -x.toVec ≤ 0 := by rw [← hzero, abs]; exact le_sup_right
      exact neg_nonpos.mp hneg
  exact ClosedPrincipalBand.ext hx0

/-- Data of an L¹ representation of one closed principal band. -/
structure BandComponent (u : E) where
  /-- Carrier of the representation. -/
  X : Type u
  /-- Sigma-algebra on the carrier. -/
  mSpace : MeasurableSpace X
  /-- Representing measure. -/
  μ : @Measure X mSpace
  /-- Lattice isometry of the closed band onto real L¹. -/
  rep : ClosedPrincipalBand u ≃ₗᵢ[ℝ] @Lp X ℝ mSpace _ 1 μ
  /-- The isometry preserves binary suprema. -/
  preserves_sup : ∀ x y : ClosedPrincipalBand u, rep (x ⊔ y) = rep x ⊔ rep y

/-- Every nonnegative vector's closed band admits an L¹ representation. -/
theorem bandComponent_nonempty (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u : E} (hu : 0 ≤ u) : Nonempty (BandComponent u) := by
  let : Fact (0 ≤ u) := ⟨hu⟩
  obtain ⟨X, m, μ, U, hsup⟩ := exists_al_representation_of_weakUnit
    (E := ClosedPrincipalBand u) (ClosedPrincipalBand.isAL hE)
    ClosedPrincipalBand.unit_nonneg (closedPrincipalBand_weakUnit hE)
  exact ⟨⟨X, m, μ, U, hsup⟩⟩

/-- Chosen L¹ representation of the closed band of a nonnegative vector. -/
noncomputable def bandComponent (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖)
    [CompleteSpace E] {u : E} (hu : 0 ≤ u) : BandComponent u :=
  Classical.choice (bandComponent_nonempty hE hu)

section IndexProj

variable (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖) [CompleteSpace E]

/-- Projection onto the closed band of one vector of the maximal family. -/
noncomputable def indexProjection {u : E} (hu : u ∈ maximalPositiveDisjointFamily) :
    E →ₗ[ℝ] E :=
  bandProjection hE (le_of_lt ((maximalPositiveDisjointFamily_spec (E := E)).1.1 u hu))

/-- On the positive cone the index projection is the truncation limit. -/
theorem indexProjection_apply_nonneg (i : bandIndex) {x : E} (hx : 0 ≤ x) :
    indexProjection hE i.mem_family x = posBandPart i.vec x :=
  bandProjection_apply_nonneg hE (bandIndex_nonneg i) hx

/-- Absolute value passes inside an index projection. -/
theorem indexProjection_abs (i : bandIndex) (x : E) :
    |indexProjection hE i.mem_family x| = indexProjection hE i.mem_family |x| :=
  bandProjection_abs hE (bandIndex_nonneg i) x

/-- The index projection agrees with the continuous band projection. -/
theorem indexProjection_eq_clm (i : bandIndex) (x : E) :
    indexProjection hE i.mem_family x = (bandProjectionCLM hE (bandIndex_nonneg i)) x :=
  rfl

/-- Distinct index vectors meet in zero. -/
theorem bandIndex_inf_eq_zero {i j : bandIndex} (hij : i ≠ j) : i.vec ⊓ j.vec = (0 : E) := by
  have h : LatticeDisjoint (E := E) i.vec j.vec := bandIndex_disjoint (i := i) (j := j) hij
  simpa [LatticeDisjoint, abs_of_nonneg (bandIndex_nonneg i),
    abs_of_nonneg (bandIndex_nonneg j)] using h

/-- Projections of one vector onto distinct bands are lattice disjoint. -/
theorem indexProjection_latticeDisjoint {i j : bandIndex} (hij : i ≠ j) (x : E) :
    LatticeDisjoint (E := E) (indexProjection hE i.mem_family x)
      (indexProjection hE j.mem_family x) := by
  rw [LatticeDisjoint, indexProjection_abs hE i x, indexProjection_abs hE j x,
    indexProjection_apply_nonneg hE i (abs_nonneg x),
    indexProjection_apply_nonneg hE j (abs_nonneg x)]
  exact posBandPart_disjoint_of_disjoint hE (bandIndex_nonneg i) (bandIndex_nonneg j)
    (abs_nonneg x) (bandIndex_inf_eq_zero hij)

/-- A positive band part is disjoint from every other index vector. -/
theorem indexProjection_inf_vec_eq_zero {i j : bandIndex} (hij : i ≠ j) {x : E} (hx : 0 ≤ x) :
    indexProjection hE i.mem_family x ⊓ j.vec = 0 := by
  rw [indexProjection_apply_nonneg hE i hx]
  have htrunc : ∀ n, trunc i.vec x n ⊓ j.vec = 0 := by
    intro n
    refine le_antisymm ?_ (le_inf (trunc_nonneg (bandIndex_nonneg i) hx n) (bandIndex_nonneg j))
    calc
      trunc i.vec x n ⊓ j.vec ≤ ((n : ℝ) • i.vec) ⊓ j.vec :=
        inf_le_inf_right _ inf_le_right
      _ = 0 := inf_smul_eq_zero (Nat.cast_nonneg n) (bandIndex_nonneg i) (bandIndex_nonneg j)
        (bandIndex_inf_eq_zero hij)
  have hlim : Tendsto (fun n => trunc i.vec x n ⊓ j.vec) atTop
      (𝓝 (posBandPart i.vec x ⊓ j.vec)) := by
    have hpair : Tendsto (fun n => (trunc i.vec x n, j.vec)) atTop
        (𝓝 (posBandPart i.vec x, j.vec)) := by
      rw [nhds_prod_eq]
      exact (posBandPart_tendsto hE (bandIndex_nonneg i) hx).prodMk tendsto_const_nhds
    exact (continuous_inf.tendsto _).comp hpair
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun n => (htrunc n).symm)

/-- The projection onto one band kills the positive part in a different band. -/
theorem indexProjection_cross_eq_zero {i j : bandIndex} (hij : i ≠ j) {x : E} (hx : 0 ≤ x) :
    indexProjection hE j.mem_family (indexProjection hE i.mem_family x) = 0 := by
  have hnonneg : 0 ≤ indexProjection hE i.mem_family x :=
    (bandProjection_contractive hE (bandIndex_nonneg i) hx).1
  rw [indexProjection_apply_nonneg hE j hnonneg]
  exact posBandPart_eq_zero_of_disjoint hE (bandIndex_nonneg j) hnonneg
    (indexProjection_inf_vec_eq_zero hE hij hx)

include hE in
/-- Each truncation lies below the band part. -/
theorem trunc_le_posBandPart {u x : E} (hu : 0 ≤ u) (hx : 0 ≤ x) (n : ℕ) :
    trunc u x n ≤ posBandPart u x := by
  apply (isClosed_Ici (a := trunc u x n)).mem_of_tendsto (posBandPart_tendsto hE hu hx)
  rw [eventually_atTop]
  exact ⟨n, fun m hm => trunc_mono hu hx hm⟩

/-- A finite sum of positive band parts is at most the vector. -/
theorem sum_indexProjection_le {x : E} (hx : 0 ≤ x) (s : Finset bandIndex) :
    ∑ i ∈ s, indexProjection hE i.mem_family x ≤ x := by
  classical
  induction s using Finset.induction with
  | empty => simp [hx]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hterm : ∀ i ∈ s, LatticeDisjoint (E := E) (indexProjection hE a.mem_family x)
        (indexProjection hE i.mem_family x) := by
      intro i hi
      have hne : a ≠ i := by
        intro h
        exact ha (h ▸ hi)
      exact indexProjection_latticeDisjoint hE hne x
    have hrest := latticeDisjoint_sum hterm
    have ha0 : 0 ≤ indexProjection hE a.mem_family x :=
      (bandProjection_contractive hE (bandIndex_nonneg a) hx).1
    have hs0 : 0 ≤ ∑ i ∈ s, indexProjection hE i.mem_family x :=
      Finset.sum_nonneg fun i hi => (bandProjection_contractive hE (bandIndex_nonneg i) hx).1
    have hinf : indexProjection hE a.mem_family x ⊓
        ∑ i ∈ s, indexProjection hE i.mem_family x = 0 := by
      simpa [LatticeDisjoint, abs_of_nonneg ha0, abs_of_nonneg hs0] using hrest
    rw [add_eq_sup_of_inf_eq_zero hinf]
    exact sup_le (bandProjection_contractive hE (bandIndex_nonneg a) hx).2 ih

/-- Norms add on finite sums of the band projections. -/
theorem norm_sum_indexProjection hE (x : E) (s : Finset bandIndex) :
    ‖∑ i ∈ s, indexProjection hE i.mem_family x‖ =
      ∑ i ∈ s, ‖indexProjection hE i.mem_family x‖ := by
  refine norm_sum_of_pairwise_latticeDisjoint hE ?_
  intro i _hi j _hj hij
  exact indexProjection_latticeDisjoint hE hij x

/-- The real series of projection norms converges. -/
theorem summable_norm_indexProjection hE (x : E) :
    Summable fun i : bandIndex => ‖indexProjection hE i.mem_family x‖ := by
  refine summable_of_sum_le (c := ‖x‖) (fun i => norm_nonneg (indexProjection hE i.mem_family x)) ?_
  intro s
  have hnorm : ∀ i : bandIndex, ‖indexProjection hE i.mem_family x‖ =
      ‖indexProjection hE i.mem_family |x|‖ := by
    intro i
    rw [← norm_abs_eq_norm (indexProjection hE i.mem_family x), indexProjection_abs hE i x]
  rw [Finset.sum_congr rfl fun i _ => hnorm i, ← norm_sum_indexProjection hE |x| s]
  apply norm_le_norm_of_abs_le_abs
  have hsum0 : 0 ≤ ∑ i ∈ s, indexProjection hE i.mem_family |x| :=
    Finset.sum_nonneg fun i _ => by
      rw [indexProjection_apply_nonneg hE i (abs_nonneg x)]
      exact posBandPart_nonneg hE (bandIndex_nonneg i) (abs_nonneg x)
  rw [abs_of_nonneg hsum0]
  exact sum_indexProjection_le hE (abs_nonneg x) s

/-- The band projections of one vector form a summable family. -/
theorem summable_indexProjection hE (x : E) :
    Summable fun i : bandIndex => indexProjection hE i.mem_family x :=
  Summable.of_norm (summable_norm_indexProjection hE x)

/-- A nonnegative vector is the sum of its band projections. -/
theorem indexProjection_tsum_nonneg {x : E} (hx : 0 ≤ x) :
    ∑' (i : bandIndex), indexProjection hE i.mem_family x = x := by
  have hsumm := summable_indexProjection hE x
  set s := ∑' (i : bandIndex), indexProjection hE i.mem_family x with hs
  have hsle : s ≤ x := by
    rw [hs]
    have hmem := (isClosed_Iic (a := x)).mem_of_tendsto hsumm.hasSum
      (Eventually.of_forall fun t => sum_indexProjection_le hE hx t)
    simpa [mem_Iic] using hmem
  set r := x - s with hr
  have hr0 : 0 ≤ r := sub_nonneg.mpr hsle
  have hPk : ∀ k : bandIndex, indexProjection hE k.mem_family s =
      indexProjection hE k.mem_family x := by
    intro k
    rw [hs]
    have hzero : ∀ i : bandIndex, i ≠ k → (bandProjectionCLM hE (bandIndex_nonneg k))
        (indexProjection hE i.mem_family x) = 0 := by
      intro i hi
      rw [← indexProjection_eq_clm hE k]
      exact indexProjection_cross_eq_zero hE hi hx
    rw [indexProjection_eq_clm hE k,
      (bandProjectionCLM hE (bandIndex_nonneg k)).map_tsum hsumm,
      (hasSum_single k hzero).tsum_eq, ← indexProjection_eq_clm hE k]
    exact bandProjection_idem hE (bandIndex_nonneg k) x
  have hPr : ∀ k : bandIndex, indexProjection hE k.mem_family r = 0 := by
    intro k
    rw [hr, map_sub, hPk k, sub_self]
  suffices hr : r = 0 by
    exact (sub_eq_zero.mp hr).symm
  by_contra hne
  have hlt : (0 : E) < r := lt_of_le_of_ne hr0 (Ne.symm hne)
  have hdisj : ∀ u ∈ maximalPositiveDisjointFamily, r ⊓ u = 0 := by
    intro u hu
    let k : bandIndex := ⟨u, hu⟩
    have hle : trunc u r 1 ≤ posBandPart u r :=
      trunc_le_posBandPart hE (bandIndex_nonneg k) hr0 1
    have hP : posBandPart u r = 0 := by
      rw [← indexProjection_apply_nonneg hE k hr0]
      exact hPr k
    have htrunc : trunc u r 1 = r ⊓ u := by simp [trunc, one_smul]
    exact le_antisymm (by simpa [htrunc, hP] using hle) (le_inf hr0 (bandIndex_nonneg k))
  by_cases hmem : r ∈ maximalPositiveDisjointFamily
  · let k : bandIndex := ⟨r, hmem⟩
    have hfix : indexProjection hE k.mem_family r = r := by
      rw [indexProjection_apply_nonneg hE k hr0]
      exact posBandPart_of_le_smul hE (bandIndex_nonneg k) hr0 zero_le_one
        (le_of_eq (one_smul ℝ r).symm)
    exact hne (hfix.symm.trans (hPr k))
  · let S := insert r maximalPositiveDisjointFamily
    have hS : IsPositiveDisjointFamily (E := E) S := by
      constructor
      · intro y hy
        rcases Set.mem_insert_iff.mp hy with rfl | hy
        · exact hlt
        · exact (maximalPositiveDisjointFamily_spec (E := E)).1.1 y hy
      · intro a ha b hb hab
        rcases Set.mem_insert_iff.mp ha with rfl | ha
        · rcases Set.mem_insert_iff.mp hb with rfl | hb
          · exact (hab rfl).elim
          · have hzero : r ⊓ b = 0 := hdisj b hb
            simpa [LatticeDisjoint, abs_of_nonneg hr0,
              abs_of_nonneg ((maximalPositiveDisjointFamily_spec (E := E)).1.1 b hb).le] using
              hzero
        · rcases Set.mem_insert_iff.mp hb with rfl | hb
          · have hzero : a ⊓ r = 0 := by simpa [inf_comm] using hdisj a ha
            simpa [LatticeDisjoint, abs_of_nonneg hr0,
              abs_of_nonneg ((maximalPositiveDisjointFamily_spec (E := E)).1.1 a ha).le] using
              hzero
          · exact (maximalPositiveDisjointFamily_spec (E := E)).1.2 ha hb hab
    have hsub : maximalPositiveDisjointFamily ⊆ S := subset_insert _ _
    have hneS : maximalPositiveDisjointFamily ≠ S := by
      intro hEq
      exact hmem (hEq ▸ mem_insert r _)
    exact hneS (Maximal.eq_of_subset (maximalPositiveDisjointFamily_spec (E := E)).2 hS hsub)

/-- Every vector is the sum of its band projections. -/
theorem indexProjection_tsum (x : E) :
    ∑' (i : bandIndex), indexProjection hE i.mem_family x = x := by
  have hlin : ∀ i : bandIndex, indexProjection hE i.mem_family x =
      indexProjection hE i.mem_family x⁺ - indexProjection hE i.mem_family x⁻ := by
    intro i
    have hsub := map_sub (indexProjection hE i.mem_family) x⁺ x⁻
    rwa [posPart_sub_negPart x] at hsub
  calc
    ∑' (i : bandIndex), indexProjection hE i.mem_family x
        = ∑' (i : bandIndex),
            (indexProjection hE i.mem_family x⁺ - indexProjection hE i.mem_family x⁻) :=
      tsum_congr hlin
    _ = (∑' (i : bandIndex), indexProjection hE i.mem_family x⁺) -
          ∑' (i : bandIndex), indexProjection hE i.mem_family x⁻ :=
      Summable.tsum_sub (summable_indexProjection hE x⁺) (summable_indexProjection hE x⁻)
    _ = x⁺ - x⁻ := by
      rw [indexProjection_tsum_nonneg hE (posPart_nonneg x),
        indexProjection_tsum_nonneg hE (negPart_nonneg x)]
    _ = x := (posPart_sub_negPart x)

/-- The series of projection norms recovers the norm. -/
theorem tsum_norm_indexProjection hE {x : E} (hx : 0 ≤ x) :
    ∑' (i : bandIndex), ‖indexProjection hE i.mem_family x‖ = ‖x‖ := by
  have hv : Tendsto (fun t : Finset bandIndex => ∑ i ∈ t, indexProjection hE i.mem_family x) atTop
      (𝓝 x) := by
    have hsum := (summable_indexProjection hE x).hasSum
    rwa [indexProjection_tsum_nonneg hE hx] at hsum
  have hn : Tendsto (fun t : Finset bandIndex => ∑ i ∈ t, ‖indexProjection hE i.mem_family x‖)
      atTop (𝓝 ‖x‖) := by
    refine ((continuous_norm.tendsto x).comp hv).congr fun t => ?_
    rw [Function.comp_apply, norm_sum_indexProjection hE x t]
  exact tendsto_nhds_unique (summable_norm_indexProjection hE x).hasSum hn

/-- Projection norms add to the ambient norm for every vector. -/
theorem tsum_norm_indexProjection_eq (x : E) :
    ∑' (i : bandIndex), ‖indexProjection hE i.mem_family x‖ = ‖x‖ := by
  have hterm : ∀ i : bandIndex, ‖indexProjection hE i.mem_family x‖ =
      ‖indexProjection hE i.mem_family |x|‖ := by
    intro i
    rw [← norm_abs_eq_norm (indexProjection hE i.mem_family x), indexProjection_abs hE i x]
  rw [tsum_congr hterm, tsum_norm_indexProjection hE (abs_nonneg x), norm_abs_eq_norm]

end IndexProj

end CKMA
