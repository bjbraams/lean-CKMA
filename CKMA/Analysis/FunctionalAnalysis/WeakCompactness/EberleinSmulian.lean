/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import CKMA.Analysis.FunctionalAnalysis.WeakCompactness.Norming
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Sequences

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Eberlein–Šmulian

Relative weak compactness of a subset of a Banach space is equivalent to relative weak sequential
compactness. The forward implication uses that the weak closure of a sequence lies in a separable
closed real subspace, hence is metrizable once countably many functionals separate its points.
The converse follows Whitley's finite-dimensional norming lemma in the form recorded by Vogt: every
weak-star cluster point of the canonical image in the bidual already lies in that image, so
Mathlib's `NormedSpace.isCompact_closure_of_isBounded` supplies weak compactness.

A weak limit lies in the closed real convex hull. That is the statement of TauCeti's Mazur lemma;
the short argument below is taken from that development and proved from Mathlib's
`Convex.toWeakSpace_closure`, because the TauCeti file is not on the import path.
-/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

namespace CKMA.EberleinSmulian

open Bornology Filter Metric NormedSpace Set Topology TopologicalSpace
open scoped BigOperators

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Scalar convergence along a sequence that converges in `WeakSpace`. -/
theorem tendsto_eval_of_tendsto_toWeakSpace {u : ℕ → E} {x : E}
    (hu : Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x)))
    (f : StrongDual 𝕜 E) : Tendsto (fun n ↦ f (u n)) atTop (𝓝 (f x)) := by
  have hinj : Function.Injective (topDualPairing 𝕜 E).flip := by
    intro a b h
    exact SeparatingDual.eq_iff_forall_dual_eq.2 fun ℓ ↦ congrArg (fun g ↦ g ℓ) h
  exact ((WeakBilin.tendsto_iff_forall_eval_tendsto (topDualPairing 𝕜 E).flip hinj).mp hu) f

/-- A weakly convergent sequence is norm-bounded, by Banach–Steinhaus on the dual. -/
theorem isBounded_range_of_tendsto_toWeakSpace {u : ℕ → E} {x : E}
    (hu : Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x))) :
    IsBounded (range u) := by
  rw [isBounded_iff_forall_norm_le]
  have hpt : ∀ f : StrongDual 𝕜 E, ∃ C : ℝ, ∀ n, ‖f (u n)‖ ≤ C := by
    intro f
    obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le).1
      (isBounded_range_of_tendsto (fun n ↦ f (u n)) (tendsto_eval_of_tendsto_toWeakSpace hu f))
    exact ⟨C, fun n ↦ hC (f (u n)) (mem_range_self n)⟩
  obtain ⟨C', hC'⟩ := banach_steinhaus
    (g := fun n : ℕ ↦ inclusionInDoubleDual 𝕜 E (u n)) hpt
  refine ⟨C', fun y hy ↦ ?_⟩
  obtain ⟨n, rfl⟩ := hy
  have hcoe : inclusionInDoubleDualLi (𝕜 := 𝕜) (E := E) (u n) =
      inclusionInDoubleDual 𝕜 E (u n) := rfl
  have hnorm : ‖u n‖ = ‖inclusionInDoubleDual 𝕜 E (u n)‖ := by
    rw [← hcoe]
    exact ((inclusionInDoubleDualLi (𝕜 := 𝕜) (E := E)).norm_map (u n)).symm
  exact hnorm.trans_le (hC' n)

/-- A weak limit lies in the norm-closed `𝕜`-span of the sequence.
Real convex combinations suffice, and a `𝕜`-submodule is an `ℝ`-submodule. -/
theorem mem_topologicalClosure_span_of_tendsto_toWeakSpace {u : ℕ → E} {x : E}
    (hu : Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x))) :
    x ∈ (Submodule.span 𝕜 (range u)).topologicalClosure := by
  letI : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  letI : Module ℝ E := .restrictScalars ℝ 𝕜 E
  haveI : IsScalarTower ℝ 𝕜 E := .restrictScalars ℝ 𝕜 E
  haveI : LocallyConvexSpace ℝ E := NormedSpace.toLocallyConvexSpace' 𝕜
  have hx : x ∈ closure (convexHull ℝ (range u)) := by
    have hx' : toWeakSpace 𝕜 E x ∈ closure (toWeakSpace 𝕜 E '' convexHull ℝ (range u)) :=
      mem_closure_of_tendsto hu (.of_forall fun n ↦
        mem_image_of_mem _ (subset_convexHull ℝ _ (mem_range_self n)))
    rw [← (convex_convexHull ℝ (range u)).toWeakSpace_closure 𝕜] at hx'
    exact (toWeakSpace 𝕜 E).injective.mem_set_image.mp hx'
  have hR : convexHull ℝ (range u) ⊆ (Submodule.span ℝ (range u) : Set E) :=
    convexHull_min Submodule.subset_span (Submodule.span ℝ (range u)).convex
  have htower : (Submodule.span ℝ (range u) : Set E) ⊆ (Submodule.span 𝕜 (range u) : Set E) :=
    Submodule.span_subset_span ℝ 𝕜 (range u)
  have hcl : x ∈ closure (Submodule.span 𝕜 (range u) : Set E) :=
    closure_mono (hR.trans htower) hx
  rw [← Submodule.topologicalClosure_coe] at hcl
  rwa [SetLike.mem_coe] at hcl

/-- Evaluation of the weak bidual embedding on the original space. -/
theorem inclusionInDoubleDualWeak_toWeakSpace_apply (x : E) (f : StrongDual 𝕜 E) :
    inclusionInDoubleDualWeak 𝕜 E (toWeakSpace 𝕜 E x) f = f x := by
  rw [← ContinuousLinearMap.coe_coe, toLinearMap_inclusionInDoubleDualWeak]
  simp [LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply, dual_def]

/-- A point of the weak-star closure is approximated on any finite list of functionals. -/
theorem exists_close_on_list (s : Set E) (phiW : WeakDual 𝕜 (StrongDual 𝕜 E))
    (hphi : phiW ∈ closure (inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' s)))
    (F : List (StrongDual 𝕜 E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ s, ∀ f ∈ F, ‖phiW f - f x‖ < ε := by
  let evals : WeakDual 𝕜 (StrongDual 𝕜 E) → Fin F.length → 𝕜 := fun psi i ↦ psi (F.get i)
  let target : Set (Fin F.length → 𝕜) := pi univ fun i ↦ ball (phiW (F.get i)) ε
  have hopen : IsOpen target := isOpen_set_pi finite_univ fun _ _ ↦ isOpen_ball
  have hcont : Continuous evals := continuous_pi fun i ↦ WeakDual.eval_continuous (F.get i)
  have hmem : phiW ∈ evals ⁻¹' target := by
    intro i
    simp [evals, mem_ball, dist_self, hε]
  obtain ⟨psi, hpsi⟩ :=
    (mem_closure_iff.mp hphi) (evals ⁻¹' target) (hopen.preimage hcont) hmem
  obtain ⟨hpsi, hA⟩ := hpsi
  obtain ⟨w, hw, rfl⟩ := hA
  obtain ⟨x, hx, rfl⟩ := hw
  refine ⟨x, hx, (List.forall_mem_iff_get).2 fun i ↦ ?_⟩
  have hi := hpsi i
  simpa [evals, mem_ball, dist_eq_norm, norm_sub_rev,
    inclusionInDoubleDualWeak_toWeakSpace_apply] using hi

/-- Generators of the bidual span used at one stage: the cluster point and the embedded vectors. -/
def generators (phiW : WeakDual 𝕜 (StrongDual 𝕜 E)) {n : ℕ} (a : Fin (n + 1) → E) :
    Option (Fin (n + 1)) → StrongDual 𝕜 (StrongDual 𝕜 E)
  | none => WeakDual.toStrongDual phiW
  | some i => inclusionInDoubleDual 𝕜 E (a i)

/-- The bidual span normed at one stage of the construction. -/
def stepSpan (phiW : WeakDual 𝕜 (StrongDual 𝕜 E)) {n : ℕ} (a : Fin (n + 1) → E) :
    Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  Submodule.span 𝕜 (range (generators phiW a))

/-- One stage of Vogt's chain: vectors from `s`, and a finite norming list in the dual ball. -/
structure VogtStep (phiW : WeakDual 𝕜 (StrongDual 𝕜 E)) (s : Set E) (n : ℕ) where
  /-- Vectors chosen through this stage, in order. -/
  a : Fin (n + 1) → E
  /-- Every chosen vector lies in `s`. -/
  mem_a : ∀ i, a i ∈ s
  /-- Dual ball vectors that norm the stage span. -/
  F : List (StrongDual 𝕜 E)
  /-- Each norming functional has norm at most one. -/
  norm_F : ∀ f ∈ F, ‖f‖ ≤ 1
  /-- The list norms the stage span up to the factor two. -/
  norming : ∀ z ∈ stepSpan phiW a, ‖z‖ ≠ 0 → ∃ f ∈ F, ‖z‖ ≤ 2 * ‖z f‖
  /-- Norming list of the previous stage. Empty at stage zero. -/
  prev : List (StrongDual 𝕜 E)
  /-- The previous list is retained. -/
  prev_sub : ∀ f ∈ prev, f ∈ F
  /-- Positive denominator of the approximation forced at this stage. -/
  closeDen : ℕ
  /-- The denominator is positive. -/
  closeDen_pos : 0 < closeDen
  /-- The newest vector approximates the cluster point on the previous list. -/
  close : ∀ f ∈ prev, ‖WeakDual.toStrongDual phiW f -
      inclusionInDoubleDual 𝕜 E (a (Fin.last n)) f‖ < 1 / (closeDen : ℝ)

variable (s : Set E)

/-- The first stage, from one point of `s`. The approximation constraint is vacuous. -/
def initial (phiW : WeakDual 𝕜 (StrongDual 𝕜 E)) {x0 : E} (hx0 : x0 ∈ s) : VogtStep phiW s 0 :=
  let a : Fin 1 → E := fun _ ↦ x0
  let hF := exists_list_norming (generators phiW a)
  { a := a
    mem_a := fun _ ↦ hx0
    F := Classical.choose hF
    norm_F := (Classical.choose_spec hF).1
    norming := (Classical.choose_spec hF).2
    prev := []
    prev_sub := by intro _ h; cases h
    closeDen := 1
    closeDen_pos := Nat.one_pos
    close := by intro _ h; cases h }

/-- Extend a stage by a vector close to the cluster point on the current norming list, then
renorm the enlarged span. -/
def extend (phiW : WeakDual 𝕜 (StrongDual 𝕜 E))
    (hphi : phiW ∈ closure (inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' s)))
    {n : ℕ} (c : VogtStep phiW s n) : VogtStep phiW s (n + 1) := by
  let eps : ℝ := 1 / ((n + 1 : ℕ) : ℝ)
  have heps : 0 < eps := by positivity
  let x : E := Classical.choose (exists_close_on_list s phiW hphi c.F heps)
  have hx := Classical.choose_spec (exists_close_on_list s phiW hphi c.F heps)
  let a' : Fin (n + 2) → E := Fin.snoc c.a x
  let hF := exists_list_norming (generators phiW a')
  let Fnew := Classical.choose hF
  exact
    { a := a'
      mem_a := by
        intro i
        refine Fin.lastCases ?_ ?_ i
        · simpa [a', Fin.snoc_last] using hx.1
        · intro j
          simpa [a', Fin.snoc_castSucc] using c.mem_a j
      F := c.F ++ Fnew
      norm_F := by
        intro f hf
        rw [List.mem_append] at hf
        rcases hf with hf | hf
        · exact c.norm_F f hf
        · exact (Classical.choose_spec hF).1 f hf
      norming := by
        intro z hz hznz
        obtain ⟨f, hf, hle⟩ := (Classical.choose_spec hF).2 z hz hznz
        exact ⟨f, List.mem_append_right _ hf, hle⟩
      prev := c.F
      prev_sub := fun f hf ↦ List.mem_append_left _ hf
      closeDen := n + 1
      closeDen_pos := Nat.succ_pos n
      close := by
        intro f hf
        have hlast : a' (Fin.last (n + 1)) = x := by simp [a', Fin.snoc_last]
        rw [hlast, WeakDual.toStrongDual_apply, NormedSpace.dual_def]
        exact hx.2 f hf }

variable (phiW : WeakDual 𝕜 (StrongDual 𝕜 E))
variable (hphi : phiW ∈ closure (inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' s)))

/-- Vogt's chain. Stage `n` carries `n + 1` vectors of `s`. -/
def chain {x0 : E} (hx0 : x0 ∈ s) : (n : ℕ) → VogtStep phiW s n
  | 0 => initial s phiW hx0
  | n + 1 => extend s phiW hphi (chain hx0 n)

/-- The newest vector at stage `n`. -/
def aSeq {x0 : E} (hx0 : x0 ∈ s) (n : ℕ) : E :=
  (chain s phiW hphi hx0 n).a (Fin.last n)

/-- Unfold one step of the chain. -/
theorem chain_succ {x0 : E} (hx0 : x0 ∈ s) (n : ℕ) :
    chain s phiW hphi hx0 (n + 1) = extend s phiW hphi (chain s phiW hphi hx0 n) := rfl

/-- The vector chosen at stage `n` lies in `s`. -/
theorem aSeq_mem {x0 : E} (hx0 : x0 ∈ s) (n : ℕ) : aSeq s phiW hphi hx0 n ∈ s :=
  (chain s phiW hphi hx0 n).mem_a (Fin.last n)

/-- Earlier coordinates of stage `n` are the vectors chosen at those stages. -/
theorem chain_a {x0 : E} (hx0 : x0 ∈ s) (n : ℕ) (i : Fin (n + 1)) :
    (chain s phiW hphi hx0 n).a i = aSeq s phiW hphi hx0 i.1 := by
  induction n with
  | zero =>
    match i with
    | ⟨0, _⟩ => simp [aSeq, chain, initial, Fin.last]
    | ⟨_ + 1, hk⟩ => omega
  | succ n ih =>
    refine Fin.lastCases ?_ ?_ i
    · simp [aSeq, chain_succ, extend, Fin.snoc_last]
    · intro j
      simp [chain_succ, extend, Fin.snoc_castSucc, ih j]

/-- Norming lists grow by concatenation. -/
theorem mem_F_mono {x0 : E} (hx0 : x0 ∈ s) {n m : ℕ} (hnm : n ≤ m) {f : StrongDual 𝕜 E}
    (hf : f ∈ (chain s phiW hphi hx0 n).F) : f ∈ (chain s phiW hphi hx0 m).F := by
  induction hnm with
  | refl => exact hf
  | @step m _ ih =>
    rw [chain_succ]
    exact List.mem_append_left _ ih

/-- The previous list at a positive stage is the norming list of the preceding stage. -/
theorem chain_prev_succ {x0 : E} (hx0 : x0 ∈ s) (n : ℕ) :
    (chain s phiW hphi hx0 (n + 1)).prev = (chain s phiW hphi hx0 n).F := by
  simp [chain_succ, extend]

/-- The approximation denominator at stage `n + 1` is `n + 1`. -/
theorem chain_closeDen {x0 : E} (hx0 : x0 ∈ s) (n : ℕ) :
    (chain s phiW hphi hx0 (n + 1)).closeDen = n + 1 := by
  simp [chain_succ, extend]

/-- Late vectors approximate the cluster point on every earlier norming functional. -/
theorem dist_late {x0 : E} (hx0 : x0 ∈ s) {n m : ℕ} (hnm : n < m) {f : StrongDual 𝕜 E}
    (hf : f ∈ (chain s phiW hphi hx0 n).F) :
    ‖WeakDual.toStrongDual phiW f -
        inclusionInDoubleDual 𝕜 E (aSeq s phiW hphi hx0 m) f‖ < 1 / (m : ℝ) := by
  have hm0 : 0 < m := Nat.zero_lt_of_lt hnm
  have hfprev : f ∈ (chain s phiW hphi hx0 m).prev := by
    have hle : n ≤ m - 1 := by omega
    have hf' : f ∈ (chain s phiW hphi hx0 (m - 1)).F := mem_F_mono s phiW hphi hx0 hle hf
    have hm : m = m - 1 + 1 := (Nat.succ_pred_eq_of_pos hm0).symm
    rw [hm, chain_prev_succ]
    exact hf'
  have hden : (chain s phiW hphi hx0 m).closeDen = m := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm0.ne'
    rw [hk]
    exact chain_closeDen s phiW hphi hx0 k
  have hlt := (chain s phiW hphi hx0 m).close f hfprev
  simpa [aSeq, hden] using hlt

/-- The range of the stage generators is the cluster point together with the embedded vectors. -/
theorem range_generators (phi : WeakDual 𝕜 (StrongDual 𝕜 E)) {n : ℕ} (a : Fin (n + 1) → E) :
    range (generators phi a) = insert (WeakDual.toStrongDual phi)
      (range fun i ↦ inclusionInDoubleDual 𝕜 E (a i)) := by
  ext z
  constructor
  · rintro ⟨j, rfl⟩
    cases j with
    | none => exact mem_insert _ _
    | some i => exact mem_insert_of_mem _ (mem_range_self i)
  · intro hz
    rw [mem_insert_iff] at hz
    rcases hz with rfl | ⟨i, rfl⟩
    · exact ⟨none, rfl⟩
    · exact ⟨some i, rfl⟩

/-- From relative weak sequential compactness, every weak-star cluster point of the canonical
image lies in the image. -/
theorem mem_range_inclusionInDoubleDualWeak_of_seq (hseq : ∀ u : ℕ → E, (∀ n, u n ∈ s) →
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ x : E,
      Tendsto (fun n ↦ toWeakSpace 𝕜 E ((u ∘ r) n)) atTop (𝓝 (toWeakSpace 𝕜 E x)))
    {phiW : WeakDual 𝕜 (StrongDual 𝕜 E)}
    (hphi : phiW ∈ closure (inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' s))) :
    phiW ∈ range (inclusionInDoubleDualWeak 𝕜 E) := by
  have hne : (inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' s)).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, closure_empty] at hphi
    exact hphi
  obtain ⟨psi0, hpsi0⟩ := hne
  obtain ⟨y, hy, rfl⟩ := hpsi0
  obtain ⟨x0, hx0, rfl⟩ := hy
  let ch : (n : ℕ) → VogtStep phiW s n := chain s phiW hphi hx0
  let a : ℕ → E := aSeq s phiW hphi hx0
  have ha : ∀ n, a n ∈ s := aSeq_mem s phiW hphi hx0
  obtain ⟨r, hr, x, hx⟩ := hseq a ha
  have hphi_eval (n : ℕ) (f : StrongDual 𝕜 E) (hf : f ∈ (ch n).F) :
      WeakDual.toStrongDual phiW f = f x := by
    have hscalar : Tendsto (fun k ↦ f (a (r k))) atTop (𝓝 (f x)) :=
      tendsto_eval_of_tendsto_toWeakSpace hx f
    have hzero : Tendsto (fun k ↦ WeakDual.toStrongDual phiW f - f (a (r k))) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hrN : Tendsto r atTop atTop := hr.tendsto_atTop
      have hdiv : Tendsto (fun k ↦ (1 : ℝ) / (r k : ℝ)) atTop (𝓝 0) :=
        (tendsto_natCast_atTop_atTop.comp hrN).const_div_atTop 1
      rw [Metric.tendsto_atTop] at hdiv
      obtain ⟨K1, hK1⟩ := (Filter.tendsto_atTop_atTop.mp hrN) (n + 1)
      obtain ⟨K2, hK2⟩ := hdiv ε hε
      refine ⟨max K1 K2, fun k hk ↦ ?_⟩
      have hnk : n < r k := Nat.lt_of_succ_le (hK1 k (le_trans (le_max_left _ _) hk))
      have hlt := dist_late s phiW hphi hx0 hnk hf
      have hεk : |(1 : ℝ) / (r k : ℝ)| < ε := by
        simpa [Real.dist_eq, sub_zero] using hK2 k (le_trans (le_max_right _ _) hk)
      have hpos : 0 ≤ (1 : ℝ) / (r k : ℝ) := by positivity
      rw [dist_eq_norm, sub_zero]
      calc
        ‖WeakDual.toStrongDual phiW f - f (a (r k))‖
          = ‖WeakDual.toStrongDual phiW f -
              inclusionInDoubleDual 𝕜 E (a (r k)) f‖ := by simp [NormedSpace.dual_def]
        _ < 1 / (r k : ℝ) := hlt
        _ = |(1 : ℝ) / (r k : ℝ)| := by rw [abs_of_nonneg hpos]
        _ < ε := hεk
    have hlim : Tendsto (fun k ↦ WeakDual.toStrongDual phiW f - f (a (r k))) atTop
        (𝓝 (WeakDual.toStrongDual phiW f - f x)) :=
      tendsto_const_nhds.sub hscalar
    have huniq := tendsto_nhds_unique hzero hlim
    exact sub_eq_zero.mp (Eq.symm huniq)
  let phiS : StrongDual 𝕜 (StrongDual 𝕜 E) := WeakDual.toStrongDual phiW
  let Ja : ℕ → StrongDual 𝕜 (StrongDual 𝕜 E) := fun n ↦ inclusionInDoubleDual 𝕜 E (a n)
  have hxspan : x ∈ (Submodule.span 𝕜 (range fun k ↦ a (r k))).topologicalClosure :=
    mem_topologicalClosure_span_of_tendsto_toWeakSpace hx
  have hsubseq : range (fun k ↦ a (r k)) ⊆ range a := by
    rintro _ ⟨k, rfl⟩
    exact ⟨r k, rfl⟩
  have hxspan' : x ∈ (Submodule.span 𝕜 (range a)).topologicalClosure :=
    (Submodule.topologicalClosure_mono (Submodule.span_mono hsubseq)) hxspan
  have hJx : inclusionInDoubleDual 𝕜 E x ∈
      closure (Submodule.span 𝕜 (inclusionInDoubleDual 𝕜 E '' range a) : Set _) := by
    have hxcl : x ∈ closure (Submodule.span 𝕜 (range a) : Set E) := by
      simpa [← SetLike.mem_coe, Submodule.topologicalClosure_coe] using hxspan'
    have himg := image_closure_subset_closure_image
      (map_continuous (inclusionInDoubleDual 𝕜 E)) (s := (Submodule.span 𝕜 (range a) : Set E))
    have hxJ := himg ⟨x, hxcl, rfl⟩
    exact closure_mono (Submodule.image_span_subset_span
      (inclusionInDoubleDual 𝕜 E).toLinearMap (range a)) hxJ
  have hspan_cl : inclusionInDoubleDual 𝕜 E x ∈
      closure (Submodule.span 𝕜 (range Ja) : Set _) := by
    have hrange : inclusionInDoubleDual 𝕜 E '' range a = range Ja := by
      ext y
      constructor
      · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨a n, ⟨n, rfl⟩, rfl⟩
    rw [← hrange]
    exact hJx
  let delta : StrongDual 𝕜 (StrongDual 𝕜 E) := phiS - inclusionInDoubleDual 𝕜 E x
  have hzero : delta = 0 := by
    apply (ContinuousLinearMap.opNorm_zero_iff (f := delta)).mp
    refine le_antisymm ?_ (ContinuousLinearMap.opNorm_nonneg _)
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    rw [zero_add]
    let nbhd : Set (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
      {g | ∀ v ∈ closedBall (0 : StrongDual 𝕜 E) 1,
        (inclusionInDoubleDual 𝕜 E x - g) v ∈ ball (0 : 𝕜) (ε / 3)}
    have hnbhd : nbhd ∈ 𝓝 (inclusionInDoubleDual 𝕜 E x) := by
      -- `toPseudoMetricSpace` keeps the seminorm distance `‖-g + Jx‖`.
      refine mem_of_superset
        (ball_mem_nhds (inclusionInDoubleDual 𝕜 E x) (by positivity : 0 < ε / 3)) ?_
      intro g hg v hv
      rw [mem_ball_iff_norm, sub_zero]
      rw [mem_ball] at hg
      have hdist : dist g (inclusionInDoubleDual 𝕜 E x) =
          ‖-g + inclusionInDoubleDual 𝕜 E x‖ := rfl
      rw [hdist] at hg
      have hsum : -g + inclusionInDoubleDual 𝕜 E x =
          inclusionInDoubleDual 𝕜 E x - g := by
        ext w
        simp [add_apply, neg_apply, sub_apply, sub_eq_add_neg, add_comm]
      rw [hsum] at hg
      have hle := ContinuousLinearMap.le_opNorm
        (inclusionInDoubleDual 𝕜 E x - g) v
      have hv1 : ‖v‖ ≤ 1 := by
        rw [mem_closedBall_iff_norm, sub_zero] at hv
        exact hv
      have hmul : ‖inclusionInDoubleDual 𝕜 E x - g‖ * ‖v‖ ≤
          ‖inclusionInDoubleDual 𝕜 E x - g‖ := by
        calc
          ‖inclusionInDoubleDual 𝕜 E x - g‖ * ‖v‖
              ≤ ‖inclusionInDoubleDual 𝕜 E x - g‖ * 1 :=
            mul_le_mul_of_nonneg_left hv1 (ContinuousLinearMap.opNorm_nonneg _)
          _ = ‖inclusionInDoubleDual 𝕜 E x - g‖ := mul_one _
      exact (hle.trans hmul).trans_lt hg
    obtain ⟨z0, hz0mem⟩ := (mem_closure_iff_nhds.mp hspan_cl) nbhd hnbhd
    obtain ⟨hz0nbhd, hz0⟩ := hz0mem
    have hop := by
      refine ContinuousLinearMap.opNorm_le_of_unit_norm
        (f := inclusionInDoubleDual 𝕜 E x - z0) (C := ε / 3) (by positivity) ?_
      intro v hv
      have hvb : v ∈ closedBall (0 : StrongDual 𝕜 E) 1 := by
        rw [mem_closedBall_iff_norm, sub_zero]
        exact le_of_eq hv
      have hlt := hz0nbhd v hvb
      rw [mem_ball_iff_norm, sub_zero] at hlt
      exact le_of_lt hlt
    let psi : StrongDual 𝕜 (StrongDual 𝕜 E) := phiS - z0
    have hdiff : psi - delta = inclusionInDoubleDual 𝕜 E x - z0 := by
      ext v
      simp only [psi, delta, sub_apply]
      ring
    obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hz0
    let N : ℕ := c.support.sup id
    have hzN : z0 ∈ Submodule.span 𝕜 (Ja '' {n | n ≤ N}) := by
      rw [← hc, Finsupp.sum]
      refine Submodule.sum_mem _ fun i hi ↦ ?_
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact ⟨i, Finset.le_sup (f := id) hi, rfl⟩
    have hzNeg : -z0 ∈ Submodule.span 𝕜 (Ja '' {n | n ≤ N}) := by
      rw [← neg_one_smul 𝕜 z0]
      exact Submodule.smul_mem _ (-1) hzN
    have hpsiN : psi ∈ stepSpan phiW (ch N).a := by
      have hpsi : psi = (1 : 𝕜) • phiS + -z0 := by
        ext v
        simp only [psi, sub_apply, add_apply, neg_apply, one_smul, sub_eq_add_neg]
      have himage : Ja '' {n | n ≤ N} ⊆
          range fun i : Fin (N + 1) ↦ inclusionInDoubleDual 𝕜 E ((ch N).a i) := by
        intro y hy
        obtain ⟨k, hk, rfl⟩ := hy
        have hkN : k ≤ N := by simpa [mem_ofPred] using hk
        have hlt : k < N + 1 := Nat.lt_succ_of_le hkN
        refine ⟨⟨k, hlt⟩, ?_⟩
        have heq : (ch N).a ⟨k, hlt⟩ = a k := by
          simpa [a] using chain_a s phiW hphi hx0 N ⟨k, hlt⟩
        simp [Ja, heq]
      have hzstage : -z0 ∈ Submodule.span 𝕜
          (range fun i ↦ inclusionInDoubleDual 𝕜 E ((ch N).a i)) :=
        Submodule.span_mono himage hzNeg
      rw [stepSpan, range_generators, hpsi]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _
        (Submodule.subset_span (mem_insert _ _)))
        (Submodule.span_mono (subset_insert _ _) hzstage)
    by_cases hψ : ‖psi‖ = 0
    · have hψ0 : psi = 0 := (ContinuousLinearMap.opNorm_zero_iff (f := psi)).mp hψ
      have hsub0 : 0 - delta = inclusionInDoubleDual 𝕜 E x - z0 := by
        simpa [hψ0] using hdiff
      have hneg0 : (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) - delta = -delta := by
        ext v
        simp [sub_apply, neg_apply, zero_apply, zero_sub]
      calc
        ‖delta‖ = ‖-delta‖ := (ContinuousLinearMap.opNorm_neg delta).symm
        _ = ‖0 - delta‖ := by rw [hneg0]
        _ = ‖inclusionInDoubleDual 𝕜 E x - z0‖ := by rw [hsub0]
        _ ≤ ε / 3 := hop
        _ ≤ ε := by linarith
    · obtain ⟨f, hf, hle⟩ := (ch N).norming psi hpsiN hψ
      have hf0 : delta f = 0 := by
        simp only [delta, sub_apply, phiS, NormedSpace.dual_def,
          hphi_eval N f hf, sub_self]
      have happ : ‖psi f‖ = ‖(psi - delta) f‖ := by
        rw [sub_apply (f := psi) (g := delta), hf0, sub_zero]
      have hle2 : ‖psi‖ ≤ 2 * ‖psi - delta‖ := by
        have hleOp : ‖(psi - delta) f‖ ≤ ‖psi - delta‖ * ‖f‖ :=
          ContinuousLinearMap.le_opNorm (psi - delta) f
        have hF : ‖f‖ ≤ 1 := (ch N).norm_F f hf
        have hmul : ‖psi - delta‖ * ‖f‖ ≤ ‖psi - delta‖ := by
          calc
            ‖psi - delta‖ * ‖f‖ ≤ ‖psi - delta‖ * 1 :=
              mul_le_mul_of_nonneg_left hF
                (ContinuousLinearMap.opNorm_nonneg _)
            _ = ‖psi - delta‖ := mul_one _
        calc
          ‖psi‖ ≤ 2 * ‖psi f‖ := hle
          _ = 2 * ‖(psi - delta) f‖ := by rw [happ]
          _ ≤ 2 * (‖psi - delta‖ * ‖f‖) :=
            mul_le_mul_of_nonneg_left hleOp (by norm_num)
          _ ≤ 2 * ‖psi - delta‖ :=
            mul_le_mul_of_nonneg_left hmul (by norm_num)
      have hadd := ContinuousLinearMap.opNorm_add_le (delta - psi) psi
      rw [sub_add_cancel] at hadd
      have hneg : -(psi - delta) = delta - psi := by
        ext v
        simp [sub_apply, neg_apply, neg_sub]
      have hrev : ‖psi - delta‖ = ‖delta - psi‖ :=
        (ContinuousLinearMap.opNorm_neg (psi - delta)).symm.trans (congrArg norm hneg)
      calc
        ‖delta‖ ≤ ‖delta - psi‖ + ‖psi‖ := hadd
        _ ≤ ‖delta - psi‖ + 2 * ‖psi - delta‖ := add_le_add_right hle2 _
        _ = ‖delta - psi‖ + 2 * ‖delta - psi‖ := by rw [hrev]
        _ = 3 * ‖delta - psi‖ := by ring
        _ = 3 * ‖inclusionInDoubleDual 𝕜 E x - z0‖ := by rw [← hrev, hdiff]
        _ ≤ 3 * (ε / 3) :=
          mul_le_mul_of_nonneg_left hop (by norm_num)
        _ = ε := by ring
  have hphiS : phiS = inclusionInDoubleDual 𝕜 E x := sub_eq_zero.mp hzero
  refine ⟨toWeakSpace 𝕜 E x, ?_⟩
  apply DFunLike.ext
  intro f
  rw [inclusionInDoubleDualWeak_toWeakSpace_apply]
  apply Eq.symm
  rw [← WeakDual.toStrongDual_apply (x := phiW) (y := f)]
  rw [show WeakDual.toStrongDual phiW = phiS from rfl]
  rw [hphiS, NormedSpace.dual_def]

/-- Sequential relative weak compactness yields norm boundedness. -/
theorem isBounded_of_seq (hseq : ∀ u : ℕ → E, (∀ n, u n ∈ s) →
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ x : E,
      Tendsto (fun n ↦ toWeakSpace 𝕜 E ((u ∘ r) n)) atTop (𝓝 (toWeakSpace 𝕜 E x))) :
    IsBounded s := by
  rw [isBounded_iff_forall_norm_le]
  by_contra h
  push Not at h
  choose u hu hnorm using fun n : ℕ ↦ h (n : ℝ)
  obtain ⟨r, hr, x, hx⟩ := hseq u hu
  obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le).1
    (isBounded_range_of_tendsto_toWeakSpace hx)
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hle := hC (u (r n)) (mem_range_self n)
  have hgt : (n : ℝ) < ‖u (r n)‖ := by
    have hrn : (n : ℝ) ≤ (r n : ℝ) := Nat.mono_cast (hr.id_le n)
    exact lt_of_le_of_lt hrn (hnorm (r n))
  have hnC : C < (n : ℝ) := by simpa using hn
  linarith

/-- A relatively weakly compact set is relatively weakly sequentially compact. -/
theorem exists_subseq_of_isCompact_closure
    (hs : IsCompact (closure (toWeakSpace 𝕜 E '' s))) (u : ℕ → E) (hu : ∀ n, u n ∈ s) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ x : E,
      Tendsto (fun n ↦ toWeakSpace 𝕜 E ((u ∘ r) n)) atTop (𝓝 (toWeakSpace 𝕜 E x)) := by
  let K : Set (WeakSpace 𝕜 E) := closure (toWeakSpace 𝕜 E '' range u)
  have hKsub : K ⊆ closure (toWeakSpace 𝕜 E '' s) :=
    closure_mono (image_mono fun y hy ↦ by
      obtain ⟨n, rfl⟩ := hy
      exact hu n)
  have hKc : IsCompact K := hs.of_isClosed_subset isClosed_closure hKsub
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  letI : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  letI : Module ℝ E := .restrictScalars ℝ 𝕜 E
  haveI : IsScalarTower ℝ 𝕜 E := .restrictScalars ℝ 𝕜 E
  haveI : LocallyConvexSpace ℝ E := NormedSpace.toLocallyConvexSpace' 𝕜
  haveI : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  let p : Submodule ℝ E := (Submodule.span ℝ (range u)).topologicalClosure
  have hpclosed : IsClosed (p : Set E) := (Submodule.span ℝ (range u)).isClosed_topologicalClosure
  have hsep : TopologicalSpace.IsSeparable (p : Set E) := by
    simpa [p, Submodule.topologicalClosure_coe] using
      ((Set.countable_range u).isSeparable.span (R := ℝ)).closure
  haveI : SeparableSpace (↥p) := hsep.separableSpace
  haveI : Nonempty (↥p) :=
    ⟨⟨u 0, (Submodule.span ℝ (range u)).le_topologicalClosure
      (Submodule.subset_span (mem_range_self 0))⟩⟩
  let v : ℕ → ↥p := denseSeq (↥p)
  let g : ℕ → StrongDual 𝕜 E := fun n ↦ Classical.choose (exists_dual_vector'' 𝕜 (v n : E))
  have hg (n : ℕ) : ‖g n‖ ≤ 1 ∧ g n (v n : E) = ‖(v n : E)‖ :=
    Classical.choose_spec (exists_dual_vector'' 𝕜 (v n : E))
  have hsep_p : ∀ {x y : E}, x ∈ p → y ∈ p → x ≠ y → ∃ n, g n x ≠ g n y := by
    intro x y hx hy hxy
    let z : ↥p := ⟨x - y, p.sub_mem hx hy⟩
    have hz0 : (z : E) ≠ 0 := sub_ne_zero.mpr hxy
    have hnorm : 0 < ‖(z : E)‖ := norm_pos_iff.mpr hz0
    obtain ⟨n, hn⟩ := (mem_closure_range_iff).1 (denseRange_denseSeq (↥p) z)
      (‖(z : E)‖ / 2) (half_pos hnorm)
    have hdist : ‖(v n : E) - (z : E)‖ < ‖(z : E)‖ / 2 := by
      rw [dist_eq_norm] at hn
      rw [← Submodule.norm_coe, Submodule.coe_sub, norm_sub_rev] at hn
      simpa [v] using hn
    let w : E := v n
    have hgv : ‖(z : E)‖ - 2 * ‖w - (z : E)‖ ≤ ‖g n (z : E)‖ := by
      have hle : ‖g n (w - (z : E))‖ ≤ ‖w - (z : E)‖ := by
        calc
          ‖g n (w - (z : E))‖ ≤ ‖g n‖ * ‖w - (z : E)‖ := (g n).le_opNorm _
          _ ≤ ‖w - (z : E)‖ := by
            simpa using mul_le_mul_of_nonneg_right (hg n).1 (norm_nonneg _)
      have hgnorm : ‖g n w‖ = ‖w‖ := by
        rw [(hg n).2, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
      have hrev : ‖w‖ - ‖w - (z : E)‖ ≤ ‖g n (z : E)‖ := by
        have hsum : ‖g n w‖ ≤ ‖g n (z : E)‖ + ‖g n (w - (z : E))‖ := by
          simpa [map_sub, sub_add_cancel] using
            norm_add_le (g n (z : E)) (g n (w - (z : E)))
        linarith
      have htri : ‖(z : E)‖ ≤ ‖w‖ + ‖w - (z : E)‖ := by
        have h := norm_add_le w ((z : E) - w)
        rw [add_sub_cancel] at h
        have hsub : ‖(z : E) - w‖ = ‖w - (z : E)‖ := norm_sub_rev _ _
        rwa [hsub] at h
      linarith
    have hpos : 0 < ‖g n (z : E)‖ := by
      have hstrict : 0 < ‖(z : E)‖ - 2 * ‖w - (z : E)‖ := by linarith
      exact lt_of_lt_of_le hstrict hgv
    exact ⟨n, sub_ne_zero.mp <| by simpa [z, map_sub] using (norm_pos_iff.mp hpos)⟩
  have hrange_p : range u ⊆ (p : Set E) := fun y hy ↦
    (Submodule.span ℝ (range u)).le_topologicalClosure (Submodule.subset_span hy)
  have himage : (toWeakSpace 𝕜 E) '' (p : Set E) =
      closure ((toWeakSpace 𝕜 E) '' (p : Set E)) := by
    rw [← p.convex.toWeakSpace_closure 𝕜, hpclosed.closure_eq]
  have hclosedW : IsClosed ((toWeakSpace 𝕜 E) '' (p : Set E)) := by
    rw [himage]
    exact isClosed_closure
  have hKp : K ⊆ (toWeakSpace 𝕜 E) '' (p : Set E) :=
    closure_minimal (image_mono hrange_p) hclosedW
  have hsepK : Pairwise fun (x y : K) ↦ ∃ n, g n x.1 ≠ g n y.1 := by
    intro x y hxy
    obtain ⟨zx, hzx, hzx'⟩ := hKp x.2
    obtain ⟨zy, hzy, hzy'⟩ := hKp y.2
    have hne : zx ≠ zy := by
      intro h
      apply hxy
      apply Subtype.ext
      rw [← hzx', ← hzy', h]
    obtain ⟨n, hn⟩ := hsep_p hzx hzy hne
    refine ⟨n, ?_⟩
    rw [← hzx', ← hzy']
    exact hn
  haveI : MetrizableSpace K :=
    Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating
      (fun n (w : K) ↦ g n w.1)
      (fun n ↦ (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip (g n)).comp
        continuous_subtype_val)
      hsepK
  haveI : SeqCompactSpace K := (compactSpace_iff_seqCompactSpace (X := K)).1 inferInstance
  let seq : ℕ → K := fun n ↦ ⟨toWeakSpace 𝕜 E (u n),
    subset_closure (mem_image_of_mem _ (mem_range_self n))⟩
  obtain ⟨a, r, hr, htend⟩ := SeqCompactSpace.tendsto_subseq seq
  refine ⟨r, hr, a.1, ?_⟩
  have htend_val : Tendsto (fun n ↦ (seq (r n)).1) atTop (𝓝 a.1) :=
    (continuous_subtype_val.tendsto a).comp htend
  have hseq : (fun n ↦ (seq (r n)).1) = fun n ↦ toWeakSpace 𝕜 E (u (r n)) := by
    funext n
    simp [seq, toWeakSpace]
  have hpt : toWeakSpace 𝕜 E a.1 = a.1 := by
    rw [toWeakSpace]
    exact LinearEquiv.refl_apply a.1
  rw [hseq, ← hpt] at htend_val
  exact htend_val

/-- **Eberlein–Šmulian**. The sequential limit lies in the ambient space. -/
theorem eberlein_smulian [CompleteSpace E] (s : Set E) :
    IsCompact (closure (toWeakSpace 𝕜 E '' s)) ↔
      ∀ u : ℕ → E, (∀ n, u n ∈ s) →
        ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ x : E,
          Tendsto (fun n ↦ toWeakSpace 𝕜 E ((u ∘ r) n)) atTop
            (𝓝 (toWeakSpace 𝕜 E x)) := by
  constructor
  · intro hs u hu
    exact exists_subseq_of_isCompact_closure s hs u hu
  · intro hseq
    refine NormedSpace.isCompact_closure_of_isBounded 𝕜 E (toWeakSpace 𝕜 E '' s) ?_ ?_
    · simpa [preimage_image_eq _ (toWeakSpace 𝕜 E).injective] using isBounded_of_seq s hseq
    · intro phi hphi
      simpa using mem_range_inclusionInDoubleDualWeak_of_seq s hseq hphi

end CKMA.EberleinSmulian
