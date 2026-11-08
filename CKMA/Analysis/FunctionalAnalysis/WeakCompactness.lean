/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Analysis.Convex.Uniform
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.Analysis.RCLike.Basic

/-!
# Weak compactness and scalar Lp geometry

Weak convergence and weak Cauchy sequences are tested by continuous scalar-valued linear
functionals. Relative weak compactness retains limits in the ambient space, so an original set
need not contain its subsequential limits. Eberlein–Šmulian relates these notions; James's
criterion concerns attainment of real continuous linear functionals on closed convex sets.

Scalar Lp uniform convexity includes every exponent strictly between one and infinity, including
two. On finite measure spaces, Dunford–Pettis uses Mathlib's uniform-integrability predicate,
which includes a uniform L1 bound. Sources: GAPS 15.28, 15.29, 15.33, and 17.23.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology MeasureTheory
open scoped ENNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Convergence against every continuous linear functional along an arbitrary filter. -/
def WeaklyTendsto (𝕜 : Type*) [RCLike 𝕜] {α E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (u : α → E) (l : Filter α) (x : E) : Prop :=
  ∀ ℓ : E →L[𝕜] 𝕜, Tendsto (fun a ↦ ℓ (u a)) l (𝓝 (ℓ x))

/-- Scalar weak convergence is convergence in Mathlib's weak-space topology. -/
theorem weaklyTendsto_iff_tendsto {α : Type*} (u : α → E) (l : Filter α) (x : E) :
    WeaklyTendsto 𝕜 u l x ↔
      Tendsto (fun a ↦ toWeakSpace 𝕜 E (u a)) l (𝓝 (toWeakSpace 𝕜 E x)) := by
  have hi : Function.Injective (topDualPairing 𝕜 E).flip := by
    intro x y h
    exact SeparatingDual.eq_iff_forall_dual_eq.2 fun ℓ ↦ congrArg (fun f ↦ f ℓ) h
  exact (WeakBilin.tendsto_iff_forall_eval_tendsto (topDualPairing 𝕜 E).flip hi).symm

/-- Weak convergence of a sequence, expressed on the original carrier. -/
def WeaklyConverges (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (u : ℕ → E) (x : E) : Prop :=
  WeaklyTendsto 𝕜 u atTop x

/-- Sequence weak convergence is convergence of the sequence viewed in `WeakSpace`. -/
theorem weaklyConverges_iff_tendsto (u : ℕ → E) (x : E) :
    WeaklyConverges 𝕜 u x ↔
      Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x)) :=
  weaklyTendsto_iff_tendsto u atTop x

/-- Relative compactness for the weak topology, retaining ambient-space limit points. -/
def IsRelativelyWeaklyCompact (𝕜 : Type*) [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (s : Set E) : Prop :=
  IsCompact (closure (toWeakSpace 𝕜 E '' s))

/-- A sequence is weakly Cauchy when all of its continuous scalar images are Cauchy. -/
def IsWeaklyCauchy (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (u : ℕ → E) : Prop :=
  ∀ ℓ : E →L[𝕜] 𝕜, CauchySeq (fun n ↦ ℓ (u n))

/-- Weak convergence implies the weak Cauchy property. -/
theorem WeaklyConverges.isWeaklyCauchy {u : ℕ → E} {x : E}
    (hu : WeaklyConverges 𝕜 u x) : IsWeaklyCauchy 𝕜 u := by
  intro ℓ
  exact (hu ℓ).cauchySeq

/-- **15.28**, Eberlein–Šmulian: weak relative compactness is weak sequential relative compactness.
The subsequence limit is in the ambient Banach space, not necessarily in `s`. -/
theorem eberlein_smulian [CompleteSpace E] (s : Set E) :
    IsRelativelyWeaklyCompact 𝕜 s ↔
      ∀ u : ℕ → E, (∀ n, u n ∈ s) →
        ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ x : E, WeaklyConverges 𝕜 (u ∘ r) x := by
  sorry

/-- **15.29**, the sufficiency direction of James's compactness theorem over the real scalars. -/
theorem isCompact_toWeakSpace_image_of_forall_exists_max {X : Type*} [NormedAddCommGroup X]
  [NormedSpace ℝ X]
    [CompleteSpace X] {s : Set X} (hb : Bornology.IsBounded s)
    (hc : IsClosed s) (hv : Convex ℝ s)
    (hattain : ∀ ℓ : X →L[ℝ] ℝ, ∃ x ∈ s, ∀ y ∈ s, ℓ y ≤ ℓ x) :
    IsCompact (toWeakSpace ℝ X '' s) := by
  sorry

/-- **15.33**: scalar Lp is uniformly convex for every exponent strictly between one and infinity.
The Hilbert exponent is included in the interface rather than unnecessarily excluded. -/
theorem uniformConvexSpace_lp {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p < ∞) :
    UniformConvexSpace (Lp 𝕜 p μ) := by
  sorry

/-- **17.23**, Dunford–Pettis: relative weak compactness of an L1 family on a finite measure
space is precisely uniform integrability, including the uniform L1 bound in Mathlib's predicate. -/
theorem dunford_pettis {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (s : Set (Lp 𝕜 1 μ)) :
    IsRelativelyWeaklyCompact 𝕜 s ↔
      UniformIntegrable (fun f : s ↦ (f.1 : X → 𝕜)) 1 μ := by
  sorry

end CKMA
