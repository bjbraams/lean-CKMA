/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Analysis.RCLike.Basic

/-!
# Basic weak-topology predicates in normed spaces

Weak convergence along a filter, sequential weak convergence, weak Cauchy sequences, and relative
weak compactness in normed spaces over `RCLike` scalars.

## Main definitions

* `CKMA.WeaklyTendsto`: convergence against every continuous scalar linear functional along a
  filter.
* `CKMA.WeaklyConverges`: sequential weak convergence along `atTop`.
* `CKMA.IsRelativelyWeaklyCompact`: relative compactness in `WeakSpace 𝕜 E`.
* `CKMA.IsWeaklyCauchy`: scalar Cauchy property under every continuous linear functional.

## Main results

* `CKMA.weaklyTendsto_iff_tendsto`: equivalence of `WeaklyTendsto` and convergence in
  `WeakSpace 𝕜 E`.
* `CKMA.weaklyConverges_iff_tendsto`: sequential specialization of `weaklyTendsto_iff_tendsto`.
* `CKMA.WeaklyConverges.isWeaklyCauchy`: weakly convergent sequences are weakly Cauchy.

## Notation

Uses `𝓝` and `atTop` from `Topology` and `Filter`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology

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

end CKMA
