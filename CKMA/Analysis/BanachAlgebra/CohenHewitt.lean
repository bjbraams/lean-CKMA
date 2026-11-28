/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

import TauCeti.Analysis.Normed.Module.CohenFactorization.Basic

/-!
# Cohen–Hewitt factorization

Let a possibly nonunital real or complex Banach algebra `A` act on a Banach space `X` through a
continuous bilinear map `act` with `act (a * b) x = act a (act b x)`. If `A` has a bounded left
approximate identity `e`, indexed by a nonempty directed preorder, along which `act (e i) x → x`
for every `x`, then every `x` factors as `act a y`, with `‖a‖` at most the bound of `e` and `y`
as close to `x` as prescribed.

Both theorems are derived from TauCeti's Cohen–Hewitt theorem
`ContinuousLinearMap.exists_apply_eq_of_mem_topologicalClosure_span`, applied to the filter
`map e atTop`: under strong convergence every `x` lies in the closed span of `act A X`.
Source: GAPS 20.47.

## Main definitions

* `CKMA.IsBoundedLeftApproximateIdentity`: bounded left approximate identity indexed by a
  directed preorder.

## Main results

* `CKMA.isBoundedLeftApproximateIdentity_iff`: defining lemma.
* `CKMA.cohen_hewitt_factorization_norm_le`: factorization `x = act a y` with `‖a‖ ≤ M` and
  `‖y - x‖ < ε`.
* `CKMA.cohen_hewitt_factorization`: the Cohen–Hewitt factorization theorem.
-/

public section

namespace CKMA

open Filter Topology

/-- A bounded left approximate identity indexed by a preorder `ι`: the net `e` is bounded in
norm and `e i * a → a` along `atTop` for every `a`. The factorization theorem takes `ι` nonempty
and directed. -/
@[expose]
def IsBoundedLeftApproximateIdentity {ι A : Type*} [Preorder ι] [NonUnitalNormedRing A]
    (e : ι → A) : Prop :=
  (∃ M : ℝ, ∀ i, ‖e i‖ ≤ M) ∧ ∀ a : A, Tendsto (fun i ↦ e i * a) atTop (𝓝 a)

/-- Defining property of `IsBoundedLeftApproximateIdentity`. -/
theorem isBoundedLeftApproximateIdentity_iff {ι A : Type*} [Preorder ι] [NonUnitalNormedRing A]
    {e : ι → A} : IsBoundedLeftApproximateIdentity e ↔
      (∃ M : ℝ, ∀ i, ‖e i‖ ≤ M) ∧ ∀ a : A, Tendsto (fun i ↦ e i * a) atTop (𝓝 a) :=
  Iff.rfl

variable {𝕜 ι A X : Type*} [RCLike 𝕜] [Preorder ι] [Nonempty ι]
    [IsDirected ι (· ≤ ·)] [NonUnitalNormedRing A]
    [NormedSpace 𝕜 A] [CompleteSpace A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- **20.47** with norm control: if the net `e` is bounded by `M`, every `x` factors as
`act a y` with `‖a‖ ≤ M` and `y` within any prescribed distance `ε > 0` of `x`. -/
theorem cohen_hewitt_factorization_norm_le (act : A →L[𝕜] X →L[𝕜] X)
    (hassoc : ∀ a b x, act (a * b) x = act a (act b x)) {e : ι → A} {M : ℝ}
    (hM : ∀ i, ‖e i‖ ≤ M) (hl : ∀ a : A, Tendsto (fun i ↦ e i * a) atTop (𝓝 a))
    (hstrong : ∀ x, Tendsto (fun i ↦ act (e i) x) atTop (𝓝 x)) (x : X) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, ∃ y : X, ‖a‖ ≤ M ∧ ‖y - x‖ < ε ∧ x = act a y := by
  have : (map e atTop).NeBot := Filter.map_neBot
  have hC : ∀ᶠ b in map e atTop, ‖b‖ ≤ M := Filter.eventually_map.2 (.of_forall hM)
  have hl' : ∀ a, Tendsto (· * a) (map e atTop) (𝓝 a) := fun a => tendsto_map'_iff.2 (hl a)
  have hx : x ∈ (Submodule.span 𝕜
      (Set.range fun p : A × X ↦ act p.1 p.2)).topologicalClosure := by
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    exact mem_closure_of_tendsto (hstrong x) <|
      .of_forall fun i => Submodule.subset_span ⟨(e i, x), rfl⟩
  obtain ⟨a, y, ha, -, hy, h⟩ :=
    ContinuousLinearMap.exists_apply_eq_of_mem_topologicalClosure_span act hassoc hC hl' hx hε
  exact ⟨a, y, ha, hy, h.symm⟩

/-- **20.47**, Cohen–Hewitt factorization for a bounded directed approximate identity
acting strongly as the identity on a real or complex Banach module. The action is a continuous
bilinear map, which supports genuinely nonunital algebras without requiring a unital Module
instance. -/
theorem cohen_hewitt_factorization (act : A →L[𝕜] X →L[𝕜] X)
    (hassoc : ∀ a b x, act (a * b) x = act a (act b x))
    (e : ι → A) (he : IsBoundedLeftApproximateIdentity e)
    (hstrong : ∀ x, Tendsto (fun i ↦ act (e i) x) atTop (𝓝 x)) :
    ∀ x : X, ∃ a : A, ∃ y : X, x = act a y := by
  intro x
  obtain ⟨⟨M, hM⟩, hl⟩ := he
  obtain ⟨a, y, -, -, h⟩ := cohen_hewitt_factorization_norm_le act hassoc hM hl hstrong x one_pos
  exact ⟨a, y, h⟩

end CKMA
