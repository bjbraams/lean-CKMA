/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.Dual
public import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
public import Mathlib.Tactic

/-!
# Monotone graphs, resolvents, and variational inequalities

Hilbert-space graph monotonicity gives resolvent uniqueness at nonnegative scales; Minty's
range criterion and existence use strictly positive scales. The normal cone includes its
base-point constraint.

For maps into a real Banach dual, monotonicity, hemicontinuity, boundedness on bounded sets,
and coercivity are expressed directly in the dual pairing. Reflexivity uses surjectivity of
the canonical bidual inclusion. Variational inequalities have separate bounded-domain and
coercive unbounded-domain existence statements. Sources: GAPS 35.32, 35.40, and 35.45.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped InnerProductSpace

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Monotonicity of a Hilbert-space graph. -/
def IsMonotoneGraph (A : Set (H × H)) : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, 0 ≤ ⟪p.1 - q.1, p.2 - q.2⟫_ℝ

/-- A monotone graph is maximal when it has no proper monotone enlargement. -/
def IsMaximalMonotoneGraph (A : Set (H × H)) : Prop :=
  IsMonotoneGraph A ∧ ∀ B, IsMonotoneGraph B → A ⊆ B → B ⊆ A

/-- A resolvent fiber: `y` belongs when `x ∈ y + a A(y)`.
This relation has a concrete body even before the existence theorem is proved. -/
def monotoneResolventFiber (A : Set (H × H)) (a : ℝ) (x : H) : Set H :=
  {y | ∃ u, (y, u) ∈ A ∧ x = y + a • u}

/-- Monotonicity alone makes a nonnegative-scale resolvent fiber single-valued.
This uniqueness statement does not depend on Minty's existence theorem. -/
theorem IsMonotoneGraph.resolventFiber_subsingleton {A : Set (H × H)}
    (hA : IsMonotoneGraph A) {a : ℝ} (ha : 0 ≤ a) (x : H) :
    (monotoneResolventFiber A a x).Subsingleton := by
  intro y hy z hz
  obtain ⟨u, hu, hxu⟩ := hy
  obtain ⟨v, hv, hxv⟩ := hz
  have hlinear : a • (u - v) = z - y := by
    calc
      a • (u - v) = (y + a • u) - (z + a • v) - (y - z) := by module
      _ = z - y := by rw [← hxu, ← hxv]; abel
  have hmon := hA (y, u) hu (z, v) hv
  have hscaled : 0 ≤ ⟪y - z, a • (u - v)⟫_ℝ := by
    simpa only [inner_smul_right, smul_eq_mul] using mul_nonneg ha hmon
  rw [hlinear] at hscaled
  have hneg : ⟪y - z, z - y⟫_ℝ = -(‖y - z‖ ^ 2) := by
    rw [show z - y = -(y - z) by abel, inner_neg_right, real_inner_self_eq_norm_sq]
  rw [hneg] at hscaled
  have hnorm : ‖y - z‖ = 0 := by nlinarith [sq_nonneg ‖y - z‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- **35.32**: Minty's characterization at each positive scale. -/
theorem isMaximalMonotoneGraph_iff_range [CompleteSpace H]
    {A : Set (H × H)} (hA : IsMonotoneGraph A) {a : ℝ} (ha : 0 < a) :
    IsMaximalMonotoneGraph A ↔ ∀ x, (monotoneResolventFiber A a x).Nonempty := by
  sorry

/-- Once a maximal monotone graph is given, every positive-scale resolvent fiber is a singleton. -/
theorem IsMaximalMonotoneGraph.existsUnique_resolvent [CompleteSpace H]
    {A : Set (H × H)} (hA : IsMaximalMonotoneGraph A) {a : ℝ} (ha : 0 < a) (x : H) :
    ∃! y, y ∈ monotoneResolventFiber A a x := by
  obtain ⟨y, hy⟩ := (isMaximalMonotoneGraph_iff_range hA.1 ha).mp hA x
  exact ⟨y, hy, fun z hz ↦ hA.1.resolventFiber_subsingleton ha.le x hz hy⟩

/-- The normal-cone graph of a convex set. Membership includes the base-point constraint. -/
def normalConeGraph (C : Set H) : Set (H × H) :=
  {p | p.1 ∈ C ∧ ∀ y ∈ C, ⟪p.2, y - p.1⟫_ℝ ≤ 0}

end Hilbert

section Banach

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Monotonicity for a map taking values in the continuous dual. -/
def IsMonotoneDualMap (A : E → StrongDual ℝ E) : Prop :=
  ∀ x y, 0 ≤ (A x - A y) (x - y)

/-- Strict monotonicity in the dual pairing. -/
def IsStrictlyMonotoneDualMap (A : E → StrongDual ℝ E) : Prop :=
  ∀ x y, x ≠ y → 0 < (A x - A y) (x - y)

/-- Hemicontinuity means continuity of every dual evaluation along each line segment. -/
def IsHemicontinuousDualMap (A : E → StrongDual ℝ E) : Prop :=
  ∀ x y z, ContinuousOn (fun t : ℝ ↦ A (x + t • y) z) (Set.Icc 0 1)

/-- Boundedness on bounded sets, without assuming global boundedness. -/
def MapsBoundedSetsToBoundedSets (A : E → StrongDual ℝ E) : Prop :=
  ∀ C : Set E, Bornology.IsBounded C → Bornology.IsBounded (A '' C)

/-- Coercivity in the dual pairing as the norm tends to infinity.
The ratio is totalized at zero, which does not affect this filter. -/
def IsCoerciveDualMap (A : E → StrongDual ℝ E) : Prop :=
  Tendsto (fun x ↦ A x x / ‖x‖) (Filter.comap (fun x : E ↦ ‖x‖) atTop) atTop

/-- **35.40**: Browder–Minty surjectivity for an everywhere-defined reflexive-Banach operator.
Reflexivity is expressed by the established bidual inclusion, as in TauCeti's weak compactness API.
  -/
theorem IsMonotoneDualMap.surjective [CompleteSpace E]
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    {A : E → StrongDual ℝ E} (hm : IsMonotoneDualMap A)
    (hh : IsHemicontinuousDualMap A) (hb : MapsBoundedSetsToBoundedSets A)
    (hc : IsCoerciveDualMap A) : Function.Surjective A := by
  sorry

/-- Strict monotonicity makes an inverse single-valued independently of existence. -/
theorem IsStrictlyMonotoneDualMap.injective {A : E → StrongDual ℝ E}
    (hA : IsStrictlyMonotoneDualMap A) : Function.Injective A := by
  intro x y hxy
  by_contra hne
  have h := hA x y hne
  simp [hxy] at h

/-- A variational inequality on `C` at forcing `f`. -/
def SolvesVariationalInequality (A : E → StrongDual ℝ E) (C : Set E)
    (f : StrongDual ℝ E) (u : E) : Prop :=
  u ∈ C ∧ ∀ v ∈ C, 0 ≤ (A u - f) (v - u)

/-- **35.45**: bounded-domain variational-inequality existence in a reflexive Banach space. -/
theorem exists_solution_variationalInequality [CompleteSpace E]
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    {A : E → StrongDual ℝ E} (hm : IsMonotoneDualMap A)
    (hh : IsHemicontinuousDualMap A) (hb : MapsBoundedSetsToBoundedSets A)
    {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hc : Convex ℝ C) (f : StrongDual ℝ E) :
    ∃ u, SolvesVariationalInequality A C f u := by
  sorry

/-- Coercivity relative to a point of an unbounded constraint set. -/
def IsCoerciveOnAt (A : E → StrongDual ℝ E) (C : Set E)
    (f : StrongDual ℝ E) (u₀ : E) : Prop :=
  Tendsto (fun u ↦ (A u - f) (u - u₀) / ‖u‖)
    ((Filter.comap (fun u : E ↦ ‖u‖) atTop) ⊓ Filter.principal C) atTop

/-- The unbounded-domain version uses coercivity relative to one feasible point. -/
theorem exists_solution_variationalInequality_of_coercive [CompleteSpace E]
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    {A : E → StrongDual ℝ E} (hm : IsMonotoneDualMap A)
    (hh : IsHemicontinuousDualMap A) (hb : MapsBoundedSetsToBoundedSets A)
    {C : Set E} (hclosed : IsClosed C) (hc : Convex ℝ C)
    (f : StrongDual ℝ E) {u₀ : E} (hu₀ : u₀ ∈ C) (hcoercive : IsCoerciveOnAt A C f u₀) :
    ∃ u, SolvesVariationalInequality A C f u := by
  sorry

end Banach

end CKMA
