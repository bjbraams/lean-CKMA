/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.FunctionalAnalysis.Basic
public import CKMA.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Weak sequence structure and local Hilbert geometry

Rosenthal's theorem is expressed using weakly Cauchy subsequences and two-sided finite
coefficient estimates for the l1 basis. Type and cotype use the L2 energy of finite Rademacher
sums, with one constant uniform over all finite families. Hilbertizability concerns an equivalent
Hilbert norm, rather than the parallelogram identity for the original norm.

Dvoretzky's theorem uses scaled embeddings, and the real Grothendieck bound has a universal
constant independent of every finite dimension. Dimension-zero cases are included.
Sources: GAPS 17.21, 17.38, 17.39, and 17.57.

## Main definitions

* `CKMA.IsEquivalentToEllOneBasis`: two-sided finite `ℓ¹` coefficient bounds for a sequence.
* `CKMA.rademacherEnergy`: second moment of a finite Rademacher sum.
* `CKMA.HasRademacherType`, `CKMA.HasRademacherCotype`: Rademacher type `p` and cotype `q`.
* `CKMA.IsHilbertizable`: existence of a continuous linear equivalence with a Hilbert space.
* `CKMA.grothendieckScalarBound`: scalar sign-choice supremum for a finite matrix.

## Main results

* `CKMA.rosenthal_ellOne`: Rosenthal's `ℓ¹` theorem.
* `CKMA.kwapien`: Kwapień's characterization of Hilbertizable Banach spaces.
* `CKMA.dvoretzky`: Dvoretzky's theorem on almost-isometric Euclidean subspaces.
* `CKMA.grothendieck_real`: the real Grothendieck inequality.

## Notation

No new notation is introduced.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped BigOperators

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Equivalence to the standard l1 basis, expressed by two-sided finite coefficient estimates.
Completeness then extends the coefficient map to the closed linear span. -/
def IsEquivalentToEllOneBasis (x : ℕ → E) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n : ℕ) (a : Fin n → ℝ),
    c * (∑ i, |a i|) ≤ ‖∑ i, a i • x i.val‖ ∧
      ‖∑ i, a i • x i.val‖ ≤ C * ∑ i, |a i|

/-- **17.21**, Rosenthal's l1 theorem over real Banach spaces. -/
theorem rosenthal_ellOne [CompleteSpace E] (x : ℕ → E)
    (hx : Bornology.IsBounded (Set.range x)) :
    ∃ r : ℕ → ℕ, StrictMono r ∧
      (IsWeaklyCauchy ℝ (x ∘ r) ∨ IsEquivalentToEllOneBasis (x ∘ r)) := by
  sorry

/-- The second moment of a finite Rademacher sum, using the uniform finite sign space. -/
def rademacherEnergy {n : ℕ} (x : Fin n → E) : ℝ :=
  ((Fintype.card (Fin n → Bool) : ℝ)⁻¹) *
    ∑ ε : Fin n → Bool, ‖∑ i, (if ε i then (1 : ℝ) else -1) • x i‖ ^ 2

/-- Type p, with a single constant uniform in all finite families. -/
def HasRademacherType (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ℝ) : Prop :=
  1 ≤ p ∧ p ≤ 2 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → E),
    Real.sqrt (rademacherEnergy x) ≤ C * (∑ i, ‖x i‖ ^ p) ^ (1 / p)

/-- Cotype q, with a single constant uniform in all finite families. -/
def HasRademacherCotype (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (q : ℝ) : Prop :=
  2 ≤ q ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → E),
    (∑ i, ‖x i‖ ^ q) ^ (1 / q) ≤ C * Real.sqrt (rademacherEnergy x)

/-- A concrete Hilbert-space isomorphism criterion for the original Banach norm. -/
def IsHilbertizable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∃ H : RealHilbertModel.{u}, Nonempty (E ≃L[ℝ] H.carrier)

/-- **17.38**, Kwapień: type two and cotype two characterize Hilbert-isomorphic Banach spaces. -/
theorem kwapien [CompleteSpace E] :
    IsHilbertizable E ↔ HasRademacherType E 2 ∧ HasRademacherCotype E 2 := by
  sorry

/-- **17.39**, Dvoretzky in a scaled embedding form equivalent to Banach–Mazur distortion
at most `1+ε`. This also makes the dimension-zero case unambiguous. -/
theorem dvoretzky [CompleteSpace E] (hE : ¬ FiniteDimensional ℝ E) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : EuclideanSpace ℝ (Fin n) →L[ℝ] E, Function.Injective T ∧
      ∀ x, ‖x‖ ≤ ‖T x‖ ∧ ‖T x‖ ≤ (1 + ε) * ‖x‖ := by
  sorry

/-- The scalar sign optimum in the real Grothendieck inequality. The set is nonempty even
if one index type is empty. -/
def grothendieckScalarBound {α β : Type*} [Fintype α] [Fintype β] (a : α → β → ℝ) : ℝ :=
  sSup {b | ∃ s : α → ℝ, ∃ t : β → ℝ,
    (∀ i, |s i| ≤ 1) ∧ (∀ j, |t j| ≤ 1) ∧ b = |∑ i, ∑ j, a i j * s i * t j|}

/-- **17.57**, the real Grothendieck inequality, with a universal constant independent of
both index types and the real inner product space. -/
theorem grothendieck_real : ∃ K : ℝ, 0 < K ∧ ∀ {α β H : Type*} [Fintype α] [Fintype β]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a : α → β → ℝ) (v : α → H) (w : β → H),
    (∀ i, ‖v i‖ ≤ 1) → (∀ j, ‖w j‖ ≤ 1) →
      |∑ i, ∑ j, a i j * inner ℝ (v i) (w j)| ≤ K * grothendieckScalarBound a := by
  sorry

end CKMA
