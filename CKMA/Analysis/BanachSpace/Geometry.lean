/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.FunctionalAnalysis.Basic
public import CKMA.Analysis.InnerProductSpace.HilbertModel
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Normed.Module.RademacherSum.TypeCotype

import TauCeti.Analysis.Matrix.Grothendieck

/-!
# Weak sequence structure and local Hilbert geometry

Rosenthal's theorem is expressed using weakly Cauchy subsequences and two-sided finite
coefficient estimates for the l1 basis. Rademacher type and cotype are TauCeti's `TauCeti.HasType`
and `TauCeti.HasCotype` (the second moment of finite Rademacher sums against the `ℓᵖ` norm of the
family) with some constant, uniform over all finite families. Hilbertizability concerns an
equivalent Hilbert norm, rather than the parallelogram identity for the original norm.

Dvoretzky's theorem uses scaled embeddings, and the real Grothendieck bound has a universal
constant independent of every finite dimension. Dimension-zero cases are included. Rosenthal's
and Dvoretzky's theorems hold for normed spaces, since the completion has the same dual and the
same finite-dimensional subspaces up to small perturbation.
Sources: GAPS 17.21, 17.38, 17.39, and 17.57.
The real Grothendieck inequality uses TauCeti's matrix inequality with constant `8` and TauCeti's
entrywise bound `Matrix.abs_sum_sum_mul_inner_le_sum_sum_abs`.
The forward Kwapień implication uses TauCeti's type and cotype transport API.

## Main definitions

* `CKMA.IsEquivalentToEllOneBasis`: two-sided finite `ℓ¹` coefficient bounds for a sequence.
* `CKMA.HasRademacherType`, `CKMA.HasRademacherCotype`: Rademacher type `p ∈ [1, 2]` and
  cotype `q ≥ 2` with some constant.
* `CKMA.IsHilbertizable`: existence of a continuous linear equivalence with a Hilbert space.
* `CKMA.grothendieckScalarBound`: scalar sign-choice supremum for a finite matrix.

## Main results

* `CKMA.exists_strictMono_isWeaklyCauchy_or_isEquivalentToEllOneBasis`: Rosenthal's `ℓ¹`
  theorem (**17.21**).
* `CKMA.isHilbertizable_iff_hasRademacherType_two_and_cotype_two`: Kwapień's characterization
  of Hilbertizable Banach spaces (**17.38**).
* `CKMA.IsHilbertizable.hasRademacherType_two_and_cotype_two`: type and cotype of Hilbertizable
  normed spaces.
* `CKMA.exists_euclideanSpace_embedding_of_not_finiteDimensional`: Dvoretzky's theorem on
  almost-isometric Euclidean subspaces (**17.39**).
* `CKMA.grothendieck_real`: the real Grothendieck inequality (**17.57**).
-/

public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped BigOperators ENNReal NNReal

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Equivalence to the standard l1 basis, expressed by two-sided finite coefficient estimates.
Completeness then extends the coefficient map to the closed linear span. -/
@[expose]
def IsEquivalentToEllOneBasis (x : ℕ → E) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n : ℕ) (a : Fin n → ℝ),
    c * (∑ i, |a i|) ≤ ‖∑ i, a i • x i.val‖ ∧
      ‖∑ i, a i • x i.val‖ ≤ C * ∑ i, |a i|

/-- Unfolding `IsEquivalentToEllOneBasis`. -/
theorem isEquivalentToEllOneBasis_iff {x : ℕ → E} :
    IsEquivalentToEllOneBasis x ↔ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n : ℕ) (a : Fin n → ℝ),
      c * (∑ i, |a i|) ≤ ‖∑ i, a i • x i.val‖ ∧ ‖∑ i, a i • x i.val‖ ≤ C * ∑ i, |a i| :=
  Iff.rfl

/-- **17.21**, Rosenthal's l1 theorem over real normed spaces. -/
theorem exists_strictMono_isWeaklyCauchy_or_isEquivalentToEllOneBasis (x : ℕ → E)
    (hx : Bornology.IsBounded (Set.range x)) :
    ∃ r : ℕ → ℕ, StrictMono r ∧
      (IsWeaklyCauchy ℝ (x ∘ r) ∨ IsEquivalentToEllOneBasis (x ∘ r)) := by
  sorry

/-- Rademacher type `p ∈ [1, 2]`: TauCeti's type inequality `R₂(y) ≤ C ‖y‖ₚ` with a single
constant `C` uniform in all finite families. -/
@[expose]
def HasRademacherType (E : Type*) [SeminormedAddCommGroup E] (p : ℝ≥0∞) : Prop :=
  1 ≤ p ∧ p ≤ 2 ∧ ∃ C : ℝ≥0, TauCeti.HasType E p C

/-- Unfolding `HasRademacherType`. -/
theorem hasRademacherType_iff {F : Type*} [SeminormedAddCommGroup F] {p : ℝ≥0∞} :
    HasRademacherType F p ↔ 1 ≤ p ∧ p ≤ 2 ∧ ∃ C : ℝ≥0, TauCeti.HasType F p C :=
  Iff.rfl

/-- Rademacher cotype `q ≥ 2`: TauCeti's cotype inequality `‖y‖_q ≤ C R₂(y)` with a single
constant `C` uniform in all finite families. -/
@[expose]
def HasRademacherCotype (E : Type*) [SeminormedAddCommGroup E] (q : ℝ≥0∞) : Prop :=
  2 ≤ q ∧ ∃ C : ℝ≥0, TauCeti.HasCotype E q C

/-- Unfolding `HasRademacherCotype`. -/
theorem hasRademacherCotype_iff {F : Type*} [SeminormedAddCommGroup F] {q : ℝ≥0∞} :
    HasRademacherCotype F q ↔ 2 ≤ q ∧ ∃ C : ℝ≥0, TauCeti.HasCotype F q C :=
  Iff.rfl

/-- A concrete Hilbert-space isomorphism criterion for the original Banach norm. -/
@[expose]
def IsHilbertizable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∃ H : RealHilbertSpace.{u}, Nonempty (E ≃L[ℝ] H.carrier)

/-- Unfolding `IsHilbertizable`. -/
theorem isHilbertizable_iff : IsHilbertizable E ↔ ∃ H : RealHilbertSpace.{u},
    Nonempty (E ≃L[ℝ] H.carrier) :=
  Iff.rfl

/-- A Hilbertizable normed space has Rademacher type and cotype `2`. -/
theorem IsHilbertizable.hasRademacherType_two_and_cotype_two (h : IsHilbertizable E) :
    HasRademacherType E 2 ∧ HasRademacherCotype E 2 := by
  obtain ⟨H, ⟨U⟩⟩ := h
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  -- Type and cotype transport from the Hilbert norm via TauCeti's equivalence lemmas.
  exact ⟨⟨by norm_num, le_rfl, _,
      (TauCeti.hasType_two_of_innerProductSpace ℝ H.carrier).of_continuousLinearEquiv U⟩,
    ⟨le_rfl, _,
      (TauCeti.hasCotype_two_of_innerProductSpace ℝ H.carrier).of_continuousLinearEquiv U⟩⟩

/-- **17.38**, Kwapień: type two and cotype two characterize Hilbert-isomorphic Banach spaces. -/
theorem isHilbertizable_iff_hasRademacherType_two_and_cotype_two [CompleteSpace E] :
    IsHilbertizable E ↔ HasRademacherType E 2 ∧ HasRademacherCotype E 2 := by
  refine ⟨IsHilbertizable.hasRademacherType_two_and_cotype_two, ?_⟩
  sorry

/-- **17.39**, Dvoretzky in a scaled embedding form equivalent to Banach–Mazur distortion
at most `1+ε`. The lower bound `‖x‖ ≤ ‖T x‖` makes `T` injective. This also makes the
dimension-zero case unambiguous. -/
theorem exists_euclideanSpace_embedding_of_not_finiteDimensional (hE : ¬ FiniteDimensional ℝ E)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : EuclideanSpace ℝ (Fin n) →L[ℝ] E,
      ∀ x, ‖x‖ ≤ ‖T x‖ ∧ ‖T x‖ ≤ (1 + ε) * ‖x‖ := by
  sorry

/-- The scalar sign optimum in the real Grothendieck inequality. The set is nonempty even
if one index type is empty. -/
@[expose]
def grothendieckScalarBound {α β : Type*} [Fintype α] [Fintype β] (a : α → β → ℝ) : ℝ :=
  sSup {b | ∃ s : α → ℝ, ∃ t : β → ℝ,
    (∀ i, |s i| ≤ 1) ∧ (∀ j, |t j| ≤ 1) ∧ b = |∑ i, ∑ j, a i j * s i * t j|}

/-- Unfolding `grothendieckScalarBound`. -/
theorem grothendieckScalarBound_def {α β : Type*} [Fintype α] [Fintype β] (a : α → β → ℝ) :
    grothendieckScalarBound a = sSup {b | ∃ s : α → ℝ, ∃ t : β → ℝ,
      (∀ i, |s i| ≤ 1) ∧ (∀ j, |t j| ≤ 1) ∧ b = |∑ i, ∑ j, a i j * s i * t j|} :=
  rfl

/-- Every sign-choice sum is at most the scalar bound. -/
theorem le_grothendieckScalarBound {α β : Type*} [Fintype α] [Fintype β] (a : α → β → ℝ)
    {s : α → ℝ} {t : β → ℝ} (hs : ∀ i, |s i| ≤ 1) (ht : ∀ j, |t j| ≤ 1) :
    |∑ i, ∑ j, a i j * s i * t j| ≤ grothendieckScalarBound a := by
  refine le_csSup ⟨∑ i, ∑ j, |a i j|, ?_⟩ ⟨s, t, hs, ht, rfl⟩
  rintro b ⟨u, z, hu, hz, rfl⟩
  -- Scalars are vectors of the real inner product space `ℝ`, with `⟪u, z⟫ = u * z`.
  have h := Matrix.abs_sum_sum_mul_inner_le_sum_sum_abs (E := ℝ) (a : Matrix α β ℝ)
    (u := u) (v := z) (fun i ↦ by simpa using hu i) (fun j ↦ by simpa using hz j)
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- **17.57**, the real Grothendieck inequality, with a universal constant independent of
both index types and the real inner product space. -/
theorem grothendieck_real : ∃ K : ℝ, 0 < K ∧ ∀ {α β H : Type*} [Fintype α] [Fintype β]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a : α → β → ℝ) (v : α → H) (w : β → H),
    (∀ i, ‖v i‖ ≤ 1) → (∀ j, ‖w j‖ ≤ 1) →
      |∑ i, ∑ j, a i j * inner ℝ (v i) (w j)| ≤ K * grothendieckScalarBound a :=
  ⟨8, by norm_num, fun a _ _ hv hw ↦ Matrix.abs_sum_sum_mul_inner_le_eight_mul a
    (fun _ _ hs ht ↦ le_grothendieckScalarBound a hs ht) hv hw⟩

end CKMA
