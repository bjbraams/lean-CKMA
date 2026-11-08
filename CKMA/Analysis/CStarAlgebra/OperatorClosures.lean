/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology

/-!
# Operator commutants, bicommutants, and Kaplansky density

The commutant uses Mathlib's set centralizer. Strong-operator approximation is tested on finite
families of vectors, and weak-operator approximation on finite families of matrix coefficients.
These criteria describe pointwise operator convergence, rather than norm or bounded convergence.
Mathlib's weak-operator topology supplies the corresponding convergence interface.

Bicommutants are considered for unital star subalgebras. Kaplansky density allows nonunital
norm-closed star subalgebras but explicitly assumes a nondegenerate action on the Hilbert space.
Inner products follow Mathlib's convention of linearity in the second variable.
Sources: GAPS 23.21 and 23.22.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded-operator commutant of a subset. -/
abbrev boundedOperatorCommutant (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H) :=
  Set.centralizer S

omit [CompleteSpace H] in
/-- Membership in the standard centralizer, in commuting-operator notation. -/
theorem mem_boundedOperatorCommutant_iff {S : Set (H →L[ℂ] H)} {T : H →L[ℂ] H} :
    T ∈ boundedOperatorCommutant S ↔ ∀ A ∈ S, Commute T A := by
  simp only [boundedOperatorCommutant, Set.mem_centralizer_iff]
  exact forall_congr' fun A ↦ forall_congr' fun _ ↦ eq_comm

/-- Strong-operator approximation on every finite family of vectors. -/
def IsStrongOperatorApproximable (S : Set (H →L[ℂ] H)) (T : H →L[ℂ] H) : Prop :=
  ∀ n : ℕ, ∀ x : Fin n → H, ∀ ε : ℝ, 0 < ε →
    ∃ A ∈ S, ∀ i, ‖(A - T) (x i)‖ < ε

/-- Weak-operator approximation on every finite family of matrix coefficients. -/
def IsWeakOperatorApproximable (S : Set (H →L[ℂ] H)) (T : H →L[ℂ] H) : Prop :=
  ∀ n : ℕ, ∀ x y : Fin n → H, ∀ ε : ℝ, 0 < ε →
    ∃ A ∈ S, ∀ i, ‖⟪y i, (A - T) (x i)⟫_ℂ‖ < ε

/-- Mathlib's weak-operator convergence is convergence of all Hilbert matrix coefficients. -/
theorem tendsto_weakOperator_iff {α : Type*} (u : α → H →L[ℂ] H)
    (l : Filter α) (T : H →L[ℂ] H) :
    Tendsto (fun a ↦ ContinuousLinearMapWOT.ofCLM (u a)) l
      (𝓝 (ContinuousLinearMapWOT.ofCLM T)) ↔
      ∀ x y, Tendsto (fun a ↦ inner ℂ y (u a x)) l (𝓝 (inner ℂ y (T x))) :=
  ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto

/-- Membership in the standard weak-operator closure gives the finite-coefficient approximation
criterion used in the bicommutant and density statements. -/
theorem IsWeakOperatorApproximable.of_mem_closure {S : Set (H →L[ℂ] H)} {T : H →L[ℂ] H}
    (h : ContinuousLinearMapWOT.ofCLM T ∈ closure (ContinuousLinearMapWOT.ofCLM '' S)) :
    IsWeakOperatorApproximable S T := by
  classical
  intro n x y ε hε
  let U : Set (H →WOT[ℂ] H) := {A | ∀ i,
    ‖inner ℂ (y i) (A (x i)) - inner ℂ (y i) (T (x i))‖ < ε}
  have hc (i : Fin n) : Continuous (fun A : H →WOT[ℂ] H ↦
      ‖inner ℂ (y i) (A (x i)) - inner ℂ (y i) (T (x i))‖) :=
    ((ContinuousLinearMapWOT.continuous_inner_apply continuous_id (x i) (y i)).sub
      continuous_const).norm
  have hU : IsOpen U := by
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_lt (hc i) continuous_const
  have hTU : ContinuousLinearMapWOT.ofCLM T ∈ U := by
    intro i
    simpa using hε
  obtain ⟨B, hBU, B', hB'S, hB'⟩ := (mem_closure_iff.1 h) U hU hTU
  refine ⟨B', hB'S, ?_⟩
  intro i
  have hi := hBU i
  rw [← hB'] at hi
  simpa only [ContinuousLinearMapWOT.ofCLM_apply, sub_apply, inner_sub_right] using hi

/-- **23.21**, the bicommutant theorem, in explicit neighborhood criteria for both operator
closures; these are the actual finite-vector definitions of the SOT and WOT closures. -/
theorem bicommutant_closures (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    (T ∈ boundedOperatorCommutant (boundedOperatorCommutant (A : Set (H →L[ℂ] H))) ↔
      IsStrongOperatorApproximable (A : Set (H →L[ℂ] H)) T) ∧
    (T ∈ boundedOperatorCommutant (boundedOperatorCommutant (A : Set (H →L[ℂ] H))) ↔
      IsWeakOperatorApproximable (A : Set (H →L[ℂ] H)) T) := by
  sorry

/-- **23.22**, Kaplansky density for a possibly nonunital, nondegenerately represented
C*-algebra. Nondegeneracy is stated by density of the linear action span. -/
theorem kaplansky_density (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hc : IsClosed (A : Set (H →L[ℂ] H)))
    (hd : Dense (Submodule.span ℂ {x : H | ∃ a ∈ A, ∃ y : H, a y = x} : Set H))
    (T : H →L[ℂ] H) (hT : T ∈ boundedOperatorCommutant
      (boundedOperatorCommutant (A : Set (H →L[ℂ] H)))) (hbound : ‖T‖ ≤ 1) :
    IsStrongOperatorApproximable {a | a ∈ A ∧ ‖a‖ ≤ 1} T := by
  sorry

/-- The self-adjoint unit-ball version of Kaplansky density. -/
theorem kaplansky_density_selfAdjoint (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hc : IsClosed (A : Set (H →L[ℂ] H)))
    (hd : Dense (Submodule.span ℂ {x : H | ∃ a ∈ A, ∃ y : H, a y = x} : Set H))
    (T : H →L[ℂ] H) (hT : T ∈ boundedOperatorCommutant
      (boundedOperatorCommutant (A : Set (H →L[ℂ] H)))) (hbound : ‖T‖ ≤ 1)
    (hsa : IsSelfAdjoint T) :
    IsStrongOperatorApproximable {a | a ∈ A ∧ ‖a‖ ≤ 1 ∧ IsSelfAdjoint a} T := by
  sorry

end CKMA
