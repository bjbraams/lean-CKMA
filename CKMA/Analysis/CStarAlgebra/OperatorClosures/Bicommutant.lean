/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology

import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import TauCeti.Analysis.VonNeumannAlgebra.Bicommutant

/-!
# Operator commutants and the bicommutant theorem

The commutant uses Mathlib's set centralizer. Strong-operator approximation is tested on finite
families of vectors, and weak-operator approximation on finite families of matrix coefficients.
These criteria describe pointwise operator convergence, rather than norm or bounded convergence.
Mathlib's weak-operator topology supplies the corresponding convergence interface.
Bicommutants are considered for unital star subalgebras.
Inner products follow Mathlib's convention of linearity in the second variable.
Sources: GAPS 23.21.

The finite-vector strong density of a unital star algebra in its bicommutant is TauCeti's
`StarSubalgebra.exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer`.
This argument is operator-algebraic and does not factor through another CKMA section's `Basic`
file. Kaplansky density is in `CKMA.Analysis.CStarAlgebra.OperatorClosures.Kaplansky`.

## Main definitions

* `CKMA.boundedOperatorCommutant`: commutant of a set of bounded Hilbert-space operators.
* `CKMA.IsStrongOperatorApproximable`: strong-operator closure criterion on finite vector tuples.
* `CKMA.IsWeakOperatorApproximable`: weak-operator closure criterion on finite matrix coefficients.

## Main results

* `CKMA.mem_boundedOperatorCommutant_iff`: characterization of membership in the commutant.
* `CKMA.IsWeakOperatorApproximable.of_mem_closure`: WOT closure implies finite-coefficient
  weak-operator approximability.
* `CKMA.bicommutant_closures`: von Neumann bicommutant theorem (**23.21**).
-/

public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded-operator commutant of a subset. -/
@[expose]
abbrev boundedOperatorCommutant (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H) :=
  Set.centralizer S

omit [CompleteSpace H] in
/-- Membership in the standard centralizer, in commuting-operator notation. -/
theorem mem_boundedOperatorCommutant_iff {S : Set (H →L[ℂ] H)} {T : H →L[ℂ] H} :
    T ∈ boundedOperatorCommutant S ↔ ∀ A ∈ S, Commute T A := by
  simp only [boundedOperatorCommutant, Set.mem_centralizer_iff]
  exact forall_congr' fun A ↦ forall_congr' fun _ ↦ eq_comm

/-- Strong-operator approximation on every finite family of vectors. -/
@[expose]
def IsStrongOperatorApproximable (S : Set (H →L[ℂ] H)) (T : H →L[ℂ] H) : Prop :=
  ∀ n : ℕ, ∀ x : Fin n → H, ∀ ε : ℝ, 0 < ε →
    ∃ A ∈ S, ∀ i, ‖(A - T) (x i)‖ < ε

/-- Weak-operator approximation on every finite family of matrix coefficients. -/
@[expose]
def IsWeakOperatorApproximable (S : Set (H →L[ℂ] H)) (T : H →L[ℂ] H) : Prop :=
  ∀ n : ℕ, ∀ x y : Fin n → H, ∀ ε : ℝ, 0 < ε →
    ∃ A ∈ S, ∀ i, ‖⟪y i, (A - T) (x i)⟫_ℂ‖ < ε

/-- Mathlib's weak-operator convergence is convergence of all Hilbert matrix coefficients. -/
@[deprecated "use `ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto`"
  (since := "2026-11-15")]
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

section

omit [CompleteSpace H]

/-- Strong-operator approximation yields weak-operator approximation by Cauchy–Schwarz. -/
private theorem isWeakOperatorApproximable_of_isStrongOperatorApproximable
    {S : Set (H →L[ℂ] H)} {T : H →L[ℂ] H} (h : IsStrongOperatorApproximable S T) :
    IsWeakOperatorApproximable S T := by
  intro n x y ε hε
  let C : ℝ := ∑ i, ‖y i‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set δ : ℝ := ε / (C + 1) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨A, hA, hAx⟩ := h n x δ hδ
  refine ⟨A, hA, fun i => ?_⟩
  have hCy : ‖y i‖ ≤ C :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have hCδ : C * δ < ε := by
    rw [hδdef, mul_div_assoc']
    rw [div_lt_iff₀ (by positivity : 0 < C + 1)]
    nlinarith [hε, hC]
  calc ‖⟪y i, (A - T) (x i)⟫_ℂ‖
      ≤ ‖y i‖ * ‖(A - T) (x i)‖ := norm_inner_le_norm _ _
    _ ≤ ‖y i‖ * δ := mul_le_mul_of_nonneg_left (hAx i).le (norm_nonneg _)
    _ ≤ C * δ := mul_le_mul_of_nonneg_right hCy (le_of_lt hδ)
    _ < ε := hCδ

end

/-- An operator weakly approximated by `S` lies in the bicommutant of `S`. -/
private theorem mem_centralizer_centralizer_of_isWeakOperatorApproximable
    {S : Set (H →L[ℂ] H)} {T : H →L[ℂ] H} (hW : IsWeakOperatorApproximable S T) :
    T ∈ boundedOperatorCommutant (boundedOperatorCommutant S) := by
  rw [mem_boundedOperatorCommutant_iff]
  intro B hB
  rw [mem_boundedOperatorCommutant_iff] at hB
  ext v
  refine ext_inner_left ℂ fun u => ?_
  rw [mul_apply_eq_comp, mul_apply_eq_comp, ← sub_eq_zero, ← inner_sub_right]
  set z : ℂ := ⟪u, T (B v) - B (T v)⟫_ℂ
  refine norm_eq_zero.mp (le_antisymm ?_ (norm_nonneg _))
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨A, hA, happrox⟩ := hW 2
    (fun i : Fin 2 => if i = 0 then B v else v)
    (fun i : Fin 2 => if i = 0 then u else (star B) u) (ε / 2) (half_pos hε)
  have hcomm : A * B = B * A := (hB A hA).eq.symm
  have hA0 := happrox 0
  have hA1 := happrox 1
  simp only [Fin.isValue, ite_true, one_ne_zero, ite_false] at hA0 hA1
  have hAB : A (B v) = B (A v) := by
    simpa [mul_apply_eq_comp] using congr_fun (congrArg DFunLike.coe hcomm) v
  have hfirst : ⟪u, T (B v)⟫_ℂ - ⟪u, A (B v)⟫_ℂ = -⟪u, (A - T) (B v)⟫_ℂ := by
    rw [← inner_sub_right, ← inner_neg_right, sub_apply, neg_sub]
  have hsecond : ⟪u, B (A v)⟫_ℂ - ⟪u, B (T v)⟫_ℂ = ⟪(star B) u, (A - T) v⟫_ℂ := by
    rw [← inner_sub_right, ← map_sub, ← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.star_eq_adjoint, sub_apply]
  have hz : z = ⟪u, T (B v)⟫_ℂ - ⟪u, B (T v)⟫_ℂ := by
    simp [z, inner_sub_right]
  have hsplit : ⟪u, T (B v)⟫_ℂ - ⟪u, B (T v)⟫_ℂ =
      (⟪u, T (B v)⟫_ℂ - ⟪u, A (B v)⟫_ℂ) + (⟪u, B (A v)⟫_ℂ - ⟪u, B (T v)⟫_ℂ) := by
    rw [hAB]
    ring
  have hinner : z = -⟪u, (A - T) (B v)⟫_ℂ + ⟪(star B) u, (A - T) v⟫_ℂ := by
    rw [hz, hsplit, hfirst, hsecond]
  have hlt : ‖z‖ < ε := by
    calc ‖z‖ = ‖-⟪u, (A - T) (B v)⟫_ℂ + ⟪(star B) u, (A - T) v⟫_ℂ‖ := by rw [hinner]
      _ ≤ ‖-⟪u, (A - T) (B v)⟫_ℂ‖ + ‖⟪(star B) u, (A - T) v⟫_ℂ‖ := norm_add_le _ _
      _ = ‖⟪u, (A - T) (B v)⟫_ℂ‖ + ‖⟪(star B) u, (A - T) v⟫_ℂ‖ := by rw [norm_neg]
      _ < ε / 2 + ε / 2 := add_lt_add hA0 hA1
      _ = ε := by ring
  simpa using hlt

/-- Membership in the bicommutant gives strong-operator approximation, by TauCeti's finite-vector
density theorem. -/
private theorem isStrongOperatorApproximable_of_mem_centralizer_centralizer
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T ∈ boundedOperatorCommutant (boundedOperatorCommutant (A : Set (H →L[ℂ] H)))) :
    IsStrongOperatorApproximable (A : Set (H →L[ℂ] H)) T := by
  intro n x ε hε
  obtain ⟨s, hs, hsx⟩ :=
    A.exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer hT x hε
  refine ⟨s, hs, fun i => ?_⟩
  simpa [sub_apply, norm_sub_rev] using hsx i

/-- **23.21**, the bicommutant theorem, in explicit neighborhood criteria for both operator
closures; these are the actual finite-vector definitions of the SOT and WOT closures. -/
theorem bicommutant_closures (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    (T ∈ boundedOperatorCommutant (boundedOperatorCommutant (A : Set (H →L[ℂ] H))) ↔
      IsStrongOperatorApproximable (A : Set (H →L[ℂ] H)) T) ∧
    (T ∈ boundedOperatorCommutant (boundedOperatorCommutant (A : Set (H →L[ℂ] H))) ↔
      IsWeakOperatorApproximable (A : Set (H →L[ℂ] H)) T) := by
  have hstrong : T ∈ boundedOperatorCommutant (boundedOperatorCommutant (A : Set _)) ↔
      IsStrongOperatorApproximable (A : Set _) T := by
    constructor
    · exact isStrongOperatorApproximable_of_mem_centralizer_centralizer A
    · intro hS
      exact mem_centralizer_centralizer_of_isWeakOperatorApproximable
        (isWeakOperatorApproximable_of_isStrongOperatorApproximable hS)
  have hweak : T ∈ boundedOperatorCommutant (boundedOperatorCommutant (A : Set _)) ↔
      IsWeakOperatorApproximable (A : Set _) T := by
    constructor
    · intro hT
      exact isWeakOperatorApproximable_of_isStrongOperatorApproximable (hstrong.mp hT)
    · exact mem_centralizer_centralizer_of_isWeakOperatorApproximable
  exact ⟨hstrong, hweak⟩

end CKMA
