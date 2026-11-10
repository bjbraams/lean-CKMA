/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Tactic

/-!
# Free moments, free cumulants, and the R-transform

Freeness of unital subalgebras is tested on nonempty alternating centered words. The free
central limit statement is convergence of each moment to the Catalan moments of the normalized
semicircle law. It uses a positive normalized state and identically distributed self-adjoint
variables, without an unnecessary boundedness assumption on those algebraic variables.

Free cumulants are defined by a triangular moment recursion. Coefficientwise additivity is
algebraic; analytic R-transform additivity is restricted to a genuine common convergence disk
for bounded variables and a continuous normalized functional. Sources: GAPS 23.65 and 23.68.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped BigOperators

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Algebraic freeness of unital subalgebras: nonempty alternating centered words have zero
expectation. Excluding the empty word is essential for a normalized functional. -/
def AreFreeSubalgebras {ι : Type*} (φ : A →ₗ[ℂ] ℂ) (S : ι → Subalgebra ℂ A) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ i : Fin n → ι, ∀ a : Fin n → A,
    (∀ j, a j ∈ S (i j)) → (∀ j, φ (a j) = 0) →
    (∀ j k : Fin n, j.val + 1 = k.val → i j ≠ i k) → φ (List.ofFn a).prod = 0

/-- The scalar moments of a noncommutative variable. -/
def noncommutativeMoments (φ : A →ₗ[ℂ] ℂ) (a : A) (n : ℕ) : ℂ := φ (a ^ n)

/-- Moments of the centered variance-one semicircle law, written in the closed Catalan form. -/
def semicircleMoment (n : ℕ) : ℂ :=
  if Even n then ((Nat.choose n (n / 2) / (n / 2 + 1) : ℕ) : ℂ) else 0

/-- A normalized positive functional in the star-algebra setting. -/
def IsPositiveNoncommutativeState {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    (φ : B →ₗ[ℂ] ℂ) : Prop :=
  φ 1 = 1 ∧ ∀ a : B, ∃ r : ℝ, 0 ≤ r ∧ φ (star a * a) = (r : ℂ)

/-- **23.65**, the free central limit theorem in moments; boundedness is unnecessary for
this algebraic moment assertion. The state is positive, the variables are self-adjoint,
and their complete moment sequences agree. -/
theorem free_central_limit {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    (φ : B →ₗ[ℂ] ℂ) (hφ : IsPositiveNoncommutativeState φ) (X : ℕ → B)
    (hsa : ∀ i, IsSelfAdjoint (X i)) (hmean : ∀ i, φ (X i) = 0)
    (hvar : ∀ i, φ (X i ^ 2) = 1)
    (hlaw : ∀ i m, noncommutativeMoments φ (X i) m = noncommutativeMoments φ (X 0) m)
    (hfree : AreFreeSubalgebras φ (fun i ↦ Algebra.adjoin ℂ {X i})) (m : ℕ) :
    Tendsto (fun n : ℕ ↦ φ ((((Real.sqrt (n + 1) : ℂ)⁻¹) •
      (∑ i ∈ Finset.range (n + 1), X i)) ^ m)) atTop (𝓝 (semicircleMoment m)) := by
  sorry

/-- The finite composition coefficient of the kth power of a scalar moment series. -/
def momentCompositionCoefficient (m : ℕ → ℂ) (k n : ℕ) : ℂ :=
  ∑ a : Fin k → Fin (n + 1), if (∑ j, (a j).val) = n then ∏ j, m (a j).val else 0

/-- Free cumulants defined by the triangular moment recursion obtained by distinguishing
the block containing the first point of a noncrossing partition. No existence theorem is used. -/
def freeCumulants (m : ℕ → ℂ) (n : ℕ) : ℂ := by
  classical
  exact Nat.strongRecOn n (fun k previous ↦ if hk : k = 0 then 0 else
    m k - ∑ j : Fin (k - 1), previous (j.val + 1) (by omega) *
      momentCompositionCoefficient m (j.val + 1) (k - (j.val + 1)))

/-- The R-transform represented by its convergent cumulant series near zero. Its analytic
convergence is a theorem for bounded variables; totalized sums outside that region are not used. -/
def freeRTransform (φ : A →ₗ[ℂ] ℂ) (a : A) (z : ℂ) : ℂ :=
  ∑' n, freeCumulants (noncommutativeMoments φ a) (n + 1) * z ^ n

/-- **23.68**, coefficientwise R-transform additivity for free variables. -/
theorem freeCumulants_add (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1)
    (S : Fin 2 → Subalgebra ℂ A) (hfree : AreFreeSubalgebras φ S)
    {a b : A} (ha : a ∈ S 0) (hb : b ∈ S 1) {n : ℕ} (hn : 0 < n) :
    freeCumulants (noncommutativeMoments φ (a + b)) n =
      freeCumulants (noncommutativeMoments φ a) n + freeCumulants (noncommutativeMoments φ b) n :=
        by
  sorry

/-- The analytic R-transform identity on a genuine common convergence disk for bounded
variables and a bounded normalized functional. -/
theorem freeRTransform_add {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
    (φ : B →L[ℂ] ℂ) (hφ : φ 1 = 1)
    (S : Fin 2 → Subalgebra ℂ B) (hfree : AreFreeSubalgebras φ.toLinearMap S)
    {a b : B} (ha : a ∈ S 0) (hb : b ∈ S 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r →
      Summable (fun n ↦ freeCumulants (noncommutativeMoments φ.toLinearMap a) (n + 1) * z ^ n) ∧
      Summable (fun n ↦ freeCumulants (noncommutativeMoments φ.toLinearMap b) (n + 1) * z ^ n) ∧
      Summable (fun n ↦ freeCumulants (noncommutativeMoments φ.toLinearMap (a + b)) (n + 1) * z ^ n)
        ∧
      freeRTransform φ.toLinearMap (a + b) z =
        freeRTransform φ.toLinearMap a z + freeRTransform φ.toLinearMap b z := by
  sorry

end CKMA
