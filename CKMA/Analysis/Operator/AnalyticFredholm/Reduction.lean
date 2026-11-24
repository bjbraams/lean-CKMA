/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes

import Mathlib.Algebra.Group.Action.Units
import Mathlib.Algebra.Module.NatInt
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NthRewrite
import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Fredholm.CompactPerturbation

/-!
# Finite-rank reduction for the analytic Fredholm theorem

A holomorphic compact family is a compact perturbation of the identity, hence Fredholm of index
zero. At each parameter a finite-rank correction, read off a Fredholm package, makes the operator
invertible. The original family factors as that invertible analytic factor times `1` minus a
finite-rank family. Invertibility of the finite-rank factor is the nonvanishing of one holomorphic
determinant, and the inverse is a holomorphic numerator over that determinant.

The resulting meromorphic representation, together with connectedness and one invertible value,
is `CKMA.analyticFredholm_aux`.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology ContinuousLinearMap Metric Submodule Matrix Module
open scoped Matrix

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- Evaluation of a finite sum of operators. -/
private theorem clm_sum_apply {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → X →L[ℂ] X) (x : X) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, add_apply, ih]

/-- A finite product of analytic scalar functions is analytic. -/
private theorem analyticAt_finset_prod {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {f : ι → ℂ → ℂ} {a : ℂ} (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) a) :
    AnalyticAt ℂ (fun z ↦ ∏ i ∈ s, f i z) a := by
  induction s using Finset.induction with
  | empty => simpa using analyticAt_const (v := (1 : ℂ))
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).mul
      (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

/-- A finite sum of analytic functions is analytic. -/
private theorem analyticAt_finset_sum {ι : Type*} [DecidableEq ι] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {s : Finset ι} {f : ι → ℂ → E} {a : ℂ}
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) a) :
    AnalyticAt ℂ (fun z ↦ ∑ i ∈ s, f i z) a := by
  induction s using Finset.induction with
  | empty => simpa using analyticAt_const (v := (0 : E))
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

/-- The determinant of a matrix of analytic scalar functions is analytic. -/
private theorem analyticAt_matrix_det {n : Type*} [Fintype n] [DecidableEq n]
    {M : ℂ → Matrix n n ℂ} {a : ℂ}
    (hM : ∀ i j, AnalyticAt ℂ (fun z ↦ M z i j) a) :
    AnalyticAt ℂ (fun z ↦ (M z).det) a := by
  have hfun : (fun z ↦ (M z).det) =
      fun z ↦ ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M z (σ i) i := by
    ext z
    rw [det_apply']
  rw [hfun]
  refine analyticAt_finset_sum fun σ _ ↦ ?_
  exact (analyticAt_const (v := ((Equiv.Perm.sign σ : ℤ) : ℂ))).mul
    (analyticAt_finset_prod fun i _ ↦ hM (σ i) i)

/-- Each entry of the adjugate of a matrix of analytic functions is analytic. -/
private theorem analyticAt_adjugate_apply {n : Type*} [Fintype n] [DecidableEq n]
    {M : ℂ → Matrix n n ℂ} {a : ℂ} {i j : n}
    (hM : ∀ i j, AnalyticAt ℂ (fun z ↦ M z i j) a) :
    AnalyticAt ℂ (fun z ↦ (M z).adjugate i j) a := by
  have hfun : (fun z ↦ (M z).adjugate i j) =
      fun z ↦ ((M z).updateRow j (Pi.single i 1)).det := by
    ext z
    rw [adjugate_apply]
  rw [hfun]
  refine analyticAt_matrix_det fun i' j' ↦ ?_
  by_cases hij : i' = j
  · have hrow : (fun z ↦ ((M z).updateRow j
          (Pi.single (M := fun _ : n ↦ ℂ) i (1 : ℂ))) i' j') =
        fun (_ : ℂ) ↦ Pi.single (M := fun _ : n ↦ ℂ) i (1 : ℂ) j' := by
      ext z
      simp [updateRow_apply, hij, Pi.single_apply]
    rw [hrow]
    exact analyticAt_const
  · have hrow : (fun z ↦ ((M z).updateRow j (Pi.single i 1)) i' j') =
        fun z ↦ M z i' j' := by
      ext z
      simp [updateRow_apply, hij]
    rw [hrow]
    exact hM i' j'

/-- Cancelling a lower power in a scalar quotient leaves the remaining power. -/
private theorem inv_mul_pow_mul_pow {c u : ℂ} {k m : ℕ} (hc : c ≠ 0) (hmk : m ≤ k) :
    (c ^ m * u)⁻¹ * c ^ k = c ^ (k - m) * u⁻¹ := by
  calc (c ^ m * u)⁻¹ * c ^ k
      = (c ^ m)⁻¹ * u⁻¹ * c ^ k := by conv_lhs => rw [mul_inv]
    _ = (c ^ m)⁻¹ * (c ^ k * u⁻¹) := by
        conv_lhs => rw [mul_assoc, mul_comm u⁻¹ (c ^ k)]
    _ = (c ^ m)⁻¹ * c ^ k * u⁻¹ := by conv_lhs => rw [← mul_assoc]
    _ = (c ^ m)⁻¹ * c ^ (k - m + m) * u⁻¹ := by
        conv_lhs => rw [← Nat.sub_add_cancel hmk]
    _ = (c ^ m)⁻¹ * (c ^ (k - m) * c ^ m) * u⁻¹ := by conv_lhs => rw [pow_add]
    _ = (c ^ m)⁻¹ * (c ^ m * c ^ (k - m)) * u⁻¹ := by
        conv_lhs => rw [mul_comm (c ^ (k - m)) (c ^ m)]
    _ = (c ^ m)⁻¹ * c ^ m * c ^ (k - m) * u⁻¹ := by conv_lhs => rw [← mul_assoc]
    _ = c ^ (k - m) * u⁻¹ := by
        conv_lhs => rw [inv_mul_cancel₀ (pow_ne_zero _ hc), one_mul]

omit [CompleteSpace X] in
/-- After cancelling a lower power, the scalar quotient acts as multiplication by the inverse. -/
private theorem inv_pow_smul_pow_smul {c u : ℂ} {v : X →L[ℂ] X} {k m : ℕ}
    (hc : c ≠ 0) (hmk : m ≤ k) :
    (c ^ m * u)⁻¹ • (c ^ k • v) = c ^ (k - m) • (u⁻¹ • v) := by
  rw [← mul_smul, inv_mul_pow_mul_pow hc hmk, mul_smul]

/-- A higher power restores a scalar quotient of a lower power. -/
private theorem pow_mul_inv_mul_pow {c u : ℂ} {k m : ℕ} (hc : c ≠ 0) (hu : u ≠ 0)
    (hkm : k ≤ m) : c ^ (m - k) * (c ^ m * u)⁻¹ * c ^ k = u⁻¹ := by
  have hcm : c ^ m ≠ 0 := pow_ne_zero _ hc
  field_simp [hcm, hu]
  rw [← pow_add, Nat.sub_add_cancel hkm]

omit [CompleteSpace X] in
/-- Restoring the missing power clears the scalar quotient. -/
private theorem pow_smul_inv_smul {c u : ℂ} {v : X →L[ℂ] X} {k m : ℕ}
    (hc : c ≠ 0) (hu : u ≠ 0) (hkm : k ≤ m) :
    c ^ (m - k) • ((c ^ m * u)⁻¹ • (c ^ k • v)) = u⁻¹ • v := by
  rw [← mul_smul, ← mul_smul, pow_mul_inv_mul_pow hc hu hkm]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The linear combination `∑ j, c j • w j`. -/
private def fredholmCombine (w : n → X) (c : n → ℂ) : X := ∑ j, c j • w j

/-- The finite-rank operator `x ↦ ∑ i, (ψ i x) • w i`. -/
private def fredholmFamily (ψ : n → X →L[ℂ] ℂ) (w : n → X) : X →L[ℂ] X :=
  ∑ i, (ψ i).smulRight (w i)

/-- The Gram coefficient matrix `A i j = ψ i (w j)`. -/
private def fredholmCoeff (ψ : n → X →L[ℂ] ℂ) (w : n → X) : Matrix n n ℂ :=
  of fun i j ↦ ψ i (w j)

/-- The matrix `1 - (ψ i (w j))`, whose determinant governs invertibility. -/
private def fredholmGram (ψ : n → X →L[ℂ] ℂ) (w : n → X) : Matrix n n ℂ :=
  1 - fredholmCoeff ψ w

/-- The finite-rank operator with coefficient matrix `C`. -/
private def fredholmCorrection (ψ : n → X →L[ℂ] ℂ) (w : n → X) (C : Matrix n n ℂ) :
    X →L[ℂ] X :=
  ∑ i, ∑ j, C j i • (ψ i).smulRight (w j)

omit [CompleteSpace X] [DecidableEq n] in
/-- `fredholmFamily` evaluates as the corresponding linear combination. -/
private theorem fredholmFamily_apply (ψ : n → X →L[ℂ] ℂ) (w : n → X) (x : X) :
    fredholmFamily ψ w x = fredholmCombine w (fun i ↦ ψ i x) := by
  simp [fredholmFamily, fredholmCombine, smulRight_apply]

omit [CompleteSpace X] [DecidableEq n] in
/-- A coefficient matrix scales the correction operator. -/
private theorem fredholmCorrection_smul (ψ : n → X →L[ℂ] ℂ) (w : n → X)
    (c : ℂ) (C : Matrix n n ℂ) :
    fredholmCorrection ψ w (c • C) = c • fredholmCorrection ψ w C := by
  ext x
  simp [fredholmCorrection, smul_apply, smulRight_apply, Matrix.smul_apply, smul_eq_mul,
    smul_smul, Finset.smul_sum]

omit [CompleteSpace X] in
/-- The correction operator evaluates as a linear combination against `C *ᵥ v`. -/
private theorem fredholmCorrection_apply (ψ : n → X →L[ℂ] ℂ) (w : n → X)
    (C : Matrix n n ℂ) (x : X) :
    fredholmCorrection ψ w C x =
      fredholmCombine w (C *ᵥ fun i ↦ ψ i x) := by
  simp only [fredholmCorrection, fredholmCombine, clm_sum_apply, smul_apply, smulRight_apply,
    smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [← Finset.sum_smul, mulVec_apply, dotProduct]

omit [CompleteSpace X] [DecidableEq n] in
/-- Applying the family to a linear combination multiplies the coefficient vector. -/
private theorem fredholmFamily_combine (ψ : n → X →L[ℂ] ℂ) (w : n → X) (c : n → ℂ) :
    fredholmFamily ψ w (fredholmCombine w c) =
      fredholmCombine w (fredholmCoeff ψ w *ᵥ c) := by
  simp only [fredholmFamily_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [fredholmCombine, map_sum, map_smul, smul_eq_mul, mul_comm, mulVec_apply, dotProduct,
    fredholmCoeff, of_apply]

omit [CompleteSpace X] [DecidableEq n] in
/-- Linear combinations commute with subtraction of coefficient vectors. -/
private theorem fredholmCombine_sub (w : n → X) (c d : n → ℂ) :
    fredholmCombine w (c - d) = fredholmCombine w c - fredholmCombine w d := by
  simp [fredholmCombine, sub_smul, Finset.sum_sub_distrib]

omit [CompleteSpace X] [DecidableEq n] in
/-- Linear combinations commute with a double subtraction of coefficient vectors. -/
private theorem fredholmCombine_sub_sub (w : n → X) (c d e : n → ℂ) :
    fredholmCombine w c - fredholmCombine w d - fredholmCombine w e =
      fredholmCombine w (c - d - e) := by
  rw [← fredholmCombine_sub, ← fredholmCombine_sub]

omit [CompleteSpace X] in
/-- Right multiplication by a corrected identity shifts the coefficient matrix by `gram * C`. -/
private theorem one_sub_family_mul_one_add_correction (ψ : n → X →L[ℂ] ℂ) (w : n → X)
    (C : Matrix n n ℂ) :
    (1 - fredholmFamily ψ w) * (1 + fredholmCorrection ψ w C) =
      1 + fredholmCorrection ψ w (fredholmGram ψ w * C - 1) := by
  ext x
  let v : n → ℂ := fun i ↦ ψ i x
  let A : Matrix n n ℂ := fredholmCoeff ψ w
  have hC : fredholmCorrection ψ w C x = fredholmCombine w (C *ᵥ v) := by
    simpa [v] using fredholmCorrection_apply ψ w C x
  have hfam : fredholmFamily ψ w x = fredholmCombine w v := by
    simpa [v] using fredholmFamily_apply ψ w x
  have hfamC : fredholmFamily ψ w (fredholmCombine w (C *ᵥ v)) =
      fredholmCombine w ((A * C) *ᵥ v) := by
    rw [fredholmFamily_combine, mulVec_mulVec]
  have hcoeff : C *ᵥ v - v - (A * C) *ᵥ v = ((1 - A) * C - 1) *ᵥ v := by
    calc C *ᵥ v - v - (A * C) *ᵥ v
        = C *ᵥ v - (A * C) *ᵥ v - v := by rw [sub_right_comm]
      _ = 1 *ᵥ (C *ᵥ v) - (A * C) *ᵥ v - v := by
          conv_lhs => rw [← one_mulVec (v := C *ᵥ v)]
      _ = 1 *ᵥ (C *ᵥ v) - A *ᵥ (C *ᵥ v) - v := by conv_lhs => rw [← mulVec_mulVec]
      _ = (1 - A) *ᵥ (C *ᵥ v) - v := by conv_lhs => rw [← sub_mulVec]
      _ = ((1 - A) * C) *ᵥ v - v := by conv_lhs => rw [mulVec_mulVec]
      _ = ((1 - A) * C) *ᵥ v - 1 *ᵥ v := by
          exact congrArg (fun t ↦ ((1 - A) * C) *ᵥ v - t) (one_mulVec v).symm
      _ = ((1 - A) * C - 1) *ᵥ v := by conv_lhs => rw [← sub_mulVec]
  have hgram : fredholmGram ψ w = 1 - A := rfl
  calc (1 - fredholmFamily ψ w) ((1 + fredholmCorrection ψ w C) x)
      = (1 - fredholmFamily ψ w) (x + fredholmCorrection ψ w C x) := by
        rw [add_apply, one_apply_eq_self]
    _ = (1 - fredholmFamily ψ w) (x + fredholmCombine w (C *ᵥ v)) := by rw [hC]
    _ = x + fredholmCombine w (C *ᵥ v) -
          fredholmFamily ψ w (x + fredholmCombine w (C *ᵥ v)) := by
        rw [sub_apply, one_apply_eq_self]
    _ = x + fredholmCombine w (C *ᵥ v) -
          (fredholmFamily ψ w x + fredholmFamily ψ w (fredholmCombine w (C *ᵥ v))) := by
        rw [map_add]
    _ = x + fredholmCombine w (C *ᵥ v) -
          (fredholmCombine w v + fredholmCombine w ((A * C) *ᵥ v)) := by
        rw [hfam, hfamC]
    _ = x + (fredholmCombine w (C *ᵥ v) - fredholmCombine w v -
          fredholmCombine w ((A * C) *ᵥ v)) := by
        rw [add_sub_assoc, sub_add_eq_sub_sub]
    _ = x + fredholmCombine w (C *ᵥ v - v - (A * C) *ᵥ v) := by
        rw [fredholmCombine_sub_sub]
    _ = x + fredholmCombine w (((1 - A) * C - 1) *ᵥ v) := by rw [hcoeff]
    _ = x + fredholmCorrection ψ w ((1 - A) * C - 1) x := by
        rw [fredholmCorrection_apply]
    _ = (1 + fredholmCorrection ψ w (fredholmGram ψ w * C - 1)) x := by
        rw [hgram, add_apply, one_apply_eq_self]

omit [CompleteSpace X] in
/-- Left multiplication by a corrected identity shifts the coefficient matrix by `C * gram`. -/
private theorem one_add_correction_mul_one_sub_family (ψ : n → X →L[ℂ] ℂ) (w : n → X)
    (C : Matrix n n ℂ) :
    (1 + fredholmCorrection ψ w C) * (1 - fredholmFamily ψ w) =
      1 + fredholmCorrection ψ w (C * fredholmGram ψ w - 1) := by
  ext x
  let v : n → ℂ := fun i ↦ ψ i x
  let A : Matrix n n ℂ := fredholmCoeff ψ w
  have hC : fredholmCorrection ψ w C x = fredholmCombine w (C *ᵥ v) := by
    simpa [v] using fredholmCorrection_apply ψ w C x
  have hcomb : fredholmCorrection ψ w C (fredholmCombine w v) =
      fredholmCombine w ((C * A) *ᵥ v) := by
    rw [fredholmCorrection_apply]
    have hψ : (fun i ↦ ψ i (fredholmCombine w v)) = A *ᵥ v := by
      ext i
      simp only [fredholmCombine, map_sum, map_smul, smul_eq_mul, mulVec_apply_eq_sum, A,
        fredholmCoeff, of_apply, mul_comm]
    rw [hψ, mulVec_mulVec]
  have hcoeff : C *ᵥ v - v - (C * A) *ᵥ v = (C * (1 - A) - 1) *ᵥ v := by
    calc C *ᵥ v - v - (C * A) *ᵥ v
        = C *ᵥ v - (C * A) *ᵥ v - v := by rw [sub_right_comm]
      _ = C *ᵥ v - C *ᵥ (A *ᵥ v) - v := by conv_lhs => rw [← mulVec_mulVec]
      _ = C *ᵥ (v - A *ᵥ v) - v := by conv_lhs => rw [← mulVec_sub]
      _ = C *ᵥ (1 *ᵥ v - A *ᵥ v) - v := by
          exact congrArg (fun t ↦ C *ᵥ (t - A *ᵥ v) - v) (one_mulVec v).symm
      _ = C *ᵥ ((1 - A) *ᵥ v) - v := by conv_lhs => rw [← sub_mulVec]
      _ = (C * (1 - A)) *ᵥ v - v := by conv_lhs => rw [mulVec_mulVec]
      _ = (C * (1 - A)) *ᵥ v - 1 *ᵥ v := by
          exact congrArg (fun t ↦ (C * (1 - A)) *ᵥ v - t) (one_mulVec v).symm
      _ = (C * (1 - A) - 1) *ᵥ v := by conv_lhs => rw [← sub_mulVec]
  have hgram : fredholmGram ψ w = 1 - A := rfl
  calc (1 + fredholmCorrection ψ w C) ((1 - fredholmFamily ψ w) x)
      = (1 + fredholmCorrection ψ w C) (x - fredholmFamily ψ w x) := by
        rw [sub_apply, one_apply_eq_self]
    _ = (1 + fredholmCorrection ψ w C) (x - fredholmCombine w v) := by
        rw [fredholmFamily_apply]
    _ = x - fredholmCombine w v + fredholmCorrection ψ w C (x - fredholmCombine w v) := by
        rw [add_apply, one_apply_eq_self]
    _ = x - fredholmCombine w v +
          (fredholmCorrection ψ w C x - fredholmCorrection ψ w C (fredholmCombine w v)) := by
        rw [map_sub]
    _ = x - fredholmCombine w v +
          (fredholmCombine w (C *ᵥ v) - fredholmCombine w ((C * A) *ᵥ v)) := by
        rw [hC, hcomb]
    _ = x + (fredholmCombine w (C *ᵥ v) - fredholmCombine w v -
          fredholmCombine w ((C * A) *ᵥ v)) := by
        abel
    _ = x + fredholmCombine w (C *ᵥ v - v - (C * A) *ᵥ v) := by
        rw [fredholmCombine_sub_sub]
    _ = x + fredholmCombine w ((C * (1 - A) - 1) *ᵥ v) := by rw [hcoeff]
    _ = x + fredholmCorrection ψ w (C * (1 - A) - 1) x := by
        rw [fredholmCorrection_apply]
    _ = (1 + fredholmCorrection ψ w (C * fredholmGram ψ w - 1)) x := by
        rw [hgram, add_apply, one_apply_eq_self]

/-- `1` minus a finite-rank family is a unit exactly when its Gram determinant is nonzero. -/
private theorem isUnit_one_sub_family_iff (ψ : n → X →L[ℂ] ℂ) (w : n → X) :
    IsUnit (1 - fredholmFamily ψ w) ↔ (fredholmGram ψ w).det ≠ 0 := by
  constructor
  · intro hunit hdet
    rw [ContinuousLinearMap.isUnit_iff_bijective] at hunit
    obtain ⟨v, hv, hMv⟩ := (exists_mulVec_eq_zero_iff.mpr hdet)
    let A : Matrix n n ℂ := fredholmCoeff ψ w
    have hA : A *ᵥ v = v := by
      have hsub : (fredholmGram ψ w) *ᵥ v = v - A *ᵥ v := by
        rw [fredholmGram, sub_mulVec, one_mulVec]
      rw [hMv] at hsub
      exact (sub_eq_zero.mp hsub.symm).symm
    let x : X := fredholmCombine w v
    have hx0 : (1 - fredholmFamily ψ w) x = 0 := by
      rw [sub_apply, one_apply_eq_self, fredholmFamily_combine, hA, sub_self]
    have hx : x ≠ 0 := by
      intro hx0'
      have hv0 : A *ᵥ v = 0 := by
        ext i
        simp only [mulVec_apply_eq_sum, A, fredholmCoeff, Matrix.of_apply]
        have hdot : ∑ j, ψ i (w j) * v j = ψ i x := by
          simp [x, fredholmCombine, map_sum, map_smul, smul_eq_mul, mul_comm]
        rw [hdot, hx0', map_zero]
        exact (Pi.zero_apply (M := fun _ : n ↦ ℂ) i).symm
      exact hv (by rw [← hA, hv0])
    have hzero : (1 - fredholmFamily ψ w) 0 = 0 := map_zero _
    exact hx (hunit.1 (hx0.trans hzero.symm))
  · intro hdet
    have hM : IsUnit (fredholmGram ψ w).det := isUnit_iff_ne_zero.mpr hdet
    let C : Matrix n n ℂ := (fredholmGram ψ w)⁻¹
    have hright := one_sub_family_mul_one_add_correction ψ w C
    have hleft := one_add_correction_mul_one_sub_family ψ w C
    rw [mul_nonsing_inv (A := fredholmGram ψ w) hM, sub_self] at hright
    rw [nonsing_inv_mul (A := fredholmGram ψ w) hM, sub_self] at hleft
    have hzero : fredholmCorrection ψ w (0 : Matrix n n ℂ) = 0 := by
      ext x
      simp [fredholmCorrection]
    rw [hzero, add_zero] at hright hleft
    exact isUnit_iff_exists.mpr ⟨1 + fredholmCorrection ψ w C, hright, hleft⟩

/-- When the Gram determinant is nonzero, the inverse is the corrected identity. -/
private theorem inverse_one_sub_family (ψ : n → X →L[ℂ] ℂ) (w : n → X)
    (hdet : (fredholmGram ψ w).det ≠ 0) :
    Ring.inverse (1 - fredholmFamily ψ w) =
      1 + (fredholmGram ψ w).det⁻¹ • fredholmCorrection ψ w (fredholmGram ψ w).adjugate := by
  have hM : IsUnit (fredholmGram ψ w).det := isUnit_iff_ne_zero.mpr hdet
  let C : Matrix n n ℂ := (fredholmGram ψ w)⁻¹
  have hunit : IsUnit (1 - fredholmFamily ψ w) :=
    (isUnit_one_sub_family_iff ψ w).mpr hdet
  have hright := one_sub_family_mul_one_add_correction ψ w C
  have hleft := one_add_correction_mul_one_sub_family ψ w C
  rw [mul_nonsing_inv (A := fredholmGram ψ w) hM, sub_self] at hright
  rw [nonsing_inv_mul (A := fredholmGram ψ w) hM, sub_self] at hleft
  have hzero : fredholmCorrection ψ w (0 : Matrix n n ℂ) = 0 := by
    ext x
    simp [fredholmCorrection]
  rw [hzero, add_zero] at hright hleft
  have hinv : 1 + fredholmCorrection ψ w C = Ring.inverse (1 - fredholmFamily ψ w) := by
    have hmul := Ring.mul_inverse_cancel (1 - fredholmFamily ψ w) hunit
    calc 1 + fredholmCorrection ψ w C
        = (1 + fredholmCorrection ψ w C) *
            ((1 - fredholmFamily ψ w) * Ring.inverse (1 - fredholmFamily ψ w)) := by
          rw [hmul, mul_one]
      _ = ((1 + fredholmCorrection ψ w C) * (1 - fredholmFamily ψ w)) *
            Ring.inverse (1 - fredholmFamily ψ w) := by rw [mul_assoc]
      _ = Ring.inverse (1 - fredholmFamily ψ w) := by rw [hleft, one_mul]
  rw [← hinv]
  have hC : C = (fredholmGram ψ w).det⁻¹ • (fredholmGram ψ w).adjugate := by
    simp only [C, Matrix.inv_def, Ring.inverse_eq_inv]
  rw [hC, fredholmCorrection_smul]

/-- An index-zero Fredholm operator differs from a unit by a finite-rank correction. -/
private theorem exists_finiteRank_add_isUnit {T : X →L[ℂ] X} (hT : IsFredholm T)
    (hind : T.index = 0) :
    ∃ n : ℕ, ∃ ψ : Fin n → X →L[ℂ] ℂ, ∃ w : Fin n → X,
      IsUnit (T + fredholmFamily ψ w) := by
  obtain ⟨pkg⟩ := hT.nonempty_fredholmPackage
  have : FiniteDimensional ℂ pkg.decDom.X₀ := pkg.decDom.finite_X₀
  have : FiniteDimensional ℂ pkg.decCodom.X₀ := pkg.decCodom.finite_X₀
  have hfin : finrank ℂ pkg.decDom.X₀ = finrank ℂ pkg.decCodom.X₀ := by
    have hidx := index_eq_finrank_sub T
    rw [hind] at hidx
    have hsub : (finrank ℂ (LinearMap.ker (T : X →ₗ[ℂ] X)) : ℤ) =
        finrank ℂ (X ⧸ LinearMap.range (T : X →ₗ[ℂ] X)) := sub_eq_zero.mp hidx.symm
    rw [pkg.ker_eq, pkg.range_eq] at hsub
    have hquot : finrank ℂ (X ⧸ pkg.decCodom.X₁) = finrank ℂ pkg.decCodom.X₀ :=
      (quotientEquivOfIsCompl _ _ pkg.decCodom.isTopCompl.isCompl).finrank_eq
    rw [hquot] at hsub
    exact Nat.cast_inj.mp hsub
  let e : pkg.decDom.X₀ ≃L[ℂ] pkg.decCodom.X₀ := ContinuousLinearEquiv.ofFinrankEq hfin
  let n : ℕ := finrank ℂ pkg.decDom.X₀
  let b : Basis (Fin n) ℂ pkg.decDom.X₀ := finBasisOfFinrankEq ℂ pkg.decDom.X₀ rfl
  let Pker : X →L[ℂ] pkg.decDom.X₀ :=
    pkg.decDom.X₀.projectionOntoL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm
  let ψ : Fin n → X →L[ℂ] ℂ := fun i ↦ (b.coord i).toContinuousLinearMap.comp Pker
  let w : Fin n → X := fun i ↦ (e (b i) : X)
  let F : X →L[ℂ] X :=
    pkg.decCodom.X₀.subtypeL ∘L (e : pkg.decDom.X₀ →L[ℂ] pkg.decCodom.X₀) ∘L Pker
  have hF : fredholmFamily ψ w = F := by
    ext x
    have hsum : ∑ i, b.coord i (Pker x) • b i = Pker x := by
      simp [Basis.coord_apply]
    calc fredholmFamily ψ w x
        = ∑ i, b.coord i (Pker x) • (e (b i) : X) := by
          simp [fredholmFamily_apply, fredholmCombine, ψ, w, ContinuousLinearMap.comp_apply,
            LinearMap.coe_toContinuousLinearMap']
      _ = (e (Pker x) : X) := by
          conv_rhs => rw [← hsum]
          rw [map_sum, Submodule.coe_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [map_smul, Submodule.coe_smul]
      _ = F x := by simp [F, ContinuousLinearMap.comp_apply, subtypeL_apply]
  refine ⟨n, ψ, w, ?_⟩
  rw [hF]
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  constructor
  · intro x y hxy
    have hsub : (T + F) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hker : ∀ u, (T + F) u = 0 → u = 0 := by
      intro u hu
      have hadd : T u + F u = 0 := by simpa [add_apply] using hu
      have hTu : T u = -F u := add_eq_zero_iff_eq_neg.mp hadd
      have hFu : F u = (e (Pker u) : X) := by
        simp [F, ContinuousLinearMap.comp_apply, subtypeL_apply]
      have hTuR : T u ∈ pkg.decCodom.X₀ := by
        rw [hTu, hFu]
        exact neg_mem (SetLike.coe_mem _)
      have hTuS : T u ∈ pkg.decCodom.X₁ := by
        rw [← pkg.range_eq]
        exact LinearMap.mem_range_self (T : X →ₗ[ℂ] X) u
      have hTu0 : T u = 0 := by
        have hbot : pkg.decCodom.X₁ ⊓ pkg.decCodom.X₀ = ⊥ :=
          pkg.decCodom.isTopCompl.isCompl.inf_eq_bot
        have : T u ∈ (⊥ : Submodule ℂ X) := by
          rw [← hbot]
          exact ⟨hTuS, hTuR⟩
        simpa [Submodule.mem_bot] using this
      have hFu0 : F u = 0 := by simpa [hTu0] using hadd
      have he0 : e (Pker u) = 0 := by
        apply Subtype.coe_injective
        simpa [hFu] using hFu0
      have hP0 : Pker u = 0 := by
        apply e.injective
        rw [map_zero]
        exact he0
      have huN : u ∈ pkg.decDom.X₀ := by
        rw [← pkg.ker_eq]
        exact LinearMap.mem_ker.mpr hTu0
      have hPid : Pker u = ⟨u, huN⟩ :=
        pkg.decDom.X₀.projectionOntoL_apply_left pkg.decDom.isTopCompl.symm ⟨u, huN⟩
      have : (⟨u, huN⟩ : pkg.decDom.X₀) = 0 := by simpa [hPid] using hP0
      exact congrArg Subtype.val this
    exact sub_eq_zero.mp (hker _ hsub)
  · intro y
    let yS : pkg.decCodom.X₁ :=
      pkg.decCodom.X₁.projectionOntoL pkg.decCodom.X₀ pkg.decCodom.isTopCompl y
    let yR : pkg.decCodom.X₀ :=
      pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm y
    let xM : pkg.decDom.X₁ := pkg.equiv.symm yS
    let xN : pkg.decDom.X₀ := e.symm yR
    refine ⟨(xM : X) + (xN : X), ?_⟩
    have hy : (yS : X) + (yR : X) = y := by
      simp only [yS, yR, coe_projectionOntoL_apply]
      exact pkg.decCodom.X₁.projectionL_add_projectionL_eq_self pkg.decCodom.isTopCompl y
    have hprojM : pkg.decDom.proj (xM : X) = xM :=
      pkg.decDom.X₁.projectionOntoL_apply_left pkg.decDom.isTopCompl xM
    have hTm : T (xM : X) = (yS : X) := by
      have happly := congr_fun (congrArg (fun f : X →L[ℂ] X ↦ (f : X → X)) pkg.eq_equiv)
        (xM : X)
      simpa [ContinuousLinearMap.comp_apply, hprojM, ContinuousLinearEquiv.apply_symm_apply,
        subtypeL_apply, xM] using happly
    have hPm : Pker (xM : X) = 0 :=
      pkg.decDom.X₀.projectionOntoL_apply_right pkg.decDom.isTopCompl.symm xM
    have hFm : F (xM : X) = 0 := by simp [F, ContinuousLinearMap.comp_apply, hPm, subtypeL_apply]
    have hTn : T (xN : X) = 0 :=
      LinearMap.mem_ker.mp (by rw [pkg.ker_eq]; exact xN.2)
    have hPn : Pker (xN : X) = xN :=
      pkg.decDom.X₀.projectionOntoL_apply_left pkg.decDom.isTopCompl.symm xN
    have hFn : F (xN : X) = (yR : X) := by
      simp [F, ContinuousLinearMap.comp_apply, hPn, subtypeL_apply, xN,
        ContinuousLinearEquiv.apply_symm_apply]
    calc (T + F) ((xM : X) + (xN : X))
        = T ((xM : X) + (xN : X)) + F ((xM : X) + (xN : X)) := by rw [add_apply]
      _ = (T (xM : X) + T (xN : X)) + (F (xM : X) + F (xN : X)) := by rw [map_add, map_add]
      _ = (T (xM : X) + F (xM : X)) + (T (xN : X) + F (xN : X)) := by abel
      _ = (yS : X) + (yR : X) := by rw [hTm, hFm, hTn, hFn, add_zero, zero_add]
      _ = y := hy

/-- Near any parameter, `1 - K` is a unit exactly off the zeros of one analytic determinant,
and the inverse is that determinant's reciprocal times an analytic operator. -/
private theorem exists_meromorphic_factor {U : Set ℂ} (hU : IsOpen U)
    {K : ℂ → X →L[ℂ] X} (hK : DifferentiableOn ℂ K U)
    (hc : ∀ z ∈ U, IsCompactOperator (K z)) {a : ℂ} (ha : a ∈ U) :
    ∃ d : ℂ → ℂ, ∃ N : ℂ → X →L[ℂ] X, AnalyticAt ℂ d a ∧ AnalyticAt ℂ N a ∧
      ∀ᶠ z in 𝓝 a, z ∈ U ∧ (IsUnit (1 - K z) ↔ d z ≠ 0) ∧
        (d z ≠ 0 → Ring.inverse (1 - K z) = (d z)⁻¹ • N z) := by
  have hFred : IsFredholm (1 - K a) := TauCeti.isFredholm_one_sub (hc a ha)
  have hindex : (1 - K a).index = 0 := index_one_sub_eq_zero (hc a ha)
  obtain ⟨n, ψ, w, hunit0⟩ := exists_finiteRank_add_isUnit hFred hindex
  let F0 : X →L[ℂ] X := fredholmFamily ψ w
  let B : ℂ → X →L[ℂ] X := fun z ↦ 1 - K z + F0
  have hBa : IsUnit (B a) := by simpa [B, F0] using hunit0
  have hBdiff : DifferentiableOn ℂ B U :=
    ((differentiableOn_const _).sub hK).add (differentiableOn_const _)
  have hBan : AnalyticAt ℂ B a := hBdiff.analyticAt (hU.mem_nhds ha)
  have hA : AnalyticAt ℂ (fun z ↦ Ring.inverse (B z)) a :=
    (analyticAt_inverse hBa.unit).comp_of_eq hBan (IsUnit.unit_spec hBa).symm
  have hunitB : ∀ᶠ z in 𝓝 a, IsUnit (B z) :=
    hBan.continuousAt.eventually (Units.isOpen.mem_nhds hBa)
  have hUmem : ∀ᶠ z in 𝓝 a, z ∈ U := eventually_mem_set.mpr (hU.mem_nhds ha)
  let A : ℂ → X →L[ℂ] X := fun z ↦ Ring.inverse (B z)
  let wA : ℂ → Fin n → X := fun z i ↦ A z (w i)
  let M : ℂ → Matrix (Fin n) (Fin n) ℂ := fun z ↦ fredholmGram ψ (wA z)
  let d : ℂ → ℂ := fun z ↦ (M z).det
  let H : ℂ → X →L[ℂ] X :=
    fun z ↦ fredholmCorrection ψ (wA z) (M z).adjugate * A z
  let N : ℂ → X →L[ℂ] X := fun z ↦ d z • A z + H z
  have hwA : ∀ i, AnalyticAt ℂ (fun z ↦ wA z i) a := by
    intro i
    exact ((apply ℂ X (w i)).analyticAt _).comp hA
  have hMentry : ∀ i j, AnalyticAt ℂ (fun z ↦ (M z) i j) a := by
    intro i j
    have hψ : AnalyticAt ℂ (fun z ↦ ψ i (wA z j)) a := (ψ i).analyticAt _ |>.comp (hwA j)
    have hfun : (fun z ↦ (M z) i j) = fun z ↦ (1 : Matrix (Fin n) (Fin n) ℂ) i j -
        ψ i (wA z j) := by
      ext z
      simp [M, fredholmGram, fredholmCoeff, of_apply]
    rw [hfun]
    exact analyticAt_const.sub hψ
  have hd : AnalyticAt ℂ d a := by simpa [d] using analyticAt_matrix_det hMentry
  have hH : AnalyticAt ℂ H a := by
    have hcorr : AnalyticAt ℂ (fun z ↦ fredholmCorrection ψ (wA z) (M z).adjugate) a := by
      have hterm : ∀ i j, AnalyticAt ℂ
          (fun z ↦ ((M z).adjugate j i) • (ψ i).smulRight (wA z j)) a := by
        intro i j
        have hcoeff := analyticAt_adjugate_apply (M := M) (i := j) (j := i) hMentry
        have hrank : AnalyticAt ℂ (fun z ↦ (ψ i).smulRight (wA z j)) a := by
          have hlin : AnalyticAt ℂ (⇑(smulRightL ℂ X X (ψ i))) (wA a j) :=
            (smulRightL ℂ X X (ψ i)).analyticAt (wA a j)
          exact hlin.comp_of_eq (hwA j) rfl
        exact hcoeff.smul hrank
      simp only [fredholmCorrection]
      refine analyticAt_finset_sum fun i _ ↦ ?_
      exact analyticAt_finset_sum fun j _ ↦ hterm i j
    exact hcorr.mul hA
  have hN : AnalyticAt ℂ N a := (hd.smul hA).add hH
  refine ⟨d, N, hd, hN, ?_⟩
  filter_upwards [hunitB, hUmem] with z hzB hzU
  refine ⟨hzU, ?_, ?_⟩
  · have hfac : 1 - K z = B z * (1 - A z * F0) := by
      have hmul : B z * (A z * F0) = F0 := by
        rw [← mul_assoc, Ring.mul_inverse_cancel (B z) hzB, one_mul]
      calc 1 - K z
          = B z - F0 := by simp [B, add_sub_cancel_right]
        _ = B z - B z * (A z * F0) := by rw [hmul]
        _ = B z * (1 - A z * F0) := by
            nth_rw 1 [← mul_one (B z)]
            rw [mul_sub]
    have hG : A z * F0 = fredholmFamily ψ (wA z) := by
      ext x
      simp [A, F0, wA, fredholmFamily_apply, fredholmCombine, mul_apply_eq_comp, map_sum,
        map_smul]
    constructor
    · intro hu
      rw [hfac] at hu
      have hGu : IsUnit (1 - A z * F0) := (IsUnit.mul_left_iff hzB).mp hu
      rw [hG] at hGu
      exact (isUnit_one_sub_family_iff ψ (wA z)).mp hGu
    · intro hdne
      have hGu : IsUnit (1 - fredholmFamily ψ (wA z)) :=
        (isUnit_one_sub_family_iff ψ (wA z)).mpr hdne
      rw [← hG] at hGu
      rw [hfac]
      exact (IsUnit.mul_left_iff hzB).mpr hGu
  · intro hdne
    have hfac : 1 - K z = B z * (1 - A z * F0) := by
      have hmul : B z * (A z * F0) = F0 := by
        rw [← mul_assoc, Ring.mul_inverse_cancel (B z) hzB, one_mul]
      calc 1 - K z
          = B z - F0 := by simp [B, add_sub_cancel_right]
        _ = B z - B z * (A z * F0) := by rw [hmul]
        _ = B z * (1 - A z * F0) := by
            nth_rw 1 [← mul_one (B z)]
            rw [mul_sub]
    have hG : A z * F0 = fredholmFamily ψ (wA z) := by
      ext x
      simp [A, F0, wA, fredholmFamily_apply, fredholmCombine, mul_apply_eq_comp, map_sum,
        map_smul]
    rw [hfac, Ring.inverse_mul (Or.inl hzB), hG, inverse_one_sub_family ψ (wA z) hdne]
    have hsm : (d z)⁻¹ • (d z • A z) = A z := by
      rw [← mul_smul, inv_mul_cancel₀ hdne, one_smul]
    calc (1 + (d z)⁻¹ • fredholmCorrection ψ (wA z) (M z).adjugate) * A z
        = A z + ((d z)⁻¹ • fredholmCorrection ψ (wA z) (M z).adjugate) * A z := by
          rw [add_mul, one_mul]
      _ = A z + (d z)⁻¹ • (fredholmCorrection ψ (wA z) (M z).adjugate * A z) := by
          rw [smul_mul_assoc]
      _ = (d z)⁻¹ • (d z • A z) + (d z)⁻¹ • H z := by nth_rw 1 [← hsm]
      _ = (d z)⁻¹ • (d z • A z + H z) := by rw [smul_add]
      _ = (d z)⁻¹ • N z := by rfl

omit [CompleteSpace X] in
/-- An inverse that agrees with a continuous operator off the base point is a unit there. -/
private theorem isUnit_of_eventually_inverse_eq {K : ℂ → X →L[ℂ] X} {a : ℂ}
    (hK : ContinuousAt K a) {F : ℂ → X →L[ℂ] X} (hF : ContinuousAt F a)
    (hunit : ∀ᶠ z in 𝓝[≠] a, IsUnit (1 - K z))
    (heq : ∀ᶠ z in 𝓝[≠] a, Ring.inverse (1 - K z) = F z) :
    IsUnit (1 - K a) := by
  have hmul : ∀ᶠ z in 𝓝[≠] a, (1 - K z) * F z = 1 := by
    filter_upwards [heq, hunit] with z hz hu
    rw [← hz]
    exact Ring.mul_inverse_cancel (1 - K z) hu
  have hmul' : ∀ᶠ z in 𝓝[≠] a, F z * (1 - K z) = 1 := by
    filter_upwards [heq, hunit] with z hz hu
    rw [← hz]
    exact Ring.inverse_mul_cancel (1 - K z) hu
  have hcont : ContinuousAt (fun z ↦ (1 - K z) * F z) a :=
    (continuousAt_const.sub hK).mul hF
  have hcont' : ContinuousAt (fun z ↦ F z * (1 - K z)) a :=
    hF.mul (continuousAt_const.sub hK)
  have hmulEq : (fun z ↦ (1 - K z) * F z) =ᶠ[𝓝[≠] a] fun _ ↦ (1 : X →L[ℂ] X) := hmul
  have hmulEq' : (fun z ↦ F z * (1 - K z)) =ᶠ[𝓝[≠] a] fun _ ↦ (1 : X →L[ℂ] X) := hmul'
  have hleft : (1 - K a) * F a = 1 :=
    tendsto_nhds_unique (l := 𝓝[≠] a)
      (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      ((tendsto_const_nhds (f := 𝓝[≠] a) (x := (1 : X →L[ℂ] X))).congr' hmulEq.symm)
  have hright : F a * (1 - K a) = 1 :=
    tendsto_nhds_unique (l := 𝓝[≠] a)
      (hcont'.tendsto.mono_left nhdsWithin_le_nhds)
      ((tendsto_const_nhds (f := 𝓝[≠] a) (x := (1 : X →L[ℂ] X))).congr' hmulEq'.symm)
  exact isUnit_iff_exists.mpr ⟨F a, hleft, hright⟩

omit [CompleteSpace X] in
/-- A meromorphic representation with a zero denominator is a genuine inverse pole. -/
private theorem pole_of_meromorphic {K : ℂ → X →L[ℂ] X} {a : ℂ}
    (hK : ContinuousAt K a) (hX : ¬ Subsingleton (X →L[ℂ] X))
    {d : ℂ → ℂ} {N : ℂ → X →L[ℂ] X}
    (hd : AnalyticAt ℂ d a) (hN : AnalyticAt ℂ N a)
    (hfac : ∀ᶠ z in 𝓝 a, (IsUnit (1 - K z) ↔ d z ≠ 0) ∧
      (d z ≠ 0 → Ring.inverse (1 - K z) = (d z)⁻¹ • N z))
    (ha : ¬ IsUnit (1 - K a)) (hd0 : ¬ ∀ᶠ z in 𝓝 a, d z = 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ F : ℂ → X →L[ℂ] X, AnalyticAt ℂ F a ∧ F a ≠ 0 ∧
      (∀ᶠ z in 𝓝[≠] a, IsUnit (1 - K z)) ∧
      ∀ᶠ z in 𝓝[≠] a, (z - a) ^ m • Ring.inverse (1 - K z) = F z := by
  have hone : (1 : X →L[ℂ] X) ≠ 0 := by
    intro h10
    apply hX
    refine subsingleton_of_forall_eq (0 : X →L[ℂ] X) fun x ↦ ?_
    rw [← one_mul x, h10, zero_mul]
  have htop : analyticOrderAt d a ≠ ⊤ := by simpa [analyticOrderAt_eq_top] using hd0
  obtain ⟨u, hu, hu_ne, hu_eq⟩ := hd.analyticOrderAt_ne_top.mp htop
  let m : ℕ := analyticOrderNatAt d a
  have hdne : ∀ᶠ z in 𝓝[≠] a, d z ≠ 0 := by
    filter_upwards [hu_eq.filter_mono nhdsWithin_le_nhds,
      (hu.continuousAt.eventually_ne hu_ne).filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with z hz hu_z hza
    rw [hz]
    exact smul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hza)) hu_z
  have hunitp : ∀ᶠ z in 𝓝[≠] a, IsUnit (1 - K z) := by
    filter_upwards [hfac.filter_mono nhdsWithin_le_nhds, hdne] with z hz hdnez
    exact hz.1.mpr hdnez
  by_cases hNtop : analyticOrderAt N a = ⊤
  · have hN0 : ∀ᶠ z in 𝓝 a, N z = 0 := analyticOrderAt_eq_top.mp hNtop
    have hinv0 : ∀ᶠ z in 𝓝[≠] a, Ring.inverse (1 - K z) = 0 := by
      filter_upwards [hfac.filter_mono nhdsWithin_le_nhds, hdne,
        hN0.filter_mono nhdsWithin_le_nhds] with z hz hdnez hNz
      rw [hz.2 hdnez, hNz, smul_zero]
    have h10 : ∀ᶠ _ in 𝓝[≠] a, (1 : X →L[ℂ] X) = 0 := by
      filter_upwards [hinv0, hunitp] with z hinv hu
      have := Ring.inverse_mul_cancel (1 - K z) hu
      rw [hinv, zero_mul] at this
      exact this.symm
    obtain ⟨_, hz⟩ := h10.exists
    exact (hone hz).elim
  · obtain ⟨v, hv, hv_ne, hv_eq⟩ := hN.analyticOrderAt_ne_top.mp hNtop
    let k : ℕ := analyticOrderNatAt N a
    by_cases hle : m ≤ k
    · let F : ℂ → X →L[ℂ] X := fun z ↦ (z - a) ^ (k - m) • ((u z)⁻¹ • v z)
      have hF : AnalyticAt ℂ F a := by
        exact ((analyticAt_id.sub analyticAt_const).pow _).smul ((hu.inv hu_ne).smul hv)
      have hinvF : ∀ᶠ z in 𝓝[≠] a, Ring.inverse (1 - K z) = F z := by
        filter_upwards [hfac.filter_mono nhdsWithin_le_nhds, hdne,
          hu_eq.filter_mono nhdsWithin_le_nhds, hv_eq.filter_mono nhdsWithin_le_nhds,
          eventually_mem_nhdsWithin] with z hz hdnez hdu hNv hza
        have hc : z - a ≠ 0 := sub_ne_zero.mpr hza
        rw [hz.2 hdnez, hdu, hNv, smul_eq_mul]
        exact inv_pow_smul_pow_smul hc hle
      exact (ha (isUnit_of_eventually_inverse_eq hK hF.continuousAt hunitp hinvF)).elim
    · have hlt : k < m := Nat.not_le.mp hle
      have hp : 0 < m - k := Nat.sub_pos_of_lt hlt
      let F : ℂ → X →L[ℂ] X := fun z ↦ (u z)⁻¹ • v z
      have hF : AnalyticAt ℂ F a := (hu.inv hu_ne).smul hv
      have hFne : F a ≠ 0 := smul_ne_zero (inv_ne_zero hu_ne) hv_ne
      have heq : ∀ᶠ z in 𝓝[≠] a, (z - a) ^ (m - k) • Ring.inverse (1 - K z) = F z := by
        filter_upwards [hfac.filter_mono nhdsWithin_le_nhds, hdne,
          hu_eq.filter_mono nhdsWithin_le_nhds, hv_eq.filter_mono nhdsWithin_le_nhds,
          (hu.continuousAt.eventually_ne hu_ne).filter_mono nhdsWithin_le_nhds,
          eventually_mem_nhdsWithin] with z hz hdnez hdu hNv hu_z hza
        have hc : z - a ≠ 0 := sub_ne_zero.mpr hza
        rw [hz.2 hdnez, hdu, hNv, smul_eq_mul]
        exact pow_smul_inv_smul hc hu_z hlt.le
      exact ⟨m - k, hp, F, hF, hFne, hunitp, heq⟩

/-- At each parameter, either a whole neighborhood lies in the exceptional set, or every
nearby point other than the parameter itself is invertible. -/
private theorem fredholm_local_alternative {U : Set ℂ} (hU : IsOpen U)
    {K : ℂ → X →L[ℂ] X} (hK : DifferentiableOn ℂ K U)
    (hc : ∀ z ∈ U, IsCompactOperator (K z)) {a : ℂ} (ha : a ∈ U) :
    (∃ V ∈ 𝓝 a, V ⊆ U ∧ ∀ z ∈ V, ¬ IsUnit (1 - K z)) ∨
      (∃ V ∈ 𝓝 a, V ⊆ U ∧ ∀ z ∈ V, z ≠ a → IsUnit (1 - K z)) := by
  obtain ⟨d, N, hd, _, hfac⟩ := exists_meromorphic_factor hU hK hc ha
  rcases hd.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · left
    have hEv : ∀ᶠ z in 𝓝 a, z ∈ U ∧ ¬ IsUnit (1 - K z) := by
      filter_upwards [hfac, hzero] with z hz hdz
      exact ⟨hz.1, fun hu ↦ hz.2.1.mp hu hdz⟩
    rcases eventually_iff_exists_mem.mp hEv with ⟨V, hV, hVp⟩
    exact ⟨V, hV, fun z hz ↦ (hVp z hz).1, fun z hz ↦ (hVp z hz).2⟩
  · right
    have hne' : ∀ᶠ z in 𝓝 a, z ≠ a → d z ≠ 0 := eventually_nhdsWithin_iff.mp hne
    have hEv : ∀ᶠ z in 𝓝 a, z ∈ U ∧ (z ≠ a → IsUnit (1 - K z)) := by
      filter_upwards [hfac, hne'] with z hz hdne
      exact ⟨hz.1, fun hza ↦ hz.2.1.mpr (hdne hza)⟩
    rcases eventually_iff_exists_mem.mp hEv with ⟨V, hV, hVp⟩
    exact ⟨V, hV, fun z hz ↦ (hVp z hz).1, fun z hz ↦ (hVp z hz).2⟩

/-- **21.15**: unfolded analytic Fredholm theorem. -/
public theorem analyticFredholm_aux {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (K : ℂ → X →L[ℂ] X) (hK : DifferentiableOn ℂ K U)
    (hc : ∀ z ∈ U, IsCompactOperator (K z))
    (hunit : ∃ z ∈ U, IsUnit (1 - K z)) :
    (∀ a ∈ {z ∈ U | ¬ IsUnit (1 - K z)}, ∃ r : ℝ, 0 < r ∧
      ∀ z ∈ {z ∈ U | ¬ IsUnit (1 - K z)}, dist z a < r → z = a) ∧
    DifferentiableOn ℂ (fun z ↦ Ring.inverse (1 - K z))
      (U \ {z ∈ U | ¬ IsUnit (1 - K z)}) ∧
    ∀ a ∈ {z ∈ U | ¬ IsUnit (1 - K z)},
      ∃ m : ℕ, 0 < m ∧ ∃ F : ℂ → X →L[ℂ] X, AnalyticAt ℂ F a ∧ F a ≠ 0 ∧
        (∀ᶠ z in 𝓝[≠] a, IsUnit (1 - K z)) ∧
        ∀ᶠ z in 𝓝[≠] a, (z - a) ^ m • Ring.inverse (1 - K z) = F z := by
  by_cases hsub : Subsingleton (X →L[ℂ] X)
  · have hS : {z ∈ U | ¬ IsUnit (1 - K z)} = ∅ := by
      ext z
      constructor
      · rintro ⟨_, hnu⟩
        exact hnu (isUnit_of_subsingleton _)
      · intro hz
        exact hz.elim
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      rw [hS] at ha
      exact ha.elim
    · rw [hS, Set.sdiff_empty]
      exact ((differentiableOn_const (1 : X →L[ℂ] X)).sub hK).inverse
        fun z _ ↦ isUnit_of_subsingleton _
    · intro a ha
      rw [hS] at ha
      exact ha.elim
  · let S : Set ℂ := {z ∈ U | ¬ IsUnit (1 - K z)}
    let W : Set ℂ := interior S
    have hloc : ∀ a ∈ U,
        (∃ V ∈ 𝓝 a, V ⊆ U ∧ ∀ z ∈ V, ¬ IsUnit (1 - K z)) ∨
          (∃ V ∈ 𝓝 a, V ⊆ U ∧ ∀ z ∈ V, z ≠ a → IsUnit (1 - K z)) :=
      fun a ha ↦ fredholm_local_alternative hU hK hc ha
    have hcov : U ⊆ W ∪ (closure W)ᶜ := by
      intro a ha
      rcases hloc a ha with ⟨V, hV, hVU, hnot⟩ | ⟨V, hV, _, hrest⟩
      · left
        rw [mem_interior_iff_mem_nhds]
        exact mem_of_superset hV fun z hz ↦ ⟨hVU hz, hnot z hz⟩
      · right
        rw [Set.mem_compl_iff]
        intro hcl
        have hsubV : V ∩ W ⊆ {a} := by
          intro z hz
          by_contra hza
          exact (interior_subset hz.2).2 (hrest z hz.1 hza)
        by_cases haW : a ∈ W
        · have hsing : {a} ∈ 𝓝 a :=
            mem_of_superset (inter_mem hV (isOpen_interior.mem_nhds haW)) hsubV
          have : a ∈ interior {a} := mem_interior_iff_mem_nhds.mpr hsing
          simp [interior_singleton a] at this
        · have hempty : V ∩ W = ∅ := by
            ext z
            constructor
            · intro hz
              have hza : z = a := hsubV hz
              exact (haW (by simpa [hza] using hz.2)).elim
            · intro hz
              simp at hz
          exact (mem_closure_iff_nhds.mp hcl V hV).ne_empty hempty
    obtain ⟨z0, hz0U, hz0u⟩ := hunit
    have hz0W : z0 ∉ W := fun hz ↦ (interior_subset hz).2 hz0u
    have hz0C : z0 ∈ (closure W)ᶜ := by
      rcases hcov hz0U with h | h
      · exact (hz0W h).elim
      · exact h
    have hUW : U ∩ W = ∅ := by
      by_contra hne
      obtain ⟨z, -, hzW, hzC⟩ := hconn W (closure W)ᶜ isOpen_interior
        isClosed_closure.isOpen_compl hcov (Set.nonempty_iff_ne_empty.mpr hne)
        ⟨z0, hz0U, hz0C⟩
      exact hzC (subset_closure hzW)
    have hWempty : W = ∅ := by
      apply Set.eq_empty_of_subset_empty
      intro z hz
      have : z ∈ U ∩ W := ⟨(interior_subset hz).1, hz⟩
      simp [hUW] at this
    have hsecond : ∀ a ∈ U, ∃ V ∈ 𝓝 a, V ⊆ U ∧ ∀ z ∈ V, z ≠ a → IsUnit (1 - K z) := by
      intro a ha
      rcases hloc a ha with ⟨V, hV, hVU, hnot⟩ | hok
      · have haW : a ∈ W := by
          rw [mem_interior_iff_mem_nhds]
          exact mem_of_superset hV fun z hz ↦ ⟨hVU hz, hnot z hz⟩
        simp [hWempty] at haW
      · exact hok
    refine ⟨?_, ?_, ?_⟩
    · intro a haS
      obtain ⟨V, hV, _, hrest⟩ := hsecond a haS.1
      obtain ⟨r, hr0, hr⟩ := Metric.mem_nhds_iff.mp hV
      refine ⟨r, hr0, ?_⟩
      intro z hzS hdist
      by_cases hza : z = a
      · exact hza
      · exact (hzS.2 (hrest z (hr (Metric.mem_ball.mpr hdist)) hza)).elim
    · have hdiff : DifferentiableOn ℂ (fun z ↦ 1 - K z) (U \ S) :=
        ((differentiableOn_const _).sub hK).mono Set.sdiff_subset
      exact hdiff.inverse fun z hz ↦ by
        have hnot : ¬ ¬ IsUnit (1 - K z) := fun hnu ↦ hz.2 ⟨hz.1, hnu⟩
        exact not_not.mp hnot
    · intro a haS
      obtain ⟨d, N, hd, hN, hfac⟩ := exists_meromorphic_factor hU hK hc haS.1
      have hd0 : ¬ ∀ᶠ z in 𝓝 a, d z = 0 := by
        intro hzero
        have hEv : ∀ᶠ z in 𝓝 a, z ∈ S := by
          filter_upwards [hfac, hzero] with z hz hdz
          exact ⟨hz.1, fun hu ↦ hz.2.1.mp hu hdz⟩
        have haW : a ∈ W := mem_interior_iff_mem_nhds.mpr (eventually_mem_set.mp hEv)
        simp [hWempty] at haW
      have hcont : ContinuousAt K a :=
        hK.continuousOn.continuousAt (hU.mem_nhds haS.1)
      have hfac' : ∀ᶠ z in 𝓝 a, (IsUnit (1 - K z) ↔ d z ≠ 0) ∧
          (d z ≠ 0 → Ring.inverse (1 - K z) = (d z)⁻¹ • N z) := by
        filter_upwards [hfac] with z hz
        exact ⟨hz.2.1, hz.2.2⟩
      exact pole_of_meromorphic hcont hsub hd hN hfac' haS.2 hd0

end CKMA
