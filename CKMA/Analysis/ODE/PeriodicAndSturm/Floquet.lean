/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import TauCeti.RingTheory.Nilpotent.Log

/-!
# Fundamental operators, Liouville's formula, and Floquet factors

Normalized fundamental operators `U` of a linear system `U' = A U` (`U 0 = 1`), their monodromy
under periodic shifts, invertibility in finite dimension, and Liouville's formula
`det (U t) = exp ∫₀ᵗ tr A` for complex systems. A logarithm of an invertible endomorphism of a
finite-dimensional complex space is built from the generalized eigenspace decomposition and
TauCeti's finite logarithm of a unipotent element (`IsNilpotent.log`). On nilpotent elements the
normed exponential is identified with that finite exponential by the terminating-series argument
of TauCeti's `IsNilpotent.normedSpace_exp_eq_exp`. The Floquet factor `P t = U t exp (-t B)` is
assembled from a logarithm `T B` of the monodromy `U T`.

## Main definitions

* `CKMA.IsFundamentalOperator`: A normalized fundamental operator `U` satisfying `U 0 = 1`
  and `U' t = A t ∘L U t`.

## Main results

* `CKMA.IsFundamentalOperator.add_period_eq_mul`: Shifting a normalized fundamental operator
  by one period `T` multiplies on the right by `U T`.
* `CKMA.IsFundamentalOperator.isInvertible_of_finiteDimensional`: Finite-dimensional fundamental
  operators are invertible at every time, by uniqueness for the linear ODE.
* `CKMA.IsFundamentalOperator.det_eq_exp_integral_trace`: **Liouville's formula**
  `det (U t) = exp ∫₀ᵗ tr A` for a complex fundamental operator.
* `CKMA.exists_normedSpace_exp_eq_of_isInvertible`: An invertible endomorphism of a
  finite-dimensional complex space has a logarithm.
* `CKMA.IsFundamentalOperator.floquet_of_exp_eq`: A Floquet factor built from a logarithm of
  the monodromy.

## References

* [Coddington and Levinson, *Theory of Ordinary Differential Equations*][coddingtonlevinson1955]
-/

public section

noncomputable section

namespace CKMA

open Filter Topology Set intervalIntegral

/-- A normalized fundamental operator for a linear equation. -/
@[expose]
def IsFundamentalOperator {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E]
    (A U : ℝ → E →L[𝕜] E) : Prop :=
  U 0 = 1 ∧ ∀ t, HasDerivAt U ((A t).comp (U t)) t

section FundamentalOperator

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  {A U : ℝ → E →L[𝕜] E}

/-- Unfolding `IsFundamentalOperator`. -/
lemma isFundamentalOperator_iff :
    IsFundamentalOperator A U ↔ U 0 = 1 ∧ ∀ t, HasDerivAt U ((A t).comp (U t)) t :=
  Iff.rfl

/-- A normalized fundamental operator is the identity at time `0`. -/
lemma IsFundamentalOperator.apply_zero (hU : IsFundamentalOperator A U) : U 0 = 1 :=
  hU.1

/-- A fundamental operator solves `U' t = A t ∘L U t`. -/
lemma IsFundamentalOperator.hasDerivAt (hU : IsFundamentalOperator A U) (t : ℝ) :
    HasDerivAt U ((A t).comp (U t)) t :=
  hU.2 t

/-- A fundamental operator is continuous. -/
lemma IsFundamentalOperator.continuous (hU : IsFundamentalOperator A U) : Continuous U :=
  continuous_iff_continuousAt.mpr fun t ↦ (hU.2 t).continuousAt

end FundamentalOperator

/-- Left multiplication by a fixed element of a seminormed ring is Lipschitz with constant
`‖c‖₊`. -/
lemma lipschitzWith_mul_left {R : Type*} [SeminormedRing R] (c : R) :
    LipschitzWith ‖c‖₊ (fun x : R ↦ c * x) :=
  LipschitzWith.of_dist_le_mul fun x y ↦ by
    simpa [dist_eq_norm, mul_sub] using norm_mul_le c (x - y)

/-- Right multiplication by a fixed endomorphism preserves little-o estimates. -/
private lemma isLittleO_mul_right {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {f : ℝ → E →L[𝕜] E} {g : ℝ → ℝ} {l : Filter ℝ} (c : E →L[𝕜] E)
    (h : f =o[l] g) : (fun t ↦ f t * c) =o[l] g := by
  refine (Asymptotics.IsBigO.of_bound ‖c‖ (Eventually.of_forall fun t ↦ ?_)).trans_isLittleO h
  exact (norm_mul_le (f t) c).trans_eq (mul_comm _ _)

/-- Differentiating a curve of endomorphisms on the right by a constant factor. -/
private lemma hasDerivAt_mul_right {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedSpace ℝ E] {U : ℝ → E →L[𝕜] E} {U' c : E →L[𝕜] E} {t : ℝ}
    (hU : HasDerivAt U U' t) : HasDerivAt (fun s ↦ U s * c) (U' * c) t := by
  refine HasDerivAt.of_isLittleO ?_
  have hEq : (fun s ↦ U s * c - U t * c - (s - t) • (U' * c)) =
      fun s ↦ (U s - U t - (s - t) • U') * c := by
    funext s
    ext v
    simp [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, sub_apply, smul_apply]
  rw [hEq]
  exact isLittleO_mul_right c hU.isLittleO

/-- Shifting a normalized fundamental operator by one period multiplies on the right by `U T`. -/
lemma IsFundamentalOperator.add_period_eq_mul {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedSpace ℝ E] {A U : ℝ → E →L[𝕜] E} {T : ℝ} (hA : Continuous A)
    (hperiod : Function.Periodic A T) (hU : IsFundamentalOperator A U) (t : ℝ) :
    U (t + T) = U t * U T := by
  let F : ℝ → E →L[𝕜] E := fun s ↦ U (s + T)
  let G : ℝ → E →L[𝕜] E := fun s ↦ U s * U T
  let a := min t (0 : ℝ) - 1
  let b := max t (0 : ℝ) + 1
  have hab : a < b := by
    dsimp [a, b]
    linarith [show min t (0 : ℝ) ≤ max t (0 : ℝ) from min_le_max]
  have ht0 : (0 : ℝ) ∈ Ioo a b := by
    constructor <;> dsimp [a, b] <;> linarith [min_le_left t (0 : ℝ), min_le_right t (0 : ℝ),
      le_max_left t (0 : ℝ), le_max_right t (0 : ℝ)]
  have htt : t ∈ Icc a b := by
    constructor <;> dsimp [a, b] <;> linarith [min_le_left t (0 : ℝ), le_max_left t (0 : ℝ)]
  obtain ⟨x, -, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (f := fun s : ℝ ↦ ‖A s‖) (⟨a, left_mem_Icc.mpr hab.le⟩ : (Icc a b).Nonempty)
    (continuous_norm.comp hA).continuousOn
  let K : NNReal := ‖A x‖₊
  have hLip : ∀ s ∈ Ioo a b, LipschitzOnWith K (fun Y : E →L[𝕜] E ↦ A s * Y) univ := by
    intro s hs
    have hs' : s ∈ Icc a b := Ioo_subset_Icc_self hs
    have hle : ‖A s‖₊ ≤ K := NNReal.coe_le_coe.mp <| by
      simpa [K] using (isMaxOn_iff.mp hmax) s hs'
    exact ((lipschitzWith_mul_left (A s)).weaken hle).lipschitzOnWith
  have hUc : Continuous U := hU.continuous
  have hF' : ∀ s ∈ Ioo a b, HasDerivAt F (A s * F s) s := by
    intro s _
    have hshift := (hU.2 (s + T)).comp_add_const s T
    simpa [F, hperiod s, ContinuousLinearMap.mul_def] using hshift
  have hG' : ∀ s ∈ Ioo a b, HasDerivAt G (A s * G s) s := by
    intro s _
    have hmul := hasDerivAt_mul_right (c := U T) (hU.2 s)
    have hassoc : ((A s).comp (U s)) * U T = A s * G s := by
      simpa [G, ContinuousLinearMap.mul_def] using
        ContinuousLinearMap.comp_assoc (A s) (U s) (U T)
    exact hmul.congr_deriv hassoc
  have hfg0 : F 0 = G 0 := by
    show U (0 + T) = U 0 * U T
    rw [zero_add, hU.1, one_mul]
  have hEq : EqOn F G (Icc a b) :=
    ODE_solution_unique_of_mem_Icc hLip ht0
      (hUc.comp (continuous_id.add (continuous_const (y := T)))).continuousOn hF'
      (fun _ _ ↦ mem_univ _)
      (hUc.mul (continuous_const (y := U T))).continuousOn hG'
      (fun _ _ ↦ mem_univ _) hfg0
  exact hEq htt

/-- Leibniz formula for the determinant, indexed by rows. -/
private lemma det_eq_sum_perm_row {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    A.det = ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A i (σ i) := by
  rw [← Matrix.det_transpose (M := A), Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  simp [Matrix.transpose_apply]

/-- The derivative of a matrix determinant is the sum of the row-replaced determinants. -/
private lemma hasDerivAt_matrix_det {n : Type*} [Fintype n] [DecidableEq n]
    {M : ℝ → Matrix n n ℂ} {dM : Matrix n n ℂ} {t : ℝ}
    (h : ∀ i j, HasDerivAt (fun s ↦ M s i j) (dM i j) t) :
    HasDerivAt (fun s ↦ (M s).det) (∑ j, ((M t).updateRow j (dM j)).det) t := by
  have hfun : (fun s ↦ (M s).det) =
      fun s ↦ ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M s i (σ i) := by
    ext s
    exact det_eq_sum_perm_row (M s)
  rw [hfun]
  have hterm (σ : Equiv.Perm n) : HasDerivAt
      (fun s ↦ ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M s i (σ i))
      (((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, M t j (σ j)) * dM i (σ i)) t := by
    refine (HasDerivAt.const_mul (((Equiv.Perm.sign σ : ℤ) : ℂ)) ?_).congr_deriv rfl
    simpa [smul_eq_mul] using HasDerivAt.fun_finsetProd (u := Finset.univ)
      (f := fun i s ↦ M s i (σ i)) (f' := fun i ↦ dM i (σ i))
      (fun i _ ↦ h i (σ i))
  refine (HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ ↦ hterm σ)).congr_deriv <| by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [det_eq_sum_perm_row]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    have hprod : (∏ i, (M t).updateRow j (dM j) i (σ i)) =
        (∏ i ∈ Finset.univ.erase j, (M t) i (σ i)) * dM j (σ j) := by
      rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ j)]
      rw [Matrix.updateRow_apply, ite_eq_left rfl]
      refine congrArg (fun z ↦ z * dM j (σ j)) (Finset.prod_congr rfl fun i hi ↦ ?_)
      rw [Matrix.updateRow_apply, ite_eq_right (Finset.mem_erase.mp hi).1]
    rw [hprod]

/-- Differentiating a determinant along `M' = B * M` multiplies it by the trace of `B`. -/
private lemma hasDerivAt_det_left_mul {n : Type*} [Fintype n] [DecidableEq n]
    {M : ℝ → Matrix n n ℂ} {B : Matrix n n ℂ} {t : ℝ}
    (h : ∀ i j, HasDerivAt (fun s ↦ M s i j) ((B * M t) i j) t) :
    HasDerivAt (fun s ↦ (M s).det) (B.trace * (M t).det) t := by
  have hdet := hasDerivAt_matrix_det h
  have hrow (j : n) : ((M t).updateRow j ((B * M t) j)).det = B j j * (M t).det := by
    have hcomb : (B * M t) j = ∑ k, B j k • (M t) k := by
      ext col
      simp [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hcomb]
    simpa [smul_eq_mul] using Matrix.det_updateRow_sum (M t) j (fun k ↦ B j k)
  have hsum : (∑ j, ((M t).updateRow j ((B * M t) j)).det) = B.trace * (M t).det := by
    simp_rw [hrow]
    rw [← Finset.sum_mul]
    simp [Matrix.trace, Matrix.diag_apply]
  simpa [hsum] using hdet

/-- Evaluating a differentiable curve of endomorphisms at a fixed vector. -/
private lemma hasDerivAt_clm_apply_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] {U : ℝ → E →L[ℂ] E} {U' : E →L[ℂ] E} {v : E} {t : ℝ}
    (hU : HasDerivAt U U' t) :
    HasDerivAt (fun s ↦ U s v) (U' v) t := by
  let φ : (E →L[ℂ] E) →L[ℝ] E := (ContinuousLinearMap.apply ℂ E v).restrictScalars ℝ
  have hφ : HasDerivAt (⇑φ ∘ U) (φ U') t := φ.hasFDerivAt.comp_hasDerivAt t hU
  simpa [φ, ContinuousLinearMap.apply_apply, ContinuousLinearMap.coe_restrictScalars',
    Function.comp_def] using hφ

/-- Each coordinate of a differentiable curve in a finite-dimensional space is differentiable. -/
private lemma hasDerivAt_coord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [FiniteDimensional ℂ E] {γ : ℝ → E} {γ' : E} {t : ℝ}
    (hγ : HasDerivAt γ γ' t)
    (b : Module.Basis (Fin (Module.finrank ℂ E)) ℂ E) (i : Fin (Module.finrank ℂ E)) :
    HasDerivAt (fun s ↦ b.coord i (γ s)) (b.coord i γ') t := by
  let ψ : E →L[ℝ] ℂ := ((b.coord i).toContinuousLinearMap).restrictScalars ℝ
  have hψ : HasDerivAt (⇑ψ ∘ γ) (ψ γ') t := ψ.hasFDerivAt.comp_hasDerivAt t hγ
  simpa [ψ, LinearMap.coe_toContinuousLinearMap', ContinuousLinearMap.coe_restrictScalars',
    Function.comp_def] using hψ

/-- Each matrix entry of a fundamental operator has the derivative predicted by the coefficient. -/
private lemma hasDerivAt_fundamental_entry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [FiniteDimensional ℂ E] {A U : ℝ → E →L[ℂ] E} {t : ℝ}
    (hU : HasDerivAt U ((A t).comp (U t)) t)
    (b : Module.Basis (Fin (Module.finrank ℂ E)) ℂ E)
    (i j : Fin (Module.finrank ℂ E)) :
    HasDerivAt (fun s ↦ LinearMap.toMatrix b b (U s).toLinearMap i j)
      ((LinearMap.toMatrix b b (A t).toLinearMap * LinearMap.toMatrix b b (U t).toLinearMap) i j)
      t := by
  have happly := hasDerivAt_clm_apply_const (v := b j) hU
  have hcoord := hasDerivAt_coord happly b i
  have hentry (s : ℝ) : LinearMap.toMatrix b b (U s).toLinearMap i j =
      b.coord i (U s (b j)) := by
    rw [LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe, ← Module.Basis.coord_apply]
  have hderiv : b.coord i (((A t).comp (U t)) (b j)) =
      (LinearMap.toMatrix b b (A t).toLinearMap *
        LinearMap.toMatrix b b (U t).toLinearMap) i j := by
    conv_lhs =>
      rw [Module.Basis.coord_apply, ← ContinuousLinearMap.coe_coe, ← LinearMap.toMatrix_apply]
    have hcomp : ((A t).comp (U t)).toLinearMap =
        (A t).toLinearMap.comp (U t).toLinearMap :=
      (ContinuousLinearMap.toLinearMap_mul (A t) (U t)).symm
    rw [hcomp, LinearMap.toMatrix_comp b b b]
  have hfun : (fun s ↦ LinearMap.toMatrix b b (U s).toLinearMap i j) =
      fun s ↦ b.coord i (U s (b j)) := by
    ext s
    exact hentry s
  rw [hfun]
  exact hcoord.congr_deriv hderiv

/-- Each matrix entry of a continuous curve of endomorphisms is continuous. -/
private lemma continuous_toMatrix_entry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {A : ℝ → E →L[ℂ] E} (hA : Continuous A)
    (b : Module.Basis (Fin (Module.finrank ℂ E)) ℂ E) (i j : Fin (Module.finrank ℂ E)) :
    Continuous (fun s ↦ LinearMap.toMatrix b b (A s).toLinearMap i j) := by
  have hcoord : Continuous (fun s ↦ b.coord i (A s (b j))) := by
    let ψ : E →L[ℝ] ℂ := ((b.coord i).toContinuousLinearMap).restrictScalars ℝ
    let φ : (E →L[ℂ] E) →L[ℝ] E := (ContinuousLinearMap.apply ℂ E (b j)).restrictScalars ℝ
    exact ψ.continuous.comp (φ.continuous.comp hA)
  refine hcoord.congr fun s ↦ ?_
  rw [LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe, ← Module.Basis.coord_apply]

/-- **Liouville's formula**: the determinant of a complex fundamental operator is the exponential
of the integral of the trace of the coefficient, `det (U t) = exp ∫₀ᵗ tr A`. -/
theorem IsFundamentalOperator.det_eq_exp_integral_trace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedSpace ℝ E] [FiniteDimensional ℂ E] {A U : ℝ → E →L[ℂ] E}
    (hA : Continuous A) (hU : IsFundamentalOperator A U) (t : ℝ) :
    (U t).det = Complex.exp (∫ s in (0 : ℝ)..t, LinearMap.trace ℂ E (A s).toLinearMap) := by
  let b := Module.finBasis ℂ E
  let M : ℝ → Matrix (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ E)) ℂ :=
    fun s ↦ LinearMap.toMatrix b b (U s).toLinearMap
  let trA : ℝ → ℂ := fun s ↦ (LinearMap.toMatrix b b (A s).toLinearMap).trace
  have htrA : (fun s ↦ LinearMap.trace ℂ E (A s).toLinearMap) = trA := by
    funext s
    exact LinearMap.trace_eq_matrix_trace ℂ b _
  have htr : Continuous trA := by
    have hsum : trA = fun s ↦ ∑ i, LinearMap.toMatrix b b (A s).toLinearMap i i := by
      ext s
      simp [trA, Matrix.trace, Matrix.diag_apply]
    rw [hsum]
    exact continuous_finsetSum _ fun i _ ↦ continuous_toMatrix_entry hA b i i
  have hdet (s : ℝ) : HasDerivAt (fun u ↦ (M u).det) (trA s * (M s).det) s :=
    hasDerivAt_det_left_mul fun i j ↦ hasDerivAt_fundamental_entry (hU.2 s) b i j
  let I : ℝ → ℂ := fun u ↦ ∫ s in (0 : ℝ)..u, trA s
  have hI (s : ℝ) : HasDerivAt I (trA s) s :=
    intervalIntegral.integral_hasDerivAt_right (htr.intervalIntegrable 0 s)
      (htr.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 s)) htr.continuousAt
  let F : ℝ → ℂ := fun s ↦ (M s).det * Complex.exp (-I s)
  have hF (s : ℝ) : HasDerivAt F 0 s :=
    ((hdet s).mul (hI s).neg.cexp).congr_deriv (by ring)
  obtain ⟨c, hc⟩ := isOpen_univ.exists_is_const_of_deriv_eq_zero isPreconnected_univ
    (fun s _ ↦ (hF s).differentiableAt.differentiableWithinAt) (fun s _ ↦ (hF s).deriv)
  have hc0 : c = 1 := by
    have hM0 : M 0 = 1 := by simp [M, hU.1, LinearMap.toMatrix_one]
    simpa [F, hM0, I] using (hc 0 (mem_univ 0)).symm
  have hmul : (M t).det * Complex.exp (-I t) = 1 := (hc t (mem_univ t)).trans hc0
  have hdetU : (U t).det = (M t).det := by simp [M, ContinuousLinearMap.det]
  have hexp : Complex.exp (-I t) * Complex.exp (I t) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  rw [hdetU, htrA]
  calc (M t).det = (M t).det * Complex.exp (-I t) * Complex.exp (I t) := by
        rw [mul_assoc, hexp, mul_one]
    _ = Complex.exp (I t) := by rw [hmul, one_mul]

/-- The determinant of a complex fundamental operator never vanishes. -/
lemma IsFundamentalOperator.det_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [FiniteDimensional ℂ E] {A U : ℝ → E →L[ℂ] E} (hA : Continuous A)
    (hU : IsFundamentalOperator A U) (t : ℝ) : (U t).det ≠ 0 := by
  rw [hU.det_eq_exp_integral_trace hA t]
  exact Complex.exp_ne_zero _

open NormedSpace ContinuousLinearMap

local notation:10000 n "!" => Nat.factorial n

section ComplexLog

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- On a nilpotent element the normed exponential agrees with TauCeti's finite exponential.
The argument is that of `IsNilpotent.normedSpace_exp_eq_exp`. -/
private lemma normedSpace_exp_eq_isNilpotent_exp {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]
    {a : A} (ha : IsNilpotent a) : exp a = IsNilpotent.exp a := by
  obtain ⟨n, hn⟩ := ha
  rw [exp_eq_tsum_rat, IsNilpotent.exp_eq_sum hn]
  exact tsum_eq_sum fun i hi ↦ by rw [pow_eq_zero_of_le (by simpa using hi) hn, smul_zero]

/-- Rational algebra structure on endomorphisms of one generalized eigenspace. -/
private instance instAlgebraRatMaxGenEigenspace (φ : Module.End ℂ E) (μ : ℂ) :
    Algebra ℚ (Module.End ℂ (Module.End.maxGenEigenspace φ μ)) :=
  Algebra.restrictScalars ℚ ℂ _

/-- Rational normed algebra on continuous endomorphisms of one generalized eigenspace. -/
private instance instNormedAlgebraRatMaxGenEigenspace (φ : Module.End ℂ E) (μ : ℂ) :
    NormedAlgebra ℚ ((Module.End.maxGenEigenspace φ μ) →L[ℂ]
      Module.End.maxGenEigenspace φ μ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

omit [FiniteDimensional ℂ E] in
/-- An invertible endomorphism has trivial generalized eigenspace at eigenvalue `0`. -/
private lemma maxGenEigenspace_eq_bot_of_isInvertible {f : E →L[ℂ] E} (hf : f.IsInvertible) :
    Module.End.maxGenEigenspace f.toLinearMap 0 = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [Module.End.mem_maxGenEigenspace] at hv
  obtain ⟨k, hk⟩ := hv
  have hk0 : (f ^ k) v = 0 := by
    rw [← coe_coe, toLinearMap_pow]
    simpa [zero_smul, sub_zero] using hk
  have hmul : ∀ n, (f.inverse ^ n) * (f ^ n) = 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', pow_succ, mul_assoc, ← mul_assoc (f.inverse ^ n) (f ^ n) f, ih, one_mul,
        mul_def, hf.inverse_comp_self, ← one_def]
  have happly : ((f.inverse ^ k) * (f ^ k)) v = v := by
    rw [hmul k, one_apply_eq_self]
  rw [mul_apply_eq_comp, hk0, map_zero] at happly
  exact happly.symm

/-- Logarithm of `φ` on its maximal generalized `μ`-eigenspace, branch `Complex.log`. -/
private noncomputable def genEigenspaceLog (φ : Module.End ℂ E) (μ : ℂ) :
    Module.End ℂ (Module.End.maxGenEigenspace φ μ) :=
  if _hμ : μ = 0 then 0 else
    let N0 := (φ - algebraMap ℂ (Module.End ℂ E) μ).restrict
      (Module.End.mapsTo_maxGenEigenspace_of_comm
        (Algebra.mul_sub_algebraMap_commutes φ μ) μ)
    algebraMap ℂ (Module.End ℂ (Module.End.maxGenEigenspace φ μ)) (Complex.log μ) +
      IsNilpotent.log (1 + μ⁻¹ • N0)

/-- On a nonzero eigenvalue, the block logarithm exponentiates to the restriction of `φ`. -/
private lemma exp_toContinuousLinearMap_genEigenspaceLog (φ : Module.End ℂ E) {μ : ℂ}
    (hμ : μ ≠ 0) :
    exp (Module.End.toContinuousLinearMap (𝕜 := ℂ) (Module.End.maxGenEigenspace φ μ)
        (genEigenspaceLog φ μ)) =
      Module.End.toContinuousLinearMap (𝕜 := ℂ) (Module.End.maxGenEigenspace φ μ)
        (φ.restrict (Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl φ) μ)) := by
  have : IsNoetherian ℂ E := IsNoetherian.iff_fg.mpr inferInstance
  let V := Module.End.maxGenEigenspace φ μ
  have : CompleteSpace V := FiniteDimensional.completeSpace ℂ V
  have : FiniteDimensional ℂ (V →L[ℂ] V) := ContinuousLinearMap.finiteDimensional
  have : CompleteSpace (V →L[ℂ] V) := FiniteDimensional.completeSpace ℂ (V →L[ℂ] V)
  let N0 := (φ - algebraMap ℂ (Module.End ℂ E) μ).restrict
    (Module.End.mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes φ μ) μ)
  have hN0 : IsNilpotent N0 :=
    Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap φ μ
  let u : Module.End ℂ V := 1 + μ⁻¹ • N0
  have hu1 : u - 1 = μ⁻¹ • N0 := by simp [u]
  have hu : IsNilpotent (u - 1) := by rw [hu1]; exact hN0.smul μ⁻¹
  let logu : Module.End ℂ V := IsNilpotent.log u
  have hlogu : IsNilpotent logu := IsNilpotent.isNilpotent_log hu
  let s : Module.End ℂ V := algebraMap ℂ (Module.End ℂ V) (Complex.log μ)
  let ψ := Module.End.toContinuousLinearMap (𝕜 := ℂ) V
  have hφ : MapsTo φ ↑V ↑V :=
    Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl φ) μ
  have hscale : μ • u = algebraMap ℂ (Module.End ℂ V) μ + N0 := by
    dsimp only [u]
    rw [smul_add, smul_smul, mul_inv_cancel₀ hμ, one_smul, ← Algebra.algebraMap_eq_smul_one]
  have hrest : φ.restrict hφ = algebraMap ℂ (Module.End ℂ V) μ + N0 := by
    ext x
    dsimp only [N0]
    erw [LinearMap.coe_restrict_apply, LinearMap.add_apply, Submodule.coe_add,
      Module.algebraMap_end_apply, LinearMap.coe_restrict_apply, LinearMap.sub_apply,
      Module.algebraMap_end_apply]
    rw [Submodule.coe_smul, add_comm, sub_add_cancel]
  have hbody : genEigenspaceLog φ μ = s + logu := by
    unfold genEigenspaceLog
    rw [dite_eq_right hμ]
  have hcomm : Commute (ψ s) (ψ logu) := by
    dsimp only [s]
    rw [ψ.commutes (Complex.log μ)]
    exact Algebra.commutes (Complex.log μ) (ψ logu)
  have hexps : exp (ψ s) = algebraMap ℂ (V →L[ℂ] V) μ := by
    rw [ψ.commutes (Complex.log μ), ← algebraMap_exp_comm (𝕂 := ℂ) (Complex.log μ),
      ← Complex.exp_eq_exp_ℂ, Complex.exp_log hμ]
  have hexplog : exp (ψ logu) = ψ u := by
    rw [normedSpace_exp_eq_isNilpotent_exp (hlogu.map ψ), ← IsNilpotent.map_exp hlogu ψ,
      IsNilpotent.exp_log hu]
  have hsum : ψ (s + logu) = ψ s + ψ logu := by
    rw [map_add]
  rw [hbody, hsum, exp_add_of_commute hcomm, hexps, hexplog, ← Algebra.smul_def, ← map_smul,
    hscale, hrest]

/-- An invertible endomorphism of a finite-dimensional complex space has a logarithm. -/
lemma exists_normedSpace_exp_eq_of_isInvertible {f : E →L[ℂ] E} (hf : f.IsInvertible) :
    ∃ L : E →L[ℂ] E, exp L = f := by
  let _ : DecidableEq ℂ := fun a b ↦ Classical.propDecidable (a = b)
  have : IsNoetherian ℂ E := IsNoetherian.iff_fg.mpr inferInstance
  have : CompleteSpace E := FiniteDimensional.completeSpace ℂ E
  have : FiniteDimensional ℂ (E →L[ℂ] E) := ContinuousLinearMap.finiteDimensional
  have : CompleteSpace (E →L[ℂ] E) := FiniteDimensional.completeSpace ℂ (E →L[ℂ] E)
  let φ := f.toLinearMap
  have hbot : Module.End.maxGenEigenspace φ 0 = ⊥ := maxGenEigenspace_eq_bot_of_isInvertible hf
  let p : ℂ → Submodule ℂ E := Module.End.maxGenEigenspace φ
  let e := (Module.End.independent_maxGenEigenspace φ).linearEquiv
    (Module.End.iSup_maxGenEigenspace_eq_top φ)
  let Ldf := DFinsupp.mapRange.linearMap (fun μ ↦ genEigenspaceLog φ μ)
  let Llin : Module.End ℂ E := e.toLinearMap.comp (Ldf.comp e.symm.toLinearMap)
  let L := LinearMap.toContinuousLinearMap Llin
  have hact (μ : ℂ) (w : p μ) : L (w : E) = (genEigenspaceLog φ μ w : E) := by
    have hs : e.symm (w : E) = DFinsupp.single μ ⟨(w : E), w.2⟩ :=
      iSupIndep.linearEquiv_symm_apply (Module.End.independent_maxGenEigenspace φ)
        (Module.End.iSup_maxGenEigenspace_eq_top φ) w.2
    dsimp only [L, Llin]
    rw [LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply, LinearMap.comp_apply]
    rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe e.symm]
    rw [hs, DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single, Subtype.eta]
    dsimp only [e, iSupIndep.linearEquiv]
    erw [LinearEquiv.ofBijective_apply, DFinsupp.lsum_single, Submodule.subtype_apply]
  refine ⟨L, ?_⟩
  have hker : LinearMap.ker ((exp L - f).toLinearMap) = ⊤ := by
    rw [eq_top_iff, ← Module.End.iSup_maxGenEigenspace_eq_top φ]
    refine iSup_le fun μ ↦ ?_
    intro v hv
    rw [LinearMap.mem_ker, toLinearMap_sub, LinearMap.sub_apply, sub_eq_zero, coe_coe, coe_coe]
    by_cases hμ : μ = 0
    · have hv0 : v = 0 := by
        rw [hμ, hbot] at hv
        exact (Submodule.mem_bot ℂ).mp hv
      simp [hv0]
    · let w : p μ := ⟨v, hv⟩
      have : CompleteSpace (p μ) := FiniteDimensional.completeSpace ℂ (p μ)
      have : FiniteDimensional ℂ ((p μ) →L[ℂ] p μ) := ContinuousLinearMap.finiteDimensional
      have : CompleteSpace ((p μ) →L[ℂ] p μ) := FiniteDimensional.completeSpace ℂ _
      let blockC :=
        Module.End.toContinuousLinearMap (𝕜 := ℂ) (p μ) (genEigenspaceLog φ μ)
      have hpow : ∀ n, (L ^ n) v = ((blockC ^ n) w : E) := by
        intro n
        induction n with
        | zero => simp [w]
        | succ n ih =>
          rw [pow_succ', mul_apply_eq_comp, ih]
          have hstep := hact μ ((blockC ^ n) w)
          rw [hstep]
          rw [pow_succ', mul_apply_eq_comp]
          rfl
      have hsumL : HasSum (fun n ↦ (n !⁻¹ : ℂ) • (L ^ n) v) (exp L v) := by
        simpa [apply_apply, smul_apply] using
          (exp_series_hasSum_exp' (𝕂 := ℂ) L).mapL (apply ℂ E v)
      have hsumB : HasSum (fun n ↦ (n !⁻¹ : ℂ) • ((blockC ^ n) w : E))
          ((exp blockC w : E)) := by
        have hs := (exp_series_hasSum_exp' (𝕂 := ℂ) blockC).mapL (apply ℂ (p μ) w)
        have hsE := hs.mapL (p μ).subtype.toContinuousLinearMap
        simpa [apply_apply, smul_apply, Submodule.coe_smul, LinearMap.coe_toContinuousLinearMap',
          Submodule.subtype_apply] using hsE
      have hsumL' : HasSum (fun n ↦ (n !⁻¹ : ℂ) • ((blockC ^ n) w : E)) (exp L v) := by
        simpa [hpow] using hsumL
      have hcoe := hsumL'.unique hsumB
      rw [hcoe, exp_toContinuousLinearMap_genEigenspaceLog φ hμ]
      rfl
  ext v
  have hvker : v ∈ LinearMap.ker ((exp L - f).toLinearMap) := by
    rw [hker]
    trivial
  rw [LinearMap.mem_ker, toLinearMap_sub, LinearMap.sub_apply, sub_eq_zero, coe_coe, coe_coe]
    at hvker
  exact hvker

end ComplexLog

/-- A fundamental operator on a finite-dimensional space is invertible at every time. -/
lemma IsFundamentalOperator.isInvertible_of_finiteDimensional {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [FiniteDimensional 𝕜 E]
    {A U : ℝ → E →L[𝕜] E} (hA : Continuous A) (hU : IsFundamentalOperator A U) (t₀ : ℝ) :
    (U t₀).IsInvertible := by
  have hker : ∀ v, U t₀ v = 0 → v = 0 := by
    intro v hv
    let f : ℝ → E := fun s ↦ U s v
    let g : ℝ → E := fun _ ↦ 0
    let a := min t₀ (0 : ℝ) - 1
    let b := max t₀ (0 : ℝ) + 1
    have hab : a < b := by
      dsimp [a, b]
      linarith [min_le_max (a := t₀) (b := (0 : ℝ))]
    have ht0 : (0 : ℝ) ∈ Ioo a b := by
      constructor <;> dsimp [a, b] <;> linarith [min_le_left t₀ (0 : ℝ), min_le_right t₀ (0 : ℝ),
        le_max_left t₀ (0 : ℝ), le_max_right t₀ (0 : ℝ)]
    have htt : t₀ ∈ Ioo a b := by
      constructor <;> dsimp [a, b] <;> linarith [min_le_left t₀ (0 : ℝ), min_le_right t₀ (0 : ℝ),
        le_max_left t₀ (0 : ℝ), le_max_right t₀ (0 : ℝ)]
    have h0mem : (0 : ℝ) ∈ Icc a b := Ioo_subset_Icc_self ht0
    obtain ⟨x, -, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (f := fun s : ℝ ↦ ‖A s‖) (⟨a, left_mem_Icc.mpr hab.le⟩ : (Icc a b).Nonempty)
      (continuous_norm.comp hA).continuousOn
    let K : NNReal := ‖A x‖₊
    have hLip : ∀ s ∈ Ioo a b, LipschitzOnWith K (fun y : E ↦ A s y) univ := by
      intro s hs
      have hle : ‖A s‖₊ ≤ K := NNReal.coe_le_coe.mp <| by
        simpa [K] using (isMaxOn_iff.mp hmax) s (Ioo_subset_Icc_self hs)
      exact ((A s).lipschitzWith.weaken hle).lipschitzOnWith
    have hUc : Continuous U := hU.continuous
    have hfcont : Continuous f := by
      let φa : (E →L[𝕜] E) →L[ℝ] E := (apply 𝕜 E v).restrictScalars ℝ
      simpa [f, φa, Function.comp_def, apply_apply, coe_restrictScalars'] using
        φa.continuous.comp hUc
    have hf' : ∀ s ∈ Ioo a b, HasDerivAt f (A s (f s)) s := by
      intro s _
      let φa : (E →L[𝕜] E) →L[ℝ] E := (apply 𝕜 E v).restrictScalars ℝ
      have hd : HasDerivAt (⇑φa ∘ U) (φa ((A s).comp (U s))) s :=
        φa.hasFDerivAt.comp_hasDerivAt s (hU.2 s)
      simpa [f, φa, Function.comp_def, apply_apply, coe_restrictScalars', mul_def,
        comp_apply] using hd
    have hg' : ∀ s ∈ Ioo a b, HasDerivAt g (A s (g s)) s := by
      intro s _
      exact (hasDerivAt_const s (0 : E)).congr_deriv (by simp [g])
    have hEq := ODE_solution_unique_of_mem_Icc hLip htt hfcont.continuousOn hf'
      (fun _ _ ↦ mem_univ _) continuous_const.continuousOn hg' (fun _ _ ↦ mem_univ _)
      (by simpa [f, g] using hv)
    simpa [f, g, hU.1, one_apply_eq_self] using hEq h0mem
  have hinj : Function.Injective (U t₀).toLinearMap := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hker (x - y)
    rw [← coe_coe, map_sub, hxy, sub_self]
  let e := LinearEquiv.ofInjectiveEndo (U t₀).toLinearMap hinj
  have he : (e.toContinuousLinearEquiv : E →L[𝕜] E) = U t₀ := by
    ext v
    rw [ContinuousLinearEquiv.coe_coe, LinearEquiv.coe_toContinuousLinearEquiv',
      LinearEquiv.coe_ofInjectiveEndo, coe_coe]
  rw [← he]
  exact isInvertible_equiv

/-- The curve `t ↦ exp (-(t • B))` of invertible operators. -/
private lemma isInvertible_exp_neg_smul {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace E] (B : E →L[𝕜] E) (z : 𝕜) :
    (exp (-(z • B))).IsInvertible := by
  let +nondep : NormedAlgebra ℚ (E →L[𝕜] E) := .restrictScalars ℚ 𝕜 _
  refine IsInvertible.of_inverse (g := exp (z • B)) ?_ ?_
  · rw [← mul_def, ← exp_add_of_commute ((Commute.refl (z • B)).neg_left), neg_add_cancel,
      exp_zero, one_def]
  · rw [← mul_def, ← exp_add_of_commute ((Commute.refl (z • B)).neg_right), add_neg_cancel,
      exp_zero, one_def]

/-- The derivative of `t ↦ exp (t • B)` along real time. -/
private lemma hasDerivAt_exp_ofReal_smul {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    (B : E →L[𝕜] E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ exp ((s : 𝕜) • B)) (exp ((t : 𝕜) • B) * B) t := by
  have hg : HasDerivAt (fun z : 𝕜 ↦ exp (z • B)) (exp ((t : 𝕜) • B) * B) (t : 𝕜) :=
    hasDerivAt_exp_smul_const B (t : 𝕜)
  have hh : HasDerivAt (fun s : ℝ ↦ (s : 𝕜)) (1 : 𝕜) t := by
    simpa [RCLike.ofRealCLM_apply] using (RCLike.ofRealCLM (K := 𝕜)).hasDerivAt (x := t)
  simpa [Function.comp_def, one_smul] using hg.scomp t hh

/-- Floquet factor built from a logarithm `L` of the monodromy `U T`: with `B = T⁻¹ L`, the
operators `P t = U t * exp (-(t • B))` are `T`-periodic, `C¹` and invertible, and
`U t = P t * exp (t • B)`. -/
lemma IsFundamentalOperator.floquet_of_exp_eq {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [FiniteDimensional 𝕜 E]
    {A U : ℝ → E →L[𝕜] E} {T : ℝ}
    (hU : IsFundamentalOperator A U) (hA : Continuous A) (hperiod : Function.Periodic A T)
    (hT : T ≠ 0) {L : E →L[𝕜] E} (hL : exp L = U T) :
    ∃ B : E →L[𝕜] E, ∃ P : ℝ → E →L[𝕜] E, Function.Periodic P T ∧ ContDiff ℝ 1 P ∧
      (∀ t, (P t).IsInvertible) ∧ ∀ t, U t = P t * exp ((t : 𝕜) • B) := by
  let +nondep : NormedAlgebra ℚ (E →L[𝕜] E) := .restrictScalars ℚ 𝕜 _
  have : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E
  let B : E →L[𝕜] E := (T : 𝕜)⁻¹ • L
  have hTB : (T : 𝕜) • B = L := by
    dsimp only [B]
    rw [smul_smul, mul_inv_cancel₀ (RCLike.ofReal_ne_zero.mpr hT), one_smul]
  have hcomm (a b : 𝕜) : Commute (a • B) (b • B) :=
    ((Commute.refl B).smul_left a).smul_right b
  let Q : ℝ → E →L[𝕜] E := fun t ↦ exp (-((t : 𝕜) • B))
  let P : ℝ → E →L[𝕜] E := fun t ↦ U t * Q t
  have hQshift (t : ℝ) : Q (t + T) = Q t * exp (-L) := by
    have harg : -(((t + T : ℝ) : 𝕜) • B) = -((t : 𝕜) • B) + -L := by
      rw [RCLike.ofReal_add, add_smul, hTB, neg_add]
    have hc : Commute (-((t : 𝕜) • B)) (-L) := by
      rw [← hTB]
      exact (hcomm (t : 𝕜) (T : 𝕜)).neg_left.neg_right
    dsimp only [Q]
    rw [harg, exp_add_of_commute hc]
  have hslide (t : ℝ) : exp L * Q t = Q t * exp L := by
    have hc : Commute L (-((t : 𝕜) • B)) := by
      rw [← hTB]
      exact (hcomm (T : 𝕜) (t : 𝕜)).neg_right
    simpa [Q] using hc.exp.eq
  have hcancel : exp L * exp (-L) = (1 : E →L[𝕜] E) := by
    rw [← exp_add_of_commute (Commute.refl L).neg_right, add_neg_cancel, exp_zero]
  have hPper : Function.Periodic P T := by
    intro t
    calc
      P (t + T) = U t * ((exp L * Q t) * exp (-L)) := by
        simp only [P]
        rw [hU.add_period_eq_mul hA hperiod t, hQshift, ← hL]
        simp only [mul_assoc]
      _ = P t := by
        simp only [P]
        rw [hslide, mul_assoc, hcancel, mul_one]
  have hUcont : Continuous U := hU.continuous
  have hQfun : Q = fun t : ℝ ↦ exp ((t : 𝕜) • -B) := by
    funext t
    dsimp only [Q]
    rw [smul_neg]
  have hQ' (t : ℝ) : HasDerivAt Q (Q t * -B) t := by
    rw [hQfun]
    exact hasDerivAt_exp_ofReal_smul (-B) t
  have hQcont : Continuous Q := continuous_iff_continuousAt.mpr fun t ↦ (hQ' t).continuousAt
  have hP' (t : ℝ) : HasDerivAt P ((A t * U t) * Q t + U t * (Q t * -B)) t := by
    let _ : NormedAlgebra ℝ (E →L[𝕜] E) := ⟨norm_smul_le⟩
    exact HasDerivAt.mul (𝔸 := E →L[𝕜] E) (by simpa [mul_def] using hU.2 t) (hQ' t)
  have hC1 : ContDiff ℝ 1 P := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun t ↦ (hP' t).differentiableAt, ?_⟩
    rw [show deriv P = _ from funext fun t ↦ (hP' t).deriv]
    exact ((hA.mul hUcont).mul hQcont).add (hUcont.mul (hQcont.mul continuous_const))
  refine ⟨B, P, hPper, hC1, fun t ↦ ?_, fun t ↦ ?_⟩
  · dsimp only [P]
    rw [mul_def]
    exact (hU.isInvertible_of_finiteDimensional hA t).comp (isInvertible_exp_neg_smul B _)
  · have hmul : exp (-((t : 𝕜) • B)) * exp ((t : 𝕜) • B) = 1 := by
      rw [← exp_add_of_commute ((Commute.refl ((t : 𝕜) • B)).neg_left), neg_add_cancel, exp_zero]
    dsimp only [P, Q]
    rw [mul_assoc, hmul, mul_one]

end CKMA
