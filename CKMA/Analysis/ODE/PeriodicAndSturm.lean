/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.JordanChevalley
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Floquet decompositions and Sturm zero theorems

Normalized fundamental operators of periodic finite-dimensional linear systems,
complex Floquet factorization and real factorization with possible period doubling.
Sturm–Liouville solutions use a positive leading coefficient; separation is certified
by a nonzero Wronskian, and comparison additionally uses a positive weight.
Operator exponentials and differentiability use Mathlib's normed-space calculus.
Sources: GAPS 31.17 and 31.20.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology Set intervalIntegral

/-- A normalized fundamental operator for a linear equation. -/
def IsFundamentalOperator {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E]
    (A U : ℝ → E →L[𝕜] E) : Prop :=
  U 0 = 1 ∧ ∀ t, HasDerivAt U ((A t).comp (U t)) t

/-- Left multiplication by a fixed continuous endomorphism is Lipschitz. -/
private lemma lipschitzWith_mul_left {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (c : E →L[𝕜] E) :
    LipschitzWith ‖c‖₊ (fun Y : E →L[𝕜] E ↦ c * Y) := by
  refine LipschitzWith.of_dist_le_mul fun Y₁ Y₂ ↦ ?_
  rw [dist_eq_norm, dist_eq_norm, ← mul_sub]
  simpa using norm_mul_le c (Y₁ - Y₂)

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
private lemma fundamental_monodromy {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
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
  have hUc : Continuous U :=
    continuous_iff_continuousAt.mpr fun s ↦ (hU.2 s).continuousAt
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

/-- The `i`-th coordinate of a vector, read in a fixed basis. -/
private lemma basis_coord_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (b : Module.Basis (Fin (Module.finrank ℂ E)) ℂ E)
    (i : Fin (Module.finrank ℂ E)) (x : E) : b.coord i x = b.repr x i := by
  unfold Module.Basis.coord
  rw [LinearMap.comp_apply, Finsupp.lapply_apply, LinearEquiv.coe_coe]

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
    rw [LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe, ← basis_coord_apply]
  have hderiv : b.coord i (((A t).comp (U t)) (b j)) =
      (LinearMap.toMatrix b b (A t).toLinearMap *
        LinearMap.toMatrix b b (U t).toLinearMap) i j := by
    conv_lhs => rw [basis_coord_apply, ← ContinuousLinearMap.coe_coe, ← LinearMap.toMatrix_apply]
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
  rw [LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe, ← basis_coord_apply]

/-- A finite sum of continuous complex functions of a real variable is continuous. -/
private lemma continuous_finset_sum' {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℂ}
    (hf : ∀ i ∈ s, Continuous (f i)) : Continuous (fun t ↦ ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simpa using continuous_const
  | insert a s ha ih =>
    rw [show (fun t ↦ ∑ i ∈ insert a s, f i t) =
        (fun t ↦ f a t + ∑ i ∈ s, f i t) by ext t; rw [Finset.sum_insert ha]]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- The determinant of a complex fundamental operator never vanishes. -/
private lemma fundamental_det_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [FiniteDimensional ℂ E] {A U : ℝ → E →L[ℂ] E} (hA : Continuous A)
    (hU : IsFundamentalOperator A U) (t : ℝ) : (U t).det ≠ 0 := by
  let b := Module.finBasis ℂ E
  let M : ℝ → Matrix (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ E)) ℂ :=
    fun s ↦ LinearMap.toMatrix b b (U s).toLinearMap
  let trA : ℝ → ℂ := fun s ↦ (LinearMap.toMatrix b b (A s).toLinearMap).trace
  have hentry (i : Fin (Module.finrank ℂ E)) :
      Continuous (fun s ↦ LinearMap.toMatrix b b (A s).toLinearMap i i) :=
    continuous_toMatrix_entry hA b i i
  have htr : Continuous trA := by
    have hsum : trA = fun s ↦ ∑ i, LinearMap.toMatrix b b (A s).toLinearMap i i := by
      ext s
      simp [trA, Matrix.trace, Matrix.diag_apply]
    rw [hsum]
    exact continuous_finset_sum' fun i _ ↦ hentry i
  have hdet (s : ℝ) : HasDerivAt (fun u ↦ (M u).det)
      ((LinearMap.toMatrix b b (A s).toLinearMap).trace * (M s).det) s :=
    hasDerivAt_det_left_mul fun i j ↦ hasDerivAt_fundamental_entry (hU.2 s) b i j
  let I : ℝ → ℂ := fun u ↦ ∫ s in (0 : ℝ)..u, trA s
  have hI (s : ℝ) : HasDerivAt I (trA s) s :=
    intervalIntegral.integral_hasDerivAt_right (a := 0) (b := s)
      (htr.intervalIntegrable 0 s)
      (htr.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 s)) htr.continuousAt
  let F : ℝ → ℂ := fun s ↦ (M s).det * Complex.exp (-I s)
  have hF (s : ℝ) : HasDerivAt F 0 s := by
    have hexp : HasDerivAt (fun u ↦ Complex.exp (-I u)) (Complex.exp (-I s) * -trA s) s :=
      (hI s).neg.cexp
    have hmul := (hdet s).mul hexp
    exact hmul.congr_deriv (by ring)
  have hconst := isOpen_univ.exists_is_const_of_deriv_eq_zero isPreconnected_univ
    (fun s _ ↦ (hF s).differentiableAt.differentiableWithinAt)
    (fun s _ ↦ (hF s).deriv)
  obtain ⟨c, hc⟩ := hconst
  have hc0 : c = 1 := by
    have hM0 : M 0 = 1 := by simp [M, hU.1, LinearMap.toMatrix_one]
    have hI0 : I 0 = 0 := by simp [I]
    simpa [F, hM0, hI0, Matrix.det_one, Complex.exp_zero] using (hc 0 (mem_univ 0)).symm
  have hFt : F t = 1 := (hc t (mem_univ t)).trans hc0
  have hmul : (M t).det * Complex.exp (-I t) = 1 := by simpa [F] using hFt
  have hdetM : (M t).det ≠ 0 := by
    intro hzero
    have hfalse : (0 : ℂ) = 1 := by simp [hzero] at hmul
    exact zero_ne_one hfalse
  have hdetU : (U t).det = (M t).det := by
    simp [M, ContinuousLinearMap.det]
  exact hdetU ▸ hdetM

/-- A complex fundamental operator is invertible at every time. -/
private lemma fundamental_isInvertible {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [FiniteDimensional ℂ E] {A U : ℝ → E →L[ℂ] E} (hA : Continuous A)
    (hU : IsFundamentalOperator A U) (t : ℝ) : (U t).IsInvertible := by
  have hdet := fundamental_det_ne_zero hA hU t
  have hequiv := ContinuousLinearMap.isInvertible_equiv
    (f := (U t).toContinuousLinearEquivOfDetNeZero hdet)
  simpa [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using hequiv


/-- **31.17**: complex Floquet factorization of a periodic linear system. -/
theorem floquet_complex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (A U : ℝ → E →L[ℂ] E) {T : ℝ} (hT : 0 < T)
    (hA : Continuous A) (hperiod : Function.Periodic A T) (hU : IsFundamentalOperator A U) :
    ∃ (B : E →L[ℂ] E) (P : ℝ → E →L[ℂ] E), Function.Periodic P T ∧
      ContDiff ℝ 1 P ∧ (∀ t, (P t).IsInvertible) ∧
      ∀ t, U t = P t * NormedSpace.exp ((t : ℂ) • B) := by
  sorry

/-- A real Floquet decomposition may require period `2T`. -/
theorem floquet_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (A U : ℝ → E →L[ℝ] E) {T : ℝ} (hT : 0 < T)
    (hA : Continuous A) (hperiod : Function.Periodic A T) (hU : IsFundamentalOperator A U) :
    ∃ (B : E →L[ℝ] E) (P : ℝ → E →L[ℝ] E), Function.Periodic P (2 * T) ∧
      ContDiff ℝ 1 P ∧ (∀ t, (P t).IsInvertible) ∧
      ∀ t, U t = P t * NormedSpace.exp (t • B) := by
  sorry

/-- A classical solution of `-(p u')' + q u = λ w u` on an interval. -/
def IsSturmLiouvilleSolutionOn (p q w : ℝ → ℝ) (μ : ℝ) (u : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ContDiffOn ℝ 2 u I ∧ ∀ x ∈ I, -deriv (fun t ↦ p t * deriv u t) x + q x * u x = μ * w x * u x

/-- The ordinary Wronskian, used only at a finite point to certify independence. -/
def sturmWronskian (u v : ℝ → ℝ) (x : ℝ) : ℝ := u x * deriv v x - v x * deriv u x

/-- On the open interval, `ContDiffOn` supplies an ambient derivative. -/
private lemma contDiffAt_of_Icc {n : WithTop ℕ∞} {f : ℝ → ℝ} {a b x : ℝ}
    (hf : ContDiffOn ℝ n f (Icc a b)) (hx : x ∈ Ioo a b) : ContDiffAt ℝ n f x :=
  hf.contDiffAt (Icc_mem_nhds_iff.mpr hx)

/-- The differentiated leading term of a Sturm–Liouville solution, at an interior point. -/
private lemma hasDerivAt_sturmLeading {a b : ℝ} (_hab : a < b) (p q w u : ℝ → ℝ) (μ : ℝ)
    (hp : ContDiffOn ℝ 1 p (Icc a b))
    (hu : IsSturmLiouvilleSolutionOn p q w μ u (Icc a b)) {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (fun t ↦ p t * deriv u t) ((q x - μ * w x) * u x) x := by
  have hux : ContDiffAt ℝ 2 u x := contDiffAt_of_Icc hu.1 hx
  have hpx : ContDiffAt ℝ 1 p x := contDiffAt_of_Icc hp hx
  have hdu : DifferentiableAt ℝ (deriv u) x :=
    (hux.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdiff : DifferentiableAt ℝ (fun t ↦ p t * deriv u t) x :=
    (hpx.differentiableAt (by norm_num)).mul hdu
  have hSL := hu.2 x (Ioo_subset_Icc_self hx)
  have hval : deriv (fun t ↦ p t * deriv u t) x = (q x - μ * w x) * u x := by
    have hD : deriv (fun t ↦ p t * deriv u t) x =
        q x * u x - μ * w x * u x := by linear_combination -hSL
    linarith [hD]
  simpa [hval] using hdiff.hasDerivAt

/-- Interior derivative of `p` times the Wronskian, equal to `(μ - ν) w u v`. -/
private lemma hasDerivAt_sturmCross {a b : ℝ} (hab : a < b) (p q w u v : ℝ → ℝ) (μ ν : ℝ)
    (hp : ContDiffOn ℝ 1 p (Icc a b))
    (hu : IsSturmLiouvilleSolutionOn p q w μ u (Icc a b))
    (hv : IsSturmLiouvilleSolutionOn p q w ν v (Icc a b)) {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (fun t ↦ u t * (p t * deriv v t) - v t * (p t * deriv u t))
      ((μ - ν) * w x * u x * v x) x := by
  have hφu := hasDerivAt_sturmLeading hab p q w u μ hp hu hx
  have hφv := hasDerivAt_sturmLeading hab p q w v ν hp hv hx
  have hu' : DifferentiableAt ℝ u x :=
    (contDiffAt_of_Icc hu.1 hx).differentiableAt (by norm_num)
  have hv' : DifferentiableAt ℝ v x :=
    (contDiffAt_of_Icc hv.1 hx).differentiableAt (by norm_num)
  have hmul := (hu'.hasDerivAt.mul hφv).sub (hv'.hasDerivAt.mul hφu)
  exact hmul.congr_deriv (by ring)

/-- A continuous function with no zero on an open interval has constant strict sign. -/
private lemma sign_const_of_ne_zero {a b : ℝ} (hab : a < b) {u : ℝ → ℝ}
    (hu : ContinuousOn u (Icc a b)) (hno : ∀ x ∈ Ioo a b, u x ≠ 0) :
    (∀ x ∈ Ioo a b, 0 < u x) ∨ (∀ x ∈ Ioo a b, u x < 0) := by
  have hc : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  rcases lt_or_gt_of_ne (hno _ hc) with hneg | hpos
  · refine Or.inr fun x hx ↦ ?_
    by_contra hnot
    have hxpos : 0 < u x := lt_of_le_of_ne (not_lt.mp hnot) (hno x hx).symm
    rcases lt_trichotomy x ((a + b) / 2) with hlt | heq | hgt
    · have hsub : ContinuousOn u (Icc x ((a + b) / 2)) :=
        hu.mono fun y hy ↦ ⟨hx.1.le.trans hy.1, hy.2.trans hc.2.le⟩
      have h0 : (0 : ℝ) ∈ Ioo (u ((a + b) / 2)) (u x) := ⟨hneg, hxpos⟩
      have himg := intermediate_value_Ioo' (le_of_lt hlt) hsub h0
      rw [mem_image] at himg
      obtain ⟨z, hz, hz0⟩ := himg
      exact hno z ⟨hx.1.trans hz.1, hz.2.trans hc.2⟩ hz0
    · rw [heq] at hxpos
      exact lt_asymm hxpos hneg
    · have hsub : ContinuousOn u (Icc ((a + b) / 2) x) :=
        hu.mono fun y hy ↦ ⟨hc.1.le.trans hy.1, hy.2.trans hx.2.le⟩
      have h0 : (0 : ℝ) ∈ Ioo (u ((a + b) / 2)) (u x) := ⟨hneg, hxpos⟩
      have himg := intermediate_value_Ioo (le_of_lt hgt) hsub h0
      rw [mem_image] at himg
      obtain ⟨z, hz, hz0⟩ := himg
      exact hno z ⟨hc.1.trans hz.1, hz.2.trans hx.2⟩ hz0
  · refine Or.inl fun x hx ↦ ?_
    by_contra hnot
    have hxneg : u x < 0 := lt_of_le_of_ne (not_lt.mp hnot) (hno x hx)
    rcases lt_trichotomy x ((a + b) / 2) with hlt | heq | hgt
    · have hsub : ContinuousOn u (Icc x ((a + b) / 2)) :=
        hu.mono fun y hy ↦ ⟨hx.1.le.trans hy.1, hy.2.trans hc.2.le⟩
      have h0 : (0 : ℝ) ∈ Ioo (u x) (u ((a + b) / 2)) := ⟨hxneg, hpos⟩
      have himg := intermediate_value_Ioo (le_of_lt hlt) hsub h0
      rw [mem_image] at himg
      obtain ⟨z, hz, hz0⟩ := himg
      exact hno z ⟨hx.1.trans hz.1, hz.2.trans hc.2⟩ hz0
    · rw [heq] at hxneg
      exact lt_asymm hpos hxneg
    · have hsub : ContinuousOn u (Icc ((a + b) / 2) x) :=
        hu.mono fun y hy ↦ ⟨hc.1.le.trans hy.1, hy.2.trans hx.2.le⟩
      have h0 : (0 : ℝ) ∈ Ioo (u x) (u ((a + b) / 2)) := ⟨hxneg, hpos⟩
      have himg := intermediate_value_Ioo' (le_of_lt hgt) hsub h0
      rw [mem_image] at himg
      obtain ⟨z, hz, hz0⟩ := himg
      exact hno z ⟨hc.1.trans hz.1, hz.2.trans hx.2⟩ hz0

/-- A strictly increasing continuous function running from `-∞` to `+∞` has one root. -/
private lemma existsUnique_strictMono_zero {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo a b)) (hmono : StrictMonoOn f (Ioo a b))
    (ha : Tendsto f (𝓝[>] a) atBot) (hb : Tendsto f (𝓝[<] b) atTop) :
    ∃! x, x ∈ Ioo a b ∧ f x = 0 := by
  have hmem_a : Ioo a b ∈ 𝓝[>] a := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact self_mem_nhdsWithin
  have hmem_b : Ioo a b ∈ 𝓝[<] b := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact self_mem_nhdsWithin
  obtain ⟨c, hfc, hc⟩ :=
    ((ha.eventually (Iio_mem_atBot (0 : ℝ))).and
      (eventually_of_mem hmem_a fun _ hx ↦ hx)).exists
  obtain ⟨d, hfd, hd⟩ :=
    ((hb.eventually (Ioi_mem_atTop (0 : ℝ))).and
      (eventually_of_mem hmem_b fun _ hx ↦ hx)).exists
  have hcd : c < d := by
    by_contra hle
    have hle' : d ≤ c := le_of_not_gt hle
    have hfd_neg : f d < 0 := by
      rcases hle'.eq_or_lt with rfl | hlt
      · exact hfc
      · exact (hmono hd hc hlt).trans hfc
    exact lt_asymm hfd hfd_neg
  have hcont : ContinuousOn f (Icc c d) :=
    hf.mono fun x hx ↦ ⟨hc.1.trans_le hx.1, hx.2.trans_lt hd.2⟩
  have himg := intermediate_value_Ioo (le_of_lt hcd) hcont ⟨hfc, hfd⟩
  rw [mem_image] at himg
  obtain ⟨z, hz, hz0⟩ := himg
  have hzab : z ∈ Ioo a b := ⟨hc.1.trans hz.1, hz.2.trans hd.2⟩
  refine ⟨z, ⟨hzab, hz0⟩, ?_⟩
  rintro y ⟨hy, hy0⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (hmono hy hzab hlt).ne (hy0.trans hz0.symm)
  · exact (hmono hzab hy hgt).ne (hz0.trans hy0.symm)

/-- Quotient blowing up on the right of a simple root. -/
private lemma tendsto_div_nhdsGT {a : ℝ} {u v : ℝ → ℝ} {u' va : ℝ}
    (hua : u a = 0) (hu' : u' ≠ 0) (hva : va ≠ 0)
    (hslope : Tendsto (fun x ↦ (u x - u a) / (x - a)) (𝓝[>] a) (𝓝 u'))
    (hv : Tendsto v (𝓝[>] a) (𝓝 va)) :
    Tendsto (fun x ↦ v x / u x) (𝓝[>] a) (if 0 < va / u' then atTop else atBot) := by
  have hsub : Tendsto (fun x ↦ x - a) (𝓝[>] a) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hbase : Tendsto (fun x ↦ x - a) (𝓝[>] a) (𝓝 0) := by
        have hraw := ((continuous_id.sub (continuous_const (y := a))).tendsto a).mono_left
          (nhdsWithin_le_nhds (s := Ioi a))
        simp only [id_eq, Pi.sub_apply, sub_self] at hraw
        exact hraw
      exact hbase
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.mpr hx
  have hinv : Tendsto (fun x ↦ (x - a)⁻¹) (𝓝[>] a) atTop := hsub.inv_tendsto_nhdsGT_zero
  have hquot : Tendsto (fun x ↦ v x / ((u x - u a) / (x - a))) (𝓝[>] a) (𝓝 (va / u')) :=
    hv.div hslope hu'
  have hne : ({(0 : ℝ)}ᶜ) ∈ 𝓝 u' := isOpen_compl_singleton.mem_nhds (by simpa using hu')
  have hident :
      (fun x ↦ v x / ((u x - u a) / (x - a)) * (x - a)⁻¹) =ᶠ[𝓝[>] a] fun x ↦ v x / u x := by
    filter_upwards [self_mem_nhdsWithin, hslope.eventually hne] with x hx hsx
    have hxa : x - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx)
    have hmul : ((u x - u a) / (x - a)) * (x - a) = u x := by
      rw [div_mul_cancel₀ _ hxa, hua, sub_zero]
    calc v x / ((u x - u a) / (x - a)) * (x - a)⁻¹
        = v x * (((u x - u a) / (x - a))⁻¹ * (x - a)⁻¹) := by rw [div_eq_mul_inv, mul_assoc]
      _ = v x * (((u x - u a) / (x - a)) * (x - a))⁻¹ := by
          rw [mul_comm (((u x - u a) / (x - a))⁻¹), ← mul_inv_rev]
      _ = v x * (u x)⁻¹ := by rw [hmul]
      _ = v x / u x := by rw [div_eq_mul_inv]
  split_ifs with hsign
  · exact (hquot.pos_mul_atTop hsign hinv).congr' hident
  · have hneg : va / u' < 0 := lt_of_le_of_ne (not_lt.mp hsign) (div_ne_zero hva hu')
    exact (hquot.neg_mul_atTop hneg hinv).congr' hident

/-- Quotient blowing up on the left of a simple root. -/
private lemma tendsto_div_nhdsLT {b : ℝ} {u v : ℝ → ℝ} {u' vb : ℝ}
    (hub : u b = 0) (hu' : u' ≠ 0) (hvb : vb ≠ 0)
    (hslope : Tendsto (fun x ↦ (u x - u b) / (x - b)) (𝓝[<] b) (𝓝 u'))
    (hv : Tendsto v (𝓝[<] b) (𝓝 vb)) :
    Tendsto (fun x ↦ v x / u x) (𝓝[<] b) (if 0 < vb / u' then atBot else atTop) := by
  have hsub : Tendsto (fun x ↦ x - b) (𝓝[<] b) (𝓝[<] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hbase : Tendsto (fun x ↦ x - b) (𝓝[<] b) (𝓝 0) := by
        have hraw := ((continuous_id.sub (continuous_const (y := b))).tendsto b).mono_left
          (nhdsWithin_le_nhds (s := Iio b))
        simp only [id_eq, Pi.sub_apply, sub_self] at hraw
        exact hraw
      exact hbase
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_neg.mpr hx
  have hinv : Tendsto (fun x ↦ (x - b)⁻¹) (𝓝[<] b) atBot := hsub.inv_tendsto_nhdsLT_zero
  have hquot : Tendsto (fun x ↦ v x / ((u x - u b) / (x - b))) (𝓝[<] b) (𝓝 (vb / u')) :=
    hv.div hslope hu'
  have hne : ({(0 : ℝ)}ᶜ) ∈ 𝓝 u' := isOpen_compl_singleton.mem_nhds (by simpa using hu')
  have hident :
      (fun x ↦ v x / ((u x - u b) / (x - b)) * (x - b)⁻¹) =ᶠ[𝓝[<] b] fun x ↦ v x / u x := by
    filter_upwards [self_mem_nhdsWithin, hslope.eventually hne] with x hx hsx
    have hxb : x - b ≠ 0 := sub_ne_zero.mpr (ne_of_lt hx)
    have hmul : ((u x - u b) / (x - b)) * (x - b) = u x := by
      rw [div_mul_cancel₀ _ hxb, hub, sub_zero]
    calc v x / ((u x - u b) / (x - b)) * (x - b)⁻¹
        = v x * (((u x - u b) / (x - b))⁻¹ * (x - b)⁻¹) := by rw [div_eq_mul_inv, mul_assoc]
      _ = v x * (((u x - u b) / (x - b)) * (x - b))⁻¹ := by
          rw [mul_comm (((u x - u b) / (x - b))⁻¹), ← mul_inv_rev]
      _ = v x * (u x)⁻¹ := by rw [hmul]
      _ = v x / u x := by rw [div_eq_mul_inv]
  split_ifs with hsign
  · exact (hquot.pos_mul_atBot hsign hinv).congr' hident
  · have hneg : vb / u' < 0 := lt_of_le_of_ne (not_lt.mp hsign) (div_ne_zero hvb hu')
    exact (hquot.neg_mul_atBot hneg hinv).congr' hident

/-- Positive values on `(a, b)` force a nonnegative left derivative at `a`. -/
private lemma derivWithin_left_nonneg {a b : ℝ} (hab : a < b) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Icc a b)) (hua : u a = 0)
    (hpos : ∀ x ∈ Ioo a b, 0 < u x) : 0 ≤ derivWithin u (Icc a b) a := by
  have hdw : HasDerivWithinAt u (derivWithin u (Icc a b) a) (Icc a b) a :=
    ((hu.differentiableOn (by norm_num)) a ⟨le_rfl, hab.le⟩).hasDerivWithinAt
  have htend := (hasDerivWithinAt_iff_tendsto_slope.mp hdw)
  simp_rw [slope_fun_def_field] at htend
  have hset : Icc a b \ {a} = Ioc a b := by
    ext x
    simp only [Set.mem_sdiff, mem_Icc, mem_singleton_iff, mem_Ioc]
    constructor
    · rintro ⟨⟨hax, hxb⟩, hne⟩
      exact ⟨lt_of_le_of_ne hax (Ne.symm hne), hxb⟩
    · rintro ⟨hax, hxb⟩
      exact ⟨⟨hax.le, hxb⟩, Ne.symm hax.ne⟩
  rw [hset, nhdsWithin_Ioc_eq_nhdsGT hab] at htend
  refine ge_of_tendsto htend ?_
  have hmem : Ioo a b ∈ 𝓝[>] a := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact self_mem_nhdsWithin
  filter_upwards [hmem] with x hx
  exact (div_pos (by simpa [hua] using hpos x hx) (sub_pos.mpr hx.1)).le

/-- Positive values on `(a, b)` force a nonpositive right derivative at `b`. -/
private lemma derivWithin_right_nonpos {a b : ℝ} (hab : a < b) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Icc a b)) (hub : u b = 0)
    (hpos : ∀ x ∈ Ioo a b, 0 < u x) : derivWithin u (Icc a b) b ≤ 0 := by
  have hdw : HasDerivWithinAt u (derivWithin u (Icc a b) b) (Icc a b) b :=
    ((hu.differentiableOn (by norm_num)) b ⟨hab.le, le_rfl⟩).hasDerivWithinAt
  have htend := (hasDerivWithinAt_iff_tendsto_slope.mp hdw)
  simp_rw [slope_fun_def_field] at htend
  have hset : Icc a b \ {b} = Ico a b := by
    ext x
    simp only [Set.mem_sdiff, mem_Icc, mem_singleton_iff, mem_Ico]
    constructor
    · rintro ⟨⟨hax, hxb⟩, hne⟩
      exact ⟨hax, lt_of_le_of_ne hxb hne⟩
    · rintro ⟨hax, hxb⟩
      exact ⟨⟨hax, hxb.le⟩, hxb.ne⟩
  rw [hset, nhdsWithin_Ico_eq_nhdsLT hab] at htend
  refine le_of_tendsto htend ?_
  have hmem : Ioo a b ∈ 𝓝[<] b := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact self_mem_nhdsWithin
  filter_upwards [hmem] with x hx
  have hden : x - b < 0 := sub_neg.mpr hx.2
  have hnum : 0 < u x - u b := by simpa [hub] using hpos x hx
  exact div_nonpos_of_nonneg_of_nonpos hnum.le hden.le

/-- A nonnegative continuous limit from the right. -/
private lemma left_endpoint_nonneg {a b : ℝ} (hab : a < b) {v : ℝ → ℝ}
    (hv : ContinuousOn v (Icc a b)) (hpos : ∀ x ∈ Ioo a b, 0 < v x) : 0 ≤ v a := by
  have hle : 𝓝[>] a ≤ 𝓝[Icc a b] a :=
    (nhdsWithin_Ioo_eq_nhdsGT hab).symm.le.trans (nhdsWithin_mono a Ioo_subset_Icc_self)
  refine ge_of_tendsto ((hv.continuousWithinAt ⟨le_rfl, hab.le⟩).tendsto.mono_left hle) ?_
  filter_upwards [by rw [← nhdsWithin_Ioo_eq_nhdsGT hab]; exact self_mem_nhdsWithin] with x hx
  exact (hpos x hx).le

/-- A nonnegative continuous limit from the left. -/
private lemma right_endpoint_nonneg {a b : ℝ} (hab : a < b) {v : ℝ → ℝ}
    (hv : ContinuousOn v (Icc a b)) (hpos : ∀ x ∈ Ioo a b, 0 < v x) : 0 ≤ v b := by
  have hle : 𝓝[<] b ≤ 𝓝[Icc a b] b :=
    (nhdsWithin_Ioo_eq_nhdsLT hab).symm.le.trans (nhdsWithin_mono b Ioo_subset_Icc_self)
  refine ge_of_tendsto ((hv.continuousWithinAt ⟨hab.le, le_rfl⟩).tendsto.mono_left hle) ?_
  filter_upwards [by rw [← nhdsWithin_Ioo_eq_nhdsLT hab]; exact self_mem_nhdsWithin] with x hx
  exact (hpos x hx).le

/-- **31.20**, separation: independent solutions have exactly one intervening zero. -/
theorem sturm_separation {a b : ℝ} (hab : a < b) (p q w u v : ℝ → ℝ) (μ : ℝ)
    (hp : ContDiffOn ℝ 1 p (Set.Icc a b)) (hq : ContinuousOn q (Set.Icc a b))
    (hw : ContinuousOn w (Set.Icc a b)) (hp_pos : ∀ x ∈ Set.Icc a b, 0 < p x)
    (hu : IsSturmLiouvilleSolutionOn p q w μ u (Set.Icc a b))
    (hv : IsSturmLiouvilleSolutionOn p q w μ v (Set.Icc a b))
    (hua : u a = 0) (hub : u b = 0) (hno : ∀ x ∈ Set.Ioo a b, u x ≠ 0)
    (hind : sturmWronskian u v a ≠ 0) : ∃! x, x ∈ Set.Ioo a b ∧ v x = 0 := by
  have _hq := hq
  have _hw := hw
  let W := sturmWronskian u v
  let f := fun t ↦ p t * W t
  have hHas : ∀ x ∈ Ioo a b, HasDerivAt f 0 x := by
    intro x hx
    have hcross := hasDerivAt_sturmCross hab p q w u v μ μ hp hu hv hx
    have hfun : (fun t ↦ u t * (p t * deriv v t) - v t * (p t * deriv u t)) = f := by
      funext t
      simp only [f, W, sturmWronskian]
      ring
    rw [hfun] at hcross
    exact hcross.congr_deriv (by ring)
  have hdiff : DifferentiableOn ℝ f (Ioo a b) := fun x hx ↦
    (hHas x hx).differentiableAt.differentiableWithinAt
  have hderiv0 : Ioo a b |>.EqOn (deriv f) 0 := fun x hx ↦ (hHas x hx).deriv
  obtain ⟨c, hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hderiv0
  have hdu_a : DifferentiableAt ℝ u a := by
    by_contra hnot
    exact hind (by simp [sturmWronskian, hua, deriv_zero_of_not_differentiableAt hnot])
  have hu'a : derivWithin u (Icc a b) a = deriv u a :=
    hdu_a.hasDerivAt.hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc hab a ⟨le_rfl, hab.le⟩)
  have hle_a : 𝓝[>] a ≤ 𝓝[Icc a b] a :=
    (nhdsWithin_Ioo_eq_nhdsGT hab).symm.le.trans (nhdsWithin_mono a Ioo_subset_Icc_self)
  have hle_b : 𝓝[<] b ≤ 𝓝[Icc a b] b :=
    (nhdsWithin_Ioo_eq_nhdsLT hab).symm.le.trans (nhdsWithin_mono b Ioo_subset_Icc_self)
  have hmem_a : Ioo a b ∈ 𝓝[>] a := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact self_mem_nhdsWithin
  have hmem_b : Ioo a b ∈ 𝓝[<] b := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact self_mem_nhdsWithin
  have hcont_du := hu.1.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  have hcont_dv := hv.1.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  have hlim_du : Tendsto (deriv u) (𝓝[>] a) (𝓝 (deriv u a)) := by
    have hbase := (hcont_du.continuousWithinAt ⟨le_rfl, hab.le⟩).tendsto.mono_left hle_a
    rw [hu'a] at hbase
    refine hbase.congr' ?_
    filter_upwards [hmem_a] with x hx
    exact derivWithin_of_mem_nhds (Icc_mem_nhds_iff.mpr hx)
  have hlim_dv : Tendsto (deriv v) (𝓝[>] a) (𝓝 (derivWithin v (Icc a b) a)) := by
    have hbase := (hcont_dv.continuousWithinAt ⟨le_rfl, hab.le⟩).tendsto.mono_left hle_a
    refine hbase.congr' ?_
    filter_upwards [hmem_a] with x hx
    exact derivWithin_of_mem_nhds (Icc_mem_nhds_iff.mpr hx)
  have hlim_u := (hu.1.continuousOn.continuousWithinAt ⟨le_rfl, hab.le⟩).tendsto.mono_left hle_a
  have hlim_v := (hv.1.continuousOn.continuousWithinAt ⟨le_rfl, hab.le⟩).tendsto.mono_left hle_a
  have hlim_p := (hp.continuousOn.continuousWithinAt ⟨le_rfl, hab.le⟩).tendsto.mono_left hle_a
  have hlimW : Tendsto W (𝓝[>] a) (𝓝 (W a)) := by
    have hprod := (hlim_u.mul hlim_dv).sub (hlim_v.mul hlim_du)
    have hpt : W a = u a * derivWithin v (Icc a b) a - v a * deriv u a := by
      simp [W, sturmWronskian, hua]
    have hfun : W = fun x ↦ u x * deriv v x - v x * deriv u x := by
      ext x
      simp [W, sturmWronskian]
    rw [hpt, hfun]
    exact hprod
  have hlimf : Tendsto f (𝓝[>] a) (𝓝 (p a * W a)) := by simpa [f] using hlim_p.mul hlimW
  have hlimc : Tendsto f (𝓝[>] a) (𝓝 c) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hmem_a] with x hx
    exact (hc x hx).symm
  have hc_eq : c = p a * W a := tendsto_nhds_unique hlimc hlimf
  have hc_ne : c ≠ 0 := hc_eq ▸ mul_ne_zero (hp_pos a ⟨le_rfl, hab.le⟩).ne' hind
  have hpa : 0 < p a := hp_pos a ⟨le_rfl, hab.le⟩
  have hpb : 0 < p b := hp_pos b ⟨hab.le, le_rfl⟩
  have hv_a : v a ≠ 0 := by
    intro hv0
    exact hind (by simp [sturmWronskian, hua, hv0])
  have hu'a_ne : deriv u a ≠ 0 := by
    intro hu0
    exact hind (by simp [sturmWronskian, hua, hu0])
  have hlim_du_b : Tendsto (deriv u) (𝓝[<] b) (𝓝 (derivWithin u (Icc a b) b)) := by
    have hbase := (hcont_du.continuousWithinAt ⟨hab.le, le_rfl⟩).tendsto.mono_left hle_b
    refine hbase.congr' ?_
    filter_upwards [hmem_b] with x hx
    exact derivWithin_of_mem_nhds (Icc_mem_nhds_iff.mpr hx)
  have hlim_dv_b : Tendsto (deriv v) (𝓝[<] b) (𝓝 (derivWithin v (Icc a b) b)) := by
    have hbase := (hcont_dv.continuousWithinAt ⟨hab.le, le_rfl⟩).tendsto.mono_left hle_b
    refine hbase.congr' ?_
    filter_upwards [hmem_b] with x hx
    exact derivWithin_of_mem_nhds (Icc_mem_nhds_iff.mpr hx)
  have hlim_u_b := (hu.1.continuousOn.continuousWithinAt ⟨hab.le, le_rfl⟩).tendsto.mono_left hle_b
  have hlim_v_b := (hv.1.continuousOn.continuousWithinAt ⟨hab.le, le_rfl⟩).tendsto.mono_left hle_b
  have hlim_p_b := (hp.continuousOn.continuousWithinAt ⟨hab.le, le_rfl⟩).tendsto.mono_left hle_b
  have hlimf_b : Tendsto f (𝓝[<] b) (𝓝 c) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hmem_b] with x hx
    exact (hc x hx).symm
  have hlimW_b : Tendsto W (𝓝[<] b) (𝓝 (c / p b)) := by
    have hW : W =ᶠ[𝓝[<] b] fun x ↦ f x / p x := by
      filter_upwards [hmem_b] with x hx
      have hpne := (hp_pos x (Ioo_subset_Icc_self hx)).ne'
      rw [eq_div_iff hpne, mul_comm]
    exact (hlimf_b.div hlim_p_b hpb.ne').congr' hW.symm
  have hstruct_b : Tendsto W (𝓝[<] b) (𝓝 (-(v b * derivWithin u (Icc a b) b))) := by
    have hprod := (hlim_u_b.mul hlim_dv_b).sub (hlim_v_b.mul hlim_du_b)
    have hfun : (fun x ↦ u x * deriv v x - v x * deriv u x) = W := by
      ext x
      simp [W, sturmWronskian]
    rw [← hfun]
    simpa [hub] using hprod
  have hWb : -(v b * derivWithin u (Icc a b) b) = c / p b :=
    tendsto_nhds_unique hstruct_b hlimW_b
  have hv_b : v b ≠ 0 := by
    intro hv0
    have : c / p b = 0 := by simpa [hv0] using hWb.symm
    exact hc_ne (((div_eq_zero_iff.mp this).resolve_right hpb.ne'))
  have hu'b_ne : derivWithin u (Icc a b) b ≠ 0 := by
    intro hu0
    have : c / p b = 0 := by simpa [hu0] using hWb.symm
    exact hc_ne (((div_eq_zero_iff.mp this).resolve_right hpb.ne'))
  have hslope_a : Tendsto (fun x ↦ (u x - u a) / (x - a)) (𝓝[>] a) (𝓝 (deriv u a)) := by
    have h := hdu_a.hasDerivAt.tendsto_slope
    simp_rw [slope_fun_def_field] at h
    exact h.mono_left (nhdsGT_le_nhdsNE a)
  have hslope_b : Tendsto (fun x ↦ (u x - u b) / (x - b)) (𝓝[<] b)
      (𝓝 (derivWithin u (Icc a b) b)) := by
    have hdw : HasDerivWithinAt u (derivWithin u (Icc a b) b) (Icc a b) b :=
      ((hu.1.differentiableOn (by norm_num)) b ⟨hab.le, le_rfl⟩).hasDerivWithinAt
    have h := (hasDerivWithinAt_iff_tendsto_slope.mp hdw)
    simp_rw [slope_fun_def_field] at h
    have hset : Icc a b \ {b} = Ico a b := by
      ext x
      simp only [Set.mem_sdiff, mem_Icc, mem_singleton_iff, mem_Ico]
      constructor
      · rintro ⟨⟨hax, hxb⟩, hne⟩
        exact ⟨hax, lt_of_le_of_ne hxb hne⟩
      · rintro ⟨hax, hxb⟩
        exact ⟨⟨hax, hxb.le⟩, hxb.ne⟩
    rw [hset, nhdsWithin_Ico_eq_nhdsLT hab] at h
    exact h
  let ratio := fun t ↦ v t / u t
  have hratio_cont : ContinuousOn ratio (Ioo a b) :=
    (hv.1.continuousOn.mono Ioo_subset_Icc_self).div
      (hu.1.continuousOn.mono Ioo_subset_Icc_self) hno
  have hratio_deriv : ∀ x ∈ Ioo a b, deriv ratio x = W x / (u x) ^ 2 := by
    intro x hx
    have hu' := (contDiffAt_of_Icc hu.1 hx).differentiableAt (by norm_num)
    have hv' := (contDiffAt_of_Icc hv.1 hx).differentiableAt (by norm_num)
    have hd := deriv_div hv' hu' (hno x hx)
    have heq : (v / u) = fun t ↦ v t / u t := by
      ext t
      simp [Pi.div_apply]
    rw [heq] at hd
    rw [hd]
    simp only [W, sturmWronskian]
    ring
  have hW_eq : ∀ x ∈ Ioo a b, W x = c / p x := by
    intro x hx
    rw [eq_div_iff (hp_pos x (Ioo_subset_Icc_self hx)).ne', mul_comm]
    exact hc x hx
  have hWa : W a = c / p a := by rw [hc_eq]; field_simp [hpa.ne']
  have hdiv_a : v a / deriv u a = -(c / p a) / (deriv u a) ^ 2 := by
    have hW : W a = -(v a * deriv u a) := by simp [W, sturmWronskian, hua]
    rw [← hWa, hW]
    field_simp [hu'a_ne]
  let ub : ℝ := derivWithin u (Icc a b) b
  have hdiv_b : v b / ub = -(c / p b) / ub ^ 2 := by
    have hmul : v b * ub = -(c / p b) := (neg_eq_iff_eq_neg).mp hWb
    rw [← hmul]
    exact (div_eq_div_iff hu'b_ne (pow_ne_zero 2 hu'b_ne)).mpr (by ring)
  have hratio_a := tendsto_div_nhdsGT hua hu'a_ne hv_a hslope_a hlim_v
  have hratio_b := tendsto_div_nhdsLT hub hu'b_ne hv_b hslope_b hlim_v_b
  have hmono_pos : 0 < c → StrictMonoOn ratio (Ioo a b) := by
    intro hc_pos
    refine strictMonoOn_of_deriv_pos (convex_Ioo a b) hratio_cont ?_
    intro x hx
    rw [isOpen_Ioo.interior_eq] at hx
    rw [hratio_deriv x hx, hW_eq x hx]
    exact div_pos (div_pos hc_pos (hp_pos x (Ioo_subset_Icc_self hx)))
      (sq_pos_of_ne_zero (hno x hx))
  rcases lt_or_gt_of_ne hc_ne with hc_neg | hc_pos
  · have hlt_a : 0 < v a / deriv u a := by
      rw [hdiv_a]
      exact div_pos (neg_pos.mpr (div_neg_of_neg_of_pos hc_neg hpa))
        (sq_pos_of_ne_zero hu'a_ne)
    have hlt_b : 0 < v b / ub := by
      rw [hdiv_b]
      exact div_pos (neg_pos.mpr (div_neg_of_neg_of_pos hc_neg hpb))
        (sq_pos_of_ne_zero hu'b_ne)
    rw [ite_eq_left hlt_a] at hratio_a
    rw [ite_eq_left hlt_b] at hratio_b
    have hanti : StrictAntiOn ratio (Ioo a b) := by
      refine strictAntiOn_of_deriv_neg (convex_Ioo a b) hratio_cont ?_
      intro x hx
      rw [isOpen_Ioo.interior_eq] at hx
      rw [hratio_deriv x hx, hW_eq x hx]
      exact div_neg_of_neg_of_pos (div_neg_of_neg_of_pos hc_neg
        (hp_pos x (Ioo_subset_Icc_self hx))) (sq_pos_of_ne_zero (hno x hx))
    have hmono : StrictMonoOn (fun x ↦ -ratio x) (Ioo a b) := by
      intro x hx y hy hxy
      exact neg_lt_neg (hanti hx hy hxy)
    have hroot := existsUnique_strictMono_zero hab hratio_cont.neg hmono
      (tendsto_neg_atTop_atBot.comp hratio_a) (tendsto_neg_atBot_atTop.comp hratio_b)
    obtain ⟨x, ⟨hx, hx0⟩, huniq⟩ := hroot
    refine ⟨x, ⟨hx, ?_⟩, ?_⟩
    · have hx0' : -(v x / u x) = 0 := by simpa [ratio] using hx0
      exact ((div_eq_zero_iff).mp (neg_eq_zero.mp hx0')).resolve_right (hno x hx)
    · intro y hy
      exact huniq y ⟨hy.1, by simp [ratio, hy.2]⟩
  · have hlt_a : v a / deriv u a < 0 := by
      rw [hdiv_a]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos (div_pos hc_pos hpa))
        (sq_pos_of_ne_zero hu'a_ne)
    have hlt_b : v b / ub < 0 := by
      rw [hdiv_b]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos (div_pos hc_pos hpb))
        (sq_pos_of_ne_zero hu'b_ne)
    rw [ite_eq_right (not_lt_of_gt hlt_a)] at hratio_a
    rw [ite_eq_right (not_lt_of_gt hlt_b)] at hratio_b
    obtain ⟨x, ⟨hx, hx0⟩, huniq⟩ := existsUnique_strictMono_zero (f := ratio) hab hratio_cont
      (hmono_pos hc_pos) hratio_a hratio_b
    refine ⟨x, ⟨hx, (div_eq_zero_iff.mp (by simpa [ratio] using hx0)).resolve_right (hno x hx)⟩, ?_⟩
    intro y hy
    exact huniq y ⟨hy.1, by simp [ratio, hy.2]⟩

/-- Increasing the spectral parameter forces a zero between successive zeros of a lower mode. -/
theorem sturm_comparison {a b μ ν : ℝ} (hab : a < b) (hμν : μ < ν)
    (p q w u v : ℝ → ℝ) (hp : ContDiffOn ℝ 1 p (Set.Icc a b))
    (hq : ContinuousOn q (Set.Icc a b)) (hw : ContinuousOn w (Set.Icc a b))
    (hp_pos : ∀ x ∈ Set.Icc a b, 0 < p x) (hw_pos : ∀ x ∈ Set.Icc a b, 0 < w x)
    (hu : IsSturmLiouvilleSolutionOn p q w μ u (Set.Icc a b))
    (hv : IsSturmLiouvilleSolutionOn p q w ν v (Set.Icc a b))
    (hua : u a = 0) (hub : u b = 0) (hno : ∀ x ∈ Set.Ioo a b, u x ≠ 0) :
    ∃ x ∈ Set.Ioo a b, v x = 0 := by
  have _hq := hq
  by_contra hnone
  have hv_ne : ∀ x ∈ Ioo a b, v x ≠ 0 := by
    intro x hx hvx
    exact hnone ⟨x, hx, hvx⟩
  let s : Set ℝ := Icc a b
  let du := derivWithin u s
  let dv := derivWithin v s
  let F : ℝ → ℝ := fun t ↦ v t * (p t * du t) - u t * (p t * dv t)
  let g : ℝ → ℝ := fun x ↦ (ν - μ) * w x * u x * v x
  have hdu_cont := hu.1.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  have hdv_cont := hv.1.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  have hF_cont : ContinuousOn F s :=
    (hv.1.continuousOn.mul (hp.continuousOn.mul hdu_cont)).sub
      (hu.1.continuousOn.mul (hp.continuousOn.mul hdv_cont))
  have hg_cont : ContinuousOn g s :=
    (((continuousOn_const.mul hw).mul hu.1.continuousOn).mul hv.1.continuousOn)
  have hF_deriv : ∀ x ∈ Ioo a b, HasDerivAt F (g x) x := by
    intro x hx
    have hcross := hasDerivAt_sturmCross hab p q w u v μ ν hp hu hv hx
    have hnear : F =ᶠ[𝓝 x]
        fun t ↦ -(u t * (p t * deriv v t) - v t * (p t * deriv u t)) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
      have hdu_eq := derivWithin_of_mem_nhds (f := u) (s := s) (x := t)
        (Icc_mem_nhds_iff.mpr ht)
      have hdv_eq := derivWithin_of_mem_nhds (f := v) (s := s) (x := t)
        (Icc_mem_nhds_iff.mpr ht)
      simp only [F, du, dv]
      rw [hdu_eq, hdv_eq]
      ring
    refine (hcross.neg.congr_of_eventuallyEq hnear).congr_deriv ?_
    simp only [g]
    ring
  have hFTC := integral_eq_sub_of_hasDerivAt_of_le hab.le hF_cont hF_deriv
    (hg_cont.intervalIntegrable_of_Icc hab.le)
  have hFa : F a = v a * (p a * du a) := by simp [F, hua]
  have hFb : F b = v b * (p b * du b) := by simp [F, hub]
  have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hIntPos (hgt : ∀ x ∈ Ioo a b, 0 < g x) (hle : F b - F a ≤ 0) : False := by
    have hnn : ∀ x ∈ Ioc a b, 0 ≤ g x := by
      intro x hx
      rcases eq_or_lt_of_le hx.2 with rfl | hxb
      · simp [g, hub]
      · exact (hgt x ⟨hx.1, hxb⟩).le
    have hpos := integral_pos hab hg_cont hnn ⟨(a + b) / 2, Ioo_subset_Icc_self hmid, hgt _ hmid⟩
    linarith [hFTC, hpos]
  have hIntNeg (hlt : ∀ x ∈ Ioo a b, g x < 0) (hge : 0 ≤ F b - F a) : False := by
    have hgt : ∀ x ∈ Ioo a b, 0 < -g x := fun x hx ↦ neg_pos.mpr (hlt x hx)
    have hnn : ∀ x ∈ Ioc a b, 0 ≤ -g x := by
      intro x hx
      rcases eq_or_lt_of_le hx.2 with rfl | hxb
      · simp [g, hub]
      · exact (hgt x ⟨hx.1, hxb⟩).le
    have hpos := integral_pos hab hg_cont.neg hnn
      ⟨(a + b) / 2, Ioo_subset_Icc_self hmid, hgt _ hmid⟩
    have hpos' : 0 < ∫ x in a..b, -g x := by simpa [Pi.neg_apply] using hpos
    have hnegint : ∫ x in a..b, -g x = -∫ x in a..b, g x :=
      intervalIntegral.integral_neg (a := a) (b := b) (μ := MeasureTheory.volume) (f := g)
    have hlt_int : ∫ x in a..b, g x < 0 := by
      rw [hnegint] at hpos'
      linarith
    linarith [hFTC, hlt_int]
  have hpa := hp_pos a ⟨le_rfl, hab.le⟩
  have hpb := hp_pos b ⟨hab.le, le_rfl⟩
  rcases sign_const_of_ne_zero hab hu.1.continuousOn hno with hu_pos | hu_neg
  · have hdu_a : 0 ≤ du a := derivWithin_left_nonneg hab hu.1 hua hu_pos
    have hdu_b : du b ≤ 0 := derivWithin_right_nonpos hab hu.1 hub hu_pos
    rcases sign_const_of_ne_zero hab hv.1.continuousOn hv_ne with hv_pos | hv_neg
    · have hFa0 : 0 ≤ F a := by
        rw [hFa]
        exact mul_nonneg (left_endpoint_nonneg hab hv.1.continuousOn hv_pos)
          (mul_nonneg hpa.le hdu_a)
      have hFb0 : F b ≤ 0 := by
        rw [hFb]
        exact mul_nonpos_of_nonneg_of_nonpos (right_endpoint_nonneg hab hv.1.continuousOn hv_pos)
          (mul_nonpos_of_nonneg_of_nonpos hpb.le hdu_b)
      exact hIntPos (fun x hx ↦ by
        have hwx := hw_pos x (Ioo_subset_Icc_self hx)
        have h1 : 0 < (ν - μ) * w x := mul_pos (sub_pos.mpr hμν) hwx
        have h2 : 0 < (ν - μ) * w x * u x := mul_pos h1 (hu_pos x hx)
        simpa [g] using mul_pos h2 (hv_pos x hx)) (by linarith)
    · have hva : v a ≤ 0 := by
        simpa using left_endpoint_nonneg hab hv.1.continuousOn.neg
          (fun x hx ↦ neg_pos.mpr (hv_neg x hx))
      have hvb : v b ≤ 0 := by
        simpa using right_endpoint_nonneg hab hv.1.continuousOn.neg
          (fun x hx ↦ neg_pos.mpr (hv_neg x hx))
      have hFa0 : F a ≤ 0 := by
        rw [hFa]
        exact mul_nonpos_of_nonpos_of_nonneg hva (mul_nonneg hpa.le hdu_a)
      have hFb0 : 0 ≤ F b := by
        rw [hFb]
        exact mul_nonneg_of_nonpos_of_nonpos hvb (mul_nonpos_of_nonneg_of_nonpos hpb.le hdu_b)
      exact hIntNeg (fun x hx ↦ by
        have hwx := hw_pos x (Ioo_subset_Icc_self hx)
        have h1 : 0 < (ν - μ) * w x := mul_pos (sub_pos.mpr hμν) hwx
        have h2 : 0 < (ν - μ) * w x * u x := mul_pos h1 (hu_pos x hx)
        simpa [g] using mul_neg_of_pos_of_neg h2 (hv_neg x hx)) (by linarith)
  · have hdu_a : du a ≤ 0 := by
      have h := derivWithin_left_nonneg hab (ContDiffOn.neg hu.1) (by simpa using hua)
        (fun x hx ↦ neg_pos.mpr (hu_neg x hx))
      have hfun : (fun t ↦ -u t) = -u := by
        ext t
        simp [Pi.neg_apply]
      rw [hfun, derivWithin.neg] at h
      simpa [du, s] using h
    have hdu_b : 0 ≤ du b := by
      have h := derivWithin_right_nonpos hab (ContDiffOn.neg hu.1) (by simpa using hub)
        (fun x hx ↦ neg_pos.mpr (hu_neg x hx))
      have hfun : (fun t ↦ -u t) = -u := by
        ext t
        simp [Pi.neg_apply]
      rw [hfun, derivWithin.neg] at h
      simpa [du, s] using h
    rcases sign_const_of_ne_zero hab hv.1.continuousOn hv_ne with hv_pos | hv_neg
    · have hva : 0 ≤ v a := left_endpoint_nonneg hab hv.1.continuousOn hv_pos
      have hvb : 0 ≤ v b := right_endpoint_nonneg hab hv.1.continuousOn hv_pos
      have hFa0 : F a ≤ 0 := by
        rw [hFa]
        exact mul_nonpos_of_nonneg_of_nonpos hva (mul_nonpos_of_nonneg_of_nonpos hpa.le hdu_a)
      have hFb0 : 0 ≤ F b := by
        rw [hFb]
        exact mul_nonneg hvb (mul_nonneg hpb.le hdu_b)
      exact hIntNeg (fun x hx ↦ by
        have hwx := hw_pos x (Ioo_subset_Icc_self hx)
        have h1 : 0 < (ν - μ) * w x := mul_pos (sub_pos.mpr hμν) hwx
        have h2 : (ν - μ) * w x * u x < 0 := mul_neg_of_pos_of_neg h1 (hu_neg x hx)
        simpa [g] using mul_neg_of_neg_of_pos h2 (hv_pos x hx)) (by linarith)
    · have hva : v a ≤ 0 := by
        simpa using left_endpoint_nonneg hab hv.1.continuousOn.neg
          (fun x hx ↦ neg_pos.mpr (hv_neg x hx))
      have hvb : v b ≤ 0 := by
        simpa using right_endpoint_nonneg hab hv.1.continuousOn.neg
          (fun x hx ↦ neg_pos.mpr (hv_neg x hx))
      have hFa0 : 0 ≤ F a := by
        rw [hFa]
        exact mul_nonneg_of_nonpos_of_nonpos hva (mul_nonpos_of_nonneg_of_nonpos hpa.le hdu_a)
      have hFb0 : F b ≤ 0 := by
        rw [hFb]
        exact mul_nonpos_of_nonpos_of_nonneg hvb (mul_nonneg hpb.le hdu_b)
      exact hIntPos (fun x hx ↦ by
        have hwx := hw_pos x (Ioo_subset_Icc_self hx)
        have h1 : 0 < (ν - μ) * w x := mul_pos (sub_pos.mpr hμν) hwx
        have h2 : 0 < u x * v x := mul_pos_of_neg_of_neg (hu_neg x hx) (hv_neg x hx)
        simpa [g, mul_assoc] using mul_pos h1 h2) (by linarith)

end CKMA
