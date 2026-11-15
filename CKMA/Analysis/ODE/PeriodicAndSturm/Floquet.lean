/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Basic

import Mathlib.Analysis.ODE.ExistUnique

/-!
# Fundamental operators and Liouville's formula for periodic linear ODEs

Normalized fundamental operators of linear ODE systems, monodromy under periodic shifts,
and Liouville's determinant formula establishing invertibility of complex fundamental
operators at all times.

## Main definitions

* `CKMA.IsFundamentalOperator`: A normalized fundamental operator `U` satisfying `U 0 = 1`
  and `U' t = A t ∘L U t`.

## Main results

* `CKMA.IsFundamentalOperator.add_period_eq_mul`: Shifting a normalized fundamental operator
  by one period `T` multiplies on the right by `U T`.
* `CKMA.IsFundamentalOperator.det_ne_zero`: Liouville's formula implies that the determinant of
  a complex fundamental operator never vanishes.
* `CKMA.IsFundamentalOperator.isInvertible`: A complex fundamental operator is invertible at
  every time.
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

/-- The determinant of a complex fundamental operator never vanishes. -/
lemma IsFundamentalOperator.det_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
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
    exact continuous_finsetSum _ fun i _ ↦ hentry i
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
lemma IsFundamentalOperator.isInvertible {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [FiniteDimensional ℂ E] {A U : ℝ → E →L[ℂ] E} (hA : Continuous A)
    (hU : IsFundamentalOperator A U) (t : ℝ) : (U t).IsInvertible := by
  have hdet := hU.det_ne_zero hA t
  have hequiv := ContinuousLinearMap.isInvertible_equiv
    (f := (U t).toContinuousLinearEquivOfDetNeZero hdet)
  simpa [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using hequiv

end CKMA
