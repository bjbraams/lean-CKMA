/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Operator.Dilation.Minimal
public import CKMA.Analysis.Operator.Dilation.WoldExtend
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Minimal unitary power dilation

The bilateral extension of a minimal isometric dilation is a minimal unitary power dilation.
Nonnegative powers reproduce the isometry, and the two-sided orbit stays dense because the
forward isometric orbit was already dense. This is Sz.-Nagy’s unitary dilation, Chapter I of
Sz.-Nagy–Foiaş–Bercovici–Kérchy.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace
open ContinuousLinearMap Submodule

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A continuous linear functional that vanishes on a densely spanning set vanishes everywhere. -/
theorem clm_vanish_of_dense_span (f : E →L[ℂ] ℂ) {s : Set E}
    (hspan : (span ℂ s).topologicalClosure = ⊤) (hf : ∀ w ∈ s, f w = 0) (z : E) : f z = 0 := by
  have hsub : (span ℂ s : Set E) ⊆ {w | f w = 0} := by
    intro w hw
    refine span_induction ?_ ?_ ?_ ?_ hw
    · intro u hu
      exact hf u hu
    · simp
    · intro a b _ _ ha hb
      simp only [Set.mem_ofPred_eq] at ha hb ⊢
      rw [map_add, ha, hb, add_zero]
    · intro c a _ ha
      simp only [Set.mem_ofPred_eq] at ha ⊢
      rw [map_smul, ha, smul_zero]
  have hcl : IsClosed {w : E | f w = 0} := isClosed_eq f.continuous continuous_const
  have hz : z ∈ closure (span ℂ s : Set E) := by
    rw [← topologicalClosure_coe, hspan]
    exact mem_top
  exact closure_minimal hsub hcl hz

/-- Iterates of a linear isometric equivalence agree with its monoid powers. -/
theorem equiv_iterate_pow_apply (e : E ≃ₗᵢ[ℂ] E) (n : ℕ) (x : E) : (e^[n]) x = (e ^ n) x := by
  induction n with
  | zero => simp [Function.iterate_zero, pow_zero, LinearIsometryEquiv.coe_one]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ', LinearIsometryEquiv.coe_mul,
      Function.comp_apply]

variable {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Co-invariance passes to every nonnegative power of the isometry. -/
theorem adjoint_isometry_pow (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y))
    (n : ℕ) (y : K) :
    J.toContinuousLinearMap.adjoint ((V ^ n) y) =
      (T ^ n) (J.toContinuousLinearMap.adjoint y) := by
  induction n generalizing y with
  | zero => simp [pow_zero, LinearIsometry.one_def, one_apply_eq_self]
  | succ n ih =>
    rw [pow_succ', LinearIsometry.mul_def, LinearIsometry.coe_comp, Function.comp_apply, hcoin,
      ih, pow_succ', mul_apply_eq_comp]

/-- The adjoint of an isometric embedding is a left inverse. -/
theorem adjoint_isometry_leftInverse (J : H →ₗᵢ[ℂ] K) (x : H) :
    J.toContinuousLinearMap.adjoint (J x) = x := by
  have hs := congrArg (fun A : H →L[ℂ] H => A x) J.adjoint_comp_self
  rw [ContinuousLinearMap.comp_apply, one_apply_eq_self] at hs
  exact hs

omit [CompleteSpace H] in
/-- Shifting a forward orbit by the bilateral unitary stays on the embedded two-sided orbit. -/
theorem woldExtension_shift_orbit (J0 : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) (k : ℤ) (n : ℕ) (x : H) :
    (woldBilateralEquiv V ^ k) (woldExtensionIncl V
        ((V.toContinuousLinearMap ^ n) (J0 x))) =
      (woldBilateralEquiv V ^ (k + (n : ℤ))) ((woldExtensionIncl V).comp J0 x) := by
  have hpow : (V ^ n) (J0 x) = (V.toContinuousLinearMap ^ n) (J0 x) :=
    isometry_pow_apply V n (J0 x)
  rw [← hpow]
  have hstep : woldExtensionIncl V ((V ^ n) (J0 x)) =
      (woldBilateralEquiv V ^ n) (woldExtensionIncl V (J0 x)) :=
    (woldExtension_pow V n (J0 x)).symm
  rw [hstep]
  have hJ : woldExtensionIncl V (J0 x) = (woldExtensionIncl V).comp J0 x := by
    simp [LinearIsometry.coe_comp]
  rw [hJ, ← zpow_natCast (woldBilateralEquiv V) n]
  have hmul : (woldBilateralEquiv V ^ k) ((woldBilateralEquiv V ^ (n : ℤ))
      ((woldExtensionIncl V).comp J0 x)) =
      ((woldBilateralEquiv V ^ k) * (woldBilateralEquiv V ^ (n : ℤ)))
        ((woldExtensionIncl V).comp J0 x) := by
    rw [LinearIsometryEquiv.coe_mul, Function.comp_apply]
  rw [hmul, ← zpow_add]

omit [CompleteSpace H] in
set_option linter.style.haveILetI false in
/-- Density of the forward isometric orbit implies density of the bilateral embedded orbit. -/
theorem minimalUnitary_of_minimalIsometric (J0 : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hmin : (span ℂ {y : K | ∃ n : ℕ, ∃ x : H,
      y = (V.toContinuousLinearMap ^ n) (J0 x)}).topologicalClosure = ⊤) :
    (span ℂ {y : lp (woldSummandInt V) 2 | ∃ k : ℤ, ∃ x : H,
      y = (woldBilateralEquiv V ^ k)
        ((woldExtensionIncl V).comp J0 x)}).topologicalClosure = ⊤ := by
  let L := lp (woldSummandInt V) 2
  let ι : K →ₗᵢ[ℂ] L := woldExtensionIncl V
  let U : L ≃ₗᵢ[ℂ] L := woldBilateralEquiv V
  let J : H →ₗᵢ[ℂ] L := ι.comp J0
  let S : Set L := {y | ∃ k : ℤ, ∃ x : H, y = (U ^ k) (J x)}
  let O : Set K := {y | ∃ n : ℕ, ∃ x : H, y = (V.toContinuousLinearMap ^ n) (J0 x)}
  let N := (span ℂ S).topologicalClosure
  haveI : CompleteSpace N := topologicalClosure.completeSpace (span ℂ S)
  have horth : Nᗮ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [mem_bot]
    have hperp : ∀ k : ℤ, ∀ z : K, ⟪(y : L), (U ^ k) (ι z)⟫_ℂ = 0 := by
      intro k z
      let φ : K →L[ℂ] ℂ := (innerSL ℂ (y : L)).comp
        ((U ^ k).toLinearIsometry.toContinuousLinearMap.comp ι.toContinuousLinearMap)
      have hφ : ∀ w : K, φ w = ⟪(y : L), (U ^ k) (ι w)⟫_ℂ := by
        intro w
        simp only [φ, ContinuousLinearMap.comp_apply, coe_innerSL_apply,
          LinearIsometry.coe_toContinuousLinearMap,
          LinearIsometryEquiv.coe_toLinearIsometry]
      have hO : ∀ w ∈ O, φ w = 0 := by
        intro w hw
        rcases hw with ⟨n, x, rfl⟩
        have hmem : (U ^ k) (ι ((V.toContinuousLinearMap ^ n) (J0 x))) ∈ N := by
          rw [woldExtension_shift_orbit J0 V k n x]
          exact le_topologicalClosure _
            (subset_span ⟨k + (n : ℤ), x, rfl⟩)
        rw [hφ]
        exact inner_left_of_mem_orthogonal hmem hy
      rw [← hφ]
      exact clm_vanish_of_dense_span φ hmin hO z
    have hall := clm_vanish_of_dense_span (innerSL ℂ (y : L)) (woldExtension_minimal V)
      (by
        intro w hw
        rcases hw with ⟨k, z, rfl⟩
        rw [coe_innerSL_apply]
        exact hperp k z)
    exact inner_self_eq_zero.mp (by
      have hself := hall (y : L)
      rw [coe_innerSL_apply] at hself
      exact hself)
  exact (orthogonal_eq_bot_iff (K := N)).mp horth

/-- A contraction has a minimal unitary power dilation, obtained by extending its minimal
isometric dilation. -/
theorem exists_minimalUnitaryPowerDilation_data (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    ∃ M : HilbertSpaceModel.{u} ℂ, ∃ J : H →ₗᵢ[ℂ] M.Carrier,
      ∃ U : M.Carrier ≃ₗᵢ[ℂ] M.Carrier,
        (∀ n : ℕ, ∀ x : H, J.toContinuousLinearMap.adjoint ((U^[n]) (J x)) = (T ^ n) x) ∧
        (span ℂ {y : M.Carrier | ∃ k : ℤ, ∃ x : H, y = (U ^ k) (J x)}).topologicalClosure = ⊤ := by
  obtain ⟨M0, J0, V, hcoin, hmin⟩ := exists_minimalIsometricDilationData T hT
  let L := lp (woldSummandInt V) 2
  let ι : M0.Carrier →ₗᵢ[ℂ] L := woldExtensionIncl V
  let U : L ≃ₗᵢ[ℂ] L := woldBilateralEquiv V
  let J : H →ₗᵢ[ℂ] L := ι.comp J0
  refine ⟨{ Carrier := L }, J, U, ?_, ?_⟩
  · intro n x
    have hiter : (U^[n]) (J x) = (U ^ n) (J x) := equiv_iterate_pow_apply U n (J x)
    have horbit : (U ^ n) (J x) = ι ((V ^ n) (J0 x)) := by
      have hJ : J x = ι (J0 x) := by
        simp [J, ι, LinearIsometry.coe_comp]
      rw [hJ]
      exact woldExtension_pow V n (J0 x)
    rw [hiter, horbit]
    have hcomp : J.toContinuousLinearMap =
        ι.toContinuousLinearMap ∘L J0.toContinuousLinearMap := by
      ext z
      simp [J, ι, LinearIsometry.coe_comp, LinearIsometry.coe_toContinuousLinearMap,
        ContinuousLinearMap.comp_apply]
    have hadj : J.toContinuousLinearMap.adjoint =
        J0.toContinuousLinearMap.adjoint ∘L ι.toContinuousLinearMap.adjoint := by
      rw [hcomp, adjoint_comp]
    rw [hadj, ContinuousLinearMap.comp_apply]
    have hι : ι.toContinuousLinearMap.adjoint (ι ((V ^ n) (J0 x))) = (V ^ n) (J0 x) :=
      adjoint_isometry_leftInverse ι ((V ^ n) (J0 x))
    rw [hι, adjoint_isometry_pow T J0 V hcoin n (J0 x), adjoint_isometry_leftInverse J0 x]
  · exact minimalUnitary_of_minimalIsometric J0 V hmin

end CKMA
