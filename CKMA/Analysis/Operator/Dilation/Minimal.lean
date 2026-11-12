/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.InnerProductSpace.HilbertModel
public import CKMA.Analysis.Operator.Dilation.Schaffer
public import CKMA.Analysis.Operator.Dilation.Wold
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Minimal isometric dilation

Schäffer's isometry on `H ⊕ ℓ²(ℕ, H)` coextends a contraction, and the closed span of the forward
orbit of the embedded copy of `H` is a minimal isometric dilation. The argument follows
Sz.-Nagy–Foiaş–Bercovici–Kérchy, Chapter I, the passage from an isometric coextension to its
minimal part.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace
open ContinuousLinearMap Submodule

universe u

variable {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The forward orbit of the embedded copy of `H` under an isometry of `K`. -/
def isometricDilationOrbit (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) : Set K :=
  {y : K | ∃ n : ℕ, ∃ x : H, y = (V.toContinuousLinearMap ^ n) (J x)}

/-- The isometry preserves the forward orbit. -/
theorem isometricDilationOrbit_mapsTo (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) :
    Set.MapsTo (⇑V) (isometricDilationOrbit J V) (isometricDilationOrbit J V) := by
  intro y hy
  rcases hy with ⟨n, x, rfl⟩
  refine ⟨n + 1, x, ?_⟩
  rw [← LinearIsometry.coe_toContinuousLinearMap V]
  exact (clm_pow_succ'_apply V.toContinuousLinearMap n (J x)).symm

/-- The closed span of the forward orbit. -/
def isometricDilationSpace (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) : Submodule ℂ K :=
  (span ℂ (isometricDilationOrbit J V)).topologicalClosure

/-- The embedded copy of `H` lies in the closed forward orbit. -/
theorem mem_isometricDilationSpace_embed (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) (x : H) :
    J x ∈ isometricDilationSpace J V := by
  refine le_topologicalClosure _ (subset_span ?_)
  exact ⟨0, x, by simp [pow_zero]⟩

/-- The isometry preserves the closed forward orbit. -/
theorem isometricDilationSpace_mapsTo (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) {x : K}
    (hx : x ∈ isometricDilationSpace J V) : V x ∈ isometricDilationSpace J V := by
  have horbit : Set.MapsTo (⇑V) (isometricDilationOrbit J V) (isometricDilationOrbit J V) :=
    isometricDilationOrbit_mapsTo J V
  have hspan : Set.MapsTo (⇑V) (span ℂ (isometricDilationOrbit J V) : Set K)
      (span ℂ (isometricDilationOrbit J V) : Set K) := by
    intro y hy
    have hle : (span ℂ (isometricDilationOrbit J V)).map V.toLinearMap ≤
        span ℂ (isometricDilationOrbit J V) := by
      rw [LinearMap.map_span, span_le]
      intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      exact subset_span (horbit hw)
    exact hle (mem_map_of_mem hy)
  have hcl : Set.MapsTo (⇑V) (closure (span ℂ (isometricDilationOrbit J V) : Set K))
      (closure (span ℂ (isometricDilationOrbit J V) : Set K)) :=
    hspan.closure V.continuous
  rw [← topologicalClosure_coe] at hcl
  exact hcl hx

/-- Schäffer's isometry, or any isometry, restricted to the closed forward orbit. -/
def isometricDilationRestrictCLM (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) :
    isometricDilationSpace J V →L[ℂ] isometricDilationSpace J V :=
  V.toContinuousLinearMap.restrict fun x hx => by
    rw [LinearIsometry.coe_toContinuousLinearMap]
    exact isometricDilationSpace_mapsTo J V hx

/-- The restricted operator as a linear isometry of the closed forward orbit. -/
def isometricDilationIsometry (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) :
    isometricDilationSpace J V →ₗᵢ[ℂ] isometricDilationSpace J V where
  toLinearMap := (isometricDilationRestrictCLM J V).toLinearMap
  norm_map' y := by
    simp only [← norm_coe, isometricDilationRestrictCLM]
    exact V.norm_map (y : K)

/-- Evaluation of the restricted isometry. -/
theorem isometricDilationIsometry_apply (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (y : isometricDilationSpace J V) :
    isometricDilationIsometry J V y = isometricDilationRestrictCLM J V y :=
  rfl

/-- The original space, viewed inside the closed forward orbit. -/
def isometricDilationEmbedCLM (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) :
    H →L[ℂ] isometricDilationSpace J V :=
  J.toContinuousLinearMap.codRestrict (isometricDilationSpace J V) fun x => by
    rw [LinearIsometry.coe_toContinuousLinearMap]
    exact mem_isometricDilationSpace_embed J V x

/-- The embedding of the original space into the closed forward orbit. -/
def isometricDilationEmbed (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) :
    H →ₗᵢ[ℂ] isometricDilationSpace J V where
  toLinearMap := (isometricDilationEmbedCLM J V).toLinearMap
  norm_map' x := by
    simp only [← norm_coe, isometricDilationEmbedCLM]
    exact J.norm_map x

/-- Evaluation of the orbit embedding. -/
theorem isometricDilationEmbed_apply (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) (x : H) :
    isometricDilationEmbed J V x = isometricDilationEmbedCLM J V x :=
  rfl

/-- The orbit embedding agrees in `K` with the original embedding. -/
theorem coe_isometricDilationEmbed (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) (x : H) :
    (isometricDilationEmbed J V x : K) = J x := by
  simp [isometricDilationEmbed_apply, isometricDilationEmbedCLM,
    LinearIsometry.coe_toContinuousLinearMap]

/-- One application of the restricted isometry agrees in `K` with the original isometry. -/
theorem coe_isometricDilationIsometry (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (y : isometricDilationSpace J V) :
    (isometricDilationIsometry J V y : K) = V (y : K) := by
  simp [isometricDilationIsometry_apply, isometricDilationRestrictCLM,
    LinearIsometry.coe_toContinuousLinearMap]

/-- Powers of the restricted isometry agree in `K` with powers of the original isometry. -/
theorem coe_isometricDilationIsometry_pow (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) (n : ℕ)
    (y : isometricDilationSpace J V) :
    (((isometricDilationIsometry J V).toContinuousLinearMap ^ n) y : K) =
      (V.toContinuousLinearMap ^ n) (y : K) := by
  induction n with
  | zero =>
    simp [pow_zero]
  | succ n ih =>
    rw [clm_pow_succ'_apply, clm_pow_succ'_apply]
    simp only [LinearIsometry.coe_toContinuousLinearMap, isometricDilationIsometry_apply,
      isometricDilationRestrictCLM]
    rw [ContinuousLinearMap.coe_restrict_apply, ih, LinearIsometry.coe_toContinuousLinearMap]

variable [CompleteSpace H] [CompleteSpace K]

/-- The closed forward orbit is a Hilbert space. -/
instance completeSpace_isometricDilationSpace (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) :
    CompleteSpace (isometricDilationSpace J V) :=
  topologicalClosure.completeSpace (span ℂ (isometricDilationOrbit J V))

/-- The adjoint of the orbit embedding is the original adjoint, read in `K`. -/
theorem isometricDilationEmbed_adjoint_apply (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (y : isometricDilationSpace J V) :
    (isometricDilationEmbed J V).toContinuousLinearMap.adjoint y =
      J.toContinuousLinearMap.adjoint (y : K) := by
  have hcomp : (isometricDilationSpace J V).subtypeL ∘L
      (isometricDilationEmbed J V).toContinuousLinearMap = J.toContinuousLinearMap := by
    ext x
    rw [ContinuousLinearMap.comp_apply, subtypeL_apply, LinearIsometry.coe_toContinuousLinearMap,
      coe_isometricDilationEmbed, LinearIsometry.coe_toContinuousLinearMap]
  have hadj := congrArg ContinuousLinearMap.adjoint hcomp
  rw [adjoint_comp] at hadj
  have happly := congrArg (fun T : K →L[ℂ] H => T (y : K)) hadj
  rw [ContinuousLinearMap.comp_apply, adjoint_subtypeL,
    orthogonalProjectionOnto_mem_subspace_eq_self] at happly
  exact happly

/-- Co-invariance passes from `K` to the closed forward orbit. -/
theorem isometricDilation_coinvariant (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y))
    (y : isometricDilationSpace J V) :
    (isometricDilationEmbed J V).toContinuousLinearMap.adjoint
        (isometricDilationIsometry J V y) =
      T ((isometricDilationEmbed J V).toContinuousLinearMap.adjoint y) := by
  rw [isometricDilationEmbed_adjoint_apply, isometricDilationEmbed_adjoint_apply]
  rw [coe_isometricDilationIsometry]
  exact hcoin (y : K)

omit [CompleteSpace H] in
set_option linter.style.haveILetI false in
/-- The closed forward orbit is minimal: the embedded orbit is dense in it. -/
theorem isometricDilation_minimal (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) :
    (span ℂ {y : isometricDilationSpace J V | ∃ n : ℕ, ∃ x : H,
      y = ((isometricDilationIsometry J V).toContinuousLinearMap ^ n)
        (isometricDilationEmbed J V x)}).topologicalClosure = ⊤ := by
  set J1 := isometricDilationEmbed J V
  set V1 := isometricDilationIsometry J V
  set S : Set (isometricDilationSpace J V) :=
    {y | ∃ n : ℕ, ∃ x : H, y = (V1.toContinuousLinearMap ^ n) (J1 x)}
  set N := (span ℂ S).topologicalClosure
  haveI : CompleteSpace N := topologicalClosure.completeSpace (span ℂ S)
  have horth : Nᗮ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [mem_bot]
    have horbit : ∀ n : ℕ, ∀ x : H,
        ⟪(y : K), (V.toContinuousLinearMap ^ n) (J x)⟫_ℂ = 0 := by
      intro n x
      have hu : (V1.toContinuousLinearMap ^ n) (J1 x) ∈ N :=
        le_topologicalClosure _ (subset_span ⟨n, x, rfl⟩)
      have h0 := inner_left_of_mem_orthogonal hu hy
      rw [coe_inner] at h0
      rw [coe_isometricDilationIsometry_pow, coe_isometricDilationEmbed] at h0
      exact h0
    have horth_span : ∀ u ∈ span ℂ (isometricDilationOrbit J V),
        ⟪(y : K), u⟫_ℂ = 0 := by
      intro u hu
      refine span_induction ?_ ?_ ?_ ?_ hu
      · intro z hz
        rcases hz with ⟨n, x, rfl⟩
        exact horbit n x
      · simp
      · intro u v _ _ ihu ihv
        rw [inner_add_right, ihu, ihv, add_zero]
      · intro c u _ ihu
        rw [inner_smul_right, ihu, mul_zero]
    have hclosed : IsClosed {u : K | ⟪(y : K), u⟫_ℂ = 0} :=
      isClosed_eq (innerSL ℂ (y : K)).continuous continuous_const
    have hspan : (span ℂ (isometricDilationOrbit J V) : Set K) ⊆
        {u : K | ⟪(y : K), u⟫_ℂ = 0} :=
      fun u hu => horth_span u hu
    have hcl : (isometricDilationSpace J V : Set K) ⊆ {u : K | ⟪(y : K), u⟫_ℂ = 0} := by
      unfold isometricDilationSpace
      rw [topologicalClosure_coe]
      exact closure_minimal hspan hclosed
    exact Subtype.ext (inner_self_eq_zero.mp (hcl (SetLike.coe_mem y)))
  exact (orthogonal_eq_bot_iff (K := N)).mp horth

variable (T : H →L[ℂ] H)

/-- A contraction has a minimal isometric dilation on the closed forward orbit of Schäffer's
coextension. -/
theorem exists_minimalIsometricDilationData (hT : ‖T‖ ≤ 1) :
    ∃ M : HilbertSpaceModel.{u} ℂ, ∃ J : H →ₗᵢ[ℂ] M.Carrier,
      ∃ V : M.Carrier →ₗᵢ[ℂ] M.Carrier,
        (∀ y : M.Carrier, J.toContinuousLinearMap.adjoint (V y) =
          T (J.toContinuousLinearMap.adjoint y)) ∧
        (span ℂ {y : M.Carrier | ∃ n : ℕ, ∃ x : H,
          y = (V.toContinuousLinearMap ^ n) (J x)}).topologicalClosure = ⊤ := by
  let J0 : H →ₗᵢ[ℂ] SchafferSpace H := schafferEmbed
  let V0 : SchafferSpace H →ₗᵢ[ℂ] SchafferSpace H := schafferIsometry T hT
  refine ⟨{ Carrier := ↥(isometricDilationSpace J0 V0) },
    isometricDilationEmbed J0 V0, isometricDilationIsometry J0 V0, ?_, ?_⟩
  · intro y
    exact isometricDilation_coinvariant T J0 V0 (schaffer_coinvariant T hT) y
  · exact isometricDilation_minimal J0 V0

end CKMA
