/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import CKMA.Analysis.InnerProductSpace.HilbertModel
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Operator.Extend
public import CKMA.Analysis.CStarAlgebra.Representation.Faithful

/-!
# Cyclic C-star representations and faithful operator representations

Cyclicity means density of the algebra orbit of one vector; that orbit is already a linear
subspace. A represented functional has the form `a ↦ ⟪Ω, π(a)Ω⟫`, with Mathlib's inner product
linear in its second variable. Cyclic realizations of one functional are compared by a unique
unitary preserving their cyclic vectors and intertwining the actions.

The faithful representation statement includes nonunital C-star algebras and norm-closed image.
Its Hilbert carrier is allowed in a larger universe for the sum over states.
Sources: GAPS 23.9 and 23.10.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace
open ContinuousLinearMap Set

universe u

/-- A complex Hilbert-space model with an explicitly chosen carrier universe. -/
abbrev ComplexHilbertSpace := HilbertSpaceModel.{u} ℂ

variable {A H K : Type*} [NonUnitalCStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A vector is cyclic if its algebra orbit is dense. Since the orbit is a linear subspace,
no separate linear span is necessary. -/
def IsCyclicVector (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (Ω : H) : Prop :=
  DenseRange (fun a ↦ π a Ω)

/-- The vector realizes `φ`, using Mathlib's inner product, which is linear in the second variable.
  -/
def RealizesFunctional (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (Ω : H) (φ : A → ℂ) : Prop :=
  ∀ a, φ a = ⟪Ω, π a Ω⟫_ℂ

/-- The linear orbit map `a ↦ π a Ω`. -/
def cyclicOrbit (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (Ω : H) : A →ₗ[ℂ] H where
  toFun a := π a Ω
  map_add' a b := by simp [map_add]
  map_smul' c a := by simp [map_smul]

@[simp]
theorem cyclicOrbit_apply (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (Ω : H) (a : A) :
    cyclicOrbit π Ω a = π a Ω :=
  rfl

/-- Orbit vectors of a represented functional satisfy `⟪π a Ω, π b Ω⟫ = φ (star a * b)`. -/
theorem inner_cyclicOrbit_star_mul {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} {Ω : H} {φ : A → ℂ}
    (hφ : RealizesFunctional π Ω φ) (a b : A) :
    ⟪π a Ω, π b Ω⟫_ℂ = φ (star a * b) := by
  calc
    ⟪π a Ω, π b Ω⟫_ℂ = inner ℂ Ω (adjoint (π a) (π b Ω)) :=
      (adjoint_inner_right (π a) Ω (π b Ω)).symm
    _ = inner ℂ Ω (star (π a) (π b Ω)) := by rw [← star_eq_adjoint]
    _ = inner ℂ Ω (π (star a) (π b Ω)) := by rw [← map_star π a]
    _ = inner ℂ Ω ((π (star a) * π b) Ω) := by rw [← mul_apply_eq_comp]
    _ = inner ℂ Ω (π (star a * b) Ω) := by rw [← map_mul π (star a) b]
    _ = φ (star a * b) := (hφ _).symm

/-- A represented functional satisfies `⟪π a Ω, Ω⟫ = φ (star a)`. -/
theorem inner_cyclicOrbit_star {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} {Ω : H} {φ : A → ℂ}
    (hφ : RealizesFunctional π Ω φ) (a : A) : ⟪π a Ω, Ω⟫_ℂ = φ (star a) := by
  calc
    ⟪π a Ω, Ω⟫_ℂ = inner ℂ Ω (adjoint (π a) Ω) :=
      (adjoint_inner_right (π a) Ω Ω).symm
    _ = inner ℂ Ω (star (π a) Ω) := by rw [← star_eq_adjoint]
    _ = inner ℂ Ω (π (star a) Ω) := by rw [← map_star π a]
    _ = φ (star a) := (hφ _).symm

/-- Cyclic orbits realizing one functional have the same inner products. -/
theorem inner_cyclicOrbit_eq {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} {ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)}
    {Ω : H} {Ω' : K} {φ : A → ℂ} (hφπ : RealizesFunctional π Ω φ)
    (hφρ : RealizesFunctional ρ Ω' φ) (a b : A) :
    ⟪π a Ω, π b Ω⟫_ℂ = ⟪ρ a Ω', ρ b Ω'⟫_ℂ := by
  rw [inner_cyclicOrbit_star_mul hφπ, inner_cyclicOrbit_star_mul hφρ]

/-- Corresponding orbit vectors of one functional have equal norms. -/
theorem norm_cyclicOrbit_eq {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} {ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)}
    {Ω : H} {Ω' : K} {φ : A → ℂ} (hφπ : RealizesFunctional π Ω φ)
    (hφρ : RealizesFunctional ρ Ω' φ) (a : A) : ‖ρ a Ω'‖ = ‖π a Ω‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) (ρ a Ω'), norm_eq_sqrt_re_inner (𝕜 := ℂ) (π a Ω),
    inner_cyclicOrbit_eq hφπ hφρ a a]

/-- The linear isometry extending `π a Ω ↦ ρ a Ω'` along the dense cyclic orbit. -/
private def cyclicRepresentationIsometry (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (Ω : H) (Ω' : K) (hπ : IsCyclicVector π Ω)
    (φ : A → ℂ) (hφπ : RealizesFunctional π Ω φ) (hφρ : RealizesFunctional ρ Ω' φ) :
    H →ₗᵢ[ℂ] K :=
  (cyclicOrbit ρ Ω').extendOfIsometry (e := cyclicOrbit π Ω) hπ
    (fun a => norm_cyclicOrbit_eq hφπ hφρ a)

@[simp]
private theorem cyclicRepresentationIsometry_apply (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (Ω : H) (Ω' : K) (hπ : IsCyclicVector π Ω)
    (φ : A → ℂ) (hφπ : RealizesFunctional π Ω φ) (hφρ : RealizesFunctional ρ Ω' φ)
    (a : A) :
    cyclicRepresentationIsometry π ρ Ω Ω' hπ φ hφπ hφρ (π a Ω) = ρ a Ω' := by
  simpa [cyclicRepresentationIsometry] using
    LinearMap.extendOfIsometry_eq (e := cyclicOrbit π Ω) (cyclicOrbit ρ Ω') hπ
      (fun b => norm_cyclicOrbit_eq hφπ hφρ b) a

/-- The orbit isometry is surjective because its range is closed and contains a dense orbit. -/
private theorem cyclicRepresentationIsometry_surjective (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (Ω : H) (Ω' : K) (hπ : IsCyclicVector π Ω)
    (hρ : IsCyclicVector ρ Ω') (φ : A → ℂ) (hφπ : RealizesFunctional π Ω φ)
    (hφρ : RealizesFunctional ρ Ω' φ) :
    Function.Surjective
      (cyclicRepresentationIsometry π ρ Ω Ω' hπ φ hφπ hφρ) := by
  let f := cyclicRepresentationIsometry π ρ Ω Ω' hπ φ hφπ hφρ
  rw [← range_eq_univ]
  have hd : Dense (range f) := by
    refine Dense.mono ?_ hρ
    rintro _ ⟨a, rfl⟩
    exact ⟨π a Ω, cyclicRepresentationIsometry_apply π ρ Ω Ω' hπ φ hφπ hφρ a⟩
  have hc : IsClosed (range f) :=
    f.antilipschitzWith.isClosed_range f.isometry.uniformContinuous
  exact hc.closure_eq.symm.trans hd.closure_eq

/-- The unitary extension of `π a Ω ↦ ρ a Ω'`. -/
private def cyclicRepresentationEquiv (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (Ω : H) (Ω' : K) (hπ : IsCyclicVector π Ω)
    (hρ : IsCyclicVector ρ Ω') (φ : A → ℂ) (hφπ : RealizesFunctional π Ω φ)
    (hφρ : RealizesFunctional ρ Ω' φ) : H ≃ₗᵢ[ℂ] K :=
  LinearIsometryEquiv.ofSurjective
    (cyclicRepresentationIsometry π ρ Ω Ω' hπ φ hφπ hφρ)
    (cyclicRepresentationIsometry_surjective π ρ Ω Ω' hπ hρ φ hφπ hφρ)

@[simp]
private theorem cyclicRepresentationEquiv_apply (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (Ω : H) (Ω' : K) (hπ : IsCyclicVector π Ω)
    (hρ : IsCyclicVector ρ Ω') (φ : A → ℂ) (hφπ : RealizesFunctional π Ω φ)
    (hφρ : RealizesFunctional ρ Ω' φ) (a : A) :
    cyclicRepresentationEquiv π ρ Ω Ω' hπ hρ φ hφπ hφρ (π a Ω) = ρ a Ω' := by
  rw [cyclicRepresentationEquiv, LinearIsometryEquiv.coe_ofSurjective,
    cyclicRepresentationIsometry_apply]

/-- An orbit-preserving unitary intertwines the representations on the whole space. -/
private theorem cyclicRepresentation_intertwining {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    {ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)} {Ω : H} {Ω' : K} (hπ : IsCyclicVector π Ω)
    (U : H ≃ₗᵢ[ℂ] K) (hU : ∀ a, U (π a Ω) = ρ a Ω') (a : A) (x : H) :
    U (π a x) = ρ a (U x) := by
  have hcomp : (fun y => U (π a y)) ∘ (fun b => π b Ω) =
      (fun y => ρ a (U y)) ∘ (fun b => π b Ω) := by
    funext b
    calc
      U (π a (π b Ω)) = U ((π a * π b) Ω) := by rw [← mul_apply_eq_comp]
      _ = U (π (a * b) Ω) := by rw [← map_mul π a b]
      _ = ρ (a * b) Ω' := hU (a * b)
      _ = (ρ a * ρ b) Ω' := by rw [map_mul ρ a b]
      _ = ρ a (ρ b Ω') := by rw [mul_apply_eq_comp]
      _ = ρ a (U (π b Ω)) := by rw [← hU b]
  have hagree := DenseRange.equalizer (f := fun b => π b Ω) hπ
    (U.continuous.comp (π a).continuous) ((ρ a).continuous.comp U.continuous) hcomp
  exact congr_fun hagree x

/-- An orbit-preserving unitary sends one cyclic vector to the other. -/
private theorem cyclicRepresentation_map_cyclicVector {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    {ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)} {Ω : H} {Ω' : K} {φ : A → ℂ}
    (hρ : IsCyclicVector ρ Ω') (hφπ : RealizesFunctional π Ω φ)
    (hφρ : RealizesFunctional ρ Ω' φ) (U : H ≃ₗᵢ[ℂ] K)
    (hU : ∀ a, U (π a Ω) = ρ a Ω') : U Ω = Ω' := by
  apply ext_inner_left ℂ
  intro v
  have hcomp : (fun w : K => ⟪w, U Ω⟫_ℂ) ∘ (fun a => ρ a Ω') =
      (fun w : K => ⟪w, Ω'⟫_ℂ) ∘ (fun a => ρ a Ω') := by
    funext a
    calc
      ⟪ρ a Ω', U Ω⟫_ℂ = ⟪U (π a Ω), U Ω⟫_ℂ := by rw [← hU a]
      _ = ⟪π a Ω, Ω⟫_ℂ := by rw [LinearIsometryEquiv.inner_map_map]
      _ = φ (star a) := inner_cyclicOrbit_star hφπ a
      _ = ⟪ρ a Ω', Ω'⟫_ℂ := (inner_cyclicOrbit_star hφρ a).symm
  have hcont : Continuous fun w : K => ⟪w, U Ω⟫_ℂ :=
    continuous_id.inner continuous_const
  have hcont' : Continuous fun w : K => ⟪w, Ω'⟫_ℂ :=
    continuous_id.inner continuous_const
  exact congr_fun (DenseRange.equalizer (f := fun a => ρ a Ω') hρ hcont hcont' hcomp) v

/-- Two unitaries that intertwine the actions and fix the cyclic vector agree everywhere. -/
private theorem cyclicRepresentation_unique {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    {ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)} {Ω : H} {Ω' : K} (hπ : IsCyclicVector π Ω)
    (U V : H ≃ₗᵢ[ℂ] K) (hUΩ : U Ω = Ω') (hVΩ : V Ω = Ω')
    (hU : ∀ a x, U (π a x) = ρ a (U x)) (hV : ∀ a x, V (π a x) = ρ a (V x)) :
    U = V := by
  have hcomp : (U : H → K) ∘ (fun a => π a Ω) = (V : H → K) ∘ (fun a => π a Ω) := by
    funext a
    rw [Function.comp_apply, Function.comp_apply, hU a Ω, hV a Ω, hUΩ, hVΩ]
  have hagree := DenseRange.equalizer (f := fun a => π a Ω) hπ U.continuous V.continuous hcomp
  ext x
  exact congr_fun hagree x

/-- **23.9**, uniqueness clause: two cyclic realizations of the same functional have a unique
unitary intertwiner preserving their cyclic vectors. Existence for nonunital algebras is separate.
  -/
theorem existsUnique_cyclicRepresentation_equiv
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K))
    (Ω : H) (Ω' : K) (hπ : IsCyclicVector π Ω) (hρ : IsCyclicVector ρ Ω')
    (φ : A → ℂ) (hφπ : RealizesFunctional π Ω φ) (hφρ : RealizesFunctional ρ Ω' φ) :
    ∃! U : H ≃ₗᵢ[ℂ] K, U Ω = Ω' ∧ ∀ a x, U (π a x) = ρ a (U x) := by
  let U := cyclicRepresentationEquiv π ρ Ω Ω' hπ hρ φ hφπ hφρ
  refine ⟨U, ⟨?_, ?_⟩, ?_⟩
  · exact cyclicRepresentation_map_cyclicVector hρ hφπ hφρ U
      (cyclicRepresentationEquiv_apply π ρ Ω Ω' hπ hρ φ hφπ hφρ)
  · intro a x
    exact cyclicRepresentation_intertwining hπ U
      (cyclicRepresentationEquiv_apply π ρ Ω Ω' hπ hρ φ hφπ hφρ) a x
  · intro V hV
    exact cyclicRepresentation_unique hπ V U hV.1
      (cyclicRepresentation_map_cyclicVector hρ hφπ hφρ U
        (cyclicRepresentationEquiv_apply π ρ Ω Ω' hπ hρ φ hφπ hφρ))
      hV.2
      (fun a x => cyclicRepresentation_intertwining hπ U
        (cyclicRepresentationEquiv_apply π ρ Ω Ω' hπ hρ φ hφπ hφρ) a x)

/-- **23.10**: a C*-algebra, including a nonunital one, has an isometric operator representation
with closed image. The larger universe permits the Hilbert sum over all states. -/
theorem exists_isometric_representation (A : Type u) [NonUnitalCStarAlgebra A] :
    ∃ H : ComplexHilbertSpace.{u + 1},
      ∃ π : A →⋆ₙₐ[ℂ] (H.Carrier →L[ℂ] H.Carrier), Isometry π ∧ IsClosed (Set.range π) :=
  exists_isometric_representation_gns (A := A)

end CKMA
