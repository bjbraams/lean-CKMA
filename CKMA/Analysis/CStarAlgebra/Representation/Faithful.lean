/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.InnerProductSpace.HilbertModel
public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Normed.Algebra.Unitization
public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Isometric Gelfand–Naimark representations

A unital complex C*-algebra acts on the `ℓ²` sum of one GNS Hilbert space for each algebra
element. The state at `b` is normalized and sends `star b * b` to `‖b‖ ^ 2`, so the diagonal
representation is isometric. Its range is norm-closed because the domain is complete.

The sum is indexed by a universe lift of the algebra, so the carrier lies in the next universe.
A non-unital C*-algebra is handled by the same construction on its unitization: the inclusion
into the unitization is an isometric non-unital star homomorphism, and the restriction of an
isometry along it remains an isometry with closed range.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace ComplexOrder
open ContinuousLinearMap Set Unitization

universe u

variable {A : Type u}

/-- A normalized positive functional sending a positive element to its norm. -/
theorem exists_state_of_nonneg [CStarAlgebra A] [Nontrivial A] [PartialOrder A]
    [StarOrderedRing A] {c : A} (hc : 0 ≤ c) :
    ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 ∧ f c = ‖c‖ := by
  have hc_sa : IsSelfAdjoint c := hc.isSelfAdjoint
  have : IsStarNormal c := hc_sa.isStarNormal
  have hc_real : ‖c‖ ∈ spectrum ℝ c := CStarAlgebra.norm_mem_spectrum_of_nonneg c hc
  have := IsStarNormal.instContinuousFunctionalCalculus (A := A)
  have hc_cx : (‖c‖ : ℂ) ∈ spectrum ℂ c :=
    (IsSelfAdjoint.coe_mem_spectrum_complex (a := c) (x := ‖c‖) hc_sa).2 hc_real
  let S := StarAlgebra.elemental ℂ c
  have : IsClosed (S : Set A) := StarAlgebra.elemental.isClosed ℂ c
  have : Nontrivial S := nontrivial_of_ne (0 : S) 1 fun h =>
    zero_ne_one (congrArg Subtype.val h)
  let cS : S := ⟨c, StarAlgebra.elemental.self_mem ℂ c⟩
  have hcS : (‖c‖ : ℂ) ∈ spectrum ℂ cS := by
    rw [StarSubalgebra.spectrum_eq (S := S)]
    simpa [cS] using hc_cx
  obtain ⟨psi, hpsi⟩ :=
    (WeakDual.CharacterSpace.mem_spectrum_iff_exists (a := cS)).1 hcS
  let p : Submodule ℂ A := S.toSubalgebra.toSubmodule
  let e : p ≃ₗ[ℂ] S := S.toSubalgebra.toSubmoduleEquiv
  let fLin : p →ₗ[ℂ] ℂ :=
    { toFun x := psi (e x)
      map_add' x y := by rw [map_add e, map_add psi]
      map_smul' r x := by rw [map_smul e, map_smul psi, RingHom.id_apply] }
  have hbound : ∀ x : p, ‖fLin x‖ ≤ 1 * ‖x‖ := by
    intro x
    rw [one_mul]
    have hle :=
      AlgHom.norm_apply_le_self (WeakDual.CharacterSpace.toAlgHom psi) (e x)
    have hnorm : ‖e x‖ = ‖x‖ := by
      change ‖(x : A)‖ = ‖x‖
      exact (Submodule.norm_coe x).symm
    simpa [fLin, hnorm] using hle
  let f : p →L[ℂ] ℂ := fLin.mkContinuous 1 hbound
  have hf_le : ‖f‖ ≤ 1 := LinearMap.mkContinuous_norm_le fLin zero_le_one hbound
  let u : p := ⟨(1 : A), Subalgebra.one_mem S.toSubalgebra⟩
  have hfu : f u = 1 := by
    change psi (e u) = 1
    have hu : e u = 1 := by
      ext
      rfl
    rw [hu, map_one]
  have hnu : ‖u‖ = 1 := by
    rw [← Submodule.norm_coe]
    simp [u]
  have hf_ge : 1 ≤ ‖f‖ := by
    have hle := f.le_opNorm u
    rw [hfu, hnu, mul_one] at hle
    simpa using hle
  have hf_norm : ‖f‖ = 1 := le_antisymm hf_le hf_ge
  obtain ⟨g, hg, hgn⟩ := exists_extension_norm_eq p f
  have hg1 : g 1 = 1 := by simpa [u, hfu] using hg u
  let cP : p := ⟨c, StarAlgebra.elemental.self_mem ℂ c⟩
  have hfc : f cP = (‖c‖ : ℂ) := by
    change psi (e cP) = (‖c‖ : ℂ)
    have hcP : e cP = cS := by
      ext
      rfl
    rw [hcP, hpsi]
  have hgc : g c = (‖c‖ : ℂ) := by simpa [cP, hfc] using hg cP
  have hg_eq : ‖g‖ = g 1 := by simp [hgn, hf_norm, hg1]
  have hmono : Monotone g :=
    ContinuousLinearMap.monotone_iff_opNorm_eq_map_one.mpr hg_eq
  have hpos : ∀ x, 0 ≤ x → 0 ≤ g x := (monotone_iff_map_nonneg g).1 hmono
  refine ⟨(PositiveContinuousLinearMap.mk₀ g hpos).toPositiveLinearMap, ?_, ?_⟩
  · change g 1 = 1
    exact hg1
  · change g c = (‖c‖ : ℂ)
    exact hgc

/-- A normalized positive functional with `f (star b * b) = ‖b‖ ^ 2`. -/
theorem exists_state_normSq [CStarAlgebra A] [Nontrivial A] [PartialOrder A]
    [StarOrderedRing A] (b : A) :
    ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 ∧ f (star b * b) = ‖b‖ ^ 2 := by
  obtain ⟨f, hf1, hfc⟩ := exists_state_of_nonneg (star_mul_self_nonneg b)
  refine ⟨f, hf1, ?_⟩
  rw [hfc, CStarRing.norm_star_mul_self, ← pow_two]
  exact Complex.ofReal_pow ‖b‖ 2

/-- Chosen state sending `star b * b` to `‖b‖ ^ 2`. -/
def stateNormSq [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A] (b : A) :
    A →ₚ[ℂ] ℂ :=
  Classical.choose (exists_state_normSq (A := A) b)

/-- The chosen state is normalized. -/
theorem stateNormSq_one [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
    (b : A) :
    stateNormSq (A := A) b 1 = 1 :=
  (Classical.choose_spec (exists_state_normSq (A := A) b)).1

/-- The chosen state reproduces `‖b‖ ^ 2` on `star b * b`. -/
theorem stateNormSq_star_mul_self [CStarAlgebra A] [Nontrivial A] [PartialOrder A]
    [StarOrderedRing A] (b : A) :
    stateNormSq (A := A) b (star b * b) = ‖b‖ ^ 2 :=
  (Classical.choose_spec (exists_state_normSq (A := A) b)).2

/-- The image of the unit in the GNS space of a normalized positive functional is a unit vector. -/
theorem norm_gnsCyclic [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (f : A →ₚ[ℂ] ℂ)
    (hf : f 1 = 1) : ‖(f.toPreGNS (1 : A) : f.GNS)‖ = 1 := by
  rw [UniformSpace.Completion.norm_coe]
  have hsq : (‖f.toPreGNS (1 : A)‖ ^ 2 : ℂ) = 1 := by
    rw [PositiveLinearMap.preGNS_norm_sq]
    simp [PositiveLinearMap.ofPreGNS_toPreGNS, star_one, hf]
  have hreal : ‖f.toPreGNS (1 : A)‖ ^ 2 = 1 := by exact_mod_cast hsq
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (hreal.trans (one_pow 2).symm)

/-- Left multiplication by `a` on the cyclic vector has norm `‖a‖` when `f (star a * a) = ‖a‖ ^ 2`.
  -/
theorem norm_gns_apply_cyclic [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (f : A →ₚ[ℂ] ℂ) (a : A) (hfa : f (star a * a) = ‖a‖ ^ 2) :
    ‖f.gnsNonUnitalStarAlgHom a (f.toPreGNS (1 : A) : f.GNS)‖ = ‖a‖ := by
  have happly :
      f.gnsNonUnitalStarAlgHom a (f.toPreGNS (1 : A) : f.GNS) = (f.toPreGNS a : f.GNS) := by
    rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe,
      PositiveLinearMap.leftMulMapPreGNS_apply]
    simp [PositiveLinearMap.ofPreGNS_toPreGNS, mul_one]
  rw [happly, UniformSpace.Completion.norm_coe]
  have hsq : (‖f.toPreGNS a‖ ^ 2 : ℂ) = (‖a‖ ^ 2 : ℂ) := by
    rw [PositiveLinearMap.preGNS_norm_sq]
    simpa [PositiveLinearMap.ofPreGNS_toPreGNS] using hfa
  have hreal : ‖f.toPreGNS a‖ ^ 2 = ‖a‖ ^ 2 := by exact_mod_cast hsq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hreal

section

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)]

/-- Evaluation of a diagonal `lp` operator on a coordinate. -/
theorem lp_mapCLM_apply_apply (T : ∀ i, E i →L[ℂ] E i) {K : ℝ} (hK : 0 ≤ K)
    (hT : ∀ i, ‖T i‖ ≤ K) (x : lp E 2) (i : ι) :
    lp.mapCLM 2 T hK hT x i = T i (x i) := by
  simp [lp.mapCLM, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]

variable [∀ i, CompleteSpace (E i)]

/-- The diagonal non-unital star representation on an `ℓ²` sum. -/
def lpDiagonal [NonUnitalCStarAlgebra A] (pi : ∀ i, A →⋆ₙₐ[ℂ] (E i →L[ℂ] E i)) :
    A →⋆ₙₐ[ℂ] (lp E 2 →L[ℂ] lp E 2) where
  toFun a :=
    lp.mapCLM 2 (fun i => pi i a) (norm_nonneg a)
      (fun i => NonUnitalStarAlgHom.norm_apply_le (pi i) a)
  map_smul' r a := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    simp
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    simp
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    simp
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    simp
  map_star' a := by
    rw [star_eq_adjoint]
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    refine tsum_congr fun i => ?_
    rw [lp_mapCLM_apply_apply, lp_mapCLM_apply_apply, map_star (pi i) a,
      ContinuousLinearMap.star_eq_adjoint]
    exact ContinuousLinearMap.adjoint_inner_left (pi i a) (y i) (x i)

/-- Coordinates of a diagonal operator. -/
@[simp]
theorem lpDiagonal_apply_apply [NonUnitalCStarAlgebra A]
    (pi : ∀ i, A →⋆ₙₐ[ℂ] (E i →L[ℂ] E i)) (a : A) (x : lp E 2)
    (i : ι) : lpDiagonal pi a x i = pi i a (x i) := by
  simp [lpDiagonal]

/-- Each diagonal operator is contractive. -/
theorem opNorm_lpDiagonal_le [NonUnitalCStarAlgebra A]
    (pi : ∀ i, A →⋆ₙₐ[ℂ] (E i →L[ℂ] E i)) (a : A) :
    ‖lpDiagonal pi a‖ ≤ ‖a‖ := by
  simpa [lpDiagonal] using
    lp.norm_mapCLM_le 2 (fun i => pi i a) (norm_nonneg a)
      (fun i => NonUnitalStarAlgHom.norm_apply_le (pi i) a)

/-- A standard basis vector is sent to the corresponding basis vector of the image. -/
theorem lpDiagonal_single [NonUnitalCStarAlgebra A] [DecidableEq ι]
    (pi : ∀ i, A →⋆ₙₐ[ℂ] (E i →L[ℂ] E i)) (a : A) (i : ι)
    (v : E i) : lpDiagonal pi a (lp.single 2 i v) = lp.single 2 i (pi i a v) := by
  apply lp.ext
  funext j
  by_cases hji : j = i
  · subst hji
    simp [lpDiagonal_apply_apply, lp.single_apply, Pi.single_eq_same]
  · simp [lpDiagonal_apply_apply, lp.single_apply, Pi.single_eq_of_ne hji, map_zero]

/-- A diagonal representation that attains `‖a‖` on some unit vector of each element is isometric.
  -/
theorem lpDiagonal_isometry [NonUnitalCStarAlgebra A]
    (pi : ∀ i, A →⋆ₙₐ[ℂ] (E i →L[ℂ] E i))
    (h : ∀ a, ∃ i, ∃ v : E i, ‖v‖ = 1 ∧ ‖pi i a v‖ = ‖a‖) : Isometry (lpDiagonal pi) := by
  have : DecidableEq ι := Classical.decEq ι
  refine AddMonoidHomClass.isometry_of_norm (lpDiagonal pi) fun a => ?_
  apply le_antisymm (opNorm_lpDiagonal_le pi a)
  obtain ⟨i, v, hv, hpi⟩ := h a
  have hs := lpDiagonal_single pi a i v
  have hle := (lpDiagonal pi a).le_opNorm (lp.single 2 i v)
  rw [hs] at hle
  have htwo : (0 : ENNReal) < 2 := zero_lt_two
  have hn1 : ‖lp.single 2 i v‖ = 1 := by
    rw [lp.norm_single htwo, hv]
  have hn2 : ‖lp.single 2 i (pi i a v)‖ = ‖a‖ := by
    rw [lp.norm_single htwo, hpi]
  rw [hn1, hn2, mul_one] at hle
  exact hle

end

/-- An isometric operator representation of a unital C*-algebra on an `ℓ²` sum of GNS spaces.
The index is a universe lift of the algebra, so the carrier has type `Type (u + 1)`. -/
theorem exists_isometric_representation_unital [CStarAlgebra A] [Nontrivial A] [PartialOrder A]
    [StarOrderedRing A] :
    ∃ H : HilbertSpaceModel.{u + 1} ℂ,
      ∃ pi : A →⋆ₙₐ[ℂ] (H.Carrier →L[ℂ] H.Carrier),
        Isometry pi ∧ IsClosed (Set.range pi) := by
  let phi : A → A →ₚ[ℂ] ℂ := fun b => stateNormSq (A := A) b
  let G : ULift.{u + 1} A → Type u := fun i => (phi i.down).GNS
  let rep : ∀ i, A →⋆ₙₐ[ℂ] (G i →L[ℂ] G i) := fun i => (phi i.down).gnsNonUnitalStarAlgHom
  have hdiag : Isometry (lpDiagonal rep) := by
    refine lpDiagonal_isometry rep fun a => ?_
    refine ⟨ULift.up a, (phi a).toPreGNS (1 : A), ?_, ?_⟩
    · exact norm_gnsCyclic (phi a) (stateNormSq_one (A := A) a)
    · exact norm_gns_apply_cyclic (phi a) a
        (stateNormSq_star_mul_self (A := A) a)
  exact ⟨{ Carrier := lp G 2 }, lpDiagonal rep, hdiag, hdiag.isClosedEmbedding.isClosed_range⟩

/-- **Gelfand–Naimark.** A C*-algebra has an isometric non-unital star representation on a
Hilbert space, with norm-closed range. -/
theorem exists_isometric_representation_gns [NonUnitalCStarAlgebra A] :
    ∃ H : HilbertSpaceModel.{u + 1} ℂ,
      ∃ pi : A →⋆ₙₐ[ℂ] (H.Carrier →L[ℂ] H.Carrier),
        Isometry pi ∧ IsClosed (Set.range pi) := by
  let B := Unitization ℂ A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  have : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  have : Nontrivial B := NormOneClass.nontrivial
  obtain ⟨H, pi, hIso, _⟩ := exists_isometric_representation_unital (A := B)
  let rho : A →⋆ₙₐ[ℂ] (H.Carrier →L[ℂ] H.Carrier) :=
    pi.comp (inrNonUnitalStarAlgHom ℂ A)
  have hnorm : ∀ a : A, ‖rho a‖ = ‖a‖ := by
    intro a
    have hpi : ‖pi (a : B)‖ = ‖(a : B)‖ := by
      simpa [dist_eq_norm, map_zero pi, sub_zero] using hIso.dist_eq (a : B) 0
    have hr : rho a = pi (a : B) := by
      simp only [rho, NonUnitalStarAlgHom.comp_apply]
      rw [inrNonUnitalStarAlgHom_apply]
    rw [hr, hpi, Unitization.norm_inr]
  have hrho : Isometry rho := AddMonoidHomClass.isometry_of_norm rho hnorm
  exact ⟨H, rho, hrho, hrho.isClosedEmbedding.isClosed_range⟩

end CKMA
