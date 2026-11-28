/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.PDE.Euclidean
public import CKMA.Analysis.PDE.HolderGauge
public import TauCeti.Analysis.Sobolev.W1p.Basic

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Matrix.MeasurableSpace
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.Analysis.PDE.Ellipticity.Basic
import TauCeti.Analysis.PDE.MaximumPrinciple.AleksandrovBakelmanPucci.Basic
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence.Basic
import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.Holder
import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.LocalMaximumPrinciple
import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.WeakHarnack

/-!
# Interior elliptic estimates and weak p-harmonic regularity

Weak divergence-form equations and interior Meyers, ABP, Krylov–Safonov, Schauder and
Hessian `L^p` estimates, measured with the extended gauges of `CKMA.Analysis.PDE.HolderGauge`.
Lower-order coefficients are included in the classical estimates. Weak p-harmonicity uses
TauCeti's `W1p` gradient and yields local regular representatives and a Harnack inequality.
Sources: GAPS 33.9, 33.14–33.16, 33.18 and 33.34.

The classical Aleksandrov–Bakelman–Pucci estimate is
`TauCeti.PDE.le_add_mul_eLpNorm_negPart_div_det_rpow`. The coefficient is replaced by
`TauCeti.PDE.coefficientSymmetricPart`, whose positive-definiteness and determinant bound are
`TauCeti.PDE.UniformlyEllipticOn.posDef` and `TauCeti.PDE.UniformlyEllipticOn.pow_card_le_det`.
The contraction identity is `TauCeti.PDE.sum_coefficientSymmetricPart_mul_fderiv_fderiv`.
The Hölder estimate is `TauCeti.PDE.exists_holderOnWith_of_sum_mul_fderiv_fderiv_eq`. The Harnack
inequality chains `TauCeti.PDE.exists_eLpNorm_le_mul_rpow_mul_add_eLpNorm_posPart` with
`TauCeti.PDE.exists_le_mul_rpow_mul_eLpNorm_posPart_add`.

## Main definitions

* `CKMA.IsWeakEllipticSolution`: weak divergence-form solution of `-div(A grad u) = div F`.
* `CKMA.IsWeakPHarmonic`: weak `p`-harmonicity in `W^{1,p}`.

## Main results

* `CKMA.meyers_higherIntegrability` (**33.9**): local Meyers higher integrability estimate.
* `CKMA.abp_classical` (**33.14**): Aleksandrov–Bakelman–Pucci maximum principle.
* `CKMA.krylov_safonov_classical` (**33.15**): Krylov–Safonov Hölder and Harnack estimates.
* `CKMA.interior_schauder` (**33.16**): interior Schauder `C^{2,α}` estimate.
* `CKMA.interior_hessian_Lp` (**33.18**): interior Calderón–Zygmund `W^{2,p}` estimate.
* `CKMA.weakPHarmonic_regular` (**33.34**): local `C^{1,α}` regularity and Harnack inequality for
  weak `p`-harmonic functions.
-/

public section

noncomputable section

namespace CKMA

open Filter MeasureTheory Metric Set TauCeti.PDE Topology
open scoped ENNReal InnerProductSpace Matrix RealInnerProductSpace

/-- Weak divergence-form equation `-div(A grad u) = div F`, tested against smooth compact tests.
The identity is a Bochner integral, so a non-integrable integrand has integral `0`. -/
@[expose]
def IsWeakEllipticSolution {d : ℕ} (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d)))
    (A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (u : TauCeti.W1p volume Ω 2) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, IsCompactSmoothTestOn Ω φ →
    ∫ x in Ω, ⟪A x ((TauCeti.W1p.gradient u) x) + F x, gradient φ x⟫_ℝ = 0

/-- The defining test identity of a weak divergence-form solution. -/
theorem isWeakEllipticSolution_iff {d : ℕ} {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {u : TauCeti.W1p volume Ω 2} :
    IsWeakEllipticSolution Ω A F u ↔ ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      IsCompactSmoothTestOn Ω φ →
        ∫ x in Ω, ⟪A x ((TauCeti.W1p.gradient u) x) + F x, gradient φ x⟫_ℝ = 0 :=
  Iff.rfl

/-- Matrix of a Euclidean endomorphism in the coordinate basis. -/
private def matrixOfCLM {d : ℕ} (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ⟪euclideanUnitVector i, T (euclideanUnitVector j)⟫_ℝ

/-- The matrix pairing `ηᵀ T ξ` is the Euclidean inner product `⟪η, T ξ⟫`. -/
private lemma dotProduct_matrixOfCLM_mulVec {d : ℕ}
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (η ξ : EuclideanSpace ℝ (Fin d)) :
    η ⬝ᵥ matrixOfCLM T *ᵥ ξ = ⟪η, T ξ⟫_ℝ := by
  let e : Fin d → EuclideanSpace ℝ (Fin d) := euclideanUnitVector
  have he (i : Fin d) : EuclideanSpace.basisFun (Fin d) ℝ i = e i := by
    simp [e, euclideanUnitVector, EuclideanSpace.basisFun_apply]
  have hξ : ξ = ∑ j, (ξ : Fin d → ℝ) j • e j := by
    simpa [he] using ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr ξ).symm
  have hcoord (i : Fin d) : (matrixOfCLM T *ᵥ (ξ : Fin d → ℝ)) i = ⟪e i, T ξ⟫_ℝ := by
    rw [Matrix.mulVec_apply_eq_sum]
    conv_rhs => rw [hξ, map_sum, inner_sum]
    simp only [map_smul, inner_smul_right, matrixOfCLM, e]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hvec : matrixOfCLM T *ᵥ (ξ : Fin d → ℝ) = fun i => ⟪e i, T ξ⟫_ℝ := funext hcoord
  have hTi : (T ξ : Fin d → ℝ) = fun i => ⟪e i, T ξ⟫_ℝ := by
    funext i
    rw [← he i, EuclideanSpace.basisFun_inner]
  rw [hvec, EuclideanSpace.inner_eq_star_dotProduct, hTi, star_trivial, dotProduct_comm]

/-- The quadratic form of `matrixOfCLM T` is the inner product `⟪ξ, T ξ⟫`. -/
private lemma matrixOfCLM_toQuadraticForm {d : ℕ}
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (ξ : EuclideanSpace ℝ (Fin d)) :
    (matrixOfCLM T).toQuadraticForm' ξ = ⟪ξ, T ξ⟫_ℝ := by
  rw [Matrix.toQuadraticForm'_apply]
  exact dotProduct_matrixOfCLM_mulVec T ξ ξ

/-- A bound on the operator norm bounds the matrix pairing. -/
private lemma matrixOfCLM_abs_dotProduct_le {d : ℕ}
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) {Λ : ℝ} (hΛ : ‖T‖ ≤ Λ)
    (η ξ : EuclideanSpace ℝ (Fin d)) :
    |η ⬝ᵥ matrixOfCLM T *ᵥ ξ| ≤ Λ * ‖η‖ * ‖ξ‖ := by
  rw [dotProduct_matrixOfCLM_mulVec]
  calc
    |⟪η, T ξ⟫_ℝ| ≤ ‖η‖ * ‖T ξ‖ := abs_real_inner_le_norm η (T ξ)
    _ ≤ ‖η‖ * (‖T‖ * ‖ξ‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm ξ) (norm_nonneg η)
    _ = ‖T‖ * ‖η‖ * ‖ξ‖ := by rw [mul_left_comm ‖η‖ ‖T‖ ‖ξ‖, mul_assoc]
    _ ≤ Λ * ‖η‖ * ‖ξ‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hΛ (norm_nonneg η)) (norm_nonneg ξ)

/-- Uniform ellipticity of an endomorphism field passes to its coordinate matrix. -/
private lemma uniformlyEllipticOn_matrixOfCLM {d : ℕ} {ell Λ : ℝ}
    {A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (h : IsUniformlyEllipticOn A ell Λ Ω) :
    UniformlyEllipticOn Ω (fun x => matrixOfCLM (A x)) ell Λ :=
  UniformlyEllipticOn.of_bounds h.1 h.2.1
    (fun x hx ξ => by
      rw [matrixOfCLM_toQuadraticForm]
      exact (h.2.2 x hx).1 ξ)
    (fun x hx η ξ => matrixOfCLM_abs_dotProduct_le (A x) ((h.2.2 x hx).2) η ξ)

/-- The symmetric part of the coordinate matrix remains uniformly elliptic. -/
private lemma uniformlyEllipticOn_symmMatrix {d : ℕ} {ell Λ : ℝ}
    {A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (h : IsUniformlyEllipticOn A ell Λ Ω) :
    UniformlyEllipticOn Ω (fun x => coefficientSymmetricPart (matrixOfCLM (A x))) ell Λ :=
  (uniformlyEllipticOn_matrixOfCLM h).coefficientSymmetricPart

/-- The nondivergence principal part equals the raw matrix contraction of the Hessian. -/
private lemma nondivergencePrincipal_eq_matrixOfCLM {d : ℕ}
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {x : EuclideanSpace ℝ (Fin d)} (hu : ContDiffAt ℝ 2 u x) :
    nondivergencePrincipal (fun _ => A) u x = ∑ i, ∑ j, matrixOfCLM A i j *
      fderiv ℝ (fderiv ℝ u) x (euclideanUnitVector i) (euclideanUnitVector j) := by
  let e : Fin d → EuclideanSpace ℝ (Fin d) := euclideanUnitVector
  let H := fderiv ℝ (fderiv ℝ u) x
  have hsymm : IsSymmSndFDerivAt ℝ u x := hu.isSymmSndFDerivAt (by simp)
  have hrep (v : EuclideanSpace ℝ (Fin d)) : v = ∑ j, ⟪e j, v⟫_ℝ • e j := by
    simpa [e, euclideanUnitVector, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_inner]
      using ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' v).symm
  have hH (i : Fin d) : H (e i) (A (e i)) =
      ∑ j, matrixOfCLM A j i * H (e i) (e j) := by
    rw [hrep (A (e i))]
    simp [matrixOfCLM, e, map_sum, map_smul, smul_eq_mul]
  simp only [nondivergencePrincipal, H, e] at hH ⊢
  simp only [hH]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsymm (e j) (e i)]

/-- The nondivergence principal part equals the symmetric-matrix contraction. -/
private lemma nondivergencePrincipal_eq_symmMatrix {d : ℕ}
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {x : EuclideanSpace ℝ (Fin d)} (hu : ContDiffAt ℝ 2 u x) :
    nondivergencePrincipal (fun _ => A) u x =
      ∑ i, ∑ j, coefficientSymmetricPart (matrixOfCLM A) i j *
        fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  rw [nondivergencePrincipal_eq_matrixOfCLM A hu]
  simpa [euclideanUnitVector] using
    (sum_coefficientSymmetricPart_mul_fderiv_fderiv (A := matrixOfCLM A) hu).symm

/-- **33.9**: a local Meyers estimate, including divergence-form inhomogeneity. -/
theorem meyers_higherIntegrability {d : ℕ} (hd : 0 < d) {ell Λ : ℝ} :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
    ∀ (A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
      (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      (u : TauCeti.W1p volume (euclideanOpenBall d 2) 2),
      Measurable A → IsUniformlyEllipticOn A ell Λ (Metric.ball 0 2) →
      MemLp F (ENNReal.ofReal (2 + ε)) (volume.restrict (Metric.ball 0 2)) →
      IsWeakEllipticSolution (euclideanOpenBall d 2) A F u →
      MemLp ((TauCeti.W1p.gradient u) : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (ENNReal.ofReal (2 + ε)) (volume.restrict (Metric.ball 0 1)) ∧
      eLpNorm (TauCeti.W1p.gradient u) (ENNReal.ofReal (2 + ε))
        (volume.restrict (Metric.ball 0 1)) ≤
        ENNReal.ofReal C * (eLpNorm (TauCeti.W1p.gradient u) 2
          (volume.restrict (Metric.ball 0 2)) +
          eLpNorm F (ENNReal.ofReal (2 + ε)) (volume.restrict (Metric.ball 0 2))) := by
  sorry

/-- A nonempty bounded set in a nontrivial real normed space has nonempty frontier. -/
private lemma frontier_nonempty_of_isBounded {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] {Ω : Set E} (hΩn : Ω.Nonempty)
    (hΩb : Bornology.IsBounded Ω) : (frontier Ω).Nonempty := by
  rw [nonempty_iff_ne_empty]
  intro hempty
  rcases isClopen_iff.mp (isClopen_iff_frontier_eq_empty.mpr hempty) with hem | huniv
  · exact hΩn.ne_empty hem
  · exact NormedSpace.unbounded_univ ℝ E (huniv ▸ hΩb)

/-- The coordinate entries of a measurable endomorphism field are measurable. -/
private lemma measurable_matrixOfCLM_apply {d : ℕ}
    {A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (hA : Measurable A) (i j : Fin d) : Measurable fun x ↦ matrixOfCLM (A x) i j :=
  (innerSL ℝ (euclideanUnitVector i)).continuous.measurable.comp
    ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin d))
      (euclideanUnitVector j)).continuous.measurable.comp hA)

/-- The symmetric part of the coordinate matrix of a measurable field is strongly measurable. -/
private lemma aestronglyMeasurable_symmMatrix {d : ℕ}
    {A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (hA : Measurable A) (μ : Measure (EuclideanSpace ℝ (Fin d))) :
    AEStronglyMeasurable (fun x ↦ coefficientSymmetricPart (matrixOfCLM (A x))) μ := by
  have : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ))
  have : SecondCountableTopology (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  refine Measurable.aestronglyMeasurable ?_
  refine measurable_pi_iff.mpr fun i ↦ measurable_pi_iff.mpr fun j ↦ ?_
  simp only [coefficientSymmetricPart_apply]
  exact ((measurable_matrixOfCLM_apply hA i j).add
    (measurable_matrixOfCLM_apply hA j i)).div_const 2

/-- The nondivergence principal part of a `C²` function with measurable coefficients is
almost everywhere strongly measurable on an open set. -/
private lemma aestronglyMeasurable_nondivergencePrincipal {d : ℕ}
    {A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩo : IsOpen Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hA : Measurable A) :
    AEStronglyMeasurable (nondivergencePrincipal A u) (volume.restrict Ω) := by
  have hH2 : ContinuousOn (fderiv ℝ (fderiv ℝ u)) Ω :=
    (hu.fderiv_of_isOpen hΩo (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hΩo le_rfl
  have hpart (i j : Fin d) : AEStronglyMeasurable
      (fun x ↦ fderiv ℝ (fderiv ℝ u) x (euclideanUnitVector i) (euclideanUnitVector j))
      (volume.restrict Ω) :=
    (((ContinuousLinearMap.apply ℝ ℝ (euclideanUnitVector j)).comp
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
        (euclideanUnitVector i))).continuous.comp_continuousOn
      hH2).aestronglyMeasurable hΩo.measurableSet
  have hsum : AEStronglyMeasurable (fun x ↦ ∑ i, ∑ j, matrixOfCLM (A x) i j *
      fderiv ℝ (fderiv ℝ u) x (euclideanUnitVector i) (euclideanUnitVector j))
      (volume.restrict Ω) :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ ↦ Finset.aestronglyMeasurable_fun_sum _
      fun j _ ↦ (measurable_matrixOfCLM_apply hA i j).aestronglyMeasurable.mul (hpart i j)
  refine hsum.congr ?_
  filter_upwards [ae_restrict_mem hΩo.measurableSet] with x hx
  exact (nondivergencePrincipal_eq_matrixOfCLM (A x) (hu.contDiffAt (hΩo.mem_nhds hx))).symm

/-- A real bound `s ≤ m + K * G.toReal` with `0 ≤ m` and `0 ≤ K` gives the extended bound
`ofReal s ≤ ofReal m + ofReal K * G`. -/
private lemma ofReal_le_ofReal_add_ofReal_mul {s m K : ℝ} {G : ℝ≥0∞} (hm : 0 ≤ m)
    (hK : 0 ≤ K) (h : s ≤ m + K * G.toReal) :
    ENNReal.ofReal s ≤ ENNReal.ofReal m + ENNReal.ofReal K * G :=
  calc
    ENNReal.ofReal s ≤ ENNReal.ofReal (m + K * G.toReal) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal m + ENNReal.ofReal K * ENNReal.ofReal G.toReal := by
      rw [ENNReal.ofReal_add hm (mul_nonneg hK ENNReal.toReal_nonneg), ENNReal.ofReal_mul hK]
    _ ≤ ENNReal.ofReal m + ENNReal.ofReal K * G := by
      gcongr
      exact ENNReal.ofReal_toReal_le

/-- On `Ω`, the ABP quotient `f⁻ / det(a)^{1/d}`, with `a` the symmetric part of the coordinate
matrix of a uniformly elliptic field, is nonnegative and at most `f⁻ / λ`. -/
private lemma negPart_div_det_rpow_le {d : ℕ} (hd : 0 < d) {ell Λ : ℝ}
    {A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hEll : IsUniformlyEllipticOn A ell Λ Ω) (t : ℝ)
    {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ Ω) :
    0 ≤ t⁻ / (coefficientSymmetricPart (matrixOfCLM (A y))).det ^ (d : ℝ)⁻¹ ∧
      t⁻ / (coefficientSymmetricPart (matrixOfCLM (A y))).det ^ (d : ℝ)⁻¹ ≤ t⁻ / ell := by
  have hell : 0 < ell := hEll.1
  have hsym := uniformlyEllipticOn_symmMatrix hEll
  have hdet0 : 0 ≤ (coefficientSymmetricPart (matrixOfCLM (A y))).det :=
    (hsym.posDef hy (coefficientSymmetricPart_isSymm _)).det_pos.le
  refine ⟨div_nonneg (negPart_nonneg _) (Real.rpow_nonneg hdet0 _), ?_⟩
  have hdet : ell ^ d ≤ (coefficientSymmetricPart (matrixOfCLM (A y))).det := by
    simpa [Fintype.card_fin] using hsym.pow_card_le_det hy (coefficientSymmetricPart_isSymm _)
  have hroot : ell ≤ (coefficientSymmetricPart (matrixOfCLM (A y))).det ^ (d : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast ell d] at hdet
    refine le_of_eq_of_le ?_ (Real.rpow_le_rpow (Real.rpow_nonneg hell.le _) hdet
      (inv_nonneg.mpr (Nat.cast_nonneg _)))
    rw [← Real.rpow_mul hell.le, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hd.ne'), Real.rpow_one]
  exact div_le_div_of_nonneg_left (negPart_nonneg _) hell hroot

/-- If the negative part of the principal part is in `L^d(Ω)`, the ABP quotient is in `L^d` of
the upper contact set, with gauge at most that of the negative part divided by `λ`. -/
private lemma memLp_negPart_div_det_rpow_and_le {d : ℕ} (hd : 0 < d) {ell Λ : ℝ}
    {A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩo : IsOpen Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hA : Measurable A) (hEll : IsUniformlyEllipticOn A ell Λ Ω)
    (htop : eLpNorm (fun x ↦ (nondivergencePrincipal A u x)⁻) (d : ℝ≥0∞)
      (volume.restrict Ω) ≠ ∞) :
    MemLp (fun y ↦ (nondivergencePrincipal A u y)⁻ /
        (coefficientSymmetricPart (matrixOfCLM (A y))).det ^ (d : ℝ)⁻¹) (d : ℝ≥0∞)
        (volume.restrict (upperContactSet u Ω)) ∧
      (eLpNorm (fun y ↦ (nondivergencePrincipal A u y)⁻ /
        (coefficientSymmetricPart (matrixOfCLM (A y))).det ^ (d : ℝ)⁻¹) (d : ℝ≥0∞)
        (volume.restrict (upperContactSet u Ω))).toReal ≤
      (eLpNorm (fun x ↦ (nondivergencePrincipal A u x)⁻) (d : ℝ≥0∞)
        (volume.restrict Ω)).toReal / ell := by
  have hell : 0 < ell := hEll.1
  let a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ :=
    fun x => coefficientSymmetricPart (matrixOfCLM (A x))
  let g : EuclideanSpace ℝ (Fin d) → ℝ := fun x => (nondivergencePrincipal A u x)⁻
  have hprin := aestronglyMeasurable_nondivergencePrincipal hΩo hu hA
  have hgLp : MemLp g (d : ℝ≥0∞) (volume.restrict Ω) := by
    rw [memLp_iff]
    exact lt_top_iff_ne_top.mpr htop
  have hdet_meas : AEStronglyMeasurable a (volume.restrict Ω) :=
    aestronglyMeasurable_symmMatrix hA _
  have hcontact : MeasurableSet (upperContactSet u Ω) :=
    measurableSet_upperContactSet hΩo (hu.of_le (by simp))
  have hquot : AEStronglyMeasurable
      (fun y => (nondivergencePrincipal A u y)⁻ / (a y).det ^ (d : ℝ)⁻¹)
      (volume.restrict (upperContactSet u Ω)) := by
    simpa [a, Fintype.card_fin, g] using
      aestronglyMeasurable_negPart_div_det_rpow
        (hdet_meas.mono_measure (Measure.restrict_mono upperContactSet_subset le_rfl))
        (hprin.mono_measure (Measure.restrict_mono upperContactSet_subset le_rfl))
  have hqnorm (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ upperContactSet u Ω) :
      ‖(nondivergencePrincipal A u y)⁻ / (a y).det ^ (d : ℝ)⁻¹‖ ≤ ‖g y / ell‖ := by
    obtain ⟨hleft, hle⟩ :=
      negPart_div_det_rpow_le hd hEll (nondivergencePrincipal A u y) (upperContactSet_subset hy)
    rw [Real.norm_eq_abs, abs_of_nonneg hleft, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (negPart_nonneg _) hell.le)]
    exact hle
  have hdom : MemLp (fun y => (nondivergencePrincipal A u y)⁻ /
      (a y).det ^ (d : ℝ)⁻¹) (d : ℝ≥0∞)
      (volume.restrict (upperContactSet u Ω)) := by
    have hscale : MemLp (fun y => g y / ell) (d : ℝ≥0∞) (volume.restrict Ω) := by
      have hfun : (fun y => g y / ell) = ell⁻¹ • g := by
        ext y
        simp [Pi.smul_apply, div_eq_inv_mul, smul_eq_mul]
      rw [hfun, memLp_iff, eLpNorm_const_smul]
      exact ENNReal.mul_lt_top (by simp) hgLp
    refine MemLp.of_le (hscale.mono_measure
      (Measure.restrict_mono upperContactSet_subset le_rfl)) hquot ?_
    filter_upwards [ae_restrict_mem hcontact] with y hy
    exact hqnorm y hy
  have hnorm' : (eLpNorm (fun y => (nondivergencePrincipal A u y)⁻ /
      (a y).det ^ (d : ℝ)⁻¹) (d : ℝ≥0∞)
      (volume.restrict (upperContactSet u Ω))).toReal ≤
      (eLpNorm g (d : ℝ≥0∞) (volume.restrict Ω)).toReal / ell := by
    have hle : eLpNorm (fun y => (nondivergencePrincipal A u y)⁻ /
        (a y).det ^ (d : ℝ)⁻¹) (d : ℝ≥0∞)
        (volume.restrict (upperContactSet u Ω)) ≤
        eLpNorm (fun y => g y / ell) (d : ℝ≥0∞) (volume.restrict Ω) := by
      refine (eLpNorm_mono_ae hquot ?_).trans (eLpNorm_mono_measure _
        (Measure.restrict_mono upperContactSet_subset le_rfl))
      filter_upwards [ae_restrict_mem hcontact] with y hy
      exact hqnorm y hy
    have hfun : eLpNorm (fun y => g y / ell) (d : ℝ≥0∞) (volume.restrict Ω) =
        ENNReal.ofReal ell⁻¹ * eLpNorm g (d : ℝ≥0∞) (volume.restrict Ω) := by
      have hsmul : (fun y => g y / ell) = ell⁻¹ • g := by
        ext y
        simp [Pi.smul_apply, div_eq_inv_mul, smul_eq_mul]
      rw [hsmul, eLpNorm_const_smul, Real.eNorm_eq_ofReal (inv_nonneg.mpr hell.le)]
    have hfin : eLpNorm (fun y => g y / ell) (d : ℝ≥0∞) (volume.restrict Ω) ≠ ∞ := by
      rw [hfun]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop
    calc
      (eLpNorm (fun y => (nondivergencePrincipal A u y)⁻ / (a y).det ^ (d : ℝ)⁻¹)
          (d : ℝ≥0∞) (volume.restrict (upperContactSet u Ω))).toReal
        ≤ (eLpNorm (fun y => g y / ell) (d : ℝ≥0∞) (volume.restrict Ω)).toReal :=
          ENNReal.toReal_mono hfin hle
      _ = (ENNReal.ofReal ell⁻¹ * eLpNorm g (d : ℝ≥0∞) (volume.restrict Ω)).toReal := by
        rw [hfun]
      _ = ell⁻¹ * (eLpNorm g (d : ℝ≥0∞) (volume.restrict Ω)).toReal :=
        ENNReal.toReal_ofReal_mul ell⁻¹ _ (inv_nonneg.mpr hell.le)
      _ = (eLpNorm g (d : ℝ≥0∞) (volume.restrict Ω)).toReal / ell := by
        rw [inv_mul_eq_div]
  exact ⟨hdom, hnorm'⟩

/-- **33.14**, the Aleksandrov–Bakelman–Pucci maximum principle for classical `C²` functions on
a bounded open set. Extended norm values make the estimate meaningful when the source norm is
infinite. -/
theorem abp_classical {d : ℕ} (hd : 0 < d) {ell Λ : ℝ} : ∃ C : ℝ, 0 < C ∧
    ∀ (Ω : Set (EuclideanSpace ℝ (Fin d))) (u : EuclideanSpace ℝ (Fin d) → ℝ)
      (A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
      IsOpen Ω → Ω.Nonempty → Bornology.IsBounded Ω → ContinuousOn u (closure Ω) →
      ContDiffOn ℝ 2 u Ω → Measurable A → IsUniformlyEllipticOn A ell Λ Ω →
      ENNReal.ofReal (sSup (u '' Ω)) ≤
        ENNReal.ofReal (sSup ((fun x ↦ max (u x) 0) '' frontier Ω)) +
        ENNReal.ofReal (C * Metric.diam Ω) *
          eLpNorm (fun x ↦ max (-(nondivergencePrincipal A u x)) 0) (d : ℝ≥0∞)
            (volume.restrict Ω) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) := inferInstance
  set ω : ℝ := (volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
  have hω : 0 < ω :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin d)) one_pos).ne'
      measure_ball_lt_top.ne
  have hden : 0 < (d : ℝ) * ω ^ (d : ℝ)⁻¹ :=
    mul_pos (Nat.cast_pos.mpr hd) (Real.rpow_pos_of_pos hω _)
  let C : ℝ := if 0 < ell then 1 / ((d : ℝ) * ω ^ (d : ℝ)⁻¹ * ell) else 1
  have hCpos : 0 < C := by
    by_cases hell : 0 < ell
    · simp only [C, ite_eq_left hell]
      exact div_pos one_pos (mul_pos hden hell)
    · simp only [C, ite_eq_right hell]
      exact one_pos
  refine ⟨C, hCpos, ?_⟩
  · intro Ω u A hΩo hΩn hΩb hcont hu hA hEll
    have hell : 0 < ell := hEll.1
    have hC : C = 1 / ((d : ℝ) * ω ^ (d : ℝ)⁻¹ * ell) := ite_eq_left hell
    have hsym := uniformlyEllipticOn_symmMatrix hEll
    let a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ :=
      fun x => coefficientSymmetricPart (matrixOfCLM (A x))
    let g : EuclideanSpace ℝ (Fin d) → ℝ := fun x => (nondivergencePrincipal A u x)⁻
    have hgmax : g = fun x => max (-(nondivergencePrincipal A u x)) 0 := by
      ext x
      simp [g, negPart_def]
    let m : ℝ := sSup ((fun x => max (u x) 0) '' frontier Ω)
    have hfr : (frontier Ω).Nonempty := frontier_nonempty_of_isBounded hΩn hΩb
    have hfrC : IsCompact (frontier Ω) :=
      hΩb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
    have hmaxCont : ContinuousOn (fun x => max (u x) 0) (frontier Ω) :=
      continuous_max.comp_continuousOn'
        ((hcont.mono frontier_subset_closure).prodMk continuousOn_const)
    have hbddM : BddAbove ((fun x => max (u x) 0) '' frontier Ω) :=
      hfrC.bddAbove_image hmaxCont
    have hm0 : 0 ≤ m := by
      obtain ⟨z, hz⟩ := hfr
      exact (le_max_right (u z) 0).trans (le_csSup hbddM ⟨z, hz, rfl⟩)
    have hmbound : ∀ z ∈ frontier Ω, u z ≤ m := by
      intro z hz
      exact (le_max_left (u z) 0).trans (le_csSup hbddM ⟨z, hz, rfl⟩)
    by_cases hsSup : 0 ≤ sSup (u '' Ω)
    · by_cases htop : eLpNorm g (d : ℝ≥0∞) (volume.restrict Ω) = ∞
      · have hx0 : ∃ x, x ∈ Ω := hΩn
        obtain ⟨x0, hx0⟩ := hx0
        have hdiam : 0 < diam Ω := hΩo.diam_pos hΩb hx0
        have hpos : 0 < C * diam Ω := mul_pos hCpos hdiam
        rw [← hgmax, htop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hpos), add_top]
        exact le_top
      · obtain ⟨hdom, hnorm⟩ := memLp_negPart_div_det_rpow_and_le hd hΩo hu hA hEll htop
        have habp : ∀ x ∈ Ω, u x ≤ m + diam Ω / ((d : ℝ) * ω ^ (d : ℝ)⁻¹) *
            (eLpNorm (fun y => (nondivergencePrincipal A u y)⁻ / (a y).det ^ (d : ℝ)⁻¹)
              (d : ℝ≥0∞) (volume.restrict (upperContactSet u Ω))).toReal := by
          intro x hx
          have hle := le_add_mul_eLpNorm_negPart_div_det_rpow (hΩb := hΩb) (hΩ := hΩo)
            (hcont := hcont) (hu := hu)
            (ha := fun y hy => hsym.posDef (upperContactSet_subset hy)
              (coefficientSymmetricPart_isSymm _))
            (f := nondivergencePrincipal A u) (a := a) (m := m)
            (hf := fun y hy => le_of_eq <| by
              have h := nondivergencePrincipal_eq_symmMatrix (A y)
                (hu.contDiffAt (hΩo.mem_nhds (upperContactSet_subset hy)))
              simpa [a, nondivergencePrincipal] using h)
            (hg := by simpa [Fintype.card_fin, a] using hdom)
            (hm := hmbound) (hx := hx)
          simpa [Fintype.card_fin, ω] using hle
        have hux (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Ω) :
            u x ≤ m + C * diam Ω * (eLpNorm g (d : ℝ≥0∞) (volume.restrict Ω)).toReal := by
          set G := (eLpNorm g (d : ℝ≥0∞) (volume.restrict Ω)).toReal
          have hstep : diam Ω / ((d : ℝ) * ω ^ (d : ℝ)⁻¹) *
              (eLpNorm (fun y => (nondivergencePrincipal A u y)⁻ / (a y).det ^ (d : ℝ)⁻¹)
                (d : ℝ≥0∞) (volume.restrict (upperContactSet u Ω))).toReal ≤
              C * diam Ω * G := by
            refine (mul_le_mul_of_nonneg_left hnorm
              (div_nonneg diam_nonneg hden.le)).trans (le_of_eq ?_)
            rw [hC]
            field_simp [hden.ne', hell.ne']
          exact (habp x hx).trans <| by
            rw [add_comm m, add_comm m]
            exact add_le_add_left hstep m
        have hsuple : sSup (u '' Ω) ≤ m + C * diam Ω *
            (eLpNorm g (d : ℝ≥0∞) (volume.restrict Ω)).toReal :=
          csSup_le (hΩn.image u) (by
            rintro _ ⟨x, hx, rfl⟩
            exact hux x hx)
        have hCd : 0 ≤ C * diam Ω := mul_nonneg hCpos.le diam_nonneg
        simpa [m, g, negPart_def] using ofReal_le_ofReal_add_ofReal_mul hm0 hCd hsuple
    · rw [ENNReal.ofReal_eq_zero.mpr (le_of_lt (not_le.mp hsSup))]
      exact zero_le

/-- The nondivergence principal part is the coordinate contraction of `A x`. -/
private lemma nondivergencePrincipal_matrix_eq {d : ℕ}
    (A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {x : EuclideanSpace ℝ (Fin d)} (hu : ContDiffAt ℝ 2 u x) :
    nondivergencePrincipal A u x = ∑ i, ∑ j, matrixOfCLM (A x) i j *
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  simpa [nondivergencePrincipal, euclideanUnitVector] using
    nondivergencePrincipal_eq_matrixOfCLM (A x) hu

/-- A one-step comparison `u c ≤ K * u y`, for `c` in the unit ball and `y` within `1 / 8` of
`c`, chains along sixteen steps to `u x ≤ K ^ 16 * u y` for all `x, y` in the unit ball. -/
private lemma le_pow_mul_of_forall_mem_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {u : E → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hctrl : ∀ c ∈ Metric.ball (0 : E) 1, ∀ y ∈ Metric.ball c (1 / 8), u c ≤ K * u y)
    {x y : E} (hx : x ∈ Metric.ball (0 : E) 1) (hy : y ∈ Metric.ball (0 : E) 1) :
    u x ≤ K ^ 16 * u y := by
  let z : ℕ → E := fun i ↦ (1 - (i : ℝ) / 16) • y + ((i : ℝ) / 16) • x
  have hz0 : z 0 = y := by simp [z]
  have hz16 : z 16 = x := by simp [z]
  have hmaxlt : max ‖x‖ ‖y‖ < 1 :=
    max_lt (mem_ball_zero_iff.mp hx) (mem_ball_zero_iff.mp hy)
  have hzMem (i : ℕ) (hi : i ≤ 16) : z i ∈ Metric.ball 0 1 := by
    rw [mem_ball_zero_iff]
    have ha : 0 ≤ 1 - (i : ℝ) / 16 := by
      rw [sub_nonneg, div_le_one (by norm_num)]
      exact_mod_cast hi
    have hb : 0 ≤ (i : ℝ) / 16 := by positivity
    calc ‖z i‖ ≤ ‖(1 - (i : ℝ) / 16) • y‖ + ‖((i : ℝ) / 16) • x‖ := norm_add_le _ _
      _ = (1 - (i : ℝ) / 16) * ‖y‖ + ((i : ℝ) / 16) * ‖x‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ (1 - (i : ℝ) / 16) * max ‖x‖ ‖y‖ + ((i : ℝ) / 16) * max ‖x‖ ‖y‖ := by
        gcongr
        · exact le_max_right _ _
        · exact le_max_left _ _
      _ = max ‖x‖ ‖y‖ := by ring
      _ < 1 := hmaxlt
  have hnear (i : ℕ) : z i ∈ Metric.ball (z (i + 1)) (1 / 8) := by
    have hdiff : z (i + 1) - z i = ((1 : ℝ) / 16) • (x - y) := by
      have h1 : (1 - ((i : ℝ) + 1) / 16) = (1 - (i : ℝ) / 16) - 1 / 16 := by ring
      have h2 : ((i : ℝ) + 1) / 16 = (i : ℝ) / 16 + 1 / 16 := by ring
      simp only [z, Nat.cast_add, Nat.cast_one]
      rw [h1, h2, sub_smul, add_smul, smul_sub]
      abel
    rw [mem_ball, dist_eq_norm_sub, norm_sub_rev, hdiff, norm_smul,
      Real.norm_of_nonneg (by norm_num)]
    have hxy : ‖x - y‖ < 2 :=
      (norm_sub_le x y).trans_lt (by linarith [le_max_left ‖x‖ ‖y‖, le_max_right ‖x‖ ‖y‖])
    linarith
  have hchain (k : ℕ) (hk : k ≤ 16) : u (z k) ≤ K ^ k * u y := by
    induction k with
    | zero => simp [hz0]
    | succ k ih =>
      calc u (z (k + 1)) ≤ K * u (z k) := hctrl _ (hzMem (k + 1) hk) _ (hnear k)
        _ ≤ K * (K ^ k * u y) := mul_le_mul_of_nonneg_left (ih (Nat.le_of_succ_le hk)) hK
        _ = K ^ (k + 1) * u y := by ring
  simpa [hz16] using hchain 16 le_rfl

/-- If `f x ≤ K * f y` for all `x, y` in a nonempty set `s` and `0 < K`, then
`sSup (f '' s) ≤ K * sInf (f '' s)`. -/
private lemma sSup_image_le_mul_sInf_image {E : Type*} {f : E → ℝ} {s : Set E}
    (hs : s.Nonempty) {K : ℝ} (hK : 0 < K) (h : ∀ x ∈ s, ∀ y ∈ s, f x ≤ K * f y) :
    sSup (f '' s) ≤ K * sInf (f '' s) := by
  have hs' := hs.image f
  have hdiv : sSup (f '' s) / K ≤ sInf (f '' s) := by
    refine le_csInf hs' ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [div_le_iff₀ hK, mul_comm]
    refine csSup_le hs' ?_
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv w hw
  rw [div_le_iff₀ hK, mul_comm] at hdiv
  exact hdiv

/-- For `0 ≤ t < 2` and `0 < α`, `t ^ (α + α) ≤ 2 ^ α * t ^ α`. -/
private lemma rpow_add_self_le_two_rpow_mul {t α : ℝ} (ht : 0 ≤ t) (ht2 : t < 2)
    (hα : 0 < α) : t ^ (α + α) ≤ 2 ^ α * t ^ α := by
  rcases ht.eq_or_lt with rfl | ht0
  · simp [Real.zero_rpow hα.ne', Real.zero_rpow (by linarith : α + α ≠ 0)]
  · rw [Real.rpow_add ht0]
    exact mul_le_mul_of_nonneg_right (Real.rpow_lt_rpow ht ht2 hα).le (Real.rpow_nonneg ht _)

/-- A classical solution of `tr(A D²u) = 0` on `B₂` satisfies the coordinate-matrix form of the
equation used by TauCeti's Krylov–Safonov theorems. -/
private lemma sum_matrixOfCLM_mul_fderiv_fderiv_eq_zero {d : ℕ}
    {A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u (Metric.ball 0 2))
    (heq : ∀ x ∈ Metric.ball 0 2, nondivergencePrincipal A u x = 0)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Metric.ball 0 2) :
    ∑ i, ∑ j, matrixOfCLM (A x) i j * fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = 0 := by
  simpa [heq x hx] using (nondivergencePrincipal_matrix_eq A
    (hu.contDiffAt (Metric.isOpen_ball.mem_nhds hx))).symm

/-- The interior Hölder half of **33.15**, from TauCeti's Krylov–Safonov Hölder estimate. -/
private lemma krylov_safonov_holder {d : ℕ} (hd : 0 < d) {ell Λ : ℝ} (hEL : 0 < ell ∧ ell ≤ Λ) :
    ∃ α Ch : ℝ, 0 < α ∧ α < 1 ∧ 0 < Ch ∧
    ∀ (A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
      (u : EuclideanSpace ℝ (Fin d) → ℝ),
      IsUniformlyEllipticOn A ell Λ (Metric.ball 0 2) →
      ContDiffOn ℝ 2 u (Metric.ball 0 2) →
      (∀ x ∈ Metric.ball 0 2, nondivergencePrincipal A u x = 0) →
      holderSeminormOn α u (Metric.ball 0 1) ≤
        ENNReal.ofReal Ch * uniformGaugeOn u (Metric.ball 0 2) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hell : 0 < ell := hEL.1
  have hκ : 0 < Λ / ell := div_pos (lt_of_lt_of_le hell hEL.2) hell
  obtain ⟨α0, C0, hα0, hα1, hC0, Hholder⟩ :=
    exists_holderOnWith_of_sum_mul_fderiv_fderiv_eq (ι := Fin d) (κ := Λ / ell) hκ
  set α : ℝ := (α0 : ℝ) / 2
  have hαpos : 0 < α := div_pos (NNReal.coe_pos.mpr hα0) two_pos
  have hαlt : α < 1 := by
    have hα0R : (α0 : ℝ) ≤ 1 := by exact_mod_cast hα1
    have : α ≤ (1 : ℝ) / 2 := div_le_div_of_nonneg_right hα0R two_pos.le
    exact this.trans_lt (by norm_num)
  set Ch : ℝ := C0 * 2 ^ α
  have hCh : 0 < Ch := mul_pos hC0 (Real.rpow_pos_of_pos two_pos _)
  refine ⟨α, Ch, hαpos, hαlt, hCh, fun A u hEll hu heq ↦ ?_⟩
  have hLam : Λ ≤ Λ / ell * ell := le_of_eq (div_mul_cancel₀ Λ hell.ne').symm
  have hsub2 : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (2 * 1) = Metric.ball 0 2 := by simp
  have heqSum : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (2 * 1),
      ∑ i, ∑ j, matrixOfCLM (A x) i j * fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = 0 := fun x hx ↦
    sum_matrixOfCLM_mul_fderiv_fderiv_eq_zero hu heq (hsub2 ▸ hx)
  have hzeroLp : MemLp (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) (Fintype.card (Fin d))
      (volume.restrict (Metric.ball 0 (2 * 1))) := by
    have : IsFiniteMeasure
        (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (2 * 1))) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    exact memLp_const 0
  by_cases htop : uniformGaugeOn u (Metric.ball 0 2) = ∞
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hCh)]
    exact le_top
  set M : ℝ := (uniformGaugeOn u (Metric.ball 0 2)).toReal
  have hAbs : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (2 * 1), |u x| ≤ M := by
    intro x hx
    rw [hsub2] at hx
    simpa only [Real.norm_eq_abs] using norm_le_toReal_uniformGaugeOn htop hx
  have hHold := Hholder one_pos (by simpa [hsub2] using uniformlyEllipticOn_matrixOfCLM hEll)
    hLam (by simpa [hsub2] using hu) hAbs heqSum hzeroLp
  have hsem : ∀ x ∈ Metric.ball 0 1, ∀ y ∈ Metric.ball 0 1,
      ‖u x - u y‖ ≤ Ch * M * dist x y ^ α := by
    intro x hx y hy
    have hdist := hHold.dist_le hx hy
    have hzeroF : eLpNorm (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) (Fintype.card (Fin d))
        (volume.restrict (Metric.ball 0 (2 * 1))) = 0 := by simp
    rw [Real.one_rpow, hzeroF, ENNReal.toReal_zero, mul_zero, zero_div, add_zero,
      mul_one] at hdist
    rw [Real.coe_toNNReal (C0 * M) (mul_nonneg hC0.le ENNReal.toReal_nonneg)] at hdist
    have hd2 : dist x y < 2 := by
      calc dist x y ≤ ‖x‖ + ‖y‖ := dist_eq_norm_sub x y ▸ norm_sub_le x y
        _ < 1 + 1 := add_lt_add (mem_ball_zero_iff.mp hx) (mem_ball_zero_iff.mp hy)
        _ = 2 := by norm_num
    have hαsum : (α0 : ℝ) = α + α := by
      unfold α
      ring
    have hpow : dist x y ^ (α0 : ℝ) ≤ 2 ^ α * dist x y ^ α :=
      hαsum ▸ rpow_add_self_le_two_rpow_mul dist_nonneg hd2 hαpos
    calc ‖u x - u y‖ = dist (u x) (u y) := by simp [dist_eq_norm_sub]
      _ ≤ C0 * M * dist x y ^ (α0 : ℝ) := by simpa [mul_assoc] using hdist
      _ ≤ C0 * M * (2 ^ α * dist x y ^ α) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg hC0.le ENNReal.toReal_nonneg)
      _ = Ch * M * dist x y ^ α := by
        unfold Ch
        ring
  have hK : 0 ≤ Ch * M := mul_nonneg hCh.le ENNReal.toReal_nonneg
  refine (holderSeminormOn_le_of_dist_le hαpos hK hsem).trans ?_
  rw [ENNReal.ofReal_mul hCh.le]
  gcongr
  exact ENNReal.ofReal_toReal_le

/-- One Harnack step for **33.15**: TauCeti's weak Harnack inequality on `B(c, 1/2)` and local
maximum principle on a small ball give `u c ≤ K * u y` for `y` within `1 / 8` of `c ∈ B₁`. -/
private lemma krylov_safonov_step {d : ℕ} (hd : 0 < d) {ell Λ : ℝ}
    (hEL : 0 < ell ∧ ell ≤ Λ) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
      (u : EuclideanSpace ℝ (Fin d) → ℝ),
      IsUniformlyEllipticOn A ell Λ (Metric.ball 0 2) →
      ContDiffOn ℝ 2 u (Metric.ball 0 2) →
      (∀ x ∈ Metric.ball 0 2, nondivergencePrincipal A u x = 0) →
      (∀ x ∈ Metric.ball 0 2, 0 ≤ u x) →
        ∀ c ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1, ∀ y ∈ Metric.ball c (1 / 8),
          u c ≤ K * u y := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hell : 0 < ell := hEL.1
  have hκ : 0 < Λ / ell := div_pos (lt_of_lt_of_le hell hEL.2) hell
  obtain ⟨p, Cw, hp, hCw, Hweak⟩ :=
    exists_eLpNorm_le_mul_rpow_mul_add_eLpNorm_posPart (ι := Fin d) (κ := Λ / ell) hκ
  obtain ⟨Cm, hCm, Hmax⟩ :=
    exists_le_mul_rpow_mul_eLpNorm_posPart_add (ι := Fin d) (κ := Λ / ell) (p := p) hp
  set S : ℝ := (1 / 2) / (16 * Real.sqrt (d : ℝ))
  have hS : 0 < S := div_pos (by norm_num) (mul_pos (by norm_num)
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)))
  have hSle : S ≤ 1 / 2 := by
    have hden : (1 : ℝ) ≤ 16 * Real.sqrt (d : ℝ) := by
      have hsqrt : (1 : ℝ) ≤ Real.sqrt (d : ℝ) :=
        Real.one_le_sqrt.mpr (by exact_mod_cast Nat.one_le_of_lt hd)
      nlinarith
    simpa [S, div_one] using
      div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 2) one_pos hden
  set q : ℝ := (d : ℝ) / p
  have hscale : S ^ (-q) * (1 / 2) ^ q = ((1 / 2) / S) ^ q := by
    rw [Real.rpow_neg hS.le, mul_comm, ← div_eq_mul_inv,
      ← Real.div_rpow (by norm_num) hS.le]
  set Cstep : ℝ := Cm * Cw * ((1 / 2) / S) ^ q
  have hCstep : 0 < Cstep := mul_pos (mul_pos hCm hCw) (Real.rpow_pos_of_pos (div_pos
    (by norm_num) hS) _)
  refine ⟨Cstep, hCstep, fun A u hEll hu heq hnonneg ↦ ?_⟩
  have hLam : Λ ≤ Λ / ell * ell := le_of_eq (div_mul_cancel₀ Λ hell.ne').symm
  have hcoeff := uniformlyEllipticOn_matrixOfCLM hEll
  have hsum (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Metric.ball 0 2) :
      ∑ i, ∑ j, matrixOfCLM (A x) i j * fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = 0 :=
    sum_matrixOfCLM_mul_fderiv_fderiv_eq_zero hu heq hx
  have hctrl (c : EuclideanSpace ℝ (Fin d)) (hc : c ∈ Metric.ball 0 1)
      (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ Metric.ball c (1 / 8)) :
      u c ≤ Cstep * u y := by
    have hclosed : Metric.closedBall c (1 / 2) ⊆ Metric.ball 0 2 := by
      intro w hw
      have hdist : dist w 0 < 2 := by
        nlinarith [dist_triangle w c 0, mem_closedBall.mp hw, mem_ball.mp hc]
      simpa [mem_ball, dist_zero_right] using hdist
    have hopen : Metric.ball c (1 / 2) ⊆ Metric.ball 0 2 :=
      Metric.ball_subset_closedBall.trans hclosed
    have hsmall : Metric.ball c S ⊆ Metric.ball 0 2 :=
      (Metric.ball_subset_ball hSle).trans hopen
    have hclosedS : Metric.closedBall c S ⊆ Metric.ball 0 2 :=
      (Metric.closedBall_subset_closedBall hSle).trans hclosed
    have hEllOpen := hcoeff.mono_set hopen
    have hEllSmall := hcoeff.mono_set hsmall
    have huClosed : ContinuousOn u (Metric.closedBall c (1 / 2)) :=
      hu.continuousOn.mono hclosed
    have huClosedS : ContinuousOn u (Metric.closedBall c S) :=
      hu.continuousOn.mono hclosedS
    have huOpen : ContDiffOn ℝ 2 u (Metric.ball c (1 / 2)) := hu.mono hopen
    have huSmall : ContDiffOn ℝ 2 u (Metric.ball c S) := hu.mono hsmall
    have hposClosed : ∀ x ∈ Metric.closedBall c (1 / 2), 0 ≤ u x :=
      fun x hx => hnonneg x (hclosed hx)
    have hsuper : ∀ x ∈ Metric.ball c (1 / 2),
        ∑ i, ∑ j, matrixOfCLM (A x) i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ 0 :=
      fun x hx => (hsum x (hopen hx)).le
    have hsubsol : ∀ x ∈ Metric.ball c S,
        0 ≤ ∑ i, ∑ j, matrixOfCLM (A x) i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
      fun x hx => (hsum x (hsmall hx)).symm.le
    have hradius : (1 / 2) / 4 = (1 / 8 : ℝ) := by norm_num
    have hy4 : y ∈ Metric.ball c ((1 / 2) / 4) := by rwa [hradius]
    have huy : 0 ≤ u y := by
      have hdist : dist y 0 < 2 := by
        nlinarith [dist_triangle y c 0, mem_ball.mp hy, mem_ball.mp hc]
      exact hnonneg y (by simpa [mem_ball, dist_zero_right] using hdist)
    have hweak := Hweak hEllOpen hLam huClosed huOpen hposClosed hsuper y hy4
    have hcard : (Fintype.card (Fin d) : ℝ) / p = q := by simp [q, Fintype.card_fin]
    have hballS :
        Metric.ball c ((1 / 2) / (16 * Real.sqrt (Fintype.card (Fin d)))) =
          Metric.ball c S := by simp [S, Fintype.card_fin]
    have hnorm : (eLpNorm u (ENNReal.ofReal p)
        (volume.restrict (Metric.ball c S))).toReal ≤ Cw * (1 / 2) ^ q * u y := by
      rw [hballS] at hweak
      have hf : eLpNorm (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)⁺)
          (Fintype.card (Fin d)) (volume.restrict (Metric.ball c (1 / 2))) = 0 := by
        simp
      rw [hf, mul_zero, add_zero, hcard] at hweak
      have hnn : 0 ≤ Cw * (1 / 2) ^ q :=
        mul_nonneg hCw.le (Real.rpow_nonneg (by norm_num) _)
      rw [← ENNReal.ofReal_mul hnn] at hweak
      exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hnn huy) hweak
    have hμ : IsFiniteMeasure (volume.restrict (Metric.ball c S)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    have hLp : MemLp (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)⁻) (Fintype.card (Fin d))
        (volume.restrict (Metric.ball c S)) := by
      rw [negPart_zero]
      exact memLp_const 0
    have hmax := Hmax hEllSmall hLam huClosedS huSmall hsubsol hLp c
      (mem_ball_self (half_pos hS))
    have hup : eLpNorm (fun w => (u w)⁺) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball c S)) =
        eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball c S)) := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
      exact posPart_eq_self.mpr (hnonneg w (hsmall hw))
    have hexp : -(Fintype.card (Fin d) : ℝ) / p = -q := by rw [neg_div, hcard]
    have hzero : (eLpNorm (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)⁻)
        (Fintype.card (Fin d)) (volume.restrict (Metric.ball c S))).toReal = 0 := by
      simp
    rw [hup, hexp, hzero, mul_zero, add_zero] at hmax
    have hpow : S ^ (-q) * (eLpNorm u (ENNReal.ofReal p)
        (volume.restrict (Metric.ball c S))).toReal ≤
        S ^ (-q) * (Cw * (1 / 2) ^ q * u y) :=
      mul_le_mul_of_nonneg_left hnorm (Real.rpow_nonneg hS.le _)
    have hfin : Cm * (S ^ (-q) * (Cw * (1 / 2) ^ q * u y)) = Cstep * u y := by
      have hgrp : S ^ (-q) * (Cw * (1 / 2) ^ q * u y) =
          Cw * (S ^ (-q) * (1 / 2) ^ q) * u y := by ring
      rw [hgrp, hscale]
      unfold Cstep
      ring
    calc u c ≤ Cm * (S ^ (-q) * (eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Metric.ball c S))).toReal) := hmax
      _ ≤ Cm * (S ^ (-q) * (Cw * (1 / 2) ^ q * u y)) :=
        mul_le_mul_of_nonneg_left hpow hCm.le
      _ = Cstep * u y := hfin
  exact hctrl

/-- The interior Harnack half of **33.15**, chaining `krylov_safonov_step` along sixteen balls
of radius `1 / 8`. -/
private lemma krylov_safonov_harnack {d : ℕ} (hd : 0 < d) {ell Λ : ℝ}
    (hEL : 0 < ell ∧ ell ≤ Λ) :
    ∃ Charn : ℝ, 0 < Charn ∧
    ∀ (A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
      (u : EuclideanSpace ℝ (Fin d) → ℝ),
      IsUniformlyEllipticOn A ell Λ (Metric.ball 0 2) →
      ContDiffOn ℝ 2 u (Metric.ball 0 2) →
      (∀ x ∈ Metric.ball 0 2, nondivergencePrincipal A u x = 0) →
      (∀ x ∈ Metric.ball 0 2, 0 ≤ u x) →
        sSup (u '' Metric.ball 0 1) ≤ Charn * sInf (u '' Metric.ball 0 1) := by
  obtain ⟨K, hK, Hstep⟩ := krylov_safonov_step hd hEL
  have hCharn : 0 < max (K ^ 16) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨max (K ^ 16) 1, hCharn, fun A u hEll hu heq hnonneg ↦ ?_⟩
  refine sSup_image_le_mul_sInf_image (Metric.nonempty_ball.mpr one_pos) hCharn
    fun x hx y hy ↦ ?_
  exact (le_pow_mul_of_forall_mem_ball hK.le (Hstep A u hEll hu heq hnonneg) hx hy).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (hnonneg y (Metric.ball_subset_ball (by norm_num) hy)))

/-- **33.15**, Harnack and Hölder estimates in the classical-solution subcase.
Measurability of `A` is not required: the classical equation uses only pointwise values. -/
theorem krylov_safonov_classical {d : ℕ} (hd : 0 < d) {ell Λ : ℝ} :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧
    ∀ (A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
      (u : EuclideanSpace ℝ (Fin d) → ℝ),
      IsUniformlyEllipticOn A ell Λ (Metric.ball 0 2) →
      ContDiffOn ℝ 2 u (Metric.ball 0 2) →
      (∀ x ∈ Metric.ball 0 2, nondivergencePrincipal A u x = 0) →
      holderSeminormOn α u (Metric.ball 0 1) ≤
        ENNReal.ofReal C * uniformGaugeOn u (Metric.ball 0 2) ∧
      ((∀ x ∈ Metric.ball 0 2, 0 ≤ u x) →
        sSup (u '' Metric.ball 0 1) ≤ C * sInf (u '' Metric.ball 0 1)) := by
  by_cases hEL : 0 < ell ∧ ell ≤ Λ
  · obtain ⟨α, Ch, hα, hα1, hCh, Hh⟩ := krylov_safonov_holder hd hEL
    obtain ⟨Charn, hCharn, Hn⟩ := krylov_safonov_harnack hd hEL
    refine ⟨α, max Ch Charn, hα, hα1, lt_max_of_lt_left hCh, fun A u hEll hu heq ↦ ⟨?_, ?_⟩⟩
    · refine (Hh A u hEll hu heq).trans ?_
      gcongr
      exact le_max_left _ _
    · intro hnonneg
      have h0inf : 0 ≤ sInf (u '' Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
        le_csInf ((Metric.nonempty_ball.mpr one_pos).image u) fun b ⟨w, hw, hb⟩ ↦
          hb ▸ hnonneg w (Metric.ball_subset_ball (by norm_num) hw)
      exact (Hn A u hEll hu heq hnonneg).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) h0inf)
  · refine ⟨1 / 2, 1, by positivity, by norm_num, one_pos, fun A u hEll _hu _heq ↦ ?_⟩
    exact absurd ⟨hEll.1, hEll.2.1⟩ hEL

/-- **33.16**: localized variable-coefficient Schauder a priori estimate including lower orders. -/
theorem interior_schauder {d : ℕ} (hd : 0 < d) {α ell Λ : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (c : EuclideanSpace ℝ (Fin d) → ℝ)
    (hA : IsUniformlyEllipticOn A ell Λ (Metric.ball 0 2))
    (hAH : holderGaugeOn α A (Metric.ball 0 2) ≠ ∞)
    (hbH : holderGaugeOn α b (Metric.ball 0 2) ≠ ∞)
    (hcH : holderGaugeOn α c (Metric.ball 0 2) ≠ ∞) :
    ∃ C : ℝ, 0 < C ∧ ∀ u f : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiffOn ℝ 2 u (Metric.ball 0 2) → holderGaugeOn α f (Metric.ball 0 2) ≠ ∞ →
      (∀ x ∈ Metric.ball 0 2, linearEllipticExpression A b c u x = f x) →
      cTwoHolderGauge α u (Metric.ball 0 1) ≤
        ENNReal.ofReal C *
          (uniformGaugeOn u (Metric.ball 0 2) + holderGaugeOn α f (Metric.ball 0 2)) := by
  sorry

/-- **33.18**, the classical interior a priori `W^{2,p}` estimate for `C²` functions, with
continuous principal coefficients and bounded measurable lower-order coefficients. -/
theorem interior_hessian_Lp {d : ℕ} (hd : 0 < d) {p : ℝ} (hp : 1 < p)
    {ell Λ : ℝ}
    (A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (c : EuclideanSpace ℝ (Fin d) → ℝ)
    (hA : IsUniformlyEllipticOn A ell Λ (Metric.ball 0 2))
    (hAc : ContinuousOn A (Metric.ball 0 2))
    (hb : Measurable b) (hc : Measurable c)
    (hbb : uniformGaugeOn b (Metric.ball 0 2) ≠ ∞)
    (hcb : uniformGaugeOn c (Metric.ball 0 2) ≠ ∞) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiffOn ℝ 2 u (Metric.ball 0 2) →
      eLpNorm (fderiv ℝ (fderiv ℝ u)) (ENNReal.ofReal p) (volume.restrict (Metric.ball 0 1)) ≤
        ENNReal.ofReal C * (eLpNorm (linearEllipticExpression A b c u) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball 0 2)) +
          eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball 0 2))) := by
  sorry

/-- Weak `p`-harmonicity using the actual weak-gradient component of `W^{1,p}`.
The identity is a Bochner integral, so a non-integrable integrand has integral `0`.
The exponent uses `p.toReal`, and `ENNReal.toReal ⊤ = 0`. -/
@[expose]
def IsWeakPHarmonic {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))) (u : TauCeti.W1p volume Ω p) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, IsCompactSmoothTestOn Ω φ →
    ∫ x in Ω, ‖(TauCeti.W1p.gradient u) x‖ ^ (p.toReal - 2) *
      ⟪(TauCeti.W1p.gradient u) x, gradient φ x⟫_ℝ = 0

/-- The defining test identity of weak `p`-harmonicity. -/
theorem isWeakPHarmonic_iff {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} {u : TauCeti.W1p volume Ω p} :
    IsWeakPHarmonic Ω u ↔ ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, IsCompactSmoothTestOn Ω φ →
      ∫ x in Ω, ‖(TauCeti.W1p.gradient u) x‖ ^ (p.toReal - 2) *
        ⟪(TauCeti.W1p.gradient u) x, gradient φ x⟫_ℝ = 0 :=
  Iff.rfl

/-- **33.34**: local `C^{1,α}` representatives and the nonnegative Harnack inequality. -/
theorem weakPHarmonic_regular {d : ℕ} (hd : 0 < d) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hp_top : p < ∞) : ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧
    ∀ u : TauCeti.W1p volume (euclideanOpenBall d 2) p,
      IsWeakPHarmonic (euclideanOpenBall d 2) u →
      ∃ v : EuclideanSpace ℝ (Fin d) → ℝ,
        v =ᵐ[volume.restrict (Metric.ball 0 1)] (TauCeti.W1p.value u) ∧ ContDiffOn ℝ 1 v
          (Metric.ball 0 1) ∧
        holderSeminormOn α (fderiv ℝ v) (Metric.ball 0 1) ≠ ∞ ∧
        ((∀ᵐ x ∂volume.restrict (Metric.ball 0 2), 0 ≤ (TauCeti.W1p.value u) x) →
          sSup (v '' Metric.ball 0 1) ≤ C * sInf (v '' Metric.ball 0 1)) := by
  sorry

end CKMA
