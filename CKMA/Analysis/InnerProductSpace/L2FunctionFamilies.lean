/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import CKMA.Analysis.InnerProductSpace.Frame

import Mathlib.Algebra.FiniteSupport.Basic

/-!
# L2 function families, Riesz bounds, and frame bounds

Finite linear combinations use finitely supported coefficients over `RCLike` scalars `𝕜`.
Riesz bounds compare their `L²` energy with coefficient `ℓ²` energy; completeness is tested by
vanishing integral coefficients against every `L²` vector. Family membership in `L²` is explicit
in the Riesz and frame predicates.

The integral coefficients use conjugation on the family element, agreeing with Mathlib's
second-variable-linear `L²` inner product. Actual function representatives are separated from their
a.e. equivalence classes, and frame energies are extended nonnegative sums over arbitrary indices.

## Main definitions

* `CKMA.l2FamilyVectors`: canonical `Lp 𝕜 2 μ` vectors associated with square-integrable
  representatives.
* `CKMA.l2FunctionCombination`: finite linear combination of a function family.
* `CKMA.finiteCoefficientEnergy`: squared `ℓ²` norm of finitely supported coefficients.
* `CKMA.IsL2RieszSequence`, `CKMA.IsL2CompleteFamily`, `CKMA.IsL2RieszBasis`,
  `CKMA.IsL2FrameFamily`: `L²` Riesz sequence, completeness, Riesz basis, and frame predicates.

## Main results

* `CKMA.inner_l2FamilyVectors`: integral formula for inner products with `l2FamilyVectors`.
* `CKMA.isL2FrameFamily_iff_isFrame`: equivalence between `IsL2FrameFamily` and `IsFrame`.
* `CKMA.IsL2RieszBasis.isL2FrameFamily`: every `L²` Riesz basis is an `L²` frame family.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The canonical L2 vectors associated with a family of square-integrable representatives. -/
@[expose]
def l2FamilyVectors {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : ι → X → 𝕜) (hf : ∀ i, MemLp (f i) 2 μ) : ι → Lp 𝕜 2 μ :=
  fun i ↦ (hf i).toLp (f i)

/-- Integral coefficients of a function family are its Hilbert-space inner products. -/
theorem inner_l2FamilyVectors {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : ι → X → 𝕜) (hf : ∀ i, MemLp (f i) 2 μ) (i : ι) (u : Lp 𝕜 2 μ) :
    inner 𝕜 (l2FamilyVectors f hf i) u = ∫ x, conj (f i x) * u x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hf i).coeFn_toLp] with x hx
  simp only [l2FamilyVectors] at *
  rw [hx]
  simp [RCLike.inner_apply, mul_comm]

/-- A finite linear combination of a function family. -/
@[expose]
def l2FunctionCombination {X ι : Type*} (f : ι → X → 𝕜) (c : ι →₀ 𝕜) (x : X) : 𝕜 :=
  c.sum (fun i z ↦ z * f i x)

/-- Squared coefficient l2 size, as a nonnegative extended real. -/
@[expose]
def finiteCoefficientEnergy {ι : Type*} (c : ι →₀ 𝕜) : ℝ≥0∞ :=
  c.sum (fun _ z ↦ ENNReal.ofReal (‖z‖ ^ 2))

/-- An L2 Riesz sequence, specified by uniform lower and upper finite-coefficient bounds. -/
@[expose]
def IsL2RieszSequence {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ι → X → 𝕜) : Prop :=
  (∀ i, MemLp (f i) 2 μ) ∧ ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧ ∀ c : ι →₀ 𝕜,
    ENNReal.ofReal A * finiteCoefficientEnergy c ≤ (eLpNorm (l2FunctionCombination f c) 2 μ) ^ 2 ∧
      (eLpNorm (l2FunctionCombination f c) 2 μ) ^ 2 ≤ ENNReal.ofReal B * finiteCoefficientEnergy c

/-- An orthogonality test on a function family: vanishing coefficients force a zero L2 class.
Square-integrability of the family itself is supplied separately in the Riesz/frame predicates. -/
@[expose]
def IsL2CompleteFamily {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ι → X → 𝕜) : Prop :=
  ∀ u : Lp 𝕜 2 μ, (∀ i, ∫ x, conj (f i x) * u x ∂μ = 0) → u = 0

/-- A Riesz basis is a complete Riesz sequence. -/
@[expose]
def IsL2RieszBasis {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ι → X → 𝕜) : Prop :=
  IsL2RieszSequence μ f ∧ IsL2CompleteFamily μ f

/-- A Riesz basis has the finite-coefficient bounds of a Riesz sequence. -/
theorem IsL2RieszBasis.isL2RieszSequence {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : ι → X → 𝕜} (hf : IsL2RieszBasis μ f) : IsL2RieszSequence μ f := hf.1

@[deprecated (since := "2026-11-15")]
alias IsL2RieszBasis.isRieszSequence := IsL2RieszBasis.isL2RieszSequence

/-- Frame inequalities for a family of actual measurable L2 representatives. -/
@[expose]
def IsL2FrameFamily {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ι → X → 𝕜) : Prop :=
  (∀ i, MemLp (f i) 2 μ) ∧ ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧ ∀ u : Lp 𝕜 2 μ,
    ENNReal.ofReal (A * ‖u‖ ^ 2) ≤
      (∑' i, ENNReal.ofReal (‖∫ x, conj (f i x) * u x ∂μ‖ ^ 2)) ∧
    (∑' i, ENNReal.ofReal (‖∫ x, conj (f i x) * u x ∂μ‖ ^ 2)) ≤
      ENNReal.ofReal (B * ‖u‖ ^ 2)

/-- The representative-based frame inequalities agree with the abstract Hilbert-frame predicate. -/
theorem isL2FrameFamily_iff_isFrame {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : ι → X → 𝕜) (hf : ∀ i, MemLp (f i) 2 μ) :
    IsL2FrameFamily μ f ↔ IsFrame (𝕜 := 𝕜) (l2FamilyVectors f hf) := by
  constructor
  · rintro ⟨_, A, B, hA, hAB, h⟩
    exact ⟨A, B, hA, hAB, fun u ↦ by
      simpa only [frameEnergy, inner_l2FamilyVectors] using h u⟩
  · rintro ⟨A, B, hA, hAB, h⟩
    exact ⟨hf, A, B, hA, hAB, fun u ↦ by
      simpa only [frameEnergy, inner_l2FamilyVectors] using h u⟩

section L2RieszFrame

open Finsupp Function

variable {X ι : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Finitely supported coefficient sequences, with the induced `ℓ²` norm. -/
private def l2FiniteCoeff (𝕜 ι : Type*) [RCLike 𝕜] : Submodule 𝕜 (lp (fun _ : ι ↦ 𝕜) 2) where
  carrier := {a | (a : ι → 𝕜).HasFiniteSupport}
  zero_mem' := by
    rw [Set.mem_ofPred_eq, lp.coeFn_zero]
    exact hasFiniteSupport_zero
  add_mem' := by
    intro a b ha hb
    rw [Set.mem_ofPred_eq] at ha hb ⊢
    rw [lp.coeFn_add]
    exact ha.add hb
  smul_mem' := by
    intro c a ha
    rw [Set.mem_ofPred_eq] at ha ⊢
    rw [lp.coeFn_smul]
    rw [HasFiniteSupport] at ha ⊢
    exact ha.subset (support_const_smul_subset c _)

/-- Finite sequences are dense in `ℓ²`: the canonical single-vector sums converge. -/
private theorem l2FiniteCoeff_dense : DenseRange (l2FiniteCoeff 𝕜 ι).subtypeL := by
  let : DecidableEq ι := Classical.decEq ι
  intro a
  refine mem_closure_of_tendsto
    (lp.hasSum_single (p := 2) (by simp : (2 : ℝ≥0∞) ≠ ⊤) a) ?_
  refine Filter.Eventually.of_forall fun s ↦ ?_
  let finiteSum : lp (fun _ : ι ↦ 𝕜) 2 := ∑ i ∈ s, lp.single 2 i (a i)
  have hfin : (finiteSum : ι → 𝕜).HasFiniteSupport := by
    rw [HasFiniteSupport, lp.coeFn_sum]
    refine s.finite_toSet.subset ?_
    intro j hj
    by_contra hjs
    have hzero : (∑ i ∈ s, (lp.single 2 i (a i) : ι → 𝕜)) j = 0 := by
      simp only [Finset.sum_apply, lp.coeFn_single]
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      have hne : j ≠ i := fun h ↦ hjs (h ▸ hi)
      simp [Pi.single_eq_of_ne hne]
    exact hj hzero
  exact ⟨⟨finiteSum, hfin⟩, by simp [finiteSum, Submodule.subtypeL_apply]⟩

/-- The inclusion of finitely supported sequences is uniform inducing. -/
private theorem l2FiniteCoeff_isUniformInducing :
    IsUniformInducing (l2FiniteCoeff 𝕜 ι).subtypeL := by
  rw [Submodule.coe_subtypeL, Submodule.coe_subtype]
  exact isUniformInducing_val ((l2FiniteCoeff 𝕜 ι) : Set (lp (fun _ : ι ↦ 𝕜) 2))

/-- Membership in the finite-coefficient submodule is finite support as a function. -/
private theorem l2FiniteCoeff_mem_iff (a : lp (fun _ : ι ↦ 𝕜) 2) :
    a ∈ l2FiniteCoeff 𝕜 ι ↔ (a : ι → 𝕜).HasFiniteSupport := by
  simp [l2FiniteCoeff, Set.mem_ofPred_eq]

/-- The coefficient function of a finitely supported `ℓ²` vector. -/
private def l2FiniteToFinsupp (a : l2FiniteCoeff 𝕜 ι) : ι →₀ 𝕜 :=
  ofSupportFinite (⇑a.1) ((l2FiniteCoeff_mem_iff a.1).mp a.2)

/-- Coefficient reading agrees with the underlying function. -/
@[simp]
private theorem l2FiniteToFinsupp_apply (a : l2FiniteCoeff 𝕜 ι) :
    (l2FiniteToFinsupp a : ι → 𝕜) = ⇑(a : lp (fun _ : ι ↦ 𝕜) 2) :=
  ofSupportFinite_coe

/-- Reading coefficients is linear on finitely supported `ℓ²` vectors. -/
private def l2FiniteToFinsuppₗ : l2FiniteCoeff 𝕜 ι →ₗ[𝕜] (ι →₀ 𝕜) where
  toFun := l2FiniteToFinsupp
  map_add' a b := by
    ext i
    simp only [l2FiniteToFinsupp_apply, Submodule.coe_add, lp.coeFn_add, coe_add, Pi.add_apply]
  map_smul' c a := by
    ext i
    simp only [l2FiniteToFinsupp_apply, Submodule.coe_smul, lp.coeFn_smul, coe_smul,
      Pi.smul_apply, RingHom.id_apply]

/-- Finite `L²` synthesis, as a linear combination of the canonical vectors. -/
private def l2FiniteSynthesisₗ (f : ι → X → 𝕜) (hf : ∀ i, MemLp (f i) 2 μ) :
    l2FiniteCoeff 𝕜 ι →ₗ[𝕜] Lp 𝕜 2 μ :=
  (linearCombination 𝕜 (l2FamilyVectors f hf)).comp l2FiniteToFinsuppₗ

/-- Finite synthesis is the `L²` linear combination of the coefficient function. -/
private theorem l2FiniteSynthesisₗ_apply (f : ι → X → 𝕜) (hf : ∀ i, MemLp (f i) 2 μ)
    (a : l2FiniteCoeff 𝕜 ι) :
    l2FiniteSynthesisₗ f hf a =
      linearCombination 𝕜 (l2FamilyVectors f hf) (l2FiniteToFinsupp a) := by
  simp [l2FiniteSynthesisₗ, l2FiniteToFinsuppₗ, LinearMap.comp_apply]

/-- A finite linear combination agrees almost everywhere with its pointwise formula. -/
private theorem linearCombination_ae_eq_l2FunctionCombination (f : ι → X → 𝕜)
    (hf : ∀ i, MemLp (f i) 2 μ) (c : ι →₀ 𝕜) :
    (linearCombination 𝕜 (l2FamilyVectors f hf) c : X → 𝕜) =ᵐ[μ] l2FunctionCombination f c := by
  set v : ι → Lp 𝕜 2 μ := l2FamilyVectors f hf
  have hlin : (linearCombination 𝕜 v c : Lp 𝕜 2 μ) = ∑ i ∈ c.support, c i • v i := by
    rw [linearCombination_apply, sum]
  rw [hlin]
  have hpt : ∀ᵐ x ∂μ, ∀ i ∈ (c.support : Set ι), (c i • v i : Lp 𝕜 2 μ) x = c i * f i x := by
    rw [ae_ball_iff c.support.countable_toSet]
    intro i hi
    filter_upwards [Lp.coeFn_smul (c i) (v i), (hf i).coeFn_toLp] with x hsm hto
    rw [hsm]
    simp only [Pi.smul_apply, smul_eq_mul, v, l2FamilyVectors, hto]
  filter_upwards [Lp.coeFn_fun_finsetSum c.support (fun i ↦ c i • v i), hpt] with x hx hptx
  simp only [l2FunctionCombination, sum]
  rw [hx]
  exact Finset.sum_congr rfl fun i hi ↦ hptx i hi

/-- Squared `L²` norm, written as an extended real. -/
private theorem eLpNorm_sq_eq_ofReal_norm_sq (u : Lp 𝕜 2 μ) :
    (eLpNorm u 2 μ) ^ 2 = ENNReal.ofReal (‖u‖ ^ 2) := by
  rw [← Lp.enorm_def, ← ofReal_norm]
  exact (ENNReal.ofReal_pow (norm_nonneg u) 2).symm

/-- Coefficient energy of a finite sequence is its squared `ℓ²` norm. -/
private theorem finiteCoefficientEnergy_eq_ofReal_norm_sq (a : l2FiniteCoeff 𝕜 ι) :
    finiteCoefficientEnergy (l2FiniteToFinsupp a) =
      ENNReal.ofReal (‖(a : lp (fun _ : ι ↦ 𝕜) 2)‖ ^ 2) := by
  have hrpow := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (a : lp (fun _ : ι ↦ 𝕜) 2)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hrpow
  have htsum : ∑' i, ‖(a : lp (fun _ : ι ↦ 𝕜) 2) i‖ ^ 2 =
      ∑ i ∈ (l2FiniteToFinsupp a).support, ‖(a : lp (fun _ : ι ↦ 𝕜) 2) i‖ ^ 2 := by
    rw [tsum_eq_sum]
    intro i hi
    have h0 : (a : lp (fun _ : ι ↦ 𝕜) 2) i = 0 := by
      simpa [l2FiniteToFinsupp_apply] using notMem_support_iff.mp hi
    simp [h0]
  rw [finiteCoefficientEnergy, sum, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ sq_nonneg _)]
  simp_rw [l2FiniteToFinsupp_apply]
  exact congrArg ENNReal.ofReal (htsum.symm.trans hrpow.symm)

/-- Riesz bounds restrict to norm bounds for finite synthesis. -/
private theorem l2FiniteSynthesis_norm_bounds (f : ι → X → 𝕜) (hf : ∀ i, MemLp (f i) 2 μ)
    {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    (hbounds : ∀ c : ι →₀ 𝕜,
      ENNReal.ofReal A * finiteCoefficientEnergy c ≤
          (eLpNorm (l2FunctionCombination f c) 2 μ) ^ 2 ∧
        (eLpNorm (l2FunctionCombination f c) 2 μ) ^ 2 ≤
          ENNReal.ofReal B * finiteCoefficientEnergy c)
    (a : l2FiniteCoeff 𝕜 ι) :
    Real.sqrt A * ‖a‖ ≤ ‖l2FiniteSynthesisₗ f hf a‖ ∧
      ‖l2FiniteSynthesisₗ f hf a‖ ≤ Real.sqrt B * ‖a‖ := by
  set c : ι →₀ 𝕜 := l2FiniteToFinsupp a
  set S : Lp 𝕜 2 μ := l2FiniteSynthesisₗ f hf a
  have hS : S = linearCombination 𝕜 (l2FamilyVectors f hf) c := l2FiniteSynthesisₗ_apply f hf a
  have hnormSq : (eLpNorm (l2FunctionCombination f c) 2 μ) ^ 2 = ENNReal.ofReal (‖S‖ ^ 2) := by
    rw [eLpNorm_congr_ae (linearCombination_ae_eq_l2FunctionCombination f hf c).symm, ← hS]
    exact eLpNorm_sq_eq_ofReal_norm_sq S
  have henergy := finiteCoefficientEnergy_eq_ofReal_norm_sq a
  have hB : 0 ≤ B := hA.le.trans hAB
  obtain ⟨hlo, hup⟩ := hbounds c
  rw [hnormSq, henergy, ← ENNReal.ofReal_mul hA.le, Submodule.norm_coe] at hlo
  rw [hnormSq, henergy, ← ENNReal.ofReal_mul hB, Submodule.norm_coe] at hup
  have hlo' : A * ‖a‖ ^ 2 ≤ ‖S‖ ^ 2 := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 hlo
  have hup' : ‖S‖ ^ 2 ≤ B * ‖a‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB (sq_nonneg _))).1 hup
  refine ⟨?_, ?_⟩
  · have hsq := Real.sqrt_le_sqrt hlo'
    rwa [Real.sqrt_mul hA.le, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hsq
  · have hsq := Real.sqrt_le_sqrt hup'
    rwa [Real.sqrt_mul hB, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hsq

end L2RieszFrame

/-- Every Riesz basis is a frame in its whole Hilbert space. -/
theorem IsL2RieszBasis.isL2FrameFamily {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : ι → X → 𝕜} (hf : IsL2RieszBasis μ f) : IsL2FrameFamily μ f := by
  let : DecidableEq ι := Classical.decEq ι
  rcases hf with ⟨⟨hmem, A, B, hA, hAB, hbounds⟩, hcomp⟩
  have hnorm := l2FiniteSynthesis_norm_bounds f hmem hA hAB hbounds
  let S : l2FiniteCoeff 𝕜 ι →L[𝕜] Lp 𝕜 2 μ :=
    (l2FiniteSynthesisₗ f hmem).mkContinuous (Real.sqrt B) fun a ↦ (hnorm a).2
  have hdense : DenseRange (l2FiniteCoeff 𝕜 ι).subtypeL := l2FiniteCoeff_dense
  have huni : IsUniformInducing (l2FiniteCoeff 𝕜 ι).subtypeL := l2FiniteCoeff_isUniformInducing
  let T := S.extend (l2FiniteCoeff 𝕜 ι).subtypeL
  have hlow (x : lp (fun _ : ι ↦ 𝕜) 2) : Real.sqrt A * ‖x‖ ≤ ‖T x‖ := by
    refine hdense.induction_on x ?_ ?_
    · exact isClosed_le (continuous_const.mul continuous_norm)
        (continuous_norm.comp T.continuous)
    · intro a
      rw [ContinuousLinearMap.extend_eq S hdense huni, LinearMap.mkContinuous_apply]
      exact (hnorm a).1
  let K : NNReal :=
    .mk ((Real.sqrt A)⁻¹) (inv_nonneg.mpr (Real.sqrt_nonneg A))
  have hanti : AntilipschitzWith K T :=
    T.antilipschitz_of_bound fun x ↦ by
      have hmul : (Real.sqrt A)⁻¹ * ‖T x‖ = K * ‖T x‖ := by
        simp only [K, NNReal.coe_mk]
      rw [← hmul]
      exact (le_inv_mul_iff₀ (Real.sqrt_pos.mpr hA)).2 (hlow x)
  have hclosed : IsClosed (T.range : Set (Lp 𝕜 2 μ)) := by
    rw [LinearMap.coe_range]
    exact hanti.isClosed_range T.uniformContinuous
  have hsingle (i : ι) : T (lp.single 2 i (1 : 𝕜)) = l2FamilyVectors f hmem i := by
    have hfin : ((lp.single 2 i (1 : 𝕜) : lp (fun _ : ι ↦ 𝕜) 2) : ι → 𝕜).HasFiniteSupport := by
      rw [Function.HasFiniteSupport, lp.coeFn_single]
      refine (Set.finite_singleton i).subset ?_
      intro j
      simp only [Function.mem_support, Set.mem_singleton_iff, ne_eq]
      rw [not_imp_comm]
      intro h
      exact Pi.single_eq_of_ne (M := fun _ ↦ 𝕜) h (1 : 𝕜)
    let a : l2FiniteCoeff 𝕜 ι := ⟨lp.single 2 i (1 : 𝕜), hfin⟩
    have ha : (l2FiniteCoeff 𝕜 ι).subtypeL a = lp.single 2 i (1 : 𝕜) := by
      rw [Submodule.subtypeL_apply]
    rw [← ha, ContinuousLinearMap.extend_eq S hdense huni, LinearMap.mkContinuous_apply,
      l2FiniteSynthesisₗ_apply, Finsupp.linearCombination_apply]
    rw [Finsupp.sum_eq_single i]
    · simp [l2FiniteToFinsupp_apply, a, one_smul]
    · intro b hb hbi
      have hzero : l2FiniteToFinsupp a b = 0 := by
        rw [l2FiniteToFinsupp_apply]
        rw [show (a : lp (fun _ : ι ↦ 𝕜) 2) = lp.single 2 i (1 : 𝕜) from rfl]
        rw [lp.coeFn_single]
        exact Pi.single_eq_of_ne (M := fun _ ↦ 𝕜) hbi (1 : 𝕜)
      exfalso
      exact hb hzero
    · simp
  have hcoord (u : Lp 𝕜 2 μ) (i : ι) :
      (T.adjoint u) i = inner 𝕜 (l2FamilyVectors f hmem i) u := by
    have hinner := T.adjoint_inner_right (lp.single 2 i (1 : 𝕜)) u
    rw [hsingle i, lp.inner_single_left] at hinner
    simpa [RCLike.inner_apply'] using hinner
  have hker : T.adjoint.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    apply hcomp
    intro i
    rw [← inner_l2FamilyVectors f hmem i u, ← hcoord u i]
    have hzero : (T.adjoint u) i = (0 : lp (fun _ : ι ↦ 𝕜) 2) i :=
      congr_arg (fun v : lp (fun _ : ι ↦ 𝕜) 2 ↦ v i) hu
    rw [hzero]
    simp
  have htop : T.range.topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, T.orthogonal_range, hker]
  have hrange : T.range = ⊤ := by
    rw [← hclosed.submodule_topologicalClosure_eq]
    exact htop
  have hsurj : Function.Surjective T := (LinearMap.range_eq_top).1 hrange
  have hC : IsFrameAnalysis (l2FamilyVectors f hmem) T.adjoint := hcoord
  have hsurjAdj : Function.Surjective T.adjoint.adjoint := by
    rw [ContinuousLinearMap.adjoint_adjoint]
    exact hsurj
  exact (isL2FrameFamily_iff_isFrame f hmem).2 (hC.isFrame_of_surjective_adjoint hsurjAdj)

@[deprecated (since := "2026-11-15")]
alias IsL2RieszBasis.isFrameFamily := IsL2RieszBasis.isL2FrameFamily

end CKMA
