/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import CKMA.Analysis.InnerProductSpace.Frame
public import Mathlib.Data.Finsupp.Basic

import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend
import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# L2 function families, Riesz bounds, and frame bounds

Finite linear combinations use finitely supported coefficients. Riesz bounds compare their L2
energy with coefficient l2 energy; completeness is tested by vanishing integral coefficients
against every L2 vector. Family membership in L2 is explicit in the Riesz and frame predicates.

The integral coefficients use conjugation on the family element, agreeing with Mathlib's
second-variable-linear L2 inner product. Actual function representatives are separated from their
a.e. equivalence classes, and frame energies are extended nonnegative sums over arbitrary indices.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate

/-- The canonical L2 vectors associated with a family of square-integrable representatives. -/
def l2FamilyVectors {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : ι → X → ℂ) (hf : ∀ i, MemLp (f i) 2 μ) : ι → Lp ℂ 2 μ :=
  fun i ↦ (hf i).toLp (f i)

/-- Integral coefficients of a function family are its Hilbert-space inner products. -/
theorem inner_l2FamilyVectors {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : ι → X → ℂ) (hf : ∀ i, MemLp (f i) 2 μ) (i : ι) (u : Lp ℂ 2 μ) :
    inner ℂ (l2FamilyVectors f hf i) u = ∫ x, conj (f i x) * u x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hf i).coeFn_toLp] with x hx
  simp only [l2FamilyVectors] at *
  rw [hx]
  simp [mul_comm]

/-- A finite linear combination of a function family. -/
def l2FunctionCombination {X ι : Type*} (f : ι → X → ℂ) (c : ι →₀ ℂ) (x : X) : ℂ :=
  c.sum (fun i z ↦ z * f i x)

/-- Squared coefficient l2 size, as a nonnegative extended real. -/
def finiteCoefficientEnergy {ι : Type*} (c : ι →₀ ℂ) : ℝ≥0∞ :=
  c.sum (fun _ z ↦ ENNReal.ofReal (‖z‖ ^ 2))

/-- An L2 Riesz sequence, specified by uniform lower and upper finite-coefficient bounds. -/
def IsL2RieszSequence {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ι → X → ℂ) : Prop :=
  (∀ i, MemLp (f i) 2 μ) ∧ ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧ ∀ c : ι →₀ ℂ,
    ENNReal.ofReal A * finiteCoefficientEnergy c ≤ (eLpNorm (l2FunctionCombination f c) 2 μ) ^ 2 ∧
      (eLpNorm (l2FunctionCombination f c) 2 μ) ^ 2 ≤ ENNReal.ofReal B * finiteCoefficientEnergy c

/-- An orthogonality test on a function family: vanishing coefficients force a zero L2 class.
Square-integrability of the family itself is supplied separately in the Riesz/frame predicates. -/
def IsL2CompleteFamily {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ι → X → ℂ) : Prop :=
  ∀ u : Lp ℂ 2 μ, (∀ i, ∫ x, conj (f i x) * u x ∂μ = 0) → u = 0

/-- A Riesz basis is a complete Riesz sequence. -/
def IsL2RieszBasis {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ι → X → ℂ) : Prop :=
  IsL2RieszSequence μ f ∧ IsL2CompleteFamily μ f

/-- A Riesz basis has the finite-coefficient bounds of a Riesz sequence. -/
theorem IsL2RieszBasis.isRieszSequence {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : ι → X → ℂ} (hf : IsL2RieszBasis μ f) : IsL2RieszSequence μ f := hf.1

/-- Frame inequalities for a family of actual measurable L2 representatives. -/
def IsL2FrameFamily {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ι → X → ℂ) : Prop :=
  (∀ i, MemLp (f i) 2 μ) ∧ ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧ ∀ u : Lp ℂ 2 μ,
    ENNReal.ofReal (A * ‖u‖ ^ 2) ≤
      (∑' i, ENNReal.ofReal (‖∫ x, conj (f i x) * u x ∂μ‖ ^ 2)) ∧
    (∑' i, ENNReal.ofReal (‖∫ x, conj (f i x) * u x ∂μ‖ ^ 2)) ≤
      ENNReal.ofReal (B * ‖u‖ ^ 2)

/-- The representative-based frame inequalities agree with the abstract Hilbert-frame predicate. -/
theorem isL2FrameFamily_iff_isFrame {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : ι → X → ℂ) (hf : ∀ i, MemLp (f i) 2 μ) :
    IsL2FrameFamily μ f ↔ IsFrame (𝕜 := ℂ) (l2FamilyVectors f hf) := by
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
private def l2FiniteCoeff (ι : Type*) : Submodule ℂ (lp (fun _ : ι ↦ ℂ) 2) where
  carrier := {a | (a : ι → ℂ).HasFiniteSupport}
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
private theorem l2FiniteCoeff_dense : DenseRange (l2FiniteCoeff ι).subtypeL := by
  let : DecidableEq ι := Classical.decEq ι
  intro a
  refine mem_closure_of_tendsto
    (lp.hasSum_single (p := 2) (by simp : (2 : ℝ≥0∞) ≠ ⊤) a) ?_
  refine Filter.Eventually.of_forall fun s ↦ ?_
  let finiteSum : lp (fun _ : ι ↦ ℂ) 2 := ∑ i ∈ s, lp.single 2 i (a i)
  have hfin : (finiteSum : ι → ℂ).HasFiniteSupport := by
    rw [HasFiniteSupport, lp.coeFn_sum]
    refine s.finite_toSet.subset ?_
    intro j hj
    by_contra hjs
    have hzero : (∑ i ∈ s, (lp.single 2 i (a i) : ι → ℂ)) j = 0 := by
      simp only [Finset.sum_apply, lp.coeFn_single]
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      have hne : j ≠ i := fun h ↦ hjs (h ▸ hi)
      simp [Pi.single_eq_of_ne hne]
    exact hj hzero
  exact ⟨⟨finiteSum, hfin⟩, by simp [finiteSum, Submodule.subtypeL_apply]⟩

/-- The inclusion of finitely supported sequences is uniform inducing. -/
private theorem l2FiniteCoeff_isUniformInducing :
    IsUniformInducing (l2FiniteCoeff ι).subtypeL := by
  rw [Submodule.coe_subtypeL, Submodule.coe_subtype]
  exact isUniformInducing_val ((l2FiniteCoeff ι) : Set (lp (fun _ : ι ↦ ℂ) 2))

/-- Membership in the finite-coefficient submodule is finite support as a function. -/
private theorem l2FiniteCoeff_mem_iff (a : lp (fun _ : ι ↦ ℂ) 2) :
    a ∈ l2FiniteCoeff ι ↔ (a : ι → ℂ).HasFiniteSupport := by
  simp [l2FiniteCoeff, Set.mem_ofPred_eq]

/-- The coefficient function of a finitely supported `ℓ²` vector. -/
private def l2FiniteToFinsupp (a : l2FiniteCoeff ι) : ι →₀ ℂ :=
  ofSupportFinite (⇑a.1) ((l2FiniteCoeff_mem_iff a.1).mp a.2)

/-- Coefficient reading agrees with the underlying function. -/
@[simp] private theorem l2FiniteToFinsupp_apply (a : l2FiniteCoeff ι) :
    (l2FiniteToFinsupp a : ι → ℂ) = ⇑(a : lp (fun _ : ι ↦ ℂ) 2) :=
  ofSupportFinite_coe

/-- Reading coefficients is linear on finitely supported `ℓ²` vectors. -/
private def l2FiniteToFinsuppₗ : l2FiniteCoeff ι →ₗ[ℂ] (ι →₀ ℂ) where
  toFun := l2FiniteToFinsupp
  map_add' a b := by
    ext i
    simp only [l2FiniteToFinsupp_apply, Submodule.coe_add, lp.coeFn_add, coe_add, Pi.add_apply]
  map_smul' c a := by
    ext i
    simp only [l2FiniteToFinsupp_apply, Submodule.coe_smul, lp.coeFn_smul, coe_smul,
      Pi.smul_apply, RingHom.id_apply]

/-- Finite `L²` synthesis, as a linear combination of the canonical vectors. -/
private def l2FiniteSynthesisₗ (f : ι → X → ℂ) (hf : ∀ i, MemLp (f i) 2 μ) :
    l2FiniteCoeff ι →ₗ[ℂ] Lp ℂ 2 μ :=
  (linearCombination ℂ (l2FamilyVectors f hf)).comp l2FiniteToFinsuppₗ

/-- Finite synthesis is the `L²` linear combination of the coefficient function. -/
private theorem l2FiniteSynthesisₗ_apply (f : ι → X → ℂ) (hf : ∀ i, MemLp (f i) 2 μ)
    (a : l2FiniteCoeff ι) :
    l2FiniteSynthesisₗ f hf a =
      linearCombination ℂ (l2FamilyVectors f hf) (l2FiniteToFinsupp a) := by
  simp [l2FiniteSynthesisₗ, l2FiniteToFinsuppₗ, LinearMap.comp_apply]

/-- A finite linear combination agrees almost everywhere with its pointwise formula. -/
private theorem linearCombination_ae_eq_l2FunctionCombination (f : ι → X → ℂ)
    (hf : ∀ i, MemLp (f i) 2 μ) (c : ι →₀ ℂ) :
    (linearCombination ℂ (l2FamilyVectors f hf) c : X → ℂ) =ᵐ[μ] l2FunctionCombination f c := by
  set v : ι → Lp ℂ 2 μ := l2FamilyVectors f hf
  have hlin : (linearCombination ℂ v c : Lp ℂ 2 μ) = ∑ i ∈ c.support, c i • v i := by
    rw [linearCombination_apply, sum]
  rw [hlin]
  have hpt : ∀ᵐ x ∂μ, ∀ i ∈ (c.support : Set ι), (c i • v i : Lp ℂ 2 μ) x = c i * f i x := by
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
private theorem eLpNorm_sq_eq_ofReal_norm_sq (u : Lp ℂ 2 μ) :
    (eLpNorm u 2 μ) ^ 2 = ENNReal.ofReal (‖u‖ ^ 2) := by
  rw [← Lp.enorm_def, ← ofReal_norm]
  exact (ENNReal.ofReal_pow (norm_nonneg u) 2).symm

/-- Coefficient energy of a finite sequence is its squared `ℓ²` norm. -/
private theorem finiteCoefficientEnergy_eq_ofReal_norm_sq (a : l2FiniteCoeff ι) :
    finiteCoefficientEnergy (l2FiniteToFinsupp a) =
      ENNReal.ofReal (‖(a : lp (fun _ : ι ↦ ℂ) 2)‖ ^ 2) := by
  have hrpow := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (a : lp (fun _ : ι ↦ ℂ) 2)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hrpow
  have htsum : ∑' i, ‖(a : lp (fun _ : ι ↦ ℂ) 2) i‖ ^ 2 =
      ∑ i ∈ (l2FiniteToFinsupp a).support, ‖(a : lp (fun _ : ι ↦ ℂ) 2) i‖ ^ 2 := by
    rw [tsum_eq_sum]
    intro i hi
    have h0 : (a : lp (fun _ : ι ↦ ℂ) 2) i = 0 := by
      simpa [l2FiniteToFinsupp_apply] using notMem_support_iff.mp hi
    simp [h0]
  rw [finiteCoefficientEnergy, sum, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ sq_nonneg _)]
  simp_rw [l2FiniteToFinsupp_apply]
  exact congrArg ENNReal.ofReal (htsum.symm.trans hrpow.symm)

/-- Riesz bounds restrict to norm bounds for finite synthesis. -/
private theorem l2FiniteSynthesis_norm_bounds (f : ι → X → ℂ) (hf : ∀ i, MemLp (f i) 2 μ)
    {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    (hbounds : ∀ c : ι →₀ ℂ,
      ENNReal.ofReal A * finiteCoefficientEnergy c ≤
          (eLpNorm (l2FunctionCombination f c) 2 μ) ^ 2 ∧
        (eLpNorm (l2FunctionCombination f c) 2 μ) ^ 2 ≤
          ENNReal.ofReal B * finiteCoefficientEnergy c)
    (a : l2FiniteCoeff ι) :
    Real.sqrt A * ‖a‖ ≤ ‖l2FiniteSynthesisₗ f hf a‖ ∧
      ‖l2FiniteSynthesisₗ f hf a‖ ≤ Real.sqrt B * ‖a‖ := by
  set c : ι →₀ ℂ := l2FiniteToFinsupp a
  set S : Lp ℂ 2 μ := l2FiniteSynthesisₗ f hf a
  have hS : S = linearCombination ℂ (l2FamilyVectors f hf) c := l2FiniteSynthesisₗ_apply f hf a
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
theorem IsL2RieszBasis.isFrameFamily {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : ι → X → ℂ} (hf : IsL2RieszBasis μ f) : IsL2FrameFamily μ f := by
  let : DecidableEq ι := Classical.decEq ι
  rcases hf with ⟨⟨hmem, A, B, hA, hAB, hbounds⟩, hcomp⟩
  have hnorm := l2FiniteSynthesis_norm_bounds f hmem hA hAB hbounds
  let S : l2FiniteCoeff ι →L[ℂ] Lp ℂ 2 μ :=
    (l2FiniteSynthesisₗ f hmem).mkContinuous (Real.sqrt B) fun a ↦ (hnorm a).2
  have hdense : DenseRange (l2FiniteCoeff ι).subtypeL := l2FiniteCoeff_dense
  have huni : IsUniformInducing (l2FiniteCoeff ι).subtypeL := l2FiniteCoeff_isUniformInducing
  let T := S.extend (l2FiniteCoeff ι).subtypeL
  have hlow (x : lp (fun _ : ι ↦ ℂ) 2) : Real.sqrt A * ‖x‖ ≤ ‖T x‖ := by
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
  have hclosed : IsClosed (T.range : Set (Lp ℂ 2 μ)) := by
    rw [LinearMap.coe_range]
    exact hanti.isClosed_range T.uniformContinuous
  have hsingle (i : ι) : T (lp.single 2 i (1 : ℂ)) = l2FamilyVectors f hmem i := by
    have hfin : ((lp.single 2 i (1 : ℂ) : lp (fun _ : ι ↦ ℂ) 2) : ι → ℂ).HasFiniteSupport := by
      rw [Function.HasFiniteSupport, lp.coeFn_single]
      refine (Set.finite_singleton i).subset ?_
      intro j
      simp only [Function.mem_support, Set.mem_singleton_iff, ne_eq]
      rw [not_imp_comm]
      intro h
      exact Pi.single_eq_of_ne (M := fun _ ↦ ℂ) h (1 : ℂ)
    let a : l2FiniteCoeff ι := ⟨lp.single 2 i (1 : ℂ), hfin⟩
    have ha : (l2FiniteCoeff ι).subtypeL a = lp.single 2 i (1 : ℂ) := by
      rw [Submodule.subtypeL_apply]
    rw [← ha, ContinuousLinearMap.extend_eq S hdense huni, LinearMap.mkContinuous_apply,
      l2FiniteSynthesisₗ_apply, Finsupp.linearCombination_apply]
    rw [Finsupp.sum_eq_single i]
    · simp [l2FiniteToFinsupp_apply, a, one_smul]
    · intro b hb hbi
      have hzero : l2FiniteToFinsupp a b = 0 := by
        rw [l2FiniteToFinsupp_apply]
        rw [show (a : lp (fun _ : ι ↦ ℂ) 2) = lp.single 2 i (1 : ℂ) from rfl]
        rw [lp.coeFn_single]
        exact Pi.single_eq_of_ne (M := fun _ ↦ ℂ) hbi (1 : ℂ)
      exfalso
      exact hb hzero
    · simp
  have hcoord (u : Lp ℂ 2 μ) (i : ι) :
      (T.adjoint u) i = inner ℂ (l2FamilyVectors f hmem i) u := by
    have hinner := T.adjoint_inner_right (lp.single 2 i (1 : ℂ)) u
    rw [hsingle i, lp.inner_single_left] at hinner
    simpa [RCLike.inner_apply'] using hinner
  have hker : T.adjoint.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    apply hcomp
    intro i
    rw [← inner_l2FamilyVectors f hmem i u, ← hcoord u i]
    have hzero : (T.adjoint u) i = (0 : lp (fun _ : ι ↦ ℂ) 2) i :=
      congr_arg (fun v : lp (fun _ : ι ↦ ℂ) 2 ↦ v i) hu
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

end CKMA
