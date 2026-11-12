/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import TauCeti.MeasureTheory.Integral.Prod

/-!
# Square-integrable kernels and Hilbert–Schmidt operators

A real or complex L2 kernel on a sigma-finite measure space defines an operator on L2 through
an a.e. integral identity. A supplied, possibly non-countably indexed Hilbert basis records its
exact Hilbert–Schmidt energy without a separability assumption. The adjoint kernel is obtained by
transposing the variables and applying the scalar star. Source: GAPS 25.3; the Hilbert–Schmidt
energy is TauCeti's existing construction.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory ContinuousLinearMap
open scoped ENNReal

variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

/-- An operator has kernel `k` when its `L²` action is given by the integral formula a.e. -/
def HasIntegralKernel (T : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ) (k : X × X → 𝕜) : Prop :=
  ∀ f : Lp 𝕜 2 μ, (fun x ↦ T f x) =ᵐ[μ] fun x ↦ ∫ y, k (x, y) * f y ∂μ

section

variable {μ}

omit [SigmaFinite μ] in
/-- The pointwise product `(x, y) ↦ f x * g y` of two `L²(μ)` functions lies in `L²(μ ⊗ μ)`. -/
private theorem memLp_mul_prod {f g : X → 𝕜} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    MemLp (fun p : X × X ↦ f p.1 * g p.2) 2 (μ.prod μ) := by
  have hfst : AEStronglyMeasurable (fun p : X × X ↦ f p.1) (μ.prod μ) :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hsnd : AEStronglyMeasurable (fun p : X × X ↦ g p.2) (μ.prod μ) :=
    hg.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hmeas : AEStronglyMeasurable (fun p : X × X ↦ f p.1 * g p.2) (μ.prod μ) := hfst.mul hsnd
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hf2 : Integrable (fun x ↦ ‖f x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hg2 : Integrable (fun y ↦ ‖g y‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  refine (hf2.mul_prod hg2).mono' (hmeas.norm.pow 2) (.of_forall fun p ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity), ← mul_pow]
  gcongr
  exact norm_mul_le _ _

/-- The `L²(μ ⊗ μ)` class of the pointwise product of two `L²(μ)` functions. -/
private noncomputable def prodMul (F G : Lp 𝕜 2 μ) : Lp 𝕜 2 (μ.prod μ) :=
  (memLp_mul_prod (Lp.memLp F) (Lp.memLp G)).toLp _

omit [SigmaFinite μ] in
/-- The representative of `prodMul F G` is the pointwise product of the representatives. -/
private theorem coeFn_prodMul (F G : Lp 𝕜 2 μ) :
    ⇑(prodMul F G) =ᵐ[μ.prod μ] fun p : X × X ↦ F p.1 * G p.2 :=
  MemLp.coeFn_toLp _

omit [SigmaFinite μ] in
/-- The tensor product is additive in its first argument. -/
private theorem prodMul_add_left (F₁ F₂ G : Lp 𝕜 2 μ) :
    prodMul (F₁ + F₂) G = prodMul F₁ G + prodMul F₂ G := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_prodMul (F₁ + F₂) G, coeFn_prodMul F₁ G, coeFn_prodMul F₂ G,
    Lp.coeFn_add (prodMul F₁ G) (prodMul F₂ G),
    (Measure.quasiMeasurePreserving_fst (β := X) (ν := μ)).ae (Lp.coeFn_add F₁ F₂)]
    with q h h1 h2 hadd hf
  simp only [h, hadd, Pi.add_apply, h1, h2, hf, add_mul]

omit [SigmaFinite μ] in
/-- The tensor product is additive in its second argument. -/
private theorem prodMul_add_right (F G₁ G₂ : Lp 𝕜 2 μ) :
    prodMul F (G₁ + G₂) = prodMul F G₁ + prodMul F G₂ := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_prodMul F (G₁ + G₂), coeFn_prodMul F G₁, coeFn_prodMul F G₂,
    Lp.coeFn_add (prodMul F G₁) (prodMul F G₂),
    (Measure.quasiMeasurePreserving_snd (α := X) (μ := μ)).ae (Lp.coeFn_add G₁ G₂)]
    with q h h1 h2 hadd hg
  simp only [h, hadd, Pi.add_apply, h1, h2, hg, mul_add]

omit [SigmaFinite μ] in
/-- The tensor product vanishes when its first argument does. -/
private theorem prodMul_zero_left (G : Lp 𝕜 2 μ) : prodMul (0 : Lp 𝕜 2 μ) G = 0 := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_prodMul (0 : Lp 𝕜 2 μ) G, Lp.coeFn_zero 𝕜 2 (μ.prod μ),
    (Measure.quasiMeasurePreserving_fst (β := X) (ν := μ)).ae (Lp.coeFn_zero 𝕜 2 μ)]
    with q h hz hf
  simp only [h, hz, hf, Pi.zero_apply, zero_mul]

omit [SigmaFinite μ] in
/-- The tensor product vanishes when its second argument does. -/
private theorem prodMul_zero_right (F : Lp 𝕜 2 μ) : prodMul F (0 : Lp 𝕜 2 μ) = 0 := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_prodMul F (0 : Lp 𝕜 2 μ), Lp.coeFn_zero 𝕜 2 (μ.prod μ),
    (Measure.quasiMeasurePreserving_snd (α := X) (μ := μ)).ae (Lp.coeFn_zero 𝕜 2 μ)]
    with q h hz hg
  simp only [h, hz, hg, Pi.zero_apply, mul_zero]

omit [SigmaFinite μ] in
/-- The tensor product is homogeneous in its first argument. -/
private theorem prodMul_smul_left (c : 𝕜) (F G : Lp 𝕜 2 μ) :
    prodMul (c • F) G = c • prodMul F G := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_prodMul (c • F) G, coeFn_prodMul F G, Lp.coeFn_smul c (prodMul F G),
    (Measure.quasiMeasurePreserving_fst (β := X) (ν := μ)).ae (Lp.coeFn_smul c F)]
    with q h h1 hsmul hf
  simp [h, hsmul, h1, hf, mul_assoc]

omit [SigmaFinite μ] in
/-- The tensor product is homogeneous in its second argument. -/
private theorem prodMul_smul_right (c : 𝕜) (F G : Lp 𝕜 2 μ) :
    prodMul F (c • G) = c • prodMul F G := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_prodMul F (c • G), coeFn_prodMul F G, Lp.coeFn_smul c (prodMul F G),
    (Measure.quasiMeasurePreserving_snd (α := X) (μ := μ)).ae (Lp.coeFn_smul c G)]
    with q h h1 hsmul hg
  simp [h, hsmul, h1, hg, mul_left_comm]

/-- Inner products of tensors factor as products of the factor inner products. -/
private theorem inner_prodMul (F₁ F₂ G₁ G₂ : Lp 𝕜 2 μ) :
    inner 𝕜 (prodMul F₁ G₁) (prodMul F₂ G₂) = inner 𝕜 F₁ F₂ * inner 𝕜 G₁ G₂ := by
  rw [L2.inner_def]
  calc
    ∫ p, inner 𝕜 (prodMul F₁ G₁ p) (prodMul F₂ G₂ p) ∂(μ.prod μ)
        = ∫ p : X × X, inner 𝕜 (F₁ p.1 * G₁ p.2) (F₂ p.1 * G₂ p.2) ∂(μ.prod μ) := by
          refine integral_congr_ae ?_
          filter_upwards [coeFn_prodMul F₁ G₁, coeFn_prodMul F₂ G₂] with p hp1 hp2
          rw [hp1, hp2]
    _ = ∫ p : X × X, inner 𝕜 (F₁ p.1) (F₂ p.1) * inner 𝕜 (G₁ p.2) (G₂ p.2) ∂(μ.prod μ) := by
          refine integral_congr_ae (.of_forall fun p ↦ ?_)
          simp only [RCLike.inner_apply', map_mul]
          ring
    _ = (∫ x, inner 𝕜 (F₁ x) (F₂ x) ∂μ) * ∫ y, inner 𝕜 (G₁ y) (G₂ y) ∂μ :=
          integral_prod_mul (fun x ↦ inner 𝕜 (F₁ x) (F₂ x)) (fun y ↦ inner 𝕜 (G₁ y) (G₂ y))
    _ = inner 𝕜 F₁ F₂ * inner 𝕜 G₁ G₂ := by rw [← L2.inner_def, ← L2.inner_def]

/-- The tensor construction multiplies norms. -/
private theorem norm_prodMul (F G : Lp 𝕜 2 μ) : ‖prodMul F G‖ = ‖F‖ * ‖G‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), mul_pow]
  exact_mod_cast (by simpa only [inner_self_eq_norm_sq_to_K] using inner_prodMul F F G G :
    ((‖prodMul F G‖ : ℝ) : 𝕜) ^ 2 = ((‖F‖ : ℝ) : 𝕜) ^ 2 * ((‖G‖ : ℝ) : 𝕜) ^ 2)

/-- The tensor product as a bounded bilinear map on `L²`. -/
private noncomputable def prodMulL : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 (μ.prod μ) :=
  LinearMap.mkContinuous₂ (LinearMap.mk₂ 𝕜 prodMul prodMul_add_left prodMul_smul_left
    prodMul_add_right prodMul_smul_right) 1 fun F G ↦ by simp [norm_prodMul]

/-- Evaluating the continuous tensor recovers `prodMul`. -/
private theorem prodMulL_apply (F G : Lp 𝕜 2 μ) : prodMulL F G = prodMul F G :=
  LinearMap.mkContinuous₂_apply _ _ _ _

omit [SigmaFinite μ] in
/-- Starring both arguments of an `L²` inner product swaps them. -/
private theorem inner_star_star (F G : Lp 𝕜 2 μ) :
    inner 𝕜 (star F) (star G) = inner 𝕜 G F := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_star F, Lp.coeFn_star G] with x hF hG
  rw [hF, hG, Pi.star_apply, Pi.star_apply, RCLike.inner_apply', RCLike.inner_apply',
    ← RCLike.star_def, star_star, RCLike.star_def, mul_comm]

omit [SigmaFinite μ] in
/-- Starring the left argument of an `L²` inner product moves the star onto the right argument. -/
private theorem inner_star_left (F G : Lp 𝕜 2 μ) :
    inner 𝕜 (star F) G = inner 𝕜 (star G) F := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_star F, Lp.coeFn_star G] with x hF hG
  simp_rw [hF, hG, Pi.star_apply, RCLike.inner_apply', ← RCLike.star_def, star_star]
  exact mul_comm _ _

omit [SigmaFinite μ] in
/-- Scalar star preserves the `L²` norm. -/
private theorem norm_star_eq (F : Lp 𝕜 2 μ) : ‖star F‖ = ‖F‖ := by
  have h := congrArg RCLike.re (inner_star_star F F)
  rw [← norm_sq_eq_re_inner (𝕜 := 𝕜), ← norm_sq_eq_re_inner (𝕜 := 𝕜)] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

omit [SigmaFinite μ] in
/-- The scalar star of a Hilbert basis is orthonormal. -/
private theorem orthonormal_star {ι : Type*} (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 μ)) :
    Orthonormal 𝕜 (fun i ↦ star (b i)) :=
  ⟨fun i ↦ (norm_star_eq (b i)).trans (b.orthonormal.norm_eq_one i),
    fun i j hij ↦ (inner_star_star (b i) (b j)).trans
      (b.orthonormal.inner_eq_zero hij.symm)⟩

omit [SigmaFinite μ] in
/-- Vectors orthogonal to every starred basis vector vanish. -/
private theorem orthogonal_span_star_eq_bot {ι : Type*} (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 μ)) :
    (Submodule.span 𝕜 (Set.range fun i ↦ star (b i)))ᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun h hh ↦ ?_
  rw [Submodule.mem_orthogonal] at hh
  have hmem : star h ∈ (Submodule.span 𝕜 (Set.range b))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨i, rfl⟩ := hu
      exact inner_eq_zero_symm.mpr ((inner_star_left (b i) h).symm.trans
        (hh _ (Submodule.subset_span ⟨i, rfl⟩)))
    | zero => exact inner_zero_left _
    | add u v _ _ ihu ihv => rw [inner_add_left, ihu, ihv, add_zero]
    | smul c u _ ihu => rw [inner_smul_left, ihu, mul_zero]
  have hbot : (Submodule.span 𝕜 (Set.range b))ᗮ = ⊥ :=
    (Submodule.topologicalClosure_eq_top_iff
      (K := Submodule.span 𝕜 (Set.range b))).mp b.dense_span
  have hzero : star h = 0 := (Submodule.mem_bot (R := 𝕜)).mp (hbot ▸ hmem)
  rw [← star_involutive h, hzero, Lp.ext_iff]
  filter_upwards [Lp.coeFn_star (0 : Lp 𝕜 2 μ), Lp.coeFn_zero 𝕜 2 μ] with x hx h0
  rw [hx, Pi.star_apply, h0, Pi.zero_apply, star_zero]

omit [SigmaFinite μ] in
/-- The starred copy of a supplied Hilbert basis. -/
private noncomputable def hilbertBasis_star {ι : Type*} (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 μ)) :
    HilbertBasis ι 𝕜 (Lp 𝕜 2 μ) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_star b) (orthogonal_span_star_eq_bot b)

omit [SigmaFinite μ] in
/-- The starred basis evaluates to the scalar star of the original basis vector. -/
private theorem hilbertBasis_star_apply {ι : Type*} (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 μ)) (i : ι) :
    hilbertBasis_star b i = star (b i) := by
  rw [hilbertBasis_star, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- A vector orthogonal to every basis tensor is orthogonal to every elementary tensor. -/
private theorem inner_prodMul_eq_zero_of_forall_basis {ι : Type*}
    (b₁ b₂ : HilbertBasis ι 𝕜 (Lp 𝕜 2 μ)) {h : Lp 𝕜 2 (μ.prod μ)}
    (hz : ∀ i j, inner 𝕜 h (prodMul (b₁ i) (b₂ j)) = 0) (F G : Lp 𝕜 2 μ) :
    inner 𝕜 h (prodMul F G) = 0 := by
  have step (i : ι) : (innerSL 𝕜 h).comp (prodMulL (b₁ i)) = 0 := by
    apply ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.2 b₂.dense_span)
    rintro _ ⟨j, rfl⟩
    simpa [prodMulL_apply, innerSL_apply_apply] using hz i j
  have hzero : (innerSL 𝕜 h).comp (prodMulL.flip G) = 0 := by
    apply ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.2 b₁.dense_span)
    rintro _ ⟨i, rfl⟩
    simpa [prodMulL_apply, innerSL_apply_apply] using DFunLike.congr_fun (step i) G
  simpa [prodMulL_apply, innerSL_apply_apply] using DFunLike.congr_fun hzero F

/-- Orthogonality to every elementary tensor kills integrals over finite-measure rectangles. -/
private theorem setIntegral_prod_eq_zero_of_forall_inner {h : Lp 𝕜 2 (μ.prod μ)}
    (hz : ∀ (F G : Lp 𝕜 2 μ), inner 𝕜 (prodMul F G) h = 0) {A : Set X} (hA : MeasurableSet A)
    (hμA : μ A ≠ ⊤) {B : Set X} (hB : MeasurableSet B) (hμB : μ B ≠ ⊤) :
    ∫ p in A ×ˢ B, h p ∂(μ.prod μ) = 0 := by
  set F : Lp 𝕜 2 μ := indicatorConstLp 2 hA hμA (1 : 𝕜)
  set G : Lp 𝕜 2 μ := indicatorConstLp 2 hB hμB (1 : 𝕜)
  have hFc : ⇑F =ᵐ[μ] A.indicator fun _ ↦ (1 : 𝕜) := indicatorConstLp_coeFn
  have hGc : ⇑G =ᵐ[μ] B.indicator fun _ ↦ (1 : 𝕜) := indicatorConstLp_coeFn
  calc
    ∫ p in A ×ˢ B, h p ∂(μ.prod μ)
        = ∫ p, (A ×ˢ B).indicator (fun q ↦ h q) p ∂(μ.prod μ) :=
          (integral_indicator (hA.prod hB)).symm
    _ = ∫ p, inner 𝕜 ((prodMul F G) p) (h p) ∂(μ.prod μ) := by
          refine integral_congr_ae ?_
          filter_upwards [coeFn_prodMul F G,
            TauCeti.ae_of_ae_fst (β := X) (ν := μ) hFc,
            TauCeti.ae_of_ae_snd (α := X) (μ := μ) hGc] with p hp hpF hpG
          rw [hp, hpF, hpG]
          by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ B <;>
            simp [Set.mem_prod, h1, h2]
    _ = inner 𝕜 (prodMul F G) h := (L2.inner_def _ _).symm
    _ = 0 := hz F G

/-- Orthogonality kills the part of a measurable set that lies in a finite-measure box. -/
private theorem setIntegral_inter_prod_eq_zero {h : Lp 𝕜 2 (μ.prod μ)}
    (hz : ∀ (F G : Lp 𝕜 2 μ), inner 𝕜 (prodMul F G) h = 0) {u : Set (X × X)}
    (hu : MeasurableSet u) {A : Set X} (hA : MeasurableSet A) (hμA : μ A ≠ ⊤) {B : Set X}
    (hB : MeasurableSet B) (hμB : μ B ≠ ⊤) :
    ∫ p in u ∩ (A ×ˢ B), h p ∂(μ.prod μ) = 0 := by
  have hboxfin : (μ.prod μ) (A ×ˢ B) ≠ ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hμA hμB
  have hrect : ∀ s, MeasurableSet s → ∀ t, MeasurableSet t →
      ∫ p in s ×ˢ t, h p ∂((μ.prod μ).restrict (A ×ˢ B)) = 0 := by
    intro s hs t ht
    rw [Measure.restrict_restrict (hs.prod ht), Set.prod_inter_prod]
    exact setIntegral_prod_eq_zero_of_forall_inner hz (hs.inter hA)
      (lt_of_le_of_lt (measure_mono Set.inter_subset_right) hμA.lt_top).ne (ht.inter hB)
      (lt_of_le_of_lt (measure_mono Set.inter_subset_right) hμB.lt_top).ne
  have hdyn := TauCeti.setIntegral_eq_zero_of_forall_prod
    (integrableOn_Lp_of_measure_ne_top h one_le_two hboxfin) hrect u hu
  rwa [Measure.restrict_restrict hu] at hdyn

/-- Orthogonality to every elementary tensor kills integrals over finite-measure sets. -/
private theorem setIntegral_eq_zero_of_forall_inner {h : Lp 𝕜 2 (μ.prod μ)}
    (hz : ∀ (F G : Lp 𝕜 2 μ), inner 𝕜 (prodMul F G) h = 0) (u : Set (X × X))
    (hu : MeasurableSet u) (hfin : (μ.prod μ) u < ⊤) : ∫ p in u, h p ∂(μ.prod μ) = 0 := by
  have hmono : Monotone fun n ↦ u ∩ (spanningSets μ n ×ˢ spanningSets μ n) := fun m n hmn ↦
    Set.inter_subset_inter_right _
      (Set.prod_mono (monotone_spanningSets μ hmn) (monotone_spanningSets μ hmn))
  have hcover : ⋃ n, u ∩ (spanningSets μ n ×ˢ spanningSets μ n) = u := by
    rw [← Set.inter_iUnion,
      Set.iUnion_prod_of_monotone (monotone_spanningSets μ) (monotone_spanningSets μ),
      iUnion_spanningSets, Set.univ_prod_univ, Set.inter_univ]
  have htend := tendsto_setIntegral_of_monotone
    (fun n ↦ hu.inter ((measurableSet_spanningSets μ n).prod (measurableSet_spanningSets μ n)))
    hmono (by rw [hcover]; exact integrableOn_Lp_of_measure_ne_top h one_le_two hfin.ne)
  rw [hcover] at htend
  simp only [fun n ↦ setIntegral_inter_prod_eq_zero hz hu (measurableSet_spanningSets μ n)
    (measure_spanningSets_lt_top μ n).ne (measurableSet_spanningSets μ n)
    (measure_spanningSets_lt_top μ n).ne] at htend
  exact tendsto_nhds_unique htend tendsto_const_nhds

/-- Basis tensors have trivial orthogonal complement in `L²(μ ⊗ μ)`. -/
private theorem orthogonal_span_range_prodMul_eq_bot {ι : Type*}
    (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 μ)) :
    (Submodule.span 𝕜 (Set.range fun ij : ι × ι ↦ prodMul (b ij.1) (star (b ij.2))))ᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun h hh ↦ ?_
  rw [Submodule.mem_orthogonal] at hh
  have hz : ∀ (F G : Lp 𝕜 2 μ), inner 𝕜 (prodMul F G) h = 0 := by
    intro F G
    rw [inner_eq_zero_symm]
    refine inner_prodMul_eq_zero_of_forall_basis b (hilbertBasis_star b) (fun i j ↦ ?_) F G
    rw [inner_eq_zero_symm, hilbertBasis_star_apply]
    exact hh _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have hae := Lp.ae_eq_zero_of_forall_setIntegral_eq_zero h (by norm_num) (by norm_num)
    (fun s _ hs' ↦ integrableOn_Lp_of_measure_ne_top h one_le_two hs'.ne)
    (fun s hs hs' ↦ setIntegral_eq_zero_of_forall_inner hz s hs hs')
  rw [Lp.ext_iff]
  exact hae.trans (Lp.coeFn_zero 𝕜 2 (μ.prod μ)).symm

/-- Pointwise products of a Hilbert basis with its starred copy are orthonormal. -/
private theorem orthonormal_tensor {ι : Type*} (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 μ)) :
    Orthonormal 𝕜 (fun ij : ι × ι ↦ prodMul (b ij.1) (star (b ij.2))) :=
  ⟨fun ij ↦ (norm_prodMul (b ij.1) (star (b ij.2))).trans <| by
      rw [norm_star_eq, b.orthonormal.norm_eq_one, b.orthonormal.norm_eq_one]
      ring,
    fun ij kl hij ↦ (inner_prodMul (b ij.1) (b kl.1) (star (b ij.2)) (star (b kl.2))).trans <| by
      rw [inner_star_star]
      by_cases h1 : ij.1 = kl.1
      · have h2 : kl.2 ≠ ij.2 := fun h ↦ hij (Prod.ext h1 h.symm)
        rw [b.orthonormal.inner_eq_zero h2, mul_zero]
      · rw [b.orthonormal.inner_eq_zero h1, zero_mul]⟩

/-- The product Hilbert basis of `L²(μ ⊗ μ)` indexed by pairs of the supplied basis. -/
private noncomputable def hilbertBasis_prod {ι : Type*} (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 μ)) :
    HilbertBasis (ι × ι) 𝕜 (Lp 𝕜 2 (μ.prod μ)) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_tensor b) (orthogonal_span_range_prodMul_eq_bot b)

/-- A product-basis vector is the tensor of the factor vector and the starred factor vector. -/
private theorem hilbertBasis_prod_apply {ι : Type*} (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 μ))
    (ij : ι × ι) : hilbertBasis_prod b ij = prodMul (b ij.1) (star (b ij.2)) := by
  rw [hilbertBasis_prod, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- Sections of an `L²` product function are square-integrable for almost every first coordinate. -/
private theorem ae_memLp_section {k : X × X → 𝕜} (hk : MemLp k 2 (μ.prod μ)) :
    ∀ᵐ x ∂μ, MemLp (fun y ↦ k (x, y)) 2 μ := by
  have hmeas : AEMeasurable (fun p : X × X ↦ ‖k p‖ₑ ^ 2) (μ.prod μ) :=
    hk.aestronglyMeasurable.enorm.pow_const 2
  have hsq : (eLpNorm k 2 (μ.prod μ)) ^ 2 = ∫⁻ p, ‖k p‖ₑ ^ 2 ∂(μ.prod μ) := by
    have hpow := eLpNorm_nnreal_pow_eq_lintegral (μ := μ.prod μ) (f := k) (p := 2) (by norm_num)
      hk.aestronglyMeasurable
    simp only [NNReal.coe_ofNat, ENNReal.rpow_two] at hpow
    exact hpow
  have hlt : ∫⁻ x, ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂μ ∂μ < ∞ := by
    rw [← lintegral_prod _ hmeas, ← hsq, lt_top_iff_ne_top]
    simp [ENNReal.pow_eq_top_iff, hk.ne]
  have hint : ∀ᵐ x ∂μ, ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂μ < ∞ :=
    ae_lt_top' hmeas.lintegral_prod_right' hlt.ne
  filter_upwards [hk.aestronglyMeasurable.prodMk_left, hint] with x hx hfin
  rw [MemLp, lt_top_iff_ne_top]
  intro htop
  have hpow : eLpNorm (fun y ↦ k (x, y)) 2 μ ^ 2 = ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂μ := by
    have hreal := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := fun y ↦ k (x, y)) (p := 2)
      (by norm_num) hx
    simp only [NNReal.coe_ofNat, ENNReal.rpow_two] at hreal
    exact hreal
  exact hfin.ne <| hpow.symm.trans <| by
    rw [htop, ENNReal.top_pow (by decide)]

/-- For almost every `x`, the slice `y ↦ k(x, y) f(y)` is integrable. -/
private theorem ae_integrable_kernel_section {k : X × X → 𝕜} (hk : MemLp k 2 (μ.prod μ))
    (f : Lp 𝕜 2 μ) : ∀ᵐ x ∂μ, Integrable (fun y ↦ k (x, y) * f y) μ := by
  filter_upwards [ae_memLp_section hk] with x hx
  exact (memLp_one_iff_integrable).1 (hx.mul (Lp.memLp f))

/-- The integral formula is almost-everywhere strongly measurable. -/
private theorem integralKernel_aestronglyMeasurable {k : X × X → 𝕜} (hk : MemLp k 2 (μ.prod μ))
    (f : Lp 𝕜 2 μ) :
    AEStronglyMeasurable (fun x ↦ ∫ y, k (x, y) * f y ∂μ) μ := by
  have hmul : AEStronglyMeasurable (fun p : X × X ↦ k p * f p.2) (μ.prod μ) :=
    hk.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd)
  simpa using hmul.integral_prod_right'

/-- Squared `L²` norm of the integral formula, bounded by the product of the squared norms. -/
private theorem eLpNorm_integralKernel_sq_le {k : X × X → 𝕜} (hk : MemLp k 2 (μ.prod μ))
    (f : Lp 𝕜 2 μ) :
    eLpNorm (fun x ↦ ∫ y, k (x, y) * f y ∂μ) 2 μ ^ 2 ≤
      (eLpNorm k 2 (μ.prod μ)) ^ 2 * ‖f‖ₑ ^ 2 := by
  set F : X → 𝕜 := fun x ↦ ∫ y, k (x, y) * f y ∂μ
  have hFasm : AEStronglyMeasurable F μ := integralKernel_aestronglyMeasurable hk f
  have hpoint (x : X) : ‖F x‖ₑ ≤ eLpNorm (fun y ↦ k (x, y)) 2 μ * ‖f‖ₑ := by
    have hsmul : (fun y ↦ k (x, y)) • (f : X → 𝕜) = fun y ↦ k (x, y) * f y := by
      ext y
      simp [smul_eq_mul]
    have hholder := eLpNorm_smul_le_mul_eLpNorm_of_pos (μ := μ) (φ := fun y ↦ k (x, y))
      (f := (f : X → 𝕜)) (p := (2 : ℝ≥0∞)) (q := 2) (r := 1) zero_lt_one
    rw [hsmul] at hholder
    calc
      ‖F x‖ₑ ≤ ∫⁻ y, ‖k (x, y) * f y‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ ≤ eLpNorm (fun y ↦ k (x, y) * f y) 1 μ := lintegral_enorm_le_eLpNorm_one
      _ ≤ eLpNorm (fun y ↦ k (x, y)) 2 μ * eLpNorm (⇑f) 2 μ := hholder
      _ = eLpNorm (fun y ↦ k (x, y)) 2 μ * ‖f‖ₑ := by rw [← Lp.enorm_def]
  have hsec : ∀ᵐ x ∂μ, eLpNorm (fun y ↦ k (x, y)) 2 μ ^ 2 = ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂μ := by
    filter_upwards [ae_memLp_section hk] with x hx
    have hreal := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := fun y ↦ k (x, y)) (p := 2)
      (by norm_num) hx.aestronglyMeasurable
    simp only [NNReal.coe_ofNat, ENNReal.rpow_two] at hreal
    exact hreal
  have hineq : ∀ᵐ x ∂μ, ‖F x‖ₑ ^ 2 ≤ (∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂μ) * ‖f‖ₑ ^ 2 := by
    filter_upwards [hsec] with x hx
    calc
      ‖F x‖ₑ ^ 2 ≤ (eLpNorm (fun y ↦ k (x, y)) 2 μ * ‖f‖ₑ) ^ 2 :=
        ENNReal.pow_le_pow_left (hpoint x)
      _ = eLpNorm (fun y ↦ k (x, y)) 2 μ ^ 2 * ‖f‖ₑ ^ 2 := by rw [mul_pow]
      _ = (∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂μ) * ‖f‖ₑ ^ 2 := by rw [hx]
  have hmeas : AEMeasurable (fun p : X × X ↦ ‖k p‖ₑ ^ 2) (μ.prod μ) :=
    hk.aestronglyMeasurable.enorm.pow_const 2
  have hkpow : (eLpNorm k 2 (μ.prod μ)) ^ 2 = ∫⁻ p, ‖k p‖ₑ ^ 2 ∂(μ.prod μ) := by
    have hreal := eLpNorm_nnreal_pow_eq_lintegral (μ := μ.prod μ) (f := k) (p := 2) (by norm_num)
      hk.aestronglyMeasurable
    simp only [NNReal.coe_ofNat, ENNReal.rpow_two] at hreal
    exact hreal
  have hr : ‖f‖ₑ ^ 2 ≠ ∞ := by simp [ENNReal.pow_eq_top_iff]
  calc
    eLpNorm F 2 μ ^ 2 = ∫⁻ x, ‖F x‖ₑ ^ 2 ∂μ := by
      have hreal := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := F) (p := 2) (by norm_num) hFasm
      simp only [NNReal.coe_ofNat, ENNReal.rpow_two] at hreal
      exact hreal
    _ ≤ ∫⁻ x, (∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂μ) * ‖f‖ₑ ^ 2 ∂μ := lintegral_mono_ae hineq
    _ = (∫⁻ x, ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂μ ∂μ) * ‖f‖ₑ ^ 2 := lintegral_mul_const' _ _ hr
    _ = (eLpNorm k 2 (μ.prod μ)) ^ 2 * ‖f‖ₑ ^ 2 := by
      rw [← lintegral_prod _ hmeas, hkpow]

/-- The integral formula defines an `L²` class. -/
private theorem memLp_integralKernel {k : X × X → 𝕜} (hk : MemLp k 2 (μ.prod μ))
    (f : Lp 𝕜 2 μ) : MemLp (fun x ↦ ∫ y, k (x, y) * f y ∂μ) 2 μ := by
  rw [MemLp, lt_top_iff_ne_top]
  intro htop
  have hsq := eLpNorm_integralKernel_sq_le hk f
  have hkfin : (eLpNorm k 2 (μ.prod μ)) ^ 2 < ∞ := by
    simp [ENNReal.pow_eq_top_iff, hk.ne, lt_top_iff_ne_top]
  have hffin : ‖f‖ₑ ^ 2 < ∞ := by simp [ENNReal.pow_eq_top_iff, lt_top_iff_ne_top]
  have hlt := hsq.trans_lt (ENNReal.mul_lt_top hkfin hffin)
  rw [htop, ENNReal.top_pow (by decide)] at hlt
  exact lt_irrefl _ hlt

/-- Operator norm bound for the integral class of an `L²` kernel. -/
private theorem norm_toLp_integralKernel_le {k : X × X → 𝕜} (hk : MemLp k 2 (μ.prod μ))
    (f : Lp 𝕜 2 μ) :
    ‖(memLp_integralKernel hk f).toLp (fun x ↦ ∫ y, k (x, y) * f y ∂μ)‖ ≤
      (eLpNorm k 2 (μ.prod μ)).toReal * ‖f‖ := by
  rw [Lp.norm_toLp]
  have hle : eLpNorm (fun x ↦ ∫ y, k (x, y) * f y ∂μ) 2 μ ≤
      eLpNorm k 2 (μ.prod μ) * ‖f‖ₑ := by
    rw [← ENNReal.pow_le_pow_left_iff (by decide : 2 ≠ 0)]
    simpa [mul_pow] using eLpNorm_integralKernel_sq_le hk f
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top hk.ne (by simp)) hle).trans ?_
  rw [ENNReal.toReal_mul, Lp.enorm_def, Lp.norm_def]

/-- The bounded integral operator on `L²` induced by an `L²` kernel. -/
private noncomputable def integralKernelCLM {k : X × X → 𝕜} (hk : MemLp k 2 (μ.prod μ)) :
    Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ :=
  LinearMap.mkContinuous
    ({ toFun := fun f ↦ (memLp_integralKernel hk f).toLp fun x ↦ ∫ y, k (x, y) * f y ∂μ
       map_add' := fun f g ↦ by
         refine (MemLp.toLp_congr (memLp_integralKernel hk (f + g))
           ((memLp_integralKernel hk f).add (memLp_integralKernel hk g)) ?_).trans
           (MemLp.toLp_add _ _)
         filter_upwards [Measure.ae_ae_of_ae_prod ((Measure.quasiMeasurePreserving_snd (μ := μ)
             (ν := μ)).ae (Lp.coeFn_add f g)),
           ae_integrable_kernel_section hk f, ae_integrable_kernel_section hk g]
           with x hx hf hg
         have hint : (fun y ↦ k (x, y) * (f + g) y) =ᵐ[μ]
             fun y ↦ k (x, y) * f y + k (x, y) * g y := by
           filter_upwards [hx] with y hy
           rw [hy, Pi.add_apply, mul_add]
         rw [Pi.add_apply, integral_congr_ae hint, integral_add hf hg]
       map_smul' := fun c f ↦ by
         refine (MemLp.toLp_congr (memLp_integralKernel hk (c • f))
             ((memLp_integralKernel hk f).const_smul c) ?_).trans
           (MemLp.toLp_const_smul c _)
         filter_upwards [Measure.ae_ae_of_ae_prod ((Measure.quasiMeasurePreserving_snd (μ := μ)
             (ν := μ)).ae (Lp.coeFn_smul c f))] with x hx
         have hint : (fun y ↦ k (x, y) * (c • f) y) =ᵐ[μ]
             fun y ↦ c * (k (x, y) * f y) := by
           filter_upwards [hx] with y hy
           rw [hy, Pi.smul_apply, smul_eq_mul]
           ring
         rw [Pi.smul_apply, smul_eq_mul, integral_congr_ae hint, integral_const_mul] }
      : Lp 𝕜 2 μ →ₗ[𝕜] Lp 𝕜 2 μ)
    (eLpNorm k 2 (μ.prod μ)).toReal (norm_toLp_integralKernel_le hk)

/-- The integral operator acts by the kernel formula almost everywhere. -/
private theorem hasIntegralKernel_integralKernelCLM {k : X × X → 𝕜} (hk : MemLp k 2 (μ.prod μ)) :
    HasIntegralKernel μ (integralKernelCLM hk) k := by
  intro f
  simpa [integralKernelCLM] using MemLp.coeFn_toLp (memLp_integralKernel hk f)

/-- The integrand of an `L²` matrix coefficient against the kernel is integrable on the product. -/
private theorem integrable_conj_kernel {k : X × X → 𝕜} (hk : MemLp k 2 (μ.prod μ))
    (f g : Lp 𝕜 2 μ) :
    Integrable (fun p : X × X ↦ star (g p.1) * k p * f p.2) (μ.prod μ) := by
  have hprod : MemLp (fun p : X × X ↦ (star g) p.1 * f p.2) 2 (μ.prod μ) :=
    memLp_mul_prod (Lp.memLp (star g)) (Lp.memLp f)
  have hstar : MemLp (fun p : X × X ↦ star (g p.1) * f p.2) 2 (μ.prod μ) := by
    refine (memLp_congr_ae ?_).1 hprod
    filter_upwards [TauCeti.ae_of_ae_fst (β := X) (ν := μ) (Lp.coeFn_star g)] with p hp
    simp [hp, Pi.star_apply]
  have hmul : MemLp ((fun p : X × X ↦ star (g p.1) * f p.2) * k) 1 (μ.prod μ) := hstar.mul hk
  refine (memLp_one_iff_integrable).1 ((memLp_congr_ae ?_).2 hmul)
  filter_upwards with p
  rw [Pi.mul_apply]
  ring

/-- The `L²` inner product against the integral operator is the absolutely convergent double
integral of the kernel. -/
private theorem inner_integralKernel_eq {k : X × X → 𝕜} (hk : MemLp k 2 (μ.prod μ))
    (f g : Lp 𝕜 2 μ) :
    inner 𝕜 g (integralKernelCLM hk f) =
      ∫ p : X × X, star (g p.1) * k p * f p.2 ∂(μ.prod μ) := by
  rw [L2.inner_def]
  calc
    ∫ x, inner 𝕜 (g x) (integralKernelCLM hk f x) ∂μ
        = ∫ x, star (g x) * integralKernelCLM hk f x ∂μ := by
          refine integral_congr_ae (.of_forall fun _ ↦ mul_comm _ _)
    _ = ∫ x, star (g x) * ∫ y, k (x, y) * f y ∂μ ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hasIntegralKernel_integralKernelCLM hk f] with x hx
          rw [hx]
    _ = ∫ x, ∫ y, star (g x) * k (x, y) * f y ∂μ ∂μ := by
          refine integral_congr_ae (.of_forall fun x ↦ ?_)
          simp_rw [← integral_const_mul, mul_assoc]
    _ = ∫ p, star (g p.1) * k p * f p.2 ∂(μ.prod μ) :=
          (integral_prod _ (integrable_conj_kernel hk f g)).symm

/-- The inner product of a tensor `F ⊗ star G` against the kernel is the same double integral. -/
private theorem inner_prodMul_star_toLp {k : X × X → 𝕜} (hk : MemLp k 2 (μ.prod μ))
    (F G : Lp 𝕜 2 μ) :
    inner 𝕜 (prodMul F (star G)) (hk.toLp k) =
      ∫ p : X × X, star (F p.1) * k p * G p.2 ∂(μ.prod μ) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_prodMul F (star G), MemLp.coeFn_toLp hk,
    TauCeti.ae_of_ae_snd (α := X) (μ := μ) (Lp.coeFn_star G)] with p hFG hk' hG
  rw [hFG, hk', hG, Pi.star_apply, RCLike.inner_apply', ← RCLike.star_def, star_mul,
    star_star]
  ring

/-- A matrix coefficient of the integral operator is the coefficient of the kernel in the product
basis. -/
private theorem inner_basis_apply_eq {k : X × X → 𝕜} (hk : MemLp k 2 (μ.prod μ)) {ι : Type*}
    (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 μ)) (i j : ι) :
    inner 𝕜 (b j) (integralKernelCLM hk (b i)) =
      inner 𝕜 (prodMul (b j) (star (b i))) (hk.toLp k) := by
  rw [inner_integralKernel_eq, inner_prodMul_star_toLp]

/-- The integral operator has Hilbert–Schmidt energy equal to the squared `L²` norm of the kernel.
-/
private theorem hilbertSchmidtEnergy_integralKernel {k : X × X → 𝕜} (hk : MemLp k 2 (μ.prod μ))
    {ι : Type*} (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 μ)) :
    (integralKernelCLM hk).hilbertSchmidtEnergy b = (eLpNorm k 2 (μ.prod μ)) ^ 2 := by
  rw [hilbertSchmidtEnergy_eq_tsum_tsum (integralKernelCLM hk) b b, ENNReal.tsum_comm]
  simp_rw [inner_basis_apply_eq hk b]
  have hP := (hilbertBasis_prod b).tsum_enorm_sq_inner (hk.toLp k)
  simp_rw [hilbertBasis_prod_apply] at hP
  have hsum := (ENNReal.tsum_prod' (f := fun ij : ι × ι ↦
    ‖inner 𝕜 (prodMul (b ij.1) (star (b ij.2))) (hk.toLp k)‖ₑ ^ 2)).symm
  rw [hsum]
  exact hP.trans (congrArg (· ^ 2) (Lp.enorm_toLp hk))

/-- The starred transpose of an `L²` kernel remains `L²` for the product measure. -/
private theorem memLp_adjointKernel {k : X × X → 𝕜} (hk : MemLp k 2 (μ.prod μ)) :
    MemLp (fun p : X × X ↦ star (k (p.2, p.1))) 2 (μ.prod μ) := by
  simpa [Pi.star_def, Function.comp_def, Prod.swap] using
    (hk.comp_measurePreserving Measure.measurePreserving_swap).star

/-- The inner product against the integral operator of the starred transpose equals the same double
integral, with the variables in the opposite order. -/
private theorem inner_adjointKernel_eq {k : X × X → 𝕜} (hk : MemLp k 2 (μ.prod μ))
    (f g : Lp 𝕜 2 μ) :
    inner 𝕜 (integralKernelCLM (memLp_adjointKernel hk) g) f =
      ∫ p : X × X, star (g p.1) * k p * f p.2 ∂(μ.prod μ) := by
  rw [L2.inner_def]
  calc
    ∫ y, inner 𝕜 (integralKernelCLM (memLp_adjointKernel hk) g y) (f y) ∂μ
        = ∫ y, star (integralKernelCLM (memLp_adjointKernel hk) g y) * f y ∂μ := by
          refine integral_congr_ae (.of_forall fun _ ↦ mul_comm _ _)
    _ = ∫ y, (∫ x, star (g x) * k (x, y) ∂μ) * f y ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hasIntegralKernel_integralKernelCLM (memLp_adjointKernel hk) g]
            with y hy
          rw [hy, RCLike.star_def, ← integral_conj]
          refine congrArg (fun z : 𝕜 ↦ z * f y) ?_
          refine integral_congr_ae (.of_forall fun x ↦ ?_)
          change star (star (k (x, y)) * g x) = star (g x) * k (x, y)
          rw [star_mul, star_star]
    _ = ∫ y, ∫ x, star (g x) * k (x, y) * f y ∂μ ∂μ := by
          refine integral_congr_ae (.of_forall fun y ↦ ?_)
          beta_reduce
          rw [← integral_mul_const]
    _ = ∫ p, star (g p.1) * k p * f p.2 ∂(μ.prod μ) :=
          (integral_prod_symm _ (integrable_conj_kernel hk f g)).symm

/-- The adjoint of the integral operator is the integral operator of the starred transpose. -/
private theorem hasIntegralKernel_adjoint {k : X × X → 𝕜} (hk : MemLp k 2 (μ.prod μ)) :
    HasIntegralKernel μ (integralKernelCLM hk).adjoint (fun p ↦ star (k (p.2, p.1))) := by
  have hEq : integralKernelCLM (memLp_adjointKernel hk) = (integralKernelCLM hk).adjoint := by
    refine ContinuousLinearMap.ext fun g ↦ ?_
    refine ext_inner_right 𝕜 fun f ↦ ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact (inner_adjointKernel_eq hk f g).trans (inner_integralKernel_eq hk f g).symm
  rw [← hEq]
  exact hasIntegralKernel_integralKernelCLM (memLp_adjointKernel hk)

end

/-- **25.3**: an `L²` kernel defines a unique bounded integral operator with its exact
Hilbert–Schmidt energy and transposed star adjoint kernel. -/
theorem existsUnique_integralOperator {k : X × X → 𝕜} (hk : MemLp k 2 (μ.prod μ))
    {ι : Type*} (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 μ)) :
    ∃! T : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ,
      HasIntegralKernel μ T k ∧
      T.hilbertSchmidtEnergy b = (eLpNorm k 2 (μ.prod μ)) ^ 2 ∧
      HasIntegralKernel μ T.adjoint (fun p ↦ star (k (p.2, p.1))) := by
  refine existsUnique_of_exists_of_unique ?_ ?_
  · exact ⟨integralKernelCLM hk, hasIntegralKernel_integralKernelCLM hk,
      hilbertSchmidtEnergy_integralKernel hk b, hasIntegralKernel_adjoint hk⟩
  · rintro T₁ T₂ ⟨hT₁, -, -⟩ ⟨hT₂, -, -⟩
    refine ContinuousLinearMap.ext fun f ↦ ?_
    exact Lp.ext ((hT₁ f).trans (hT₂ f).symm)

end CKMA
