/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.HansonWright.Estimates

public import CKMA.Probability.Concentration
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
/-!
# Hanson–Wright off-diagonal comparison

A Bernoulli average separates the off-diagonal quadratic form. Gaussian integrals
bound the resulting moment generating function.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal RealInnerProductSpace Matrix Matrix.Norms.L2Operator

universe u

variable {n : ℕ}

/-- `(1 - z) ^ (-1 / 2) ≤ exp z` on the interval `0 ≤ z ≤ 1 / 2`. -/
lemma one_sub_rpow_le_exp {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 1 / 2) :
    (1 - z) ^ (-1 / 2 : ℝ) ≤ Real.exp z := by
  have h1z : 0 < 1 - z := by linarith
  have hzabs : |z| < 1 := by rw [abs_of_nonneg hz0]; linarith
  have hle : ∀ n : ℕ, z ^ (n + 1) / (n + 1) ≤ z ^ (n + 1) := by
    intro n
    exact div_le_self (pow_nonneg hz0 _) (by exact_mod_cast Nat.succ_pos n : (1 : ℝ) ≤ n + 1)
  have hg : HasSum (fun n : ℕ ↦ z ^ (n + 1)) (z / (1 - z)) := by
    have hmul := (hasSum_geometric_of_lt_one hz0 (by linarith : z < 1)).mul_right z
    have hfun : (fun n : ℕ ↦ z ^ (n + 1)) = fun n ↦ z ^ n * z := by
      ext n
      rw [pow_succ]
    rw [hfun, show z / (1 - z) = (1 - z)⁻¹ * z by rw [div_eq_mul_inv, mul_comm]]
    exact hmul
  have hlog : -Real.log (1 - z) ≤ z / (1 - z) :=
    hasSum_le hle (Real.hasSum_pow_div_log_of_abs_lt_one hzabs) hg
  have htwice : z / (1 - z) ≤ 2 * z := by
    rw [div_le_iff₀ h1z]
    nlinarith
  rw [Real.rpow_def_of_pos h1z]
  exact Real.exp_le_exp.mpr (by linarith [hlog.trans htwice])

/-- Exponential second moment of a standard real Gaussian, for `β < 1 / 2`. -/
lemma integral_exp_mul_sq_gaussianReal {β : ℝ} (hβ : β < 1 / 2) :
    Integrable (fun x : ℝ ↦ Real.exp (β * x ^ 2)) (gaussianReal 0 1) ∧
      ∫ x, Real.exp (β * x ^ 2) ∂(gaussianReal 0 1) =
        (1 - 2 * β) ^ (-1 / 2 : ℝ) := by
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  have hb : 0 < 1 / 2 - β := by linarith
  set b : ℝ := 1 / 2 - β
  have hpdfMeas : Measurable (gaussianPDF (0 : ℝ) (1 : NNReal)) :=
    (measurable_gaussianPDFReal 0 (1 : NNReal)).ennreal_ofReal
  have hlt : ∀ᵐ x ∂(volume : Measure ℝ), gaussianPDF 0 (1 : NNReal) x < ⊤ :=
    ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hrewrite : (fun x : ℝ ↦ gaussianPDFReal 0 (1 : NNReal) x * Real.exp (β * x ^ 2)) =
      fun x ↦ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-b * x ^ 2) := by
    ext x
    rw [gaussianPDFReal]
    simp only [NNReal.coe_one, sub_zero, mul_one]
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    unfold b
    ring
  have hintVol : Integrable (fun x : ℝ ↦ gaussianPDFReal 0 1 x * Real.exp (β * x ^ 2)) := by
    rw [hrewrite]
    exact (integrable_exp_neg_mul_sq hb).const_mul _
  have hintG : Integrable (fun x : ℝ ↦ Real.exp (β * x ^ 2)) (gaussianReal 0 1) := by
    rw [gaussianReal_of_var_ne_zero 0 hv]
    exact (integrable_withDensity_iff hpdfMeas hlt).2 (by simpa [mul_comm] using hintVol)
  refine ⟨hintG, ?_⟩
  rw [gaussianReal_of_var_ne_zero 0 hv,
    integral_withDensity_eq_integral_toReal_smul hpdfMeas hlt]
  simp_rw [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), smul_eq_mul]
  rw [hrewrite, integral_const_mul, integral_gaussian b]
  have hsqrt : (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / b) =
      (1 - 2 * β) ^ (-1 / 2 : ℝ) := by
    have h2b : 2 * b = 1 - 2 * β := by unfold b; ring
    have hbpos : 0 < b := by unfold b; linarith
    have harg : (Real.pi / b) / (2 * Real.pi) = 1 / (2 * b) := by field_simp
    calc
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / b) =
          Real.sqrt (Real.pi / b) / Real.sqrt (2 * Real.pi) := by ring
      _ = Real.sqrt ((Real.pi / b) / (2 * Real.pi)) := by
          rw [← Real.sqrt_div (div_nonneg Real.pi_nonneg hbpos.le)]
      _ = Real.sqrt (1 / (2 * b)) := by rw [harg]
      _ = Real.sqrt ((2 * b)⁻¹) := by congr 1; ring
      _ = ((2 * b)⁻¹) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
      _ = (2 * b) ^ (-1 / 2 : ℝ) := by
          rw [← Real.rpow_neg_eq_inv_rpow, neg_div]
      _ = (1 - 2 * β) ^ (-1 / 2 : ℝ) := by rw [h2b]
  exact hsqrt

/-- Product Gaussian integral of a diagonal quadratic exponential. -/
lemma integral_exp_weighted_sq_gaussian {μ : Fin n → ℝ} {β : ℝ}
    (hβ : ∀ i, β * μ i < 1 / 2) :
    Integrable (fun x : Fin n → ℝ ↦ Real.exp (β * ∑ i, μ i * x i ^ 2))
        (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) ∧
      ∫ x, Real.exp (β * ∑ i, μ i * x i ^ 2)
          ∂(Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) =
        ∏ i, (1 - 2 * β * μ i) ^ (-1 / 2 : ℝ) := by
  have hfun : (fun x : Fin n → ℝ ↦ Real.exp (β * ∑ i, μ i * x i ^ 2)) =
      fun x ↦ ∏ i, Real.exp (β * μ i * x i ^ 2) := by
    ext x
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  have hone : ∀ i, Integrable (fun t : ℝ ↦ Real.exp (β * μ i * t ^ 2)) (gaussianReal 0 1) :=
    fun i ↦ (integral_exp_mul_sq_gaussianReal (by simpa [mul_assoc] using hβ i)).1
  have hint : Integrable (fun x : Fin n → ℝ ↦ ∏ i, Real.exp (β * μ i * x i ^ 2))
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) :=
    Integrable.fintype_prod hone
  refine ⟨?_, ?_⟩
  · simpa [hfun] using hint
  · rw [hfun]
    rw [integral_fintype_prod_eq_prod (fun i (t : ℝ) ↦ Real.exp (β * μ i * t ^ 2))
      (μ := fun _ : Fin n ↦ gaussianReal 0 1)]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    have hI := (integral_exp_mul_sq_gaussianReal (β := β * μ i) (by simpa using hβ i)).2
    rw [hI]
    congr 1
    ring

/-- A squared matrix-vector image is the quadratic form of `Mᵀ M`. -/
lemma dot_mulVec_sq (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    (M *ᵥ x) ⬝ᵥ (M *ᵥ x) = x ⬝ᵥ (M.transpose * M) *ᵥ x := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.dotProduct_mulVec]

/-- Gaussian tails of `‖M x‖²` are controlled by the Frobenius and operator norms. -/
lemma integral_exp_mulVec_sq_gaussian (M : Matrix (Fin n) (Fin n) ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (hβop : β * realMatrixOperatorNorm M ^ 2 ≤ 1 / 4) :
    Integrable (fun x : Fin n → ℝ ↦ Real.exp (β * ((M *ᵥ x) ⬝ᵥ (M *ᵥ x))))
        (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) ∧
      ∫ x, Real.exp (β * ((M *ᵥ x) ⬝ᵥ (M *ᵥ x)))
          ∂(Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) ≤
        Real.exp (2 * β * realMatrixFrobeniusSq M) := by
  rw [realMatrixOperatorNorm_eq] at hβop
  let γ : Measure (Fin n → ℝ) := Measure.pi fun _ ↦ gaussianReal 0 1
  let H : Matrix (Fin n) (Fin n) ℝ := M.transpose * M
  have hPSD : H.PosSemidef := by
    simpa [H, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self M
  let hH : H.IsHermitian := hPSD.isHermitian
  let b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := hH.eigenvectorBasis
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) H
  let φ : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n) := fun x ↦ ∑ i, x i • b i
  have hTb : ∀ i, T (b i) = hH.eigenvalues i • b i := by
    intro i
    apply (WithLp.ofLp_injective (p := (2 : ℝ≥0∞))).eq_iff.mp
    rw [WithLp.ofLp_smul, Matrix.ofLp_toEuclideanCLM]
    simpa [b] using hH.mulVec_eigenvectorBasis i
  have hopH : ‖H‖ = ‖M‖ ^ 2 := by
    have hstar : H = Matrix.conjTranspose M * M := by
      simp [H, Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [hstar, Matrix.l2_opNorm_conjTranspose_mul_self, pow_two]
  have hμle : ∀ i, hH.eigenvalues i ≤ ‖H‖ := by
    intro i
    have hμ0 : 0 ≤ hH.eigenvalues i := hPSD.eigenvalues_nonneg i
    have hnorm : ‖T (b i)‖ = hH.eigenvalues i := by
      rw [hTb i, norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ0, b.orthonormal.norm_eq_one i,
        mul_one]
    calc
      hH.eigenvalues i = ‖T (b i)‖ := hnorm.symm
      _ ≤ ‖T‖ * ‖b i‖ := T.le_opNorm _
      _ = ‖H‖ := by
        rw [b.orthonormal.norm_eq_one i, mul_one]
        simp [T, Matrix.l2_opNorm_toEuclideanCLM]
  have hβμ : ∀ i, β * hH.eigenvalues i ≤ 1 / 4 := by
    intro i
    calc
      β * hH.eigenvalues i ≤ β * ‖H‖ := mul_le_mul_of_nonneg_left (hμle i) hβ
      _ = β * ‖M‖ ^ 2 := by rw [hopH]
      _ ≤ 1 / 4 := hβop
  have hβstrict : ∀ i, β * hH.eigenvalues i < 1 / 2 :=
    fun i ↦ lt_of_le_of_lt (hβμ i) (by norm_num)
  have hdiag := integral_exp_weighted_sq_gaussian (μ := hH.eigenvalues) (β := β) hβstrict
  have hcoord : ∀ x i, ⟪b i, φ x⟫ = x i := by
    intro x i
    simp only [φ, inner_sum]
    rw [Finset.sum_eq_single i]
    · rw [inner_smul_right, real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one i]
      ring
    · intro j _ hji
      rw [inner_smul_right, b.orthonormal.inner_eq_zero hji.symm, mul_zero]
    · simp
  have hTφ : ∀ x, T (φ x) = ∑ i, (hH.eigenvalues i * x i) • b i := by
    intro x
    simp only [φ, map_sum, map_smul, hTb, smul_smul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_comm]
  have hquadForm : ∀ x, ⟪φ x, T (φ x)⟫ = ∑ i, hH.eigenvalues i * x i ^ 2 := by
    intro x
    rw [hTφ x, ← OrthonormalBasis.sum_inner_mul_inner b (φ x)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_comm, hcoord x i]
    have h2 : ⟪b i, ∑ j, (hH.eigenvalues j * x j) • b j⟫ = hH.eigenvalues i * x i := by
      rw [inner_sum, Finset.sum_eq_single i]
      · rw [inner_smul_right, real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one i]
        ring
      · intro j _ hji
        rw [inner_smul_right, b.orthonormal.inner_eq_zero hji.symm, mul_zero]
      · simp
    rw [h2]
    ring
  have hφmeas : AEMeasurable φ γ := by
    let L : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
      { toFun := fun x ↦ ∑ i, x i • b i
        map_add' := fun x y ↦ by simp [Finset.sum_add_distrib, add_smul]
        map_smul' := fun c x ↦ by simp [Finset.smul_sum, smul_smul] }
    have hcont : Continuous φ := by
      change Continuous L
      exact L.continuous_of_finiteDimensional
    exact hcont.aemeasurable
  let quad : EuclideanSpace ℝ (Fin n) → ℝ := fun v ↦ Real.exp (β * ⟪v, T v⟫)
  have hquadCont : Continuous quad := by
    fun_prop
  have hφeq : ∀ x, quad (φ x) =
      Real.exp (β * ∑ i, hH.eigenvalues i * x i ^ 2) := by
    intro x
    simp [quad, hquadForm x]
  have hdiagFun : (fun x ↦ quad (φ x)) =
      fun x ↦ Real.exp (β * ∑ i, hH.eigenvalues i * x i ^ 2) := by
    ext x
    exact hφeq x
  have hmapφ : γ.map φ = stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    simpa [γ, φ] using (stdGaussian_eq_map_pi_orthonormalBasis b).symm
  have hintQuad : Integrable quad (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    rw [← hmapφ]
    apply (integrable_map_measure hquadCont.aestronglyMeasurable hφmeas).2
    have hcompφ : quad ∘ φ =
        fun x ↦ Real.exp (β * ∑ i, hH.eigenvalues i * x i ^ 2) := by
      ext x
      simp [Function.comp, quad, hquadForm]
    rw [hcompφ]
    simpa [γ] using hdiag.1
  have hintDiag : ∫ v, quad v ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ∫ x, Real.exp (β * ∑ i, hH.eigenvalues i * x i ^ 2) ∂γ := by
    rw [← hmapφ, integral_map hφmeas hquadCont.aestronglyMeasurable, hdiagFun]
  have hLp : γ.map (WithLp.toLp (2 : ℝ≥0∞)) =
      stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    simpa [γ] using map_pi_eq_stdGaussian (ι := Fin n)
  have hinner (x : Fin n → ℝ) : (M *ᵥ x) ⬝ᵥ (M *ᵥ x) =
      ⟪WithLp.toLp (2 : ℝ≥0∞) x, T (WithLp.toLp (2 : ℝ≥0∞) x)⟫ := by
    rw [dot_mulVec_sq]
    simpa [H, T, PiLp.toLp_apply] using
      (Matrix.inner_toEuclideanCLM H (WithLp.toLp (2 : ℝ≥0∞) x)
        (WithLp.toLp (2 : ℝ≥0∞) x)).symm
  have htoMeas : AEMeasurable
      (WithLp.toLp (2 : ℝ≥0∞) : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) γ :=
    (PiLp.continuous_toLp (p := (2 : ℝ≥0∞)) (β := fun _ : Fin n ↦ ℝ)).aemeasurable
  have hcomp : (fun x ↦ quad (WithLp.toLp (2 : ℝ≥0∞) x)) =
      fun x ↦ Real.exp (β * ((M *ᵥ x) ⬝ᵥ (M *ᵥ x))) := by
    ext x
    simp [quad, hinner]
  have hintF : Integrable (fun x ↦ Real.exp (β * ((M *ᵥ x) ⬝ᵥ (M *ᵥ x)))) γ := by
    rw [← hLp] at hintQuad
    exact hcomp ▸ (integrable_map_measure hquadCont.aestronglyMeasurable htoMeas).1 hintQuad
  refine ⟨by simpa [γ] using hintF, ?_⟩
  have hintEq : ∫ x, Real.exp (β * ((M *ᵥ x) ⬝ᵥ (M *ᵥ x))) ∂γ =
      ∫ v, quad v ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    rw [← hLp, integral_map htoMeas hquadCont.aestronglyMeasurable]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by simp [quad, hinner])
  have hprodle : ∏ i, (1 - 2 * β * hH.eigenvalues i) ^ (-1 / 2 : ℝ) ≤
      ∏ i, Real.exp (2 * β * hH.eigenvalues i) := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact Real.rpow_nonneg (by linarith [hβstrict i]) _
    · intro i _
      have hz0 : 0 ≤ 2 * β * hH.eigenvalues i :=
        mul_nonneg (mul_nonneg (by norm_num) hβ) (hPSD.eigenvalues_nonneg i)
      have hz : 2 * β * hH.eigenvalues i ≤ 1 / 2 := by linarith [hβμ i]
      simpa using one_sub_rpow_le_exp hz0 hz
  have hsumμ : ∑ i, hH.eigenvalues i = realMatrixFrobeniusSq M := by
    have htr : H.trace = ∑ i, hH.eigenvalues i := by
      simpa using hH.trace_eq_sum_eigenvalues
    have hF : H.trace = realMatrixFrobeniusSq M := by
      simp only [H]
      rw [Matrix.trace_mul_comm, realMatrixFrobeniusSq_eq_trace_mul_transpose]
    linarith
  have hsum : ∑ i, 2 * β * hH.eigenvalues i = 2 * β * realMatrixFrobeniusSq M := by
    rw [← Finset.mul_sum, hsumμ]
  calc
    ∫ x, Real.exp (β * ((M *ᵥ x) ⬝ᵥ (M *ᵥ x))) ∂γ =
        ∫ v, quad v ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) := hintEq
    _ = ∫ x, Real.exp (β * ∑ i, hH.eigenvalues i * x i ^ 2) ∂γ := hintDiag
    _ = ∏ i, (1 - 2 * β * hH.eigenvalues i) ^ (-1 / 2 : ℝ) := hdiag.2
    _ ≤ ∏ i, Real.exp (2 * β * hH.eigenvalues i) := hprodle
    _ = Real.exp (∑ i, 2 * β * hH.eigenvalues i) := by rw [← Real.exp_sum]
    _ = Real.exp (2 * β * realMatrixFrobeniusSq M) := by rw [hsum]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A psi-two bound at scale `2K` is sub-Gaussian with proxy `64 K²`. -/
lemma hasSubgaussianMGF_scale [IsProbabilityMeasure μ] {X : Ω → ℝ} (hm : Measurable X)
    (h0 : ∫ ω, X ω ∂μ = 0) {K : ℝ} (h : HasPsiTwoBound X μ (2 * K)) :
    HasSubgaussianMGF X (⟨64 * K ^ 2, by positivity⟩ : ℝ≥0) μ := by
  have hsub := h.hasSubgaussianMGF hm h0
  have hnum : (16 : ℝ) * (2 * K) ^ 2 = 64 * K ^ 2 := by
    rw [mul_pow]
    have h4 : (2 : ℝ) ^ 2 = 4 := by norm_num
    have h64 : (16 : ℝ) * 4 = 64 := by norm_num
    rw [h4, ← mul_assoc, h64]
  have hcoe : (⟨16 * (2 * K) ^ 2, by positivity⟩ : ℝ≥0) =
      (⟨64 * K ^ 2, by positivity⟩ : ℝ≥0) := Subtype.ext hnum
  exact ⟨hsub.integrable_exp_mul, fun t ↦ (hsub.mgf_le t).trans_eq (by
    congr 1
    simp [hcoe])⟩

/-- Independent sub-Gaussian coordinates have a sub-Gaussian linear form. -/
lemma integral_exp_linear_of_subgaussian [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (Y : ι → Ω → ℝ) (hindep : iIndepFun Y μ) {c : ℝ≥0}
    (hc : ∀ i, HasSubgaussianMGF (Y i) c μ) (v : ι → ℝ) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * ∑ i, v i * Y i ω)) μ ∧
      ∫ ω, Real.exp (t * ∑ i, v i * Y i ω) ∂μ ≤
        Real.exp ((c : ℝ) * (∑ i, v i ^ 2) * t ^ 2 / 2) := by
  let Z : ι → Ω → ℝ := fun i ω ↦ v i * Y i ω
  have hZindep : iIndepFun Z μ := by
    simpa [Z, Function.comp_def] using
      hindep.comp (fun i r ↦ v i * r) fun _ ↦ measurable_id.const_mul _
  have hZ : ∀ i, HasSubgaussianMGF (Z i)
      (NNReal.mk ((v i) ^ 2) (sq_nonneg (v i)) * c) μ :=
    fun i ↦ (hc i).const_mul (v i)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun
    (c := fun i ↦ NNReal.mk ((v i) ^ 2) (sq_nonneg (v i)) * c) hZindep
    (s := Finset.univ) fun i _ ↦ hZ i
  refine ⟨by simpa [Z, Finset.sum_apply] using hsum.integrable_exp_mul t, ?_⟩
  have hcoef :
      (((∑ i, NNReal.mk ((v i) ^ 2) (sq_nonneg (v i)) * c) : ℝ≥0) : ℝ) =
        (c : ℝ) * ∑ i, v i ^ 2 := by
    rw [NNReal.coe_sum]
    simp_rw [NNReal.coe_mul, NNReal.coe_mk]
    rw [← Finset.sum_mul, mul_comm]
  calc
    ∫ ω, Real.exp (t * ∑ i, v i * Y i ω) ∂μ = mgf (fun ω ↦ ∑ i, Z i ω) μ t := by
      simp [mgf, Z]
    _ ≤ Real.exp (((∑ i, NNReal.mk ((v i) ^ 2) (sq_nonneg (v i)) * c) : ℝ≥0) *
        t ^ 2 / 2) := hsum.mgf_le t
    _ = Real.exp ((c : ℝ) * (∑ i, v i ^ 2) * t ^ 2 / 2) := by
      rw [hcoef]

/-- Coordinate projections inherit a product of identical sub-Gaussian proxies. -/
lemma hasSubgaussianMGF_pi_eval {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] {c : ℝ≥0}
    (h : ∀ i, HasSubgaussianMGF id c (ν i)) (i : ι) :
    HasSubgaussianMGF (fun x : ι → ℝ ↦ x i) c (Measure.pi ν) := by
  have hmap := (measurePreserving_eval ν i).map_eq
  exact (HasSubgaussianMGF.id_map_iff (measurable_pi_apply i).aemeasurable).1
    (by simpa [← hmap] using h i)

/-- `exp(α ‖c‖²)` is the moment-generating integral of a standard Gaussian vector. -/
lemma exp_dot_sq_eq_gaussian_integral (c : Fin n → ℝ) {α : ℝ} (hα : 0 ≤ α) :
    Real.exp (α * ∑ i, c i ^ 2) =
      ∫ g, Real.exp (Real.sqrt (2 * α) * (c ⬝ᵥ g))
        ∂(Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) := by
  let t : Fin n → ℝ := fun i ↦ Real.sqrt (2 * α) * c i
  have hfun : (fun g : Fin n → ℝ ↦ Real.exp (Real.sqrt (2 * α) * (c ⬝ᵥ g))) =
      fun g ↦ ∏ i, Real.exp (t i * g i) := by
    ext g
    rw [← Real.exp_sum]
    congr 1
    simp only [dotProduct]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [t]
    ring
  rw [hfun, integral_fintype_prod_eq_prod (fun i u ↦ Real.exp (t i * u))
    (μ := fun _ : Fin n ↦ gaussianReal 0 1)]
  have hprod : ∏ i, Real.exp (t i ^ 2 / 2) = Real.exp (α * ∑ i, c i ^ 2) := by
    rw [← Real.exp_sum]
    congr 1
    have hterm : ∀ i, t i ^ 2 / 2 = α * c i ^ 2 := by
      intro i
      simp only [t, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * α)]
      ring
    simp_rw [hterm, ← Finset.mul_sum]
  refine (hprod.symm).trans (Finset.prod_congr rfl fun i _ ↦ ?_)
  have hmgf := congrFun (mgf_id_gaussianReal (μ := 0) (v := (1 : ℝ≥0))) (t i)
  simpa [mgf, NNReal.coe_one, mul_one, zero_mul, zero_add] using hmgf.symm

/-- The mean of a sampled quadratic form is the diagonal sum of second moments. -/
lemma integral_sampledQuadraticForm [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (hcent : ∀ i, ∫ ω, X i ω ∂μ = 0) {K : ℝ}
    (hpsi : ∀ i, HasPsiTwoBound (X i) μ (2 * K)) (A : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (sampledQuadraticForm A X) μ ∧
      ∫ ω, sampledQuadraticForm A X ω ∂μ = ∑ i, A i i * ∫ ω, X i ω ^ 2 ∂μ := by
  have hsq : ∀ i, Integrable (fun ω ↦ X i ω ^ 2) μ := by
    intro i
    have hG : HasGaussianMoments (X i) μ (4 * K) := by
      simpa [show 2 * (2 * K) = 4 * K by ring] using (hpsi i).hasGaussianMoments (hmeas i)
    have hmem : MemLp (X i) 2 μ := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
      exact (hG.2 2 (by norm_num)).trans_lt ENNReal.ofReal_lt_top
    exact hmem.integrable_sq
  have hprod : ∀ i j, Integrable (fun ω ↦ X i ω * X j ω) μ := by
    intro i j
    refine Integrable.mono (((hsq i).add (hsq j)).div_const 2)
      (((hmeas i).mul (hmeas j)).aestronglyMeasurable) ?_
    refine ae_of_all _ fun ω ↦ ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Pi.add_apply, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ (X i ω ^ 2 + X j ω ^ 2) / 2)]
    have hdiff : 0 ≤ X i ω ^ 2 - 2 * |X i ω| * |X j ω| + X j ω ^ 2 := by
      have hsq := sq_nonneg (|X i ω| - |X j ω|)
      have hexp : (|X i ω| - |X j ω|) ^ 2 =
          |X i ω| ^ 2 - 2 * |X i ω| * |X j ω| + |X j ω| ^ 2 := by ring
      rw [hexp, sq_abs, sq_abs] at hsq
      exact hsq
    linarith
  have hterm : ∀ i j, Integrable (fun ω ↦ A i j * X i ω * X j ω) μ :=
    fun i j ↦ by simpa [mul_assoc] using (hprod i j).const_mul (A i j)
  refine ⟨?_, ?_⟩
  · unfold sampledQuadraticForm
    exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hterm i j
  · unfold sampledQuadraticForm
    rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hterm i j]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_finsetSum _ fun j _ ↦ hterm i j]
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by
      have hmul := IndepFun.integral_fun_mul_eq_mul_integral (hindep.indepFun hj.symm)
        (hmeas i).aestronglyMeasurable (hmeas j).aestronglyMeasurable
      have hfun : (fun a ↦ A i j * X i a * X j a) =
          fun a ↦ A i j * (X i a * X j a) := by
        ext a
        rw [mul_assoc]
      rw [hfun, integral_const_mul, hmul, hcent i, hcent j]
      simp)
      (fun hi ↦ absurd (Finset.mem_univ i) hi)]
    have hdiag : (fun ω ↦ A i i * X i ω * X i ω) = fun ω ↦ A i i * X i ω ^ 2 := by
      ext ω
      rw [pow_two, mul_assoc]
    rw [hdiag, integral_const_mul]

/-- Matrix with the Boolean cut `δ i ∧ ¬δ j` retained. -/
def maskedMatrix (A : Matrix (Fin n) (Fin n) ℝ) (δ : Fin n → Bool) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ if δ i = true ∧ δ j = false then A i j else 0

/-- Erasing entries does not increase the squared Frobenius norm. -/
lemma maskedMatrix_frobenius_le (A : Matrix (Fin n) (Fin n) ℝ) (δ : Fin n → Bool) :
    realMatrixFrobeniusSq (maskedMatrix A δ) ≤ realMatrixFrobeniusSq A := by
  unfold maskedMatrix realMatrixFrobeniusSq
  refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
  by_cases h : δ i = true ∧ δ j = false <;> simp [h, sq_nonneg]

/-- Transposition preserves the squared Frobenius norm. -/
lemma realMatrixFrobeniusSq_transpose (A : Matrix (Fin n) (Fin n) ℝ) :
    realMatrixFrobeniusSq A.transpose = realMatrixFrobeniusSq A := by
  unfold realMatrixFrobeniusSq
  simp_rw [Matrix.transpose_apply]
  exact Finset.sum_comm

/-- A Boolean cut does not increase the Euclidean operator norm. -/
lemma maskedMatrix_opNorm_le (A : Matrix (Fin n) (Fin n) ℝ) (δ : Fin n → Bool) :
    realMatrixOperatorNorm (maskedMatrix A δ) ≤ realMatrixOperatorNorm A := by
  classical
  let dTrue : Fin n → ℝ := fun i ↦ if δ i = true then 1 else 0
  let dFalse : Fin n → ℝ := fun j ↦ if δ j = false then 1 else 0
  have hM : maskedMatrix A δ = Matrix.diagonal dTrue * A * Matrix.diagonal dFalse := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [maskedMatrix, dTrue, dFalse]
    by_cases hi : δ i = true <;> by_cases hj : δ j = false <;> simp [hi, hj]
  have hTrue : ‖dTrue‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    by_cases hi : δ i = true <;> simp [dTrue, hi]
  have hFalse : ‖dFalse‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    by_cases hj : δ j = false <;> simp [dFalse, hj]
  rw [realMatrixOperatorNorm_eq, realMatrixOperatorNorm_eq, hM]
  have hmulA := Matrix.l2_opNorm_mul (Matrix.diagonal dTrue) A
  have hmulD := Matrix.l2_opNorm_mul (Matrix.diagonal dTrue * A) (Matrix.diagonal dFalse)
  have hdiagT : ‖Matrix.diagonal dTrue‖ = ‖dTrue‖ := Matrix.l2_opNorm_diagonal dTrue
  have hdiagF : ‖Matrix.diagonal dFalse‖ = ‖dFalse‖ := Matrix.l2_opNorm_diagonal dFalse
  set u : ℝ := ‖dTrue‖
  set v : ℝ := ‖dFalse‖
  set a : ℝ := ‖A‖
  have hu0 : 0 ≤ u := norm_nonneg _
  have hv0 : 0 ≤ v := norm_nonneg _
  have ha0 : 0 ≤ a := norm_nonneg _
  have hprod : u * a * v ≤ a := by
    have h1 : u * a ≤ a := by simpa using mul_le_mul_of_nonneg_right hTrue ha0
    have h2 : u * a * v ≤ u * a := by
      simpa using mul_le_mul_of_nonneg_left hFalse (mul_nonneg hu0 ha0)
    exact h2.trans h1
  calc
    ‖Matrix.diagonal dTrue * A * Matrix.diagonal dFalse‖ ≤
        ‖Matrix.diagonal dTrue * A‖ * ‖Matrix.diagonal dFalse‖ := hmulD
    _ ≤ (‖Matrix.diagonal dTrue‖ * ‖A‖) * ‖Matrix.diagonal dFalse‖ :=
      mul_le_mul_of_nonneg_right hmulA (norm_nonneg _)
    _ = u * a * v := by rw [hdiagT, hdiagF]
    _ ≤ a := hprod

/-- Off-diagonal part of a quadratic form. -/
def offDiagonalForm (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else A i j * x i * x j

/-- One Boolean slice of the off-diagonal form. -/
def bernoulliSlice (A : Matrix (Fin n) (Fin n) ℝ) (δ : Fin n → Bool) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, if δ i = true ∧ δ j = false then A i j * x i * x j else 0

/-- For `i ≠ j`, a quarter of the Boolean vectors select the ordered pair. -/
lemma card_bool_split (i j : Fin n) (hij : i ≠ j) :
    Fintype.card {δ : Fin n → Bool // δ i = true ∧ δ j = false} = 2 ^ (n - 2) := by
  classical
  let T := {k : Fin n // k ≠ i ∧ k ≠ j}
  let e : {δ : Fin n → Bool // δ i = true ∧ δ j = false} ≃ (T → Bool) :=
    { toFun := fun δ t ↦ δ.1 t.1
      invFun := fun f ↦ ⟨fun k ↦ if hk : k = i then true else if hj : k = j then false else
          f ⟨k, hk, hj⟩, by simp [hij.symm]⟩
      left_inv := by
        intro δ
        ext k
        by_cases hk : k = i
        · simp [hk, δ.2.1]
        · by_cases hj : k = j
          · simp [hj, hij.symm, δ.2.2]
          · simp [hk, hj]
      right_inv := by
        intro f
        ext t
        simp [t.2.1, t.2.2] }
  have hT : Fintype.card T = n - 2 := by
    rw [Fintype.card_subtype]
    have hsub : ({k : Fin n | k ≠ i ∧ k ≠ j} : Finset _) = Finset.univ \ {i, j} := by
      ext k
      simp [Finset.mem_sdiff]
    rw [hsub, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
      (Finset.card_pair_eq_two_iff.mpr hij)]
  have hE : Fintype.card {δ : Fin n → Bool // δ i = true ∧ δ j = false} =
      2 ^ (n - 2) := by
    rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool, hT]
  exact hE

/-- The Boolean average of a pair indicator is `0` on the diagonal and `1 / 4` off it. -/
lemma sum_indicator_pair (i j : Fin n) :
    ∑ δ : Fin n → Bool, (if δ i = true ∧ δ j = false then (1 : ℝ) else 0) =
      if i = j then 0 else (2 : ℝ) ^ n / 4 := by
  classical
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  by_cases hij : i = j
  · simp [hij]
  · rw [ite_eq_right hij]
    have hcard : ((Finset.univ.filter fun δ : Fin n → Bool ↦
        δ i = true ∧ δ j = false).card : ℝ) = (2 : ℝ) ^ (n - 2) := by
      rw [← Fintype.card_subtype, card_bool_split i j hij]
      norm_cast
    rw [hcard]
    have hn : 2 ≤ n := by
      have hne : i.1 ≠ j.1 := Fin.val_injective.ne hij
      omega
    have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 2) * 4 := by
      conv_lhs => rw [← Nat.sub_add_cancel hn]
      rw [pow_add]
      norm_num
    rw [eq_div_iff (by norm_num : (4 : ℝ) ≠ 0)]
    exact hpow.symm

/-- The off-diagonal form is four times the average Boolean slice. -/
lemma offDiagonalForm_eq_average (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    offDiagonalForm A v =
      (4 / (2 : ℝ) ^ n) * ∑ δ : Fin n → Bool, bernoulliSlice A δ v := by
  classical
  unfold offDiagonalForm bernoulliSlice
  symm
  rw [Finset.mul_sum]
  have hpull : ∀ δ : Fin n → Bool, (4 / (2 : ℝ) ^ n) *
      (∑ i, ∑ j, if δ i = true ∧ δ j = false then A i j * v i * v j else 0) =
      ∑ i, (∑ j, (4 / (2 : ℝ) ^ n) *
        (if δ i = true ∧ δ j = false then A i j * v i * v j else 0)) := by
    intro δ
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
  simp_rw [hpull]
  have hswap : ∑ δ : Fin n → Bool, ∑ i, (∑ j, (4 / (2 : ℝ) ^ n) *
      (if δ i = true ∧ δ j = false then A i j * v i * v j else 0)) =
      ∑ i, ∑ δ : Fin n → Bool, (∑ j, (4 / (2 : ℝ) ^ n) *
        (if δ i = true ∧ δ j = false then A i j * v i * v j else 0)) :=
    Finset.sum_comm
  rw [hswap]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hswap2 : ∑ δ : Fin n → Bool, (∑ j, (4 / (2 : ℝ) ^ n) *
      (if δ i = true ∧ δ j = false then A i j * v i * v j else 0)) =
      ∑ j, ∑ δ : Fin n → Bool, (4 / (2 : ℝ) ^ n) *
        (if δ i = true ∧ δ j = false then A i j * v i * v j else 0) :=
    Finset.sum_comm
  rw [hswap2]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hcoef := sum_indicator_pair (n := n) i j
  by_cases hij : i = j
  · simp [hij]
  · have hc : ∀ δ : Fin n → Bool,
        (4 / (2 : ℝ) ^ n) * (if δ i = true ∧ δ j = false then A i j * v i * v j else 0) =
          (A i j * v i * v j) * ((4 / (2 : ℝ) ^ n) *
            (if δ i = true ∧ δ j = false then (1 : ℝ) else 0)) := by
      intro δ
      by_cases hδ : δ i = true ∧ δ j = false
      · simp [hδ, mul_comm]
      · simp [hδ]
    simp_rw [hc, ← Finset.mul_sum, hcoef, ite_eq_right hij]
    field_simp

/-- Jensen compares the off-diagonal exponential with the average slice exponential. -/
lemma exp_offDiagonal_le_avg (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (θ : ℝ) :
    Real.exp (θ * offDiagonalForm A v) ≤
      (∑ δ : Fin n → Bool, Real.exp (4 * θ * bernoulliSlice A δ v)) / (2 : ℝ) ^ n := by
  have hsumw : ∑ δ : Fin n → Bool, (1 : ℝ) / (2 : ℝ) ^ n = 1 := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
  have hexp : θ * offDiagonalForm A v =
      ∑ δ : Fin n → Bool, ((1 : ℝ) / (2 : ℝ) ^ n) • (4 * θ * bernoulliSlice A δ v) := by
    rw [offDiagonalForm_eq_average, ← mul_assoc, Finset.mul_sum]
    simp_rw [smul_eq_mul]
    refine Finset.sum_congr rfl fun _ _ ↦ ?_
    ring_nf
  rw [hexp]
  have hineq := convexOn_exp.map_sum_le (t := Finset.univ)
    (w := fun _ : Fin n → Bool ↦ (1 : ℝ) / (2 : ℝ) ^ n)
    (p := fun δ ↦ 4 * θ * bernoulliSlice A δ v) (fun _ _ ↦ by positivity) hsumw
    (fun _ _ ↦ Set.mem_univ _)
  simp_rw [smul_eq_mul, div_eq_mul_inv] at hineq ⊢
  simp only [one_mul] at hineq ⊢
  refine hineq.trans ?_
  rw [← Finset.mul_sum, mul_comm]

/-- Transposition preserves the Euclidean operator norm. -/
lemma realMatrixOperatorNorm_transpose (A : Matrix (Fin n) (Fin n) ℝ) :
    realMatrixOperatorNorm A.transpose = realMatrixOperatorNorm A := by
  rw [realMatrixOperatorNorm_eq, realMatrixOperatorNorm_eq,
    ← Matrix.conjTranspose_eq_transpose_of_trivial A, Matrix.l2_opNorm_conjTranspose]

/-- A Boolean slice is the dot product against the masked transpose. -/
lemma bernoulliSlice_eq_dot (A : Matrix (Fin n) (Fin n) ℝ) (δ : Fin n → Bool)
    (x : Fin n → ℝ) :
    bernoulliSlice A δ x = ((maskedMatrix A δ).transpose *ᵥ x) ⬝ᵥ x := by
  classical
  unfold bernoulliSlice
  simp only [maskedMatrix, Matrix.transpose_apply, Matrix.mulVec_apply_eq_sum, dotProduct]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hfac : ∀ i,
      (if δ i = true ∧ δ j = false then A i j * x i * x j else 0) =
        ((if δ i = true ∧ δ j = false then A i j else 0) * x i) * x j := by
    intro i
    by_cases h : δ i = true ∧ δ j = false
    · rw [ite_eq_left h, ite_eq_left h, mul_assoc]
    · rw [ite_eq_right h, ite_eq_right h, zero_mul, zero_mul]
  simp_rw [hfac, ← Finset.sum_mul]

/-- `exp(α ‖M x‖²)` on a sub-Gaussian product, for `α` below the operator scale. -/
lemma integral_exp_mulVec_sq_subgaussian (ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] {K α : ℝ} (hK : 0 < K) (hα : 0 ≤ α)
    (hsub : ∀ i, HasSubgaussianMGF id (⟨64 * K ^ 2, by positivity⟩ : ℝ≥0) (ν i))
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hcut : 64 * K ^ 2 * α * realMatrixOperatorNorm M ^ 2 ≤ 1 / 4) :
    Integrable (fun x ↦ Real.exp (α * ((M *ᵥ x) ⬝ᵥ (M *ᵥ x)))) (Measure.pi ν) ∧
      ∫ x, Real.exp (α * ((M *ᵥ x) ⬝ᵥ (M *ᵥ x))) ∂Measure.pi ν ≤
        Real.exp (128 * K ^ 2 * α * realMatrixFrobeniusSq M) := by
  let ρ := Measure.pi ν
  let γ := Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)
  let t : ℝ := Real.sqrt (2 * α)
  have h2α : 0 ≤ 2 * α := mul_nonneg (by norm_num) hα
  have ht : t ^ 2 = 2 * α := Real.sq_sqrt h2α
  have hdot : ∀ x g : Fin n → ℝ, (M *ᵥ x) ⬝ᵥ g = (M.transpose *ᵥ g) ⬝ᵥ x := by
    intro x g
    rw [dotProduct_comm (M *ᵥ x) g, ← Matrix.dotProduct_transpose_mulVec M x g,
      dotProduct_comm]
  let F : (Fin n → ℝ) × (Fin n → ℝ) → ℝ :=
    fun p ↦ Real.exp (t * ((M *ᵥ p.1) ⬝ᵥ p.2))
  have hFcont : Continuous F := by
    unfold F
    fun_prop
  have hFsm : StronglyMeasurable F := hFcont.stronglyMeasurable
  have hindep : iIndepFun (fun i (x : Fin n → ℝ) ↦ x i) ρ :=
    iIndepFun_pi (fun _ ↦ aemeasurable_id)
  have hc : ∀ i, HasSubgaussianMGF (fun x : Fin n → ℝ ↦ x i)
      (⟨64 * K ^ 2, by positivity⟩ : ℝ≥0) ρ := fun i ↦ hasSubgaussianMGF_pi_eval ν hsub i
  have hlin : ∀ g, Integrable (fun x ↦ Real.exp (t * ((M.transpose *ᵥ g) ⬝ᵥ x))) ρ ∧
      ∫ x, Real.exp (t * ((M.transpose *ᵥ g) ⬝ᵥ x)) ∂ρ ≤
        Real.exp (64 * K ^ 2 * α * ((M.transpose *ᵥ g) ⬝ᵥ (M.transpose *ᵥ g))) := by
    intro g
    let v : Fin n → ℝ := fun i ↦ (M.transpose *ᵥ g) i
    have hbound :=
      integral_exp_linear_of_subgaussian (fun i (x : Fin n → ℝ) ↦ x i) hindep hc v t
    have hv : (fun x ↦ Real.exp (t * ((M.transpose *ᵥ g) ⬝ᵥ x))) =
        fun x ↦ Real.exp (t * ∑ i, v i * x i) := by
      ext x; simp [v, dotProduct]
    have hpow : ((⟨64 * K ^ 2, by positivity⟩ : ℝ≥0) : ℝ) * (∑ i, v i ^ 2) * t ^ 2 / 2 =
        64 * K ^ 2 * α * ((M.transpose *ᵥ g) ⬝ᵥ (M.transpose *ᵥ g)) := by
      simp only [ht, v, dotProduct, sq]
      ring_nf
    rw [hv]
    exact ⟨hbound.1, hbound.2.trans_eq (congrArg Real.exp hpow)⟩
  have hcutT : (64 * K ^ 2 * α) * realMatrixOperatorNorm M.transpose ^ 2 ≤ 1 / 4 := by
    rw [realMatrixOperatorNorm_transpose]
    simpa [mul_assoc] using hcut
  have hgauss := integral_exp_mulVec_sq_gaussian M.transpose (β := 64 * K ^ 2 * α)
    (mul_nonneg (by positivity) hα) hcutT
  have houter : Integrable (fun g ↦ ∫ x, ‖F (x, g)‖ ∂ρ) γ := by
    have hsm : StronglyMeasurable (fun g ↦ ∫ x, ‖F (x, g)‖ ∂ρ) :=
      hFsm.norm.integral_prod_left'
    refine Integrable.mono' hgauss.1 hsm.aestronglyMeasurable ?_
    filter_upwards with g
    have hnn : 0 ≤ ∫ x, ‖F (x, g)‖ ∂ρ := integral_nonneg fun _ ↦ norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc
      ∫ x, ‖F (x, g)‖ ∂ρ =
          ∫ x, Real.exp (t * ((M.transpose *ᵥ g) ⬝ᵥ x)) ∂ρ := by
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        dsimp only [F]
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hdot x g]
      _ ≤ Real.exp (64 * K ^ 2 * α *
          ((M.transpose *ᵥ g) ⬝ᵥ (M.transpose *ᵥ g))) := (hlin g).2
  have hintProd : Integrable F (ρ.prod γ) :=
    (integrable_prod_iff' hFsm.aestronglyMeasurable).2
      ⟨ae_of_all _ fun g ↦ by simpa [F, hdot] using (hlin g).1, houter⟩
  have hrep : ∀ x, ∫ g, F (x, g) ∂γ =
      Real.exp (α * ((M *ᵥ x) ⬝ᵥ (M *ᵥ x))) := by
    intro x
    have hsq : (M *ᵥ x) ⬝ᵥ (M *ᵥ x) = ∑ i, (M *ᵥ x) i ^ 2 := by simp [dotProduct, sq]
    simpa [F, t, hsq] using (exp_dot_sq_eq_gaussian_integral (M *ᵥ x) hα).symm
  have hid : (fun x ↦ ∫ g, F (x, g) ∂γ) =
      fun x ↦ Real.exp (α * ((M *ᵥ x) ⬝ᵥ (M *ᵥ x))) := funext hrep
  refine ⟨by simpa [hid] using hintProd.integral_prod_left, ?_⟩
  have hright : Integrable (fun g ↦ ∫ x, F (x, g) ∂ρ) γ := hintProd.integral_prod_right
  have hswap : ∫ x, (∫ g, F (x, g) ∂γ) ∂ρ = ∫ g, ∫ x, F (x, g) ∂ρ ∂γ :=
    integral_integral_swap (f := fun x g ↦ F (x, g)) hintProd
  calc
    ∫ x, Real.exp (α * ((M *ᵥ x) ⬝ᵥ (M *ᵥ x))) ∂ρ =
        ∫ x, (∫ g, F (x, g) ∂γ) ∂ρ := by rw [← hid]
    _ = ∫ g, ∫ x, F (x, g) ∂ρ ∂γ := hswap
    _ ≤ ∫ g, Real.exp (64 * K ^ 2 * α *
        ((M.transpose *ᵥ g) ⬝ᵥ (M.transpose *ᵥ g))) ∂γ := by
      refine integral_mono hright hgauss.1 fun g ↦ ?_
      calc
        ∫ x, F (x, g) ∂ρ =
            ∫ x, Real.exp (t * ((M.transpose *ᵥ g) ⬝ᵥ x)) ∂ρ := by
          refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
          simp [F, hdot]
        _ ≤ Real.exp (64 * K ^ 2 * α *
            ((M.transpose *ᵥ g) ⬝ᵥ (M.transpose *ᵥ g))) := (hlin g).2
    _ ≤ Real.exp (2 * (64 * K ^ 2 * α) * realMatrixFrobeniusSq M.transpose) := hgauss.2
    _ = Real.exp (128 * K ^ 2 * α * realMatrixFrobeniusSq M) := by
      rw [realMatrixFrobeniusSq_transpose]
      ring_nf


end CKMA
