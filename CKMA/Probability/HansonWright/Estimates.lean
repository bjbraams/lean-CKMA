/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

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
# Hanson–Wright norm and diagonal estimates

Squared Frobenius norm, Euclidean operator norm, and the sampled quadratic form.
Sub-Gaussian moment generating functions give the diagonal contribution to the
Hanson–Wright tail.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal RealInnerProductSpace Matrix Matrix.Norms.L2Operator

universe u

variable {n : ℕ}

/-- The squared Frobenius norm of a real matrix, given by its entries. -/
def realMatrixFrobeniusSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- Euclidean operator norm, as distinct from the entrywise matrix norm. -/
def realMatrixOperatorNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖

/-- The real quadratic form sampled at a coordinate family. -/
def sampledQuadraticForm {Ω : Type*} {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i, ∑ j, A i j * X i ω * X j ω

variable {n : ℕ}

/-- Squared entry sums are nonnegative. -/
lemma realMatrixFrobeniusSq_nonneg (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ realMatrixFrobeniusSq A :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The Euclidean operator norm is nonnegative. -/
lemma realMatrixOperatorNorm_nonneg (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ realMatrixOperatorNorm A :=
  norm_nonneg _

/-- The adapter agrees with the scoped Euclidean operator norm. -/
lemma realMatrixOperatorNorm_eq (A : Matrix (Fin n) (Fin n) ℝ) :
    realMatrixOperatorNorm A = ‖A‖ := by
  simp [realMatrixOperatorNorm, Matrix.l2_opNorm_def]

/-- A diagonal entry is bounded by the operator norm. -/
lemma abs_diag_le_realMatrixOperatorNorm (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    |A i i| ≤ realMatrixOperatorNorm A := by
  rw [realMatrixOperatorNorm_eq, Matrix.cstar_norm_def]
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
  have he : ‖e‖ = 1 := by simp [e, EuclideanSpace.single, PiLp.norm_single]
  have hfun : (e : Fin n → ℝ) = Pi.single i 1 := by
    simp [e, EuclideanSpace.single, PiLp.ofLp_single]
  have hdot : ⟪e, T A e⟫ = A i i := by
    rw [Matrix.inner_toEuclideanCLM, hfun, Matrix.mulVec_single_one, single_one_dotProduct]
    simp [Matrix.col_apply]
  calc
    |A i i| = |⟪e, T A e⟫| := by rw [hdot]
    _ ≤ ‖e‖ * ‖T A e‖ := abs_real_inner_le_norm e _
    _ ≤ ‖e‖ * (‖T A‖ * ‖e‖) := by
      gcongr
      exact (T A).le_opNorm e
    _ = ‖T A‖ := by rw [he]; ring

/-- The sum of squared diagonal entries is at most the squared Frobenius norm. -/
lemma sum_diag_sq_le_realMatrixFrobeniusSq (A : Matrix (Fin n) (Fin n) ℝ) :
    ∑ i, (A i i) ^ 2 ≤ realMatrixFrobeniusSq A := by
  unfold realMatrixFrobeniusSq
  refine Finset.sum_le_sum fun i _ ↦ ?_
  exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (A i j)) (Finset.mem_univ i)

/-- Squared Frobenius norm as the trace of `A` times its transpose. -/
lemma realMatrixFrobeniusSq_eq_trace_mul_transpose (A : Matrix (Fin n) (Fin n) ℝ) :
    realMatrixFrobeniusSq A = (A * A.transpose).trace := by
  unfold realMatrixFrobeniusSq Matrix.trace
  simp_rw [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, sq]

/-- Each coordinate of a matrix-vector product is controlled by Cauchy–Schwarz. -/
lemma sq_mulVec_apply_le (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (i : Fin n) :
    (∑ j, A i j * x j) ^ 2 ≤ (∑ j, (A i j) ^ 2) * ∑ j, x j ^ 2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
    (fun j ↦ A i j) (fun j ↦ x j)

/-- The squared operator norm is at most the squared Frobenius norm. -/
lemma realMatrixOperatorNorm_sq_le_frobenius (A : Matrix (Fin n) (Fin n) ℝ) :
    realMatrixOperatorNorm A ^ 2 ≤ realMatrixFrobeniusSq A := by
  have hF := realMatrixFrobeniusSq_nonneg A
  rw [realMatrixOperatorNorm_eq]
  suffices hbound : ‖A‖ ≤ Real.sqrt (realMatrixFrobeniusSq A) by
    calc
      ‖A‖ ^ 2 ≤ (Real.sqrt (realMatrixFrobeniusSq A)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hbound 2
      _ = realMatrixFrobeniusSq A := Real.sq_sqrt hF
  rw [← Matrix.l2_opNorm_toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x ↦ ?_
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)
  have hsq : ‖T A x‖ ^ 2 ≤ realMatrixFrobeniusSq A * ‖x‖ ^ 2 := by
    have hcoord : ∀ i, (T A x) i = ∑ j, A i j * (x : Fin n → ℝ) j := by
      intro i
      rw [Matrix.ofLp_toEuclideanCLM]
      exact Matrix.mulVec_apply_eq_sum A x.ofLp i
    calc
      ‖T A x‖ ^ 2 = ∑ i, ((T A x) i) ^ 2 := EuclideanSpace.real_norm_sq_eq _
      _ = ∑ i, (∑ j, A i j * (x : Fin n → ℝ) j) ^ 2 := by simp_rw [hcoord]
      _ ≤ ∑ i, (∑ j, (A i j) ^ 2) * ∑ j, ((x : Fin n → ℝ) j) ^ 2 := by
        refine Finset.sum_le_sum fun i _ ↦ sq_mulVec_apply_le A (x : Fin n → ℝ) i
      _ = (∑ i, ∑ j, (A i j) ^ 2) * ∑ j, ((x : Fin n → ℝ) j) ^ 2 := by
        rw [← Finset.sum_mul]
      _ = realMatrixFrobeniusSq A * ‖x‖ ^ 2 := by
        rw [← realMatrixFrobeniusSq, ← EuclideanSpace.real_norm_sq_eq]
  calc
    ‖T A x‖ = Real.sqrt (‖T A x‖ ^ 2) := by rw [Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (realMatrixFrobeniusSq A * ‖x‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (realMatrixFrobeniusSq A) * ‖x‖ := by
      rw [Real.sqrt_mul hF, Real.sqrt_sq (norm_nonneg _)]

/-- Vanishing squared Frobenius norm means every entry is zero. -/
lemma realMatrixFrobeniusSq_eq_zero_iff (A : Matrix (Fin n) (Fin n) ℝ) :
    realMatrixFrobeniusSq A = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have hsum : ∑ i, ∑ j, (A i j) ^ 2 = 0 := by simpa [realMatrixFrobeniusSq] using h
    have hrow : ∑ j, (A i j) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _)).1
        hsum i (Finset.mem_univ i)
    have hentry : (A i j) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg _)).1 hrow j (Finset.mem_univ j)
    exact sq_eq_zero_iff.mp hentry
  · intro h
    simp [realMatrixFrobeniusSq, h]

/-- A zero Frobenius norm forces the operator norm to vanish. -/
lemma realMatrixOperatorNorm_eq_zero_of_frobenius {A : Matrix (Fin n) (Fin n) ℝ}
    (h : realMatrixFrobeniusSq A = 0) : realMatrixOperatorNorm A = 0 := by
  have hsq : realMatrixOperatorNorm A ^ 2 = 0 :=
    le_antisymm ((realMatrixOperatorNorm_sq_le_frobenius A).trans_eq h)
      (sq_nonneg _)
  exact sq_eq_zero_iff.mp hsq

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A larger scale remains an admissible psi-two bound. -/
lemma HasPsiTwoBound.mono {X : Ω → ℝ} {K L : ℝ} (h : HasPsiTwoBound X μ K) (hKL : K ≤ L) :
    HasPsiTwoBound X μ L := by
  refine ⟨h.1.trans_le hKL, ?_⟩
  have hdiv : ∀ ω, (X ω / L) ^ 2 ≤ (X ω / K) ^ 2 := by
    intro ω
    have habs : |X ω| / L ≤ |X ω| / K :=
      div_le_div_of_nonneg_left (abs_nonneg _) h.1 hKL
    have hsq := pow_le_pow_left₀ (div_nonneg (abs_nonneg _) (h.1.trans_le hKL).le) habs 2
    simpa [div_pow, sq_abs] using hsq
  calc
    ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / L) ^ 2)) ∂μ ≤
        ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / K) ^ 2)) ∂μ := by
      refine lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hdiv ω))
    _ ≤ 2 := h.2

/-- A gauge at most `K` yields an admissible psi-two bound at scale `2K`. -/
lemma hasPsiTwoBound_of_psiTwoGauge_le {X : Ω → ℝ} {K : ℝ} (hK : 0 < K)
    (h : psiTwoGauge X μ ≤ ENNReal.ofReal K) : HasPsiTwoBound X μ (2 * K) := by
  have hlt : psiTwoGauge X μ < ENNReal.ofReal (2 * K) :=
    h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < 2 * K)).mpr (by linarith))
  rw [psiTwoGauge, sInf_lt_iff] at hlt
  obtain ⟨s, hs, hslt⟩ := hlt
  obtain ⟨K', rfl, hK'⟩ := hs
  have hK'lt : K' < 2 * K := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp hslt
  exact hK'.mono hK'lt.le

/-- Natural absolute moments controlled by Gaussian moment growth. -/
lemma lintegral_abs_pow_le_of_gaussianMoments {X : Ω → ℝ} (hm : Measurable X) {K : ℝ}
    (h : HasGaussianMoments X μ K) {m : ℕ} (hmpos : 0 < m) :
    (∫⁻ ω, ENNReal.ofReal (|X ω| ^ m) ∂μ) ≤ ENNReal.ofReal ((K * Real.sqrt m) ^ m) := by
  have hm0 : 0 < (m : ℝ) := Nat.cast_pos.mpr hmpos
  have he := ENNReal.rpow_le_rpow (h.2 m (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hmpos.ne')))
    hm0.le
  rw [eLpNorm_eq_eLpNorm' (by simpa using hmpos.ne') ENNReal.ofReal_ne_top
      hm.aestronglyMeasurable, ENNReal.toReal_ofReal hm0.le,
    ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hm0] at he
  simpa only [ENNReal.rpow_natCast, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
    ← ENNReal.ofReal_pow (mul_nonneg h.1.le (Real.sqrt_nonneg _))] using he

/-- The same comparison for the Bochner integral of an absolute power. -/
lemma integral_abs_pow_le_of_gaussianMoments [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hm : Measurable X) {K : ℝ} (h : HasGaussianMoments X μ K) {m : ℕ} (hmpos : 0 < m) :
    ∫ ω, |X ω| ^ m ∂μ ≤ (K * Real.sqrt m) ^ m := by
  have hlin := lintegral_abs_pow_le_of_gaussianMoments hm h hmpos
  have hmem : MemLp X (.ofReal m) μ := (h.2 m
    (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hmpos.ne'))).trans_lt ENNReal.ofReal_lt_top
  have hint : Integrable (fun ω ↦ |X ω| ^ m) μ := by
    simpa [Real.norm_eq_abs] using hmem.integrable_norm_rpow
      (by simpa using hmpos.ne') ENNReal.ofReal_ne_top
  have hnn : 0 ≤ᵐ[μ] fun ω ↦ |X ω| ^ m := ae_of_all _ fun _ ↦ by positivity
  have hboch := (ofReal_integral_eq_lintegral_ofReal hint hnn).trans_le hlin
  exact (ENNReal.ofReal_le_ofReal_iff
    (pow_nonneg (mul_nonneg h.1.le (Real.sqrt_nonneg _)) _)).mp hboch

/-- A psi-two bound at scale `2K` controls moments of the centered square. -/
lemma integral_abs_pow_centered_sq [IsProbabilityMeasure μ] {X : Ω → ℝ} (hm : Measurable X)
    {K : ℝ} (h : HasPsiTwoBound X μ (2 * K)) {m : ℕ} (hmpos : 0 < m) :
    Integrable (fun ω ↦ |X ω ^ 2 - ∫ η, X η ^ 2 ∂μ| ^ m) μ ∧
      ∫ ω, |X ω ^ 2 - ∫ η, X η ^ 2 ∂μ| ^ m ∂μ ≤ (64 * (m : ℝ) * K ^ 2) ^ m := by
  have hG : HasGaussianMoments X μ (4 * K) := by
    simpa [show 2 * (2 * K) = 4 * K by ring] using h.hasGaussianMoments hm
  have hmem2 : MemLp X (ENNReal.ofReal 2) μ :=
    (hG.2 2 (by norm_num)).trans_lt ENNReal.ofReal_lt_top
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) μ := by
    have : MemLp X 2 μ := by simpa using hmem2
    exact this.integrable_sq
  set σ : ℝ := ∫ η, X η ^ 2 ∂μ
  have hσnn : 0 ≤ σ := integral_nonneg fun _ ↦ sq_nonneg _
  have hσle : σ ≤ 32 * K ^ 2 := by
    have hpow := integral_abs_pow_le_of_gaussianMoments hm hG (m := 2) (by decide)
    have hsq : (4 * K * Real.sqrt 2) ^ 2 = 32 * K ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    simpa [sq_abs, hsq] using hpow
  have hZ : ∀ ω, |X ω ^ 2 - σ| ≤ X ω ^ 2 + σ := by
    intro ω
    calc
      |X ω ^ 2 - σ| = |X ω ^ 2 + -σ| := by ring_nf
      _ ≤ |X ω ^ 2| + |-σ| := abs_add_le _ _
      _ = X ω ^ 2 + σ := by rw [abs_of_nonneg (sq_nonneg _), abs_neg, abs_of_nonneg hσnn]
  have hsqPow : ∀ ω, (X ω ^ 2) ^ m = |X ω| ^ (2 * m) := by
    intro ω
    rw [show (X ω ^ 2) ^ m = X ω ^ (2 * m) from (pow_mul (X ω) 2 m).symm]
    rw [← abs_of_nonneg (Even.pow_nonneg (even_two_mul m) (X ω)), abs_pow]
  have hX2m : ∫ ω, |X ω| ^ (2 * m) ∂μ ≤ (32 * (m : ℝ) * K ^ 2) ^ m := by
    refine (integral_abs_pow_le_of_gaussianMoments hm hG (m := 2 * m)
      (Nat.mul_pos (by decide : 0 < 2) hmpos)).trans_eq ?_
    have hsqrt : Real.sqrt ((2 * m : ℕ) : ℝ) = Real.sqrt (2 * (m : ℝ)) := by
      rw [Nat.cast_mul, Nat.cast_ofNat]
    rw [hsqrt]
    have hsm : 0 ≤ 2 * (m : ℝ) := by positivity
    calc
      (4 * K * Real.sqrt (2 * (m : ℝ))) ^ (2 * m)
          = ((4 * K) ^ (2 * m)) * (Real.sqrt (2 * (m : ℝ))) ^ (2 * m) := by rw [mul_pow]
      _ = ((4 * K) ^ 2) ^ m * ((Real.sqrt (2 * (m : ℝ))) ^ 2) ^ m := by
          rw [pow_mul (4 * K) 2 m, pow_mul (Real.sqrt (2 * (m : ℝ))) 2 m]
      _ = (16 * K ^ 2) ^ m * (2 * (m : ℝ)) ^ m := by
          rw [show (4 * K) ^ 2 = 16 * K ^ 2 by ring, Real.sq_sqrt hsm]
      _ = (16 * K ^ 2 * (2 * (m : ℝ))) ^ m := by rw [← mul_pow]
      _ = (32 * (m : ℝ) * K ^ 2) ^ m := by ring
  have hσm : σ ^ m ≤ (32 * (m : ℝ) * K ^ 2) ^ m := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_of_lt hmpos
    have hbase : 32 * K ^ 2 ≤ 32 * (m : ℝ) * K ^ 2 := by nlinarith [hm1]
    exact pow_le_pow_left₀ hσnn (hσle.trans hbase) _
  have hmemAbs : MemLp X (ENNReal.ofReal (2 * m)) μ :=
    (hG.2 (2 * m) (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_pos (by decide : 0 < 2) hmpos).ne'))).trans_lt ENNReal.ofReal_lt_top
  have hintAbs : Integrable (fun ω ↦ |X ω| ^ (2 * m)) μ := by
    have hintR : Integrable (fun ω ↦ |X ω| ^ ((2 : ℝ) * (m : ℝ))) μ := by
      simpa [Real.norm_eq_abs] using hmemAbs.integrable_norm_rpow
        (by simpa using (Nat.mul_pos (by decide : 0 < 2) hmpos).ne') ENNReal.ofReal_ne_top
    refine hintR.congr (ae_of_all _ fun ω ↦ ?_)
    rw [show (2 : ℝ) * (m : ℝ) = ((2 * m : ℕ) : ℝ) by rw [Nat.cast_mul, Nat.cast_ofNat]]
    exact Real.rpow_natCast (|X ω|) _
  have hpoint : ∀ ω, |X ω ^ 2 - σ| ^ m ≤
      (2 : ℝ) ^ (m - 1) * ((X ω ^ 2) ^ m + σ ^ m) := by
    intro ω
    calc
      |X ω ^ 2 - σ| ^ m ≤ (X ω ^ 2 + σ) ^ m :=
        pow_le_pow_left₀ (abs_nonneg _) (hZ ω) m
      _ ≤ (2 : ℝ) ^ (m - 1) * ((X ω ^ 2) ^ m + σ ^ m) :=
        add_pow_le (sq_nonneg _) hσnn _
  have hpow : Integrable (fun ω ↦ (X ω ^ 2) ^ m) μ :=
    hintAbs.congr (ae_of_all _ fun ω ↦ (hsqPow ω).symm)
  have hRHS : Integrable (fun ω ↦ (2 : ℝ) ^ (m - 1) * ((X ω ^ 2) ^ m + σ ^ m)) μ :=
    (hpow.add (integrable_const (σ ^ m))).const_mul _
  have hintZ : Integrable (fun ω ↦ |X ω ^ 2 - σ| ^ m) μ := by
    refine ⟨((continuous_abs.measurable.comp
      ((hm.pow_const 2).sub_const σ)).pow_const m).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ by positivity)]
    refine (lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal (hpoint ω)).trans_lt ?_
    rw [← hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ by positivity)]
    exact hRHS.hasFiniteIntegral
  refine ⟨hintZ, ?_⟩
  calc
    ∫ ω, |X ω ^ 2 - σ| ^ m ∂μ ≤
        ∫ ω, (2 : ℝ) ^ (m - 1) * ((X ω ^ 2) ^ m + σ ^ m) ∂μ :=
      integral_mono hintZ hRHS hpoint
    _ = (2 : ℝ) ^ (m - 1) * (∫ ω, (X ω ^ 2) ^ m ∂μ + σ ^ m) := by
      rw [integral_const_mul, integral_add hpow (integrable_const _), integral_const,
        Measure.real_def, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one, one_smul]
    _ ≤ (2 : ℝ) ^ (m - 1) *
        ((32 * (m : ℝ) * K ^ 2) ^ m + (32 * (m : ℝ) * K ^ 2) ^ m) := by
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      refine add_le_add ?_ hσm
      have hchange : ∫ ω, (X ω ^ 2) ^ m ∂μ = ∫ ω, |X ω| ^ (2 * m) ∂μ :=
        integral_congr_ae (ae_of_all _ fun ω ↦ hsqPow ω)
      rw [hchange]
      exact hX2m
    _ = (64 * (m : ℝ) * K ^ 2) ^ m := by
      have h2 : (2 : ℝ) ^ (m - 1) * 2 = 2 ^ m := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
        subst hk
        simp [pow_succ]
      calc
        (2 : ℝ) ^ (m - 1) * ((32 * (m : ℝ) * K ^ 2) ^ m + (32 * (m : ℝ) * K ^ 2) ^ m)
            = (2 : ℝ) ^ (m - 1) * (2 * (32 * (m : ℝ) * K ^ 2) ^ m) := by ring
        _ = 2 ^ m * (32 * (m : ℝ) * K ^ 2) ^ m := by rw [← mul_assoc, h2]
        _ = (2 * (32 * (m : ℝ) * K ^ 2)) ^ m := by rw [← mul_pow]
        _ = (64 * (m : ℝ) * K ^ 2) ^ m := by ring

/-- At a sufficiently small scale, the centered square has a quadratic exponential moment. -/
lemma mgf_centered_sq_le [IsProbabilityMeasure μ] {X : Ω → ℝ} (hm : Measurable X) {K : ℝ}
    (h : HasPsiTwoBound X μ (2 * K)) {s : ℝ}
    (hs : |s| ≤ 1 / (128 * Real.exp 1 * K ^ 2)) :
    Integrable (fun ω ↦ Real.exp (s * (X ω ^ 2 - ∫ η, X η ^ 2 ∂μ))) μ ∧
      ∫ ω, Real.exp (s * (X ω ^ 2 - ∫ η, X η ^ 2 ∂μ)) ∂μ ≤
        Real.exp (8192 * (Real.exp 1) ^ 2 * K ^ 4 * s ^ 2) := by
  have hK : 0 < K := by linarith [h.1]
  have hK2 : 0 < 2 * K := by linarith
  set σ : ℝ := ∫ η, X η ^ 2 ∂μ
  let Z : Ω → ℝ := fun ω ↦ X ω ^ 2 - σ
  have hZmeas : Measurable Z := (hm.pow_const 2).sub_const σ
  have hσnn : 0 ≤ σ := integral_nonneg fun _ ↦ sq_nonneg _
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) μ := by
    have hG : HasGaussianMoments X μ (4 * K) := by
      simpa [show 2 * (2 * K) = 4 * K by ring] using h.hasGaussianMoments hm
    have hmem2 : MemLp X (ENNReal.ofReal 2) μ :=
      (hG.2 2 (by norm_num)).trans_lt ENNReal.ofReal_lt_top
    have : MemLp X 2 μ := by simpa using hmem2
    exact this.integrable_sq
  have hZint : Integrable Z μ := hX2.sub (integrable_const σ)
  have hZmean : ∫ ω, Z ω ∂μ = 0 := by
    rw [integral_sub hX2 (integrable_const σ), integral_const, Measure.real_def,
      IsProbabilityMeasure.measure_univ, ENNReal.toReal_one, one_smul]
    ring
  have hZle : ∀ ω, |Z ω| ≤ X ω ^ 2 + σ := by
    intro ω
    dsimp [Z]
    calc
      |X ω ^ 2 - σ| = |X ω ^ 2 + -σ| := by ring_nf
      _ ≤ |X ω ^ 2| + |-σ| := abs_add_le _ _
      _ = X ω ^ 2 + σ := by rw [abs_of_nonneg (sq_nonneg _), abs_neg, abs_of_nonneg hσnn]
  have hs4 : |s| ≤ 1 / (4 * K ^ 2) := by
    refine hs.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num), sq_nonneg K]
  have hsq : ∀ ω, |s| * X ω ^ 2 ≤ (X ω / (2 * K)) ^ 2 := by
    intro ω
    have hmul := mul_le_mul_of_nonneg_right hs4 (sq_nonneg (X ω))
    calc
      |s| * X ω ^ 2 ≤ X ω ^ 2 / (4 * K ^ 2) := by
        simpa [div_eq_mul_inv, mul_comm] using hmul
      _ = (X ω / (2 * K)) ^ 2 := by rw [div_pow]; ring
  have hintAbs : Integrable (fun ω ↦ Real.exp (|s| * |Z ω|)) μ := by
    refine Integrable.mono' ((h.integrable_exp_sq hm).const_mul (Real.exp (|s| * σ)))
      ((continuous_abs.measurable.comp hZmeas).const_mul |s|).exp.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    calc
      |s| * |Z ω| ≤ |s| * (X ω ^ 2 + σ) :=
        mul_le_mul_of_nonneg_left (hZle ω) (abs_nonneg _)
      _ = |s| * X ω ^ 2 + |s| * σ := by ring
      _ ≤ (X ω / (2 * K)) ^ 2 + |s| * σ := by linarith [hsq ω]
      _ = |s| * σ + (X ω / (2 * K)) ^ 2 := by ring
  have hint : Integrable (fun ω ↦ Real.exp (s * Z ω)) μ := by
    refine hintAbs.mono ((hZmeas.const_mul s).exp.aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by rw [abs_mul]))
  let term : ℕ → Ω → ℝ := fun k ω ↦ (s * Z ω) ^ k / (Nat.factorial k : ℝ)
  let bound : ℕ → Ω → ℝ := fun k ω ↦ (|s| * |Z ω|) ^ k / (Nat.factorial k : ℝ)
  have hseries : HasSum (fun k ↦ ∫ ω, term k ω ∂μ) (∫ ω, Real.exp (s * Z ω) ∂μ) := by
    refine hasSum_integral_of_dominated_convergence bound
      (fun k ↦ ((hZmeas.const_mul s).pow_const k).div_const
        (Nat.factorial k : ℝ) |>.aestronglyMeasurable)
      (fun k ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ ?_) ?_ (ae_of_all _ fun ω ↦ ?_)
    · have hfac : |(Nat.factorial k : ℝ)| = Nat.factorial k :=
        abs_of_nonneg (Nat.cast_nonneg _)
      rw [Real.norm_eq_abs, abs_div, abs_pow, abs_mul, hfac]
    · exact Real.summable_pow_div_factorial (|s| * |Z ω|)
    · have hfun : (fun ω ↦ ∑' k, bound k ω) = fun ω ↦ Real.exp (|s| * |Z ω|) := by
        ext ω
        simpa [bound, Real.exp_eq_exp_ℝ] using
          (NormedSpace.expSeries_div_hasSum_exp (|s| * |Z ω|)).tsum_eq
      simpa [hfun] using hintAbs
    · simpa [term, Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (s * Z ω)
  have hr : |s| * 64 * Real.exp 1 * K ^ 2 ≤ (1 / 2 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 64 * Real.exp 1 * K ^ 2)
    calc
      |s| * 64 * Real.exp 1 * K ^ 2 = 64 * Real.exp 1 * K ^ 2 * |s| := by ring
      _ ≤ 64 * Real.exp 1 * K ^ 2 * (1 / (128 * Real.exp 1 * K ^ 2)) := hmul
      _ = 1 / 2 := by field_simp; ring
  set r : ℝ := |s| * 64 * Real.exp 1 * K ^ 2
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 / 2 := hr
  have hrlt : r < 1 := lt_of_le_of_lt hr1 (by norm_num)
  have hmoment : ∀ k : ℕ, 0 < k → |∫ ω, term k ω ∂μ| ≤ r ^ k := by
    intro k hk
    have hintk := (integral_abs_pow_centered_sq hm h hk).1
    have hpow := (integral_abs_pow_centered_sq hm h hk).2
    have hcoef : 0 ≤ |s| ^ k / (Nat.factorial k : ℝ) := by positivity
    have habs_eq : ∀ ω, |term k ω| =
        |s| ^ k / (Nat.factorial k : ℝ) * |Z ω| ^ k := by
      intro ω
      have hfac : |(Nat.factorial k : ℝ)| = Nat.factorial k :=
        abs_of_nonneg (Nat.cast_nonneg _)
      dsimp [term]
      rw [abs_div, abs_pow, abs_mul, hfac, mul_pow, div_eq_mul_inv]
      ring
    have hintTerm : Integrable (fun ω ↦ |term k ω|) μ := by
      simpa [habs_eq] using hintk.const_mul (|s| ^ k / (Nat.factorial k : ℝ))
    calc
      |∫ ω, term k ω ∂μ| = ‖∫ ω, term k ω ∂μ‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ ω, ‖term k ω‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ ω, |term k ω| ∂μ := by simp [Real.norm_eq_abs]
      _ = |s| ^ k / (Nat.factorial k : ℝ) * ∫ ω, |Z ω| ^ k ∂μ := by
          simp_rw [habs_eq]
          rw [integral_const_mul]
      _ ≤ |s| ^ k / (Nat.factorial k : ℝ) * (64 * (k : ℝ) * K ^ 2) ^ k :=
          mul_le_mul_of_nonneg_left hpow hcoef
      _ ≤ r ^ k := by
          have hfact := Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k
          have hkpow : (64 * (k : ℝ) * K ^ 2) ^ k = (64 * K ^ 2) ^ k * (k : ℝ) ^ k := by
            ring
          have hexp : Real.exp (k : ℝ) = Real.exp 1 ^ k := by
            rw [← mul_one (k : ℝ), Real.exp_nat_mul]
          rw [hkpow]
          calc
            |s| ^ k / (Nat.factorial k : ℝ) * ((64 * K ^ 2) ^ k * (k : ℝ) ^ k)
                = (|s| * 64 * K ^ 2) ^ k * ((k : ℝ) ^ k / (Nat.factorial k : ℝ)) := by
                  ring
            _ ≤ (|s| * 64 * K ^ 2) ^ k * Real.exp (k : ℝ) := by
                gcongr
            _ = (|s| * 64 * K ^ 2 * Real.exp 1) ^ k := by
                rw [hexp, ← mul_pow]
            _ = r ^ k := by ring
  have hsplit := hseries.summable.sum_add_tsum_nat_add 2
  have hhead : ∑ i ∈ Finset.range 2, (∫ ω, term i ω ∂μ) = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have h0 : ∫ ω, term 0 ω ∂μ = 1 := by
      simp [term, integral_const, Measure.real_def, IsProbabilityMeasure.measure_univ,
        ENNReal.toReal_one]
    have h1 : ∫ ω, term 1 ω ∂μ = 0 := by
      simp [term, integral_const_mul, hZmean]
    simp [h0, h1]
  have htail : |∑' k, ∫ ω, term (k + 2) ω ∂μ| ≤ 2 * r ^ 2 := by
    have hpoint : ∀ k, ‖∫ ω, term (k + 2) ω ∂μ‖ ≤ r ^ 2 * r ^ k := by
      intro k
      have hk2 : 0 < k + 2 := by omega
      have hmk := hmoment (k + 2) hk2
      rw [show r ^ (k + 2) = r ^ 2 * r ^ k by rw [pow_add]; ring] at hmk
      simpa [Real.norm_eq_abs] using hmk
    have hhas := (hasSum_geometric_of_lt_one hr0 hrlt).mul_left (r ^ 2)
    have hbound := tsum_of_norm_bounded hhas hpoint
    have hdiv : r ^ 2 * (1 - r)⁻¹ ≤ 2 * r ^ 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by linarith : 0 < 1 - r)]
      nlinarith [hr1]
    calc
      |∑' k, ∫ ω, term (k + 2) ω ∂μ| = ‖∑' k, ∫ ω, term (k + 2) ω ∂μ‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ r ^ 2 * (1 - r)⁻¹ := hbound
      _ ≤ 2 * r ^ 2 := hdiv
  refine ⟨hint, ?_⟩
  have hr2 : 2 * r ^ 2 = 8192 * (Real.exp 1) ^ 2 * K ^ 4 * s ^ 2 := by
    unfold r
    have hassoc : |s| * 64 * Real.exp 1 * K ^ 2 =
        |s| * (64 * Real.exp 1 * K ^ 2) := by ring
    have hfac : (|s| * (64 * Real.exp 1 * K ^ 2)) ^ 2 =
        s ^ 2 * (64 * Real.exp 1 * K ^ 2) ^ 2 := by
      rw [mul_pow, sq_abs]
    rw [hassoc, hfac]
    ring
  calc
    ∫ ω, Real.exp (s * Z ω) ∂μ = ∑' k, ∫ ω, term k ω ∂μ := hseries.tsum_eq.symm
    _ = (∑ i ∈ Finset.range 2, ∫ ω, term i ω ∂μ) + ∑' k, ∫ ω, term (k + 2) ω ∂μ :=
      hsplit.symm
    _ = 1 + ∑' k, ∫ ω, term (k + 2) ω ∂μ := by rw [hhead]
    _ ≤ 1 + |∑' k, ∫ ω, term (k + 2) ω ∂μ| := by gcongr; exact le_abs_self _
    _ ≤ 1 + 2 * r ^ 2 := by gcongr
    _ ≤ Real.exp (2 * r ^ 2) := by rw [add_comm]; exact Real.add_one_le_exp _
    _ = Real.exp (8192 * (Real.exp 1) ^ 2 * K ^ 4 * s ^ 2) := by rw [hr2]

/-- Each matrix entry is bounded by the Euclidean operator norm. -/
lemma abs_entry_le_realMatrixOperatorNorm (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    |A i j| ≤ realMatrixOperatorNorm A := by
  rw [realMatrixOperatorNorm_eq, Matrix.cstar_norm_def]
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)
  let ei : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
  let ej : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j 1
  have hei : ‖ei‖ = 1 := by simp [ei, EuclideanSpace.single, PiLp.norm_single]
  have hej : ‖ej‖ = 1 := by simp [ej, EuclideanSpace.single, PiLp.norm_single]
  have hxi : (ei : Fin n → ℝ) = Pi.single i 1 := by
    simp [ei, EuclideanSpace.single, PiLp.ofLp_single]
  have hyj : (ej : Fin n → ℝ) = Pi.single j 1 := by
    simp [ej, EuclideanSpace.single, PiLp.ofLp_single]
  have hdot : ⟪ei, T A ej⟫ = A i j := by
    rw [Matrix.inner_toEuclideanCLM, hxi, hyj, Matrix.mulVec_single_one, single_one_dotProduct]
    simp [Matrix.col_apply]
  calc
    |A i j| = |⟪ei, T A ej⟫| := by rw [hdot]
    _ ≤ ‖ei‖ * ‖T A ej‖ := abs_real_inner_le_norm ei _
    _ ≤ ‖ei‖ * (‖T A‖ * ‖ej‖) := by
      gcongr
      exact (T A).le_opNorm ej
    _ = ‖T A‖ := by rw [hei, hej]; ring

/-- The operator norm vanishes exactly on the zero matrix. -/
lemma realMatrixOperatorNorm_eq_zero_iff (A : Matrix (Fin n) (Fin n) ℝ) :
    realMatrixOperatorNorm A = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have habs : |A i j| ≤ 0 :=
      (abs_entry_le_realMatrixOperatorNorm A i j).trans_eq h
    exact abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))
  · intro h
    have hF : realMatrixFrobeniusSq A = 0 :=
      (realMatrixFrobeniusSq_eq_zero_iff A).mpr h
    exact realMatrixOperatorNorm_eq_zero_of_frobenius hF

/-- A quadratic exponential moment on a bounded scale gives a one-sided tail. -/
lemma measure_ge_of_quad_mgf [IsProbabilityMeasure μ] {Y : Ω → ℝ} {Q cap t : ℝ}
    (hQ : 0 < Q) (hcap : 0 < cap) (ht : 0 < t)
    (hmgf : ∀ s : ℝ, 0 ≤ s → s ≤ cap →
      Integrable (fun ω ↦ Real.exp (s * Y ω)) μ ∧
        ∫ ω, Real.exp (s * Y ω) ∂μ ≤ Real.exp (Q * s ^ 2)) :
    μ {ω | t ≤ Y ω} ≤
      ENNReal.ofReal (Real.exp (-min (t ^ 2 / (4 * Q)) (t * cap / 2))) := by
  let s := min (t / (2 * Q)) cap
  have hs0 : 0 ≤ s := le_min (by positivity) (by positivity)
  have hscap : s ≤ cap := min_le_right _ _
  have hsQ : s ≤ t / (2 * Q) := min_le_left _ _
  obtain ⟨hint, hmoment⟩ := hmgf s hs0 hscap
  have hchernoff := measure_ge_le_exp_mul_mgf (X := Y) (t := s) (μ := μ) t hs0 hint
  have hmgf_le : mgf Y μ s ≤ Real.exp (Q * s ^ 2) := hmoment
  have hexp : -s * t + Q * s ^ 2 ≤ -min (t ^ 2 / (4 * Q)) (t * cap / 2) := by
    rcases le_total (t / (2 * Q)) cap with hle | hge
    · have hseq : s = t / (2 * Q) := min_eq_left hle
      have hminle : t ^ 2 / (4 * Q) ≤ t * cap / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hcross : t ≤ cap * (2 * Q) := by rwa [div_le_iff₀ (by positivity)] at hle
        nlinarith
      have hgoal : (-s) * t + Q * s ^ 2 = -(t ^ 2 / (4 * Q)) := by
        rw [hseq]
        field_simp
        ring
      rw [min_eq_left hminle, hgoal]
    · have hseq : s = cap := min_eq_right hge
      have hquad : Q * s ^ 2 ≤ s * t / 2 := by
        have hstep : s * s ≤ (t / (2 * Q)) * s :=
          mul_le_mul_of_nonneg_right hsQ hs0
        calc
          Q * s ^ 2 = Q * (s * s) := by rw [pow_two]
          _ ≤ Q * ((t / (2 * Q)) * s) :=
            mul_le_mul_of_nonneg_left hstep hQ.le
          _ = s * t / 2 := by field_simp
      have hhalf : (-s) * t + Q * s ^ 2 ≤ -(t * cap / 2) := by
        rw [hseq]
        have hq : Q * cap ^ 2 ≤ cap * t / 2 := by simpa [hseq] using hquad
        have hlin : (-cap) * t + Q * cap ^ 2 ≤ (-cap) * t + cap * t / 2 := by
          linarith
        have hsum : (-cap) * t + cap * t / 2 = -(t * cap / 2) := by ring
        linarith
      have hminle : t * cap / 2 ≤ t ^ 2 / (4 * Q) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hcross : cap * (2 * Q) ≤ t := by rwa [le_div_iff₀ (by positivity)] at hge
        nlinarith
      exact hhalf.trans (by rw [min_eq_right hminle])
  have hreal : μ.real {ω | t ≤ Y ω} ≤
      Real.exp (-min (t ^ 2 / (4 * Q)) (t * cap / 2)) := by
    calc
      μ.real {ω | t ≤ Y ω} ≤ Real.exp (-s * t) * mgf Y μ s := hchernoff
      _ ≤ Real.exp (-s * t) * Real.exp (Q * s ^ 2) := by
        gcongr
      _ = Real.exp (-s * t + Q * s ^ 2) := by rw [← Real.exp_add]
      _ ≤ Real.exp (-min (t ^ 2 / (4 * Q)) (t * cap / 2)) :=
        Real.exp_le_exp.mpr hexp
  have hμ : μ {ω | t ≤ Y ω} = ENNReal.ofReal (μ.real {ω | t ≤ Y ω}) := by
    rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact hμ.trans_le (ENNReal.ofReal_le_ofReal hreal)

/-- Diagonal energy controls the joint exponential moment of the centered squares. -/
lemma integral_exp_diag_le [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ) {K : ℝ}
    (hpsi : ∀ i, HasPsiTwoBound (X i) μ (2 * K)) (A : Matrix (Fin n) (Fin n) ℝ) {s : ℝ}
    (hs : |s| * realMatrixOperatorNorm A ≤ 1 / (128 * Real.exp 1 * K ^ 2)) :
    Integrable (fun ω ↦ Real.exp (s *
      ∑ i, A i i * (X i ω ^ 2 - ∫ η, X i η ^ 2 ∂μ))) μ ∧
      ∫ ω, Real.exp (s * ∑ i, A i i * (X i ω ^ 2 - ∫ η, X i η ^ 2 ∂μ)) ∂μ ≤
        Real.exp (8192 * (Real.exp 1) ^ 2 * K ^ 4 *
          (∑ i, (A i i) ^ 2) * s ^ 2) := by
  let σ : Fin n → ℝ := fun i ↦ ∫ η, X i η ^ 2 ∂μ
  let Y : Fin n → Ω → ℝ := fun i ω ↦ A i i * (X i ω ^ 2 - σ i)
  have hYfun : (fun ω ↦ ∑ i, Y i ω) =
      fun ω ↦ ∑ i, A i i * (X i ω ^ 2 - ∫ η, X i η ^ 2 ∂μ) := by
    ext ω; simp [Y, σ]
  have hg : ∀ i, Measurable (fun x : ℝ ↦ A i i * (x ^ 2 - σ i)) := fun i ↦
    ((measurable_id.pow_const 2).sub_const (σ i)).const_mul (A i i)
  have hYindep : iIndepFun Y μ := by
    simpa [Y, Function.comp_def] using hindep.comp (fun i x ↦ A i i * (x ^ 2 - σ i)) hg
  have hYmeas : ∀ i, Measurable (Y i) := fun i ↦
    ((hmeas i).pow_const 2).sub_const (σ i) |>.const_mul (A i i)
  have hcoeff : ∀ i, |s * A i i| ≤ 1 / (128 * Real.exp 1 * K ^ 2) := by
    intro i
    calc
      |s * A i i| = |s| * |A i i| := abs_mul _ _
      _ ≤ |s| * realMatrixOperatorNorm A := by
        gcongr
        exact abs_diag_le_realMatrixOperatorNorm A i
      _ ≤ 1 / (128 * Real.exp 1 * K ^ 2) := hs
  have hone : ∀ i, Integrable (fun ω ↦ Real.exp (s * Y i ω)) μ ∧
      ∫ ω, Real.exp (s * Y i ω) ∂μ ≤
        Real.exp (8192 * (Real.exp 1) ^ 2 * K ^ 4 * (s * A i i) ^ 2) := by
    intro i
    have hrewrite : (fun ω ↦ Real.exp (s * Y i ω)) =
        fun ω ↦ Real.exp ((s * A i i) * (X i ω ^ 2 - ∫ η, X i η ^ 2 ∂μ)) := by
      ext ω
      simp [Y, σ, ← mul_assoc]
    rw [hrewrite]
    simpa [σ] using mgf_centered_sq_le (hmeas i) (hpsi i) (hcoeff i)
  have hint : Integrable (fun ω ↦ Real.exp (s * ∑ i, Y i ω)) μ := by
    simpa [Finset.sum_apply] using
      hYindep.integrable_exp_mul_sum hYmeas (t := s) (s := Finset.univ)
        (fun i _ ↦ (hone i).1)
  have hprod : ∫ ω, Real.exp (s * ∑ i, Y i ω) ∂μ ≤
      Real.exp (8192 * (Real.exp 1) ^ 2 * K ^ 4 * (∑ i, (A i i) ^ 2) * s ^ 2) := by
    have hmgfEq := hYindep.mgf_sum hYmeas Finset.univ (t := s)
    have hstep : ∏ i, mgf (Y i) μ s ≤
        ∏ i, Real.exp (8192 * (Real.exp 1) ^ 2 * K ^ 4 * (s * A i i) ^ 2) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact mgf_nonneg
      · intro i hi
        simpa [mgf] using (hone i).2
    calc
      ∫ ω, Real.exp (s * ∑ i, Y i ω) ∂μ = mgf (∑ i, Y i) μ s := by
        simp [mgf, Finset.sum_apply]
      _ = ∏ i, mgf (Y i) μ s := by simpa [Finset.sum_apply] using hmgfEq
      _ ≤ ∏ i, Real.exp (8192 * (Real.exp 1) ^ 2 * K ^ 4 * (s * A i i) ^ 2) := hstep
      _ = Real.exp (∑ i, 8192 * (Real.exp 1) ^ 2 * K ^ 4 * (s * A i i) ^ 2) := by
        rw [← Real.exp_sum]
      _ = Real.exp (8192 * (Real.exp 1) ^ 2 * K ^ 4 * (∑ i, (A i i) ^ 2) * s ^ 2) := by
        congr 1
        simp_rw [mul_pow]
        calc
          ∑ i, 8192 * (Real.exp 1) ^ 2 * K ^ 4 * (s ^ 2 * (A i i) ^ 2)
              = ∑ i, (8192 * (Real.exp 1) ^ 2 * K ^ 4 * s ^ 2) * (A i i) ^ 2 := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            ring
          _ = (8192 * (Real.exp 1) ^ 2 * K ^ 4 * s ^ 2) * ∑ i, (A i i) ^ 2 := by
            rw [← Finset.mul_sum]
          _ = 8192 * (Real.exp 1) ^ 2 * K ^ 4 * (∑ i, (A i i) ^ 2) * s ^ 2 := by ring
  refine ⟨?_, ?_⟩
  · simpa [Y, σ] using hint
  · simpa [Y, σ] using hprod

/-- The diagonal Bernstein rate is at least the scaled Hanson–Wright rate. -/
lemma diag_rate_ge {K t E F op : ℝ} (hK : 0 < K) (ht : 0 < t) (hE : 0 < E) (hEF : E ≤ F)
    (hop : 0 < op) :
    (1 / (32768 * (Real.exp 1) ^ 2)) *
        min (t ^ 2 / (K ^ 4 * F)) (t / (K ^ 2 * op)) ≤
      min (t ^ 2 / (32768 * (Real.exp 1) ^ 2 * K ^ 4 * E))
        (t / (256 * Real.exp 1 * K ^ 2 * op)) := by
  set c : ℝ := 1 / (32768 * (Real.exp 1) ^ 2)
  have hc : 0 < c := by positivity
  have h1 : c * (t ^ 2 / (K ^ 4 * F)) ≤
      t ^ 2 / (32768 * (Real.exp 1) ^ 2 * K ^ 4 * E) := by
    have hden : K ^ 4 * E ≤ K ^ 4 * F := mul_le_mul_of_nonneg_left hEF (by positivity)
    have hfrac : t ^ 2 / (K ^ 4 * F) ≤ t ^ 2 / (K ^ 4 * E) :=
      div_le_div_of_nonneg_left (sq_nonneg t) (by positivity) hden
    have hmul := mul_le_mul_of_nonneg_left hfrac hc.le
    refine hmul.trans_eq ?_
    simp only [c]
    field_simp
  have h2 : c * (t / (K ^ 2 * op)) ≤ t / (256 * Real.exp 1 * K ^ 2 * op) := by
    have hcoef : c ≤ 1 / (256 * Real.exp 1) := by
      simp only [c]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcoef
      (by positivity : 0 ≤ t / (K ^ 2 * op))
    refine hmul.trans_eq ?_
    field_simp
  have hmin : c * min (t ^ 2 / (K ^ 4 * F)) (t / (K ^ 2 * op)) =
      min (c * (t ^ 2 / (K ^ 4 * F))) (c * (t / (K ^ 2 * op))) := by
    rcases le_total (t ^ 2 / (K ^ 4 * F)) (t / (K ^ 2 * op)) with hab | hba
    · rw [min_eq_left hab, min_eq_left (mul_le_mul_of_nonneg_left hab hc.le)]
    · rw [min_eq_right hba, min_eq_right (mul_le_mul_of_nonneg_left hba hc.le)]
  rw [hmin]
  exact min_le_min h1 h2

/-- Centered diagonal contribution of a sampled quadratic form. -/
lemma diagonalDeviation_tail [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ i, HasPsiTwoBound (X i) μ (2 * K)) (A : Matrix (Fin n) (Fin n) ℝ) {t : ℝ}
    (ht : 0 < t) :
    μ {ω | t < |∑ i, A i i * (X i ω ^ 2 - ∫ η, X i η ^ 2 ∂μ)|} ≤
      ENNReal.ofReal (2 * Real.exp (-(1 / (32768 * (Real.exp 1) ^ 2)) *
        min (t ^ 2 / (K ^ 4 * realMatrixFrobeniusSq A))
          (t / (K ^ 2 * realMatrixOperatorNorm A)))) := by
  by_cases hE0 : ∑ i, (A i i) ^ 2 = 0
  · have hzero : ∀ i, A i i = 0 := by
      intro i
      have hsq : (A i i) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg _)).1 hE0 i
          (Finset.mem_univ i)
      exact sq_eq_zero_iff.mp hsq
    have hempty :
        {ω | t < |∑ i, A i i * (X i ω ^ 2 - ∫ η, X i η ^ 2 ∂μ)|} = ∅ := by
      ext ω
      simp [hzero, abs_zero, not_lt.mpr ht.le]
    simp [hempty]
  · have hE : 0 < ∑ i, (A i i) ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (Ne.symm hE0)
    have hop : 0 < realMatrixOperatorNorm A := by
      by_contra hnonpos
      have hnorm : realMatrixOperatorNorm A = 0 :=
        le_antisymm (le_of_not_gt hnonpos) (realMatrixOperatorNorm_nonneg A)
      have hentry : ∀ i, A i i = 0 := by
        intro i
        exact abs_eq_zero.mp <| le_antisymm
          ((abs_diag_le_realMatrixOperatorNorm A i).trans_eq hnorm) (abs_nonneg _)
      exact hE0 (by simp [hentry])
    let D : Ω → ℝ := fun ω ↦ ∑ i, A i i * (X i ω ^ 2 - ∫ η, X i η ^ 2 ∂μ)
    let E : ℝ := ∑ i, (A i i) ^ 2
    let Q : ℝ := 8192 * (Real.exp 1) ^ 2 * K ^ 4 * E
    let cap : ℝ := 1 / (128 * Real.exp 1 * K ^ 2 * realMatrixOperatorNorm A)
    have hQ : 0 < Q := by
      dsimp [Q, E]
      positivity
    have hcap : 0 < cap := by
      dsimp [cap]
      positivity
    have hscale : ∀ s : ℝ, |s| ≤ cap →
        |s| * realMatrixOperatorNorm A ≤ 1 / (128 * Real.exp 1 * K ^ 2) := by
      intro s hs
      have hop' : 0 < realMatrixOperatorNorm A := hop
      calc
        |s| * realMatrixOperatorNorm A ≤ cap * realMatrixOperatorNorm A := by
          gcongr
        _ = 1 / (128 * Real.exp 1 * K ^ 2) := by
          dsimp [cap]
          field_simp
    have hDmgf : ∀ s : ℝ, 0 ≤ s → s ≤ cap →
        Integrable (fun ω ↦ Real.exp (s * D ω)) μ ∧
          ∫ ω, Real.exp (s * D ω) ∂μ ≤ Real.exp (Q * s ^ 2) := by
      intro s hs0 hscap
      have hbound := integral_exp_diag_le X hmeas hindep hpsi A
        (hscale s (by simpa [abs_of_nonneg hs0] using hscap))
      exact ⟨hbound.1, hbound.2⟩
    have hneg : ∀ s : ℝ, 0 ≤ s → s ≤ cap →
        Integrable (fun ω ↦ Real.exp (s * (-D) ω)) μ ∧
          ∫ ω, Real.exp (s * (-D) ω) ∂μ ≤ Real.exp (Q * s ^ 2) := by
      intro s hs0 hscap
      have hbound := integral_exp_diag_le X hmeas hindep hpsi A
        (s := -s) (by simpa [abs_neg] using hscale s (by rwa [abs_of_nonneg hs0]))
      have hfun : (fun ω ↦ Real.exp ((-s) * D ω)) = fun ω ↦ Real.exp (s * (-D) ω) := by
        ext ω
        simp only [Pi.neg_apply, neg_mul, mul_neg]
      rw [← hfun]
      refine ⟨hbound.1, hbound.2.trans_eq ?_⟩
      congr 1
      simp [Q, E]
    have hup := measure_ge_of_quad_mgf (Y := D) hQ hcap ht hDmgf
    have hlow := measure_ge_of_quad_mgf (Y := -D) hQ hcap ht hneg
    have hsub : {ω | t < |D ω|} ⊆ {ω | t ≤ D ω} ∪ {ω | t ≤ (-D) ω} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      rcases le_or_gt 0 (D ω) with hpos | hnegD
      · exact Or.inl (by rw [abs_of_nonneg hpos] at hω; exact hω.le)
      · exact Or.inr (by rw [abs_of_neg hnegD] at hω; exact hω.le)
    set c0 : ℝ := 1 / (32768 * (Real.exp 1) ^ 2)
    set φ : ℝ := min (t ^ 2 / (K ^ 4 * realMatrixFrobeniusSq A))
      (t / (K ^ 2 * realMatrixOperatorNorm A))
    have hrate := diag_rate_ge (K := K) (t := t) (E := E) (F := realMatrixFrobeniusSq A)
      (op := realMatrixOperatorNorm A) hK ht hE (sum_diag_sq_le_realMatrixFrobeniusSq A) hop
    have hdecay : Real.exp (-min (t ^ 2 / (4 * Q)) (t * cap / 2)) ≤ Real.exp (-c0 * φ) := by
      apply Real.exp_le_exp.mpr
      have h4Q : t ^ 2 / (4 * Q) = t ^ 2 / (32768 * (Real.exp 1) ^ 2 * K ^ 4 * E) := by
        simp [Q]; field_simp; ring_nf
      have hcap2 : t * cap / 2 =
          t / (256 * Real.exp 1 * K ^ 2 * realMatrixOperatorNorm A) := by
        simp [cap]; field_simp; ring_nf
      have hmin : c0 * φ ≤ min (t ^ 2 / (4 * Q)) (t * cap / 2) := by
        rw [h4Q, hcap2]; simpa [c0, E, φ] using hrate
      linarith
    have hone := hup.trans (ENNReal.ofReal_le_ofReal hdecay)
    have hother := hlow.trans (ENNReal.ofReal_le_ofReal hdecay)
    have hunion := (measure_mono hsub).trans
      ((measure_union_le _ _).trans (add_le_add hone hother))
    have hadd : ENNReal.ofReal (Real.exp (-c0 * φ)) + ENNReal.ofReal (Real.exp (-c0 * φ)) =
        ENNReal.ofReal (2 * Real.exp (-c0 * φ)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    have htwo : μ {ω | t < |D ω|} ≤ ENNReal.ofReal (2 * Real.exp (-c0 * φ)) :=
      hunion.trans_eq hadd
    simpa [D, c0, φ] using htwo

end CKMA
