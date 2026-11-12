/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family.Schatten
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFan
public import TauCeti.Analysis.Normed.Operator.Compact.FiniteRank
public import TauCeti.Analysis.InnerProductSpace.Parseval
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Schatten products and the Hilbert-space trace

Schatten gauges reuse TauCeti's operator-ideal family, with finite Banach exponents at least one.
The product estimate has constant one at conjugate exponents. Trace class is finiteness of the
Schatten-one gauge.

A supplied Hilbert basis defines the scalar trace sum. Trace-class membership gives absolute
convergence, independence of the possibly differently indexed basis, and cyclicity under bounded
multiplication. Inner products are linear in the second slot. Sources: GAPS 21.22 and 21.23.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped ENNReal InnerProductSpace InnerProduct NNReal

open Filter Topology InnerProductSpace ContinuousLinearMap Module End

variable {𝕜 H K L ι κ : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace 𝕜 L] [CompleteSpace L]

/-- The upstream Schatten gauge. No second approximation-number definition is introduced. -/
abbrev schattenGauge (p : ℝ) (hp : 1 ≤ p) (T : H →L[𝕜] K) : ℝ≥0∞ :=
  (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge T

/-- **21.22**: the constant-one Schatten Hölder estimate at finite exponents. -/
theorem schatten_holder {p q r : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hpqr : r⁻¹ = p⁻¹ + q⁻¹) (S : K →L[𝕜] L) (T : H →L[𝕜] K) :
    schattenGauge r hr (S.comp T) ≤ schattenGauge p hp S * schattenGauge q hq T := by
  sorry

/-- Trace-class membership through the actual upstream extended Schatten-one gauge. -/
def IsTraceClassOperator (T : H →L[𝕜] K) : Prop := schattenGauge 1 le_rfl T ≠ ∞

/-- Trace computed in a supplied Hilbert basis, using Mathlib's second-variable-linear inner
product convention. The trace-class theorems establish that this sum is legitimate. -/
def hilbertTrace (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] H) : 𝕜 :=
  ∑' i, ⟪b i, T (b i)⟫_𝕜

omit [CompleteSpace H] in
/-- The trace of the zero operator is zero. -/
theorem hilbertTrace_zero (b : HilbertBasis ι 𝕜 H) : hilbertTrace b (0 : H →L[𝕜] H) = 0 := by
  simp [hilbertTrace]

/-- Sum of the approximation numbers, the nuclear gauge. -/
private abbrev nuclearGauge (T : H →L[𝕜] K) : ℝ≥0∞ :=
  ∑' n, (T.singularValue n : ℝ≥0∞)

/-- The Schatten-one gauge is the nuclear gauge. -/
private theorem schattenGauge_one_eq_nuclearGauge (T : H →L[𝕜] K) :
    schattenGauge 1 le_rfl T = nuclearGauge T := by
  simp [schattenGauge, nuclearGauge, TauCeti.OperatorIdealFamily.gauge_schatten,
    ENNReal.rpow_one]

/-- Each Ky Fan prefix is at most the nuclear gauge. -/
private theorem kyFanGauge_le_nuclearGauge (T : H →L[𝕜] K) (k : ℕ) :
    (T.kyFanGauge k : ℝ≥0∞) ≤ nuclearGauge T := by
  rw [nuclearGauge, ContinuousLinearMap.kyFanGauge_def, ENNReal.ofNNReal_finsetSum]
  exact ENNReal.sum_le_tsum (Finset.range k)

/-- Postcomposition does not increase the nuclear gauge beyond the operator enorm. -/
private theorem nuclearGauge_comp_left_le (A : K →L[𝕜] L) (T : H →L[𝕜] K) :
    nuclearGauge (A.comp T) ≤ ‖A‖ₑ * nuclearGauge T := by
  have hpoint (n : ℕ) :
      ((A.comp T).singularValue n : ℝ≥0∞) ≤ ‖A‖ₑ * (T.singularValue n : ℝ≥0∞) := by
    rw [enorm_eq_nnnorm]
    exact_mod_cast A.singularValue_comp_le_left T n
  calc nuclearGauge (A.comp T)
      ≤ ∑' n, ‖A‖ₑ * (T.singularValue n : ℝ≥0∞) := ENNReal.tsum_le_tsum hpoint
    _ = ‖A‖ₑ * nuclearGauge T := by simp [nuclearGauge, ENNReal.tsum_mul_left]

/-- Precomposition does not increase the nuclear gauge beyond the operator enorm. -/
private theorem nuclearGauge_comp_right_le (T : K →L[𝕜] L) (B : H →L[𝕜] K) :
    nuclearGauge (T.comp B) ≤ nuclearGauge T * ‖B‖ₑ := by
  have hpoint (n : ℕ) :
      ((T.comp B).singularValue n : ℝ≥0∞) ≤ (T.singularValue n : ℝ≥0∞) * ‖B‖ₑ := by
    rw [enorm_eq_nnnorm]
    exact_mod_cast T.singularValue_comp_le_right B n
  calc nuclearGauge (T.comp B)
      ≤ ∑' n, (T.singularValue n : ℝ≥0∞) * ‖B‖ₑ := ENNReal.tsum_le_tsum hpoint
    _ = nuclearGauge T * ‖B‖ₑ := by simp [nuclearGauge, ENNReal.tsum_mul_right]

/-- Unit-ball scalar with `phaseScalar z * z = (‖z‖ : 𝕜)`. At zero the scalar vanishes. -/
private def phaseScalar (z : 𝕜) : 𝕜 := (‖z‖ : 𝕜) * z⁻¹

/-- `phaseScalar z` has norm at most one. -/
private theorem norm_phaseScalar_le_one (z : 𝕜) : ‖phaseScalar z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [phaseScalar, hz, inv_zero]
  · rw [phaseScalar, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), norm_inv,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz)]

/-- `phaseScalar z` rotates `z` onto its norm. -/
private theorem phaseScalar_mul (z : 𝕜) : phaseScalar z * z = (‖z‖ : 𝕜) := by
  by_cases hz : z = 0
  · simp [phaseScalar, hz, inv_zero]
  · rw [phaseScalar, mul_assoc, inv_mul_cancel₀ hz, mul_one]

/-- Phased rank-one sum along a finite orthonormal set has operator norm at most one. -/
private theorem opNorm_sum_phase_rankOne_le {ι : Type*} (b : HilbertBasis ι 𝕜 H) (c : ι → 𝕜)
    (s : Finset ι) (hc : ∀ i ∈ s, ‖c i‖ ≤ 1) :
    ‖∑ i ∈ s, c i • rankOne 𝕜 (b i) (b i)‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun x ↦ ?_
  let alpha : ι → 𝕜 := fun i ↦ c i * ⟪b i, x⟫_𝕜
  have happly : (∑ i ∈ s, c i • rankOne 𝕜 (b i) (b i)) x = ∑ i ∈ s, alpha i • b i := by
    simp [alpha, rankOne_apply, mul_smul]
  have hsq : ‖(∑ i ∈ s, c i • rankOne 𝕜 (b i) (b i)) x‖ ^ 2 = ∑ i ∈ s, ‖alpha i‖ ^ 2 := by
    rw [happly, norm_sq_eq_re_inner (𝕜 := 𝕜), b.orthonormal.inner_sum alpha alpha s]
    simp [RCLike.conj_mul, map_sum]
  have hle : ‖(∑ i ∈ s, c i • rankOne 𝕜 (b i) (b i)) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hsq]
    refine le_trans ?_ (b.orthonormal.sum_inner_products_le (s := s) x)
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have hmul : ‖c i‖ * ‖⟪b i, x⟫_𝕜‖ ≤ ‖⟪b i, x⟫_𝕜‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (hc i hi)
    calc ‖alpha i‖ ^ 2
        = (‖c i‖ * ‖⟪b i, x⟫_𝕜‖) ^ 2 := by simp only [alpha, norm_mul]
      _ ≤ ‖⟪b i, x⟫_𝕜‖ ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hmul 2
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg x)] using sq_le_sq.mp hle

/-- A finite pairing of two orthonormal families is bounded by the nuclear gauge. -/
private theorem enorm_sum_inner_two_families_le (T : H →L[𝕜] H) {ι : Type*} [Fintype ι]
    (u v : ι → H) (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    ‖∑ i, ⟪u i, T (v i)⟫_𝕜‖ₑ ≤ nuclearGauge T := by
  classical
  let W : Submodule 𝕜 H := Submodule.span 𝕜 (Set.range u)
  let V : Submodule 𝕜 H := Submodule.span 𝕜 (Set.range v)
  haveI : FiniteDimensional 𝕜 W := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range u)
  haveI : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  haveI := FiniteDimensional.complete 𝕜 W
  haveI := FiniteDimensional.complete 𝕜 V
  let uW : ι → W := fun i ↦ ⟨u i, Submodule.subset_span ⟨i, rfl⟩⟩
  let vV : ι → V := fun i ↦ ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩
  have huW : Orthonormal 𝕜 uW := by
    refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
    · simpa [uW] using hu.norm_eq_one i
    · simpa [uW, Submodule.coe_inner] using hu.inner_eq_zero hij
  have hvV : Orthonormal 𝕜 vV := by
    refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
    · simpa [vV] using hv.norm_eq_one i
    · simpa [vV, Submodule.coe_inner] using hv.inner_eq_zero hij
  let C : V →L[𝕜] W := W.orthogonalProjectionOnto ∘L T ∘L V.subtypeL
  have hterm (i : ι) : ⟪uW i, C (vV i)⟫_𝕜 = ⟪u i, T (v i)⟫_𝕜 := by
    simp only [C, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  have hky : ‖∑ i, ⟪u i, T (v i)⟫_𝕜‖ ≤ (C.kyFanGauge (Fintype.card ι) : ℝ) := by
    rw [C.kyFanGauge_eq_kyFanSum]
    have hcongr : ∑ i, ⟪uW i, (C : V →ₗ[𝕜] W) (vV i)⟫_𝕜 = ∑ i, ⟪u i, T (v i)⟫_𝕜 := by
      refine Fintype.sum_congr _ _ fun i ↦ hterm i
    rw [← hcongr]
    exact LinearMap.norm_sum_inner_le_kyFanSum (C : V →ₗ[𝕜] W) huW hvV
  have hP : ‖W.orthogonalProjectionOnto‖₊ ≤ 1 := by
    exact_mod_cast W.orthogonalProjectionOnto_norm_le
  have hι : ‖V.subtypeL‖₊ ≤ 1 := by
    exact_mod_cast V.norm_subtypeL_le
  have hsing (n : ℕ) : C.singularValue n ≤ T.singularValue n := by
    refine le_trans
      (ContinuousLinearMap.singularValue_comp_comp_le
        W.orthogonalProjectionOnto T V.subtypeL n) ?_
    calc ‖W.orthogonalProjectionOnto‖₊ * T.singularValue n * ‖V.subtypeL‖₊
        ≤ 1 * T.singularValue n * 1 := by gcongr
      _ = T.singularValue n := by simp
  have hnu : nuclearGauge C ≤ nuclearGauge T :=
    ENNReal.tsum_le_tsum fun n ↦ by exact_mod_cast hsing n
  calc ‖∑ i, ⟪u i, T (v i)⟫_𝕜‖ₑ
      = ENNReal.ofReal ‖∑ i, ⟪u i, T (v i)⟫_𝕜‖ := by simp [ofReal_norm]
    _ ≤ ENNReal.ofReal (C.kyFanGauge (Fintype.card ι) : ℝ) :=
        ENNReal.ofReal_le_ofReal hky
    _ = (C.kyFanGauge (Fintype.card ι) : ℝ≥0∞) := by simp
    _ ≤ nuclearGauge C := kyFanGauge_le_nuclearGauge C _
    _ ≤ nuclearGauge T := hnu

/-- A finite orthonormal compression has nuclear gauge at most that of the original operator. -/
private theorem enorm_finset_sum_inner_le_nuclearGauge (T : H →L[𝕜] H) {ι : Type*} (v : ι → H)
    (hv : Orthonormal 𝕜 v) (s : Finset ι) :
    ‖∑ i ∈ s, ⟪v i, T (v i)⟫_𝕜‖ₑ ≤ nuclearGauge T := by
  classical
  let u : s → H := fun i ↦ v i
  have hu : Orthonormal 𝕜 u := hv.comp (fun i : s ↦ (i : ι)) Subtype.val_injective
  rw [← Finset.sum_coe_sort s (fun i : ι ↦ ⟪v i, T (v i)⟫_𝕜)]
  simpa [u] using enorm_sum_inner_two_families_le T u u hu hu

/-- Finite sums of absolute diagonal entries are bounded by the nuclear gauge. -/
private theorem sum_norm_inner_diag_le (T : H →L[𝕜] H) (hT : nuclearGauge T ≠ ∞)
    (b : HilbertBasis ι 𝕜 H) (s : Finset ι) :
    ∑ i ∈ s, ‖⟪b i, T (b i)⟫_𝕜‖ ≤ (nuclearGauge T).toReal := by
  let c : ι → 𝕜 := fun i ↦ phaseScalar ⟪b i, T (b i)⟫_𝕜
  let U : H →L[𝕜] H := ∑ i ∈ s, c i • rankOne 𝕜 (b i) (b i)
  have hU : ‖U‖ ≤ 1 := opNorm_sum_phase_rankOne_le b c s fun _ _ ↦ norm_phaseScalar_le_one _
  have hUb (i : ι) (hi : i ∈ s) : U (b i) = c i • b i := by
    classical
    have hon := orthonormal_iff_ite.mp b.orthonormal
    simp only [U, sum_apply, smul_apply, rankOne_apply, hon, smul_smul]
    simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul]
    rw [Finset.sum_ite_eq']
    simp [hi, c]
  have hdiag : ∑ i ∈ s, ⟪b i, (T.comp U) (b i)⟫_𝕜 = ∑ i ∈ s, (‖⟪b i, T (b i)⟫_𝕜‖ : 𝕜) := by
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [comp_apply, hUb i hi, map_smul, inner_smul_right]
    simp only [c]
    exact phaseScalar_mul _
  have hreal : ‖∑ i ∈ s, (‖⟪b i, T (b i)⟫_𝕜‖ : 𝕜)‖ = ∑ i ∈ s, ‖⟪b i, T (b i)⟫_𝕜‖ := by
    rw [← map_sum (algebraMap ℝ 𝕜), RCLike.norm_ofReal,
      abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
  have hUnn : ‖U‖₊ ≤ 1 := by exact_mod_cast hU
  have hnu : nuclearGauge (T.comp U) ≤ nuclearGauge T := by
    refine ENNReal.tsum_le_tsum fun n ↦ ?_
    have hle : (T.comp U).singularValue n ≤ T.singularValue n :=
      (T.singularValue_comp_le_right U n).trans (mul_le_of_le_one_right' hUnn)
    exact_mod_cast hle
  have hbig : ENNReal.ofReal (∑ i ∈ s, ‖⟪b i, T (b i)⟫_𝕜‖) ≤ nuclearGauge T := by
    rw [← hreal, ofReal_norm, ← hdiag]
    exact (enorm_finset_sum_inner_le_nuclearGauge (T.comp U) b b.orthonormal s).trans hnu
  exact (ENNReal.ofReal_le_iff_le_toReal hT).mp hbig

/-- **21.23**: absolute convergence and the trace-norm bound for every Hilbert basis. -/
theorem IsTraceClassOperator.summable_trace {T : H →L[𝕜] H} (hT : IsTraceClassOperator T)
    (b : HilbertBasis ι 𝕜 H) :
    Summable (fun i ↦ ‖⟪b i, T (b i)⟫_𝕜‖) ∧
      ‖hilbertTrace b T‖ₑ ≤ schattenGauge 1 le_rfl T := by
  have hnu : nuclearGauge T ≠ ∞ := by
    rw [← schattenGauge_one_eq_nuclearGauge]
    exact hT
  have hsum : Summable fun i ↦ ‖⟪b i, T (b i)⟫_𝕜‖ :=
    summable_of_sum_le (fun _ ↦ norm_nonneg _) fun s ↦ sum_norm_inner_diag_le T hnu b s
  refine ⟨hsum, ?_⟩
  rw [schattenGauge_one_eq_nuclearGauge, hilbertTrace]
  refine le_of_tendsto'
    ((continuous_enorm.tendsto _).comp (Summable.of_norm hsum).hasSum) fun s ↦ ?_
  simpa using enorm_finset_sum_inner_le_nuclearGauge T b b.orthonormal s

/-- Approximation numbers tend to zero exactly for operator-norm limits of rank-controlled maps. -/
private theorem tendsto_singularValue_nhds_zero_iff {T : H →L[𝕜] K} :
    Tendsto T.singularValue atTop (𝓝 0) ↔
      ∃ R : ℕ → H →L[𝕜] K, (∀ n, (R n).rank ≤ n) ∧ Tendsto R atTop (𝓝 T) := by
  constructor
  · intro h
    choose R hR hRT using fun n : ℕ ↦ ContinuousLinearMap.exists_rank_le_nnnorm_sub_lt
      (lt_add_of_pos_right (T.singularValue n) (by positivity : (0 : ℝ≥0) < 1 / ((n : ℝ≥0) + 1)))
    have hlim : Tendsto (fun n : ℕ ↦ T.singularValue n + 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 0) := by
      simpa using h.add tendsto_one_div_add_atTop_nhds_zero_nat
    refine ⟨R, hR, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) (NNReal.tendsto_coe.mpr hlim)
    rw [norm_sub_rev]
    exact_mod_cast (hRT n).le
  · rintro ⟨R, hR, hRT⟩
    have hnorm : Tendsto (fun n ↦ ‖T - R n‖₊) atTop (𝓝 0) := by
      rw [← NNReal.tendsto_coe]
      simpa [norm_sub_rev] using tendsto_iff_norm_sub_tendsto_zero.mp hRT
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hnorm (fun _ ↦ zero_le)
      fun n ↦ T.singularValue_le_nnnorm_sub (hR n)

/-- Finite nuclear gauge implies compactness. -/
private theorem isCompactOperator_of_nuclearGauge_ne_top {T : H →L[𝕜] K}
    (hT : nuclearGauge T ≠ ∞) : IsCompactOperator T := by
  haveI : ProperSpace 𝕜 := FiniteDimensional.proper_rclike ℝ 𝕜
  have hlim : Tendsto T.singularValue atTop (𝓝 0) :=
    ENNReal.tendsto_coe.mp (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hT)
  obtain ⟨R, hR, hRT⟩ := tendsto_singularValue_nhds_zero_iff.mp hlim
  refine isCompactOperator_of_tendsto hRT (.of_forall fun n ↦ ?_)
  have : Module.Finite 𝕜 (LinearMap.range (R n : H →ₗ[𝕜] K)) :=
    Module.rank_lt_aleph0_iff.mp ((hR n).trans_lt Cardinal.natCast_lt_aleph0)
  exact LinearMap.HasFiniteRange.isCompactOperator (Module.Finite.iff_fg.mp this)

/-- A vector orthogonal to a Hilbert basis of a subspace is orthogonal to the subspace. -/
private theorem hilbertBasis_inner_eq_zero {K : Submodule 𝕜 H} {ι : Type*}
    (bK : HilbertBasis ι 𝕜 K) {x : H} (hx : ∀ i, ⟪x, (bK i : H)⟫_𝕜 = 0) {y : H} (hy : y ∈ K) :
    ⟪x, y⟫_𝕜 = 0 := by
  have hsum := ((innerSL 𝕜 x).comp K.subtypeL).hasSum (bK.hasSum_repr ⟨y, hy⟩)
  have hzero : HasSum (fun _ : ι ↦ (0 : 𝕜)) ⟪x, y⟫_𝕜 := by
    simpa only [ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL, Submodule.subtype_apply,
      innerSL_apply_apply, map_smul, hx, smul_zero] using hsum
  exact hzero.unique hasSum_zero

/-- A trace-class operator has a Hilbert basis of eigenvectors of `T† ∘ T`. -/
private theorem exists_gramEigenbasis (T : H →L[𝕜] H) (hT : nuclearGauge T ≠ ∞) :
    ∃ (s : Set H) (e : HilbertBasis s 𝕜 H),
      (∀ i, (T† ∘L T) (e i) = (‖T (e i)‖ ^ 2 : 𝕜) • e i) := by
  classical
  let S : H →L[𝕜] H := T† ∘L T
  have hsym : (S : H →ₗ[𝕜] H).IsSymmetric := by
    intro x y
    calc ⟪S x, y⟫_𝕜 = ⟪T x, T y⟫_𝕜 := by
          simp only [S]
          rw [comp_apply, adjoint_inner_left]
      _ = ⟪x, S y⟫_𝕜 := by
          simp only [S]
          rw [comp_apply, adjoint_inner_right]
  have hSc : IsCompactOperator S := by
    rw [show (S : H → H) = ⇑(T†) ∘ ⇑T by simp [S, coe_comp]]
    exact (isCompactOperator_of_nuclearGauge_ne_top hT).clm_comp (T†)
  have hspan : (⨆ mu : 𝕜, eigenspace (S : Module.End 𝕜 H) mu)ᗮ = ⊥ :=
    ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hSc hsym
  have hbasis : ∀ mu : 𝕜, ∃ (w : Set (eigenspace (S : Module.End 𝕜 H) mu))
      (b : HilbertBasis w 𝕜 (eigenspace (S : Module.End 𝕜 H) mu)),
      ⇑b = ((↑) : w → eigenspace (S : Module.End 𝕜 H) mu) := by
    intro mu
    have : CompleteSpace (eigenspace (S : Module.End 𝕜 H) mu) :=
      (isClosed_eigenspace S mu).completeSpace_coe
    exact exists_hilbertBasis 𝕜 _
  choose w bw _ using hbasis
  let v : (Σ mu : 𝕜, w mu) → H := fun p ↦
    (eigenspace (S : Module.End 𝕜 H) p.1).subtypeₗᵢ (bw p.1 p.2)
  have hv : Orthonormal 𝕜 v :=
    hsym.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal fun mu ↦ (bw mu).orthonormal
  have hinj : Function.Injective v := hv.linearIndependent.injective
  have hmem (p : Σ mu : 𝕜, w mu) : v p ∈ eigenspace (S : Module.End 𝕜 H) p.1 := (bw p.1 p.2).2
  have hvspan : (Submodule.span 𝕜 (Set.range v))ᗮ = ⊥ := by
    refine le_antisymm ?_ bot_le
    rw [← hspan, ← Submodule.iInf_orthogonal]
    intro x hx
    have hx' : ∀ p, ⟪x, v p⟫_𝕜 = 0 := fun p ↦
      (Submodule.mem_orthogonal' _ x).mp hx _ (Submodule.subset_span ⟨p, rfl⟩)
    simp only [Submodule.mem_iInf]
    intro mu
    rw [Submodule.mem_orthogonal']
    exact fun y hy ↦ hilbertBasis_inner_eq_zero (bw mu) (fun i ↦ hx' ⟨mu, i⟩) hy
  have key : ∀ x : Set.range v, ∃ mu : 𝕜, HasEigenvector (S : Module.End 𝕜 H) mu (x : H) := by
    rintro ⟨-, p, rfl⟩
    refine ⟨p.1, hmem p, fun hzero ↦ ?_⟩
    have hzero' : v p = 0 := hzero
    have hnorm : ‖v p‖ = 1 := hv.1 p
    rw [hzero', norm_zero] at hnorm
    exact zero_ne_one hnorm
  choose nu hnu using key
  refine ⟨Set.range v, HilbertBasis.mkOfOrthogonalEqBot ((orthonormal_subtype_range hinj).2 hv)
    (by rwa [Subtype.range_coe]), ?_⟩
  intro i
  have hvec : S (i : H) = nu i • (i : H) := (hnu i).apply_eq_smul
  have hcoe : (HilbertBasis.mkOfOrthogonalEqBot ((orthonormal_subtype_range hinj).2 hv)
      (by rwa [Subtype.range_coe]) : Set.range v → H) i = (i : H) := by
    simp
  rw [hcoe]
  have hinner : ⟪(i : H), S (i : H)⟫_𝕜 = (‖T (i : H)‖ ^ 2 : 𝕜) := by
    simp only [S]
    rw [comp_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  have hunit : ⟪(i : H), (i : H)⟫_𝕜 = 1 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp [((orthonormal_subtype_range hinj).2 hv).norm_eq_one i]
  rw [hvec, inner_smul_right, hunit, mul_one] at hinner
  rw [hvec, hinner]

/-- Cauchy–Schwarz for the coordinatewise absolute products in a Hilbert basis. -/
private theorem sum_mul_abs_inner_le (b : HilbertBasis κ 𝕜 H) (x y : H) (t : Finset κ) :
    ∑ j ∈ t, ‖⟪b j, x⟫_𝕜‖ * ‖⟪b j, y⟫_𝕜‖ ≤ ‖x‖ * ‖y‖ := by
  have h1 : ∑ j ∈ t, ‖⟪b j, x⟫_𝕜‖ ^ 2 ≤ ∑' j, ‖⟪b j, x⟫_𝕜‖ ^ 2 :=
    (b.summable_norm_sq_inner x).sum_le_tsum t fun _ _ ↦ sq_nonneg _
  have h2 : ∑ j ∈ t, ‖⟪b j, y⟫_𝕜‖ ^ 2 ≤ ∑' j, ‖⟪b j, y⟫_𝕜‖ ^ 2 :=
    (b.summable_norm_sq_inner y).sum_le_tsum t fun _ _ ↦ sq_nonneg _
  calc ∑ j ∈ t, ‖⟪b j, x⟫_𝕜‖ * ‖⟪b j, y⟫_𝕜‖
      ≤ √(∑ j ∈ t, ‖⟪b j, x⟫_𝕜‖ ^ 2) * √(∑ j ∈ t, ‖⟪b j, y⟫_𝕜‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt t (fun j ↦ ‖⟪b j, x⟫_𝕜‖) (fun j ↦ ‖⟪b j, y⟫_𝕜‖)
    _ ≤ √(∑' j, ‖⟪b j, x⟫_𝕜‖ ^ 2) * √(∑' j, ‖⟪b j, y⟫_𝕜‖ ^ 2) := by
        exact mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = ‖x‖ * ‖y‖ := by simp [b.tsum_norm_sq_inner, Real.sqrt_sq (norm_nonneg _)]

/-- The series of absolute coordinate products is at most the product of the norms. -/
private theorem tsum_mul_abs_inner_le (b : HilbertBasis κ 𝕜 H) (x y : H) :
    ∑' j, ‖⟪b j, x⟫_𝕜‖ * ‖⟪b j, y⟫_𝕜‖ ≤ ‖x‖ * ‖y‖ :=
  Real.tsum_le_of_sum_le (fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (sum_mul_abs_inner_le b x y)

/-- On a Gram eigenbasis, `∑ ‖T eᵢ‖` converges and is at most the nuclear gauge. -/
private theorem summable_norm_apply_gram (T : H →L[𝕜] H) (hT : nuclearGauge T ≠ ∞)
    {s : Set H} (e : HilbertBasis s 𝕜 H)
    (hE : ∀ i, (T† ∘L T) (e i) = (‖T (e i)‖ ^ 2 : 𝕜) • e i) :
    Summable (fun i ↦ ‖T (e i)‖) ∧ ∑' i, ‖T (e i)‖ ≤ (nuclearGauge T).toReal := by
  classical
  have horth {i j : s} (hij : i ≠ j) : ⟪T (e i), T (e j)⟫_𝕜 = 0 := by
    rw [← adjoint_inner_left T (e j) (T (e i)), ← ContinuousLinearMap.comp_apply, hE i,
      inner_smul_left, e.orthonormal.inner_eq_zero hij, mul_zero]
  have hfin (t0 : Finset s) : ∑ i ∈ t0, ‖T (e i)‖ ≤ (nuclearGauge T).toReal := by
    let t : Finset s := t0.filter fun i ↦ T (e i) ≠ 0
    have hsplit : ∑ i ∈ t0, ‖T (e i)‖ = ∑ i ∈ t, ‖T (e i)‖ := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ t0) fun i hi hnot ↦ ?_
      have hzero : T (e i) = 0 := by
        by_contra hnz
        exact hnot (Finset.mem_filter.mpr ⟨hi, hnz⟩)
      simp [hzero]
    rw [hsplit]
    let u : t → H := fun i ↦ (‖T (e i)‖ : 𝕜)⁻¹ • T (e i)
    let v : t → H := fun i ↦ e i
    have hv : Orthonormal 𝕜 v :=
      e.orthonormal.comp (fun i : t ↦ (i : s)) Subtype.val_injective
    have hu : Orthonormal 𝕜 u := by
      refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
      · have hne : ‖T (e i)‖ ≠ 0 := by
          have hi := i.2
          rw [Finset.mem_filter] at hi
          exact norm_ne_zero_iff.mpr hi.2
        simp only [u]
        rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
          inv_mul_cancel₀ hne]
      · have hval : (i : s) ≠ j := fun h ↦ hij (Subtype.ext h)
        simp only [u, inner_smul_left, inner_smul_right, horth hval, mul_zero]
    have hdiag (i : t) : ⟪u i, T (v i)⟫_𝕜 = (‖T (e i)‖ : 𝕜) := by
      have hne : ‖T (e i)‖ ≠ 0 := by
        have hi := i.2
        rw [Finset.mem_filter] at hi
        exact norm_ne_zero_iff.mpr hi.2
      simp only [u, v, inner_smul_left, inner_self_eq_norm_sq_to_K]
      rw [show starRingEnd 𝕜 ((‖T (e i)‖ : 𝕜)⁻¹) = (‖T (e i)‖ : 𝕜)⁻¹ by
        rw [← RCLike.ofReal_inv, RCLike.conj_ofReal, RCLike.ofReal_inv]]
      rw [← RCLike.ofReal_inv, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul]
      congr 1
      rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    have hreal : ‖∑ i : t, (‖T (e i)‖ : 𝕜)‖ = ∑ i ∈ t, ‖T (e i)‖ := by
      rw [Finset.sum_coe_sort t (fun i : s ↦ (‖T (e i)‖ : 𝕜)), ← map_sum (algebraMap ℝ 𝕜),
        RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
    have hbig : ENNReal.ofReal (∑ i ∈ t, ‖T (e i)‖) ≤ nuclearGauge T := by
      have hfam := enorm_sum_inner_two_families_le T u v hu hv
      rw [show ∑ i, ⟪u i, T (v i)⟫_𝕜 = ∑ i : t, (‖T (e i)‖ : 𝕜) from
        Finset.sum_congr rfl fun i _ ↦ hdiag i] at hfam
      rw [← ofReal_norm, hreal] at hfam
      exact hfam
    exact (ENNReal.ofReal_le_iff_le_toReal hT).mp hbig
  exact ⟨summable_of_sum_le (fun _ ↦ norm_nonneg _) hfin,
    Real.tsum_le_of_sum_le (fun _ ↦ norm_nonneg _) hfin⟩

/-- Scalar coefficients of `T` applied to a Hilbert expansion. -/
private theorem hasSum_inner_expand (T : H →L[𝕜] H) {s : Type*} (e : HilbertBasis s 𝕜 H)
    (x y : H) : HasSum (fun i ↦ ⟪e i, y⟫_𝕜 * ⟪x, T (e i)⟫_𝕜) ⟪x, T y⟫_𝕜 := by
  convert (innerSL 𝕜 x).hasSum (T.hasSum (e.hasSum_repr y)) using 1
  · ext i
    simp [e.repr_apply_apply, innerSL_apply_apply, map_smul]
  · simp [innerSL_apply_apply]

/-- If `∑ ‖T eᵢ‖` converges, every Hilbert trace equals `∑ ⟪eᵢ, T eᵢ⟫`. -/
private theorem hilbertTrace_eq_sum_inner_apply (T : H →L[𝕜] H) {s : Type*}
    (e : HilbertBasis s 𝕜 H) (hsum : Summable fun i ↦ ‖T (e i)‖) (b : HilbertBasis κ 𝕜 H) :
    hilbertTrace b T = ∑' i, ⟪e i, T (e i)⟫_𝕜 := by
  let f : s → κ → 𝕜 := fun i j ↦ ⟪e i, b j⟫_𝕜 * ⟪b j, T (e i)⟫_𝕜
  have hpoint (j : κ) : ⟪b j, T (b j)⟫_𝕜 = ∑' i, f i j :=
    (hasSum_inner_expand T e (b j) (b j)).tsum_eq.symm
  have habs (i : s) (j : κ) : ‖f i j‖ = ‖⟪b j, e i⟫_𝕜‖ * ‖⟪b j, T (e i)⟫_𝕜‖ := by
    simp only [f, norm_mul, norm_inner_symm]
  have hrow (i : s) : ∑' j, ‖f i j‖ ≤ ‖T (e i)‖ := by
    calc ∑' j, ‖f i j‖
        = ∑' j, ‖⟪b j, e i⟫_𝕜‖ * ‖⟪b j, T (e i)⟫_𝕜‖ := by simp_rw [habs]
      _ ≤ ‖e i‖ * ‖T (e i)‖ := tsum_mul_abs_inner_le b (e i) (T (e i))
      _ = ‖T (e i)‖ := by rw [e.orthonormal.norm_eq_one, one_mul]
  have hpair : Summable fun p : s × κ ↦ ‖f p.1 p.2‖ := by
    rw [summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)]
    refine ⟨fun i ↦ ?_, ?_⟩
    · refine summable_of_sum_le (c := ‖T (e i)‖) (fun _ ↦ norm_nonneg _) fun t ↦ ?_
      calc ∑ j ∈ t, ‖f i j‖
          = ∑ j ∈ t, ‖⟪b j, e i⟫_𝕜‖ * ‖⟪b j, T (e i)⟫_𝕜‖ := by simp_rw [habs]
        _ ≤ ‖e i‖ * ‖T (e i)‖ := sum_mul_abs_inner_le b (e i) (T (e i)) t
        _ = ‖T (e i)‖ := by rw [e.orthonormal.norm_eq_one, one_mul]
    · exact Summable.of_nonneg_of_le (fun i ↦ tsum_nonneg fun _ ↦ norm_nonneg _) hrow hsum
  have hunc : Summable (Function.uncurry f) :=
    Summable.of_norm (by simpa [Function.uncurry] using hpair)
  have hcol (i : s) : ∑' j, f i j = ⟪e i, T (e i)⟫_𝕜 := by
    simpa [f] using (b.hasSum_inner_mul_inner (e i) (T (e i))).tsum_eq
  rw [hilbertTrace, tsum_congr hpoint, hunc.tsum_comm]
  simp_rw [hcol]

/-- The trace is independent of the possibly differently indexed Hilbert basis. -/
theorem hilbertTrace_basis_independent {T : H →L[𝕜] H} (hT : IsTraceClassOperator T)
    (b : HilbertBasis ι 𝕜 H) (c : HilbertBasis κ 𝕜 H) : hilbertTrace b T = hilbertTrace c T := by
  have hnu : nuclearGauge T ≠ ∞ := by
    rw [← schattenGauge_one_eq_nuclearGauge]
    exact hT
  obtain ⟨s, e, hE⟩ := exists_gramEigenbasis T hnu
  obtain ⟨hsum, -⟩ := summable_norm_apply_gram T hnu e hE
  rw [hilbertTrace_eq_sum_inner_apply T e hsum b, hilbertTrace_eq_sum_inner_apply T e hsum c]

/-- Bounded multiplication preserves trace class, and the trace is cyclic. -/
theorem IsTraceClassOperator.trace_cyclic {T : H →L[𝕜] H} (hT : IsTraceClassOperator T)
    (A : H →L[𝕜] H) (b : HilbertBasis ι 𝕜 H) :
    IsTraceClassOperator (A.comp T) ∧ IsTraceClassOperator (T.comp A) ∧
      hilbertTrace b (A.comp T) = hilbertTrace b (T.comp A) := by
  have hnu : nuclearGauge T ≠ ∞ := by
    rw [← schattenGauge_one_eq_nuclearGauge]
    exact hT
  have hA : ‖A‖ₑ ≠ ∞ := by simp [enorm_eq_nnnorm]
  have hAT : IsTraceClassOperator (A.comp T) := by
    rw [IsTraceClassOperator, schattenGauge_one_eq_nuclearGauge]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hA hnu) (nuclearGauge_comp_left_le A T)
  have hTA : IsTraceClassOperator (T.comp A) := by
    rw [IsTraceClassOperator, schattenGauge_one_eq_nuclearGauge]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hnu hA) (nuclearGauge_comp_right_le T A)
  obtain ⟨s, e, hE⟩ := exists_gramEigenbasis T hnu
  obtain ⟨hsum, -⟩ := summable_norm_apply_gram T hnu e hE
  let f : s → ι → 𝕜 := fun i j ↦ ⟪e i, b j⟫_𝕜 * ⟪b j, A (T (e i))⟫_𝕜
  have habs (i : s) (j : ι) : ‖f i j‖ = ‖⟪b j, e i⟫_𝕜‖ * ‖⟪b j, A (T (e i))⟫_𝕜‖ := by
    simp only [f, norm_mul, norm_inner_symm]
  have hrow (i : s) : ∑' j, ‖f i j‖ ≤ ‖A‖ * ‖T (e i)‖ := by
    calc ∑' j, ‖f i j‖
        = ∑' j, ‖⟪b j, e i⟫_𝕜‖ * ‖⟪b j, A (T (e i))⟫_𝕜‖ := by simp_rw [habs]
      _ ≤ ‖e i‖ * ‖A (T (e i))‖ := tsum_mul_abs_inner_le b (e i) (A (T (e i)))
      _ ≤ ‖A‖ * ‖T (e i)‖ := by
          rw [e.orthonormal.norm_eq_one, one_mul]
          exact A.le_opNorm (T (e i))
  have hpair : Summable fun p : s × ι ↦ ‖f p.1 p.2‖ := by
    rw [summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)]
    refine ⟨fun i ↦ ?_, ?_⟩
    · refine summable_of_sum_le (c := ‖A‖ * ‖T (e i)‖) (fun _ ↦ norm_nonneg _) fun t ↦ ?_
      calc ∑ j ∈ t, ‖f i j‖
          = ∑ j ∈ t, ‖⟪b j, e i⟫_𝕜‖ * ‖⟪b j, A (T (e i))⟫_𝕜‖ := by simp_rw [habs]
        _ ≤ ‖e i‖ * ‖A (T (e i))‖ := sum_mul_abs_inner_le b (e i) (A (T (e i))) t
        _ ≤ ‖A‖ * ‖T (e i)‖ := by
            rw [e.orthonormal.norm_eq_one, one_mul]
            exact A.le_opNorm (T (e i))
    · exact Summable.of_nonneg_of_le (fun i ↦ tsum_nonneg fun _ ↦ norm_nonneg _) hrow
        (hsum.mul_left ‖A‖)
  have hunc : Summable (Function.uncurry f) :=
    Summable.of_norm (by simpa [Function.uncurry] using hpair)
  have hpoint (j : ι) : ⟪b j, (A.comp T) (b j)⟫_𝕜 = ∑' i, f i j := by
    rw [comp_apply]
    have hs := (innerSL 𝕜 (b j)).hasSum (A.hasSum (T.hasSum (e.hasSum_repr (b j))))
    simp only [innerSL_apply_apply] at hs
    rw [← hs.tsum_eq]
    refine tsum_congr fun i ↦ ?_
    simp [f, e.repr_apply_apply, map_smul, inner_smul_right]
  have hcol (i : s) : ∑' j, f i j = ⟪e i, A (T (e i))⟫_𝕜 := by
    simpa [f] using (b.hasSum_inner_mul_inner (e i) (A (T (e i)))).tsum_eq
  have hleft : hilbertTrace b (A.comp T) = ∑' i, ⟪e i, A (T (e i))⟫_𝕜 := by
    rw [hilbertTrace, tsum_congr hpoint, hunc.tsum_comm]
    simp_rw [hcol]
  let g : s → ι → 𝕜 := fun i j ↦ ⟪e i, A (b j)⟫_𝕜 * ⟪b j, T (e i)⟫_𝕜
  have hgabs (i : s) (j : ι) : ‖g i j‖ = ‖⟪b j, (A†) (e i)⟫_𝕜‖ * ‖⟪b j, T (e i)⟫_𝕜‖ := by
    simp only [g]
    rw [← adjoint_inner_left, norm_mul, norm_inner_symm]
  have hAnorm : ‖A†‖ = ‖A‖ := (adjoint (E := H) (F := H)).norm_map A
  have hgrow (i : s) : ∑' j, ‖g i j‖ ≤ ‖A‖ * ‖T (e i)‖ := by
    calc ∑' j, ‖g i j‖
        = ∑' j, ‖⟪b j, (A†) (e i)⟫_𝕜‖ * ‖⟪b j, T (e i)⟫_𝕜‖ := by simp_rw [hgabs]
      _ ≤ ‖(A†) (e i)‖ * ‖T (e i)‖ := tsum_mul_abs_inner_le b ((A†) (e i)) (T (e i))
      _ ≤ ‖A‖ * ‖T (e i)‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact ((A†).le_opNorm _).trans (by rw [hAnorm, e.orthonormal.norm_eq_one, mul_one])
  have hgpair : Summable fun p : s × ι ↦ ‖g p.1 p.2‖ := by
    rw [summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)]
    refine ⟨fun i ↦ ?_, ?_⟩
    · refine summable_of_sum_le (c := ‖A‖ * ‖T (e i)‖) (fun _ ↦ norm_nonneg _) fun t ↦ ?_
      calc ∑ j ∈ t, ‖g i j‖
          = ∑ j ∈ t, ‖⟪b j, (A†) (e i)⟫_𝕜‖ * ‖⟪b j, T (e i)⟫_𝕜‖ := by simp_rw [hgabs]
        _ ≤ ‖(A†) (e i)‖ * ‖T (e i)‖ := sum_mul_abs_inner_le b _ _ t
        _ ≤ ‖A‖ * ‖T (e i)‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            exact ((A†).le_opNorm _).trans
              (by rw [hAnorm, e.orthonormal.norm_eq_one, mul_one])
    · exact Summable.of_nonneg_of_le (fun i ↦ tsum_nonneg fun _ ↦ norm_nonneg _) hgrow
        (hsum.mul_left ‖A‖)
  have hgunc : Summable (Function.uncurry g) :=
    Summable.of_norm (by simpa [Function.uncurry] using hgpair)
  have hgpoint (j : ι) : ⟪b j, (T.comp A) (b j)⟫_𝕜 = ∑' i, g i j := by
    rw [comp_apply]
    simpa [g] using (hasSum_inner_expand T e (b j) (A (b j))).tsum_eq.symm
  have hgcol (i : s) : ∑' j, g i j = ⟪e i, A (T (e i))⟫_𝕜 := by
    have hgj : ∀ j, g i j = ⟪(A†) (e i), b j⟫_𝕜 * ⟪b j, T (e i)⟫_𝕜 := by
      intro j
      simp only [g, adjoint_inner_left]
    simp_rw [hgj]
    exact (b.hasSum_inner_mul_inner ((A†) (e i)) (T (e i))).tsum_eq.trans
      (adjoint_inner_left A (T (e i)) (e i))
  have hright : hilbertTrace b (T.comp A) = ∑' i, ⟪e i, A (T (e i))⟫_𝕜 := by
    rw [hilbertTrace, tsum_congr hgpoint, hgunc.tsum_comm]
    simp_rw [hgcol]
  exact ⟨hAT, hTA, hleft.trans hright.symm⟩

end CKMA
