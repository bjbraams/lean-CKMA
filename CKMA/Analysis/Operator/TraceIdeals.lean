/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Operator.Basic

import TauCeti.Analysis.OperatorIdeal.Family.TraceClass
import TauCeti.Analysis.InnerProductSpace.Parseval
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

/-!
# Schatten products and the Hilbert-space trace

The definitions `CKMA.schattenGauge`, `CKMA.IsTraceClassOperator` and `CKMA.hilbertTrace` are in
`CKMA.Analysis.Operator.Basic`. The product estimate has constant one at conjugate exponents.
Trace-class membership gives absolute convergence of the diagonal series in every Hilbert basis,
independence of the possibly differently indexed basis, and cyclicity `tr (A T) = tr (T A)` for
`T : H →L K` trace class and `A : K →L H` bounded, the two traces taken on `H` and on `K`.
Inner products are linear in the second slot. Sources: GAPS 21.22 and 21.23.

## Main results

* `CKMA.schatten_holder` (**21.22**): Schatten Hölder inequality with constant one.
* `CKMA.isTraceClassOperator_iff_schattenGauge_ne_top`: trace class is finiteness of the
  Schatten-one gauge.
* `CKMA.IsTraceClassOperator.summable_and_enorm_hilbertTrace_le` (**21.23**): absolute
  convergence of the trace series and the trace-norm bound, also available separately as
  `CKMA.IsTraceClassOperator.summable_norm_inner_apply` and
  `CKMA.IsTraceClassOperator.enorm_hilbertTrace_le`.
* `CKMA.hilbertTrace_basis_independent`: basis independence of the Hilbert-space trace.
* `CKMA.IsTraceClassOperator.comp_left`, `CKMA.IsTraceClassOperator.comp_right`: trace class is
  a two-sided ideal.
* `CKMA.IsTraceClassOperator.hilbertTrace_comp_comm`: cyclicity of the trace.

## Auxiliary results

* `CKMA.phaseScalar`: a unit-ball scalar `c` with `c * z = ‖z‖`.
* `CKMA.sum_mul_norm_inner_hilbertBasis_le`, `CKMA.tsum_mul_norm_inner_hilbertBasis_le`:
  Cauchy–Schwarz for the absolute coordinate products in a Hilbert basis.
* `CKMA.inner_eq_zero_of_forall_inner_hilbertBasis_eq_zero`: orthogonality to a Hilbert basis of
  a subspace is orthogonality to the subspace.
-/

public section

noncomputable section

namespace CKMA

open scoped ENNReal InnerProductSpace InnerProduct NNReal

open Filter Topology InnerProductSpace ContinuousLinearMap Module End

variable {𝕜 H K L ι κ : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace 𝕜 L] [CompleteSpace L]

/-- **21.22**: the constant-one Schatten Hölder estimate at finite exponents. -/
theorem schatten_holder {p q r : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hpqr : r⁻¹ = p⁻¹ + q⁻¹) (S : K →L[𝕜] L) (T : H →L[𝕜] K) :
    schattenGauge r hr (S.comp T) ≤ schattenGauge p hp S * schattenGauge q hq T := by
  sorry

/-- The Schatten-one gauge is TauCeti's nuclear gauge. -/
theorem schattenGauge_one_eq_nuclearENorm (T : H →L[𝕜] K) :
    schattenGauge 1 le_rfl T = T.nuclearENorm := by
  simp [schattenGauge, TauCeti.OperatorIdealFamily.schatten_one]

/-- Trace class is finiteness of the Schatten-one gauge. -/
theorem isTraceClassOperator_iff_schattenGauge_ne_top (T : H →L[𝕜] K) :
    IsTraceClassOperator T ↔ schattenGauge 1 le_rfl T ≠ ∞ := by
  rw [isTraceClassOperator_iff, schattenGauge_one_eq_nuclearENorm]

/-- A unit-ball scalar with `phaseScalar z * z = (‖z‖ : 𝕜)`: the conjugate phase of `z`. At
zero the scalar vanishes. -/
def phaseScalar (z : 𝕜) : 𝕜 := (‖z‖ : 𝕜) * z⁻¹

/-- The defining formula of `phaseScalar`. -/
theorem phaseScalar_def (z : 𝕜) : phaseScalar z = (‖z‖ : 𝕜) * z⁻¹ := by
  unfold phaseScalar; rfl

/-- `phaseScalar z` has norm at most one. -/
theorem norm_phaseScalar_le_one (z : 𝕜) : ‖phaseScalar z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [phaseScalar_def, hz, inv_zero]
  · rw [phaseScalar_def, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), norm_inv,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz)]

/-- `phaseScalar z` rotates `z` onto its norm. -/
theorem phaseScalar_mul (z : 𝕜) : phaseScalar z * z = (‖z‖ : 𝕜) := by
  by_cases hz : z = 0
  · simp [phaseScalar_def, hz, inv_zero]
  · rw [phaseScalar_def, mul_assoc, inv_mul_cancel₀ hz, mul_one]

omit [CompleteSpace H] in
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

omit [CompleteSpace H] [CompleteSpace K] in
/-- A finite pairing of two orthonormal families is bounded by the nuclear gauge. -/
private theorem enorm_sum_inner_two_families_le (T : H →L[𝕜] K) {ι : Type*} [Fintype ι]
    (u : ι → K) (v : ι → H) (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    ‖∑ i, ⟪u i, T (v i)⟫_𝕜‖ₑ ≤ T.nuclearENorm := by
  classical
  let W : Submodule 𝕜 K := Submodule.span 𝕜 (Set.range u)
  let V : Submodule 𝕜 H := Submodule.span 𝕜 (Set.range v)
  have : FiniteDimensional 𝕜 W := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range u)
  have : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  have := FiniteDimensional.completeSpace 𝕜 W
  have := FiniteDimensional.completeSpace 𝕜 V
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
  have hnu : C.nuclearENorm ≤ T.nuclearENorm := by
    simp only [nuclearENorm_def]
    exact tsum_le_tsum fun n ↦ ENNReal.coe_le_coe.mpr (hsing n)
  calc ‖∑ i, ⟪u i, T (v i)⟫_𝕜‖ₑ
      = ENNReal.ofReal ‖∑ i, ⟪u i, T (v i)⟫_𝕜‖ := by simp [ofReal_norm]
    _ ≤ ENNReal.ofReal (C.kyFanGauge (Fintype.card ι) : ℝ) :=
        ENNReal.ofReal_le_ofReal hky
    _ = (C.kyFanGauge (Fintype.card ι) : ℝ≥0∞) := by simp
    _ ≤ C.nuclearENorm := C.kyFanGauge_le_nuclearENorm _
    _ ≤ T.nuclearENorm := hnu

omit [CompleteSpace H] in
/-- A finite orthonormal compression has nuclear gauge at most that of the original operator. -/
private theorem enorm_finset_sum_inner_le_nuclearENorm (T : H →L[𝕜] H) {ι : Type*} (v : ι → H)
    (hv : Orthonormal 𝕜 v) (s : Finset ι) :
    ‖∑ i ∈ s, ⟪v i, T (v i)⟫_𝕜‖ₑ ≤ T.nuclearENorm := by
  classical
  let u : s → H := fun i ↦ v i
  have hu : Orthonormal 𝕜 u := hv.comp (fun i : s ↦ (i : ι)) Subtype.val_injective
  rw [← Finset.sum_coe_sort s (fun i : ι ↦ ⟪v i, T (v i)⟫_𝕜)]
  simpa [u] using enorm_sum_inner_two_families_le T u u hu hu

omit [CompleteSpace H] in
/-- Finite sums of absolute diagonal entries are bounded by the nuclear gauge. -/
private theorem sum_norm_inner_diag_le (T : H →L[𝕜] H) (hT : T.nuclearENorm ≠ ∞)
    (b : HilbertBasis ι 𝕜 H) (s : Finset ι) :
    ∑ i ∈ s, ‖⟪b i, T (b i)⟫_𝕜‖ ≤ T.nuclearENorm.toReal := by
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
  have hnu : (T.comp U).nuclearENorm ≤ T.nuclearENorm := by
    simp only [nuclearENorm_def]
    exact tsum_le_tsum fun n ↦ ENNReal.coe_le_coe.mpr
      ((T.singularValue_comp_le_right U n).trans (mul_le_of_le_one_right' hUnn))
  have hbig : ENNReal.ofReal (∑ i ∈ s, ‖⟪b i, T (b i)⟫_𝕜‖) ≤ T.nuclearENorm := by
    rw [← hreal, ofReal_norm, ← hdiag]
    exact (enorm_finset_sum_inner_le_nuclearENorm (T.comp U) b b.orthonormal s).trans hnu
  exact (ENNReal.ofReal_le_iff_le_toReal hT).mp hbig

omit [CompleteSpace H] in
/-- The diagonal entries of a trace-class operator in a Hilbert basis are absolutely
summable. -/
theorem IsTraceClassOperator.summable_norm_inner_apply {T : H →L[𝕜] H}
    (hT : IsTraceClassOperator T) (b : HilbertBasis ι 𝕜 H) :
    Summable (fun i ↦ ‖⟪b i, T (b i)⟫_𝕜‖) :=
  summable_of_sum_le (fun _ ↦ norm_nonneg _) fun s ↦
    sum_norm_inner_diag_le T hT.nuclearENorm_ne_top b s

/-- The trace of a trace-class operator in any Hilbert basis is bounded by its trace norm. -/
theorem IsTraceClassOperator.enorm_hilbertTrace_le {T : H →L[𝕜] H}
    (hT : IsTraceClassOperator T) (b : HilbertBasis ι 𝕜 H) :
    ‖hilbertTrace b T‖ₑ ≤ schattenGauge 1 le_rfl T := by
  rw [schattenGauge_one_eq_nuclearENorm, hilbertTrace_def]
  refine le_of_tendsto' ((continuous_eNorm.tendsto _).comp
    (Summable.of_norm (hT.summable_norm_inner_apply b)).hasSum) fun s ↦ ?_
  simpa using enorm_finset_sum_inner_le_nuclearENorm T b b.orthonormal s

/-- **21.23**: absolute convergence and the trace-norm bound for every Hilbert basis. -/
theorem IsTraceClassOperator.summable_and_enorm_hilbertTrace_le {T : H →L[𝕜] H}
    (hT : IsTraceClassOperator T) (b : HilbertBasis ι 𝕜 H) :
    Summable (fun i ↦ ‖⟪b i, T (b i)⟫_𝕜‖) ∧
      ‖hilbertTrace b T‖ₑ ≤ schattenGauge 1 le_rfl T :=
  ⟨hT.summable_norm_inner_apply b, hT.enorm_hilbertTrace_le b⟩

omit [CompleteSpace H] in
/-- A vector orthogonal to a Hilbert basis of a subspace is orthogonal to the subspace. -/
theorem inner_eq_zero_of_forall_inner_hilbertBasis_eq_zero {K : Submodule 𝕜 H} {ι : Type*}
    (bK : HilbertBasis ι 𝕜 K) {x : H} (hx : ∀ i, ⟪x, (bK i : H)⟫_𝕜 = 0) {y : H} (hy : y ∈ K) :
    ⟪x, y⟫_𝕜 = 0 := by
  have hsum := ((innerSL 𝕜 x).comp K.subtypeL).hasSum (bK.hasSum_repr ⟨y, hy⟩)
  have hzero : HasSum (fun _ : ι ↦ (0 : 𝕜)) ⟪x, y⟫_𝕜 := by
    simpa only [ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL, Submodule.subtype_apply,
      innerSL_apply_apply, map_smul, hx, smul_zero] using hsum
  exact hzero.unique hasSum_zero

/-- A trace-class operator `T : H →L K` has a Hilbert basis of `H` of eigenvectors of
`T† ∘ T`. -/
private theorem exists_gramEigenbasis (T : H →L[𝕜] K) (hT : T.nuclearENorm ≠ ∞) :
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
    exact (isCompactOperator_of_nuclearENorm_ne_top hT).clm_comp (T†)
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
    exact fun y hy ↦
      inner_eq_zero_of_forall_inner_hilbertBasis_eq_zero (bw mu) (fun i ↦ hx' ⟨mu, i⟩) hy
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

omit [CompleteSpace H] in
/-- Cauchy–Schwarz for the coordinatewise absolute products in a Hilbert basis. -/
theorem sum_mul_norm_inner_hilbertBasis_le (b : HilbertBasis κ 𝕜 H) (x y : H) (t : Finset κ) :
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

omit [CompleteSpace H] in
/-- The series of absolute coordinate products is at most the product of the norms. -/
theorem tsum_mul_norm_inner_hilbertBasis_le (b : HilbertBasis κ 𝕜 H) (x y : H) :
    ∑' j, ‖⟪b j, x⟫_𝕜‖ * ‖⟪b j, y⟫_𝕜‖ ≤ ‖x‖ * ‖y‖ :=
  Real.tsum_le_of_sum_le (fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (sum_mul_norm_inner_hilbertBasis_le b x y)

omit [CompleteSpace H] [CompleteSpace K] in
/-- If the images `T eᵢ` of a Hilbert basis are pairwise orthogonal, `∑ ‖T eᵢ‖` converges and is
at most the nuclear gauge. -/
private theorem summable_norm_apply_gram (T : H →L[𝕜] K) (hT : T.nuclearENorm ≠ ∞)
    {s : Set H} (e : HilbertBasis s 𝕜 H)
    (horth : ∀ i j, i ≠ j → ⟪T (e i), T (e j)⟫_𝕜 = 0) :
    Summable (fun i ↦ ‖T (e i)‖) ∧ ∑' i, ‖T (e i)‖ ≤ T.nuclearENorm.toReal := by
  classical
  have hfin (t0 : Finset s) : ∑ i ∈ t0, ‖T (e i)‖ ≤ T.nuclearENorm.toReal := by
    let t : Finset s := t0.filter fun i ↦ T (e i) ≠ 0
    have hsplit : ∑ i ∈ t0, ‖T (e i)‖ = ∑ i ∈ t, ‖T (e i)‖ := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ t0) fun i hi hnot ↦ ?_
      have hzero : T (e i) = 0 := by
        by_contra hnz
        exact hnot (Finset.mem_filter.mpr ⟨hi, hnz⟩)
      simp [hzero]
    rw [hsplit]
    have hne (i : t) : ‖T (e i)‖ ≠ 0 := norm_ne_zero_iff.mpr (Finset.mem_filter.mp i.2).2
    let u : t → K := fun i ↦ (‖T (e i)‖ : 𝕜)⁻¹ • T (e i)
    let v : t → H := fun i ↦ e i
    have hv : Orthonormal 𝕜 v :=
      e.orthonormal.comp (fun i : t ↦ (i : s)) Subtype.val_injective
    have hu : Orthonormal 𝕜 u := by
      refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
      · simp only [u]
        rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
          inv_mul_cancel₀ (hne i)]
      · have hval : (i : s) ≠ j := fun h ↦ hij (Subtype.ext h)
        simp only [u, inner_smul_left, inner_smul_right, horth _ _ hval, mul_zero]
    have hdiag (i : t) : ⟪u i, T (v i)⟫_𝕜 = (‖T (e i)‖ : 𝕜) := by
      simp only [u, v, inner_smul_left, inner_self_eq_norm_sq_to_K]
      rw [show starRingEnd 𝕜 ((‖T (e i)‖ : 𝕜)⁻¹) = (‖T (e i)‖ : 𝕜)⁻¹ by
        rw [← RCLike.ofReal_inv, RCLike.conj_ofReal, RCLike.ofReal_inv]]
      rw [← RCLike.ofReal_inv, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul]
      congr 1
      rw [pow_two, ← mul_assoc, inv_mul_cancel₀ (hne i), one_mul]
    have hreal : ‖∑ i : t, (‖T (e i)‖ : 𝕜)‖ = ∑ i ∈ t, ‖T (e i)‖ := by
      rw [Finset.sum_coe_sort t (fun i : s ↦ (‖T (e i)‖ : 𝕜)), ← map_sum (algebraMap ℝ 𝕜),
        RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
    have hbig : ENNReal.ofReal (∑ i ∈ t, ‖T (e i)‖) ≤ T.nuclearENorm := by
      have hfam := enorm_sum_inner_two_families_le T u v hu hv
      rw [show ∑ i, ⟪u i, T (v i)⟫_𝕜 = ∑ i : t, (‖T (e i)‖ : 𝕜) from
        Finset.sum_congr rfl fun i _ ↦ hdiag i] at hfam
      rw [← ofReal_norm, hreal] at hfam
      exact hfam
    exact (ENNReal.ofReal_le_iff_le_toReal hT).mp hbig
  exact ⟨summable_of_sum_le (fun _ ↦ norm_nonneg _) hfin,
    Real.tsum_le_of_sum_le (fun _ ↦ norm_nonneg _) hfin⟩

/-- A trace-class `T : H →L K` has a Hilbert basis `e` of `H` with `∑ ‖T eᵢ‖ < ∞`. -/
private theorem exists_hilbertBasis_summable_norm_apply (T : H →L[𝕜] K)
    (hT : T.nuclearENorm ≠ ∞) :
    ∃ (s : Set H) (e : HilbertBasis s 𝕜 H), Summable fun i ↦ ‖T (e i)‖ := by
  obtain ⟨s, e, hE⟩ := exists_gramEigenbasis T hT
  refine ⟨s, e, (summable_norm_apply_gram T hT e fun i j hij ↦ ?_).1⟩
  rw [← adjoint_inner_left T (e j) (T (e i)), ← ContinuousLinearMap.comp_apply, hE i,
    inner_smul_left, e.orthonormal.inner_eq_zero hij, mul_zero]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Scalar coefficients of `T` applied to a Hilbert expansion. -/
private theorem hasSum_inner_expand (T : H →L[𝕜] K) {s : Type*} (e : HilbertBasis s 𝕜 H)
    (x : K) (y : H) : HasSum (fun i ↦ ⟪e i, y⟫_𝕜 * ⟪x, T (e i)⟫_𝕜) ⟪x, T y⟫_𝕜 := by
  convert (innerSL 𝕜 x).hasSum (T.hasSum (e.hasSum_repr y)) using 1
  · ext i
    simp [e.repr_apply_apply, innerSL_apply_apply, map_smul]
  · simp [innerSL_apply_apply]

/-- If `∑ ‖T eᵢ‖` converges for a Hilbert basis `e` of `H` and `A : K →L H` is bounded, the
trace of `T ∘ A` in any Hilbert basis of `K` is `∑ ⟪eᵢ, A (T eᵢ)⟫`. With `A = id` this is the
trace of `T` itself. -/
private theorem hilbertTrace_comp_eq_tsum (T : H →L[𝕜] K) {s : Type*}
    (e : HilbertBasis s 𝕜 H) (hsum : Summable fun i ↦ ‖T (e i)‖) (A : K →L[𝕜] H)
    (c : HilbertBasis κ 𝕜 K) :
    hilbertTrace c (T.comp A) = ∑' i, ⟪e i, A (T (e i))⟫_𝕜 := by
  let g : s → κ → 𝕜 := fun i j ↦ ⟪e i, A (c j)⟫_𝕜 * ⟪c j, T (e i)⟫_𝕜
  have hgj (i : s) (j : κ) : g i j = ⟪(A†) (e i), c j⟫_𝕜 * ⟪c j, T (e i)⟫_𝕜 := by
    simp only [g, adjoint_inner_left]
  have hgabs (i : s) (j : κ) : ‖g i j‖ = ‖⟪c j, (A†) (e i)⟫_𝕜‖ * ‖⟪c j, T (e i)⟫_𝕜‖ := by
    rw [hgj, norm_mul, norm_inner_symm]
  have hAe (i : s) : ‖(A†) (e i)‖ * ‖T (e i)‖ ≤ ‖A‖ * ‖T (e i)‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine ((A†).le_opNorm _).trans ?_
    rw [(adjoint (E := K) (F := H)).norm_map A, e.orthonormal.norm_eq_one, mul_one]
  have hfin (i : s) (t : Finset κ) : ∑ j ∈ t, ‖g i j‖ ≤ ‖A‖ * ‖T (e i)‖ := by
    simp_rw [hgabs]
    exact (sum_mul_norm_inner_hilbertBasis_le c _ _ t).trans (hAe i)
  have hpair : Summable fun p : s × κ ↦ ‖g p.1 p.2‖ := by
    rw [summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)]
    refine ⟨fun i ↦ summable_of_sum_le (fun _ ↦ norm_nonneg _) (hfin i), ?_⟩
    exact Summable.of_nonneg_of_le (fun i ↦ tsum_nonneg fun _ ↦ norm_nonneg _)
      (fun i ↦ Real.tsum_le_of_sum_le (fun _ ↦ norm_nonneg _) (hfin i)) (hsum.mul_left ‖A‖)
  have hunc : Summable (Function.uncurry g) :=
    Summable.of_norm (by simpa [Function.uncurry] using hpair)
  have hpoint (j : κ) : ⟪c j, (T.comp A) (c j)⟫_𝕜 = ∑' i, g i j := by
    rw [comp_apply]
    simpa [g] using (hasSum_inner_expand T e (c j) (A (c j))).tsum_eq.symm
  have hcol (i : s) : ∑' j, g i j = ⟪e i, A (T (e i))⟫_𝕜 := by
    simp_rw [hgj]
    exact (c.hasSum_inner_mul_inner ((A†) (e i)) (T (e i))).tsum_eq.trans
      (adjoint_inner_left A (T (e i)) (e i))
  rw [hilbertTrace_def, tsum_congr hpoint, hunc.tsum_comm]
  simp_rw [hcol]

/-- The trace is independent of the possibly differently indexed Hilbert basis. -/
theorem hilbertTrace_basis_independent {T : H →L[𝕜] H} (hT : IsTraceClassOperator T)
    (b : HilbertBasis ι 𝕜 H) (c : HilbertBasis κ 𝕜 H) : hilbertTrace b T = hilbertTrace c T := by
  obtain ⟨s, e, hsum⟩ := exists_hilbertBasis_summable_norm_apply T hT.nuclearENorm_ne_top
  have hb := hilbertTrace_comp_eq_tsum T e hsum (ContinuousLinearMap.id 𝕜 H) b
  have hc := hilbertTrace_comp_eq_tsum T e hsum (ContinuousLinearMap.id 𝕜 H) c
  simp only [comp_id, id_apply] at hb hc
  rw [hb, hc]

omit [CompleteSpace H] [CompleteSpace K] [CompleteSpace L] in
/-- Trace class is a left ideal: `A ∘ T` is trace class for bounded `A`. -/
theorem IsTraceClassOperator.comp_left {T : H →L[𝕜] K} (hT : IsTraceClassOperator T)
    (A : K →L[𝕜] L) : IsTraceClassOperator (A.comp T) := by
  have h := nuclearENorm_comp_comp_le A T (ContinuousLinearMap.id 𝕜 H)
  rw [comp_id] at h
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp [eNorm_eq_nnNorm])
    hT.nuclearENorm_ne_top) (by simp [eNorm_eq_nnNorm])) h

omit [CompleteSpace H] [CompleteSpace K] [CompleteSpace L] in
/-- Trace class is a right ideal: `T ∘ B` is trace class for bounded `B`. -/
theorem IsTraceClassOperator.comp_right {T : H →L[𝕜] K} (hT : IsTraceClassOperator T)
    (B : L →L[𝕜] H) : IsTraceClassOperator (T.comp B) := by
  have h := nuclearENorm_comp_comp_le (ContinuousLinearMap.id 𝕜 K) T B
  rw [id_comp] at h
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp [eNorm_eq_nnNorm])
    hT.nuclearENorm_ne_top) (by simp [eNorm_eq_nnNorm])) h

/-- Cyclicity of the trace: for trace-class `T : H →L K` and bounded `A : K →L H`, the trace of
`A ∘ T` on `H` equals the trace of `T ∘ A` on `K`, in any Hilbert bases of the two spaces. -/
theorem IsTraceClassOperator.hilbertTrace_comp_comm {T : H →L[𝕜] K}
    (hT : IsTraceClassOperator T) (A : K →L[𝕜] H) (b : HilbertBasis ι 𝕜 H)
    (c : HilbertBasis κ 𝕜 K) : hilbertTrace b (A.comp T) = hilbertTrace c (T.comp A) := by
  obtain ⟨s, e, hsum⟩ := exists_hilbertBasis_summable_norm_apply T hT.nuclearENorm_ne_top
  have hsumA : Summable fun i ↦ ‖(A.comp T) (e i)‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun i ↦ A.le_opNorm (T (e i)))
      (hsum.mul_left ‖A‖)
  have hleft := hilbertTrace_comp_eq_tsum (A.comp T) e hsumA (ContinuousLinearMap.id 𝕜 H) b
  simp only [comp_id, id_apply] at hleft
  rw [hleft, hilbertTrace_comp_eq_tsum T e hsum A c]
  rfl

end CKMA
