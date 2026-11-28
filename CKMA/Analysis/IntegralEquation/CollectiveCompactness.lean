/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.RCLike.Basic

import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# Collectively compact approximation

A family of bounded operators `K i` on a normed space is collectively compact when the union of
the images of the closed unit ball has compact closure. If `K n → T` strongly on a Banach space
over `ℝ` or `ℂ`, the sequence is collectively compact and `1 - T` is injective, then `1 - K n`
is eventually invertible with uniformly bounded inverses, and the solutions of
`u n - K n (u n) = f n` converge to the solution of `u₀ - T u₀ = f₀` whenever `f n → f₀`.
Since `T` is compact (a strong limit of a collectively compact sequence), injectivity of `1 - T`
already makes it invertible by the Fredholm alternative. Source: GAPS 25.47.

## Main definitions

* `CKMA.IsCollectivelyCompact`: collective compactness of a family of bounded linear operators.

## Main results

* `CKMA.IsCollectivelyCompact.isCompactOperator`: each member of a collectively compact family is
  compact.
* `CKMA.IsCollectivelyCompact.eventually_isInvertible_one_sub` (**25.47**): eventual
  invertibility of `1 - K n` with uniformly bounded inverses when `1 - T` is injective.
* `CKMA.IsCollectivelyCompact.tendsto_of_sub_apply_eq`: convergence of the approximate solutions.

## References

* R. Kress, *Linear Integral Equations*, 3rd ed., Springer, 2014.
-/

public section

namespace CKMA

open ContinuousLinearEquiv Filter Metric Module End Set Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A family of operators `K i` is collectively compact when the union of the images of the
closed unit ball has compact closure. -/
@[expose]
def IsCollectivelyCompact {ι : Type*} (K : ι → E →L[𝕜] E) : Prop :=
  IsCompact (closure (⋃ i, K i '' Metric.closedBall 0 1))

/-- Defining property of `IsCollectivelyCompact`. -/
theorem isCollectivelyCompact_iff {ι : Type*} {K : ι → E →L[𝕜] E} :
    IsCollectivelyCompact K ↔ IsCompact (closure (⋃ i, K i '' Metric.closedBall 0 1)) :=
  Iff.rfl

/-- Each member of a collectively compact family is a compact operator. -/
theorem IsCollectivelyCompact.isCompactOperator {ι : Type*} {K : ι → E →L[𝕜] E}
    (hc : IsCollectivelyCompact K) (i : ι) : IsCompactOperator (K i) := by
  rw [isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image (⇑(K i))]
  refine ⟨closedBall (0 : E) 1, closedBall_mem_nhds 0 zero_lt_one, ?_⟩
  refine hc.of_isClosed_subset isClosed_closure ?_
  exact closure_mono <| subset_iUnion (fun j ↦ (K j) '' closedBall (0 : E) 1) i

variable [CompleteSpace E]

/-- Strongly convergent operators on a Banach space are uniformly bounded. -/
private theorem exists_norm_le_of_strong_tendsto {K : ℕ → E →L[𝕜] E} {T : E →L[𝕜] E}
    (hconv : ∀ x, Tendsto (fun n ↦ K n x) atTop (𝓝 (T x))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖K n‖ ≤ M := by
  have hpt : ∀ x, ∃ C, ∀ n, ‖K n x‖ ≤ C := by
    intro x
    obtain ⟨r, hr⟩ :=
      (isBounded_range_of_tendsto (fun n ↦ K n x) (hconv x)).subset_closedBall (0 : E)
    refine ⟨r, fun n ↦ ?_⟩
    simpa [mem_closedBall_iff_norm, sub_zero] using hr (mem_range_self n)
  obtain ⟨C, hC⟩ := banach_steinhaus hpt
  exact ⟨max C 0, le_max_right _ _, fun n ↦ (hC n).trans (le_max_left _ _)⟩

omit [CompleteSpace E] in
/-- If `1 - K n` is not eventually bounded below, there are unit vectors `x k` and indices
`n k ≥ k` with `‖(1 - K (n k)) (x k)‖ < 1 / (k + 1)`. -/
private theorem exists_unit_of_not_eventually_norm_ge (K : ℕ → E →L[𝕜] E)
    (H : ¬ ∃ c > 0, ∀ᶠ n in atTop, ∀ x, c * ‖x‖ ≤ ‖(1 - K n) x‖) (k : ℕ) :
    ∃ n : ℕ, ∃ x : E, k ≤ n ∧ ‖x‖ = 1 ∧ ‖(1 - K n) x‖ < (1 : ℝ) / ((k : ℝ) + 1) := by
  have hc : 0 < (1 : ℝ) / ((k : ℝ) + 1) := by positivity
  have hnot : ¬ ∀ᶠ n in atTop, ∀ x, (1 : ℝ) / ((k : ℝ) + 1) * ‖x‖ ≤ ‖(1 - K n) x‖ :=
    fun hall ↦ H ⟨_, hc, hall⟩
  rw [not_eventually] at hnot
  obtain ⟨n, hkn, hn⟩ := frequently_atTop.mp hnot k
  push Not at hn
  obtain ⟨x, hx⟩ := hn
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  refine ⟨n, (‖x‖⁻¹ : 𝕜) • x, hkn, ?_, ?_⟩
  · rw [norm_smul, norm_inv, RCLike.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hpos.ne']
  · rw [ContinuousLinearMap.map_smul, norm_smul, norm_inv, RCLike.norm_of_nonneg (norm_nonneg _)]
    calc
      ‖x‖⁻¹ * ‖(1 - K n) x‖ < ‖x‖⁻¹ * ((1 : ℝ) / ((k : ℝ) + 1) * ‖x‖) :=
        mul_lt_mul_of_pos_left hx (inv_pos.mpr hpos)
      _ = (1 : ℝ) / ((k : ℝ) + 1) := by
        rw [mul_left_comm, inv_mul_cancel₀ hpos.ne', mul_one]

/-- A collectively compact strong approximation of an injective `1 - T` is eventually
bounded below. -/
private theorem exists_eventually_norm_ge (K : ℕ → E →L[𝕜] E) (T : E →L[𝕜] E)
    (hc : IsCollectivelyCompact K) (hconv : ∀ x, Tendsto (fun n ↦ K n x) atTop (𝓝 (T x)))
    (hinj : Function.Injective (⇑(1 - T))) :
    ∃ c > 0, ∀ᶠ n in atTop, ∀ x, c * ‖x‖ ≤ ‖(1 - K n) x‖ := by
  by_contra H
  choose n x hkn hxnorm hxlt using exists_unit_of_not_eventually_norm_ge K H
  obtain ⟨M, -, hM⟩ := exists_norm_le_of_strong_tendsto hconv
  have hmem : ∀ k, K (n k) (x k) ∈ closure (⋃ m, K m '' closedBall (0 : E) 1) := by
    intro k
    refine subset_closure <| mem_iUnion.2 ⟨n k, ?_⟩
    refine ⟨x k, ?_, rfl⟩
    simpa [mem_closedBall_iff_norm, sub_zero] using (hxnorm k).le
  obtain ⟨y, -, φ, hφ, hφlim⟩ := hc.tendsto_subseq hmem
  have hxφ : Tendsto (fun k ↦ x (φ k)) atTop (𝓝 y) := by
    have hres : Tendsto (fun k ↦ (1 - K (n (φ k))) (x (φ k))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ (hxlt (φ k)).le)
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
    have hsum := hres.add hφlim
    refine (tendsto_congr fun k ↦ ?_).mp (by simpa [zero_add] using hsum)
    simp
  have hynorm : ‖y‖ = 1 := by
    have hlim : Tendsto (fun k ↦ ‖x (φ k)‖) atTop (𝓝 ‖y‖) :=
      (continuous_norm.tendsto y).comp hxφ
    exact tendsto_nhds_unique ((tendsto_congr fun k ↦ hxnorm (φ k)).mp hlim) tendsto_const_nhds
  have hnφ : Tendsto (fun k ↦ n (φ k)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    exact ⟨N, fun k hk ↦ hk.trans ((StrictMono.id_le hφ k).trans (hkn (φ k)))⟩
  have hdy : Tendsto (fun k ↦ K (n (φ k)) (x (φ k) - y)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hdist : Tendsto (fun k ↦ ‖x (φ k) - y‖) atTop (𝓝 0) := by
      rw [← tendsto_zero_iff_norm_tendsto_zero]
      simpa [sub_self] using hxφ.sub (tendsto_const_nhds (x := y))
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_)
      (by simpa [mul_zero] using (tendsto_const_nhds (x := M)).mul hdist)
    calc
      ‖K (n (φ k)) (x (φ k) - y)‖
          ≤ ‖K (n (φ k))‖ * ‖x (φ k) - y‖ := by
            exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * ‖x (φ k) - y‖ := by
        exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  have hKy : Tendsto (fun k ↦ K (n (φ k)) y) atTop (𝓝 (T y)) := (hconv y).comp hnφ
  have hy_eq : y = T y := by
    have hTy : Tendsto (fun k ↦ K (n (φ k)) (x (φ k))) atTop (𝓝 (T y)) := by
      have hsum := hdy.add hKy
      refine (tendsto_congr fun k ↦ ?_).mp (by simpa [zero_add] using hsum)
      simp
    exact tendsto_nhds_unique hφlim hTy
  have hyT : (1 - T) y = 0 := by
    simp [sub_apply, one_apply_eq_self, ← hy_eq, sub_self]
  have hy0 : y = 0 := hinj (hyT.trans (ZeroHomClass.map_zero (1 - T)).symm)
  exact one_ne_zero (hynorm.symm.trans (by simp [hy0]))

/-- **25.47**, collectively compact approximation: if `K n → T` strongly, `(K n)` is
collectively compact and `1 - T` is injective, then `1 - K n` is eventually invertible, with
inverses bounded by a common constant. -/
theorem IsCollectivelyCompact.eventually_isInvertible_one_sub {K : ℕ → E →L[𝕜] E}
    (hc : IsCollectivelyCompact K) {T : E →L[𝕜] E}
    (hconv : ∀ x, Tendsto (fun n ↦ K n x) atTop (𝓝 (T x)))
    (hinj : Function.Injective (⇑(1 - T))) :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∃ Sₙ : E ≃L[𝕜] E,
      Sₙ.toContinuousLinearMap = 1 - K n ∧ ‖Sₙ.symm.toContinuousLinearMap‖ ≤ C := by
  obtain ⟨c, hc0, hlower⟩ := exists_eventually_norm_ge K T hc hconv hinj
  refine ⟨c⁻¹, ?_⟩
  filter_upwards [hlower] with n hn
  have hnot : ¬ HasEigenvalue (K n : E →ₗ[𝕜] E) (1 : 𝕜) := by
    intro heig
    obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
    have hv_eq : K n v = v := by
      simpa [ContinuousLinearMap.coe_coe, one_smul] using hv.apply_eq_smul
    have hzero : (1 - K n) v = 0 := by simp [hv_eq, sub_self]
    have := hn v
    rw [hzero, norm_zero] at this
    exact (not_lt_of_ge this) (mul_pos hc0 (norm_pos_iff.mpr hv.2))
  have hres : (1 : 𝕜) ∈ resolventSet 𝕜 (K n) :=
    ((hc.isCompactOperator n).hasEigenvalue_or_mem_resolventSet
      (one_ne_zero : (1 : 𝕜) ≠ 0)).resolve_left hnot
  have hunit : IsUnit (1 - K n) := by
    simpa [Algebra.algebraMap_eq_smul_one, one_smul] using spectrum.mem_resolventSet_iff.mp hres
  have hbij : Function.Bijective (⇑(1 - K n)) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  have hker : (1 - K n).ker = ⊥ := LinearMap.ker_eq_bot.mpr hbij.1
  have hrange : (1 - K n).range = ⊤ := LinearMap.range_eq_top.mpr hbij.2
  let Sₙ := ofBijective (1 - K n) hker hrange
  refine ⟨Sₙ, coe_ofBijective (1 - K n) hker hrange, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc0.le) fun y ↦ ?_
  rw [le_inv_mul_iff₀ hc0]
  calc
    c * ‖Sₙ.symm.toContinuousLinearMap y‖ = c * ‖Sₙ.symm y‖ := by simp [coe_apply]
    _ ≤ ‖(1 - K n) (Sₙ.symm y)‖ := hn (Sₙ.symm y)
    _ = ‖y‖ := by rw [show (1 - K n) (Sₙ.symm y) = y from Sₙ.apply_symm_apply y]

/-- Under collectively compact strong approximation `K n → T` with `1 - T` injective, solutions
of `u n - K n (u n) = f n` converge to the solution `u₀` of `u₀ - T u₀ = f₀` whenever
`f n → f₀`. -/
theorem IsCollectivelyCompact.tendsto_of_sub_apply_eq {K : ℕ → E →L[𝕜] E}
    (hc : IsCollectivelyCompact K) {T : E →L[𝕜] E}
    (hconv : ∀ x, Tendsto (fun n ↦ K n x) atTop (𝓝 (T x)))
    (hinj : Function.Injective (⇑(1 - T))) {f u : ℕ → E} {f₀ u₀ : E}
    (hu₀ : u₀ - T u₀ = f₀) (hf : Tendsto f atTop (𝓝 f₀))
    (hu : ∀ᶠ n in atTop, u n - K n (u n) = f n) :
    Tendsto u atTop (𝓝 u₀) := by
  obtain ⟨C, hC⟩ := hc.eventually_isInvertible_one_sub hconv hinj
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hres : ∀ n, (1 - K n) (u n - u₀) = (u n - K n (u n)) - f₀ + (K n - T) u₀ := by
    intro n
    rw [← hu₀]
    simp only [sub_apply, one_apply_eq_self, ContinuousLinearMap.map_sub]
    abel
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (g := fun n ↦ C * ‖f n - f₀ + (K n - T) u₀‖) ?_
  · filter_upwards [hC, hu] with n hn hu_n
    obtain ⟨Sₙ, hSₙ, hnorm⟩ := hn
    have hId : u n - u₀ = Sₙ.symm.toContinuousLinearMap (f n - f₀ + (K n - T) u₀) := by
      rw [← hu_n, ← hres, coe_coe, ← hSₙ, coe_coe, symm_apply_apply]
    rw [hId]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
  · have hK : Tendsto (fun n ↦ (K n - T) u₀) atTop (𝓝 0) := by
      simpa [sub_apply] using (hconv u₀).sub_const (T u₀)
    have hadd : Tendsto (fun n ↦ f n - f₀ + (K n - T) u₀) atTop (𝓝 0) := by
      simpa using (hf.sub_const f₀).add hK
    simpa using (tendsto_const_nhds (x := C)).mul (tendsto_zero_iff_norm_tendsto_zero.mp hadd)

end CKMA
