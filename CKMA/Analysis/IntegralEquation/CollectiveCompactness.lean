/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Sequences

/-!
# Collectively compact approximation

Collectively compact operator approximations combine strong convergence with compact closure of
the union of unit-ball images. The scalar field is real or complex. The statements control
inverses of `1 - Kₙ` and convergence of solutions.
Source: GAPS 25.47.
-/

@[expose] public section

namespace CKMA

open ContinuousLinearEquiv Filter Metric Module End Set Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- Collective compactness of a sequence of operators. -/
def IsCollectivelyCompact (K : ℕ → E →L[𝕜] E) : Prop :=
  IsCompact (closure (⋃ n, K n '' Metric.closedBall 0 1))

omit [CompleteSpace E] in
/-- Each operator of a collectively compact sequence is compact. -/
private theorem isCompactOperator_of_isCollectivelyCompact {K : ℕ → E →L[𝕜] E}
    (hc : IsCollectivelyCompact K) (n : ℕ) : IsCompactOperator (K n) := by
  rw [isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image (⇑(K n))]
  refine ⟨closedBall (0 : E) 1, closedBall_mem_nhds 0 zero_lt_one, ?_⟩
  refine hc.of_isClosed_subset isClosed_closure ?_
  exact closure_mono <| subset_iUnion (fun m ↦ (K m) '' closedBall (0 : E) 1) n

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

/-- A collectively compact strong approximation of an injective `1 - T` is eventually
bounded below. -/
private theorem exists_eventually_norm_ge (K : ℕ → E →L[𝕜] E) (T : E →L[𝕜] E)
    (hc : IsCollectivelyCompact K) (hconv : ∀ x, Tendsto (fun n ↦ K n x) atTop (𝓝 (T x)))
    (hinj : Function.Injective (⇑(1 - T))) :
    ∃ c > 0, ∀ᶠ n in atTop, ∀ x, c * ‖x‖ ≤ ‖(1 - K n) x‖ := by
  by_contra H
  have H' : ∀ c : ℝ, 0 < c → ∃ᶠ n in atTop, ∃ x : E, ‖(1 - K n) x‖ < c * ‖x‖ := by
    intro c hc
    have hnot : ¬ ∀ᶠ n in atTop, ∀ x, c * ‖x‖ ≤ ‖(1 - K n) x‖ := by
      intro hall
      exact H ⟨c, hc, hall⟩
    rw [not_eventually] at hnot
    exact hnot.mono fun _n hn ↦ by
      push Not at hn
      exact hn
  have hex : ∀ k : ℕ, ∃ n : ℕ, ∃ x : E, k ≤ n ∧ ‖x‖ = 1 ∧
      ‖(1 - K n) x‖ < (1 : ℝ) / ((k : ℝ) + 1) := by
    intro k
    have hc : 0 < (1 : ℝ) / ((k : ℝ) + 1) := by positivity
    obtain ⟨n, hkn, hx⟩ := (frequently_atTop.mp (H' _ hc)) k
    obtain ⟨x, hx⟩ := hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    refine ⟨n, (‖x‖⁻¹ : 𝕜) • x, hkn, ?_, ?_⟩
    · rw [norm_smul, norm_inv, RCLike.norm_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]
    · have hpos : 0 < ‖x‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hx0)
      calc
        ‖(1 - K n) ((‖x‖⁻¹ : 𝕜) • x)‖
            = ‖x‖⁻¹ * ‖(1 - K n) x‖ := by
              rw [ContinuousLinearMap.map_smul, norm_smul, norm_inv,
                RCLike.norm_of_nonneg (norm_nonneg _)]
          _ < ‖x‖⁻¹ * ((1 : ℝ) / ((k : ℝ) + 1) * ‖x‖) :=
              mul_lt_mul_of_pos_left hx hpos
          _ = (1 : ℝ) / ((k : ℝ) + 1) := by
              rw [mul_left_comm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0), mul_one]
  choose n x hkn hxnorm hxlt using hex
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

/-- **25.47**: strong collectively compact approximations have uniformly bounded inverses
near an invertible limit. The equivalences witness both bijectivity and bounded inverses. -/
theorem collectivelyCompact_eventually_inverse (K : ℕ → E →L[𝕜] E) (T : E →L[𝕜] E)
    (hc : IsCollectivelyCompact K) (hconv : ∀ x, Tendsto (fun n ↦ K n x) atTop (𝓝 (T x)))
    (S : E ≃L[𝕜] E) (hS : S.toContinuousLinearMap = 1 - T) :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∃ Sₙ : E ≃L[𝕜] E,
      Sₙ.toContinuousLinearMap = 1 - K n ∧ ‖Sₙ.symm.toContinuousLinearMap‖ ≤ C := by
  have hinj : Function.Injective (⇑(1 - T)) := by
    have hEq : (1 - T : E →L[𝕜] E) = S := by
      rw [← hS]
    rw [hEq]
    exact S.injective
  obtain ⟨c, hc0, hlower⟩ := exists_eventually_norm_ge K T hc hconv hinj
  refine ⟨c⁻¹, ?_⟩
  filter_upwards [hlower] with n hn
  have hcomp : IsCompactOperator (K n) := isCompactOperator_of_isCollectivelyCompact hc n
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
    (hcomp.hasEigenvalue_or_mem_resolventSet (one_ne_zero : (1 : 𝕜) ≠ 0)).resolve_left hnot
  have hunit : IsUnit (1 - K n) := by
    simpa [Algebra.algebraMap_eq_smul_one, one_smul] using spectrum.mem_resolventSet_iff.mp hres
  have hbij : Function.Bijective (⇑(1 - K n)) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  have hker : (1 - K n).ker = ⊥ := LinearMap.ker_eq_bot.mpr hbij.1
  have hrange : (1 - K n).range = ⊤ := LinearMap.range_eq_top.mpr hbij.2
  let Sₙ := ofBijective (1 - K n) hker hrange
  refine ⟨Sₙ, ?_, ?_⟩
  · exact coe_ofBijective (1 - K n) hker hrange
  · refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc0.le) fun y ↦ ?_
    rw [le_inv_mul_iff₀ hc0]
    have hlow := hn (Sₙ.symm y)
    have happ : (1 - K n) (Sₙ.symm y) = y := Sₙ.apply_symm_apply y
    calc
      c * ‖Sₙ.symm.toContinuousLinearMap y‖ = c * ‖Sₙ.symm y‖ := by
        simp [coe_apply]
      _ ≤ ‖(1 - K n) (Sₙ.symm y)‖ := hlow
      _ = ‖y‖ := by rw [happ]

/-- Solutions for convergent right-hand sides converge under collectively compact approximation. -/
theorem collectivelyCompact_solution_tendsto (K : ℕ → E →L[𝕜] E) (T : E →L[𝕜] E)
    (hc : IsCollectivelyCompact K) (hconv : ∀ x, Tendsto (fun n ↦ K n x) atTop (𝓝 (T x)))
    (S : E ≃L[𝕜] E) (hS : S.toContinuousLinearMap = 1 - T)
    (f u : ℕ → E) (f₀ : E) (hf : Tendsto f atTop (𝓝 f₀))
    (hu : ∀ᶠ n in atTop, u n - K n (u n) = f n) :
    Tendsto u atTop (𝓝 (S.symm f₀)) := by
  obtain ⟨C, hC⟩ := collectivelyCompact_eventually_inverse K T hc hconv S hS
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ ↦ norm_nonneg _
  · filter_upwards [hC, hu] with n hn hu_n
    obtain ⟨Sₙ, hSₙ, hnorm⟩ := hn
    have hx₀ : (1 - T) (S.symm f₀) = f₀ := by
      rw [← hS]
      simp [coe_apply]
    have hu' : (1 - K n) (u n) = f n := by
      simpa [sub_apply, one_apply_eq_self] using hu_n
    have hId : u n - S.symm f₀ =
        Sₙ.symm (f n - f₀ + (K n - T) (S.symm f₀)) := by
      rw [eq_comm, Sₙ.symm_apply_eq]
      calc
        f n - f₀ + (K n - T) (S.symm f₀)
            = (1 - K n) (u n) - (1 - T) (S.symm f₀) + (K n - T) (S.symm f₀) := by
              rw [hu', hx₀]
          _ = (1 - K n) (u n) -
                ((1 - T) (S.symm f₀) - (K n - T) (S.symm f₀)) := by abel
          _ = (1 - K n) (u n) - (1 - K n) (S.symm f₀) := by
              congr 1
              simp only [sub_apply, one_apply_eq_self]
              abel
          _ = (1 - K n) (u n - S.symm f₀) := by
              rw [← ContinuousLinearMap.map_sub]
          _ = Sₙ (u n - S.symm f₀) := by
              rw [← hSₙ]
              simp [coe_apply]
    calc
      ‖u n - S.symm f₀‖
          = ‖Sₙ.symm (f n - f₀ + (K n - T) (S.symm f₀))‖ := by rw [hId]
        _ = ‖Sₙ.symm.toContinuousLinearMap
              (f n - f₀ + (K n - T) (S.symm f₀))‖ := by simp [coe_apply]
        _ ≤ ‖Sₙ.symm.toContinuousLinearMap‖ *
              ‖f n - f₀ + (K n - T) (S.symm f₀)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ C * ‖f n - f₀ + (K n - T) (S.symm f₀)‖ :=
            mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
  · have hf0 : Tendsto (fun n ↦ f n - f₀) atTop (𝓝 (0 : E)) := by
      simpa [sub_self] using hf.sub (tendsto_const_nhds (x := f₀))
    have hK : Tendsto (fun n ↦ (K n - T) (S.symm f₀)) atTop (𝓝 0) := by
      have h := (hconv (S.symm f₀)).sub (tendsto_const_nhds (x := T (S.symm f₀)))
      simp only [sub_self] at h
      simpa [sub_apply] using h
    have hadd : Tendsto (fun n ↦ f n - f₀ + (K n - T) (S.symm f₀)) atTop (𝓝 0) := by
      simpa [add_zero] using hf0.add hK
    have hnorm := (tendsto_zero_iff_norm_tendsto_zero).mp hadd
    simpa [mul_zero] using (tendsto_const_nhds (x := C)).mul hnorm

end CKMA
