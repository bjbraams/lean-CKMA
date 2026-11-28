/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.RealMethod

/-!
# The real interpolation bound for nonnegative endpoint bounds

For compatible couples `(X₀, X₁)` and `(Y₀, Y₁)` and a linear map `T` of their sum spaces that
restricts to maps `T₀ : X₀ → Y₀` and `T₁ : X₁ → Y₁` with `‖T₀ x‖ ≤ M₀ ‖x‖` and
`‖T₁ x‖ ≤ M₁ ‖x‖`, the `K`-method norm satisfies
`‖T u‖_{θ,q} ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖_{θ,q}` for every exponent `q` and `0 ≤ θ ≤ 1`.
TauCeti's `TauCeti.CompatibleCouple.kMethodENorm_map_le` proves this for positive `M₀`, `M₁`
and every `θ`; here the bounds `M₀`, `M₁` may vanish, by replacing `Mᵢ` with `Mᵢ + ε` and
letting `ε → 0`. This passage to the limit uses `‖u‖_{θ,q} < ∞` and `0 ≤ θ ≤ 1`.

The complex interpolation bound (GAPS 26.54) is TauCeti's
`TauCeti.CompatibleCouple.ComplexMethodSpace.norm_map_le`, which allows `M₀, M₁ ≥ 0`
and `0 ≤ θ ≤ 1`.

Sources: GAPS 26.53 and 26.54. Compatible couples, the `K`-functional, the `K`-method norm and
the real interpolation spaces are TauCeti's (`TauCeti.Analysis.Normed.Interpolation`).

## Main results

* `CKMA.kMethodENorm_map_le_of_nonneg` (**26.53**): the real interpolation bound for the
  `K`-method norm of an element of the sum space with finite norm.
* `CKMA.KMethodSpace.norm_map_le_of_nonneg`: the same bound for the induced map of the real
  interpolation spaces.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology Set TauCeti TauCeti.CompatibleCouple
open scoped ENNReal

/-- If a bound holds for every `Mᵢ + ε`, it holds for nonnegative `Mᵢ`, when `0 ≤ θ ≤ 1`. -/
private theorem le_of_endpointFactor_eps {θ : ℝ} (hθ : θ ∈ Icc 0 1) {M₀ M₁ : ℝ}
    {a G : ℝ≥0∞} (hG : G ≠ ∞)
    (h : ∀ ε : ℝ, 0 < ε →
      a ≤ ENNReal.ofReal ((M₀ + ε) ^ (1 - θ) * (M₁ + ε) ^ θ) * G) :
    a ≤ ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * G := by
  let εn : ℕ → ℝ := fun n => (↑(n + 1) : ℝ)⁻¹
  have hεpos : ∀ n, 0 < εn n := fun n => inv_pos.mpr (Nat.cast_pos.mpr n.succ_pos)
  have hεlim : Tendsto εn atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hpow0 : Tendsto (fun n => (M₀ + εn n) ^ (1 - θ)) atTop (𝓝 (M₀ ^ (1 - θ))) := by
    simpa [add_zero] using
      (tendsto_const_nhds.add hεlim).rpow_const (Or.inr (sub_nonneg.mpr hθ.2))
  have hpow1 : Tendsto (fun n => (M₁ + εn n) ^ θ) atTop (𝓝 (M₁ ^ θ)) := by
    simpa [add_zero] using (tendsto_const_nhds.add hεlim).rpow_const (Or.inr hθ.1)
  have hmul : Tendsto (fun n => ENNReal.ofReal ((M₀ + εn n) ^ (1 - θ) * (M₁ + εn n) ^ θ) * G)
      atTop (𝓝 (ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * G)) :=
    ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal (hpow0.mul hpow1)) (Or.inr hG)
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hmul fun n => h (εn n) (hεpos n)

section Gauge

variable {𝕜 X₀ X₁ V Y₀ Y₁ W : Type*} [NormedField 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [ContinuousAdd V]
  [NormedAddCommGroup Y₀] [NormedSpace 𝕜 Y₀] [NormedAddCommGroup Y₁] [NormedSpace 𝕜 Y₁]
  [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W] [ContinuousAdd W]
  {C : CompatibleCouple 𝕜 X₀ X₁ V} {D : CompatibleCouple 𝕜 Y₀ Y₁ W}

/-- **26.53**, real interpolation theorem: a linear map of sum spaces restricting to endpoint
maps with bounds `M₀, M₁ ≥ 0` multiplies the `K`-method norm of an element of finite norm by at
most `M₀ ^ (1 - θ) * M₁ ^ θ`, for `0 ≤ θ ≤ 1` and every exponent `q`. -/
theorem kMethodENorm_map_le_of_nonneg (T : C.SumSpace →ₗ[𝕜] D.SumSpace) {T₀ : X₀ → Y₀}
    {T₁ : X₁ → Y₁} (hT₀ : ∀ x, T (C.fstToSum x) = D.fstToSum (T₀ x))
    (hT₁ : ∀ x, T (C.sndToSum x) = D.sndToSum (T₁ x)) {θ : ℝ} (hθ : θ ∈ Icc 0 1)
    {q : ℝ≥0∞} {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖)
    (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) {u : C.SumSpace} (hu : C.kMethodENorm θ q u ≠ ∞) :
    D.kMethodENorm θ q (T u) ≤
      ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * C.kMethodENorm θ q u := by
  refine le_of_endpointFactor_eps hθ hu fun ε hε => ?_
  exact kMethodENorm_map_le T hT₀ hT₁ (by positivity) (by positivity)
    (fun x => (h₀ x).trans (by gcongr; linarith))
    (fun x => (h₁ x).trans (by gcongr; linarith)) u

end Gauge

section Space

variable {𝕜 X₀ X₁ V Y₀ Y₁ W : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  [NormedAddCommGroup Y₀] [NormedSpace 𝕜 Y₀] [NormedAddCommGroup Y₁] [NormedSpace 𝕜 Y₁]
  [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W] [ContinuousAdd W] [T1Space W]
  {C : CompatibleCouple 𝕜 X₀ X₁ V} {D : CompatibleCouple 𝕜 Y₀ Y₁ W} {θ : ℝ} {q : ℝ≥0∞}
  [Fact (1 ≤ q)]

/-- The real interpolation theorem for the induced map `(X₀, X₁)_{θ,q} → (Y₀, Y₁)_{θ,q}`, with
endpoint bounds `M₀, M₁ ≥ 0` and `0 ≤ θ ≤ 1`. -/
theorem KMethodSpace.norm_map_le_of_nonneg (T : C.SumSpace →ₗ[𝕜] D.SumSpace)
    {T₀ : X₀ →L[𝕜] Y₀} {T₁ : X₁ →L[𝕜] Y₁} (hT₀ : ∀ x, T (C.fstToSum x) = D.fstToSum (T₀ x))
    (hT₁ : ∀ x, T (C.sndToSum x) = D.sndToSum (T₁ x)) (hθ : θ ∈ Icc 0 1) {M₀ M₁ : ℝ}
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖)
    (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) (u : C.KMethodSpace θ q) :
    ‖KMethodSpace.map T hT₀ hT₁ u‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖ := by
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_mul (by positivity),
    KMethodSpace.ofReal_norm, KMethodSpace.ofReal_norm, KMethodSpace.toSumₗ_map]
  have hu : C.kMethodENorm θ q (KMethodSpace.toSumₗ u) ≠ ∞ := by
    rw [← KMethodSpace.ofReal_norm]
    exact ENNReal.ofReal_ne_top
  exact kMethodENorm_map_le_of_nonneg T hT₀ hT₁ hθ hM₀ hM₁ h₀ h₁ hu

end Space

end CKMA
