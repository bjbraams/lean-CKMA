/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.PDE.Euclidean
public import TauCeti.Analysis.Sobolev.W1p.Basic
public import TauCeti.Analysis.Sobolev.W1p.Zero

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.DenselyOrdered
import TauCeti.Analysis.Sobolev.W1p.Density

/-!
# Finite-energy waves: definitions and uniqueness

Forced linear waves `∂ₜ²u - c² Δu = f` with position in TauCeti's first-order Sobolev space
`H¹(ℝ^d)` and velocity in `L²(ℝ^d)`. Solutions are continuous energy-space curves on a compact
time interval `[0, T]`, with a strong position derivative and an integrated weak velocity
equation tested against smooth compactly supported functions. Uniqueness follows from the energy
identity for the difference of two solutions, after extending the weak equation from tests to
all of `H¹` by density (TauCeti's `w1p0Submodule_top_eq_top`).

## Main definitions

* `CKMA.WavePositionSpace`, `CKMA.WaveVelocitySpace`: `H¹(ℝ^d)` position and `L²(ℝ^d)` velocity
  spaces for finite-energy waves.
* `CKMA.intervalCurveExtend`: extension by zero of a curve on a compact time interval.
* `CKMA.IsWaveEnergySolution`: weak finite-energy solutions of the forced linear wave equation.

## Main results

* `CKMA.isWaveEnergySolution_iff`: the defining conditions.
* `CKMA.wave_inner_residual_eq_zero_iff`: the tested weak equation as a residual pairing of
  Sobolev jets.
* `CKMA.IsWaveEnergySolution.unique`: uniqueness of finite-energy solutions with given data.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory TauCeti Filter Metric Set TopologicalSpace
open scoped InnerProductSpace Interval Distributions

/-- The actual first-order real Sobolev space on all of Euclidean space. -/
abbrev WavePositionSpace (d : ℕ) := TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin d))) ⊤ 2

/-- The scalar velocity space of finite-energy waves. -/
abbrev WaveVelocitySpace (d : ℕ) :=
  Lp ℝ 2 ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict
    ((⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d))))

/-- Extend a curve off its time interval by zero. Interior derivative assertions do not depend
on the chosen extension, and uniqueness below is on the actual compact time interval. -/
@[expose]
def intervalCurveExtend {F : Type*} [Zero F] (T : ℝ) (u : Set.Icc (0 : ℝ) T → F) (t : ℝ) : F := by
  classical
  exact if ht : t ∈ Set.Icc (0 : ℝ) T then u ⟨t, ht⟩ else 0

/-- Weak energy solution using continuous `H¹` and `L²` curves, their actual Sobolev gradients,
and an integrated velocity equation. The integral identity excludes singular-in-time
continuous curves with zero derivative almost everywhere. -/
@[expose]
def IsWaveEnergySolution {d : ℕ} (c T : ℝ) (u₀ : WavePositionSpace d)
    (v₀ : WaveVelocitySpace d) (f : ℝ → WaveVelocitySpace d)
    (uv : C(Set.Icc (0 : ℝ) T, WavePositionSpace d) ×
      C(Set.Icc (0 : ℝ) T, WaveVelocitySpace d)) : Prop :=
  (∀ t, t.1 = 0 → uv.1 t = u₀ ∧ uv.2 t = v₀) ∧
  (∀ (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
    HasDerivAt (intervalCurveExtend T (fun τ ↦ TauCeti.W1p.value (uv.1 τ)))
      (uv.2 ⟨t, ⟨ht.1.le, ht.2.le⟩⟩) t) ∧
  ∀ ψ : EuclideanSpace ℝ (Fin d) → ℝ, IsCompactSmoothTestOn Set.univ ψ →
    ∀ t : Set.Icc (0 : ℝ) T,
      (∫ x, (uv.2 t) x * ψ x) = (∫ x, v₀ x * ψ x) +
        ∫ s in (0 : ℝ)..t.1,
          (∫ x, f s x * ψ x) - c ^ 2 * ∫ x,
            ⟪TauCeti.W1p.gradient (intervalCurveExtend T uv.1 s) x, gradient ψ x⟫_ℝ

/-- The three defining conditions of a finite-energy wave solution: initial data, the strong
position derivative in the open time interval, and the integrated weak velocity equation. -/
theorem isWaveEnergySolution_iff {d : ℕ} {c T : ℝ} {u₀ : WavePositionSpace d}
    {v₀ : WaveVelocitySpace d} {f : ℝ → WaveVelocitySpace d}
    {uv : C(Set.Icc (0 : ℝ) T, WavePositionSpace d) ×
      C(Set.Icc (0 : ℝ) T, WaveVelocitySpace d)} :
    IsWaveEnergySolution c T u₀ v₀ f uv ↔
      (∀ t, t.1 = 0 → uv.1 t = u₀ ∧ uv.2 t = v₀) ∧
      (∀ (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
        HasDerivAt (intervalCurveExtend T (fun τ ↦ TauCeti.W1p.value (uv.1 τ)))
          (uv.2 ⟨t, ⟨ht.1.le, ht.2.le⟩⟩) t) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin d) → ℝ, IsCompactSmoothTestOn Set.univ ψ →
        ∀ t : Set.Icc (0 : ℝ) T,
          (∫ x, (uv.2 t) x * ψ x) = (∫ x, v₀ x * ψ x) +
            ∫ s in (0 : ℝ)..t.1,
              (∫ x, f s x * ψ x) - c ^ 2 * ∫ x,
                ⟪TauCeti.W1p.gradient (intervalCurveExtend T uv.1 s) x, gradient ψ x⟫_ℝ :=
  Iff.rfl

/-- The value of the zero extension on its time interval. -/
theorem intervalCurveExtend_of_mem {F : Type*} [Zero F] {T : ℝ}
    (u : Set.Icc (0 : ℝ) T → F) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    intervalCurveExtend T u t = u ⟨t, ht⟩ := by
  unfold intervalCurveExtend
  simp [ht]

/-- Off its time interval the zero extension vanishes. -/
theorem intervalCurveExtend_of_notMem {F : Type*} [Zero F] {T : ℝ}
    (u : Set.Icc (0 : ℝ) T → F) {t : ℝ} (ht : t ∉ Set.Icc (0 : ℝ) T) :
    intervalCurveExtend T u t = 0 := by
  unfold intervalCurveExtend
  simp [ht]

/-- Read a position curve at the clamped time, so the resulting map is defined on all of `ℝ`. -/
private def clampedPosition {d : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (u : C(Set.Icc (0 : ℝ) T, WavePositionSpace d)) (t : ℝ) : WavePositionSpace d :=
  u (Set.projIcc 0 T hT t)

/-- The clamped position curve is continuous. -/
private theorem continuous_clampedPosition {d : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (u : C(Set.Icc (0 : ℝ) T, WavePositionSpace d)) :
    Continuous (clampedPosition hT u) :=
  u.continuous.comp continuous_projIcc

/-- On `[0, T]`, clamping does not change the position. -/
private theorem clampedPosition_of_mem {d : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (u : C(Set.Icc (0 : ℝ) T, WavePositionSpace d)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    clampedPosition hT u t = u ⟨t, ht⟩ := by
  simp [clampedPosition, Set.projIcc_of_mem hT ht]

/-- Clamping commutes with subtraction of position curves. -/
private theorem clampedPosition_sub {d : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (u w : C(Set.Icc (0 : ℝ) T, WavePositionSpace d)) (t : ℝ) :
    clampedPosition hT (u - w) t = clampedPosition hT u t - clampedPosition hT w t := by
  simp [clampedPosition, ContinuousMap.sub_apply]

/-- Time integral of a clamped position curve, based at time `0`. -/
private def integratedPosition {d : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (u : C(Set.Icc (0 : ℝ) T, WavePositionSpace d)) (t : ℝ) : WavePositionSpace d :=
  ∫ s in (0 : ℝ)..t, clampedPosition hT u s

/-- The time integral of a continuous position curve has derivative equal to the curve. -/
private theorem hasDerivAt_integratedPosition {d : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (u : C(Set.Icc (0 : ℝ) T, WavePositionSpace d)) (t : ℝ) :
    HasDerivAt (integratedPosition hT u) (clampedPosition hT u t) t :=
  ((continuous_clampedPosition hT u).integral_hasStrictDerivAt 0 t).hasDerivAt

/-- The weak gradient passes through the time integral. -/
private theorem gradient_integratedPosition {d : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (u : C(Set.Icc (0 : ℝ) T, WavePositionSpace d)) (t : ℝ) :
    W1p.gradient (integratedPosition hT u t) =
      ∫ s in (0 : ℝ)..t, W1p.gradient (clampedPosition hT u s) := by
  rw [integratedPosition, ← W1p.gradientL_apply]
  have hint : IntervalIntegrable (clampedPosition hT u) volume 0 t :=
    (continuous_clampedPosition hT u).intervalIntegrable 0 t
  rw [← W1p.gradientL.intervalIntegral_comp_comm hint]
  refine intervalIntegral.integral_congr fun _ _ => ?_
  exact W1p.gradientL_apply _

/-- Pair an `L²` velocity against the value of a position. -/
private def valuePairingCLM {d : ℕ} (v : WaveVelocitySpace d) : WavePositionSpace d →L[ℝ] ℝ :=
  (innerSL ℝ v).comp W1p.valueL

/-- The velocity pairing is the real `L²` inner product of the value. -/
private theorem valuePairingCLM_apply {d : ℕ} (v : WaveVelocitySpace d) (w : WavePositionSpace d) :
    valuePairingCLM v w = ⟪v, W1p.value w⟫_ℝ := by
  rw [valuePairingCLM, ContinuousLinearMap.comp_apply, W1p.valueL_apply, innerSL_apply_apply]

/-- Accumulate `c²` times the integrated gradient, as a continuous linear functional of a test. -/
private def gradientAccumCLM {d : ℕ} {T : ℝ} (hT : 0 ≤ T) (c : ℝ)
    (u : C(Set.Icc (0 : ℝ) T, WavePositionSpace d)) (t : ℝ) : WavePositionSpace d →L[ℝ] ℝ :=
  (c ^ 2) •
    (innerSL ℝ (∫ s in (0 : ℝ)..t, W1p.gradient (clampedPosition hT u s))).comp W1p.gradientL

/-- The accumulated gradient pairing is `c²` times the inner product of the integrated gradient. -/
private theorem gradientAccumCLM_apply {d : ℕ} {T : ℝ} (hT : 0 ≤ T) (c : ℝ)
    (u : C(Set.Icc (0 : ℝ) T, WavePositionSpace d)) (t : ℝ) (w : WavePositionSpace d) :
    gradientAccumCLM hT c u t w =
      c ^ 2 * ⟪∫ s in (0 : ℝ)..t, W1p.gradient (clampedPosition hT u s), W1p.gradient w⟫_ℝ := by
  rw [gradientAccumCLM, smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    smul_eq_mul, W1p.gradientL_apply]

/-- The integrated weak form, packaged as a continuous linear functional of the spatial test. -/
private def waveResidualCLM {d : ℕ} {T : ℝ} (hT : 0 ≤ T) (c : ℝ) (v₀ : WaveVelocitySpace d)
    (f : ℝ → WaveVelocitySpace d)
    (uv : C(Set.Icc (0 : ℝ) T, WavePositionSpace d) ×
      C(Set.Icc (0 : ℝ) T, WaveVelocitySpace d))
    (t : Set.Icc (0 : ℝ) T) : WavePositionSpace d →L[ℝ] ℝ :=
  valuePairingCLM (uv.2 t) - valuePairingCLM v₀ -
    valuePairingCLM (∫ s in (0 : ℝ)..t.1, f s) + gradientAccumCLM hT c uv.1 t.1

/-- A smooth compactly supported test is the value of its Sobolev jet in the velocity pairing. -/
private theorem integral_velocity_mul_test {d : ℕ} (v : WaveVelocitySpace d)
    (φ : 𝓓(⊤, ℝ)) :
    ∫ x, v x * (φ : EuclideanSpace ℝ (Fin d) → ℝ) x =
      ⟪v, W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 φ)⟫_ℝ := by
  rw [L2.inner_def]
  simp only [Opens.coe_top, Measure.restrict_univ]
  refine integral_congr_ae ?_
  filter_upwards [W1p.value_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ] with x hx
  simp [hx, RCLike.inner_apply, mul_comm]

/-- A compactly supported smooth gradient pairs with an `L²` field through the Sobolev jet. -/
private theorem integral_gradient_inner_test {d : ℕ}
    (g : Lp (EuclideanSpace ℝ (Fin d)) 2
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict
        ((⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))) :
          Set (EuclideanSpace ℝ (Fin d)))))
    (φ : 𝓓(⊤, ℝ)) :
    ∫ x, ⟪g x, gradient (φ : EuclideanSpace ℝ (Fin d) → ℝ) x⟫_ℝ =
      ⟪g, W1p.gradient (W1p.ofTestFunctionₗ volume ⊤ 2 φ)⟫_ℝ := by
  rw [L2.inner_def]
  simp only [Opens.coe_top, Measure.restrict_univ]
  refine integral_congr_ae ?_
  filter_upwards [W1p.gradient_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ] with x hx
  rw [hx]

/-- Forcing in `L¹([0, T]; L²)` is interval integrable on every subinterval of `[0, T]`. -/
private theorem intervalIntegrable_force {d : ℕ} {T : ℝ} {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    {f : ℝ → WaveVelocitySpace d} (hf : IntegrableOn f (Set.Icc (0 : ℝ) T)) :
    IntervalIntegrable f volume 0 t :=
  (hf.mono_set (by
    rw [uIcc_of_le ht0]
    exact Icc_subset_Icc le_rfl htT)).intervalIntegrable

/-- A continuous linear image of an interval-integrable curve stays interval integrable. -/
private theorem wave_intervalIntegrable_clm {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {f : ℝ → E} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun s => L (f s)) volume a b :=
  ⟨L.integrable_comp hf.1, L.integrable_comp hf.2⟩

/-- Evaluate a difference of continuous linear functionals before adding another. -/
private theorem waveCLM_sub_sub_add_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A B C D : G →L[ℝ] ℝ) (x : G) :
    (A - B - C + D) x = A x - B x - C x + D x := by
  rw [add_apply, sub_apply, sub_apply]

/-- The residual functional, evaluated on one position, is the integrated weak form. -/
private theorem waveResidualCLM_apply {d : ℕ} {T : ℝ} (hT : 0 ≤ T) (c : ℝ)
    (v₀ : WaveVelocitySpace d) (f : ℝ → WaveVelocitySpace d)
    (uv : C(Set.Icc (0 : ℝ) T, WavePositionSpace d) ×
      C(Set.Icc (0 : ℝ) T, WaveVelocitySpace d))
    (t : Set.Icc (0 : ℝ) T) (w : WavePositionSpace d) :
    waveResidualCLM hT c v₀ f uv t w =
      ⟪uv.2 t, W1p.value w⟫_ℝ - ⟪v₀, W1p.value w⟫_ℝ -
        ⟪∫ s in (0 : ℝ)..t.1, f s, W1p.value w⟫_ℝ +
        c ^ 2 * ⟪∫ s in (0 : ℝ)..t.1, W1p.gradient (clampedPosition hT uv.1 s),
          W1p.gradient w⟫_ℝ := by
  simp only [waveResidualCLM, waveCLM_sub_sub_add_apply, valuePairingCLM_apply,
    gradientAccumCLM_apply]

set_option maxHeartbeats 1000000 in
/-- The scalar residual is zero exactly when the integrated test equation holds. -/
private theorem wave_test_scalar_zero_iff {d : ℕ} {c T : ℝ} (hT : 0 ≤ T)
    (v₀ : WaveVelocitySpace d) {f : ℝ → WaveVelocitySpace d}
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) T))
    (uv : C(Set.Icc (0 : ℝ) T, WavePositionSpace d) ×
      C(Set.Icc (0 : ℝ) T, WaveVelocitySpace d))
    (t : Set.Icc (0 : ℝ) T) (φ : 𝓓(⊤, ℝ)) :
    ⟪uv.2 t, W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 φ)⟫_ℝ -
        ⟪v₀, W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 φ)⟫_ℝ -
        ⟪∫ s in (0 : ℝ)..t.1, f s,
          W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 φ)⟫_ℝ +
        c ^ 2 * ⟪∫ s in (0 : ℝ)..t.1, W1p.gradient (clampedPosition hT uv.1 s),
          W1p.gradient (W1p.ofTestFunctionₗ volume ⊤ 2 φ)⟫_ℝ = 0 ↔
      (∫ x, (uv.2 t) x * (φ : EuclideanSpace ℝ (Fin d) → ℝ) x) =
        (∫ x, v₀ x * (φ : EuclideanSpace ℝ (Fin d) → ℝ) x) +
          ∫ s in (0 : ℝ)..t.1, (∫ x, f s x * (φ : EuclideanSpace ℝ (Fin d) → ℝ) x) -
            c ^ 2 * ∫ x, ⟪W1p.gradient (intervalCurveExtend T uv.1 s) x,
              gradient (φ : EuclideanSpace ℝ (Fin d) → ℝ) x⟫_ℝ := by
  set w : WavePositionSpace d := W1p.ofTestFunctionₗ volume ⊤ 2 φ with hw
  have hvel := integral_velocity_mul_test (uv.2 t) φ
  have hv0 := integral_velocity_mul_test v₀ φ
  have hforce_pt : ∀ s, ∫ x, f s x * (φ : EuclideanSpace ℝ (Fin d) → ℝ) x =
      ⟪f s, W1p.value w⟫_ℝ :=
    fun s => integral_velocity_mul_test (f s) φ
  have hintf : IntervalIntegrable f volume 0 t.1 :=
    intervalIntegrable_force t.2.1 t.2.2 hf
  have hintF : IntervalIntegrable (fun s => ⟪f s, W1p.value w⟫_ℝ) volume 0 t.1 := by
    refine (wave_intervalIntegrable_clm (innerSL ℝ (W1p.value w)) hintf).congr ?_
    intro _ _
    dsimp
    rw [real_inner_comm]
  let Fs : ℝ → ℝ := fun s => ∫ x, f s x * (φ : EuclideanSpace ℝ (Fin d) → ℝ) x
  let Gs : ℝ → ℝ := fun s => ∫ x,
    ⟪W1p.gradient (intervalCurveExtend T uv.1 s) x, gradient (φ : EuclideanSpace ℝ (Fin d) → ℝ) x⟫_ℝ
  let Gi : ℝ → ℝ := fun s =>
    ⟪W1p.gradient (clampedPosition hT uv.1 s), W1p.gradient w⟫_ℝ
  have hcontGi : Continuous Gi := by
    refine Continuous.congr
      ((innerSL ℝ (W1p.gradient w)).continuous.comp
        (W1p.gradientL.continuous.comp (continuous_clampedPosition hT uv.1))) ?_
    intro s
    unfold Gi
    dsimp
    rw [← W1p.gradientL_apply (clampedPosition hT uv.1 s), ← W1p.gradientL_apply w,
      real_inner_comm]
  have hintGi : IntervalIntegrable Gi volume 0 t.1 := hcontGi.intervalIntegrable 0 t.1
  have hGe : EqOn Gs Gi (Icc (0 : ℝ) t.1) := by
    intro s hs
    have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans t.2.2⟩
    have hsame : intervalCurveExtend T uv.1 s = clampedPosition hT uv.1 s := by
      rw [intervalCurveExtend_of_mem uv.1 hsT, clampedPosition_of_mem hT uv.1 hsT]
    unfold Gs Gi
    rw [hsame, hw]
    exact integral_gradient_inner_test
      (W1p.gradient (clampedPosition hT uv.1 s)) φ
  have hGint : ∫ s in (0 : ℝ)..t.1, Gs s = ∫ s in (0 : ℝ)..t.1, Gi s :=
    intervalIntegral.integral_congr (by
      rw [uIcc_of_le t.2.1]
      exact hGe)
  have hFint : ∫ s in (0 : ℝ)..t.1, Fs s = ∫ s in (0 : ℝ)..t.1, ⟪f s, W1p.value w⟫_ℝ :=
    intervalIntegral.integral_congr (fun s _ => hforce_pt s)
  have hintFs : IntervalIntegrable Fs volume 0 t.1 :=
    hintF.congr fun _ _ => (hforce_pt _).symm
  have hintGs : IntervalIntegrable Gs volume 0 t.1 := by
    refine hintGi.congr ?_
    rw [uIoc_of_le t.2.1]
    intro s hs
    exact (hGe ⟨le_of_lt hs.1, hs.2⟩).symm
  have hintcGs : IntervalIntegrable (fun s => c ^ 2 * Gs s) volume 0 t.1 := by
    simpa [smul_eq_mul] using
      wave_intervalIntegrable_clm ((c ^ 2) • ContinuousLinearMap.id ℝ ℝ) hintGs
  have hsplit : ∫ s in (0 : ℝ)..t.1, Fs s - c ^ 2 * Gs s =
      (∫ s in (0 : ℝ)..t.1, ⟪f s, W1p.value w⟫_ℝ) -
        c ^ 2 * ∫ s in (0 : ℝ)..t.1, Gi s := by
    rw [intervalIntegral.integral_sub hintFs hintcGs, intervalIntegral.integral_const_mul,
      hFint, hGint]
  have hinnerF : ⟪∫ s in (0 : ℝ)..t.1, f s, W1p.value w⟫_ℝ =
      ∫ s in (0 : ℝ)..t.1, ⟪f s, W1p.value w⟫_ℝ := by
    rw [real_inner_comm, ← innerSL_apply_apply]
    rw [← (innerSL ℝ (W1p.value w)).intervalIntegral_comp_comm hintf]
    refine intervalIntegral.integral_congr fun _ _ => ?_
    rw [innerSL_apply_apply, real_inner_comm]
  have hintClamp : IntervalIntegrable (clampedPosition hT uv.1) volume 0 t.1 :=
    (continuous_clampedPosition hT uv.1).intervalIntegrable 0 t.1
  have hintGrad : IntervalIntegrable
      (fun s => W1p.gradient (clampedPosition hT uv.1 s)) volume 0 t.1 := by
    refine (wave_intervalIntegrable_clm W1p.gradientL hintClamp).congr ?_
    intro _ _
    dsimp
    exact W1p.gradientL_apply _
  have hinnerG : ⟪∫ s in (0 : ℝ)..t.1, W1p.gradient (clampedPosition hT uv.1 s),
      W1p.gradient w⟫_ℝ = ∫ s in (0 : ℝ)..t.1, Gi s := by
    rw [real_inner_comm, ← innerSL_apply_apply]
    rw [← (innerSL ℝ (W1p.gradient w)).intervalIntegral_comp_comm hintGrad]
    refine intervalIntegral.integral_congr fun _ _ => ?_
    rw [innerSL_apply_apply, real_inner_comm]
  -- Use the named scalar integrands in the interval-integral identity.
  change _ ↔ (∫ x, (uv.2 t) x * (φ : EuclideanSpace ℝ (Fin d) → ℝ) x) =
    (∫ x, v₀ x * (φ : EuclideanSpace ℝ (Fin d) → ℝ) x) + ∫ s in (0 : ℝ)..t.1, Fs s - c ^ 2 * Gs s
  rw [← hw] at hvel hv0
  rw [hinnerF, hinnerG, ← hvel, ← hv0, hsplit]
  constructor <;> intro h <;> linarith

/-- The residual of an energy solution vanishes on every compactly supported smooth test. -/
private theorem waveResidualCLM_ofTestFunction {d : ℕ} {c T : ℝ} (hT : 0 ≤ T)
    (u₀ : WavePositionSpace d) (v₀ : WaveVelocitySpace d) {f : ℝ → WaveVelocitySpace d}
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) T))
    (uv : C(Set.Icc (0 : ℝ) T, WavePositionSpace d) ×
      C(Set.Icc (0 : ℝ) T, WaveVelocitySpace d))
    (huv : IsWaveEnergySolution c T u₀ v₀ f uv) (t : Set.Icc (0 : ℝ) T) (φ : 𝓓(⊤, ℝ)) :
    waveResidualCLM hT c v₀ f uv t (W1p.ofTestFunctionₗ volume ⊤ 2 φ) = 0 := by
  rw [waveResidualCLM_apply]
  have hψ : IsCompactSmoothTestOn Set.univ (φ : EuclideanSpace ℝ (Fin d) → ℝ) :=
    ⟨φ.contDiff, φ.hasCompactSupport, by simpa only [Opens.coe_top] using φ.tsupport_subset⟩
  exact (wave_test_scalar_zero_iff hT v₀ hf uv t φ).2 (huv.2.2 _ hψ t)

/-- The residual of an energy solution vanishes on every finite-energy position. -/
private theorem waveResidualCLM_eq_zero {d : ℕ} {c T : ℝ} (hT : 0 ≤ T)
    (u₀ : WavePositionSpace d) (v₀ : WaveVelocitySpace d) {f : ℝ → WaveVelocitySpace d}
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) T))
    (uv : C(Set.Icc (0 : ℝ) T, WavePositionSpace d) ×
      C(Set.Icc (0 : ℝ) T, WaveVelocitySpace d))
    (huv : IsWaveEnergySolution c T u₀ v₀ f uv) (t : Set.Icc (0 : ℝ) T) :
    waveResidualCLM hT c v₀ f uv t = 0 := by
  let L := waveResidualCLM hT c v₀ f uv t
  have htest : ∀ φ, L (W1p.ofTestFunctionₗ volume ⊤ 2 φ) = 0 :=
    waveResidualCLM_ofTestFunction hT u₀ v₀ hf uv huv t
  have hclosed : IsClosed {w : WavePositionSpace d | L w = 0} :=
    isClosed_eq L.continuous continuous_const
  have hsub := w1p0Submodule_subset_of_isClosed (mu := volume)
    (Omega := (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d)))) (p := 2) hclosed htest
  have htop := w1p0Submodule_top_eq_top (mu := volume)
    (E := EuclideanSpace ℝ (Fin d)) (p := 2) (hp := by simp)
  rw [htop] at hsub
  ext w
  simpa using hsub (by simp)

/-- Cancel the shared initial velocity and forcing in two integrated scalar identities. -/
private theorem wave_scalar_sub_cancel (a b p q r s : ℝ) (ha : a - p - q + r = 0)
    (hb : b - p - q + s = 0) : (a - b) + (r - s) = 0 := by
  linarith

/-- The clamped gradient curve is interval integrable. -/
private theorem wave_intervalIntegrable_gradient {d : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (u : C(Set.Icc (0 : ℝ) T, WavePositionSpace d)) (t : ℝ) :
    IntervalIntegrable (fun s => W1p.gradient (clampedPosition hT u s)) volume 0 t := by
  refine (wave_intervalIntegrable_clm W1p.gradientL
    ((continuous_clampedPosition hT u).intervalIntegrable 0 t)).congr ?_
  intro _ _
  dsimp
  exact W1p.gradientL_apply _

/-- The integrated gradient of a position difference is the difference of the integrals. -/
private theorem gradient_integratedPosition_sub {d : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (u w : C(Set.Icc (0 : ℝ) T, WavePositionSpace d)) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, W1p.gradient (clampedPosition hT u s)) -
        ∫ s in (0 : ℝ)..t, W1p.gradient (clampedPosition hT w s) =
      W1p.gradient (integratedPosition hT (u - w) t) := by
  rw [← intervalIntegral.integral_sub (wave_intervalIntegrable_gradient hT u t)
    (wave_intervalIntegrable_gradient hT w t)]
  rw [gradient_integratedPosition hT (u - w) t]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [← W1p.gradient_sub]
  rw [clampedPosition_sub]

/-- Two energy solutions with the same data have orthogonal position-velocity differences. -/
private theorem waveResidual_sub_apply {d : ℕ} {c T : ℝ} (hT : 0 ≤ T) (u₀ : WavePositionSpace d)
    (v₀ : WaveVelocitySpace d) {f : ℝ → WaveVelocitySpace d}
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) T))
    (uv wv : C(Set.Icc (0 : ℝ) T, WavePositionSpace d) ×
      C(Set.Icc (0 : ℝ) T, WaveVelocitySpace d))
    (huv : IsWaveEnergySolution c T u₀ v₀ f uv) (hwv : IsWaveEnergySolution c T u₀ v₀ f wv)
    (t : Set.Icc (0 : ℝ) T) (w : WavePositionSpace d) :
    ⟪(uv.2 - wv.2) t, W1p.value w⟫_ℝ +
        c ^ 2 * ⟪W1p.gradient (integratedPosition hT (uv.1 - wv.1) t.1),
          W1p.gradient w⟫_ℝ = 0 := by
  have hEu : ⟪uv.2 t, W1p.value w⟫_ℝ - ⟪v₀, W1p.value w⟫_ℝ -
      ⟪∫ s in (0 : ℝ)..t.1, f s, W1p.value w⟫_ℝ +
      c ^ 2 * ⟪∫ s in (0 : ℝ)..t.1, W1p.gradient (clampedPosition hT uv.1 s),
        W1p.gradient w⟫_ℝ = 0 := by
    have hzero : waveResidualCLM hT c v₀ f uv t w = 0 := by
      rw [waveResidualCLM_eq_zero hT u₀ v₀ hf uv huv t]
      exact zero_apply w
    rw [waveResidualCLM_apply] at hzero
    exact hzero
  have hEw : ⟪wv.2 t, W1p.value w⟫_ℝ - ⟪v₀, W1p.value w⟫_ℝ -
      ⟪∫ s in (0 : ℝ)..t.1, f s, W1p.value w⟫_ℝ +
      c ^ 2 * ⟪∫ s in (0 : ℝ)..t.1, W1p.gradient (clampedPosition hT wv.1 s),
        W1p.gradient w⟫_ℝ = 0 := by
    have hzero : waveResidualCLM hT c v₀ f wv t w = 0 := by
      rw [waveResidualCLM_eq_zero hT u₀ v₀ hf wv hwv t]
      exact zero_apply w
    rw [waveResidualCLM_apply] at hzero
    exact hzero
  have hgrad : c ^ 2 * ⟪W1p.gradient (integratedPosition hT (uv.1 - wv.1) t.1),
      W1p.gradient w⟫_ℝ =
      c ^ 2 * ⟪∫ s in (0 : ℝ)..t.1, W1p.gradient (clampedPosition hT uv.1 s),
        W1p.gradient w⟫_ℝ -
      c ^ 2 * ⟪∫ s in (0 : ℝ)..t.1, W1p.gradient (clampedPosition hT wv.1 s),
        W1p.gradient w⟫_ℝ := by
    rw [← gradient_integratedPosition_sub hT uv.1 wv.1 t.1]
    rw [inner_sub_left]
    rw [mul_sub]
  calc ⟪(uv.2 - wv.2) t, W1p.value w⟫_ℝ +
        c ^ 2 * ⟪W1p.gradient (integratedPosition hT (uv.1 - wv.1) t.1),
          W1p.gradient w⟫_ℝ
      = (⟪uv.2 t, W1p.value w⟫_ℝ - ⟪wv.2 t, W1p.value w⟫_ℝ) +
          (c ^ 2 * ⟪∫ s in (0 : ℝ)..t.1, W1p.gradient (clampedPosition hT uv.1 s),
            W1p.gradient w⟫_ℝ -
          c ^ 2 * ⟪∫ s in (0 : ℝ)..t.1, W1p.gradient (clampedPosition hT wv.1 s),
            W1p.gradient w⟫_ℝ) := by
        rw [ContinuousMap.sub_apply]
        rw [inner_sub_left]
        rw [hgrad]
      _ = 0 := wave_scalar_sub_cancel _ _ _ _ _ _ hEu hEw

/-- On `[0, T]`, the value of a clamped position difference is the difference of the extensions. -/
private theorem value_clampedDiff_eq {d : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (u w : C(Set.Icc (0 : ℝ) T, WavePositionSpace d)) {s : ℝ}
    (hsT : s ∈ Set.Icc (0 : ℝ) T) :
    W1p.value (clampedPosition hT (u - w) s) =
      intervalCurveExtend T (fun τ => W1p.value (u τ)) s -
        intervalCurveExtend T (fun τ => W1p.value (w τ)) s := by
  rw [intervalCurveExtend_of_mem (fun τ => W1p.value (u τ)) hsT]
  rw [intervalCurveExtend_of_mem (fun τ => W1p.value (w τ)) hsT]
  rw [clampedPosition_of_mem hT (u - w) hsT]
  rw [ContinuousMap.sub_apply]
  rw [← W1p.valueL_apply]
  rw [map_sub]
  rw [W1p.valueL_apply]
  rw [W1p.valueL_apply]

/-- On `(0, T)`, the value of a position difference has derivative equal to the velocity
difference. -/
private theorem hasDerivAt_value_clampedDiff {d : ℕ} {c T : ℝ} (hT : 0 < T)
    (u₀ : WavePositionSpace d) (v₀ : WaveVelocitySpace d) (f : ℝ → WaveVelocitySpace d)
    (uv wv : C(Set.Icc (0 : ℝ) T, WavePositionSpace d) ×
      C(Set.Icc (0 : ℝ) T, WaveVelocitySpace d))
    (huv : IsWaveEnergySolution c T u₀ v₀ f uv) (hwv : IsWaveEnergySolution c T u₀ v₀ f wv)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun s => W1p.value (clampedPosition hT.le (uv.1 - wv.1) s))
      ((uv.2 - wv.2) ⟨t, ⟨ht.1.le, ht.2.le⟩⟩) t := by
  have hsub := (huv.2.1 t ht).sub (hwv.2.1 t ht)
  have hfun : (fun s => W1p.value (clampedPosition hT.le (uv.1 - wv.1) s)) =ᶠ[nhds t]
      fun s => intervalCurveExtend T (fun τ => W1p.value (uv.1 τ)) s -
        intervalCurveExtend T (fun τ => W1p.value (wv.1 τ)) s := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact value_clampedDiff_eq hT.le uv.1 wv.1 ⟨hs.1.le, hs.2.le⟩
  refine (hsub.congr_of_eventuallyEq hfun).congr_deriv ?_
  rw [ContinuousMap.sub_apply]

/-- The weak gradient of a time-integrated position has derivative equal to the gradient. -/
private theorem hasDerivAt_gradient_integrated {d : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (u : C(Set.Icc (0 : ℝ) T, WavePositionSpace d)) (t : ℝ) :
    HasDerivAt (fun s => W1p.gradient (integratedPosition hT u s))
      (W1p.gradient (clampedPosition hT u t)) t := by
  have hI := hasDerivAt_integratedPosition hT u t
  have hG := (W1p.gradientL.hasFDerivAt
    (x := integratedPosition hT u t)).comp_hasDerivAt t hI
  refine (hG.congr_deriv (W1p.gradientL_apply (clampedPosition hT u t))).congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall fun s => ?_
  exact (W1p.gradientL_apply (integratedPosition hT u s)).symm

/-- Quadratic form whose derivative is the difference of the integrated weak forms. -/
private def waveDiffEnergy {d : ℕ} {T : ℝ} (hT : 0 ≤ T) (c : ℝ)
    (δ : C(Set.Icc (0 : ℝ) T, WavePositionSpace d)) (t : ℝ) : ℝ :=
  (1 / 2) * ‖W1p.value (clampedPosition hT δ t)‖ ^ 2 +
    (c ^ 2 / 2) * ‖W1p.gradient (integratedPosition hT δ t)‖ ^ 2

/-- The difference energy is continuous in time. -/
private theorem continuous_waveDiffEnergy {d : ℕ} {T : ℝ} (hT : 0 ≤ T) (c : ℝ)
    (δ : C(Set.Icc (0 : ℝ) T, WavePositionSpace d)) :
    Continuous (waveDiffEnergy hT c δ) := by
  have hdiff : Differentiable ℝ (integratedPosition hT δ) :=
    fun t => (hasDerivAt_integratedPosition hT δ t).differentiableAt
  have hI : Continuous (integratedPosition hT δ) := hdiff.continuous
  unfold waveDiffEnergy
  refine Continuous.add ?_ ?_
  · refine Continuous.congr ((continuous_const (y := (1 / 2 : ℝ))).mul
        (((W1p.valueL.continuous.comp (continuous_clampedPosition hT δ)).norm).pow 2)) ?_
    intro t
    dsimp
    rw [← W1p.valueL_apply]
  · refine Continuous.congr ((continuous_const (y := c ^ 2 / 2)).mul
        (((W1p.gradientL.continuous.comp hI).norm).pow 2)) ?_
    intro t
    dsimp
    rw [← W1p.gradientL_apply]

/-- Where the difference tests to zero against itself, the difference energy is stationary. -/
private theorem hasDerivAt_waveDiffEnergy {d : ℕ} {T : ℝ} (hT : 0 ≤ T) (c : ℝ)
    (δ : C(Set.Icc (0 : ℝ) T, WavePositionSpace d)) {t : ℝ} {v : WaveVelocitySpace d}
    (hv : HasDerivAt (fun s => W1p.value (clampedPosition hT δ s)) v t)
    (hpair : ⟪v, W1p.value (clampedPosition hT δ t)⟫_ℝ +
      c ^ 2 * ⟪W1p.gradient (integratedPosition hT δ t),
        W1p.gradient (clampedPosition hT δ t)⟫_ℝ = 0) :
    HasDerivAt (waveDiffEnergy hT c δ) 0 t := by
  have hval : HasDerivAt (fun s => (1 / 2) * ‖W1p.value (clampedPosition hT δ s)‖ ^ 2)
      ⟪v, W1p.value (clampedPosition hT δ t)⟫_ℝ t := by
    refine (hv.norm_sq.const_mul (1 / 2)).congr_deriv ?_
    rw [real_inner_comm]
    ring
  have hgrad : HasDerivAt
      (fun s => (c ^ 2 / 2) * ‖W1p.gradient (integratedPosition hT δ s)‖ ^ 2)
      (c ^ 2 * ⟪W1p.gradient (integratedPosition hT δ t),
        W1p.gradient (clampedPosition hT δ t)⟫_ℝ) t := by
    refine ((hasDerivAt_gradient_integrated hT δ t).norm_sq.const_mul (c ^ 2 / 2)).congr_deriv ?_
    ring
  have hsum := (hval.add hgrad).congr_deriv hpair
  refine hsum.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall fun _ => ?_
  unfold waveDiffEnergy
  rfl

/-- The difference energy vanishes at time `0` when the positions agree there. -/
private theorem waveDiffEnergy_zero {d : ℕ} {T : ℝ} (hT : 0 ≤ T) (c : ℝ)
    (δ : C(Set.Icc (0 : ℝ) T, WavePositionSpace d))
    (hδ : δ ⟨0, ⟨le_rfl, hT⟩⟩ = 0) : waveDiffEnergy hT c δ 0 = 0 := by
  unfold waveDiffEnergy
  rw [clampedPosition_of_mem hT δ (⟨le_rfl, hT⟩ : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T)]
  rw [hδ]
  rw [integratedPosition]
  rw [intervalIntegral.integral_same]
  rw [← W1p.valueL_apply, map_zero]
  rw [← W1p.gradientL_apply, map_zero]
  simp

/-- A stationary difference energy that starts at zero stays zero on `[0, T]`. -/
private theorem waveDiffEnergy_eq_zero {d : ℕ} {T : ℝ} (hT : 0 < T) (c : ℝ)
    (δ : C(Set.Icc (0 : ℝ) T, WavePositionSpace d))
    (hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt (waveDiffEnergy hT.le c δ) 0 t)
    (hzero : waveDiffEnergy hT.le c δ 0 = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, waveDiffEnergy hT.le c δ t = 0 := by
  intro t ht
  have hcont : ContinuousOn (waveDiffEnergy hT.le c δ) (Set.Icc (0 : ℝ) T) :=
    (continuous_waveDiffEnergy hT.le c δ).continuousOn
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) T) hcont
    (fun x hx => by
      rw [interior_Icc] at hx
      exact (hderiv x hx).hasDerivWithinAt)
    (fun _ _ => le_rfl)
  have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) T) hcont
    (fun x hx => by
      rw [interior_Icc] at hx
      exact (hderiv x hx).hasDerivWithinAt)
    (fun _ _ => le_rfl)
  have hle : waveDiffEnergy hT.le c δ 0 ≤ waveDiffEnergy hT.le c δ t :=
    hmono (a := (0 : ℝ)) ⟨le_rfl, hT.le⟩ (b := t) ht ht.1
  have hge : waveDiffEnergy hT.le c δ t ≤ waveDiffEnergy hT.le c δ 0 :=
    hanti (a := (0 : ℝ)) ⟨le_rfl, hT.le⟩ (b := t) ht ht.1
  rw [le_antisymm hge hle, hzero]

/-- Vanishing difference energy forces the position difference itself to vanish. -/
private theorem waveDiffEnergy_position {d : ℕ} {T : ℝ} (hT : 0 ≤ T) (c : ℝ)
    (δ : C(Set.Icc (0 : ℝ) T, WavePositionSpace d)) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (hQ : waveDiffEnergy hT c δ t = 0) : δ ⟨t, ht⟩ = 0 := by
  set v : WaveVelocitySpace d := W1p.value (clampedPosition hT δ t) with hv
  unfold waveDiffEnergy at hQ
  have hnn : 0 ≤ (c ^ 2 / 2) * ‖W1p.gradient (integratedPosition hT δ t)‖ ^ 2 :=
    mul_nonneg (div_nonneg (sq_nonneg _) zero_le_two) (sq_nonneg _)
  have hhalf : (1 / 2) * ‖v‖ ^ 2 = 0 :=
    le_antisymm ((le_add_of_nonneg_right hnn).trans_eq hQ)
      (mul_nonneg (div_nonneg zero_le_one zero_le_two) (sq_nonneg _))
  have hnorm : ‖v‖ = 0 := by
    have hsq : ‖v‖ ^ 2 = 0 := mul_left_cancel₀ (div_ne_zero one_ne_zero two_ne_zero)
      (by simpa [mul_zero] using hhalf)
    exact sq_eq_zero_iff.mp hsq
  have hvalue : v = 0 := norm_eq_zero.mp hnorm
  rw [hv] at hvalue
  rw [clampedPosition_of_mem hT δ ht] at hvalue
  apply W1p.ext_value
  rw [hvalue]
  rw [← W1p.valueL_apply, map_zero]

/-- Equal position curves give equal velocity curves, including the endpoints. -/
private theorem waveEnergySolution_velocity_eq {d : ℕ} {c T : ℝ} (hT : 0 < T)
    (u₀ : WavePositionSpace d) (v₀ : WaveVelocitySpace d) (f : ℝ → WaveVelocitySpace d)
    (uv wv : C(Set.Icc (0 : ℝ) T, WavePositionSpace d) ×
      C(Set.Icc (0 : ℝ) T, WaveVelocitySpace d))
    (huv : IsWaveEnergySolution c T u₀ v₀ f uv) (hwv : IsWaveEnergySolution c T u₀ v₀ f wv)
    (hpos : uv.1 = wv.1) : uv.2 = wv.2 := by
  have hopen : ∀ s, ∀ hs : s ∈ Set.Ioo (0 : ℝ) T,
      uv.2 ⟨s, ⟨hs.1.le, hs.2.le⟩⟩ = wv.2 ⟨s, ⟨hs.1.le, hs.2.le⟩⟩ := by
    intro s hs
    have hu := huv.2.1 s hs
    have hw := hwv.2.1 s hs
    rw [hpos] at hu
    exact hu.unique hw
  let s : Set (Set.Icc (0 : ℝ) T) := {u | 0 < u.1 ∧ u.1 < T}
  have hclosure : closure s = Set.univ := by
    rw [eq_univ_iff_forall]
    intro u
    rw [closure_subtype]
    have himage : ((↑) : Set.Icc (0 : ℝ) T → ℝ) '' s = Set.Ioo (0 : ℝ) T := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨hu.1, hu.2⟩
      · intro hx
        exact ⟨⟨x, ⟨hx.1.le, hx.2.le⟩⟩, ⟨hx.1, hx.2⟩, rfl⟩
    rw [himage, closure_Ioo hT.ne]
    exact u.2
  have hclosed : IsClosed {u : Set.Icc (0 : ℝ) T | uv.2 u = wv.2 u} :=
    isClosed_eq uv.2.continuous wv.2.continuous
  have hsub : s ⊆ {u | uv.2 u = wv.2 u} := by
    intro u hu
    exact hopen u.1 hu
  have hcl : closure s ⊆ {u | uv.2 u = wv.2 u} := hclosed.closure_subset_iff.mpr hsub
  rw [hclosure] at hcl
  refine DFunLike.ext uv.2 wv.2 fun t => ?_
  exact hcl (mem_univ t)

/-- Energy solutions of one forced wave, with the same data, are equal. -/
private theorem waveEnergySolution_unique {d : ℕ} {c T : ℝ} (hT : 0 < T)
    (u₀ : WavePositionSpace d) (v₀ : WaveVelocitySpace d) {f : ℝ → WaveVelocitySpace d}
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) T))
    (uv wv : C(Set.Icc (0 : ℝ) T, WavePositionSpace d) ×
      C(Set.Icc (0 : ℝ) T, WaveVelocitySpace d))
    (huv : IsWaveEnergySolution c T u₀ v₀ f uv) (hwv : IsWaveEnergySolution c T u₀ v₀ f wv) :
    uv = wv := by
  have hδ0 : (uv.1 - wv.1) ⟨0, ⟨le_rfl, hT.le⟩⟩ = 0 := by
    have hu := (huv.1 ⟨0, ⟨le_rfl, hT.le⟩⟩ rfl).1
    have hw := (hwv.1 ⟨0, ⟨le_rfl, hT.le⟩⟩ rfl).1
    rw [ContinuousMap.sub_apply, hu, hw, sub_self]
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (waveDiffEnergy hT.le c (uv.1 - wv.1)) 0 t := by
    intro t ht
    refine hasDerivAt_waveDiffEnergy hT.le c (uv.1 - wv.1)
      (hasDerivAt_value_clampedDiff hT u₀ v₀ f uv wv huv hwv ht) ?_
    exact waveResidual_sub_apply hT.le u₀ v₀ hf uv wv huv hwv ⟨t, ⟨ht.1.le, ht.2.le⟩⟩
      (clampedPosition hT.le (uv.1 - wv.1) t)
  have hQ := waveDiffEnergy_eq_zero hT c (uv.1 - wv.1) hderiv
    (waveDiffEnergy_zero hT.le c (uv.1 - wv.1) hδ0)
  have hpos : uv.1 = wv.1 := by
    refine DFunLike.ext uv.1 wv.1 fun t => ?_
    have hzero : (uv.1 - wv.1) t = 0 :=
      waveDiffEnergy_position hT.le c (uv.1 - wv.1) t.2 (hQ t.1 t.2)
    rw [ContinuousMap.sub_apply] at hzero
    exact sub_eq_zero.mp hzero
  exact Prod.ext hpos (waveEnergySolution_velocity_eq hT u₀ v₀ f uv wv huv hwv hpos)

/-- The integrated weak velocity equation tested against a smooth compactly supported `φ` is the
vanishing of the residual pairing of `φ`'s Sobolev jet, with the position read at the clamped
time `Set.projIcc 0 T hT s`. -/
theorem wave_inner_residual_eq_zero_iff {d : ℕ} {c T : ℝ} (hT : 0 ≤ T)
    (v₀ : WaveVelocitySpace d) {f : ℝ → WaveVelocitySpace d}
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) T))
    (uv : C(Set.Icc (0 : ℝ) T, WavePositionSpace d) ×
      C(Set.Icc (0 : ℝ) T, WaveVelocitySpace d))
    (t : Set.Icc (0 : ℝ) T) (φ : 𝓓(⊤, ℝ)) :
    ⟪uv.2 t, W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 φ)⟫_ℝ -
        ⟪v₀, W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 φ)⟫_ℝ -
        ⟪∫ s in (0 : ℝ)..t.1, f s,
          W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 φ)⟫_ℝ +
        c ^ 2 * ⟪∫ s in (0 : ℝ)..t.1, W1p.gradient (uv.1 (Set.projIcc 0 T hT s)),
          W1p.gradient (W1p.ofTestFunctionₗ volume ⊤ 2 φ)⟫_ℝ = 0 ↔
      (∫ x, (uv.2 t) x * (φ : EuclideanSpace ℝ (Fin d) → ℝ) x) =
        (∫ x, v₀ x * (φ : EuclideanSpace ℝ (Fin d) → ℝ) x) +
          ∫ s in (0 : ℝ)..t.1, (∫ x, f s x * (φ : EuclideanSpace ℝ (Fin d) → ℝ) x) -
            c ^ 2 * ∫ x, ⟪W1p.gradient (intervalCurveExtend T uv.1 s) x,
              gradient (φ : EuclideanSpace ℝ (Fin d) → ℝ) x⟫_ℝ :=
  wave_test_scalar_zero_iff hT v₀ hf uv t φ

/-- Uniqueness of finite-energy wave solutions: two energy solutions of one forced wave with the
same data on `[0, T]`, `0 < T`, are equal. -/
theorem IsWaveEnergySolution.unique {d : ℕ} {c T : ℝ} {u₀ : WavePositionSpace d}
    {v₀ : WaveVelocitySpace d} {f : ℝ → WaveVelocitySpace d}
    {uv wv : C(Set.Icc (0 : ℝ) T, WavePositionSpace d) ×
      C(Set.Icc (0 : ℝ) T, WaveVelocitySpace d)}
    (huv : IsWaveEnergySolution c T u₀ v₀ f uv) (hwv : IsWaveEnergySolution c T u₀ v₀ f wv)
    (hT : 0 < T) (hf : IntegrableOn f (Set.Icc (0 : ℝ) T)) : uv = wv :=
  waveEnergySolution_unique hT u₀ v₀ hf uv wv huv hwv

end CKMA
