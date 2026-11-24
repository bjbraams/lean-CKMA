/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.PDE.Euclidean
public import TauCeti.Analysis.Sobolev.W1p.Basic

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import TauCeti.Analysis.Semigroups.CauchyProblem.Inhomogeneous
import TauCeti.Analysis.Semigroups.Dissipative.Hilbert
import TauCeti.Analysis.Semigroups.Generation.BoundedPerturbation
import TauCeti.Analysis.Sobolev.W1p.ClosedOperator

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.DenselyOrdered
import TauCeti.Analysis.Sobolev.W1p.Density

/-!
# Finite-energy waves and finite propagation

Forced waves with position in TauCeti's first-order Sobolev space and velocity in L².
Solutions are continuous energy-space curves on a compact time interval, with a strong
position derivative and an integrated weak velocity equation. Initial and forcing data
agreeing on a backward cone give spatial almost-everywhere agreement in its later balls.
Sources: GAPS 32.50 and 32.52. Existence uses Mathlib's Lax–Milgram theorem for the
wave resolvent and TauCeti's semigroup generation, bounded perturbation and Duhamel theorems.

## Main definitions

* `CKMA.WavePositionSpace`, `CKMA.WaveVelocitySpace`: `H¹(ℝ^d)` position and `L²(ℝ^d)` velocity
  spaces for finite-energy waves.
* `CKMA.intervalCurveExtend`: extension by zero of a curve on a compact time interval.
* `CKMA.IsWaveEnergySolution`: weak finite-energy solutions of the forced linear wave equation.

## Main results

* `CKMA.existsUnique_waveEnergySolution` (**32.50**): existence and uniqueness of finite-energy
  wave solutions on a compact time interval.
* `CKMA.wave_finitePropagation` (**32.52**): finite speed of propagation on backward light cones.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory TauCeti Filter Metric Set TopologicalSpace
open TauCeti.Semigroups
open scoped InnerProductSpace Interval Distributions

/-- The actual first-order real Sobolev space on all of Euclidean space. -/
@[expose]
abbrev WavePositionSpace (d : ℕ) := TauCeti.W1p (volume : Measure (EuclideanRealSpace d)) ⊤ 2

/-- The scalar velocity space of finite-energy waves. -/
@[expose]
abbrev WaveVelocitySpace (d : ℕ) :=
  Lp ℝ 2 ((volume : Measure (EuclideanRealSpace d)).restrict
    ((⊤ : TopologicalSpace.Opens (EuclideanRealSpace d)) : Set (EuclideanRealSpace d)))

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
  ∀ ψ : EuclideanRealSpace d → ℝ, IsCompactSmoothTestOn Set.univ ψ →
    ∀ t : Set.Icc (0 : ℝ) T,
      (∫ x, (uv.2 t) x * ψ x) = (∫ x, v₀ x * ψ x) +
        ∫ s in (0 : ℝ)..t.1,
          (∫ x, f s x * ψ x) - c ^ 2 * ∫ x,
            ⟪TauCeti.W1p.gradient (intervalCurveExtend T uv.1 s) x, gradient ψ x⟫_ℝ

/-- The value of the zero extension on its time interval. -/
private theorem intervalCurveExtend_of_mem {F : Type*} [Zero F] {T : ℝ}
    (u : Set.Icc (0 : ℝ) T → F) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    intervalCurveExtend T u t = u ⟨t, ht⟩ := by
  unfold intervalCurveExtend
  simp [ht]

/-- Clamp a real time into the compact interval `[0, T]`. -/
private def timeClamp {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : Set.Icc (0 : ℝ) T :=
  ⟨max 0 (min t T), ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩⟩

/-- Clamping fixes every time already in `[0, T]`. -/
private theorem timeClamp_of_mem {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    timeClamp hT t = ⟨t, ht⟩ := by
  apply Subtype.ext
  simp only [timeClamp]
  rw [min_eq_left ht.2, max_eq_right ht.1]

/-- Clamping is continuous as a map into the time interval. -/
private theorem continuous_timeClamp {T : ℝ} (hT : 0 ≤ T) : Continuous (timeClamp hT) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_const.max
    (continuous_min.comp (continuous_id.prodMk continuous_const))

/-- Read a position curve at the clamped time, so the resulting map is defined on all of `ℝ`. -/
private def clampedPosition {d : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (u : C(Set.Icc (0 : ℝ) T, WavePositionSpace d)) (t : ℝ) : WavePositionSpace d :=
  u (timeClamp hT t)

/-- The clamped position curve is continuous. -/
private theorem continuous_clampedPosition {d : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (u : C(Set.Icc (0 : ℝ) T, WavePositionSpace d)) :
    Continuous (clampedPosition hT u) :=
  u.continuous.comp (continuous_timeClamp hT)

/-- On `[0, T]`, clamping does not change the position. -/
private theorem clampedPosition_of_mem {d : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (u : C(Set.Icc (0 : ℝ) T, WavePositionSpace d)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    clampedPosition hT u t = u ⟨t, ht⟩ := by
  simp [clampedPosition, timeClamp_of_mem hT ht]

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
    ∫ x, v x * (φ : EuclideanRealSpace d → ℝ) x =
      ⟪v, W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 φ)⟫_ℝ := by
  rw [L2.inner_def]
  simp only [Opens.coe_top, Measure.restrict_univ]
  refine integral_congr_ae ?_
  filter_upwards [W1p.value_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ] with x hx
  simp [hx, RCLike.inner_apply, mul_comm]

/-- A compactly supported smooth gradient pairs with an `L²` field through the Sobolev jet. -/
private theorem integral_gradient_inner_test {d : ℕ}
    (g : Lp (EuclideanRealSpace d) 2
      ((volume : Measure (EuclideanRealSpace d)).restrict
        ((⊤ : TopologicalSpace.Opens (EuclideanRealSpace d)) :
          Set (EuclideanRealSpace d))))
    (φ : 𝓓(⊤, ℝ)) :
    ∫ x, ⟪g x, gradient (φ : EuclideanRealSpace d → ℝ) x⟫_ℝ =
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
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
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
  unfold waveResidualCLM
  rw [waveCLM_sub_sub_add_apply]
  rw [valuePairingCLM_apply]
  rw [valuePairingCLM_apply]
  rw [valuePairingCLM_apply]
  rw [gradientAccumCLM_apply]

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
      (∫ x, (uv.2 t) x * (φ : EuclideanRealSpace d → ℝ) x) =
        (∫ x, v₀ x * (φ : EuclideanRealSpace d → ℝ) x) +
          ∫ s in (0 : ℝ)..t.1, (∫ x, f s x * (φ : EuclideanRealSpace d → ℝ) x) -
            c ^ 2 * ∫ x, ⟪W1p.gradient (intervalCurveExtend T uv.1 s) x,
              gradient (φ : EuclideanRealSpace d → ℝ) x⟫_ℝ := by
  set w : WavePositionSpace d := W1p.ofTestFunctionₗ volume ⊤ 2 φ with hw
  have hvel := integral_velocity_mul_test (uv.2 t) φ
  have hv0 := integral_velocity_mul_test v₀ φ
  have hforce_pt : ∀ s, ∫ x, f s x * (φ : EuclideanRealSpace d → ℝ) x =
      ⟪f s, W1p.value w⟫_ℝ :=
    fun s => integral_velocity_mul_test (f s) φ
  have hintf : IntervalIntegrable f volume 0 t.1 :=
    intervalIntegrable_force t.2.1 t.2.2 hf
  have hintF : IntervalIntegrable (fun s => ⟪f s, W1p.value w⟫_ℝ) volume 0 t.1 := by
    refine (wave_intervalIntegrable_clm (innerSL ℝ (W1p.value w)) hintf).congr ?_
    intro _ _
    dsimp
    rw [real_inner_comm]
  let Fs : ℝ → ℝ := fun s => ∫ x, f s x * (φ : EuclideanRealSpace d → ℝ) x
  let Gs : ℝ → ℝ := fun s => ∫ x,
    ⟪W1p.gradient (intervalCurveExtend T uv.1 s) x, gradient (φ : EuclideanRealSpace d → ℝ) x⟫_ℝ
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
  change _ ↔ (∫ x, (uv.2 t) x * (φ : EuclideanRealSpace d → ℝ) x) =
    (∫ x, v₀ x * (φ : EuclideanRealSpace d → ℝ) x) + ∫ s in (0 : ℝ)..t.1, Fs s - c ^ 2 * Gs s
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
  have hψ : IsCompactSmoothTestOn Set.univ (φ : EuclideanRealSpace d → ℝ) :=
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
    (Omega := (⊤ : TopologicalSpace.Opens (EuclideanRealSpace d))) (p := 2) hclosed htest
  have htop := w1p0Submodule_top_eq_top (mu := volume)
    (E := EuclideanRealSpace d) (p := 2) (hp := by simp)
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

section WaveSkew

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The wave phase space uses the Hilbert product of position and velocity. -/
private abbrev WavePhase (V H : Type*) := WithLp 2 (V × H)

variable (J : V →L[ℝ] H)

/-- The graph of the skew wave block for the inhomogeneous Sobolev inner product. -/
private def waveSkewGraph : Submodule ℝ (WavePhase V H × WavePhase V H) where
  carrier := {p | J p.2.fst = p.1.snd ∧
    ∀ z : V, ⟪p.2.snd, J z⟫_ℝ = -⟪p.1.fst, z⟫_ℝ}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    obtain ⟨hp₁, hp₂⟩ := hp
    obtain ⟨hq₁, hq₂⟩ := hq
    refine ⟨?_, fun z => ?_⟩
    · simp only [Prod.fst_add, Prod.snd_add, WithLp.add_fst, WithLp.add_snd, map_add, hp₁, hq₁]
    · simp only [Prod.fst_add, Prod.snd_add, WithLp.add_fst, WithLp.add_snd, inner_add_left,
        hp₂ z, hq₂ z, neg_add]
  smul_mem' := by
    intro a p hp
    obtain ⟨hp₁, hp₂⟩ := hp
    refine ⟨?_, fun z => ?_⟩
    · simp only [Prod.smul_fst, Prod.smul_snd, WithLp.smul_fst, WithLp.smul_snd, map_smul, hp₁]
    · simp only [Prod.smul_fst, Prod.smul_snd, WithLp.smul_fst, WithLp.smul_snd,
        real_inner_smul_left, hp₂ z, mul_neg]

/-- The skew wave block on the product of the inhomogeneous Sobolev space and L². -/
private def waveSkew : WavePhase V H →ₗ.[ℝ] WavePhase V H :=
  (waveSkewGraph J).toLinearPMap

omit [CompleteSpace V] [CompleteSpace H] in
/-- The two component equations characterize membership in the skew wave graph. -/
private theorem mem_waveSkew_graph_iff (hJ : Function.Injective J) (hdense : DenseRange J)
    {x y : WavePhase V H} :
    (x, y) ∈ (waveSkew J).graph ↔ J y.fst = x.snd ∧
      ∀ z : V, ⟪y.snd, J z⟫_ℝ = -⟪x.fst, z⟫_ℝ := by
  rw [waveSkew, Submodule.toLinearPMap_graph_eq]
  · rfl
  · rintro ⟨x, y⟩ ⟨hy₁, hy₂⟩ rfl
    have hy₁' : y.fst = 0 := hJ (by simpa only [map_zero, WithLp.zero_snd] using hy₁)
    have hy₂' : y.snd = 0 := hdense.eq_zero_of_inner_left ℝ (by
      simpa only [WithLp.zero_fst, inner_zero_left, neg_zero] using hy₂)
    exact (WithLp.equiv 2 _).injective (Prod.ext hy₁' hy₂')

omit [CompleteSpace V] [CompleteSpace H] in
/-- The skew wave generator has vanishing real quadratic form. -/
private theorem inner_waveSkew_self (hJ : Function.Injective J) (hdense : DenseRange J)
    (x : (waveSkew J).domain) :
    ⟪waveSkew J x, (x : WavePhase V H)⟫_ℝ = 0 := by
  obtain ⟨hx, hy⟩ := (mem_waveSkew_graph_iff J hJ hdense).1 ((waveSkew J).mem_graph x)
  have hpair := hy ((waveSkew J x).fst)
  rw [hx, real_inner_comm (waveSkew J x).fst] at hpair
  simp only [WithLp.fst, WithLp.snd] at hpair
  simp only [WithLp.prod_inner_apply, hpair, add_neg_cancel]

/-- The coercive operator for the unit resolvent of the skew wave block. -/
private def waveResolventOp : V →L[ℝ] V :=
  1 + J.adjoint.comp J

/-- The resolvent operator is coercive by positivity of the L² value pairing. -/
private theorem waveResolventOp_coercive :
    IsCoercive ((innerSL ℝ).comp (waveResolventOp J)) := by
  refine ⟨1, zero_lt_one, fun z => ?_⟩
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, waveResolventOp,
    add_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply,
    inner_add_left, ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg ‖J z‖]

/-- Lax–Milgram gives the unit resolvent of the skew wave block. -/
private theorem waveSkew_surjective (hJ : Function.Injective J) (hdense : DenseRange J) :
    Function.Surjective fun x : (waveSkew J).domain => (x : WavePhase V H) - waveSkew J x := by
  intro y
  let w := (waveResolventOp_coercive J).continuousLinearEquivOfBilin.symm
    (J.adjoint y.snd - y.fst)
  have hw (z : V) :
      ⟪J w - y.snd, J z⟫_ℝ = -⟪y.fst + w, z⟫_ℝ := by
    have heq := (waveResolventOp_coercive J).continuousLinearEquivOfBilin_apply w z
    have hE : (waveResolventOp_coercive J).continuousLinearEquivOfBilin w =
        J.adjoint y.snd - y.fst :=
      (waveResolventOp_coercive J).continuousLinearEquivOfBilin.apply_symm_apply _
    rw [hE, ContinuousLinearMap.comp_apply, innerSL_apply_apply, waveResolventOp,
      add_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply,
      inner_add_left, inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left] at heq
    rw [inner_sub_left, inner_add_left]
    linarith
  let x : WavePhase V H := WithLp.toLp 2 (y.fst + w, J w)
  let z : WavePhase V H := WithLp.toLp 2 (w, J w - y.snd)
  have hg : (x, z) ∈ (waveSkew J).graph := (mem_waveSkew_graph_iff J hJ hdense).mpr ⟨rfl, hw⟩
  obtain ⟨u, hu₁, hu₂⟩ := (LinearPMap.mem_graph_iff _).mp hg
  refine ⟨u, ?_⟩
  dsimp only
  rw [hu₁, hu₂]
  apply (WithLp.equiv 2 _).injective
  exact Prod.ext (by simp [x, z]) (by simp [x, z])

/-- The skew wave block has dense domain by its vanishing quadratic form and unit resolvent. -/
private theorem waveSkew_dense (hJ : Function.Injective J) (hdense : DenseRange J) :
    Dense ((waveSkew J).domain : Set (WavePhase V H)) := by
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
    ← Submodule.orthogonal_orthogonal_eq_closure]
  suffices ((waveSkew J).domain)ᗮ = ⊥ by
    rw [this, Submodule.bot_orthogonal_eq_top, Submodule.top_coe]
  refine le_antisymm (fun y hy => ?_) bot_le
  obtain ⟨x, hx⟩ := waveSkew_surjective J hJ hdense y
  have hinner := Submodule.inner_right_of_mem_orthogonal x.property hy
  have horth := inner_waveSkew_self J hJ hdense x
  rw [real_inner_comm] at horth
  rw [← hx, inner_sub_right, horth, sub_zero, inner_self_eq_zero] at hinner
  have hx0 : x = 0 := Subtype.ext hinner
  exact (Submodule.mem_bot ℝ).mpr (by simpa [hx0] using hx.symm)

/-- Positive multiples of the skew wave block are maximally dissipative. -/
private theorem waveSkew_isMDissipative (hJ : Function.Injective J) (hdense : DenseRange J)
    {c : ℝ} (hc : 0 < c) :
    IsMDissipative (c • waveSkew J) := by
  have hdis : IsDissipative (waveSkew J) := (isDissipative_iff_real_inner_nonpos _).2
    fun x => (inner_waveSkew_self J hJ hdense x).le
  apply (hdis.smul hc.le).isMDissipative hc
  intro y
  obtain ⟨x, hx⟩ := waveSkew_surjective J hJ hdense (c⁻¹ • y)
  refine ⟨x, ?_⟩
  have he : c • ((x : WavePhase V H) - waveSkew J x) = y :=
    (congrArg (c • ·) hx).trans (smul_inv_smul₀ hc.ne' _)
  simpa only [smul_sub, LinearPMap.smul_apply] using he

/-- The velocity inclusion in the Hilbert product. -/
private def wavePhaseInr : H →L[ℝ] WavePhase V H :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ V H).symm.toContinuousLinearMap.comp
    (LinearIsometry.inr ℝ V H).toContinuousLinearMap

omit [CompleteSpace V] [CompleteSpace H] in
/-- The velocity inclusion has zero position and the given velocity. -/
private theorem wavePhaseInr_apply (v : H) :
    (wavePhaseInr : H →L[ℝ] WavePhase V H) v = WithLp.toLp 2 (0, v) := rfl

/-- The mass correction cancels the value term in the inhomogeneous Sobolev inner product. -/
private def waveMassCorrection (c : ℝ) : WavePhase V H →L[ℝ] WavePhase V H :=
  c • (wavePhaseInr.comp (J.comp (WithLp.fstL 2 ℝ V H)))

/-- The Hilbert product trajectory satisfies its two integrated component equations. -/
private theorem exists_wavePhaseTrajectory (hJ : Function.Injective J) (hdense : DenseRange J)
    {c : ℝ} (hc : 0 < c) (x₀ : WavePhase V H) {f : ℝ → H} (hf : Integrable f) :
    ∃ Q : C(ℝ, WavePhase V H), Q 0 = x₀ ∧
      ∀ t : ℝ, 0 ≤ t →
        J (Q t).fst = J x₀.fst + c • (∫ s in Ioc 0 t, (Q s).snd) ∧
        ∀ w : V,
          ⟪(Q t).snd, J w⟫_ℝ = ⟪x₀.snd, J w⟫_ℝ + ⟪∫ s in Ioc 0 t, f s, J w⟫_ℝ +
            c * (⟪J (∫ s in Ioc 0 t, (Q s).fst), J w⟫_ℝ -
              ⟪∫ s in Ioc 0 t, (Q s).fst, w⟫_ℝ) := by
  let B := waveMassCorrection J c
  have hD : Dense ((c • waveSkew J).domain : Set (WavePhase V H)) := by
    rw [LinearPMap.smul_domain]
    exact waveSkew_dense J hJ hdense
  obtain ⟨S, hgen, _⟩ :=
    (waveSkew_isMDissipative J hJ hdense hc).exists_stronglyContinuousSemigroup_generator_eq_vadd
      hD B
  let L : H →L[ℝ] WavePhase V H := wavePhaseInr
  let F : ℝ → WavePhase V H := fun t => L (f t)
  have hF : Integrable F := L.integrable_comp hf
  let q : ℝ → WavePhase V H := fun t => S.realOperator t x₀ + S.duhamel F t
  have hq := S.isForcedMildSolution_realOperator_add_duhamel
    hF.integrableOn.locallyIntegrableOn x₀
  let Q : C(ℝ, WavePhase V H) :=
    ⟨fun t => q (max 0 t), hq.continuousOn.comp_continuous
      (continuous_const.max continuous_id) (fun t => Set.mem_Ici.2 (le_max_left (0 : ℝ) t))⟩
  have hQ : IsForcedMildSolution S.generator F x₀ Q :=
    hq.congr fun t ht => congrArg q (max_eq_right ht).symm
  rw [hgen] at hQ
  refine ⟨Q, hQ.apply_zero, fun t ht => ?_⟩
  let z : (waveSkew J).domain := ⟨_, hQ.integral_mem_domain ht⟩
  have hz : B (z : WavePhase V H) + c • waveSkew J z =
      Q t - x₀ - ∫ s in Ioc 0 t, F s := hQ.map_integral_eq_sub ht
  obtain ⟨hpos, hvel⟩ := (mem_waveSkew_graph_iff J hJ hdense).1 ((waveSkew J).mem_graph z)
  have hint : IntegrableOn Q (Ioc 0 t) := (Q.continuous.intervalIntegrable 0 t).1
  have hfst : (z : WavePhase V H).fst = ∫ s in Ioc 0 t, (Q s).fst :=
    ((WithLp.fstL 2 ℝ V H).integral_comp_comm hint).symm
  have hsnd : (z : WavePhase V H).snd = ∫ s in Ioc 0 t, (Q s).snd :=
    ((WithLp.sndL 2 ℝ V H).integral_comp_comm hint).symm
  have hFint : (∫ s in Ioc 0 t, F s) = WithLp.toLp 2 (0, ∫ s in Ioc 0 t, f s) := by
    exact (L.integral_comp_comm hf.integrableOn).trans (wavePhaseInr_apply _)
  have hB : B z = WithLp.toLp 2 (0, c • J (z : WavePhase V H).fst) := by
    dsimp only [B]
    rw [waveMassCorrection, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, WithLp.fstL_apply, wavePhaseInr_apply]
    exact (WithLp.equiv 2 _).injective (Prod.ext (smul_zero c) rfl)
  constructor
  · have h := congrArg (fun a : WavePhase V H => J a.fst) hz
    simp only [hB, hFint, WithLp.add_fst, WithLp.sub_fst, WithLp.smul_fst, WithLp.toLp_fst,
      zero_add, sub_zero, map_smul, map_sub, hpos, hsnd] at h
    exact (sub_eq_iff_eq_add.mp h.symm).trans (add_comm _ _)
  · intro w
    have h := congrArg (fun a : WavePhase V H => ⟪a.snd, J w⟫_ℝ) hz
    simp only [hB, hFint, WithLp.add_snd, WithLp.sub_snd, WithLp.smul_snd, WithLp.toLp_snd,
      inner_add_left, inner_sub_left, real_inner_smul_left, hvel, hfst] at h
    linarith

end WaveSkew


/-- The Sobolev value map is injective and has dense range in the velocity space. -/
private theorem wave_valueL_injective_dense (d : ℕ) :
    Function.Injective (W1p.valueL : WavePositionSpace d →L[ℝ] WaveVelocitySpace d) ∧
      DenseRange (W1p.valueL : WavePositionSpace d →L[ℝ] WaveVelocitySpace d) := by
  refine ⟨fun _ _ h => W1p.ext_value (by simpa only [W1p.valueL_apply] using h), ?_⟩
  have h := dense_domain_weakGradientPMap (mu := (volume : Measure (EuclideanRealSpace d)))
    (Omega := ⊤)
  refine h.mono ?_
  intro f hf
  obtain ⟨u, hu⟩ := mem_domain_weakGradientPMap_iff.mp hf
  exact ⟨u, (W1p.valueL_apply u).trans hu⟩

/-- The Sobolev inner product splits into the value and gradient pairings. -/
private theorem wave_inner_position {d : ℕ} (u w : WavePositionSpace d) :
    ⟪u, w⟫_ℝ = ⟪W1p.valueL u, W1p.valueL w⟫_ℝ + ⟪W1p.gradientL u, W1p.gradientL w⟫_ℝ := by
  simp only [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    ← sq, W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq, W1p.valueL_apply,
    W1p.gradientL_apply, W1p.value_sub, W1p.gradient_sub]
  ring

set_option maxHeartbeats 1400000 in
/-- Integrable forcing produces an energy solution via the perturbed skew wave semigroup. -/
private theorem exists_waveEnergySolution {d : ℕ} {c T : ℝ} (hc : 0 < c) (hT : 0 < T)
    (u₀ : WavePositionSpace d) (v₀ : WaveVelocitySpace d) {f : ℝ → WaveVelocitySpace d}
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) T)) :
    ∃ uv, IsWaveEnergySolution c T u₀ v₀ f uv := by
  let F := (Icc (0 : ℝ) T).indicator f
  have hF : Integrable F := (integrable_indicator_iff measurableSet_Icc).2 hf
  let J : WavePositionSpace d →L[ℝ] WaveVelocitySpace d := W1p.valueL
  obtain ⟨hJ, hJdense⟩ := wave_valueL_injective_dense d
  obtain ⟨Q, hQ0, hQ⟩ := exists_wavePhaseTrajectory J hJ hJdense hc
    (WithLp.toLp 2 (c • u₀, v₀)) hF
  let u : ℝ → WavePositionSpace d := fun s => c⁻¹ • (Q s).fst
  let v : ℝ → WaveVelocitySpace d := fun s => (Q s).snd
  have hq₁ : Continuous (fun s : ℝ => (Q s).fst) :=
    (WithLp.continuous_fst 2 _ _).comp Q.continuous
  have hucont : Continuous u := hq₁.const_smul c⁻¹
  have hvcont : Continuous v := (WithLp.continuous_snd 2 _ _).comp Q.continuous
  let up : C(Icc (0 : ℝ) T, WavePositionSpace d) :=
    ⟨fun t => u t.1, hucont.comp continuous_subtype_val⟩
  let vp : C(Icc (0 : ℝ) T, WaveVelocitySpace d) :=
    ⟨fun t => v t.1, hvcont.comp continuous_subtype_val⟩
  refine ⟨(up, vp), ?_, ?_, ?_⟩
  · intro t ht
    simp only [up, vp, ContinuousMap.coe_mk, u, v, ht, hQ0, WithLp.toLp_fst, WithLp.toLp_snd,
      inv_smul_smul₀ hc.ne', and_self]
  · intro t ht
    have hD := ((hvcont.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add (W1p.value u₀))
    refine hD.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
    rw [intervalCurveExtend_of_mem _ hsT]
    have h₁ : J (Q s).fst = c • J u₀ + c • (∫ τ in Ioc 0 s, v τ) := by
      simpa only [WithLp.toLp_fst, map_smul, v] using (hQ s hs.1.le).1
    have h₂ : J (u s) = J u₀ + ∫ τ in Ioc 0 s, v τ := by
      dsimp only [u]
      rw [map_smul, h₁, smul_add, inv_smul_smul₀ hc.ne', inv_smul_smul₀ hc.ne']
    simpa only [← intervalIntegral.integral_of_le hs.1.le, up, ContinuousMap.coe_mk,
      J, W1p.valueL_apply] using h₂
  · intro ψ hψ t
    let φ : 𝓓(⊤, ℝ) := ⟨ψ, hψ.1, hψ.2.1, by simp⟩
    have hintf : (∫ s in Ioc 0 t.1, F s) = ∫ s in (0 : ℝ)..t.1, f s := by
      rw [intervalIntegral.integral_of_le t.2.1]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.trans t.2.2⟩
      exact Set.indicator_of_mem hsT f
    let G := W1p.gradientL (mu := (volume : Measure (EuclideanRealSpace d))) (Omega := ⊤) (p := 2)
    have hGrad :
        (∫ s in (0 : ℝ)..t.1, W1p.gradient (clampedPosition hT.le up s)) =
          c⁻¹ • G (∫ s in Ioc 0 t.1, (Q s).fst) := by
      have hcongr : (∫ s in (0 : ℝ)..t.1, W1p.gradient (clampedPosition hT.le up s)) =
          ∫ s in (0 : ℝ)..t.1, c⁻¹ • G ((Q s).fst) := by
        refine intervalIntegral.integral_congr ?_
        rw [uIcc_of_le t.2.1]
        intro s hs
        have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans t.2.2⟩
        dsimp only
        rw [clampedPosition_of_mem hT.le up hsT, ← W1p.gradientL_apply]
        exact G.map_smul c⁻¹ ((Q s).fst)
      rw [hcongr, intervalIntegral.integral_smul,
        G.intervalIntegral_comp_comm (hq₁.intervalIntegrable 0 t.1),
        intervalIntegral.integral_of_le t.2.1]
    let w : WavePositionSpace d := W1p.ofTestFunctionₗ volume ⊤ 2 φ
    have h₂ := (hQ t.1 t.2.1).2 w
    simp only [WithLp.toLp_snd, hintf, wave_inner_position] at h₂
    have hpair :
        ⟪v t.1, W1p.value w⟫_ℝ - ⟪v₀, W1p.value w⟫_ℝ -
            ⟪∫ s in (0 : ℝ)..t.1, f s, W1p.value w⟫_ℝ +
            c ^ 2 * ⟪∫ s in (0 : ℝ)..t.1, W1p.gradient (clampedPosition hT.le up s),
              W1p.gradient w⟫_ℝ = 0 := by
      rw [hGrad, real_inner_smul_left, ← W1p.gradientL_apply w]
      have hc' : c ^ 2 * c⁻¹ = c := by field_simp
      rw [← mul_assoc, hc']
      simp only [v, W1p.valueL_apply, J, G] at h₂ ⊢
      linarith
    exact (wave_test_scalar_zero_iff hT.le v₀ hf (up, vp) t φ).1 hpair

/-- **32.50**: existence and uniqueness of the finite-energy forced wave on a compact time interval.
  -/
theorem existsUnique_waveEnergySolution {d : ℕ} {c T : ℝ} (hc : 0 < c) (hT : 0 < T)
    (u₀ : WavePositionSpace d) (v₀ : WaveVelocitySpace d) (f : ℝ → WaveVelocitySpace d)
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) T)) :
    ∃! uv, IsWaveEnergySolution c T u₀ v₀ f uv := by
  obtain ⟨uv, huv⟩ := exists_waveEnergySolution hc hT u₀ v₀ hf
  refine ⟨uv, huv, ?_⟩
  intro wv hwv
  exact waveEnergySolution_unique hT u₀ v₀ hf wv uv hwv huv

set_option warn.sorry false in
/-- **32.52**: data agreeing on an initial ball and forcing agreeing in its shrinking
backward cone give position representatives agreeing in every later shrinking ball.
The identified quantity is `TauCeti.W1p.value` of the position component. All spatial
identities are almost everywhere, as required for energy-space data. -/
theorem wave_finitePropagation {d : ℕ} {c T R : ℝ} (hc : 0 < c) (hT : 0 < T) (hR : 0 < R)
    (x₀ : EuclideanRealSpace d) (u₀ u₁ : WavePositionSpace d)
    (v₀ v₁ : WaveVelocitySpace d) (f g : ℝ → WaveVelocitySpace d)
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) T)) (hg : IntegrableOn g (Set.Icc (0 : ℝ) T))
    (uv wv : C(Set.Icc (0 : ℝ) T, WavePositionSpace d) ×
      C(Set.Icc (0 : ℝ) T, WaveVelocitySpace d))
    (huv : IsWaveEnergySolution c T u₀ v₀ f uv) (hwv : IsWaveEnergySolution c T u₁ v₁ g wv)
    (hpos : TauCeti.W1p.value u₀ =ᵐ[volume.restrict (Metric.ball x₀ R)] TauCeti.W1p.value u₁)
    (hvel : v₀ =ᵐ[volume.restrict (Metric.ball x₀ R)] v₁)
    (hforce : ∀ᵐ s ∂volume.restrict (Set.Icc (0 : ℝ) T),
      f s =ᵐ[volume.restrict (Metric.ball x₀ (R - c * s))] g s) :
    ∀ t : Set.Icc (0 : ℝ) T, c * t.1 < R →
      TauCeti.W1p.value (uv.1 t) =ᵐ[volume.restrict (Metric.ball x₀ (R - c * t.1))]
        TauCeti.W1p.value (wv.1 t) := by
  sorry

end CKMA
