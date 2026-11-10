/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.PDE.Euclidean
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Finite-energy waves and finite propagation

Forced waves with position in TauCeti's first-order Sobolev space and velocity in L².
Solutions are continuous energy-space curves on a compact time interval, with a strong
position derivative and an integrated weak velocity equation. Initial and forcing data
agreeing on a backward cone give spatial almost-everywhere agreement in its later balls.
Sources: GAPS 32.50 and 32.52. Compact curves and Bochner integrals use Mathlib.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped InnerProductSpace

/-- The actual first-order real Sobolev space on all of Euclidean space. -/
abbrev WavePositionSpace (d : ℕ) := TauCeti.W1p (volume : Measure (EuclideanRealSpace d)) ⊤ 2

/-- The scalar velocity space of finite-energy waves. -/
abbrev WaveVelocitySpace (d : ℕ) :=
  Lp ℝ 2 ((volume : Measure (EuclideanRealSpace d)).restrict
    ((⊤ : TopologicalSpace.Opens (EuclideanRealSpace d)) : Set (EuclideanRealSpace d)))

/-- Extend a curve off its time interval by zero. Interior derivative assertions do not depend
on the chosen extension, and uniqueness below is on the actual compact time interval. -/
def intervalCurveExtend {F : Type*} [Zero F] (T : ℝ) (u : Set.Icc (0 : ℝ) T → F) (t : ℝ) : F := by
  classical
  exact if ht : t ∈ Set.Icc (0 : ℝ) T then u ⟨t, ht⟩ else 0

/-- Weak energy solution using continuous `H¹` and `L²` curves, their actual Sobolev gradients,
and an integrated velocity equation. The integral identity excludes singular-in-time
continuous curves with zero derivative almost everywhere. -/
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

/-- **32.50**: existence and uniqueness of the finite-energy forced wave on a compact time interval.
  -/
theorem existsUnique_waveEnergySolution {d : ℕ} {c T : ℝ} (hc : 0 < c) (hT : 0 < T)
    (u₀ : WavePositionSpace d) (v₀ : WaveVelocitySpace d) (f : ℝ → WaveVelocitySpace d)
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) T)) :
    ∃! uv, IsWaveEnergySolution c T u₀ v₀ f uv := by
  sorry

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
