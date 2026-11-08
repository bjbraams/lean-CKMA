/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.PDE.Euclidean
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Interior elliptic estimates and weak p-harmonic regularity

Extended supremum and Hölder gauges, weak divergence-form equations and interior
Meyers, ABP, Krylov–Safonov, Schauder and Hessian `L^p` estimates. Lower-order coefficients
are included in the classical estimates. Weak p-harmonicity uses TauCeti's actual
`W1p` gradient and yields local regular representatives and a Harnack inequality.
Sources: GAPS 33.9, 33.14–33.16, 33.18 and 33.34.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped ENNReal InnerProductSpace

/-- Supremum gauge on a set, allowing infinite values. -/
def uniformGaugeOn {X F : Type*} [NormedAddCommGroup F] (f : X → F) (Ω : Set X) : ℝ≥0∞ :=
  ⨆ x ∈ Ω, ENNReal.ofReal ‖f x‖

/-- Hölder seminorm gauge using all distinct pairs; the diagonal contributes zero. -/
def holderSeminormOn {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]
    (α : ℝ) (f : X → F) (Ω : Set X) : ℝ≥0∞ :=
  ⨆ x ∈ Ω, ⨆ y ∈ Ω, ENNReal.ofReal ‖f x - f y‖ / ENNReal.ofReal (dist x y ^ α)

/-- Full zeroth-order Hölder gauge. -/
def holderGaugeOn {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]
    (α : ℝ) (f : X → F) (Ω : Set X) : ℝ≥0∞ :=
  uniformGaugeOn f Ω + holderSeminormOn α f Ω

/-- Full `C^{2,α}` gauge of a scalar function on a Euclidean set. -/
def cTwoHolderGauge {d : ℕ} (α : ℝ) (u : EuclideanRealSpace d → ℝ)
    (Ω : Set (EuclideanRealSpace d)) : ℝ≥0∞ :=
  uniformGaugeOn u Ω + uniformGaugeOn (fderiv ℝ u) Ω +
    holderGaugeOn α (fderiv ℝ (fderiv ℝ u)) Ω

/-- Weak divergence-form equation `-div(A grad u) = div F`, tested against smooth compact tests. -/
def IsWeakEllipticSolution {d : ℕ} (Ω : TopologicalSpace.Opens (EuclideanRealSpace d))
    (A : EuclideanRealSpace d → EuclideanRealSpace d →L[ℝ] EuclideanRealSpace d)
    (F : EuclideanRealSpace d → EuclideanRealSpace d) (u : TauCeti.W1p volume Ω 2) : Prop :=
  ∀ φ : EuclideanRealSpace d → ℝ, IsCompactSmoothTestOn Ω φ →
    ∫ x in Ω, ⟪A x ((TauCeti.W1p.gradient u) x) + F x, gradient φ x⟫_ℝ = 0

/-- **33.9**: a local Meyers estimate, including divergence-form inhomogeneity. -/
theorem meyers_higherIntegrability {d : ℕ} (hd : 0 < d) {ell Λ : ℝ}
    (hell : 0 < ell) (hΛ : ell ≤ Λ) : ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
    ∀ (A : EuclideanRealSpace d → EuclideanRealSpace d →L[ℝ] EuclideanRealSpace d)
      (F : EuclideanRealSpace d → EuclideanRealSpace d)
      (u : TauCeti.W1p volume (euclideanOpenBall d 2) 2),
      Measurable A → IsUniformlyEllipticOn A ell Λ (Metric.ball 0 2) →
      MemLp F (ENNReal.ofReal (2 + ε)) (volume.restrict (Metric.ball 0 2)) →
      IsWeakEllipticSolution (euclideanOpenBall d 2) A F u →
      MemLp ((TauCeti.W1p.gradient u) : EuclideanRealSpace d → EuclideanRealSpace d)
        (ENNReal.ofReal (2 + ε)) (volume.restrict (Metric.ball 0 1)) ∧
      eLpNorm (TauCeti.W1p.gradient u) (ENNReal.ofReal (2 + ε)) (volume.restrict (Metric.ball 0 1))
        ≤
        ENNReal.ofReal C * (eLpNorm (TauCeti.W1p.gradient u) 2 (volume.restrict (Metric.ball 0 2)) +
          eLpNorm F (ENNReal.ofReal (2 + ε)) (volume.restrict (Metric.ball 0 2))) := by
  sorry

/-- **33.14**, ABP for classical functions. The strong `W^{2,d}` interface remains separate.
Extended norm values make the estimate meaningful without totalizing an infinite source norm. -/
theorem abp_classical {d : ℕ} (hd : 0 < d) {ell Λ : ℝ}
    (hell : 0 < ell) (hΛ : ell ≤ Λ) : ∃ C : ℝ, 0 < C ∧
    ∀ (Ω : Set (EuclideanRealSpace d)) (u : EuclideanRealSpace d → ℝ)
      (A : EuclideanRealSpace d → EuclideanRealSpace d →L[ℝ] EuclideanRealSpace d),
      IsOpen Ω → Ω.Nonempty → Bornology.IsBounded Ω → ContinuousOn u (closure Ω) →
      ContDiffOn ℝ 2 u Ω → Measurable A → IsUniformlyEllipticOn A ell Λ Ω →
      ENNReal.ofReal (sSup (u '' Ω)) ≤
        ENNReal.ofReal (sSup ((fun x ↦ max (u x) 0) '' frontier Ω)) +
        ENNReal.ofReal (C * Metric.diam Ω) *
          eLpNorm (fun x ↦ max (-(nondivergencePrincipal A u x)) 0) (d : ℝ≥0∞)
            (volume.restrict Ω) := by
  sorry

/-- **33.15**, Harnack and Hölder estimates in the classical-solution subcase. -/
theorem krylov_safonov_classical {d : ℕ} (hd : 0 < d) {ell Λ : ℝ}
    (hell : 0 < ell) (hΛ : ell ≤ Λ) : ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧
    ∀ (A : EuclideanRealSpace d → EuclideanRealSpace d →L[ℝ] EuclideanRealSpace d)
      (u : EuclideanRealSpace d → ℝ),
      Measurable A → IsUniformlyEllipticOn A ell Λ (Metric.ball 0 2) →
      ContDiffOn ℝ 2 u (Metric.ball 0 2) →
      (∀ x ∈ Metric.ball 0 2, nondivergencePrincipal A u x = 0) →
      holderSeminormOn α u (Metric.ball 0 1) ≤ ENNReal.ofReal C * uniformGaugeOn u (Metric.ball 0 2)
        ∧
      ((∀ x ∈ Metric.ball 0 2, 0 ≤ u x) →
        sSup (u '' Metric.ball 0 1) ≤ C * sInf (u '' Metric.ball 0 1)) := by
  sorry

/-- **33.16**: localized variable-coefficient Schauder a priori estimate including lower orders. -/
theorem interior_schauder {d : ℕ} (hd : 0 < d) {α ell Λ : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (A : EuclideanRealSpace d → EuclideanRealSpace d →L[ℝ] EuclideanRealSpace d)
    (b : EuclideanRealSpace d → EuclideanRealSpace d) (c : EuclideanRealSpace d → ℝ)
    (hA : IsUniformlyEllipticOn A ell Λ (Metric.ball 0 2))
    (hAH : holderGaugeOn α A (Metric.ball 0 2) ≠ ∞)
    (hbH : holderGaugeOn α b (Metric.ball 0 2) ≠ ∞)
    (hcH : holderGaugeOn α c (Metric.ball 0 2) ≠ ∞) :
    ∃ C : ℝ, 0 < C ∧ ∀ u f : EuclideanRealSpace d → ℝ,
      ContDiffOn ℝ 2 u (Metric.ball 0 2) → holderGaugeOn α f (Metric.ball 0 2) ≠ ∞ →
      (∀ x ∈ Metric.ball 0 2, linearEllipticExpression A b c u x = f x) →
      cTwoHolderGauge α u (Metric.ball 0 1) ≤
        ENNReal.ofReal C * (uniformGaugeOn u (Metric.ball 0 2) + holderGaugeOn α f (Metric.ball 0
          2)) := by
  sorry

/-- **33.18**, classical a priori `W^{2,p}` estimate. The full strong-solution API is separate. -/
theorem interior_hessian_Lp {d : ℕ} (hd : 0 < d) {p : ℝ} (hp : 1 < p)
    {ell Λ : ℝ}
    (A : EuclideanRealSpace d → EuclideanRealSpace d →L[ℝ] EuclideanRealSpace d)
    (b : EuclideanRealSpace d → EuclideanRealSpace d) (c : EuclideanRealSpace d → ℝ)
    (hA : IsUniformlyEllipticOn A ell Λ (Metric.ball 0 2))
    (hAc : ContinuousOn A (Metric.ball 0 2))
    (hb : Measurable b) (hc : Measurable c)
    (hbb : uniformGaugeOn b (Metric.ball 0 2) ≠ ∞)
    (hcb : uniformGaugeOn c (Metric.ball 0 2) ≠ ∞) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : EuclideanRealSpace d → ℝ,
      ContDiffOn ℝ 2 u (Metric.ball 0 2) →
      eLpNorm (fderiv ℝ (fderiv ℝ u)) (ENNReal.ofReal p) (volume.restrict (Metric.ball 0 1)) ≤
        ENNReal.ofReal C * (eLpNorm (linearEllipticExpression A b c u) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball 0 2)) +
          eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball 0 2))) := by
  sorry

/-- Weak `p`-harmonicity using the actual weak-gradient component of `W^{1,p}`. -/
def IsWeakPHarmonic {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (Ω : TopologicalSpace.Opens (EuclideanRealSpace d)) (u : TauCeti.W1p volume Ω p) : Prop :=
  ∀ φ : EuclideanRealSpace d → ℝ, IsCompactSmoothTestOn Ω φ →
    ∫ x in Ω, ‖(TauCeti.W1p.gradient u) x‖ ^ (p.toReal - 2) * ⟪(TauCeti.W1p.gradient u) x, gradient
      φ x⟫_ℝ = 0

/-- **33.34**: local `C^{1,α}` representatives and the nonnegative Harnack inequality. -/
theorem weakPHarmonic_regular {d : ℕ} (hd : 0 < d) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hp_top : p < ∞) : ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧
    ∀ u : TauCeti.W1p volume (euclideanOpenBall d 2) p,
      IsWeakPHarmonic (euclideanOpenBall d 2) u →
      ∃ v : EuclideanRealSpace d → ℝ,
        v =ᵐ[volume.restrict (Metric.ball 0 1)] (TauCeti.W1p.value u) ∧ ContDiffOn ℝ 1 v
          (Metric.ball 0 1) ∧
        holderSeminormOn α (fderiv ℝ v) (Metric.ball 0 1) ≠ ∞ ∧
        ((∀ᵐ x ∂volume.restrict (Metric.ball 0 2), 0 ≤ (TauCeti.W1p.value u) x) →
          sSup (v '' Metric.ball 0 1) ≤ C * sInf (v '' Metric.ball 0 1)) := by
  sorry

end CKMA
