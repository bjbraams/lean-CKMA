/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.PDE.Euclidean
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Global symbols, left quantization and Sobolev estimates

Global scalar symbols of class `S^m_{1,0}`, mixed spatial/frequency derivatives and
left quantization in the physical `exp(-i x·xi)` Fourier convention. The statements
include the Calderón–Vaillancourt bound, Sobolev mapping on Schwartz inputs and sharp
Gårding. Fourier inversion uses `(2*pi)^(-d)`; squared Sobolev energies retain extended
values. Derivatives, Schwartz maps and integration reuse Mathlib.
Sources: GAPS 30.27, 30.28 and 30.31.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped ENNReal ComplexConjugate

/-- Mixed derivatives of a symbol, differentiated in frequency first and then in space. -/
def symbolMixedDerivative {d : ℕ} (a : EuclideanRealSpace d × EuclideanRealSpace d → ℂ)
    (k l : ℕ) (x ξ : EuclideanRealSpace d) :=
  iteratedFDeriv ℝ k (fun y ↦ iteratedFDeriv ℝ l (fun η ↦ a (y, η)) ξ) x

/-- The globally controlled `S^m_{1,0}` symbol class, with norm bounds on all mixed derivatives. -/
def IsGlobalSymbol {d : ℕ} (m : ℝ) (a : EuclideanRealSpace d × EuclideanRealSpace d → ℂ) : Prop :=
  ContDiff ℝ (↑(⊤ : ℕ∞)) a ∧ ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ x ξ, ‖symbolMixedDerivative a k l x ξ‖ ≤ C * (1 + ‖ξ‖) ^ (m - l)

/-- Fourier transform in the physical `exp(-ix·ξ)` convention of GAPS section 30. -/
def physicalFourier {d : ℕ} (u : EuclideanRealSpace d → ℂ) (ξ : EuclideanRealSpace d) : ℂ :=
  ∫ x, Complex.exp (-Complex.I * (inner ℝ x ξ : ℝ)) * u x

/-- Left quantization on scalar functions. For polynomially controlled symbols and Schwartz
inputs this ordinary Fourier integral is absolutely convergent. -/
def leftQuantization {d : ℕ} (a : EuclideanRealSpace d × EuclideanRealSpace d → ℂ)
    (u : EuclideanRealSpace d → ℂ) (x : EuclideanRealSpace d) : ℂ :=
  ((2 * Real.pi) ^ d : ℝ)⁻¹ *
    ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℝ)) * a (x, ξ) * physicalFourier u ξ

/-- Squared Sobolev norm at real order, in the same physical Fourier convention. -/
def physicalSobolevEnergy {d : ℕ} (s : ℝ) (u : EuclideanRealSpace d → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (((2 * Real.pi) ^ d : ℝ)⁻¹) *
    ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * ‖physicalFourier u ξ‖ ^ 2)

/-- **30.27**: a finite number of globally bounded derivatives controls the `L²` norm.
The derivative count and constant are uniform in the symbol and Schwartz input. -/
theorem calderon_vaillancourt (d : ℕ) : ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (a : EuclideanRealSpace d × EuclideanRealSpace d → ℂ) (M : ℝ),
      0 ≤ M → ContDiff ℝ (↑(⊤ : ℕ∞)) a →
      (∀ k ≤ N, ∀ z, ‖iteratedFDeriv ℝ k a z‖ ≤ M) →
      ∀ u : SchwartzMap (EuclideanRealSpace d) ℂ,
        eLpNorm (leftQuantization a u) 2 volume ≤ ENNReal.ofReal (C * M) * eLpNorm u 2 volume := by
  sorry

/-- **30.28**, global a priori Sobolev mapping on Schwartz inputs. The bounded extension to
completed Sobolev spaces and properly supported local versions are separate interfaces. -/
theorem sobolevEnergy_leftQuantization_le {d : ℕ} {m : ℝ}
    {a : EuclideanRealSpace d × EuclideanRealSpace d → ℂ} (ha : IsGlobalSymbol m a) (s : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : SchwartzMap (EuclideanRealSpace d) ℂ,
      physicalSobolevEnergy (s - m) (leftQuantization a u) ≤
        ENNReal.ofReal C * physicalSobolevEnergy s u := by
  sorry

/-- **30.31**: global sharp Gårding for nonnegative real scalar symbols. -/
theorem sharp_garding {d : ℕ} {m : ℝ}
    (a : EuclideanRealSpace d × EuclideanRealSpace d → ℝ)
    (ha : IsGlobalSymbol m (fun z ↦ (a z : ℂ))) (hpos : ∀ z, 0 ≤ a z) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : SchwartzMap (EuclideanRealSpace d) ℂ,
      -C * (physicalSobolevEnergy ((m - 1) / 2) u).toReal ≤
        Complex.re (∫ x, conj (u x) * leftQuantization (fun z ↦ (a z : ℂ)) u x) := by
  sorry

end CKMA
