/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.PDE.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Global symbols, left quantization and Sobolev estimates

Global scalar symbols of class `S^m_{1,0}`, mixed spatial/frequency derivatives and
left quantization in the physical `exp(-i x·xi)` Fourier convention. The statements
include the Calderón–Vaillancourt bound, Sobolev mapping on Schwartz inputs and sharp
Gårding. Fourier inversion uses `(2*pi)^(-d)`; squared Sobolev energies retain extended
values. Derivatives, Schwartz maps and integration reuse Mathlib.
Sources: GAPS 30.27, 30.28 and 30.31.

## Main definitions

* `CKMA.symbolMixedDerivative`: mixed spatial and frequency iterated Fréchet derivative of a
  symbol.
* `CKMA.IsGlobalSymbol`: global Hörmander symbol class `S^m_{1,0}` on `ℝ^d × ℝ^d`.
* `CKMA.physicalFourier`: Fourier integral in the physical `exp(-i x·ξ)` normalization.
* `CKMA.leftQuantization`: left Kohn–Nirenberg quantization of a symbol on scalar functions.
* `CKMA.physicalSobolevEnergy`: squared Sobolev norm of order `s` in the physical Fourier
  convention.

## Main results

* `CKMA.calderon_vaillancourt`: Calderón–Vaillancourt `L²` boundedness theorem (**30.27**).
* `CKMA.sobolevEnergy_leftQuantization_le`: Sobolev mapping estimate for `S^m_{1,0}` symbols
  (**30.28**).
* `CKMA.sharp_garding`: sharp Gårding inequality for nonnegative scalar symbols (**30.31**).
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped ENNReal ComplexConjugate

/-- Mixed derivatives of a symbol, differentiated in frequency first and then in space. -/
@[expose]
def symbolMixedDerivative {d : ℕ} (a : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℂ)
    (k l : ℕ) (x ξ : EuclideanSpace ℝ (Fin d)) :=
  iteratedFDeriv ℝ k (fun y ↦ iteratedFDeriv ℝ l (fun η ↦ a (y, η)) ξ) x

/-- Unfolding the mixed derivative. -/
theorem symbolMixedDerivative_def {d : ℕ}
    (a : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℂ) (k l : ℕ)
    (x ξ : EuclideanSpace ℝ (Fin d)) :
    symbolMixedDerivative a k l x ξ =
      iteratedFDeriv ℝ k (fun y ↦ iteratedFDeriv ℝ l (fun η ↦ a (y, η)) ξ) x := rfl

/-- The globally controlled `S^m_{1,0}` symbol class, with norm bounds on all mixed derivatives. -/
@[expose]
def IsGlobalSymbol {d : ℕ} (m : ℝ)
    (a : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℂ) : Prop :=
  ContDiff ℝ (↑(⊤ : ℕ∞)) a ∧ ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ x ξ, ‖symbolMixedDerivative a k l x ξ‖ ≤ C * (1 + ‖ξ‖) ^ (m - l)

/-- Unfolding the global symbol class. -/
theorem isGlobalSymbol_iff {d : ℕ} {m : ℝ}
    {a : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℂ} :
    IsGlobalSymbol m a ↔ ContDiff ℝ (↑(⊤ : ℕ∞)) a ∧ ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ξ, ‖symbolMixedDerivative a k l x ξ‖ ≤ C * (1 + ‖ξ‖) ^ (m - l) := Iff.rfl

/-- A global symbol is smooth. -/
theorem IsGlobalSymbol.contDiff {d : ℕ} {m : ℝ}
    {a : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℂ} (ha : IsGlobalSymbol m a) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) a := ha.1

/-- The symbol estimates of a global symbol. -/
theorem IsGlobalSymbol.exists_bound {d : ℕ} {m : ℝ}
    {a : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℂ} (ha : IsGlobalSymbol m a)
    (k l : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ξ, ‖symbolMixedDerivative a k l x ξ‖ ≤ C * (1 + ‖ξ‖) ^ (m - l) := ha.2 k l

/-- Fourier transform in the physical `exp(-ix·ξ)` convention of GAPS section 30. -/
@[expose]
def physicalFourier {d : ℕ} (u : EuclideanSpace ℝ (Fin d) → ℂ) (ξ : EuclideanSpace ℝ (Fin d)) :
    ℂ :=
  ∫ x, Complex.exp (-Complex.I * (inner ℝ x ξ : ℝ)) * u x

/-- Unfolding the physical Fourier integral. -/
theorem physicalFourier_def {d : ℕ} (u : EuclideanSpace ℝ (Fin d) → ℂ)
    (ξ : EuclideanSpace ℝ (Fin d)) :
    physicalFourier u ξ = ∫ x, Complex.exp (-Complex.I * (inner ℝ x ξ : ℝ)) * u x := rfl

/-- Left quantization on scalar functions. For polynomially controlled symbols and Schwartz
inputs this ordinary Fourier integral is absolutely convergent. -/
@[expose]
def leftQuantization {d : ℕ} (a : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℂ)
    (u : EuclideanSpace ℝ (Fin d) → ℂ) (x : EuclideanSpace ℝ (Fin d)) : ℂ :=
  ((2 * Real.pi) ^ d : ℝ)⁻¹ *
    ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℝ)) * a (x, ξ) * physicalFourier u ξ

/-- Unfolding the left quantization. -/
theorem leftQuantization_def {d : ℕ}
    (a : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℂ)
    (u : EuclideanSpace ℝ (Fin d) → ℂ) (x : EuclideanSpace ℝ (Fin d)) :
    leftQuantization a u x = ((2 * Real.pi) ^ d : ℝ)⁻¹ *
      ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℝ)) * a (x, ξ) * physicalFourier u ξ := rfl

/-- Squared Sobolev norm at real order, in the same physical Fourier convention. -/
@[expose]
def physicalSobolevEnergy {d : ℕ} (s : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (((2 * Real.pi) ^ d : ℝ)⁻¹) *
    ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * ‖physicalFourier u ξ‖ ^ 2)

/-- Unfolding the physical Sobolev energy. -/
theorem physicalSobolevEnergy_def {d : ℕ} (s : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℂ) :
    physicalSobolevEnergy s u = ENNReal.ofReal (((2 * Real.pi) ^ d : ℝ)⁻¹) *
      ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * ‖physicalFourier u ξ‖ ^ 2) := rfl

/-- **30.27**, Calderón–Vaillancourt in the `S⁰_{0,0}` form: there are `N` and `C` such that a
smooth symbol whose derivatives up to order `N` are bounded by `M` gives
`‖Op(a) u‖₂ ≤ C M ‖u‖₂` for every Schwartz `u`; `N` and `C` depend only on `d`. -/
theorem calderon_vaillancourt (d : ℕ) : ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (a : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℂ) (M : ℝ),
      0 ≤ M → ContDiff ℝ (↑(⊤ : ℕ∞)) a →
      (∀ k ≤ N, ∀ z, ‖iteratedFDeriv ℝ k a z‖ ≤ M) →
      ∀ u : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ,
        eLpNorm (leftQuantization a u) 2 volume ≤
          ENNReal.ofReal (C * M) * eLpNorm u 2 volume := by
  sorry

/-- **30.28**, Sobolev mapping on Schwartz inputs: a global symbol of order `m` maps `H^s` to
`H^{s-m}`, `‖Op(a) u‖_{s-m} ≤ C ‖u‖_s`, with squared energies in `ℝ≥0∞`. -/
theorem sobolevEnergy_leftQuantization_le {d : ℕ} {m : ℝ}
    {a : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℂ} (ha : IsGlobalSymbol m a)
    (s : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ,
      physicalSobolevEnergy (s - m) (leftQuantization a u) ≤
        ENNReal.ofReal C * physicalSobolevEnergy s u := by
  sorry

/-- **30.31**, sharp Gårding: for a nonnegative real global symbol of order `m`,
`Re ⟨Op(a) u, u⟩ ≥ -C ‖u‖²_{(m-1)/2}` for every Schwartz `u`. -/
theorem sharp_garding {d : ℕ} {m : ℝ}
    (a : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (ha : IsGlobalSymbol m (fun z ↦ (a z : ℂ))) (hpos : ∀ z, 0 ≤ a z) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ,
      -C * (physicalSobolevEnergy ((m - 1) / 2) u).toReal ≤
        Complex.re (∫ x, conj (u x) * leftQuantization (fun z ↦ (a z : ℂ)) u x) := by
  sorry

end CKMA
