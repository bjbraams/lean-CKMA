/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Complex.Basic
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart

/-!
# Weak Beltrami equations and quasiconformal area distortion

Wirtinger components of a real-linear weak differential formulate the Beltrami
equation with local W¹,² regularity. Quasiconformality is imposed on plane
homeomorphisms through the same differential. A measurable coefficient of norm below
one determines the normalized homeomorphism fixing zero and one; normalized disk
self-maps satisfy Astala's area exponent.

Sources: GAPS 44.38 and 44.49. Weak differentials reuse TauCeti's Sobolev API, and the Wirtinger
components are the values at `1` of TauCeti's `ContinuousLinearMap.complexLinearPart` and
`ContinuousLinearMap.complexAntilinearPart`.

## Main definitions

* `CKMA.wirtingerZ`, `CKMA.wirtingerBar`: Wirtinger derivatives of an `ℝ`-linear map `ℂ →L[ℝ] ℂ`.
* `CKMA.IsWeakW12FieldOn`: local `W^{1,2}` weak differentiability on an open set.
* `CKMA.IsBeltramiSolutionOn`: weak `W^{1,2}_{\mathrm{loc}}` solution of the Beltrami equation.
* `CKMA.IsQuasiconformalOn`: analytic definition of `K`-quasiconformality.

## Main results

* `CKMA.existsUnique_beltrami_homeomorph`: Ahlfors–Bers measurable Riemann mapping theorem.
* `CKMA.astala_disk_area`: Astala's area distortion theorem for quasiconformal disk maps.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped ENNReal

/-- The `z`-derivative `(U 1 - i U i) / 2` of a real-linear complex differential: the value at
`1` of its complex-linear part `ContinuousLinearMap.complexLinearPart`. -/
def wirtingerZ (U : ℂ →L[ℝ] ℂ) : ℂ := U.complexLinearPart 1

/-- The conjugate-coordinate derivative `(U 1 + i U i) / 2` of a real-linear complex
differential: the value at `1` of its complex-antilinear part
`ContinuousLinearMap.complexAntilinearPart`. -/
def wirtingerBar (U : ℂ →L[ℝ] ℂ) : ℂ := U.complexAntilinearPart 1

/-- `wirtingerZ U` is the complex-linear part of `U` evaluated at `1`. -/
theorem wirtingerZ_eq_complexLinearPart (U : ℂ →L[ℝ] ℂ) :
    wirtingerZ U = U.complexLinearPart 1 := by
  rw [wirtingerZ]

/-- `wirtingerBar U` is the complex-antilinear part of `U` evaluated at `1`. -/
theorem wirtingerBar_eq_complexAntilinearPart (U : ℂ →L[ℝ] ℂ) :
    wirtingerBar U = U.complexAntilinearPart 1 := by
  rw [wirtingerBar]

/-- The coordinate formula `∂U = (U 1 - i U i) / 2`. -/
theorem wirtingerZ_def (U : ℂ →L[ℝ] ℂ) : wirtingerZ U = (U 1 - Complex.I * U Complex.I) / 2 := by
  rw [wirtingerZ, ContinuousLinearMap.complexLinearPart_apply]
  simp only [smul_eq_mul, mul_one, Complex.real_smul]
  push_cast
  ring

/-- The coordinate formula `∂̄U = (U 1 + i U i) / 2`. -/
theorem wirtingerBar_def (U : ℂ →L[ℝ] ℂ) :
    wirtingerBar U = (U 1 + Complex.I * U Complex.I) / 2 := by
  rw [wirtingerBar, ContinuousLinearMap.complexAntilinearPart_apply]
  simp only [smul_eq_mul, mul_one, Complex.real_smul]
  push_cast
  ring

/-- A specified weak differential lies locally in the first-order square-integrable Sobolev class.
  -/
@[expose]
def IsWeakW12FieldOn (f : ℂ → ℂ) (U : ℂ → ℂ →L[ℝ] ℂ)
    (Ω : TopologicalSpace.Opens ℂ) : Prop :=
  TauCeti.HasWeakFDerivOn volume Ω f U ∧
    ∀ K : Set ℂ, IsCompact K → K ⊆ (Ω : Set ℂ) →
      MemLp f 2 (volume.restrict K) ∧ MemLp U 2 (volume.restrict K)

/-- Characterization of `IsWeakW12FieldOn`: `U` is the weak differential of `f` on `Ω`, and `f`
and `U` are square-integrable on compact subsets of `Ω`. -/
theorem isWeakW12FieldOn_iff {f : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ} {Ω : TopologicalSpace.Opens ℂ} :
    IsWeakW12FieldOn f U Ω ↔ TauCeti.HasWeakFDerivOn volume Ω f U ∧
      ∀ K : Set ℂ, IsCompact K → K ⊆ (Ω : Set ℂ) →
        MemLp f 2 (volume.restrict K) ∧ MemLp U 2 (volume.restrict K) :=
  Iff.rfl

/-- The weak Beltrami equation, including the required local Sobolev regularity. -/
@[expose]
def IsBeltramiSolutionOn (μ f : ℂ → ℂ) (Ω : TopologicalSpace.Opens ℂ) : Prop :=
  ∃ U : ℂ → ℂ →L[ℝ] ℂ, IsWeakW12FieldOn f U Ω ∧
    ∀ᵐ z ∂volume.restrict (Ω : Set ℂ), wirtingerBar (U z) = μ z * wirtingerZ (U z)

/-- Characterization of `IsBeltramiSolutionOn`: a local `W^{1,2}` weak differential satisfying
`∂̄f = μ ∂f` almost everywhere on `Ω`. -/
theorem isBeltramiSolutionOn_iff {μ f : ℂ → ℂ} {Ω : TopologicalSpace.Opens ℂ} :
    IsBeltramiSolutionOn μ f Ω ↔ ∃ U : ℂ → ℂ →L[ℝ] ℂ, IsWeakW12FieldOn f U Ω ∧
      ∀ᵐ z ∂volume.restrict (Ω : Set ℂ), wirtingerBar (U z) = μ z * wirtingerZ (U z) :=
  Iff.rfl

/-- Quasiconformality of a plane homeomorphism on an open subset, in the analytic convention.
The homeomorphism is part of the argument type, so constant PDE solutions cannot qualify. -/
@[expose]
def IsQuasiconformalOn (K : ℝ) (f : ℂ ≃ₜ ℂ) (Ω : TopologicalSpace.Opens ℂ) : Prop :=
  1 ≤ K ∧ ∃ U : ℂ → ℂ →L[ℝ] ℂ, IsWeakW12FieldOn f U Ω ∧
    ∀ᵐ z ∂volume.restrict (Ω : Set ℂ),
      ‖wirtingerBar (U z)‖ ≤ ((K - 1) / (K + 1)) * ‖wirtingerZ (U z)‖

/-- Characterization of `IsQuasiconformalOn`: `1 ≤ K` and a local `W^{1,2}` weak differential with
`|∂̄f| ≤ (K - 1)/(K + 1) |∂f|` almost everywhere on `Ω`. -/
theorem isQuasiconformalOn_iff {K : ℝ} {f : ℂ ≃ₜ ℂ} {Ω : TopologicalSpace.Opens ℂ} :
    IsQuasiconformalOn K f Ω ↔ 1 ≤ K ∧ ∃ U : ℂ → ℂ →L[ℝ] ℂ, IsWeakW12FieldOn f U Ω ∧
      ∀ᵐ z ∂volume.restrict (Ω : Set ℂ),
        ‖wirtingerBar (U z)‖ ≤ ((K - 1) / (K + 1)) * ‖wirtingerZ (U z)‖ :=
  Iff.rfl

/-- **44.38**: the normalized plane form of the measurable Riemann mapping theorem.
A plane homeomorphism fixes infinity on its one-point compactification; fixing zero and one
therefore gives the three-point sphere normalization without arbitrary values at infinity. -/
theorem existsUnique_beltrami_homeomorph (μ : ℂ → ℂ) (hμ : Measurable μ)
    {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) (hbound : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k) :
    ∃! f : ℂ ≃ₜ ℂ, f 0 = 0 ∧ f 1 = 1 ∧ IsBeltramiSolutionOn μ f ⊤ ∧
      IsQuasiconformalOn ((1 + k) / (1 - k)) f ⊤ := by
  sorry

/-- **44.49**: Astala's area exponent on disk self-maps that are restrictions of plane
homeomorphisms: `|f(E)| ≤ C |E|^{1/K}` for measurable `E` in the unit disk. -/
theorem astala_disk_area {K : ℝ} (hK : 1 ≤ K) : ∃ C : ℝ, 0 < C ∧
    ∀ f : ℂ ≃ₜ ℂ,
      IsQuasiconformalOn K f ⟨complexUnitDisk, isOpen_complexUnitDisk⟩ →
      f 0 = 0 → f '' complexUnitDisk = complexUnitDisk →
      ∀ E : Set ℂ, MeasurableSet E → E ⊆ complexUnitDisk →
        volume (f '' E) ≤ ENNReal.ofReal C * (volume E) ^ (1 / K) := by
  sorry

end CKMA
