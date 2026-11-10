/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Banach couples and real and complex interpolation gauges

A Banach couple is embedded in its algebraic sum equipped with the canonical sum norm.
Compatible operators are given by a single ambient map and its bounded endpoint restrictions.
Peetre's K-functional defines real interpolation through the dilation-invariant measure `dt/t`,
with a separate supremum formula at exponent infinity.

Complex interpolation uses bounded holomorphic strip functions with continuous endpoint lifts
vanishing at infinity. The gauges retain the value infinity off their finite-gauge carriers.
The operator bounds are in `CKMA.Analysis.Interpolation.Bounds`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology
open scoped ENNReal

universe u

/-- A Banach couple realized in its normed sum space.
The sum-norm identity is part of the data, rather than an assumption hidden in the strip theory. -/
structure BanachCouple (𝕜 : Type*) [RCLike 𝕜] where
  /-- First endpoint. -/
  left : Type u
  /-- Second endpoint. -/
  right : Type u
  /-- Common ambient space. -/
  ambient : Type u
  /-- Norm on the first endpoint. -/
  [leftGroup : NormedAddCommGroup left]
  /-- Scalars on the first endpoint. -/
  [leftSpace : NormedSpace 𝕜 left]
  /-- Completeness at the first endpoint. -/
  [leftComplete : CompleteSpace left]
  /-- Norm on the second endpoint. -/
  [rightGroup : NormedAddCommGroup right]
  /-- Scalars on the second endpoint. -/
  [rightSpace : NormedSpace 𝕜 right]
  /-- Completeness at the second endpoint. -/
  [rightComplete : CompleteSpace right]
  /-- Ambient norm. -/
  [ambientGroup : NormedAddCommGroup ambient]
  /-- Ambient scalars. -/
  [ambientSpace : NormedSpace 𝕜 ambient]
  /-- First inclusion. -/
  inLeft : left →L[𝕜] ambient
  /-- Second inclusion. -/
  inRight : right →L[𝕜] ambient
  /-- The ambient space carries the canonical sum norm. This also forces it to be the
  algebraic sum, and supplies the sum topology used by complex strip functions. -/
  sum_norm : ∀ x : ambient, ENNReal.ofReal ‖x‖ =
    ⨅ (x₀ : left) (x₁ : right) (_h : inLeft x₀ + inRight x₁ = x),
      ENNReal.ofReal (‖x₀‖ + ‖x₁‖)
  /-- The first inclusion is injective. -/
  inLeft_injective : Function.Injective inLeft
  /-- The second inclusion is injective. -/
  inRight_injective : Function.Injective inRight

attribute [instance] BanachCouple.leftGroup BanachCouple.leftSpace BanachCouple.leftComplete
  BanachCouple.rightGroup BanachCouple.rightSpace BanachCouple.rightComplete
  BanachCouple.ambientGroup BanachCouple.ambientSpace

/-- Peetre's `K` functional, extended by `∞` off the algebraic sum. -/
def BanachCouple.kFunctional {𝕜 : Type*} [RCLike 𝕜] (C : BanachCouple 𝕜)
    (t : ℝ) (x : C.ambient) : ℝ≥0∞ :=
  ⨅ (x₀ : C.left) (x₁ : C.right) (_h : C.inLeft x₀ + C.inRight x₁ = x),
    ENNReal.ofReal (‖x₀‖ + t * ‖x₁‖)

/-- The dilation-invariant measure `dt/t` on the positive half-line. -/
def interpolationMeasure : Measure ℝ :=
  (volume.restrict (Set.Ioi 0)).withDensity (fun t ↦ ENNReal.ofReal t⁻¹)

/-- Real interpolation gauge, including `q = ∞`. -/
def BanachCouple.realInterpolationGauge {𝕜 : Type*} [RCLike 𝕜]
    (C : BanachCouple 𝕜) (θ : ℝ) (q : ℝ≥0∞) (x : C.ambient) : ℝ≥0∞ :=
  if q = ∞ then ⨆ (t : ℝ) (_ht : 0 < t),
    ENNReal.ofReal (t ^ (-θ)) * C.kFunctional t x
  else (∫⁻ t, (ENNReal.ofReal (t ^ (-θ)) * C.kFunctional t x) ^ q.toReal
    ∂interpolationMeasure) ^ (1 / q.toReal)

/-- The real interpolation space as its finite-gauge carrier.
Bundled normed-space and completeness instances are separate infrastructure targets. -/
def BanachCouple.realInterpolationSet {𝕜 : Type*} [RCLike 𝕜]
    (C : BanachCouple 𝕜) (θ : ℝ) (q : ℝ≥0∞) : Set C.ambient :=
  {x | C.realInterpolationGauge θ q x ≠ ∞}

/-- A single ambient map with compatible bounded restrictions to both endpoints. -/
structure CoupleMap {𝕜 : Type*} [RCLike 𝕜] (C D : BanachCouple 𝕜) where
  /-- The map on the common ambient spaces. -/
  ambientMap : C.ambient →L[𝕜] D.ambient
  /-- First restriction. -/
  leftMap : C.left →L[𝕜] D.left
  /-- Second restriction. -/
  rightMap : C.right →L[𝕜] D.right
  /-- Compatibility on the first endpoint. -/
  left_comm : ∀ x, ambientMap (C.inLeft x) = D.inLeft (leftMap x)
  /-- Compatibility on the second endpoint. -/
  right_comm : ∀ x, ambientMap (C.inRight x) = D.inRight (rightMap x)

/-- Calderón strip functions with continuous endpoint lifts vanishing at infinity. -/
structure InterpolationStripFunction (C : BanachCouple ℂ) where
  /-- Function on the closed strip, extended arbitrarily outside it. -/
  toFun : ℂ → C.ambient
  /-- Continuity on the closed strip. -/
  continuousOn : ContinuousOn toFun {z | 0 ≤ z.re ∧ z.re ≤ 1}
  /-- Holomorphy on the open strip. -/
  differentiableOn : DifferentiableOn ℂ toFun {z | 0 < z.re ∧ z.re < 1}
  /-- Boundedness in the ambient norm on the closed strip. -/
  bounded : ∃ M : ℝ, ∀ z, 0 ≤ z.re → z.re ≤ 1 → ‖toFun z‖ ≤ M
  /-- Boundary values lifted to the first endpoint. -/
  leftBoundary : C(ℝ, C.left)
  /-- Boundary values lifted to the second endpoint. -/
  rightBoundary : C(ℝ, C.right)
  /-- First boundary agreement. -/
  left_eq : ∀ t : ℝ, toFun ((t : ℂ) * Complex.I) = C.inLeft (leftBoundary t)
  /-- Second boundary agreement. -/
  right_eq : ∀ t : ℝ, toFun (1 + (t : ℂ) * Complex.I) = C.inRight (rightBoundary t)
  /-- First boundary decay. -/
  left_zero : Tendsto leftBoundary (cocompact ℝ) (𝓝 0)
  /-- Second boundary decay. -/
  right_zero : Tendsto rightBoundary (cocompact ℝ) (𝓝 0)

/-- The supremum of the two endpoint norms. -/
def InterpolationStripFunction.boundaryNorm {C : BanachCouple ℂ}
    (F : InterpolationStripFunction C) : ℝ :=
  max (sSup (Set.range (fun t ↦ ‖F.leftBoundary t‖)))
    (sSup (Set.range (fun t ↦ ‖F.rightBoundary t‖)))

/-- Complex interpolation gauge as the infimum of boundary norms of interpolants. -/
def BanachCouple.complexInterpolationGauge (C : BanachCouple ℂ)
    (θ : ℝ) (x : C.ambient) : ℝ≥0∞ :=
  ⨅ (F : InterpolationStripFunction C) (_h : F.toFun θ = x),
    ENNReal.ofReal F.boundaryNorm

/-- Finite-gauge carrier of complex interpolation. -/
def BanachCouple.complexInterpolationSet (C : BanachCouple ℂ) (θ : ℝ) : Set C.ambient :=
  {x | C.complexInterpolationGauge θ x ≠ ∞}

end CKMA
