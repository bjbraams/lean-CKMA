/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Extended supremum and Hölder gauges

Extended-valued supremum, Hölder and `C^{2,α}` gauges of a function on a set, used by the
interior elliptic estimates and by Evans–Krylov regularity. All gauges take values in `ℝ≥0∞`,
so a function that is unbounded or not Hölder on the set has infinite gauge instead of a junk
real value. For a nonnegative exponent the Hölder seminorm is the least Hölder constant in
Mathlib's sense (`HolderOnWith`).

## Main definitions

* `CKMA.uniformGaugeOn`: the supremum of `‖f x‖` over `x ∈ Ω`.
* `CKMA.holderSeminormOn`: the supremum of `‖f x - f y‖ / dist x y ^ α` over `x, y ∈ Ω`.
* `CKMA.holderGaugeOn`: the sum of the two.
* `CKMA.cTwoHolderGauge`: the `C^{2,α}` gauge `‖u‖_∞ + ‖Du‖_∞ + ‖D²u‖_{C^α}`.

## Main results

* `CKMA.uniformGaugeOn_le_iff`, `CKMA.holderSeminormOn_le_iff`: the gauges are bounded by `C`
  exactly when every term is.
* `CKMA.holderSeminormOn_le_coe_iff`: for `α C : ℝ≥0`, `holderSeminormOn α f Ω ≤ C` is
  `HolderOnWith C α f Ω`.
* `CKMA.holderSeminormOn_le_of_dist_le`: a real Hölder bound controls the seminorm.
-/

public section

noncomputable section

namespace CKMA

open Metric Set
open scoped ENNReal NNReal

section Gauges

variable {X F : Type*} [NormedAddCommGroup F]

/-- Supremum gauge on a set, allowing infinite values. -/
@[expose]
def uniformGaugeOn (f : X → F) (Ω : Set X) : ℝ≥0∞ :=
  ⨆ x ∈ Ω, ENNReal.ofReal ‖f x‖

/-- The supremum gauge as an iterated supremum. -/
theorem uniformGaugeOn_def (f : X → F) (Ω : Set X) :
    uniformGaugeOn f Ω = ⨆ x ∈ Ω, ENNReal.ofReal ‖f x‖ := rfl

/-- Each value on `Ω` is bounded by the supremum gauge. -/
theorem ofReal_norm_le_uniformGaugeOn {f : X → F} {Ω : Set X} {x : X} (hx : x ∈ Ω) :
    ENNReal.ofReal ‖f x‖ ≤ uniformGaugeOn f Ω :=
  le_iSup₂ (f := fun y (_ : y ∈ Ω) ↦ ENNReal.ofReal ‖f y‖) x hx

/-- The supremum gauge is at most `C` exactly when every value on `Ω` is. -/
theorem uniformGaugeOn_le_iff {f : X → F} {Ω : Set X} {C : ℝ≥0∞} :
    uniformGaugeOn f Ω ≤ C ↔ ∀ x ∈ Ω, ENNReal.ofReal ‖f x‖ ≤ C :=
  iSup₂_le_iff

/-- A finite supremum gauge bounds every norm on `Ω` by its real value. -/
theorem norm_le_toReal_uniformGaugeOn {f : X → F} {Ω : Set X} (h : uniformGaugeOn f Ω ≠ ∞)
    {x : X} (hx : x ∈ Ω) : ‖f x‖ ≤ (uniformGaugeOn f Ω).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal h).1 (ofReal_norm_le_uniformGaugeOn hx)

variable [MetricSpace X]

/-- Hölder seminorm gauge using all pairs of points of `Ω`. A pair with `x = y` contributes
`0 / 0 = 0` in `ℝ≥0∞`. -/
@[expose]
def holderSeminormOn (α : ℝ) (f : X → F) (Ω : Set X) : ℝ≥0∞ :=
  ⨆ x ∈ Ω, ⨆ y ∈ Ω, ENNReal.ofReal ‖f x - f y‖ / ENNReal.ofReal (dist x y ^ α)

/-- The Hölder seminorm gauge as an iterated supremum. -/
theorem holderSeminormOn_def (α : ℝ) (f : X → F) (Ω : Set X) :
    holderSeminormOn α f Ω =
      ⨆ x ∈ Ω, ⨆ y ∈ Ω, ENNReal.ofReal ‖f x - f y‖ / ENNReal.ofReal (dist x y ^ α) := rfl

/-- The Hölder seminorm gauge is at most `C` exactly when every difference quotient is. -/
theorem holderSeminormOn_le_iff {α : ℝ} {f : X → F} {Ω : Set X} {C : ℝ≥0∞} :
    holderSeminormOn α f Ω ≤ C ↔ ∀ x ∈ Ω, ∀ y ∈ Ω,
      ENNReal.ofReal ‖f x - f y‖ / ENNReal.ofReal (dist x y ^ α) ≤ C := by
  simp only [holderSeminormOn, iSup₂_le_iff]

/-- For a nonnegative exponent, a bound `C` on the Hölder seminorm gauge is exactly Mathlib's
Hölder condition `HolderOnWith C α f Ω`. -/
theorem holderSeminormOn_le_coe_iff {α C : ℝ≥0} {f : X → F} {Ω : Set X} :
    holderSeminormOn α f Ω ≤ C ↔ HolderOnWith C α f Ω := by
  rw [holderSeminormOn_le_iff]
  refine forall₂_congr fun x _ ↦ forall₂_congr fun y _ ↦ ?_
  rw [edist_dist, edist_dist, dist_eq_norm (f x),
    ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg]
  rcases eq_or_ne x y with rfl | hxy
  · simp
  · have hpos : ENNReal.ofReal (dist x y ^ (α : ℝ)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.2 (Real.rpow_pos_of_pos (dist_pos.2 hxy) _)
    exact ENNReal.div_le_iff hpos ENNReal.ofReal_ne_top

/-- A pointwise real Hölder bound controls the extended Hölder seminorm gauge. -/
theorem holderSeminormOn_le_of_dist_le {α K : ℝ} {f : X → F} {Ω : Set X} (hα : 0 < α)
    (hK : 0 ≤ K) (h : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖f x - f y‖ ≤ K * dist x y ^ α) :
    holderSeminormOn α f Ω ≤ ENNReal.ofReal K := by
  refine holderSeminormOn_le_iff.2 fun x hx y hy ↦ ?_
  by_cases hxy : dist x y = 0
  · have hzero : ‖f x - f y‖ = 0 := by
      have hle := h x hx y hy
      rw [hxy, Real.zero_rpow hα.ne'] at hle
      exact le_antisymm (by simpa using hle) (norm_nonneg _)
    simp [norm_eq_zero.mp hzero, hxy, Real.zero_rpow hα.ne', ENNReal.ofReal_zero]
  · have hd : 0 < dist x y ^ α :=
      Real.rpow_pos_of_pos (lt_of_le_of_ne dist_nonneg (Ne.symm hxy)) α
    calc
      ENNReal.ofReal ‖f x - f y‖ / ENNReal.ofReal (dist x y ^ α)
        ≤ ENNReal.ofReal (K * dist x y ^ α) / ENNReal.ofReal (dist x y ^ α) := by
          gcongr
          exact h x hx y hy
      _ = ENNReal.ofReal K := by
        rw [ENNReal.ofReal_mul hK]
        exact ENNReal.mul_div_cancel_right (ENNReal.ofReal_ne_zero_iff.mpr hd)
          ENNReal.ofReal_ne_top

/-- Full zeroth-order Hölder gauge: supremum gauge plus Hölder seminorm gauge. -/
@[expose]
def holderGaugeOn (α : ℝ) (f : X → F) (Ω : Set X) : ℝ≥0∞ :=
  uniformGaugeOn f Ω + holderSeminormOn α f Ω

/-- The Hölder gauge is the sum of the supremum gauge and the Hölder seminorm gauge. -/
theorem holderGaugeOn_def (α : ℝ) (f : X → F) (Ω : Set X) :
    holderGaugeOn α f Ω = uniformGaugeOn f Ω + holderSeminormOn α f Ω := rfl

/-- A finite Hölder gauge has a finite supremum gauge. -/
theorem uniformGaugeOn_ne_top_of_holderGaugeOn {α : ℝ} {f : X → F} {Ω : Set X}
    (h : holderGaugeOn α f Ω ≠ ∞) : uniformGaugeOn f Ω ≠ ∞ :=
  ne_top_of_le_ne_top h le_self_add

/-- A finite Hölder gauge has a finite Hölder seminorm gauge. -/
theorem holderSeminormOn_ne_top_of_holderGaugeOn {α : ℝ} {f : X → F} {Ω : Set X}
    (h : holderGaugeOn α f Ω ≠ ∞) : holderSeminormOn α f Ω ≠ ∞ :=
  ne_top_of_le_ne_top h le_add_self

end Gauges

/-- Full `C^{2,α}` gauge of a scalar function on a set: the supremum gauges of `u` and `Du`
plus the Hölder gauge of `D²u`. Derivatives are Mathlib's `fderiv`, which is `0` where `u` is
not differentiable. -/
@[expose]
def cTwoHolderGauge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) (u : E → ℝ)
    (Ω : Set E) : ℝ≥0∞ :=
  uniformGaugeOn u Ω + uniformGaugeOn (fderiv ℝ u) Ω + holderGaugeOn α (fderiv ℝ (fderiv ℝ u)) Ω

/-- The `C^{2,α}` gauge in terms of the zeroth-order gauges. -/
theorem cTwoHolderGauge_def {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ)
    (u : E → ℝ) (Ω : Set E) :
    cTwoHolderGauge α u Ω =
      uniformGaugeOn u Ω + uniformGaugeOn (fderiv ℝ u) Ω +
        holderGaugeOn α (fderiv ℝ (fderiv ℝ u)) Ω := rfl

end CKMA
