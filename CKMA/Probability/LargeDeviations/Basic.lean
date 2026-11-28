/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Probability.LargeDeviations.Basic

/-!
# Large deviation bounds at speed `n + 1`

`HasLargeDeviationBounds` combines lower bounds on open sets and upper bounds on closed sets
at speed `n + 1`, without asking the rate to be lower semicontinuous. `logProbabilityRate`
uses an extended logarithm so that zero probabilities retain value minus infinity.

Rate functions and large deviation principles are TauCeti's
`TauCeti.Probability.IsGoodRateFunction` and `TauCeti.Probability.HasLDP`. At speed
`(n + 1)⁻¹`, `HasLDP` is lower semicontinuity of the rate together with
`HasLargeDeviationBounds` (`hasLDP_iff_hasLargeDeviationBounds`).

## Main definitions

* `CKMA.logProbabilityRate`: normalized logarithmic probability at speed `n + 1`.
* `CKMA.HasLargeDeviationBounds`: open lower and closed upper large deviation bounds.

## Main results

* `CKMA.isGoodRateFunction_of_isCompact_nnreal`: goodness from compact sublevels at levels
  in `ℝ≥0`.
* `CKMA.hasLDP_iff_hasLargeDeviationBounds`: TauCeti's LDP at speed `(n + 1)⁻¹` in terms of
  the two bounds.
-/

public section

noncomputable section

namespace CKMA

open scoped NNReal ENNReal


open MeasureTheory Filter Topology Set Finset

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- Logarithmic probability at speed `n + 1`. Extended logarithms retain zero probabilities. -/
@[expose]
def logProbabilityRate (P : ℕ → Measure X) (s : Set X) (n : ℕ) : EReal :=
  (((n + 1 : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (P n s)

omit [TopologicalSpace X] in
/-- Defining formula of `logProbabilityRate`. -/
lemma logProbabilityRate_def (P : ℕ → Measure X) (s : Set X) (n : ℕ) :
    logProbabilityRate P s n = (((n + 1 : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (P n s) :=
  rfl

/-- The open lower and closed upper bounds of a large deviation principle at speed `n + 1`.
Lower semicontinuity of `I` is not part of this predicate. -/
@[expose]
def HasLargeDeviationBounds (P : ℕ → Measure X) (I : X → ℝ≥0∞) : Prop :=
  (∀ s, IsOpen s → -(⨅ x ∈ s, (I x : EReal)) ≤
    liminf (logProbabilityRate P s) atTop) ∧
  (∀ s, IsClosed s → limsup (logProbabilityRate P s) atTop ≤
    -(⨅ x ∈ s, (I x : EReal)))

/-- Defining property of `HasLargeDeviationBounds`. -/
lemma hasLargeDeviationBounds_iff {P : ℕ → Measure X} {I : X → ℝ≥0∞} :
    HasLargeDeviationBounds P I ↔
      (∀ s, IsOpen s → -(⨅ x ∈ s, (I x : EReal)) ≤ liminf (logProbabilityRate P s) atTop) ∧
      (∀ s, IsClosed s → limsup (logProbabilityRate P s) atTop ≤ -(⨅ x ∈ s, (I x : EReal))) :=
  Iff.rfl

/-- The open-set lower bound of `HasLargeDeviationBounds`. -/
lemma HasLargeDeviationBounds.le_liminf {P : ℕ → Measure X} {I : X → ℝ≥0∞}
    (h : HasLargeDeviationBounds P I) {s : Set X} (hs : IsOpen s) :
    -(⨅ x ∈ s, (I x : EReal)) ≤ liminf (logProbabilityRate P s) atTop :=
  h.1 s hs

/-- The closed-set upper bound of `HasLargeDeviationBounds`. -/
lemma HasLargeDeviationBounds.limsup_le {P : ℕ → Measure X} {I : X → ℝ≥0∞}
    (h : HasLargeDeviationBounds P I) {s : Set X} (hs : IsClosed s) :
    limsup (logProbabilityRate P s) atTop ≤ -(⨅ x ∈ s, (I x : EReal)) :=
  h.2 s hs

omit [TopologicalSpace X] [MeasurableSpace X] in
/-- The coercion `ℝ≥0∞ → EReal` commutes with bounded infima. -/
lemma coe_ennreal_biInf (s : Set X) (I : X → ℝ≥0∞) :
    ((⨅ x ∈ s, I x : ℝ≥0∞) : EReal) = ⨅ x ∈ s, (I x : EReal) := by
  refine le_antisymm (le_iInf₂ fun x hx ↦ EReal.coe_ennreal_le_coe_ennreal_iff.2
    (iInf₂_le x hx)) ?_
  have h0 : 0 ≤ ⨅ x ∈ s, (I x : EReal) := le_iInf₂ fun x _ ↦ EReal.coe_ennreal_nonneg _
  rw [← EReal.coe_toENNReal h0]
  refine EReal.coe_ennreal_le_coe_ennreal_iff.2 (le_iInf₂ fun x hx ↦ ?_)
  simpa using EReal.toENNReal_le_toENNReal (iInf₂_le x hx : ⨅ y ∈ s, (I y : EReal) ≤ I x)

omit [MeasurableSpace X] in
/-- A lower semicontinuous rate function with compact sublevels at all levels in `ℝ≥0` is
good. -/
lemma isGoodRateFunction_of_isCompact_nnreal {I : X → ℝ≥0∞} (hI : LowerSemicontinuous I)
    (hc : ∀ a : ℝ≥0, IsCompact {x | I x ≤ a}) : TauCeti.Probability.IsGoodRateFunction I :=
  ⟨hI, fun α hα ↦ by simpa [ENNReal.coe_toNNReal hα] using hc α.toNNReal⟩

/-- At speed `(n + 1)⁻¹`, TauCeti's large deviation principle is lower semicontinuity of the
rate together with the two bounds of `HasLargeDeviationBounds`. -/
lemma hasLDP_iff_hasLargeDeviationBounds {P : ℕ → Measure X} {I : X → ℝ≥0∞} :
    TauCeti.Probability.HasLDP atTop (fun n : ℕ ↦ ((n : ℝ≥0) + 1)⁻¹) P I ↔
      LowerSemicontinuous I ∧ HasLargeDeviationBounds P I := by
  have hrate : ∀ s, (fun n : ℕ ↦ (((((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ) : EReal) *
      ENNReal.log (P n s)) = logProbabilityRate P s := fun s ↦ by
    funext n
    simp [logProbabilityRate]
  constructor
  · intro h
    refine ⟨h.lowerSemicontinuous, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
    · simpa only [hrate, coe_ennreal_biInf] using h.lower_bound s hs
    · simpa only [hrate, coe_ennreal_biInf] using h.upper_bound s hs
  · rintro ⟨hI, hlow, hup⟩
    refine ⟨hI, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
    · simpa only [hrate, coe_ennreal_biInf] using hlow s hs
    · simpa only [hrate, coe_ennreal_biInf] using hup s hs

/-- TauCeti's large deviation principle at speed `(n + 1)⁻¹` gives the two bounds. -/
lemma hasLargeDeviationBounds_of_hasLDP {P : ℕ → Measure X}
    {I : X → ℝ≥0∞}
    (h : TauCeti.Probability.HasLDP atTop (fun n : ℕ ↦ ((n : ℝ≥0) + 1)⁻¹) P I) :
    HasLargeDeviationBounds P I :=
  (hasLDP_iff_hasLargeDeviationBounds.1 h).2

/-- The two bounds and a lower semicontinuous rate give TauCeti's large deviation principle. -/
lemma HasLargeDeviationBounds.hasLDP {P : ℕ → Measure X} {I : X → ℝ≥0∞}
    (h : HasLargeDeviationBounds P I) (hI : LowerSemicontinuous I) :
    TauCeti.Probability.HasLDP atTop (fun n : ℕ ↦ ((n : ℝ≥0) + 1)⁻¹) P I :=
  hasLDP_iff_hasLargeDeviationBounds.2 ⟨hI, h⟩

end CKMA
