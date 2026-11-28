/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Complex.Basic
public import TauCeti.Analysis.Complex.Laurent.Series
import TauCeti.Topology.MetricSpace.EBall
import TauCeti.Analysis.Complex.Laurent.Expansion

/-!
# Normal convergence of Laurent series on annuli

TauCeti's Laurent theory on annuli `Metric.eball c R \ Metric.closedBall c r` with values in a
complex normed space `E` provides the coefficients `TauCeti.circleLaurentCoeff`, Laurent's theorem
`DifferentiableOn.hasLaurentSeriesOnAnnulus` (with coefficients taken on any intermediate circle),
their independence of the circle `TauCeti.HasLaurentSeriesOnAnnulus.circleLaurentCoeff_eq`, and
the pointwise expansion `TauCeti.HasLaurentSeriesOnAnnulus.hasSum`. This file adds normal
convergence on compact subsets, in the sense of `CKMA.NormallySummableOn`, and the uniqueness of
normally convergent expansions.

Source: GAPS 40.25.

## Main definitions

* `CKMA.complexAnnulus`: the open annulus `eball a R \ closedBall a r`, with `R : ℝ≥0∞`.

## Main results

* `CKMA.mem_complexAnnulus`, `CKMA.complexAnnulus_ofReal`: membership and real outer radii.
* `CKMA.normallySummableOn_laurentSeries`: a Laurent expansion on an annulus converges normally on
  compact subsets.
* `CKMA.eq_circleLaurentCoeff`: uniqueness of normally convergent Laurent expansions.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology Metric Complex
open scoped Real ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The open annulus `{z | r < ‖z - a‖, ‖z - a‖ < R}` with an extended outer radius, as in
TauCeti's Laurent theory. -/
abbrev complexAnnulus (a : ℂ) (r : ℝ) (R : ℝ≥0∞) : Set ℂ := eball a R \ closedBall a r

/-- Membership in the annulus compares `‖z - a‖` with both radii. -/
theorem mem_complexAnnulus {a z : ℂ} {r : ℝ} {R : ℝ≥0∞} :
    z ∈ complexAnnulus a r R ↔ r < ‖z - a‖ ∧ ENNReal.ofReal ‖z - a‖ < R := by
  rw [Set.mem_sdiff, mem_eball, edist_dist, dist_eq_norm, mem_closedBall, dist_eq_norm, not_le,
    and_comm]

/-- With a real outer radius, the annulus is `{z | r < ‖z - a‖ ∧ ‖z - a‖ < R}`. -/
theorem complexAnnulus_ofReal (a : ℂ) (r R : ℝ) :
    complexAnnulus a r (ENNReal.ofReal R) = {z | r < ‖z - a‖ ∧ ‖z - a‖ < R} := by
  ext z
  rw [mem_complexAnnulus, ENNReal.ofReal_lt_ofReal_iff']
  exact ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, (norm_nonneg _).trans_lt h.2⟩⟩

/-- A Laurent expansion on an annulus converges normally on its compact subsets. -/
theorem normallySummableOn_laurentSeries {f : ℂ → E} {c : ℤ → E} {a : ℂ} {r : ℝ} {R : ℝ≥0∞}
    (h : TauCeti.HasLaurentSeriesOnAnnulus f c a r R) :
    NormallySummableOn (fun n ↦ fun z ↦ (z - a) ^ n • c n) (complexAnnulus a r R) := by
  refine NormallySummableOn.of_norm_le fun K hK hKsub ↦ ?_
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, summable_zero, fun _ _ hx ↦ hx.elim⟩
  have hnormCont : ContinuousOn (fun w : ℂ ↦ ‖w - a‖) K :=
    (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn
  obtain ⟨wMin, hwMin, hmin⟩ := hK.exists_isMinOn hKne hnormCont
  obtain ⟨wMax, hwMax, hmax⟩ := hK.exists_isMaxOn hKne hnormCont
  obtain ⟨B, hB, hbound⟩ := h.exists_summable_norm_bound_on_closedAnnulus
    (mem_complexAnnulus.1 (hKsub hwMin)).1 (hmax hwMin) (mem_complexAnnulus.1 (hKsub hwMax)).2
  refine ⟨B, hB, fun n z hz ↦ hbound n z ⟨?_, ?_⟩⟩
  · rw [mem_closedBall, dist_eq_norm]; exact hmax hz
  · rw [mem_ball, dist_eq_norm, not_lt]; exact hmin hz

/-- A normally convergent Laurent expansion on an annulus has the circle Laurent coefficients of
its sum, taken on any circle inside the annulus. -/
theorem eq_circleLaurentCoeff [CompleteSpace E] {f : ℂ → E} {a : ℂ} {r ρ : ℝ} {R : ℝ≥0∞}
    (c : ℤ → E) (hr : 0 ≤ r) (hρ : r < ρ) (hρR : ENNReal.ofReal ρ < R)
    (hn : NormallySummableOn (fun n ↦ fun z ↦ (z - a) ^ n • c n) (complexAnnulus a r R))
    (hs : ∀ z ∈ complexAnnulus a r R, HasSum (fun n ↦ (z - a) ^ n • c n) (f z)) :
    c = TauCeti.circleLaurentCoeff f a ρ := by
  have hρ0 : 0 < ρ := hr.trans_lt hρ
  have hsphere : sphere a ρ ⊆ complexAnnulus a r R :=
    TauCeti.sphere_subset_eball_sdiff_closedBall hρ hρR
  obtain ⟨hbdd, hsup⟩ := hn (sphere a ρ) (isCompact_sphere a ρ) hsphere
  have hnorm : Summable fun k : ℤ ↦ ‖c k‖ * ρ ^ k := by
    refine Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (norm_nonneg _) (zpow_nonneg hρ0.le _))
      (fun k ↦ ?_) hsup
    have hw := circleMap_mem_sphere a hρ0.le 0
    have heq : ‖(circleMap a ρ 0 - a) ^ k • c k‖ = ‖c k‖ * ρ ^ k := by
      rw [norm_smul, norm_zpow, mem_sphere_iff_norm.1 hw, mul_comm]
    exact heq.symm.le.trans (le_csSup (hbdd k) (Set.mem_image_of_mem _ hw))
  funext k
  exact (TauCeti.circleLaurentCoeff_eq_of_hasSum_sphere hρ0
    (fun z hz ↦ hs z (hsphere hz)) hnorm k).symm

end CKMA
