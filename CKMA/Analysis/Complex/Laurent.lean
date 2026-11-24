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
# Laurent series on annuli

Contour integrals on positively oriented circles define Laurent coefficients.
Holomorphic functions on annuli have bilateral expansions, independent of the chosen
intermediate circle, and normal convergence on compact subsets.

Source: GAPS 40.25. The results are derived from TauCeti's Laurent theory on annuli
`Metric.eball c R \ Metric.closedBall c r` (`TauCeti.circleLaurentCoeff`,
`TauCeti.HasLaurentSeriesOnAnnulus`, `DifferentiableOn.hasLaurentSeriesOnAnnulus`).
Normal summability is the predicate from `CKMA.Analysis.Complex.Basic`.

## Main definitions

* `CKMA.complexAnnulus`: open concentric annulus `{z | r < ‖z - a‖ ∧ ‖z - a‖ < R}`.
* `CKMA.laurentCoefficient`: contour integral defining the `n`th Laurent coefficient on a circle.

## Main results

* `CKMA.complexAnnulus_eq_eball_sdiff_closedBall`,
  `CKMA.laurentCoefficient_eq_circleLaurentCoeff`: comparison with TauCeti's annuli and
  coefficients.
* `CKMA.laurentCoefficient_eq`: independence of Laurent coefficients from the intermediate radius.
* `CKMA.hasSum_laurentSeries`: pointwise Laurent expansion on an annulus.
* `CKMA.normallySummableOn_laurentSeries`: normal convergence of the Laurent series on compact
  subsets.
* `CKMA.eq_laurentCoefficient`: uniqueness of Laurent coefficients.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology Metric Complex
open scoped Real

/-- The open annulus with finite real inner and outer radii. -/
@[expose]
def complexAnnulus (a : ℂ) (r R : ℝ) : Set ℂ := {z | r < ‖z - a‖ ∧ ‖z - a‖ < R}

/-- Laurent coefficient computed on the positively oriented circle of radius `ρ`. -/
@[expose]
def laurentCoefficient (f : ℂ → ℂ) (a : ℂ) (ρ : ℝ) (n : ℤ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * ∮ z in C(a, ρ), (z - a) ^ (-n - 1) * f z

/-- The annulus is TauCeti's annulus `eball a (ofReal R) \ closedBall a r`. -/
theorem complexAnnulus_eq_eball_sdiff_closedBall (a : ℂ) (r R : ℝ) :
    complexAnnulus a r R = eball a (ENNReal.ofReal R) \ closedBall a r := by
  ext z
  rw [Set.mem_sdiff, mem_eball, edist_dist, dist_eq_norm, mem_closedBall, dist_eq_norm, not_le,
    ENNReal.ofReal_lt_ofReal_iff']
  exact ⟨fun h ↦ ⟨⟨h.2, (norm_nonneg _).trans_lt h.2⟩, h.1⟩, fun h ↦ ⟨h.2, h.1.1⟩⟩

/-- The Laurent coefficients are TauCeti's circle Laurent coefficients. -/
theorem laurentCoefficient_eq_circleLaurentCoeff (f : ℂ → ℂ) (a : ℂ) (ρ : ℝ) :
    laurentCoefficient f a ρ = TauCeti.circleLaurentCoeff f a ρ := by
  funext n
  simp only [laurentCoefficient, TauCeti.circleLaurentCoeff_def, smul_eq_mul]

/-- A function holomorphic on an annulus has the Laurent series with the coefficients taken on
any intermediate circle, in the sense of TauCeti. -/
theorem hasLaurentSeriesOnAnnulus_laurentCoefficient {f : ℂ → ℂ} {a : ℂ} {r R ρ : ℝ}
    (hr : 0 ≤ r) (hf : DifferentiableOn ℂ f (complexAnnulus a r R)) (hρ : r < ρ) (hρR : ρ < R) :
    TauCeti.HasLaurentSeriesOnAnnulus f (laurentCoefficient f a ρ) a r (ENNReal.ofReal R) := by
  rw [complexAnnulus_eq_eball_sdiff_closedBall] at hf
  rw [laurentCoefficient_eq_circleLaurentCoeff]
  exact hf.hasLaurentSeriesOnAnnulus hr hρ
    (ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hρR, (hr.trans_lt hρ).trans hρR⟩)

/-- Laurent coefficients taken on any two circles in the annulus agree. -/
theorem laurentCoefficient_eq {f : ℂ → ℂ} {a : ℂ} {r R ρ σ : ℝ} (hr : 0 ≤ r)
    (hf : DifferentiableOn ℂ f (complexAnnulus a r R)) (hρ : r < ρ) (hρR : ρ < R)
    (hσ : r < σ) (hσR : σ < R) : laurentCoefficient f a ρ = laurentCoefficient f a σ := by
  funext n
  rw [laurentCoefficient_eq_circleLaurentCoeff f a σ]
  exact ((hasLaurentSeriesOnAnnulus_laurentCoefficient hr hf hρ hρR).circleLaurentCoeff_eq hσ
    (ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hσR, (hr.trans_lt hσ).trans hσR⟩) n).symm

/-- A function holomorphic on an annulus equals its Laurent series at each point. -/
theorem hasSum_laurentSeries {f : ℂ → ℂ} {a : ℂ} {r R ρ : ℝ} (hr : 0 ≤ r)
    (hf : DifferentiableOn ℂ f (complexAnnulus a r R)) (hρ : r < ρ) (hρR : ρ < R)
    {z : ℂ} (hz : z ∈ complexAnnulus a r R) :
    HasSum (fun n : ℤ ↦ laurentCoefficient f a ρ n * (z - a) ^ n) (f z) := by
  rw [complexAnnulus_eq_eball_sdiff_closedBall] at hz
  convert (hasLaurentSeriesOnAnnulus_laurentCoefficient hr hf hρ hρR).hasSum hz using 1
  funext n
  rw [smul_eq_mul, mul_comm]

/-- The Laurent series of a holomorphic function converges normally on the annulus. -/
theorem normallySummableOn_laurentSeries {f : ℂ → ℂ} {a : ℂ} {r R ρ : ℝ} (hr : 0 ≤ r)
    (hf : DifferentiableOn ℂ f (complexAnnulus a r R)) (hρ : r < ρ) (hρR : ρ < R) :
    NormallySummableOn (fun n ↦ fun z ↦ laurentCoefficient f a ρ n * (z - a) ^ n)
      (complexAnnulus a r R) := by
  intro K hK hKsub
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · refine ⟨fun _ ↦ by rw [Set.image_empty]; exact bddAbove_empty, ?_⟩
    simp only [Set.image_empty, Real.sSup_empty]
    exact summable_zero
  have hnormCont : ContinuousOn (fun w : ℂ ↦ ‖w - a‖) K :=
    (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn
  obtain ⟨wMin, hwMin, hmin⟩ := hK.exists_isMinOn hKne hnormCont
  obtain ⟨wMax, hwMax, hmax⟩ := hK.exists_isMaxOn hKne hnormCont
  have hmaxR := (hKsub hwMax).2
  have hL := hasLaurentSeriesOnAnnulus_laurentCoefficient hr hf hρ hρR
  obtain ⟨B, hB, hbound⟩ := hL.exists_summable_norm_bound_on_closedAnnulus (hKsub hwMin).1
    (hmax hwMin) (ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hmaxR, (norm_nonneg _).trans_lt hmaxR⟩)
  have hle : ∀ n, ∀ z ∈ K, ‖laurentCoefficient f a ρ n * (z - a) ^ n‖ ≤ B n := by
    intro n z hz
    have hzK : z ∈ closedBall a ‖wMax - a‖ \ ball a ‖wMin - a‖ :=
      ⟨by rw [mem_closedBall, dist_eq_norm]; exact hmax hz,
        by rw [mem_ball, dist_eq_norm, not_lt]; exact hmin hz⟩
    have h := hbound n z hzK
    rwa [smul_eq_mul, mul_comm] at h
  have hbdd : ∀ n, BddAbove ((fun z ↦ ‖laurentCoefficient f a ρ n * (z - a) ^ n‖) '' K) :=
    fun n ↦ ⟨B n, by rintro y ⟨z, hz, rfl⟩; exact hle n z hz⟩
  refine ⟨hbdd, Summable.of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_) hB⟩
  · exact (norm_nonneg _).trans (le_csSup (hbdd n) (Set.mem_image_of_mem _ hwMin))
  · exact csSup_le (hKne.image _) (by rintro y ⟨z, hz, rfl⟩; exact hle n z hz)

/-- A normally summable Laurent expansion is the contour series of its sum. -/
theorem eq_laurentCoefficient {f : ℂ → ℂ} {a : ℂ} {r R ρ : ℝ} (c : ℤ → ℂ) (hr : 0 ≤ r)
    (hρ : r < ρ) (hρR : ρ < R)
    (hn : NormallySummableOn (fun n ↦ fun z ↦ c n * (z - a) ^ n) (complexAnnulus a r R))
    (hs : ∀ z ∈ complexAnnulus a r R, HasSum (fun n ↦ c n * (z - a) ^ n) (f z)) :
    c = laurentCoefficient f a ρ := by
  have hρ0 : 0 < ρ := hr.trans_lt hρ
  have hsphere : sphere a ρ ⊆ complexAnnulus a r R := by
    rw [complexAnnulus_eq_eball_sdiff_closedBall]
    exact TauCeti.sphere_subset_eball_sdiff_closedBall hρ
      (ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hρR, hρ0.trans hρR⟩)
  obtain ⟨hbdd, hsup⟩ := hn (sphere a ρ) (isCompact_sphere a ρ) hsphere
  have hnorm : Summable fun k : ℤ ↦ ‖c k‖ * ρ ^ k := by
    refine Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (norm_nonneg _) (zpow_nonneg hρ0.le _))
      (fun k ↦ ?_) hsup
    have hw := circleMap_mem_sphere a hρ0.le 0
    have heq : ‖c k * (circleMap a ρ 0 - a) ^ k‖ = ‖c k‖ * ρ ^ k := by
      rw [norm_mul, norm_zpow, mem_sphere_iff_norm.1 hw]
    exact heq.symm.le.trans (le_csSup (hbdd k) (Set.mem_image_of_mem _ hw))
  funext k
  rw [laurentCoefficient_eq_circleLaurentCoeff]
  refine (TauCeti.circleLaurentCoeff_eq_of_hasSum_sphere hρ0 (fun z hz ↦ ?_) hnorm k).symm
  convert hs z (hsphere hz) using 1
  funext n
  rw [smul_eq_mul, mul_comm]

end CKMA
