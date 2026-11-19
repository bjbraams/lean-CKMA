/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.MeasureTheory.Integral.MaximalFunction
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Measurability of a weighted centred maximal function

`TauCeti.maximalFunction` on a weighted Lebesgue measure is a countable supremum of ball
averages. Positive rational radii decrease to any positive real radius, and a weight that
vanishes on spheres identifies the limiting average with the real-radius average. Each
fixed-radius average is measurable in the centre, so the maximal function is measurable.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Metric Set ENNReal Filter
open scoped ENNReal Topology

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A positive rational, used as a countable family of ball radii. -/
abbrev PosRat := {q : ℚ // 0 < (q : ℝ)}

/-- A rational strictly between two reals. -/
private def ratBetween (a b : ℝ) (h : a < b) : ℚ :=
  Classical.choose (exists_rat_btwn h)

/-- The chosen rational lies above the lower endpoint. -/
private lemma ratBetween_gt (a b : ℝ) (h : a < b) : a < (ratBetween a b h : ℝ) :=
  (Classical.choose_spec (exists_rat_btwn h)).1

/-- The chosen rational lies below the upper endpoint. -/
private lemma ratBetween_lt (a b : ℝ) (h : a < b) : (ratBetween a b h : ℝ) < b :=
  (Classical.choose_spec (exists_rat_btwn h)).2

/-- A smaller positive rational radius above `r` and below both `q` and `r + 1/(n+2)`. -/
private lemma exists_next (r : ℝ) {q : ℚ} (hq : r < (q : ℝ)) (n : ℕ) :
    ∃ q' : ℚ, r < (q' : ℝ) ∧ (q' : ℝ) < q ∧ (q' : ℝ) < r + 1 / (n + 2) := by
  have hlt : r < min (q : ℝ) (r + 1 / (n + 2)) :=
    lt_min hq (lt_add_of_pos_right r (by positivity))
  obtain ⟨q', hgt, hlt'⟩ := exists_rat_btwn hlt
  exact ⟨q', hgt, hlt'.trans_le (min_le_left _ _), hlt'.trans_le (min_le_right _ _)⟩

/-- The rational selected by `exists_next`. -/
private def nextRat (r : ℝ) (n : ℕ) (q : ℚ) (hq : r < (q : ℝ)) : ℚ :=
  Classical.choose (exists_next r hq n)

/-- `nextRat` stays above `r`. -/
private lemma nextRat_gt (r : ℝ) (n : ℕ) (q : ℚ) (hq : r < (q : ℝ)) :
    r < (nextRat r n q hq : ℝ) :=
  (Classical.choose_spec (exists_next r hq n)).1

/-- `nextRat` is strictly smaller than the previous radius. -/
private lemma nextRat_lt (r : ℝ) (n : ℕ) (q : ℚ) (hq : r < (q : ℝ)) :
    (nextRat r n q hq : ℝ) < q :=
  (Classical.choose_spec (exists_next r hq n)).2.1

/-- `nextRat` lies below the explicit shift `r + 1/(n+2)`. -/
private lemma nextRat_shift (r : ℝ) (n : ℕ) (q : ℚ) (hq : r < (q : ℝ)) :
    (nextRat r n q hq : ℝ) < r + 1 / (n + 2) :=
  (Classical.choose_spec (exists_next r hq n)).2.2

/-- Positive rational radii decreasing to `r`, packaged with the lower bound. -/
private def ratPack (r : ℝ) : ℕ → {q : ℚ // r < (q : ℝ)}
  | 0 =>
    ⟨ratBetween r (r + 1) (lt_add_of_pos_right r one_pos),
      ratBetween_gt r (r + 1) (lt_add_of_pos_right r one_pos)⟩
  | n + 1 =>
    ⟨nextRat r n (ratPack r n) (ratPack r n).2,
      nextRat_gt r n (ratPack r n) (ratPack r n).2⟩

/-- A positive rational radius strictly above `r`, decreasing in `n`. -/
private def ratDescend (r : ℝ) (n : ℕ) : ℚ := ratPack r n

/-- Every term of `ratDescend` is strictly above `r`. -/
private lemma ratDescend_gt (r : ℝ) (n : ℕ) : r < (ratDescend r n : ℝ) :=
  (ratPack r n).2

/-- Successive terms of `ratDescend` decrease. -/
private lemma ratDescend_succ_lt (r : ℝ) (n : ℕ) :
    (ratDescend r (n + 1) : ℝ) < ratDescend r n := by
  simpa only [ratDescend, ratPack] using nextRat_lt r n (ratPack r n) (ratPack r n).2

/-- `ratDescend` is bounded by the explicit shift `r + 1/(n+1)`. -/
private lemma ratDescend_lt (r : ℝ) (n : ℕ) :
    (ratDescend r n : ℝ) < r + 1 / (n + 1) := by
  induction n with
  | zero =>
    simpa only [ratDescend, ratPack, Nat.cast_zero, zero_add, div_one] using
      ratBetween_lt r (r + 1) (lt_add_of_pos_right r one_pos)
  | succ n _ =>
    unfold ratDescend ratPack
    have hcast : (↑(n + 1) + 1 : ℝ) = ↑n + 2 := by
      push_cast
      ring
    rw [hcast]
    exact nextRat_shift r n (ratPack r n) (ratPack r n).2

/-- `ratDescend r` is antitone. -/
private lemma ratDescend_antitone (r : ℝ) : Antitone fun n => (ratDescend r n : ℝ) :=
  antitone_nat_of_succ_le fun n => (ratDescend_succ_lt r n).le

/-- The rational radii decrease to `r`. -/
private lemma tendsto_ratDescend (r : ℝ) :
    Tendsto (fun n => (ratDescend r n : ℝ)) atTop (𝓝 r) := by
  have hshift : Tendsto (fun n : ℕ => r + 1 / ((n : ℝ) + 1)) atTop (𝓝 r) := by
    have hzero := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using tendsto_const_nhds.add hzero
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hshift
    (fun n => (ratDescend_gt r n).le) (fun n => (ratDescend_lt r n).le)

/-- Balls along `ratDescend` meet in the closed ball of radius `r`. -/
private lemma iInter_ball_ratDescend {x : E} {r : ℝ} :
    ⋂ n, ball x (ratDescend r n : ℝ) = closedBall x r := by
  ext y
  constructor
  · intro hy
    refine mem_closedBall.mpr ?_
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (tendsto_ratDescend r)) ε hε
    have hdist : dist y x < ratDescend r N := mem_ball.mp (mem_iInter.mp hy N)
    have habs : |(ratDescend r N : ℝ) - r| < ε := by
      rw [← Real.dist_eq]
      exact hN N le_rfl
    have hqlt : (ratDescend r N : ℝ) < r + ε := by
      have hle : (ratDescend r N : ℝ) - r ≤ |(ratDescend r N : ℝ) - r| := le_abs_self _
      linarith
    exact (hdist.trans hqlt).le
  · intro hy
    refine mem_iInter.mpr fun n => mem_ball.mpr ?_
    exact (mem_closedBall.mp hy).trans_lt (ratDescend_gt r n)

/-- An open ball and its sphere are disjoint. -/
private lemma disjoint_ball_sphere {x : E} {r : ℝ} : Disjoint (ball x r) (sphere x r) := by
  rw [Set.disjoint_left]
  intro y hy hs
  exact (mem_ball.mp hy).ne (mem_sphere.mp hs)

/-- A measure vanishing on the sphere gives the same integral on the ball and the closed ball. -/
private lemma setLIntegral_closedBall_eq_ball {η : Measure E} {h : E → ℝ≥0∞} {x : E} {r : ℝ}
    (hsphere : η (sphere x r) = 0) :
    ∫⁻ y in closedBall x r, h y ∂η = ∫⁻ y in ball x r, h y ∂η := by
  calc ∫⁻ y in closedBall x r, h y ∂η
      = ∫⁻ y in ball x r ∪ sphere x r, h y ∂η := by rw [ball_union_sphere]
    _ = ∫⁻ y in ball x r, h y ∂η + ∫⁻ y in sphere x r, h y ∂η :=
        lintegral_union isClosed_sphere.measurableSet disjoint_ball_sphere
    _ = ∫⁻ y in ball x r, h y ∂η := by
        rw [setLIntegral_measure_zero _ h hsphere, add_zero]

/-- Indicators of the descending balls are antitone. -/
private lemma indicator_ratDescend_antitone {h : E → ℝ≥0∞} {x : E} {r : ℝ} :
    Antitone fun n => (ball x (ratDescend r n : ℝ)).indicator h := by
  intro m n hmn y
  have hsub : ball x (ratDescend r n : ℝ) ⊆ ball x (ratDescend r m : ℝ) :=
    ball_subset_ball (ratDescend_antitone r hmn)
  dsimp
  by_cases hy : y ∈ ball x (ratDescend r n : ℝ)
  · rw [indicator_of_mem hy, indicator_of_mem (hsub hy)]
  · rw [indicator_of_notMem hy]
    exact bot_le

/-- The infimum of the descending ball indicators is the closed-ball indicator. -/
private lemma iInf_indicator_ratDescend {h : E → ℝ≥0∞} {x : E} {r : ℝ} :
    ⨅ n, (ball x (ratDescend r n : ℝ)).indicator h = (closedBall x r).indicator h := by
  ext y
  simp only [iInf_apply]
  by_cases hy : y ∈ closedBall x r
  · rw [indicator_of_mem hy]
    have hyall : ∀ n, y ∈ ball x (ratDescend r n : ℝ) := fun n =>
      mem_ball.mpr ((mem_closedBall.mp hy).trans_lt (ratDescend_gt r n))
    have hterm : ∀ n, (ball x (ratDescend r n : ℝ)).indicator h y = h y := fun n =>
      indicator_of_mem (hyall n) h
    rw [iInf_congr hterm, iInf_const]
  · rw [indicator_of_notMem hy]
    have hnot : ∃ n, y ∉ ball x (ratDescend r n : ℝ) := by
      have hy' : y ∉ ⋂ n, ball x (ratDescend r n : ℝ) := by rwa [iInter_ball_ratDescend]
      simpa [mem_iInter] using hy'
    obtain ⟨n, hn⟩ := hnot
    apply le_antisymm
    · exact (iInf_le _ n).trans_eq (indicator_of_notMem hn h)
    · exact bot_le

/-- Ball integrals along `ratDescend` converge to the integral over the ball of radius `r`. -/
private lemma tendsto_setLIntegral_ratDescend {η : Measure E} {h : E → ℝ≥0∞} (hh : Measurable h)
    {x : E} {r : ℝ} (hsphere : η (sphere x r) = 0)
    (hfin0 : ∫⁻ y in ball x (ratDescend r 0 : ℝ), h y ∂η ≠ ∞) :
    Tendsto (fun n => ∫⁻ y in ball x (ratDescend r n : ℝ), h y ∂η) atTop
      (𝓝 (∫⁻ y in ball x r, h y ∂η)) := by
  let f : ℕ → E → ℝ≥0∞ := fun n => (ball x (ratDescend r n : ℝ)).indicator h
  have hfmeas : ∀ n, Measurable (f n) := fun n => hh.indicator measurableSet_ball
  have hanti : Antitone f := indicator_ratDescend_antitone
  have hint0 : ∫⁻ y, f 0 y ∂η ≠ ∞ := by
    rwa [lintegral_indicator measurableSet_ball]
  have hint : ∫⁻ y, (⨅ n, f n y) ∂η = ⨅ n, ∫⁻ y, f n y ∂η :=
    lintegral_iInf hfmeas hanti hint0
  have hclosed : ∫⁻ y in closedBall x r, h y ∂η = ⨅ n, ∫⁻ y in ball x (ratDescend r n), h y ∂η := by
    have hfun : ∫⁻ y, (⨅ n, f n y) ∂η = ∫⁻ y in closedBall x r, h y ∂η := by
      rw [← lintegral_indicator isClosed_closedBall.measurableSet]
      refine lintegral_congr fun y => ?_
      rw [← iInf_apply]
      exact congrFun iInf_indicator_ratDescend y
    rw [← hfun, hint]
    refine congrArg _ ?_
    ext n
    exact lintegral_indicator measurableSet_ball h
  have htend : Tendsto (fun n => ∫⁻ y in ball x (ratDescend r n), h y ∂η) atTop
      (𝓝 (∫⁻ y in closedBall x r, h y ∂η)) := by
    rw [hclosed]
    exact tendsto_atTop_iInf fun m n hmn => lintegral_mono_set (ball_subset_ball
      (ratDescend_antitone r hmn))
  simpa [setLIntegral_closedBall_eq_ball hsphere] using htend

/-- A real-radius ball average is at most the supremum of the positive-rational averages. -/
private lemma setLAverage_le_iSup_posRat {ρ h : E → ℝ≥0∞}
    (hh : Measurable h) {x : E} {r : ℝ} (hr : 0 < r)
    (hpos : ∀ s, 0 < s → volume.withDensity ρ (ball x s) ≠ 0)
    (hfin : ∀ s, 0 < s → volume.withDensity ρ (ball x s) ≠ ∞) :
    ⨍⁻ y in ball x r, h y ∂volume.withDensity ρ ≤
      ⨆ q : PosRat, ⨍⁻ y in ball x (q.1 : ℝ), h y ∂volume.withDensity ρ := by
  let η : Measure E := volume.withDensity ρ
  let S : PosRat → ℝ≥0∞ := fun q => ⨍⁻ y in ball x (q.1 : ℝ), h y ∂η
  have hsphere : η (sphere x r) = 0 := by
    rw [withDensity_apply _ isClosed_sphere.measurableSet]
    exact setLIntegral_measure_zero _ _ (Measure.addHaar_sphere_of_ne_zero volume x hr.ne')
  by_cases htop : ∫⁻ y in ball x (ratDescend r 0 : ℝ), h y ∂η = ∞
  · have hq : 0 < (ratDescend r 0 : ℝ) := lt_trans hr (ratDescend_gt r 0)
    let q0 : PosRat := ⟨ratDescend r 0, hq⟩
    refine le_iSup_of_le q0 ?_
    rw [show (q0.1 : ℝ) = (ratDescend r 0 : ℝ) by rfl]
    conv_rhs =>
      rw [setLAverage_eq, htop, ENNReal.top_div_of_ne_top (hfin _ hq)]
    exact le_top
  · have hpos0 : 0 < (ratDescend r 0 : ℝ) := lt_trans hr (ratDescend_gt r 0)
    have hden_fin : ∫⁻ _ in ball x (ratDescend r 0 : ℝ), (1 : ℝ≥0∞) ∂η ≠ ∞ := by
      rw [setLIntegral_one]
      exact hfin _ hpos0
    have hnum := tendsto_setLIntegral_ratDescend hh hsphere htop
    have hden_int := tendsto_setLIntegral_ratDescend measurable_const hsphere hden_fin
    have hden : Tendsto (fun n => η (ball x (ratDescend r n : ℝ))) atTop
        (𝓝 (η (ball x r))) := by
      simpa only [setLIntegral_one] using hden_int
    have hdiv := ENNReal.Tendsto.div hnum (Or.inr (hpos r hr)) hden (Or.inl (hfin r hr))
    have havg : Tendsto (fun n => ⨍⁻ y in ball x (ratDescend r n : ℝ), h y ∂η) atTop
        (𝓝 (⨍⁻ y in ball x r, h y ∂η)) := by
      simpa only [setLAverage_eq] using hdiv
    refine le_of_tendsto' havg fun n => ?_
    exact le_iSup S ⟨ratDescend r n, lt_trans hr (ratDescend_gt r n)⟩

/-- The centred maximal function is the supremum of its positive-rational ball averages. -/
private lemma maximalFunction_eq_iSup_posRat {ρ h : E → ℝ≥0∞} (hh : Measurable h)
    (hpos : ∀ x s, 0 < s → volume.withDensity ρ (ball x s) ≠ 0)
    (hfin : ∀ x s, 0 < s → volume.withDensity ρ (ball x s) ≠ ∞) (x : E) :
    TauCeti.maximalFunction (volume.withDensity ρ) h x =
      ⨆ q : PosRat, ⨍⁻ y in ball x (q.1 : ℝ), h y ∂volume.withDensity ρ := by
  apply le_antisymm
  · rw [TauCeti.maximalFunction_def]
    refine iSup₂_le fun r hr => ?_
    exact setLAverage_le_iSup_posRat hh hr (hpos x) (hfin x)
  · refine iSup_le fun q => ?_
    exact TauCeti.setLAverage_le_maximalFunction _ h x q.2

/-- The integrand of a ball of radius `q` centred at the first variable. -/
private def centerIntegrand (q : ℝ) (h : E → ℝ≥0∞) : E × E → ℝ≥0∞ :=
  fun p => if dist p.1 p.2 < q then h p.2 else 0

/-- `centerIntegrand` is jointly measurable for a measurable integrand. -/
private lemma measurable_centerIntegrand {h : E → ℝ≥0∞} (hh : Measurable h) (q : ℝ) :
    Measurable (centerIntegrand q h) := by
  refine Measurable.ite (measurableSet_lt measurable_dist measurable_const)
    (hh.comp measurable_snd) measurable_const

/-- The integral of a measurable function over `ball x q` is measurable in the centre `x`. -/
private lemma measurable_setLIntegral_ball {h : E → ℝ≥0∞} (hh : Measurable h) (q : ℝ) :
    Measurable fun x : E => ∫⁻ y in ball x q, h y ∂volume := by
  have hmeas : Measurable fun x => ∫⁻ y, centerIntegrand q h (x, y) ∂volume :=
    (measurable_centerIntegrand hh q).lintegral_prod_right'
  convert hmeas using 1
  ext x
  rw [← lintegral_indicator (measurableSet_ball : MeasurableSet (ball x q)) h]
  refine lintegral_congr fun y => ?_
  simp only [centerIntegrand, Set.indicator, mem_ball]
  rw [dist_comm]

/-- A fixed positive-radius weighted ball average is measurable in the centre. -/
private lemma measurable_setLAverage_withDensity {ρ h : E → ℝ≥0∞} (hρ : Measurable ρ)
    (hh : Measurable h) (q : ℝ) :
    Measurable fun x => ⨍⁻ y in ball x q, h y ∂volume.withDensity ρ := by
  have hnum : Measurable fun x => ∫⁻ y in ball x q, ρ y * h y ∂volume :=
    measurable_setLIntegral_ball (hρ.mul hh) q
  have hden : Measurable fun x => ∫⁻ y in ball x q, ρ y ∂volume :=
    measurable_setLIntegral_ball hρ q
  have hform : (fun z => ⨍⁻ y in ball z q, h y ∂volume.withDensity ρ) =
      fun z => (∫⁻ y in ball z q, ρ y * h y ∂volume) *
        (∫⁻ y in ball z q, ρ y ∂volume)⁻¹ := by
    ext z
    rw [setLAverage_eq, div_eq_mul_inv,
      setLIntegral_withDensity_eq_setLIntegral_mul volume hρ hh measurableSet_ball,
      withDensity_apply ρ measurableSet_ball]
    refine congrArg (fun t => t * (∫⁻ y in ball z q, ρ y ∂volume)⁻¹) ?_
    exact setLIntegral_congr_fun measurableSet_ball fun y _ => Pi.mul_apply ρ h y
  rw [hform]
  exact hnum.mul hden.inv

/-- The centred maximal function of a measurable density is measurable. -/
private lemma measurable_maximalFunction_withDensity_of_measurable {ρ h : E → ℝ≥0∞}
    (hρ : Measurable ρ) (hh : Measurable h)
    (hpos : ∀ x r, 0 < r → volume.withDensity ρ (ball x r) ≠ 0)
    (hfin : ∀ x r, 0 < r → volume.withDensity ρ (ball x r) ≠ ∞) :
    Measurable fun x => TauCeti.maximalFunction (volume.withDensity ρ) h x := by
  have hsup : Measurable fun x =>
      ⨆ q : PosRat, ⨍⁻ y in ball x (q.1 : ℝ), h y ∂volume.withDensity ρ :=
    .iSup fun q => measurable_setLAverage_withDensity hρ hh (q.1 : ℝ)
  convert hsup using 1
  ext x
  exact maximalFunction_eq_iSup_posRat hh hpos hfin x

/-- The centred maximal function on `volume.withDensity ρ` is measurable when every positive ball
has positive finite weighted measure. An almost-everywhere version of the integrand is replaced
by a measurable one; the maximal functions agree everywhere. -/
theorem measurable_maximalFunction_withDensity
    {ρ h : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hρ : Measurable ρ)
    (hh : AEMeasurable h (volume.withDensity ρ))
    (hpos : ∀ x r, 0 < r → volume.withDensity ρ (ball x r) ≠ 0)
    (hfin : ∀ x r, 0 < r → volume.withDensity ρ (ball x r) ≠ ∞) :
    Measurable fun x => TauCeti.maximalFunction (volume.withDensity ρ) h x := by
  let η : Measure E := volume.withDensity ρ
  let h' : E → ℝ≥0∞ := hh.mk h
  have hnorm : ∀ᵐ y ∂η, ‖h y‖ₑ = ‖h' y‖ₑ :=
    hh.ae_eq_mk.mono fun y hy => congrArg enorm hy
  have heq : ∀ x, TauCeti.maximalFunction η h x = TauCeti.maximalFunction η h' x :=
    fun x => TauCeti.maximalFunction_congr_ae hnorm
  have hfun : (fun x => TauCeti.maximalFunction (volume.withDensity ρ) h x) =
      fun x => TauCeti.maximalFunction (volume.withDensity ρ) h' x := funext heq
  rw [hfun]
  exact measurable_maximalFunction_withDensity_of_measurable hρ hh.measurable_mk hpos hfin

end CKMA
