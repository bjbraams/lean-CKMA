/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Semigroup.Inhomogeneous
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import CKMA.Analysis.Real.IntervalIntegral
import TauCeti.Analysis.Semigroups.Generator.OrbitDerivative
import TauCeti.Analysis.Semigroups.GrowthBound
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Classical solutions of the inhomogeneous Cauchy problem

For a strongly continuous semigroup `S` with generator `A` on a real Banach space, an initial
value `x ∈ D(A)` and a forcing `f` that is `C¹` on `[0, T]`, the variation-of-constants trajectory
`u(t) = S(t) x + ∫₀ᵗ S(t - s) f(s) ds` takes values in `D(A)` on `[0, T]` and satisfies
`u'(t) = A u(t) + f(t)` on `(0, T)`. Source: GAPS 24.13.

The proof writes the Duhamel term as `∫₀ᵗ S(s) f(t - s) ds`, computes its one-sided difference
quotients from the uniform continuity of `f'` on `[0, T]`, and identifies the generator on it from
the semigroup difference quotient.

## Main results

* `CKMA.variation_of_constants_classical`: the trajectory is a classical solution in the interior
  time interval, with values in the generator domain on `[0, T]`.

The one-variable facts on interval integrals and one-sided slopes are in
`CKMA.Analysis.Real.IntervalIntegral`.

## References

* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology TauCeti.Semigroups intervalIntegral
open scoped NNReal Interval

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A positive distance to `0` is the point itself. -/
private theorem lt_of_dist_Ioi {a δ : ℝ} (ha : 0 < a) (hdist : dist a 0 < δ) : a < δ := by
  rwa [Real.dist_eq, sub_zero, abs_of_pos ha] at hdist

/-- The weight `C t / (C t + 1)` is at most one, so this multiple of `ε` is at most `ε / 2`. -/
private theorem mul_div_two_le {C t ε : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) (hε : 0 ≤ ε) :
    C * t * (ε / (2 * (C * t + 1))) ≤ ε / 2 := by
  have hden : 0 < C * t + 1 := by linarith [mul_nonneg hC ht]
  have hfrac : C * t / (C * t + 1) ≤ 1 := by
    rw [div_le_one hden]
    linarith
  have hmul : C * t * (ε / (2 * (C * t + 1))) = ε / 2 * (C * t / (C * t + 1)) := by
    field_simp [(mul_ne_zero two_ne_zero hden.ne' : (2 : ℝ) * (C * t + 1) ≠ 0)]
  rw [hmul]
  exact mul_le_of_le_one_right (div_nonneg hε zero_le_two) hfrac

/-- Derivative within `[0, T]` of a forcing defined on that interval. -/
private def forcingDeriv (T : ℝ) (f : ℝ → X) : ℝ → X :=
  derivWithin f (Set.Icc 0 T)

omit [CompleteSpace X] in
/-- `forcingDeriv` is the derivative within the closed interval. -/
private theorem forcingDeriv_def (T : ℝ) (f : ℝ → X) :
    forcingDeriv T f = derivWithin f (Set.Icc 0 T) := rfl

omit [CompleteSpace X] in
/-- A `C¹` forcing has continuous derivative on the compact interval. -/
private theorem continuousOn_forcingDeriv {T : ℝ} {f : ℝ → X} (hT : 0 < T)
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 T)) :
    ContinuousOn (forcingDeriv T f) (Set.Icc 0 T) := by
  rw [forcingDeriv_def]
  exact hf.continuousOn_derivWithin (uniqueDiffOn_Icc hT) le_rfl

/-- On a subinterval of `[0, T]`, integrating the derivative recovers the increment of `f`. -/
private theorem integral_forcingDeriv_eq_sub {T : ℝ} {f : ℝ → X}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 T)) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hbT : b ≤ T) : ∫ s in a..b, forcingDeriv T f s = f b - f a := by
  have hsub : ContDiffOn ℝ 1 f (Set.Icc a b) := hf.mono (Set.Icc_subset_Icc ha0 hbT)
  rcases hab.eq_or_lt with rfl | hablt
  · rw [integral_same, sub_self]
  rw [← integral_derivWithin_Icc_of_contDiffOn_Icc hsub hablt.le, forcingDeriv_def]
  rw [integral_of_le hablt.le, integral_of_le hablt.le]
  refine integral_congr_ae ?_
  rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with s hs
  have hs0 : 0 < s := lt_of_le_of_lt ha0 hs.1
  have hsT : s < T := lt_of_lt_of_le hs.2 hbT
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hs0 hsT),
    derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)]

/-- The forward difference quotient of a `C¹` forcing is the average of its derivative. -/
private theorem forcingQuotient_eq_average {T : ℝ} {f : ℝ → X}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 T)) {y h : ℝ} (hy : 0 ≤ y) (hh : 0 < h)
    (hyh : y + h ≤ T) : h⁻¹ • (f (y + h) - f y) =
      h⁻¹ • ∫ r in (0 : ℝ)..h, forcingDeriv T f (y + r) := by
  have hftc := integral_forcingDeriv_eq_sub hf hy (by linarith) hyh
  have hcomm : ∫ r in (0 : ℝ)..h, forcingDeriv T f (y + r) =
      ∫ r in (0 : ℝ)..h, forcingDeriv T f (r + y) :=
    integral_congr fun _ _ => by rw [add_comm]
  rw [hcomm, integral_comp_add_right (forcingDeriv T f) y, zero_add, add_comm h y, hftc]

/-- Uniform continuity of the derivative makes forward quotients uniformly close to it. -/
private theorem exists_forcingQuotient_close {T : ℝ} {f : ℝ → X} (hT : 0 < T)
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 T)) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ {y h : ℝ}, 0 ≤ y → 0 < h → h ≤ δ → y + h ≤ T →
      ‖h⁻¹ • (f (y + h) - f y) - forcingDeriv T f y‖ ≤ η := by
  have hdf := continuousOn_forcingDeriv hT hf
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hdf
  rw [Metric.uniformContinuousOn_iff_le] at huc
  obtain ⟨δ, hδ0, hδ⟩ := huc η hη
  refine ⟨δ, hδ0, fun {y h} hy hh hle hyh => ?_⟩
  rw [forcingQuotient_eq_average hf hy hh hyh]
  refine norm_inv_smul_intervalIntegral_sub_le hh ?_ fun r hr => ?_
  · refine hdf.comp' (continuous_const_add y).continuousOn fun r hr => ?_
    refine ⟨add_nonneg hy hr.1, le_trans ?_ hyh⟩
    have hle' : r + y ≤ h + y := add_le_add_left hr.2 y
    rwa [add_comm r y, add_comm h y] at hle'
  · have hyT : y ≤ T := le_trans (le_add_of_nonneg_right hh.le) hyh
    have hdist : dist (y + r) y ≤ δ := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hr.1]
      exact hr.2.trans hle
    have hyr : y + r ≤ y + h := by
      have hle' : r + y ≤ h + y := add_le_add_left hr.2 y
      rwa [add_comm r y, add_comm h y] at hle'
    have hleη := hδ (y + r) ⟨add_nonneg hy hr.1, le_trans hyr hyh⟩ y ⟨hy, hyT⟩ hdist
    rwa [dist_eq_norm] at hleη

/-- `s ↦ S(s) (f (c - s))` is continuous where every forcing argument stays in `[0, T]`. -/
private theorem continuousOn_elapsed_forcing (S : StronglyContinuousSemigroup X) {T : ℝ}
    {f : ℝ → X} (hf : ContinuousOn f (Set.Icc 0 T)) {c : ℝ} {s : Set ℝ}
    (hmem : ∀ u ∈ s, c - u ∈ Set.Icc 0 T) :
    ContinuousOn (fun u => S.realOperator u (f (c - u))) s := by
  refine S.continuousOn_realOperator_apply continuous_id.continuousOn
    (hf.comp' (continuous_const.sub continuous_id).continuousOn hmem)

omit [CompleteSpace X] in
/-- Substitution putting the elapsed time in the semigroup argument of a Duhamel integral. -/
private theorem duhamel_eq_shifted (S : StronglyContinuousSemigroup X) (f : ℝ → X) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, S.realOperator (t - s) (f s)) =
      ∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s)) := by
  have hsub := integral_comp_sub_left (fun s => S.realOperator s (f (t - s))) (a := 0) (b := t) t
  have hcongr : (∫ s in (0 : ℝ)..t, S.realOperator (t - s) (f s)) =
      ∫ s in (0 : ℝ)..t, S.realOperator (t - s) (f (t - (t - s))) :=
    integral_congr fun _ _ => by rw [sub_sub_cancel]
  rw [hcongr]
  simpa [sub_self, sub_zero] using hsub

omit [CompleteSpace X] in
/-- The variation-of-constants trajectory is the shifted Duhamel formula. -/
private theorem forced_eq_shifted (S : StronglyContinuousSemigroup X) (x : X) (f : ℝ → X)
    (t : ℝ) : forcedSemigroupTrajectory S x f t =
      S.realOperator t x + ∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s)) := by
  rw [forcedSemigroupTrajectory, duhamel_eq_shifted]

/-- Forward increment of the shifted Duhamel integral, split at the old upper limit. -/
private theorem shiftedDuhamel_sub_right (S : StronglyContinuousSemigroup X) {T : ℝ}
    {f : ℝ → X} (hf : ContinuousOn f (Set.Icc 0 T)) {t h : ℝ} (ht0 : 0 ≤ t) (hh : 0 < h)
    (hth : t + h ≤ T) :
    (∫ s in (0 : ℝ)..(t + h), S.realOperator s (f (t + h - s))) -
        ∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s)) =
      (∫ s in (0 : ℝ)..t, S.realOperator s (f (t + h - s) - f (t - s))) +
        ∫ s in t..(t + h), S.realOperator s (f (t + h - s)) := by
  have htT : t ≤ T := le_trans (le_add_of_nonneg_right hh.le) hth
  have hht : t ≤ t + h := le_add_of_nonneg_right hh.le
  have hcontψ : ContinuousOn (fun s => S.realOperator s (f (t + h - s)))
      (Set.Icc 0 (t + h)) :=
    continuousOn_elapsed_forcing S hf fun u hu =>
      ⟨by linarith [hu.2], by linarith [hu.1, hth]⟩
  have hcontφ : ContinuousOn (fun s => S.realOperator s (f (t - s))) (Set.Icc 0 t) :=
    continuousOn_elapsed_forcing S hf fun u hu =>
      ⟨by linarith [hu.2], by linarith [hu.1, htT]⟩
  have hintψ0 : IntervalIntegrable (fun s => S.realOperator s (f (t + h - s))) volume 0 t :=
    (hcontψ.mono (Set.Icc_subset_Icc_right hht)).intervalIntegrable_of_Icc ht0
  have hintψ1 : IntervalIntegrable (fun s => S.realOperator s (f (t + h - s))) volume t (t + h) :=
    (hcontψ.mono (Set.Icc_subset_Icc_left ht0)).intervalIntegrable_of_Icc hht
  have hintφ : IntervalIntegrable (fun s => S.realOperator s (f (t - s))) volume 0 t :=
    hcontφ.intervalIntegrable_of_Icc ht0
  have hsplit := integral_add_adjacent_intervals hintψ0 hintψ1
  have hdiff : ∫ s in (0 : ℝ)..t,
      (S.realOperator s (f (t + h - s)) - S.realOperator s (f (t - s))) =
      (∫ s in (0 : ℝ)..t, S.realOperator s (f (t + h - s))) -
        ∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s)) := integral_sub hintψ0 hintφ
  have hmap : ∫ s in (0 : ℝ)..t, S.realOperator s (f (t + h - s) - f (t - s)) =
      ∫ s in (0 : ℝ)..t,
        (S.realOperator s (f (t + h - s)) - S.realOperator s (f (t - s))) :=
    integral_congr fun s _ => (S.realOperator s).map_sub _ _
  calc (∫ s in (0 : ℝ)..(t + h), S.realOperator s (f (t + h - s))) -
        ∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s))
      = ((∫ s in (0 : ℝ)..t, S.realOperator s (f (t + h - s))) +
          ∫ s in t..(t + h), S.realOperator s (f (t + h - s))) -
          ∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s)) := by rw [hsplit]
    _ = ((∫ s in (0 : ℝ)..t, S.realOperator s (f (t + h - s))) -
          ∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s))) +
          ∫ s in t..(t + h), S.realOperator s (f (t + h - s)) := by abel
    _ = (∫ s in (0 : ℝ)..t,
          (S.realOperator s (f (t + h - s)) - S.realOperator s (f (t - s)))) +
          ∫ s in t..(t + h), S.realOperator s (f (t + h - s)) := by rw [hdiff]
    _ = (∫ s in (0 : ℝ)..t, S.realOperator s (f (t + h - s) - f (t - s))) +
          ∫ s in t..(t + h), S.realOperator s (f (t + h - s)) := by rw [hmap]

/-- Backward increment of the shifted Duhamel integral, split at the new upper limit. -/
private theorem shiftedDuhamel_sub_left (S : StronglyContinuousSemigroup X) {T : ℝ}
    {f : ℝ → X} (hf : ContinuousOn f (Set.Icc 0 T)) {t k : ℝ} (hk0 : 0 < k) (hkt : k ≤ t)
    (htT : t ≤ T) :
    (∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s))) -
        ∫ s in (0 : ℝ)..(t - k), S.realOperator s (f (t - k - s)) =
      (∫ s in (0 : ℝ)..(t - k), S.realOperator s (f (t - s) - f (t - k - s))) +
        ∫ s in (t - k)..t, S.realOperator s (f (t - s)) := by
  have ht0 : 0 ≤ t - k := sub_nonneg.mpr hkt
  have htk : t - k ≤ t := sub_le_self t hk0.le
  have hcontφ : ContinuousOn (fun s => S.realOperator s (f (t - s))) (Set.Icc 0 t) :=
    continuousOn_elapsed_forcing S hf fun u hu =>
      ⟨by linarith [hu.2], by linarith [hu.1, htT]⟩
  have hcontψ : ContinuousOn (fun s => S.realOperator s (f (t - k - s))) (Set.Icc 0 (t - k)) :=
    continuousOn_elapsed_forcing S hf fun u hu =>
      ⟨by linarith [hu.2], by linarith [hu.1, hk0.le, htT]⟩
  have hintφ0 : IntervalIntegrable (fun s => S.realOperator s (f (t - s))) volume 0 (t - k) :=
    (hcontφ.mono (Set.Icc_subset_Icc_right htk)).intervalIntegrable_of_Icc ht0
  have hintφ1 : IntervalIntegrable (fun s => S.realOperator s (f (t - s))) volume (t - k) t :=
    (hcontφ.mono (Set.Icc_subset_Icc_left ht0)).intervalIntegrable_of_Icc htk
  have hintψ : IntervalIntegrable (fun s => S.realOperator s (f (t - k - s))) volume 0 (t - k) :=
    hcontψ.intervalIntegrable_of_Icc ht0
  have hsplit := integral_add_adjacent_intervals hintφ0 hintφ1
  have hdiff : ∫ s in (0 : ℝ)..(t - k),
      (S.realOperator s (f (t - s)) - S.realOperator s (f (t - k - s))) =
      (∫ s in (0 : ℝ)..(t - k), S.realOperator s (f (t - s))) -
        ∫ s in (0 : ℝ)..(t - k), S.realOperator s (f (t - k - s)) :=
    integral_sub hintφ0 hintψ
  have hmap : ∫ s in (0 : ℝ)..(t - k), S.realOperator s (f (t - s) - f (t - k - s)) =
      ∫ s in (0 : ℝ)..(t - k),
        (S.realOperator s (f (t - s)) - S.realOperator s (f (t - k - s))) :=
    integral_congr fun s _ => (S.realOperator s).map_sub _ _
  calc (∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s))) -
        ∫ s in (0 : ℝ)..(t - k), S.realOperator s (f (t - k - s))
      = ((∫ s in (0 : ℝ)..(t - k), S.realOperator s (f (t - s))) +
          ∫ s in (t - k)..t, S.realOperator s (f (t - s))) -
          ∫ s in (0 : ℝ)..(t - k), S.realOperator s (f (t - k - s)) := by rw [hsplit]
    _ = ((∫ s in (0 : ℝ)..(t - k), S.realOperator s (f (t - s))) -
          ∫ s in (0 : ℝ)..(t - k), S.realOperator s (f (t - k - s))) +
          ∫ s in (t - k)..t, S.realOperator s (f (t - s)) := by abel
    _ = (∫ s in (0 : ℝ)..(t - k),
          (S.realOperator s (f (t - s)) - S.realOperator s (f (t - k - s)))) +
          ∫ s in (t - k)..t, S.realOperator s (f (t - s)) := by rw [hdiff]
    _ = (∫ s in (0 : ℝ)..(t - k), S.realOperator s (f (t - s) - f (t - k - s))) +
          ∫ s in (t - k)..t, S.realOperator s (f (t - s)) := by rw [hmap]

/-- Semigroup translate of a shifted Duhamel integral, split into three orbit integrals. -/
private theorem realOperator_sub_shiftedDuhamel (S : StronglyContinuousSemigroup X) {T : ℝ}
    {f : ℝ → X} (hf : ContinuousOn f (Set.Icc 0 T)) {t h : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hh : 0 < h) (hht : h ≤ t) :
    S.realOperator h (∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s))) -
        ∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s)) =
      (∫ u in h..t, S.realOperator u (f (t + h - u) - f (t - u))) +
        (∫ u in t..(t + h), S.realOperator u (f (t + h - u))) -
        ∫ u in (0 : ℝ)..h, S.realOperator u (f (t - u)) := by
  have hbase : ContinuousOn (fun s => S.realOperator s (f (t - s))) (Set.Icc 0 t) :=
    continuousOn_elapsed_forcing S hf fun u hu =>
      ⟨by linarith [hu.2], by linarith [hu.1, htT]⟩
  have hshift : ContinuousOn (fun u => S.realOperator u (f (t + h - u)))
      (Set.Icc h (t + h)) :=
    continuousOn_elapsed_forcing S hf fun u hu =>
      ⟨by linarith [hu.2], by linarith [hu.1, htT]⟩
  have hintBase : IntervalIntegrable (fun s => S.realOperator s (f (t - s))) volume 0 t :=
    hbase.intervalIntegrable_of_Icc ht0
  have hpush : S.realOperator h (∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s))) =
      ∫ u in h..(t + h), S.realOperator u (f (t + h - u)) := by
    rw [← (S.realOperator h).intervalIntegral_comp_comm hintBase]
    have hpt : ∫ s in (0 : ℝ)..t, S.realOperator h (S.realOperator s (f (t - s))) =
        ∫ s in (0 : ℝ)..t, S.realOperator (s + h) (f (t - s)) := by
      refine integral_congr fun s hs => ?_
      have hs0 : 0 ≤ s := by
        rw [Set.uIcc_of_le ht0] at hs
        exact hs.1
      rw [add_comm s h]
      exact (S.realOperator_add_apply h s hh.le hs0 _).symm
    rw [hpt]
    have hintegrand : ∫ s in (0 : ℝ)..t, S.realOperator (s + h) (f (t - s)) =
        ∫ s in (0 : ℝ)..t, S.realOperator (s + h) (f (t + h - (s + h))) :=
      integral_congr fun s _ => by
        have harg : t - s = t + h - (s + h) := by ring
        rw [harg]
    rw [hintegrand, integral_comp_add_right (fun u => S.realOperator u (f (t + h - u))) h,
      zero_add]
  have hintLeft : IntervalIntegrable (fun u => S.realOperator u (f (t - u))) volume 0 h :=
    (hbase.mono (Set.Icc_subset_Icc_right hht)).intervalIntegrable_of_Icc hh.le
  have hintMidBase : IntervalIntegrable (fun u => S.realOperator u (f (t - u))) volume h t :=
    (hbase.mono (Set.Icc_subset_Icc_left hh.le)).intervalIntegrable_of_Icc hht
  have hintMidShift : IntervalIntegrable (fun u => S.realOperator u (f (t + h - u)))
      volume h t := by
    refine (hshift.mono ?_).intervalIntegrable_of_Icc hht
    exact Set.Icc_subset_Icc_right (le_add_of_nonneg_right hh.le)
  have hintRight : IntervalIntegrable (fun u => S.realOperator u (f (t + h - u)))
      volume t (t + h) :=
    (hshift.mono (Set.Icc_subset_Icc_left hht)).intervalIntegrable_of_Icc
      (le_add_of_nonneg_right hh.le)
  have hsplitShift := integral_add_adjacent_intervals hintMidShift hintRight
  have hsplitBase := integral_add_adjacent_intervals hintLeft hintMidBase
  have hdiff : ∫ u in h..t,
      (S.realOperator u (f (t + h - u)) - S.realOperator u (f (t - u))) =
      (∫ u in h..t, S.realOperator u (f (t + h - u))) -
        ∫ u in h..t, S.realOperator u (f (t - u)) := integral_sub hintMidShift hintMidBase
  have hmap : ∫ u in h..t, S.realOperator u (f (t + h - u) - f (t - u)) =
      ∫ u in h..t, (S.realOperator u (f (t + h - u)) - S.realOperator u (f (t - u))) :=
    integral_congr fun u _ => (S.realOperator u).map_sub _ _
  calc S.realOperator h (∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s))) -
        ∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s))
      = (∫ u in h..(t + h), S.realOperator u (f (t + h - u))) -
          ∫ u in (0 : ℝ)..t, S.realOperator u (f (t - u)) := by rw [hpush]
    _ = ((∫ u in h..t, S.realOperator u (f (t + h - u))) +
          ∫ u in t..(t + h), S.realOperator u (f (t + h - u))) -
          ((∫ u in (0 : ℝ)..h, S.realOperator u (f (t - u))) +
            ∫ u in h..t, S.realOperator u (f (t - u))) := by
        rw [hsplitShift, hsplitBase]
    _ = ((∫ u in h..t, S.realOperator u (f (t + h - u))) -
          ∫ u in h..t, S.realOperator u (f (t - u))) +
          (∫ u in t..(t + h), S.realOperator u (f (t + h - u))) -
          ∫ u in (0 : ℝ)..h, S.realOperator u (f (t - u)) := by abel
    _ = (∫ u in h..t,
          (S.realOperator u (f (t + h - u)) - S.realOperator u (f (t - u)))) +
          (∫ u in t..(t + h), S.realOperator u (f (t + h - u))) -
          ∫ u in (0 : ℝ)..h, S.realOperator u (f (t - u)) := by rw [hdiff]
    _ = (∫ u in h..t, S.realOperator u (f (t + h - u) - f (t - u))) +
          (∫ u in t..(t + h), S.realOperator u (f (t + h - u))) -
          ∫ u in (0 : ℝ)..h, S.realOperator u (f (t - u)) := by rw [hmap]

/-- The forward boundary average of an orbit tends to the orbit of the initial forcing. -/
private theorem tendsto_shiftBoundary (S : StronglyContinuousSemigroup X) {T : ℝ} {f : ℝ → X}
    (hT : 0 < T) (hf : ContinuousOn f (Set.Icc 0 T)) {t : ℝ} (ht0 : 0 ≤ t) :
    Tendsto (fun h : ℝ => h⁻¹ • ∫ u in t..(t + h), S.realOperator u (f (t + h - u)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (S.realOperator t (f 0))) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  let K := Set.Icc (0 : ℝ) (t + 1) ×ˢ Set.Icc 0 T
  have hcont : ContinuousOn (fun p : ℝ × ℝ => S.realOperator p.1 (f p.2)) K :=
    S.continuousOn_realOperator_apply continuous_fst.continuousOn
      (hf.comp' continuous_snd.continuousOn fun p hp => hp.2)
  have huc := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff_le] at huc
  obtain ⟨δ, hδ0, hδ⟩ := huc (ε / 2) (half_pos hε)
  refine ⟨min δ (min 1 T), lt_min hδ0 (lt_min one_pos hT), fun h hh hdist => ?_⟩
  have hh0 : 0 < h := hh
  have hmin := lt_min_iff.mp (lt_of_dist_Ioi hh0 hdist)
  have hhδ : h ≤ δ := hmin.1.le
  have hh1 : h ≤ 1 := (lt_min_iff.mp hmin.2).1.le
  have hhT : h ≤ T := (lt_min_iff.mp hmin.2).2.le
  let c : X := S.realOperator t (f 0)
  have hcontF : ContinuousOn (fun u => S.realOperator u (f (t + h - u)))
      (Set.Icc t (t + h)) :=
    continuousOn_elapsed_forcing S hf fun u hu =>
      ⟨by linarith [hu.2], by linarith [hu.1, hhT]⟩
  have hintF : IntervalIntegrable (fun u => S.realOperator u (f (t + h - u))) volume t (t + h) :=
    hcontF.intervalIntegrable_of_Icc (le_add_of_nonneg_right hh0.le)
  have hintC : IntervalIntegrable (fun _ : ℝ => c) volume t (t + h) :=
    continuousOn_const.intervalIntegrable_of_Icc (le_add_of_nonneg_right hh0.le)
  have hlen : (t + h) - t = h := by ring
  have hsplit : (h⁻¹ • ∫ u in t..(t + h), S.realOperator u (f (t + h - u))) - c =
      h⁻¹ • ∫ u in t..(t + h), (S.realOperator u (f (t + h - u)) - c) := by
    rw [integral_sub hintF hintC, intervalIntegral.integral_const, hlen, smul_sub, smul_smul,
      inv_mul_cancel₀ hh0.ne', one_smul]
  have hpoint : ∀ u ∈ Ι t (t + h), ‖S.realOperator u (f (t + h - u)) - c‖ ≤ ε / 2 := by
    intro u hu
    rw [Set.uIoc_of_le (le_add_of_nonneg_right hh0.le)] at hu
    have hu0 : 0 ≤ u := ht0.trans hu.1.le
    have hu1 : u ≤ t + 1 := by linarith [hh1, hu.2]
    have harg0 : 0 ≤ t + h - u := by linarith [hu.2]
    have hargT : t + h - u ≤ T := by linarith [hhT, hu.1.le]
    have hdistp : dist (u, t + h - u) (t, (0 : ℝ)) ≤ δ := by
      simp only [Prod.dist_eq]
      rw [Real.dist_eq, Real.dist_eq, sub_zero,
        abs_of_nonneg (by linarith [hu.1] : 0 ≤ u - t), abs_of_nonneg harg0]
      exact max_le (by linarith [hu.2, hhδ]) (by linarith [hu.1, hhδ])
    have hle := hδ (u, t + h - u) ⟨⟨hu0, hu1⟩, ⟨harg0, hargT⟩⟩ (t, (0 : ℝ))
      ⟨⟨ht0, by linarith⟩, ⟨le_rfl, hT.le⟩⟩ hdistp
    rwa [dist_eq_norm] at hle
  have hnorm := norm_integral_le_of_norm_le_const hpoint
  have hfin : ‖h⁻¹ • ∫ u in t..(t + h), (S.realOperator u (f (t + h - u)) - c)‖ ≤ ε / 2 := by
    calc ‖h⁻¹ • ∫ u in t..(t + h), (S.realOperator u (f (t + h - u)) - c)‖
        = h⁻¹ * ‖∫ u in t..(t + h), (S.realOperator u (f (t + h - u)) - c)‖ := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hh0.le)]
      _ ≤ h⁻¹ * ((ε / 2) * h) := by
          rw [add_sub_cancel_left, abs_of_pos hh0] at hnorm
          exact mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hh0.le)
      _ = ε / 2 := by rw [mul_comm (ε / 2) h, ← mul_assoc, inv_mul_cancel₀ hh0.ne', one_mul]
  rw [dist_eq_norm, hsplit]
  exact hfin.trans_lt (half_lt_self hε)

/-- An orbit integral of a uniformly small increment is controlled by the operator bound. -/
private theorem norm_scaled_orbit_sub_le (S : StronglyContinuousSemigroup X) {a b c C η : ℝ}
    {p q d : ℝ → X} (hab : a ≤ b) (hC : 0 ≤ C)
    (hbound : ∀ s : ℝ, a ≤ s → s ≤ b → ‖S.realOperator s‖ ≤ C)
    (hp : ContinuousOn p (Set.Icc a b)) (hq : ContinuousOn q (Set.Icc a b))
    (hd : ContinuousOn d (Set.Icc a b))
    (hclose : ∀ s ∈ Set.Icc a b, ‖c • (p s - q s) - d s‖ ≤ η) :
    ‖(c • ∫ s in a..b, S.realOperator s (p s - q s)) -
        ∫ s in a..b, S.realOperator s (d s)‖ ≤ C * η * (b - a) := by
  have hcontDiff : ContinuousOn (fun s => p s - q s) (Set.Icc a b) := hp.sub hq
  have hcontScaled : ContinuousOn (fun s => c • (p s - q s)) (Set.Icc a b) :=
    hcontDiff.const_smul c
  have hintScaled : IntervalIntegrable (fun s => S.realOperator s (c • (p s - q s)))
      volume a b :=
    (S.continuousOn_realOperator_apply continuous_id.continuousOn
      hcontScaled).intervalIntegrable_of_Icc hab
  have hintD : IntervalIntegrable (fun s => S.realOperator s (d s)) volume a b :=
    (S.continuousOn_realOperator_apply continuous_id.continuousOn hd).intervalIntegrable_of_Icc hab
  have hsmul : ∫ s in a..b, S.realOperator s (c • (p s - q s)) =
      c • ∫ s in a..b, S.realOperator s (p s - q s) := by
    rw [integral_congr (fun s _ => (S.realOperator s).map_smul c (p s - q s)),
      intervalIntegral.integral_smul]
  have hlin : ∫ s in a..b, S.realOperator s (c • (p s - q s) - d s) =
      ∫ s in a..b, (S.realOperator s (c • (p s - q s)) - S.realOperator s (d s)) :=
    integral_congr fun s _ => (S.realOperator s).map_sub _ _
  have hsub : ∫ s in a..b, (S.realOperator s (c • (p s - q s)) - S.realOperator s (d s)) =
      (∫ s in a..b, S.realOperator s (c • (p s - q s))) -
        ∫ s in a..b, S.realOperator s (d s) :=
    intervalIntegral.integral_sub hintScaled hintD
  have heq : (c • ∫ s in a..b, S.realOperator s (p s - q s)) -
      ∫ s in a..b, S.realOperator s (d s) =
      ∫ s in a..b, S.realOperator s (c • (p s - q s) - d s) := by
    rw [← hsmul, ← hsub, ← hlin]
  rw [heq]
  have hpoint : ∀ s ∈ Ι a b, ‖S.realOperator s (c • (p s - q s) - d s)‖ ≤ C * η := by
    intro s hs
    rw [Set.uIoc_of_le hab] at hs
    have hsI : s ∈ Set.Icc a b := ⟨hs.1.le, hs.2⟩
    calc ‖S.realOperator s (c • (p s - q s) - d s)‖
        ≤ ‖S.realOperator s‖ * ‖c • (p s - q s) - d s‖ :=
          (S.realOperator s).le_opNorm _
      _ ≤ C * ‖c • (p s - q s) - d s‖ :=
          mul_le_mul_of_nonneg_right (hbound s hsI.1 hsI.2) (norm_nonneg _)
      _ ≤ C * η := mul_le_mul_of_nonneg_left (hclose s hsI) hC
  have hnorm := norm_integral_le_of_norm_le_const hpoint
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hnorm
  exact hnorm

/-- The orbit of the closed-interval derivative stays continuous on a subinterval. -/
private theorem continuousOn_orbitDeriv (S : StronglyContinuousSemigroup X) {T : ℝ}
    (hT : 0 < T) {f : ℝ → X} (hf : ContDiffOn ℝ 1 f (Set.Icc 0 T)) {t : ℝ} (htT : t ≤ T) :
    ContinuousOn (fun s => S.realOperator s (forcingDeriv T f (t - s))) (Set.Icc 0 t) := by
  refine S.continuousOn_realOperator_apply continuous_id.continuousOn ?_
  refine (continuousOn_forcingDeriv hT hf).comp'
    (continuous_const.sub continuous_id).continuousOn fun s hs =>
      ⟨by linarith [hs.2], by linarith [hs.1, htT]⟩

/-- The backward boundary average of an orbit tends to the orbit of the initial forcing. -/
private theorem tendsto_leftBoundary (S : StronglyContinuousSemigroup X) {T : ℝ} {f : ℝ → X}
    (hT : 0 < T) (hf : ContinuousOn f (Set.Icc 0 T)) {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T) :
    Tendsto (fun k : ℝ => k⁻¹ • ∫ u in (t - k)..t, S.realOperator u (f (t - u)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (S.realOperator t (f 0))) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  let K := Set.Icc (0 : ℝ) T ×ˢ Set.Icc 0 T
  have hcont : ContinuousOn (fun p : ℝ × ℝ => S.realOperator p.1 (f p.2)) K :=
    S.continuousOn_realOperator_apply continuous_fst.continuousOn
      (hf.comp' continuous_snd.continuousOn fun p hp => hp.2)
  have huc := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff_le] at huc
  obtain ⟨δ, hδ0, hδ⟩ := huc (ε / 2) (half_pos hε)
  refine ⟨min δ t, lt_min hδ0 ht0, fun k hk hdist => ?_⟩
  have hk0 : 0 < k := hk
  have hmin := lt_min_iff.mp (lt_of_dist_Ioi hk0 hdist)
  have hkδ : k ≤ δ := hmin.1.le
  have hkt : k ≤ t := hmin.2.le
  let c : X := S.realOperator t (f 0)
  have hcontF : ContinuousOn (fun u => S.realOperator u (f (t - u))) (Set.Icc (t - k) t) :=
    continuousOn_elapsed_forcing S hf fun u hu =>
      ⟨by linarith [hu.2], by linarith [hu.1, hkt, htT]⟩
  have hintF : IntervalIntegrable (fun u => S.realOperator u (f (t - u))) volume (t - k) t :=
    hcontF.intervalIntegrable_of_Icc (by linarith)
  have hintC : IntervalIntegrable (fun _ : ℝ => c) volume (t - k) t :=
    continuousOn_const.intervalIntegrable_of_Icc (by linarith)
  have hlen : t - (t - k) = k := by ring
  have hsplit : (k⁻¹ • ∫ u in (t - k)..t, S.realOperator u (f (t - u))) - c =
      k⁻¹ • ∫ u in (t - k)..t, (S.realOperator u (f (t - u)) - c) := by
    rw [integral_sub hintF hintC, intervalIntegral.integral_const, hlen, smul_sub, smul_smul,
      inv_mul_cancel₀ hk0.ne', one_smul]
  have hpoint : ∀ u ∈ Ι (t - k) t, ‖S.realOperator u (f (t - u)) - c‖ ≤ ε / 2 := by
    intro u hu
    rw [Set.uIoc_of_le (by linarith : t - k ≤ t)] at hu
    have hu0 : 0 ≤ u := by linarith [hkt, hu.1]
    have huT : u ≤ T := le_trans hu.2 htT
    have harg0 : 0 ≤ t - u := by linarith [hu.2]
    have hargT : t - u ≤ T := by linarith [hu.1, hkt, htT]
    have hdistp : dist (u, t - u) (t, (0 : ℝ)) ≤ δ := by
      simp only [Prod.dist_eq]
      have hgap : u - t = -(t - u) := by ring
      rw [Real.dist_eq, Real.dist_eq, sub_zero, hgap, abs_neg, abs_of_nonneg harg0]
      exact max_le (by linarith [hu.1, hkδ]) (by linarith [hu.1, hkδ])
    have hle := hδ (u, t - u) ⟨⟨hu0, huT⟩, ⟨harg0, hargT⟩⟩ (t, (0 : ℝ))
      ⟨⟨ht0.le, htT⟩, ⟨le_rfl, hT.le⟩⟩ hdistp
    rwa [dist_eq_norm] at hle
  have hnorm := norm_integral_le_of_norm_le_const hpoint
  have hfin : ‖k⁻¹ • ∫ u in (t - k)..t, (S.realOperator u (f (t - u)) - c)‖ ≤ ε / 2 := by
    calc ‖k⁻¹ • ∫ u in (t - k)..t, (S.realOperator u (f (t - u)) - c)‖
        = k⁻¹ * ‖∫ u in (t - k)..t, (S.realOperator u (f (t - u)) - c)‖ := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hk0.le)]
      _ ≤ k⁻¹ * ((ε / 2) * k) := by
          rw [hlen, abs_of_pos hk0] at hnorm
          exact mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hk0.le)
      _ = ε / 2 := by rw [mul_comm (ε / 2) k, ← mul_assoc, inv_mul_cancel₀ hk0.ne', one_mul]
  rw [dist_eq_norm, hsplit]
  exact hfin.trans_lt (half_lt_self hε)

omit [CompleteSpace X] in
/-- A backward forcing quotient is close to the derivative when the derivative is uniformly
continuous. -/
private theorem backwardQuotient_close {T : ℝ} {f : ℝ → X} {ζ δf δd : ℝ}
    (hδf : ∀ {y h : ℝ}, 0 ≤ y → 0 < h → h ≤ δf → y + h ≤ T →
      ‖h⁻¹ • (f (y + h) - f y) - forcingDeriv T f y‖ ≤ ζ / 2)
    (hδd : ∀ x ∈ Set.Icc 0 T, ∀ y ∈ Set.Icc 0 T, dist x y ≤ δd →
      dist (forcingDeriv T f x) (forcingDeriv T f y) ≤ ζ / 2)
    {t k s : ℝ} (hk0 : 0 < k) (hkf : k ≤ δf) (hkd : k ≤ δd) (htT : t ≤ T)
    (hs0 : 0 ≤ s) (hsk : s ≤ t - k) :
    ‖k⁻¹ • (f (t - s) - f (t - k - s)) - forcingDeriv T f (t - s)‖ ≤ ζ := by
  have hy : 0 ≤ t - s - k := by linarith
  have hyh : (t - s - k) + k ≤ T := by
    have : (t - s - k) + k = t - s := by ring
    linarith [hs0, htT]
  have hle := hδf hy hk0 hkf hyh
  have hz : (t - s - k) + k = t - s := by ring
  rw [hz] at hle
  have hsub : t - k - s = t - s - k := by ring
  have hmem1 : t - s - k ∈ Set.Icc 0 T := ⟨hy, by linarith [hs0, htT]⟩
  have hmem2 : t - s ∈ Set.Icc 0 T := ⟨by linarith, by linarith [hs0, htT]⟩
  have hdist : dist (t - s - k) (t - s) ≤ δd := by
    have harg : (t - s - k) - (t - s) = -k := by ring
    rw [Real.dist_eq, harg, abs_neg, abs_of_pos hk0]
    exact hkd
  have hosc := hδd _ hmem1 _ hmem2 hdist
  rw [dist_eq_norm] at hosc
  rw [hsub]
  have hsplit : k⁻¹ • (f (t - s) - f (t - s - k)) - forcingDeriv T f (t - s) =
      (k⁻¹ • (f (t - s) - f (t - s - k)) - forcingDeriv T f (t - s - k)) +
        (forcingDeriv T f (t - s - k) - forcingDeriv T f (t - s)) := by
    abel
  rw [hsplit]
  have hhalf : ζ / 2 + ζ / 2 = ζ := by ring
  rw [← hhalf]
  exact le_trans (norm_add_le _ _) (add_le_add hle hosc)

/-- Right difference quotients of the shifted Duhamel integral. -/
private theorem tendsto_rightQuotient_shiftedDuhamel (S : StronglyContinuousSemigroup X)
    {T : ℝ} (hT : 0 < T) {f : ℝ → X} (hf : ContDiffOn ℝ 1 f (Set.Icc 0 T)) {t : ℝ}
    (ht0 : 0 < t) (htT : t < T) :
    Tendsto (fun h : ℝ => h⁻¹ •
        ((∫ s in (0 : ℝ)..(t + h), S.realOperator s (f (t + h - s))) -
          ∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s))))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((∫ s in (0 : ℝ)..t, S.realOperator s (forcingDeriv T f (t - s))) +
        S.realOperator t (f 0))) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨C, hC, hCbound⟩ := S.exists_norm_realOperator_le T
  have hden : 0 < C * t + 1 := by linarith [mul_nonneg hC ht0.le]
  set η : ℝ := ε / (2 * (C * t + 1))
  have hη : 0 < η := div_pos hε (mul_pos two_pos hden)
  obtain ⟨δf, hδf0, hquot⟩ := exists_forcingQuotient_close hT hf hη
  have hboundary := tendsto_shiftBoundary S hT hf.continuousOn ht0.le
  rw [Metric.tendsto_nhdsWithin_nhds] at hboundary
  obtain ⟨δb, hδb0, hboundary⟩ := hboundary (ε / 2) (half_pos hε)
  refine ⟨min (min δf δb) (T - t), lt_min (lt_min hδf0 hδb0) (sub_pos.mpr htT),
      fun h hh hdist => ?_⟩
  have hh0 : 0 < h := hh
  have hmin := lt_min_iff.mp (lt_of_dist_Ioi hh0 hdist)
  have hmin2 := lt_min_iff.mp hmin.1
  have hhδf : h ≤ δf := hmin2.1.le
  have hth : t + h ≤ T := by linarith [hmin.2]
  have hdistb : dist h 0 < δb := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hh0]
    exact hmin2.2
  have hcontf := hf.continuousOn
  have hsplit := shiftedDuhamel_sub_right S hcontf ht0.le hh0 hth
  set I : X := ∫ s in (0 : ℝ)..t, S.realOperator s (forcingDeriv T f (t - s))
  set c : X := S.realOperator t (f 0)
  have hdec : h⁻¹ • ((∫ s in (0 : ℝ)..(t + h), S.realOperator s (f (t + h - s))) -
        ∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s))) =
      (h⁻¹ • ∫ s in (0 : ℝ)..t, S.realOperator s (f (t + h - s) - f (t - s))) +
        h⁻¹ • ∫ s in t..(t + h), S.realOperator s (f (t + h - s)) := by
    rw [hsplit, smul_add]
  have herr : h⁻¹ • ((∫ s in (0 : ℝ)..(t + h), S.realOperator s (f (t + h - s))) -
        ∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s))) - (I + c) =
      ((h⁻¹ • ∫ s in (0 : ℝ)..t, S.realOperator s (f (t + h - s) - f (t - s))) - I) +
        ((h⁻¹ • ∫ s in t..(t + h), S.realOperator s (f (t + h - s))) - c) := by
    rw [hdec]
    abel
  have hp : ContinuousOn (fun s => f (t + h - s)) (Set.Icc 0 t) :=
    hcontf.comp' (continuous_const.sub continuous_id).continuousOn fun s hs =>
      ⟨by linarith [hs.2], by linarith [hs.1, hth]⟩
  have hq : ContinuousOn (fun s => f (t - s)) (Set.Icc 0 t) :=
    hcontf.comp' (continuous_const.sub continuous_id).continuousOn fun s hs =>
      ⟨by linarith [hs.2], by linarith [hs.1, htT.le]⟩
  have hd : ContinuousOn (fun s => forcingDeriv T f (t - s)) (Set.Icc 0 t) :=
    (continuousOn_forcingDeriv hT hf).comp'
      (continuous_const.sub continuous_id).continuousOn fun s hs =>
        ⟨by linarith [hs.2], by linarith [hs.1, htT.le]⟩
  have hclose : ∀ s ∈ Set.Icc 0 t,
      ‖h⁻¹ • (f (t + h - s) - f (t - s)) - forcingDeriv T f (t - s)‖ ≤ η := by
    intro s hs
    have hy : 0 ≤ t - s := by linarith [hs.2]
    have harg : (t - s) + h = t + h - s := by ring
    have hyh : (t - s) + h ≤ T := by
      rw [harg]
      linarith [hs.1, hth]
    have hle := hquot hy hh0 hhδf hyh
    rwa [harg] at hle
  have hmain := norm_scaled_orbit_sub_le S ht0.le hC
    (fun s _ hsb => hCbound s (le_trans hsb htT.le)) hp hq hd hclose
  have hrew : C * η * (t - 0) = C * t * η := by ring
  have hηle : C * t * η ≤ ε / 2 := by
    unfold η
    exact mul_div_two_le hC ht0.le hε.le
  rw [hrew] at hmain
  have hboundlt : ‖(h⁻¹ • ∫ s in t..(t + h), S.realOperator s (f (t + h - s))) - c‖ <
      ε / 2 := by
    rw [← dist_eq_norm]
    exact hboundary hh hdistb
  rw [dist_eq_norm, herr]
  have htri := norm_add_le
    ((h⁻¹ • ∫ s in (0 : ℝ)..t, S.realOperator s (f (t + h - s) - f (t - s))) - I)
    ((h⁻¹ • ∫ s in t..(t + h), S.realOperator s (f (t + h - s))) - c)
  linarith

/-- Left difference quotients of the shifted Duhamel integral. -/
private theorem tendsto_leftQuotient_shiftedDuhamel (S : StronglyContinuousSemigroup X)
    {T : ℝ} (hT : 0 < T) {f : ℝ → X} (hf : ContDiffOn ℝ 1 f (Set.Icc 0 T)) {t : ℝ}
    (ht0 : 0 < t) (htT : t < T) :
    Tendsto (fun k : ℝ => k⁻¹ •
        ((∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s))) -
          ∫ s in (0 : ℝ)..(t - k), S.realOperator s (f (t - k - s))))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((∫ s in (0 : ℝ)..t, S.realOperator s (forcingDeriv T f (t - s))) +
        S.realOperator t (f 0))) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨C, hC, hCbound⟩ := S.exists_norm_realOperator_le T
  have hden : 0 < C * t + 1 := by linarith [mul_nonneg hC ht0.le]
  set ζ : ℝ := (ε / 2) / (2 * (C * t + 1))
  have hζ : 0 < ζ := div_pos (half_pos hε) (mul_pos two_pos hden)
  obtain ⟨δf, hδf0, hquot⟩ := exists_forcingQuotient_close hT hf (half_pos hζ)
  have hdf := continuousOn_forcingDeriv hT hf
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hdf
  rw [Metric.uniformContinuousOn_iff_le] at huc
  obtain ⟨δd, hδd0, hosc⟩ := huc (ζ / 2) (half_pos hζ)
  have htail0 :=
    tendsto_intervalIntegral_sub_left_nhdsGT_zero ht0 (continuousOn_orbitDeriv S hT hf htT.le)
  rw [Metric.tendsto_nhdsWithin_nhds] at htail0
  obtain ⟨δt, hδt0, htail0⟩ := htail0 (ε / 4) (div_pos hε four_pos)
  have hboundary := tendsto_leftBoundary S hT hf.continuousOn ht0 htT.le
  rw [Metric.tendsto_nhdsWithin_nhds] at hboundary
  obtain ⟨δb, hδb0, hboundary⟩ := hboundary (ε / 2) (half_pos hε)
  refine ⟨min (min (min δf δd) (min δt δb)) t,
      lt_min (lt_min (lt_min hδf0 hδd0) (lt_min hδt0 hδb0)) ht0, fun k hk hdist => ?_⟩
  have hk0 : 0 < k := hk
  have hmin := lt_min_iff.mp (lt_of_dist_Ioi hk0 hdist)
  have hleft := lt_min_iff.mp hmin.1
  have hfd := lt_min_iff.mp hleft.1
  have htb := lt_min_iff.mp hleft.2
  have hkf : k ≤ δf := hfd.1.le
  have hkd : k ≤ δd := hfd.2.le
  have hkt : k ≤ t := hmin.2.le
  have hdistt : dist k 0 < δt := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hk0]
    exact htb.1
  have hdistb : dist k 0 < δb := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hk0]
    exact htb.2
  have hcontf := hf.continuousOn
  have hsplit := shiftedDuhamel_sub_left S hcontf hk0 hkt htT.le
  set I : X := ∫ s in (0 : ℝ)..t, S.realOperator s (forcingDeriv T f (t - s))
  set c : X := S.realOperator t (f 0)
  have hdec : k⁻¹ • ((∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s))) -
        ∫ s in (0 : ℝ)..(t - k), S.realOperator s (f (t - k - s))) =
      (k⁻¹ • ∫ s in (0 : ℝ)..(t - k),
          S.realOperator s (f (t - s) - f (t - k - s))) +
        k⁻¹ • ∫ s in (t - k)..t, S.realOperator s (f (t - s)) := by
    rw [hsplit, smul_add]
  have hg := continuousOn_orbitDeriv S hT hf htT.le
  have hintTrunc : IntervalIntegrable (fun s => S.realOperator s (forcingDeriv T f (t - s)))
      volume 0 (t - k) :=
    (hg.mono (Set.Icc_subset_Icc_right (by linarith : t - k ≤ t))).intervalIntegrable_of_Icc
      (by linarith : 0 ≤ t - k)
  have hintTail : IntervalIntegrable (fun s => S.realOperator s (forcingDeriv T f (t - s)))
      volume (t - k) t :=
    (hg.mono (Set.Icc_subset_Icc_left (by linarith : 0 ≤ t - k))).intervalIntegrable_of_Icc
      (by linarith)
  have hsplitI := integral_add_adjacent_intervals hintTrunc hintTail
  have herr : k⁻¹ • ((∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s))) -
        ∫ s in (0 : ℝ)..(t - k), S.realOperator s (f (t - k - s))) - (I + c) =
      ((k⁻¹ • ∫ s in (0 : ℝ)..(t - k),
          S.realOperator s (f (t - s) - f (t - k - s))) -
          ∫ s in (0 : ℝ)..(t - k), S.realOperator s (forcingDeriv T f (t - s))) +
        ((k⁻¹ • ∫ s in (t - k)..t, S.realOperator s (f (t - s))) - c) +
        -∫ s in (t - k)..t, S.realOperator s (forcingDeriv T f (t - s)) := by
    rw [hdec]
    unfold I
    rw [← hsplitI]
    abel
  have hp : ContinuousOn (fun s => f (t - s)) (Set.Icc 0 (t - k)) :=
    hcontf.comp' (continuous_const.sub continuous_id).continuousOn fun s hs =>
      ⟨by linarith [hs.2, hkt], by linarith [hs.1, htT.le]⟩
  have hq : ContinuousOn (fun s => f (t - k - s)) (Set.Icc 0 (t - k)) :=
    hcontf.comp' (continuous_const.sub continuous_id).continuousOn fun s hs =>
      ⟨by linarith [hs.2], by linarith [hs.1, hk0.le, htT.le]⟩
  have hd : ContinuousOn (fun s => forcingDeriv T f (t - s)) (Set.Icc 0 (t - k)) :=
    hdf.comp' (continuous_const.sub continuous_id).continuousOn fun s hs =>
      ⟨by linarith [hs.2, hkt], by linarith [hs.1, htT.le]⟩
  have hclose : ∀ s ∈ Set.Icc 0 (t - k),
      ‖k⁻¹ • (f (t - s) - f (t - k - s)) - forcingDeriv T f (t - s)‖ ≤ ζ := by
    intro s hs
    exact backwardQuotient_close hquot hosc hk0 hkf hkd htT.le hs.1 hs.2
  have hmain := norm_scaled_orbit_sub_le S (by linarith : (0 : ℝ) ≤ t - k) hC
    (fun s _ hsb => hCbound s (by linarith [hsb, htT])) hp hq hd
    hclose
  have hrew : C * ζ * ((t - k) - 0) = C * ζ * (t - k) := by ring
  have hcmp : C * ζ * (t - k) ≤ C * t * ζ := by
    have hmul : 0 ≤ C * ζ := mul_nonneg hC hζ.le
    have hsub : t - k ≤ t := by linarith
    have hcomm : C * ζ * t = C * t * ζ := by ring
    rw [← hcomm]
    exact mul_le_mul_of_nonneg_left hsub hmul
  have hζle : C * t * ζ ≤ ε / 4 := by
    have hquarter : (ε / 2) / 2 = ε / 4 := by ring
    unfold ζ
    rw [← hquarter]
    exact mul_div_two_le hC ht0.le (div_nonneg hε.le zero_le_two)
  rw [hrew] at hmain
  have htail : ‖∫ s in (t - k)..t, S.realOperator s (forcingDeriv T f (t - s))‖ < ε / 4 := by
    rw [← sub_zero (∫ s in (t - k)..t, S.realOperator s (forcingDeriv T f (t - s))),
      ← dist_eq_norm]
    exact htail0 hk hdistt
  have hboundlt : ‖(k⁻¹ • ∫ s in (t - k)..t, S.realOperator s (f (t - s))) - c‖ < ε / 2 := by
    rw [← dist_eq_norm]
    exact hboundary hk hdistb
  rw [dist_eq_norm, herr]
  have htri1 := norm_add_le
    (((k⁻¹ • ∫ s in (0 : ℝ)..(t - k),
          S.realOperator s (f (t - s) - f (t - k - s))) -
        ∫ s in (0 : ℝ)..(t - k), S.realOperator s (forcingDeriv T f (t - s))) +
      ((k⁻¹ • ∫ s in (t - k)..t, S.realOperator s (f (t - s))) - c))
    (-∫ s in (t - k)..t, S.realOperator s (forcingDeriv T f (t - s)))
  have htri2 := norm_add_le
    ((k⁻¹ • ∫ s in (0 : ℝ)..(t - k),
        S.realOperator s (f (t - s) - f (t - k - s))) -
      ∫ s in (0 : ℝ)..(t - k), S.realOperator s (forcingDeriv T f (t - s)))
    ((k⁻¹ • ∫ s in (t - k)..t, S.realOperator s (f (t - s))) - c)
  rw [norm_neg] at htri1
  linarith [htri1, htri2, hmain, hcmp, hζle, htail, hboundlt]

/-- On `(0, T)`, the shifted Duhamel integral has derivative equal to the orbit of the
forcing derivative plus the orbit of the initial value. -/
private theorem hasDerivAt_shiftedDuhamel (S : StronglyContinuousSemigroup X) {T : ℝ}
    (hT : 0 < T) {f : ℝ → X} (hf : ContDiffOn ℝ 1 f (Set.Icc 0 T)) {t : ℝ}
    (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt (fun τ => ∫ s in (0 : ℝ)..τ, S.realOperator s (f (τ - s)))
      ((∫ s in (0 : ℝ)..t, S.realOperator s (forcingDeriv T f (t - s))) +
        S.realOperator t (f 0)) t := by
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  exact ⟨tendsto_slope_nhdsLT_of_tendsto (tendsto_leftQuotient_shiftedDuhamel S hT hf ht0 htT),
    tendsto_slope_nhdsGT_of_tendsto (tendsto_rightQuotient_shiftedDuhamel S hT hf ht0 htT)⟩

/-- The shifted Duhamel integral takes values in the generator domain, and the generator
acts by the integrated forcing derivative corrected by the endpoint values. -/
private theorem generator_shiftedDuhamel (S : StronglyContinuousSemigroup X) {T : ℝ}
    (hT : 0 < T) {f : ℝ → X} (hf : ContDiffOn ℝ 1 f (Set.Icc 0 T)) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∃ hmem : (∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s))) ∈ S.domain,
      S.generator ⟨∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s)),
        by rw [S.generator_domain]; exact hmem⟩ =
        (∫ s in (0 : ℝ)..t, S.realOperator s (forcingDeriv T f (t - s))) +
          S.realOperator t (f 0) - f t := by
  have hcontf := hf.continuousOn
  rcases ht0.eq_or_lt with rfl | htpos
  · have hzero : (∫ s in (0 : ℝ)..0, S.realOperator s (f (0 - s))) = 0 := integral_same
    have hmem : (∫ s in (0 : ℝ)..0, S.realOperator s (f (0 - s))) ∈ S.domain := by
      rw [hzero]
      exact Submodule.zero_mem _
    refine ⟨hmem, ?_⟩
    have hgen0 : S.generator ⟨∫ s in (0 : ℝ)..0, S.realOperator s (f (0 - s)),
        by rw [S.generator_domain]; exact hmem⟩ = 0 := by
      have heq : (⟨∫ s in (0 : ℝ)..0, S.realOperator s (f (0 - s)),
          by rw [S.generator_domain]; exact hmem⟩ : S.generator.domain) = 0 :=
        Subtype.ext hzero
      rw [heq, LinearPMap.map_zero]
    have hdf0 : (∫ s in (0 : ℝ)..0, S.realOperator s (forcingDeriv T f (0 - s))) = 0 :=
      integral_same
    rw [hgen0, hdf0, S.realOperator_zero_apply, zero_add, sub_self]
  · set φt : X := ∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s))
    set L : X := (∫ s in (0 : ℝ)..t, S.realOperator s (forcingDeriv T f (t - s))) +
      S.realOperator t (f 0) - f t
    have htend : Tendsto (fun h : ℝ => h⁻¹ • (S.realOperator h φt - φt))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
      rw [Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      obtain ⟨C, hC, hCbound⟩ := S.exists_norm_realOperator_le T
      have hden : 0 < C * t + 1 := by linarith [mul_nonneg hC htpos.le]
      set η : ℝ := (ε / 2) / (2 * (C * t + 1))
      have hη : 0 < η := div_pos (half_pos hε) (mul_pos two_pos hden)
      obtain ⟨δf, hδf0, hquot⟩ := exists_forcingQuotient_close hT hf hη
      have hboundary := tendsto_shiftBoundary S hT hcontf htpos.le
      rw [Metric.tendsto_nhdsWithin_nhds] at hboundary
      obtain ⟨δb, hδb0, hboundary⟩ := hboundary (ε / 4) (div_pos hε four_pos)
      have hg := continuousOn_orbitDeriv S hT hf htT
      have htail0 := tendsto_intervalIntegral_zero_nhdsGT_zero htpos hg
      rw [Metric.tendsto_nhdsWithin_nhds] at htail0
      obtain ⟨δt, hδt0, htail0⟩ := htail0 (ε / 4) (div_pos hε four_pos)
      have hinit := tendsto_inv_smul_intervalIntegral_nhdsGT_zero htpos
        (continuousOn_elapsed_forcing (c := t) S hcontf fun u hu =>
          ⟨by linarith [hu.2], by linarith [hu.1, htT]⟩)
      rw [Metric.tendsto_nhdsWithin_nhds] at hinit
      obtain ⟨δi, hδi0, hinit⟩ := hinit (ε / 4) (div_pos hε four_pos)
      refine ⟨min (min (min δf δb) (min δt δi)) t,
          lt_min (lt_min (lt_min hδf0 hδb0) (lt_min hδt0 hδi0)) htpos,
          fun h hh hdist => ?_⟩
      have hh0 : 0 < h := hh
      have hmin := lt_min_iff.mp (lt_of_dist_Ioi hh0 hdist)
      have hleft := lt_min_iff.mp hmin.1
      have hfb := lt_min_iff.mp hleft.1
      have hti := lt_min_iff.mp hleft.2
      have hhδf : h ≤ δf := hfb.1.le
      have hht : h ≤ t := hmin.2.le
      have hdistb : dist h 0 < δb := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hh0]
        exact hfb.2
      have hdistt : dist h 0 < δt := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hh0]
        exact hti.1
      have hdisti : dist h 0 < δi := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hh0]
        exact hti.2
      have hident := realOperator_sub_shiftedDuhamel S hcontf htpos.le htT hh0 hht
      have hdec : h⁻¹ • (S.realOperator h φt - φt) =
          (h⁻¹ • ∫ u in h..t, S.realOperator u (f (t + h - u) - f (t - u))) +
            (h⁻¹ • ∫ u in t..(t + h), S.realOperator u (f (t + h - u))) -
            h⁻¹ • ∫ u in (0 : ℝ)..h, S.realOperator u (f (t - u)) := by
        rw [hident, smul_sub, smul_add]
      have hintTail : IntervalIntegrable
          (fun u => S.realOperator u (forcingDeriv T f (t - u))) volume 0 h :=
        (hg.mono (Set.Icc_subset_Icc_right hht)).intervalIntegrable_of_Icc hh0.le
      have hintTrunc : IntervalIntegrable
          (fun u => S.realOperator u (forcingDeriv T f (t - u))) volume h t :=
        (hg.mono (Set.Icc_subset_Icc_left hh0.le)).intervalIntegrable_of_Icc hht
      have hsplitI := integral_add_adjacent_intervals hintTail hintTrunc
      set cvec : X := S.realOperator t (f 0)
      have herr : h⁻¹ • (S.realOperator h φt - φt) - L =
          ((h⁻¹ • ∫ u in h..t, S.realOperator u (f (t + h - u) - f (t - u))) -
              ∫ u in h..t, S.realOperator u (forcingDeriv T f (t - u))) +
            ((h⁻¹ • ∫ u in t..(t + h), S.realOperator u (f (t + h - u))) - cvec) +
            (f t - h⁻¹ • ∫ u in (0 : ℝ)..h, S.realOperator u (f (t - u))) +
            -∫ u in (0 : ℝ)..h, S.realOperator u (forcingDeriv T f (t - u)) := by
        rw [hdec]
        unfold L
        rw [← hsplitI]
        abel
      have hp : ContinuousOn (fun u => f (t + h - u)) (Set.Icc h t) :=
        hcontf.comp' (continuous_const.sub continuous_id).continuousOn fun u hu =>
          ⟨by linarith [hu.2], by linarith [hu.1, htT]⟩
      have hq : ContinuousOn (fun u => f (t - u)) (Set.Icc h t) :=
        hcontf.comp' (continuous_const.sub continuous_id).continuousOn fun u hu =>
          ⟨by linarith [hu.2, hh0.le], by linarith [hu.1, htT]⟩
      have hd : ContinuousOn (fun u => forcingDeriv T f (t - u)) (Set.Icc h t) :=
        (continuousOn_forcingDeriv hT hf).comp'
          (continuous_const.sub continuous_id).continuousOn fun u hu =>
            ⟨by linarith [hu.2, hh0.le], by linarith [hu.1, htT]⟩
      have hclose : ∀ u ∈ Set.Icc h t,
          ‖h⁻¹ • (f (t + h - u) - f (t - u)) - forcingDeriv T f (t - u)‖ ≤ η := by
        intro u hu
        have hy : 0 ≤ t - u := by linarith [hu.2]
        have harg : (t - u) + h = t + h - u := by ring
        have hyh : (t - u) + h ≤ T := by
          rw [harg]
          linarith [hu.1, htT]
        have hle := hquot hy hh0 hhδf hyh
        rwa [harg] at hle
      have hmain := norm_scaled_orbit_sub_le S hht hC
        (fun s _ hsb => hCbound s (le_trans hsb htT)) hp hq hd hclose
      have hcmp : C * η * (t - h) ≤ C * t * η := by
        have hmul : 0 ≤ C * η := mul_nonneg hC hη.le
        have hsub : t - h ≤ t := by linarith
        have hcomm : C * η * t = C * t * η := by ring
        rw [← hcomm]
        exact mul_le_mul_of_nonneg_left hsub hmul
      have hηle : C * t * η ≤ ε / 4 := by
        have hquarter : (ε / 2) / 2 = ε / 4 := by ring
        unfold η
        rw [← hquarter]
        exact mul_div_two_le hC htpos.le (div_nonneg hε.le zero_le_two)
      have hboundlt : ‖(h⁻¹ • ∫ u in t..(t + h), S.realOperator u (f (t + h - u))) - cvec‖ <
          ε / 4 := by
        rw [← dist_eq_norm]
        exact hboundary hh hdistb
      have htail : ‖∫ u in (0 : ℝ)..h, S.realOperator u (forcingDeriv T f (t - u))‖ <
          ε / 4 := by
        rw [← sub_zero (∫ u in (0 : ℝ)..h, S.realOperator u (forcingDeriv T f (t - u))),
          ← dist_eq_norm]
        exact htail0 hh hdistt
      have hinitlt : ‖f t - h⁻¹ • ∫ u in (0 : ℝ)..h, S.realOperator u (f (t - u))‖ <
          ε / 4 := by
        rw [norm_sub_rev, ← dist_eq_norm]
        have hzero : S.realOperator 0 (f (t - 0)) = f t := by
          rw [sub_zero, S.realOperator_zero_apply]
        rw [← hzero]
        exact hinit hh hdisti
      rw [dist_eq_norm, herr]
      have htri := norm_add₄_le
        (a := (h⁻¹ • ∫ u in h..t, S.realOperator u (f (t + h - u) - f (t - u))) -
          ∫ u in h..t, S.realOperator u (forcingDeriv T f (t - u)))
        (b := (h⁻¹ • ∫ u in t..(t + h), S.realOperator u (f (t + h - u))) - cvec)
        (c := f t - h⁻¹ • ∫ u in (0 : ℝ)..h, S.realOperator u (f (t - u)))
        (d := -∫ u in (0 : ℝ)..h, S.realOperator u (forcingDeriv T f (t - u)))
      rw [norm_neg] at htri
      linarith
    have htend' : Tendsto (fun h : ℝ => (1 / h) • (S.realOperator h φt - φt))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
      simpa [one_div] using htend
    have hmem : φt ∈ S.domain := (S.mem_domain_iff_tendsto φt).2 ⟨L, htend'⟩
    exact ⟨hmem, S.generator_eq_of_tendsto hmem htend'⟩

/-- With initial value in the generator domain and forcing `C¹` on `[0, T]`, the
variation-of-constants trajectory takes values in the generator domain on `[0, T]` and satisfies
`u'(t) = A u(t) + f(t)` at every `t ∈ (0, T)`. -/
theorem variation_of_constants_classical (S : StronglyContinuousSemigroup X) {T : ℝ}
    (hT : 0 < T) (x : S.generator.domain) {f : ℝ → X}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 T)) :
    (∀ t ∈ Set.Icc 0 T, forcedSemigroupTrajectory S x f t ∈ S.generator.domain) ∧
      ∀ t ∈ Set.Ioo 0 T, ∃ h : forcedSemigroupTrajectory S x f t ∈ S.generator.domain,
        HasDerivAt (forcedSemigroupTrajectory S x f)
          (S.generator ⟨forcedSemigroupTrajectory S x f t, h⟩ + f t) t := by
  have hxdom : (x : X) ∈ S.domain := S.generator_domain ▸ x.property
  have hmem {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
      S.realOperator t (x : X) ∈ S.generator.domain ∧
        (∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s))) ∈ S.generator.domain := by
    simp only [S.generator_domain]
    exact ⟨S.realOperator_mem_domain hxdom, (generator_shiftedDuhamel S hT hf ht.1 ht.2).1⟩
  have hsum {t : ℝ} (ht : t ∈ Set.Icc 0 T) := add_mem (hmem ht).1 (hmem ht).2
  refine ⟨fun t ht => (forced_eq_shifted S x f t).symm ▸ hsum ht, fun t ht => ?_⟩
  have htI : t ∈ Set.Icc 0 T := Set.Ioo_subset_Icc_self ht
  obtain ⟨hφmem, hφeq⟩ := generator_shiftedDuhamel S hT hf htI.1 htI.2
  have horbit := (S.realOperator_hasDerivWithinAt_Ici ⟨(x : X), hxdom⟩ ht.1.le).hasDerivAt
    (Ici_mem_nhds ht.1)
  have htraj := (horbit.add (hasDerivAt_shiftedDuhamel S hT hf ht.1 ht.2)).congr_of_eventuallyEq
    (Eventually.of_forall fun τ => forced_eq_shifted S (x : X) f τ)
  have hmem' : forcedSemigroupTrajectory S x f t ∈ S.generator.domain :=
    (forced_eq_shifted S x f t).symm ▸ hsum htI
  refine ⟨hmem', htraj.congr_deriv ?_⟩
  rw [linearPMap_mk_congr _ (forced_eq_shifted S x f t) hmem' (hsum htI),
    linearPMap_mk_add _ (hmem htI).1 (hmem htI).2, hφeq, add_assoc, sub_add_cancel]

end CKMA
