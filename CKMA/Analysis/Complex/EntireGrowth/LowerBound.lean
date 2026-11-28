/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Complex.EntireGrowth.Product
public import CKMA.Analysis.Complex.EntireGrowth.ZeroCount

import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Field
import TauCeti.Analysis.SpecialFunctions.Log.Base
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# A lower bound for canonical products on separated circles

For a list of slopes with `O(R ^ B)` count and `p < B < p + 1`, every interval `(T, T + 1]` with
`T` large contains a radius `R` at distance at least `‖w‖ ^ (-(p + 1))` from every listed modulus
`‖w‖`, by a measure count of the excluded intervals. On such a circle the genus-`p` canonical
product satisfies `log ‖∏ E_p(z / w)‖ ≥ -K R ^ B (log (2R) + 1)`: the factors with `‖w‖ ≥ 2R` are
estimated by `CKMA.log_norm_weierstrassFactor_ge_half`, the others by
`CKMA.log_norm_weierstrassFactor_ge`, and the sums by `CKMA.dyadic_tail_le` and
`CKMA.dyadic_head_le`.

## Main results

* `CKMA.exists_good_radius`: separated radii in every large unit interval.
* `CKMA.exists_log_norm_tprod_lower`: the power-logarithmic lower bound for the product.
-/

public section

noncomputable section

namespace CKMA

open Asymptotics Bornology Classical Complex Filter Finset MeasureTheory Metric Set Topology
open scoped BigOperators ENNReal

/-- Every large interval `(T, T + 1]` contains a radius separated from the listed zeros. -/
theorem exists_good_radius {a : ℕ → Option ℂ} {B q C R0 : ℝ}
    (hBq : B < q) (hq : 0 < q) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hfin : ∀ R : ℝ, {n | ∃ w, a n = some w ∧ ‖w‖ ≤ R}.Finite)
    (hcount : ∀ R : ℝ, R0 ≤ R →
      (({n | ∃ w, a n = some w ∧ ‖w‖ ≤ R}.ncard : ℝ) ≤ C * R ^ B)) :
    ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T → ∃ R : ℝ, T < R ∧ R ≤ T + 1 ∧
      ∀ n w, a n = some w → |R - ‖w‖| < 1 → ‖w‖ ^ (-q) ≤ |R - ‖w‖| := by
  classical
  let K : ℝ := 2 * C * (4 : ℝ) ^ B
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (by norm_num) hC) (Real.rpow_nonneg (by norm_num) _)
  have hqB : 0 < q - B := sub_pos.mpr hBq
  let base : ℝ := K + 1
  have hbase : 0 < base := by dsimp [base]; linarith
  let expo : ℝ := (q - B)⁻¹
  let T0 : ℝ := max (max R0 2) (1 + base ^ expo)
  refine ⟨T0, ?_⟩
  intro T hT
  have hTge : (2 : ℝ) ≤ T :=
    ((le_max_right R0 2).trans (le_max_left _ _)).trans hT
  have hTR0 : R0 ≤ T := ((le_max_left R0 2).trans (le_max_left _ _)).trans hT
  have hTm : 0 < T - 1 := by linarith
  have hbasepow : base ^ expo ≤ T - 1 := by
    have h1 : 1 + base ^ expo ≤ T := (le_max_right _ _).trans hT
    linarith
  have hpow : base ≤ (T - 1) ^ (q - B) := by
    have hmono := Real.rpow_le_rpow (Real.rpow_nonneg hbase.le _) hbasepow hqB.le
    have hmul : expo * (q - B) = 1 := inv_mul_cancel₀ hqB.ne'
    have hid : (base ^ expo) ^ (q - B) = base := by
      rw [← Real.rpow_mul hbase.le, hmul, Real.rpow_one]
    calc
      base = (base ^ expo) ^ (q - B) := hid.symm
      _ ≤ (T - 1) ^ (q - B) := hmono
  have hball : {n | ∃ w, a n = some w ∧ ‖w‖ ≤ T + 2}.Finite := hfin (T + 2)
  have hT2 : R0 ≤ T + 2 := by linarith
  let u : Finset ℕ := hball.toFinset.filter fun n =>
    ∃ w, a n = some w ∧ T - 1 ≤ ‖w‖ ∧ ‖w‖ ≤ T + 2
  let wOf : ℕ → ℂ := fun n =>
    if h : ∃ w, a n = some w ∧ T - 1 ≤ ‖w‖ ∧ ‖w‖ ≤ T + 2 then Classical.choose h else 0
  let rad : ℕ → ℝ := fun n => ‖wOf n‖ ^ (-q)
  let bad : ℕ → Set ℝ := fun n =>
    if h : ∃ w, a n = some w ∧ T - 1 ≤ ‖w‖ ∧ ‖w‖ ≤ T + 2 then
      Ioo (‖wOf n‖ - rad n) (‖wOf n‖ + rad n)
    else ∅
  have hlen : ∀ n ∈ u, volume (bad n) ≤ ENNReal.ofReal (2 * (T - 1) ^ (-q)) := by
    intro n hn
    have hn' : ∃ w, a n = some w ∧ T - 1 ≤ ‖w‖ ∧ ‖w‖ ≤ T + 2 :=
      (Finset.mem_filter.mp hn).2
    have hw : a n = some (wOf n) ∧ T - 1 ≤ ‖wOf n‖ ∧ ‖wOf n‖ ≤ T + 2 := by
      have hwOf : wOf n = Classical.choose hn' := by
        simp only [wOf]
        rw [dite_eq_left hn']
      rw [hwOf]
      exact Classical.choose_spec hn'
    have hrle : rad n ≤ (T - 1) ^ (-q) := by
      dsimp [rad]
      exact Real.rpow_le_rpow_of_nonpos hTm hw.2.1 (neg_nonpos.mpr hq.le)
    have hbadn : bad n = Ioo (‖wOf n‖ - rad n) (‖wOf n‖ + rad n) := by
      simp only [bad]
      rw [dite_eq_left hn']
    rw [hbadn, Real.volume_Ioo]
    have hdiff : (‖wOf n‖ + rad n) - (‖wOf n‖ - rad n) = 2 * rad n := by ring
    rw [hdiff]
    refine ENNReal.ofReal_le_ofReal ?_
    exact mul_le_mul_of_nonneg_left hrle (by norm_num)
  have hcard : (u.card : ℝ) ≤ C * (T + 2) ^ B := by
    refine (Nat.cast_le.mpr ?_).trans (hcount (T + 2) hT2)
    refine (Finset.card_le_card (Finset.filter_subset _ _)).trans ?_
    rw [Set.ncard_eq_toFinset_card _ hball]
  have hscale : (u.card : ℝ) * (2 * (T - 1) ^ (-q)) ≤ K * (T - 1) ^ (B - q) := by
    have hnonneg : 0 ≤ 2 * (T - 1) ^ (-q) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg hTm.le _)
    have hstep1 : (u.card : ℝ) * (2 * (T - 1) ^ (-q)) ≤
        C * (T + 2) ^ B * (2 * (T - 1) ^ (-q)) :=
      mul_le_mul_of_nonneg_right hcard hnonneg
    have hfour : T + 2 ≤ 4 * (T - 1) := by linarith
    have hpow4 : (T + 2) ^ B ≤ (4 * (T - 1)) ^ B :=
      Real.rpow_le_rpow (by linarith) hfour hB
    have hsplit : (4 * (T - 1)) ^ B = (4 : ℝ) ^ B * (T - 1) ^ B :=
      Real.mul_rpow (by norm_num) hTm.le
    have hradd : (T - 1) ^ B * (T - 1) ^ (-q) = (T - 1) ^ (B - q) := by
      rw [← Real.rpow_add hTm]
      exact (congrArg (fun t : ℝ => (T - 1) ^ t) (sub_eq_add_neg B q)).symm
    calc
      (u.card : ℝ) * (2 * (T - 1) ^ (-q))
          ≤ C * (T + 2) ^ B * (2 * (T - 1) ^ (-q)) := hstep1
      _ ≤ C * ((4 : ℝ) ^ B * (T - 1) ^ B) * (2 * (T - 1) ^ (-q)) := by
          refine mul_le_mul_of_nonneg_right ?_ hnonneg
          exact mul_le_mul_of_nonneg_left (hpow4.trans_eq hsplit) hC
      _ = (2 * C * (4 : ℝ) ^ B) * ((T - 1) ^ B * (T - 1) ^ (-q)) := by ring
      _ = K * (T - 1) ^ (B - q) := by rw [hradd]
  have hlt : K * (T - 1) ^ (B - q) < 1 := by
    have hden : 0 < (T - 1) ^ (q - B) := Real.rpow_pos_of_pos hTm _
    have hinv : (T - 1) ^ (B - q) = ((T - 1) ^ (q - B))⁻¹ := by
      rw [← Real.rpow_neg hTm.le, neg_sub]
    rw [hinv]
    have hfrac : K / (T - 1) ^ (q - B) ≤ K / base :=
      div_le_div_of_nonneg_left hK0 hbase hpow
    have hunit : K / base < 1 := by
      dsimp [base]
      rw [div_lt_one (by linarith)]
      linarith
    calc
      K * ((T - 1) ^ (q - B))⁻¹ = K / (T - 1) ^ (q - B) := by rw [div_eq_mul_inv]
      _ ≤ K / base := hfrac
      _ < 1 := hunit
  have hvol : volume (⋃ n ∈ u, bad n) ≤ ENNReal.ofReal (K * (T - 1) ^ (B - q)) := by
    refine (measure_biUnion_finset_le u bad).trans ?_
    refine (Finset.sum_le_sum hlen).trans ?_
    have hconst : ∑ n ∈ u, ENNReal.ofReal (2 * (T - 1) ^ (-q)) =
        ENNReal.ofReal ((u.card : ℝ) * (2 * (T - 1) ^ (-q))) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [show (u.card : ℝ≥0∞) = ENNReal.ofReal (u.card : ℝ) from
        (ENNReal.ofReal_natCast u.card).symm,
        (ENNReal.ofReal_mul (Nat.cast_nonneg u.card)).symm]
    rw [hconst]
    exact ENNReal.ofReal_le_ofReal hscale
  have hnot : ¬ Ioc T (T + 1) ⊆ ⋃ n ∈ u, bad n := by
    intro hinc
    have hle := measure_mono (μ := volume) hinc
    have hleft : volume (Ioc T (T + 1)) = 1 := by
      have hsub : (T + 1) - T = 1 := by ring
      rw [Real.volume_Ioc, hsub, ENNReal.ofReal_one]
    have hright : volume (⋃ n ∈ u, bad n) < 1 := by
      refine lt_of_le_of_lt hvol ?_
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hlt
    exact lt_irrefl _ <| hleft.symm.trans_lt (hle.trans_lt hright)
  obtain ⟨R, hRmem, hRout⟩ := Set.not_subset.mp hnot
  refine ⟨R, hRmem.1, hRmem.2, ?_⟩
  intro n w hw hclose
  have hwin : T - 1 ≤ ‖w‖ ∧ ‖w‖ ≤ T + 2 := by
    have habs := abs_lt.mp hclose
    constructor <;> linarith [hRmem.1, hRmem.2, habs.1, habs.2]
  have hnex : ∃ w', a n = some w' ∧ T - 1 ≤ ‖w'‖ ∧ ‖w'‖ ≤ T + 2 :=
    ⟨w, hw, hwin.1, hwin.2⟩
  have hn : n ∈ u := by
    refine Finset.mem_filter.mpr ⟨?_, hnex⟩
    exact hball.mem_toFinset.mpr ⟨w, hw, hwin.2⟩
  have hnotn : R ∉ bad n := by
    intro hbadR
    exact hRout (mem_iUnion₂.mpr ⟨n, hn, hbadR⟩)
  have hwOf : w = wOf n := by
    have hspec := Classical.choose_spec hnex
    have hwo : wOf n = Classical.choose hnex := by
      simp only [wOf]
      rw [dite_eq_left hnex]
    exact Option.some_injective _ (hw.symm.trans (hwo ▸ hspec.1))
  have hbadn : bad n = Ioo (‖w‖ - ‖w‖ ^ (-q)) (‖w‖ + ‖w‖ ^ (-q)) := by
    simp only [bad, rad]
    rw [dite_eq_left hnex, hwOf]
  rw [hbadn] at hnotn
  have hge : ¬ |R - ‖w‖| < ‖w‖ ^ (-q) := by
    intro hltR
    rw [abs_lt] at hltR
    exact hnotn ⟨by linarith, by linarith⟩
  exact le_of_not_gt hge

/-- A lower bound for `log ‖Eₚ(z / w)‖` on the circle of radius `R`. -/
private def genusFactorLogLower (p : ℕ) (a : ℕ → Option ℂ) (R : ℝ) (n : ℕ) : ℝ :=
  match a n with
  | none => 0
  | some w =>
      if 2 * R ≤ ‖w‖ then -2 * R ^ ((p : ℝ) + 1) * ‖w‖ ^ (-((p : ℝ) + 1))
      else -((p : ℝ) + 2) * Real.log (2 * R) - (p : ℝ) -
        (p : ℝ) * R ^ (p : ℝ) * ‖w‖ ^ (-(p : ℝ))

/-- Each canonical factor lies above `genusFactorLogLower` on a separated circle. -/
private theorem log_norm_genusFactor_lower {p : ℕ} {a : ℕ → Option ℂ} {n : ℕ} {z : ℂ} {R : ℝ}
    (hne : ∀ w, a n = some w → w ≠ 0) (hR : 1 ≤ R) (hz : ‖z‖ = R)
    (hgood : ∀ w, a n = some w → |R - ‖w‖| < 1 →
      ‖w‖ ^ (-((p : ℝ) + 1)) ≤ |R - ‖w‖|) :
    genusFactorLogLower p a R n ≤ Real.log ‖genusFactor p a n z‖ := by
  classical
  cases ha : a n with
  | none =>
    have hlow : genusFactorLogLower p a R n = 0 := by simp [genusFactorLogLower, ha]
    rw [hlow, genusFactor_none ha, norm_one, Real.log_one]
  | some w =>
    have hw0 : w ≠ 0 := hne w ha
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hlow : genusFactorLogLower p a R n =
        if 2 * R ≤ ‖w‖ then -2 * R ^ ((p : ℝ) + 1) * ‖w‖ ^ (-((p : ℝ) + 1))
        else -((p : ℝ) + 2) * Real.log (2 * R) - (p : ℝ) -
          (p : ℝ) * R ^ (p : ℝ) * ‖w‖ ^ (-(p : ℝ)) := by
      simp [genusFactorLogLower, ha]
    rw [hlow, genusFactor_some ha]
    split_ifs with hfar
    ·
      have hu : ‖z / w‖ ≤ 1 / 2 := by
        rw [norm_div, hz, div_le_iff₀ hwpos]
        linarith
      have hhalf := log_norm_weierstrassFactor_ge_half (p := p) hu
      have hpow : (R / ‖w‖) ^ (p + 1) =
          R ^ ((p : ℝ) + 1) * ‖w‖ ^ (-((p : ℝ) + 1)) := by
        have hcast : ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 := by simp [Nat.cast_add, Nat.cast_one]
        rw [div_pow, ← Real.rpow_natCast R (p + 1), ← Real.rpow_natCast ‖w‖ (p + 1), hcast,
          div_eq_mul_inv, ← Real.rpow_neg (norm_nonneg w)]
      calc
        -2 * R ^ ((p : ℝ) + 1) * ‖w‖ ^ (-((p : ℝ) + 1))
            = -2 * (R / ‖w‖) ^ (p + 1) := by rw [mul_assoc, ← hpow]
        _ = -2 * ‖z / w‖ ^ (p + 1) := by rw [norm_div, hz]
        _ ≤ Real.log ‖weierstrassFactor p (z / w)‖ := hhalf
    · have hnear : ‖w‖ ≤ 2 * R := le_of_lt (lt_of_not_ge hfar)
      have hu : z / w ≠ 1 := by
        intro hdiv
        have hz_w : z = w := by rw [div_eq_iff hw0, one_mul] at hdiv; exact hdiv
        have hzero : |R - ‖w‖| = 0 := by rw [← hz_w, hz, sub_self, abs_zero]
        have hsep := hgood w ha (by rw [hzero]; norm_num)
        exact (not_le_of_gt (Real.rpow_pos_of_pos hwpos _)) (by simpa [hzero] using hsep)
      have hbase := log_norm_weierstrassFactor_ge (p := p) (u := z / w) hu
      have hdist : |R - ‖w‖| ≤ ‖z - w‖ := by simpa [hz] using abs_norm_sub_norm_le z w
      have hzwpos : 0 < ‖z - w‖ := by
        rw [norm_pos_iff, ne_eq, sub_eq_zero]
        intro hzw
        exact hu (by rw [hzw, div_self hw0])
      have hnorm : ‖(1 : ℂ) - z / w‖ = ‖z - w‖ / ‖w‖ := by
        have hsub : (w - z) / w = 1 - z / w := by rw [sub_div, div_self hw0]
        rw [← hsub, norm_div, norm_sub_rev]
      have hlogu : Real.log ‖(1 : ℂ) - z / w‖ = Real.log ‖z - w‖ - Real.log ‖w‖ := by
        rw [hnorm, Real.log_div hzwpos.ne' hwpos.ne']
      have hlogw : Real.log ‖w‖ ≤ Real.log (2 * R) :=
        Real.log_le_log hwpos hnear
      have hlog2 : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
      have hlogzw : -((p : ℝ) + 1) * Real.log (2 * R) ≤ Real.log ‖z - w‖ := by
        by_cases hclose : |R - ‖w‖| < 1
        · have hsep := (hgood w ha hclose).trans hdist
          have hlogsep := Real.log_le_log (Real.rpow_pos_of_pos hwpos _) hsep
          rw [Real.log_rpow hwpos] at hlogsep
          have habs := abs_lt.mp hclose
          have hwR : ‖w‖ ≤ 2 * R := by linarith
          exact hlogsep.trans' <|
            mul_le_mul_of_nonpos_left (Real.log_le_log hwpos hwR) (by linarith)
        · have hone : (1 : ℝ) ≤ ‖z - w‖ := (le_of_not_gt hclose).trans hdist
          have hnonneg : 0 ≤ Real.log ‖z - w‖ := by
            rw [← Real.log_one]
            exact Real.log_le_log zero_lt_one hone
          exact hnonneg.trans' <| mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog2
      have hlog1 : -((p : ℝ) + 2) * Real.log (2 * R) ≤ Real.log ‖(1 : ℂ) - z / w‖ := by
        rw [hlogu]
        calc
          -((p : ℝ) + 2) * Real.log (2 * R)
              = -((p : ℝ) + 1) * Real.log (2 * R) + -Real.log (2 * R) := by ring
          _ ≤ Real.log ‖z - w‖ + -Real.log ‖w‖ := by
              refine add_le_add hlogzw ?_
              exact neg_le_neg hlogw
          _ = Real.log ‖z - w‖ - Real.log ‖w‖ := by ring
      have hupow : ‖z / w‖ ^ p = R ^ (p : ℝ) * ‖w‖ ^ (-(p : ℝ)) := by
        rw [norm_div, hz, div_pow, ← Real.rpow_natCast R p, ← Real.rpow_natCast ‖w‖ p,
          div_eq_mul_inv, ← Real.rpow_neg (norm_nonneg w)]
      calc
        -((p : ℝ) + 2) * Real.log (2 * R) - (p : ℝ) -
              (p : ℝ) * R ^ (p : ℝ) * ‖w‖ ^ (-(p : ℝ))
            = -((p : ℝ) + 2) * Real.log (2 * R) -
              (p : ℝ) * (‖z / w‖ ^ p + 1) := by rw [hupow]; ring
        _ ≤ Real.log ‖(1 : ℂ) - z / w‖ - (p : ℝ) * (‖z / w‖ ^ p + 1) := by
            linarith
        _ ≤ Real.log ‖weierstrassFactor p (z / w)‖ := hbase

/-- On separated circles the canonical product has a power-logarithmic lower bound. -/
theorem exists_log_norm_tprod_lower {a : ℕ → Option ℂ} {p : ℕ} {B C R0 : ℝ}
    (hpB : (p : ℝ) < B) (hBq : B < (p : ℝ) + 1) (hC : 0 ≤ C) (hR0 : 1 ≤ R0)
    (hsum : Summable (slopeWeight p a)) (hne : ∀ n w, a n = some w → w ≠ 0)
    (hfin : ∀ R : ℝ, {n | ∃ w, a n = some w ∧ ‖w‖ ≤ R}.Finite)
    (hcount : ∀ R : ℝ, R0 ≤ R →
      (({n | ∃ w, a n = some w ∧ ‖w‖ ≤ R}.ncard : ℝ) ≤ C * R ^ B)) :
    ∃ K : ℝ, ∀ {R : ℝ}, R0 ≤ R →
      (∀ n w, a n = some w → |R - ‖w‖| < 1 →
        ‖w‖ ^ (-((p : ℝ) + 1)) ≤ |R - ‖w‖|) →
      ∀ z : ℂ, ‖z‖ = R →
        -K * R ^ B * (Real.log (2 * R) + 1) ≤
          Real.log ‖∏' n, genusFactor p a n z‖ := by
  classical
  let q : ℝ := (p : ℝ) + 1
  let α : ℝ := (p : ℝ)
  have hqB : B < q := by simpa [q] using hBq
  have hαB : α < B := by dsimp [α]; exact hpB
  let sSmall : Finset ℕ := (hfin R0).toFinset.filter fun n =>
    ∃ w, a n = some w ∧ ‖w‖ ≤ R0
  let wpow : ℕ → ℝ := fun n =>
    match a n with
    | none => 0
    | some w => ‖w‖ ^ (-α)
  let S0 : ℝ := ∑ n ∈ sSmall, wpow n
  have hS0 : 0 ≤ S0 := by
    dsimp [S0]
    refine Finset.sum_nonneg fun n _ => ?_
    cases ha : a n with
    | none => simp [wpow, ha]
    | some w => simp [wpow, ha, Real.rpow_nonneg]
  let headCoeff : ℝ :=
    C * (2 : ℝ) ^ B * (4 : ℝ) ^ (B - α) / ((2 : ℝ) ^ (B - α) - 1)
  let tailCoeff : ℝ := C * (2 : ℝ) ^ B / (1 - (2 : ℝ) ^ (B - q))
  have hhead : 0 ≤ headCoeff := by
    have hden : 0 < (2 : ℝ) ^ (B - α) - 1 := by
      have hgt := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (sub_pos.mpr hαB)
      linarith
    dsimp [headCoeff]
    exact div_nonneg (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg (by norm_num) _)) hden.le
  have htail : 0 ≤ tailCoeff := by
    have hden : 0 < 1 - (2 : ℝ) ^ (B - q) := by
      have hlt := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
        (sub_neg.mpr hqB)
      linarith
    dsimp [tailCoeff]
    exact div_nonneg (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)) hden.le
  let K : ℝ := C * (2 : ℝ) ^ B * (α + 2) + α * (S0 + headCoeff) + 2 * tailCoeff
  refine ⟨K, ?_⟩
  intro R hR hgood z hz
  have hR1 : 1 ≤ R := hR0.trans hR
  have hRpos : 0 < R := by linarith
  have h2R : R0 ≤ 2 * R := by linarith
  let low : ℕ → ℝ := genusFactorLogLower p a R
  have hlow : ∀ n, low n ≤ Real.log ‖genusFactor p a n z‖ := by
    intro n
    exact log_norm_genusFactor_lower (fun w hw => hne n w hw) hR1 hz
      (fun w hw hclose => hgood n w hw hclose)
  let nearFun : ℕ → ℝ := fun n =>
    match a n with
    | none => 0
    | some w =>
        if ‖w‖ < 2 * R then
          -(α + 2) * Real.log (2 * R) - α - α * R ^ α * ‖w‖ ^ (-α)
        else 0
  let farFun : ℕ → ℝ := fun n =>
    match a n with
    | none => 0
    | some w =>
        if 2 * R ≤ ‖w‖ then -2 * R ^ q * ‖w‖ ^ (-q) else 0
  have hsplit : ∀ n, low n = nearFun n + farFun n := by
    intro n
    cases ha : a n with
    | none => simp [low, genusFactorLogLower, nearFun, farFun, ha]
    | some w =>
      by_cases hfar : 2 * R ≤ ‖w‖
      · simp [low, genusFactorLogLower, nearFun, farFun, ha, hfar, q]
      · have hlt : ‖w‖ < 2 * R := lt_of_not_ge hfar
        simp [low, genusFactorLogLower, nearFun, farFun, ha, hfar, hlt, α]
  let weight : ℕ → ℝ := fun n =>
    match a n with
    | none => 0
    | some w => if 2 * R ≤ ‖w‖ then ‖w‖ ^ (-q) else 0
  have hweight_nn : ∀ n, 0 ≤ weight n := by
    intro n
    cases ha : a n with
    | none => simp [weight, ha]
    | some w =>
      simp only [weight, ha]
      split_ifs
      · exact Real.rpow_nonneg (norm_nonneg _) _
      · exact le_rfl
  have hweight_le : ∀ n, weight n ≤ slopeWeight p a n := by
    intro n
    cases ha : a n with
    | none => simp [weight, slopeWeight, ha]
    | some w =>
      simp only [weight, slopeWeight, ha, q]
      split_ifs
      · rfl
      · exact Real.rpow_nonneg (norm_nonneg _) _
  have hweight_sum : Summable weight :=
    Summable.of_norm_bounded hsum fun n => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hweight_nn n)]
      exact hweight_le n
  have hfar_eq : ∀ n, farFun n = -2 * R ^ q * weight n := by
    intro n
    cases ha : a n with
    | none => simp [farFun, weight, ha]
    | some w =>
      by_cases hfar : 2 * R ≤ ‖w‖
      · simp [farFun, weight, ha, hfar]
      · simp [farFun, weight, ha, hfar]
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have htail_bound := dyadic_tail_le (a := a) (B := B) (q := q) (C := C) (R0 := R0)
    hqB hq0 hC hR0 hfin hcount hR
  have htsum_weight : ∑' n, weight n ≤ tailCoeff * R ^ (B - q) := by
    convert htail_bound using 3 with n
    dsimp only [weight]
    cases a n <;> rfl
  have hfar_sum : Summable farFun := by
    have hmul : Summable fun n => -2 * R ^ q * weight n := hweight_sum.mul_left _
    exact hmul.congr fun n => (hfar_eq n).symm
  have htsum_far : -2 * tailCoeff * R ^ B ≤ ∑' n, farFun n := by
    have hmul := tsum_mul_left (L := SummationFilter.unconditional ℕ)
      (a := -2 * R ^ q) (f := weight)
    have hnonpos : -2 * R ^ q ≤ 0 := by
      have hpow : 0 ≤ R ^ q := Real.rpow_nonneg hRpos.le _
      linarith
    have hstep := mul_le_mul_of_nonpos_left htsum_weight hnonpos
    have hprod : R ^ q * R ^ (B - q) = R ^ B := by
      rw [← Real.rpow_add hRpos]
      exact congrArg (fun t : ℝ => R ^ t) (by ring)
    have hfun : farFun = fun n => -2 * R ^ q * weight n := funext hfar_eq
    calc
      -2 * tailCoeff * R ^ B = -2 * R ^ q * (tailCoeff * R ^ (B - q)) := by
        rw [← hprod]; ring
      _ ≤ -2 * R ^ q * ∑' n, weight n := hstep
      _ = ∑' n, -2 * R ^ q * weight n := hmul.symm
      _ = ∑' n, farFun n := congrArg (fun f : ℕ → ℝ => ∑' n, f n) hfun.symm
  let sNear : Finset ℕ := (hfin (2 * R)).toFinset.filter fun n =>
    ∃ w, a n = some w ∧ ‖w‖ < 2 * R
  have hnear_zero : ∀ n ∉ sNear, nearFun n = 0 := by
    intro n hn
    cases ha : a n with
    | none => simp [nearFun, ha]
    | some w =>
      by_cases hlt : ‖w‖ < 2 * R
      · have hmem : n ∈ sNear := by
          refine Finset.mem_filter.mpr ⟨?_, ⟨w, ha, hlt⟩⟩
          exact (hfin (2 * R)).mem_toFinset.mpr ⟨w, ha, hlt.le⟩
        exact (hn hmem).elim
      · simp [nearFun, ha, hlt]
  have hnear_sum : Summable nearFun := summable_of_ne_finset_zero hnear_zero
  have htsum_near : ∑' n, nearFun n = ∑ n ∈ sNear, nearFun n :=
    tsum_eq_sum (L := SummationFilter.unconditional ℕ) hnear_zero
  have hcard : (sNear.card : ℝ) ≤ C * (2 * R) ^ B := by
    refine (Nat.cast_le.mpr ?_).trans (hcount (2 * R) h2R)
    refine (Finset.card_le_card (Finset.filter_subset _ _)).trans ?_
    exact le_of_eq (Set.ncard_eq_toFinset_card _ (hfin (2 * R))).symm
  have htwo : (2 * R) ^ B = (2 : ℝ) ^ B * R ^ B :=
    Real.mul_rpow (by norm_num) hRpos.le
  let sHead : Finset ℕ := (hfin (2 * R)).toFinset.filter fun n =>
    ∃ w, a n = some w ∧ R0 ≤ ‖w‖ ∧ ‖w‖ < 2 * R
  have hhead_sum : ∑ n ∈ sHead, wpow n ≤ headCoeff * R ^ (B - α) := by
    have hmem : ∀ n ∈ sHead, ∃ w, a n = some w ∧ R0 ≤ ‖w‖ ∧ ‖w‖ < 2 * R :=
      fun n hn => (Finset.mem_filter.mp hn).2
    have hdy := dyadic_head_le (a := a) (B := B) (α := α) (C := C) (R0 := R0)
      (Nat.cast_nonneg p) hαB hC hR0 hfin hcount hR sHead hmem
    convert hdy using 2 with n
    dsimp only [wpow]
    cases a n <;> rfl
  have hsmall_sum : ∑ n ∈ sSmall, wpow n = S0 := rfl
  have hcover : sNear ⊆ sSmall ∪ sHead := by
    intro n hn
    obtain ⟨hball, hex⟩ := Finset.mem_filter.mp hn
    obtain ⟨w, hw, hlt⟩ := hex
    by_cases hle : ‖w‖ ≤ R0
    · exact Finset.mem_union_left _ <| Finset.mem_filter.mpr
        ⟨(hfin R0).mem_toFinset.mpr ⟨w, hw, hle⟩, ⟨w, hw, hle⟩⟩
    · exact Finset.mem_union_right _ <| Finset.mem_filter.mpr
        ⟨hball, ⟨w, hw, le_of_not_ge hle, hlt⟩⟩
  have hwpow_nn : ∀ n, 0 ≤ wpow n := by
    intro n
    cases ha : a n with
    | none => simp [wpow, ha]
    | some w => simp [wpow, ha, Real.rpow_nonneg]
  have hnear_w : ∑ n ∈ sNear, wpow n ≤ S0 + headCoeff * R ^ (B - α) := by
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg hcover
      (fun n _ _ => hwpow_nn n)
    have hinter : 0 ≤ ∑ n ∈ sSmall ∩ sHead, wpow n :=
      Finset.sum_nonneg fun n _ => hwpow_nn n
    have hunion := Finset.sum_union_inter (s₁ := sSmall) (s₂ := sHead) (f := wpow)
    have hsplit_sum : ∑ n ∈ sSmall ∪ sHead, wpow n ≤ ∑ n ∈ sSmall, wpow n +
        ∑ n ∈ sHead, wpow n := by linarith
    have hsum_le : ∑ n ∈ sSmall ∪ sHead, wpow n ≤ S0 + headCoeff * R ^ (B - α) := by
      calc
        ∑ n ∈ sSmall ∪ sHead, wpow n ≤ ∑ n ∈ sSmall, wpow n + ∑ n ∈ sHead, wpow n :=
          hsplit_sum
        _ ≤ S0 + headCoeff * R ^ (B - α) := by
          rw [hsmall_sum]
          exact add_le_add le_rfl hhead_sum
    exact hsub.trans hsum_le
  have hpoint : ∀ n ∈ sNear, nearFun n =
      -(α + 2) * Real.log (2 * R) - α - α * R ^ α * wpow n := by
    intro n hn
    obtain ⟨_, hex⟩ := Finset.mem_filter.mp hn
    obtain ⟨w, hw, hlt⟩ := hex
    simp [nearFun, wpow, hw, hlt, α]
  have hsum_near_eq : ∑ n ∈ sNear, nearFun n =
      (sNear.card : ℝ) * (-(α + 2) * Real.log (2 * R) - α) -
        α * R ^ α * ∑ n ∈ sNear, wpow n := by
    rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.mul_sum]
  have hlognn : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  have hlog1 : 1 ≤ Real.log (2 * R) + 1 := by linarith
  have hRb : 0 ≤ R ^ B := Real.rpow_nonneg hRpos.le _
  have hRα : R ^ α ≤ R ^ B :=
    Real.rpow_le_rpow_of_exponent_le hR1 (le_of_lt hαB)
  have hRsplit : R ^ α * R ^ (B - α) = R ^ B := by
    rw [← Real.rpow_add hRpos]
    exact congrArg (fun t : ℝ => R ^ t) (by ring)
  have hN : (sNear.card : ℝ) * ((α + 2) * Real.log (2 * R) + α) ≤
      C * (2 : ℝ) ^ B * (α + 2) * R ^ B * (Real.log (2 * R) + 1) := by
    have hterm : (α + 2) * Real.log (2 * R) + α ≤ (α + 2) * (Real.log (2 * R) + 1) := by
      linarith
    have hcard' : (sNear.card : ℝ) ≤ C * (2 : ℝ) ^ B * R ^ B := by
      calc
        (sNear.card : ℝ) ≤ C * (2 * R) ^ B := hcard
        _ = C * (2 : ℝ) ^ B * R ^ B := by rw [htwo]; ring
    have hnonneg : 0 ≤ (α + 2) * Real.log (2 * R) + α := by
      have hα2 : 0 ≤ α + 2 := by dsimp [α]; linarith
      nlinarith
    calc
      (sNear.card : ℝ) * ((α + 2) * Real.log (2 * R) + α)
          ≤ (C * (2 : ℝ) ^ B * R ^ B) * ((α + 2) * (Real.log (2 * R) + 1)) := by
            exact mul_le_mul hcard' hterm hnonneg (mul_nonneg
              (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)) hRb)
      _ = C * (2 : ℝ) ^ B * (α + 2) * R ^ B * (Real.log (2 * R) + 1) := by ring
  have hpow_bound : α * R ^ α * ∑ n ∈ sNear, wpow n ≤
      α * (S0 + headCoeff) * R ^ B * (Real.log (2 * R) + 1) := by
    have hα0 : 0 ≤ α := by dsimp [α]; exact Nat.cast_nonneg p
    have hRαnn : 0 ≤ R ^ α := Real.rpow_nonneg hRpos.le _
    have hleft : α * (R ^ α * S0) ≤ α * (R ^ B * S0) := by
      refine mul_le_mul_of_nonneg_left ?_ hα0
      exact mul_le_mul_of_nonneg_right hRα hS0
    have hright : α * (R ^ α * (headCoeff * R ^ (B - α))) = α * (headCoeff * R ^ B) := by
      calc
        α * (R ^ α * (headCoeff * R ^ (B - α)))
            = α * headCoeff * (R ^ α * R ^ (B - α)) := by ring
        _ = α * headCoeff * R ^ B := by rw [hRsplit]
        _ = α * (headCoeff * R ^ B) := by ring
    calc
      α * R ^ α * ∑ n ∈ sNear, wpow n
          ≤ α * R ^ α * (S0 + headCoeff * R ^ (B - α)) :=
            mul_le_mul_of_nonneg_left hnear_w (mul_nonneg hα0 hRαnn)
      _ = α * (R ^ α * S0) + α * (R ^ α * (headCoeff * R ^ (B - α))) := by ring
      _ ≤ α * (R ^ B * S0) + α * (headCoeff * R ^ B) := by
          exact add_le_add hleft (le_of_eq hright)
      _ = α * (S0 + headCoeff) * R ^ B := by ring
      _ ≤ α * (S0 + headCoeff) * R ^ B * (Real.log (2 * R) + 1) :=
          le_mul_of_one_le_right
            (mul_nonneg (mul_nonneg hα0 (add_nonneg hS0 hhead)) hRb) hlog1
  have hnear_ge : -(C * (2 : ℝ) ^ B * (α + 2) + α * (S0 + headCoeff)) * R ^ B *
      (Real.log (2 * R) + 1) ≤ ∑ n ∈ sNear, nearFun n := by
    rw [hsum_near_eq]
    have hident : (sNear.card : ℝ) * (-(α + 2) * Real.log (2 * R) - α) -
        α * R ^ α * ∑ n ∈ sNear, wpow n =
        -((sNear.card : ℝ) * ((α + 2) * Real.log (2 * R) + α)) -
          α * R ^ α * ∑ n ∈ sNear, wpow n := by ring
    rw [hident]
    have hneg1 : -(C * (2 : ℝ) ^ B * (α + 2) * R ^ B * (Real.log (2 * R) + 1)) ≤
        -((sNear.card : ℝ) * ((α + 2) * Real.log (2 * R) + α)) := neg_le_neg hN
    have hneg2 : -(α * (S0 + headCoeff) * R ^ B * (Real.log (2 * R) + 1)) ≤
        -(α * R ^ α * ∑ n ∈ sNear, wpow n) := neg_le_neg hpow_bound
    have hjoin : -(C * (2 : ℝ) ^ B * (α + 2) + α * (S0 + headCoeff)) * R ^ B *
        (Real.log (2 * R) + 1) =
        -(C * (2 : ℝ) ^ B * (α + 2) * R ^ B * (Real.log (2 * R) + 1)) +
          -(α * (S0 + headCoeff) * R ^ B * (Real.log (2 * R) + 1)) := by ring
    exact hjoin.trans_le (add_le_add hneg1 hneg2)
  have hfar_ge : -((2 * tailCoeff) * R ^ B * (Real.log (2 * R) + 1)) ≤ ∑' n, farFun n := by
    have hscale : 2 * tailCoeff * R ^ B ≤ 2 * tailCoeff * R ^ B * (Real.log (2 * R) + 1) :=
      le_mul_of_one_le_right (mul_nonneg (mul_nonneg (by norm_num) htail) hRb) hlog1
    have hneg_eq : -(2 * tailCoeff * R ^ B) = -2 * tailCoeff * R ^ B := by ring
    exact (neg_le_neg hscale).trans (hneg_eq.trans_le htsum_far)
  have hlow_sum : Summable low :=
    (hnear_sum.add hfar_sum).congr fun n => (hsplit n).symm
  have htsum_split : ∑' n, low n = ∑' n, nearFun n + ∑' n, farFun n := by
    rw [← hnear_sum.tsum_add hfar_sum]
    refine tsum_congr ?_
    intro n
    exact hsplit n
  have htsum_low : -K * R ^ B * (Real.log (2 * R) + 1) ≤ ∑' n, low n := by
    rw [htsum_split, htsum_near]
    have hjoin : -K * R ^ B * (Real.log (2 * R) + 1) =
        -(C * (2 : ℝ) ^ B * (α + 2) + α * (S0 + headCoeff)) * R ^ B *
          (Real.log (2 * R) + 1) +
          -((2 * tailCoeff) * R ^ B * (Real.log (2 * R) + 1)) := by
      dsimp [K]
      ring
    exact hjoin.trans_le (add_le_add hnear_ge hfar_ge)
  have hsub := summable_norm_genusFactor_sub_one p a hsum hne z
  have hlogsum : Summable fun n => Real.log ‖genusFactor p a n z‖ := by
    have h := (hsub.summable_log_norm_one_add (f := fun n => genusFactor p a n z - 1))
    refine h.congr fun n => ?_
    rw [show (1 : ℂ) + (genusFactor p a n z - 1) = genusFactor p a n z by ring]
  have hcmp : ∑' n, low n ≤ ∑' n, Real.log ‖genusFactor p a n z‖ :=
    hlow_sum.tsum_le_tsum hlow hlogsum
  have hFne : ∀ n, genusFactor p a n z ≠ 0 := by
    intro n hzero
    have hsome := (genusFactor_eq_zero_iff (fun w hw => hne n w hw)).mp hzero
    have hsep := hgood n z hsome (by simp [hz])
    exact (not_le_of_gt (Real.rpow_pos_of_pos (norm_pos_iff.mpr (hne n z hsome)) _))
      (by simpa [hz] using hsep)
  have hposF : ∀ n, 0 < ‖genusFactor p a n z‖ := fun n => norm_pos_iff.mpr (hFne n)
  have hprod := Real.rexp_tsum_eq_tprod hposF hlogsum
  have hnorm := (multipliable_genusFactor p a hsum hne z).norm_tprod
  have hlogeq : Real.log ‖∏' n, genusFactor p a n z‖ =
      ∑' n, Real.log ‖genusFactor p a n z‖ := by
    rw [hnorm, ← hprod, Real.log_exp]
  exact (htsum_low.trans hcmp).trans_eq hlogeq.symm

end CKMA
