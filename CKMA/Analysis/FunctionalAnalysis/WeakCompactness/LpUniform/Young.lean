/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Order.Filter.Extr
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.OrderClosed

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar defect for uniform convexity of scalar Lp

The estimates are those of Hanche-Olsen, *On the uniform convexity of Lp*, Proceedings of the
American Mathematical Society 134 (2006), 2359–2362 (arXiv:math/0502021). The Young defect
`‖u‖ ^ p - 1 + p * (1 - re u)` is nonnegative for `1 < p`, vanishes only at `1`, and controls
`‖u - 1‖ ^ p` once `‖u - 1‖` is bounded below. The dual weight `star z * ‖z‖ ^ (p - 2)` satisfies
`z * lpDualFun p z = ‖z‖ ^ p` and `‖lpDualFun p z‖ = ‖z‖ ^ (p - 1)`.
-/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

namespace CKMA.WeakCompactness

open Filter Metric Real Set Topology
open scoped NNReal

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Young defect `‖u‖ ^ p - 1 + p * (1 - re u)` of a scalar. -/
def youngDefect (p : ℝ) (u : 𝕜) : ℝ :=
  ‖u‖ ^ p - 1 + p * (1 - RCLike.re u)

/-- The defect expands as `‖u‖ ^ p - p * re u + p - 1`. -/
theorem youngDefect_eq (p : ℝ) (u : 𝕜) :
    youngDefect p u = ‖u‖ ^ p - p * RCLike.re u + p - 1 := by
  unfold youngDefect
  ring

/-- The defect depends continuously on the scalar. -/
theorem continuous_youngDefect {p : ℝ} (hp : 1 < p) : Continuous (youngDefect p : 𝕜 → ℝ) := by
  have hp0 : (0 : ℝ) ≤ p := by linarith
  unfold youngDefect
  exact ((continuous_norm.rpow_const fun _ ↦ Or.inr hp0).sub continuous_const).add
    (continuous_const.mul (continuous_const.sub RCLike.continuous_re))

/-- Young’s inequality at the second argument `1` gives `p * ‖u‖ ≤ ‖u‖ ^ p + p - 1`. -/
theorem p_mul_norm_le_norm_rpow_add {p : ℝ} (hp : 1 < p) (u : 𝕜) :
    p * ‖u‖ ≤ ‖u‖ ^ p + p - 1 := by
  have hq : p.HolderConjugate (conjExponent p) := HolderConjugate.conjExponent hp
  have hy := young_inequality_of_nonneg (norm_nonneg u) zero_le_one hq
  rw [mul_one, one_rpow] at hy
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hmul := mul_le_mul_of_nonneg_left hy hp0.le
  have hrewrite : p * (‖u‖ ^ p / p + 1 / conjExponent p) = ‖u‖ ^ p + p / conjExponent p := by
    field_simp [hp0.ne', hq.symm.ne_zero]
  rw [hrewrite, hq.div_conj_eq_sub_one] at hmul
  linarith

/-- The Young defect is nonnegative for every scalar when `1 < p`. -/
theorem youngDefect_nonneg {p : ℝ} (hp : 1 < p) (u : 𝕜) : 0 ≤ youngDefect p u := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hre : p * RCLike.re u ≤ p * ‖u‖ :=
    mul_le_mul_of_nonneg_left (RCLike.re_le_norm u) hp0.le
  rw [youngDefect_eq]
  linarith [hre.trans (p_mul_norm_le_norm_rpow_add hp u)]

/-- The Young defect vanishes if and only if the scalar equals `1`. -/
theorem youngDefect_eq_zero_iff {p : ℝ} (hp : 1 < p) {u : 𝕜} :
    youngDefect p u = 0 ↔ u = 1 := by
  constructor
  · intro h0
    have hq : p.HolderConjugate (conjExponent p) := HolderConjugate.conjExponent hp
    have hp0 : 0 < p := zero_lt_one.trans hp
    have hpre : p * RCLike.re u = ‖u‖ ^ p + p - 1 := by
      rw [youngDefect_eq] at h0
      linarith
    have hnorm_eq : p * ‖u‖ = ‖u‖ ^ p + p - 1 := by
      linarith [hpre, mul_le_mul_of_nonneg_left (RCLike.re_le_norm u) hp0.le,
        p_mul_norm_le_norm_rpow_add hp u]
    have hre_norm : RCLike.re u = ‖u‖ :=
      mul_left_cancel₀ hp0.ne' (by linarith [hpre, hnorm_eq])
    have hdiv : ‖u‖ = ‖u‖ ^ p / p + (p - 1) / p := by
      apply mul_left_cancel₀ hp0.ne'
      field_simp [hp0.ne']
      linarith [hnorm_eq]
    have hconj : (p - 1) / p = (conjExponent p)⁻¹ := by
      simp only [conjExponent]
      field_simp
    have hyeq : ‖u‖ * 1 = ‖u‖ ^ p / p + (1 : ℝ) ^ conjExponent p / conjExponent p := by
      rw [mul_one, one_rpow]
      calc
        ‖u‖ = ‖u‖ ^ p / p + (p - 1) / p := hdiv
        _ = ‖u‖ ^ p / p + (conjExponent p)⁻¹ := by rw [hconj]
        _ = ‖u‖ ^ p / p + 1 / conjExponent p := by rw [← one_div]
    have hpow : ‖u‖ ^ p = (1 : ℝ) ^ conjExponent p :=
      (young_inequality_eq_iff_of_nonneg (norm_nonneg u) zero_le_one hq).mp hyeq
    have hnorm : ‖u‖ = 1 :=
      (rpow_left_inj (norm_nonneg u) zero_le_one hp0.ne').mp (by simpa [one_rpow] using hpow)
    have hu : u = (‖u‖ : 𝕜) :=
      (RCLike.norm_le_re_iff_eq_norm).mp (by linarith [hre_norm])
    rw [hnorm] at hu
    simpa [RCLike.ofReal_one] using hu
  · rintro rfl
    simp [youngDefect, norm_one, RCLike.one_re, one_rpow]

/-- For `‖u‖` at least `R`, with `R ^ (p - 1) ≥ 2p` and `R ≥ 1`, the defect is at least half of
`‖u‖ ^ p`. -/
theorem youngDefect_ge_half_norm_rpow {p : ℝ} (hp : 1 < p) {R : ℝ} (hR1 : 1 ≤ R)
    (hRpow : 2 * p ≤ R ^ (p - 1)) {u : 𝕜} (hu : R ≤ ‖u‖) :
    ‖u‖ ^ p / 2 ≤ youngDefect p u := by
  have hp1 : 0 ≤ p - 1 := by linarith
  have hupow : 2 * p ≤ ‖u‖ ^ (p - 1) :=
    (hRpow).trans (rpow_le_rpow (by linarith) hu hp1)
  have hnorm1 : 1 ≤ ‖u‖ := hR1.trans hu
  have hsplit : ‖u‖ * ‖u‖ ^ (p - 1) = ‖u‖ ^ p := by
    have hpos : 0 < ‖u‖ := by linarith
    calc
      ‖u‖ * ‖u‖ ^ (p - 1) = ‖u‖ ^ (1 : ℝ) * ‖u‖ ^ (p - 1) :=
        congrArg (· * ‖u‖ ^ (p - 1)) (rpow_one _).symm
      _ = ‖u‖ ^ (1 + (p - 1)) := (rpow_add hpos 1 (p - 1)).symm
      _ = ‖u‖ ^ p := by
        refine congrArg (‖u‖ ^ ·) ?_
        ring
  have hhalf : p * ‖u‖ ≤ ‖u‖ ^ p / 2 := by
    have hmul : ‖u‖ * (2 * p) ≤ ‖u‖ * ‖u‖ ^ (p - 1) := by gcongr
    have : 2 * p * ‖u‖ ≤ ‖u‖ ^ p := by
      calc
        2 * p * ‖u‖ = ‖u‖ * (2 * p) := by ring
        _ ≤ ‖u‖ * ‖u‖ ^ (p - 1) := hmul
        _ = ‖u‖ ^ p := hsplit
    linarith
  have hre : p * RCLike.re u ≤ ‖u‖ ^ p / 2 := by
    calc
      p * RCLike.re u ≤ p * ‖u‖ := by gcongr; exact RCLike.re_le_norm u
      _ ≤ ‖u‖ ^ p / 2 := hhalf
  rw [youngDefect_eq]
  linarith

/-- On the region `ε ≤ ‖u - 1‖`, some positive multiple of the defect dominates `‖u - 1‖ ^ p`. -/
theorem exists_youngDefect_mul_le {p : ℝ} (hp : 1 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ α > 0, ∀ u : 𝕜, ε ≤ ‖u - 1‖ → ‖u - 1‖ ^ p ≤ α * youngDefect p u := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hp1 : 0 < p - 1 := by linarith
  let R : ℝ := max (1 + ε) ((2 * p) ^ (1 / (p - 1)))
  have hRε : 1 + ε ≤ R := le_max_left _ _
  have hR1 : 1 ≤ R := le_trans (by linarith) hRε
  have hpowt : ((2 * p) ^ (1 / (p - 1))) ^ (p - 1) = 2 * p := by
    rw [← rpow_mul (by linarith : 0 ≤ 2 * p)]
    have : (1 / (p - 1)) * (p - 1) = 1 := by field_simp
    rw [this, rpow_one]
  have hRpow : 2 * p ≤ R ^ (p - 1) := by
    calc
      2 * p = ((2 * p) ^ (1 / (p - 1))) ^ (p - 1) := hpowt.symm
      _ ≤ R ^ (p - 1) :=
        rpow_le_rpow (rpow_nonneg (by linarith) _) (le_max_right _ _) hp1.le
  let s : Set 𝕜 := {u | ε ≤ ‖u - 1‖} ∩ closedBall 0 R
  have hs_closed : IsClosed s :=
    (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))).inter
      isClosed_closedBall
  have hs_compact : IsCompact s :=
    (isCompact_closedBall (0 : 𝕜) R).of_isClosed_subset hs_closed fun u hu ↦ hu.2
  have hs_nonempty : s.Nonempty := by
    refine ⟨((1 + ε : ℝ) : 𝕜), ?_, ?_⟩
    · have hsub : ((1 + ε : ℝ) : 𝕜) - 1 = (ε : 𝕜) := by
        rw [RCLike.ofReal_add, RCLike.ofReal_one, add_sub_cancel_left]
      change ε ≤ ‖((1 + ε : ℝ) : 𝕜) - 1‖
      rw [hsub, RCLike.norm_ofReal, abs_of_pos hε]
    · rw [mem_closedBall, dist_zero_right, RCLike.norm_ofReal,
        abs_of_pos (by linarith : 0 < 1 + ε)]
      exact hRε
  have hpos : ∀ u ∈ s, 0 < youngDefect p u := by
    intro u hu
    have hne : u ≠ 1 := by
      intro hu1
      have : ε ≤ ‖(1 : 𝕜) - 1‖ := by simpa [hu1] using hu.1
      simp at this
      linarith
    have hne0 : youngDefect p u ≠ 0 := (youngDefect_eq_zero_iff hp).not.mpr hne
    exact lt_of_le_of_ne (youngDefect_nonneg hp u) (Ne.symm hne0)
  have hnum : Continuous fun u : 𝕜 ↦ ‖u - 1‖ ^ p :=
    (continuous_norm.comp (continuous_id.sub continuous_const)).rpow_const fun _ ↦ Or.inr hp0.le
  have hcont : ContinuousOn (fun u ↦ ‖u - 1‖ ^ p / youngDefect p u) s :=
    hnum.continuousOn.div (continuous_youngDefect hp).continuousOn fun u hu ↦ (hpos u hu).ne'
  obtain ⟨u0, hu0, hmax⟩ := hs_compact.exists_isMaxOn hs_nonempty hcont
  let α : ℝ := max (‖u0 - 1‖ ^ p / youngDefect p u0) (2 ^ (p + 1))
  have hα : 0 < α := lt_max_of_lt_right (by positivity)
  refine ⟨α, hα, fun u huε ↦ ?_⟩
  by_cases hball : ‖u‖ ≤ R
  · have hus : u ∈ s := ⟨huε, by rwa [mem_closedBall, dist_zero_right]⟩
    have hratio : ‖u - 1‖ ^ p / youngDefect p u ≤ α :=
      calc
        ‖u - 1‖ ^ p / youngDefect p u ≤ ‖u0 - 1‖ ^ p / youngDefect p u0 :=
          (isMaxOn_iff.mp hmax) u hus
        _ ≤ α := le_max_left _ _
    exact (div_le_iff₀ (hpos u hus)).mp hratio
  · push Not at hball
    have huR : R ≤ ‖u‖ := le_of_lt hball
    have hdef : ‖u‖ ^ p / 2 ≤ youngDefect p u :=
      youngDefect_ge_half_norm_rpow hp hR1 hRpow huR
    have hle : ‖u - 1‖ ≤ 2 * ‖u‖ := by
      calc
        ‖u - 1‖ ≤ ‖u‖ + ‖(-1 : 𝕜)‖ := by simpa [sub_eq_add_neg] using norm_add_le u (-1 : 𝕜)
        _ = ‖u‖ + 1 := by simp
        _ ≤ ‖u‖ + ‖u‖ := by gcongr; exact hR1.trans huR
        _ = 2 * ‖u‖ := by ring
    have hrpow : ‖u - 1‖ ^ p ≤ (2 * ‖u‖) ^ p := rpow_le_rpow (norm_nonneg _) hle hp0.le
    have hprod : (2 * ‖u‖) ^ p = 2 ^ p * ‖u‖ ^ p := mul_rpow (by norm_num) (norm_nonneg _)
    have htwo : 2 ^ p * (2 * youngDefect p u) = 2 ^ (p + 1) * youngDefect p u := by
      calc
        2 ^ p * (2 * youngDefect p u) = (2 ^ p * 2 ^ (1 : ℝ)) * youngDefect p u := by
          rw [rpow_one]; ring
        _ = 2 ^ (p + 1) * youngDefect p u := by
          rw [← rpow_add (by norm_num : (0 : ℝ) < 2) p 1]
    have hlarge : ‖u - 1‖ ^ p ≤ 2 ^ (p + 1) * youngDefect p u := by
      calc
        ‖u - 1‖ ^ p ≤ 2 ^ p * ‖u‖ ^ p := by rwa [hprod] at hrpow
        _ ≤ 2 ^ p * (2 * youngDefect p u) := by gcongr; linarith
        _ = 2 ^ (p + 1) * youngDefect p u := htwo
    calc
      ‖u - 1‖ ^ p ≤ 2 ^ (p + 1) * youngDefect p u := hlarge
      _ ≤ α * youngDefect p u := by
        gcongr
        · exact youngDefect_nonneg hp u
        · exact le_max_right _ _

/-- Pointwise dual weight `star z * ‖z‖ ^ (p - 2)`, equal to zero at the origin. -/
def lpDualFun (p : ℝ) (z : 𝕜) : 𝕜 :=
  star z * RCLike.ofReal (‖z‖ ^ (p - 2))

/-- The dual weight vanishes at zero for every exponent. -/
@[simp]
theorem lpDualFun_zero (p : ℝ) : lpDualFun p (0 : 𝕜) = 0 := by
  simp [lpDualFun]

/-- Multiplication by the scalar recovers the powered norm: `z * lpDualFun p z = ‖z‖ ^ p`. -/
theorem mul_lpDualFun {p : ℝ} (hp : 1 < p) (z : 𝕜) :
    z * lpDualFun p z = RCLike.ofReal (‖z‖ ^ p) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Real.zero_rpow (show p ≠ 0 by linarith)]
  · have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
    unfold lpDualFun
    rw [RCLike.star_def, ← mul_assoc, RCLike.mul_conj]
    have hpow : ‖z‖ ^ (2 : ℕ) * ‖z‖ ^ (p - 2) = ‖z‖ ^ p := by
      rw [show ‖z‖ ^ (2 : ℕ) = ‖z‖ ^ ((2 : ℕ) : ℝ) from (rpow_natCast ‖z‖ 2).symm,
        (rpow_add hz0 ((2 : ℕ) : ℝ) (p - 2)).symm]
      exact congrArg (‖z‖ ^ ·) (by ring)
    rw [← RCLike.ofReal_pow ‖z‖ 2, ← RCLike.ofReal_mul, hpow]

/-- The dual weight has norm `‖z‖ ^ (p - 1)`. -/
theorem norm_lpDualFun {p : ℝ} (hp : 1 < p) (z : 𝕜) : ‖lpDualFun p z‖ = ‖z‖ ^ (p - 1) := by
  have hnonneg : 0 ≤ ‖z‖ ^ (p - 2) := rpow_nonneg (norm_nonneg _) _
  have hstar : ‖(star z : 𝕜)‖ = ‖z‖ := by simp [RCLike.star_def]
  rw [lpDualFun, norm_mul, hstar, RCLike.norm_ofReal, abs_of_nonneg hnonneg]
  rcases eq_or_ne z 0 with rfl | hz
  · simp [norm_zero, Real.zero_rpow (show p - 1 ≠ 0 by linarith)]
  · have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
    calc
      ‖z‖ * ‖z‖ ^ (p - 2) = ‖z‖ ^ (1 : ℝ) * ‖z‖ ^ (p - 2) :=
        congrArg (· * ‖z‖ ^ (p - 2)) (rpow_one _).symm
      _ = ‖z‖ ^ (1 + (p - 2)) := (rpow_add hz0 1 (p - 2)).symm
      _ = ‖z‖ ^ (p - 1) := by
        refine congrArg (‖z‖ ^ ·) ?_
        ring

/-- The dual weight is continuous on the scalar field, including at the origin. -/
theorem continuous_lpDualFun {p : ℝ} (hp : 1 < p) : Continuous (lpDualFun p : 𝕜 → 𝕜) := by
  refine continuous_iff_continuousAt.2 fun z ↦ ?_
  by_cases hz : z = 0
  · subst hz
    simp only [ContinuousAt, lpDualFun_zero]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim :=
      (continuous_norm.tendsto (0 : 𝕜)).rpow_const (Or.inr (by linarith : 0 ≤ p - 1))
    simp only [norm_zero, Real.zero_rpow (show p - 1 ≠ 0 by linarith)] at hlim
    simpa [norm_lpDualFun hp] using hlim
  · unfold lpDualFun
    refine ContinuousAt.mul ?_ (RCLike.continuous_ofReal.continuousAt.comp ?_)
    · simpa [RCLike.star_def] using RCLike.continuous_conj.continuousAt
    · exact continuous_norm.continuousAt.rpow_const (Or.inl (norm_ne_zero_iff.mpr hz))

end CKMA.WeakCompactness
