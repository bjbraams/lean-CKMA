/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Ordered

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Positive approximation operators on the unit interval

For order-preserving continuous linear operators on real continuous functions on
`[0,1]`, convergence on `1`, the coordinate function, and its square characterizes
strong convergence to the identity. Positivity uses Mathlib's order predicate
`Monotone`, which is equivalent to preserving nonnegative functions for linear maps.

The direct estimate is the quadratic domination
`|f y - f x| ≤ ε + 2 * ‖f‖ * δ⁻² * (y - x)²` coming from uniform continuity.

Source: GAPS 47.17.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Metric Topology

/-- The real continuous functions on the unit interval, with their supremum norm. -/
abbrev UnitIntervalContinuousMap := C(Set.Icc (0 : ℝ) 1, ℝ)

/-- The coordinate function on the unit interval. -/
def unitIntervalId : UnitIntervalContinuousMap := ⟨fun x ↦ x.1, continuous_subtype_val⟩

/-- Order preservation of a linear operator, equivalently preservation of nonnegative functions. -/
abbrev IsPositiveContinuousMapOperator (L : UnitIntervalContinuousMap →L[ℝ]
    UnitIntervalContinuousMap) : Prop := Monotone L

/-- Monotonicity of a real-linear operator on `C([0,1])` is preservation of nonnegative
functions. -/
private lemma monotone_iff_map_nonneg (L : UnitIntervalContinuousMap →L[ℝ]
    UnitIntervalContinuousMap) : Monotone L ↔ ∀ f, 0 ≤ f → 0 ≤ L f := by
  constructor
  · intro hL f hf
    simpa [L.map_zero] using hL hf
  · intro hL f g hfg
    have hnonneg : 0 ≤ g - f := by
      rw [ContinuousMap.le_def]
      intro x
      rw [ContinuousMap.sub_apply, ContinuousMap.zero_apply]
      exact sub_nonneg.mpr ((ContinuousMap.le_def.mp hfg) x)
    have hmap : 0 ≤ L g - L f := by
      simpa [L.map_sub] using hL (g - f) hnonneg
    rw [ContinuousMap.le_def] at hmap ⊢
    intro x
    have hx : 0 ≤ (L g) x - (L f) x := by
      simpa [ContinuousMap.sub_apply, ContinuousMap.zero_apply] using hmap x
    exact sub_nonneg.mp hx

/-- The square `(y - x) ^ 2`, as a continuous function of `y`, for fixed `x`. -/
private def unitIntervalQuadratic (x : Set.Icc (0 : ℝ) 1) : UnitIntervalContinuousMap :=
  unitIntervalId ^ 2 - (2 * x.1) • unitIntervalId + (x.1 ^ 2) • 1

private lemma unitIntervalQuadratic_apply (x y : Set.Icc (0 : ℝ) 1) :
    unitIntervalQuadratic x y = (y.1 - x.1) ^ 2 := by
  unfold unitIntervalQuadratic unitIntervalId
  simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.pow_apply,
    ContinuousMap.smul_apply, ContinuousMap.one_apply, ContinuousMap.coe_mk, smul_eq_mul]
  ring

private lemma unitIntervalQuadratic_nonneg (x : Set.Icc (0 : ℝ) 1) :
    0 ≤ unitIntervalQuadratic x := by
  rw [ContinuousMap.le_def]
  intro y
  rw [unitIntervalQuadratic_apply, ContinuousMap.zero_apply]
  exact sq_nonneg _

/-- Uniform continuity on the unit interval gives the standard quadratic domination. -/
private lemma abs_sub_le_quadratic (f : UnitIntervalContinuousMap) {ε δ : ℝ} (hε : 0 ≤ ε)
    (hδ : 0 < δ) (hf : ∀ {x y : Set.Icc (0 : ℝ) 1}, dist x y < δ → dist (f x) (f y) < ε)
    (x y : Set.Icc (0 : ℝ) 1) :
    |f y - f x| ≤ ε + (2 * ‖f‖ / δ ^ 2) * (y.1 - x.1) ^ 2 := by
  have hc : 0 ≤ 2 * ‖f‖ / δ ^ 2 :=
    div_nonneg (mul_nonneg zero_le_two (norm_nonneg f)) (sq_nonneg δ)
  by_cases hlt : dist x y < δ
  · have hnear : |f y - f x| < ε := by
      rw [abs_sub_comm, ← Real.dist_eq]
      exact hf hlt
    exact hnear.le.trans (le_add_of_nonneg_right (mul_nonneg hc (sq_nonneg _)))
  · have hdist : δ ≤ |x.1 - y.1| := by
      rw [← Real.dist_eq, ← Subtype.dist_eq]
      exact le_of_not_gt hlt
    have hsq : δ ^ 2 ≤ (y.1 - x.1) ^ 2 := by
      calc
        δ ^ 2 ≤ |x.1 - y.1| ^ 2 := pow_le_pow_left₀ hδ.le hdist 2
        _ = (y.1 - x.1) ^ 2 := by rw [sq_abs]; ring
    have hratio : 1 ≤ (y.1 - x.1) ^ 2 / δ ^ 2 :=
      (one_le_div (sq_pos_of_pos hδ)).mpr hsq
    calc
      |f y - f x| = dist (f x) (f y) := by rw [Real.dist_eq, abs_sub_comm]
      _ ≤ 2 * ‖f‖ := f.dist_le_two_norm x y
      _ = (2 * ‖f‖) * 1 := by ring
      _ ≤ (2 * ‖f‖) * ((y.1 - x.1) ^ 2 / δ ^ 2) :=
        mul_le_mul_of_nonneg_left hratio (mul_nonneg zero_le_two (norm_nonneg f))
      _ = (2 * ‖f‖ / δ ^ 2) * (y.1 - x.1) ^ 2 := by ring
      _ ≤ ε + (2 * ‖f‖ / δ ^ 2) * (y.1 - x.1) ^ 2 := le_add_of_nonneg_left hε

/-- The Korovkin remainder `L(t²) - 2 t L(t) + t² L(1)`, evaluated in the variable `t`. -/
private def korovkinDeviation (L : UnitIntervalContinuousMap →L[ℝ] UnitIntervalContinuousMap) :
    UnitIntervalContinuousMap :=
  L (unitIntervalId ^ 2) - (2 : ℝ) • (unitIntervalId * L unitIntervalId) +
    unitIntervalId ^ 2 * L 1

private lemma eval_unitIntervalQuadratic (L : UnitIntervalContinuousMap →L[ℝ]
    UnitIntervalContinuousMap) (x : Set.Icc (0 : ℝ) 1) :
    (L (unitIntervalQuadratic x)) x = korovkinDeviation L x := by
  unfold unitIntervalQuadratic korovkinDeviation
  rw [L.map_add, L.map_sub, L.map_smul, L.map_smul]
  simp only [ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    ContinuousMap.mul_apply, ContinuousMap.pow_apply, unitIntervalId, ContinuousMap.coe_mk,
    smul_eq_mul]
  ring

private lemma korovkinDeviation_tendsto_zero (L : ℕ → UnitIntervalContinuousMap →L[ℝ]
    UnitIntervalContinuousMap) (h1 : Tendsto (fun n ↦ L n 1) atTop (𝓝 1))
    (hid : Tendsto (fun n ↦ L n unitIntervalId) atTop (𝓝 unitIntervalId))
    (hid2 : Tendsto (fun n ↦ L n (unitIntervalId ^ 2)) atTop (𝓝 (unitIntervalId ^ 2))) :
    Tendsto (fun n ↦ korovkinDeviation (L n)) atTop (𝓝 0) := by
  have hmulId : Tendsto (fun n ↦ unitIntervalId * L n unitIntervalId) atTop
      (𝓝 (unitIntervalId * unitIntervalId)) :=
    tendsto_const_nhds.mul hid
  have hmulSq : Tendsto (fun n ↦ unitIntervalId ^ 2 * L n 1) atTop
      (𝓝 (unitIntervalId ^ 2 * 1)) :=
    tendsto_const_nhds.mul h1
  have hsmul : Tendsto (fun n ↦ (2 : ℝ) • (unitIntervalId * L n unitIntervalId)) atTop
      (𝓝 ((2 : ℝ) • (unitIntervalId * unitIntervalId))) :=
    hmulId.const_smul 2
  have hlim : unitIntervalId ^ 2 - (2 : ℝ) • (unitIntervalId * unitIntervalId) +
      unitIntervalId ^ 2 = 0 := by
    ext x
    simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      ContinuousMap.mul_apply, ContinuousMap.pow_apply, ContinuousMap.zero_apply, unitIntervalId,
      ContinuousMap.coe_mk, smul_eq_mul]
    rw [sq]
    ring
  simpa [korovkinDeviation, mul_one, hlim] using (hid2.sub hsmul).add hmulSq

private lemma one_nonneg_unitInterval : (0 : UnitIntervalContinuousMap) ≤ 1 := by
  rw [ContinuousMap.le_def]
  intro x
  simp

/-- Pointwise Korovkin estimate at a fixed `x`, after applying a positive operator. -/
private lemma abs_eval_sub_le (L : UnitIntervalContinuousMap →L[ℝ] UnitIntervalContinuousMap)
    (hL : Monotone L) (f : UnitIntervalContinuousMap) {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hf : ∀ {x y : Set.Icc (0 : ℝ) 1}, dist x y < δ → dist (f x) (f y) < ε)
    (x : Set.Icc (0 : ℝ) 1) :
    |(L f) x - f x| ≤ ε * ‖L 1‖ + (2 * ‖f‖ / δ ^ 2) * ‖korovkinDeviation L‖ +
      ‖f‖ * ‖L 1 - 1‖ := by
  let c : ℝ := 2 * ‖f‖ / δ ^ 2
  have hc : 0 ≤ c :=
    div_nonneg (mul_nonneg zero_le_two (norm_nonneg f)) (sq_nonneg δ)
  have hpos : ∀ g, 0 ≤ g → 0 ≤ L g := (monotone_iff_map_nonneg L).mp hL
  let b : UnitIntervalContinuousMap := ε • 1 + c • unitIntervalQuadratic x
  let g : UnitIntervalContinuousMap := f - (f x) • 1
  have hgy : ∀ y, g y = f y - f x := by
    intro y
    simp [g, ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
      smul_eq_mul, mul_one]
  have hby : ∀ y, b y = ε + c * (y.1 - x.1) ^ 2 := by
    intro y
    simp [b, unitIntervalQuadratic_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul, mul_one]
  have hg_le : g ≤ b := by
    rw [ContinuousMap.le_def]
    intro y
    rw [hgy, hby]
    exact (abs_le.mp (abs_sub_le_quadratic f hε hδ hf x y)).2
  have hge : -b ≤ g := by
    rw [ContinuousMap.le_def]
    intro y
    rw [ContinuousMap.neg_apply, hgy, hby]
    exact (abs_le.mp (abs_sub_le_quadratic f hε hδ hf x y)).1
  have hup : L g ≤ L b := hL hg_le
  have hlo : -(L b) ≤ L g := by simpa [L.map_neg] using hL hge
  have habs : |(L g) x| ≤ (L b) x := by
    rw [abs_le]
    refine ⟨?_, (ContinuousMap.le_def.mp hup) x⟩
    simpa [ContinuousMap.neg_apply] using (ContinuousMap.le_def.mp hlo) x
  have hLg : (L g) x = (L f) x - f x * (L 1) x := by
    simp [g, L.map_sub, L.map_smul, ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul]
  have hLb : (L b) x = ε * (L 1) x + c * korovkinDeviation L x := by
    simp [b, L.map_add, L.map_smul, ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul,
      eval_unitIntervalQuadratic]
  have h1x : (L 1) x ≤ ‖L 1‖ := by
    have hnn : 0 ≤ (L 1) x :=
      (ContinuousMap.le_def.mp (hpos 1 one_nonneg_unitInterval)) x
    rw [← abs_of_nonneg hnn]
    simpa [Real.norm_eq_abs] using (L 1).norm_coe_le_norm x
  have hdevx : korovkinDeviation L x ≤ ‖korovkinDeviation L‖ := by
    have hnn : 0 ≤ korovkinDeviation L x := by
      rw [← eval_unitIntervalQuadratic L x]
      exact (ContinuousMap.le_def.mp (hpos _ (unitIntervalQuadratic_nonneg x))) x
    rw [← abs_of_nonneg hnn]
    simpa [Real.norm_eq_abs] using (korovkinDeviation L).norm_coe_le_norm x
  have hfx : |f x| ≤ ‖f‖ := by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x
  have hsubx : |(L 1) x - 1| ≤ ‖L 1 - 1‖ := by
    simpa [ContinuousMap.sub_apply, Real.norm_eq_abs] using (L 1 - 1).norm_coe_le_norm x
  calc
    |(L f) x - f x| = |(L g) x + f x * ((L 1) x - 1)| := by
      rw [hLg]
      congr 1
      ring
    _ ≤ |(L g) x| + |f x * ((L 1) x - 1)| := abs_add_le _ _
    _ = |(L g) x| + |f x| * |(L 1) x - 1| := by rw [abs_mul]
    _ ≤ (L b) x + ‖f‖ * ‖L 1 - 1‖ :=
      add_le_add habs (mul_le_mul hfx hsubx (abs_nonneg _) (norm_nonneg _))
    _ ≤ ε * ‖L 1‖ + c * ‖korovkinDeviation L‖ + ‖f‖ * ‖L 1 - 1‖ := by
      rw [hLb]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left h1x hε)
        (mul_le_mul_of_nonneg_left hdevx hc)) le_rfl

private lemma norm_sub_le_korovkin (L : UnitIntervalContinuousMap →L[ℝ] UnitIntervalContinuousMap)
    (hL : Monotone L) (f : UnitIntervalContinuousMap) {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hf : ∀ {x y : Set.Icc (0 : ℝ) 1}, dist x y < δ → dist (f x) (f y) < ε) :
    ‖L f - f‖ ≤ ε * ‖L 1‖ + (2 * ‖f‖ / δ ^ 2) * ‖korovkinDeviation L‖ +
      ‖f‖ * ‖L 1 - 1‖ := by
  have hC : 0 ≤ ε * ‖L 1‖ + (2 * ‖f‖ / δ ^ 2) * ‖korovkinDeviation L‖ + ‖f‖ * ‖L 1 - 1‖ := by
    positivity
  rw [(L f - f).norm_le hC]
  intro x
  simpa [ContinuousMap.sub_apply, Real.norm_eq_abs] using abs_eval_sub_le L hL f hε hδ hf x

/-- **47.17**: the three Korovkin test functions characterize strong convergence. -/
theorem korovkin_iff (L : ℕ → UnitIntervalContinuousMap →L[ℝ]
    UnitIntervalContinuousMap) (hL : ∀ n, Monotone (L n)) :
    (∀ f, Tendsto (fun n ↦ L n f) atTop (𝓝 f)) ↔
      Tendsto (fun n ↦ L n 1) atTop (𝓝 1) ∧
      Tendsto (fun n ↦ L n unitIntervalId) atTop (𝓝 unitIntervalId) ∧
      Tendsto (fun n ↦ L n (unitIntervalId ^ 2)) atTop (𝓝 (unitIntervalId ^ 2)) := by
  constructor
  · intro h
    exact ⟨h 1, h unitIntervalId, h (unitIntervalId ^ 2)⟩
  · rintro ⟨h1, hid, hid2⟩ f
    rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_atTop]
    intro η hη
    have hεpos : 0 < η / 4 := div_pos hη (by norm_num)
    obtain ⟨δ, hδpos, hδ⟩ := f.uniform_continuity (η / 4) hεpos
    have hdev : Tendsto (fun n ↦ ‖korovkinDeviation (L n)‖) atTop (𝓝 0) := by
      simpa using (korovkinDeviation_tendsto_zero L h1 hid hid2).norm
    have hnorm1 : Tendsto (fun n ↦ ‖L n 1‖) atTop (𝓝 1) := by simpa using h1.norm
    have hsub1 : Tendsto (fun n ↦ ‖L n 1 - 1‖) atTop (𝓝 0) := by
      simpa using (h1.sub (tendsto_const_nhds (x := (1 : UnitIntervalContinuousMap)))).norm
    rw [← eventually_atTop]
    have hA : ∀ᶠ n in atTop, (η / 4) * ‖L n 1‖ < η / 2 :=
      (Tendsto.const_mul (η / 4) hnorm1).eventually_lt
        (tendsto_const_nhds (x := η / 2)) (by rw [mul_one]; linarith)
    have hB : ∀ᶠ n in atTop, (2 * ‖f‖ / δ ^ 2) * ‖korovkinDeviation (L n)‖ < η / 4 :=
      (Tendsto.const_mul (2 * ‖f‖ / δ ^ 2) hdev).eventually_lt
        (tendsto_const_nhds (x := η / 4)) (by simpa [mul_zero] using hεpos)
    have hC : ∀ᶠ n in atTop, ‖f‖ * ‖L n 1 - 1‖ < η / 4 :=
      (Tendsto.const_mul ‖f‖ hsub1).eventually_lt
        (tendsto_const_nhds (x := η / 4)) (by simpa [mul_zero] using hεpos)
    filter_upwards [hA, hB, hC] with n hnA hnB hnC
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    calc
      ‖L n f - f‖ ≤ (η / 4) * ‖L n 1‖ + (2 * ‖f‖ / δ ^ 2) * ‖korovkinDeviation (L n)‖ +
          ‖f‖ * ‖L n 1 - 1‖ :=
        norm_sub_le_korovkin (L n) (hL n) f hεpos.le hδpos hδ
      _ < η / 2 + η / 4 + η / 4 := add_lt_add (add_lt_add hnA hnB) hnC
      _ = η := by ring

end CKMA
