/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.RectangularDifferentiation.Base

import Mathlib.MeasureTheory.Integral.Layercake
import CKMA.Analysis.Real.RectangularDifferentiation.Endpoint

/-!
# One iteration of the strong maximal inequality

Fubini and the one-dimensional weak-type bound control the distribution of the strong maximal
function in dimension `n + 1` by the truncated strong maximal function of the slices. The
logarithmic kernel turns that distribution into the endpoint growth of order `n + 1`.

## Main results

* `CKMA.strongMaximal_endpoint`: the Jessen–Marcinkiewicz–Zygmund endpoint weak-type bound
  `|{M f > a}| ≤ C ∫ Φ_d(|f| / a)` with `Φ_d(u) = u (1 + log⁺ u)^(d-1)`, in every dimension `d`
  (in dimension `0` with `C = 1`, in dimension `1` with `C = 5`).

## Implementation notes

The proof is by induction on the dimension. The inductive step, from dimension `n` to `n + 1`
with constant `10 C (2 (1 + log 4)^n)`, combines the truncated slice bound
`CKMA.strongMaximal_volume_le_truncIntegral` with a layer-cake computation and the kernel
inequality `CKMA.strongMaximalGrowth_scaled_kernel`.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Set StrongMaximal
open scoped ENNReal intervalIntegral

/-- A nonnegative extended number bounded by every positive real is zero. -/
private theorem eq_zero_of_forall_le_ofReal {c : ℝ≥0∞}
    (h : ∀ ε : ℝ, 0 < ε → c ≤ ENNReal.ofReal ε) : c = 0 := by
  by_cases htop : c = ∞
  · have hle := h 1 one_pos
    rw [htop] at hle
    exact absurd hle (not_le_of_gt ENNReal.ofReal_lt_top)
  · by_cases h0 : c = 0
    · exact h0
    · have hpos : 0 < c.toReal := ENNReal.toReal_pos h0 htop
      set r : ℝ := c.toReal
      have hle := h (r / 2) (by linarith)
      have hc : c = ENNReal.ofReal r := (ENNReal.ofReal_toReal htop).symm
      rw [hc] at hle
      have : r ≤ r / 2 :=
        (ENNReal.ofReal_le_ofReal_iff (by linarith : (0 : ℝ) ≤ r / 2)).1 hle
      linarith

/-- The endpoint growth is nonnegative on the nonnegative reals. -/
theorem strongMaximalGrowth_nonneg {d : ℕ} {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ strongMaximalGrowth d u :=
  le_trans hu (strongMaximalGrowth_ge_self hu)

/-- Passing from height `k` back to height `a` costs a single logarithm. -/
private theorem strongMaximalGrowth_height_le {n k : ℕ} (hk : 1 ≤ k) {a v : ℝ} (ha : 0 < a)
    (hv : 0 ≤ v) :
    strongMaximalGrowth n (v / k) ≤
      (a / (k : ℝ)) * (1 + |Real.log a|) ^ (n - 1) *
        strongMaximalGrowth (n + 1) (v / a) := by
  have hdiv := strongMaximalGrowth_div_le (n := n) hk hv
  have hsmul := strongMaximalGrowth_smul_le (n := n) ha (div_nonneg hv ha.le)
  have hprod : a * (v / a) = v := by field_simp [ha.ne']
  rw [hprod] at hsmul
  calc
    strongMaximalGrowth n (v / k) ≤ (1 / (k : ℝ)) * strongMaximalGrowth n v := hdiv
    _ ≤ (1 / (k : ℝ)) * (a * (1 + |Real.log a|) ^ (n - 1) *
          strongMaximalGrowth (n + 1) (v / a)) :=
      mul_le_mul_of_nonneg_left hsmul (by positivity)
    _ = (a / (k : ℝ)) * (1 + |Real.log a|) ^ (n - 1) *
          strongMaximalGrowth (n + 1) (v / a) := by ring

/-- The ratio `2v / t` is continuous on a compact interval bounded away from zero, so the endpoint
growth in that ratio is continuous. -/
private theorem continuousOn_strongMaximalGrowth_ratio {n : ℕ} {v c d : ℝ} (hc : 0 < c) :
    ContinuousOn (fun t ↦ strongMaximalGrowth n (2 * v / t)) (Icc c d) := by
  have hratio : ContinuousOn (fun t : ℝ ↦ 2 * v / t) (Icc c d) :=
    (continuous_const.continuousOn).div continuous_id.continuousOn fun t ht ↦
      (lt_of_lt_of_le hc ht.1).ne'
  rw [funext fun t ↦ strongMaximalGrowth_def n (2 * v / t)]
  exact hratio.mul ((continuousOn_const.add
    (Real.continuous_posLog.comp_continuousOn hratio)).pow _)

/-- The partial maximal function, replaced by zero at infinity and on the half-height set. -/
private def truncatedPartialReal {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (a : ℝ)
    (p : ℝ × (Fin n → ℝ)) : ℝ :=
  if partialStrongMax f p.1 p.2 = ∞ then 0
  else if ENNReal.ofReal (a / 2) < partialStrongMax f p.1 p.2 then
    (partialStrongMax f p.1 p.2).toReal else 0

/-- The real truncation of the partial maximal function is measurable. -/
private theorem measurable_truncatedPartialReal {n : ℕ} (hn : 0 < n)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) (a : ℝ) :
    Measurable (truncatedPartialReal f a) := by
  have hT : Measurable fun p : ℝ × (Fin n → ℝ) ↦ partialStrongMax f p.1 p.2 :=
    measurable_partialStrongMax hn hf
  unfold truncatedPartialReal
  refine Measurable.ite (hT (measurableSet_singleton ∞)) measurable_const ?_
  exact Measurable.ite (measurableSet_lt measurable_const hT)
    (ENNReal.measurable_toReal.comp hT) measurable_const

/-- A finite Orlicz integral of order `n + 1` forces the partial maximal function to be finite
almost everywhere. -/
private theorem partialStrongMax_top_null {n : ℕ} (hn : 1 ≤ n) {C : ℝ} (hC : 0 < C)
    (hIH : HasStrongMaximalOrliczBound n C)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) {a : ℝ} (ha : 0 < a)
    (hI : ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth (n + 1) (|f x| / a)) ≠ ∞) :
    volume {p : ℝ × (Fin n → ℝ) | partialStrongMax f p.1 p.2 = ∞} = 0 := by
  set I : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth (n + 1) (|f x| / a))
  set L : ℝ := (1 + |Real.log a|) ^ (n - 1)
  refine eq_zero_of_forall_le_ofReal fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := exists_nat_gt (max (1 : ℝ) (C * a * L * I.toReal / ε))
  have hk1 : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hk0 : (0 : ℝ) < k := one_pos.trans hk1
  have hc : 0 ≤ a / k * L := by positivity
  have hgrow : ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth n (|f x| / k)) ≤
      ENNReal.ofReal (a / k * L) * I := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x ↦ ?_
    rw [← ENNReal.ofReal_mul hc]
    exact ENNReal.ofReal_le_ofReal
      (strongMaximalGrowth_height_le (Nat.one_le_cast.mp hk1.le) ha (abs_nonneg (f x)))
  have hsmall : C * (a / k * L) * I.toReal ≤ ε := by
    have h := (div_lt_iff₀ hε).1 ((le_max_right _ _).trans_lt hk)
    rw [show C * (a / k * L) * I.toReal = C * a * L * I.toReal / k by ring, div_le_iff₀ hk0]
    linarith
  calc
    _ ≤ volume {p : ℝ × (Fin n → ℝ) | ENNReal.ofReal k < partialStrongMax f p.1 p.2} :=
      measure_mono fun p hp ↦ by
        simp only [mem_ofPred_eq] at hp ⊢
        rw [hp]
        exact ENNReal.ofReal_lt_top
    _ ≤ ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth n (|f x| / k)) :=
      volume_partialStrongMax_gt_le hn hIH hf hk0
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (a / k * L) * I) := by gcongr
    _ = ENNReal.ofReal (C * (a / k * L) * I.toReal) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hC.le hc), ENNReal.ofReal_toReal hI,
        ENNReal.ofReal_mul hC.le, mul_assoc]
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hsmall

/-- Off the null set where a slice maximal function is infinite, truncation does not change the
integral. -/
private theorem lintegral_truncatedPartial_eq {n : ℕ} (hn : 0 < n)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) {a : ℝ}
    (hnull : volume {p : ℝ × (Fin n → ℝ) | partialStrongMax f p.1 p.2 = ∞} = 0) :
    ∫⁻ p : ℝ × (Fin n → ℝ), truncatedPartial f a p.1 p.2 =
      ∫⁻ p : ℝ × (Fin n → ℝ), ENNReal.ofReal (truncatedPartialReal f a p) := by
  let N : Set (ℝ × (Fin n → ℝ)) := {p | partialStrongMax f p.1 p.2 = ∞}
  have hT : Measurable fun p : ℝ × (Fin n → ℝ) ↦ partialStrongMax f p.1 p.2 :=
    measurable_partialStrongMax hn hf
  have hN : MeasurableSet N := hT (measurableSet_singleton ∞)
  have hzero : ∫⁻ p in N, truncatedPartial f a p.1 p.2 = 0 :=
    setLIntegral_measure_zero _ _ hnull
  have hzero' : ∫⁻ p in N, ENNReal.ofReal (truncatedPartialReal f a p) = 0 :=
    setLIntegral_measure_zero _ _ hnull
  have hagree : ∫⁻ p in Nᶜ, truncatedPartial f a p.1 p.2 =
      ∫⁻ p in Nᶜ, ENNReal.ofReal (truncatedPartialReal f a p) := by
    refine setLIntegral_congr_fun hN.compl fun p hp ↦ ?_
    have hfin : partialStrongMax f p.1 p.2 ≠ ∞ := by
      simpa [N, mem_compl_iff, mem_ofPred_eq] using hp
    by_cases hgt : ENNReal.ofReal (a / 2) < partialStrongMax f p.1 p.2
    · have hL : truncatedPartial f a p.1 p.2 = partialStrongMax f p.1 p.2 := by
        unfold truncatedPartial
        rw [ite_eq_left hgt]
      have hR : truncatedPartialReal f a p = (partialStrongMax f p.1 p.2).toReal := by
        unfold truncatedPartialReal
        rw [ite_eq_right hfin, ite_eq_left hgt]
      rw [hL, hR]
      exact (ENNReal.ofReal_toReal hfin).symm
    · have hL : truncatedPartial f a p.1 p.2 = 0 := by
        unfold truncatedPartial
        rw [ite_eq_right hgt]
      have hnot : partialStrongMax f p.1 p.2 ≠ ∞ := by
        intro hinf
        have hgt' := hgt
        rw [hinf] at hgt'
        exact hgt' ENNReal.ofReal_lt_top
      have hR : truncatedPartialReal f a p = 0 := by
        unfold truncatedPartialReal
        rw [ite_eq_right hnot, ite_eq_right hgt]
      rw [hL, hR]
      exact ENNReal.ofReal_zero.symm
  calc
    ∫⁻ p : ℝ × (Fin n → ℝ), truncatedPartial f a p.1 p.2 =
        (∫⁻ p : ℝ × (Fin n → ℝ) in N, truncatedPartial f a p.1 p.2) +
          (∫⁻ p : ℝ × (Fin n → ℝ) in Nᶜ, truncatedPartial f a p.1 p.2) := by
      symm
      exact lintegral_add_compl _ hN
    _ = ∫⁻ p : ℝ × (Fin n → ℝ) in Nᶜ, ENNReal.ofReal (truncatedPartialReal f a p) := by
      rw [hzero, zero_add, hagree]
    _ = (∫⁻ p : ℝ × (Fin n → ℝ) in N, ENNReal.ofReal (truncatedPartialReal f a p)) +
          (∫⁻ p : ℝ × (Fin n → ℝ) in Nᶜ,
            ENNReal.ofReal (truncatedPartialReal f a p)) := by
      rw [hzero', zero_add]
    _ = ∫⁻ p : ℝ × (Fin n → ℝ), ENNReal.ofReal (truncatedPartialReal f a p) :=
      lintegral_add_compl _ hN

/-- The tail integral in the last coordinate is at most the logarithmic kernel. -/
private theorem slice_tail_integral_le {n : ℕ} {a v : ℝ} (ha : 0 < a) (hv : 0 ≤ v) :
    ∫⁻ t : ℝ, (if a / 2 < t ∧ t / 2 < v then
        ENNReal.ofReal (strongMaximalGrowth n (2 * v / t)) else 0) ≤
      ENNReal.ofReal (if v ≤ a / 4 then 0 else
        ∫ t in (a / 2)..(2 * v), strongMaximalGrowth n (2 * v / t)) := by
  have hφ : (fun t : ℝ ↦ if a / 2 < t ∧ t / 2 < v then
      ENNReal.ofReal (strongMaximalGrowth n (2 * v / t)) else 0) =
      (Ioo (a / 2) (2 * v)).indicator
        fun t ↦ ENNReal.ofReal (strongMaximalGrowth n (2 * v / t)) := by
    funext t
    simp only [indicator_apply, mem_Ioo, show t / 2 < v ↔ t < 2 * v by
      constructor <;> intro h <;> linarith]
  rw [hφ, lintegral_indicator measurableSet_Ioo, setLIntegral_congr Ioo_ae_eq_Ioc]
  split_ifs with hv4
  · rw [Ioc_eq_empty (by linarith), Measure.restrict_empty, lintegral_zero_measure,
      ENNReal.ofReal_zero]
  have h2v : a / 2 < 2 * v := by linarith
  have hint : IntegrableOn (fun t ↦ strongMaximalGrowth n (2 * v / t))
      (Ioc (a / 2) (2 * v)) volume :=
    ((continuousOn_strongMaximalGrowth_ratio (div_pos ha (by norm_num : (0 : ℝ) < 2))
      ).intervalIntegrable_of_Icc h2v.le).1
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (a / 2) (2 * v))]
      fun t ↦ strongMaximalGrowth n (2 * v / t) :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦
      strongMaximalGrowth_nonneg (div_nonneg (by positivity) (by linarith [ht.1]))
  rw [intervalIntegral.integral_of_le h2v.le, ofReal_integral_eq_lintegral_ofReal hint hnn]

/-- The scaled kernel, written with extended nonnegative values. -/
private theorem iteration_ofReal_le {n : ℕ} (hn : 1 ≤ n) {a v : ℝ} (ha : 0 < a) (hv : 0 ≤ v) :
    ENNReal.ofReal ((a / 2) * strongMaximalGrowth n (2 * v / a)) +
      ENNReal.ofReal (if v ≤ a / 4 then 0 else
        ∫ t in (a / 2)..(2 * v), strongMaximalGrowth n (2 * v / t)) ≤
      ENNReal.ofReal (a * strongMaximalIterationFactor n *
        strongMaximalGrowth (n + 1) (v / a)) := by
  have hhead : 0 ≤ (a / 2) * strongMaximalGrowth n (2 * v / a) :=
    mul_nonneg (div_nonneg ha.le (by norm_num))
      (strongMaximalGrowth_nonneg (div_nonneg (mul_nonneg (by norm_num) hv) ha.le))
  have htail : 0 ≤ (if v ≤ a / 4 then (0 : ℝ) else
      ∫ t in (a / 2)..(2 * v), strongMaximalGrowth n (2 * v / t)) := by
    split_ifs with hv4
    · exact le_rfl
    · have h2v : a / 2 ≤ 2 * v := by linarith
      exact intervalIntegral.integral_nonneg h2v fun t ht ↦
        strongMaximalGrowth_nonneg (div_nonneg
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hv)
          (le_trans (div_nonneg ha.le (by norm_num)) ht.1))
  rw [← ENNReal.ofReal_add hhead htail]
  exact ENNReal.ofReal_le_ofReal (strongMaximal_iteration_scale hn ha hv)

/-- The truncated slice maximal function exceeds a level `t ≤ a / 2` only where the slice maximal
function exceeds `a / 2`, so the head of its layer-cake integral is controlled by the
lower-dimensional inequality. -/
private theorem setLIntegral_Ioc_volume_lt_truncatedPartialReal_le {n : ℕ} (hn : 1 ≤ n) {C : ℝ}
    (hIH : HasStrongMaximalOrliczBound n C)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) {a : ℝ} (ha : 0 < a) :
    ∫⁻ t in Ioc (0 : ℝ) (a / 2), volume {p | t < truncatedPartialReal f a p} ≤
      ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
        ((a / 2) * strongMaximalGrowth n (2 * |f x| / a)) := by
  have hhalf : 0 < a / 2 := div_pos ha (by norm_num)
  let H : ℝ≥0∞ := volume
    {p : ℝ × (Fin n → ℝ) | ENNReal.ofReal (a / 2) < partialStrongMax f p.1 p.2}
  have hhead_le : ∫⁻ t in Ioc (0 : ℝ) (a / 2),
      volume {p | t < truncatedPartialReal f a p} ≤ H * ENNReal.ofReal (a / 2) := by
    have hpt : ∀ t ∈ Ioc (0 : ℝ) (a / 2),
        volume {p | t < truncatedPartialReal f a p} ≤ H := by
      intro t ht
      refine measure_mono fun p hp ↦ ?_
      simp only [mem_ofPred_eq] at hp ⊢
      unfold truncatedPartialReal at hp
      split_ifs at hp with hinf hgt
      · exact absurd hp (not_lt.mpr (le_of_lt ht.1))
      · exact hgt
      · exact absurd hp (not_lt.mpr (le_of_lt ht.1))
    calc
      ∫⁻ t in Ioc (0 : ℝ) (a / 2), volume {p | t < truncatedPartialReal f a p} ≤
          ∫⁻ t in Ioc (0 : ℝ) (a / 2), H :=
        setLIntegral_mono' measurableSet_Ioc hpt
      _ = H * volume (Ioc (0 : ℝ) (a / 2)) := setLIntegral_const _ _
      _ = H * ENNReal.ofReal (a / 2) := by
        rw [Real.volume_Ioc]
        congr 1
        ring_nf
  have hquot : ∀ x, |f x| / (a / 2) = 2 * |f x| / a := by
    intro x
    field_simp [ha.ne']
  have hH : H ≤ ENNReal.ofReal C *
      ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth n (2 * |f x| / a)) := by
    simpa [hquot] using volume_partialStrongMax_gt_le hn hIH hf hhalf
  calc
    _ ≤ H * ENNReal.ofReal (a / 2) := hhead_le
    _ ≤ (ENNReal.ofReal C *
          ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth n (2 * |f x| / a))) *
          ENNReal.ofReal (a / 2) := mul_le_mul' hH le_rfl
    _ = ENNReal.ofReal C * (ENNReal.ofReal (a / 2) *
        ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth n (2 * |f x| / a))) := by
      rw [mul_assoc]
      congr 1
      exact mul_comm _ _
    _ = ENNReal.ofReal C * ∫⁻ x,
        ENNReal.ofReal ((a / 2) * strongMaximalGrowth n (2 * |f x| / a)) := by
      congr 1
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun x ↦ ?_
      exact (ENNReal.ofReal_mul hhalf.le).symm

/-- Above height `a / 2`, each level set of the truncated slice maximal function is controlled
by the lower-dimensional inequality applied to the half-level truncation of `f`. -/
private theorem volume_lt_truncatedPartialReal_le {n : ℕ} (hn : 1 ≤ n) {C : ℝ}
    (hIH : HasStrongMaximalOrliczBound n C)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) {a : ℝ} (ha : 0 < a) {t : ℝ}
    (ht : a / 2 < t) :
    volume {p | t < truncatedPartialReal f a p} ≤
      ENNReal.ofReal C * ∫⁻ x, (if a / 2 < t ∧ t / 2 < |f x| then
        ENNReal.ofReal (strongMaximalGrowth n (2 * |f x| / t)) else 0) := by
  have hhalf : 0 < a / 2 := div_pos ha (by norm_num)
  refine le_trans (measure_mono ?_) ((volume_partialStrongMax_gt_le_trunc hn hIH hf
    (lt_trans hhalf ht)).trans ?_)
  · intro p hp
    simp only [mem_ofPred_eq] at hp ⊢
    unfold truncatedPartialReal at hp
    split_ifs at hp with hinf hgt
    · exact absurd hp (not_lt.mpr (le_trans hhalf.le ht.le))
    · have hto : t < (partialStrongMax f p.1 p.2).toReal := hp
      have hfin : partialStrongMax f p.1 p.2 ≠ ∞ := hinf
      rw [← ENNReal.ofReal_toReal hfin]
      exact ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < (partialStrongMax f p.1 p.2).toReal)
        |>.2 hto
    · exact absurd hp (not_lt.mpr (le_trans hhalf.le ht.le))
  · refine mul_le_mul' le_rfl ?_
    refine lintegral_mono fun x ↦ ?_
    by_cases hx : t / 2 < |f x|
    · have habs : |halfLevelTrunc t f x| = |f x| := by
        unfold halfLevelTrunc
        rw [ite_eq_left hx]
      have hdiv : |halfLevelTrunc t f x| / (t / 2) = 2 * |f x| / t := by
        rw [habs]
        field_simp [show t ≠ 0 by linarith]
      rw [hdiv, ite_eq_left ⟨ht, hx⟩]
    · have hzero : halfLevelTrunc t f x = 0 := by
        unfold halfLevelTrunc
        rw [ite_eq_right hx]
      have hnot : ¬ (a / 2 < t ∧ t / 2 < |f x|) := fun h ↦ hx h.2
      rw [hzero, ite_eq_right hnot]
      simp [strongMaximalGrowth_def]

/-- The tail of the layer-cake integral of the truncated slice maximal function, above height
`a / 2`, is controlled by the logarithmic tail kernel. -/
private theorem setLIntegral_Ioi_volume_lt_truncatedPartialReal_le {n : ℕ} (hn : 1 ≤ n)
    {C : ℝ}
    (hIH : HasStrongMaximalOrliczBound n C)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) {a : ℝ} (ha : 0 < a) :
    ∫⁻ t in Ioi (a / 2), volume {p | t < truncatedPartialReal f a p} ≤
      ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
        (if |f x| ≤ a / 4 then 0 else
          ∫ s in (a / 2)..(2 * |f x|), strongMaximalGrowth n (2 * |f x| / s)) := by
  let tailφ : ℝ → (Fin (n + 1) → ℝ) → ℝ≥0∞ := fun t x ↦
    if a / 2 < t ∧ t / 2 < |f x| then
      ENNReal.ofReal (strongMaximalGrowth n (2 * |f x| / t)) else 0
  have htail_meas : Measurable fun p : ℝ × (Fin (n + 1) → ℝ) ↦ tailφ p.1 p.2 := by
    have habs : Measurable fun p : ℝ × (Fin (n + 1) → ℝ) ↦ |f p.2| :=
      continuous_abs.measurable.comp (hf.comp measurable_snd)
    have hset : MeasurableSet {p : ℝ × (Fin (n + 1) → ℝ) |
        a / 2 < p.1 ∧ p.1 / 2 < |f p.2|} :=
      MeasurableSet.inter (measurableSet_lt measurable_const measurable_fst)
        (measurableSet_lt (measurable_fst.div_const 2) habs)
    have hfun : Measurable fun p : ℝ × (Fin (n + 1) → ℝ) ↦
        ENNReal.ofReal (strongMaximalGrowth n (2 * |f p.2| / p.1)) :=
      ENNReal.measurable_ofReal.comp ((measurable_strongMaximalGrowth n).comp
        ((measurable_const.mul habs).div measurable_fst))
    simpa [tailφ] using hfun.ite hset measurable_const
  have hpt : ∫⁻ t in Ioi (a / 2), volume {p | t < truncatedPartialReal f a p} ≤
      ∫⁻ t in Ioi (a / 2), ENNReal.ofReal C * ∫⁻ x, tailφ t x :=
    setLIntegral_mono' measurableSet_Ioi fun t ht ↦
      volume_lt_truncatedPartialReal_le hn hIH hf ha ht
  have hcompl : ∫⁻ t in (Ioi (a / 2))ᶜ, ENNReal.ofReal C * ∫⁻ x, tailφ t x = 0 := by
    refine setLIntegral_eq_zero measurableSet_Ioi.compl fun t ht ↦ ?_
    have ht' : ¬ a / 2 < t := by simpa [mem_compl_iff, mem_Ioi] using ht
    have hfun : (fun x ↦ tailφ t x) = fun _ ↦ 0 := by
      funext x
      unfold tailφ
      split_ifs with hcond
      · exact absurd hcond.1 ht'
      · rfl
    rw [hfun]
    simp
  have hfull : ∫⁻ t in Ioi (a / 2), ENNReal.ofReal C * ∫⁻ x, tailφ t x =
      ∫⁻ t, ENNReal.ofReal C * ∫⁻ x, tailφ t x := by
    have hadd := lintegral_add_compl (μ := volume)
      (fun t : ℝ ↦ ENNReal.ofReal C * ∫⁻ x, tailφ t x)
      (measurableSet_Ioi (a := a / 2))
    rw [hcompl, add_zero] at hadd
    exact hadd
  have hpull : ∫⁻ t, ENNReal.ofReal C * ∫⁻ x, tailφ t x =
      ENNReal.ofReal C * ∫⁻ t, ∫⁻ x, tailφ t x :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hswap : ∫⁻ t, ∫⁻ x, tailφ t x = ∫⁻ x, ∫⁻ t, tailφ t x :=
    lintegral_lintegral_swap htail_meas.aemeasurable
  have hpoint : ∀ x, ∫⁻ t, tailφ t x ≤ ENNReal.ofReal
      (if |f x| ≤ a / 4 then 0 else
        ∫ s in (a / 2)..(2 * |f x|), strongMaximalGrowth n (2 * |f x| / s)) :=
    fun x ↦ by simpa [tailφ] using slice_tail_integral_le (n := n) ha (abs_nonneg (f x))
  calc
    ∫⁻ t in Ioi (a / 2), volume {p | t < truncatedPartialReal f a p} ≤
        ∫⁻ t in Ioi (a / 2), ENNReal.ofReal C * ∫⁻ x, tailφ t x := hpt
    _ = ENNReal.ofReal C * ∫⁻ x, ∫⁻ t, tailφ t x := by rw [hfull, hpull, hswap]
    _ ≤ ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
        (if |f x| ≤ a / 4 then 0 else
          ∫ s in (a / 2)..(2 * |f x|),
            strongMaximalGrowth n (2 * |f x| / s)) :=
      mul_le_mul' le_rfl (lintegral_mono hpoint)

/-- The head and tail kernels together integrate to at most `a` times the iteration factor times
the Orlicz integral of order `n + 1`. -/
private theorem lintegral_head_add_lintegral_tail_le {n : ℕ} (hn : 1 ≤ n)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) {a : ℝ} (ha : 0 < a) :
    (∫⁻ x, ENNReal.ofReal ((a / 2) * strongMaximalGrowth n (2 * |f x| / a))) +
        (∫⁻ x, ENNReal.ofReal (if |f x| ≤ a / 4 then 0 else
          ∫ s in (a / 2)..(2 * |f x|), strongMaximalGrowth n (2 * |f x| / s))) ≤
      ENNReal.ofReal (a * strongMaximalIterationFactor n) *
        ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth (n + 1) (|f x| / a)) := by
  have hhead_fun : Measurable fun x ↦
      ENNReal.ofReal ((a / 2) * strongMaximalGrowth n (2 * |f x| / a)) := by
    have habs : Measurable fun x ↦ |f x| := continuous_abs.measurable.comp hf
    refine ENNReal.measurable_ofReal.comp (measurable_const.mul ?_)
    exact (measurable_strongMaximalGrowth n).comp
      ((measurable_const.mul habs).div_const a)
  have hfactor : 0 ≤ a * strongMaximalIterationFactor n :=
    mul_nonneg ha.le (strongMaximalIterationFactor_pos n).le
  rw [← lintegral_add_left hhead_fun]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (a * strongMaximalIterationFactor n *
        strongMaximalGrowth (n + 1) (|f x| / a)) :=
      lintegral_mono fun x ↦ iteration_ofReal_le hn ha (abs_nonneg (f x))
    _ = ∫⁻ x, ENNReal.ofReal (a * strongMaximalIterationFactor n) *
        ENNReal.ofReal (strongMaximalGrowth (n + 1) (|f x| / a)) := by
      refine lintegral_congr fun x ↦ ?_
      exact ENNReal.ofReal_mul hfactor
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The integral of the truncated slice maximal function is bounded by the Orlicz integral of
order `n + 1`, splitting its layer-cake representation at height `a / 2`. -/
private theorem lintegral_truncatedPartialReal_le {n : ℕ} (hn : 1 ≤ n) {C : ℝ} (hC : 0 < C)
    (hIH : HasStrongMaximalOrliczBound n C)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) {a : ℝ} (ha : 0 < a) :
    ∫⁻ p, ENNReal.ofReal (truncatedPartialReal f a p) ≤
      ENNReal.ofReal (C * a * strongMaximalIterationFactor n) *
        ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth (n + 1) (|f x| / a)) := by
  have hn0 : 0 < n := by omega
  have hreal : Measurable (truncatedPartialReal f a) :=
    measurable_truncatedPartialReal hn0 hf a
  have hnn : 0 ≤ᵐ[volume] truncatedPartialReal f a :=
    ae_of_all volume fun p ↦ by
      unfold truncatedPartialReal
      split_ifs <;> first | exact le_rfl | exact ENNReal.toReal_nonneg
  have hcake := lintegral_eq_lintegral_meas_lt (μ := volume) hnn hreal.aemeasurable
  have hhalf : 0 < a / 2 := div_pos ha (by norm_num)
  have hcap : Ioi (0 : ℝ) ∩ Ioc 0 (a / 2) = Ioc 0 (a / 2) :=
    inter_eq_self_of_subset_right fun _ ht ↦ ht.1
  have hrest : Ioi (0 : ℝ) \ Ioc 0 (a / 2) = Ioi (a / 2) := by
    ext t
    constructor
    · rintro ⟨ht0, hnot⟩
      exact lt_of_not_ge fun hle ↦ hnot ⟨ht0, hle⟩
    · intro ht
      exact ⟨lt_trans hhalf ht, fun hmem ↦ not_le_of_gt ht hmem.2⟩
  have hsplit := (lintegral_inter_add_sdiff (μ := volume)
    (fun t ↦ volume {p | t < truncatedPartialReal f a p}) (Ioi (0 : ℝ))
    (measurableSet_Ioc (a := (0 : ℝ)) (b := a / 2))).symm
  calc
    ∫⁻ p, ENNReal.ofReal (truncatedPartialReal f a p) =
        (∫⁻ t in Ioc (0 : ℝ) (a / 2), volume {p | t < truncatedPartialReal f a p}) +
          (∫⁻ t in Ioi (a / 2), volume {p | t < truncatedPartialReal f a p}) := by
      rw [hcake, hsplit, hcap, hrest]
    _ ≤ (ENNReal.ofReal C *
          ∫⁻ x, ENNReal.ofReal ((a / 2) * strongMaximalGrowth n (2 * |f x| / a))) +
        (ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (if |f x| ≤ a / 4 then 0 else
          ∫ s in (a / 2)..(2 * |f x|), strongMaximalGrowth n (2 * |f x| / s))) :=
      add_le_add (setLIntegral_Ioc_volume_lt_truncatedPartialReal_le hn hIH hf ha)
        (setLIntegral_Ioi_volume_lt_truncatedPartialReal_le hn hIH hf ha)
    _ = ENNReal.ofReal C *
        ((∫⁻ x, ENNReal.ofReal ((a / 2) * strongMaximalGrowth n (2 * |f x| / a))) +
          (∫⁻ x, ENNReal.ofReal (if |f x| ≤ a / 4 then 0 else
            ∫ s in (a / 2)..(2 * |f x|),
              strongMaximalGrowth n (2 * |f x| / s)))) := by
      rw [mul_add]
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (a * strongMaximalIterationFactor n) *
          ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth (n + 1) (|f x| / a))) :=
      mul_le_mul' le_rfl (lintegral_head_add_lintegral_tail_le hn hf ha)
    _ = ENNReal.ofReal (C * a * strongMaximalIterationFactor n) *
          ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth (n + 1) (|f x| / a)) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hC.le, mul_assoc C]

/-- The distribution inequality in dimension `n + 1`, obtained from dimension `n` by one
application of the kernel. -/
private theorem strongMaximal_step {n : ℕ} (hn : 1 ≤ n) {C : ℝ} (hC : 0 < C)
    (hIH : HasStrongMaximalOrliczBound n C)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) {a : ℝ} (ha : 0 < a) :
    volume {x | ENNReal.ofReal a < strongMaximalFunction f x} ≤
      ENNReal.ofReal (10 * C * strongMaximalIterationFactor n) *
        ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth (n + 1) (|f x| / a)) := by
  set I : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth (n + 1) (|f x| / a))
  by_cases hI : I = ∞
  · have hpos : ENNReal.ofReal (10 * C * strongMaximalIterationFactor n) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (by
        have := strongMaximalIterationFactor_pos n
        positivity)).ne'
    rw [hI, ENNReal.mul_top hpos]
    exact le_top
  have hn0 : 0 < n := by omega
  have hnull := partialStrongMax_top_null hn hC hIH hf ha hI
  have hint := lintegral_truncatedPartial_eq hn0 hf (a := a) hnull
  have hvol := strongMaximal_volume_le_truncIntegral hn hf ha
  have htrunc := lintegral_truncatedPartialReal_le hn hC hIH hf ha
  have h10 : 0 ≤ 10 / a := div_nonneg (by norm_num) ha.le
  have hconst : (10 / a) * (C * a * strongMaximalIterationFactor n) =
      10 * C * strongMaximalIterationFactor n := by
    field_simp [ha.ne']
  have hbound : volume {x | ENNReal.ofReal a < strongMaximalFunction f x} ≤
      ENNReal.ofReal (10 / a) *
        (ENNReal.ofReal (C * a * strongMaximalIterationFactor n) * I) := by
    refine hvol.trans ?_
    rw [hint]
    exact mul_le_mul' le_rfl htrunc
  have hrew : ENNReal.ofReal (10 / a) *
      (ENNReal.ofReal (C * a * strongMaximalIterationFactor n) * I) =
      ENNReal.ofReal (10 * C * strongMaximalIterationFactor n) * I := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul h10, hconst]
  exact hbound.trans_eq hrew

/-- In dimension zero the strong maximal function is at most `|f|`: the only rectangle is the
whole space, a single point of volume one. -/
private theorem strongMaximalFunction_le_of_fin_zero (f : (Fin 0 → ℝ) → ℝ) (x : Fin 0 → ℝ) :
    strongMaximalFunction f x ≤ ENNReal.ofReal |f x| := by
  refine iSup₂_le fun R _ ↦ ?_
  have hc : R.carrier = univ := eq_univ_of_forall fun _ j ↦ j.elim0
  have hf : (fun y ↦ ENNReal.ofReal |f y|) = fun _ ↦ ENNReal.ofReal |f x| :=
    funext fun y ↦ by rw [Subsingleton.elim y x]
  rw [hc, Measure.restrict_univ, hf, lintegral_const]
  exact ENNReal.div_le_of_le_mul le_rfl

/-- The weak-type bound in dimension zero, with constant `1`. -/
private theorem strongMaximal_weakType_fin_zero (f : (Fin 0 → ℝ) → ℝ) (hf : Measurable f)
    {a : ℝ} (ha : 0 < a) :
    volume {x | ENNReal.ofReal a < strongMaximalFunction f x} ≤
      ENNReal.ofReal 1 * ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth 0 (|f x| / a)) := by
  have hg : ∀ u, strongMaximalGrowth 0 u = u := fun u ↦ by simp [strongMaximalGrowth_def]
  simp only [hg, ENNReal.ofReal_one, one_mul]
  have hsub : {x | ENNReal.ofReal a < strongMaximalFunction f x} ⊆
      {x | 1 ≤ ENNReal.ofReal (|f x| / a)} := by
    intro x hx
    have h := hx.trans_le (strongMaximalFunction_le_of_fin_zero f x)
    rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha.le] at h
    rw [mem_ofPred_eq, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((one_le_div ha).2 h.le)
  have hm : AEMeasurable (fun x ↦ ENNReal.ofReal (|f x| / a)) volume :=
    ((continuous_abs.measurable.comp hf).div_const a).ennreal_ofReal.aemeasurable
  refine (measure_mono hsub).trans ?_
  simpa using mul_meas_ge_le_lintegral₀ hm 1

/-- **Jessen–Marcinkiewicz–Zygmund**: the strong maximal operator is of weak type
`L(log⁺L)^{d-1}` in every dimension `d`. -/
theorem strongMaximal_endpoint (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : (Fin d → ℝ) → ℝ), Measurable f →
      ∀ a : ℝ, 0 < a →
        volume {x | ENNReal.ofReal a < strongMaximalFunction f x} ≤
          ENNReal.ofReal C *
            ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth d (|f x| / a)) := by
  induction d with
  | zero => exact ⟨1, one_pos, fun f hf a ha ↦ strongMaximal_weakType_fin_zero f hf ha⟩
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · exact ⟨5, by norm_num, fun f _ a ha ↦ strongMaximal_weakType_one f ha⟩
    · obtain ⟨C, hC, hIH⟩ := ih
      have := strongMaximalIterationFactor_pos m
      exact ⟨10 * C * strongMaximalIterationFactor m, by positivity,
        fun f hf a ha ↦ strongMaximal_step hm1 hC hIH hf ha⟩

end CKMA
