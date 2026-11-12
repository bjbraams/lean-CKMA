/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.RectangularDifferentiation.Endpoint
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Order.Lattice

/-!
# One iteration of the strong maximal inequality

Fubini and the one-dimensional weak-type bound control the distribution of the strong maximal
function in dimension `n + 1` by the truncated strong maximal function of the slices. The
logarithmic kernel turns that distribution into the endpoint growth of order `n + 1`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Set
open scoped ENNReal intervalIntegral

/-- A nonnegative extended number bounded by every positive real is zero. -/
theorem eq_zero_of_forall_le_ofReal {c : ℝ≥0∞}
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
theorem strongMaximalGrowth_height_le {n k : ℕ} (hk : 1 ≤ k) {a v : ℝ} (ha : 0 < a)
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

/-- The ratio `2v / t` stays positive and continuous on a compact interval bounded away from zero,
so the endpoint growth in that ratio is continuous. -/
theorem continuousOn_strongMaximalGrowth_ratio {n : ℕ} {v c d : ℝ} (hc : 0 < c) (hv : 0 < v) :
    ContinuousOn (fun t ↦ strongMaximalGrowth n (2 * v / t)) (Icc c d) := by
  have hratio : ContinuousOn (fun t : ℝ ↦ 2 * v / t) (Icc c d) :=
    (continuous_const.continuousOn).div continuous_id.continuousOn fun t ht ↦
      (lt_of_lt_of_le hc ht.1).ne'
  have hlog : ContinuousOn (fun t ↦ Real.log (2 * v / t)) (Icc c d) :=
    Real.continuousOn_log.comp hratio fun t ht ↦
      (div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hv) (lt_of_lt_of_le hc ht.1)).ne'
  have hmaxSup : ContinuousOn (fun t ↦ (0 : ℝ) ⊔ Real.log (2 * v / t)) (Icc c d) :=
    continuousOn_const.sup hlog
  have hmax : ContinuousOn (fun t ↦ max 0 (Real.log (2 * v / t))) (Icc c d) :=
    hmaxSup.congr fun t _ ↦ by
      rw [max_def]
      exact (congr_fun₂ sup_eq_maxDefault (0 : ℝ) (Real.log (2 * v / t))).symm
  unfold strongMaximalGrowth
  exact hratio.mul ((continuousOn_const.add hmax).pow _)

/-- The partial maximal function, replaced by zero at infinity and on the half-height set. -/
def truncatedPartialReal {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (a : ℝ)
    (p : ℝ × (Fin n → ℝ)) : ℝ :=
  if partialStrongMax f p.1 p.2 = ∞ then 0
  else if ENNReal.ofReal (a / 2) < partialStrongMax f p.1 p.2 then
    (partialStrongMax f p.1 p.2).toReal else 0

/-- The real truncation of the partial maximal function is measurable. -/
theorem measurable_truncatedPartialReal {n : ℕ} (hn : 0 < n)
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
theorem partialStrongMax_top_null {n : ℕ} (hn : 1 ≤ n) {C : ℝ} (hC : 0 < C)
    (hIH : ∀ (g : (Fin n → ℝ) → ℝ), Measurable g → ∀ b : ℝ, 0 < b →
      volume {z | ENNReal.ofReal b < strongMaximalFunction g z} ≤
        ENNReal.ofReal C *
          ∫⁻ z, ENNReal.ofReal (strongMaximalGrowth n (|g z| / b)))
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Measurable f) {a : ℝ} (ha : 0 < a)
    (hI : ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth (n + 1) (|f x| / a)) ≠ ∞) :
    volume {p : ℝ × (Fin n → ℝ) | partialStrongMax f p.1 p.2 = ∞} = 0 := by
  let N : Set (ℝ × (Fin n → ℝ)) := {p | partialStrongMax f p.1 p.2 = ∞}
  have hn0 : 0 < n := by omega
  have hT : Measurable fun p : ℝ × (Fin n → ℝ) ↦ partialStrongMax f p.1 p.2 :=
    measurable_partialStrongMax hn0 hf
  have hN : MeasurableSet N := hT (measurableSet_singleton ∞)
  set I : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth (n + 1) (|f x| / a))
  let M : ℝ := C * a * (1 + |Real.log a|) ^ (n - 1)
  have hM : 0 < M := by
    have hpow : 0 < (1 + |Real.log a|) ^ (n - 1) := by positivity
    positivity
  refine eq_zero_of_forall_le_ofReal fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := exists_nat_gt (max (1 : ℝ) (M * I.toReal / ε))
  have hk1 : (1 : ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hkpos : 1 ≤ k := by
    have : (0 : ℝ) < k := lt_trans zero_lt_one hk1
    exact Nat.one_le_cast.mp (le_of_lt hk1)
  have hsub : N ⊆ {p | ENNReal.ofReal (k : ℝ) < partialStrongMax f p.1 p.2} := by
    intro p hp
    simp only [mem_ofPred_eq]
    have hinf : partialStrongMax f p.1 p.2 = ∞ := by simpa [N, mem_ofPred_eq] using hp
    rw [hinf]
    exact ENNReal.ofReal_lt_top
  have hdist := partial_distribution hn hIH hf
    (show 0 < (k : ℝ) by exact_mod_cast (lt_trans zero_lt_one hk1))
  have hgrow : ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth n (|f x| / k)) ≤
      ENNReal.ofReal ((a / (k : ℝ)) * (1 + |Real.log a|) ^ (n - 1)) * I := by
    let c : ℝ := (a / (k : ℝ)) * (1 + |Real.log a|) ^ (n - 1)
    have hc : 0 ≤ c := by positivity
    have hpt : ∀ x, ENNReal.ofReal (strongMaximalGrowth n (|f x| / k)) ≤
        ENNReal.ofReal c * ENNReal.ofReal (strongMaximalGrowth (n + 1) (|f x| / a)) := by
      intro x
      have hle := strongMaximalGrowth_height_le (n := n) hkpos ha (abs_nonneg (f x))
      calc
        ENNReal.ofReal (strongMaximalGrowth n (|f x| / k)) ≤
            ENNReal.ofReal (c * strongMaximalGrowth (n + 1) (|f x| / a)) :=
          ENNReal.ofReal_le_ofReal hle
        _ = ENNReal.ofReal c *
            ENNReal.ofReal (strongMaximalGrowth (n + 1) (|f x| / a)) :=
          ENNReal.ofReal_mul hc
    calc
      ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth n (|f x| / k)) ≤
          ∫⁻ x, ENNReal.ofReal c *
            ENNReal.ofReal (strongMaximalGrowth (n + 1) (|f x| / a)) :=
        lintegral_mono hpt
      _ = ENNReal.ofReal c * I := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hcoeff : ENNReal.ofReal C *
      ENNReal.ofReal ((a / (k : ℝ)) * (1 + |Real.log a|) ^ (n - 1)) =
        ENNReal.ofReal (M / (k : ℝ)) := by
    rw [← ENNReal.ofReal_mul hC.le]
    congr 1
    simp only [M]
    ring
  have hvol : volume N ≤ ENNReal.ofReal (M / (k : ℝ)) * I := by
    calc
      volume N ≤ volume {p | ENNReal.ofReal (k : ℝ) < partialStrongMax f p.1 p.2} :=
        measure_mono hsub
      _ ≤ ENNReal.ofReal C *
          ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth n (|f x| / k)) := hdist
      _ ≤ ENNReal.ofReal C *
          (ENNReal.ofReal ((a / (k : ℝ)) * (1 + |Real.log a|) ^ (n - 1)) * I) :=
        mul_le_mul' le_rfl hgrow
      _ = ENNReal.ofReal (M / (k : ℝ)) * I := by rw [← mul_assoc, hcoeff]
  set r : ℝ := I.toReal
  have hIeq : I = ENNReal.ofReal r := (ENNReal.ofReal_toReal hI).symm
  have hsmall : (M / (k : ℝ)) * r ≤ ε := by
    have hk0 : (0 : ℝ) < k := lt_trans zero_lt_one hk1
    have hdiv : M * r / ε < k := lt_of_le_of_lt (le_max_right _ _) hk
    have hmul : M * r < ε * k := by
      calc
        M * r < k * ε := (div_lt_iff₀ hε).mp hdiv
        _ = ε * k := by rw [mul_comm]
    have hquot : M * r / k < ε := (div_lt_iff₀ hk0).mpr hmul
    have hcomm : (M / (k : ℝ)) * r = M * r / k := by ring
    rw [hcomm]
    exact le_of_lt hquot
  calc
    volume N ≤ ENNReal.ofReal (M / (k : ℝ)) * I := hvol
    _ = ENNReal.ofReal ((M / (k : ℝ)) * r) := by
      rw [hIeq, ← ENNReal.ofReal_mul (div_nonneg hM.le (Nat.cast_nonneg k))]
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hsmall

/-- Off the null set where a slice maximal function is infinite, truncation does not change the
integral. -/
theorem lintegral_truncatedPartial_eq {n : ℕ} (hn : 0 < n)
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
theorem slice_tail_integral_le {n : ℕ} {a v : ℝ} (ha : 0 < a) (hv : 0 ≤ v) :
    ∫⁻ t : ℝ, (if a / 2 < t ∧ t / 2 < v then
        ENNReal.ofReal (strongMaximalGrowth n (2 * v / t)) else 0) ≤
      ENNReal.ofReal (if v ≤ a / 4 then 0 else
        ∫ t in (a / 2)..(2 * v), strongMaximalGrowth n (2 * v / t)) := by
  let φ : ℝ → ℝ≥0∞ := fun t ↦
    if a / 2 < t ∧ t / 2 < v then ENNReal.ofReal (strongMaximalGrowth n (2 * v / t)) else 0
  let ψ : ℝ → ℝ≥0∞ := fun t ↦
    if t / 2 < v then ENNReal.ofReal (strongMaximalGrowth n (2 * v / t)) else 0
  have hcompl : ∫⁻ t in (Ioi (a / 2))ᶜ, φ t = 0 :=
    setLIntegral_eq_zero measurableSet_Ioi.compl fun t ht ↦ by
      have ht' : ¬ a / 2 < t := by simpa [mem_compl_iff, mem_Ioi] using ht
      simp [φ, ht']
  have hon : ∫⁻ t in Ioi (a / 2), φ t = ∫⁻ t in Ioi (a / 2), ψ t :=
    setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ by
      have ht' : a / 2 < t := ht
      by_cases hv' : t / 2 < v
      · simp [φ, ψ, ht', hv']
      · simp [φ, ψ, ht', hv']
  have heq : ∫⁻ t, φ t = ∫⁻ t in Ioi (a / 2), ψ t := by
    calc
      ∫⁻ t, φ t = (∫⁻ t in Ioi (a / 2), φ t) + (∫⁻ t in (Ioi (a / 2))ᶜ, φ t) := by
        symm
        exact lintegral_add_compl _ measurableSet_Ioi
      _ = ∫⁻ t in Ioi (a / 2), ψ t := by rw [hcompl, add_zero, hon]
  rw [heq]
  by_cases hv4 : v ≤ a / 4
  · have hzero : ∫⁻ t in Ioi (a / 2), ψ t = 0 :=
      setLIntegral_eq_zero measurableSet_Ioi fun t ht ↦ by
        have hnot : ¬ t / 2 < v := by
          intro hlt
          have htv : t < 2 * v := by linarith
          have h2 : 2 * v ≤ a / 2 := by linarith
          linarith [show a / 2 < t from ht]
        simp [ψ, hnot]
    simp [hv4, hzero]
  · have h2v : a / 2 < 2 * v := by linarith
    have hsub : Ioo (a / 2) (2 * v) ⊆ Ioi (a / 2) := fun _ ht ↦ ht.1
    have hon' : ∫⁻ t in Ioo (a / 2) (2 * v), ψ t =
        ∫⁻ t in Ioo (a / 2) (2 * v), ENNReal.ofReal (strongMaximalGrowth n (2 * v / t)) :=
      setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ by
        have hlt : t / 2 < v := by linarith [ht.2]
        simp [ψ, hlt]
    have hoff : ∫⁻ t in Ioi (a / 2) \ Ioo (a / 2) (2 * v), ψ t = 0 :=
      setLIntegral_eq_zero (measurableSet_Ioi.diff measurableSet_Ioo) fun t ht ↦ by
        have hnot : ¬ t / 2 < v := by
          intro hlt
          exact ht.2 ⟨ht.1, by linarith⟩
        simp [ψ, hnot]
    have hsplit := (lintegral_inter_add_sdiff (μ := volume) ψ (Ioi (a / 2))
      (measurableSet_Ioo (a := a / 2) (b := 2 * v))).symm
    have hcap : Ioi (a / 2) ∩ Ioo (a / 2) (2 * v) = Ioo (a / 2) (2 * v) :=
      inter_eq_self_of_subset_right hsub
    have hIoi : ∫⁻ t in Ioi (a / 2), ψ t =
        ∫⁻ t in Ioo (a / 2) (2 * v),
          ENNReal.ofReal (strongMaximalGrowth n (2 * v / t)) := by
      rw [hsplit, hcap, hon', hoff, add_zero]
    have hdiff : volume (Ioc (a / 2) (2 * v) \ Ioo (a / 2) (2 * v)) = 0 := by
      refine measure_mono_null ?_ (by simp : volume ({2 * v} : Set ℝ) = 0)
      intro t ht
      have h1 : a / 2 < t := ht.1.1
      have h2 : t ≤ 2 * v := ht.1.2
      have h3 : ¬ t < 2 * v := by
        intro hlt
        exact ht.2 ⟨h1, hlt⟩
      exact mem_singleton_of_eq (le_antisymm h2 (le_of_not_gt h3))
    have hIoc : ∫⁻ t in Ioo (a / 2) (2 * v),
          ENNReal.ofReal (strongMaximalGrowth n (2 * v / t)) =
        ∫⁻ t in Ioc (a / 2) (2 * v),
          ENNReal.ofReal (strongMaximalGrowth n (2 * v / t)) := by
      have hinc : Ioo (a / 2) (2 * v) ⊆ Ioc (a / 2) (2 * v) :=
        fun t ht ↦ ⟨ht.1, le_of_lt ht.2⟩
      have hsplit' := (lintegral_inter_add_sdiff (μ := volume)
        (fun t ↦ ENNReal.ofReal (strongMaximalGrowth n (2 * v / t)))
        (Ioc (a / 2) (2 * v)) (measurableSet_Ioo (a := a / 2) (b := 2 * v))).symm
      have hcap' : Ioc (a / 2) (2 * v) ∩ Ioo (a / 2) (2 * v) = Ioo (a / 2) (2 * v) := by
        rw [inter_comm, inter_eq_self_of_subset_left hinc]
      have hzero := setLIntegral_measure_zero (Ioc (a / 2) (2 * v) \ Ioo (a / 2) (2 * v))
        (fun t ↦ ENNReal.ofReal (strongMaximalGrowth n (2 * v / t))) hdiff
      rw [hsplit', hcap', hzero, add_zero]
    have hvpos : 0 < v := by linarith
    have hcont : ContinuousOn (fun t ↦ strongMaximalGrowth n (2 * v / t))
        (Icc (a / 2) (2 * v)) :=
      continuousOn_strongMaximalGrowth_ratio
        (div_pos ha (by norm_num : (0 : ℝ) < 2)) hvpos
    have hint : IntegrableOn (fun t ↦ strongMaximalGrowth n (2 * v / t))
        (Ioc (a / 2) (2 * v)) volume :=
      (hcont.intervalIntegrable_of_Icc (le_of_lt h2v)).1
    have hnn : 0 ≤ᵐ[volume.restrict (Ioc (a / 2) (2 * v))]
        fun t ↦ strongMaximalGrowth n (2 * v / t) :=
      ae_restrict_of_forall_mem (measurableSet_Ioc (a := a / 2) (b := 2 * v)) fun t ht ↦
        strongMaximalGrowth_nonneg (div_nonneg
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hv)
          (le_trans (div_nonneg ha.le (by norm_num)) (le_of_lt ht.1)))
    have hof := ofReal_integral_eq_lintegral_ofReal hint hnn
    rw [← intervalIntegral.integral_of_le (le_of_lt h2v)] at hof
    rw [hIoi, hIoc, ← hof]
    simp [hv4]

/-- The scaled kernel, written with extended nonnegative values. -/
theorem iteration_ofReal_le {n : ℕ} (hn : 1 ≤ n) {a v : ℝ} (ha : 0 < a) (hv : 0 ≤ v) :
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

/-- The distribution inequality in dimension `n + 1`, obtained from dimension `n` by one
application of the kernel. -/
theorem strongMaximal_step {n : ℕ} (hn : 1 ≤ n) {C : ℝ} (hC : 0 < C)
    (hIH : ∀ (g : (Fin n → ℝ) → ℝ), Measurable g → ∀ b : ℝ, 0 < b →
      volume {z | ENNReal.ofReal b < strongMaximalFunction g z} ≤
        ENNReal.ofReal C *
          ∫⁻ z, ENNReal.ofReal (strongMaximalGrowth n (|g z| / b)))
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
  · have hn0 : 0 < n := by omega
    have hnull := partialStrongMax_top_null hn hC hIH hf ha hI
    have hint := lintegral_truncatedPartial_eq hn0 hf (a := a) hnull
    have hvol := strongMaximal_volume_le_truncIntegral hn hf ha
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
    have hdist := partial_distribution hn hIH hf hhalf
    have hquot : ∀ x, |f x| / (a / 2) = 2 * |f x| / a := by
      intro x
      field_simp [ha.ne']
    have hH : H ≤ ENNReal.ofReal C *
        ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth n (2 * |f x| / a)) := by
      simpa [hquot] using hdist
    have hhead_nn : 0 ≤ a / 2 := hhalf.le
    have hhead_int : H * ENNReal.ofReal (a / 2) ≤
        ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
          ((a / 2) * strongMaximalGrowth n (2 * |f x| / a)) := by
      calc
        H * ENNReal.ofReal (a / 2) ≤
            (ENNReal.ofReal C *
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
          exact (ENNReal.ofReal_mul hhead_nn).symm
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
    have htail_vol : ∀ t, a / 2 < t →
        volume {p | t < truncatedPartialReal f a p} ≤
          ENNReal.ofReal C * ∫⁻ x, tailφ t x := by
      intro t ht
      refine le_trans (measure_mono ?_) ((partial_distribution_trunc hn hIH hf
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
        · have habs : |truncAt t f x| = |f x| := by
            unfold truncAt
            rw [ite_eq_left hx]
          have hdiv : |truncAt t f x| / (t / 2) = 2 * |f x| / t := by
            rw [habs]
            field_simp [show t ≠ 0 by linarith]
          have htailx : tailφ t x =
              ENNReal.ofReal (strongMaximalGrowth n (2 * |f x| / t)) := by
            unfold tailφ
            rw [ite_eq_left ⟨ht, hx⟩]
          rw [hdiv, htailx]
        · have hzero : truncAt t f x = 0 := by
            unfold truncAt
            rw [ite_eq_right hx]
          have hnot : ¬ (a / 2 < t ∧ t / 2 < |f x|) := fun h ↦ hx h.2
          have htailx : tailφ t x = 0 := by
            unfold tailφ
            rw [ite_eq_right hnot]
          rw [hzero, htailx]
          simp [strongMaximalGrowth, Real.log_zero, abs_zero]
    have htail_int : ∫⁻ t in Ioi (a / 2), volume {p | t < truncatedPartialReal f a p} ≤
        ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
          (if |f x| ≤ a / 4 then 0 else
            ∫ s in (a / 2)..(2 * |f x|), strongMaximalGrowth n (2 * |f x| / s)) := by
      have hpt : ∫⁻ t in Ioi (a / 2), volume {p | t < truncatedPartialReal f a p} ≤
          ∫⁻ t in Ioi (a / 2), ENNReal.ofReal C * ∫⁻ x, tailφ t x :=
        setLIntegral_mono' measurableSet_Ioi fun t ht ↦ htail_vol t ht
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
    have hhead_fun : Measurable fun x ↦
        ENNReal.ofReal ((a / 2) * strongMaximalGrowth n (2 * |f x| / a)) := by
      have habs : Measurable fun x ↦ |f x| := continuous_abs.measurable.comp hf
      refine ENNReal.measurable_ofReal.comp (measurable_const.mul ?_)
      exact (measurable_strongMaximalGrowth n).comp
        ((measurable_const.mul habs).div_const a)
    have hkernel : ∀ x,
        ENNReal.ofReal ((a / 2) * strongMaximalGrowth n (2 * |f x| / a)) +
          ENNReal.ofReal (if |f x| ≤ a / 4 then 0 else
            ∫ s in (a / 2)..(2 * |f x|), strongMaximalGrowth n (2 * |f x| / s)) ≤
          ENNReal.ofReal (a * strongMaximalIterationFactor n *
            strongMaximalGrowth (n + 1) (|f x| / a)) :=
      fun x ↦ iteration_ofReal_le hn ha (abs_nonneg (f x))
    have hsum_int :
        (∫⁻ x, ENNReal.ofReal ((a / 2) * strongMaximalGrowth n (2 * |f x| / a))) +
          (∫⁻ x, ENNReal.ofReal (if |f x| ≤ a / 4 then 0 else
            ∫ s in (a / 2)..(2 * |f x|), strongMaximalGrowth n (2 * |f x| / s))) ≤
          ENNReal.ofReal (a * strongMaximalIterationFactor n) * I := by
      have hjoin :
          (∫⁻ x, ENNReal.ofReal ((a / 2) * strongMaximalGrowth n (2 * |f x| / a))) +
            (∫⁻ x, ENNReal.ofReal (if |f x| ≤ a / 4 then 0 else
              ∫ s in (a / 2)..(2 * |f x|), strongMaximalGrowth n (2 * |f x| / s))) =
            ∫⁻ x, ENNReal.ofReal ((a / 2) * strongMaximalGrowth n (2 * |f x| / a)) +
              ENNReal.ofReal (if |f x| ≤ a / 4 then 0 else
                ∫ s in (a / 2)..(2 * |f x|), strongMaximalGrowth n (2 * |f x| / s)) :=
        (lintegral_add_left hhead_fun _).symm
      have hfactor : 0 ≤ a * strongMaximalIterationFactor n :=
        mul_nonneg ha.le (strongMaximalIterationFactor_pos n).le
      calc
        (∫⁻ x, ENNReal.ofReal ((a / 2) * strongMaximalGrowth n (2 * |f x| / a))) +
            (∫⁻ x, ENNReal.ofReal (if |f x| ≤ a / 4 then 0 else
              ∫ s in (a / 2)..(2 * |f x|), strongMaximalGrowth n (2 * |f x| / s))) =
            ∫⁻ x, ENNReal.ofReal ((a / 2) * strongMaximalGrowth n (2 * |f x| / a)) +
              ENNReal.ofReal (if |f x| ≤ a / 4 then 0 else
                ∫ s in (a / 2)..(2 * |f x|), strongMaximalGrowth n (2 * |f x| / s)) := hjoin
        _ ≤ ∫⁻ x, ENNReal.ofReal (a * strongMaximalIterationFactor n *
            strongMaximalGrowth (n + 1) (|f x| / a)) := lintegral_mono hkernel
        _ = ∫⁻ x, ENNReal.ofReal (a * strongMaximalIterationFactor n) *
            ENNReal.ofReal (strongMaximalGrowth (n + 1) (|f x| / a)) := by
          refine lintegral_congr fun x ↦ ?_
          exact ENNReal.ofReal_mul hfactor
        _ = ENNReal.ofReal (a * strongMaximalIterationFactor n) * I :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have hsplit_cake : ∫⁻ p, ENNReal.ofReal (truncatedPartialReal f a p) =
        (∫⁻ t in Ioc (0 : ℝ) (a / 2), volume {p | t < truncatedPartialReal f a p}) +
          (∫⁻ t in Ioi (a / 2), volume {p | t < truncatedPartialReal f a p}) := by
      rw [hcake, hsplit, hcap, hrest]
    have htrunc : ∫⁻ p, ENNReal.ofReal (truncatedPartialReal f a p) ≤
        ENNReal.ofReal (C * a * strongMaximalIterationFactor n) * I := by
      calc
        ∫⁻ p, ENNReal.ofReal (truncatedPartialReal f a p) =
            (∫⁻ t in Ioc (0 : ℝ) (a / 2), volume {p | t < truncatedPartialReal f a p}) +
              (∫⁻ t in Ioi (a / 2), volume {p | t < truncatedPartialReal f a p}) := hsplit_cake
        _ ≤ (ENNReal.ofReal C *
              ∫⁻ x, ENNReal.ofReal ((a / 2) * strongMaximalGrowth n (2 * |f x| / a))) +
            (ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (if |f x| ≤ a / 4 then 0 else
              ∫ s in (a / 2)..(2 * |f x|), strongMaximalGrowth n (2 * |f x| / s))) :=
          add_le_add (hhead_le.trans hhead_int) htail_int
        _ = ENNReal.ofReal C *
            ((∫⁻ x, ENNReal.ofReal ((a / 2) * strongMaximalGrowth n (2 * |f x| / a))) +
              (∫⁻ x, ENNReal.ofReal (if |f x| ≤ a / 4 then 0 else
                ∫ s in (a / 2)..(2 * |f x|),
                  strongMaximalGrowth n (2 * |f x| / s)))) := by
          rw [mul_add]
        _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (a * strongMaximalIterationFactor n) * I) :=
          mul_le_mul' le_rfl hsum_int
        _ = ENNReal.ofReal (C * a * strongMaximalIterationFactor n) * I := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hC.le]
          congr 1
          ring
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

/-- The strong maximal operator is weak type `L(log⁺L)^{d-1}` in every positive dimension. -/
theorem strongMaximal_orlicz {d : ℕ} (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : (Fin d → ℝ) → ℝ), Measurable f →
      ∀ a : ℝ, 0 < a →
        volume {x | ENNReal.ofReal a < strongMaximalFunction f x} ≤
          ENNReal.ofReal C *
            ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth d (|f x| / a)) := by
  revert hd
  induction d with
  | zero =>
    intro h
    omega
  | succ m ih =>
    intro hm
    by_cases hm0 : m = 0
    · subst hm0
      refine ⟨oneDimWeakConstant, ?_, ?_⟩
      · unfold oneDimWeakConstant
        norm_num
      · intro f _ a ha
        exact strongMaximal_weakType_one f ha
    · have hm1 : 1 ≤ m := by omega
      obtain ⟨C, hC, hIH⟩ := ih hm1
      refine ⟨10 * C * strongMaximalIterationFactor m,
        mul_pos (mul_pos (by norm_num) hC) (strongMaximalIterationFactor_pos m), ?_⟩
      intro f hf a ha
      exact strongMaximal_step hm1 hC hIH hf ha

end CKMA
