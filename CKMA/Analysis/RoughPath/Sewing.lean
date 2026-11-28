/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.RoughPath.Sewing.Basic
public import Mathlib.Topology.MetricSpace.Holder
import CKMA.Analysis.RoughPath.Sewing.Construction
import CKMA.Analysis.RoughPath.Sewing.YoungIntegral
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Sewing and Young integration

Ordered partitions allow repeated nodes and degenerate intervals. Their mesh and increment sums
define sewing limits with a normalized continuous primitive and a quantitative remainder for
defect exponent greater than one. Young integration `∫ Y dX` of an operator-valued integrand `Y`
against an integrator `X` is stated for Hölder paths and for continuous paths of complementary
finite variation exponents. Hölder predicates and compact continuous maps are Mathlib's.
Sources: GAPS 09.21 and 09.22.

## Main results

* `CKMA.sewing_lemma`: Gubinelli's sewing lemma with a normalized continuous primitive.
* `CKMA.young_holder`: Young integration for Hölder paths with complementary exponents.
* `CKMA.young_variation`: Young integration for continuous paths of complementary finite
  variation.
* `CKMA.holderOnWith_Icc_eq_of_one_lt`: a path that is Hölder of order greater than one on an
  interval is constant there.

## Implementation notes

All three theorems build the path as `x ↦ Z a x` from an additive increment field `Z`
(`CKMA.exists_isLeftNormalized_sub_eq`) and get uniqueness from the partition-sum limit
(`CKMA.IsLeftNormalized.eq_of_hasPartitionSumLimit`). Uniqueness is among paths on `[a, b]`, so
the values of `A`, `X` and `Y` outside `[a, b]` play no role.

## References

* [P. K. Friz and M. Hairer, *A Course on Rough Paths*][frizhairer2020]
-/

public section

noncomputable section

namespace CKMA

open scoped BigOperators NNReal ENNReal
open Filter Topology

/-- **09.22**: the sewing lemma. If a continuous increment field `A` on `a ≤ s ≤ t ≤ b` has
defect `‖A s t - A s u - A u t‖ ≤ C |t - s| ^ γ` with `γ > 1`, there is a unique continuous path
`I` on `[a, b]` with `I a = 0` whose increments are the limits of the partition sums of `A`, and
`‖I t - I s - A s t‖ ≤ sewingConstant γ · C · |t - s| ^ γ`. -/
theorem sewing_lemma {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {a b γ C : ℝ} (hab : a ≤ b) (hγ : 1 < γ) (A : ℝ → ℝ → E)
    (hcont : ContinuousOn (fun p : ℝ × ℝ ↦ A p.1 p.2)
      {p | a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b})
    (hdefect : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ C * |t - s| ^ γ) :
    ∃! I : C(Set.Icc a b, E), IsLeftNormalized I ∧
      HasSewingRemainder A I γ (sewingConstant γ * C) ∧ HasPartitionSumLimit A I := by
  -- The construction uses a nonnegative defect constant; `max C 0` is one.
  have hC' : 0 ≤ max C 0 := le_max_right C 0
  have hdefect' : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ max C 0 * |t - s| ^ γ := fun s u t hs hsu hut ht =>
    (hdefect s u t hs hsu hut ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg (abs_nonneg _) _))
  have hcontT : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2) (sewingTriangle a b) := hcont
  obtain ⟨I, hleft, hinc⟩ := exists_isLeftNormalized_sub_eq hab _
    (Sewing.continuousOn_sewnIncrement hab hγ hC' hcontT hdefect')
    fun s u t hs hsu hut ht => Sewing.sewnIncrement_add hab hγ hC' hcontT hdefect' hs hsu hut ht
  have hlim : HasPartitionSumLimit A I := fun s t hst => by
    rw [hinc s t hst]
    refine partitionSumsConverge_of_norm_le hγ
      (mul_nonneg (mul_nonneg (sewingConstant_pos hγ).le hC') (sub_nonneg.mpr hst))
      fun π => (Sewing.norm_partition_sub hab hγ hC' hcontT hdefect' s.2.1 t.2.2 π).trans_eq ?_
    ring
  refine ⟨I, ⟨hleft, fun s t hst => ?_, hlim⟩, fun J hJ => ?_⟩
  · rw [hinc s t hst]
    exact Sewing.norm_sewnIncrement_sub hγ hdefect s.2.1 hst t.2.2
  · exact hJ.1.eq_of_hasPartitionSumLimit hleft hJ.2.2 hlim

/-- A path that is Hölder of order `r > 1` on `[a, b]` is constant on `[a, b]`. -/
theorem holderOnWith_Icc_eq_of_one_lt {E : Type*} [NormedAddCommGroup E] {C r : ℝ≥0}
    {X : ℝ → E} {a b : ℝ} (h : HolderOnWith C r X (Set.Icc a b)) (hr : 1 < r) {x y : ℝ}
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) : X x = X y := by
  wlog hxy : x ≤ y generalizing x y
  · exact (this hy hx (le_of_not_ge hxy)).symm
  have hr' : (1 : ℝ) < r := by exact_mod_cast hr
  have hbound : ∀ n : ℕ, 0 < n →
      ‖X y - X x‖ ≤ C * (y - x) ^ (r : ℝ) * (n : ℝ) ^ (1 - (r : ℝ)) := by
    intro n hn
    have hnode : ∀ i ≤ n, Sewing.equalNode x y n i ∈ Set.Icc a b := fun i hi =>
      ⟨hx.1.trans (Sewing.equalNode_mem hxy hn hi).1, (Sewing.equalNode_mem hxy hn hi).2.trans hy.2⟩
    have htel : X y - X x = ∑ i ∈ Finset.range n,
        (X (Sewing.equalNode x y n (i + 1)) - X (Sewing.equalNode x y n i)) := by
      rw [Finset.sum_range_sub (fun i => X (Sewing.equalNode x y n i)),
        Sewing.equalNode_last x y hn, Sewing.equalNode_zero]
    have hstep : ∀ i ∈ Finset.range n,
        ‖X (Sewing.equalNode x y n (i + 1)) - X (Sewing.equalNode x y n i)‖ ≤
          C * ((y - x) / n) ^ (r : ℝ) := fun i hi => by
      have hi' := Finset.mem_range.mp hi
      have hd := h.dist_le (hnode (i + 1) hi') (hnode i hi'.le)
      rwa [dist_eq_norm, Real.dist_eq, Sewing.equalNode_sub,
        abs_of_nonneg (div_nonneg (sub_nonneg.mpr hxy) (Nat.cast_nonneg _))] at hd
    calc
      ‖X y - X x‖ ≤ ∑ i ∈ Finset.range n, C * ((y - x) / n) ^ (r : ℝ) :=
        htel ▸ (norm_sum_le _ _).trans (Finset.sum_le_sum hstep)
      _ = C * (y - x) ^ (r : ℝ) * (n : ℝ) ^ (1 - (r : ℝ)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_left_comm,
          nat_mul_div_rpow hn (sub_nonneg.mpr hxy) (by positivity)]
        ring
  have hlim : Tendsto (fun n : ℕ => C * (y - x) ^ (r : ℝ) * (n : ℝ) ^ (1 - (r : ℝ)))
      atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (sub_pos.mpr hr')).comp
      tendsto_natCast_atTop_atTop).const_mul (C * (y - x) ^ (r : ℝ))
    simpa [Function.comp_def, neg_sub] using this
  have hle : ‖X y - X x‖ ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun n hn => hbound n hn⟩)
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp hle)).symm

/-- The three-point defect of the Young increment of an `α`-Hölder integrator `X` and a
`β`-Hölder integrand `Y` on `[a, b]` is at most `Hx · Hy · |t - s| ^ (α + β)`. -/
theorem norm_youngIncrement_defect_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {α β Hx Hy : ℝ≥0} (hαβ : α + β ≠ 0)
    {X : ℝ → E} {Y : ℝ → E →L[ℝ] F}
    (hX : HolderOnWith Hx α X (Set.Icc a b)) (hY : HolderOnWith Hy β Y (Set.Icc a b))
    {s u t : ℝ} (hs : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (ht : t ≤ b) :
    ‖youngIncrement X Y s t - youngIncrement X Y s u - youngIncrement X Y u t‖ ≤
      (Hx : ℝ) * Hy * |t - s| ^ (↑(α + β) : ℝ) := by
  have hAlg : youngIncrement X Y s t - youngIncrement X Y s u - youngIncrement X Y u t =
      (Y s - Y u) (X t - X u) := by
    simp only [youngIncrement]
    rw [← map_sub]
    have : (X t - X s) - (X u - X s) = X t - X u := by abel
    rw [this, ← sub_apply]
  rw [hAlg]
  by_cases hst : s = t
  · have hu : u = s := le_antisymm (by simpa [hst] using hut) hsu
    subst hst hu
    simp [map_zero, sub_self]
    rw [Real.zero_rpow (show ((α : ℝ) + β) ≠ 0 by exact_mod_cast hαβ)]
    simp
  · have hlt : s < t := lt_of_le_of_ne (hsu.trans hut) hst
    have hpos : 0 < |t - s| := abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hlt))
    have hus : |u - s| ≤ |t - s| := by
      rw [abs_of_nonneg (sub_nonneg.mpr hsu), abs_of_nonneg (sub_nonneg.mpr (hsu.trans hut))]
      linarith
    have htu : |t - u| ≤ |t - s| := by
      rw [abs_of_nonneg (sub_nonneg.mpr hut), abs_of_nonneg (sub_nonneg.mpr (hsu.trans hut))]
      linarith
    have hYs : s ∈ Set.Icc a b := ⟨hs, (hsu.trans hut).trans ht⟩
    have hYu : u ∈ Set.Icc a b := ⟨hs.trans hsu, hut.trans ht⟩
    have hXt : t ∈ Set.Icc a b := ⟨(hs.trans hsu).trans hut, ht⟩
    have hYn : ‖Y s - Y u‖ ≤ (Hy : ℝ) * |u - s| ^ (β : ℝ) := by
      simpa [dist_eq_norm, Real.dist_eq, abs_sub_comm] using hY.dist_le hYs hYu
    have hXn : ‖X t - X u‖ ≤ (Hx : ℝ) * |t - u| ^ (α : ℝ) := by
      simpa [dist_eq_norm, Real.dist_eq, abs_sub_comm] using hX.dist_le hXt hYu
    have hpowu : |u - s| ^ (β : ℝ) ≤ |t - s| ^ (β : ℝ) :=
      Real.rpow_le_rpow (abs_nonneg _) hus (NNReal.coe_nonneg β)
    have hpowt : |t - u| ^ (α : ℝ) ≤ |t - s| ^ (α : ℝ) :=
      Real.rpow_le_rpow (abs_nonneg _) htu (NNReal.coe_nonneg α)
    calc
      ‖(Y s - Y u) (X t - X u)‖ ≤ ‖Y s - Y u‖ * ‖X t - X u‖ :=
        (Y s - Y u).le_opNorm _
      _ ≤ ((Hy : ℝ) * |u - s| ^ (β : ℝ)) * ((Hx : ℝ) * |t - u| ^ (α : ℝ)) :=
        mul_le_mul hYn hXn (norm_nonneg _)
          (mul_nonneg (NNReal.coe_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _))
      _ ≤ ((Hy : ℝ) * |t - s| ^ (β : ℝ)) * ((Hx : ℝ) * |t - s| ^ (α : ℝ)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hpowu (NNReal.coe_nonneg _))
          (mul_le_mul_of_nonneg_left hpowt (NNReal.coe_nonneg _)) ?_ ?_
        · exact mul_nonneg (NNReal.coe_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _)
        · exact mul_nonneg (NNReal.coe_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _)
      _ = (Hx : ℝ) * Hy * (|t - s| ^ (β : ℝ) * |t - s| ^ (α : ℝ)) := by ring
      _ = (Hx : ℝ) * Hy * |t - s| ^ ((β : ℝ) + (α : ℝ)) := by
        rw [← Real.rpow_add hpos]
      _ = (Hx : ℝ) * Hy * |t - s| ^ (↑(α + β) : ℝ) := by
        rw [add_comm (β : ℝ), ← NNReal.coe_add]

/-- **09.21**: Hölder Young integration with the Young–Loeve remainder estimate. For an
`α`-Hölder integrator `X` and a `β`-Hölder operator-valued integrand `Y` with `α > 0` and
`α + β > 1`, the Young integral `∫ Y dX` exists as the unique left-normalized continuous path whose
increments are the limits of the partition sums of `Y s (X t - X s)`. For `β = 0` the integrator
is constant on `[a, b]` and the integral is zero. -/
theorem young_holder {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {a b : ℝ} (hab : a ≤ b) {α β Hx Hy : ℝ≥0}
    (hα : 0 < α) (hαβ : 1 < α + β)
    (X : ℝ → E) (Y : ℝ → E →L[ℝ] F)
    (hX : HolderOnWith Hx α X (Set.Icc a b))
    (hY : HolderOnWith Hy β Y (Set.Icc a b)) :
    ∃! I : C(Set.Icc a b, F), IsLeftNormalized I ∧
      HasPartitionSumLimit (youngIncrement X Y) I ∧
      HasSewingRemainder (youngIncrement X Y) I (α + β : ℝ≥0)
        (sewingConstant (α + β : ℝ≥0) * Hx * Hy) := by
  have hγ : (1 : ℝ) < ↑(α + β) := by exact_mod_cast hαβ
  have hXcont := hX.continuousOn (by exact_mod_cast hα)
  let A := youngIncrement X Y
  have htri : sewingTriangle a b ⊆ Set.Icc a b ×ˢ Set.Icc a b := by
    rintro p ⟨hs, hst, ht⟩
    exact ⟨⟨hs, hst.trans ht⟩, ⟨hs.trans hst, ht⟩⟩
  have hcontA : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2) (sewingTriangle a b) := by
    rcases eq_or_ne β 0 with hβ | hβ
    · -- For `β = 0` the integrator is constant on `[a, b]`, so `A` vanishes on the triangle.
      have hα1 : 1 < α := by simpa [hβ] using hαβ
      refine (continuousOn_const (c := (0 : F))).congr fun p hp => ?_
      have hXeq := holderOnWith_Icc_eq_of_one_lt hX hα1 (htri hp).2 (htri hp).1
      simp [A, youngIncrement, hXeq]
    have hYcont := hY.continuousOn (by exact_mod_cast pos_iff_ne_zero.mpr hβ)
    have hYc : ContinuousOn (fun p : ℝ × ℝ => Y p.1) (sewingTriangle a b) :=
      hYcont.comp continuous_fst.continuousOn fun p hp => (htri hp).1
    have hXc : ContinuousOn (fun p : ℝ × ℝ => X p.2 - X p.1) (sewingTriangle a b) :=
      (hXcont.comp continuous_snd.continuousOn fun p hp => (htri hp).2).sub
        (hXcont.comp continuous_fst.continuousOn fun p hp => (htri hp).1)
    simpa [A, youngIncrement] using hYc.clm_apply hXc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2)
      {p | a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b} := by
    simpa [sewingTriangle] using hcontA
  have hdefect : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ (Hx : ℝ) * Hy * |t - s| ^ (↑(α + β) : ℝ) :=
    fun s u t hs hsu hut ht => norm_youngIncrement_defect_le (ne_of_gt (zero_lt_one.trans hαβ))
      hX hY hs hsu hut ht
  rcases sewing_lemma hab hγ A hcont hdefect with ⟨I, hI, huniq⟩
  rcases hI with ⟨hleft, hrem, hlim⟩
  refine ⟨I, ⟨⟨hleft, hlim, ?_⟩, ?_⟩⟩
  · simpa [mul_assoc, A] using hrem
  · intro J hJ
    exact huniq J ⟨hJ.1, by simpa [mul_assoc, A] using hJ.2.2, hJ.2.1⟩

/-- **09.21**, variation form: Young integration `∫ Y dX` for a continuous integrator `X` of
finite `p`-variation and a continuous operator-valued integrand `Y` of finite `q`-variation with
`1 < p⁻¹ + q⁻¹`, with the Young–Loeve remainder `sewingConstant (p⁻¹ + q⁻¹)` times the product of
the variation moduli. -/
theorem young_variation {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {a b p q : ℝ} (hab : a ≤ b) (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 < p⁻¹ + q⁻¹)
    (X : ℝ → E) (Y : ℝ → E →L[ℝ] F)
    (hX : ContinuousOn X (Set.Icc a b)) (hY : ContinuousOn Y (Set.Icc a b))
    (hVp : pathVariationPower p X a b ≠ ∞) (hVq : pathVariationPower q Y a b ≠ ∞) :
    ∃! I : C(Set.Icc a b, F), IsLeftNormalized I ∧
      HasPartitionSumLimit (youngIncrement X Y) I ∧
      ∀ s t : Set.Icc a b, s.val ≤ t.val →
        ‖(I t - I s) - youngIncrement X Y s.val t.val‖ ≤
          sewingConstant (p⁻¹ + q⁻¹) *
            (pathVariationPower p X s.val t.val).toReal ^ p⁻¹ *
            (pathVariationPower q Y s.val t.val).toReal ^ q⁻¹ := by
  let D : YoungLoeve.YoungData E F := ⟨a, b, p, q, hab, hp, hq, hpq, X, Y, hX, hY, hVp, hVq⟩
  obtain ⟨I, hleft, hinc⟩ := exists_isLeftNormalized_sub_eq hab _ D.continuousOn_youngLimit
    fun s u t hs hsu hut ht => D.youngLimit_add hs hsu hut ht
  have hlim : HasPartitionSumLimit (youngIncrement X Y) I := fun s t hst ε hε => by
    obtain ⟨δ, hδ, hδπ⟩ := D.exists_partition_close s.2.1 t.2.2 ε hε
    refine ⟨δ, hδ, fun π hmesh => ?_⟩
    rw [hinc s t hst]
    exact hδπ π hmesh
  refine ⟨I, ⟨hleft, hlim, fun s t hst => ?_⟩, fun J hJ => ?_⟩
  · rw [hinc s t hst]
    exact D.norm_youngLimit_sharp s.2.1 hst t.2.2
  · exact hJ.1.eq_of_hasPartitionSumLimit hleft hJ.2.1 hlim

end CKMA
