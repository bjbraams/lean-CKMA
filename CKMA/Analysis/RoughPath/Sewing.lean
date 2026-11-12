/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.RoughPath.Sewing.Construction
public import CKMA.Analysis.RoughPath.Sewing.YoungIntegral
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Sewing and Young integration

Ordered partitions allow repeated nodes and degenerate intervals. Their mesh and
increment sums define sewing limits with a normalized continuous primitive and a
quantitative remainder for defect exponent greater than one. Young integration is
stated for Hölder paths and for continuous paths of complementary finite variation
exponents. Hölder predicates and compact continuous maps use Mathlib.
Sources: GAPS 09.21 and 09.22.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped BigOperators NNReal ENNReal


/-- **09.22**: the sewing lemma with a normalized continuous primitive.
Uniqueness is on the interval, so arbitrary extensions outside it cannot cause false uniqueness. -/
theorem sewing_lemma {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {a b γ C : ℝ} (hab : a ≤ b) (hγ : 1 < γ) (hC : 0 ≤ C) (A : ℝ → ℝ → E)
    (hcont : ContinuousOn (fun p : ℝ × ℝ ↦ A p.1 p.2)
      {p | a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b})
    (hdiag : ∀ s ∈ Set.Icc a b, A s s = 0)
    (hdefect : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ C * |t - s| ^ γ) :
    ∃! I : C(Set.Icc a b, E), IsLeftNormalized I ∧
      HasSewingRemainder A I γ (sewingConstant γ * C) ∧ HasPartitionSumLimit A I := by
  have hcontT : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2) (sewingTriangle a b) := by
    simpa [sewingTriangle] using hcont
  let Z := Sewing.sewnIncrement A
  let I : C(Set.Icc a b, E) := ⟨fun x => Z a x.val,
    (Sewing.continuousOn_sewnIncrement hab hγ hC hcontT hdefect).comp_continuous
      (continuous_const.prodMk continuous_subtype_val) fun x => ⟨le_rfl, x.2.1, x.2.2⟩⟩
  have hinc : ∀ {s t : Set.Icc a b}, s.val ≤ t.val → I t - I s = Z s.val t.val := by
    intro s t hst
    have hadd := Sewing.sewnIncrement_add hab hγ hC hcontT hdiag hdefect le_rfl
      s.2.1 hst t.2.2
    have hIt : I t = Z a t.val := rfl
    have hIs : I s = Z a s.val := rfl
    rw [hIt, hIs]
    change Sewing.sewnIncrement A a t.val - Sewing.sewnIncrement A a s.val =
      Sewing.sewnIncrement A s.val t.val
    rw [hadd]
    abel
  have hleft : IsLeftNormalized I := by
    intro x hx
    change Z a x.val = 0
    rw [hx]
    exact Sewing.sewnIncrement_same hdiag le_rfl hab
  have hrem : HasSewingRemainder A I γ (sewingConstant γ * C) := by
    intro s t hst
    rw [hinc hst]
    exact Sewing.norm_sewnIncrement_sub hγ hC hdefect s.2.1 hst t.2.2
  have hlim : HasPartitionSumLimit A I := by
    intro s t hst ε hε
    let L := sewingConstant γ * C * (t.val - s.val)
    by_cases hL0 : L = 0
    · refine ⟨1, one_pos, fun π _ => ?_⟩
      rw [hinc hst]
      refine lt_of_le_of_lt (Sewing.norm_partition_sub hab hγ hC hcontT hdiag hdefect
        s.2.1 t.2.2 π) ?_
      rw [show sewingConstant γ * C * (π.mesh : ℝ) ^ (γ - 1) * (t.val - s.val) = 0 by
        rw [show sewingConstant γ * C * (π.mesh : ℝ) ^ (γ - 1) * (t.val - s.val) =
            (π.mesh : ℝ) ^ (γ - 1) * L by simp only [L]; ring, hL0, mul_zero]]
      exact hε
    · have hne : (0 : ℝ) ≠ L := fun h => hL0 h.symm
      have hLpos : 0 < L := lt_of_le_of_ne (mul_nonneg
        (mul_nonneg (Sewing.sewingConstant_pos hγ).le hC) (sub_nonneg.mpr hst)) hne
      refine ⟨(ε / L) ^ (γ - 1)⁻¹, Real.rpow_pos_of_pos (div_pos hε hLpos) _,
        fun π hmesh => ?_⟩
      rw [hinc hst]
      refine lt_of_le_of_lt (Sewing.norm_partition_sub hab hγ hC hcontT hdiag hdefect
        s.2.1 t.2.2 π) ?_
      have hγ1 : 0 < γ - 1 := sub_pos.mpr hγ
      have hpow : (π.mesh : ℝ) ^ (γ - 1) < ε / L := by
        have hlt := Real.rpow_lt_rpow (NNReal.coe_nonneg π.mesh) hmesh hγ1
        have hbase : ((ε / L) ^ (γ - 1)⁻¹) ^ (γ - 1) = ε / L := by
          rw [← Real.rpow_mul (div_nonneg hε.le hLpos.le)]
          have : (γ - 1)⁻¹ * (γ - 1) = 1 := by field_simp
          rw [this, Real.rpow_one]
        simpa [hbase] using hlt
      have hassoc : sewingConstant γ * C * (π.mesh : ℝ) ^ (γ - 1) * (t.val - s.val) =
          L * (π.mesh : ℝ) ^ (γ - 1) := by simp only [L]; ring
      rw [hassoc]
      exact (mul_lt_mul_of_pos_left hpow hLpos).trans_eq (by field_simp)
  refine ⟨I, ⟨⟨hleft, hrem, hlim⟩, ?_⟩⟩
  intro J hJ
  apply ContinuousMap.ext
  intro x
  let a0 : Set.Icc a b := ⟨a, ⟨le_rfl, hab⟩⟩
  have hI0 := hleft a0 rfl
  have hJ0 := hJ.1 a0 rfl
  have hEq := Sewing.partitionLimit_unique x.2.1 (hlim a0 x x.2.1) (hJ.2.2 a0 x x.2.1)
  simpa [hI0, hJ0] using hEq.symm

/-- The field of left-point Young increments for an operator-valued integrand. -/
def youngIncrement {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (X : ℝ → E) (Y : ℝ → E →L[ℝ] F) (s t : ℝ) : F := Y s (X t - X s)

/-- **09.21**: Holder Young integration with the Young–Loeve remainder estimate. -/
theorem young_holder {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {a b : ℝ} (hab : a ≤ b) {α β Hx Hy : ℝ≥0}
    (hα : 0 < α) (hβ : 0 < β) (hαβ : 1 < α + β)
    (X : ℝ → E) (Y : ℝ → E →L[ℝ] F)
    (hX : HolderOnWith Hx α X (Set.Icc a b))
    (hY : HolderOnWith Hy β Y (Set.Icc a b)) :
    ∃! I : C(Set.Icc a b, F), IsLeftNormalized I ∧
      HasPartitionSumLimit (youngIncrement X Y) I ∧
      HasSewingRemainder (youngIncrement X Y) I (α + β : ℝ≥0)
        (sewingConstant (α + β : ℝ≥0) * Hx * Hy) := by
  have hγ : (1 : ℝ) < ↑(α + β) := by exact_mod_cast hαβ
  have hC : 0 ≤ (Hx : ℝ) * Hy :=
    mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  have hXcont := hX.continuousOn (by exact_mod_cast hα)
  have hYcont := hY.continuousOn (by exact_mod_cast hβ)
  let A := youngIncrement X Y
  have htri : sewingTriangle a b ⊆ Set.Icc a b ×ˢ Set.Icc a b := by
    rintro p ⟨hs, hst, ht⟩
    exact ⟨⟨hs, hst.trans ht⟩, ⟨hs.trans hst, ht⟩⟩
  have hcontA : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2) (sewingTriangle a b) := by
    have hYc : ContinuousOn (fun p : ℝ × ℝ => Y p.1) (sewingTriangle a b) :=
      hYcont.comp continuous_fst.continuousOn fun p hp => (htri hp).1
    have hXc : ContinuousOn (fun p : ℝ × ℝ => X p.2 - X p.1) (sewingTriangle a b) :=
      (hXcont.comp continuous_snd.continuousOn fun p hp => (htri hp).2).sub
        (hXcont.comp continuous_fst.continuousOn fun p hp => (htri hp).1)
    simpa [A, youngIncrement] using hYc.clm_apply hXc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2)
      {p | a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b} := by
    simpa [sewingTriangle] using hcontA
  have hdiag : ∀ s ∈ Set.Icc a b, A s s = 0 := by
    intro s _
    simp [A, youngIncrement, map_zero]
  have hdefect : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ (Hx : ℝ) * Hy * |t - s| ^ (↑(α + β) : ℝ) := by
    intro s u t hs hsu hut ht
    have hAlg : A s t - A s u - A u t = (Y s - Y u) (X t - X u) := by
      simp only [A, youngIncrement]
      rw [← map_sub]
      have : (X t - X s) - (X u - X s) = X t - X u := by abel
      rw [this, ← sub_apply]
    rw [hAlg]
    by_cases hst : s = t
    · have hu : u = s := le_antisymm (by simpa [hst] using hut) hsu
      subst hst hu
      simp [map_zero, sub_self]
      rw [Real.zero_rpow (show ((α : ℝ) + β) ≠ 0 by
        rw [← NNReal.coe_add]
        exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hαβ)))]
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
        Real.rpow_le_rpow (abs_nonneg _) hus (by exact_mod_cast hβ.le)
      have hpowt : |t - u| ^ (α : ℝ) ≤ |t - s| ^ (α : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg _) htu (by exact_mod_cast hα.le)
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
  rcases sewing_lemma hab hγ hC A hcont hdiag hdefect with ⟨I, hI, huniq⟩
  rcases hI with ⟨hleft, hrem, hlim⟩
  refine ⟨I, ⟨⟨hleft, hlim, ?_⟩, ?_⟩⟩
  · simpa [mul_assoc, A] using hrem
  · intro J hJ
    exact huniq J ⟨hJ.1, by simpa [mul_assoc, A] using hJ.2.2, hJ.2.1⟩

/-- Young integration for continuous paths of complementary finite variation exponents. -/
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
  have hstep : youngIncrement X Y = YoungLoeve.youngStep X Y := by
    funext s t
    rfl
  simpa [← hstep] using YoungLoeve.young_integral hab hp hq hpq X Y hX hY hVp hVq

end CKMA
