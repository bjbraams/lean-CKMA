/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.RoughPath.Sewing.YoungGrid
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Young integral from complementary finite variation

Uniform partition sums of a Young increment are Cauchy when the paths are
continuous and have complementary finite `p`- and `q`-variation. The limit is
additive and continuous, and the Young–Loeve remainder is
`sewingConstant (p⁻¹ + q⁻¹)` times the product of the variation moduli. The data
`YoungData`, `youngGrid`, and `youngLimit` are defined in
`CKMA.Analysis.RoughPath.Sewing.YoungGrid`.

## Main results

* `CKMA.YoungLoeve.norm_youngLimit_sharp`: sharp Young–Loeve defect estimate with
  `sewingConstant (p⁻¹ + q⁻¹)`.
* `CKMA.YoungLoeve.young_integral` (**09.21**, variation form): existence and uniqueness of the
  Young integral of complementary finite-variation paths.
-/

@[expose] public section

noncomputable section

namespace CKMA

namespace YoungLoeve

open scoped BigOperators NNReal ENNReal
open Finset Filter Topology Metric Sewing

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable [D : YoungData E F]

/-- The Young control vanishes on a degenerate interval `[s, s]`. -/
lemma youngCtrl_same (s : ℝ) : youngCtrl p q youngLeftPath youngRightPath s s = 0 := by
  rw [youngCtrl, variationReal_point (lt_of_lt_of_le zero_lt_one one_le_leftExponent)
      youngLeftPath s,
    variationReal_point (lt_of_lt_of_le zero_lt_one one_le_rightExponent) youngRightPath s,
    Real.zero_rpow (youngAlpha_pos one_le_leftExponent one_lt_inv_add_inv).ne',
    Real.zero_rpow (youngBeta_pos one_le_rightExponent one_lt_inv_add_inv).ne', zero_mul]

/-- The Young control is continuous in its right endpoint on `[s, b]`. -/
lemma continuousOn_ctrl_right {s : ℝ} (hs : a ≤ s) (_hsb : s ≤ b) :
    ContinuousOn (fun r => youngCtrl p q youngLeftPath youngRightPath s r) (Set.Icc s b) := by
  have hXs : ContinuousOn youngLeftPath (Set.Icc s b) :=
    continuousOn_youngLeftPath.mono (Set.Icc_subset_Icc hs le_rfl)
  have hYs : ContinuousOn youngRightPath (Set.Icc s b) :=
    continuousOn_youngRightPath.mono (Set.Icc_subset_Icc hs le_rfl)
  have hfinX : pathVariationPower p youngLeftPath s b ≠ ∞ :=
    ne_top_of_le_ne_top leftPathVariation_ne_top (pathVariationPower_mono hs le_rfl p youngLeftPath)
  have hfinY : pathVariationPower q youngRightPath s b ≠ ∞ :=
    ne_top_of_le_ne_top rightPathVariation_ne_top
      (pathVariationPower_mono hs le_rfl q youngRightPath)
  have hvX := (continuousOn_variationReal one_le_leftExponent youngLeftPath hXs hfinX).rpow_const
    (fun _ _ => Or.inr (youngAlpha_pos one_le_leftExponent one_lt_inv_add_inv).le)
  have hvY := (continuousOn_variationReal one_le_rightExponent youngRightPath hYs hfinY).rpow_const
    (fun _ _ => Or.inr (youngBeta_pos one_le_rightExponent one_lt_inv_add_inv).le)
  refine (hvX.mul hvY).congr fun r _ => ?_
  simp [youngCtrl, Pi.mul_apply]

/-- Doubling `2 ^ (-θ)` gives `2 ^ (1 - θ)`. -/
lemma two_rpow_neg (θ : ℝ) : (2 : ℝ) * (2 : ℝ) ^ (-θ) = (2 : ℝ) ^ (1 - θ) := by
  have h2 : (2 : ℝ) ^ (1 : ℝ) = 2 := Real.rpow_one _
  calc
    (2 : ℝ) * (2 : ℝ) ^ (-θ) = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-θ) := by
      conv_lhs => arg 1; rw [← h2]
    _ = (2 : ℝ) ^ ((1 : ℝ) + -θ) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2) (1 : ℝ) (-θ)]
    _ = (2 : ℝ) ^ (1 - θ) := by
      congr 1

/-- Fixed-point relation for the geometric sewing constant. -/
lemma sewingConstant_shift {θ : ℝ} (hθ : 1 < θ) :
    sewingConstant θ * (2 : ℝ) ^ (1 - θ) + 1 = sewingConstant θ := by
  have hr := Sewing.sewingRatio_mem hθ
  have hne : (1 : ℝ) - (2 : ℝ) ^ (1 - θ) ≠ 0 := (sub_ne_zero.mpr (ne_of_lt hr.2).symm)
  rw [sewingConstant]
  field_simp [hne]
  ring

/-- Removing one medial point upgrades the loose bound to the sewing constant. -/
lemma norm_defect_iterate {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (n : ℕ) :
    ‖youngLimit s t - youngStep youngLeftPath youngRightPath s t‖ ≤
      sewingConstant (youngTheta p q) * youngModulus p q youngLeftPath youngRightPath s t +
        ((2 : ℝ) ^ (1 - youngTheta p q)) ^ n * youngLoose (youngTheta p q) *
          youngModulus p q youngLeftPath youngRightPath s t := by
  induction n generalizing s t with
  | zero =>
    have hloose := norm_youngLimit_sub hs hst ht
    have hκ : 0 ≤ sewingConstant (youngTheta p q) :=
      (Sewing.sewingConstant_pos (by simpa [youngTheta] using one_lt_inv_add_inv)).le
    rw [pow_zero, one_mul]
    exact hloose.trans (le_add_of_nonneg_left
      (mul_nonneg hκ (youngModulus_nonneg youngLeftPath youngRightPath s t)))
  | succ n ih =>
    rcases eq_or_lt_of_le (youngCtrl_nonneg youngLeftPath youngRightPath s t) with hzero | hpos
    · have hmod0 : youngModulus p q youngLeftPath youngRightPath s t = 0 := by
        rw [youngModulus_eq_ctrl_pow one_le_leftExponent one_le_rightExponent one_lt_inv_add_inv
            youngLeftPath youngRightPath s t, hzero.symm,
          Real.zero_rpow (youngTheta_pos one_lt_inv_add_inv).ne']
      have hloose := norm_youngLimit_sub hs hst ht
      rw [hmod0, mul_zero] at hloose
      simpa [hmod0, mul_zero, add_zero] using hloose
    · have hcont := continuousOn_ctrl_right hs (hst.trans ht)
      have hhalf : youngCtrl p q youngLeftPath youngRightPath s t / 2 ∈
          Set.Icc (youngCtrl p q youngLeftPath youngRightPath s s)
            (youngCtrl p q youngLeftPath youngRightPath s t) := by
        rw [youngCtrl_same s]
        exact ⟨div_nonneg (youngCtrl_nonneg youngLeftPath youngRightPath s t) (by norm_num),
          half_le_self (youngCtrl_nonneg youngLeftPath youngRightPath s t)⟩
      obtain ⟨m, hm, hfm⟩ :=
        (intermediate_value_Icc hst (hcont.mono (Set.Icc_subset_Icc le_rfl ht))) hhalf
      have hsm : youngCtrl p q youngLeftPath youngRightPath s m =
          youngCtrl p q youngLeftPath youngRightPath s t / 2 := hfm
      have hfinX : pathVariationPower p youngLeftPath s t ≠ ∞ :=
        ne_top_of_le_ne_top leftPathVariation_ne_top
          (pathVariationPower_mono hs ht p youngLeftPath)
      have hfinY : pathVariationPower q youngRightPath s t ≠ ∞ :=
        ne_top_of_le_ne_top rightPathVariation_ne_top
          (pathVariationPower_mono hs ht q youngRightPath)
      have hsuper := youngCtrl_superadd hm.1 hm.2 one_le_leftExponent one_le_rightExponent
        one_lt_inv_add_inv youngLeftPath youngRightPath hfinX hfinY
      have hright : youngCtrl p q youngLeftPath youngRightPath m t ≤
          youngCtrl p q youngLeftPath youngRightPath s t / 2 := by
        rw [hsm] at hsuper
        linarith
      have hρL : youngModulus p q youngLeftPath youngRightPath s m =
          (2 : ℝ) ^ (-youngTheta p q) * youngModulus p q youngLeftPath youngRightPath s t := by
        rw [youngModulus_eq_ctrl_pow one_le_leftExponent one_le_rightExponent one_lt_inv_add_inv
            youngLeftPath youngRightPath s m, hsm,
          youngModulus_eq_ctrl_pow one_le_leftExponent one_le_rightExponent one_lt_inv_add_inv
            youngLeftPath youngRightPath s t,
          Real.div_rpow (youngCtrl_nonneg youngLeftPath youngRightPath s t)
            (by norm_num : (0 : ℝ) ≤ 2),
          div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        exact mul_comm _ _
      have hρR : youngModulus p q youngLeftPath youngRightPath m t ≤
          (2 : ℝ) ^ (-youngTheta p q) * youngModulus p q youngLeftPath youngRightPath s t := by
        rw [youngModulus_eq_ctrl_pow one_le_leftExponent one_le_rightExponent one_lt_inv_add_inv
            youngLeftPath youngRightPath m t,
          youngModulus_eq_ctrl_pow one_le_leftExponent one_le_rightExponent one_lt_inv_add_inv
            youngLeftPath youngRightPath s t]
        have hle := Real.rpow_le_rpow (youngCtrl_nonneg youngLeftPath youngRightPath m t) hright
          (youngTheta_pos one_lt_inv_add_inv).le
        rw [Real.div_rpow (youngCtrl_nonneg youngLeftPath youngRightPath s t)
            (by norm_num : (0 : ℝ) ≤ 2),
          div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          mul_comm (youngCtrl p q youngLeftPath youngRightPath s t ^ youngTheta p q)] at hle
        exact hle
      set ρ : ℝ := youngModulus p q youngLeftPath youngRightPath s t
      set r : ℝ := (2 : ℝ) ^ (1 - youngTheta p q)
      set Λ : ℝ := youngLoose (youngTheta p q)
      set κ : ℝ := sewingConstant (youngTheta p q)
      have hadd := youngLimit_add hs hm.1 hm.2 ht
      have hAlg : youngLimit s t - youngStep youngLeftPath youngRightPath s t =
          (youngLimit s m - youngStep youngLeftPath youngRightPath s m) +
            (youngLimit m t - youngStep youngLeftPath youngRightPath m t) +
            (youngStep youngLeftPath youngRightPath s m +
              youngStep youngLeftPath youngRightPath m t -
              youngStep youngLeftPath youngRightPath s t) := by
        rw [hadd]
        abel
      have hδ := norm_young_defect hm.1 hm.2 one_le_leftExponent one_le_rightExponent
        youngLeftPath youngRightPath hfinX hfinY
      have ihL := ih hs hm.1 (hm.2.trans ht)
      have ihR := ih (hs.trans hm.1) hm.2 ht
      have hsumρ : youngModulus p q youngLeftPath youngRightPath s m +
          youngModulus p q youngLeftPath youngRightPath m t ≤ r * ρ := by
        calc
          youngModulus p q youngLeftPath youngRightPath s m +
              youngModulus p q youngLeftPath youngRightPath m t ≤
              (2 : ℝ) ^ (-youngTheta p q) * ρ + (2 : ℝ) ^ (-youngTheta p q) * ρ := by
            rw [hρL]; exact add_le_add le_rfl hρR
          _ = ((2 : ℝ) * (2 : ℝ) ^ (-youngTheta p q)) * ρ := by ring
          _ = r * ρ := by rw [two_rpow_neg]
      have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
      have hΛ0 : 0 ≤ Λ := youngLoose_nonneg (by simpa [youngTheta] using one_lt_inv_add_inv)
      have hκ0 : 0 ≤ κ :=
        (Sewing.sewingConstant_pos (by simpa [youngTheta] using one_lt_inv_add_inv)).le
      have hcoef : 0 ≤ κ + r ^ n * Λ :=
        add_nonneg hκ0 (mul_nonneg (pow_nonneg hr0 n) hΛ0)
      have hmul := mul_le_mul_of_nonneg_left hsumρ hcoef
      have hthree : ‖youngLimit s t - youngStep youngLeftPath youngRightPath s t‖ ≤
          ‖youngLimit s m - youngStep youngLeftPath youngRightPath s m‖ +
            ‖youngLimit m t - youngStep youngLeftPath youngRightPath m t‖ + ρ := by
        simp only [ρ]
        rw [hAlg]
        refine (norm_add_le _ _).trans ?_
        refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
        exact add_le_add le_rfl hδ
      have hbound : ‖youngLimit s t - youngStep youngLeftPath youngRightPath s t‖ ≤
          (κ + r ^ n * Λ) * (r * ρ) + ρ := by
        calc
          ‖youngLimit s t - youngStep youngLeftPath youngRightPath s t‖ ≤
              ‖youngLimit s m - youngStep youngLeftPath youngRightPath s m‖ +
                ‖youngLimit m t - youngStep youngLeftPath youngRightPath m t‖ + ρ := hthree
          _ ≤ (κ * youngModulus p q youngLeftPath youngRightPath s m +
                r ^ n * Λ * youngModulus p q youngLeftPath youngRightPath s m) +
                (κ * youngModulus p q youngLeftPath youngRightPath m t +
                  r ^ n * Λ * youngModulus p q youngLeftPath youngRightPath m t) + ρ :=
            add_le_add (add_le_add ihL ihR) le_rfl
          _ = (κ + r ^ n * Λ) * (youngModulus p q youngLeftPath youngRightPath s m +
                youngModulus p q youngLeftPath youngRightPath m t) + ρ := by
            ring
          _ ≤ (κ + r ^ n * Λ) * (r * ρ) + ρ := add_le_add hmul le_rfl
      have hsew := sewingConstant_shift (by simpa [youngTheta] using one_lt_inv_add_inv)
      have hrκ : κ * r + 1 = κ := by simpa [κ, r, youngTheta] using hsew
      calc
        ‖youngLimit s t - youngStep youngLeftPath youngRightPath s t‖ ≤
            (κ + r ^ n * Λ) * (r * ρ) + ρ := hbound
        _ = κ * r * ρ + r ^ n * r * Λ * ρ + ρ := by ring
        _ = (κ * r + 1) * ρ + (r ^ n * r) * Λ * ρ := by ring
        _ = κ * ρ + r ^ (n + 1) * Λ * ρ := by rw [← pow_succ, hrκ]

/-- Sharp Young–Loeve remainder bound with `sewingConstant (p⁻¹ + q⁻¹)`. -/
lemma norm_youngLimit_sharp {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    ‖youngLimit s t - youngStep youngLeftPath youngRightPath s t‖ ≤
      sewingConstant (p⁻¹ + q⁻¹) * (pathVariationPower p youngLeftPath s t).toReal ^ p⁻¹ *
        (pathVariationPower q youngRightPath s t).toReal ^ q⁻¹ := by
  have hr := Sewing.sewingRatio_mem (by simpa [youngTheta] using one_lt_inv_add_inv)
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr.1 hr.2
  set ρ : ℝ := youngModulus p q youngLeftPath youngRightPath s t
  set κ : ℝ := sewingConstant (youngTheta p q)
  set Λ : ℝ := youngLoose (youngTheta p q)
  set r : ℝ := (2 : ℝ) ^ (1 - youngTheta p q)
  have hstep : ∀ n, ‖youngLimit s t - youngStep youngLeftPath youngRightPath s t‖ ≤
      κ * ρ + r ^ n * Λ * ρ :=
    fun n => norm_defect_iterate hs hst ht n
  have hlim : ‖youngLimit s t - youngStep youngLeftPath youngRightPath s t‖ ≤ κ * ρ := by
    have htend : Tendsto (fun n : ℕ => κ * ρ + r ^ n * Λ * ρ) atTop (𝓝 (κ * ρ)) := by
      have hzero : Tendsto (fun n : ℕ => r ^ n * (Λ * ρ)) atTop (𝓝 0) := by
        have hrθ : r = (2 : ℝ) ^ (1 - (p⁻¹ + q⁻¹)) := by simp [r, youngTheta]
        rw [hrθ]
        simpa [zero_mul] using hpow.mul_const (Λ * ρ)
      have hfun : (fun n : ℕ => κ * ρ + r ^ n * Λ * ρ) =
          fun n => κ * ρ + r ^ n * (Λ * ρ) := by
        funext n; ring
      simpa [hfun] using tendsto_const_nhds.add hzero
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds htend hstep
  have hassoc : κ * ρ =
      sewingConstant (p⁻¹ + q⁻¹) * (pathVariationPower p youngLeftPath s t).toReal ^ p⁻¹ *
        (pathVariationPower q youngRightPath s t).toReal ^ q⁻¹ := by
    simp [κ, ρ, youngModulus, variationReal, youngTheta, mul_assoc]
  simpa [hassoc] using hlim

/-- The Young limit telescopes along any monotone sequence of nodes in `[a, b]`. -/
lemma youngLimit_seq (n : ℕ) (c : ℕ → ℝ) (hc : Monotone c) (h0 : a ≤ c 0) (hn : c n ≤ b) :
    youngLimit (c 0) (c n) = ∑ i ∈ range n, youngLimit (c i) (c (i + 1)) := by
  induction n with
  | zero =>
    simp
    exact youngLimit_same h0 hn
  | succ n ih =>
    rw [sum_range_succ]
    have hstep : c n ≤ c (n + 1) := hc (Nat.le_succ n)
    have hmid : c 0 ≤ c n := hc (Nat.zero_le n)
    rw [youngLimit_add h0 hmid hstep hn, ih (hstep.trans hn)]

/-- The Young limit equals the sum of its increments across any ordered partition. -/
lemma youngLimit_nodes {s t : ℝ} (hs : a ≤ s) (ht : t ≤ b) (π : OrderedIntervalPartition s t) :
    youngLimit s t =
      ∑ i : Fin π.size, youngLimit (π.node i.castSucc) (π.node i.succ) := by
  have hseq := youngLimit_seq π.size (nodeSeq π) (monotone_nodeSeq π)
    (by simpa [nodeSeq_zero] using hs) (by simpa [nodeSeq_size] using ht)
  rw [nodeSeq_zero, nodeSeq_size] at hseq
  have hterm : ∀ i : Fin π.size,
      youngLimit (π.node i.castSucc) (π.node i.succ) =
        youngLimit (nodeSeq π (i : ℕ)) (nodeSeq π ((i : ℕ) + 1)) := by
    intro i
    have hi : (i : ℕ) ≤ π.size := le_of_lt i.isLt
    have hi1 : (i : ℕ) + 1 ≤ π.size := Nat.succ_le_of_lt i.isLt
    have hs' : i.succ = ⟨(i : ℕ) + 1, by omega⟩ := by ext; simp [Fin.val_succ]
    have hc : i.castSucc = ⟨(i : ℕ), by omega⟩ := by ext; simp [Fin.val_castSucc]
    simp [hs', hc, nodeSeq_of_le, hi, hi1]
  rw [Finset.sum_congr rfl fun i _ => hterm i,
    Fin.sum_univ_eq_sum_range
      (fun i => youngLimit (nodeSeq π i) (nodeSeq π (i + 1))) π.size, hseq]

/-- Each partition step is bounded by the partition mesh. -/
lemma partition_step_le_mesh {s t : ℝ} (π : OrderedIntervalPartition s t) (i : Fin π.size) :
    π.node i.succ - π.node i.castSucc ≤ (π.mesh : ℝ) := by
  have hxy : π.node i.castSucc ≤ π.node i.succ :=
    π.monotone_node (Fin.castSucc_le_succ i)
  have hΔ : 0 ≤ π.node i.succ - π.node i.castSucc := sub_nonneg.mpr hxy
  let fmesh : Fin π.size → ℝ≥0 := fun j =>
    (π.node j.succ - π.node j.castSucc).toNNReal
  have hsup : fmesh i ≤ Finset.univ.sup fmesh := Finset.le_sup (Finset.mem_univ i)
  have hcoe : (fmesh i : ℝ) ≤ (π.mesh : ℝ) := by
    unfold OrderedIntervalPartition.mesh
    exact NNReal.coe_le_coe.mpr hsup
  have hcoe' : (fmesh i : ℝ) = π.node i.succ - π.node i.castSucc := by
    simp [fmesh, Real.coe_toNNReal', max_eq_left hΔ]
  linarith [hcoe, hcoe']

/-- Partition sums approach the additive Young limit once the mesh is small. -/
lemma exists_partition_close {s t : ℝ} (hs : a ≤ s) (_hst : s ≤ t) (ht : t ≤ b) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ π : OrderedIntervalPartition s t, (π.mesh : ℝ) < δ →
      ‖π.incrementSum (youngStep youngLeftPath youngRightPath) - youngLimit s t‖ < ε := by
  have hθ : 1 < youngTheta p q := by simpa [youngTheta] using one_lt_inv_add_inv
  have hθ1 : 0 < youngTheta p q - 1 := sub_pos.mpr hθ
  set κ : ℝ := sewingConstant (youngTheta p q)
  set Ω : ℝ := youngCtrl p q youngLeftPath youngRightPath s t
  have hκ : 0 ≤ κ := (Sewing.sewingConstant_pos hθ).le
  have hΩ : 0 ≤ Ω := youngCtrl_nonneg youngLeftPath youngRightPath s t
  set C : ℝ := κ * Ω
  set τ : ℝ := ε / (2 * (C + 1))
  have hτ : 0 < τ := div_pos hε (mul_pos (by norm_num) (by linarith [mul_nonneg hκ hΩ]))
  set η : ℝ := τ ^ (youngTheta p q - 1)⁻¹
  have hη : 0 < η := Real.rpow_pos_of_pos hτ _
  have hηpow : η ^ (youngTheta p q - 1) = τ := by
    rw [← Real.rpow_mul hτ.le]
    have hinv : (youngTheta p q - 1)⁻¹ * (youngTheta p q - 1) = 1 := by
      field_simp [hθ1.ne']
    rw [hinv, Real.rpow_one]
  have hτle : C * τ ≤ ε / 2 := by
    simp only [τ]
    rw [mul_div, div_le_iff₀ (by linarith [mul_nonneg hκ hΩ] : (0 : ℝ) < 2 * (C + 1))]
    have hclear : ε / 2 * (2 * (C + 1)) = ε * (C + 1) := by ring
    rw [hclear]
    linarith [hε]
  obtain ⟨δ, hδ, hδc⟩ := exists_ctrl_short one_le_leftExponent one_le_rightExponent
    one_lt_inv_add_inv youngLeftPath youngRightPath continuousOn_youngLeftPath
    continuousOn_youngRightPath leftPathVariation_ne_top rightPathVariation_ne_top η hη
  refine ⟨δ, hδ, fun π hmesh => ?_⟩
  rw [youngLimit_nodes hs ht π, OrderedIntervalPartition.incrementSum, ← sum_sub_distrib]
  refine lt_of_le_of_lt ((norm_sum_le _ _).trans ?_) (by linarith : ε / 2 < ε)
  have hpiece : ∀ i : Fin π.size,
      ‖youngStep youngLeftPath youngRightPath (π.node i.castSucc) (π.node i.succ) -
        youngLimit (π.node i.castSucc) (π.node i.succ)‖ ≤
        κ * η ^ (youngTheta p q - 1) *
          youngCtrl p q youngLeftPath youngRightPath (π.node i.castSucc) (π.node i.succ) := by
    intro i
    have hxy : π.node i.castSucc ≤ π.node i.succ :=
      π.monotone_node (Fin.castSucc_le_succ i)
    have hx : a ≤ π.node i.castSucc := by
      have h0 : s ≤ π.node i.castSucc := by
        simpa [π.node_zero] using π.monotone_node (Fin.zero_le i.castSucc)
      exact le_trans hs h0
    have hy : π.node i.succ ≤ b := by
      have hlast : π.node i.succ ≤ π.node (Fin.last π.size) := π.monotone_node (Fin.le_last _)
      exact hlast.trans (by simpa [π.node_last] using ht)
    have hlen : π.node i.succ - π.node i.castSucc < δ :=
      lt_of_le_of_lt (partition_step_le_mesh π i) hmesh
    have hctrl := hδc _ _ hx hxy hy hlen
    have hsharp := norm_youngLimit_sharp hx hxy hy
    rw [norm_sub_rev]
    have hmod : youngModulus p q youngLeftPath youngRightPath (π.node i.castSucc) (π.node i.succ) ≤
        η ^ (youngTheta p q - 1) *
          youngCtrl p q youngLeftPath youngRightPath (π.node i.castSucc) (π.node i.succ) :=
      youngModulus_le_eta hη.le hctrl
    have hκmod : sewingConstant (p⁻¹ + q⁻¹) *
        (pathVariationPower p youngLeftPath (π.node i.castSucc) (π.node i.succ)).toReal ^ p⁻¹ *
        (pathVariationPower q youngRightPath (π.node i.castSucc) (π.node i.succ)).toReal ^ q⁻¹ =
        κ * youngModulus p q youngLeftPath youngRightPath (π.node i.castSucc) (π.node i.succ) := by
      simp [κ, youngModulus, variationReal, youngTheta, mul_assoc]
    exact (hsharp.trans (le_of_eq hκmod)).trans
      (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hmod hκ)
  refine (sum_le_sum fun i _ => hpiece i).trans ?_
  rw [← mul_sum]
  have hmon : Monotone (nodeSeq π) := monotone_nodeSeq π
  have hctrl := ctrl_sum_seq π.size (nodeSeq π) hmon
    (by simpa [nodeSeq_zero] using hs) (by simpa [nodeSeq_size] using ht)
  have hfin : ∑ i : Fin π.size,
      youngCtrl p q youngLeftPath youngRightPath (π.node i.castSucc) (π.node i.succ) ≤ Ω := by
    have hterm : ∀ i : Fin π.size,
        youngCtrl p q youngLeftPath youngRightPath (π.node i.castSucc) (π.node i.succ) =
          youngCtrl p q youngLeftPath youngRightPath (nodeSeq π (i : ℕ))
            (nodeSeq π ((i : ℕ) + 1)) := by
      intro i
      have hi : (i : ℕ) ≤ π.size := le_of_lt i.isLt
      have hi1 : (i : ℕ) + 1 ≤ π.size := Nat.succ_le_of_lt i.isLt
      have hs' : i.succ = ⟨(i : ℕ) + 1, by omega⟩ := by ext; simp [Fin.val_succ]
      have hc : i.castSucc = ⟨(i : ℕ), by omega⟩ := by ext; simp [Fin.val_castSucc]
      simp [hs', hc, nodeSeq_of_le, hi, hi1]
    rw [Finset.sum_congr rfl fun i _ => hterm i,
      Fin.sum_univ_eq_sum_range
        (fun i => youngCtrl p q youngLeftPath youngRightPath (nodeSeq π i)
          (nodeSeq π (i + 1))) π.size]
    simpa [Ω, nodeSeq_zero, nodeSeq_size] using hctrl
  have hC : κ * η ^ (youngTheta p q - 1) * Ω ≤ ε / 2 := by
    calc
      κ * η ^ (youngTheta p q - 1) * Ω = κ * τ * Ω := by rw [hηpow]
      _ = C * τ := by simp only [C]; ring
      _ ≤ ε / 2 := hτle
  exact (mul_le_mul_of_nonneg_left hfin
    (mul_nonneg hκ (Real.rpow_nonneg hη.le _))).trans hC

omit [YoungData E F] in
/-- **09.21**, variation form: the Young integral of complementary finite-variation paths. -/
theorem young_integral {a b p q : ℝ} (hab : a ≤ b) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : 1 < p⁻¹ + q⁻¹) (X : ℝ → E) (Y : ℝ → E →L[ℝ] F)
    (hX : ContinuousOn X (Set.Icc a b)) (hY : ContinuousOn Y (Set.Icc a b))
    (hVp : pathVariationPower p X a b ≠ ∞) (hVq : pathVariationPower q Y a b ≠ ∞) :
    ∃! I : C(Set.Icc a b, F), IsLeftNormalized I ∧
      HasPartitionSumLimit (youngStep X Y) I ∧
      ∀ s t : Set.Icc a b, s.val ≤ t.val →
        ‖(I t - I s) - youngStep X Y s.val t.val‖ ≤
          sewingConstant (p⁻¹ + q⁻¹) *
            (pathVariationPower p X s.val t.val).toReal ^ p⁻¹ *
            (pathVariationPower q Y s.val t.val).toReal ^ q⁻¹ := by
  letI : YoungData E F :=
    ⟨a, b, p, q, hab, hp, hq, hpq, X, Y, hX, hY, hVp, hVq⟩
  let g : Set.Icc a b → ℝ × ℝ := fun x => (a, x.val)
  have hg : Continuous g := continuous_const.prodMk continuous_subtype_val
  have hcomp : Continuous ((fun p : ℝ × ℝ => youngLimit p.1 p.2) ∘ g) :=
    continuousOn_youngLimit.comp_continuous hg fun x => ⟨le_rfl, x.2.1, x.2.2⟩
  have hfun : (fun p : ℝ × ℝ => youngLimit p.1 p.2) ∘ g = fun x => youngLimit a x.val := by
    funext x; rfl
  let I : C(Set.Icc a b, F) := ⟨fun x => youngLimit a x.val, hfun ▸ hcomp⟩
  have hinc : ∀ {s t : Set.Icc a b}, s.val ≤ t.val →
      I t - I s = youngLimit s.val t.val := by
    intro s t hst
    have hadd : youngLimit a t.val = youngLimit a s.val + youngLimit s.val t.val :=
      youngLimit_add le_rfl s.2.1 hst t.2.2
    change youngLimit a t.val - youngLimit a s.val = youngLimit s.val t.val
    rw [hadd]
    abel
  have hleft : IsLeftNormalized I := by
    intro x hx
    change youngLimit a x.val = 0
    rw [hx]
    exact youngLimit_same le_rfl hab
  have hlim : HasPartitionSumLimit (youngStep X Y) I := by
    intro s t hst ε hε
    obtain ⟨δ, hδ, hδπ⟩ := exists_partition_close s.2.1 hst t.2.2 ε hε
    refine ⟨δ, hδ, fun π hmesh => ?_⟩
    rw [hinc hst]
    exact hδπ π hmesh
  refine ⟨I, ⟨⟨hleft, hlim, ?_⟩, ?_⟩⟩
  · intro s t hst
    rw [hinc hst]
    exact norm_youngLimit_sharp s.2.1 hst t.2.2
  · intro J hJ
    apply ContinuousMap.ext
    intro x
    let a0 : Set.Icc a b := ⟨a, ⟨le_rfl, hab⟩⟩
    have hI0 := hleft a0 rfl
    have hJ0 := hJ.1 a0 rfl
    have hEq := Sewing.partitionLimit_unique x.2.1 (hlim a0 x x.2.1) (hJ.2.1 a0 x x.2.1)
    simpa [hI0, hJ0] using hEq.symm

end YoungLoeve

end CKMA
