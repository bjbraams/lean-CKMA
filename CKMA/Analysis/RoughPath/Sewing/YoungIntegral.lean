/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.RoughPath.Sewing.YoungGrid
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Young integral from complementary finite variation

Uniform partition sums of a Young increment are Cauchy when the paths are
continuous and have complementary finite `p`- and `q`-variation. The limit is
additive and continuous, and the Young–Loeve remainder is
`sewingConstant (p⁻¹ + q⁻¹)` times the product of the variation moduli. The data
`YoungData`, `YoungData.youngGrid`, and `YoungData.youngLimit` are defined in
`CKMA.Analysis.RoughPath.Sewing.YoungGrid`; the resulting existence and uniqueness
theorem is `CKMA.young_variation` in `CKMA.Analysis.RoughPath.Sewing`.

## Main results

* `CKMA.YoungLoeve.YoungData.norm_youngLimit_sharp`: sharp Young–Loeve defect estimate with
  `sewingConstant (p⁻¹ + q⁻¹)`.
* `CKMA.YoungLoeve.YoungData.exists_partition_close`: partition sums of small mesh approach
  the Young limit.

## References

* [P. K. Friz and M. Hairer, *A Course on Rough Paths*][frizhairer2020]
-/

public section

noncomputable section

namespace CKMA

namespace YoungLoeve

open scoped BigOperators NNReal ENNReal
open Finset Filter Topology Metric Sewing

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
namespace YoungData

variable {D : YoungData E F}

omit [CompleteSpace F] in
/-- The Young control vanishes on a degenerate interval `[s, s]`. -/
private lemma youngCtrl_same (s : ℝ) : youngCtrl D.p D.q D.X D.Y s s = 0 := by
  rw [youngCtrl, variationReal_point (lt_of_lt_of_le zero_lt_one D.one_le_p)
      D.X s,
    variationReal_point (lt_of_lt_of_le zero_lt_one D.one_le_q) D.Y s,
    Real.zero_rpow (youngAlpha_pos D.one_le_p D.one_lt_inv_add_inv).ne',
    Real.zero_rpow (youngBeta_pos D.one_le_q D.one_lt_inv_add_inv).ne', zero_mul]

omit [CompleteSpace F] in
/-- The Young control is continuous in its right endpoint on `[s, b]`. -/
private lemma continuousOn_ctrl_right {s : ℝ} (hs : D.a ≤ s) :
    ContinuousOn (fun r => youngCtrl D.p D.q D.X D.Y s r) (Set.Icc s D.b) := by
  have hXs : ContinuousOn D.X (Set.Icc s D.b) :=
    D.continuousOn_X.mono (Set.Icc_subset_Icc hs le_rfl)
  have hYs : ContinuousOn D.Y (Set.Icc s D.b) :=
    D.continuousOn_Y.mono (Set.Icc_subset_Icc hs le_rfl)
  have hfinX : pathVariationPower D.p D.X s D.b ≠ ∞ :=
    ne_top_of_le_ne_top D.pathVariationPower_X_ne_top (pathVariationPower_mono hs le_rfl D.p D.X)
  have hfinY : pathVariationPower D.q D.Y s D.b ≠ ∞ :=
    ne_top_of_le_ne_top D.pathVariationPower_Y_ne_top
      (pathVariationPower_mono hs le_rfl D.q D.Y)
  have hvX := (continuousOn_variationReal D.one_le_p D.X hXs hfinX).rpow_const
    (fun _ _ => Or.inr (youngAlpha_pos D.one_le_p D.one_lt_inv_add_inv).le)
  have hvY := (continuousOn_variationReal D.one_le_q D.Y hYs hfinY).rpow_const
    (fun _ _ => Or.inr (youngBeta_pos D.one_le_q D.one_lt_inv_add_inv).le)
  refine (hvX.mul hvY).congr fun r _ => ?_
  simp [youngCtrl, Pi.mul_apply]

/-- Fixed-point relation for the geometric sewing constant. -/
private lemma sewingConstant_shift {θ : ℝ} (hθ : 1 < θ) :
    sewingConstant θ * (2 : ℝ) ^ (1 - θ) + 1 = sewingConstant θ := by
  have hr := sewingRatio_mem hθ
  have hne : (1 : ℝ) - (2 : ℝ) ^ (1 - θ) ≠ 0 := (sub_ne_zero.mpr (ne_of_lt hr.2).symm)
  rw [sewingConstant]
  field_simp [hne]
  ring

/-- Removing one medial point upgrades the loose bound to the sewing constant. -/
private lemma norm_defect_iterate {s t : ℝ} (hs : D.a ≤ s) (hst : s ≤ t) (ht : t ≤ D.b) (n : ℕ) :
    ‖D.youngLimit s t - youngIncrement D.X D.Y s t‖ ≤
      sewingConstant (youngTheta D.p D.q) * youngModulus D.p D.q D.X D.Y s t +
        ((2 : ℝ) ^ (1 - youngTheta D.p D.q)) ^ n * youngLoose (youngTheta D.p D.q) *
          youngModulus D.p D.q D.X D.Y s t := by
  induction n generalizing s t with
  | zero =>
    have hloose := norm_youngLimit_sub hs hst ht
    have hκ : 0 ≤ sewingConstant (youngTheta D.p D.q) :=
      (sewingConstant_pos (by simpa [youngTheta] using D.one_lt_inv_add_inv)).le
    rw [pow_zero, one_mul]
    exact hloose.trans (le_add_of_nonneg_left
      (mul_nonneg hκ (youngModulus_nonneg D.X D.Y s t)))
  | succ n ih =>
    rcases eq_or_lt_of_le (youngCtrl_nonneg D.X D.Y s t) with hzero | hpos
    · have hmod0 : youngModulus D.p D.q D.X D.Y s t = 0 := by
        rw [youngModulus_eq_ctrl_pow D.one_le_p D.one_le_q D.one_lt_inv_add_inv
            D.X D.Y s t, hzero.symm,
          Real.zero_rpow (youngTheta_pos D.one_lt_inv_add_inv).ne']
      have hloose := norm_youngLimit_sub hs hst ht
      rw [hmod0, mul_zero] at hloose
      simpa [hmod0, mul_zero, add_zero] using hloose
    · have hcont := continuousOn_ctrl_right hs
      have hhalf : youngCtrl D.p D.q D.X D.Y s t / 2 ∈
          Set.Icc (youngCtrl D.p D.q D.X D.Y s s)
            (youngCtrl D.p D.q D.X D.Y s t) := by
        rw [youngCtrl_same s]
        exact ⟨div_nonneg (youngCtrl_nonneg D.X D.Y s t) (by norm_num),
          half_le_self (youngCtrl_nonneg D.X D.Y s t)⟩
      obtain ⟨m, hm, hfm⟩ :=
        (intermediate_value_Icc hst (hcont.mono (Set.Icc_subset_Icc le_rfl ht))) hhalf
      have hsm : youngCtrl D.p D.q D.X D.Y s m =
          youngCtrl D.p D.q D.X D.Y s t / 2 := hfm
      have hfinX : pathVariationPower D.p D.X s t ≠ ∞ :=
        ne_top_of_le_ne_top D.pathVariationPower_X_ne_top
          (pathVariationPower_mono hs ht D.p D.X)
      have hfinY : pathVariationPower D.q D.Y s t ≠ ∞ :=
        ne_top_of_le_ne_top D.pathVariationPower_Y_ne_top
          (pathVariationPower_mono hs ht D.q D.Y)
      have hsuper := youngCtrl_superadd hm.1 hm.2 D.one_le_p D.one_le_q
        D.one_lt_inv_add_inv D.X D.Y hfinX hfinY
      have hright : youngCtrl D.p D.q D.X D.Y m t ≤
          youngCtrl D.p D.q D.X D.Y s t / 2 := by
        rw [hsm] at hsuper
        linarith
      have hρL : youngModulus D.p D.q D.X D.Y s m =
          (2 : ℝ) ^ (-youngTheta D.p D.q) * youngModulus D.p D.q D.X D.Y s t := by
        rw [youngModulus_eq_ctrl_pow D.one_le_p D.one_le_q D.one_lt_inv_add_inv
            D.X D.Y s m, hsm,
          youngModulus_eq_ctrl_pow D.one_le_p D.one_le_q D.one_lt_inv_add_inv
            D.X D.Y s t,
          Real.div_rpow (youngCtrl_nonneg D.X D.Y s t)
            (by norm_num : (0 : ℝ) ≤ 2),
          div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        exact mul_comm _ _
      have hρR : youngModulus D.p D.q D.X D.Y m t ≤
          (2 : ℝ) ^ (-youngTheta D.p D.q) * youngModulus D.p D.q D.X D.Y s t := by
        rw [youngModulus_eq_ctrl_pow D.one_le_p D.one_le_q D.one_lt_inv_add_inv
            D.X D.Y m t,
          youngModulus_eq_ctrl_pow D.one_le_p D.one_le_q D.one_lt_inv_add_inv
            D.X D.Y s t]
        have hle := Real.rpow_le_rpow (youngCtrl_nonneg D.X D.Y m t) hright
          (youngTheta_pos D.one_lt_inv_add_inv).le
        rw [Real.div_rpow (youngCtrl_nonneg D.X D.Y s t)
            (by norm_num : (0 : ℝ) ≤ 2),
          div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          mul_comm (youngCtrl D.p D.q D.X D.Y s t ^ youngTheta D.p D.q)] at hle
        exact hle
      set ρ : ℝ := youngModulus D.p D.q D.X D.Y s t
      set r : ℝ := (2 : ℝ) ^ (1 - youngTheta D.p D.q)
      set Λ : ℝ := youngLoose (youngTheta D.p D.q)
      set κ : ℝ := sewingConstant (youngTheta D.p D.q)
      have hadd := youngLimit_add hs hm.1 hm.2 ht
      have hAlg : D.youngLimit s t - youngIncrement D.X D.Y s t =
          (D.youngLimit s m - youngIncrement D.X D.Y s m) +
            (D.youngLimit m t - youngIncrement D.X D.Y m t) +
            (youngIncrement D.X D.Y s m +
              youngIncrement D.X D.Y m t -
              youngIncrement D.X D.Y s t) := by
        rw [hadd]
        abel
      have hδ := norm_young_defect hm.1 hm.2 D.one_le_p D.one_le_q
        D.X D.Y hfinX hfinY
      have ihL := ih hs hm.1 (hm.2.trans ht)
      have ihR := ih (hs.trans hm.1) hm.2 ht
      have hsumρ : youngModulus D.p D.q D.X D.Y s m +
          youngModulus D.p D.q D.X D.Y m t ≤ r * ρ := by
        calc
          youngModulus D.p D.q D.X D.Y s m +
              youngModulus D.p D.q D.X D.Y m t ≤
              (2 : ℝ) ^ (-youngTheta D.p D.q) * ρ + (2 : ℝ) ^ (-youngTheta D.p D.q) * ρ := by
            rw [hρL]; exact add_le_add le_rfl hρR
          _ = ((2 : ℝ) * (2 : ℝ) ^ (-youngTheta D.p D.q)) * ρ := by ring
          _ = r * ρ := by
            rw [mul_comm 2, ← Real.rpow_add_one two_ne_zero, neg_add_eq_sub]
      have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
      have hΛ0 : 0 ≤ Λ := youngLoose_nonneg _
      have hκ0 : 0 ≤ κ :=
        (sewingConstant_pos (by simpa [youngTheta] using D.one_lt_inv_add_inv)).le
      have hcoef : 0 ≤ κ + r ^ n * Λ :=
        add_nonneg hκ0 (mul_nonneg (pow_nonneg hr0 n) hΛ0)
      have hmul := mul_le_mul_of_nonneg_left hsumρ hcoef
      have hthree : ‖D.youngLimit s t - youngIncrement D.X D.Y s t‖ ≤
          ‖D.youngLimit s m - youngIncrement D.X D.Y s m‖ +
            ‖D.youngLimit m t - youngIncrement D.X D.Y m t‖ + ρ := by
        simp only [ρ]
        rw [hAlg]
        refine (norm_add_le _ _).trans ?_
        refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
        exact add_le_add le_rfl hδ
      have hbound : ‖D.youngLimit s t - youngIncrement D.X D.Y s t‖ ≤
          (κ + r ^ n * Λ) * (r * ρ) + ρ := by
        calc
          ‖D.youngLimit s t - youngIncrement D.X D.Y s t‖ ≤
              ‖D.youngLimit s m - youngIncrement D.X D.Y s m‖ +
                ‖D.youngLimit m t - youngIncrement D.X D.Y m t‖ + ρ := hthree
          _ ≤ (κ * youngModulus D.p D.q D.X D.Y s m +
                r ^ n * Λ * youngModulus D.p D.q D.X D.Y s m) +
                (κ * youngModulus D.p D.q D.X D.Y m t +
                  r ^ n * Λ * youngModulus D.p D.q D.X D.Y m t) + ρ :=
            add_le_add (add_le_add ihL ihR) le_rfl
          _ = (κ + r ^ n * Λ) * (youngModulus D.p D.q D.X D.Y s m +
                youngModulus D.p D.q D.X D.Y m t) + ρ := by
            ring
          _ ≤ (κ + r ^ n * Λ) * (r * ρ) + ρ := add_le_add hmul le_rfl
      have hsew := sewingConstant_shift (by simpa [youngTheta] using D.one_lt_inv_add_inv)
      have hrκ : κ * r + 1 = κ := by simpa [κ, r, youngTheta] using hsew
      calc
        ‖D.youngLimit s t - youngIncrement D.X D.Y s t‖ ≤
            (κ + r ^ n * Λ) * (r * ρ) + ρ := hbound
        _ = κ * r * ρ + r ^ n * r * Λ * ρ + ρ := by ring
        _ = (κ * r + 1) * ρ + (r ^ n * r) * Λ * ρ := by ring
        _ = κ * ρ + r ^ (n + 1) * Λ * ρ := by rw [← pow_succ, hrκ]

/-- Sharp Young–Loeve remainder bound with `sewingConstant (p⁻¹ + q⁻¹)`. -/
lemma norm_youngLimit_sharp {s t : ℝ} (hs : D.a ≤ s) (hst : s ≤ t) (ht : t ≤ D.b) :
    ‖D.youngLimit s t - youngIncrement D.X D.Y s t‖ ≤
      sewingConstant (D.p⁻¹ + D.q⁻¹) * (pathVariationPower D.p D.X s t).toReal ^ D.p⁻¹ *
        (pathVariationPower D.q D.Y s t).toReal ^ D.q⁻¹ := by
  have hr := sewingRatio_mem (by simpa [youngTheta] using D.one_lt_inv_add_inv)
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr.1 hr.2
  set ρ : ℝ := youngModulus D.p D.q D.X D.Y s t
  set κ : ℝ := sewingConstant (youngTheta D.p D.q)
  set Λ : ℝ := youngLoose (youngTheta D.p D.q)
  set r : ℝ := (2 : ℝ) ^ (1 - youngTheta D.p D.q)
  have hstep : ∀ n, ‖D.youngLimit s t - youngIncrement D.X D.Y s t‖ ≤
      κ * ρ + r ^ n * Λ * ρ :=
    fun n => norm_defect_iterate hs hst ht n
  have hlim : ‖D.youngLimit s t - youngIncrement D.X D.Y s t‖ ≤ κ * ρ := by
    have htend : Tendsto (fun n : ℕ => κ * ρ + r ^ n * Λ * ρ) atTop (𝓝 (κ * ρ)) := by
      have hzero : Tendsto (fun n : ℕ => r ^ n * (Λ * ρ)) atTop (𝓝 0) := by
        have hrθ : r = (2 : ℝ) ^ (1 - (D.p⁻¹ + D.q⁻¹)) := by simp [r, youngTheta]
        rw [hrθ]
        simpa [zero_mul] using hpow.mul_const (Λ * ρ)
      have hfun : (fun n : ℕ => κ * ρ + r ^ n * Λ * ρ) =
          fun n => κ * ρ + r ^ n * (Λ * ρ) := by
        funext n; ring
      simpa [hfun] using tendsto_const_nhds.add hzero
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds htend hstep
  have hassoc : κ * ρ =
      sewingConstant (D.p⁻¹ + D.q⁻¹) * (pathVariationPower D.p D.X s t).toReal ^ D.p⁻¹ *
        (pathVariationPower D.q D.Y s t).toReal ^ D.q⁻¹ := by
    simp [κ, ρ, youngModulus, variationReal, youngTheta, mul_assoc]
  simpa [hassoc] using hlim

/-- The Young limit telescopes along any monotone sequence of nodes in `[a, b]`. -/
private lemma youngLimit_seq (n : ℕ) (c : ℕ → ℝ) (hc : Monotone c) (h0 : D.a ≤ c 0)
    (hn : c n ≤ D.b) :
    D.youngLimit (c 0) (c n) = ∑ i ∈ range n, D.youngLimit (c i) (c (i + 1)) := by
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
private lemma youngLimit_nodes {s t : ℝ} (hs : D.a ≤ s) (ht : t ≤ D.b)
    (π : OrderedIntervalPartition s t) :
    D.youngLimit s t =
      ∑ i : Fin π.size, D.youngLimit (π.node i.castSucc) (π.node i.succ) := by
  have hseq := youngLimit_seq π.size (nodeSeq π) (monotone_nodeSeq π)
    (by simpa [nodeSeq_zero] using hs) (by simpa [nodeSeq_size] using ht)
  rw [nodeSeq_zero, nodeSeq_size] at hseq
  have hterm : ∀ i : Fin π.size,
      D.youngLimit (π.node i.castSucc) (π.node i.succ) =
        D.youngLimit (nodeSeq π (i : ℕ)) (nodeSeq π ((i : ℕ) + 1)) := by
    intro i
    have hi : (i : ℕ) ≤ π.size := le_of_lt i.isLt
    have hi1 : (i : ℕ) + 1 ≤ π.size := Nat.succ_le_of_lt i.isLt
    have hs' : i.succ = ⟨(i : ℕ) + 1, by omega⟩ := by ext; simp [Fin.val_succ]
    have hc : i.castSucc = ⟨(i : ℕ), by omega⟩ := by ext; simp [Fin.val_castSucc]
    simp [hs', hc, nodeSeq_of_le, hi, hi1]
  rw [Finset.sum_congr rfl fun i _ => hterm i,
    Fin.sum_univ_eq_sum_range
      (fun i => D.youngLimit (nodeSeq π i) (nodeSeq π (i + 1))) π.size, hseq]

/-- Each partition step is bounded by the partition mesh. -/
private lemma partition_step_le_mesh {s t : ℝ} (π : OrderedIntervalPartition s t) (i : Fin π.size) :
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
lemma exists_partition_close {s t : ℝ} (hs : D.a ≤ s) (ht : t ≤ D.b) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ π : OrderedIntervalPartition s t, (π.mesh : ℝ) < δ →
      ‖π.incrementSum (youngIncrement D.X D.Y) - D.youngLimit s t‖ < ε := by
  have hθ : 1 < youngTheta D.p D.q := by simpa [youngTheta] using D.one_lt_inv_add_inv
  have hθ1 : 0 < youngTheta D.p D.q - 1 := sub_pos.mpr hθ
  set κ : ℝ := sewingConstant (youngTheta D.p D.q)
  set Ω : ℝ := youngCtrl D.p D.q D.X D.Y s t
  have hκ : 0 ≤ κ := (sewingConstant_pos hθ).le
  have hΩ : 0 ≤ Ω := youngCtrl_nonneg D.X D.Y s t
  set C : ℝ := κ * Ω
  set τ : ℝ := ε / (2 * (C + 1))
  have hτ : 0 < τ := div_pos hε (mul_pos (by norm_num) (by linarith [mul_nonneg hκ hΩ]))
  set η : ℝ := τ ^ (youngTheta D.p D.q - 1)⁻¹
  have hη : 0 < η := Real.rpow_pos_of_pos hτ _
  have hηpow : η ^ (youngTheta D.p D.q - 1) = τ := by
    rw [← Real.rpow_mul hτ.le]
    have hinv : (youngTheta D.p D.q - 1)⁻¹ * (youngTheta D.p D.q - 1) = 1 := by
      field_simp [hθ1.ne']
    rw [hinv, Real.rpow_one]
  have hτle : C * τ ≤ ε / 2 := by
    simp only [τ]
    rw [mul_div, div_le_iff₀ (by linarith [mul_nonneg hκ hΩ] : (0 : ℝ) < 2 * (C + 1))]
    have hclear : ε / 2 * (2 * (C + 1)) = ε * (C + 1) := by ring
    rw [hclear]
    linarith [hε]
  obtain ⟨δ, hδ, hδc⟩ := exists_ctrl_short D.one_le_p D.one_le_q
    D.one_lt_inv_add_inv D.X D.Y D.continuousOn_X
    D.continuousOn_Y D.pathVariationPower_X_ne_top D.pathVariationPower_Y_ne_top η hη
  refine ⟨δ, hδ, fun π hmesh => ?_⟩
  rw [youngLimit_nodes hs ht π, OrderedIntervalPartition.incrementSum, ← sum_sub_distrib]
  refine lt_of_le_of_lt ((norm_sum_le _ _).trans ?_) (by linarith : ε / 2 < ε)
  have hpiece : ∀ i : Fin π.size,
      ‖youngIncrement D.X D.Y (π.node i.castSucc) (π.node i.succ) -
        D.youngLimit (π.node i.castSucc) (π.node i.succ)‖ ≤
        κ * η ^ (youngTheta D.p D.q - 1) *
          youngCtrl D.p D.q D.X D.Y (π.node i.castSucc) (π.node i.succ) := by
    intro i
    have hxy : π.node i.castSucc ≤ π.node i.succ :=
      π.monotone_node (Fin.castSucc_le_succ i)
    have hx : D.a ≤ π.node i.castSucc := by
      have h0 : s ≤ π.node i.castSucc := by
        simpa [π.node_zero] using π.monotone_node (Fin.zero_le i.castSucc)
      exact le_trans hs h0
    have hy : π.node i.succ ≤ D.b := by
      have hlast : π.node i.succ ≤ π.node (Fin.last π.size) := π.monotone_node (Fin.le_last _)
      exact hlast.trans (by simpa [π.node_last] using ht)
    have hlen : π.node i.succ - π.node i.castSucc < δ :=
      lt_of_le_of_lt (partition_step_le_mesh π i) hmesh
    have hctrl := hδc _ _ hx hxy hy hlen
    have hsharp := norm_youngLimit_sharp hx hxy hy
    rw [norm_sub_rev]
    have hmod : youngModulus D.p D.q D.X D.Y (π.node i.castSucc) (π.node i.succ) ≤
        η ^ (youngTheta D.p D.q - 1) *
          youngCtrl D.p D.q D.X D.Y (π.node i.castSucc) (π.node i.succ) :=
      youngModulus_le_eta hctrl
    have hκmod : sewingConstant (D.p⁻¹ + D.q⁻¹) *
        (pathVariationPower D.p D.X (π.node i.castSucc) (π.node i.succ)).toReal ^ D.p⁻¹ *
        (pathVariationPower D.q D.Y (π.node i.castSucc) (π.node i.succ)).toReal ^ D.q⁻¹ =
        κ * youngModulus D.p D.q D.X D.Y (π.node i.castSucc) (π.node i.succ) := by
      simp [κ, youngModulus, variationReal, youngTheta, mul_assoc]
    exact (hsharp.trans (le_of_eq hκmod)).trans
      (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hmod hκ)
  refine (sum_le_sum fun i _ => hpiece i).trans ?_
  rw [← mul_sum]
  have hmon : Monotone (nodeSeq π) := monotone_nodeSeq π
  have hctrl := ctrl_sum_seq π.size (nodeSeq π) hmon
    (by simpa [nodeSeq_zero] using hs) (by simpa [nodeSeq_size] using ht)
  have hfin : ∑ i : Fin π.size,
      youngCtrl D.p D.q D.X D.Y (π.node i.castSucc) (π.node i.succ) ≤ Ω := by
    have hterm : ∀ i : Fin π.size,
        youngCtrl D.p D.q D.X D.Y (π.node i.castSucc) (π.node i.succ) =
          youngCtrl D.p D.q D.X D.Y (nodeSeq π (i : ℕ))
            (nodeSeq π ((i : ℕ) + 1)) := by
      intro i
      have hi : (i : ℕ) ≤ π.size := le_of_lt i.isLt
      have hi1 : (i : ℕ) + 1 ≤ π.size := Nat.succ_le_of_lt i.isLt
      have hs' : i.succ = ⟨(i : ℕ) + 1, by omega⟩ := by ext; simp [Fin.val_succ]
      have hc : i.castSucc = ⟨(i : ℕ), by omega⟩ := by ext; simp [Fin.val_castSucc]
      simp [hs', hc, nodeSeq_of_le, hi, hi1]
    rw [Finset.sum_congr rfl fun i _ => hterm i,
      Fin.sum_univ_eq_sum_range
        (fun i => youngCtrl D.p D.q D.X D.Y (nodeSeq π i)
          (nodeSeq π (i + 1))) π.size]
    simpa [Ω, nodeSeq_zero, nodeSeq_size] using hctrl
  have hC : κ * η ^ (youngTheta D.p D.q - 1) * Ω ≤ ε / 2 := by
    calc
      κ * η ^ (youngTheta D.p D.q - 1) * Ω = κ * τ * Ω := by rw [hηpow]
      _ = C * τ := by simp only [C]; ring
      _ ≤ ε / 2 := hτle
  exact (mul_le_mul_of_nonneg_left hfin
    (mul_nonneg hκ (Real.rpow_nonneg hη.le _))).trans hC

end YoungData

end YoungLoeve

end CKMA
