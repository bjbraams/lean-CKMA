/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Ergodic.Pointwise.Birkhoff
public import CKMA.Dynamics.Ergodic.Pointwise.KingmanOrbit
public import Mathlib.Analysis.Subadditive
public import Mathlib.MeasureTheory.Integral.Bochner.L1
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Topology.Instances.EReal.Lemmas

import Mathlib.Tactic

/-!
# Kingman's subadditive ergodic theorem

The normalized integrals converge by Fekete's lemma. Under a linear pointwise lower bound the
liminf is identified by the Avila–Bochi orbit estimate, and Birkhoff's theorem along multiples
controls the limsup. Truncation removes the lower bound, and Scheffé's lemma gives L¹ convergence.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Set MeasureTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

attribute [local instance] Classical.propDecidable

/-- Integral of each positive length, with the unused length zero set to `0`. -/
def kingmanIntegral (f : ℕ → Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  if n = 0 then 0 else ∫ ω, f n ω ∂μ

/-- Positive-length integrals ignore the artificial zero value. -/
lemma kingmanIntegral_pos {f : ℕ → Ω → ℝ} {n : ℕ} (hn : n ≠ 0) :
    kingmanIntegral f μ n = ∫ ω, f n ω ∂μ := by
  simp [kingmanIntegral, hn]

/-- Normalized positive-length integrals are the ratios in the mean-rate infimum. -/
lemma kingmanIntegral_div {f : ℕ → Ω → ℝ} {n : ℕ} (hn : 0 < n) :
    kingmanIntegral f μ n / n = (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ := by
  rw [kingmanIntegral_pos hn.ne', div_eq_mul_inv, mul_comm]

/-- Subadditivity passes to integrals along a measure-preserving map. -/
lemma kingmanIntegral_add_le (hT : MeasurePreserving T μ μ) {f : ℕ → Ω → ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    ∫ ω, f (n + m) ω ∂μ ≤ ∫ ω, f n ω ∂μ + ∫ ω, f m ω ∂μ := by
  have hnm : 0 < n + m := Nat.add_pos_left hn m
  have hcomp : Integrable (fun ω => f m ((T^[n]) ω)) μ :=
    (hT.iterate n).integrable_comp_of_integrable (hf m hm)
  have hint : Integrable (fun ω => f n ω + f m ((T^[n]) ω)) μ := (hf n hn).add hcomp
  have hle := hsub n m hn hm
  have hmono := integral_mono_ae (hf (n + m) hnm) hint hle
  have hsum : ∫ ω, f n ω + f m ((T^[n]) ω) ∂μ =
      ∫ ω, f n ω ∂μ + ∫ ω, f m ((T^[n]) ω) ∂μ :=
    integral_add (hf n hn) hcomp
  have hshift : ∫ ω, f m ((T^[n]) ω) ∂μ = ∫ ω, f m ω ∂μ :=
    integral_comp_measurePreserving (hT.iterate n) (hf m hm)
  linarith

/-- The padded integral sequence is subadditive. -/
lemma kingmanIntegral_subadditive (hT : MeasurePreserving T μ μ) {f : ℕ → Ω → ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω)) :
    Subadditive (kingmanIntegral f μ) := by
  intro m n
  cases m with
  | zero =>
    simp [kingmanIntegral]
  | succ m =>
    cases n with
    | zero =>
      simp [kingmanIntegral]
    | succ n =>
      have hm0 : m + 1 ≠ 0 := Nat.succ_ne_zero m
      have hn0 : n + 1 ≠ 0 := Nat.succ_ne_zero n
      have hmn0 : m + 1 + (n + 1) ≠ 0 := by omega
      rw [kingmanIntegral_pos hmn0, kingmanIntegral_pos hm0, kingmanIntegral_pos hn0]
      exact kingmanIntegral_add_le hT hf hsub (Nat.succ_pos m) (Nat.succ_pos n)

/-- A uniform lower bound on normalized integrals bounds every ratio, including the zero term. -/
lemma kingmanIntegral_bddBelow {f : ℕ → Ω → ℝ}
    (hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ) :
    BddBelow (range fun n => kingmanIntegral f μ n / n) := by
  obtain ⟨c, hc⟩ := hlower
  refine ⟨min c 0, ?_⟩
  rintro y ⟨n, rfl⟩
  cases n with
  | zero =>
    simp [kingmanIntegral]
  | succ n =>
    exact le_trans (min_le_left _ _) ((hc (n + 1) (Nat.succ_pos n)).trans_eq
      (kingmanIntegral_div (Nat.succ_pos n)).symm)

/-- The Fekete infimum is exactly the infimum of the positive normalized integrals. -/
lemma kingmanIntegral_lim_eq (hT : MeasurePreserving T μ μ) {f : ℕ → Ω → ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω)) :
    (kingmanIntegral_subadditive hT hf hsub).lim =
      sInf {a : ℝ | ∃ n : ℕ, 0 < n ∧ a = (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ} := by
  rw [Subadditive.lim]
  congr 1
  ext a
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hpos : 0 < n := Nat.succ_le_iff.mp (mem_Ici.mp hn)
    exact ⟨n, hpos, kingmanIntegral_div hpos⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, mem_Ici.mpr (Nat.succ_le_of_lt hn), kingmanIntegral_div hn⟩

/-- Normalized positive-length integrals converge to their infimum. -/
lemma tendsto_kingmanIntegral_div (hT : MeasurePreserving T μ μ) {f : ℕ → Ω → ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ) :
    Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹ * ∫ ω, f (n + 1) ω ∂μ) atTop
      (𝓝 (sInf {a : ℝ | ∃ n : ℕ, 0 < n ∧ a = (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ})) := by
  have hsubU := kingmanIntegral_subadditive hT hf hsub
  have hbdd := kingmanIntegral_bddBelow (f := f) (μ := μ) hlower
  have hlim := hsubU.tendsto_lim hbdd
  rw [← kingmanIntegral_lim_eq hT hf hsub]
  have hshift : Tendsto (fun n : ℕ =>
      kingmanIntegral f μ (n + 1) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 hsubU.lim) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  refine hshift.congr fun n => ?_
  rw [kingmanIntegral_div (Nat.succ_pos n), Nat.cast_succ]

/-- A coefficient tending to `1` preserves liminf for a nonnegative sequence. -/
lemma liminf_mul_tendsto_one_nonneg {w c : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hc : Tendsto c atTop (𝓝 (1 : ℝ))) (hc_pos : ∀ᶠ n in atTop, 0 < c n) :
    liminf (fun n => ((c n * w n : ℝ) : EReal)) atTop =
      liminf (fun n => (w n : EReal)) atTop := by
  set L : EReal := liminf (fun n => (w n : EReal)) atTop
  set Lc : EReal := liminf (fun n => ((c n * w n : ℝ) : EReal)) atTop
  have hL0 : (0 : EReal) ≤ L := by
    have hzero : (0 : EReal) ≤ liminf (fun n => (w n : EReal)) atTop :=
      le_liminf_of_le (h := Eventually.of_forall fun n => EReal.coe_nonneg.mpr (hw n))
    simpa [L] using hzero
  have hsqueeze : ∀ ε : ℝ, 0 < ε → ε < 1 → ((1 - ε : ℝ) : EReal) * L ≤ Lc ∧
      Lc ≤ ((1 + ε : ℝ) : EReal) * L := by
    intro ε hε hε1
    have hmem : ∀ᶠ n in atTop, (1 - ε) < c n ∧ c n < 1 + ε := by
      have hnhds : {x : ℝ | (1 - ε) < x ∧ x < 1 + ε} ∈ 𝓝 (1 : ℝ) := by
        exact (isOpen_Ioo.mem_nhds (by constructor <;> linarith))
      exact hc.eventually hnhds
    have hlow : liminf (fun n => ((((1 - ε) * w n : ℝ) : EReal))) atTop ≤ Lc := by
      refine liminf_le_liminf ?_
      filter_upwards [hmem, hc_pos] with n hn hpos
      have hmul : (1 - ε) * w n ≤ c n * w n :=
        mul_le_mul_of_nonneg_right hn.1.le (hw n)
      exact EReal.coe_le_coe_iff.mpr hmul
    have hhigh : Lc ≤ liminf (fun n => ((((1 + ε) * w n : ℝ) : EReal))) atTop := by
      refine liminf_le_liminf ?_
      filter_upwards [hmem] with n hn
      have hmul : c n * w n ≤ (1 + ε) * w n :=
        mul_le_mul_of_nonneg_right hn.2.le (hw n)
      exact EReal.coe_le_coe_iff.mpr hmul
    have hconst₁ : liminf (fun n => ((((1 - ε) * w n : ℝ) : EReal))) atTop =
        ((1 - ε : ℝ) : EReal) * L := by
      have hfun : (fun n => ((((1 - ε) * w n : ℝ) : EReal))) =
          fun n => ((1 - ε : ℝ) : EReal) * (w n : EReal) := by
        ext n
        simp [EReal.coe_mul]
      rw [hfun]
      exact EReal.liminf_const_mul_of_nonneg_of_ne_top
        (EReal.coe_nonneg.mpr (by linarith : (0 : ℝ) ≤ 1 - ε)) (EReal.coe_ne_top _)
    have hconst₂ : liminf (fun n => ((((1 + ε) * w n : ℝ) : EReal))) atTop =
        ((1 + ε : ℝ) : EReal) * L := by
      have hfun : (fun n => ((((1 + ε) * w n : ℝ) : EReal))) =
          fun n => ((1 + ε : ℝ) : EReal) * (w n : EReal) := by
        ext n
        simp [EReal.coe_mul]
      rw [hfun]
      exact EReal.liminf_const_mul_of_nonneg_of_ne_top
        (EReal.coe_nonneg.mpr (by linarith : (0 : ℝ) ≤ 1 + ε)) (EReal.coe_ne_top _)
    rw [hconst₁] at hlow
    rw [hconst₂] at hhigh
    exact ⟨hlow, hhigh⟩
  cases hL : L with
  | bot =>
    exact (not_le_of_gt (EReal.bot_lt_coe (0 : ℝ)) (hL ▸ hL0)).elim
  | top =>
    have hhalf := (hsqueeze (1 / 2) (by norm_num) (by norm_num)).1
    rw [hL] at hhalf
    have hmul : ((1 / 2 : ℝ) : EReal) * ⊤ = ⊤ :=
      EReal.mul_top_of_pos (by norm_num)
    have hcoe : ((1 - (1 / 2 : ℝ) : ℝ) : EReal) = (1 / 2 : ℝ) := by norm_num
    rw [hcoe, hmul] at hhalf
    have hLc : Lc = ⊤ := top_le_iff.mp hhalf
    simp [Lc, hLc]
  | coe a =>
    have ha0 : 0 ≤ a := EReal.coe_le_coe_iff.mp (by simpa [hL] using hL0)
    have hne_top : Lc ≠ ⊤ := by
      intro htop
      have hhi := (hsqueeze (1 / 2) (by norm_num) (by norm_num)).2
      rw [hL, htop, ← EReal.coe_mul] at hhi
      exact not_le_of_gt (EReal.coe_lt_top ((1 + 1 / 2) * a)) hhi
    have hne_bot : Lc ≠ ⊥ := by
      intro hbot
      have hlo := (hsqueeze (1 / 2) (by norm_num) (by norm_num)).1
      rw [hL, hbot, ← EReal.coe_mul] at hlo
      exact not_le_of_gt (EReal.bot_lt_coe ((1 - 1 / 2) * a)) hlo
    have hbdd : ∀ ε : ℝ, 0 < ε → ε < 1 →
        (1 - ε) * a ≤ Lc.toReal ∧ Lc.toReal ≤ (1 + ε) * a := by
      intro ε hε hε1
      obtain ⟨hlo, hhi⟩ := hsqueeze ε hε hε1
      rw [hL, ← EReal.coe_toReal hne_top hne_bot] at hlo hhi
      exact ⟨EReal.coe_le_coe_iff.mp hlo, EReal.coe_le_coe_iff.mp hhi⟩
    have hupper : Lc.toReal ≤ a := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      let ε : ℝ := min (1 / 2) (δ / (a + 1))
      have hε0 : 0 < ε := by positivity
      have hε1 : ε < 1 := by
        have : ε ≤ 1 / 2 := min_le_left _ _
        linarith
      have hεa : ε * a ≤ δ := by
        have hle : ε ≤ δ / (a + 1) := min_le_right _ _
        have hmul : ε * a ≤ δ / (a + 1) * a := mul_le_mul_of_nonneg_right hle ha0
        have hfrac : δ / (a + 1) * a ≤ δ := by
          rw [div_mul_eq_mul_div]
          have hden : (0 : ℝ) < a + 1 := by linarith
          rw [div_le_iff₀ hden]
          nlinarith
        exact hmul.trans hfrac
      have := (hbdd ε hε0 hε1).2
      linarith
    have hlower : a ≤ Lc.toReal := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      let ε : ℝ := min (1 / 2) (δ / (a + 1))
      have hε0 : 0 < ε := by positivity
      have hε1 : ε < 1 := by
        have : ε ≤ 1 / 2 := min_le_left _ _
        linarith
      have hεa : ε * a ≤ δ := by
        have hle : ε ≤ δ / (a + 1) := min_le_right _ _
        have hmul : ε * a ≤ δ / (a + 1) * a := mul_le_mul_of_nonneg_right hle ha0
        have hfrac : δ / (a + 1) * a ≤ δ := by
          rw [div_mul_eq_mul_div]
          have hden : (0 : ℝ) < a + 1 := by linarith
          rw [div_le_iff₀ hden]
          nlinarith
        exact hmul.trans hfrac
      have := (hbdd ε hε0 hε1).1
      linarith
    have hclose : Lc.toReal = a := le_antisymm hupper hlower
    rw [← EReal.coe_toReal hne_top hne_bot, hclose]

/-- Adding a convergent real sequence shifts an extended liminf by the limit. -/
lemma liminf_add_tendsto {u : ℕ → EReal} {v : ℕ → ℝ} {b : ℝ} (hv : Tendsto v atTop (𝓝 b)) :
    liminf (fun n => u n + (v n : EReal)) atTop = liminf u atTop + (b : EReal) := by
  have hvE : Tendsto (fun n => (v n : EReal)) atTop (𝓝 (b : EReal)) :=
    (continuous_coe_real_ereal.tendsto b).comp hv
  have hsup : limsup (fun n => (v n : EReal)) atTop = (b : EReal) := hvE.limsup_eq
  have hinf : liminf (fun n => (v n : EReal)) atTop = (b : EReal) := hvE.liminf_eq
  have hadd : (fun n => u n + (v n : EReal)) = u + fun n => (v n : EReal) := by
    ext n
    rfl
  rw [hadd]
  apply le_antisymm
  · have hle := EReal.liminf_add_le (u := fun n => (v n : EReal)) (v := u) (f := atTop)
      (Or.inl (by simp [hsup])) (Or.inl (by simp [hsup]))
    have hcomm : (fun n => (v n : EReal)) + u = u + fun n => (v n : EReal) := by
      ext n
      dsimp
      rw [add_comm]
    rw [hcomm] at hle
    have hrhs : limsup (fun n => (v n : EReal)) atTop + liminf u atTop =
        liminf u atTop + (b : EReal) := by
      rw [hsup, add_comm]
    rwa [hrhs] at hle
  · have hge := EReal.le_liminf_add (u := u) (v := fun n => (v n : EReal)) (f := atTop)
    simpa [hinf] using hge

/-- A coefficient tending to `1` preserves liminf for a sequence bounded below. -/
lemma liminf_mul_tendsto_one_ge {z c : ℕ → ℝ} {M : ℝ} (hz : ∀ n, -M ≤ z n)
    (hc : Tendsto c atTop (𝓝 (1 : ℝ))) (hc_pos : ∀ᶠ n in atTop, 0 < c n) :
    liminf (fun n => ((c n * z n : ℝ) : EReal)) atTop =
      liminf (fun n => (z n : EReal)) atTop := by
  let w : ℕ → ℝ := fun n => z n + M
  have hw : ∀ n, 0 ≤ w n := fun n => by linarith [hz n]
  have hwnonneg := liminf_mul_tendsto_one_nonneg hw hc hc_pos
  have hshift : liminf (fun n => (w n : EReal)) atTop =
      liminf (fun n => (z n : EReal)) atTop + (M : EReal) := by
    have hadd := liminf_add_tendsto (u := fun n => (z n : EReal))
      (v := fun _ : ℕ => M) tendsto_const_nhds
    have hfun : (fun n => (z n : EReal) + (M : EReal)) = fun n => (w n : EReal) := by
      ext n
      simp [w, EReal.coe_add]
    simpa [hfun] using hadd
  have hprod : liminf (fun n => ((c n * z n : ℝ) : EReal)) atTop =
      liminf (fun n => ((c n * w n : ℝ) : EReal)) atTop + ((-M : ℝ) : EReal) := by
    have hcM : Tendsto (fun n => -(c n * M)) atTop (𝓝 (-M)) := by
      simpa using (hc.mul tendsto_const_nhds).neg
    have hadd := liminf_add_tendsto (u := fun n => ((c n * w n : ℝ) : EReal)) hcM
    have hfun :
        (fun n => ((c n * w n : ℝ) : EReal) + ((-(c n * M) : ℝ) : EReal)) =
          fun n => ((c n * z n : ℝ) : EReal) := by
      ext n
      rw [← EReal.coe_add]
      congr 1
      simp only [w]
      ring
    rw [hfun] at hadd
    exact hadd
  rw [hwnonneg, hshift] at hprod
  rw [EReal.coe_neg, ← sub_eq_add_neg] at hprod
  simpa [EReal.add_sub_cancel_right] using hprod 

end CKMA
