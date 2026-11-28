/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Ergodic.Pointwise.Kingman.Defs
public import Mathlib.Analysis.Subadditive

import CKMA.Dynamics.Ergodic.Pointwise.Maximal

/-!
# Fekete's lemma for the expectations of a subadditive process

Along a measure-preserving map, the expectations of a subadditive process form a subadditive
sequence, so by Fekete's lemma their normalized values converge to the mean rate
`subadditiveMeanRate`.

## Main definitions

* `CKMA.kingmanIntegral`: integral of each positive length, with length zero set to `0`.

## Main results

* `CKMA.kingmanIntegral_subadditive`: subadditivity of the padded integral sequence.
* `CKMA.tendsto_kingmanIntegral_div`: normalized positive-length integrals converge to the mean
  rate.
* `CKMA.tendsto_integral_kingmanShift`: the same for the shifted normalized values.
-/

public section

noncomputable section

namespace CKMA

open Set MeasureTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

attribute [local instance] Classical.propDecidable

/-- Integral of each positive length, with the unused length zero set to `0`. -/
@[expose]
def kingmanIntegral (f : ℕ → Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  if n = 0 then 0 else ∫ ω, f n ω ∂μ

/-- Defining equation of `kingmanIntegral`. -/
lemma kingmanIntegral_def (f : ℕ → Ω → ℝ) (μ : Measure Ω) (n : ℕ) :
    kingmanIntegral f μ n = if n = 0 then 0 else ∫ ω, f n ω ∂μ := rfl

/-- Positive-length integrals ignore the artificial zero value. -/
private lemma kingmanIntegral_pos {f : ℕ → Ω → ℝ} {n : ℕ} (hn : n ≠ 0) :
    kingmanIntegral f μ n = ∫ ω, f n ω ∂μ := by
  simp [kingmanIntegral, hn]

/-- Normalized positive-length integrals are the ratios in the mean-rate infimum. -/
private lemma kingmanIntegral_div {f : ℕ → Ω → ℝ} {n : ℕ} (hn : 0 < n) :
    kingmanIntegral f μ n / n = (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ := by
  rw [kingmanIntegral_pos hn.ne', div_eq_mul_inv, mul_comm]

/-- Subadditivity passes to integrals along a measure-preserving map. -/
private lemma kingmanIntegral_add_le (hT : MeasurePreserving T μ μ) {f : ℕ → Ω → ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ) (hsub : IsSubadditiveProcess T f μ)
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
    integral_comp_measurePreserving (hT.iterate n) (hf m hm).aestronglyMeasurable
  linarith

/-- The padded integral sequence is subadditive. -/
lemma kingmanIntegral_subadditive (hT : MeasurePreserving T μ μ) {f : ℕ → Ω → ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ) (hsub : IsSubadditiveProcess T f μ) :
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
private lemma kingmanIntegral_bddBelow {f : ℕ → Ω → ℝ}
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

/-- The Fekete infimum is exactly the mean rate. -/
private lemma kingmanIntegral_lim_eq (hT : MeasurePreserving T μ μ) {f : ℕ → Ω → ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ) (hsub : IsSubadditiveProcess T f μ) :
    (kingmanIntegral_subadditive hT hf hsub).lim = subadditiveMeanRate f μ := by
  rw [Subadditive.lim, subadditiveMeanRate_def]
  congr 1
  ext a
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hpos : 0 < n := Nat.succ_le_iff.mp (mem_Ici.mp hn)
    exact ⟨n, hpos, kingmanIntegral_div hpos⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, mem_Ici.mpr (Nat.succ_le_of_lt hn), kingmanIntegral_div hn⟩

/-- Normalized positive-length integrals converge to the mean rate. -/
lemma tendsto_kingmanIntegral_div (hT : MeasurePreserving T μ μ) {f : ℕ → Ω → ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ) (hsub : IsSubadditiveProcess T f μ)
    (hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ) :
    Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹ * ∫ ω, f (n + 1) ω ∂μ) atTop
      (𝓝 (subadditiveMeanRate f μ)) := by
  have hsubU := kingmanIntegral_subadditive hT hf hsub
  have hbdd := kingmanIntegral_bddBelow (f := f) (μ := μ) hlower
  have hlim := hsubU.tendsto_lim hbdd
  rw [← kingmanIntegral_lim_eq hT hf hsub]
  have hshift : Tendsto (fun n : ℕ =>
      kingmanIntegral f μ (n + 1) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 hsubU.lim) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  refine hshift.congr fun n => ?_
  rw [kingmanIntegral_div (Nat.succ_pos n), Nat.cast_succ]

/-- A pointwise linear bound yields the same bound for normalized integrals. -/
lemma kingman_integral_ge_of_pointwise [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} {C : ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ) (hC : HasLinearLowerBound f C) {n : ℕ}
    (hn : 0 < n) :
    -C ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ := by
  have hconst_int : Integrable (fun _ : Ω => -C * (n : ℝ)) μ := integrable_const _
  have hge : ∫ ω, -C * (n : ℝ) ∂μ ≤ ∫ ω, f n ω ∂μ :=
    integral_mono hconst_int (hf n hn) fun ω => hC n hn ω
  have hconst : ∫ ω, -C * (n : ℝ) ∂μ = -C * (n : ℝ) := by
    rw [integral_const]
    simp [measureReal_def, IsProbabilityMeasure.measure_univ]
  have hinv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_left hge hinv
  rw [hconst] at hmul
  have hcancel : (n : ℝ)⁻¹ * (-C * (n : ℝ)) = -C := by
    field_simp
  rwa [hcancel] at hmul

/-- Shifted normalized integrals converge to the mean rate plus the shift. -/
lemma tendsto_integral_kingmanShift [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} {C : ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hsub : IsSubadditiveProcess T f μ) (hC : HasLinearLowerBound f C) :
    Tendsto (fun n : ℕ => ∫ ω, kingmanRatio f n ω + C ∂μ) atTop
      (𝓝 (subadditiveMeanRate f μ + C)) := by
  have hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ :=
    ⟨-C, fun n hn => kingman_integral_ge_of_pointwise hf hC hn⟩
  have hdiv := tendsto_kingmanIntegral_div hT hf hsub hlower
  have hint : ∀ n, ∫ ω, kingmanRatio f n ω + C ∂μ =
      (n + 1 : ℝ)⁻¹ * ∫ ω, f (n + 1) ω ∂μ + C := by
    intro n
    unfold kingmanRatio
    rw [integral_add ((hf (n + 1) (Nat.succ_pos n)).const_mul _) (integrable_const _),
      integral_const_mul, integral_const]
    simp [measureReal_def, IsProbabilityMeasure.measure_univ]
  exact (hdiv.add tendsto_const_nhds).congr fun n => (hint n).symm

end CKMA
