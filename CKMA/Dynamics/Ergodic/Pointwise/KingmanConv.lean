/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Ergodic.Pointwise.KingmanLimit
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Order.OrderClosed

import Mathlib.Tactic

/-!
# Convergence in Kingman's theorem

Birkhoff's theorem along `T^[m]` bounds the limsup of a linearly controlled subadditive process.
The liminf and limsup therefore agree, and Scheffé's identity gives L¹ convergence.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Set MeasureTheory Filter Topology Finset
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

attribute [local instance] Classical.propDecidable

omit [MeasurableSpace Ω] in
/-- A value below every positive translate is below the translate's base. -/
lemma ereal_le_of_forall_pos_le_add {a b : EReal}
    (h : ∀ ε : ℝ, 0 < ε → a ≤ b + ε) : a ≤ b := by
  cases a with
  | bot => exact bot_le
  | top =>
      cases b with
      | top => exact le_rfl
      | bot =>
          exfalso
          have h1 := h 1 one_pos
          rw [EReal.bot_add] at h1
          exact not_le_of_gt bot_lt_top h1
      | coe c =>
          exfalso
          have h1 := h 1 one_pos
          have hadd : (c : EReal) + (1 : ℝ) = ((c + 1 : ℝ) : EReal) :=
            (EReal.coe_add c 1).symm
          rw [hadd] at h1
          exact not_le_of_gt (EReal.coe_lt_top (c + 1)) h1
  | coe z =>
      cases b with
      | top => exact le_top
      | bot =>
          exfalso
          have h1 := h 1 one_pos
          rw [EReal.bot_add] at h1
          exact not_le_of_gt (EReal.bot_lt_coe z) h1
      | coe c =>
          refine EReal.coe_le_coe_iff.mpr (le_of_forall_pos_le_add fun ε hε => ?_)
          have h1 := h ε hε
          have hadd : (c : EReal) + (ε : ℝ) = ((c + ε : ℝ) : EReal) :=
            (EReal.coe_add c ε).symm
          rw [hadd] at h1
          exact EReal.coe_le_coe_iff.mp h1

omit [MeasurableSpace Ω] in
/-- A convex weight does not increase a value beyond the slack in a lower bound. -/
lemma kingman_convex_mul_le {a c C : ℝ} (ha : -C ≤ a) (_hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    c * a ≤ a + (1 - c) * C := by
  have hgap : 0 ≤ 1 - c := by linarith
  have hneg : -a ≤ C := by linarith
  have hmul := mul_le_mul_of_nonneg_left hneg hgap
  linarith

omit [MeasurableSpace Ω] in
/-- Dividing a block sum by the block count and the block length recovers the average. -/
lemma birkhoffSum_div_mul_eq_average (S : Ω → Ω) (g : Ω → ℝ) (q m : ℕ) (ω : Ω) :
    birkhoffSum S g q ω / ((q * m : ℕ) : ℝ) =
      birkhoffAverage ℝ S g q ω / (m : ℝ) := by
  calc
    birkhoffSum S g q ω / ((q * m : ℕ) : ℝ)
        = birkhoffSum S g q ω * ((q * m : ℕ) : ℝ)⁻¹ := by rw [div_eq_mul_inv]
    _ = birkhoffSum S g q ω * ((q : ℝ) * (m : ℝ))⁻¹ := by rw [Nat.cast_mul]
    _ = birkhoffSum S g q ω * ((q : ℝ)⁻¹ * (m : ℝ)⁻¹) := by rw [mul_inv]
    _ = birkhoffSum S g q ω * (q : ℝ)⁻¹ * (m : ℝ)⁻¹ := by rw [mul_assoc]
    _ = (q : ℝ)⁻¹ * birkhoffSum S g q ω * (m : ℝ)⁻¹ := by
          rw [mul_comm (birkhoffSum S g q ω) ((q : ℝ)⁻¹)]
    _ = birkhoffAverage ℝ S g q ω * (m : ℝ)⁻¹ := by
          rw [birkhoffAverage, smul_eq_mul]
    _ = birkhoffAverage ℝ S g q ω / (m : ℝ) := by rw [div_eq_mul_inv]

omit [MeasurableSpace Ω] in
/-- The indexed ratio is division by the shifted length. -/
lemma kingmanRatio_eq_div (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    kingmanRatio f n ω = f (n + 1) ω / (n + 1 : ℝ) := by
  unfold kingmanRatio
  rw [div_eq_mul_inv, mul_comm]

omit [MeasurableSpace Ω] in
/-- The absolute difference expands through the minimum. -/
lemma abs_sub_eq_add_sub_two_min (a b : ℝ) :
    |a - b| = a + b - 2 * min a b := by
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr hab), min_eq_left hab]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr hba), min_eq_right hba]
    ring

omit [MeasurableSpace Ω] in
/-- Equal blocks are dominated by the Birkhoff sum of the block increment. -/
lemma kingman_birkhoffSum_blocks_le {f : ℕ → Ω → ℝ} {m : ℕ} (hm : 0 < m) {q : ℕ}
    (hq : 0 < q) {ω : Ω}
    (hsub : ∀ i n m' : ℕ, 0 < n → 0 < m' →
      f (n + m') ((T^[i]) ω) ≤ f n ((T^[i]) ω) + f m' ((T^[i + n]) ω)) :
    f (q * m) ω ≤ birkhoffSum (T^[m]) (f m) q ω := by
  let u : ℕ → ℕ → ℝ := fun i n => f n ((T^[i]) ω)
  have hcocycle : ∀ i n m', 0 < n → 0 < m' →
      u i (n + m') ≤ u i n + u (i + n) m' := by
    intro i n m' hn hm'
    exact hsub i n m' hn hm'
  have hsum := kingmanCocycle_le_sum_blocks hcocycle hm hq
  have hfun : ∑ j ∈ range q, u (j * m) m = birkhoffSum (T^[m]) (f m) q ω := by
    unfold birkhoffSum u
    refine sum_congr rfl fun j _ => ?_
    have hiter : ((T^[m])^[j]) ω = (T^[j * m]) ω := by
      rw [← Function.iterate_mul]
      congr 1
      exact Nat.mul_comm m j
    rw [hiter]
  exact hsum.trans_eq hfun

omit [MeasurableSpace Ω] in
/-- One long normalized length lies under the block average, up to a fixed margin. -/
lemma kingman_one_ratio_lt {f : ℕ → Ω → ℝ} {C φ δ : ℝ} {m n : ℕ} {ω : Ω}
    (hm : 0 < m) (hn : 0 < n) (hδ : 0 < δ)
    (hC : ∀ k : ℕ, 0 < k → -C * (k : ℝ) ≤ f k ω)
    (hsub : ∀ i a b : ℕ, 0 < a → 0 < b →
      f (a + b) ((T^[i]) ω) ≤ f a ((T^[i]) ω) + f b ((T^[i + a]) ω))
    (hq1 : 1 ≤ n / m)
    (hcoeff : (m : ℝ) * |C| / (n : ℝ) ≤ δ)
    (hQ : dist (birkhoffAverage ℝ (T^[m]) (f m) (n / m) ω) φ < (m : ℝ) * δ)
    (htail : ∀ r : ℕ, 0 < r → r < m →
      |f r ((T^[(n / m) * m]) ω)| / (((n / m) * m : ℕ) : ℝ) < δ) :
    f n ω / (n : ℝ) < φ / (m : ℝ) + 3 * δ := by
  let q : ℕ := n / m
  let r : ℕ := n % m
  have hdiv : q * m + r = n := by
    simpa [q, r, Nat.mul_comm] using Nat.div_add_mod n m
  have hrlt : r < m := Nat.mod_lt n hm
  have hqpos : 0 < q := hq1
  have hqm_pos : 0 < q * m := Nat.mul_pos hqpos hm
  have hqm_le : q * m ≤ n := by
    rw [← hdiv]
    exact Nat.le_add_right _ _
  have hblock := kingman_birkhoffSum_blocks_le hm hqpos hsub
  have hmpos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have havg_lt : birkhoffAverage ℝ (T^[m]) (f m) q ω / (m : ℝ) < φ / (m : ℝ) + δ := by
    rw [div_lt_iff₀ hmpos]
    have hupper : birkhoffAverage ℝ (T^[m]) (f m) q ω - φ < (m : ℝ) * δ :=
      (abs_lt.mp (by rwa [Real.dist_eq] at hQ)).2
    have hright : (φ / (m : ℝ) + δ) * (m : ℝ) = φ + (m : ℝ) * δ := by
      rw [add_mul, div_mul_cancel₀ _ hmpos.ne', mul_comm δ]
    linarith
  by_cases hr0 : r = 0
  · have hnqm : n = q * m := by simpa [hr0] using hdiv.symm
    have hle : f n ω / (n : ℝ) ≤
        birkhoffSum (T^[m]) (f m) q ω / ((q * m : ℕ) : ℝ) := by
      rw [hnqm]
      exact div_le_div_of_nonneg_right hblock (Nat.cast_nonneg _)
    rw [birkhoffSum_div_mul_eq_average] at hle
    have hlt : f n ω / (n : ℝ) < φ / (m : ℝ) + δ := hle.trans_lt havg_lt
    linarith
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    let c : ℝ := ((q * m : ℕ) : ℝ) / (n : ℝ)
    let a : ℝ := f (q * m) ω / ((q * m : ℕ) : ℝ)
    have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hc0 : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) hn0.le
    have hc1 : c ≤ 1 := by
      rw [div_le_one₀ hn0]
      exact Nat.cast_le.mpr hqm_le
    have ha_low : -C ≤ a := by
      rw [le_div_iff₀ (Nat.cast_pos.mpr hqm_pos)]
      exact hC (q * m) hqm_pos
    have hconv := kingman_convex_mul_le ha_low hc0 hc1
    have hsum : ((q * m : ℕ) : ℝ) + (r : ℝ) = (n : ℝ) := by
      rw [← Nat.cast_add, hdiv]
    have hc_id : 1 - c = (r : ℝ) / (n : ℝ) := by
      have hleft : ((n : ℝ) - ((q * m : ℕ) : ℝ)) / (n : ℝ) = 1 - c := by
        unfold c
        rw [sub_div, div_self hn0.ne']
      have hright : (n : ℝ) - ((q * m : ℕ) : ℝ) = (r : ℝ) := by linarith
      rw [← hleft, hright]
    have hslack : (1 - c) * C ≤ δ := by
      have h1c : 0 ≤ 1 - c := by linarith
      have hmulC : (1 - c) * C ≤ (1 - c) * |C| :=
        mul_le_mul_of_nonneg_left (le_abs_self C) h1c
      have hr_le : (r : ℝ) / (n : ℝ) ≤ (m : ℝ) / (n : ℝ) :=
        div_le_div_of_nonneg_right (Nat.cast_le.mpr (le_of_lt hrlt)) hn0.le
      have hfrac : (r : ℝ) / (n : ℝ) * |C| ≤ (m : ℝ) / (n : ℝ) * |C| :=
        mul_le_mul_of_nonneg_right hr_le (abs_nonneg _)
      have hrew : (1 - c) * |C| = (r : ℝ) / (n : ℝ) * |C| := by rw [hc_id]
      have hmfrac : (m : ℝ) / (n : ℝ) * |C| = (m : ℝ) * |C| / (n : ℝ) := by ring
      linarith [hcoeff, hmulC, hfrac, hrew, hmfrac]
    have hca : c * a = f (q * m) ω / (n : ℝ) := by
      unfold c a
      have hqm0 : ((q * m : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [hqm0, hn0.ne']
    have hsplit := hsub 0 (q * m) r hqm_pos hrpos
    have hsplit' : f n ω ≤ f (q * m) ω + f r ((T^[q * m]) ω) := by
      simpa [Function.iterate_zero_apply, Nat.zero_add, hdiv] using hsplit
    have hdivle : f n ω / (n : ℝ) ≤
        f (q * m) ω / (n : ℝ) + f r ((T^[q * m]) ω) / (n : ℝ) := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right hsplit' hn0.le
    have hrest : f r ((T^[q * m]) ω) / (n : ℝ) < δ := by
      have htailr := htail r hrpos hrlt
      have habs_le : f r ((T^[q * m]) ω) / (n : ℝ) ≤
          |f r ((T^[q * m]) ω)| / (n : ℝ) :=
        div_le_div_of_nonneg_right (le_abs_self _) hn0.le
      have hden : |f r ((T^[q * m]) ω)| / (n : ℝ) ≤
          |f r ((T^[q * m]) ω)| / ((q * m : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (Nat.cast_pos.mpr hqm_pos)
          (Nat.cast_le.mpr hqm_le)
      exact habs_le.trans_lt (hden.trans_lt htailr)
    have ha_le : a ≤ birkhoffAverage ℝ (T^[m]) (f m) q ω / (m : ℝ) := by
      have hdiva :=
        div_le_div_of_nonneg_right hblock (Nat.cast_nonneg (q * m))
      rw [birkhoffSum_div_mul_eq_average] at hdiva
      simpa [a] using hdiva
    have hstep : f n ω / (n : ℝ) ≤ a + (1 - c) * C +
        f r ((T^[q * m]) ω) / (n : ℝ) := by
      calc
        f n ω / (n : ℝ) ≤ c * a + f r ((T^[q * m]) ω) / (n : ℝ) := by
          simpa [hca] using hdivle
        _ ≤ a + (1 - c) * C + f r ((T^[q * m]) ω) / (n : ℝ) := by linarith
    have hlt_a : f n ω / (n : ℝ) < a + 2 * δ := by linarith
    calc
      f n ω / (n : ℝ) < a + 2 * δ := hlt_a
      _ ≤ birkhoffAverage ℝ (T^[m]) (f m) q ω / (m : ℝ) + 2 * δ := by linarith
      _ < φ / (m : ℝ) + δ + 2 * δ := by linarith
      _ = φ / (m : ℝ) + 3 * δ := by ring

omit [MeasurableSpace Ω] in
/-- Normalized lengths eventually lie under the block mean plus an arbitrary margin. -/
lemma kingman_ratio_eventually_le {f : ℕ → Ω → ℝ} {C φ : ℝ} {m : ℕ} {ω : Ω}
    (hm : 0 < m)
    (hC : ∀ k : ℕ, 0 < k → -C * (k : ℝ) ≤ f k ω)
    (hsub : ∀ i a b : ℕ, 0 < a → 0 < b →
      f (a + b) ((T^[i]) ω) ≤ f a ((T^[i]) ω) + f b ((T^[i + a]) ω))
    (havg : Tendsto (fun q : ℕ => birkhoffAverage ℝ (T^[m]) (f m) q ω) atTop (𝓝 φ))
    (htail : ∀ r : ℕ, 0 < r → r < m →
      Tendsto (fun k : ℕ => f r ((T^[k]) ω) / (k : ℝ)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, f (n + 1) ω / (n + 1 : ℝ) < φ / (m : ℝ) + ε := by
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by positivity
  have hεδ : 3 * δ = ε := by
    unfold δ
    field_simp
  rw [Metric.tendsto_atTop] at havg
  obtain ⟨Q, hQ⟩ := havg ((m : ℝ) * δ) (mul_pos (Nat.cast_pos.mpr hm) hδ)
  have htail_all : ∀ᶠ k : ℕ in atTop, ∀ r ∈ Finset.Ico 1 m,
      |f r ((T^[k]) ω)| / (k : ℝ) < δ := by
    rw [Filter.eventually_all_finset]
    intro r hr
    have hr0 : 0 < r := (mem_Ico.mp hr).1
    have hrm : r < m := (mem_Ico.mp hr).2
    have htr := htail r hr0 hrm
    rw [Metric.tendsto_nhds] at htr
    filter_upwards [htr δ hδ, eventually_gt_atTop 0] with k hk hk0
    rw [Real.dist_eq, sub_zero, abs_div, Nat.abs_cast] at hk
    exact hk
  obtain ⟨K, hK⟩ := eventually_atTop.1 htail_all
  let q0 : ℕ := max Q (max K 1)
  let NC : ℕ := ⌈(m : ℝ) * |C| / δ⌉₊
  let N0 : ℕ := max (q0 * m) (max NC 1)
  have hlarge : ∀ᶠ N : ℕ in atTop, f N ω / (N : ℝ) < φ / (m : ℝ) + ε := by
    rw [eventually_atTop]
    refine ⟨N0, fun n hn => ?_⟩
    have hn1 : 1 ≤ n :=
      le_trans (le_max_right NC 1) (le_trans (le_max_right (q0 * m) _) hn)
    have hn0 : 0 < n := hn1
    have hNCl : NC ≤ n :=
      le_trans (le_max_left NC 1) (le_trans (le_max_right (q0 * m) _) hn)
    have hceil : (m : ℝ) * |C| / δ ≤ (n : ℝ) := Nat.ceil_le.mp hNCl
    have hcoeff : (m : ℝ) * |C| / (n : ℝ) ≤ δ := by
      have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn0
      have hmul : (m : ℝ) * |C| ≤ (n : ℝ) * δ := by
        have hmul' := mul_le_mul_of_nonneg_right hceil hδ.le
        rwa [div_mul_cancel₀ _ hδ.ne'] at hmul'
      rw [div_le_iff₀ hnpos, mul_comm δ (n : ℝ)]
      exact hmul
    have hq0le : q0 ≤ n / m :=
      (Nat.le_div_iff_mul_le hm).mpr (le_trans (le_max_left (q0 * m) _) hn)
    have hq1 : 1 ≤ n / m :=
      le_trans (le_trans (le_max_right K 1) (le_max_right Q _)) hq0le
    have hqK : K ≤ n / m :=
      le_trans (le_trans (le_max_left K 1) (le_max_right Q _)) hq0le
    have hqmK : K ≤ (n / m) * m := by
      have hm1 : 1 ≤ m := hm
      exact hqK.trans (by simpa using Nat.mul_le_mul_left (n / m) hm1)
    have hdist := hQ (n / m) (le_trans (le_max_left Q _) hq0le)
    have htailn : ∀ r : ℕ, 0 < r → r < m →
        |f r ((T^[(n / m) * m]) ω)| / (((n / m) * m : ℕ) : ℝ) < δ := by
      intro r hr hrm
      exact hK ((n / m) * m) hqmK r (mem_Ico.mpr ⟨hr, hrm⟩)
    have hlt :=
      kingman_one_ratio_lt hm hn0 hδ hC hsub hq1 hcoeff hdist htailn
    linarith
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hlarge] with n hn
  simpa [Nat.cast_succ] using hn

/-- The extended limsup stays above the linear lower bound. -/
lemma kingmanLimsup_ge {f : ℕ → Ω → ℝ} {C : ℝ}
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) (ω : Ω) :
    (-C : EReal) ≤ kingmanLimsup f ω :=
  (kingmanLiminf_ge hC ω).trans (liminf_le_limsup
    (ereal_isBoundedUnder_le atTop _) (ereal_isBoundedUnder_ge atTop _))

/-- The extended limsup is never `⊥` under a real linear lower bound. -/
lemma kingmanLimsup_ne_bot {f : ℕ → Ω → ℝ} {C : ℝ}
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) (ω : Ω) :
    kingmanLimsup f ω ≠ ⊥ := by
  intro hbot
  have hle := kingmanLimsup_ge hC ω
  rw [hbot] at hle
  exact not_le_of_gt (EReal.bot_lt_coe (-C)) hle

/-- The limsup is at most the normalized invariant conditional expectation of each block. -/
lemma kingmanLimsup_le_condExp [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} {C : ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) {m : ℕ} (hm : 0 < m) :
    ∀ᵐ ω ∂μ, kingmanLimsup f ω ≤
      ((((μ[f m | MeasurableSpace.invariants (T^[m])]) ω) / (m : ℝ) : ℝ) : EReal) := by
  have hS : MeasurePreserving (T^[m]) μ μ := hT.iterate m
  have hconv := birkhoffAverage_ae_tendsto_condExp hS (hf m hm)
  have hsub_ae := ae_forall_iterate hT (kingman_ae_subadditive hsub)
  have htail : ∀ᵐ ω ∂μ, ∀ r ∈ Finset.Ico 1 m,
      Tendsto (fun k => f r ((T^[k]) ω) / (k : ℝ)) atTop (𝓝 0) := by
    rw [Filter.eventually_all_finset]
    intro r hr
    exact tendsto_comp_iterate_div hT (hf r (mem_Ico.mp hr).1)
      (hf_meas r (mem_Ico.mp hr).1)
  filter_upwards [hconv, hsub_ae, htail] with ω hconvω hsubω htailω
  refine ereal_le_of_forall_pos_le_add fun ε hε => ?_
  have hcocycle : ∀ i a b : ℕ, 0 < a → 0 < b →
      f (a + b) ((T^[i]) ω) ≤ f a ((T^[i]) ω) + f b ((T^[i + a]) ω) := by
    intro i a b ha hb
    have hineq := hsubω i a b ha hb
    have hiter : (T^[a]) ((T^[i]) ω) = (T^[i + a]) ω := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    simpa [hiter] using hineq
  have htail_pt : ∀ r : ℕ, 0 < r → r < m →
      Tendsto (fun k => f r ((T^[k]) ω) / (k : ℝ)) atTop (𝓝 0) :=
    fun r hr hrm => htailω r (mem_Ico.mpr ⟨hr, hrm⟩)
  have hev := kingman_ratio_eventually_le hm (fun k hk => hC k hk ω) hcocycle hconvω
    htail_pt hε
  rw [← EReal.coe_add]
  apply limsup_le_of_le (ereal_isCoboundedUnder_le atTop _)
  filter_upwards [hev] with n hn
  rw [kingmanRatio_eq_div]
  exact EReal.coe_le_coe_iff.mpr (le_of_lt hn)

/-- The extended limsup is measurable for a measurable cocycle. -/
lemma measurable_kingmanLimsup {f : ℕ → Ω → ℝ}
    (hf : ∀ n : ℕ, 0 < n → Measurable (f n)) : Measurable (kingmanLimsup f) := by
  unfold kingmanLimsup
  refine Measurable.limsup fun n => ?_
  exact (measurable_kingmanRatio (hf (n + 1) (Nat.succ_pos n))).coe_real_ereal

/-- The real representative of the extended limsup. Infinities are sent to zero. -/
def kingmanLimsupReal (f : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  (kingmanLimsup f ω).toReal

/-- The extended limsup is finite almost everywhere. -/
lemma kingmanLimsup_ae_ne_top [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} {C : ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) :
    ∀ᵐ ω ∂μ, kingmanLimsup f ω ≠ ⊤ := by
  have hle := kingmanLimsup_le_condExp hT hf hf_meas hsub hC Nat.one_pos
  filter_upwards [hle] with ω hω htop
  rw [htop] at hω
  refine not_le_of_gt ?_ hω
  exact EReal.coe_lt_top _

/-- Under a pointwise linear bound, the real limsup is integrable. -/
lemma kingmanLimsupReal_integrable [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} {C : ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) :
    Integrable (kingmanLimsupReal f) μ := by
  let bLim : Ω → ℝ := μ[f 1 | MeasurableSpace.invariants (T^[1])]
  have hle := kingmanLimsup_le_condExp hT hf hf_meas hsub hC Nat.one_pos
  have hne := kingmanLimsup_ae_ne_top hT hf hf_meas hsub hC
  have hb_int : Integrable bLim μ := integrable_condExp
  have hmeas : Measurable (kingmanLimsupReal f) :=
    (measurable_kingmanLimsup hf_meas).ereal_toReal
  have habs : ∀ᵐ ω ∂μ, |kingmanLimsupReal f ω| ≤ |bLim ω| + |C| := by
    filter_upwards [hle, hne] with ω hω htop
    have hbot := kingmanLimsup_ne_bot hC ω
    have hup := EReal.toReal_le_toReal hω hbot (EReal.coe_ne_top _)
    have hlow := EReal.toReal_le_toReal (kingmanLimsup_ge hC ω) (EReal.coe_ne_bot (-C)) htop
    rw [abs_le]
    constructor
    · have hlow' : -C ≤ kingmanLimsupReal f ω := by
        unfold kingmanLimsupReal
        rw [← EReal.toReal_coe (-C)]
        exact hlow
      have hCabs : -|C| ≤ -C := neg_le_neg (le_abs_self C)
      have hsum : -(|bLim ω| + |C|) ≤ -|C| := by
        linarith [abs_nonneg (bLim ω)]
      linarith
    · have hup' : kingmanLimsupReal f ω ≤ bLim ω / ((1 : ℕ) : ℝ) := by
        unfold kingmanLimsupReal
        rw [EReal.toReal_coe] at hup
        exact hup
      have hdiv : bLim ω / ((1 : ℕ) : ℝ) = bLim ω := by
        rw [Nat.cast_one, div_one]
      linarith [hup', hdiv, le_abs_self (bLim ω), abs_nonneg C]
  have hbound : Integrable (fun ω => |bLim ω| + |C|) μ :=
    hb_int.abs.add (integrable_const |C|)
  refine hbound.mono hmeas.aestronglyMeasurable ?_
  filter_upwards [habs] with ω hω
  have hnorm : ‖|bLim ω| + |C|‖ = |bLim ω| + |C| := by
    rw [Real.norm_eq_abs]
    exact abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
  rw [Real.norm_eq_abs, hnorm]
  exact hω

/-- The real limsup has mean at most every normalized positive-length integral. -/
lemma kingmanLimsupReal_integral_le [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} {C : ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) {n : ℕ} (hn : 0 < n) :
    ∫ ω, kingmanLimsupReal f ω ∂μ ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ := by
  let bLim : Ω → ℝ := μ[f n | MeasurableSpace.invariants (T^[n])]
  have hle := kingmanLimsup_le_condExp hT hf hf_meas hsub hC hn
  have hs_int := kingmanLimsupReal_integrable hT hf hf_meas hsub hC
  have hb_int : Integrable bLim μ := integrable_condExp
  have hσ : SigmaFinite (μ.trim (MeasurableSpace.invariants_le (T^[n]))) := inferInstance
  have hint : ∫ ω, bLim ω ∂μ = ∫ ω, f n ω ∂μ :=
    integral_condExp (MeasurableSpace.invariants_le (T^[n]))
  have hreal : ∀ᵐ ω ∂μ, kingmanLimsupReal f ω ≤ bLim ω / (n : ℝ) := by
    filter_upwards [hle] with ω hω
    have hto := EReal.toReal_le_toReal hω (kingmanLimsup_ne_bot hC ω) (EReal.coe_ne_top _)
    unfold kingmanLimsupReal
    rw [EReal.toReal_coe] at hto
    exact hto
  have hdiv_int : Integrable (fun ω => bLim ω / (n : ℝ)) μ := hb_int.div_const _
  have hineq := integral_mono_ae hs_int hdiv_int hreal
  rw [integral_div, hint, div_eq_mul_inv, mul_comm] at hineq
  exact hineq

/-- The real limsup has mean at most the Fekete infimum. -/
lemma kingmanLimsupReal_integral_le_mean [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) {f : ℕ → Ω → ℝ} {C : ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) :
    ∫ ω, kingmanLimsupReal f ω ∂μ ≤
      sInf {a : ℝ | ∃ n : ℕ, 0 < n ∧ a = (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ} := by
  refine le_csInf ⟨((1 : ℕ) : ℝ)⁻¹ * ∫ ω, f 1 ω ∂μ, ⟨1, Nat.one_pos, rfl⟩⟩ ?_
  rintro a ⟨n, hn, rfl⟩
  exact kingmanLimsupReal_integral_le hT hf hf_meas hsub hC hn

/-- The real liminf and limsup agree almost everywhere. -/
lemma kingmanLiminfReal_ae_eq_limsupReal [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) {f : ℕ → Ω → ℝ} {C : ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) :
    kingmanLiminfReal f =ᵐ[μ] kingmanLimsupReal f := by
  obtain ⟨hg_int, -, hne_inf, -⟩ := kingmanLiminfReal_integrable_le hT hf hf_meas hsub hC
  have hint_inf := kingmanLiminfReal_integral_eq hT hf hf_meas hsub hC
  have hint_sup := kingmanLimsupReal_integral_le_mean hT hf hf_meas hsub hC
  have hs_int := kingmanLimsupReal_integrable hT hf hf_meas hsub hC
  have hne_sup := kingmanLimsup_ae_ne_top hT hf hf_meas hsub hC
  have hle : kingmanLiminfReal f ≤ᵐ[μ] kingmanLimsupReal f := by
    filter_upwards [hne_inf, hne_sup] with ω hinf hsup
    have horder := liminf_le_limsup (u := fun n => (kingmanRatio f n ω : EReal))
      (ereal_isBoundedUnder_le atTop _) (ereal_isBoundedUnder_ge atTop _)
    have hreal := EReal.toReal_le_toReal horder (kingmanLiminf_ne_bot hC ω) hsup
    unfold kingmanLiminfReal kingmanLimsupReal
    exact hreal
  have hdiff_nn : 0 ≤ᵐ[μ] fun ω => kingmanLimsupReal f ω - kingmanLiminfReal f ω := by
    filter_upwards [hle] with ω hω
    have : 0 ≤ kingmanLimsupReal f ω - kingmanLiminfReal f ω := by linarith
    exact this
  have hdiff_int := hs_int.sub hg_int
  have hint_le : ∫ ω, kingmanLimsupReal f ω - kingmanLiminfReal f ω ∂μ ≤ 0 := by
    rw [integral_sub hs_int hg_int]
    linarith
  have hint0 : ∫ ω, kingmanLimsupReal f ω - kingmanLiminfReal f ω ∂μ = 0 :=
    le_antisymm hint_le (integral_nonneg_of_ae hdiff_nn)
  have heq0 := (integral_eq_zero_iff_of_nonneg_ae hdiff_nn hdiff_int).1 hint0
  filter_upwards [heq0] with ω hω
  have hzero : kingmanLimsupReal f ω - kingmanLiminfReal f ω = 0 := by
    simpa using hω
  exact (sub_eq_zero.mp hzero).symm

/-- Normalized lengths converge almost everywhere to the real liminf. -/
lemma kingmanRatio_ae_tendsto_linear [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} {C : ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹ * f (n + 1) ω) atTop
      (𝓝 (kingmanLiminfReal f ω)) := by
  have heq := kingmanLiminfReal_ae_eq_limsupReal hT hf hf_meas hsub hC
  obtain ⟨-, -, hne_inf, -⟩ := kingmanLiminfReal_integrable_le hT hf hf_meas hsub hC
  have hne_sup := kingmanLimsup_ae_ne_top hT hf hf_meas hsub hC
  filter_upwards [heq, hne_inf, hne_sup] with ω heqω hinf hsup
  have hbot_sup := kingmanLimsup_ne_bot hC ω
  have hcoe_inf : kingmanLiminf f ω = (kingmanLiminfReal f ω : EReal) :=
    (EReal.coe_toReal hinf (kingmanLiminf_ne_bot hC ω)).symm
  have hcoe_sup : kingmanLimsup f ω = (kingmanLimsupReal f ω : EReal) :=
    (EReal.coe_toReal hsup hbot_sup).symm
  have hsame : kingmanLiminf f ω = kingmanLimsup f ω := by
    rw [hcoe_inf, hcoe_sup, heqω]
  have htendE : Tendsto (fun n => (kingmanRatio f n ω : EReal)) atTop
      (𝓝 (kingmanLiminf f ω)) := by
    apply tendsto_of_liminf_eq_limsup
      (u := fun n => (kingmanRatio f n ω : EReal)) (a := kingmanLiminf f ω)
    · rfl
    · simpa [kingmanLiminf, kingmanLimsup] using hsame.symm
  rw [hcoe_inf] at htendE
  simpa [kingmanRatio] using (EReal.tendsto_coe).1 htendE

/-- The normalized process converges to the liminf in L¹. -/
lemma kingman_eLpNorm_tendsto_of_linear [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} {C : ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun ω => (n + 1 : ℝ)⁻¹ * f (n + 1) ω - kingmanLiminfReal f ω) 1 μ) atTop (𝓝 0) := by
  set g : Ω → ℝ := kingmanLiminfReal f
  set L : ℝ := sInf {a : ℝ | ∃ n : ℕ, 0 < n ∧ a = (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ}
  obtain ⟨hg_int, -, -, -⟩ := kingmanLiminfReal_integrable_le hT hf hf_meas hsub hC
  have hg_meas : Measurable g := (measurable_kingmanLiminf hf_meas).ereal_toReal
  have hint_g := kingmanLiminfReal_integral_eq hT hf hf_meas hsub hC
  have hnn_g : ∀ᵐ ω ∂μ, 0 ≤ g ω + C := by
    have hge := (kingmanLiminfReal_integrable_le hT hf hf_meas hsub hC).2.2.2
    filter_upwards [hge] with ω hω
    linarith
  have hconv := kingmanRatio_ae_tendsto_linear hT hf hf_meas hsub hC
  have hmin_tend : Tendsto (fun n => ∫ ω,
      min (kingmanRatio f n ω + C) (g ω + C) ∂μ) atTop (𝓝 (∫ ω, g ω + C ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => g ω + C)
      (fun n => ?_) (hg_int.add (integrable_const C)) (fun n => ?_) ?_
    · exact (((measurable_kingmanRatio (hf_meas (n + 1) (Nat.succ_pos n))).add
        measurable_const).min (hg_meas.add measurable_const)).aestronglyMeasurable
    · filter_upwards [hnn_g] with ω hω
      have hρ : 0 ≤ kingmanRatio f n ω + C := by linarith [kingmanRatio_ge hC n ω]
      have hmin0 : 0 ≤ min (kingmanRatio f n ω + C) (g ω + C) := le_min hρ hω
      rw [Real.norm_eq_abs, abs_of_nonneg hmin0]
      exact min_le_right _ _
    · filter_upwards [hconv] with ω hω
      have hρC := hω.add (tendsto_const_nhds (x := C))
      have hmin := hρC.min (tendsto_const_nhds (x := g ω + C))
      simpa [kingmanRatio, g, min_self] using hmin
  have habs_int : ∀ n, Integrable (fun ω => |kingmanRatio f n ω - g ω|) μ :=
    fun n => ((integrable_kingmanRatio hf n).sub hg_int).abs
  have hmin_int : ∀ n, Integrable (fun ω =>
      min (kingmanRatio f n ω + C) (g ω + C)) μ := by
    intro n
    have hform : (fun ω => min (kingmanRatio f n ω + C) (g ω + C)) =
        fun ω => ((kingmanRatio f n ω + C) + (g ω + C) -
          |kingmanRatio f n ω - g ω|) / 2 := by
      ext ω
      have h := abs_sub_eq_add_sub_two_min (kingmanRatio f n ω + C) (g ω + C)
      have habs : |kingmanRatio f n ω + C - (g ω + C)| =
          |kingmanRatio f n ω - g ω| := by
        congr 1
        ring
      have h2 : 2 * min (kingmanRatio f n ω + C) (g ω + C) =
          (kingmanRatio f n ω + C) + (g ω + C) - |kingmanRatio f n ω - g ω| := by
        rw [← habs]
        linarith
      rw [eq_div_iff two_ne_zero, mul_comm]
      exact h2
    rw [hform]
    exact ((((integrable_kingmanRatio hf n).add (integrable_const C)).add
      (hg_int.add (integrable_const C))).sub (habs_int n)).div_const 2
  have hsplit : ∀ n, ∫ ω, |kingmanRatio f n ω - g ω| ∂μ =
      ∫ ω, kingmanRatio f n ω + C ∂μ + ∫ ω, g ω + C ∂μ -
        2 * ∫ ω, min (kingmanRatio f n ω + C) (g ω + C) ∂μ := by
    intro n
    let A : Ω → ℝ := fun ω => kingmanRatio f n ω + C
    let B : Ω → ℝ := fun ω => g ω + C
    let M : Ω → ℝ := fun ω => min (A ω) (B ω)
    have hpt : (fun ω => |kingmanRatio f n ω - g ω|) =
        A + B - fun ω => 2 * M ω := by
      ext ω
      have hid := abs_sub_eq_add_sub_two_min (A ω) (B ω)
      have habs : |A ω - B ω| = |kingmanRatio f n ω - g ω| := by
        simp only [A, B]
        congr 1
        ring
      rw [Pi.sub_apply, Pi.add_apply]
      simp only [M]
      rw [← habs, hid]
    have hA : Integrable A μ :=
      (integrable_kingmanRatio hf n).add (integrable_const _)
    have hB : Integrable B μ := hg_int.add (integrable_const _)
    have hAB := hA.add hB
    have hM2 : Integrable (fun ω => 2 * M ω) μ := (hmin_int n).const_mul 2
    rw [hpt, integral_sub' hAB hM2, integral_add' hA hB, integral_const_mul]
  have hA_tend := tendsto_integral_kingmanShift hT hf hsub hC
  have hB : ∫ ω, g ω + C ∂μ = L + C := by
    rw [integral_add hg_int (integrable_const C), integral_const, hint_g]
    simp [L, measureReal_def, IsProbabilityMeasure.measure_univ]
  have hcomb := (hA_tend.add (tendsto_const_nhds (x := ∫ ω, g ω + C ∂μ))).sub
    (hmin_tend.const_mul 2)
  have hzero : (L + C) + ∫ ω, g ω + C ∂μ - 2 * ∫ ω, g ω + C ∂μ = 0 := by
    rw [hB]
    ring
  have hInt : Tendsto (fun n => ∫ ω, |kingmanRatio f n ω - g ω| ∂μ) atTop (𝓝 0) := by
    have hshifted := hcomb.congr fun n => (hsplit n).symm
    rw [hzero] at hshifted
    exact hshifted
  have hLp : ∀ n, eLpNorm (fun ω => kingmanRatio f n ω - g ω) 1 μ =
      ENNReal.ofReal (∫ ω, |kingmanRatio f n ω - g ω| ∂μ) := by
    intro n
    have hmeas : AEStronglyMeasurable (fun ω => kingmanRatio f n ω - g ω) μ :=
      ((measurable_kingmanRatio (hf_meas (n + 1) (Nat.succ_pos n))).sub
        hg_meas).aestronglyMeasurable
    have hnn : 0 ≤ᵐ[μ] fun ω => |kingmanRatio f n ω - g ω| :=
      Eventually.of_forall fun _ => abs_nonneg _
    rw [eLpNorm_one_eq_lintegral_enorm hmeas]
    have hfun : (fun ω => ‖kingmanRatio f n ω - g ω‖ₑ) =
        fun ω => ENNReal.ofReal |kingmanRatio f n ω - g ω| := by
      ext ω
      exact Real.enorm_eq_ofReal_abs _
    rw [hfun, ← ofReal_integral_eq_lintegral_ofReal (habs_int n) hnn]
  have h0 : ENNReal.ofReal 0 = 0 := (ENNReal.ofReal_eq_zero).2 le_rfl
  have henn : Tendsto (fun n => eLpNorm (fun ω => kingmanRatio f n ω - g ω) 1 μ) atTop
      (𝓝 0) := by
    have hmap := (ENNReal.tendsto_ofReal hInt).congr fun n => (hLp n).symm
    simpa [h0] using hmap
  simpa [g, kingmanRatio] using henn

/-- Kingman's theorem under a measurable cocycle and a pointwise linear lower bound. -/
lemma kingman_pointwise_of_linear [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} {C : ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hC : ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω) :
    ∃ g : Ω → ℝ, Integrable g μ ∧ (g ∘ T =ᵐ[μ] g) ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹ * f (n + 1) ω) atTop (𝓝 (g ω))) ∧
      Tendsto (fun n : ℕ ↦ eLpNorm (fun ω ↦ (n + 1 : ℝ)⁻¹ * f (n + 1) ω - g ω) 1 μ)
        atTop (𝓝 0) ∧
      (∫ ω, g ω ∂μ) =
        sInf {a : ℝ | ∃ n : ℕ, 0 < n ∧ a = (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ} := by
  refine ⟨kingmanLiminfReal f, ?_, ?_, ?_, ?_, ?_⟩
  · exact (kingmanLiminfReal_integrable_le hT hf hf_meas hsub hC).1
  · exact kingmanLiminfReal_ae_invariant hT hf hf_meas hsub hC
  · exact kingmanRatio_ae_tendsto_linear hT hf hf_meas hsub hC
  · exact kingman_eLpNorm_tendsto_of_linear hT hf hf_meas hsub hC
  · exact kingmanLiminfReal_integral_eq hT hf hf_meas hsub hC

end CKMA
