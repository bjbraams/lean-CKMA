/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Ergodic.Pointwise.KingmanConv

import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Kingman's theorem without a pointwise bound

A measurable cocycle controlled from below is already covered by
`kingman_pointwise_of_linear`. The height `-K n` truncation keeps subadditivity and creates
that bound. Sending `K` to infinity, as in the comparison of Avila and Bochi, identifies the
liminf and the limsup. The truncated L¹ convergence then passes to the original process.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Set MeasureTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

attribute [local instance] Classical.propDecidable

/-- The Fekete infimum of the normalized positive-length integrals. -/
def kingmanFekete (f : ℕ → Ω → ℝ) (μ : Measure Ω) : ℝ :=
  sInf {a : ℝ | ∃ n : ℕ, 0 < n ∧ a = (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ}

omit [MeasurableSpace Ω] in
/-- On `EReal`, the linear maximum agrees with the lattice supremum. -/
lemma ereal_max_eq_sup (a b : EReal) : max a b = a ⊔ b := by
  rcases le_total a b with hab | hba
  · calc
      max a b = b := max_eq_right hab
      _ = a ⊔ b := (sup_of_le_right hab).symm
  · calc
      max a b = a := max_eq_left hba
      _ = a ⊔ b := (sup_of_le_left hba).symm

omit [MeasurableSpace Ω] in
/-- A nonpositive floor does not increase the absolute value of a maximum. -/
lemma abs_max_le_abs_of_nonpos {a c : ℝ} (hc : c ≤ 0) : |max a c| ≤ |a| := by
  rcases le_total a c with hac | hca
  · rw [max_eq_right hac, abs_of_nonpos hc, abs_of_nonpos (hac.trans hc)]
    linarith
  · rw [max_eq_left hca]

omit [MeasurableSpace Ω] in
/-- The coercion into `EReal` preserves binary maxima. -/
lemma ereal_coe_max (a b : ℝ) :
    ((max a b : ℝ) : EReal) = max (a : EReal) (b : EReal) := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, max_eq_right (EReal.coe_le_coe_iff.mpr hab)]
  · rw [max_eq_left hba, max_eq_left (EReal.coe_le_coe_iff.mpr hba)]

omit [MeasurableSpace Ω] in
/-- Extended reals that share every negative-integer truncation are equal when the larger one
is finite. -/
lemma ereal_eq_of_max_neg {x y : EReal} (hxy : x ≤ y) (hy_top : y ≠ ⊤) (hy_bot : y ≠ ⊥)
    (hmax : ∀ K : ℕ, max x ((-(K : ℝ) : EReal)) = max y ((-(K : ℝ) : EReal))) : x = y := by
  have hy : y = (y.toReal : EReal) := (EReal.coe_toReal hy_top hy_bot).symm
  cases x with
  | top =>
      exact absurd (top_unique hxy) hy_top
  | bot =>
      exfalso
      let K : ℕ := Nat.ceil (-y.toReal) + 1
      have hK : -(K : ℝ) < y.toReal := by
        have hceil : -y.toReal ≤ ↑(Nat.ceil (-y.toReal)) := Nat.le_ceil _
        have hsucc : (↑(Nat.ceil (-y.toReal)) : ℝ) + 1 = (K : ℝ) := by
          simp [K, Nat.cast_add, Nat.cast_one]
        linarith
      have hlt : ((-(K : ℝ) : EReal)) < y := by
        rw [hy]
        exact EReal.coe_lt_coe_iff.mpr hK
      have hmaxK := hmax K
      rw [max_eq_right bot_le, max_eq_left (le_of_lt hlt)] at hmaxK
      exact ne_of_lt hlt hmaxK
  | coe t =>
      cases y with
      | top => exact absurd rfl hy_top
      | bot => exact absurd rfl hy_bot
      | coe r =>
          have htr : t ≤ r := EReal.coe_le_coe_iff.mp hxy
          suffices ht_eq : t = r by simp [ht_eq]
          by_contra hne
          have hlt : t < r := lt_of_le_of_ne htr hne
          let K : ℕ := Nat.ceil (-t)
          have htK : -(K : ℝ) ≤ t := by
            have hceil : -t ≤ ↑(Nat.ceil (-t)) := Nat.le_ceil _
            linarith
          have hrK : -(K : ℝ) ≤ r := htK.trans hlt.le
          have htE : ((-(K : ℝ) : EReal)) ≤ (t : EReal) :=
            EReal.coe_le_coe_iff.mpr htK
          have hrE : ((-(K : ℝ) : EReal)) ≤ (r : EReal) :=
            EReal.coe_le_coe_iff.mpr hrK
          have hmaxK := hmax K
          rw [max_eq_left htE, max_eq_left hrE, EReal.coe_eq_coe_iff] at hmaxK
          exact hne hmaxK

/-- A measurable representative of each positive-length integrable function. -/
def kingmanMk {f : ℕ → Ω → ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ) (n : ℕ) : Ω → ℝ :=
  if hn : 0 < n then (hf n hn).aestronglyMeasurable.mk (f n) else 0

/-- At a positive length the representative agrees almost everywhere with the original. -/
lemma kingmanMk_ae {f : ℕ → Ω → ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ) {n : ℕ}
    (hn : 0 < n) : f n =ᵐ[μ] kingmanMk hf n := by
  simp only [kingmanMk, dite_eq_left hn]
  exact (hf n hn).aestronglyMeasurable.ae_eq_mk

/-- The positive-length representative is measurable. -/
lemma measurable_kingmanMk {f : ℕ → Ω → ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ) {n : ℕ}
    (hn : 0 < n) : Measurable (kingmanMk hf n) := by
  simp only [kingmanMk, dite_eq_left hn]
  exact (hf n hn).aestronglyMeasurable.measurable_mk

/-- The positive-length representative is integrable. -/
lemma integrable_kingmanMk {f : ℕ → Ω → ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ) {n : ℕ}
    (hn : 0 < n) : Integrable (kingmanMk hf n) μ :=
  (hf n hn).congr (kingmanMk_ae hf hn)

/-- The measurable representative remains subadditive. -/
lemma kingmanMk_subadditive [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω)) :
    ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      kingmanMk hf (n + m) ω ≤
        kingmanMk hf n ω + kingmanMk hf m ((T^[n]) ω) := by
  intro n m hn hm
  have hnm := kingmanMk_ae hf (Nat.add_pos_left hn m)
  have hn' := kingmanMk_ae hf hn
  have hm' := kingmanMk_ae hf hm
  have hmT := (hT.iterate n).quasiMeasurePreserving.ae_eq_comp hm'
  filter_upwards [hnm, hn', hmT, hsub n m hn hm] with ω hnmω hnω hmω hsubω
  have hmApply : f m ((T^[n]) ω) = kingmanMk hf m ((T^[n]) ω) := by
    simpa [Function.comp_apply] using hmω
  rw [← hnmω, ← hnω, ← hmApply]
  exact hsubω

/-- Positive-length integrals are unchanged by the measurable representative. -/
lemma kingmanMk_integral {f : ℕ → Ω → ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ) {n : ℕ}
    (hn : 0 < n) : ∫ ω, kingmanMk hf n ω ∂μ = ∫ ω, f n ω ∂μ :=
  (integral_congr_ae (kingmanMk_ae hf hn)).symm

/-- The Fekete infima of a process and of its measurable representative agree. -/
lemma kingmanMk_fekete {f : ℕ → Ω → ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ) :
    kingmanFekete (kingmanMk hf) μ = kingmanFekete f μ := by
  unfold kingmanFekete
  congr 1
  ext a
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, by rw [kingmanMk_integral hf hn]⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, by rw [kingmanMk_integral hf hn]⟩

/-- The height truncation `max(f n, -K n)`. -/
def kingmanTrunc (K : ℕ) (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  max (f n ω) (-(K : ℝ) * (n : ℝ))

omit [MeasurableSpace Ω] in
/-- Truncation does not decrease the original value. -/
lemma kingmanTrunc_ge {K n : ℕ} {f : ℕ → Ω → ℝ} {ω : Ω} :
    f n ω ≤ kingmanTrunc K f n ω :=
  le_max_left _ _

omit [MeasurableSpace Ω] in
/-- A larger height cut produces a smaller truncation. -/
lemma kingmanTrunc_antitone {K K' n : ℕ} {f : ℕ → Ω → ℝ} {ω : Ω} (hK : K ≤ K') :
    kingmanTrunc K' f n ω ≤ kingmanTrunc K f n ω := by
  unfold kingmanTrunc
  have hmul : -(K' : ℝ) * (n : ℝ) ≤ -(K : ℝ) * (n : ℝ) := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have hneg : -(K' : ℝ) ≤ -(K : ℝ) := neg_le_neg (Nat.cast_le.mpr hK)
    exact mul_le_mul_of_nonneg_right hneg hn
  exact max_le_max le_rfl hmul

omit [MeasurableSpace Ω] in
/-- At a nonnegative height the truncation is bounded by the original absolute value. -/
lemma abs_kingmanTrunc_le {K n : ℕ} {f : ℕ → Ω → ℝ} {ω : Ω} :
    |kingmanTrunc K f n ω| ≤ |f n ω| := by
  unfold kingmanTrunc
  have hc : -(K : ℝ) * (n : ℝ) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  exact abs_max_le_abs_of_nonpos hc

/-- Truncation preserves measurability. -/
lemma measurable_kingmanTrunc {K n : ℕ} {f : ℕ → Ω → ℝ} (hf : Measurable (f n)) :
    Measurable (kingmanTrunc K f n) := by
  unfold kingmanTrunc
  exact hf.max measurable_const

/-- Truncation preserves integrability. -/
lemma integrable_kingmanTrunc {K n : ℕ} {f : ℕ → Ω → ℝ} (hf : Integrable (f n) μ)
    (hf_meas : Measurable (f n)) : Integrable (kingmanTrunc K f n) μ := by
  refine hf.abs.mono (measurable_kingmanTrunc hf_meas).aestronglyMeasurable ?_
  filter_upwards with ω
  have hnorm : ‖kingmanTrunc K f n ω‖ = |kingmanTrunc K f n ω| := Real.norm_eq_abs _
  have hdom : ‖|f n ω|‖ = |f n ω| := by
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
  rw [hnorm, hdom]
  exact abs_kingmanTrunc_le

omit [MeasurableSpace Ω] in
/-- The truncation stays above the linear floor `-K n`. -/
lemma kingmanTrunc_lower {K n : ℕ} {f : ℕ → Ω → ℝ} {ω : Ω} :
    -(K : ℝ) * (n : ℝ) ≤ kingmanTrunc K f n ω :=
  le_max_right _ _

omit [MeasurableSpace Ω] in
/-- Maxima add when the floors themselves add. -/
lemma max_add_max_le {a b p q : ℝ} : max (a + b) (p + q) ≤ max a p + max b q := by
  refine max_le ?_ ?_
  · exact add_le_add (le_max_left a p) (le_max_left b q)
  · exact add_le_add (le_max_right a p) (le_max_right b q)

/-- The height truncation of a subadditive process is subadditive. -/
lemma kingmanTrunc_subadditive {K : ℕ} {f : ℕ → Ω → ℝ}
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω)) :
    ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      kingmanTrunc K f (n + m) ω ≤
        kingmanTrunc K f n ω + kingmanTrunc K f m ((T^[n]) ω) := by
  intro n m hn hm
  filter_upwards [hsub n m hn hm] with ω hω
  unfold kingmanTrunc
  have hfloor : -(K : ℝ) * ((n + m : ℕ) : ℝ) =
      -(K : ℝ) * (n : ℝ) + -(K : ℝ) * (m : ℝ) := by
    rw [Nat.cast_add]
    ring
  have hle : max (f (n + m) ω) (-(K : ℝ) * ((n + m : ℕ) : ℝ)) ≤
      max (f n ω + f m ((T^[n]) ω))
        (-(K : ℝ) * (n : ℝ) + -(K : ℝ) * (m : ℝ)) := by
    rw [hfloor]
    exact max_le_max hω le_rfl
  exact hle.trans (max_add_max_le)

omit [MeasurableSpace Ω] in
/-- Normalized truncations are the original ratios cut at `-K`. -/
lemma kingmanRatio_trunc (K n : ℕ) (f : ℕ → Ω → ℝ) (ω : Ω) :
    kingmanRatio (kingmanTrunc K f) n ω = max (kingmanRatio f n ω) (-(K : ℝ)) := by
  unfold kingmanRatio kingmanTrunc
  rw [← Nat.cast_succ]
  have hpos : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
  rw [mul_max_of_nonneg _ _ hpos]
  have hcancel : ((n + 1 : ℕ) : ℝ)⁻¹ * (-(K : ℝ) * ((n + 1 : ℕ) : ℝ)) = -(K : ℝ) := by
    rw [mul_comm (-(K : ℝ)) ((n + 1 : ℕ) : ℝ), ← mul_assoc,
      inv_mul_cancel₀ (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0), one_mul]
  rw [hcancel]

omit [MeasurableSpace Ω] in
/-- Truncation raises the extended liminf exactly to `-K`. -/
lemma kingmanLiminf_trunc (K : ℕ) (f : ℕ → Ω → ℝ) (ω : Ω) :
    kingmanLiminf (kingmanTrunc K f) ω =
      max (kingmanLiminf f ω) (-((K : ℝ) : EReal)) := by
  unfold kingmanLiminf
  have hrat : ∀ n, (kingmanRatio (kingmanTrunc K f) n ω : EReal) =
      (kingmanRatio f n ω : EReal) ⊔ -((K : ℝ) : EReal) := by
    intro n
    rw [kingmanRatio_trunc, ereal_coe_max, EReal.coe_neg, ereal_max_eq_sup]
  have hswap : (fun n => (kingmanRatio f n ω : EReal) ⊔ -((K : ℝ) : EReal)) =
      fun n => -((K : ℝ) : EReal) ⊔ (kingmanRatio f n ω : EReal) := by
    ext n
    exact sup_comm _ _
  simp_rw [hrat, hswap]
  rw [← sup_liminf (f := atTop) (u := fun n => (kingmanRatio f n ω : EReal))
    (-((K : ℝ) : EReal)), sup_comm, ← ereal_max_eq_sup]

omit [MeasurableSpace Ω] in
/-- Truncation raises the extended limsup exactly to `-K`. -/
lemma kingmanLimsup_trunc (K : ℕ) (f : ℕ → Ω → ℝ) (ω : Ω) :
    kingmanLimsup (kingmanTrunc K f) ω =
      max (kingmanLimsup f ω) (-((K : ℝ) : EReal)) := by
  unfold kingmanLimsup
  have hrat : ∀ n, (kingmanRatio (kingmanTrunc K f) n ω : EReal) =
      (kingmanRatio f n ω : EReal) ⊔ -((K : ℝ) : EReal) := by
    intro n
    rw [kingmanRatio_trunc, ereal_coe_max, EReal.coe_neg, ereal_max_eq_sup]
  have hswap : (fun n => (kingmanRatio f n ω : EReal) ⊔ -((K : ℝ) : EReal)) =
      fun n => -((K : ℝ) : EReal) ⊔ (kingmanRatio f n ω : EReal) := by
    ext n
    exact sup_comm _ _
  simp_rw [hrat, hswap]
  rw [← sup_limsup (f := atTop) (u := fun n => (kingmanRatio f n ω : EReal))
    (-((K : ℝ) : EReal)), sup_comm, ← ereal_max_eq_sup]

/-- Normalized integrals of a fixed length pass to the limit under truncation. -/
lemma tendsto_integral_kingmanTrunc [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} {n : ℕ}
    (hn : 0 < n) (hf : Integrable (f n) μ) (hf_meas : Measurable (f n)) :
    Tendsto (fun K : ℕ => (n : ℝ)⁻¹ * ∫ ω, kingmanTrunc K f n ω ∂μ) atTop
      (𝓝 ((n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ)) := by
  have hint : Tendsto (fun K : ℕ => ∫ ω, kingmanTrunc K f n ω ∂μ) atTop
      (𝓝 (∫ ω, f n ω ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => |f n ω|)
      (fun K => (measurable_kingmanTrunc hf_meas).aestronglyMeasurable) hf.abs
      (fun K => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
    · rw [Real.norm_eq_abs]
      exact abs_kingmanTrunc_le
    · refine (tendsto_const_nhds (x := f n ω)).congr' ?_
      unfold Filter.EventuallyEq
      rw [eventually_atTop]
      refine ⟨Nat.ceil ((-f n ω) / (n : ℝ)), fun K hK => ?_⟩
      have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      have hceil : (-f n ω) / (n : ℝ) ≤ (K : ℝ) := Nat.ceil_le.mp hK
      have hfloor : -(K : ℝ) * (n : ℝ) ≤ f n ω := by
        have hmul : -f n ω ≤ (K : ℝ) * (n : ℝ) := (div_le_iff₀ hnpos).mp hceil
        linarith
      unfold kingmanTrunc
      exact (max_eq_left hfloor).symm
  exact hint.const_mul (n : ℝ)⁻¹

/-- Every truncated Fekete value lies above the untruncated one. -/
lemma kingmanFekete_le_trunc [IsProbabilityMeasure μ] {K : ℕ} {f : ℕ → Ω → ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ) :
    kingmanFekete f μ ≤ kingmanFekete (kingmanTrunc K f) μ := by
  unfold kingmanFekete
  obtain ⟨c, hc⟩ := hlower
  refine le_csInf ⟨((1 : ℕ) : ℝ)⁻¹ * ∫ ω, kingmanTrunc K f 1 ω ∂μ,
      ⟨1, Nat.one_pos, rfl⟩⟩ ?_
  rintro b ⟨n, hn, rfl⟩
  have hbdd : BddBelow {a : ℝ | ∃ m : ℕ, 0 < m ∧ a = (m : ℝ)⁻¹ * ∫ ω, f m ω ∂μ} := by
    refine ⟨c, ?_⟩
    rintro a ⟨m, hm, rfl⟩
    exact hc m hm
  have ha : sInf {a : ℝ | ∃ m : ℕ, 0 < m ∧ a = (m : ℝ)⁻¹ * ∫ ω, f m ω ∂μ} ≤
      (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ :=
    csInf_le hbdd ⟨n, hn, rfl⟩
  have hmono : (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ ≤
      (n : ℝ)⁻¹ * ∫ ω, kingmanTrunc K f n ω ∂μ := by
    have hint : ∫ ω, f n ω ∂μ ≤ ∫ ω, kingmanTrunc K f n ω ∂μ :=
      integral_mono (hf n hn) (integrable_kingmanTrunc (hf n hn) (hf_meas n hn))
        fun ω => kingmanTrunc_ge
    exact mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact ha.trans hmono

end CKMA
