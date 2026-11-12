/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Ergodic.Pointwise.KingmanFull

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Kingman's theorem by truncation

Height cuts reduce a measurable subadditive process to the linearly bounded case. The bad set
where the limsup is `⊥` is null because its truncated means fall below the Fekete lower bound.
Monotone convergence identifies the mean, and the truncated L¹ convergence passes to the limit.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Set MeasureTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

attribute [local instance] Classical.propDecidable

omit [MeasurableSpace Ω] in
/-- An extended real lying under every negative integer is `⊥`. -/
lemma ereal_eq_bot_of_forall_le_neg {x : EReal}
    (h : ∀ n : ℕ, x ≤ -((n : ℝ) : EReal)) : x = ⊥ := by
  cases x with
  | bot => rfl
  | top =>
      exfalso
      exact not_le_of_gt (EReal.coe_lt_top (-((1 : ℕ) : ℝ)))
        ((h 1).trans_eq (EReal.coe_neg ((1 : ℕ) : ℝ)).symm)
  | coe r =>
      obtain ⟨n, hn⟩ := exists_nat_gt (-r)
      have hle : r ≤ -(n : ℝ) := by
        have hcoe : (r : EReal) ≤ ↑(-(n : ℝ)) := by
          simpa [EReal.coe_neg] using h n
        exact EReal.coe_le_coe_iff.mp hcoe
      linarith

/-- The L¹ seminorm is the `ofReal` of the integral of the absolute value. -/
lemma eLpNorm_one_eq_ofReal_abs {w : Ω → ℝ} (hw : AEStronglyMeasurable w μ)
    (hi : Integrable w μ) :
    eLpNorm w 1 μ = ENNReal.ofReal (∫ ω, |w ω| ∂μ) := by
  have habs : Integrable (fun ω => |w ω|) μ := hi.abs
  have hnn : 0 ≤ᵐ[μ] fun ω => |w ω| := Eventually.of_forall fun _ => abs_nonneg _
  rw [eLpNorm_one_eq_lintegral_enorm hw]
  have hfun : (fun ω => ‖w ω‖ₑ) = fun ω => ENNReal.ofReal |w ω| := by
    ext ω
    exact Real.enorm_eq_ofReal_abs _
  rw [hfun, ← ofReal_integral_eq_lintegral_ofReal habs hnn]

/-- Truncated Fekete values decrease to the untruncated infimum. -/
lemma tendsto_kingmanFekete_trunc [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ) :
    Tendsto (fun K : ℕ => kingmanFekete (kingmanTrunc K f) μ) atTop
      (𝓝 (kingmanFekete f μ)) := by
  set L : ℝ := kingmanFekete f μ
  set LK : ℕ → ℝ := fun K => kingmanFekete (kingmanTrunc K f) μ
  have hL_le : ∀ K, L ≤ LK K := fun K => kingmanFekete_le_trunc hf hf_meas hlower
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨a, haMem, haLt⟩ := exists_lt_of_csInf_lt
    (s := {a : ℝ | ∃ n : ℕ, 0 < n ∧ a = (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ})
    ⟨((1 : ℕ) : ℝ)⁻¹ * ∫ ω, f 1 ω ∂μ, ⟨1, Nat.one_pos, rfl⟩⟩
    (lt_add_of_pos_right (kingmanFekete f μ) hε)
  rcases haMem with ⟨n, hn, rfl⟩
  have htr := tendsto_integral_kingmanTrunc hn (hf n hn) (hf_meas n hn)
  filter_upwards [htr.eventually (isOpen_Iio.mem_nhds haLt)] with K hK
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hL_le K))]
  have hLK_le : LK K ≤ (n : ℝ)⁻¹ * ∫ ω, kingmanTrunc K f n ω ∂μ := by
    have hbdd : BddBelow {x : ℝ | ∃ m : ℕ, 0 < m ∧
        x = (m : ℝ)⁻¹ * ∫ ω, kingmanTrunc K f m ω ∂μ} := by
      obtain ⟨c, hc⟩ := hlower
      refine ⟨c, ?_⟩
      rintro x ⟨m, hm, rfl⟩
      have hmono : ∫ ω, f m ω ∂μ ≤ ∫ ω, kingmanTrunc K f m ω ∂μ :=
        integral_mono (hf m hm)
          (integrable_kingmanTrunc (hf m hm) (hf_meas m hm)) fun _ => kingmanTrunc_ge
      exact (hc m hm).trans (mul_le_mul_of_nonneg_left hmono
        (inv_nonneg.mpr (Nat.cast_nonneg _)))
    simpa [LK, kingmanFekete] using csInf_le hbdd ⟨n, hn, rfl⟩
  linarith [hLK_le.trans_lt hK]

/-- A measurable subadditive process has an invariant Kingman limit with the Fekete mean. -/
lemma kingman_limit_of_measurable [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ) :
    Integrable (kingmanLiminfReal f) μ ∧
      (kingmanLiminfReal f ∘ T =ᵐ[μ] kingmanLiminfReal f) ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹ * f (n + 1) ω) atTop
        (𝓝 (kingmanLiminfReal f ω))) ∧
      (∫ ω, kingmanLiminfReal f ω ∂μ) = kingmanFekete f μ ∧
      (∀ᵐ ω ∂μ, ∀ K : ℕ, kingmanLiminfReal (kingmanTrunc K f) ω =
        max (kingmanLiminfReal f ω) (-(K : ℝ))) := by
  have htrunc_int : ∀ K n, 0 < n → Integrable (kingmanTrunc K f n) μ :=
    fun K n hn => integrable_kingmanTrunc (hf n hn) (hf_meas n hn)
  have htrunc_meas : ∀ K n, 0 < n → Measurable (kingmanTrunc K f n) :=
    fun K n hn => measurable_kingmanTrunc (hf_meas n hn)
  have htrunc_C : ∀ K : ℕ, ∀ n : ℕ, 0 < n → ∀ ω,
      -(K : ℝ) * (n : ℝ) ≤ kingmanTrunc K f n ω :=
    fun K n hn ω => kingmanTrunc_lower
  let gK : ℕ → Ω → ℝ := fun K => kingmanLiminfReal (kingmanTrunc K f)
  let LK : ℕ → ℝ := fun K => kingmanFekete (kingmanTrunc K f) μ
  let g : Ω → ℝ := kingmanLiminfReal f
  let L : ℝ := kingmanFekete f μ
  have hratioK : ∀ᵐ ω ∂μ, ∀ K, Tendsto (fun n => kingmanRatio (kingmanTrunc K f) n ω)
      atTop (𝓝 (gK K ω)) :=
    (ae_all_iff).2 fun K => by
      simpa [gK, kingmanRatio] using kingmanRatio_ae_tendsto_linear hT (htrunc_int K)
        (htrunc_meas K) (kingmanTrunc_subadditive hsub) (htrunc_C K)
  have hinvK : ∀ᵐ ω ∂μ, ∀ K, gK K (T ω) = gK K ω :=
    (ae_all_iff).2 fun K => by
      have h := kingmanLiminfReal_ae_invariant hT (htrunc_int K) (htrunc_meas K)
        (kingmanTrunc_subadditive hsub) (htrunc_C K)
      filter_upwards [h] with ω hω
      simpa [gK, Function.comp_apply] using hω
  have hgK_int : ∀ K, Integrable (gK K) μ := fun K =>
    (kingmanLiminfReal_integrable_le hT (htrunc_int K) (htrunc_meas K)
      (kingmanTrunc_subadditive hsub) (htrunc_C K)).1
  have hintK : ∀ K, ∫ ω, gK K ω ∂μ = LK K := by
    intro K
    simpa [gK, LK, kingmanFekete] using kingmanLiminfReal_integral_eq hT (htrunc_int K)
      (htrunc_meas K) (kingmanTrunc_subadditive hsub) (htrunc_C K)
  have hL_le : ∀ K, L ≤ LK K := fun K => kingmanFekete_le_trunc hf hf_meas hlower
  have hLK_tend : Tendsto LK atTop (𝓝 L) := by
    simpa [LK, L] using tendsto_kingmanFekete_trunc hf hf_meas hlower
  have hmax : ∀ᵐ ω ∂μ, ∀ K : ℕ,
      max (kingmanLiminf f ω) (-((K : ℝ) : EReal)) = (gK K ω : EReal) ∧
      max (kingmanLimsup f ω) (-((K : ℝ) : EReal)) = (gK K ω : EReal) := by
    filter_upwards [hratioK] with ω hω K
    have hE := (EReal.tendsto_coe).2 (hω K)
    have hinf : kingmanLiminf (kingmanTrunc K f) ω = (gK K ω : EReal) := by
      simpa [kingmanLiminf] using hE.liminf_eq
    have hsup : kingmanLimsup (kingmanTrunc K f) ω = (gK K ω : EReal) := by
      simpa [kingmanLimsup] using hE.limsup_eq
    constructor
    · simpa [kingmanLiminf_trunc] using hinf
    · simpa [kingmanLimsup_trunc] using hsup
  have hsup_le : ∀ ω, kingmanLimsup f ω ≤ kingmanLimsup (kingmanTrunc 0 f) ω := by
    intro ω
    unfold kingmanLimsup
    refine limsup_le_limsup (Eventually.of_forall fun n => ?_)
    refine EReal.coe_le_coe_iff.mpr ?_
    unfold kingmanRatio
    exact mul_le_mul_of_nonneg_left (kingmanTrunc_ge (K := 0))
      (inv_nonneg.mpr (by positivity))
  have hsup_ne_top : ∀ᵐ ω ∂μ, kingmanLimsup f ω ≠ ⊤ := by
    have h0 := kingmanLimsup_ae_ne_top hT (htrunc_int 0) (htrunc_meas 0)
      (kingmanTrunc_subadditive hsub) (htrunc_C 0)
    filter_upwards [h0] with ω hω htop
    have hle := hsup_le ω
    rw [htop] at hle
    exact hω (top_le_iff.mp hle)
  have horder : ∀ ω, kingmanLiminf f ω ≤ kingmanLimsup f ω := fun ω =>
    liminf_le_limsup (u := fun n => (kingmanRatio f n ω : EReal))
  let A : Set Ω := {ω | kingmanLimsup f ω = ⊥}
  have hA_meas : MeasurableSet A := by
    have hEq : A = ⋂ n : ℕ, kingmanLimsup f ⁻¹' Iic (-((n : ℝ) : EReal)) := by
      ext ω
      simp only [A, mem_ofPred_eq, mem_iInter, mem_preimage, mem_Iic]
      constructor
      · intro hbot n
        exact hbot.symm ▸ (bot_le : ⊥ ≤ -((n : ℝ) : EReal))
      · intro h
        exact ereal_eq_bot_of_forall_le_neg h
    rw [hEq]
    exact MeasurableSet.iInter fun n =>
      (isClosed_Iic.measurableSet).preimage (measurable_kingmanLimsup hf_meas)
  have honA : ∀ᵐ ω ∂μ, ∀ K, ω ∈ A → gK K ω = -(K : ℝ) := by
    filter_upwards [hmax] with ω hω K hmem
    have hmaxK := (hω K).2
    rw [show kingmanLimsup f ω = ⊥ from hmem, max_eq_right bot_le] at hmaxK
    exact (EReal.coe_injective ((EReal.coe_neg (K : ℝ)).symm.trans hmaxK)).symm
  have hmon : ∀ K ω, kingmanLiminf (kingmanTrunc K f) ω ≤
      kingmanLiminf (kingmanTrunc 0 f) ω := by
    intro K ω
    unfold kingmanLiminf
    refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
    refine EReal.coe_le_coe_iff.mpr ?_
    unfold kingmanRatio
    exact mul_le_mul_of_nonneg_left (kingmanTrunc_antitone (Nat.zero_le K))
      (inv_nonneg.mpr (by positivity))
  have htoReal : ∀ᵐ ω ∂μ, ∀ K, gK K ω ≤ gK 0 ω := by
    have hfin := (kingmanLiminfReal_integrable_le hT (htrunc_int 0) (htrunc_meas 0)
      (kingmanTrunc_subadditive hsub) (htrunc_C 0)).2.2.1
    filter_upwards [hfin] with ω htop K
    have hreal := EReal.toReal_le_toReal (hmon K ω)
      (kingmanLiminf_ne_bot (htrunc_C K) ω) htop
    simpa [gK, kingmanLiminfReal] using hreal
  have habs : ∀ᵐ ω ∂μ, ∀ K, gK K ω ≤ |gK 0 ω| := by
    filter_upwards [htoReal] with ω hω K
    exact (hω K).trans (le_abs_self _)
  have hA_null : μ A = 0 := by
    have hnonneg : (0 : ℝ) ≤ μ.real A := ENNReal.toReal_nonneg
    suffices hle : μ.real A ≤ 0 by
      have heq : μ.real A = 0 := le_antisymm hle hnonneg
      rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at heq
      exact heq.resolve_right (measure_ne_top μ A)
    by_contra hgt
    have hμpos : 0 < μ.real A := lt_of_not_ge hgt
    obtain ⟨c, hc⟩ := hlower
    have hcL : c ≤ L := by
      unfold L kingmanFekete
      refine le_csInf ⟨((1 : ℕ) : ℝ)⁻¹ * ∫ ω, f 1 ω ∂μ, ⟨1, Nat.one_pos, rfl⟩⟩ ?_
      rintro a ⟨n, hn, rfl⟩
      exact hc n hn
    let B : ℝ := ∫ ω, |gK 0 ω| ∂μ
    have hBint : Integrable (fun ω => |gK 0 ω|) μ := (hgK_int 0).abs
    let Knat : ℕ := Nat.ceil ((B - c) / μ.real A) + 1
    have hdiv : (B - c) / μ.real A < (Knat : ℝ) := by
      have hceil : (B - c) / μ.real A ≤ ↑(Nat.ceil ((B - c) / μ.real A)) := Nat.le_ceil _
      have hsucc : ↑(Nat.ceil ((B - c) / μ.real A)) + 1 = (Knat : ℝ) := by
        simp [Knat, Nat.cast_add, Nat.cast_one]
      exact lt_of_le_of_lt hceil (by
        rw [← hsucc]
        exact lt_add_of_pos_right _ one_pos)
    have hmul : B - c < (Knat : ℝ) * μ.real A := (div_lt_iff₀ hμpos).mp hdiv
    have hAeq : ∫ ω in A, gK Knat ω ∂μ = μ.real A * -(Knat : ℝ) := by
      have hmem : ∀ᵐ ω ∂μ, ω ∈ A → gK Knat ω = -(Knat : ℝ) := by
        filter_upwards [honA] with ω hω hAω
        exact hω Knat hAω
      rw [setIntegral_congr_ae hA_meas hmem, setIntegral_const, smul_eq_mul]
    have hcompl : ∫ ω in Aᶜ, gK Knat ω ∂μ ≤ B := by
      have hmonoI : ∫ ω in Aᶜ, gK Knat ω ∂μ ≤ ∫ ω in Aᶜ, |gK 0 ω| ∂μ :=
        setIntegral_mono_ae (s := Aᶜ) (hf := (hgK_int Knat).integrableOn (s := Aᶜ))
          (hg := hBint.integrableOn (s := Aᶜ)) (by
            filter_upwards [habs] with ω hω
            exact hω Knat)
      exact hmonoI.trans (setIntegral_le_integral hBint
        (Eventually.of_forall fun _ => abs_nonneg _))
    have hupper : ∫ ω, gK Knat ω ∂μ < c := by
      rw [← integral_add_compl hA_meas (hgK_int Knat), hAeq]
      have hmoved : B < c + (Knat : ℝ) * μ.real A := (sub_lt_iff_lt_add').mp hmul
      have hsub : B - (Knat : ℝ) * μ.real A < c := by
        rw [add_comm] at hmoved
        exact (sub_lt_iff_lt_add').mpr hmoved
      have hneg : -((Knat : ℝ) * μ.real A) = μ.real A * -(Knat : ℝ) := by
        rw [mul_comm (Knat : ℝ) (μ.real A), mul_neg]
      have hsum : B + μ.real A * -(Knat : ℝ) < c := by
        rw [← hneg, ← sub_eq_add_neg]
        exact hsub
      have hhalf : μ.real A * -(Knat : ℝ) + B < c := by
        rw [add_comm]
        exact hsum
      have hle : μ.real A * -(Knat : ℝ) + ∫ ω in Aᶜ, gK Knat ω ∂μ ≤
          μ.real A * -(Knat : ℝ) + B := by
        have hright := add_le_add_left hcompl (μ.real A * -(Knat : ℝ))
        rw [add_comm (∫ ω in Aᶜ, gK Knat ω ∂μ), add_comm B] at hright
        exact hright
      exact lt_of_le_of_lt hle hhalf
    have hge : c ≤ ∫ ω, gK Knat ω ∂μ := by
      rw [hintK]
      exact hcL.trans (hL_le Knat)
    exact not_lt_of_ge hge hupper
  have hA0 : ∀ᵐ ω ∂μ, ω ∉ A := (measure_eq_zero_iff_ae_notMem).1 hA_null
  have hgood : ∀ᵐ ω ∂μ, kingmanLiminf f ω = (g ω : EReal) ∧
      kingmanLimsup f ω = (g ω : EReal) := by
    filter_upwards [hmax, hsup_ne_top, hA0] with ω hmaxω htop hAω
    have hbot : kingmanLimsup f ω ≠ ⊥ := by
      simpa [A] using hAω
    have heq := ereal_eq_of_max_neg (horder ω) htop hbot fun K => by
      rw [(hmaxω K).1, (hmaxω K).2]
    have hcoe := (EReal.coe_toReal (heq ▸ htop) (heq ▸ hbot)).symm
    exact ⟨hcoe.trans (by simp [g, kingmanLiminfReal]), heq.symm.trans hcoe |>.trans
      (by simp [g, kingmanLiminfReal])⟩
  have hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => kingmanRatio f n ω) atTop (𝓝 (g ω)) := by
    filter_upwards [hgood] with ω hω
    have hsame : kingmanLiminf f ω = kingmanLimsup f ω := by rw [hω.1, hω.2]
    have htendE : Tendsto (fun n => (kingmanRatio f n ω : EReal)) atTop
        (𝓝 (kingmanLiminf f ω)) := by
      apply tendsto_of_liminf_eq_limsup
        (u := fun n => (kingmanRatio f n ω : EReal)) (a := kingmanLiminf f ω)
      · rfl
      · simpa [kingmanLiminf, kingmanLimsup] using hsame.symm
    rw [hω.1] at htendE
    simpa [g] using (EReal.tendsto_coe).1 htendE
  have hcut : ∀ᵐ ω ∂μ, ∀ K, gK K ω = max (g ω) (-(K : ℝ)) := by
    filter_upwards [hmax, hgood] with ω hmaxω hgoodω K
    have hmaxg := (hmaxω K).1
    rw [hgoodω.1, ← EReal.coe_neg (K : ℝ), ← ereal_coe_max] at hmaxg
    exact (EReal.coe_injective hmaxg).symm
  have hinv : g ∘ T =ᵐ[μ] g := by
    have hcutT := hT.quasiMeasurePreserving.ae hcut
    filter_upwards [hcut, hcutT, hinvK] with ω hcutω hcutTω hinvω
    let K : ℕ := Nat.ceil (max (-g ω) (-g (T ω)))
    have hceil : max (-g ω) (-g (T ω)) ≤ (K : ℝ) := Nat.le_ceil _
    have hωle : -(K : ℝ) ≤ g ω := by
      refine (neg_le_neg hceil).trans ?_
      calc -(max (-g ω) (-g (T ω))) ≤ -(-g ω) := neg_le_neg (le_max_left _ _)
        _ = g ω := neg_neg _
    have hTle : -(K : ℝ) ≤ g (T ω) := by
      refine (neg_le_neg hceil).trans ?_
      calc -(max (-g ω) (-g (T ω))) ≤ -(-g (T ω)) := neg_le_neg (le_max_right _ _)
        _ = g (T ω) := neg_neg _
    calc g (T ω) = gK K (T ω) := by rw [hcutTω K, max_eq_left hTle]
      _ = gK K ω := hinvω K
      _ = g ω := by rw [hcutω K, max_eq_left hωle]
  let cut : ℕ → Ω → ℝ := fun K ω => max (g ω) (-(K : ℝ))
  have hg_meas : Measurable g := (measurable_kingmanLiminf hf_meas).ereal_toReal
  have hcut_meas : ∀ K, Measurable (cut K) := fun K => hg_meas.max measurable_const
  have hcut_ae : ∀ K, gK K =ᵐ[μ] cut K := by
    intro K
    filter_upwards [hcut] with ω hω
    exact hω K
  have hcut_int : ∀ K, Integrable (cut K) μ := fun K => (hgK_int K).congr (hcut_ae K)
  have hcut_integral : ∀ K, ∫ ω, cut K ω ∂μ = LK K := by
    intro K
    rw [← integral_congr_ae (hcut_ae K), hintK K]
  have hpt : ∀ ω, Tendsto (fun K => cut K ω) atTop (𝓝 (g ω)) := by
    intro ω
    refine (tendsto_const_nhds (x := g ω)).congr' ?_
    unfold Filter.EventuallyEq
    rw [eventually_atTop]
    refine ⟨Nat.ceil (-g ω), fun K hK => ?_⟩
    have hceil : -g ω ≤ ↑(Nat.ceil (-g ω)) := Nat.le_ceil _
    have hcast : ↑(Nat.ceil (-g ω)) ≤ (K : ℝ) := Nat.cast_le.mpr hK
    have hlow : -↑(Nat.ceil (-g ω)) ≤ g ω := by simpa using (neg_le_neg hceil)
    have hle : -(K : ℝ) ≤ g ω := (neg_le_neg hcast).trans hlow
    exact (max_eq_left hle).symm
  have hlin : Tendsto (fun K : ℕ => ∫⁻ ω, ENNReal.ofReal (cut 0 ω - cut K ω) ∂μ) atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (cut 0 ω - g ω) ∂μ)) :=
    lintegral_tendsto_of_tendsto_of_monotone (μ := μ)
      (fun K => ((hcut_meas 0).sub (hcut_meas K)).ennreal_ofReal.aemeasurable)
      (Eventually.of_forall fun ω K K' hK =>
        ENNReal.ofReal_le_ofReal (sub_le_sub_left
          (max_le_max le_rfl (neg_le_neg (Nat.cast_le.mpr hK))) (cut 0 ω)))
      (Eventually.of_forall fun ω =>
        (ENNReal.continuous_ofReal.tendsto (cut 0 ω - g ω)).comp
          ((tendsto_const_nhds (x := cut 0 ω)).sub (hpt ω)))
  have hlin_eq : ∀ K, ∫⁻ ω, ENNReal.ofReal (cut 0 ω - cut K ω) ∂μ =
      ENNReal.ofReal (LK 0 - LK K) := by
    intro K
    have hnn : 0 ≤ᵐ[μ] cut 0 - cut K := Eventually.of_forall fun ω => by
      rw [Pi.sub_apply]
      refine sub_nonneg.mpr ?_
      show cut K ω ≤ cut 0 ω
      unfold cut
      exact max_le_max le_rfl (neg_le_neg (Nat.cast_le.mpr (Nat.zero_le K)))
    have hfun : (fun ω => ENNReal.ofReal (cut 0 ω - cut K ω)) =
        fun ω => ENNReal.ofReal ((cut 0 - cut K) ω) := by
      ext ω
      rw [Pi.sub_apply]
    rw [hfun, ← ofReal_integral_eq_lintegral_ofReal ((hcut_int 0).sub (hcut_int K)) hnn,
      integral_sub' (hcut_int 0) (hcut_int K), hcut_integral 0, hcut_integral K]
  have hOf : ∫⁻ ω, ENNReal.ofReal (cut 0 ω - g ω) ∂μ =
      ENNReal.ofReal (LK 0 - L) := by
    have hlim : Tendsto (fun K : ℕ => ENNReal.ofReal (LK 0 - LK K)) atTop
        (𝓝 (ENNReal.ofReal (LK 0 - L))) :=
      (ENNReal.continuous_ofReal.tendsto (LK 0 - L)).comp
        ((tendsto_const_nhds (x := LK 0)).sub hLK_tend)
    have hcongr : Tendsto (fun K : ℕ => ENNReal.ofReal (LK 0 - LK K)) atTop
        (𝓝 (∫⁻ ω, ENNReal.ofReal (cut 0 ω - g ω) ∂μ)) :=
      hlin.congr fun K => hlin_eq K
    exact tendsto_nhds_unique hcongr hlim
  have hdiff_nn : 0 ≤ᵐ[μ] fun ω => cut 0 ω - g ω :=
    Eventually.of_forall fun ω => sub_nonneg.mpr (le_max_left _ _)
  have hdiff_int : Integrable (fun ω => cut 0 ω - g ω) μ := by
    refine ⟨((hcut_meas 0).sub hg_meas).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal hdiff_nn).2 (by
      rw [hOf]
      exact ENNReal.ofReal_lt_top)
  have hg_int : Integrable g μ := by
    have hsubI : Integrable (fun ω => cut 0 ω - (cut 0 ω - g ω)) μ :=
      (hcut_int 0).sub hdiff_int
    exact hsubI.congr (Eventually.of_forall fun ω => sub_sub_cancel _ _)
  have hint_diff : ∫ ω, cut 0 ω - g ω ∂μ = LK 0 - L := by
    have hnnI : 0 ≤ ∫ ω, cut 0 ω - g ω ∂μ := integral_nonneg fun ω =>
      sub_nonneg.mpr (le_max_left _ _)
    have hLnn : 0 ≤ LK 0 - L := sub_nonneg.mpr (hL_le 0)
    have hOfI : ENNReal.ofReal (∫ ω, cut 0 ω - g ω ∂μ) =
        ENNReal.ofReal (LK 0 - L) := by
      rw [ofReal_integral_eq_lintegral_ofReal hdiff_int hdiff_nn, hOf]
    have hto := congrArg ENNReal.toReal hOfI
    rwa [ENNReal.toReal_ofReal hnnI, ENNReal.toReal_ofReal hLnn] at hto
  have hint_g : ∫ ω, g ω ∂μ = L := by
    have hsubeq := integral_sub (hcut_int 0) hg_int
    rw [hcut_integral 0, hint_diff] at hsubeq
    exact (sub_right_inj.mp hsubeq).symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [g] using hg_int
  · simpa [g] using hinv
  · simpa [g, kingmanRatio] using hconv
  · simpa [g, L] using hint_g
  · simpa [g, gK] using hcut

/-- Normalized lengths of a measurable subadditive process converge in L¹. -/
lemma kingman_eLpNorm_of_measurable [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun ω => (n + 1 : ℝ)⁻¹ * f (n + 1) ω - kingmanLiminfReal f ω) 1 μ) atTop (𝓝 0) := by
  obtain ⟨hg_int, -, -, hint_g, hcut⟩ :=
    kingman_limit_of_measurable hT hf hf_meas hsub hlower
  let g : Ω → ℝ := kingmanLiminfReal f
  let L : ℝ := kingmanFekete f μ
  have hg_meas : Measurable g := (measurable_kingmanLiminf hf_meas).ereal_toReal
  have hLK_tend : Tendsto (fun K : ℕ => kingmanFekete (kingmanTrunc K f) μ) atTop (𝓝 L) := by
    simpa [L] using tendsto_kingmanFekete_trunc hf hf_meas hlower
  have hL_le : ∀ K, L ≤ kingmanFekete (kingmanTrunc K f) μ :=
    fun K => kingmanFekete_le_trunc hf hf_meas hlower
  have hint_abs : Tendsto (fun n : ℕ =>
      ∫ ω, |kingmanRatio f n ω - g ω| ∂μ) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have h4pos : (0 : ℝ) < 4 := Nat.cast_pos.mpr (by decide : 0 < 4)
    have hε4 : 0 < ε / 4 := div_pos hε h4pos
    obtain ⟨K0, hK0⟩ := (Metric.tendsto_atTop.mp hLK_tend) (ε / 4) hε4
    let K : ℕ := K0
    let FK : ℝ := kingmanFekete (kingmanTrunc K f) μ
    have hδ : FK - L < ε / 4 := by
      have hdist := hK0 K le_rfl
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hL_le K))] at hdist
      exact hdist
    let gK : Ω → ℝ := kingmanLiminfReal (kingmanTrunc K f)
    let ρ : ℕ → Ω → ℝ := kingmanRatio f
    let ρK : ℕ → Ω → ℝ := kingmanRatio (kingmanTrunc K f)
    have htrunc_int : ∀ n, 0 < n → Integrable (kingmanTrunc K f n) μ :=
      fun n hn => integrable_kingmanTrunc (hf n hn) (hf_meas n hn)
    have htrunc_meas : ∀ n, 0 < n → Measurable (kingmanTrunc K f n) :=
      fun n hn => measurable_kingmanTrunc (hf_meas n hn)
    have hC : ∀ n : ℕ, 0 < n → ∀ ω, -(K : ℝ) * (n : ℝ) ≤ kingmanTrunc K f n ω :=
      fun _ _ _ => kingmanTrunc_lower
    have hgK_int : Integrable gK μ :=
      (kingmanLiminfReal_integrable_le hT htrunc_int htrunc_meas
        (kingmanTrunc_subadditive hsub) hC).1
    have hintK : ∫ ω, gK ω ∂μ = FK := by
      simpa [gK, FK, kingmanFekete] using kingmanLiminfReal_integral_eq hT htrunc_int
        htrunc_meas (kingmanTrunc_subadditive hsub) hC
    have hlowerK : ∃ c : ℝ, ∀ n : ℕ, 0 < n →
        c ≤ (n : ℝ)⁻¹ * ∫ ω, kingmanTrunc K f n ω ∂μ := by
      obtain ⟨c, hc⟩ := hlower
      refine ⟨c, fun n hn => ?_⟩
      exact (hc n hn).trans (mul_le_mul_of_nonneg_left
        (integral_mono (hf n hn) (htrunc_int n hn) fun _ => kingmanTrunc_ge)
        (inv_nonneg.mpr (Nat.cast_nonneg n)))
    have hdivK := tendsto_kingmanIntegral_div hT htrunc_int
      (kingmanTrunc_subadditive hsub) hlowerK
    have hdiv := tendsto_kingmanIntegral_div hT hf hsub hlower
    have hu_eq : ∀ n, ∫ ω, ρK n ω - ρ n ω ∂μ =
        (n + 1 : ℝ)⁻¹ * ∫ ω, kingmanTrunc K f (n + 1) ω ∂μ -
          (n + 1 : ℝ)⁻¹ * ∫ ω, f (n + 1) ω ∂μ := by
      intro n
      rw [integral_sub (integrable_kingmanRatio htrunc_int n) (integrable_kingmanRatio hf n)]
      simp only [kingmanRatio, integral_const_mul]
    have hu_tend : Tendsto (fun n => ∫ ω, ρK n ω - ρ n ω ∂μ) atTop (𝓝 (FK - L)) := by
      simpa [FK, L, kingmanFekete] using (hdivK.sub hdiv).congr fun n => (hu_eq n).symm
    have hLpK : Tendsto (fun n => eLpNorm (fun ω => ρK n ω - gK ω) 1 μ) atTop (𝓝 0) := by
      simpa [ρK, gK, kingmanRatio] using kingman_eLpNorm_tendsto_of_linear hT htrunc_int
        htrunc_meas (kingmanTrunc_subadditive hsub) hC
    have hv_eq : ∀ n, ∫ ω, |ρK n ω - gK ω| ∂μ =
        (eLpNorm (fun ω => ρK n ω - gK ω) 1 μ).toReal := by
      intro n
      have hsubI : Integrable (fun ω => ρK n ω - gK ω) μ :=
        (integrable_kingmanRatio htrunc_int n).sub' hgK_int
      have hmeas : AEStronglyMeasurable (fun ω => ρK n ω - gK ω) μ :=
        ((measurable_kingmanRatio (htrunc_meas (n + 1) (Nat.succ_pos n))).aestronglyMeasurable).sub
          hgK_int.aestronglyMeasurable
      rw [eLpNorm_one_eq_ofReal_abs hmeas hsubI, ENNReal.toReal_ofReal
        (integral_nonneg fun _ => abs_nonneg _)]
    have hv_tend : Tendsto (fun n => ∫ ω, |ρK n ω - gK ω| ∂μ) atTop (𝓝 0) := by
      have hto := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hLpK
      rw [ENNReal.toReal_zero] at hto
      exact hto.congr fun n => (hv_eq n).symm
    have hw_eq : ∫ ω, |gK ω - g ω| ∂μ = FK - L := by
      have hnn : 0 ≤ᵐ[μ] fun ω => gK ω - g ω := by
        filter_upwards [hcut] with ω hω
        refine sub_nonneg.mpr ?_
        rw [show gK ω = max (g ω) (-(K : ℝ)) from by simpa [gK, g] using hω K]
        exact le_max_left _ _
      have hae : (fun ω => |gK ω - g ω|) =ᵐ[μ] fun ω => gK ω - g ω := by
        filter_upwards [hnn] with ω hω
        exact abs_of_nonneg hω
      rw [integral_congr_ae hae, integral_sub hgK_int hg_int, hintK]
      simpa [g, L] using hint_g
    have hu_ev := hu_tend.eventually (isOpen_Iio.mem_nhds (lt_add_of_pos_right (FK - L) hε4))
    have hv_ev := hv_tend.eventually (isOpen_Iio.mem_nhds hε4)
    rw [eventually_atTop] at hu_ev hv_ev
    rcases hu_ev with ⟨N1, hN1⟩
    rcases hv_ev with ⟨N2, hN2⟩
    refine ⟨max N1 N2, fun n hn => ?_⟩
    have hn1 : N1 ≤ n := (le_max_left N1 N2).trans hn
    have hn2 : N2 ≤ n := (le_max_right N1 N2).trans hn
    have hu_lt : ∫ ω, ρK n ω - ρ n ω ∂μ < FK - L + ε / 4 := hN1 n hn1
    have hv_lt : ∫ ω, |ρK n ω - gK ω| ∂μ < ε / 4 := hN2 n hn2
    let u : Ω → ℝ := fun ω => ρK n ω - ρ n ω
    let v : Ω → ℝ := fun ω => |ρK n ω - gK ω|
    let w : Ω → ℝ := fun ω => |gK ω - g ω|
    have hu : Integrable u μ :=
      (integrable_kingmanRatio htrunc_int n).sub' (integrable_kingmanRatio hf n)
    have hv : Integrable v μ := ((integrable_kingmanRatio htrunc_int n).sub' hgK_int).abs
    have hw : Integrable w μ := (hgK_int.sub' hg_int).abs
    have habs : Integrable (fun ω => |ρ n ω - g ω|) μ :=
      ((integrable_kingmanRatio hf n).sub' hg_int).abs
    have hsum : Integrable (fun ω => u ω + v ω + w ω) μ := by
      refine ((hu.add hv).add hw).congr (Eventually.of_forall fun ω => ?_)
      rw [Pi.add_apply, Pi.add_apply]
    have hsplit : ∫ ω, u ω + v ω + w ω ∂μ = ∫ ω, u ω ∂μ + ∫ ω, v ω ∂μ + ∫ ω, w ω ∂μ := by
      have hpi : ∫ ω, (u + v + w) ω ∂μ = ∫ ω, u ω ∂μ + ∫ ω, v ω ∂μ + ∫ ω, w ω ∂μ := by
        rw [integral_add' (hu.add hv) hw, integral_add' hu hv]
      have hfun : (fun ω => (u + v + w) ω) = fun ω => u ω + v ω + w ω := by
        ext ω
        rw [Pi.add_apply, Pi.add_apply]
      rw [← hfun]
      exact hpi
    have hle : ∫ ω, |ρ n ω - g ω| ∂μ ≤ ∫ ω, u ω + v ω + w ω ∂μ := by
      refine integral_mono habs hsum fun ω => ?_
      rw [show u ω + v ω + w ω = (ρK n ω - ρ n ω) + |ρK n ω - gK ω| + |gK ω - g ω| by
        rfl]
      have hge : ρ n ω ≤ ρK n ω := by
        unfold ρ ρK kingmanRatio
        exact mul_le_mul_of_nonneg_left kingmanTrunc_ge (inv_nonneg.mpr (by positivity))
      have h1 := abs_sub_le (ρ n ω) (ρK n ω) (g ω)
      have h2 := abs_sub_le (ρK n ω) (gK ω) (g ω)
      have habsρ : |ρ n ω - ρK n ω| = ρK n ω - ρ n ω := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hge)]
      calc |ρ n ω - g ω| ≤ |ρ n ω - ρK n ω| + |ρK n ω - g ω| := h1
        _ = (ρK n ω - ρ n ω) + |ρK n ω - g ω| := by rw [habsρ]
        _ ≤ (ρK n ω - ρ n ω) + (|ρK n ω - gK ω| + |gK ω - g ω|) :=
          add_le_add_right h2 (ρK n ω - ρ n ω)
        _ = (ρK n ω - ρ n ω) + |ρK n ω - gK ω| + |gK ω - g ω| := by rw [← add_assoc]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
    have hsum_lt : ∫ ω, u ω ∂μ + ∫ ω, v ω ∂μ + ∫ ω, w ω ∂μ < ε := by
      rw [show ∫ ω, u ω ∂μ = ∫ ω, ρK n ω - ρ n ω ∂μ by rfl,
        show ∫ ω, v ω ∂μ = ∫ ω, |ρK n ω - gK ω| ∂μ by rfl,
        show ∫ ω, w ω ∂μ = ∫ ω, |gK ω - g ω| ∂μ by rfl, hw_eq]
      linarith
    exact lt_of_le_of_lt (hle.trans (le_of_eq hsplit)) hsum_lt
  have hLp_eq : ∀ n, eLpNorm (fun ω => kingmanRatio f n ω - g ω) 1 μ =
      ENNReal.ofReal (∫ ω, |kingmanRatio f n ω - g ω| ∂μ) := by
    intro n
    have hsubI : Integrable (fun ω => kingmanRatio f n ω - g ω) μ :=
      (integrable_kingmanRatio hf n).sub' hg_int
    have hmeas : AEStronglyMeasurable (fun ω => kingmanRatio f n ω - g ω) μ :=
      ((measurable_kingmanRatio (hf_meas (n + 1) (Nat.succ_pos n))).sub
        hg_meas).aestronglyMeasurable
    exact eLpNorm_one_eq_ofReal_abs hmeas hsubI
  have hmap := (ENNReal.tendsto_ofReal hint_abs).congr fun n => (hLp_eq n).symm
  simpa [g, kingmanRatio, ENNReal.ofReal_zero] using hmap

/-- Kingman's theorem for a measurable subadditive process. -/
lemma kingman_of_measurable [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ) :
    ∃ g : Ω → ℝ, Integrable g μ ∧ (g ∘ T =ᵐ[μ] g) ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹ * f (n + 1) ω) atTop (𝓝 (g ω))) ∧
      Tendsto (fun n : ℕ ↦ eLpNorm (fun ω ↦ (n + 1 : ℝ)⁻¹ * f (n + 1) ω - g ω) 1 μ)
        atTop (𝓝 0) ∧
      (∫ ω, g ω ∂μ) = kingmanFekete f μ := by
  obtain ⟨hg, hinv, hconv, hint, -⟩ :=
    kingman_limit_of_measurable hT hf hf_meas hsub hlower
  exact ⟨kingmanLiminfReal f, hg, hinv, hconv,
    kingman_eLpNorm_of_measurable hT hf hf_meas hsub hlower, hint⟩

/-- Kingman's theorem for an integrable subadditive process. -/
lemma kingman_of_integrable [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ) :
    ∃ g : Ω → ℝ, Integrable g μ ∧ (g ∘ T =ᵐ[μ] g) ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹ * f (n + 1) ω) atTop (𝓝 (g ω))) ∧
      Tendsto (fun n : ℕ ↦ eLpNorm (fun ω ↦ (n + 1 : ℝ)⁻¹ * f (n + 1) ω - g ω) 1 μ)
        atTop (𝓝 0) ∧
      (∫ ω, g ω ∂μ) = kingmanFekete f μ := by
  have hf_int : ∀ n : ℕ, 0 < n → Integrable (kingmanMk hf n) μ :=
    fun n hn => integrable_kingmanMk hf hn
  have hf_meas : ∀ n : ℕ, 0 < n → Measurable (kingmanMk hf n) :=
    fun n hn => measurable_kingmanMk hf hn
  have hlower' : ∃ c : ℝ, ∀ n : ℕ, 0 < n →
      c ≤ (n : ℝ)⁻¹ * ∫ ω, kingmanMk hf n ω ∂μ := by
    obtain ⟨c, hc⟩ := hlower
    refine ⟨c, fun n hn => ?_⟩
    rw [kingmanMk_integral hf hn]
    exact hc n hn
  obtain ⟨g, hg_int, hinv, hconv, hL1, hint⟩ := kingman_of_measurable hT hf_int hf_meas
    (kingmanMk_subadditive hT hf hsub) hlower'
  refine ⟨g, hg_int, hinv, ?_, ?_, ?_⟩
  · have hae : ∀ᵐ ω ∂μ, ∀ n : ℕ, f (n + 1) ω = kingmanMk hf (n + 1) ω :=
      (ae_all_iff).2 fun n => kingmanMk_ae hf (Nat.succ_pos n)
    filter_upwards [hconv, hae] with ω hω hpt
    exact hω.congr fun n => by rw [hpt n]
  · refine hL1.congr fun n => ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [kingmanMk_ae hf (Nat.succ_pos n)] with ω hω
    rw [hω]
  · rw [← kingmanMk_fekete hf]
    exact hint

/-- In an ergodic system the subadditive limit equals the constant mean rate. -/
lemma kingman_ae_tendsto_of_ergodic [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    {f : ℕ → Ω → ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹ * f (n + 1) ω) atTop
      (𝓝 (kingmanFekete f μ)) := by
  obtain ⟨g, hg_int, hinv, hconv, -, hint⟩ :=
    kingman_of_integrable hT.toMeasurePreserving hf hsub hlower
  obtain ⟨c, hc⟩ := hT.ae_eq_const_of_ae_eq_comp_ae hg_int.aestronglyMeasurable hinv
  have hcL : c = kingmanFekete f μ := by
    have heq : ∫ ω, g ω ∂μ = c := by
      rw [integral_congr_ae hc]
      simp only [Function.const]
      rw [integral_const]
      simp [measureReal_def, IsProbabilityMeasure.measure_univ, smul_eq_mul, one_mul]
    exact heq.symm.trans hint
  filter_upwards [hconv, hc] with ω hω hωc
  simpa [hωc, hcL] using hω

end CKMA

