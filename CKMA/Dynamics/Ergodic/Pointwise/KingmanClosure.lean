/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Ergodic.Pointwise.KingmanFull

import CKMA.Dynamics.Ergodic.Pointwise.KingmanConv
import CKMA.Dynamics.Ergodic.Pointwise.KingmanLimit
import CKMA.Dynamics.Ergodic.Pointwise.Kingman
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Kingman's theorem by truncation

Height cuts reduce a measurable subadditive process to the linearly bounded case. The bad set
where the limsup is `⊥` is null because its truncated means fall below the Fekete lower bound.
Monotone convergence identifies the mean, and the truncated L¹ convergence passes to the limit.

## Main results

* `CKMA.kingman_of_measurable`: Kingman's theorem for a measurable subadditive process. The
  integrable and ergodic cases, `CKMA.kingman_subadditive` and
  `CKMA.kingman_subadditive_of_ergodic`, are in `Dynamics.Ergodic.Pointwise`.
-/

public section

noncomputable section

namespace CKMA

open Set MeasureTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

attribute [local instance] Classical.propDecidable

omit [MeasurableSpace Ω] in
/-- An extended real lying under every negative integer is `⊥`. -/
private lemma ereal_eq_bot_of_forall_le_neg {x : EReal}
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
private lemma eLpNorm_one_eq_ofReal_abs {w : Ω → ℝ} (hw : AEStronglyMeasurable w μ)
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
lemma tendsto_subadditiveMeanRate_trunc [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ) :
    Tendsto (fun K : ℕ => subadditiveMeanRate (kingmanTrunc K f) μ) atTop
      (𝓝 (subadditiveMeanRate f μ)) := by
  set L : ℝ := subadditiveMeanRate f μ
  set LK : ℕ → ℝ := fun K => subadditiveMeanRate (kingmanTrunc K f) μ
  have hL_le : ∀ K, L ≤ LK K := fun K => subadditiveMeanRate_le_trunc hf hf_meas hlower
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨a, haMem, haLt⟩ := exists_lt_of_csInf_lt
    (s := {a : ℝ | ∃ n : ℕ, 0 < n ∧ a = (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ})
    ⟨((1 : ℕ) : ℝ)⁻¹ * ∫ ω, f 1 ω ∂μ, ⟨1, Nat.one_pos, rfl⟩⟩
    (lt_add_of_pos_right (subadditiveMeanRate f μ) hε)
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
    simpa [LK, subadditiveMeanRate] using csInf_le hbdd ⟨n, hn, rfl⟩
  linarith [hLK_le.trans_lt hK]

@[deprecated (since := "2026-11-15")]
alias tendsto_kingmanFekete_trunc := tendsto_subadditiveMeanRate_trunc

/-- The height-`K` truncation of an integrable measurable subadditive process satisfies the
hypotheses of the linearly bounded case, with slope `K`. -/
private lemma kingmanTrunc_linear_case {f : ℕ → Ω → ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω)) (K : ℕ) :
    (∀ n : ℕ, 0 < n → Integrable (kingmanTrunc K f n) μ) ∧
      (∀ n : ℕ, 0 < n → Measurable (kingmanTrunc K f n)) ∧
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
        kingmanTrunc K f (n + m) ω ≤ kingmanTrunc K f n ω + kingmanTrunc K f m ((T^[n]) ω)) ∧
      (∀ n : ℕ, 0 < n → ∀ ω, -(K : ℝ) * (n : ℝ) ≤ kingmanTrunc K f n ω) :=
  ⟨fun n hn => integrable_kingmanTrunc (hf n hn) (hf_meas n hn),
    fun n hn => measurable_kingmanTrunc (hf_meas n hn), kingmanTrunc_subadditive hsub,
    fun _ _ _ => kingmanTrunc_lower⟩

/-- The liminf of a truncated process is integrable, with integral the truncated Fekete
infimum. -/
private lemma integrable_kingmanLiminfReal_trunc [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) {f : ℕ → Ω → ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω)) (K : ℕ) :
    Integrable (kingmanLiminfReal (kingmanTrunc K f)) μ ∧
      ∫ ω, kingmanLiminfReal (kingmanTrunc K f) ω ∂μ =
        subadditiveMeanRate (kingmanTrunc K f) μ := by
  obtain ⟨hi, hm, hs, hC⟩ := kingmanTrunc_linear_case hf hf_meas hsub K
  exact ⟨(kingmanLiminfReal_integrable_le hT hi hm hs hC).1, by
    simpa [subadditiveMeanRate] using kingmanLiminfReal_integral_eq hT hi hm hs hC⟩

/-- Almost surely, every height cut of the extended liminf and of the extended limsup equals
the liminf of the truncated process. -/
private lemma kingman_ae_max_trunc [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω)) :
    ∀ᵐ ω ∂μ, ∀ K : ℕ,
      max (kingmanLiminf f ω) (-((K : ℝ) : EReal)) =
          (kingmanLiminfReal (kingmanTrunc K f) ω : EReal) ∧
        max (kingmanLimsup f ω) (-((K : ℝ) : EReal)) =
          (kingmanLiminfReal (kingmanTrunc K f) ω : EReal) := by
  have hratioK : ∀ᵐ ω ∂μ, ∀ K, Tendsto (fun n => kingmanRatio (kingmanTrunc K f) n ω)
      atTop (𝓝 (kingmanLiminfReal (kingmanTrunc K f) ω)) :=
    (ae_all_iff).2 fun K => by
      obtain ⟨hi, hm, hs, hC⟩ := kingmanTrunc_linear_case hf hf_meas hsub K
      simpa [kingmanRatio] using kingmanRatio_ae_tendsto_linear hT hi hm hs hC
  filter_upwards [hratioK] with ω hω K
  have hE := (EReal.tendsto_coe).2 (hω K)
  have hinf : kingmanLiminf (kingmanTrunc K f) ω =
      (kingmanLiminfReal (kingmanTrunc K f) ω : EReal) := by
    simpa [kingmanLiminf] using hE.liminf_eq
  have hsup : kingmanLimsup (kingmanTrunc K f) ω =
      (kingmanLiminfReal (kingmanTrunc K f) ω : EReal) := by
    simpa [kingmanLimsup] using hE.limsup_eq
  constructor
  · simpa [kingmanLiminf_trunc] using hinf
  · simpa [kingmanLimsup_trunc] using hsup

/-- Almost surely the extended limsup of a measurable subadditive process is not `⊤`. -/
private lemma kingmanLimsup_ae_ne_top_of_measurable [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {f : ℕ → Ω → ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω)) :
    ∀ᵐ ω ∂μ, kingmanLimsup f ω ≠ ⊤ := by
  have hsup_le : ∀ ω, kingmanLimsup f ω ≤ kingmanLimsup (kingmanTrunc 0 f) ω := by
    intro ω
    unfold kingmanLimsup
    refine limsup_le_limsup (Eventually.of_forall fun n => ?_)
    refine EReal.coe_le_coe_iff.mpr ?_
    unfold kingmanRatio
    exact mul_le_mul_of_nonneg_left (kingmanTrunc_ge (K := 0))
      (inv_nonneg.mpr (by positivity))
  obtain ⟨hi, hm, hs, hC⟩ := kingmanTrunc_linear_case hf hf_meas hsub 0
  filter_upwards [kingmanLimsup_ae_ne_top hT hi hm hs hC] with ω hω htop
  have hle := hsup_le ω
  rw [htop] at hle
  exact hω (top_le_iff.mp hle)

/-- The set where the extended limsup is `⊥` is measurable. -/
private lemma measurableSet_kingmanLimsup_eq_bot {f : ℕ → Ω → ℝ}
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n)) :
    MeasurableSet {ω | kingmanLimsup f ω = ⊥} := by
  have hEq : {ω | kingmanLimsup f ω = ⊥} =
      ⋂ n : ℕ, kingmanLimsup f ⁻¹' Iic (-((n : ℝ) : EReal)) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage, mem_Iic]
    constructor
    · intro hbot n
      exact hbot.symm ▸ (bot_le : ⊥ ≤ -((n : ℝ) : EReal))
    · intro h
      exact ereal_eq_bot_of_forall_le_neg h
  rw [hEq]
  exact MeasurableSet.iInter fun n =>
    (isClosed_Iic.measurableSet).preimage (measurable_kingmanLimsup hf_meas)

/-- Almost surely, the truncated liminfs are bounded by the one at height `0`. -/
private lemma kingman_ae_trunc_le_zero [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω)) :
    ∀ᵐ ω ∂μ, ∀ K, kingmanLiminfReal (kingmanTrunc K f) ω ≤
      kingmanLiminfReal (kingmanTrunc 0 f) ω := by
  have hmon : ∀ K ω, kingmanLiminf (kingmanTrunc K f) ω ≤
      kingmanLiminf (kingmanTrunc 0 f) ω := by
    intro K ω
    unfold kingmanLiminf
    refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
    refine EReal.coe_le_coe_iff.mpr ?_
    unfold kingmanRatio
    exact mul_le_mul_of_nonneg_left (kingmanTrunc_antitone (Nat.zero_le K))
      (inv_nonneg.mpr (by positivity))
  obtain ⟨hi, hm, hs, hC⟩ := kingmanTrunc_linear_case hf hf_meas hsub 0
  filter_upwards [(kingmanLiminfReal_integrable_le hT hi hm hs hC).2.2.1] with ω htop K
  have hreal := EReal.toReal_le_toReal (hmon K ω)
    (kingmanLiminf_ne_bot (kingmanTrunc_linear_case hf hf_meas hsub K).2.2.2 ω) htop
  simpa [kingmanLiminfReal] using hreal

/-- The set where the extended limsup is `⊥` is null: on it the truncated liminf at height `K`
equals `-K`, which pushes the truncated means below the Fekete lower bound for large `K`. -/
private lemma measure_kingmanLimsup_eq_bot [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) {f : ℕ → Ω → ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ) :
    μ {ω | kingmanLimsup f ω = ⊥} = 0 := by
  let A : Set Ω := {ω | kingmanLimsup f ω = ⊥}
  let gK : ℕ → Ω → ℝ := fun K => kingmanLiminfReal (kingmanTrunc K f)
  have hA_meas : MeasurableSet A := measurableSet_kingmanLimsup_eq_bot hf_meas
  have hgK_int : ∀ K, Integrable (gK K) μ := fun K =>
    (integrable_kingmanLiminfReal_trunc hT hf hf_meas hsub K).1
  have honA : ∀ᵐ ω ∂μ, ∀ K, ω ∈ A → gK K ω = -(K : ℝ) := by
    filter_upwards [kingman_ae_max_trunc hT hf hf_meas hsub] with ω hω K hmem
    have hmaxK := (hω K).2
    rw [show kingmanLimsup f ω = ⊥ from hmem, max_eq_right bot_le] at hmaxK
    exact (EReal.coe_injective ((EReal.coe_neg (K : ℝ)).symm.trans hmaxK)).symm
  have habs : ∀ᵐ ω ∂μ, ∀ K, gK K ω ≤ |gK 0 ω| := by
    filter_upwards [kingman_ae_trunc_le_zero hT hf hf_meas hsub] with ω hω K
    exact (hω K).trans (le_abs_self _)
  have hnonneg : (0 : ℝ) ≤ μ.real A := ENNReal.toReal_nonneg
  suffices hle : μ.real A ≤ 0 by
    have heq : μ.real A = 0 := le_antisymm hle hnonneg
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at heq
    exact heq.resolve_right (measure_ne_top μ A)
  by_contra hgt
  have hμpos : 0 < μ.real A := lt_of_not_ge hgt
  obtain ⟨c, hc⟩ := hlower
  have hcL : c ≤ subadditiveMeanRate f μ := by
    unfold subadditiveMeanRate
    refine le_csInf ⟨((1 : ℕ) : ℝ)⁻¹ * ∫ ω, f 1 ω ∂μ, ⟨1, Nat.one_pos, rfl⟩⟩ ?_
    rintro a ⟨n, hn, rfl⟩
    exact hc n hn
  let B : ℝ := ∫ ω, |gK 0 ω| ∂μ
  have hBint : Integrable (fun ω => |gK 0 ω|) μ := (hgK_int 0).abs
  -- Choose a height `K` with `B - c < K μ(A)`.
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
    linarith
  have hge : c ≤ ∫ ω, gK Knat ω ∂μ := by
    rw [(integrable_kingmanLiminfReal_trunc hT hf hf_meas hsub Knat).2]
    exact hcL.trans (subadditiveMeanRate_le_trunc hf hf_meas ⟨c, hc⟩)
  exact not_lt_of_ge hge hupper

/-- If the height cuts `max g (-K)` of a measurable function are integrable, their integrals
converge to `L`, and `L` is at most the integral of the cut at height `0`, then `g` is
integrable with integral `L` (monotone convergence). -/
private lemma integrable_and_integral_eq_of_tendsto_integral_max {g : Ω → ℝ}
    (hg_meas : Measurable g)
    (hcut_int : ∀ K : ℕ, Integrable (fun ω => max (g ω) (-(K : ℝ))) μ) {L : ℝ}
    (htend : Tendsto (fun K : ℕ => ∫ ω, max (g ω) (-(K : ℝ)) ∂μ) atTop (𝓝 L))
    (hle : L ≤ ∫ ω, max (g ω) (-((0 : ℕ) : ℝ)) ∂μ) :
    Integrable g μ ∧ ∫ ω, g ω ∂μ = L := by
  let cut : ℕ → Ω → ℝ := fun K ω => max (g ω) (-(K : ℝ))
  let LK : ℕ → ℝ := fun K => ∫ ω, cut K ω ∂μ
  have hcut_int' : ∀ K, Integrable (cut K) μ := hcut_int
  have hLK_tend : Tendsto LK atTop (𝓝 L) := htend
  have hcut_meas : ∀ K, Measurable (cut K) := fun K => hg_meas.max measurable_const
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
      exact max_le_max le_rfl (neg_le_neg (Nat.cast_le.mpr (Nat.zero_le K)))
    have hfun : (fun ω => ENNReal.ofReal (cut 0 ω - cut K ω)) =
        fun ω => ENNReal.ofReal ((cut 0 - cut K) ω) := by
      ext ω
      rw [Pi.sub_apply]
    rw [hfun, ← ofReal_integral_eq_lintegral_ofReal ((hcut_int' 0).sub (hcut_int' K)) hnn,
      integral_sub' (hcut_int' 0) (hcut_int' K)]
  have hOf : ∫⁻ ω, ENNReal.ofReal (cut 0 ω - g ω) ∂μ = ENNReal.ofReal (LK 0 - L) := by
    have hlim : Tendsto (fun K : ℕ => ENNReal.ofReal (LK 0 - LK K)) atTop
        (𝓝 (ENNReal.ofReal (LK 0 - L))) :=
      (ENNReal.continuous_ofReal.tendsto (LK 0 - L)).comp
        ((tendsto_const_nhds (x := LK 0)).sub hLK_tend)
    exact tendsto_nhds_unique (hlin.congr fun K => hlin_eq K) hlim
  have hdiff_nn : 0 ≤ᵐ[μ] fun ω => cut 0 ω - g ω :=
    Eventually.of_forall fun ω => sub_nonneg.mpr (le_max_left _ _)
  have hdiff_int : Integrable (fun ω => cut 0 ω - g ω) μ := by
    refine ⟨((hcut_meas 0).sub hg_meas).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal hdiff_nn).2 (by
      rw [hOf]
      exact ENNReal.ofReal_lt_top)
  have hg_int : Integrable g μ := by
    have hsubI : Integrable (fun ω => cut 0 ω - (cut 0 ω - g ω)) μ :=
      (hcut_int' 0).sub hdiff_int
    exact hsubI.congr (Eventually.of_forall fun ω => sub_sub_cancel _ _)
  have hint_diff : ∫ ω, cut 0 ω - g ω ∂μ = LK 0 - L := by
    have hnnI : 0 ≤ ∫ ω, cut 0 ω - g ω ∂μ := integral_nonneg fun ω =>
      sub_nonneg.mpr (le_max_left _ _)
    have hLnn : 0 ≤ LK 0 - L := sub_nonneg.mpr hle
    have hOfI : ENNReal.ofReal (∫ ω, cut 0 ω - g ω ∂μ) = ENNReal.ofReal (LK 0 - L) := by
      rw [ofReal_integral_eq_lintegral_ofReal hdiff_int hdiff_nn, hOf]
    have hto := congrArg ENNReal.toReal hOfI
    rwa [ENNReal.toReal_ofReal hnnI, ENNReal.toReal_ofReal hLnn] at hto
  refine ⟨hg_int, ?_⟩
  have hsubeq := integral_sub (hcut_int' 0) hg_int
  rw [hint_diff] at hsubeq
  exact (sub_right_inj.mp hsubeq).symm

/-- A measurable subadditive process has an invariant Kingman limit with the Fekete mean. -/
private lemma kingman_limit_of_measurable [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ) :
    Integrable (kingmanLiminfReal f) μ ∧
      (kingmanLiminfReal f ∘ T =ᵐ[μ] kingmanLiminfReal f) ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹ * f (n + 1) ω) atTop
        (𝓝 (kingmanLiminfReal f ω))) ∧
      (∫ ω, kingmanLiminfReal f ω ∂μ) = subadditiveMeanRate f μ ∧
      (∀ᵐ ω ∂μ, ∀ K : ℕ, kingmanLiminfReal (kingmanTrunc K f) ω =
        max (kingmanLiminfReal f ω) (-(K : ℝ))) := by
  let gK : ℕ → Ω → ℝ := fun K => kingmanLiminfReal (kingmanTrunc K f)
  let g : Ω → ℝ := kingmanLiminfReal f
  have hmax := kingman_ae_max_trunc hT hf hf_meas hsub
  have hbot : ∀ᵐ ω ∂μ, kingmanLimsup f ω ≠ ⊥ :=
    (measure_eq_zero_iff_ae_notMem).1 (measure_kingmanLimsup_eq_bot hT hf hf_meas hsub hlower)
  -- Almost surely the extended liminf and limsup agree with the real liminf.
  have hgood : ∀ᵐ ω ∂μ, kingmanLiminf f ω = (g ω : EReal) ∧
      kingmanLimsup f ω = (g ω : EReal) := by
    filter_upwards [hmax, kingmanLimsup_ae_ne_top_of_measurable hT hf hf_meas hsub, hbot]
      with ω hmaxω htop hbotω
    have horder : kingmanLiminf f ω ≤ kingmanLimsup f ω :=
      liminf_le_limsup (u := fun n => (kingmanRatio f n ω : EReal))
    have heq := ereal_eq_of_max_neg horder htop hbotω fun K => by
      rw [(hmaxω K).1, (hmaxω K).2]
    have hcoe := (EReal.coe_toReal (heq ▸ htop) (heq ▸ hbotω)).symm
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
    rw [hgoodω.1, ← EReal.coe_neg (K : ℝ), ← EReal.coe_strictMono.monotone.map_max] at hmaxg
    exact (EReal.coe_injective hmaxg).symm
  -- Invariance: a common height cut below `g ω` and `g (T ω)` is invariant.
  have hinv : g ∘ T =ᵐ[μ] g := by
    have hcutT := hT.quasiMeasurePreserving.ae hcut
    have hinvK : ∀ᵐ ω ∂μ, ∀ K, gK K (T ω) = gK K ω :=
      (ae_all_iff).2 fun K => by
        obtain ⟨hi, hm, hs, hC⟩ := kingmanTrunc_linear_case hf hf_meas hsub K
        filter_upwards [kingmanLiminfReal_ae_invariant hT hi hm hs hC] with ω hω
        simpa [gK, Function.comp_apply] using hω
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
  -- Integrability and mean, by monotone convergence of the height cuts.
  have hcut_ae : ∀ K, gK K =ᵐ[μ] fun ω => max (g ω) (-(K : ℝ)) := by
    intro K
    filter_upwards [hcut] with ω hω
    exact hω K
  have hcut_eq : ∀ K, subadditiveMeanRate (kingmanTrunc K f) μ =
      ∫ ω, max (g ω) (-(K : ℝ)) ∂μ := fun K =>
    (integrable_kingmanLiminfReal_trunc hT hf hf_meas hsub K).2.symm.trans
      (integral_congr_ae (hcut_ae K))
  obtain ⟨hg_int, hint_g⟩ := integrable_and_integral_eq_of_tendsto_integral_max
    (μ := μ) ((measurable_kingmanLiminf hf_meas).ereal_toReal)
    (fun K => (integrable_kingmanLiminfReal_trunc hT hf hf_meas hsub K).1.congr (hcut_ae K))
    ((tendsto_subadditiveMeanRate_trunc hf hf_meas hlower).congr hcut_eq)
    ((subadditiveMeanRate_le_trunc (K := 0) hf hf_meas hlower).trans_eq (hcut_eq 0))
  refine ⟨hg_int, hinv, ?_, hint_g, ?_⟩
  · simpa [g, kingmanRatio] using hconv
  · simpa [g, gK] using hcut

omit [MeasurableSpace Ω] in
/-- Triangle bound through an upper comparison value: if `a ≤ b`, then
`|a - c| ≤ (b - a) + |b - d| + |d - c|`. -/
private lemma abs_sub_le_of_le_add_abs {a b c d : ℝ} (hab : a ≤ b) :
    |a - c| ≤ (b - a) + |b - d| + |d - c| := by
  have h1 := abs_sub_le a b c
  have h2 := abs_sub_le b d c
  rw [abs_sub_comm a b, abs_of_nonneg (sub_nonneg.mpr hab)] at h1
  linarith

/-- For each height `K`, eventually the L¹ distance of the normalized lengths to the liminf is
less than twice the gap between the truncated and the untruncated Fekete infima plus `δ`. -/
private lemma kingman_eventually_integral_abs_lt [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) {f : ℕ → Ω → ℝ}
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ) (K : ℕ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∫ ω, |kingmanRatio f n ω - kingmanLiminfReal f ω| ∂μ <
      2 * (subadditiveMeanRate (kingmanTrunc K f) μ - subadditiveMeanRate f μ) + δ := by
  obtain ⟨hg_int, -, -, hint_g, hcut⟩ :=
    kingman_limit_of_measurable hT hf hf_meas hsub hlower
  obtain ⟨hi, hm, hs, hC⟩ := kingmanTrunc_linear_case hf hf_meas hsub K
  obtain ⟨hgK_int, hintK⟩ := integrable_kingmanLiminfReal_trunc hT hf hf_meas hsub K
  let g : Ω → ℝ := kingmanLiminfReal f
  let gK : Ω → ℝ := kingmanLiminfReal (kingmanTrunc K f)
  let ρ : ℕ → Ω → ℝ := kingmanRatio f
  let ρK : ℕ → Ω → ℝ := kingmanRatio (kingmanTrunc K f)
  let FK : ℝ := subadditiveMeanRate (kingmanTrunc K f) μ
  let L : ℝ := subadditiveMeanRate f μ
  -- The truncation gap of the normalized means tends to `FK - L`.
  have hu_tend : Tendsto (fun n => ∫ ω, ρK n ω - ρ n ω ∂μ) atTop (𝓝 (FK - L)) := by
    have hlowerK : ∃ c : ℝ, ∀ n : ℕ, 0 < n →
        c ≤ (n : ℝ)⁻¹ * ∫ ω, kingmanTrunc K f n ω ∂μ := by
      obtain ⟨c, hc⟩ := hlower
      refine ⟨c, fun n hn => ?_⟩
      exact (hc n hn).trans (mul_le_mul_of_nonneg_left
        (integral_mono (hf n hn) (hi n hn) fun _ => kingmanTrunc_ge)
        (inv_nonneg.mpr (Nat.cast_nonneg n)))
    have hu_eq : ∀ n, ∫ ω, ρK n ω - ρ n ω ∂μ =
        (n + 1 : ℝ)⁻¹ * ∫ ω, kingmanTrunc K f (n + 1) ω ∂μ -
          (n + 1 : ℝ)⁻¹ * ∫ ω, f (n + 1) ω ∂μ := by
      intro n
      rw [integral_sub (integrable_kingmanRatio hi n) (integrable_kingmanRatio hf n)]
      simp only [kingmanRatio, integral_const_mul]
    simpa [FK, L, subadditiveMeanRate] using
      ((tendsto_kingmanIntegral_div hT hi hs hlowerK).sub
        (tendsto_kingmanIntegral_div hT hf hsub hlower)).congr fun n => (hu_eq n).symm
  -- The truncated process converges in L¹ by the linearly bounded case.
  have hv_tend : Tendsto (fun n => ∫ ω, |ρK n ω - gK ω| ∂μ) atTop (𝓝 0) := by
    have hLpK : Tendsto (fun n => eLpNorm (fun ω => ρK n ω - gK ω) 1 μ) atTop (𝓝 0) := by
      simpa [ρK, gK, kingmanRatio] using kingman_eLpNorm_tendsto_of_linear hT hi hm hs hC
    have hv_eq : ∀ n, ∫ ω, |ρK n ω - gK ω| ∂μ =
        (eLpNorm (fun ω => ρK n ω - gK ω) 1 μ).toReal := by
      intro n
      have hmeas : AEStronglyMeasurable (fun ω => ρK n ω - gK ω) μ :=
        ((measurable_kingmanRatio (hm (n + 1) (Nat.succ_pos n))).aestronglyMeasurable).sub
          hgK_int.aestronglyMeasurable
      rw [eLpNorm_one_eq_ofReal_abs hmeas ((integrable_kingmanRatio hi n).sub' hgK_int),
        ENNReal.toReal_ofReal (integral_nonneg fun _ => abs_nonneg _)]
    have hto := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hLpK
    rw [ENNReal.toReal_zero] at hto
    exact hto.congr fun n => (hv_eq n).symm
  -- The truncated liminf lies above the liminf, with mean gap `FK - L`.
  have hw_eq : ∫ ω, |gK ω - g ω| ∂μ = FK - L := by
    have hnn : 0 ≤ᵐ[μ] fun ω => gK ω - g ω := by
      filter_upwards [hcut] with ω hω
      refine sub_nonneg.mpr ?_
      rw [show gK ω = max (g ω) (-(K : ℝ)) from by simpa [gK, g] using hω K]
      exact le_max_left _ _
    have hae : (fun ω => |gK ω - g ω|) =ᵐ[μ] fun ω => gK ω - g ω := by
      filter_upwards [hnn] with ω hω
      exact abs_of_nonneg hω
    rw [integral_congr_ae hae, integral_sub hgK_int hg_int, hintK, hint_g]
  have hbound : ∀ n, ∫ ω, |ρ n ω - g ω| ∂μ ≤
      ∫ ω, ρK n ω - ρ n ω ∂μ + ∫ ω, |ρK n ω - gK ω| ∂μ + (FK - L) := by
    intro n
    have hu : Integrable (fun ω => ρK n ω - ρ n ω) μ :=
      (integrable_kingmanRatio hi n).sub' (integrable_kingmanRatio hf n)
    have hv : Integrable (fun ω => |ρK n ω - gK ω|) μ :=
      ((integrable_kingmanRatio hi n).sub' hgK_int).abs
    have hw : Integrable (fun ω => |gK ω - g ω|) μ := (hgK_int.sub' hg_int).abs
    have huv : Integrable (fun ω => (ρK n ω - ρ n ω) + |ρK n ω - gK ω|) μ := hu.add hv
    have hle : ∫ ω, |ρ n ω - g ω| ∂μ ≤
        ∫ ω, (ρK n ω - ρ n ω) + |ρK n ω - gK ω| + |gK ω - g ω| ∂μ := by
      refine integral_mono ((integrable_kingmanRatio hf n).sub' hg_int).abs
        (huv.add hw) fun ω => abs_sub_le_of_le_add_abs ?_
      unfold ρ ρK kingmanRatio
      exact mul_le_mul_of_nonneg_left kingmanTrunc_ge (inv_nonneg.mpr (by positivity))
    rwa [integral_add huv hw, integral_add hu hv, hw_eq] at hle
  have hlim := (hu_tend.add hv_tend).add_const (FK - L)
  rw [add_zero, ← two_mul] at hlim
  filter_upwards [hlim.eventually_lt_const (lt_add_of_pos_right _ hδ)] with n hn
  exact (hbound n).trans_lt hn

/-- Normalized lengths of a measurable subadditive process converge in L¹. -/
private lemma kingman_eLpNorm_of_measurable [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : ℕ → Ω → ℝ} (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hf_meas : ∀ n : ℕ, 0 < n → Measurable (f n))
    (hsub : ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω))
    (hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun ω => (n + 1 : ℝ)⁻¹ * f (n + 1) ω - kingmanLiminfReal f ω) 1 μ) atTop (𝓝 0) := by
  obtain ⟨hg_int, -, -, -, -⟩ := kingman_limit_of_measurable hT hf hf_meas hsub hlower
  have hg_meas : Measurable (kingmanLiminfReal f) :=
    (measurable_kingmanLiminf hf_meas).ereal_toReal
  have hint_abs : Tendsto (fun n : ℕ =>
      ∫ ω, |kingmanRatio f n ω - kingmanLiminfReal f ω| ∂μ) atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n =>
      ha.trans_le (integral_nonneg fun _ => abs_nonneg _), fun ε hε => ?_⟩
    -- Choose a height whose Fekete gap is below `ε / 4`.
    obtain ⟨K, hK⟩ := ((tendsto_subadditiveMeanRate_trunc hf hf_meas hlower).eventually_lt_const
      (lt_add_of_pos_right (subadditiveMeanRate f μ) (by positivity : 0 < ε / 4))).exists
    filter_upwards [kingman_eventually_integral_abs_lt hT hf hf_meas hsub hlower K
      (half_pos hε)] with n hn
    linarith
  have hLp_eq : ∀ n, eLpNorm (fun ω => kingmanRatio f n ω - kingmanLiminfReal f ω) 1 μ =
      ENNReal.ofReal (∫ ω, |kingmanRatio f n ω - kingmanLiminfReal f ω| ∂μ) := by
    intro n
    have hmeas : AEStronglyMeasurable (fun ω => kingmanRatio f n ω - kingmanLiminfReal f ω) μ :=
      ((measurable_kingmanRatio (hf_meas (n + 1) (Nat.succ_pos n))).sub
        hg_meas).aestronglyMeasurable
    exact eLpNorm_one_eq_ofReal_abs hmeas ((integrable_kingmanRatio hf n).sub' hg_int)
  have hmap := (ENNReal.tendsto_ofReal hint_abs).congr fun n => (hLp_eq n).symm
  simpa [kingmanRatio, ENNReal.ofReal_zero] using hmap

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
      (∫ ω, g ω ∂μ) = subadditiveMeanRate f μ := by
  obtain ⟨hg, hinv, hconv, hint, -⟩ :=
    kingman_limit_of_measurable hT hf hf_meas hsub hlower
  exact ⟨kingmanLiminfReal f, hg, hinv, hconv,
    kingman_eLpNorm_of_measurable hT hf hf_meas hsub hlower, hint⟩

end CKMA

