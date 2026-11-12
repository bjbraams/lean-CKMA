/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Empirical symmetrization for countable classes (07.33)

`IsRademacher` fixes the symmetric law on the real signs. `symmetrization` bounds the
expected supremum of centered empirical averages by twice the corresponding signed
supremum for a nonempty countable function class with an integrable envelope.

Data and signs are sampled on separate probability spaces. Independence within each
sample and equality of the data laws are explicit; the positive sample size avoids a
zero-sample mean convention.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped NNReal ENNReal

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open Classical

/-- A measurable sign with the symmetric law on `{-1, 1}`. -/
def IsRademacher {Ω : Type*} [MeasurableSpace Ω] (ε : Ω → ℝ) (μ : Measure Ω) : Prop :=
  Measurable ε ∧ μ.map ε =
    (1 / 2 : ℝ≥0∞) • Measure.dirac (-1) + (1 / 2 : ℝ≥0∞) • Measure.dirac 1

/-- The two symmetric weights on the extended nonnegative line sum to one. -/
private lemma half_add_half : (1 / 2 : ℝ≥0∞) + 1 / 2 = 1 := by
  simp only [one_div]
  rw [← two_mul]
  exact ENNReal.mul_inv_cancel (by simp) (by simp)

/-- The symmetric two-point law on `{-1, 1}` is a probability measure. -/
private lemma rademacherLaw_isProbabilityMeasure :
    IsProbabilityMeasure
      ((1 / 2 : ℝ≥0∞) • Measure.dirac (-1) +
        (1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)) := by
  refine ⟨?_⟩
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact half_add_half

/-- The symmetric two-point law is supported on `{-1, 1}`. -/
private lemma rademacherLaw_apply_pair :
    (((1 / 2 : ℝ≥0∞) • Measure.dirac (-1) +
        (1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)) : Measure ℝ) ({-1, 1} : Set ℝ) = 1 := by
  have hneg : (-1 : ℝ) ∈ ({-1, 1} : Set ℝ) := by simp
  have hpos : (1 : ℝ) ∈ ({-1, 1} : Set ℝ) := by simp
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem hneg,
    Measure.dirac_apply_of_mem hpos, smul_eq_mul, mul_one]
  exact half_add_half

/-- The image of a finite measure under a measurable map is finite. -/
private lemma isFiniteMeasure_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [IsFiniteMeasure μ] {φ : α → β} (hφ : Measurable φ) :
    IsFiniteMeasure (μ.map φ) where
  measure_univ_lt_top := by
    rw [Measure.map_apply hφ MeasurableSet.univ, Set.preimage_univ]
    exact measure_lt_top μ Set.univ

/-- A probability space has real total mass one. -/
private lemma prob_real_univ {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] : μ.real Set.univ = 1 := by
  simp [Measure.real]

/-- Integrating out a probability coordinate leaves the first marginal. -/
private lemma integral_fst_of_prob {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α → ℝ} (hf : Integrable f μ) :
    ∫ p, f p.1 ∂μ.prod ν = ∫ a, f a ∂μ := by
  rw [integral_prod _ (hf.comp_fst ν)]
  simp [integral_const]

/-- Integrating out a probability coordinate leaves the second marginal. -/
private lemma integral_snd_of_prob {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : β → ℝ} (hf : Integrable f ν) :
    ∫ p, f p.2 ∂μ.prod ν = ∫ b, f b ∂ν := by
  rw [integral_prod_symm _ (hf.comp_snd μ)]
  simp [integral_const]

/-- Swap the paired coordinates whose sign equals `-1`. -/
private def pairFlip {E : Type*} {n : ℕ} (σ : Fin n → ℝ) (z : Fin n → E × E) :
    Fin n → E × E :=
  fun j => if σ j = -1 then (z j).swap else z j

/-- Exchange the two ghost samples on the coordinates whose sign equals `-1`. -/
private def ghostFlip {E : Type*} {n : ℕ} (σ : Fin n → ℝ)
    (p : (Fin n → E) × (Fin n → E)) : (Fin n → E) × (Fin n → E) :=
  (fun j => if σ j = -1 then p.2 j else p.1 j,
    fun j => if σ j = -1 then p.1 j else p.2 j)

/-- Coordinatewise swaps of `P × P` preserve the law of an i.i.d. ghost pair. -/
private lemma ghostFlip_measurePreserving {E : Type*} [MeasurableSpace E] {n : ℕ}
    {P : Measure E} [IsProbabilityMeasure P] (σ : Fin n → ℝ) :
    MeasurePreserving (ghostFlip σ)
      ((Measure.pi (fun _ : Fin n => P)).prod (Measure.pi (fun _ : Fin n => P)))
      ((Measure.pi (fun _ : Fin n => P)).prod (Measure.pi (fun _ : Fin n => P))) := by
  let π : Measure (Fin n → E) := Measure.pi (fun _ => P)
  let Q : Measure (Fin n → E × E) := Measure.pi (fun _ => P.prod P)
  let flip (j : Fin n) : E × E → E × E := fun p => if σ j = -1 then p.swap else p
  have hφ (j : Fin n) : Measurable (flip j) := by
    by_cases hσ : σ j = -1
    · simpa [flip, hσ] using (measurable_swap : Measurable (Prod.swap : E × E → E × E))
    · have hid : flip j = id := by
        funext p
        simp [flip, hσ]
      simpa [hid] using (measurable_id : Measurable (id : E × E → E × E))
  have hcoord (j : Fin n) : (P.prod P).map (flip j) = P.prod P := by
    by_cases hσ : σ j = -1
    · have hfun : flip j = Prod.swap := by
        funext p
        simp [flip, hσ, Prod.swap]
      rw [hfun]
      exact Measure.prod_swap
    · have hfun : flip j = id := by
        funext p
        simp [flip, hσ]
      rw [hfun]
      exact Measure.map_id
  have hfin (j : Fin n) : IsFiniteMeasure ((P.prod P).map (flip j)) :=
    isFiniteMeasure_map (hφ j)
  have : ∀ j : Fin n, SigmaFinite ((P.prod P).map (flip j)) := fun j =>
    @IsFiniteMeasure.toSigmaFinite _ _ ((P.prod P).map (flip j)) (hfin j)
  have hpair_meas : Measurable (pairFlip (E := E) σ) := by
    rw [measurable_pi_iff]
    intro j
    change Measurable (flip j ∘ fun (x : Fin n → E × E) => x j)
    exact (hφ j).comp (measurable_pi_apply j)
  have hpair_map : Q.map (pairFlip (E := E) σ) = Q := by
    have hfun : pairFlip (E := E) σ = fun z j => flip j (z j) := rfl
    rw [hfun, Measure.pi_map_pi (fun j => (hφ j).aemeasurable)]
    congr
    funext j
    exact hcoord j
  let e := MeasurableEquiv.arrowProdEquivProdArrow E E (Fin n)
  have he : MeasurePreserving (⇑e) Q (π.prod π) :=
    measurePreserving_arrowProdEquivProdArrow E E (Fin n) (fun _ => P) (fun _ => P)
  have hcomp : MeasurePreserving (⇑e ∘ pairFlip σ ∘ ⇑e.symm) (π.prod π) (π.prod π) :=
    he.comp ((⟨hpair_meas, hpair_map⟩ :
      MeasurePreserving (pairFlip (E := E) σ) Q Q).comp he.symm)
  have hfun : ghostFlip σ = ⇑e ∘ pairFlip σ ∘ ⇑e.symm := by
    funext p
    apply Prod.ext
    · ext j
      by_cases hσ : σ j = -1 <;>
        simp [ghostFlip, pairFlip, hσ, e, MeasurableEquiv.arrowProdEquivProdArrow,
          Equiv.arrowProdEquivProdArrow]
    · ext j
      by_cases hσ : σ j = -1 <;>
        simp [ghostFlip, pairFlip, hσ, e, MeasurableEquiv.arrowProdEquivProdArrow,
          Equiv.arrowProdEquivProdArrow]
  exact hfun.symm ▸ hcomp

/-- Absolute value on `ℝ` is measurable. The norm reduces to it only inside its defining module. -/
private lemma measurable_abs : Measurable (fun r : ℝ => |r|) := by
  have hfun : (fun r : ℝ => ‖r‖) = fun r => |r| := funext Real.norm_eq_abs
  rw [← hfun]
  exact measurable_id.norm

/-- An integrable real function dominated by the envelope is integrable. -/
private lemma integrable_of_envelope {E : Type*} [MeasurableSpace E] {P : Measure E}
    [IsProbabilityMeasure P] {g envelope : E → ℝ} (hg : Measurable g)
    (he : Integrable envelope P) (henv0 : ∀ x, 0 ≤ envelope x)
    (hbound : ∀ x, |g x| ≤ envelope x) : Integrable g P := by
  refine he.mono hg.aemeasurable.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (henv0 x)]
  exact hbound x

set_option maxHeartbeats 2000000 in
/-- Centering an empirical mean by an independent ghost sample does not decrease the
expected supremum. -/
private lemma expectedSup_centered_le_ghost {E ι : Type*} [MeasurableSpace E] [Countable ι]
    [Nonempty ι] {P : Measure E} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {f : ι → E → ℝ} (hf : ∀ i, Measurable (f i)) {envelope : E → ℝ}
    (he : Integrable envelope P) (hbound : ∀ i x, |f i x| ≤ envelope x) :
    (∫ y, ⨆ i, |(n : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P|
        ∂Measure.pi (fun _ : Fin n => P)) ≤
      ∫ p, ⨆ i, |(n : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))|
        ∂(Measure.pi (fun _ : Fin n => P)).prod (Measure.pi (fun _ : Fin n => P)) := by
  let π : Measure (Fin n → E) := Measure.pi (fun _ => P)
  have henv0 (x : E) : 0 ≤ envelope x :=
    Nonempty.elim ‹Nonempty ι› fun i => (abs_nonneg _).trans (hbound i x)
  have hfi (i : ι) : Integrable (f i) P :=
    integrable_of_envelope (hf i) he henv0 (hbound i)
  have hinv0 : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have heval (j : Fin n) :
      Integrable (fun y : Fin n → E => envelope (y j)) π :=
    (measurePreserving_eval (fun _ : Fin n => P) j).integrable_comp_of_integrable he
  have hevalf (i : ι) (j : Fin n) :
      Integrable (fun y : Fin n → E => f i (y j)) π :=
    (measurePreserving_eval (fun _ : Fin n => P) j).integrable_comp_of_integrable (hfi i)
  have hmarg (i : ι) (j : Fin n) :
      ∫ y, f i (y j) ∂π = ∫ x, f i x ∂P := by
    have hpres := measurePreserving_eval (fun _ : Fin n => P) j
    rw [← hpres.map_eq]
    exact (integral_map hpres.measurable.aemeasurable
      ((hf i).aemeasurable.aestronglyMeasurable)).symm
  have henvSum : Integrable (fun y : Fin n → E => ∑ j, envelope (y j)) π :=
    integrable_finsetSum _ fun j _ => heval j
  have hcenter (i : ι) (y : Fin n → E) :
      ∫ y', (n : ℝ)⁻¹ * ∑ j, (f i (y j) - f i (y' j)) ∂π =
        (n : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P := by
    have hterm (j : Fin n) :
        Integrable (fun y' : Fin n → E => f i (y j) - f i (y' j)) π :=
      (integrable_const _).sub (hevalf i j)
    rw [integral_const_mul, integral_finsetSum _ fun j _ => hterm j]
    have hsub (j : Fin n) :
        ∫ y', f i (y j) - f i (y' j) ∂π = f i (y j) - ∫ x, f i x ∂P := by
      rw [integral_sub (integrable_const _) (hevalf i j), integral_const, hmarg i j,
        prob_real_univ, one_smul]
    simp_rw [hsub, Finset.sum_sub_distrib]
    have hsummean : ∑ j : Fin n, (∫ x, f i x ∂P) = (n : ℝ) * ∫ x, f i x ∂P := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    rw [hsummean, mul_sub, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  have hdiff_le (i : ι) (y y' : Fin n → E) :
      |(n : ℝ)⁻¹ * ∑ j, (f i (y j) - f i (y' j))| ≤
        (n : ℝ)⁻¹ * ∑ j, (envelope (y j) + envelope (y' j)) := by
    rw [abs_mul, abs_of_nonneg hinv0]
    refine mul_le_mul_of_nonneg_left ?_ hinv0
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun j _ => ?_
    exact (abs_sub _ _).trans (add_le_add (hbound i _) (hbound i _))
  let Φ : (Fin n → E) × (Fin n → E) → ℝ := fun p =>
    ⨆ i, |(n : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))|
  have hΦmeas : Measurable Φ := by
    refine Measurable.iSup fun i => measurable_abs.comp ?_
    refine (Finset.measurable_fun_sum Finset.univ fun j _ => ?_).const_mul (n : ℝ)⁻¹
    exact ((hf i).comp ((measurable_pi_apply j).comp measurable_fst)).sub
      ((hf i).comp ((measurable_pi_apply j).comp measurable_snd))
  have hbdd (p : (Fin n → E) × (Fin n → E)) :
      BddAbove (Set.range fun i => |(n : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))|) := by
    refine ⟨(n : ℝ)⁻¹ * ∑ j, (envelope (p.1 j) + envelope (p.2 j)), ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hdiff_le i p.1 p.2
  have hΦ0 (p : (Fin n → E) × (Fin n → E)) : 0 ≤ Φ p :=
    Nonempty.elim ‹Nonempty ι› fun i => (abs_nonneg _).trans (le_ciSup (hbdd p) i)
  have hΦle (p : (Fin n → E) × (Fin n → E)) :
      Φ p ≤ (n : ℝ)⁻¹ * ∑ j, (envelope (p.1 j) + envelope (p.2 j)) :=
    ciSup_le fun i => hdiff_le i p.1 p.2
  have hdom : Integrable (fun p : (Fin n → E) × (Fin n → E) =>
      (n : ℝ)⁻¹ * ∑ j, (envelope (p.1 j) + envelope (p.2 j))) (π.prod π) := by
    have hsum : Integrable (fun p : (Fin n → E) × (Fin n → E) =>
        ∑ j, envelope (p.1 j) + ∑ j, envelope (p.2 j)) (π.prod π) :=
      (henvSum.comp_fst π).add (henvSum.comp_snd π)
    have hfun : (fun p : (Fin n → E) × (Fin n → E) =>
        (n : ℝ)⁻¹ * ∑ j, (envelope (p.1 j) + envelope (p.2 j))) =
        fun p => (n : ℝ)⁻¹ * (∑ j, envelope (p.1 j) + ∑ j, envelope (p.2 j)) := by
      funext p
      rw [Finset.sum_add_distrib]
    rw [hfun]
    exact hsum.const_mul _
  have hΦint : Integrable Φ (π.prod π) := by
    refine hdom.mono' hΦmeas.aemeasurable.aestronglyMeasurable ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (hΦ0 p)]
    exact hΦle p
  have hslice (y : Fin n → E) : Integrable (fun y2 => Φ (y, y2)) π := by
    have hdomy : Integrable (fun y2 =>
        (n : ℝ)⁻¹ * ∑ j, (envelope (y j) + envelope (y2 j))) π := by
      have hconst : Integrable (fun _ : Fin n → E => ∑ j, envelope (y j)) π :=
        integrable_const _
      have hfun : (fun y2 : Fin n → E =>
            (n : ℝ)⁻¹ * ∑ j, (envelope (y j) + envelope (y2 j))) =
          fun y2 : Fin n → E =>
            (n : ℝ)⁻¹ * (∑ j, envelope (y j) + ∑ j, envelope (y2 j)) := by
        funext y2
        rw [Finset.sum_add_distrib]
      rw [hfun]
      exact (hconst.add henvSum).const_mul _
    have hmeas_y : Measurable (fun y2 => Φ (y, y2)) :=
      hΦmeas.comp (measurable_const.prodMk measurable_id)
    refine hdomy.mono' hmeas_y.aemeasurable.aestronglyMeasurable ?_
    filter_upwards with y2
    rw [Real.norm_eq_abs, abs_of_nonneg (hΦ0 (y, y2))]
    exact hΦle (y, y2)
  have hpoint (i : ι) (y : Fin n → E) :
      |(n : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P| ≤ ∫ y', Φ (y, y') ∂π := by
    rw [← hcenter i y]
    refine (abs_integral_le_integral_abs).trans ?_
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (hslice y) ?_
    exact ae_of_all _ fun y' => le_ciSup (hbdd (y, y')) i
  have hsup_le (y : Fin n → E) :
      ⨆ i, |(n : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P| ≤ ∫ y', Φ (y, y') ∂π :=
    ciSup_le fun i => hpoint i y
  let hC : ℝ := ∫ x, envelope x ∂P
  have hmean_le (i : ι) : |∫ x, f i x ∂P| ≤ hC := by
    calc
      |∫ x, f i x ∂P| ≤ ∫ x, |f i x| ∂P := abs_integral_le_integral_abs
      _ ≤ hC := integral_mono (hfi i).abs he fun x => hbound i x
  have hcent_le (i : ι) (y : Fin n → E) :
      |(n : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P| ≤
        (n : ℝ)⁻¹ * ∑ j, envelope (y j) + hC := by
    calc
      |(n : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P| ≤
          |(n : ℝ)⁻¹ * ∑ j, f i (y j)| + |∫ x, f i x ∂P| := abs_sub _ _
      _ ≤ (n : ℝ)⁻¹ * ∑ j, |f i (y j)| + hC := by
        refine add_le_add ?_ (hmean_le i)
        rw [abs_mul, abs_of_nonneg hinv0]
        exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hinv0
      _ ≤ (n : ℝ)⁻¹ * ∑ j, envelope (y j) + hC :=
        add_le_add
          (mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun j _ => hbound i (y j)) hinv0)
          le_rfl
  have hleft_le (y : Fin n → E) :
      ⨆ i, |(n : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P| ≤
        (n : ℝ)⁻¹ * ∑ j, envelope (y j) + hC :=
    ciSup_le fun i => hcent_le i y
  have hleft_meas : Measurable (fun y : Fin n → E =>
      ⨆ i, |(n : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P|) := by
    refine Measurable.iSup fun i => measurable_abs.comp ?_
    exact ((Finset.measurable_fun_sum Finset.univ fun j _ =>
      (hf i).comp (measurable_pi_apply j)).const_mul (n : ℝ)⁻¹).sub measurable_const
  have hleft_int : Integrable (fun y : Fin n → E =>
      ⨆ i, |(n : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P|) π := by
    have hdomL : Integrable (fun y : Fin n → E =>
        (n : ℝ)⁻¹ * ∑ j, envelope (y j) + hC) π :=
      (henvSum.const_mul _).add (integrable_const _)
    refine hdomL.mono' hleft_meas.aemeasurable.aestronglyMeasurable ?_
    filter_upwards with y
    have hnn : 0 ≤ ⨆ i, |(n : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P| :=
      Nonempty.elim ‹Nonempty ι› fun i =>
        (abs_nonneg _).trans <| le_ciSup
          ⟨(n : ℝ)⁻¹ * ∑ j, envelope (y j) + hC, by
            rintro _ ⟨k, rfl⟩
            exact hcent_le k y⟩ i
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hleft_le y
  have houter : Integrable (fun y => ∫ y', Φ (y, y') ∂π) π :=
    hΦint.integral_prod_left
  calc
    (∫ y, ⨆ i, |(n : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P| ∂π) ≤
        ∫ y, ∫ y', Φ (y, y') ∂π ∂π :=
      integral_mono hleft_int houter hsup_le
    _ = ∫ p, Φ p ∂π.prod π := (integral_prod _ hΦint).symm

set_option maxHeartbeats 2000000 in
/-- Random signs do not change the ghost comparison, and the triangle inequality
splits it into two equidistributed signed copies. -/
private lemma expectedSup_ghost_le_twice_signed {E ι : Type*} [MeasurableSpace E]
    [Countable ι] [Nonempty ι] {P : Measure E} [IsProbabilityMeasure P] {n : ℕ}
    (_hn : 0 < n) {f : ι → E → ℝ} (hf : ∀ i, Measurable (f i)) {envelope : E → ℝ}
    (he : Integrable envelope P) (hbound : ∀ i x, |f i x| ≤ envelope x) :
    (∫ p, ⨆ i, |(n : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))|
        ∂(Measure.pi (fun _ : Fin n => P)).prod (Measure.pi (fun _ : Fin n => P))) ≤
      2 * ∫ q, ⨆ i, |(n : ℝ)⁻¹ * ∑ j, q.2 j * f i (q.1 j)|
        ∂(Measure.pi (fun _ : Fin n => P)).prod
          (Measure.pi (fun _ : Fin n =>
            (1 / 2 : ℝ≥0∞) • Measure.dirac (-1) +
              (1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ))) := by
  let π : Measure (Fin n → E) := Measure.pi (fun _ => P)
  let rad : Measure ℝ :=
    (1 / 2 : ℝ≥0∞) • Measure.dirac (-1) + (1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)
  have : IsProbabilityMeasure rad := rademacherLaw_isProbabilityMeasure
  let ρ : Measure (Fin n → ℝ) := Measure.pi (fun _ => rad)
  let S : Set (Fin n → ℝ) := Set.univ.pi (fun _ => ({-1, 1} : Set ℝ))
  have henv0 (x : E) : 0 ≤ envelope x :=
    Nonempty.elim ‹Nonempty ι› fun i => (abs_nonneg _).trans (hbound i x)
  have hinv0 : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hpair_meas : MeasurableSet ({-1, 1} : Set ℝ) :=
    (measurableSet_singleton (1 : ℝ)).insert (-1)
  have hSmeas : MeasurableSet S := MeasurableSet.univ_pi fun _ => hpair_meas
  have hSmeasure : ρ S = 1 := by
    dsimp only [ρ, S]
    rw [Measure.pi_pi]
    have hrad : rad ({-1, 1} : Set ℝ) = 1 := by
      simpa [rad] using rademacherLaw_apply_pair
    simp only [hrad, Finset.prod_const_one]
  have hnull : ρ Sᶜ = 0 := by
    rw [measure_compl hSmeas (by simp [hSmeasure] : ρ S ≠ ∞), hSmeasure, measure_univ]
    exact ENNReal.sub_eq_of_eq_add (by simp) (by simp)
  have haeS : ∀ᵐ σ ∂ρ, σ ∈ S := by
    rw [ae_iff]
    exact hnull
  have habs1 {σ : Fin n → ℝ} (hσ : σ ∈ S) (j : Fin n) : |σ j| = 1 := by
    have hj : σ j = -1 ∨ σ j = 1 := by
      have hmem := hσ j
      simpa [S, Set.mem_univ_pi, Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
    rcases hj with h | h <;> simp [h]
  have hone : (1 : ℝ) ≠ -1 :=
    (ne_of_lt (lt_trans (neg_lt_zero.mpr zero_lt_one) zero_lt_one)).symm
  let Φ : (Fin n → E) × (Fin n → E) → ℝ := fun p =>
    ⨆ i, |(n : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))|
  have hΦmeas : Measurable Φ := by
    refine Measurable.iSup fun i => measurable_abs.comp ?_
    refine (Finset.measurable_fun_sum Finset.univ fun j _ => ?_).const_mul (n : ℝ)⁻¹
    exact ((hf i).comp ((measurable_pi_apply j).comp measurable_fst)).sub
      ((hf i).comp ((measurable_pi_apply j).comp measurable_snd))
  have henvSum : Integrable (fun y : Fin n → E => ∑ j, envelope (y j)) π :=
    integrable_finsetSum _ fun j _ =>
      (measurePreserving_eval (fun _ : Fin n => P) j).integrable_comp_of_integrable he
  have hdom : Integrable (fun p : (Fin n → E) × (Fin n → E) =>
      (n : ℝ)⁻¹ * ∑ j, (envelope (p.1 j) + envelope (p.2 j))) (π.prod π) := by
    have hsum : Integrable (fun p : (Fin n → E) × (Fin n → E) =>
        ∑ j, envelope (p.1 j) + ∑ j, envelope (p.2 j)) (π.prod π) :=
      (henvSum.comp_fst π).add (henvSum.comp_snd π)
    have hfun : (fun p : (Fin n → E) × (Fin n → E) =>
        (n : ℝ)⁻¹ * ∑ j, (envelope (p.1 j) + envelope (p.2 j))) =
        fun p => (n : ℝ)⁻¹ * (∑ j, envelope (p.1 j) + ∑ j, envelope (p.2 j)) := by
      funext p
      rw [Finset.sum_add_distrib]
    rw [hfun]
    exact hsum.const_mul _
  have hdiff_le (i : ι) (y y' : Fin n → E) :
      |(n : ℝ)⁻¹ * ∑ j, (f i (y j) - f i (y' j))| ≤
        (n : ℝ)⁻¹ * ∑ j, (envelope (y j) + envelope (y' j)) := by
    rw [abs_mul, abs_of_nonneg hinv0]
    refine mul_le_mul_of_nonneg_left ?_ hinv0
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun j _ => ?_
    exact (abs_sub _ _).trans (add_le_add (hbound i _) (hbound i _))
  have hbddΦ (p : (Fin n → E) × (Fin n → E)) :
      BddAbove (Set.range fun i => |(n : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))|) := by
    refine ⟨(n : ℝ)⁻¹ * ∑ j, (envelope (p.1 j) + envelope (p.2 j)), ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hdiff_le i p.1 p.2
  have hΦ0 (p) : 0 ≤ Φ p :=
    Nonempty.elim ‹Nonempty ι› fun i => (abs_nonneg _).trans (le_ciSup (hbddΦ p) i)
  have hΦint : Integrable Φ (π.prod π) := by
    refine hdom.mono' hΦmeas.aemeasurable.aestronglyMeasurable ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (hΦ0 p)]
    exact ciSup_le fun i => hdiff_le i p.1 p.2
  have hterms {σ : Fin n → ℝ} (hσ : σ ∈ S) (p : (Fin n → E) × (Fin n → E)) (i : ι) :
      ∑ j, (f i ((ghostFlip σ p).1 j) - f i ((ghostFlip σ p).2 j)) =
        ∑ j, σ j * (f i (p.1 j) - f i (p.2 j)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : σ j = -1 ∨ σ j = 1 := by
      simpa [S, Set.mem_univ_pi, Set.mem_insert_iff, Set.mem_singleton_iff] using hσ j
    rcases hj with hj | hj
    · have h1 : (ghostFlip σ p).1 j = p.2 j := by simp [ghostFlip, hj]
      have h2 : (ghostFlip σ p).2 j = p.1 j := by simp [ghostFlip, hj]
      rw [h1, h2, hj, neg_one_mul, neg_sub]
    · have hne : σ j ≠ -1 := by simpa [hj] using hone
      have h1 : (ghostFlip σ p).1 j = p.1 j := by simp [ghostFlip, hne]
      have h2 : (ghostFlip σ p).2 j = p.2 j := by simp [ghostFlip, hne]
      rw [h1, h2, hj, one_mul]
  have hint_eq {σ : Fin n → ℝ} (hσ : σ ∈ S) :
      ∫ p, ⨆ i, |(n : ℝ)⁻¹ * ∑ j, σ j * (f i (p.1 j) - f i (p.2 j))| ∂π.prod π =
        ∫ p, Φ p ∂π.prod π := by
    have hpres := ghostFlip_measurePreserving (P := P) σ
    have hint : ∫ p, Φ (ghostFlip σ p) ∂π.prod π = ∫ p, Φ p ∂π.prod π := by
      conv_rhs => rw [← hpres.map_eq]
      exact (integral_map hpres.measurable.aemeasurable
        (hΦmeas.aestronglyMeasurable :
          AEStronglyMeasurable Φ (Measure.map (ghostFlip σ) (π.prod π)))).symm
    rw [← hint]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    refine congr_arg iSup (funext fun i => ?_)
    rw [hterms hσ p i]
  let m := (π.prod π).prod ρ
  let Φσ : ((Fin n → E) × (Fin n → E)) × (Fin n → ℝ) → ℝ := fun z =>
    ⨆ i, |(n : ℝ)⁻¹ * ∑ j, z.2 j * (f i (z.1.1 j) - f i (z.1.2 j))|
  have hΦσmeas : Measurable Φσ := by
    refine Measurable.iSup fun i => measurable_abs.comp ?_
    refine (Finset.measurable_fun_sum Finset.univ fun j _ => ?_).const_mul (n : ℝ)⁻¹
    exact (((measurable_pi_apply j).comp measurable_snd).mul
      (((hf i).comp ((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst))).sub
        ((hf i).comp ((measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)))))
  let ψ : (Fin n → E) × (Fin n → ℝ) → ℝ := fun q =>
    ⨆ i, |(n : ℝ)⁻¹ * ∑ j, q.2 j * f i (q.1 j)|
  have hψmeas : Measurable ψ := by
    refine Measurable.iSup fun i => measurable_abs.comp ?_
    refine (Finset.measurable_fun_sum Finset.univ fun j _ => ?_).const_mul (n : ℝ)⁻¹
    exact ((measurable_pi_apply j).comp measurable_snd).mul
      ((hf i).comp ((measurable_pi_apply j).comp measurable_fst))
  have hwild (σ : Fin n → ℝ) (y : Fin n → E) (i : ι) :
      |(n : ℝ)⁻¹ * ∑ j, σ j * f i (y j)| ≤
        (n : ℝ)⁻¹ * ∑ j, |σ j| * envelope (y j) := by
    rw [abs_mul, abs_of_nonneg hinv0]
    refine mul_le_mul_of_nonneg_left ?_ hinv0
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hbound i (y j)) (abs_nonneg _)
  have hbddψ (σ : Fin n → ℝ) (y : Fin n → E) :
      BddAbove (Set.range fun i => |(n : ℝ)⁻¹ * ∑ j, σ j * f i (y j)|) := by
    refine ⟨(n : ℝ)⁻¹ * ∑ j, |σ j| * envelope (y j), ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hwild σ y i
  have hψ0 (q : (Fin n → E) × (Fin n → ℝ)) : 0 ≤ ψ q :=
    Nonempty.elim ‹Nonempty ι› fun i => (abs_nonneg _).trans (le_ciSup (hbddψ q.2 q.1) i)
  have hψ_good (σ : Fin n → ℝ) (y : Fin n → E) (hσ : σ ∈ S) :
      ψ (y, σ) ≤ (n : ℝ)⁻¹ * ∑ j, envelope (y j) := by
    refine ciSup_le fun i => ?_
    rw [abs_mul, abs_of_nonneg hinv0]
    refine mul_le_mul_of_nonneg_left ?_ hinv0
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, habs1 hσ j, one_mul]
    exact hbound i _
  have henvAvg : Integrable (fun y : Fin n → E => (n : ℝ)⁻¹ * ∑ j, envelope (y j)) π :=
    henvSum.const_mul _
  have hae_prod : ∀ᵐ q ∂π.prod ρ, q.2 ∈ S := by
    rw [ae_iff]
    have : {q : (Fin n → E) × (Fin n → ℝ) | q.2 ∉ S} = Set.univ ×ˢ Sᶜ := by
      ext q
      simp
    rw [this, Measure.prod_prod, hnull, measure_univ, one_mul]
  have hψint : Integrable ψ (π.prod ρ) := by
    refine (henvAvg.comp_fst ρ).mono' hψmeas.aemeasurable.aestronglyMeasurable ?_
    filter_upwards [hae_prod] with q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (hψ0 q)]
    exact hψ_good q.2 q.1 hq
  let Ψ1 : ((Fin n → E) × (Fin n → E)) × (Fin n → ℝ) → ℝ := fun z => ψ (z.1.1, z.2)
  let Ψ2 : ((Fin n → E) × (Fin n → E)) × (Fin n → ℝ) → ℝ := fun z => ψ (z.1.2, z.2)
  have hΨ1meas : Measurable Ψ1 :=
    hψmeas.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hΨ2meas : Measurable Ψ2 :=
    hψmeas.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hae_m : ∀ᵐ z ∂m, z.2 ∈ S := by
    rw [ae_iff]
    have : {z : ((Fin n → E) × (Fin n → E)) × (Fin n → ℝ) | z.2 ∉ S} =
        Set.univ ×ˢ Sᶜ := by
      ext z
      simp
    rw [this, Measure.prod_prod, hnull, measure_univ, one_mul]
  have hdom1 : Integrable (fun z => (n : ℝ)⁻¹ * ∑ j, envelope (z.1.1 j)) m :=
    (henvAvg.comp_fst π).comp_fst ρ
  have hdom2 : Integrable (fun z => (n : ℝ)⁻¹ * ∑ j, envelope (z.1.2 j)) m :=
    (henvAvg.comp_snd π).comp_fst ρ
  have hΨ10 (z) : 0 ≤ Ψ1 z := hψ0 (z.1.1, z.2)
  have hΨ20 (z) : 0 ≤ Ψ2 z := hψ0 (z.1.2, z.2)
  have hΨ1int : Integrable Ψ1 m := by
    refine hdom1.mono' hΨ1meas.aemeasurable.aestronglyMeasurable ?_
    filter_upwards [hae_m] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (hΨ10 z)]
    exact hψ_good z.2 z.1.1 hz
  have hΨ2int : Integrable Ψ2 m := by
    refine hdom2.mono' hΨ2meas.aemeasurable.aestronglyMeasurable ?_
    filter_upwards [hae_m] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (hΨ20 z)]
    exact hψ_good z.2 z.1.2 hz
  have hΦσ0 (z) : 0 ≤ Φσ z := by
    have hbdd : BddAbove (Set.range fun i =>
        |(n : ℝ)⁻¹ * ∑ j, z.2 j * (f i (z.1.1 j) - f i (z.1.2 j))|) := by
      refine ⟨(n : ℝ)⁻¹ * ∑ j, |z.2 j| * (envelope (z.1.1 j) + envelope (z.1.2 j)), ?_⟩
      intro t ht
      rcases ht with ⟨i, rfl⟩
      show |(n : ℝ)⁻¹ * ∑ j, z.2 j * (f i (z.1.1 j) - f i (z.1.2 j))| ≤
        (n : ℝ)⁻¹ * ∑ j, |z.2 j| * (envelope (z.1.1 j) + envelope (z.1.2 j))
      rw [abs_mul, abs_of_nonneg hinv0]
      refine mul_le_mul_of_nonneg_left ?_ hinv0
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine Finset.sum_le_sum fun j _ => ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        ((abs_sub _ _).trans (add_le_add (hbound i _) (hbound i _))) (abs_nonneg _)
    exact Nonempty.elim ‹Nonempty ι› fun i => (abs_nonneg _).trans (le_ciSup hbdd i)
  have hΦσdom : Integrable (fun z =>
      (n : ℝ)⁻¹ * ∑ j, envelope (z.1.1 j) + (n : ℝ)⁻¹ * ∑ j, envelope (z.1.2 j)) m := by
    refine (hdom1.add hdom2).congr ?_
    refine ae_of_all _ fun z => ?_
    exact Pi.add_apply _ _ z
  have hΦσint : Integrable Φσ m := by
    refine hΦσdom.mono' hΦσmeas.aemeasurable.aestronglyMeasurable ?_
    filter_upwards [hae_m] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (hΦσ0 z)]
    refine ciSup_le fun i => ?_
    calc
      |(n : ℝ)⁻¹ * ∑ j, z.2 j * (f i (z.1.1 j) - f i (z.1.2 j))|
          = (n : ℝ)⁻¹ * |∑ j, z.2 j * (f i (z.1.1 j) - f i (z.1.2 j))| := by
            rw [abs_mul, abs_of_nonneg hinv0]
      _ ≤ (n : ℝ)⁻¹ * ∑ j, |z.2 j * (f i (z.1.1 j) - f i (z.1.2 j))| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hinv0
      _ ≤ (n : ℝ)⁻¹ * ∑ j, (envelope (z.1.1 j) + envelope (z.1.2 j)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hinv0
        rw [abs_mul, habs1 hz j, one_mul]
        exact (abs_sub _ _).trans (add_le_add (hbound i _) (hbound i _))
      _ = (n : ℝ)⁻¹ * ∑ j, envelope (z.1.1 j) +
          (n : ℝ)⁻¹ * ∑ j, envelope (z.1.2 j) := by
        rw [Finset.sum_add_distrib, mul_add]
  have heq_sign : ∫ z, Φσ z ∂m = ∫ p, Φ p ∂π.prod π := by
    rw [integral_prod_symm _ hΦσint]
    have hinner : (fun σ => ∫ p, ⨆ i,
        |(n : ℝ)⁻¹ * ∑ j, σ j * (f i (p.1 j) - f i (p.2 j))| ∂π.prod π) =ᵐ[ρ]
        fun _ => ∫ p, Φ p ∂π.prod π := by
      filter_upwards [haeS] with σ hσ
      simpa [Φσ] using hint_eq hσ
    rw [integral_congr_ae hinner, integral_const, prob_real_univ, one_smul]
  have htri (z) : Φσ z ≤ Ψ1 z + Ψ2 z := by
    refine ciSup_le fun i => ?_
    have hsplit : ∑ j, z.2 j * (f i (z.1.1 j) - f i (z.1.2 j)) =
        ∑ j, z.2 j * f i (z.1.1 j) - ∑ j, z.2 j * f i (z.1.2 j) := by
      simp_rw [mul_sub]
      exact Finset.sum_sub_distrib _ _
    have habs : |(n : ℝ)⁻¹ *
        (∑ j, z.2 j * f i (z.1.1 j) - ∑ j, z.2 j * f i (z.1.2 j))| ≤
        |(n : ℝ)⁻¹ * ∑ j, z.2 j * f i (z.1.1 j)| +
          |(n : ℝ)⁻¹ * ∑ j, z.2 j * f i (z.1.2 j)| := by
      let a := ∑ j, z.2 j * f i (z.1.1 j)
      let b := ∑ j, z.2 j * f i (z.1.2 j)
      calc
        |(n : ℝ)⁻¹ * (a - b)| = (n : ℝ)⁻¹ * |a - b| := by
          rw [abs_mul, abs_of_nonneg hinv0]
        _ ≤ (n : ℝ)⁻¹ * (|a| + |b|) := mul_le_mul_of_nonneg_left (abs_sub a b) hinv0
        _ = (n : ℝ)⁻¹ * |a| + (n : ℝ)⁻¹ * |b| := by rw [mul_add]
        _ = |(n : ℝ)⁻¹ * a| + |(n : ℝ)⁻¹ * b| := by
          apply congrArg₂ (· + ·)
          · rw [abs_mul, abs_of_nonneg hinv0]
          · rw [abs_mul, abs_of_nonneg hinv0]
    rw [hsplit]
    exact habs.trans (add_le_add (le_ciSup (hbddψ z.2 z.1.1) i) (le_ciSup (hbddψ z.2 z.1.2) i))
  have hsum_int : Integrable (fun z => Ψ1 z + Ψ2 z) m := hΨ1int.add hΨ2int
  have hI1 : ∫ z, Ψ1 z ∂m = ∫ q, ψ q ∂π.prod ρ := by
    have hF : Integrable (fun y => ∫ σ, ψ (y, σ) ∂ρ) π := hψint.integral_prod_left
    rw [integral_prod _ hΨ1int, integral_fst_of_prob hF, integral_prod _ hψint]
  have hI2 : ∫ z, Ψ2 z ∂m = ∫ q, ψ q ∂π.prod ρ := by
    have hF : Integrable (fun y => ∫ σ, ψ (y, σ) ∂ρ) π := hψint.integral_prod_left
    rw [integral_prod _ hΨ2int, integral_snd_of_prob hF, integral_prod _ hψint]
  calc
    ∫ p, Φ p ∂π.prod π = ∫ z, Φσ z ∂m := heq_sign.symm
    _ ≤ ∫ z, Ψ1 z + Ψ2 z ∂m := integral_mono hΦσint hsum_int htri
    _ = ∫ z, Ψ1 z ∂m + ∫ z, Ψ2 z ∂m := integral_add hΨ1int hΨ2int
    _ = ∫ q, ψ q ∂π.prod ρ + ∫ q, ψ q ∂π.prod ρ := by rw [hI1, hI2]
    _ = 2 * ∫ q, ψ q ∂π.prod ρ := by rw [← two_mul]

/-- **07.33**: symmetrization for a nonempty countable class with an integrable envelope.
The signs are sampled on a separate probability space, so independence from the data is explicit. -/
theorem symmetrization {Ω Ω' E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace E] [Countable ι] [Nonempty ι]
    (μ : Measure Ω) (ν : Measure Ω') (P : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → E) (ε : Fin n → Ω' → ℝ)
    (hX : ∀ i, Measurable (X i)) (hXi : iIndepFun X μ)
    (hlaw : ∀ i, μ.map (X i) = P) (hε : ∀ i, IsRademacher (ε i) ν)
    (hεi : iIndepFun ε ν) (f : ι → E → ℝ) (hf : ∀ i, Measurable (f i))
    (envelope : E → ℝ) (he : Integrable envelope P)
    (hbound : ∀ i x, |f i x| ≤ envelope x) :
    (∫ ω, ⨆ i, |(n : ℝ)⁻¹ * (∑ j, f i (X j ω)) - ∫ x, f i x ∂P| ∂μ) ≤
      2 * ∫ ω, ⨆ i, |(n : ℝ)⁻¹ * ∑ j, ε j ω.2 * f i (X j ω.1)| ∂μ.prod ν := by
  let π : Measure (Fin n → E) := Measure.pi (fun _ => P)
  let ρ : Measure (Fin n → ℝ) :=
    Measure.pi (fun _ : Fin n =>
      (1 / 2 : ℝ≥0∞) • Measure.dirac (-1) + (1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ))
  let sample : Ω → Fin n → E := fun ω j => X j ω
  let signs : Ω' → Fin n → ℝ := fun ω' j => ε j ω'
  have hsample_meas : Measurable sample := by
    rw [measurable_pi_iff]
    intro j
    exact hX j
  have hsigns_meas : Measurable signs := by
    rw [measurable_pi_iff]
    intro j
    exact (hε j).1
  have hsample_law : μ.map sample = π := by
    rw [hXi.map_fun_eq_pi_map fun j => (hX j).aemeasurable]
    refine congrArg Measure.pi ?_
    funext j
    exact hlaw j
  have hsigns_law : ν.map signs = ρ := by
    rw [hεi.map_fun_eq_pi_map fun j => (hε j).1.aemeasurable]
    refine congrArg Measure.pi ?_
    funext j
    exact (hε j).2
  have hpush : (μ.prod ν).map (Prod.map sample signs) = π.prod ρ := by
    rw [← Measure.map_prod_map μ ν hsample_meas hsigns_meas, hsample_law, hsigns_law]
  have hleft_meas : Measurable (fun y : Fin n → E =>
      ⨆ i, |(n : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P|) := by
    refine Measurable.iSup fun i => measurable_abs.comp ?_
    exact ((Finset.measurable_fun_sum Finset.univ fun j _ =>
      (hf i).comp (measurable_pi_apply j)).const_mul (n : ℝ)⁻¹).sub measurable_const
  have hright_meas : Measurable (fun q : (Fin n → E) × (Fin n → ℝ) =>
      ⨆ i, |(n : ℝ)⁻¹ * ∑ j, q.2 j * f i (q.1 j)|) := by
    refine Measurable.iSup fun i => measurable_abs.comp ?_
    refine (Finset.measurable_fun_sum Finset.univ fun j _ => ?_).const_mul (n : ℝ)⁻¹
    exact ((measurable_pi_apply j).comp measurable_snd).mul
      ((hf i).comp ((measurable_pi_apply j).comp measurable_fst))
  calc
    (∫ ω, ⨆ i, |(n : ℝ)⁻¹ * (∑ j, f i (X j ω)) - ∫ x, f i x ∂P| ∂μ) =
        ∫ y, ⨆ i, |(n : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P| ∂π := by
      rw [← hsample_law]
      exact (integral_map hsample_meas.aemeasurable
        hleft_meas.aemeasurable.aestronglyMeasurable).symm
    _ ≤ ∫ p, ⨆ i, |(n : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))| ∂π.prod π :=
      expectedSup_centered_le_ghost hn hf he hbound
    _ ≤ 2 * ∫ q, ⨆ i, |(n : ℝ)⁻¹ * ∑ j, q.2 j * f i (q.1 j)| ∂π.prod ρ :=
      expectedSup_ghost_le_twice_signed hn hf he hbound
    _ = 2 * ∫ ω, ⨆ i, |(n : ℝ)⁻¹ * ∑ j, ε j ω.2 * f i (X j ω.1)| ∂μ.prod ν := by
      rw [← hpush]
      refine congrArg (fun t : ℝ => 2 * t) ?_
      exact integral_map (hsample_meas.prodMap hsigns_meas).aemeasurable
        hright_meas.aemeasurable.aestronglyMeasurable

end CKMA
