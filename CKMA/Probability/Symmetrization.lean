/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Probability.Distributions.Rademacher.Basic

/-!
# Empirical symmetrization (07.33)

`IsRademacher` fixes the symmetric law on the real signs, TauCeti's
`TauCeti.Probability.rademacherMeasure`. `symmetrization` bounds the
expected supremum of centered empirical averages by twice the corresponding signed
supremum for a nonempty countable function class with an integrable envelope;
`symmetrization_of_measurable` proves the same inequality for an arbitrary nonempty class
whose relevant suprema are measurable functions of the sample points.

Data and signs are sampled on separate probability spaces. Independence within each
sample and equality of the data laws are explicit; the nonempty finite sample index
avoids a zero-sample mean convention.

## Main definitions

* `CKMA.IsRademacher`: predicate for a measurable random variable with the symmetric law on
  `{-1, 1}`.

## Main results

* `CKMA.symmetrization_of_measurable`: empirical symmetrization inequality for an arbitrary
  nonempty function class with an integrable envelope and measurable suprema (**07.33**).
* `CKMA.symmetrization`: empirical symmetrization inequality for a nonempty countable function
  class with an integrable envelope (**07.33**).
-/

public section

noncomputable section

namespace CKMA

open scoped NNReal ENNReal

open MeasureTheory ProbabilityTheory TauCeti.Probability
open scoped BigOperators

/-- A measurable sign with the symmetric law on `{-1, 1}`, TauCeti's
`TauCeti.Probability.rademacherMeasure`. -/
@[expose]
def IsRademacher {Ω : Type*} [MeasurableSpace Ω] (ε : Ω → ℝ) (μ : Measure Ω) : Prop :=
  Measurable ε ∧ μ.map ε = rademacherMeasure

/-- Defining property of `IsRademacher`. -/
lemma isRademacher_iff {Ω : Type*} [MeasurableSpace Ω] {ε : Ω → ℝ} {μ : Measure Ω} :
    IsRademacher ε μ ↔ Measurable ε ∧ μ.map ε = rademacherMeasure :=
  Iff.rfl

/-- Swap the paired coordinates whose sign equals `-1`. -/
private def pairFlip {E J : Type*} (σ : J → ℝ) (z : J → E × E) :
    J → E × E :=
  fun j => if σ j = -1 then (z j).swap else z j

/-- Exchange the two ghost samples on the coordinates whose sign equals `-1`. -/
private def ghostFlip {E J : Type*} (σ : J → ℝ)
    (p : (J → E) × (J → E)) : (J → E) × (J → E) :=
  (fun j => if σ j = -1 then p.2 j else p.1 j,
    fun j => if σ j = -1 then p.1 j else p.2 j)

/-- Coordinatewise swaps of `P × P` preserve the law of an i.i.d. ghost pair. -/
private lemma ghostFlip_measurePreserving {E J : Type*} [MeasurableSpace E] [Fintype J]
    {P : Measure E} [IsProbabilityMeasure P] (σ : J → ℝ) :
    MeasurePreserving (ghostFlip σ)
      ((Measure.pi (fun _ : J => P)).prod (Measure.pi (fun _ : J => P)))
      ((Measure.pi (fun _ : J => P)).prod (Measure.pi (fun _ : J => P))) := by
  let π : Measure (J → E) := Measure.pi (fun _ => P)
  let Q : Measure (J → E × E) := Measure.pi (fun _ => P.prod P)
  let flip (j : J) : E × E → E × E := fun p => if σ j = -1 then p.swap else p
  have hφ (j : J) : Measurable (flip j) := by
    by_cases hσ : σ j = -1
    · simpa [flip, hσ] using (measurable_swap : Measurable (Prod.swap : E × E → E × E))
    · have hid : flip j = id := by
        funext p
        simp [flip, hσ]
      simpa [hid] using (measurable_id : Measurable (id : E × E → E × E))
  have hcoord (j : J) : (P.prod P).map (flip j) = P.prod P := by
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
  have hpair_meas : Measurable (pairFlip (E := E) σ) := by
    rw [measurable_pi_iff]
    intro j
    change Measurable (flip j ∘ fun (x : J → E × E) => x j)
    exact (hφ j).comp (measurable_pi_apply j)
  have hpair_map : Q.map (pairFlip (E := E) σ) = Q := by
    have hfun : pairFlip (E := E) σ = fun z j => flip j (z j) := rfl
    rw [hfun, Measure.pi_map_pi (fun j => (hφ j).aemeasurable)]
    congr
    funext j
    exact hcoord j
  let e := MeasurableEquiv.arrowProdEquivProdArrow E E J
  have he : MeasurePreserving (⇑e) Q (π.prod π) :=
    measurePreserving_arrowProdEquivProdArrow E E J (fun _ => P) (fun _ => P)
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

/-- An integrable real function dominated by the envelope is integrable. -/
private lemma integrable_of_envelope {E : Type*} [MeasurableSpace E] {P : Measure E}
    {g envelope : E → ℝ} (hg : Measurable g)
    (he : Integrable envelope P) (henv0 : ∀ x, 0 ≤ envelope x)
    (hbound : ∀ x, |g x| ≤ envelope x) : Integrable g P := by
  refine he.mono hg.aemeasurable.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (henv0 x)]
  exact hbound x

/-- The sum of the envelopes of an i.i.d. sample is integrable. -/
private lemma integrable_sum_envelope {E J : Type*} [MeasurableSpace E] [Fintype J]
    {P : Measure E} [IsProbabilityMeasure P] {envelope : E → ℝ} (he : Integrable envelope P) :
    Integrable (fun y : J → E => ∑ j, envelope (y j)) (Measure.pi fun _ => P) :=
  integrable_finsetSum _ fun j _ =>
    (measurePreserving_eval (fun _ : J => P) j).integrable_comp_of_integrable he

/-- The averaged ghost difference is dominated by the averaged envelopes of both samples. -/
private lemma abs_avg_sub_le {E ι J : Type*} [Fintype J] {f : ι → E → ℝ} {envelope : E → ℝ}
    (hbound : ∀ i x, |f i x| ≤ envelope x) (i : ι) (y y' : J → E) :
    |(Fintype.card J : ℝ)⁻¹ * ∑ j, (f i (y j) - f i (y' j))| ≤
      (Fintype.card J : ℝ)⁻¹ * ∑ j, (envelope (y j) + envelope (y' j)) := by
  have hinv0 : 0 ≤ (Fintype.card J : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  rw [abs_mul, abs_of_nonneg hinv0]
  refine mul_le_mul_of_nonneg_left ?_ hinv0
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  exact (abs_sub _ _).trans (add_le_add (hbound i _) (hbound i _))

/-- The supremum over the class of averaged ghost differences is measurable. -/
private lemma measurable_ghostSup {E ι J : Type*} [MeasurableSpace E] [Countable ι]
    [Fintype J] {f : ι → E → ℝ} (hf : ∀ i, Measurable (f i)) :
    Measurable fun p : (J → E) × (J → E) =>
      ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))| := by
  refine Measurable.iSup fun i => continuous_abs.measurable.comp ?_
  refine (Finset.measurable_fun_sum Finset.univ fun j _ => ?_).const_mul _
  exact ((hf i).comp ((measurable_pi_apply j).comp measurable_fst)).sub
    ((hf i).comp ((measurable_pi_apply j).comp measurable_snd))

/-- The supremum of the averaged ghost differences is dominated by the averaged envelopes. -/
private lemma ghostSup_le {E ι J : Type*} [Nonempty ι] [Fintype J] {f : ι → E → ℝ}
    {envelope : E → ℝ} (hbound : ∀ i x, |f i x| ≤ envelope x) (y y' : J → E) :
    ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, (f i (y j) - f i (y' j))| ≤
      (Fintype.card J : ℝ)⁻¹ * ∑ j, (envelope (y j) + envelope (y' j)) :=
  ciSup_le fun i => abs_avg_sub_le hbound i y y'

/-- The supremum of the averaged ghost differences is integrable for two i.i.d. samples,
and so is each of its sections in the second sample. -/
private lemma integrable_ghostSup {E ι J : Type*} [MeasurableSpace E]
    [Nonempty ι] [Fintype J] {P : Measure E} [IsProbabilityMeasure P] {f : ι → E → ℝ}
    (hmeas : Measurable fun p : (J → E) × (J → E) =>
      ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))|)
    {envelope : E → ℝ} (he : Integrable envelope P)
    (hbound : ∀ i x, |f i x| ≤ envelope x) :
    Integrable (fun p : (J → E) × (J → E) =>
        ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))|)
        ((Measure.pi fun _ : J => P).prod (Measure.pi fun _ : J => P)) ∧
      ∀ y : J → E, Integrable (fun y' : J → E =>
        ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, (f i (y j) - f i (y' j))|)
        (Measure.pi fun _ : J => P) := by
  let π : Measure (J → E) := Measure.pi fun _ => P
  have henvSum : Integrable (fun y : J → E => ∑ j, envelope (y j)) π :=
    integrable_sum_envelope he
  have hnorm (y y' : J → E) :
      ‖⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, (f i (y j) - f i (y' j))|‖ ≤
        (Fintype.card J : ℝ)⁻¹ * ∑ j, (envelope (y j) + envelope (y' j)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.iSup_nonneg fun _ => abs_nonneg _)]
    exact ghostSup_le hbound y y'
  constructor
  · have hdom : Integrable (fun p : (J → E) × (J → E) =>
        (Fintype.card J : ℝ)⁻¹ * ∑ j, (envelope (p.1 j) + envelope (p.2 j))) (π.prod π) := by
      simp_rw [Finset.sum_add_distrib]
      exact ((henvSum.comp_fst π).add (henvSum.comp_snd π)).const_mul _
    refine hdom.mono' hmeas.aemeasurable.aestronglyMeasurable ?_
    filter_upwards with p
    exact hnorm p.1 p.2
  · intro y
    have hdom : Integrable (fun y' : J → E =>
        (Fintype.card J : ℝ)⁻¹ * ∑ j, (envelope (y j) + envelope (y' j))) π := by
      simp_rw [Finset.sum_add_distrib]
      exact ((integrable_const _).add henvSum).const_mul _
    refine hdom.mono' (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable ?_
    filter_upwards with y'
    exact hnorm y y'

/-- The supremum over the class of centered empirical means is measurable. -/
private lemma measurable_centeredSup {E ι J : Type*} [MeasurableSpace E] [Countable ι]
    [Fintype J] {f : ι → E → ℝ} (hf : ∀ i, Measurable (f i)) (c : ι → ℝ) :
    Measurable fun y : J → E => ⨆ i, |(Fintype.card J : ℝ)⁻¹ * (∑ j, f i (y j)) - c i| := by
  refine Measurable.iSup fun i => continuous_abs.measurable.comp ?_
  exact ((Finset.measurable_fun_sum Finset.univ fun j _ =>
    (hf i).comp (measurable_pi_apply j)).const_mul _).sub measurable_const

/-- Averaging the ghost differences over the ghost sample recovers the centered empirical
mean. -/
private lemma integral_avg_sub_ghost {E J : Type*} [MeasurableSpace E] [Fintype J] [Nonempty J]
    {P : Measure E} [IsProbabilityMeasure P] {g : E → ℝ} (hg : Measurable g)
    (hgi : Integrable g P) (y : J → E) :
    ∫ y', (Fintype.card J : ℝ)⁻¹ * ∑ j, (g (y j) - g (y' j)) ∂Measure.pi (fun _ => P) =
      (Fintype.card J : ℝ)⁻¹ * (∑ j, g (y j)) - ∫ x, g x ∂P := by
  let π : Measure (J → E) := Measure.pi fun _ => P
  have hn0 : (Fintype.card J : ℝ) ≠ 0 := (Nat.cast_pos.mpr Fintype.card_pos).ne'
  have hevalg (j : J) : Integrable (fun y : J → E => g (y j)) π :=
    (measurePreserving_eval (fun _ : J => P) j).integrable_comp_of_integrable hgi
  have hmarg (j : J) : ∫ y, g (y j) ∂π = ∫ x, g x ∂P := by
    have hpres := measurePreserving_eval (fun _ : J => P) j
    rw [← hpres.map_eq]
    exact (integral_map hpres.measurable.aemeasurable hg.aemeasurable.aestronglyMeasurable).symm
  have hterm (j : J) : Integrable (fun y' : J → E => g (y j) - g (y' j)) π :=
    (integrable_const _).sub (hevalg j)
  rw [integral_const_mul, integral_finsetSum _ fun j _ => hterm j]
  have hsub (j : J) : ∫ y', g (y j) - g (y' j) ∂π = g (y j) - ∫ x, g x ∂P := by
    rw [integral_sub (integrable_const _) (hevalg j), integral_const, hmarg j,
      probReal_univ, one_smul]
  simp_rw [hsub, Finset.sum_sub_distrib]
  have hsummean : ∑ _j : J, (∫ x, g x ∂P) = (Fintype.card J : ℝ) * ∫ x, g x ∂P := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hsummean, mul_sub, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]

/-- The supremum of the centered empirical means is integrable, being dominated by the
averaged envelope plus the mean envelope. -/
private lemma integrable_centeredSup {E ι J : Type*} [MeasurableSpace E]
    [Nonempty ι] [Fintype J] {P : Measure E} [IsProbabilityMeasure P] {f : ι → E → ℝ}
    (hf : ∀ i, Measurable (f i))
    (hmeas : Measurable fun y : J → E =>
      ⨆ i, |(Fintype.card J : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P|)
    {envelope : E → ℝ} (he : Integrable envelope P)
    (hbound : ∀ i x, |f i x| ≤ envelope x) :
    Integrable (fun y : J → E =>
      ⨆ i, |(Fintype.card J : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P|)
      (Measure.pi fun _ => P) := by
  have hinv0 : 0 ≤ (Fintype.card J : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have henv0 (x : E) : 0 ≤ envelope x :=
    Nonempty.elim ‹Nonempty ι› fun i => (abs_nonneg _).trans (hbound i x)
  let hC : ℝ := ∫ x, envelope x ∂P
  have hmean_le (i : ι) : |∫ x, f i x ∂P| ≤ hC :=
    abs_integral_le_integral_abs.trans <|
      integral_mono (integrable_of_envelope (hf i) he henv0 (hbound i)).abs he
        fun x => hbound i x
  have hcent_le (i : ι) (y : J → E) :
      |(Fintype.card J : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P| ≤
        (Fintype.card J : ℝ)⁻¹ * ∑ j, envelope (y j) + hC := by
    calc
      |(Fintype.card J : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P| ≤
          |(Fintype.card J : ℝ)⁻¹ * ∑ j, f i (y j)| + |∫ x, f i x ∂P| := abs_sub _ _
      _ ≤ (Fintype.card J : ℝ)⁻¹ * ∑ j, |f i (y j)| + hC := by
        refine add_le_add ?_ (hmean_le i)
        rw [abs_mul, abs_of_nonneg hinv0]
        exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hinv0
      _ ≤ (Fintype.card J : ℝ)⁻¹ * ∑ j, envelope (y j) + hC :=
        add_le_add
          (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hbound i (y j)) hinv0)
          le_rfl
  have hdomL : Integrable (fun y : J → E =>
      (Fintype.card J : ℝ)⁻¹ * ∑ j, envelope (y j) + hC) (Measure.pi fun _ => P) :=
    ((integrable_sum_envelope he).const_mul _).add (integrable_const _)
  refine hdomL.mono' hmeas.aemeasurable.aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.iSup_nonneg fun _ => abs_nonneg _)]
  exact ciSup_le fun i => hcent_le i y

/-- Centering an empirical mean by an independent ghost sample does not decrease the
expected supremum. -/
private lemma expectedSup_centered_le_ghost {E ι J : Type*} [MeasurableSpace E]
    [Nonempty ι] [Fintype J] [Nonempty J] {P : Measure E} [IsProbabilityMeasure P]
    {f : ι → E → ℝ} (hf : ∀ i, Measurable (f i))
    (hcent : Measurable fun y : J → E =>
      ⨆ i, |(Fintype.card J : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P|)
    (hghost : Measurable fun p : (J → E) × (J → E) =>
      ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))|)
    {envelope : E → ℝ} (he : Integrable envelope P) (hbound : ∀ i x, |f i x| ≤ envelope x) :
    (∫ y, ⨆ i, |(Fintype.card J : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P|
        ∂Measure.pi (fun _ : J => P)) ≤
      ∫ p, ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))|
        ∂(Measure.pi (fun _ : J => P)).prod (Measure.pi (fun _ : J => P)) := by
  let π : Measure (J → E) := Measure.pi (fun _ => P)
  let Φ : (J → E) × (J → E) → ℝ := fun p =>
    ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))|
  have henv0 (x : E) : 0 ≤ envelope x :=
    Nonempty.elim ‹Nonempty ι› fun i => (abs_nonneg _).trans (hbound i x)
  obtain ⟨hΦint, hslice⟩ := integrable_ghostSup (J := J) hghost he hbound
  have hsup_le (y : J → E) :
      ⨆ i, |(Fintype.card J : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P| ≤
        ∫ y', Φ (y, y') ∂π := by
    refine ciSup_le fun i => ?_
    rw [← integral_avg_sub_ghost (hf i) (integrable_of_envelope (hf i) he henv0 (hbound i)) y]
    refine (abs_integral_le_integral_abs).trans ?_
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (hslice y) ?_
    exact ae_of_all _ fun y' => le_ciSup ⟨_, by
      rintro _ ⟨k, rfl⟩
      exact abs_avg_sub_le hbound k y y'⟩ i
  calc
    (∫ y, ⨆ i, |(Fintype.card J : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P| ∂π) ≤
        ∫ y, ∫ y', Φ (y, y') ∂π ∂π :=
      integral_mono (integrable_centeredSup hf hcent he hbound) hΦint.integral_prod_left hsup_le
    _ = ∫ p, Φ p ∂π.prod π := (integral_prod _ hΦint).symm

/-- Almost every Rademacher sign vector takes values in `{-1, 1}`. -/
private lemma ae_mem_signs {J : Type*} [Fintype J] :
    ∀ᵐ σ ∂Measure.pi (fun _ : J => rademacherMeasure),
      σ ∈ Set.univ.pi fun _ => ({-1, 1} : Set ℝ) := by
  let ρ : Measure (J → ℝ) := Measure.pi (fun _ => rademacherMeasure)
  let S : Set (J → ℝ) := Set.univ.pi (fun _ => ({-1, 1} : Set ℝ))
  have hpair_meas : MeasurableSet ({-1, 1} : Set ℝ) :=
    (measurableSet_singleton (1 : ℝ)).insert (-1)
  have hSmeas : MeasurableSet S := MeasurableSet.univ_pi fun _ => hpair_meas
  have hSmeasure : ρ S = 1 := by
    dsimp only [ρ, S]
    rw [Measure.pi_pi]
    have hrad : rademacherMeasure ({-1, 1} : Set ℝ) = 1 := by
      rw [rademacherMeasure_eq]
      simp [ENNReal.inv_two_add_inv_two]
    simp only [hrad, Finset.prod_const_one]
  have hnull : ρ Sᶜ = 0 := by
    rw [measure_compl hSmeas (by simp [hSmeasure] : ρ S ≠ ∞), hSmeasure, measure_univ]
    exact ENNReal.sub_eq_of_eq_add (by simp) (by simp)
  rw [ae_iff]
  exact hnull

/-- A sign vector with values in `{-1, 1}` has coordinates of absolute value one. -/
private lemma abs_eq_one_of_mem_signs {J : Type*} {σ : J → ℝ}
    (hσ : σ ∈ Set.univ.pi fun _ => ({-1, 1} : Set ℝ)) (j : J) : |σ j| = 1 := by
  have hj : σ j = -1 ∨ σ j = 1 := by
    simpa [Set.mem_univ_pi, Set.mem_insert_iff, Set.mem_singleton_iff] using hσ j
  rcases hj with h | h <;> simp [h]

/-- For a sign vector with values in `{-1, 1}`, multiplying the ghost differences by the
signs amounts to swapping the two samples on the coordinates with sign `-1`. -/
private lemma signedGhostSup_eq_ghostFlip {E ι J : Type*} [Fintype J] {f : ι → E → ℝ}
    {σ : J → ℝ} (hσ : σ ∈ Set.univ.pi fun _ => ({-1, 1} : Set ℝ)) (p : (J → E) × (J → E)) :
    ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, σ j * (f i (p.1 j) - f i (p.2 j))| =
      ⨆ i, |(Fintype.card J : ℝ)⁻¹ *
        ∑ j, (f i ((ghostFlip σ p).1 j) - f i ((ghostFlip σ p).2 j))| := by
  have hone : (1 : ℝ) ≠ -1 :=
    (ne_of_lt (lt_trans (neg_lt_zero.mpr zero_lt_one) zero_lt_one)).symm
  have hterms (i : ι) :
      ∑ j, (f i ((ghostFlip σ p).1 j) - f i ((ghostFlip σ p).2 j)) =
        ∑ j, σ j * (f i (p.1 j) - f i (p.2 j)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : σ j = -1 ∨ σ j = 1 := by
      simpa [Set.mem_univ_pi, Set.mem_insert_iff, Set.mem_singleton_iff] using hσ j
    rcases hj with hj | hj
    · have h1 : (ghostFlip σ p).1 j = p.2 j := by simp [ghostFlip, hj]
      have h2 : (ghostFlip σ p).2 j = p.1 j := by simp [ghostFlip, hj]
      rw [h1, h2, hj, neg_one_mul, neg_sub]
    · have hne : σ j ≠ -1 := by simpa [hj] using hone
      have h1 : (ghostFlip σ p).1 j = p.1 j := by simp [ghostFlip, hne]
      have h2 : (ghostFlip σ p).2 j = p.2 j := by simp [ghostFlip, hne]
      rw [h1, h2, hj, one_mul]
  exact congr_arg iSup (funext fun i => by rw [hterms i])

/-- The sign-dependent swap of the two ghost samples is jointly measurable. -/
private lemma measurable_ghostFlip_uncurry {E J : Type*} [MeasurableSpace E] :
    Measurable fun z : ((J → E) × (J → E)) × (J → ℝ) => ghostFlip z.2 z.1 := by
  have hset (j : J) : MeasurableSet {z : ((J → E) × (J → E)) × (J → ℝ) | z.2 j = -1} :=
    measurableSet_eq_fun ((measurable_pi_apply j).comp measurable_snd) measurable_const
  have h1 (j : J) : Measurable fun z : ((J → E) × (J → E)) × (J → ℝ) => z.1.1 j :=
    (measurable_pi_apply j).comp (measurable_fst.comp measurable_fst)
  have h2 (j : J) : Measurable fun z : ((J → E) × (J → E)) × (J → ℝ) => z.1.2 j :=
    (measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)
  refine Measurable.prodMk ?_ ?_ <;> rw [measurable_pi_iff] <;> intro j
  · exact Measurable.ite (hset j) (h2 j) (h1 j)
  · exact Measurable.ite (hset j) (h1 j) (h2 j)

/-- For a fixed sign vector with values in `{-1, 1}`, multiplying the ghost differences by
the signs does not change the expected ghost supremum, because swapping the two samples on
the coordinates with sign `-1` preserves their joint law. -/
private lemma integral_signedGhostSup_eq {E ι J : Type*} [MeasurableSpace E]
    [Fintype J] {P : Measure E} [IsProbabilityMeasure P] {f : ι → E → ℝ}
    (hghost : Measurable fun p : (J → E) × (J → E) =>
      ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))|)
    {σ : J → ℝ} (hσ : σ ∈ Set.univ.pi fun _ => ({-1, 1} : Set ℝ)) :
    ∫ p, ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, σ j * (f i (p.1 j) - f i (p.2 j))|
        ∂(Measure.pi (fun _ : J => P)).prod (Measure.pi (fun _ : J => P)) =
      ∫ p, ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))|
        ∂(Measure.pi (fun _ : J => P)).prod (Measure.pi (fun _ : J => P)) := by
  let π : Measure (J → E) := Measure.pi (fun _ => P)
  let Φ : (J → E) × (J → E) → ℝ := fun p =>
    ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))|
  have hpres := ghostFlip_measurePreserving (P := P) σ
  have hint : ∫ p, Φ (ghostFlip σ p) ∂π.prod π = ∫ p, Φ p ∂π.prod π := by
    conv_rhs => rw [← hpres.map_eq]
    exact (integral_map hpres.measurable.aemeasurable
      (hghost.aestronglyMeasurable :
        AEStronglyMeasurable Φ (Measure.map (ghostFlip σ) (π.prod π)))).symm
  rw [← hint]
  exact integral_congr_ae (ae_of_all _ fun p => signedGhostSup_eq_ghostFlip (f := f) hσ p)

/-- The supremum over the class of signed averages is measurable. -/
private lemma measurable_signedSup {E ι J : Type*} [MeasurableSpace E] [Countable ι]
    [Fintype J] {f : ι → E → ℝ} (hf : ∀ i, Measurable (f i)) :
    Measurable fun q : (J → E) × (J → ℝ) =>
      ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, q.2 j * f i (q.1 j)| := by
  refine Measurable.iSup fun i => continuous_abs.measurable.comp ?_
  refine (Finset.measurable_fun_sum Finset.univ fun j _ => ?_).const_mul _
  exact ((measurable_pi_apply j).comp measurable_snd).mul
    ((hf i).comp ((measurable_pi_apply j).comp measurable_fst))

/-- A signed average is dominated by the envelope weighted by the absolute signs. -/
private lemma abs_avg_signed_le {E ι J : Type*} [Fintype J] {f : ι → E → ℝ}
    {envelope : E → ℝ} (hbound : ∀ i x, |f i x| ≤ envelope x) (σ : J → ℝ) (y : J → E)
    (i : ι) :
    |(Fintype.card J : ℝ)⁻¹ * ∑ j, σ j * f i (y j)| ≤
      (Fintype.card J : ℝ)⁻¹ * ∑ j, |σ j| * envelope (y j) := by
  have hinv0 : 0 ≤ (Fintype.card J : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  rw [abs_mul, abs_of_nonneg hinv0]
  refine mul_le_mul_of_nonneg_left ?_ hinv0
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hbound i (y j)) (abs_nonneg _)

/-- The signed averages are bounded above uniformly over the class. -/
private lemma bddAbove_abs_avg_signed {E ι J : Type*} [Fintype J] {f : ι → E → ℝ}
    {envelope : E → ℝ} (hbound : ∀ i x, |f i x| ≤ envelope x) (σ : J → ℝ) (y : J → E) :
    BddAbove (Set.range fun i => |(Fintype.card J : ℝ)⁻¹ * ∑ j, σ j * f i (y j)|) :=
  ⟨_, by
    rintro _ ⟨i, rfl⟩
    exact abs_avg_signed_le hbound σ y i⟩

/-- For signs in `{-1, 1}`, the signed supremum is dominated by the averaged envelope. -/
private lemma signedSup_le_of_mem {E ι J : Type*} [Nonempty ι] [Fintype J] {f : ι → E → ℝ}
    {envelope : E → ℝ} (hbound : ∀ i x, |f i x| ≤ envelope x) {σ : J → ℝ}
    (hσ : σ ∈ Set.univ.pi fun _ => ({-1, 1} : Set ℝ)) (y : J → E) :
    ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, σ j * f i (y j)| ≤
      (Fintype.card J : ℝ)⁻¹ * ∑ j, envelope (y j) := by
  refine ciSup_le fun i => (abs_avg_signed_le hbound σ y i).trans_eq ?_
  simp only [abs_eq_one_of_mem_signs hσ, one_mul]

/-- The signed supremum is integrable for a sample and independent Rademacher signs. -/
private lemma integrable_signedSup {E ι J : Type*} [MeasurableSpace E]
    [Nonempty ι] [Fintype J] {P : Measure E} [IsProbabilityMeasure P] {f : ι → E → ℝ}
    (hsigned : Measurable fun q : (J → E) × (J → ℝ) =>
      ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, q.2 j * f i (q.1 j)|)
    {envelope : E → ℝ} (he : Integrable envelope P)
    (hbound : ∀ i x, |f i x| ≤ envelope x) :
    Integrable (fun q : (J → E) × (J → ℝ) =>
      ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, q.2 j * f i (q.1 j)|)
      ((Measure.pi fun _ : J => P).prod (Measure.pi fun _ : J => rademacherMeasure)) := by
  have hdom : Integrable (fun q : (J → E) × (J → ℝ) =>
      (Fintype.card J : ℝ)⁻¹ * ∑ j, envelope (q.1 j))
      ((Measure.pi fun _ : J => P).prod (Measure.pi fun _ : J => rademacherMeasure)) :=
    ((integrable_sum_envelope he).const_mul _).comp_fst _
  refine hdom.mono' hsigned.aemeasurable.aestronglyMeasurable ?_
  filter_upwards [(Measure.quasiMeasurePreserving_snd
    (μ := Measure.pi fun _ : J => P)).ae ae_mem_signs] with q hq
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.iSup_nonneg fun _ => abs_nonneg _)]
  exact signedSup_le_of_mem hbound hq q.1

/-- The triangle inequality splits the signed ghost supremum into the signed suprema of the
two samples. -/
private lemma signedGhostSup_le {E ι J : Type*} [Nonempty ι] [Fintype J] {f : ι → E → ℝ}
    {envelope : E → ℝ} (hbound : ∀ i x, |f i x| ≤ envelope x) (σ : J → ℝ) (y y' : J → E) :
    ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, σ j * (f i (y j) - f i (y' j))| ≤
      (⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, σ j * f i (y j)|) +
        ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, σ j * f i (y' j)| := by
  refine ciSup_le fun i => ?_
  have hsplit : (Fintype.card J : ℝ)⁻¹ * ∑ j, σ j * (f i (y j) - f i (y' j)) =
      (Fintype.card J : ℝ)⁻¹ * ∑ j, σ j * f i (y j) -
        (Fintype.card J : ℝ)⁻¹ * ∑ j, σ j * f i (y' j) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, mul_sub]
  rw [hsplit]
  exact (abs_sub _ _).trans (add_le_add (le_ciSup (bddAbove_abs_avg_signed hbound σ y) i)
    (le_ciSup (bddAbove_abs_avg_signed hbound σ y') i))

/-- The signed ghost supremum is integrable for two i.i.d. samples and independent
Rademacher signs. -/
private lemma integrable_signedGhostSup {E ι J : Type*} [MeasurableSpace E]
    [Nonempty ι] [Fintype J] {P : Measure E} [IsProbabilityMeasure P] {f : ι → E → ℝ}
    (hghost : Measurable fun p : (J → E) × (J → E) =>
      ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))|)
    {envelope : E → ℝ} (he : Integrable envelope P)
    (hbound : ∀ i x, |f i x| ≤ envelope x) :
    Integrable (fun z : ((J → E) × (J → E)) × (J → ℝ) =>
      ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, z.2 j * (f i (z.1.1 j) - f i (z.1.2 j))|)
      (((Measure.pi fun _ : J => P).prod (Measure.pi fun _ : J => P)).prod
        (Measure.pi fun _ : J => rademacherMeasure)) := by
  let π : Measure (J → E) := Measure.pi (fun _ => P)
  have hsigns := (Measure.quasiMeasurePreserving_snd (μ := π.prod π)).ae
    (ae_mem_signs (J := J))
  have hmeas : AEStronglyMeasurable (fun z : ((J → E) × (J → E)) × (J → ℝ) =>
      ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, z.2 j * (f i (z.1.1 j) - f i (z.1.2 j))|)
      ((π.prod π).prod (Measure.pi fun _ : J => rademacherMeasure)) := by
    refine (hghost.comp measurable_ghostFlip_uncurry).aestronglyMeasurable.congr ?_
    filter_upwards [hsigns] with z hz
    exact (signedGhostSup_eq_ghostFlip hz z.1).symm
  have hdom : Integrable (fun z : ((J → E) × (J → E)) × (J → ℝ) =>
      (Fintype.card J : ℝ)⁻¹ * ∑ j, envelope (z.1.1 j) +
        (Fintype.card J : ℝ)⁻¹ * ∑ j, envelope (z.1.2 j))
        ((π.prod π).prod (Measure.pi fun _ : J => rademacherMeasure)) :=
    ((((integrable_sum_envelope he).const_mul _).comp_fst π).comp_fst _).add
      ((((integrable_sum_envelope he).const_mul _).comp_snd π).comp_fst _)
  refine hdom.mono' hmeas ?_
  filter_upwards [hsigns] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.iSup_nonneg fun _ => abs_nonneg _)]
  exact (signedGhostSup_le hbound z.2 z.1.1 z.1.2).trans
    (add_le_add (signedSup_le_of_mem hbound hz _) (signedSup_le_of_mem hbound hz _))

/-- Composing an integrable function on a product with a measure-preserving map in the first
factor keeps it integrable and preserves its integral. -/
private lemma integrable_comp_fst_and_integral_eq {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure α} {μ' : Measure β} {ν : Measure γ}
    [SFinite μ] [SFinite ν] {g : α → β} (hg : MeasurePreserving g μ μ') {ψ : β × γ → ℝ}
    (hψm : Measurable ψ) (hψ : Integrable ψ (μ'.prod ν)) :
    Integrable (fun z : α × γ => ψ (g z.1, z.2)) (μ.prod ν) ∧
      ∫ z, ψ (g z.1, z.2) ∂μ.prod ν = ∫ q, ψ q ∂μ'.prod ν := by
  have h := hg.prod (MeasurePreserving.id ν)
  refine ⟨h.integrable_comp_of_integrable hψ, ?_⟩
  calc
    ∫ z, ψ (g z.1, z.2) ∂μ.prod ν = ∫ q, ψ q ∂(μ.prod ν).map (Prod.map g id) :=
      (integral_map h.measurable.aemeasurable hψm.aestronglyMeasurable).symm
    _ = ∫ q, ψ q ∂μ'.prod ν := by rw [h.map_eq]

/-- Random signs do not change the ghost comparison, and the triangle inequality
splits it into two equidistributed signed copies. -/
private lemma expectedSup_ghost_le_twice_signed {E ι J : Type*} [MeasurableSpace E]
    [Nonempty ι] [Fintype J] {P : Measure E} [IsProbabilityMeasure P] {f : ι → E → ℝ}
    (hghost : Measurable fun p : (J → E) × (J → E) =>
      ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))|)
    (hsigned : Measurable fun q : (J → E) × (J → ℝ) =>
      ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, q.2 j * f i (q.1 j)|)
    {envelope : E → ℝ} (he : Integrable envelope P) (hbound : ∀ i x, |f i x| ≤ envelope x) :
    (∫ p, ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))|
        ∂(Measure.pi (fun _ : J => P)).prod (Measure.pi (fun _ : J => P))) ≤
      2 * ∫ q, ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, q.2 j * f i (q.1 j)|
        ∂(Measure.pi (fun _ : J => P)).prod
          (Measure.pi (fun _ : J => rademacherMeasure)) := by
  let π : Measure (J → E) := Measure.pi (fun _ => P)
  let ρ : Measure (J → ℝ) := Measure.pi (fun _ => rademacherMeasure)
  let Φσ : ((J → E) × (J → E)) × (J → ℝ) → ℝ := fun z =>
    ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, z.2 j * (f i (z.1.1 j) - f i (z.1.2 j))|
  let ψ : (J → E) × (J → ℝ) → ℝ := fun q =>
    ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, q.2 j * f i (q.1 j)|
  have hψmeas : Measurable ψ := hsigned
  have hψint : Integrable ψ (π.prod ρ) := integrable_signedSup hsigned he hbound
  have hΦσint : Integrable Φσ ((π.prod π).prod ρ) := integrable_signedGhostSup hghost he hbound
  obtain ⟨hΨ1int, hI1⟩ :=
    integrable_comp_fst_and_integral_eq (measurePreserving_fst (μ := π) (ν := π)) hψmeas hψint
  obtain ⟨hΨ2int, hI2⟩ :=
    integrable_comp_fst_and_integral_eq (measurePreserving_snd (μ := π) (ν := π)) hψmeas hψint
  have heq_sign : ∫ z, Φσ z ∂(π.prod π).prod ρ = ∫ p, ⨆ i,
      |(Fintype.card J : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))| ∂π.prod π := by
    rw [integral_prod_symm _ hΦσint]
    have hinner : (fun σ => ∫ p, ⨆ i,
        |(Fintype.card J : ℝ)⁻¹ * ∑ j, σ j * (f i (p.1 j) - f i (p.2 j))| ∂π.prod π) =ᵐ[ρ]
        fun _ => ∫ p, ⨆ i,
          |(Fintype.card J : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))| ∂π.prod π := by
      filter_upwards [ae_mem_signs] with σ hσ
      exact integral_signedGhostSup_eq hghost hσ
    rw [integral_congr_ae hinner, integral_const, probReal_univ, one_smul]
  calc
    _ = ∫ z, Φσ z ∂(π.prod π).prod ρ := heq_sign.symm
    _ ≤ ∫ z, ψ (z.1.1, z.2) + ψ (z.1.2, z.2) ∂(π.prod π).prod ρ :=
      integral_mono hΦσint (hΨ1int.add hΨ2int) fun z => signedGhostSup_le hbound z.2 z.1.1 z.1.2
    _ = ∫ z, ψ (z.1.1, z.2) ∂(π.prod π).prod ρ + ∫ z, ψ (z.1.2, z.2) ∂(π.prod π).prod ρ :=
      integral_add hΨ1int hΨ2int
    _ = 2 * ∫ q, ψ q ∂π.prod ρ := by rw [hI1, hI2, ← two_mul]

/-- **07.33**, measurable-supremum form: symmetrization for an arbitrary nonempty class with
an integrable envelope, assuming that the three suprema over the class occurring in the argument
are measurable functions of the sample points: the centered empirical supremum, the supremum of
the ghost-sample differences, and the signed supremum. Data and signs live on separate
probability spaces, and the signed side is integrated over the product; `iIndepFun X μ` makes
`μ` a probability measure. The class is assumed nonempty for the proof; for an empty class both
sides are `0`. -/
theorem symmetrization_of_measurable {Ω Ω' E ι J : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace E] [Nonempty ι] [Fintype J] [Nonempty J]
    (μ : Measure Ω) (ν : Measure Ω') (P : Measure E)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure P]
    (X : J → Ω → E) (ε : J → Ω' → ℝ)
    (hX : ∀ j, Measurable (X j)) (hXi : iIndepFun X μ)
    (hlaw : ∀ j, μ.map (X j) = P) (hε : ∀ j, IsRademacher (ε j) ν)
    (hεi : iIndepFun ε ν) (f : ι → E → ℝ) (hf : ∀ i, Measurable (f i))
    (envelope : E → ℝ) (he : Integrable envelope P)
    (hbound : ∀ i x, |f i x| ≤ envelope x)
    (hcent : Measurable fun y : J → E =>
      ⨆ i, |(Fintype.card J : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P|)
    (hghost : Measurable fun p : (J → E) × (J → E) =>
      ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))|)
    (hsigned : Measurable fun q : (J → E) × (J → ℝ) =>
      ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, q.2 j * f i (q.1 j)|) :
    (∫ ω, ⨆ i, |(Fintype.card J : ℝ)⁻¹ * (∑ j, f i (X j ω)) - ∫ x, f i x ∂P| ∂μ) ≤
      2 * ∫ ω, ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, ε j ω.2 * f i (X j ω.1)| ∂μ.prod ν := by
  let n : ℕ := Fintype.card J
  let π : Measure (J → E) := Measure.pi (fun _ => P)
  let ρ : Measure (J → ℝ) := Measure.pi (fun _ : J => rademacherMeasure)
  let sample : Ω → J → E := fun ω j => X j ω
  let signs : Ω' → J → ℝ := fun ω' j => ε j ω'
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
  calc
    (∫ ω, ⨆ i, |(n : ℝ)⁻¹ * (∑ j, f i (X j ω)) - ∫ x, f i x ∂P| ∂μ) =
        ∫ y, ⨆ i, |(n : ℝ)⁻¹ * (∑ j, f i (y j)) - ∫ x, f i x ∂P| ∂π := by
      rw [← hsample_law]
      exact (integral_map hsample_meas.aemeasurable
        hcent.aemeasurable.aestronglyMeasurable).symm
    _ ≤ ∫ p, ⨆ i, |(n : ℝ)⁻¹ * ∑ j, (f i (p.1 j) - f i (p.2 j))| ∂π.prod π :=
      expectedSup_centered_le_ghost hf hcent hghost he hbound
    _ ≤ 2 * ∫ q, ⨆ i, |(n : ℝ)⁻¹ * ∑ j, q.2 j * f i (q.1 j)| ∂π.prod ρ :=
      expectedSup_ghost_le_twice_signed hghost hsigned he hbound
    _ = 2 * ∫ ω, ⨆ i, |(n : ℝ)⁻¹ * ∑ j, ε j ω.2 * f i (X j ω.1)| ∂μ.prod ν := by
      rw [← hpush]
      refine congrArg (fun t : ℝ => 2 * t) ?_
      exact integral_map (hsample_meas.prodMap hsigns_meas).aemeasurable
        hsigned.aemeasurable.aestronglyMeasurable

/-- **07.33**: symmetrization for a nonempty countable class with an integrable envelope.
The signs are sampled on a separate probability space, so independence from the data is
explicit; `iIndepFun X μ` makes `μ` a probability measure. The class is assumed nonempty for the
proof; for an empty class both sides are `0`. -/
theorem symmetrization {Ω Ω' E ι J : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace E] [Countable ι] [Nonempty ι] [Fintype J] [Nonempty J]
    (μ : Measure Ω) (ν : Measure Ω') (P : Measure E)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure P]
    (X : J → Ω → E) (ε : J → Ω' → ℝ)
    (hX : ∀ j, Measurable (X j)) (hXi : iIndepFun X μ)
    (hlaw : ∀ j, μ.map (X j) = P) (hε : ∀ j, IsRademacher (ε j) ν)
    (hεi : iIndepFun ε ν) (f : ι → E → ℝ) (hf : ∀ i, Measurable (f i))
    (envelope : E → ℝ) (he : Integrable envelope P)
    (hbound : ∀ i x, |f i x| ≤ envelope x) :
    (∫ ω, ⨆ i, |(Fintype.card J : ℝ)⁻¹ * (∑ j, f i (X j ω)) - ∫ x, f i x ∂P| ∂μ) ≤
      2 * ∫ ω, ⨆ i, |(Fintype.card J : ℝ)⁻¹ * ∑ j, ε j ω.2 * f i (X j ω.1)| ∂μ.prod ν :=
  symmetrization_of_measurable μ ν P X ε hX hXi hlaw hε hεi f hf envelope he hbound
    (measurable_centeredSup hf fun i => ∫ x, f i x ∂P) (measurable_ghostSup hf)
    (measurable_signedSup hf)

end CKMA
