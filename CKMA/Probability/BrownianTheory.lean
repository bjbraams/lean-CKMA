/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.BrownianTheory.Existence
public import CKMA.Probability.BrownianTheory.Reflection.Bound
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Probability.Process.Filtration.AmbientNullAugmentation

import TauCeti.Probability.Process.StoppingApproximation
import TauCeti.Probability.BrownianMotion.RightContinuity
import CKMA.Probability.ProjectiveLimit.Basic

/-!
# Brownian laws, modifications, strong Markov and reflection (08.1, 08.3, 08.4)

The canonical law is a probability measure on `C(ℝ≥0, ℝ)` with its compact-open Borel
sigma-algebra. Its coordinate process has continuous paths by construction. A separate
modification theorem starts from an arbitrary pre-Brownian process and gives every
local Hölder exponent below one half.

`brownianShift` describes increments after a finite-valued stopping time. The strong
Markov property is stated for any filtration relative to which the future increment process
after each deterministic time is independent of the past, with finite-dimensional
independence from the stopping-time sigma-algebra. It is specialized to the raw natural
filtration and to the right-continuous natural filtration augmented by the ambient null
events, where almost surely finite stopping times are allowed. The reflection principle uses
a strictly positive level and includes time zero.

The strong Markov property is proved by rounding the stopping time up to dyadic grids
(TauCeti's `dyadicCeilTime`). At each grid value the independence of the future increments
applies: Mathlib's weak Markov property `IsPreBrownianReal.indepFun_shift` for the natural
filtration, and TauCeti's `IsBrownianReal.indep_shift_rightCont_natural` for its
right-continuous augmentation. Path continuity and dominated convergence then pass
the identity to the original time, and finite Borel laws are identified by bounded continuous
test functions.
The target statements correspond to the indicated entries of `GAPS.md`.

## Main definitions

* `CKMA.brownianShift`: shifted process after a finite-valued stopping time.

## Main results

* `CKMA.exists_brownianMeasure`: existence of Wiener measure on `C(ℝ≥0, ℝ)` (**08.1**,
  in `BrownianTheory.Existence`).
* `CKMA.exists_holder_brownianModification`: existence of a continuous modification with every
  local Hölder exponent below `1 / 2`.
* `CKMA.brownian_strongMarkov_of_indep`: strong Markov property relative to any filtration
  whose past is independent of the future increments (**08.3**).
* `CKMA.brownian_strongMarkov`: strong Markov property for the natural filtration (**08.3**).
* `CKMA.brownian_strongMarkov_augmented`: strong Markov property for almost surely finite
  stopping times of the augmented right-continuous natural filtration (**08.3**).
* `CKMA.brownian_reflection`: reflection principle for Brownian motion (**08.4**,
  in `BrownianTheory.Reflection.Bound`).
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory Filter Brownian
open scoped NNReal ENNReal Topology

/-- **08.1**: a canonical Brownian law on the Borel space of continuous real paths.
The coordinate process is continuous for every sample path. -/
theorem exists_brownianMeasure : ∃ μ : Measure C(ℝ≥0, ℝ),
    IsProbabilityMeasure μ ∧ IsBrownianReal (fun t ω ↦ ω t) μ := by
  have : ∀ I : Finset ℝ≥0, IsProbabilityMeasure (BrownianReal.projectiveFamily I) :=
    fun _ => inferInstance
  obtain ⟨ν, hν, _⟩ := existsUnique_isProjectiveLimit (ι := ℝ≥0) (X := fun _ => ℝ)
    BrownianReal.projectiveFamily BrownianReal.isProjectiveMeasureFamily_projectiveFamily
  obtain ⟨hprob, hlim⟩ := hν
  have : IsProbabilityMeasure ν := hprob
  refine ⟨wienerOfPreBrownian (coordinatePreBrownian_isPreBrownian ν hlim),
    isProbabilityMeasure_wienerOfPreBrownian _,
    wienerOfPreBrownian_isBrownian _⟩

@[deprecated (since := "2026-11-15")] alias exists_wienerMeasure := exists_brownianMeasure

/-- A pre-Brownian process has a continuous modification that is almost surely locally Hölder
  of every exponent `α < 1 / 2`. -/
theorem exists_holder_brownianModification {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) :
    ∃ C : ℝ≥0 → Ω → ℝ, IsBrownianReal C μ ∧
      (∀ t, C t =ᵐ[μ] B t) ∧ ∀ᵐ ω ∂μ, ∀ α : ℝ≥0, α < 1 / 2 →
        ∀ T : ℝ≥0, ∃ K : ℝ≥0, HolderOnWith K α (fun t ↦ C t ω) (Set.Icc 0 T) := by
  obtain ⟨C, _, _, hBr, hmod, hH⟩ := exists_continuous_holder_modification hB
  exact ⟨C, hBr, hmod, hH⟩

/-- The shifted process after a finite-valued stopping time. -/
@[expose]
def brownianShift {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : ℝ := B (T ω + t) ω - B (T ω) ω

/-- Finite-dimensional laws of two pre-Brownian processes agree at arbitrary finite families of
times, repetitions allowed. -/
private lemma map_eval_eq_of_isPreBrownianReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : ℝ≥0 → Ω → ℝ} (hX : IsPreBrownianReal X μ) (hY : IsPreBrownianReal Y μ)
    {ι : Type*} [Fintype ι] (t : ι → ℝ≥0) :
    μ.map (fun ω i ↦ X (t i) ω) = μ.map (fun ω i ↦ Y (t i) ω) := by
  classical
  let I : Finset ℝ≥0 := Finset.univ.image t
  let g : (I → ℝ) → ι → ℝ :=
    fun x i ↦ x ⟨t i, Finset.mem_image_of_mem t (Finset.mem_univ i)⟩
  have hg : Measurable g := Measurable.of_eval fun i ↦ measurable_pi_apply _
  have hX' : μ.map (fun ω i ↦ X (t i) ω) = (μ.map (fun ω ↦ I.restrict (X · ω))).map g :=
    (AEMeasurable.map_map_of_aemeasurable hg.aemeasurable (hX.hasLaw I).aemeasurable).symm
  have hY' : μ.map (fun ω i ↦ Y (t i) ω) = (μ.map (fun ω ↦ I.restrict (Y · ω))).map g :=
    (AEMeasurable.map_map_of_aemeasurable hg.aemeasurable (hY.hasLaw I).aemeasurable).symm
  rw [hX', hY', (hX.hasLaw I).map_eq, (hY.hasLaw I).map_eq]

/-- Upward rounding of a finite random time to the dyadic grid of mesh `2 ^ (-n)`. -/
private def dyadicTime {Ω : Type*} (T : Ω → ℝ≥0) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  (⌈T ω * 2 ^ n⌉₊ : ℝ≥0) / 2 ^ n

/-- The dyadic index of a random time is fixed exactly on a level set of TauCeti's rounding. -/
private lemma setOf_ceil_eq {Ω : Type*} (T : Ω → ℝ≥0) (n k : ℕ) :
    {ω | ⌈T ω * 2 ^ n⌉₊ = k} =
      {ω | TauCeti.dyadicCeilTime n (T ω : WithTop ℝ≥0) =
        (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : WithTop ℝ≥0)} := by
  ext ω
  simp only [Set.mem_ofPred_eq, TauCeti.dyadicCeilTime_coe, WithTop.coe_inj,
    div_left_inj' (pow_ne_zero n (two_ne_zero : (2 : ℝ≥0) ≠ 0)), Nat.cast_inj]

/-- Dyadic rounding decreases to the original time. -/
private lemma tendsto_dyadicTime {Ω : Type*} (T : Ω → ℝ≥0) (ω : Ω) :
    Tendsto (fun n ↦ dyadicTime T n ω) atTop (𝓝 (T ω)) := by
  have hle (n : ℕ) : T ω ≤ dyadicTime T n ω := by
    have h := TauCeti.le_dyadicCeilTime n (T ω : WithTop ℝ≥0)
    rwa [TauCeti.dyadicCeilTime_coe, WithTop.coe_le_coe] at h
  have hlt (n : ℕ) : dyadicTime T n ω ≤ T ω + ((2 : ℝ≥0) ^ n)⁻¹ := by
    have h := TauCeti.dyadicCeilTime_lt n (T ω)
    rw [TauCeti.dyadicCeilTime_coe, WithTop.coe_lt_coe] at h
    exact h.le
  have hpow : Tendsto (fun n : ℕ ↦ ((2 : ℝ≥0) ^ n)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ≥0)⁻¹) zero_le (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ hle hlt
  simpa only [add_zero] using tendsto_const_nhds.add hpow

variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0}
  {𝒢 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- The dyadic index of a stopping time is measurable. -/
private lemma measurable_ceil (hT : IsStoppingTime 𝒢 (fun ω ↦ (T ω : WithTop ℝ≥0))) (n : ℕ) :
    Measurable (fun ω ↦ ⌈T ω * 2 ^ n⌉₊) := by
  refine measurable_to_countable' fun k ↦ ?_
  rw [show (fun ω ↦ ⌈T ω * 2 ^ n⌉₊) ⁻¹' {k} = {ω | ⌈T ω * 2 ^ n⌉₊ = k} from rfl,
    setOf_ceil_eq]
  exact Filtration.le _ _ _ ((hT.dyadicCeilTime n).measurableSet_eq_of_countable_range
    (TauCeti.countable_range_dyadicCeilTime _ n) _)

/-- Brownian increments after a dyadically rounded stopping time are measurable. -/
private lemma measurable_brownianShift_dyadicTime (hm : ∀ t, Measurable (B t))
    (hT : IsStoppingTime 𝒢 (fun ω ↦ (T ω : WithTop ℝ≥0))) (n : ℕ) (s : ℝ≥0) :
    Measurable (fun ω ↦ brownianShift B (dyadicTime T n) s ω) := by
  have hF : Measurable (fun p : Ω × ℕ ↦
      B ((p.2 : ℝ≥0) / 2 ^ n + s) p.1 - B ((p.2 : ℝ≥0) / 2 ^ n) p.1) :=
    measurable_from_prod_countable_left fun k ↦
      (hm ((k : ℝ≥0) / 2 ^ n + s)).sub (hm ((k : ℝ≥0) / 2 ^ n))
  have heq : (fun ω ↦ brownianShift B (dyadicTime T n) s ω) =
      (fun p : Ω × ℕ ↦ B ((p.2 : ℝ≥0) / 2 ^ n + s) p.1 - B ((p.2 : ℝ≥0) / 2 ^ n) p.1) ∘
        fun ω ↦ (ω, ⌈T ω * 2 ^ n⌉₊) := by
    funext ω
    simp only [Function.comp_apply, brownianShift, dyadicTime]
  rw [heq]
  exact hF.comp (measurable_id'.prodMk (measurable_ceil hT n))

/-- The natural filtration satisfies the independence hypothesis of the generic strong Markov
argument: Mathlib's weak Markov property `IsPreBrownianReal.indepFun_shift`. -/
private lemma indep_shift_natural (hm : ∀ t, Measurable (B t)) {μ : Measure Ω}
    (hB : IsPreBrownianReal B μ) (s : ℝ≥0) :
    Indep (MeasurableSpace.comap (fun ω v ↦ B (s + v) ω - B s ω) inferInstance)
      (Filtration.natural B (fun t ↦ (hm t).stronglyMeasurable) s) μ := by
  rw [Filtration.natural_eq_comap]
  exact (IndepFun_iff_Indep ..).1 (hB.indepFun_shift s)

/-- Strong Markov identity at a dyadically rounded stopping time. The rounded time has countably
many values, and at each value the future increments are independent of the past. -/
private lemma measure_inter_brownianShift_dyadicTime (hm : ∀ t, Measurable (B t))
    (μ : Measure Ω) (hB : IsPreBrownianReal B μ)
    (hindep : ∀ s, Indep (MeasurableSpace.comap (fun ω v ↦ B (s + v) ω - B s ω) inferInstance)
      (𝒢 s) μ)
    (hT : IsStoppingTime 𝒢 (fun ω ↦ (T ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hT.measurableSpace] A) (n : ℕ)
    {ι : Type*} [Fintype ι] (t : ι → ℝ≥0) {S : Set (ι → ℝ)} (hS : MeasurableSet S) :
    μ (A ∩ (fun ω i ↦ brownianShift B (dyadicTime T n) (t i) ω) ⁻¹' S) =
      μ A * μ ((fun ω i ↦ B (t i) ω) ⁻¹' S) := by
  let ℱ := 𝒢
  let K : Ω → ℕ := fun ω ↦ ⌈T ω * 2 ^ n⌉₊
  let q : ℕ → ℝ≥0 := fun k ↦ (k : ℝ≥0) / 2 ^ n
  have hσ := hT.dyadicCeilTime n
  have hcount := TauCeti.countable_range_dyadicCeilTime (fun ω ↦ (T ω : WithTop ℝ≥0)) n
  have hpast (k : ℕ) : MeasurableSet[ℱ (q k)] (A ∩ {ω | K ω = k}) := by
    rw [setOf_ceil_eq]
    refine (hσ.measurableSet_inter_eq_iff _ _).1 ?_
    exact (hT.measurableSpace_mono hσ (fun ω ↦ TauCeti.le_dyadicCeilTime n _) A hA).inter
      (hσ.measurableSet_eq_of_countable_range' hcount _)
  let shiftQ (k : ℕ) : Ω → ℝ≥0 → ℝ := fun ω s ↦ B (q k + s) ω - B (q k) ω
  have hshiftQ (k : ℕ) : Measurable (shiftQ k) :=
    Measurable.of_eval fun s ↦ (hm (q k + s)).sub (hm (q k))
  let G : Set (ℝ≥0 → ℝ) := {g | (fun i ↦ g (t i)) ∈ S}
  have hG : MeasurableSet G := (Measurable.of_eval fun i ↦ measurable_pi_apply (t i)) hS
  have hvec (k : ℕ) (ω : Ω) (hω : K ω = k) :
      (fun i ↦ brownianShift B (dyadicTime T n) (t i) ω) = fun i ↦ shiftQ k ω (t i) := by
    have h : dyadicTime T n ω = q k := by rw [← hω]; rfl
    funext i
    rw [brownianShift, h]
  have hsplit : A ∩ (fun ω i ↦ brownianShift B (dyadicTime T n) (t i) ω) ⁻¹' S =
      ⋃ k, (A ∩ {ω | K ω = k}) ∩ shiftQ k ⁻¹' G := by
    ext ω
    constructor
    · rintro ⟨hA, hS⟩
      rw [Set.mem_preimage, hvec (K ω) ω rfl] at hS
      exact Set.mem_iUnion.2 ⟨K ω, ⟨hA, rfl⟩, hS⟩
    · intro h
      obtain ⟨k, ⟨hA, hk⟩, hS⟩ := Set.mem_iUnion.1 h
      refine ⟨hA, ?_⟩
      rw [Set.mem_preimage, hvec k ω hk]
      exact hS
  have hmeasA (k : ℕ) : MeasurableSet (A ∩ {ω | K ω = k}) := ℱ.le _ _ (hpast k)
  have hterm (k : ℕ) : μ ((A ∩ {ω | K ω = k}) ∩ shiftQ k ⁻¹' G) =
      μ (A ∩ {ω | K ω = k}) * μ ((fun ω i ↦ B (t i) ω) ⁻¹' S) := by
    have hmul := (Indep_iff _ _ μ).1 (hindep (q k)) (shiftQ k ⁻¹' G) _ ⟨G, hG, rfl⟩ (hpast k)
    have hlaw : μ (shiftQ k ⁻¹' G) = μ ((fun ω i ↦ B (t i) ω) ⁻¹' S) := by
      have h : μ.map (fun ω i ↦ B (q k + t i) ω - B (q k) ω) = μ.map (fun ω i ↦ B (t i) ω) :=
        map_eval_eq_of_isPreBrownianReal (hB.shift (q k)) hB t
      calc μ (shiftQ k ⁻¹' G)
          = μ.map (fun ω i ↦ B (q k + t i) ω - B (q k) ω) S :=
            (Measure.map_apply (Measurable.of_eval fun i ↦
              (hm (q k + t i)).sub (hm (q k))) hS).symm
        _ = μ.map (fun ω i ↦ B (t i) ω) S := by rw [h]
        _ = _ := Measure.map_apply (Measurable.of_eval fun i ↦ hm (t i)) hS
    rw [Set.inter_comm, hmul, hlaw, mul_comm]
  have hdisj : Pairwise (Function.onFun Disjoint fun k ↦ (A ∩ {ω | K ω = k}) ∩ shiftQ k ⁻¹' G) :=
    fun j k hjk ↦ Set.disjoint_left.2 fun ω hj hk ↦ hjk (hj.1.2.symm.trans hk.1.2)
  have hdisjA : Pairwise (Function.onFun Disjoint fun k ↦ A ∩ {ω | K ω = k}) :=
    fun j k hjk ↦ Set.disjoint_left.2 fun ω hj hk ↦ hjk (hj.2.symm.trans hk.2)
  have hA' : A = ⋃ k, A ∩ {ω | K ω = k} := by
    rw [← Set.inter_iUnion, Set.iUnion_eq_univ_iff.2 fun ω ↦ ⟨K ω, rfl⟩, Set.inter_univ]
  rw [hsplit, measure_iUnion hdisj fun k ↦ (hmeasA k).inter ((hshiftQ k) hG)]
  simp only [hterm]
  rw [ENNReal.tsum_mul_right, ← measure_iUnion hdisjA hmeasA, ← hA']

/-- After a finite stopping time the increment vector, restricted to a stopping-time event,
has the law of the Brownian vector scaled by the event's probability. Dyadic rounding and path
continuity pass the countable-valued identity to the limit. -/
private lemma map_restrict_brownianShift (hm : ∀ t, Measurable (B t))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hB : IsBrownianReal B μ)
    (hindep : ∀ s, Indep (MeasurableSpace.comap (fun ω v ↦ B (s + v) ω - B s ω) inferInstance)
      (𝒢 s) μ)
    (hT : IsStoppingTime 𝒢 (fun ω ↦ (T ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hT.measurableSpace] A)
    {ι : Type*} [Fintype ι] (t : ι → ℝ≥0) :
    AEMeasurable (fun ω i ↦ brownianShift B T (t i) ω) μ ∧
      (μ.restrict A).map (fun ω i ↦ brownianShift B T (t i) ω) =
        μ A • μ.map (fun ω i ↦ B (t i) ω) := by
  let F : ℕ → Ω → ι → ℝ := fun n ω i ↦ brownianShift B (dyadicTime T n) (t i) ω
  let G : Ω → ι → ℝ := fun ω i ↦ brownianShift B T (t i) ω
  have hFm (n : ℕ) : Measurable (F n) :=
    Measurable.of_eval fun i ↦ measurable_brownianShift_dyadicTime hm hT n (t i)
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ F n ω) atTop (𝓝 (G ω)) := by
    filter_upwards [hB.cont] with ω hω
    refine tendsto_pi_nhds.2 fun i ↦ ?_
    exact ((hω.tendsto _).comp ((tendsto_dyadicTime T ω).add_const (t i))).sub
      ((hω.tendsto _).comp (tendsto_dyadicTime T ω))
  have hGm : AEMeasurable G μ :=
    aemeasurable_of_tendsto_metrizable_ae' (fun n ↦ (hFm n).aemeasurable) hlim
  have hBm : Measurable (fun ω i ↦ B (t i) ω) := Measurable.of_eval fun i ↦ hm (t i)
  have hFA (n : ℕ) : (μ.restrict A).map (F n) = μ A • μ.map (fun ω i ↦ B (t i) ω) := by
    ext S hS
    rw [Measure.map_apply (hFm n) hS, Measure.restrict_apply ((hFm n) hS), smul_apply,
      Measure.map_apply hBm hS, smul_eq_mul, Set.inter_comm]
    exact measure_inter_brownianShift_dyadicTime hm μ hB.toIsPreBrownianReal hindep hT hA n t hS
  have hGmA : AEMeasurable G (μ.restrict A) := hGm.mono_measure Measure.restrict_le_self
  have hGA : (μ.restrict A).map G = (μ.restrict A).map (F 0) := by
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun φ ↦ ?_
    have hφ := φ.continuous.aestronglyMeasurable (μ := (μ.restrict A).map G)
    rw [integral_map hGmA φ.continuous.aestronglyMeasurable,
      integral_map (hFm 0).aemeasurable φ.continuous.aestronglyMeasurable]
    have hconst (n : ℕ) : ∫ ω, φ (F n ω) ∂μ.restrict A = ∫ ω, φ (F 0 ω) ∂μ.restrict A := by
      rw [← integral_map (hFm n).aemeasurable φ.continuous.aestronglyMeasurable,
        ← integral_map (hFm 0).aemeasurable φ.continuous.aestronglyMeasurable, hFA n, hFA 0]
    have htend : Tendsto (fun n ↦ ∫ ω, φ (F n ω) ∂μ.restrict A) atTop
        (𝓝 (∫ ω, φ (G ω) ∂μ.restrict A)) :=
      tendsto_integral_of_dominated_convergence (fun _ ↦ ‖φ‖)
        (fun n ↦ (φ.continuous.measurable.comp (hFm n)).aestronglyMeasurable)
        (integrable_const _) (fun n ↦ ae_of_all _ fun ω ↦ φ.norm_coe_le_norm _)
        (ae_restrict_of_ae (hlim.mono fun ω hω ↦ (φ.continuous.tendsto _).comp hω))
    exact tendsto_nhds_unique htend (tendsto_const_nhds.congr fun n ↦ (hconst n).symm)
  exact ⟨hGm, hGA.trans (hFA 0)⟩

/-- **08.3**, filtration interface: let `𝒢` be a filtration relative to which the whole future
increment process of Brownian motion after each deterministic time `s` is independent of `𝒢 s`.
For a finite-valued `𝒢`-stopping time the shifted process is Brownian, and its
finite-dimensional laws are independent of the sigma-algebra at the stopping time. -/
theorem brownian_strongMarkov_of_indep {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (hB : IsBrownianReal B μ) (𝒢 : Filtration ℝ≥0 ‹_›)
    (hindep : ∀ s, Indep (MeasurableSpace.comap (fun ω v ↦ B (s + v) ω - B s ω) inferInstance)
      (𝒢 s) μ)
    (T : Ω → ℝ≥0) (hT : IsStoppingTime 𝒢 (fun ω ↦ (T ω : WithTop ℝ≥0))) :
    IsBrownianReal (brownianShift B T) μ ∧
      ∀ A : Set Ω, MeasurableSet[hT.measurableSpace] A →
      ∀ (n : ℕ) (t : Fin n → ℝ≥0) (S : Set (Fin n → ℝ)), MeasurableSet S →
        μ (A ∩ {ω | (fun i ↦ brownianShift B T (t i) ω) ∈ S}) =
          μ A * μ {ω | (fun i ↦ B (t i) ω) ∈ S} := by
  refine ⟨⟨⟨fun I ↦ ?_⟩, ?_⟩, fun A hA n t S hS ↦ ?_⟩
  · obtain ⟨hGm, hmap⟩ := map_restrict_brownianShift hm μ hB hindep hT
      (@MeasurableSet.univ _ hT.measurableSpace) (fun i : I ↦ (i : ℝ≥0))
    rw [Measure.restrict_univ, measure_univ, one_smul] at hmap
    exact ⟨hGm, hmap.trans (hB.hasLaw I).map_eq⟩
  · filter_upwards [hB.cont] with ω hω
    simp only [brownianShift]
    fun_prop
  · obtain ⟨hGm, hmap⟩ := map_restrict_brownianShift hm μ hB hindep hT hA t
    have h : (μ.restrict A).map (fun ω i ↦ brownianShift B T (t i) ω) S =
        (μ A • μ.map (fun ω i ↦ B (t i) ω)) S := by rw [hmap]
    rwa [Measure.map_apply_of_aemeasurable (hGm.mono_measure Measure.restrict_le_self) hS,
      Measure.restrict_apply' (hT.measurableSpace_le A hA), smul_apply,
      Measure.map_apply (Measurable.of_eval fun i ↦ hm (t i)) hS, smul_eq_mul,
      Set.inter_comm] at h

/-- **08.3**, raw-natural-filtration version: the shifted process is Brownian and its
finite-dimensional laws are independent of the sigma-algebra at the stopping time.
The completed right-continuous augmentation is `brownian_strongMarkov_augmented`. -/
theorem brownian_strongMarkov {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (hB : IsBrownianReal B μ) (T : Ω → ℝ≥0)
    (hT : IsStoppingTime (Filtration.natural B (fun t ↦ (hm t).stronglyMeasurable))
      (fun ω ↦ (T ω : WithTop ℝ≥0))) :
    IsBrownianReal (brownianShift B T) μ ∧
      ∀ A : Set Ω, MeasurableSet[hT.measurableSpace] A →
      ∀ (n : ℕ) (t : Fin n → ℝ≥0) (S : Set (Fin n → ℝ)), MeasurableSet S →
        μ (A ∩ {ω | (fun i ↦ brownianShift B T (t i) ω) ∈ S}) =
          μ A * μ {ω | (fun i ↦ B (t i) ω) ∈ S} :=
  brownian_strongMarkov_of_indep μ B hm hB _
    (indep_shift_natural hm hB.toIsPreBrownianReal) T hT

/-- The right-continuous natural filtration augmented by the ambient null events satisfies the
independence hypothesis of `brownian_strongMarkov_of_indep` (TauCeti's
`IsBrownianReal.indep_shift_rightCont_natural`, which uses path continuity). -/
private lemma indep_shift_augmented (hm : ∀ t, Measurable (B t)) {μ : Measure Ω}
    (hB : IsBrownianReal B μ) (s : ℝ≥0) :
    Indep (MeasurableSpace.comap (fun ω v ↦ B (s + v) ω - B s ω) inferInstance)
      ((Filtration.natural B (fun t ↦ (hm t).stronglyMeasurable)).rightCont.ambientNullAugmentation
        μ s) μ := by
  have h := (Indep_iff _ _ μ).1
    (hB.indep_shift_rightCont_natural (fun t ↦ (hm t).stronglyMeasurable) s)
  rw [Indep_iff]
  intro t₁ t₂ ht₁ ht₂
  obtain ⟨-, t₃, ht₃, h₂₃⟩ :=
    (Filtration.measurableSet_ambientNullAugmentation_iff _ μ s t₂).1 ht₂
  rw [measure_congr ((EventuallyEqSet.refl (ae μ) t₁).inter h₂₃), measure_congr h₂₃]
  exact h t₁ t₃ ht₁ ht₃

/-- **08.3**, completed right-continuous augmentation: let `𝒢` be the right-continuous natural
filtration of Brownian motion with all ambient-measurable null events adjoined. For an almost
surely finite `𝒢`-stopping time `T`, the shifted process `B (T + t) - B T` (with `T` replaced
by `0` on the null event `T = ∞`) is Brownian, and its finite-dimensional laws are independent
of the sigma-algebra at `T`. -/
theorem brownian_strongMarkov_augmented {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (hB : IsBrownianReal B μ) (T : Ω → WithTop ℝ≥0)
    (hT : IsStoppingTime ((Filtration.natural B
      (fun t ↦ (hm t).stronglyMeasurable)).rightCont.ambientNullAugmentation μ) T)
    (hfin : ∀ᵐ ω ∂μ, T ω ≠ ⊤) :
    IsBrownianReal (brownianShift B fun ω ↦ (T ω).untopD 0) μ ∧
      ∀ A : Set Ω, MeasurableSet[hT.measurableSpace] A →
      ∀ (n : ℕ) (t : Fin n → ℝ≥0) (S : Set (Fin n → ℝ)), MeasurableSet S →
        μ (A ∩ {ω | (fun i ↦ brownianShift B (fun ω ↦ (T ω).untopD 0) (t i) ω) ∈ S}) =
          μ A * μ {ω | (fun i ↦ B (t i) ω) ∈ S} := by
  let 𝒢 := (Filtration.natural B
    (fun t ↦ (hm t).stronglyMeasurable)).rightCont.ambientNullAugmentation μ
  let T' : Ω → ℝ≥0 := fun ω ↦ (T ω).untopD 0
  have htop : {ω | T ω = ⊤} = (⋃ k : ℕ, {ω | T ω ≤ ((k : ℝ≥0) : WithTop ℝ≥0)})ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    refine ⟨fun h k hk ↦ by simp [h] at hk, fun h ↦ ?_⟩
    by_contra hne
    obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hne
    obtain ⟨k, hk⟩ := exists_nat_ge x
    exact h k (hx ▸ WithTop.coe_le_coe.2 hk)
  have hNm : MeasurableSet {ω | T ω = ⊤} := by
    rw [htop]
    exact (MeasurableSet.iUnion fun k : ℕ ↦ 𝒢.le _ _ (hT (k : ℝ≥0))).compl
  have hN0 : μ {ω | T ω = ⊤} = 0 := by
    rw [ae_iff] at hfin
    simpa only [ne_eq, not_not] using hfin
  have hsplit (A : Set Ω) (i : ℝ≥0) : A ∩ {ω | (T' ω : WithTop ℝ≥0) ≤ i} =
      (A ∩ {ω | T ω ≤ i}) ∪ (A ∩ {ω | T ω = ⊤}) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq, T']
    by_cases h : T ω = ⊤
    · simp only [h, WithTop.untopD_top, WithTop.coe_le_coe, zero_le, top_le_iff,
        WithTop.coe_ne_top]
      tauto
    · obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 h
      simp only [← hx, WithTop.untopD_coe, WithTop.coe_ne_top, and_false, or_false]
  have hnull (A : Set Ω) (hA : MeasurableSet A) (i : ℝ≥0) :
      MeasurableSet[𝒢 i] (A ∩ {ω | T ω = ⊤}) :=
    Filtration.measurableSet_ambientNullAugmentation_of_null _ μ i (hA.inter hNm)
      (measure_mono_null Set.inter_subset_right hN0)
  have hT' : IsStoppingTime 𝒢 (fun ω ↦ (T' ω : WithTop ℝ≥0)) := by
    intro i
    have h := (MeasurableSet.univ.inter (hT i)).union (hnull Set.univ MeasurableSet.univ i)
    rwa [← hsplit Set.univ i, Set.univ_inter] at h
  have hA' (A : Set Ω) (hA : MeasurableSet[hT.measurableSpace] A) :
      MeasurableSet[hT'.measurableSpace] A := by
    refine ⟨hA.1, fun i ↦ ?_⟩
    rw [hsplit A i]
    exact (hA.2 i).union (hnull A (hT.measurableSpace_le A hA) i)
  obtain ⟨hlaw, hind⟩ := brownian_strongMarkov_of_indep μ B hm hB 𝒢
    (indep_shift_augmented hm hB) T' hT'
  exact ⟨hlaw, fun A hA ↦ hind A (hA' A hA)⟩

end CKMA
