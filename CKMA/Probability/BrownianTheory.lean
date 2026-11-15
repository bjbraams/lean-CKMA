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
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import TauCeti.Probability.Process.StoppingApproximation

/-!
# Brownian laws, modifications, strong Markov and reflection (08.1, 08.3, 08.4)

The canonical law is a probability measure on `C(ℝ≥0, ℝ)` with its compact-open Borel
sigma-algebra. Its coordinate process has continuous paths by construction. A separate
modification theorem starts from an arbitrary pre-Brownian process and gives every
local Hölder exponent below one half.

`brownianShift` describes increments after a finite-valued stopping time. The strong
Markov interface uses the raw natural filtration and finite-dimensional independence;
the reflection principle uses a strictly positive level and includes time zero.

The strong Markov property is proved by rounding the stopping time up to dyadic grids
(TauCeti's `dyadicCeilTime`). At each grid value Mathlib's weak Markov property
`IsPreBrownianReal.indepFun_shift` applies. Path continuity and dominated convergence then pass
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
* `CKMA.brownian_strongMarkov`: strong Markov property for Brownian motion (**08.3**).
* `CKMA.brownian_reflection`: reflection principle for Brownian motion (**08.4**,
  in `BrownianTheory.Reflection.Bound`).
-/

@[expose] public section

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

variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
  {T : Ω → ℝ≥0}

/-- The dyadic index of a stopping time is measurable. -/
private lemma measurable_ceil
    (hT : IsStoppingTime (Filtration.natural B (fun t ↦ (hm t).stronglyMeasurable))
      (fun ω ↦ (T ω : WithTop ℝ≥0))) (n : ℕ) :
    Measurable (fun ω ↦ ⌈T ω * 2 ^ n⌉₊) := by
  refine measurable_to_countable' fun k ↦ ?_
  rw [show (fun ω ↦ ⌈T ω * 2 ^ n⌉₊) ⁻¹' {k} = {ω | ⌈T ω * 2 ^ n⌉₊ = k} from rfl,
    setOf_ceil_eq]
  exact Filtration.le _ _ _ ((hT.dyadicCeilTime n).measurableSet_eq_of_countable_range
    (TauCeti.countable_range_dyadicCeilTime _ n) _)

/-- Brownian increments after a dyadically rounded stopping time are measurable. -/
private lemma measurable_brownianShift_dyadicTime
    (hT : IsStoppingTime (Filtration.natural B (fun t ↦ (hm t).stronglyMeasurable))
      (fun ω ↦ (T ω : WithTop ℝ≥0))) (n : ℕ) (s : ℝ≥0) :
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
  exact hF.comp (measurable_id'.prodMk (measurable_ceil hm hT n))

/-- Strong Markov identity at a dyadically rounded stopping time. The rounded time has countably
many values, and at each value the weak Markov property applies. -/
private lemma measure_inter_brownianShift_dyadicTime (μ : Measure Ω)
    (hB : IsPreBrownianReal B μ)
    (hT : IsStoppingTime (Filtration.natural B (fun t ↦ (hm t).stronglyMeasurable))
      (fun ω ↦ (T ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hT.measurableSpace] A) (n : ℕ)
    {ι : Type*} [Fintype ι] (t : ι → ℝ≥0) {S : Set (ι → ℝ)} (hS : MeasurableSet S) :
    μ (A ∩ (fun ω i ↦ brownianShift B (dyadicTime T n) (t i) ω) ⁻¹' S) =
      μ A * μ ((fun ω i ↦ B (t i) ω) ⁻¹' S) := by
  let ℱ := Filtration.natural B (fun t ↦ (hm t).stronglyMeasurable)
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
    have hcomap : MeasurableSet[MeasurableSpace.comap
        (fun ω (j : Set.Iic (q k)) ↦ B j ω) inferInstance] (A ∩ {ω | K ω = k}) :=
      Filtration.natural_eq_comap B (fun t ↦ (hm t).stronglyMeasurable) (q k) ▸ hpast k
    obtain ⟨s', hs', hpre⟩ := MeasurableSpace.measurableSet_comap.1 hcomap
    have hmul := (hB.indepFun_shift (q k)).measure_inter_preimage_eq_mul G s' hG hs'
    have hlaw : μ (shiftQ k ⁻¹' G) = μ ((fun ω i ↦ B (t i) ω) ⁻¹' S) := by
      have h : μ.map (fun ω i ↦ B (q k + t i) ω - B (q k) ω) = μ.map (fun ω i ↦ B (t i) ω) :=
        map_eval_eq_of_isPreBrownianReal (hB.shift (q k)) hB t
      calc μ (shiftQ k ⁻¹' G)
          = μ.map (fun ω i ↦ B (q k + t i) ω - B (q k) ω) S :=
            (Measure.map_apply (Measurable.of_eval fun i ↦
              (hm (q k + t i)).sub (hm (q k))) hS).symm
        _ = μ.map (fun ω i ↦ B (t i) ω) S := by rw [h]
        _ = _ := Measure.map_apply (Measurable.of_eval fun i ↦ hm (t i)) hS
    calc μ ((A ∩ {ω | K ω = k}) ∩ shiftQ k ⁻¹' G)
        = μ (shiftQ k ⁻¹' G ∩ (fun ω (j : Set.Iic (q k)) ↦ B j ω) ⁻¹' s') := by
          rw [Set.inter_comm (A ∩ _), hpre]
      _ = μ (shiftQ k ⁻¹' G) * μ ((fun ω (j : Set.Iic (q k)) ↦ B j ω) ⁻¹' s') := hmul
      _ = _ := by rw [mul_comm, hpre, hlaw]
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
private lemma map_restrict_brownianShift (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hB : IsBrownianReal B μ)
    (hT : IsStoppingTime (Filtration.natural B (fun t ↦ (hm t).stronglyMeasurable))
      (fun ω ↦ (T ω : WithTop ℝ≥0)))
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
    exact measure_inter_brownianShift_dyadicTime hm μ hB.toIsPreBrownianReal hT hA n t hS
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

/-- **08.3**, raw-natural-filtration version: the shifted process is Brownian and its
finite-dimensional laws are independent of the sigma-algebra at the stopping time.
The completed right-continuous augmentation is a separate interface. -/
theorem brownian_strongMarkov {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (hB : IsBrownianReal B μ) (T : Ω → ℝ≥0)
    (hT : IsStoppingTime (Filtration.natural B (fun t ↦ (hm t).stronglyMeasurable))
      (fun ω ↦ (T ω : WithTop ℝ≥0))) :
    IsBrownianReal (brownianShift B T) μ ∧
      ∀ A : Set Ω, MeasurableSet[hT.measurableSpace] A →
      ∀ (n : ℕ) (t : Fin n → ℝ≥0) (S : Set (Fin n → ℝ)), MeasurableSet S →
        μ (A ∩ {ω | (fun i ↦ brownianShift B T (t i) ω) ∈ S}) =
          μ A * μ {ω | (fun i ↦ B (t i) ω) ∈ S} := by
  refine ⟨⟨⟨fun I ↦ ?_⟩, ?_⟩, fun A hA n t S hS ↦ ?_⟩
  · obtain ⟨hGm, hmap⟩ := map_restrict_brownianShift hm μ hB hT
      (@MeasurableSet.univ _ hT.measurableSpace) (fun i : I ↦ (i : ℝ≥0))
    rw [Measure.restrict_univ, measure_univ, one_smul] at hmap
    exact ⟨hGm, hmap.trans (hB.hasLaw I).map_eq⟩
  · filter_upwards [hB.cont] with ω hω
    simp only [brownianShift]
    fun_prop
  · obtain ⟨hGm, hmap⟩ := map_restrict_brownianShift hm μ hB hT hA t
    have h : (μ.restrict A).map (fun ω i ↦ brownianShift B T (t i) ω) S =
        (μ A • μ.map (fun ω i ↦ B (t i) ω)) S := by rw [hmap]
    rwa [Measure.map_apply_of_aemeasurable (hGm.mono_measure Measure.restrict_le_self) hS,
      Measure.restrict_apply' (hT.measurableSpace_le A hA), smul_apply,
      Measure.map_apply (Measurable.of_eval fun i ↦ hm (t i)) hS, smul_eq_mul,
      Set.inter_comm] at h

end CKMA
