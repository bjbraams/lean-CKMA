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
public import TauCeti.Probability.Process.Filtration.AmbientNullAugmentation

import Mathlib.MeasureTheory.Constructions.KolmogorovExtension
import TauCeti.Probability.BrownianMotion.StrongMarkov

/-!
# Brownian laws, strong Markov property and reflection (08.1, 08.3, 08.4)

The canonical law is a probability measure on `C(ℝ≥0, ℝ)` with its compact-open Borel
sigma-algebra. It is built from Mathlib's Kolmogorov extension `projectiveLimit` of the Brownian
finite-dimensional laws and the continuous modification of `BrownianTheory.HolderPath`, whose
statement `CKMA.Brownian.exists_continuous_holder_modification` also gives every local Hölder
exponent below one half.

`brownianShift B T` is the increment process `t ↦ B (T + t) - B T` after a finite-valued random
time. It agrees with TauCeti's restarted process
`fun t ω ↦ stoppedValue B (fun ω' ↦ T ω' + t) ω - stoppedValue B T ω`
(`brownianShift_eq_stoppedValue_sub`). The strong Markov property is stated for the natural
filtration and for the right-continuous natural filtration augmented by the ambient null events,
where almost surely finite stopping times are allowed; in both cases the shifted process is
Brownian and its whole path is independent of the sigma-algebra at the stopping time. Both are
specializations of TauCeti's strong Markov theorems
(`TauCeti.Probability.BrownianMotion.StrongMarkov`). The reflection principle uses a strictly
positive level and includes time zero.

## Main definitions

* `CKMA.brownianShift`: shifted process after a finite-valued random time.

## Main results

* `CKMA.exists_brownianMeasure`: existence of Wiener measure on `C(ℝ≥0, ℝ)` (**08.1**).
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
  have hP := BrownianReal.isProjectiveMeasureFamily_projectiveFamily
  have : ∀ I : Finset ℝ≥0, IsProbabilityMeasure (BrownianReal.projectiveFamily I) :=
    fun _ ↦ inferInstance
  have hlim := isProjectiveLimit_projectiveLimit hP
  exact ⟨wienerOfPreBrownian (coordinatePreBrownian_isPreBrownian _ hlim),
    isProbabilityMeasure_wienerOfPreBrownian _, wienerOfPreBrownian_isBrownian _⟩

/-- The shifted process after a finite-valued random time. -/
@[expose]
def brownianShift {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : ℝ := B (T ω + t) ω - B (T ω) ω

/-- Defining equation of `brownianShift`. -/
theorem brownianShift_apply {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    brownianShift B T t ω = B (T ω + t) ω - B (T ω) ω := rfl

/-- After the time `0` the shifted process is the increment `B t - B 0`. -/
@[simp]
theorem brownianShift_zero_left {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    brownianShift B (fun _ ↦ 0) t ω = B t ω - B 0 ω := by
  simp [brownianShift]

/-- At elapsed time `0` the shifted process vanishes. -/
@[simp]
theorem brownianShift_zero_right {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (ω : Ω) :
    brownianShift B T 0 ω = 0 := by
  simp [brownianShift]

/-- `brownianShift` is TauCeti's restarted increment process at the finite random time `T`. -/
theorem brownianShift_eq_stoppedValue_sub {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) :
    brownianShift B T = fun (t : ℝ≥0) ω ↦
      stoppedValue B (fun ω' ↦ (T ω' : WithTop ℝ≥0) + t) ω -
        stoppedValue B (fun ω' ↦ (T ω' : WithTop ℝ≥0)) ω := by
  funext t ω
  simp only [brownianShift, stoppedValue, ← WithTop.coe_add, WithTop.untopA, WithTop.untopD_coe]

/-- **08.3**, natural filtration: for a finite-valued stopping time `T` of the natural filtration
of a Brownian motion, the shifted process `brownianShift B T` is Brownian and its whole path is
independent of the sigma-algebra at `T`. -/
theorem brownian_strongMarkov {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (hB : IsBrownianReal B μ) (T : Ω → ℝ≥0)
    (hT : IsStoppingTime (Filtration.natural B (fun t ↦ (hm t).stronglyMeasurable))
      (fun ω ↦ (T ω : WithTop ℝ≥0))) :
    IsBrownianReal (brownianShift B T) μ ∧
      Indep (MeasurableSpace.comap (fun ω t ↦ brownianShift B T t ω) inferInstance)
        hT.measurableSpace μ := by
  have hfin : ∀ᵐ ω ∂μ, (T ω : WithTop ℝ≥0) ≠ ⊤ := ae_of_all _ fun _ ↦ WithTop.coe_ne_top
  rw [brownianShift_eq_stoppedValue_sub]
  exact ⟨hB.stoppedValue_shift_natural _ hT hfin, hB.indep_stoppedValue_shift_natural _ hT hfin⟩

/-- The two shifted processes at an almost surely finite time agree almost surely as paths. -/
private lemma ae_eq_brownianShift_untopD {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (B : ℝ≥0 → Ω → ℝ) {T : Ω → WithTop ℝ≥0} (hfin : ∀ᵐ ω ∂μ, T ω ≠ ⊤) :
    ∀ᵐ ω ∂μ, (fun t ↦ brownianShift B (fun ω ↦ (T ω).untopD 0) t ω) =
      fun (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ T ω' + t) ω - stoppedValue B T ω := by
  filter_upwards [hfin] with ω hω
  obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hω
  funext t
  simp only [brownianShift, stoppedValue, ← hx, ← WithTop.coe_add, WithTop.untopA,
    WithTop.untopD_coe]

/-- **08.3**, completed right-continuous augmentation: let `𝒢` be the right-continuous natural
filtration of Brownian motion with all ambient-measurable null events adjoined. For an almost
surely finite `𝒢`-stopping time `T`, the shifted process `B (T + t) - B T` (with `T` replaced
by `0` on the null event `T = ∞`) is Brownian, and its whole path is independent of the
sigma-algebra at `T`. -/
theorem brownian_strongMarkov_augmented {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (hB : IsBrownianReal B μ) (T : Ω → WithTop ℝ≥0)
    (hT : IsStoppingTime ((Filtration.natural B
      (fun t ↦ (hm t).stronglyMeasurable)).rightCont.ambientNullAugmentation μ) T)
    (hfin : ∀ᵐ ω ∂μ, T ω ≠ ⊤) :
    IsBrownianReal (brownianShift B fun ω ↦ (T ω).untopD 0) μ ∧
      Indep (MeasurableSpace.comap
          (fun ω t ↦ brownianShift B (fun ω ↦ (T ω).untopD 0) t ω) inferInstance)
        hT.measurableSpace μ := by
  have hF := ((hB.isFilteredPreBrownianReal_natural fun t ↦ (hm t).stronglyMeasurable).rightCont
    fun s ↦ hB.cont.mono fun ω hω ↦ hω.continuousAt.continuousWithinAt).ambientNullAugmentation
  have hrc : ∀ᵐ ω ∂μ, IsRightContinuous (B · ω) := hB.cont.mono fun _ hω ↦ hω.isRightContinuous
  have hae := ae_eq_brownianShift_untopD (μ := μ) B hfin
  have hlaw := hF.isBrownianReal_stoppedValue_shift hB.cont hT hfin
  have hind := hF.indep_stoppedValue_shift hrc hT hfin
  refine ⟨⟨hlaw.toIsPreBrownianReal.congr fun t ↦ ?_, ?_⟩, ?_⟩
  · filter_upwards [hae] with ω hω using (congrFun hω t).symm
  · filter_upwards [hae, hlaw.cont] with ω hω hc
    rwa [hω]
  · rw [Indep_iff] at hind ⊢
    rintro _ s₂ ⟨S, hS, rfl⟩ hs₂
    have hpre : (fun ω t ↦ brownianShift B (fun ω ↦ (T ω).untopD 0) t ω) ⁻¹' S =ᵐ[μ]
        (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ T ω' + t) ω - stoppedValue B T ω) ⁻¹' S := by
      filter_upwards [hae] with ω hω
      simp only [Set.mem_preimage, hω]
    rw [measure_congr (hpre.inter (EventuallyEqSet.refl (ae μ) s₂)), measure_congr hpre]
    exact hind _ _ ⟨S, hS, rfl⟩ hs₂

end CKMA
