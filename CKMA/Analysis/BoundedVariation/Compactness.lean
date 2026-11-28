/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Space

import TauCeti.Analysis.BoundedVariation.Compactness

/-!
# BV compactness for families with common compact support

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`. A
sequence of integrable functions `E → ℝ` that vanish almost everywhere off a common compact set
and are bounded in `L¹(μ)` and in total variation has a subsequence converging in `L¹(μ)` to a
BV function that vanishes almost everywhere off the same set, and whose total variation is at
most the `liminf` of the total variations along the subsequence.

The space of BV functions is TauCeti's `TauCeti.MemBV`, the total variation is
`TauCeti.totalVariationOn`, total boundedness is
`TauCeti.totallyBounded_of_lintegral_le_of_totalVariationOn_le` and lower semicontinuity of the
variation is `TauCeti.totalVariationOn_le_liminf`. The coarea formula (GAPS 37.30) is TauCeti's
`TauCeti.totalVariationOn_eq_lintegral_perimeter`, for every function locally integrable on the
domain, with possibly infinite perimeters.

Sources: GAPS 37.24 and 37.30.

## Main results

* `CKMA.ae_eq_zero_of_notMem_of_tendsto_eLpNorm_sub`: an `L¹` limit of functions vanishing
  almost everywhere off a measurable set vanishes almost everywhere off that set.
* `CKMA.bv_compactness_of_compact_support`: Rellich-type `L¹` compactness for BV functions
  with common compact support.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology TopologicalSpace Set
open scoped ENNReal

/-- An `L¹` limit of functions vanishing almost everywhere off a measurable set `K` vanishes
almost everywhere off `K`. -/
theorem ae_eq_zero_of_notMem_of_tendsto_eLpNorm_sub {X F ι : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] {μ : Measure X} {l : Filter ι} [l.NeBot] {K : Set X}
    (hK : MeasurableSet K) {f : ι → X → F} {v : X → F}
    (hf : ∀ i, ∀ᵐ x ∂μ, x ∉ K → f i x = 0)
    (hlim : Tendsto (fun i ↦ eLpNorm (f i - v) 1 μ) l (𝓝 0)) :
    ∀ᵐ x ∂μ, x ∉ K → v x = 0 := by
  have hle (i : ι) : eLpNorm v 1 (μ.restrict Kᶜ) ≤ eLpNorm (f i - v) 1 μ := by
    have hfi : f i =ᵐ[μ.restrict Kᶜ] 0 := (ae_restrict_iff' hK.compl).mpr (hf i)
    have hv : v =ᵐ[μ.restrict Kᶜ] -(f i - v) := by
      filter_upwards [hfi] with x hx
      simp [hx]
    rw [eLpNorm_congr_ae hv, eLpNorm_neg]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have h0 : eLpNorm v 1 (μ.restrict Kᶜ) = 0 :=
    le_antisymm (ge_of_tendsto' hlim hle) zero_le
  exact (ae_restrict_iff' hK.compl).mp ((eLpNorm_eq_zero_iff (μ := μ.restrict Kᶜ)
    one_ne_zero).mp h0)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] {μ : Measure E}

/-- Total variation on the whole space depends only on the almost-everywhere class. -/
private lemma totalVariationOn_top_congr_ae {f g : E → ℝ} (h : f =ᵐ[μ] g) :
    TauCeti.totalVariationOn μ ⊤ f = TauCeti.totalVariationOn μ ⊤ g :=
  TauCeti.totalVariationOn_congr_ae (by rwa [Opens.coe_top, Measure.restrict_univ])

/-- **37.24**, whole-space BV compactness: integrable functions vanishing almost everywhere off
a common compact set, with uniform bounds `M` in `L¹(μ)` and `B` in total variation, have a
subsequence converging in `L¹(μ)` to a BV function vanishing almost everywhere off the same set,
whose total variation is at most the `liminf` along the subsequence. -/
theorem bv_compactness_of_compact_support [BorelSpace E] [μ.IsAddHaarMeasure] (u : ℕ → E → ℝ)
    (hu : ∀ n, Integrable (u n) μ) {K : Set E} (hK : IsCompact K)
    (hs : ∀ n, ∀ᵐ x ∂μ, x ∉ K → u n x = 0) {M B : ℝ≥0∞} (hM : M ≠ ∞) (hB : B ≠ ∞)
    (hnorm : ∀ n, eLpNorm (u n) 1 μ ≤ M)
    (hvar : ∀ n, TauCeti.totalVariationOn μ ⊤ (u n) ≤ B) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ v : E → ℝ,
      TauCeti.MemBV μ ⊤ v ∧ (∀ᵐ x ∂μ, x ∉ K → v x = 0) ∧
      Tendsto (fun n ↦ eLpNorm (u (r n) - v) 1 μ) atTop (𝓝 0) ∧
      TauCeti.totalVariationOn μ ⊤ v ≤
        liminf (fun n ↦ TauCeti.totalVariationOn μ ⊤ (u (r n))) atTop := by
  let x : ℕ → Lp ℝ 1 μ := fun n ↦ (hu n).toL1 (u n)
  have hx (n : ℕ) : ⇑(x n) =ᵐ[μ] u n := (hu n).coeFn_toL1
  have hTB : TotallyBounded (range x) := by
    refine TauCeti.totallyBounded_of_lintegral_le_of_totalVariationOn_le hK.isBounded hM hB
      ?_ ?_ ?_ <;> rintro _ ⟨n, rfl⟩
    · filter_upwards [hx n, hs n] with y hy hsy hyK
      rw [hy, hsy hyK]
    · rw [lintegral_congr_ae (by filter_upwards [hx n] with y hy; rw [hy]),
        ← eLpNorm_one_eq_lintegral_eNorm (hu n).aestronglyMeasurable]
      exact hnorm n
    · rw [totalVariationOn_top_congr_ae (hx n)]
      exact hvar n
  obtain ⟨g, -, r, hr, hlim⟩ := (hTB.closure.isCompact_of_isClosed isClosed_closure)
    |>.tendsto_subseq fun n ↦ subset_closure (mem_range_self n)
  have hL1 : Tendsto (fun n ↦ eLpNorm (u (r n) - ⇑g) 1 μ) atTop (𝓝 0) := by
    refine ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' (x ∘ r) g).mp hlim).congr fun n ↦ ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [hx (r n)] with y hy
    simp [hy]
  have hgint : Integrable (⇑g) μ := L1.integrable_coeFn g
  have hglob : Tendsto (fun n ↦ ∫⁻ y, ‖u (r n) y - g y‖ₑ ∂μ) atTop (𝓝 0) :=
    hL1.congr fun n ↦ eLpNorm_one_eq_lintegral_eNorm ((hu (r n)).sub hgint).aestronglyMeasurable
  have hgOn : IntegrableOn (⇑g) (⊤ : Opens E) μ := by
    rwa [IntegrableOn, Opens.coe_top, Measure.restrict_univ]
  have hlsc := TauCeti.totalVariationOn_le_liminf (μ := μ) (Ω := ⊤)
    (u := fun n ↦ u (r n)) (u₀ := g) (l := atTop)
    (Eventually.of_forall fun n ↦ (hu (r n)).integrableOn.locallyIntegrableOn)
    hgOn.locallyIntegrableOn fun L _ _ ↦ tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hglob (fun _ ↦ zero_le) fun n ↦ setLIntegral_le_lintegral L _
  refine ⟨r, hr, g, TauCeti.memBV_iff.mpr ⟨hgOn, ?_⟩,
    ae_eq_zero_of_notMem_of_tendsto_eLpNorm_sub hK.isClosed.measurableSet
      (fun n ↦ hs (r n)) hL1, hL1, hlsc⟩
  exact hlsc.trans_lt <| (liminf_le_of_frequently_le'
    (Eventually.of_forall fun n ↦ hvar (r n)).frequently).trans_lt (lt_top_iff_ne_top.mpr hB)

end CKMA
