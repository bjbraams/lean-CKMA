/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

import TauCeti.Analysis.BoundedVariation.Coarea
import TauCeti.Analysis.BoundedVariation.Compactness

/-!
# BV compactness and the coarea formula

Integrable scalar functions of bounded distributional variation, their size bounds,
and compactness for families supported in a common compact set. The coarea formula
expresses total variation through perimeters of superlevel sets, retaining infinite values.
Variation, perimeter and their lower semicontinuity are the objects of TauCeti's
`Analysis.BoundedVariation.TotalVariation` and `Perimeter` modules.
The coarea identity is `TauCeti.totalVariationOn_eq_lintegral_perimeter`.
Whole-space compactness uses
`TauCeti.totallyBounded_of_lintegral_le_of_totalVariationOn_le`,
and the variation bound on the limit is `TauCeti.totalVariationOn_le_liminf`.
Sources: GAPS 37.24 and 37.30.

## Main definitions

* `CKMA.IsBVFunctionOn`: integrable functions of finite total variation on an open set.
* `CKMA.bvSizeOn`: extended `L¹`-plus-variation gauge.

## Main results

* `CKMA.isBVFunctionOn_zero`: the zero function has bounded variation.
* `CKMA.bv_compactness_of_compact_support`: Rellich-type `L¹` compactness for BV functions
  with common compact support.
* `CKMA.bv_coarea`: Fleming–Rishel coarea formula for BV functions.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology TopologicalSpace Set
open scoped ENNReal

/-- Integrable functions of finite variation, using TauCeti's actual distributional variation. -/
@[expose]
def IsBVFunctionOn {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  IntegrableOn u Ω ∧ TauCeti.totalVariationOn volume Ω u < ∞

/-- The extended L1-plus-variation bound; no representative quotient or norm instance is assumed. -/
@[expose]
def bvSizeOn {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  eLpNorm u 1 (volume.restrict Ω) + TauCeti.totalVariationOn volume Ω u

/-- Zero is BV on every open set, including unbounded sets. -/
theorem isBVFunctionOn_zero {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin d))) :
    IsBVFunctionOn Ω (fun _ ↦ 0) := by
  constructor
  · exact integrableOn_zero
  · simp

/-- **37.24**, whole-space BV compactness for uniformly bounded families supported in a fixed
compact set. The bounded-Lipschitz-domain extension interface is a separate target. -/
theorem bv_compactness_of_compact_support {d : ℕ}
    (u : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hu : ∀ n, IsBVFunctionOn ⊤ (u n)) (K : Set (EuclideanSpace ℝ (Fin d)))
    (hK : IsCompact K) (hs : ∀ n, ∀ᵐ x ∂volume, x ∉ K → u n x = 0)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hb : ∀ n, bvSizeOn ⊤ (u n) ≤ C) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ v : EuclideanSpace ℝ (Fin d) → ℝ,
      IsBVFunctionOn ⊤ v ∧ (∀ᵐ x ∂volume, x ∉ K → v x = 0) ∧
      Tendsto (fun n ↦ eLpNorm (fun x ↦ u (r n) x - v x) 1 volume) atTop (𝓝 0) ∧
      TauCeti.totalVariationOn volume ⊤ v ≤
        liminf (fun n ↦ TauCeti.totalVariationOn volume ⊤ (u (r n))) atTop := by
  -- Representatives supported on `K` have the same `L¹` class and the same variation, so
  -- `TauCeti.totallyBounded_of_lintegral_le_of_totalVariationOn_le` applies on the whole space.
  let u' : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun n => K.indicator (u n)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hae (n : ℕ) : u n =ᵐ[volume] u' n := by
    filter_upwards [hs n] with x hx
    by_cases hxK : x ∈ K
    · simpa [u'] using (indicator_of_mem hxK (u n)).symm
    · simpa [u', indicator_of_notMem hxK] using hx hxK
  have hint (n : ℕ) : Integrable (u n) volume := by
    simpa [IntegrableOn, Opens.coe_top, Measure.restrict_univ] using (hu n).1
  have hint' (n : ℕ) : Integrable (u' n) volume := (hint n).congr (hae n)
  have hmem (n : ℕ) : MemLp (u' n) 1 volume := memLp_one_iff_integrable.mpr (hint' n)
  have hvar (n : ℕ) : TauCeti.totalVariationOn volume ⊤ (u n) ≤ C := by
    calc
      TauCeti.totalVariationOn volume ⊤ (u n) ≤ bvSizeOn ⊤ (u n) := by
        rw [bvSizeOn, Opens.coe_top, Measure.restrict_univ]
        exact le_add_self
      _ ≤ C := hb n
  have hvar' (n : ℕ) : TauCeti.totalVariationOn volume ⊤ (u' n) ≤ C := by
    rw [TauCeti.totalVariationOn_congr_ae (Ω := ⊤) (μ := volume) (u := u' n) (v := u n) ?_]
    · exact hvar n
    · simp only [Opens.coe_top, Measure.restrict_univ]
      exact (hae n).symm
  have hnorm (n : ℕ) : ∫⁻ x, ‖u' n x‖ₑ ∂volume ≤ C := by
    have hcongr : (fun x => ‖u' n x‖ₑ) =ᵐ[volume] fun x => ‖u n x‖ₑ := by
      filter_upwards [hae n] with x hx
      rw [hx]
    calc ∫⁻ x, ‖u' n x‖ₑ ∂volume
        = ∫⁻ x, ‖u n x‖ₑ ∂volume := lintegral_congr_ae hcongr
      _ = eLpNorm (u n) 1 volume :=
          (eLpNorm_one_eq_lintegral_enorm (hint n).aestronglyMeasurable).symm
      _ ≤ bvSizeOn ⊤ (u n) := by
          rw [bvSizeOn, Opens.coe_top, Measure.restrict_univ]
          exact le_self_add
      _ ≤ C := hb n
  let S : Set (Lp ℝ 1 volume) := {f | ∃ w ∈ range u', f =ᵐ[volume] w}
  have hTB : TotallyBounded S :=
    TauCeti.totallyBounded_of_lintegral_le_of_totalVariationOn_le
      (S := S) (L := K) (M := C) (B := C) hK.isBounded hC hC
      (fun f hf => by
        obtain ⟨w, hw, hfw⟩ := hf
        obtain ⟨n, rfl⟩ := hw
        filter_upwards [hfw] with x hx
        intro hxK
        rw [hx]
        exact indicator_of_notMem hxK (u n))
      (fun f hf => by
        obtain ⟨w, hw, hfw⟩ := hf
        obtain ⟨n, rfl⟩ := hw
        have hcongr : (fun x => ‖f x‖ₑ) =ᵐ[volume] fun x => ‖u' n x‖ₑ := by
          filter_upwards [hfw] with x hx
          rw [hx]
        calc
          ∫⁻ x, ‖f x‖ₑ ∂volume = ∫⁻ x, ‖u' n x‖ₑ ∂volume := lintegral_congr_ae hcongr
          _ ≤ C := hnorm n)
      (fun f hf => by
        obtain ⟨w, hw, hfw⟩ := hf
        obtain ⟨n, rfl⟩ := hw
        rw [TauCeti.totalVariationOn_congr_ae (Ω := ⊤) (μ := volume)
          (u := f) (v := u' n) ?_]
        · exact hvar' n
        · simp only [Opens.coe_top, Measure.restrict_univ]
          exact hfw)
  have hcompact : IsCompact (closure S) := hTB.closure.isCompact_of_isClosed isClosed_closure
  let x : ℕ → Lp ℝ 1 volume := fun n => (hmem n).toLp (u' n)
  have hx (n : ℕ) : x n ∈ closure S :=
    subset_closure ⟨u' n, mem_range_self n, (hmem n).coeFn_toLp⟩
  obtain ⟨g, -, r, hr, hlim⟩ := hcompact.tendsto_subseq hx
  let v : EuclideanSpace ℝ (Fin d) → ℝ := g
  have hlimLp : Tendsto (fun n => eLpNorm (⇑(x (r n)) - v) 1 volume) atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (x ∘ r) g).mp hlim
  have hL1 : Tendsto (fun n => eLpNorm (fun y => u (r n) y - v y) 1 volume) atTop (𝓝 0) := by
    refine hlimLp.congr fun n => eLpNorm_congr_ae ?_
    filter_upwards [(hmem (r n)).coeFn_toLp, (hae (r n)).symm] with y hy₁ hy₂
    rw [Pi.sub_apply]
    dsimp only [x]
    rw [hy₁, hy₂]
  have hzero (n : ℕ) : u' n =ᵐ[volume.restrict Kᶜ] 0 :=
    ae_restrict_of_forall_mem hKm.compl fun y hy => indicator_of_notMem hy (u n)
  have hle (n : ℕ) :
      eLpNorm v 1 (volume.restrict Kᶜ) ≤ eLpNorm (u' (r n) - v) 1 volume := by
    have hcancel : v = v - u' (r n) + u' (r n) := by
      ext y
      simp only [Pi.add_apply, Pi.sub_apply, sub_add_cancel]
    calc
      eLpNorm v 1 (volume.restrict Kᶜ)
          = eLpNorm (v - u' (r n) + u' (r n)) 1 (volume.restrict Kᶜ) :=
          congrArg (fun f => eLpNorm f 1 (volume.restrict Kᶜ)) hcancel
      _ ≤ eLpNorm (v - u' (r n)) 1 (volume.restrict Kᶜ) +
            eLpNorm (u' (r n)) 1 (volume.restrict Kᶜ) :=
          eLpNorm_add_le (μ := volume.restrict Kᶜ) le_rfl
      _ = eLpNorm (v - u' (r n)) 1 (volume.restrict Kᶜ) := by
          rw [eLpNorm_eq_zero_of_ae_zero (hzero (r n)), add_zero]
      _ = eLpNorm (u' (r n) - v) 1 (volume.restrict Kᶜ) := by rw [eLpNorm_sub_comm]
      _ ≤ eLpNorm (u' (r n) - v) 1 volume :=
          eLpNorm_mono_measure _ Measure.restrict_le_self
  have hL1' : Tendsto (fun n => eLpNorm (u' (r n) - v) 1 volume) atTop (𝓝 0) := by
    refine hL1.congr fun n => eLpNorm_congr_ae ?_
    filter_upwards [(hae (r n)).symm] with y hy
    rw [Pi.sub_apply, ← hy]
  have hvK : ∀ᵐ y ∂volume, y ∉ K → v y = 0 := by
    have hnorm0 : eLpNorm v 1 (volume.restrict Kᶜ) = 0 :=
      le_antisymm (ge_of_tendsto' hL1' hle) zero_le
    simp only [← mem_compl_iff]
    rw [← ae_restrict_iff' hKm.compl]
    exact (eLpNorm_eq_zero_iff (μ := volume.restrict Kᶜ) one_ne_zero).mp hnorm0
  have hvint : Integrable v volume := memLp_one_iff_integrable.mp (Lp.memLp g)
  have hglob : Tendsto (fun n => ∫⁻ y, ‖u (r n) y - v y‖ₑ ∂volume) atTop (𝓝 0) := by
    refine hL1.congr fun n => ?_
    exact eLpNorm_one_eq_lintegral_enorm ((hint (r n)).sub' hvint).aestronglyMeasurable
  have hloc (L : Set (EuclideanSpace ℝ (Fin d))) (_ : IsCompact L) :
      Tendsto (fun n => ∫⁻ y in L, ‖u (r n) y - v y‖ₑ ∂volume) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hglob
      (fun _ => zero_le) fun n => setLIntegral_le_lintegral L _
  have hvOn : IntegrableOn v (⊤ : Opens (EuclideanSpace ℝ (Fin d))) volume := by
    rw [IntegrableOn, Opens.coe_top, Measure.restrict_univ]
    exact hvint
  have hlsc := TauCeti.totalVariationOn_le_liminf (μ := volume) (Ω := ⊤)
    (u := fun n => u (r n)) (u₀ := v) (l := atTop)
    (Eventually.of_forall fun n => (hu (r n)).1.locallyIntegrableOn) hvOn.locallyIntegrableOn
    fun L hL _ => hloc L hL
  refine ⟨r, hr, v, ?_, hvK, hL1, hlsc⟩
  exact ⟨hvOn, hlsc.trans_lt <| (liminf_le_of_frequently_le'
    (Eventually.of_forall fun n => hvar (r n)).frequently).trans_lt (lt_top_iff_ne_top.mpr hC)⟩

/-- **37.30**: the full scalar BV coarea identity, retaining possibly infinite perimeters. -/
theorem bv_coarea {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin d)))
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hm : Measurable u) (hu : IsBVFunctionOn Ω u) :
    TauCeti.totalVariationOn volume Ω u =
      ∫⁻ t : ℝ, TauCeti.perimeter volume Ω {x | t < u x} := by
  -- Measurability is the strong-measurability half of integrability on `Ω`.
  -- `TauCeti.totalVariationOn_eq_lintegral_perimeter` retains infinite level perimeters.
  have hint : IntegrableOn u Ω volume := ⟨hm.aestronglyMeasurable, hu.1.hasFiniteIntegral⟩
  exact TauCeti.totalVariationOn_eq_lintegral_perimeter hint.locallyIntegrableOn

end CKMA
