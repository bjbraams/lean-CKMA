/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import TauCeti.GroupTheory.Amenable.LocallyCompact

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Algebra.Group.Basic
import TauCeti.GroupTheory.Amenable.Abelian
import TauCeti.MeasureTheory.Function.Lp.One
import TauCeti.MeasureTheory.Function.Lp.Restriction

/-!
# Invariant means on Haar L∞ spaces

A positive normalized continuous linear functional on `L∞(G, μ)` is left invariant when
translated representatives agree almost everywhere (`CKMA.IsHaarInvariantMean`). For a regular
Haar measure on a locally compact group, the existence of such a mean is TauCeti's amenability
`TauCeti.Amenable G` (`CKMA.isHaarAmenable_iff_amenable`, from
`TauCeti.amenable_iff_exists_lpTop_invariant_of_regular`). Closed subgroups of amenable locally
compact groups are amenable (**28.58**), stated with TauCeti's class.

The compact and abelian cases hold for every Haar measure, without a regularity assumption. On a
compact group the normalized Bochner integral is an invariant mean: left invariance is Mathlib's
`MeasureTheory.map_mul_left_eq_self` together with `Topology.IsClosedEmbedding.integral_map`, so
the argument needs no second-countable `MeasurableMul` instance. On a locally compact abelian
group, TauCeti's amenability of the underlying discrete group (`TauCeti.Amenable.of_commGroup`)
averages the translates of the normalized integral over a compact neighbourhood, using TauCeti's
`Set.setIntegralLp` and its continuity theorem for positive functionals on real `L∞`
(`PositiveLinearMap.continuous_lpTop`). In TauCeti's class language these two cases are the
instances `TauCeti.Amenable.of_compactSpace` and `TauCeti.Amenable.of_commGroup`.

Source: GAPS 28.58.

## Main definitions

* `CKMA.IsHaarInvariantMean`: positive normalized left-invariant continuous linear functional on
  `Lp ℝ ∞ μ`.
* `CKMA.IsHaarAmenable`: existence of a left-invariant mean on `Lp ℝ ∞ μ`.

## Main results

* `CKMA.isHaarAmenable_iff_amenable`: for a regular Haar measure, `IsHaarAmenable μ` is
  TauCeti's `Amenable G`.
* `CKMA.isHaarAmenable_of_compact`: compact groups have invariant means on `L∞` of every Haar
  measure.
* `CKMA.isHaarAmenable_of_commutative`: so do locally compact abelian groups.
* `CKMA.amenable_of_isClosed` (**28.58**): closed subgroups of amenable locally compact groups are
  amenable.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped ENNReal BoundedContinuousFunction

section Group

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]

/-- A positive normalized left-invariant bounded functional on Haar L-infinity.
Translation is specified by a.e. representative equality, so no chosen representative is shifted
as if pointwise equality were intrinsic to the L-infinity class. -/
@[expose]
def IsHaarInvariantMean (μ : Measure G) (m : Lp ℝ ∞ μ →L[ℝ] ℝ) : Prop :=
  (∀ f : Lp ℝ ∞ μ, (∀ᵐ x ∂μ, 0 ≤ f x) → 0 ≤ m f) ∧
    (∀ f : Lp ℝ ∞ μ, (∀ᵐ x ∂μ, f x = 1) → m f = 1) ∧
    ∀ (g : G) (f h : Lp ℝ ∞ μ), (∀ᵐ x ∂μ, h x = f (g⁻¹ * x)) → m h = m f

/-- Amenability in the invariant-mean model on the chosen Haar space. -/
@[expose]
def IsHaarAmenable (μ : Measure G) : Prop := ∃ m, IsHaarInvariantMean μ m

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] in
/-- Unfolding `IsHaarInvariantMean`. -/
theorem isHaarInvariantMean_iff {μ : Measure G} {m : Lp ℝ ∞ μ →L[ℝ] ℝ} :
    IsHaarInvariantMean μ m ↔
      (∀ f : Lp ℝ ∞ μ, (∀ᵐ x ∂μ, 0 ≤ f x) → 0 ≤ m f) ∧
        (∀ f : Lp ℝ ∞ μ, (∀ᵐ x ∂μ, f x = 1) → m f = 1) ∧
        ∀ (g : G) (f h : Lp ℝ ∞ μ), (∀ᵐ x ∂μ, h x = f (g⁻¹ * x)) → m h = m f :=
  Iff.rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] in
/-- An invariant mean is nonnegative on a.e. nonnegative classes. -/
theorem IsHaarInvariantMean.nonneg {μ : Measure G} {m : Lp ℝ ∞ μ →L[ℝ] ℝ}
    (hm : IsHaarInvariantMean μ m) {f : Lp ℝ ∞ μ} (hf : ∀ᵐ x ∂μ, 0 ≤ f x) : 0 ≤ m f :=
  hm.1 f hf

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] in
/-- An invariant mean is normalized. -/
theorem IsHaarInvariantMean.apply_eq_one {μ : Measure G} {m : Lp ℝ ∞ μ →L[ℝ] ℝ}
    (hm : IsHaarInvariantMean μ m) {f : Lp ℝ ∞ μ} (hf : ∀ᵐ x ∂μ, f x = 1) : m f = 1 :=
  hm.2.1 f hf

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] in
/-- An invariant mean is left invariant. -/
theorem IsHaarInvariantMean.apply_eq {μ : Measure G} {m : Lp ℝ ∞ μ →L[ℝ] ℝ}
    (hm : IsHaarInvariantMean μ m) (g : G) {f h : Lp ℝ ∞ μ}
    (hh : ∀ᵐ x ∂μ, h x = f (g⁻¹ * x)) : m h = m f :=
  hm.2.2 g f h hh

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] in
/-- Unfolding `IsHaarAmenable`. -/
theorem isHaarAmenable_iff {μ : Measure G} : IsHaarAmenable μ ↔ ∃ m, IsHaarInvariantMean μ m :=
  Iff.rfl

/-- For a regular Haar measure on a locally compact group, an invariant mean on `L∞(G, μ)`
exists exactly when `G` is amenable in TauCeti's sense. -/
theorem isHaarAmenable_iff_amenable [LocallyCompactSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.Regular] : IsHaarAmenable μ ↔ TauCeti.Amenable G := by
  rw [TauCeti.amenable_iff_exists_lpTop_invariant_of_regular μ]
  constructor
  · rintro ⟨m, hpos, hone, hinv⟩
    refine ⟨PositiveLinearMap.mk₀ m.toLinearMap fun f hf ↦ hpos f ((Lp.coeFn_nonneg f).2 hf),
      hone 1 (Lp.coeFn_one (E := ℝ)), fun g φ ↦ hinv g φ _ (Lp.coeFn_leftTranslation g φ)⟩
  · rintro ⟨M, hM, hinv⟩
    refine ⟨⟨M.toLinearMap, M.continuous_lpTop⟩, fun f hf ↦ map_nonneg M ((Lp.coeFn_nonneg f).1 hf),
      fun f hf ↦ ?_, fun g f h hh ↦ ?_⟩
    · have : f = 1 := Lp.ext (Filter.EventuallyEq.trans hf (Lp.coeFn_one (E := ℝ)).symm)
      simpa [this] using hM
    · have : h = Lp.leftTranslation μ ∞ ℝ g f :=
        Lp.ext (Filter.EventuallyEq.trans hh (Lp.coeFn_leftTranslation g f).symm)
      simpa [this] using hinv g f

/-- Compact groups admit invariant means on the `L∞` space of every Haar measure: the
normalized Haar integral. -/
theorem isHaarAmenable_of_compact [CompactSpace G]
    (μ : Measure G) [Measure.IsHaarMeasure μ] : IsHaarAmenable μ := by
  have hμ : 0 < μ.real Set.univ := by
    rw [Measure.real]
    exact ENNReal.toReal_pos
      (isOpen_univ.measure_ne_zero μ ⟨(1 : G), trivial⟩) (measure_ne_top μ Set.univ)
  let c : ℝ := (μ.real Set.univ)⁻¹
  let L : Lp ℝ ∞ μ →ₗ[ℝ] ℝ :=
    { toFun := fun f => c * ∫ x, (f : G → ℝ) x ∂μ
      map_add' := fun f g => by
        have hf := MemLp.integrable le_top (Lp.memLp f)
        have hg := MemLp.integrable le_top (Lp.memLp g)
        rw [integral_congr_ae (Lp.coeFn_add f g), integral_add' hf hg, mul_add]
      map_smul' := fun r f => by
        rw [integral_congr_ae (Lp.coeFn_smul r f)]
        simp_rw [Pi.smul_apply]
        rw [integral_smul]
        simp only [smul_eq_mul]
        exact mul_left_comm c r _ }
  have hnorm : ∀ f : Lp ℝ ∞ μ, ∀ᵐ x ∂μ, ‖(f : G → ℝ) x‖ ≤ ‖f‖ := by
    intro f
    have hfin : eLpNormEssSup (f : G → ℝ) μ ≠ ∞ := by
      rw [← eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
      exact (Lp.memLp f).ne
    filter_upwards [ae_le_eLpNormEssSup (f := (f : G → ℝ))] with x hx
    have hle : ‖(f : G → ℝ) x‖ ≤ (eLpNormEssSup (f : G → ℝ) μ).toReal := by
      rw [← toReal_eNorm ((f : G → ℝ) x)]
      exact ENNReal.toReal_mono hfin hx
    rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
    exact hle
  have hbound : ∀ f, ‖L f‖ ≤ 1 * ‖f‖ := by
    intro f
    dsimp only [L]
    have hint : ‖∫ x, (f : G → ℝ) x ∂μ‖ ≤ ‖f‖ * μ.real Set.univ :=
      norm_integral_le_of_norm_le_const (hnorm f)
    calc
      ‖c * ∫ x, (f : G → ℝ) x ∂μ‖ = |c * ∫ x, (f : G → ℝ) x ∂μ| := Real.norm_eq_abs _
      _ = |c| * |∫ x, (f : G → ℝ) x ∂μ| := abs_mul _ _
      _ = c * |∫ x, (f : G → ℝ) x ∂μ| := by rw [abs_of_nonneg (inv_nonneg.mpr hμ.le)]
      _ ≤ c * (‖f‖ * μ.real Set.univ) :=
        mul_le_mul_of_nonneg_left (by rwa [Real.norm_eq_abs] at hint) (inv_nonneg.mpr hμ.le)
      _ = (c * μ.real Set.univ) * ‖f‖ := by ring
      _ = 1 * ‖f‖ := by rw [inv_mul_cancel₀ hμ.ne', one_mul]
  have hL (f : Lp ℝ ∞ μ) : L.mkContinuous 1 hbound f = c * ∫ x, (f : G → ℝ) x ∂μ := rfl
  refine ⟨L.mkContinuous 1 hbound, fun f hf ↦ ?_, fun f hf ↦ ?_, fun g f h hh ↦ ?_⟩
  · rw [hL]
    exact mul_nonneg (inv_nonneg.mpr hμ.le) (integral_nonneg_of_ae hf)
  · rw [hL, integral_congr_ae hf, integral_const, smul_eq_mul, mul_one, inv_mul_cancel₀ hμ.ne']
  · have hmap :=
      (Homeomorph.mulLeft g⁻¹).isClosedEmbedding.integral_map (μ := μ) (f : G → ℝ)
    simp only [Homeomorph.coe_mulLeft] at hmap
    rw [hL, hL, integral_congr_ae hh, ← hmap, map_mul_left_eq_self μ g⁻¹]

/-- **28.58**: a closed subgroup of an amenable locally compact group is amenable. -/
theorem amenable_of_isClosed [LocallyCompactSpace G] [TauCeti.Amenable G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : TauCeti.Amenable H := by
  sorry

end Group

section CommGroup

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]

/-- Locally compact abelian groups admit invariant means on the `L∞` space of every Haar
measure. -/
theorem isHaarAmenable_of_commutative [LocallyCompactSpace G]
    (μ : Measure G) [Measure.IsHaarMeasure μ] : IsHaarAmenable μ := by
  obtain ⟨K, hK, hKmem⟩ := exists_compact_mem_nhds (1 : G)
  have hmass : 0 < μ.real K :=
    ENNReal.toReal_pos (μ.measure_pos_of_mem_nhds hKmem).ne' hK.measure_lt_top.ne
  -- Start with the normalized integral on a compact neighborhood.
  let L : Lp ℝ ∞ μ →L[ℝ] ℝ :=
    (μ.real K)⁻¹ • Set.setIntegralLp (𝕜 := ℝ) K hK.measure_lt_top
  have hL (f : Lp ℝ ∞ μ) : L f = (μ.real K)⁻¹ * ∫ x in K, f x ∂μ := by
    simp only [L, smul_apply, Set.setIntegralLp_apply, smul_eq_mul]
  have hL_nonneg (f : Lp ℝ ∞ μ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x) : 0 ≤ L f := by
    rw [hL]
    exact mul_nonneg (inv_nonneg.mpr hmass.le) (integral_nonneg_of_ae (ae_restrict_of_ae hf))
  have hL_one (f : Lp ℝ ∞ μ) (hf : ∀ᵐ x ∂μ, f x = 1) : L f = 1 := by
    rw [hL, integral_congr_ae (ae_restrict_of_ae hf), integral_const, smul_eq_mul, mul_one]
    simp only [Measure.real, Measure.restrict_apply_univ]
    exact inv_mul_cancel₀ hmass.ne'
  have hmul (g : G) : MeasurePreserving (g * ·) μ μ :=
    ⟨(Homeomorph.mulLeft g).continuous.measurable, map_mul_left_eq_self μ g⟩
  let T (g : G) : Lp ℝ ∞ μ →ₗᵢ[ℝ] Lp ℝ ∞ μ :=
    Lp.compMeasurePreservingₗᵢ ℝ (g * ·) (hmul g)
  have hT (g : G) (f : Lp ℝ ∞ μ) : T g f =ᵐ[μ] fun x ↦ f (g * x) :=
    Lp.coeFn_compMeasurePreserving f (hmul g)
  have hT_nonneg (g : G) (f : Lp ℝ ∞ μ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x) :
      ∀ᵐ x ∂μ, 0 ≤ T g f x := by
    filter_upwards [hT g f, (hmul g).quasiMeasurePreserving.ae hf] with x hx hg
    exact hx ▸ hg
  have hT_one (g : G) (f : Lp ℝ ∞ μ) (hf : ∀ᵐ x ∂μ, f x = 1) :
      ∀ᵐ x ∂μ, T g f x = 1 :=
    (hT g f).trans ((hmul g).quasiMeasurePreserving.ae hf)
  have htranslate (g u : G) (f h : Lp ℝ ∞ μ)
      (hh : h =ᵐ[μ] fun x ↦ f (g⁻¹ * x)) : T u h = T (g⁻¹ * u) f := by
    apply Lp.ext
    filter_upwards [hT u h, (hmul u).quasiMeasurePreserving.ae_eq_comp hh, hT (g⁻¹ * u) f]
      with x hx hhx hfx
    dsimp only [Function.comp_apply] at hhx
    rw [hx, hhx, hfx, mul_assoc]
  -- Average the bounded orbit using TauCeti's mean on the underlying discrete group.
  let : TopologicalSpace G := ⊥
  have : DiscreteTopology G := ⟨rfl⟩
  obtain ⟨M, hM_one, hM_inv⟩ :=
    (TauCeti.amenable_iff_exists_boundedContinuousFunction_mean G).1
      TauCeti.Amenable.of_commGroup
  let R : Lp ℝ ∞ μ →ₗ[ℝ] (G →ᵇ ℝ) :=
    { toFun f := BoundedContinuousFunction.mkOfDiscrete (fun g ↦ L (T g f))
        (2 * (‖L‖ * ‖f‖)) (fun g h ↦ by
          have hg : ‖L (T g f)‖ ≤ ‖L‖ * ‖f‖ := by
            simpa only [LinearIsometry.norm_map] using L.le_opNorm (T g f)
          have hh : ‖L (T h f)‖ ≤ ‖L‖ * ‖f‖ := by
            simpa only [LinearIsometry.norm_map] using L.le_opNorm (T h f)
          rw [dist_eq_norm]
          exact (norm_sub_le _ _).trans (by linarith))
      map_add' f h := by
        ext g
        simp
      map_smul' c f := by
        ext g
        simp }
  let m₀ : Lp ℝ ∞ μ →ₚ[ℝ] ℝ :=
    PositiveLinearMap.mk₀ (M.toLinearMap.comp R) (by
      intro f hf
      have hR_nonneg : 0 ≤ R f := fun g ↦ hL_nonneg _ (hT_nonneg g f ((Lp.coeFn_nonneg f).2 hf))
      exact (map_zero M).symm.le.trans (M.monotone' hR_nonneg))
  let m : Lp ℝ ∞ μ →L[ℝ] ℝ := ⟨m₀.toLinearMap, m₀.continuous_lpTop⟩
  have hm (f : Lp ℝ ∞ μ) : m f = M (R f) := rfl
  refine ⟨m, ?_, ?_, ?_⟩
  · intro f hf
    exact map_nonneg m₀ ((Lp.coeFn_nonneg f).1 hf)
  · intro f hf
    have hRf : R f = 1 := BoundedContinuousFunction.ext fun g ↦ hL_one _ (hT_one g f hf)
    rw [hm, hRf, hM_one]
  · intro g f h hh
    have hRh : R h = (R f).compContinuous (ContinuousMap.mulLeft g⁻¹) :=
      BoundedContinuousFunction.ext fun u ↦ congrArg L (htranslate g u f h hh)
    rw [hm, hm, hRh, hM_inv]

end CommGroup

end CKMA
