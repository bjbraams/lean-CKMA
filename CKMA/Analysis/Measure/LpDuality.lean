/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import TauCeti.MeasureTheory.Function.L1Space.Dual
import TauCeti.MeasureTheory.Function.Lp.Dual
import TauCeti.MeasureTheory.Function.Lp.Star

/-!
# Surjective scalar Lp duality

The scalar pairing integrates `f * star g`, so it is linear in the first argument and
conjugate-linear in the representing function. On sigma-finite measure spaces, every continuous
linear functional on Lp for finite `p ≥ 1` is represented by a unique conjugate-exponent Lq
function with the same norm. The endpoint `p=1, q=∞` is included. Source: GAPS 04.39.

## Main definitions

* `CKMA.lpDualPairing`: sesquilinear integral pairing `∫ x, f x * star (g x) ∂μ` between `Lp` and
  `Lq`.

## Main results

* `CKMA.existsUnique_lpDualRepresentation`: Riesz representation of continuous linear functionals
  on `Lp 𝕜 p μ` for `1 ≤ p < ∞` on sigma-finite measure spaces (**04.39**).

## Implementation notes

The bilinear integral pairing `MeasureTheory.Lp.toDual` of TauCeti is an isometry onto the dual
for `1 < p < ∞` (`MeasureTheory.Lp.toDual_surjective`) and, for finite measures, for `p = 1`
(`MeasureTheory.Lp.exists_toDual_eq`). The sigma-finite case `p = 1` is reduced to the finite
case: for an everywhere positive integrable weight `w`, multiplication by `w` maps
`L¹(μ.withDensity w)` isometrically onto `L¹(μ)`, and `μ` and `μ.withDensity w` have the same
null sets. The sesquilinear pairing is the bilinear one applied to `star g`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped ENNReal NNReal

variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X]

/-- The scalar `Lᵖ` dual pairing, linear in its first argument and conjugate-linear in its
second. -/
def lpDualPairing {p q : ℝ≥0∞} {μ : Measure X} (f : Lp 𝕜 p μ) (g : Lp 𝕜 q μ) : 𝕜 :=
  ∫ x, f x * star (g x) ∂μ

section WeightedL1

variable {μ : Measure X} {w : X → ℝ≥0}

/-- Multiplying an `L¹(μ.withDensity w)` function by `w` gives an `L¹(μ)` function. -/
private theorem memLp_one_weight_smul (hw : Measurable w)
    (f : Lp 𝕜 1 (μ.withDensity fun x => (w x : ℝ≥0∞))) :
    MemLp (fun x => w x • f x) 1 μ :=
  memLp_one_iff_integrable.2
    ((integrable_withDensity_iff_integrable_smul hw).1 (L1.integrable_coeFn f))

private theorem absolutelyContinuous_withDensity_weight (hw : Measurable w)
    (hpos : ∀ x, 0 < w x) : μ ≪ μ.withDensity fun x => (w x : ℝ≥0∞) :=
  withDensity_absolutelyContinuous' hw.coe_nnreal_ennreal.aemeasurable
    (ae_of_all _ fun x => by simpa using (hpos x).ne')

/-- Multiplication by an everywhere positive weight `w`, as a continuous linear map
`L¹(μ.withDensity w) → L¹(μ)`. -/
private def weightSmulL1 (hw : Measurable w) (hpos : ∀ x, 0 < w x) :
    Lp 𝕜 1 (μ.withDensity fun x => (w x : ℝ≥0∞)) →L[𝕜] Lp 𝕜 1 μ :=
  have hac := absolutelyContinuous_withDensity_weight (μ := μ) hw hpos
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_one_weight_smul hw f).toLp _
      map_add' := fun f g => by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [hac.ae_le (Lp.coeFn_add f g)] with x hx
        change w x • (f + g) x = w x • f x + w x • g x
        rw [hx, Pi.add_apply, smul_add]
      map_smul' := fun c f => by
        rw [← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [hac.ae_le (Lp.coeFn_smul c f)] with x hx
        change w x • (c • f) x = c • (w x • f x)
        rw [hx, Pi.smul_apply, smul_comm] }
    1 fun f => by
      rw [one_mul]
      refine le_of_eq ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm,
        integral_withDensity_eq_integral_smul hw]
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (memLp_one_weight_smul hw f)] with x hx
      rw [hx]
      simp only [NNReal.smul_def, norm_smul, smul_eq_mul, Real.norm_of_nonneg (w x).coe_nonneg]

private theorem weightSmulL1_coeFn (hw : Measurable w) (hpos : ∀ x, 0 < w x)
    (f : Lp 𝕜 1 (μ.withDensity fun x => (w x : ℝ≥0∞))) :
    weightSmulL1 hw hpos f =ᵐ[μ] fun x => w x • f x :=
  MemLp.coeFn_toLp (memLp_one_weight_smul hw f)

/-- Multiplication by `w` maps `L¹(μ.withDensity w)` onto `L¹(μ)`. -/
private theorem weightSmulL1_surjective (hw : Measurable w) (hpos : ∀ x, 0 < w x) :
    Function.Surjective (weightSmulL1 (𝕜 := 𝕜) (μ := μ) hw hpos) := by
  intro F
  have hsmul : (fun x => w x • ((w x)⁻¹ • F x)) = F := by
    funext x
    exact smul_inv_smul₀ (hpos x).ne' (F x)
  have hF : MemLp (fun x => (w x)⁻¹ • F x) 1 (μ.withDensity fun x => (w x : ℝ≥0∞)) :=
    memLp_one_iff_integrable.2
      ((integrable_withDensity_iff_integrable_smul hw).2
        (by rw [hsmul]; exact L1.integrable_coeFn F))
  refine ⟨hF.toLp _, Lp.ext ?_⟩
  filter_upwards [weightSmulL1_coeFn hw hpos (hF.toLp _),
    (absolutelyContinuous_withDensity_weight hw hpos).ae_le hF.coeFn_toLp] with x hx hx'
  rw [hx, hx']
  exact smul_inv_smul₀ (hpos x).ne' (F x)

/-- On a sigma-finite measure space, every continuous linear functional on `L¹(μ)` is integration
against an essentially bounded function. -/
private theorem exists_toDual_top_one_eq [SigmaFinite μ] (φ : StrongDual 𝕜 (Lp 𝕜 1 μ)) :
    ∃ g : Lp 𝕜 ∞ μ, Lp.toDual 𝕜 μ ∞ 1 g = φ := by
  obtain ⟨w, hpos, hw, hint⟩ := exists_pos_lintegral_lt_of_sigmaFinite μ one_ne_zero
  set ν := μ.withDensity fun x => (w x : ℝ≥0∞)
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity (hint.trans ENNReal.one_lt_top).ne
  have hac : μ ≪ ν := absolutelyContinuous_withDensity_weight hw hpos
  set T := weightSmulL1 (𝕜 := 𝕜) (μ := μ) hw hpos
  obtain ⟨h, hh⟩ := Lp.exists_toDual_eq (φ.comp T)
  have key : ∀ f, φ (T f) = ∫ x, h x * T f x ∂μ := fun f => by
    rw [← ContinuousLinearMap.comp_apply, ← hh, Lp.toDual_apply,
      integral_withDensity_eq_integral_smul hw]
    refine integral_congr_ae ?_
    filter_upwards [weightSmulL1_coeFn hw hpos f] with x hx
    rw [hx, mul_smul_comm]
  have hmem : MemLp (h : X → 𝕜) ∞ μ := by
    rw [memLp_iff, eLpNorm_exponent_top ((Lp.aestronglyMeasurable h).mono_ac hac)]
    refine (eLpNormEssSup_mono_measure _ hac).trans_lt ?_
    rw [← eLpNorm_exponent_top (Lp.aestronglyMeasurable h)]
    exact Lp.eLpNorm_lt_top h
  refine ⟨hmem.toLp _, ContinuousLinearMap.ext fun F => ?_⟩
  obtain ⟨f, rfl⟩ := weightSmulL1_surjective (𝕜 := 𝕜) (μ := μ) hw hpos F
  rw [Lp.toDual_apply, key]
  refine integral_congr_ae ?_
  filter_upwards [hmem.coeFn_toLp] with x hx
  rw [hx]

end WeightedL1

/-- The sesquilinear pairing against `g` is the bilinear pairing against `star g`. -/
private theorem lpDualPairing_eq_toDual_star {μ : Measure X} [SigmaFinite μ] {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p] (f : Lp 𝕜 p μ) (g : Lp 𝕜 q μ) :
    lpDualPairing f g = Lp.toDual 𝕜 μ q p (star g) f := by
  rw [lpDualPairing, Lp.toDual_apply]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_star g] with x hx
  rw [hx, mul_comm]
  rfl

/-- **04.39**: every scalar functional is represented by a unique conjugate-exponent function,
with the norm identity. Sigma-finiteness includes the `p=1, q=∞` endpoint. -/
theorem existsUnique_lpDualRepresentation (μ : Measure X) [SigmaFinite μ]
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : p < ∞)
    (hpq : p⁻¹ + q⁻¹ = 1) (ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜) :
    ∃! g : Lp 𝕜 q μ, (∀ f, ℓ f = lpDualPairing f g) ∧ ‖ℓ‖ = ‖g‖ := by
  have : q.HolderConjugate p := ENNReal.holderConjugate_iff.2 (by rwa [add_comm])
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : Lp 𝕜 q μ, Lp.toDual 𝕜 μ q p g₀ = ℓ := by
    rcases (Fact.out : 1 ≤ p).eq_or_lt with h1 | h1
    · subst h1
      obtain rfl : q = ∞ := (ENNReal.HolderConjugate.eq_top_iff_eq_one q 1).2 rfl
      exact exists_toDual_top_one_eq ℓ
    · exact Lp.toDual_surjective (p := q) (q := p) h1 hp.ne ℓ
  refine ⟨star g₀, ⟨fun f => ?_, ?_⟩, fun g ⟨hg, _⟩ => ?_⟩
  · rw [lpDualPairing_eq_toDual_star, star_star, hg₀]
  · rw [← hg₀, LinearIsometry.norm_map, norm_star]
  · have : Lp.toDual 𝕜 μ q p (star g) = Lp.toDual 𝕜 μ q p g₀ :=
      ContinuousLinearMap.ext fun f => by rw [← lpDualPairing_eq_toDual_star, ← hg, hg₀]
    rw [← (Lp.toDual 𝕜 μ q p).injective this, star_star]

end CKMA
