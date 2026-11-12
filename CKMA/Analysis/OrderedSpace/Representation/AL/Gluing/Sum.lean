/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.OrderedSpace.Representation.AL.Gluing
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Sum of the band measures

The closed principal bands of a maximal positive disjoint family are represented by real L¹
spaces. Their carriers form a disjoint union, and the sum of the pushed-forward measures
represents the original AL-space. The index set is not assumed countable or σ-finite: each
vector meets only countably many bands, and the norm series forces the rest to vanish.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open Classical Set Filter Function MeasureTheory Topology
open scoped ENNReal

namespace CKMA

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E]
  [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]

variable (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖) [CompleteSpace E]
  [Fact (1 ≤ (1 : ENNReal))]

/-- Carrier of one band in the disjoint union. -/
abbrev bandFiber (i : bandIndex (E := E)) : Type u :=
  (bandComponent hE (bandIndex_nonneg i)).X

instance (i : bandIndex (E := E)) : MeasurableSpace (bandFiber hE i) :=
  (bandComponent hE (bandIndex_nonneg i)).mSpace

/-- Disjoint union of the band carriers. -/
abbrev alCarrier : Type u := Σ i : bandIndex (E := E), bandFiber hE i

/-- Measure of one band. -/
def bandMeasure (i : bandIndex (E := E)) : Measure (bandFiber hE i) :=
  (bandComponent hE (bandIndex_nonneg i)).μ

/-- Inclusion of one fiber into the disjoint union. -/
def bandIncl (i : bandIndex (E := E)) : bandFiber hE i → alCarrier hE :=
  Sigma.mk i

/-- A set in the disjoint union is measurable exactly on every fiber. -/
theorem measurableSet_alCarrier {s : Set (alCarrier hE)} :
    MeasurableSet s ↔ ∀ i, MeasurableSet (bandIncl hE i ⁻¹' s) := by
  simp only [MeasurableSpace.measurableSet_iInf, MeasurableSpace.map_def, bandIncl]

/-- Each fiber inclusion is a measurable embedding. -/
theorem bandIncl_measurableEmbedding (i : bandIndex (E := E)) :
    MeasurableEmbedding (bandIncl hE i) where
  injective := fun a b h => by
    injection h
  measurable := fun s hs => (measurableSet_alCarrier hE).1 hs i
  measurableSet_image' := by
    intro t ht
    rw [measurableSet_alCarrier]
    intro j
    by_cases hij : j = i
    · rw [hij]
      have hinj : Injective (bandIncl hE i) := fun a b h => by
        injection h
      change MeasurableSet (bandIncl hE i ⁻¹' (bandIncl hE i '' t))
      rw [preimage_image_eq _ hinj]
      exact ht
    · have hempty : bandIncl hE j ⁻¹' (bandIncl hE i '' t) = ∅ := by
        ext a
        simp only [mem_preimage, mem_image, mem_empty_iff_false, iff_false]
        rintro ⟨b, -, hab⟩
        exact hij (congrArg Sigma.fst hab).symm
      rw [hempty]
      exact MeasurableSet.empty

/-- Sum of the pushed-forward band measures. -/
def alMeasure : Measure (alCarrier hE) :=
  Measure.sum fun i => (bandMeasure hE i).map (bandIncl hE i)

/-- Fiberwise almost-everywhere equal measurable functions agree on the sum. -/
theorem ae_eq_alCarrier {f g : alCarrier hE → ℝ} (hf : Measurable f) (hg : Measurable g)
    (h : ∀ i, f ∘ bandIncl hE i =ᵐ[bandMeasure hE i] g ∘ bandIncl hE i) :
    f =ᵐ[alMeasure hE] g := by
  rw [EventuallyEq, ae_iff]
  have hms : MeasurableSet {a | f a ≠ g a} := by
    rw [show {a | f a ≠ g a} = {a | f a = g a}ᶜ by
      ext a
      simp]
    exact (measurableSet_eq_fun hf hg).compl
  rw [alMeasure, Measure.sum_apply _ hms]
  refine ENNReal.tsum_eq_zero.mpr fun i => ?_
  rw [Measure.map_apply (bandIncl_measurableEmbedding hE i).measurable hms]
  simpa [Function.comp_apply, ne_eq] using ae_iff.mp (h i)

/-- The band projection, packaged as a vector of the closed band. -/
def toBandₗ (i : bandIndex (E := E)) : E →ₗ[ℝ] ClosedPrincipalBand i.vec where
  toFun x := ⟨indexProjection hE i.mem_family x,
    bandProjection_mem_closure hE (bandIndex_nonneg i) x⟩
  map_add' x y := by
    ext
    exact (indexProjection hE i.mem_family).map_add x y
  map_smul' c x := by
    ext
    exact (indexProjection hE i.mem_family).map_smul c x

@[simp] theorem toBand_toVec (i : bandIndex (E := E)) (x : E) :
    (toBandₗ hE i x).toVec = indexProjection hE i.mem_family x := rfl

/-- The band projection preserves binary suprema. -/
theorem toBand_sup (i : bandIndex (E := E)) (x y : E) :
    toBandₗ hE i (x ⊔ y) = toBandₗ hE i x ⊔ toBandₗ hE i y := by
  ext
  exact bandProjection_sup hE (bandIndex_nonneg i) x y

/-- Chosen L¹ representation of one closed band. -/
def componentRep (i : bandIndex (E := E)) :
    ClosedPrincipalBand i.vec ≃ₗᵢ[ℝ] Lp ℝ 1 (bandMeasure hE i) :=
  (bandComponent hE (bandIndex_nonneg i)).rep

/-- Pointwise gluing of the band representatives. -/
def glueFn (x : E) : alCarrier hE → ℝ :=
  fun z => (componentRep hE z.fst (toBandₗ hE z.fst x) : bandFiber hE z.fst → ℝ) z.snd

/-- On each fiber the glued function is that band's representative. -/
theorem glueFn_incl (x : E) (i : bandIndex (E := E)) :
    glueFn hE x ∘ bandIncl hE i =
      (componentRep hE i (toBandₗ hE i x) : bandFiber hE i → ℝ) := rfl

/-- The glued representative is measurable. -/
theorem measurable_glueFn (x : E) : Measurable (glueFn hE x) := by
  intro s hs
  rw [measurableSet_alCarrier]
  intro i
  rw [← preimage_comp, glueFn_incl]
  exact (Lp.stronglyMeasurable _).measurable hs

/-- Norm of one band representative, as an extended real. -/
theorem eLpNorm_component (i : bandIndex (E := E)) (x : E) :
    eLpNorm (componentRep hE i (toBandₗ hE i x) : bandFiber hE i → ℝ) 1 (bandMeasure hE i) =
      ENNReal.ofReal ‖indexProjection hE i.mem_family x‖ := by
  rw [← Lp.enorm_def, ← ofReal_norm, (componentRep hE i).norm_map]
  change ENNReal.ofReal ‖(toBandₗ hE i x).toVec‖ = _
  exact congrArg (fun z : E => ENNReal.ofReal ‖z‖) (toBand_toVec hE i x)

/-- The glued representative lies in L¹ and its norm is the ambient norm. -/
theorem eLpNorm_glueFn (x : E) :
    eLpNorm (glueFn hE x) 1 (alMeasure hE) =
      ENNReal.ofReal ‖x‖ := by
  have hmeas : AEStronglyMeasurable (glueFn hE x) (alMeasure hE) :=
    (measurable_glueFn hE x).aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm hmeas, alMeasure, lintegral_sum_measure]
  have hterm : ∀ i, ∫⁻ z, ‖glueFn hE x z‖ₑ
      ∂(bandMeasure hE i).map (bandIncl hE i) =
      ENNReal.ofReal ‖indexProjection hE i.mem_family x‖ := by
    intro i
    rw [(bandIncl_measurableEmbedding hE i).lintegral_map]
    change ∫⁻ a, ‖(glueFn hE x ∘ bandIncl hE i) a‖ₑ ∂(bandMeasure hE i) = _
    rw [glueFn_incl,
      ← eLpNorm_one_eq_lintegral_enorm (Lp.stronglyMeasurable _).aestronglyMeasurable]
    exact eLpNorm_component hE i x
  rw [tsum_congr hterm,
    ← ENNReal.ofReal_tsum_of_nonneg (fun i => norm_nonneg _)
      (summable_norm_indexProjection hE x),
    tsum_norm_indexProjection_eq hE x]

/-- The glued representative is integrable. -/
theorem memLp_glueFn (x : E) : MemLp (glueFn hE x) 1 (alMeasure hE) := by
  rw [memLp_iff, eLpNorm_glueFn]
  exact ENNReal.ofReal_lt_top

/-- Lattice isometry data, as a linear map into the summed L¹ space. -/
def alRepₗ : E →ₗ[ℝ] Lp ℝ 1 (alMeasure hE) where
  toFun x := (memLp_glueFn hE x).toLp (glueFn hE x)
  map_add' x y := by
    have hpt : glueFn hE (x + y) =ᵐ[alMeasure hE] glueFn hE x + glueFn hE y := by
      refine ae_eq_alCarrier hE (measurable_glueFn hE _)
        ((measurable_glueFn hE x).add (measurable_glueFn hE y)) ?_
      intro i
      have hr : (glueFn hE x + glueFn hE y) ∘ bandIncl hE i =
          glueFn hE x ∘ bandIncl hE i + glueFn hE y ∘ bandIncl hE i := by
        funext a
        simp [Function.comp_apply, Pi.add_apply]
      have hsum : componentRep hE i (toBandₗ hE i (x + y)) =
          componentRep hE i (toBandₗ hE i x) +
            componentRep hE i (toBandₗ hE i y) := by
        rw [(toBandₗ hE i).map_add]
        exact (componentRep hE i).map_add (toBandₗ hE i x) (toBandₗ hE i y)
      rw [glueFn_incl, hsum, hr, glueFn_incl, glueFn_incl]
      exact Lp.coeFn_add (componentRep hE i (toBandₗ hE i x))
        (componentRep hE i (toBandₗ hE i y))
    have hmem : MemLp (glueFn hE x + glueFn hE y) 1 (alMeasure hE) :=
      (memLp_glueFn hE x).add (memLp_glueFn hE y)
    rw [MemLp.toLp_congr (memLp_glueFn hE (x + y)) hmem hpt, MemLp.toLp_add]
  map_smul' c x := by
    have hpt : glueFn hE (c • x) =ᵐ[alMeasure hE] c • glueFn hE x := by
      refine ae_eq_alCarrier hE (measurable_glueFn hE _)
        ((measurable_glueFn hE x).const_smul c) ?_
      intro i
      have hr : (c • glueFn hE x) ∘ bandIncl hE i =
          c • (glueFn hE x ∘ bandIncl hE i) := by
        funext a
        simp [Function.comp_apply, Pi.smul_apply]
      have hsmul : componentRep hE i (toBandₗ hE i (c • x)) =
          c • componentRep hE i (toBandₗ hE i x) := by
        rw [(toBandₗ hE i).map_smul]
        exact (componentRep hE i).map_smul c (toBandₗ hE i x)
      rw [glueFn_incl, hsmul, hr, glueFn_incl]
      exact Lp.coeFn_smul c (componentRep hE i (toBandₗ hE i x))
    have hmem : MemLp (c • glueFn hE x) 1 (alMeasure hE) :=
      (memLp_glueFn hE x).const_smul c
    rw [MemLp.toLp_congr (memLp_glueFn hE (c • x)) hmem hpt]
    exact MemLp.toLp_const_smul c (memLp_glueFn hE x)

/-- The representation preserves norms. -/
theorem norm_alRepₗ (x : E) : ‖alRepₗ hE x‖ = ‖x‖ := by
  suffices ‖(memLp_glueFn hE x).toLp (glueFn hE x)‖ = ‖x‖ by
    simpa only [alRepₗ, LinearMap.coe_mk, AddHom.coe_mk] using this
  rw [Lp.norm_toLp, eLpNorm_glueFn, ENNReal.toReal_ofReal (norm_nonneg x)]

/-- The representation as a linear isometry. -/
def alRepₗᵢ : E →ₗᵢ[ℝ] Lp ℝ 1 (alMeasure hE) where
  toLinearMap := alRepₗ hE
  norm_map' := norm_alRepₗ hE

/-- The representation preserves binary suprema. -/
theorem alRepₗ_sup (x y : E) :
    alRepₗ hE (x ⊔ y) = alRepₗ hE x ⊔ alRepₗ hE y := by
  have hglue : Measurable (glueFn hE x ⊔ glueFn hE y) := by
    have hmax := Measurable.max (measurable_glueFn hE x) (measurable_glueFn hE y)
    have hfun : (fun a => max (glueFn hE x a) (glueFn hE y a)) =
        glueFn hE x ⊔ glueFn hE y := by
      funext a
      rw [Pi.sup_apply]
    rw [← hfun]
    exact hmax
  have hpt : glueFn hE (x ⊔ y) =ᵐ[alMeasure hE] glueFn hE x ⊔ glueFn hE y := by
    refine ae_eq_alCarrier hE (measurable_glueFn hE _) hglue ?_
    intro i
    have hr : (glueFn hE x ⊔ glueFn hE y) ∘ bandIncl hE i =
        glueFn hE x ∘ bandIncl hE i ⊔ glueFn hE y ∘ bandIncl hE i := by
      funext a
      simp [Function.comp_apply, Pi.sup_apply]
    have hpres : componentRep hE i (toBandₗ hE i (x ⊔ y)) =
        componentRep hE i (toBandₗ hE i x) ⊔
          componentRep hE i (toBandₗ hE i y) := by
      rw [toBand_sup]
      exact (bandComponent hE (bandIndex_nonneg i)).preserves_sup
        (toBandₗ hE i x) (toBandₗ hE i y)
    rw [glueFn_incl, hpres, hr, glueFn_incl, glueFn_incl]
    exact Lp.coeFn_sup (componentRep hE i (toBandₗ hE i x))
      (componentRep hE i (toBandₗ hE i y))
  have hmem : MemLp (glueFn hE x ⊔ glueFn hE y) 1 (alMeasure hE) :=
    (memLp_glueFn hE x).sup (memLp_glueFn hE y)
  have hcoe : ⇑(alRepₗ hE x ⊔ alRepₗ hE y) =ᵐ[alMeasure hE]
      glueFn hE x ⊔ glueFn hE y := by
    have hx0 : (alRepₗ hE x : alCarrier hE → ℝ) =ᵐ[alMeasure hE] glueFn hE x := by
      simpa only [alRepₗ, LinearMap.coe_mk, AddHom.coe_mk] using
        MemLp.coeFn_toLp (memLp_glueFn hE x)
    have hy0 : (alRepₗ hE y : alCarrier hE → ℝ) =ᵐ[alMeasure hE] glueFn hE y := by
      simpa only [alRepₗ, LinearMap.coe_mk, AddHom.coe_mk] using
        MemLp.coeFn_toLp (memLp_glueFn hE y)
    filter_upwards [Lp.coeFn_sup (alRepₗ hE x) (alRepₗ hE y), hx0, hy0] with z hz hx hy
    rw [hz, Pi.sup_apply, hx, hy, Pi.sup_apply]
  have hEq := MemLp.toLp_congr (memLp_glueFn hE (x ⊔ y))
    (Lp.memLp (alRepₗ hE x ⊔ alRepₗ hE y)) (hpt.trans hcoe.symm)
  simpa [alRepₗ, MemLp.coeFn_toLp] using hEq

/-- Restriction of an L¹ function to one fiber is integrable. -/
theorem memLp_slice (ψ : Lp ℝ 1 (alMeasure hE)) (i : bandIndex (E := E)) :
    MemLp ((ψ : alCarrier hE → ℝ) ∘ bandIncl hE i) 1 (bandMeasure hE i) := by
  have hμ : MemLp (ψ : alCarrier hE → ℝ) 1
      ((bandMeasure hE i).map (bandIncl hE i)) :=
    (Lp.memLp ψ).mono_measure (Measure.le_sum
      (fun j => (bandMeasure hE j).map (bandIncl hE j)) i)
  exact (bandIncl_measurableEmbedding hE i).memLp_map_measure_iff.mp hμ

/-- Band component of an L¹ function, read through the fiber representation. -/
def alSlice (ψ : Lp ℝ 1 (alMeasure hE)) (i : bandIndex (E := E)) : ClosedPrincipalBand i.vec :=
  (componentRep hE i).symm ((memLp_slice hE ψ i).toLp
    ((ψ : alCarrier hE → ℝ) ∘ bandIncl hE i))

/-- A vector of a closed band is fixed by its own index projection. -/
theorem indexProjection_eq_self_of_band (i : bandIndex (E := E)) (y : ClosedPrincipalBand i.vec) :
    indexProjection hE i.mem_family y.toVec = y.toVec :=
  bandProjection_eq_of_mem_closure hE (bandIndex_nonneg i) y.mem_band

/-- A vector fixed by one band is killed by every other band. -/
theorem indexProjection_fixed_cross {i j : bandIndex (E := E)} (hij : i ≠ j) {x : E}
    (hx : indexProjection hE i.mem_family x = x) :
    indexProjection hE j.mem_family x = 0 := by
  have hsplit : indexProjection hE i.mem_family x =
      indexProjection hE i.mem_family x⁺ - indexProjection hE i.mem_family x⁻ := by
    have hsub := map_sub (indexProjection hE i.mem_family) x⁺ x⁻
    rwa [posPart_sub_negPart x] at hsub
  rw [← hx, hsplit]
  have hsub := map_sub (indexProjection hE j.mem_family)
    (indexProjection hE i.mem_family x⁺) (indexProjection hE i.mem_family x⁻)
  rw [hsub, indexProjection_cross_eq_zero hE hij (posPart_nonneg x),
    indexProjection_cross_eq_zero hE hij (negPart_nonneg x), sub_self]

/-- Projection passes inside a sum of vectors supported on distinct bands. -/
theorem indexProjection_tsum_fixed {z : bandIndex (E := E) → E} (hsum : Summable z)
    (hself : ∀ i, indexProjection hE i.mem_family (z i) = z i)
    (hcross : ∀ i j, i ≠ j → indexProjection hE j.mem_family (z i) = 0)
    (j : bandIndex (E := E)) :
    indexProjection hE j.mem_family (∑' (i : bandIndex (E := E)), z i) = z j := by
  rw [indexProjection_eq_clm hE j,
    (bandProjectionCLM hE (bandIndex_nonneg j)).map_tsum hsum]
  have hzero : ∀ i, i ≠ j → (bandProjectionCLM hE (bandIndex_nonneg j)) (z i) = 0 := by
    intro i hi
    rw [← indexProjection_eq_clm hE j]
    exact hcross i j hi
  rw [(hasSum_single j hzero).tsum_eq, ← indexProjection_eq_clm hE j, hself j]

/-- Norm of a sliced component. -/
theorem norm_alSlice (ψ : Lp ℝ 1 (alMeasure hE)) (i : bandIndex (E := E)) :
    ‖(alSlice hE ψ i).toVec‖ =
      ENNReal.toReal (eLpNorm ((ψ : alCarrier hE → ℝ) ∘ bandIncl hE i) 1
        (bandMeasure hE i)) := by
  rw [show ‖(alSlice hE ψ i).toVec‖ = ‖alSlice hE ψ i‖ from rfl]
  simp only [alSlice]
  rw [(componentRep hE i).symm.norm_map, Lp.norm_toLp]

/-- The sliced components form a norm-summable family. -/
theorem summable_alSlice (ψ : Lp ℝ 1 (alMeasure hE)) :
    Summable fun i : bandIndex (E := E) => (alSlice hE ψ i).toVec := by
  refine Summable.of_norm (summable_of_sum_le (c := ‖ψ‖) (fun i => norm_nonneg _) ?_)
  intro s
  have hfin : ∀ i, eLpNorm ((ψ : alCarrier hE → ℝ) ∘ bandIncl hE i) 1 (bandMeasure hE i) ≠ ∞ :=
    fun i => (memLp_slice hE ψ i).ne
  have hsum : ∑ i ∈ s, ‖(alSlice hE ψ i).toVec‖ =
      ENNReal.toReal (∑ i ∈ s, eLpNorm ((ψ : alCarrier hE → ℝ) ∘ bandIncl hE i) 1
        (bandMeasure hE i)) := by
    rw [ENNReal.toReal_sum (fun i _ => hfin i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact norm_alSlice hE ψ i
  rw [hsum]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top ψ) ?_
  have hle : ∑ i ∈ s, eLpNorm ((ψ : alCarrier hE → ℝ) ∘ bandIncl hE i) 1
      (bandMeasure hE i) ≤ ∑' (i : bandIndex (E := E)), eLpNorm
        ((ψ : alCarrier hE → ℝ) ∘ bandIncl hE i) 1 (bandMeasure hE i) :=
    ENNReal.sum_le_tsum _
  refine hle.trans ?_
  have hslice : ∀ i, AEStronglyMeasurable ((ψ : alCarrier hE → ℝ) ∘ bandIncl hE i)
      (bandMeasure hE i) := by
    intro i
    have hpush : AEStronglyMeasurable (ψ : alCarrier hE → ℝ)
        ((bandMeasure hE i).map (bandIncl hE i)) :=
      (Lp.aestronglyMeasurable ψ).mono_measure (Measure.le_sum
        (fun j : bandIndex (E := E) => (bandMeasure hE j).map (bandIncl hE j)) i)
    exact hpush.comp_measurable (bandIncl_measurableEmbedding hE i).measurable
  have hterm : ∀ i, eLpNorm ((ψ : alCarrier hE → ℝ) ∘ bandIncl hE i) 1
      (bandMeasure hE i) = ∫⁻ z, ‖(ψ : alCarrier hE → ℝ) z‖ₑ
        ∂(bandMeasure hE i).map (bandIncl hE i) := by
    intro i
    rw [eLpNorm_one_eq_lintegral_enorm (hslice i),
      (bandIncl_measurableEmbedding hE i).lintegral_map]
    simp [Function.comp_apply]
  rw [tsum_congr hterm, ← lintegral_sum_measure, ← alMeasure,
    ← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable ψ)]

/-- Sum of the sliced band components. -/
def alPreimage (ψ : Lp ℝ 1 (alMeasure hE)) : E :=
  ∑' (i : bandIndex (E := E)), (alSlice hE ψ i).toVec

/-- Each slice is the corresponding band projection of the preimage. -/
theorem indexProjection_alPreimage (ψ : Lp ℝ 1 (alMeasure hE)) (j : bandIndex (E := E)) :
    indexProjection hE j.mem_family (alPreimage hE ψ) = (alSlice hE ψ j).toVec := by
  simpa [alPreimage] using indexProjection_tsum_fixed hE (summable_alSlice hE ψ)
    (fun i => indexProjection_eq_self_of_band hE i (alSlice hE ψ i))
    (fun i j hij => indexProjection_fixed_cross hE hij
      (indexProjection_eq_self_of_band hE i (alSlice hE ψ i))) j

/-- The representation hits every L¹ class. -/
theorem alRepₗ_surjective : Function.Surjective (alRepₗ hE) := by
  intro ψ
  refine ⟨alPreimage hE ψ, ?_⟩
  have hpt : glueFn hE (alPreimage hE ψ) =ᵐ[alMeasure hE] (ψ : alCarrier hE → ℝ) := by
    refine ae_eq_alCarrier hE (measurable_glueFn hE _)
      (Lp.stronglyMeasurable ψ).measurable ?_
    intro i
    have hband : toBandₗ hE i (alPreimage hE ψ) = alSlice hE ψ i := by
      ext
      exact indexProjection_alPreimage hE ψ i
    simp only [glueFn_incl, hband, alSlice, LinearIsometryEquiv.apply_symm_apply]
    exact MemLp.coeFn_toLp (memLp_slice hE ψ i)
  have hEq := MemLp.toLp_congr (memLp_glueFn hE (alPreimage hE ψ)) (Lp.memLp ψ) hpt
  simpa [alRepₗ] using hEq

/-- Lattice isometry of an AL-space onto the summed L¹ space. -/
def alRep : E ≃ₗᵢ[ℝ] Lp ℝ 1 (alMeasure hE) :=
  LinearIsometryEquiv.ofSurjective (alRepₗᵢ hE) (alRepₗ_surjective hE)

/-- The summed representation preserves binary suprema. -/
theorem alRep_sup (x y : E) : alRep hE (x ⊔ y) = alRep hE x ⊔ alRep hE y := by
  simpa [alRep, alRepₗᵢ, LinearIsometryEquiv.coe_ofSurjective] using
    alRepₗ_sup hE x y

/-- An AL-space is lattice isometric to real L¹ of the summed band measures. -/
theorem exists_al_representation
    (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖) :
    ∃ (X : Type u) (_ : MeasurableSpace X) (μ : Measure X) (U : E ≃ₗᵢ[ℝ] Lp ℝ 1 μ),
      ∀ x y, U (x ⊔ y) = U x ⊔ U y :=
  ⟨alCarrier hE, inferInstance, alMeasure hE, alRep hE, alRep_sup hE⟩

end CKMA
