/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Metrizable.Basic
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Complete
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Mixture.Basic
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward

/-!
# Self-similar compact sets and invariant laws (39.73)

A nonempty finite family of maps with a common contraction constant below one has a
unique nonempty compact attractor in a complete nonempty metric space. The proof applies
Mathlib's Banach contraction theorem
to the Hausdorff metric on nonempty compact sets.
The measure theorem allows any nonnegative weights summing to one, including zero weights.

The invariant Borel probability is unique among all invariant probabilities; no moment
assumption is imposed. It is the pushforward of the Banach fixed point of the weight
mixture on the 1-Wasserstein space of the compact attractor. Strictly positive weights
are unnecessary for this conclusion, although they matter when identifying the support
with the full compact attractor.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory TopologicalSpace Metric Filter Set
open scoped BigOperators NNReal ENNReal Topology

variable {X ι : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    [Fintype ι]

/-- **39.73**: Hutchinson's unique nonempty compact attractor. -/
theorem existsUnique_selfSimilar_compact [Nonempty ι] (S : ι → X → X) {c : ℝ≥0}
    (hc : c < 1) (hS : ∀ i, LipschitzWith c (S i)) :
    ∃! K : NonemptyCompacts X, (K : Set X) = ⋃ i, S i '' (K : Set X) := by
  classical
  let F : NonemptyCompacts X → NonemptyCompacts X := fun K ↦
    ⟨⟨⋃ i, S i '' (K : Set X), isCompact_iUnion (fun i ↦ K.isCompact.image (hS i).continuous)⟩,
      Set.nonempty_iUnion.mpr ⟨Classical.arbitrary ι, K.nonempty.image _⟩⟩
  have hmap (i : ι) (A B : NonemptyCompacts X) :
      hausdorffEDist (S i '' (A : Set X)) (S i '' (B : Set X)) ≤ c * edist A B := by
    have haux (A B : NonemptyCompacts X) (x : X) (hx : x ∈ A) :
        ∃ y ∈ S i '' (B : Set X), edist (S i x) y ≤ c * edist A B := by
      obtain ⟨y, hy, he⟩ := B.isCompact.exists_infEDist_eq_edist B.nonempty x
      refine ⟨S i y, ⟨y, hy, rfl⟩, (hS i x y).trans ?_⟩
      have hxy : edist x y ≤ edist A B := by
        rw [← he]
        change infEDist x (B : Set X) ≤ hausdorffEDist (A : Set X) B
        exact infEDist_le_hausdorffEDist_of_mem hx
      exact mul_le_mul_of_nonneg_left hxy zero_le
    apply hausdorffEDist_le_of_mem_edist
    · rintro _ ⟨x, hx, rfl⟩
      exact haux A B x hx
    · rintro _ ⟨x, hx, rfl⟩
      simpa only [edist_comm] using haux B A x hx
  have hF : ContractingWith c F := by
    refine ⟨hc, fun A B ↦ ?_⟩
    change hausdorffEDist (⋃ i, S i '' (A : Set X)) (⋃ i, S i '' (B : Set X)) ≤ _
    exact hausdorffEDist_iUnion_le.trans (iSup_le fun i ↦ hmap i A B)
  refine ⟨hF.fixedPoint F, ?_, ?_⟩
  · exact (congrArg (fun K : NonemptyCompacts X ↦ (K : Set X)) hF.fixedPoint_isFixedPt).symm
  · intro K hK
    exact hF.fixedPoint_unique (NonemptyCompacts.ext hK.symm)

/-- Weights summing to one cannot be indexed by the empty type. -/
private theorem nonempty_of_sum_eq_one {p : ι → ℝ≥0} (hsum : ∑ i, p i = 1) : Nonempty ι := by
  refine (isEmpty_or_nonempty ι).resolve_left ?_
  intro hι
  have : IsEmpty ι := hι
  simp [Finset.univ_eq_empty, Finset.sum_empty] at hsum

omit [CompleteSpace X] [Nonempty X] [Fintype ι] in
/-- A branch preserving a nonempty set moves points toward that set at the Lipschitz rate. -/
private theorem infDist_mapsTo_le {s : Set X} (hs : s.Nonempty) {S : ι → X → X} {c : ℝ≥0}
    (hmaps : ∀ i, S i '' s ⊆ s) (hS : ∀ i, LipschitzWith c (S i)) (i : ι) (x : X) :
    infDist (S i x) s ≤ c * infDist x s := by
  obtain ⟨y₀, hy₀⟩ := hs
  have : Nonempty s := ⟨⟨y₀, hy₀⟩⟩
  have hE : infEDist (S i x) s ≤ (c : ℝ≥0∞) * infEDist x s := by
    calc
      infEDist (S i x) s ≤ ⨅ y : s, edist (S i x) (S i (y : X)) :=
        le_iInf fun y ↦ infEDist_le_edist_of_mem (hmaps i ⟨y, y.2, rfl⟩)
      _ ≤ ⨅ y : s, (c : ℝ≥0∞) * edist x (y : X) :=
        iInf_mono fun y ↦ (hS i).edist_le_mul x (y : X)
      _ = (c : ℝ≥0∞) * ⨅ y : s, edist x (y : X) := by
        rw [← ENNReal.mul_iInf fun h ↦ (ENNReal.coe_ne_top h).elim]
      _ = (c : ℝ≥0∞) * infEDist x s := by rw [infEDist, iInf_subtype']
  have hfin : (c : ℝ≥0∞) * infEDist x s ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.coe_ne_top (r := c)) (infEDist_ne_top ⟨y₀, hy₀⟩)
  rw [infDist, infDist]
  simpa [ENNReal.toReal_mul, ENNReal.coe_toReal] using ENNReal.toReal_mono hfin hE

omit [CompleteSpace X] [Nonempty X] in
/-- Every invariant probability is supported on a nonempty closed invariant set: invariance
pushes mass at positive distance onto sets whose distance threshold tends to infinity. -/
private theorem measure_compl_selfSimilar_eq_zero [MeasurableSpace X] [BorelSpace X]
    (S : ι → X → X) {c : ℝ≥0} (hc : c < 1) (hS : ∀ i, LipschitzWith c (S i)) {s : Set X}
    (hs : IsClosed s) (hsne : s.Nonempty) (hmaps : ∀ i, S i '' s ⊆ s) (p : ι → ℝ≥0)
    (hsum : ∑ i, p i = 1) {μ : Measure X} [IsProbabilityMeasure μ]
    (hμ : μ = ∑ i, p i • μ.map (S i)) : μ sᶜ = 0 := by
  let A (t : ℝ) : Set X := {x | t < infDist x s}
  have hA (t : ℝ) : MeasurableSet (A t) :=
    (isOpen_lt continuous_const (continuous_infDist_pt s)).measurableSet
  have hzero {ε : ℝ} (hε : 0 < ε) : μ (A ε) = 0 := by
    by_cases hc0 : c = 0
    · rw [hμ, Measure.finsetSum_apply]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [Measure.coe_nnreal_smul_apply,
        Measure.map_apply (hS i).continuous.measurable (hA ε)]
      have hpre : S i ⁻¹' A ε = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        intro hx
        have hle := infDist_mapsTo_le hsne hmaps hS i x
        rw [hc0, NNReal.coe_zero, zero_mul] at hle
        have hdist : infDist (S i x) s = 0 := le_antisymm hle infDist_nonneg
        exact lt_asymm hε (hdist ▸ hx)
      simp [hpre]
    · have hcpos : (0 : ℝ) < c :=
        NNReal.coe_pos.mpr (lt_of_le_of_ne (zero_le (a := c)) (Ne.symm hc0))
      have hmass (t : ℝ) : μ (A t) ≤ μ (A (t / c)) := by
        have hsub (i : ι) : S i ⁻¹' A t ⊆ A (t / c) := by
          intro x hx
          simp only [A, Set.mem_preimage, Set.mem_ofPred_eq] at hx ⊢
          have hle := infDist_mapsTo_le hsne hmaps hS i x
          exact (div_lt_iff₀' hcpos).mpr (lt_of_lt_of_le hx hle)
        have hterm (i : ι) :
            (p i • μ.map (S i)) (A t) ≤ (p i : ℝ≥0∞) * μ (A (t / c)) := by
          rw [Measure.coe_nnreal_smul_apply,
            Measure.map_apply (hS i).continuous.measurable (hA t)]
          exact mul_le_mul_of_nonneg_left (measure_mono (hsub i)) bot_le
        calc
          μ (A t) = ∑ i, (p i • μ.map (S i)) (A t) := by
            conv_lhs => rw [hμ]
            rw [Measure.finsetSum_apply]
          _ ≤ ∑ i, (p i : ℝ≥0∞) * μ (A (t / c)) :=
            Finset.sum_le_sum fun i _ ↦ hterm i
          _ = (∑ i, (p i : ℝ≥0∞)) * μ (A (t / c)) := by rw [Finset.sum_mul]
          _ = μ (A (t / c)) := by
            rw [← ENNReal.ofNNReal_finsetSum, hsum]
            simp
      have hiter (n : ℕ) : μ (A ε) ≤ μ (A (ε / (c : ℝ) ^ n)) := by
        induction n with
        | zero => simp
        | succ n ih =>
          refine ih.trans ?_
          have hdiv : ε / (c : ℝ) ^ n / c = ε / (c : ℝ) ^ (n + 1) := by
            rw [div_div, mul_comm, ← pow_succ']
          simpa [hdiv] using hmass (ε / (c : ℝ) ^ n)
      have hanti : Antitone fun n ↦ A (ε / (c : ℝ) ^ n) := by
        intro m n hmn x hx
        have hpow : (c : ℝ) ^ n ≤ (c : ℝ) ^ m :=
          pow_le_pow_of_le_one hcpos.le (by exact_mod_cast hc.le) hmn
        have hdiv : ε / (c : ℝ) ^ m ≤ ε / (c : ℝ) ^ n := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          exact mul_le_mul_of_nonneg_left hpow hε.le
        exact lt_of_le_of_lt hdiv hx
      have hinter : ⋂ n, A (ε / (c : ℝ) ^ n) = ∅ := by
        ext x
        simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
        intro hx
        have hpow : Tendsto (fun n : ℕ ↦ (c : ℝ) ^ n) atTop (𝓝 0) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one hcpos.le (by exact_mod_cast hc)
        have hinv : Tendsto (fun n : ℕ ↦ ((c : ℝ) ^ n)⁻¹) atTop atTop :=
          tendsto_inv_nhdsGT_zero.comp
            (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
              hpow (Eventually.of_forall fun _ ↦ pow_pos hcpos _))
        have hdiv : Tendsto (fun n : ℕ ↦ ε / (c : ℝ) ^ n) atTop atTop := by
          simpa [div_eq_mul_inv, tendsto_const_mul_atTop_of_pos hε] using hinv
        obtain ⟨n, hn⟩ := (hdiv.eventually (eventually_gt_atTop (infDist x s))).exists
        exact lt_asymm hn (hx n)
      have hlim : Tendsto (fun n ↦ μ (A (ε / (c : ℝ) ^ n))) atTop (𝓝 0) := by
        rw [show (0 : ℝ≥0∞) = μ (⋂ n, A (ε / (c : ℝ) ^ n)) by simp [hinter]]
        exact tendsto_measure_iInter_atTop (fun n ↦ (hA _).nullMeasurableSet) hanti
          ⟨0, measure_ne_top _ _⟩
      exact le_antisymm (ge_of_tendsto' hlim hiter) bot_le
  have hcover : sᶜ ⊆ ⋃ n : ℕ, A (1 / (n + 1 : ℝ)) := by
    intro x hx
    have hpos : 0 < infDist x s := (hs.notMem_iff_infDist_pos hsne).1 hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    exact Set.mem_iUnion.2 ⟨n, hn⟩
  exact measure_mono_null hcover (measure_iUnion_null fun n ↦ hzero (by positivity))

open TauCeti in
/-- Nonnegative weights of total mass one give a unique invariant Borel probability measure.
Uniqueness is among all invariant probabilities, without a moment assumption. -/
theorem existsUnique_selfSimilar_measure [MeasurableSpace X] [BorelSpace X]
    (S : ι → X → X) {c : ℝ≥0} (hc : c < 1) (hS : ∀ i, LipschitzWith c (S i))
    (p : ι → ℝ≥0) (hsum : ∑ i, p i = 1) :
    ∃! μ : Measure X, IsProbabilityMeasure μ ∧ μ = ∑ i, p i • μ.map (S i) := by
  have : Nonempty ι := nonempty_of_sum_eq_one hsum
  obtain ⟨K, hK, _⟩ := existsUnique_selfSimilar_compact S hc hS
  let s : Set X := K
  have hsclosed : IsClosed s := K.isCompact.isClosed
  have hsmeas : MeasurableSet s := hsclosed.measurableSet
  have hsne : s.Nonempty := K.nonempty
  have hmaps : ∀ i, S i '' s ⊆ s := by
    intro i
    calc
      S i '' s ⊆ ⋃ j, S j '' s := Set.subset_iUnion (fun j ↦ S j '' s) i
      _ = s := hK.symm
  let Y : Type _ := ↥s
  obtain ⟨x₀, hx₀⟩ := K.nonempty
  have : Nonempty Y := ⟨⟨x₀, hx₀⟩⟩
  have : CompactSpace Y := isCompact_iff_compactSpace.mp K.isCompact
  have : IsClosed s := hsclosed
  have : CompleteSpace Y := inferInstance
  have : SecondCountableTopology Y := inferInstance
  have : BorelSpace Y := inferInstance
  have : PolishSpace Y := inferInstance
  have : StandardBorelSpace Y := inferInstance
  have : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  have : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.one_ne_top⟩
  let T : ι → Y → Y := fun i y ↦ ⟨S i y, hmaps i ⟨y, y.2, rfl⟩⟩
  have hTlip (i : ι) : LipschitzWith c (T i) := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    rw [Subtype.dist_eq, Subtype.dist_eq]
    simpa [T] using (hS i).dist_le_mul x.1 y.1
  have hTmeas (i : ι) : Measurable (T i) := (hTlip i).continuous.measurable
  let inc : Y → X := Subtype.val
  have hinc : MeasurableEmbedding inc := MeasurableEmbedding.subtype_coe hsmeas
  have hsumE : ∑ i, (p i : ℝ≥0∞) = 1 := by
    rw [← ENNReal.ofNNReal_finsetSum]
    simp [hsum]
  let mixture (ν : Measure Y) : Measure Y := ∑ i, (p i : ℝ≥0∞) • ν.map (T i)
  have hprob (ν : Measure Y) [IsProbabilityMeasure ν] : IsProbabilityMeasure (mixture ν) := by
    constructor
    unfold mixture
    rw [Measure.finsetSum_apply]
    refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans hsumE
    rw [Measure.smul_apply, Measure.map_apply (hTmeas i) MeasurableSet.univ, Set.preimage_univ,
      measure_univ, smul_eq_mul, mul_one]
  have hmom (ν : Measure Y) [IsProbabilityMeasure ν] : HasFiniteMoment 1 (mixture ν) := by
    have := hprob ν
    exact hasFiniteMoment_of_boundedSpace (mixture ν)
  let mixProb (ν : Measure Y) [IsProbabilityMeasure ν] : ProbabilityMeasure Y :=
    have : IsProbabilityMeasure (mixture ν) := hprob ν
    Measure.toProbabilityMeasure (mixture ν)
  have hmixCoe (ν : Measure Y) [IsProbabilityMeasure ν] :
      (mixProb ν : Measure Y) = mixture ν := by
    simp [mixProb, Measure.coe_toProbabilityMeasure]
  let step (μ : WassersteinSpace 1 Y) : WassersteinSpace 1 Y :=
    WassersteinSpace.mk (mixProb (WassersteinSpace.toProbabilityMeasure μ : Measure Y)) <| by
      rw [hmixCoe]
      exact hmom _
  have hcoe (μ : WassersteinSpace 1 Y) :
      (WassersteinSpace.toProbabilityMeasure (step μ) : Measure Y) =
        mixture (WassersteinSpace.toProbabilityMeasure μ : Measure Y) := by
    unfold step
    rw [WassersteinSpace.coe_mk, hmixCoe]
  have hstep : ContractingWith c step := by
    refine ⟨hc, fun μ ν ↦ ?_⟩
    rw [WassersteinSpace.edist_def, WassersteinSpace.edist_def]
    rw [hcoe, hcoe]
    let μ0 : Measure Y := WassersteinSpace.toProbabilityMeasure μ
    let ν0 : Measure Y := WassersteinSpace.toProbabilityMeasure ν
    have hmix := wassersteinEDist_finset_sum_smul_rpow_le (p := 1) measurable_edist
      (by simp : (1 : ℝ≥0∞) ≠ 0) ENNReal.one_ne_top Finset.univ
      (a := fun i ↦ (p i : ℝ≥0∞)) (fun i _ ↦ ENNReal.coe_ne_top (r := p i))
      (fun i ↦ μ0.map (T i)) (fun i ↦ ν0.map (T i))
    have hmix' : wassersteinEDist 1 (mixture μ0) (mixture ν0) ≤
        ∑ i, (p i : ℝ≥0∞) * wassersteinEDist 1 (μ0.map (T i)) (ν0.map (T i)) := by
      simpa [mixture, ENNReal.toReal_one, ENNReal.rpow_one] using hmix
    have hterm (i : ι) :
        (p i : ℝ≥0∞) * wassersteinEDist 1 (μ0.map (T i)) (ν0.map (T i)) ≤
          (p i : ℝ≥0∞) * ((c : ℝ≥0∞) * wassersteinEDist 1 μ0 ν0) :=
      mul_le_mul_of_nonneg_left
        (wassersteinEDist_map_le_mul (p := 1) measurable_edist (hTmeas i) (hTlip i) μ0 ν0) bot_le
    calc
      wassersteinEDist 1 (mixture μ0) (mixture ν0)
          ≤ ∑ i, (p i : ℝ≥0∞) * wassersteinEDist 1 (μ0.map (T i)) (ν0.map (T i)) := hmix'
      _ ≤ ∑ i, (p i : ℝ≥0∞) * ((c : ℝ≥0∞) * wassersteinEDist 1 μ0 ν0) :=
        Finset.sum_le_sum fun i _ ↦ hterm i
      _ = (∑ i, (p i : ℝ≥0∞)) * ((c : ℝ≥0∞) * wassersteinEDist 1 μ0 ν0) := by
        rw [Finset.sum_mul]
      _ = (c : ℝ≥0∞) * wassersteinEDist 1 μ0 ν0 := by rw [hsumE, one_mul]
  have : Nonempty (WassersteinSpace 1 Y) :=
    ⟨WassersteinSpace.mk (diracProba ⟨x₀, hx₀⟩) (hasFiniteMoment_dirac 1 _)⟩
  let μW : WassersteinSpace 1 Y := hstep.fixedPoint step
  have hfix : step μW = μW := hstep.fixedPoint_isFixedPt
  let νY : Measure Y := WassersteinSpace.toProbabilityMeasure μW
  have hνY : νY = mixture νY := by
    simpa [νY, hfix] using hcoe μW
  have hpush (ρ : Measure Y) :
      (mixture ρ).map inc = ∑ i, p i • (ρ.map inc).map (S i) := by
    unfold mixture
    rw [Measure.map_finset_sum' (f := inc) hinc.measurable.aemeasurable]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Measure.map_smul _ hinc.measurable.aemeasurable,
      Measure.map_map hinc.measurable (hTmeas i),
      show inc ∘ T i = S i ∘ inc from funext fun _ ↦ rfl,
      Measure.map_map (hS i).continuous.measurable hinc.measurable, Measure.coe_nnreal_smul]
  let μX : Measure X := νY.map inc
  have hinv : μX = ∑ i, p i • μX.map (S i) := by
    have hμX : μX = (mixture νY).map inc := congrArg (Measure.map inc) hνY
    conv_lhs => rw [hμX]
    rw [hpush]
  refine ⟨μX, ⟨inferInstance, hinv⟩, ?_⟩
  intro ν hν
  have : IsProbabilityMeasure ν := hν.1
  have hcompl : ν sᶜ = 0 :=
    measure_compl_selfSimilar_eq_zero S hc hS hsclosed hsne hmaps p hsum hν.2
  let ρ : Measure Y := Measure.comap inc ν
  have hρmap : ρ.map inc = ν := by
    rw [hinc.map_comap]
    have hrange : range inc = s := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [hrange]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff]
    convert hcompl using 1
  have : IsProbabilityMeasure ρ :=
    (Measure.isProbabilityMeasure_map_iff hinc.measurable.aemeasurable).1 (hρmap ▸ inferInstance)
  have hρeq : ρ = mixture ρ := by
    have hsame : (mixture ρ).map inc = ρ.map inc := by
      rw [hpush, hρmap, ← hν.2]
    rw [← hinc.comap_map (mixture ρ), hsame, hinc.comap_map]
  let ρW : WassersteinSpace 1 Y :=
    WassersteinSpace.mk ρ.toProbabilityMeasure (hasFiniteMoment_of_boundedSpace ρ)
  have hρWcoe : WassersteinSpace.toProbabilityMeasure ρW = ρ.toProbabilityMeasure :=
    WassersteinSpace.coe_mk _ _
  have hfixρ : step ρW = ρW := by
    refine WassersteinSpace.toProbabilityMeasure_injective ?_
    refine ProbabilityMeasure.toMeasure_injective ?_
    calc
      (WassersteinSpace.toProbabilityMeasure (step ρW) : Measure Y)
          = mixture (WassersteinSpace.toProbabilityMeasure ρW : Measure Y) := hcoe ρW
      _ = mixture ρ := by rw [hρWcoe, Measure.coe_toProbabilityMeasure]
      _ = ρ := hρeq.symm
      _ = (WassersteinSpace.toProbabilityMeasure ρW : Measure Y) := by
        rw [hρWcoe, Measure.coe_toProbabilityMeasure]
  have hρW : ρW = μW := hstep.fixedPoint_unique hfixρ
  have hρν : ρ = νY := by
    have hprobEq : WassersteinSpace.toProbabilityMeasure ρW =
        WassersteinSpace.toProbabilityMeasure μW :=
      congrArg WassersteinSpace.toProbabilityMeasure hρW
    rw [← Measure.coe_toProbabilityMeasure ρ, ← hρWcoe, hprobEq]
  simpa [μX, hρmap] using congrArg (Measure.map inc) hρν

end CKMA
