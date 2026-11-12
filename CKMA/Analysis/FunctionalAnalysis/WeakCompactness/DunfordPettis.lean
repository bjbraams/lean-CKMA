/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Bornology.BoundedOperation
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Ultrafilter
public import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Dunford–Pettis

On a finite measure space, uniform integrability of a subset of scalar `L¹` implies relative weak
compactness. Truncations at a fixed height lie in a ball of the reflexive space `L²`, the inclusion
`L² → L¹` is weak-to-weak continuous, and a set that can be norm-approximated by relatively weakly
compact sets is itself relatively weakly compact.

The truncation scheme follows Albiac and Kalton, *Topics in Banach Space Theory*, second edition,
Theorem 5.2.8, (ii) ⇒ (i). Reflexivity of a complete inner product space is the Fréchet–Riesz
theorem, arranged so that the bidual inclusion is linear rather than conjugate-linear.
-/

@[expose] public section

noncomputable section

open Bornology Filter Function Metric Set Topology
open InnerProductSpace MeasureTheory NormedSpace
open scoped ENNReal NNReal Pointwise

namespace CKMA.WeakCompactness

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A complete inner product space is reflexive.

`InnerProductSpace.toDual` is conjugate-linear, so the preimage functional is twisted by `star`
before Riesz representation is applied. -/
theorem surjective_inclusionInDoubleDual_of_complete_innerProductSpace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] :
    Surjective (inclusionInDoubleDual 𝕜 E) := by
  intro Φ
  let J : E ≃ₗᵢ⋆[𝕜] StrongDual 𝕜 E := toDual 𝕜 E
  let ψ₀ : E →ₗ[𝕜] 𝕜 :=
    { toFun := fun x ↦ star (Φ (J x))
      map_add' := fun x y ↦ by
        change star (Φ (J (x + y))) = star (Φ (J x)) + star (Φ (J y))
        rw [map_add J, map_add Φ, star_add]
      map_smul' := fun c x ↦ by
        change star (Φ (J (c • x))) = c * star (Φ (J x))
        rw [J.map_smulₛₗ, starRingEnd_apply, map_smul, smul_eq_mul, star_mul, star_star,
          mul_comm] }
  have hψ : ∀ x, ‖ψ₀ x‖ ≤ ‖Φ‖ * ‖x‖ := by
    intro x
    calc
      ‖ψ₀ x‖ = ‖Φ (J x)‖ := by
        change ‖star (Φ (J x))‖ = ‖Φ (J x)‖
        exact norm_star _
      _ ≤ ‖Φ‖ * ‖J x‖ := Φ.le_opNorm (J x)
      _ = ‖Φ‖ * ‖x‖ := by rw [J.norm_map]
  let ψ : E →L[𝕜] 𝕜 := ψ₀.mkContinuous ‖Φ‖ hψ
  refine ⟨J.symm ψ, ?_⟩
  ext f
  obtain ⟨x, rfl⟩ := J.surjective f
  rw [dual_def]
  change (J x) (J.symm ψ) = Φ (J x)
  have hψx : ψ x = star (Φ (J x)) := by
    simp [ψ, ψ₀, LinearMap.mkContinuous_apply]
  have hJy : J (J.symm ψ) = ψ := J.apply_symm_apply ψ
  have hinner : inner 𝕜 (J.symm ψ) x = star (Φ (J x)) := by
    calc
      inner 𝕜 (J.symm ψ) x = (J (J.symm ψ)) x :=
        (toDual_apply_apply (x := J.symm ψ) (y := x)).symm
      _ = ψ x := congrFun (congrArg DFunLike.coe hJy) x
      _ = star (Φ (J x)) := hψx
  rw [toDual_apply_apply, ← inner_conj_symm x (J.symm ψ), starRingEnd_apply, hinner, star_star]

/-- In an additive topological group, a compact summand can be taken outside the closure. -/
theorem closure_add_subset_add_closure_of_isCompact
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {A K : Set G} (hK : IsCompact K) :
    closure (A + K) ⊆ closure A + K := by
  classical
  intro z hz
  obtain ⟨u, huAK, huz⟩ := mem_closure_iff_ultrafilter.mp hz
  have hexists : ∀ w ∈ A + K, ∃ k ∈ K, w - k ∈ A := by
    intro w hw
    obtain ⟨a, ha, k, hk, rfl⟩ := mem_add.mp hw
    exact ⟨k, hk, by simpa [add_sub_cancel_right] using ha⟩
  let kof : G → G := fun w ↦
    if hw : w ∈ A + K then Classical.choose (hexists w hw) else 0
  have hkof_mem : ∀ w, w ∈ A + K → kof w ∈ K := by
    intro w hw
    simp only [kof, dite_eq_left hw]
    exact (Classical.choose_spec (hexists w hw)).1
  have hkof_sub : ∀ w, w ∈ A + K → w - kof w ∈ A := by
    intro w hw
    simp only [kof, dite_eq_left hw]
    exact (Classical.choose_spec (hexists w hw)).2
  obtain ⟨k, hk, huk⟩ :=
    hK.ultrafilter_le_nhds' (Ultrafilter.map kof u) (by
      rw [Ultrafilter.mem_map]
      exact mem_of_superset huAK fun w hw ↦ hkof_mem w hw)
  have hzT : Tendsto id (u : Filter G) (𝓝 z) := by
    simpa [Tendsto] using huz
  have hkT : Tendsto kof (u : Filter G) (𝓝 k) := by
    simpa [Ultrafilter.coe_map, Tendsto] using huk
  have hsubT : Tendsto (fun w ↦ w - kof w) (u : Filter G) (𝓝 (z - k)) :=
    hzT.sub hkT
  have hA : z - k ∈ closure A := by
    rw [mem_closure_iff_ultrafilter]
    refine ⟨Ultrafilter.map (fun w ↦ w - kof w) u, ?_, ?_⟩
    · rw [Ultrafilter.mem_map]
      exact mem_of_superset huAK fun w hw ↦ hkof_sub w hw
    · simpa [Ultrafilter.coe_map, Tendsto] using hsubT
  have hzEq : z = (z - k) + k := (sub_add_cancel z k).symm
  rw [hzEq]
  exact add_mem_add hA hk

/-- The weak-star bidual embedding agrees with the strong bidual embedding. -/
theorem toStrongDual_inclusionInDoubleDualWeak
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (z : E) :
    WeakDual.toStrongDual (inclusionInDoubleDualWeak 𝕜 E (toWeakSpace 𝕜 E z)) =
      inclusionInDoubleDual 𝕜 E z := by
  simp [inclusionInDoubleDualWeak_apply, LinearEquiv.symm_apply_apply,
    StrongDual.toStrongDual_toWeakDual]

/-- The canonical image of a Banach space is norm-closed in the bidual. -/
theorem isClosed_range_inclusionInDoubleDual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] :
    IsClosed (Set.range (inclusionInDoubleDual 𝕜 E)) := by
  let L := inclusionInDoubleDualLi (𝕜 := 𝕜) (E := E)
  have hclosed :=
    L.antilipschitzWith.isComplete_range L.isometry.uniformContinuous |>.isClosed
  have hfun : (L : E → StrongDual 𝕜 (StrongDual 𝕜 E)) = inclusionInDoubleDual 𝕜 E := by
    ext x
    rfl
  simpa [hfun] using hclosed

/-- A weak-star bidual point lies in the canonical image exactly when its strong representative
does. -/
theorem mem_range_inclusionInDoubleDualWeak_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (φ : WeakDual 𝕜 (StrongDual 𝕜 E)) :
    φ ∈ Set.range (inclusionInDoubleDualWeak 𝕜 E) ↔
      WeakDual.toStrongDual φ ∈ Set.range (inclusionInDoubleDual 𝕜 E) := by
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨(toWeakSpace 𝕜 E).symm w, ?_⟩
    rw [← toStrongDual_inclusionInDoubleDualWeak]
    congr 1
  · rintro ⟨z, hz⟩
    refine ⟨toWeakSpace 𝕜 E z, ?_⟩
    apply WeakDual.toStrongDual.injective
    rw [toStrongDual_inclusionInDoubleDualWeak, hz]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A point of the weak-star closure of `s` lies within `ε` of the canonical image when `s` lies
within `ε` of a relatively weakly compact set. -/
theorem exists_norm_sub_inclusion_le_of_norm_approx [CompleteSpace E] {s : Set E} {ε : ℝ}
    (_hε : 0 < ε) {t : Set E} (ht : IsCompact (closure (toWeakSpace 𝕜 E '' t)))
    (happ : ∀ x ∈ s, ∃ y ∈ t, ‖x - y‖ ≤ ε) {φ : WeakDual 𝕜 (StrongDual 𝕜 E)}
    (hφ : φ ∈ closure (inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' s))) :
    ∃ z : E, ‖WeakDual.toStrongDual φ - inclusionInDoubleDual 𝕜 E z‖ ≤ ε := by
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  let J := inclusionInDoubleDualWeak 𝕜 E
  let A : Set (WeakDual 𝕜 (StrongDual 𝕜 E)) := J '' (toWeakSpace 𝕜 E '' t)
  let K : Set (WeakDual 𝕜 (StrongDual 𝕜 E)) :=
    WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) ε
  have hK : IsCompact K := WeakDual.isCompact_closedBall 0 ε
  have hsub : J '' (toWeakSpace 𝕜 E '' s) ⊆ A + K := by
    intro w hw
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hw
    obtain ⟨y, hy, hxy⟩ := happ x hx
    refine ⟨J (toWeakSpace 𝕜 E y), ?_, J (toWeakSpace 𝕜 E (x - y)), ?_, ?_⟩
    · exact ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    · rw [mem_preimage]
      -- The bidual metric is not definitionally the seminormed-group metric.
      have hdist :
          dist (WeakDual.toStrongDual (J (toWeakSpace 𝕜 E (x - y)))) 0 =
            ‖-WeakDual.toStrongDual (J (toWeakSpace 𝕜 E (x - y))) + 0‖ :=
        SeminormedAddCommGroup.dist_eq _ (0 : StrongDual 𝕜 (StrongDual 𝕜 E))
      rw [mem_closedBall, hdist, add_zero, ContinuousLinearMap.opNorm_neg,
        toStrongDual_inclusionInDoubleDualWeak]
      exact (double_dual_bound 𝕜 E (x - y)).trans hxy
    · calc
        J (toWeakSpace 𝕜 E y) + J (toWeakSpace 𝕜 E (x - y))
            = J (toWeakSpace 𝕜 E y + toWeakSpace 𝕜 E (x - y)) := (map_add J _ _).symm
        _ = J (toWeakSpace 𝕜 E (y + (x - y))) := by
            congr 1
        _ = J (toWeakSpace 𝕜 E x) := by
            congr 1
            rw [add_comm, sub_add_cancel]
  have hφadd : φ ∈ closure A + K :=
    closure_add_subset_add_closure_of_isCompact hK ((closure_mono hsub) hφ)
  obtain ⟨a, ha, k, hk, rfl⟩ := mem_add.mp hφadd
  have hAclosed : IsClosed (J '' closure (toWeakSpace 𝕜 E '' t)) :=
    (ht.image J.continuous).isClosed
  have haMem : a ∈ J '' closure (toWeakSpace 𝕜 E '' t) :=
    (closure_minimal
      (by
        intro w hw
        obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hw
        exact ⟨toWeakSpace 𝕜 E y, subset_closure ⟨y, hy, rfl⟩, rfl⟩)
      hAclosed) ha
  obtain ⟨w, -, rfl⟩ := haMem
  let z : E := (toWeakSpace 𝕜 E).symm w
  refine ⟨z, ?_⟩
  have hkNorm : ‖WeakDual.toStrongDual k‖ ≤ ε := by
    have hk' : WeakDual.toStrongDual k ∈ closedBall (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) ε := by
      simpa [K, mem_preimage] using hk
    have hdist : dist (WeakDual.toStrongDual k) 0 = ‖-(WeakDual.toStrongDual k) + 0‖ :=
      SeminormedAddCommGroup.dist_eq _ (0 : StrongDual 𝕜 (StrongDual 𝕜 E))
    rw [mem_closedBall, hdist, add_zero, ContinuousLinearMap.opNorm_neg] at hk'
    exact hk'
  have hwz : w = toWeakSpace 𝕜 E z := by simp [z]
  rw [map_add, hwz, toStrongDual_inclusionInDoubleDualWeak]
  have hEq : inclusionInDoubleDual 𝕜 E z + WeakDual.toStrongDual k -
      inclusionInDoubleDual 𝕜 E z = WeakDual.toStrongDual k := by abel
  rw [hEq]
  exact hkNorm

/-- A set with compact weak closure is norm bounded.

Each continuous linear functional is weakly continuous, so its image of the set is bounded, and
Banach–Steinhaus promotes that pointwise bound to a norm bound. -/
theorem isBounded_of_isCompact_closure_toWeakSpace {t : Set E}
    (ht : IsCompact (closure (toWeakSpace 𝕜 E '' t))) : IsBounded t := by
  have hfun (f : StrongDual 𝕜 E) : IsBounded (f '' t) := by
    have hcont := WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip f
    refine ((ht.image hcont).isBounded).subset ?_
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨toWeakSpace 𝕜 E x, subset_closure ⟨x, hx, rfl⟩, ?_⟩
    rfl
  have hpointwise (f : StrongDual 𝕜 E) :
      ∃ C, ∀ x : t, ‖inclusionInDoubleDual 𝕜 E (x : E) f‖ ≤ C := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (hfun f)
    exact ⟨C, fun x ↦ by simpa [dual_def] using hC (f ↑x) ⟨↑x, x.2, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus
    (g := fun x : t ↦ inclusionInDoubleDual 𝕜 E (x : E)) hpointwise
  refine isBounded_iff_forall_norm_le.mpr ⟨C, fun x hx ↦ ?_⟩
  exact (inclusionInDoubleDualLi (𝕜 := 𝕜) (E := E)).norm_map x ▸ hC ⟨x, hx⟩

/-- A set that lies in every norm neighbourhood of a relatively weakly compact set is relatively
weakly compact. Completeness makes the canonical image of the space norm-closed in the bidual. -/
theorem isCompact_closure_toWeakSpace_of_norm_approx [CompleteSpace E] {s : Set E}
    (h : ∀ ε > 0, ∃ t : Set E, IsCompact (closure (toWeakSpace 𝕜 E '' t)) ∧
      ∀ x ∈ s, ∃ y ∈ t, ‖x - y‖ ≤ ε) :
    IsCompact (closure (toWeakSpace 𝕜 E '' s)) := by
  have hs : IsBounded s := by
    obtain ⟨t, ht, happ⟩ := h 1 one_pos
    have htB : IsBounded t := isBounded_of_isCompact_closure_toWeakSpace ht
    have hball : IsBounded (closedBall (0 : E) 1) := isBounded_closedBall
    refine (isBounded_add (t := closedBall (0 : E) 1) htB hball).subset ?_
    intro x hx
    obtain ⟨y, hy, hxy⟩ := happ x hx
    have hxEq : x = y + (x - y) :=
      ((add_comm _ _).trans (sub_add_cancel x y)).symm
    rw [hxEq]
    exact add_mem_add hy <| by rwa [mem_closedBall_iff_norm, sub_zero]
  apply isCompact_closure_of_isBounded 𝕜 E
  · simpa [preimage_image_eq _ (toWeakSpace 𝕜 E).injective] using hs
  · intro φ hφ
    rw [mem_range_inclusionInDoubleDualWeak_iff,
      ← isClosed_range_inclusionInDoubleDual.closure_eq, mem_closure_iff_nhds_zero]
    intro U hU
    obtain ⟨SV, hSV, hsub⟩ := ContinuousLinearMap.hasBasis_nhds_zero.mem_iff.mp hU
    obtain ⟨r, hr⟩ := (NormedSpace.isVonNBounded_iff' (𝕜 := 𝕜)).mp hSV.1
    obtain ⟨η, hη, hηV⟩ := Metric.mem_nhds_iff.mp hSV.2
    let ρ : ℝ := max r 0
    have hρ (x : StrongDual 𝕜 E) (hx : x ∈ SV.1) : ‖x‖ ≤ ρ :=
      (hr x hx).trans (le_max_left _ _)
    have hδ : 0 < η / (ρ + 1) := div_pos hη (by positivity)
    obtain ⟨t, ht, happ⟩ := h (η / (ρ + 1)) hδ
    obtain ⟨z, hz⟩ := exists_norm_sub_inclusion_le_of_norm_approx hδ ht happ hφ
    refine ⟨inclusionInDoubleDual 𝕜 E z, ⟨z, rfl⟩, hsub ?_⟩
    intro x hx
    refine hηV ?_
    rw [mem_ball_iff_norm, sub_zero]
    have hflip :
        ‖inclusionInDoubleDual 𝕜 E z - WeakDual.toStrongDual φ‖ ≤ η / (ρ + 1) := by
      have hneg : inclusionInDoubleDual 𝕜 E z - WeakDual.toStrongDual φ =
          -(WeakDual.toStrongDual φ - inclusionInDoubleDual 𝕜 E z) := by abel
      rw [hneg, ContinuousLinearMap.opNorm_neg]
      exact hz
    calc
      ‖(inclusionInDoubleDual 𝕜 E z - WeakDual.toStrongDual φ) x‖
          ≤ ‖inclusionInDoubleDual 𝕜 E z - WeakDual.toStrongDual φ‖ * ‖x‖ :=
            ContinuousLinearMap.le_opNorm _ _
      _ ≤ (η / (ρ + 1)) * ρ :=
          mul_le_mul hflip (hρ x hx) (norm_nonneg _) hδ.le
      _ < η := by
          have hfrac : ρ / (ρ + 1) < 1 := by
            rw [div_lt_one (by positivity)]
            exact lt_add_one ρ
          calc
            (η / (ρ + 1)) * ρ = η * (ρ / (ρ + 1)) := by ring
            _ < η * 1 := mul_lt_mul_of_pos_left hfrac hη
            _ = η := mul_one η

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- On a finite measure space, the `L¹` norm is at most the `L²` norm times the square root of the
total measure. -/
theorem eLpNorm_one_le_eLpNorm_two_mul_sqrt [IsFiniteMeasure μ] (f : Lp 𝕜 2 μ) :
    (eLpNorm f 1 μ).toReal ≤ ‖f‖ * μ.real Set.univ ^ (1 / 2 : ℝ) := by
  have hle := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    fact_one_le_two_ennreal.elim (Lp.aestronglyMeasurable f)
  have hexp : 1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal = 1 / 2 := by
    simp only [ENNReal.toReal_one, ENNReal.toReal_ofNat]
    norm_num
  rw [hexp] at hle
  refine (ENNReal.toReal_mono ?_ hle).trans_eq ?_
  · exact ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f)
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top μ Set.univ))
  · rw [ENNReal.toReal_mul, Lp.norm_def, measureReal_def, ← ENNReal.toReal_rpow]

/-- Continuous inclusion of scalar `L²` into scalar `L¹` on a finite measure space. -/
def lpInclL2L1 [IsFiniteMeasure μ] : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 1 μ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ⟨f.1, Lp.antitone fact_one_le_two_ennreal.elim f.2⟩
      map_add' := fun f g ↦ Subtype.ext rfl
      map_smul' := fun c f ↦ Subtype.ext rfl }
    (μ.real Set.univ ^ (1 / 2 : ℝ))
    (fun f ↦ by
      simpa [Lp.norm_def] using
        (eLpNorm_one_le_eLpNorm_two_mul_sqrt (μ := μ) f).trans_eq (mul_comm _ _))

/-- The set where a representative exceeds height `C`. -/
def tailSet (C : ℝ≥0) (f : X → 𝕜) : Set X := {x | C ≤ ‖f x‖₊}

/-- Truncation of a representative to the set where its norm is strictly below `C`. -/
def truncAt (C : ℝ≥0) (f : X → 𝕜) : X → 𝕜 := (tailSet C f)ᶜ.indicator f

/-- The tail of a representative above height `C`. -/
def tailAt (C : ℝ≥0) (f : X → 𝕜) : X → 𝕜 := (tailSet C f).indicator f

omit [MeasurableSpace X] in
/-- Truncation is pointwise bounded by the truncation height. -/
theorem norm_truncAt_le (C : ℝ≥0) (f : X → 𝕜) (x : X) : ‖truncAt C f x‖ ≤ C := by
  simp only [truncAt, norm_indicator_eq_indicator_norm]
  by_cases hx : x ∈ (tailSet C f)ᶜ
  · rw [indicator_of_mem hx]
    have hlt : ‖f x‖₊ < C := by
      simpa [tailSet, mem_compl_iff, Set.mem_ofPred_eq] using hx
    exact_mod_cast hlt.le
  · rw [indicator_of_notMem hx]
    exact NNReal.coe_nonneg C

omit [MeasurableSpace X] in
/-- The square of a truncation is dominated by the height times the original norm. -/
theorem norm_sq_truncAt_le (C : ℝ≥0) (f : X → 𝕜) (x : X) :
    ‖truncAt C f x‖ ^ 2 ≤ (C : ℝ) * ‖f x‖ := by
  calc
    ‖truncAt C f x‖ ^ 2 = ‖truncAt C f x‖ * ‖truncAt C f x‖ := by ring
    _ ≤ (C : ℝ) * ‖f x‖ :=
      mul_le_mul (norm_truncAt_le C f x)
        (by simpa [truncAt] using norm_indicator_le_norm_self f x) (norm_nonneg _)
        (NNReal.coe_nonneg C)

omit [MeasurableSpace X] in
/-- The squared extended norm of a truncation is dominated by the height times the original
extended norm. -/
theorem enorm_rpow_two_truncAt_le (C : ℝ≥0) (f : X → 𝕜) (x : X) :
    ‖truncAt C f x‖ₑ ^ (2 : ℝ) ≤ (C : ℝ≥0∞) * ‖f x‖ₑ := by
  calc
    ‖truncAt C f x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal ‖truncAt C f x‖ ^ (2 : ℝ) := by
      rw [← ofReal_norm]
    _ = ENNReal.ofReal (‖truncAt C f x‖ ^ (2 : ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two
    _ ≤ ENNReal.ofReal ((C : ℝ) * ‖f x‖) :=
      ENNReal.ofReal_le_ofReal <| by
        rw [Real.rpow_two]
        exact norm_sq_truncAt_le C f x
    _ = ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ‖f x‖ := by
      rw [ENNReal.ofReal_mul (NNReal.coe_nonneg C)]
    _ = (C : ℝ≥0∞) * ‖f x‖ₑ := by
      rw [ENNReal.ofReal_coe_nnreal, ofReal_norm]

/-- Truncation preserves almost-everywhere strong measurability. -/
theorem aestronglyMeasurable_truncAt {f : X → 𝕜} (hf : AEStronglyMeasurable f μ) (C : ℝ≥0) :
    AEStronglyMeasurable (truncAt C f) μ := by
  have hset : NullMeasurableSet (tailSet C f) μ :=
    nullMeasurableSet_le aemeasurable_const hf.nnnorm.aemeasurable
  simpa [truncAt] using hf.indicator₀ hset.compl

/-- A truncation of an `L¹` function remains in `L¹`. -/
theorem memLp_truncAt_one {f : X → 𝕜} (hf : MemLp f 1 μ) (C : ℝ≥0) :
    MemLp (truncAt C f) 1 μ :=
  hf.of_le (aestronglyMeasurable_truncAt hf.aestronglyMeasurable C)
    (Eventually.of_forall fun x ↦ by simpa [truncAt] using norm_indicator_le_norm_self f x)

/-- A truncation of an `L¹` function lies in `L²`, with no finiteness assumption on the measure. -/
theorem memLp_truncAt_two {f : X → 𝕜} (hf : MemLp f 1 μ) (C : ℝ≥0) :
    MemLp (truncAt C f) 2 μ := by
  have hmeas := aestronglyMeasurable_truncAt hf.aestronglyMeasurable C
  rw [memLp_iff,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) two_ne_zero ENNReal.ofNat_ne_top hmeas]
  simp only [ENNReal.toReal_ofNat]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_of_lt ?_)
  refine lt_of_le_of_lt (lintegral_mono fun x ↦ enorm_rpow_two_truncAt_le C f x) ?_
  rw [lintegral_const_mul'' _ hf.aestronglyMeasurable.enorm,
    ← eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
  exact ENNReal.mul_lt_top (by finiteness) hf.eLpNorm_lt_top

/-- The `L²` norm of a truncation is at most the square root of height times the `L¹` norm. -/
theorem eLpNorm_truncAt_two_le {f : X → 𝕜} (hf : MemLp f 1 μ) (C : ℝ≥0) :
    eLpNorm (truncAt C f) 2 μ ≤ ((C : ℝ≥0∞) * eLpNorm f 1 μ) ^ (1 / 2 : ℝ) := by
  have hmeas := aestronglyMeasurable_truncAt hf.aestronglyMeasurable C
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) two_ne_zero ENNReal.ofNat_ne_top hmeas,
    eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  rw [← lintegral_const_mul'' _ hf.aestronglyMeasurable.enorm]
  exact lintegral_mono fun x ↦ enorm_rpow_two_truncAt_le C f x

/-- The truncation of an `L¹` class, as an `L¹` class. -/
def truncLp (C : ℝ≥0) (f : Lp 𝕜 1 μ) : Lp 𝕜 1 μ :=
  (memLp_truncAt_one (Lp.memLp f) C).toLp (truncAt C f)

/-- The truncation of an `L¹` class, as an `L²` class. -/
def truncLpTwo (C : ℝ≥0) (f : Lp 𝕜 1 μ) : Lp 𝕜 2 μ :=
  (memLp_truncAt_two (Lp.memLp f) C).toLp (truncAt C f)

/-- The inclusion sends the `L²` truncation to the `L¹` truncation. -/
theorem lpInclL2L1_truncLpTwo [IsFiniteMeasure μ] (C : ℝ≥0) (f : Lp 𝕜 1 μ) :
    lpInclL2L1 (μ := μ) (truncLpTwo C f) = truncLp C f := by
  refine Subtype.ext ?_
  simp only [lpInclL2L1, LinearMap.mkContinuous_apply, truncLpTwo, truncLp, MemLp.toLp]
  exact (AEEqFun.mk_eq_mk).mpr (ae_eq_refl _)

/-- Norm bound for the `L²` truncation. -/
theorem norm_truncLpTwo_le (C : ℝ≥0) (f : Lp 𝕜 1 μ) :
    ‖truncLpTwo C f‖ ≤ ((C : ℝ) * ‖f‖) ^ (1 / 2 : ℝ) := by
  rw [Lp.norm_def]
  have hcong : eLpNorm (truncLpTwo C f) 2 μ = eLpNorm (truncAt C (f : X → 𝕜)) 2 μ :=
    eLpNorm_congr_ae (MemLp.coeFn_toLp _)
  rw [hcong]
  refine (ENNReal.toReal_mono ?_ (eLpNorm_truncAt_two_le (Lp.memLp f) C)).trans_eq ?_
  · exact ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (ENNReal.mul_ne_top (by finiteness) (Lp.eLpNorm_ne_top f))
  · rw [← ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.coe_toReal, Lp.norm_def]

omit [MeasurableSpace X] in
/-- Subtracting the truncation leaves the tail. -/
theorem sub_truncAt (C : ℝ≥0) (f : X → 𝕜) (x : X) :
    f x - truncAt C f x = tailAt C f x := by
  by_cases hx : x ∈ tailSet C f
  · simp [truncAt, tailAt, hx, indicator_of_mem, indicator_of_notMem]
  · simp [truncAt, tailAt, hx, indicator_of_mem, indicator_of_notMem]

/-- The `L¹` distance from a function to its truncation is the `L¹` norm of the tail. -/
theorem norm_sub_truncLp_le {ε : ℝ} (hε : 0 ≤ ε) (C : ℝ≥0) (f : Lp 𝕜 1 μ)
    (htail : eLpNorm (tailAt C (f : X → 𝕜)) 1 μ ≤ ENNReal.ofReal ε) :
    ‖f - truncLp C f‖ ≤ ε := by
  rw [Lp.norm_def]
  refine ENNReal.toReal_le_of_le_ofReal hε ?_
  have hfun : ⇑(f - truncLp C f) =ᵐ[μ] tailAt C (f : X → 𝕜) := by
    filter_upwards [Lp.coeFn_sub f (truncLp C f), MemLp.coeFn_toLp (memLp_truncAt_one
      (Lp.memLp f) C)] with x hx1 hx2
    rw [hx1, Pi.sub_apply]
    rw [show (truncLp C f : X → 𝕜) x = truncAt C (f : X → 𝕜) x by simpa [truncLp] using hx2]
    exact sub_truncAt C (f : X → 𝕜) x
  exact (eLpNorm_congr_ae hfun).trans_le htail

/-- The image of a closed `L²` ball under the inclusion is weakly compact in `L¹`. -/
theorem isCompact_toWeakSpace_lpInclL2L1_closedBall [IsFiniteMeasure μ] (R : ℝ) :
    IsCompact (toWeakSpace 𝕜 (Lp 𝕜 1 μ) '' (lpInclL2L1 (μ := μ) '' closedBall 0 R)) := by
  have hE : Surjective (inclusionInDoubleDual 𝕜 (Lp 𝕜 2 μ)) :=
    surjective_inclusionInDoubleDual_of_complete_innerProductSpace
  have hcomp := (TauCeti.isCompact_toWeakSpace_closedBall hE (0 : Lp 𝕜 2 μ) R).image
    (WeakSpace.map (lpInclL2L1 (μ := μ))).continuous
  convert hcomp using 1
  ext w
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨toWeakSpace 𝕜 (Lp 𝕜 2 μ) g, ⟨g, hg, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨lpInclL2L1 (μ := μ) g, ⟨g, hg, rfl⟩, rfl⟩

/-- Uniform integrability implies relative weak compactness in scalar `L¹` on a finite measure
space. Mathlib's predicate already includes the uniform `L¹` bound. -/
theorem isCompact_closure_toWeakSpace_of_uniformIntegrable [IsFiniteMeasure μ]
    {s : Set (Lp 𝕜 1 μ)}
    (hUI : UniformIntegrable (fun f : s ↦ (f.1 : X → 𝕜)) 1 μ) :
    IsCompact (closure (toWeakSpace 𝕜 (Lp 𝕜 1 μ) '' s)) := by
  refine isCompact_closure_toWeakSpace_of_norm_approx fun ε hε ↦ ?_
  obtain ⟨C, hC⟩ := hUI.spec one_ne_zero ENNReal.one_ne_top
    (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨M, hM⟩ := hUI.2
  let R : ℝ := ((C : ℝ) * (M : ℝ)) ^ (1 / 2 : ℝ)
  let t : Set (Lp 𝕜 1 μ) := range fun i : s ↦ truncLp C i.1
  have htSub : t ⊆ lpInclL2L1 (μ := μ) '' closedBall 0 R := by
    rintro _ ⟨i, rfl⟩
    refine ⟨truncLpTwo C i.1, ?_, lpInclL2L1_truncLpTwo C i.1⟩
    rw [mem_closedBall_iff_norm, sub_zero]
    refine (norm_truncLpTwo_le C i.1).trans ?_
    have hnorm : ‖i.1‖ ≤ (M : ℝ) := by
      rw [Lp.norm_def]
      exact (ENNReal.toReal_mono (by finiteness) (hM i)).trans_eq (ENNReal.coe_toReal M)
    exact Real.rpow_le_rpow (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hnorm (NNReal.coe_nonneg _)) (by positivity)
  have htCompact : IsCompact (closure (toWeakSpace 𝕜 (Lp 𝕜 1 μ) '' t)) := by
    refine (isCompact_toWeakSpace_lpInclL2L1_closedBall (μ := μ) R).of_isClosed_subset
      isClosed_closure ?_
    exact closure_minimal (image_mono htSub)
      (isCompact_toWeakSpace_lpInclL2L1_closedBall (μ := μ) R).isClosed
  refine ⟨t, htCompact, ?_⟩
  intro f hf
  refine ⟨truncLp C f, ⟨⟨f, hf⟩, rfl⟩, ?_⟩
  exact norm_sub_truncLp_le hε.le C f (by simpa [tailAt, tailSet] using hC ⟨f, hf⟩)

end CKMA.WeakCompactness
