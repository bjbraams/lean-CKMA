/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Convex.Subdifferential
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import CKMA.Analysis.Convex.Duality.Subdifferential
import CKMA.Analysis.Convex.Duality.Sum
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Slater's condition and subgradient KKT multipliers

Strict feasibility produces nonnegative inequality multipliers and an equality multiplier
so that the Lagrangian is stationary on the affine constraint and complementary slackness
holds. The argument separates the slack set from the open negative orthant, normalizes by
the positive objective weight, and reads stationarity from the sum rule: the indicator of
the affine fiber is the unqualified summand, and the Lagrangian carries the continuity.
Sources: Boyd–Vandenberghe, *Convex Optimization*, §§5.5 and 5.9; GAPS 12.40.

## Main results

* `CKMA.exists_convexKKTMultipliers_of_slater`: existence of subgradient KKT multipliers under
  Slater's strict feasibility condition (GAPS 12.40).
* `CKMA.ConvexOn.finset_sum_mul`: a nonnegative linear combination of convex functions is
  convex.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped Pointwise
open Set ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluation pairing of a vector against a continuous linear functional. -/
private abbrev dualPairing (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (topDualPairing ℝ E).flip

/-- The flipped top dual pairing is evaluation. -/
private lemma dualPairing_apply (z : E) (w : StrongDual ℝ E) :
    (dualPairing E z w : ℝ) = w z := by
  simp [dualPairing, LinearMap.flip_apply, topDualPairing_apply]

/-- The zero function has only the zero subgradient. -/
private lemma subdifferential_zero_fun (x : E) :
    TauCeti.subdifferential (dualPairing E) (fun _ : E => ((0 : ℝ) : EReal)) x =
      {(0 : StrongDual ℝ E)} := by
  ext w
  rw [TauCeti.mem_subdifferential_coe_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    ext z
    rw [IsZeroApply.zero_apply]
    have hpos := h (x + z)
    have hneg := h (x - z)
    have hpos' : w z ≤ 0 := by
      have hsub : (x + z) - x = z := by abel
      rw [hsub, dualPairing_apply] at hpos
      linarith
    have hneg' : -(w z) ≤ 0 := by
      have hsub : (x - z) - x = -z := by abel
      have hpair : dualPairing E (-z) w = -(w z) := by
        rw [map_neg, LinearMap.neg_apply, dualPairing_apply]
      rw [hsub, hpair] at hneg
      linarith
    linarith
  · rintro rfl z
    rw [dualPairing_apply, IsZeroApply.zero_apply]
    simp

omit [NormedSpace ℝ E] in
/-- A real-valued function, viewed in `EReal`, is proper. -/
private lemma proper_coe (f : E → ℝ) :
    IsProperERealFunction (fun z => (f z : EReal)) :=
  ⟨fun _ => EReal.coe_ne_bot _, ⟨0, EReal.coe_ne_top _⟩⟩

/-- Finite-dimensional convex functions are continuous after coercion to `EReal`. -/
private lemma continuousAt_coe [FiniteDimensional ℝ E] {f : E → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (x : E) :
    ContinuousAt (fun z => (f z : EReal)) x := by
  have hcont : Continuous f :=
    continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  exact (continuous_coe_real_ereal.comp hcont).continuousAt

/-- Subdifferentials add for finite-dimensional real convex functions. -/
private lemma subdifferential_add_coe [FiniteDimensional ℝ E] {f g : E → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hg : ConvexOn ℝ Set.univ g) (x : E) :
    TauCeti.subdifferential (dualPairing E) (fun z => ((f z + g z : ℝ) : EReal)) x =
      TauCeti.subdifferential (dualPairing E) (fun z => (f z : EReal)) x +
        TauCeti.subdifferential (dualPairing E) (fun z => (g z : EReal)) x := by
  have hfun : (fun z => ((f z + g z : ℝ) : EReal)) =
      fun z => (f z : EReal) + (g z : EReal) := by
    funext z
    rw [EReal.coe_add]
  rw [hfun]
  exact subdifferential_add_eq (proper_coe f) (proper_coe g)
    (ConvexOn.convex_epigraph_coe hf) (ConvexOn.convex_epigraph_coe hg)
    ⟨EReal.coe_ne_top _, EReal.coe_ne_top _⟩ (continuousAt_coe hg x) x

/-- Positive scaling preserves convex subdifferentials, and the zero multiple is `{0}`. -/
private lemma subdifferential_const_mul [FiniteDimensional ℝ E] {c : ℝ} (hc : 0 ≤ c)
    {g : E → ℝ}
    (hg : ConvexOn ℝ Set.univ g) (x : E) :
    TauCeti.subdifferential (dualPairing E) (fun z => ((c * g z : ℝ) : EReal)) x =
      c • TauCeti.subdifferential (dualPairing E) (fun z => (g z : EReal)) x := by
  by_cases hc0 : c = 0
  · subst hc0
    ext w
    constructor
    · intro hw
      have hw0 : w ∈ TauCeti.subdifferential (dualPairing E)
          (fun _ : E => ((0 : ℝ) : EReal)) x := by
        simpa using hw
      rw [subdifferential_zero_fun] at hw0
      simp only [Set.mem_singleton_iff] at hw0
      subst hw0
      obtain ⟨v, hv⟩ := exists_mem_subdifferential_of_convexOn hg x
      exact ⟨v, hv, by simp⟩
    · rintro ⟨v, -, rfl⟩
      simp only [zero_smul, zero_mul]
      rw [subdifferential_zero_fun]
      exact Set.mem_singleton _
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    ext w
    rw [Set.mem_smul_set]
    constructor
    · intro hw
      refine ⟨c⁻¹ • w, ?_, ?_⟩
      · rw [TauCeti.mem_subdifferential_coe_iff] at hw ⊢
        intro z
        have hsub := hw z
        rw [dualPairing_apply] at hsub ⊢
        rw [smul_apply, smul_eq_mul]
        have hmul : c * (g x + c⁻¹ * w (z - x)) = c * g x + w (z - x) := by
          field_simp
        rw [← mul_le_mul_iff_of_pos_left hcpos, hmul]
        exact hsub
      · rw [smul_inv_smul₀ hcpos.ne']
    · rintro ⟨v, hv, rfl⟩
      rw [TauCeti.mem_subdifferential_coe_iff] at hv ⊢
      intro z
      have hsub := hv z
      rw [dualPairing_apply] at hsub ⊢
      rw [smul_apply, smul_eq_mul]
      have hmul := mul_le_mul_of_nonneg_left hsub hc
      have hident : c * (g x + v (z - x)) = c * g x + c * v (z - x) := by
        ring
      linarith

/-- A nonnegative linear combination, over a finset, of functions convex on `t` is convex on `t`. -/
theorem ConvexOn.finset_sum_mul {ι : Type*} {t : Set E} (ht : Convex ℝ t) (s : Finset ι)
    (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) (g : ι → E → ℝ) (hg : ∀ i ∈ s, ConvexOn ℝ t (g i)) :
    ConvexOn ℝ t (fun z => ∑ i ∈ s, c i * g i z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hfun : (fun z : E => ∑ i ∈ (∅ : Finset ι), c i * g i z) = fun _ => (0 : ℝ) := by
      ext z
      simp
    rw [hfun]
    exact convexOn_const 0 ht
  | @insert a s ha ih =>
    let f1 : E → ℝ := fun z => c a * g a z
    let f2 : E → ℝ := fun z => ∑ i ∈ s, c i * g i z
    have hf1 : ConvexOn ℝ t f1 := by
      simpa [f1, smul_eq_mul] using (hg a (Finset.mem_insert_self a s)).smul
        (hc a (Finset.mem_insert_self a s))
    have hf2 : ConvexOn ℝ t f2 :=
      ih (fun i hi => hc i (Finset.mem_insert_of_mem hi))
        (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    have hfun : (fun z => ∑ i ∈ insert a s, c i * g i z) = f1 + f2 := by
      ext z
      simp [f1, f2, Finset.sum_insert ha]
    rw [hfun]
    exact hf1.add hf2

/-- A nonnegative combination of convex functions is convex. -/
private lemma convexOn_weighted_sum {ι : Type*} [Fintype ι] (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (g : ι → E → ℝ) (hg : ∀ i, ConvexOn ℝ Set.univ (g i)) :
    ConvexOn ℝ Set.univ (fun z => ∑ i, c i * g i z) :=
  ConvexOn.finset_sum_mul convex_univ Finset.univ c (fun i _ => hc i) g (fun i _ => hg i)

/-- A subgradient of a weighted sum over a finset splits into scaled subgradients. -/
private lemma exists_subdifferential_weighted_sum_finset [FiniteDimensional ℝ E] {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) (g : ι → E → ℝ)
    (hg : ∀ i ∈ s, ConvexOn ℝ Set.univ (g i)) {x : E} {w : StrongDual ℝ E}
    (hw : w ∈ TauCeti.subdifferential (dualPairing E)
      (fun z => ((∑ i ∈ s, c i * g i z : ℝ) : EReal)) x) :
    ∃ v : ι → StrongDual ℝ E,
      (∀ i ∈ s, v i ∈ TauCeti.subdifferential (dualPairing E)
        (fun z => (g i z : EReal)) x) ∧
      w = ∑ i ∈ s, c i • v i := by
  classical
  induction s using Finset.induction_on generalizing w with
  | empty =>
    have hw0 : w ∈ TauCeti.subdifferential (dualPairing E)
        (fun _ : E => ((0 : ℝ) : EReal)) x := by
      simpa using hw
    rw [subdifferential_zero_fun] at hw0
    simp only [Set.mem_singleton_iff] at hw0
    subst hw0
    exact ⟨fun _ => 0, fun _ h => (Finset.notMem_empty _ h).elim, by simp⟩
  | @insert a s ha ih =>
    let f1 : E → ℝ := fun z => c a * g a z
    let f2 : E → ℝ := fun z => ∑ i ∈ s, c i * g i z
    have hfun : (fun z => ((∑ i ∈ insert a s, c i * g i z : ℝ) : EReal)) =
        fun z => ((f1 z + f2 z : ℝ) : EReal) := by
      funext z
      exact congrArg (fun r : ℝ => (r : EReal)) (by simp [f1, f2, Finset.sum_insert ha])
    rw [hfun] at hw
    have hca := hc a (Finset.mem_insert_self a s)
    have hga := hg a (Finset.mem_insert_self a s)
    have hcs : ∀ i ∈ s, 0 ≤ c i := fun i hi => hc i (Finset.mem_insert_of_mem hi)
    have hgs : ∀ i ∈ s, ConvexOn ℝ Set.univ (g i) :=
      fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hf1 : ConvexOn ℝ Set.univ f1 := by
      simpa [f1, smul_eq_mul] using hga.smul hca
    have hf2 : ConvexOn ℝ Set.univ f2 := ConvexOn.finset_sum_mul convex_univ s c hcs g hgs
    rw [subdifferential_add_coe hf1 hf2 x] at hw
    obtain ⟨w1, hw1, w2, hw2, hwadd⟩ := Set.mem_add.mp hw
    rw [subdifferential_const_mul hca hga x] at hw1
    obtain ⟨v0, hv0, hv0eq⟩ := Set.mem_smul_set.mp hw1
    have hw2' : w2 ∈ TauCeti.subdifferential (dualPairing E)
        (fun z => ((∑ i ∈ s, c i * g i z : ℝ) : EReal)) x := by
      simpa [f2] using hw2
    obtain ⟨vrest, hvrest, hvsum⟩ := ih hcs hgs hw2'
    refine ⟨Function.update vrest a v0, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | his
      · simpa using hv0
      · have hia : i ≠ a := fun h => ha (h ▸ his)
        simpa [Function.update_of_ne hia] using hvrest i his
    · rw [← hwadd, ← hv0eq, hvsum, Finset.sum_insert ha]
      simp only [Function.update_self, add_right_inj]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      simp [Function.update_of_ne hia]

/-- A subgradient of a weighted sum splits into scaled subgradients. -/
private lemma exists_subdifferential_weighted_sum [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (g : ι → E → ℝ)
    (hg : ∀ i, ConvexOn ℝ Set.univ (g i)) {x : E} {w : StrongDual ℝ E}
    (hw : w ∈ TauCeti.subdifferential (dualPairing E)
      (fun z => ((∑ i, c i * g i z : ℝ) : EReal)) x) :
    ∃ v : ι → StrongDual ℝ E,
      (∀ i, v i ∈ TauCeti.subdifferential (dualPairing E)
        (fun z => (g i z : EReal)) x) ∧
      w = ∑ i, c i • v i := by
  obtain ⟨v, hv, hw⟩ := exists_subdifferential_weighted_sum_finset Finset.univ c
    (fun i _ => hc i) g (fun i _ => hg i) hw
  exact ⟨v, fun i => hv i (Finset.mem_univ i), hw⟩

/-- A subgradient of the Lagrangian splits into objective and constraint subgradients. -/
private lemma exists_subdifferential_lagrangian [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (g : ι → E → ℝ) (hg : ∀ i, ConvexOn ℝ Set.univ (g i)) {x : E}
    {w : StrongDual ℝ E}
    (hw : w ∈ TauCeti.subdifferential (dualPairing E)
      (fun z => ((f z + ∑ i, c i * g i z : ℝ) : EReal)) x) :
    ∃ u : StrongDual ℝ E, ∃ v : ι → StrongDual ℝ E,
      u ∈ TauCeti.subdifferential (dualPairing E) (fun z => (f z : EReal)) x ∧
      (∀ i, v i ∈ TauCeti.subdifferential (dualPairing E)
        (fun z => (g i z : EReal)) x) ∧
      w = u + ∑ i, c i • v i := by
  let f2 : E → ℝ := fun z => ∑ i, c i * g i z
  have hfun : (fun z => ((f z + ∑ i, c i * g i z : ℝ) : EReal)) =
      fun z => ((f z + f2 z : ℝ) : EReal) := by
    funext z
    rfl
  rw [hfun] at hw
  have hf2 : ConvexOn ℝ Set.univ f2 := convexOn_weighted_sum c hc g hg
  rw [subdifferential_add_coe hf hf2 x] at hw
  obtain ⟨u, hu, w2, hw2, rfl⟩ := Set.mem_add.mp hw
  have hw2' : w2 ∈ TauCeti.subdifferential (dualPairing E)
      (fun z => ((∑ i, c i * g i z : ℝ) : EReal)) x := by
    simpa [f2] using hw2
  obtain ⟨v, hv, hvsum⟩ := exists_subdifferential_weighted_sum c hc g hg hw2'
  exact ⟨u, v, hu, hv, by rw [hvsum]⟩

/-- An affine fiber is convex. -/
private lemma convex_eq_fiber {m : ℕ} (A : E →L[ℝ] (Fin m → ℝ)) (b : Fin m → ℝ) :
    Convex ℝ {z : E | A z = b} := by
  intro z hz w hw a d ha hd had
  rw [Set.mem_ofPred] at hz hw ⊢
  rw [map_add, map_smul, map_smul, hz, hw, ← add_smul, had, one_smul]

/-- The zero indicator of a convex set has convex real epigraph. -/
private lemma convex_epigraph_indicator {C : Set E} [DecidablePred (· ∈ C)]
    (hC : Convex ℝ C) :
    Convex ℝ {p : E × ℝ |
      (if p.1 ∈ C then ((0 : ℝ) : EReal) else ⊤) ≤ p.2} := by
  have hepi : {p : E × ℝ |
        (if p.1 ∈ C then ((0 : ℝ) : EReal) else ⊤) ≤ p.2} =
      {p : E × ℝ | p.1 ∈ C ∧ (0 : ℝ) ≤ p.2} := by
    ext p
    by_cases hp : p.1 ∈ C <;> simp [hp]
  rw [hepi]
  exact (convexOn_const (0 : ℝ) hC).convex_epigraph

/-- A functional vanishing on `ker A` factors as `y ∘ A`. -/
private lemma exists_dual_factor {m : ℕ} (A : E →L[ℝ] (Fin m → ℝ))
    (normal : StrongDual ℝ E) (hker : ∀ d, A d = 0 → normal d = 0) :
    ∃ y : StrongDual ℝ (Fin m → ℝ), y.comp A = normal := by
  let coordProj (j : Fin m) : (Fin m → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j
  let L : Fin m → E →ₗ[ℝ] ℝ := fun j => ((coordProj j).comp A).toLinearMap
  have hpi : LinearMap.pi L = A.toLinearMap := by
    ext z j
    simp [L, coordProj]
  have hle : (⨅ j, LinearMap.ker (L j)) ≤ LinearMap.ker normal.toLinearMap := by
    rw [← LinearMap.ker_pi, hpi]
    intro d hd
    exact hker d hd
  have hspan := mem_span_of_iInf_ker_le_ker (L := L) (K := normal.toLinearMap) hle
  obtain ⟨coord, hcoord⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (R := ℝ) (v := L)).1 hspan
  let yLin : (Fin m → ℝ) →ₗ[ℝ] ℝ :=
    ∑ j, coord j • (coordProj j).toLinearMap
  let y : StrongDual ℝ (Fin m → ℝ) := yLin.toContinuousLinearMap
  refine ⟨y, ?_⟩
  ext z
  rw [comp_apply]
  have hyz : y (A z) = ∑ j, coord j * (A z) j := by
    change yLin (A z) = ∑ j, coord j * (A z) j
    simp only [yLin, LinearMap.sum_apply, LinearMap.smul_apply, coordProj, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.coe_proj, LinearMap.proj_apply]
  have hnz : normal z = ∑ j, coord j * (A z) j := by
    have hrewrite := congr_arg (fun f : E →ₗ[ℝ] ℝ => f z) hcoord
    have hleft : normal z = (∑ j, coord j • L j) z := hrewrite.symm
    rw [hleft, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.smul_apply, smul_eq_mul]
    change coord j * L j z = coord j * (A z) j
    simp only [L, coordProj, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rw [hyz, hnz]

/-- First coordinate of a convex combination in the slack space. -/
private lemma fst_combo {ι : Type*} (a d : ℝ) (p q : (ι → ℝ) × ℝ) (i : ι) :
    (a • p + d • q).1 i = a * p.1 i + d * q.1 i := by
  rw [Prod.fst_add, Prod.smul_fst, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
    Pi.smul_apply, smul_eq_mul, smul_eq_mul]

/-- Second coordinate of a convex combination in the slack space. -/
private lemma snd_combo {ι : Type*} (a d : ℝ) (p q : (ι → ℝ) × ℝ) :
    (a • p + d • q).2 = a * p.2 + d * q.2 := by
  rw [Prod.snd_add, Prod.smul_snd, Prod.smul_snd, smul_eq_mul, smul_eq_mul]

/-- A convex combination of two negative reals is negative. -/
private lemma convex_combo_neg {a d u v : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (had : a + d = 1)
    (hu : u < 0) (hv : v < 0) : a * u + d * v < 0 :=
  calc
    a * u + d * v ≤ a * max u v + d * max u v := by
      gcongr
      exacts [le_max_left _ _, le_max_right _ _]
    _ = max u v := by rw [← add_mul, had, one_mul]
    _ < 0 := max_lt hu hv

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The open negative orthant of the slack space is open. -/
private lemma isOpen_negOrthant {ι : Type*} [Finite ι] :
    IsOpen {p : (ι → ℝ) × ℝ | (∀ i, p.1 i < 0) ∧ p.2 < 0} := by
  have hset : {p : (ι → ℝ) × ℝ | (∀ i, p.1 i < 0) ∧ p.2 < 0} =
      (⋂ i, {p : (ι → ℝ) × ℝ | p.1 i < 0}) ∩ {p | p.2 < 0} := by
    ext p
    simp
  rw [hset]
  refine (isOpen_iInter_of_finite fun i => ?_).inter (isOpen_lt continuous_snd continuous_const)
  exact isOpen_lt ((continuous_apply i).comp continuous_fst) continuous_const

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The open negative orthant of the slack space is convex. -/
private lemma convex_negOrthant {ι : Type*} :
    Convex ℝ {p : (ι → ℝ) × ℝ | (∀ i, p.1 i < 0) ∧ p.2 < 0} := by
  intro p hp q hq a d ha hd had
  rw [Set.mem_ofPred] at hp hq ⊢
  refine ⟨fun i => ?_, ?_⟩
  · rw [fst_combo]
    exact convex_combo_neg ha hd had (hp.1 i) (hq.1 i)
  · rw [snd_combo]
    exact convex_combo_neg ha hd had hp.2 hq.2

/-- The set of slack vectors dominating the constraint values and the objective increase of some
point of the affine fiber is convex. -/
private lemma convex_kktSlack {m : ℕ} {ι : Type*} (f : E → ℝ) (g : ι → E → ℝ)
    (A : E →L[ℝ] (Fin m → ℝ)) (b : Fin m → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i)) (x : E) :
    Convex ℝ {p : (ι → ℝ) × ℝ | ∃ z : E, A z = b ∧ (∀ i, g i z ≤ p.1 i) ∧ f z - f x ≤ p.2} := by
  intro p hp q hq a d ha hd had
  rw [Set.mem_ofPred] at hp hq ⊢
  obtain ⟨z, hzA, hzg, hzf⟩ := hp
  obtain ⟨w, hwA, hwg, hwf⟩ := hq
  refine ⟨a • z + d • w, ?_, ?_, ?_⟩
  · rw [map_add, map_smul, map_smul, hzA, hwA, ← add_smul, had, one_smul]
  · intro i
    have hgv := (hg i).2 (Set.mem_univ z) (Set.mem_univ w) ha hd had
    have hlin : a * g i z + d * g i w ≤ a * p.1 i + d * q.1 i := by
      gcongr
      · exact hzg i
      · exact hwg i
    calc
      g i (a • z + d • w) ≤ a * g i z + d * g i w := by
        simpa [smul_eq_mul] using hgv
      _ ≤ a * p.1 i + d * q.1 i := hlin
      _ = (a • p + d • q).1 i := by rw [fst_combo]
  · have hfv := hf.2 (Set.mem_univ z) (Set.mem_univ w) ha hd had
    simp only [smul_eq_mul] at hfv
    have hfx : a * f x + d * f x = f x := by rw [← add_mul, had, one_mul]
    rw [snd_combo]
    linarith [mul_le_mul_of_nonneg_left hzf ha, mul_le_mul_of_nonneg_left hwf hd]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A continuous linear functional on the slack space `(ι → ℝ) × ℝ` is determined by its values
on the coordinate vectors. -/
private lemma strongDual_slack_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sep : StrongDual ℝ ((ι → ℝ) × ℝ)) (p : (ι → ℝ) × ℝ) :
    sep p = ∑ i, sep (Pi.single i 1, 0) * p.1 i + p.2 * sep (0, 1) := by
  have hp : p = ∑ i, p.1 i • ((Pi.single i 1 : ι → ℝ), (0 : ℝ)) +
      p.2 • ((0 : ι → ℝ), (1 : ℝ)) := by
    ext j
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  conv_lhs => rw [hp, map_add, map_sum, map_smul]
  simp only [map_smul, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- For `w < 0` and `level ≤ 0`, some positive multiple of `w` equals `level - 1`. -/
private lemma exists_pos_mul_eq_sub_one {w level : ℝ} (hw : w < 0) (hlevel : level ≤ 0) :
    ∃ r : ℝ, 0 < r ∧ r * w = level - 1 := by
  have hw0 : w ≠ 0 := hw.ne
  refine ⟨(1 - level) / (-w), div_pos (by linarith) (by linarith), ?_⟩
  field_simp
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A convex set in the slack space that contains the origin, contains the positive coordinate
half-axes, and misses the open negative orthant is supported at the origin by a functional with
nonnegative, not all vanishing, coefficients. -/
private lemma exists_nonneg_separator {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Set ((ι → ℝ) × ℝ)} (hS : Convex ℝ S)
    (hdisj : Disjoint {p : (ι → ℝ) × ℝ | (∀ i, p.1 i < 0) ∧ p.2 < 0} S)
    (h0 : ((0 : ι → ℝ), (0 : ℝ)) ∈ S)
    (hsingle : ∀ i, ∀ r : ℝ, 0 < r → ((Pi.single i r : ι → ℝ), (0 : ℝ)) ∈ S)
    (hvert : ∀ r : ℝ, 0 < r → ((0 : ι → ℝ), r) ∈ S) :
    ∃ w : ι → ℝ, ∃ μ : ℝ, (∀ i, 0 ≤ w i) ∧ 0 ≤ μ ∧ 0 < ∑ i, w i + μ ∧
      ∀ p ∈ S, 0 ≤ ∑ i, w i * p.1 i + p.2 * μ := by
  obtain ⟨sep, level, hUsep, hSsep⟩ :=
    geometric_hahn_banach_open convex_negOrthant isOpen_negOrthant hS hdisj
  set w : ι → ℝ := fun i => sep (Pi.single i 1, 0)
  set μ : ℝ := sep (0, 1)
  have hsep (p : (ι → ℝ) × ℝ) : sep p = ∑ i, w i * p.1 i + p.2 * μ :=
    strongDual_slack_apply sep p
  have hlevel : level ≤ 0 := by
    have h0' := hSsep _ h0
    rw [← Prod.zero_eq_mk, map_zero] at h0'
    exact h0'
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    by_contra hlt
    obtain ⟨r, hr, hrw⟩ := exists_pos_mul_eq_sub_one (lt_of_not_ge hlt) hlevel
    have hle := hSsep _ (hsingle i r hr)
    have hcalc : sep (Pi.single i r, (0 : ℝ)) = r * w i := by
      rw [hsep]
      simp [Pi.single_apply, mul_comm]
    linarith
  have hμ : 0 ≤ μ := by
    by_contra hlt
    obtain ⟨r, hr, hrw⟩ := exists_pos_mul_eq_sub_one (lt_of_not_ge hlt) hlevel
    have hle := hSsep _ (hvert r hr)
    have hcalc : sep ((0 : ι → ℝ), r) = r * μ := by
      rw [hsep]
      simp
    linarith
  have hsep_neg (ε : ℝ) : sep (fun _ : ι => -ε, -ε) = -ε * (∑ i, w i + μ) := by
    rw [hsep, mul_add, Finset.mul_sum]
    simp only [mul_comm]
  have hUneg (ε : ℝ) (hε : 0 < ε) :
      (fun _ : ι => -ε, -ε) ∈ {p : (ι → ℝ) × ℝ | (∀ i, p.1 i < 0) ∧ p.2 < 0} :=
    ⟨fun _ => neg_lt_zero.mpr hε, neg_lt_zero.mpr hε⟩
  set σ : ℝ := ∑ i, w i + μ
  have hσ_nonneg : 0 ≤ σ := add_nonneg (Finset.sum_nonneg fun i _ => hw i) hμ
  have hσ : 0 < σ := by
    refine lt_of_le_of_ne hσ_nonneg fun hzero => ?_
    have hlt := hUsep _ (hUneg 1 one_pos)
    rw [hsep_neg 1, ← hzero, mul_zero] at hlt
    linarith
  have hlevel0 : level = 0 := by
    refine le_antisymm hlevel (le_of_not_gt fun hlt => ?_)
    have hεpos : 0 < -level / (2 * σ) := div_pos (by linarith) (by positivity)
    have hltU := hUsep _ (hUneg _ hεpos)
    rw [hsep_neg] at hltU
    have hval : -(-level / (2 * σ)) * σ = level / 2 := by
      field_simp
    linarith
  refine ⟨w, μ, hw, hμ, hσ, fun p hp => ?_⟩
  rw [← hsep, ← hlevel0]
  exact hSsep p hp

/-- Separation against the negative orthant produces the KKT weights. -/
private lemma exists_kkt_weights {m : ℕ} {ι : Type*} [Fintype ι] (f : E → ℝ) (g : ι → E → ℝ)
    (A : E →L[ℝ] (Fin m → ℝ)) (b : Fin m → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hslater : ∃ x₀, A x₀ = b ∧ ∀ i, g i x₀ < 0) {x : E}
    (hx : (∀ i, g i x ≤ 0) ∧ A x = b)
    (hmin : ∀ z, (∀ i, g i z ≤ 0) → A z = b → f x ≤ f z) :
    ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ (∀ i, c i * g i x = 0) ∧
      ∀ z, A z = b →
        f x + ∑ i, c i * g i x ≤ f z + ∑ i, c i * g i z := by
  classical
  set S : Set ((ι → ℝ) × ℝ) :=
    {p | ∃ z : E, A z = b ∧ (∀ i, g i z ≤ p.1 i) ∧ f z - f x ≤ p.2}
  have hdisj : Disjoint {p : (ι → ℝ) × ℝ | (∀ i, p.1 i < 0) ∧ p.2 < 0} S := by
    rw [Set.disjoint_left]
    intro p hpU hpS
    rw [Set.mem_ofPred] at hpU hpS
    obtain ⟨z, hzA, hzg, hzf⟩ := hpS
    have hfeas : ∀ i, g i z ≤ 0 := fun i => (lt_of_le_of_lt (hzg i) (hpU.1 i)).le
    have hbetter : f z < f x := by linarith [hzf, hpU.2]
    exact (not_le_of_gt hbetter) (hmin z hfeas hzA)
  have hsingle : ∀ i, ∀ r : ℝ, 0 < r → ((Pi.single i r : ι → ℝ), (0 : ℝ)) ∈ S := by
    intro i r hr
    refine ⟨x, hx.2, fun j => ?_, by simp⟩
    by_cases hji : j = i
    · subst hji
      simp only [Pi.single_eq_same]
      linarith [hx.1 j]
    · simp [Pi.single_eq_of_ne hji, hx.1 j]
  obtain ⟨w, μ, hw, hμ, hσ, hsep⟩ :=
    exists_nonneg_separator (convex_kktSlack f g A b hf hg x) hdisj
      ⟨x, hx.2, by simpa using hx.1, by simp⟩ hsingle
      (fun r hr => ⟨x, hx.2, by simpa using hx.1, by simpa using hr.le⟩)
  obtain ⟨x₀, hx₀A, hx₀g⟩ := hslater
  -- The Slater point forces the objective coefficient to be positive.
  have hμpos : 0 < μ := by
    refine lt_of_le_of_ne hμ fun hzero => ?_
    have hge := hsep _ (⟨x₀, hx₀A, fun _ => le_rfl, le_rfl⟩ :
      ((fun i => g i x₀), f x₀ - f x) ∈ S)
    rw [← hzero, mul_zero, add_zero] at hge
    have hterm : ∀ i ∈ Finset.univ, w i * g i x₀ ≤ 0 := fun i _ =>
      mul_nonpos_of_nonneg_of_nonpos (hw i) (hx₀g i).le
    have hzero_term := (Finset.sum_eq_zero_iff_of_nonpos hterm).1
      (le_antisymm (Finset.sum_nonpos hterm) hge)
    have hw0 : ∀ i, w i = 0 := fun i =>
      (mul_eq_zero.mp (hzero_term i (Finset.mem_univ i))).resolve_right (hx₀g i).ne
    simp [hw0, ← hzero] at hσ
  let c : ι → ℝ := fun i => w i / μ
  have hc : ∀ i, 0 ≤ c i := fun i => div_nonneg (hw i) hμpos.le
  have hlag_ge : ∀ z, A z = b → 0 ≤ ∑ i, c i * g i z + (f z - f x) := by
    intro z hz
    have hge := hsep _ (⟨z, hz, fun _ => le_rfl, le_rfl⟩ : ((fun i => g i z), f z - f x) ∈ S)
    have hrew : ∑ i, w i * g i z + (f z - f x) * μ =
        μ * (∑ i, c i * g i z + (f z - f x)) := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [c]
        field_simp
      · ring
    rw [hrew] at hge
    exact nonneg_of_mul_nonneg_right (by linarith) hμpos
  have hcomp : ∀ i, c i * g i x = 0 := by
    have hterm : ∀ i ∈ Finset.univ, c i * g i x ≤ 0 := fun i _ =>
      mul_nonpos_of_nonneg_of_nonpos (hc i) (hx.1 i)
    have hsumge : 0 ≤ ∑ i, c i * g i x := by simpa using hlag_ge x hx.2
    have hzero_term := (Finset.sum_eq_zero_iff_of_nonpos hterm).1
      (le_antisymm (Finset.sum_nonpos hterm) hsumge)
    exact fun i => hzero_term i (Finset.mem_univ i)
  refine ⟨c, hc, hcomp, fun z hz => ?_⟩
  have hsum0 : ∑ i, c i * g i x = 0 := Finset.sum_eq_zero fun i _ => hcomp i
  linarith [hlag_ge z hz]

/-- Minimizing the Lagrangian on the affine fiber produces KKT subgradients. -/
private lemma exists_kkt_from_lagrange [FiniteDimensional ℝ E] {m : ℕ}
    {ι : Type*} [Fintype ι] (f : E → ℝ) (g : ι → E → ℝ)
    (A : E →L[ℝ] (Fin m → ℝ)) (b : Fin m → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hslater : ∃ x₀, A x₀ = b ∧ ∀ i, g i x₀ < 0) {x : E} (hxA : A x = b)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hminL : ∀ z, A z = b →
      f x + ∑ i, c i * g i x ≤ f z + ∑ i, c i * g i z) :
    ∃ u : StrongDual ℝ E, ∃ v : ι → StrongDual ℝ E,
      ∃ y : StrongDual ℝ (Fin m → ℝ),
      u ∈ TauCeti.subdifferential (dualPairing E) (fun z => (f z : EReal)) x ∧
      (∀ i, v i ∈ TauCeti.subdifferential (dualPairing E)
        (fun z => (g i z : EReal)) x) ∧
      u + ∑ i, c i • v i + y.comp A = 0 := by
  classical
  let C : Set E := {z | A z = b}
  have hxC : x ∈ C := hxA
  obtain ⟨x₀, hx₀A, -⟩ := hslater
  have hx₀C : x₀ ∈ C := hx₀A
  let lagrange : E → ℝ := fun z => f z + ∑ i, c i * g i z
  have hlag_conv : ConvexOn ℝ Set.univ lagrange :=
    hf.add (convexOn_weighted_sum c hc g hg)
  have hminC : ∀ z ∈ C, lagrange x ≤ lagrange z := by
    intro z hz
    simpa [lagrange, C] using hminL z hz
  let delta : E → EReal := fun z => if z ∈ C then ((0 : ℝ) : EReal) else ⊤
  let ell : E → EReal := fun z => (lagrange z : EReal)
  have hproper_delta : IsProperERealFunction delta := by
    refine ⟨?_, ⟨x₀, ?_⟩⟩
    · intro z
      by_cases hz : z ∈ C
      · simp [delta, hz]
      · simp [delta, hz]
    · simp [delta, hx₀C]
  have hconv_delta : Convex ℝ {p : E × ℝ | delta p.1 ≤ p.2} := by
    have hset : {p : E × ℝ | delta p.1 ≤ p.2} =
        {p : E × ℝ |
          (if p.1 ∈ C then ((0 : ℝ) : EReal) else ⊤) ≤ p.2} := by
      ext p
      simp [delta]
    rw [hset]
    exact convex_epigraph_indicator (convex_eq_fiber A b)
  have hconv_ell : Convex ℝ {p : E × ℝ | ell p.1 ≤ p.2} := by
    simpa [ell] using ConvexOn.convex_epigraph_coe hlag_conv
  have hfin : delta x₀ ≠ ⊤ ∧ ell x₀ ≠ ⊤ := by
    constructor
    · simp [delta, hx₀C]
    · exact EReal.coe_ne_top _
  have hcont : ContinuousAt ell x₀ := by
    simpa [ell] using continuousAt_coe hlag_conv x₀
  have h0 : (0 : StrongDual ℝ E) ∈ TauCeti.subdifferential (dualPairing E)
      (fun z => delta z + ell z) x := by
    rw [TauCeti.mem_subdifferential_iff]
    refine ⟨?_, ?_, ?_⟩
    · have hdx : delta x = ((0 : ℝ) : EReal) := by simp [delta, hxC]
      rw [hdx]
      exact EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, EReal.coe_ne_bot _⟩
    · have hdx : delta x = ((0 : ℝ) : EReal) := by simp [delta, hxC]
      rw [hdx]
      exact EReal.add_ne_top (EReal.coe_ne_top _) (EReal.coe_ne_top _)
    · intro z
      have hdx : delta x = ((0 : ℝ) : EReal) := by simp [delta, hxC]
      rw [hdx, dualPairing_apply, zero_apply, EReal.coe_zero, add_zero, zero_add]
      by_cases hz : z ∈ C
      · have hdz : delta z = ((0 : ℝ) : EReal) := by simp [delta, hz]
        unfold ell
        rw [hdz, ← EReal.coe_add, EReal.coe_le_coe_iff]
        linarith [hminC z hz]
      · have hdz : delta z = ⊤ := by simp [delta, hz]
        rw [hdz, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
        exact le_top
  have hsplit := subdifferential_add_eq hproper_delta (proper_coe lagrange)
    hconv_delta hconv_ell hfin hcont x
  have h0split : (0 : StrongDual ℝ E) ∈
      TauCeti.subdifferential (dualPairing E) delta x +
        TauCeti.subdifferential (dualPairing E) ell x := by
    rw [← hsplit]
    simpa [ell] using h0
  obtain ⟨normal, hnormal, lag, hlag, hsum0⟩ := Set.mem_add.mp h0split
  have hlag' : lag ∈ TauCeti.subdifferential (dualPairing E)
      (fun z => ((lagrange z : ℝ) : EReal)) x := by
    simpa [ell] using hlag
  obtain ⟨u, v, hu, hv, hlag_eq⟩ :=
    exists_subdifferential_lagrangian c hc f hf g hg hlag'
  have hnorm := (TauCeti.mem_subdifferential_ite_iff (dualPairing E)
    (Ω := C) (u := fun _ => (0 : ℝ)) hxC).1 hnormal
  have hvanish : ∀ d, A d = 0 → normal d = 0 := by
    intro d hd
    have hz : x + d ∈ C := by
      rw [Set.mem_ofPred]
      simp [map_add, hxA, hd]
    have hzn : x + (-d) ∈ C := by
      rw [Set.mem_ofPred]
      simp [map_add, map_neg, hxA, hd, neg_zero]
    have hpos := hnorm (x + d) hz
    have hneg := hnorm (x + (-d)) hzn
    have hpos' : normal d ≤ 0 := by
      have hsub : (x + d) - x = d := by abel
      rw [hsub, dualPairing_apply] at hpos
      linarith
    have hneg' : -(normal d) ≤ 0 := by
      have hsub : (x + (-d)) - x = -d := by abel
      have hpair : dualPairing E (-d) normal = -(normal d) := by
        rw [map_neg, LinearMap.neg_apply, dualPairing_apply]
      rw [hsub, hpair] at hneg
      linarith
    linarith
  obtain ⟨y, hy⟩ := exists_dual_factor A normal hvanish
  refine ⟨u, v, y, hu, hv, ?_⟩
  rw [← hlag_eq, hy, add_comm]
  exact hsum0

/-- **12.40**: strict feasibility gives subgradient KKT multipliers at a minimizer. -/
theorem exists_convexKKTMultipliers_of_slater [FiniteDimensional ℝ E] {m : ℕ}
    {ι : Type*} [Fintype ι] (f : E → ℝ)
    (g : ι → E → ℝ) (A : E →L[ℝ] (Fin m → ℝ)) (b : Fin m → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hslater : ∃ x₀, A x₀ = b ∧ ∀ i, g i x₀ < 0) {x : E}
    (hx : (∀ i, g i x ≤ 0) ∧ A x = b)
    (hmin : ∀ z, (∀ i, g i z ≤ 0) → A z = b → f x ≤ f z) :
    ∃ (c : ι → ℝ) (u : StrongDual ℝ E) (v : ι → StrongDual ℝ E)
      (y : StrongDual ℝ (Fin m → ℝ)),
      (∀ i, 0 ≤ c i) ∧
      u ∈ TauCeti.subdifferential (topDualPairing ℝ E).flip
        (fun z => (f z : EReal)) x ∧
      (∀ i, v i ∈ TauCeti.subdifferential (topDualPairing ℝ E).flip
        (fun z => (g i z : EReal)) x) ∧
      u + ∑ i, c i • v i + y.comp A = 0 ∧
      ∀ i, c i * g i x = 0 := by
  obtain ⟨c, hc, hcomp, hminL⟩ := exists_kkt_weights f g A b hf hg hslater hx hmin
  obtain ⟨u, v, y, hu, hv, hstat⟩ :=
    exists_kkt_from_lagrange f g A b hf hg hslater hx.2 c hc hminL
  exact ⟨c, u, v, y, hc, hu, hv, hstat, hcomp⟩

end CKMA
