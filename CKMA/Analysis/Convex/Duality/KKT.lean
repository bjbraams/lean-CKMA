/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Convex.Duality.Sum
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Order.OrderClosed

/-!
# Slater's condition and subgradient KKT multipliers

Strict feasibility produces nonnegative inequality multipliers and an equality multiplier
so that the Lagrangian is stationary on the affine constraint and complementary slackness
holds. The argument separates the slack set from the open negative orthant, normalizes by
the positive objective weight, and reads stationarity from the sum rule: the indicator of
the affine fiber is the unqualified summand, and the Lagrangian carries the continuity.
Sources: Boyd–Vandenberghe, *Convex Optimization*, §§5.5 and 5.9; GAPS 12.40.
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

/-- A real-valued function has convex epigraph after coercion to `EReal`. -/
private lemma convex_epigraph_coe {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    Convex ℝ {p : E × ℝ | (f p.1 : EReal) ≤ p.2} := by
  have hset : {p : E × ℝ | (f p.1 : EReal) ≤ p.2} =
      {p : E × ℝ | f p.1 ≤ p.2} := by
    ext p
    simp [EReal.coe_le_coe_iff]
  rw [hset]
  simpa using hf.convex_epigraph

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
    (convex_epigraph_coe hf) (convex_epigraph_coe hg)
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

/-- A nonnegative combination of convex functions is convex. -/
private lemma convexOn_weighted_sum {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (g : Fin n → E → ℝ) (hg : ∀ i, ConvexOn ℝ Set.univ (g i)) :
    ConvexOn ℝ Set.univ (fun z => ∑ i, c i * g i z) := by
  induction n with
  | zero =>
    have hfun : (fun z : E => ∑ i : Fin 0, c i * g i z) = fun _ => (0 : ℝ) := by
      ext z
      simp
    rw [hfun]
    exact convexOn_const 0 convex_univ
  | succ n ih =>
    let f1 : E → ℝ := fun z => c 0 * g 0 z
    let f2 : E → ℝ := fun z => ∑ i : Fin n, c i.succ * g i.succ z
    have hf1 : ConvexOn ℝ Set.univ f1 := by
      simpa [f1, smul_eq_mul] using (hg 0).smul (hc 0)
    have hf2 : ConvexOn ℝ Set.univ f2 :=
      ih (fun i => c i.succ) (fun i => hc i.succ) (fun i => g i.succ) (fun i => hg i.succ)
    have hfun : (fun z => ∑ i, c i * g i z) = f1 + f2 := by
      ext z
      simp [f1, f2, Fin.sum_univ_succ]
    rw [hfun]
    exact hf1.add hf2

/-- A subgradient of a weighted sum splits into scaled subgradients. -/
private lemma exists_subdifferential_weighted_sum [FiniteDimensional ℝ E] {n : ℕ}
    (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i) (g : Fin n → E → ℝ) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    {x : E} {w : StrongDual ℝ E}
    (hw : w ∈ TauCeti.subdifferential (dualPairing E)
      (fun z => ((∑ i, c i * g i z : ℝ) : EReal)) x) :
    ∃ v : Fin n → StrongDual ℝ E,
      (∀ i, v i ∈ TauCeti.subdifferential (dualPairing E)
        (fun z => (g i z : EReal)) x) ∧
      w = ∑ i, c i • v i := by
  induction n generalizing w with
  | zero =>
    have hw0 : w ∈ TauCeti.subdifferential (dualPairing E)
        (fun _ : E => ((0 : ℝ) : EReal)) x := by
      simpa using hw
    rw [subdifferential_zero_fun] at hw0
    simp only [Set.mem_singleton_iff] at hw0
    subst hw0
    refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
    simp
  | succ n ih =>
    let f1 : E → ℝ := fun z => c 0 * g 0 z
    let f2 : E → ℝ := fun z => ∑ i : Fin n, c i.succ * g i.succ z
    have hfun : (fun z => ((∑ i, c i * g i z : ℝ) : EReal)) =
        fun z => ((f1 z + f2 z : ℝ) : EReal) := by
      funext z
      exact congrArg (fun r : ℝ => (r : EReal)) (by simp [f1, f2, Fin.sum_univ_succ])
    rw [hfun] at hw
    have hf1 : ConvexOn ℝ Set.univ f1 := by
      simpa [f1, smul_eq_mul] using (hg 0).smul (hc 0)
    have hf2 : ConvexOn ℝ Set.univ f2 :=
      convexOn_weighted_sum (fun i => c i.succ) (fun i => hc i.succ)
        (fun i => g i.succ) (fun i => hg i.succ)
    rw [subdifferential_add_coe hf1 hf2 x] at hw
    obtain ⟨w1, hw1, w2, hw2, hwadd⟩ := Set.mem_add.mp hw
    rw [subdifferential_const_mul (hc 0) (hg 0) x] at hw1
    obtain ⟨v0, hv0, hv0eq⟩ := Set.mem_smul_set.mp hw1
    have hw2' : w2 ∈ TauCeti.subdifferential (dualPairing E)
        (fun z => ((∑ i : Fin n, c i.succ * g i.succ z : ℝ) : EReal)) x := by
      simpa [f2] using hw2
    obtain ⟨vrest, hvrest, hvsum⟩ :=
      ih (fun i => c i.succ) (fun i => hc i.succ) (fun i => g i.succ)
        (fun i => hg i.succ) hw2'
    refine ⟨Fin.cons v0 vrest, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · simpa [Fin.cons_zero] using hv0
      · intro j
        simpa [Fin.cons_succ] using hvrest j
    · rw [← hwadd, ← hv0eq, hvsum, Fin.sum_univ_succ]
      simp [Fin.cons_zero, Fin.cons_succ]

/-- A subgradient of the Lagrangian splits into objective and constraint subgradients. -/
private lemma exists_subdifferential_lagrangian [FiniteDimensional ℝ E] {n : ℕ}
    (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i) (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (g : Fin n → E → ℝ) (hg : ∀ i, ConvexOn ℝ Set.univ (g i)) {x : E}
    {w : StrongDual ℝ E}
    (hw : w ∈ TauCeti.subdifferential (dualPairing E)
      (fun z => ((f z + ∑ i, c i * g i z : ℝ) : EReal)) x) :
    ∃ u : StrongDual ℝ E, ∃ v : Fin n → StrongDual ℝ E,
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
private lemma fst_combo {n : ℕ} (a d : ℝ) (p q : (Fin n → ℝ) × ℝ) (i : Fin n) :
    (a • p + d • q).1 i = a * p.1 i + d * q.1 i := by
  rw [Prod.fst_add, Prod.smul_fst, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
    Pi.smul_apply, smul_eq_mul, smul_eq_mul]

/-- Second coordinate of a convex combination in the slack space. -/
private lemma snd_combo {n : ℕ} (a d : ℝ) (p q : (Fin n → ℝ) × ℝ) :
    (a • p + d • q).2 = a * p.2 + d * q.2 := by
  rw [Prod.snd_add, Prod.smul_snd, Prod.smul_snd, smul_eq_mul, smul_eq_mul]

/-- Separation against the negative orthant produces the KKT weights. -/
private lemma exists_kkt_weights {m n : ℕ} (f : E → ℝ) (g : Fin n → E → ℝ)
    (A : E →L[ℝ] (Fin m → ℝ)) (b : Fin m → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hslater : ∃ x₀, A x₀ = b ∧ ∀ i, g i x₀ < 0) {x : E}
    (hx : (∀ i, g i x ≤ 0) ∧ A x = b)
    (hmin : ∀ z, (∀ i, g i z ≤ 0) → A z = b → f x ≤ f z) :
    ∃ c : Fin n → ℝ, (∀ i, 0 ≤ c i) ∧ (∀ i, c i * g i x = 0) ∧
      ∀ z, A z = b →
        f x + ∑ i, c i * g i x ≤ f z + ∑ i, c i * g i z := by
  let P := (Fin n → ℝ) × ℝ
  let U : Set P := {p | (∀ i, p.1 i < 0) ∧ p.2 < 0}
  let S : Set P := {p | ∃ z : E, A z = b ∧ (∀ i, g i z ≤ p.1 i) ∧ f z - f x ≤ p.2}
  have hUopen : IsOpen U := by
    have h1 : IsOpen {p : P | ∀ i, p.1 i < 0} := by
      have hset : {p : P | ∀ i, p.1 i < 0} = ⋂ i, {p : P | p.1 i < 0} := by
        ext p
        simp
      rw [hset]
      refine isOpen_iInter_of_finite fun i => ?_
      exact isOpen_lt ((continuous_apply i).comp continuous_fst) continuous_const
    have h2 : IsOpen {p : P | p.2 < 0} :=
      isOpen_lt continuous_snd continuous_const
    have hU : U = {p : P | ∀ i, p.1 i < 0} ∩ {p : P | p.2 < 0} := by
      ext p
      simp [U]
    rw [hU]
    exact h1.inter h2
  have hUconv : Convex ℝ U := by
    intro p hp q hq a d ha hd had
    rw [Set.mem_ofPred] at hp hq ⊢
    refine ⟨fun i => ?_, ?_⟩
    · have hpi : p.1 i < 0 := hp.1 i
      have hqi : q.1 i < 0 := hq.1 i
      rw [fst_combo]
      rcases eq_or_lt_of_le ha with ha0 | ha0
      · have hd1 : d = 1 := by linarith
        rw [← ha0, hd1, zero_mul, one_mul, zero_add]
        exact hqi
      · rcases eq_or_lt_of_le hd with hd0 | hd0
        · have ha1 : a = 1 := by linarith
          rw [← hd0, ha1, zero_mul, one_mul, add_zero]
          exact hpi
        · have hpa : a * p.1 i < 0 := mul_neg_of_pos_of_neg ha0 hpi
          have hqd : d * q.1 i < 0 := mul_neg_of_pos_of_neg hd0 hqi
          linarith
    · rw [snd_combo]
      rcases eq_or_lt_of_le ha with ha0 | ha0
      · have hd1 : d = 1 := by linarith
        rw [← ha0, hd1, zero_mul, one_mul, zero_add]
        exact hq.2
      · rcases eq_or_lt_of_le hd with hd0 | hd0
        · have ha1 : a = 1 := by linarith
          rw [← hd0, ha1, zero_mul, one_mul, add_zero]
          exact hp.2
        · nlinarith [hp.2, hq.2]
  have hSconv : Convex ℝ S := by
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
      have hz' : f z ≤ f x + p.2 := by linarith
      have hw' : f w ≤ f x + q.2 := by linarith
      have hsum : a * f z + d * f w ≤ f x + (a * p.2 + d * q.2) := by
        have hcomb : a * f z + d * f w ≤ a * (f x + p.2) + d * (f x + q.2) := by
          gcongr
        have hident : a * (f x + p.2) + d * (f x + q.2) =
            f x + (a * p.2 + d * q.2) := by
          have hrewrite : a * (f x + p.2) + d * (f x + q.2) =
              (a + d) * f x + a * p.2 + d * q.2 := by ring
          rw [hrewrite, had, one_mul, add_assoc]
        linarith
      have hgoal : a * f z + d * f w - f x ≤ a * p.2 + d * q.2 := by
        linarith
      calc
        f (a • z + d • w) - f x ≤ a * f z + d * f w - f x := by
          simpa [smul_eq_mul] using sub_le_sub_right hfv (f x)
        _ ≤ a * p.2 + d * q.2 := hgoal
        _ = (a • p + d • q).2 := by rw [snd_combo]
  have hdisj : Disjoint U S := by
    rw [Set.disjoint_left]
    intro p hpU hpS
    rw [Set.mem_ofPred] at hpU hpS
    obtain ⟨z, hzA, hzg, hzf⟩ := hpS
    have hfeas : ∀ i, g i z ≤ 0 := fun i =>
      le_of_lt (lt_of_le_of_lt (hzg i) (hpU.1 i))
    have hbetter : f z < f x := by linarith [hzf, hpU.2]
    exact (not_le_of_gt hbetter) (hmin z hfeas hzA)
  obtain ⟨sep, level, hUsep, hSsep⟩ :=
    geometric_hahn_banach_open hUconv hUopen hSconv hdisj
  have h0S : ((0 : Fin n → ℝ), (0 : ℝ)) ∈ S := by
    refine ⟨x, hx.2, ?_, ?_⟩
    · intro i
      simpa using hx.1 i
    · simp
  have hlevel : level ≤ 0 := by
    have h0 := hSsep _ h0S
    rw [← Prod.zero_eq_mk, map_zero] at h0
    exact h0
  let slope := sep.comp (inl ℝ (Fin n → ℝ) ℝ)
  let multMap := sep.comp (inr ℝ (Fin n → ℝ) ℝ)
  let mult : ℝ := multMap 1
  have hsep_apply (p : P) : sep p = slope p.1 + p.2 * mult := by
    have hsplit := comp_inl_add_comp_inr sep p
    have hmul : multMap p.2 = p.2 * mult := by
      have hmap : toSpanSingleton ℝ (multMap 1) = multMap :=
        toSpanSingleton_apply_map_one (c := multMap)
      rw [← hmap, toSpanSingleton_apply, smul_eq_mul]
    linarith
  let weight : Fin n → ℝ := fun i => slope (Pi.single i 1)
  have hslope (s : Fin n → ℝ) : slope s = ∑ i, weight i * s i := by
    calc
      slope s = slope (∑ i, s i • Pi.single i 1) := by
        congr 1
        exact pi_eq_sum_univ' s
      _ = ∑ i, slope (s i • Pi.single i 1) := map_sum _ _ _
      _ = ∑ i, s i * slope (Pi.single i 1) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, smul_eq_mul]
      _ = ∑ i, weight i * s i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_comm]
  have hweight (i : Fin n) (r : ℝ) : slope (Pi.single i r) = weight i * r := by
    rw [hslope, Finset.sum_eq_single i]
    · simp [Pi.single_eq_same, mul_comm]
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  have hweight_nonneg : ∀ i, 0 ≤ weight i := by
    intro i
    by_contra hlt
    have hlt' : weight i < 0 := lt_of_not_ge hlt
    set r : ℝ := (1 - level) / (-weight i) with hrdef
    have hrpos : 0 < r := div_pos (by linarith) (by linarith)
    have hmem : (Pi.single i r, (0 : ℝ)) ∈ S := by
      refine ⟨x, hx.2, ?_, ?_⟩
      · intro j
        by_cases hji : j = i
        · rw [hji]
          simp [Pi.single_eq_same]
          linarith [hx.1 i, hrpos]
        · simp [Pi.single_eq_of_ne hji, hx.1 j]
      · simp
    have hle := hSsep _ hmem
    have hcalc : sep (Pi.single i r, (0 : ℝ)) = r * weight i := by
      rw [hsep_apply, hweight, zero_mul, add_zero, mul_comm]
    have hrw : r * weight i = level - 1 := by
      have hwne : weight i ≠ 0 := hlt'.ne
      rw [hrdef, div_mul_eq_mul_div, mul_div_assoc, div_neg, div_self hwne]
      ring
    linarith
  have horth (r : ℝ) : sep ((0 : Fin n → ℝ), r) = r * mult := by
    rw [hsep_apply, hslope]
    simp
  have hmult_nonneg : 0 ≤ mult := by
    by_contra hlt
    have hlt' : mult < 0 := lt_of_not_ge hlt
    set r : ℝ := (1 - level) / (-mult) with hrdef
    have hrpos : 0 < r := div_pos (by linarith) (by linarith)
    have hmem : ((0 : Fin n → ℝ), r) ∈ S := by
      refine ⟨x, hx.2, ?_, ?_⟩
      · intro i
        simpa using hx.1 i
      · linarith
    have hle := hSsep _ hmem
    have hrw : r * mult = level - 1 := by
      have hmne : mult ≠ 0 := hlt'.ne
      rw [hrdef, div_mul_eq_mul_div, mul_div_assoc, div_neg, div_self hmne]
      ring
    linarith [horth r]
  have hsep_neg (ε : ℝ) : sep (fun _ : Fin n => -ε, -ε) =
      -ε * (∑ i, weight i + mult) := by
    rw [hsep_apply, hslope]
    have hsum : ∑ i, weight i * (-ε) = -ε * ∑ i, weight i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hsum]
    ring
  have hUneg (ε : ℝ) (hε : 0 < ε) : (fun _ : Fin n => -ε, -ε) ∈ U := by
    refine ⟨fun i => ?_, neg_lt_zero.mpr hε⟩
    simpa using (neg_lt_zero.mpr hε)
  let sigma : ℝ := ∑ i, weight i + mult
  have hsigma_nonneg : 0 ≤ sigma := by
    have hsum : 0 ≤ ∑ i, weight i := Finset.sum_nonneg fun i _ => hweight_nonneg i
    linarith
  have hsigma_pos : 0 < sigma := by
    by_contra hle
    have hzero : sigma = 0 := le_antisymm (le_of_not_gt hle) hsigma_nonneg
    have hlt := hUsep _ (hUneg 1 one_pos)
    rw [hsep_neg 1] at hlt
    have hsum0 : ∑ i, weight i + mult = 0 := by simpa [sigma] using hzero
    rw [hsum0, mul_zero] at hlt
    linarith
  have hlevel0 : level = 0 := by
    apply le_antisymm hlevel
    by_contra hlt
    have hlt' : level < 0 := lt_of_not_ge hlt
    set ε : ℝ := -level / (2 * sigma) with hεdef
    have hεpos : 0 < ε := div_pos (by linarith) (by positivity)
    have hltU := hUsep _ (hUneg ε hεpos)
    rw [hsep_neg ε] at hltU
    have hval : -ε * sigma = level / 2 := by
      rw [hεdef]
      field_simp
    linarith
  obtain ⟨x₀, hx₀A, hx₀g⟩ := hslater
  have hmult_pos : 0 < mult := by
    by_contra hle
    have hzero : mult = 0 := le_antisymm (le_of_not_gt hle) hmult_nonneg
    have hmem : ((fun i => g i x₀), f x₀ - f x) ∈ S :=
      ⟨x₀, hx₀A, fun _ => le_rfl, le_rfl⟩
    have hge := hSsep _ hmem
    rw [hlevel0, hsep_apply, hslope, hzero, mul_zero, add_zero] at hge
    have hterm : ∀ i, weight i * g i x₀ ≤ 0 := fun i =>
      mul_nonpos_of_nonneg_of_nonpos (hweight_nonneg i) (hx₀g i).le
    have hsumle : ∑ i, weight i * g i x₀ ≤ 0 :=
      Finset.sum_nonpos fun i _ => hterm i
    have hsum0 : ∑ i, weight i * g i x₀ = 0 := le_antisymm hsumle hge
    have hterms : ∀ i ∈ Finset.univ, 0 ≤ -(weight i * g i x₀) := fun i _ =>
      neg_nonneg.mpr (hterm i)
    have hsumneg : ∑ i, -(weight i * g i x₀) = 0 := by
      rw [Finset.sum_neg_distrib, hsum0, neg_zero]
    have hzero_term := (Finset.sum_eq_zero_iff_of_nonneg hterms).1 hsumneg
    have hweight0 : ∀ i, weight i = 0 := by
      intro i
      have hi : weight i * g i x₀ = 0 := by linarith [hzero_term i (Finset.mem_univ i)]
      exact (mul_eq_zero.mp hi).resolve_right (hx₀g i).ne
    have hsig : sigma = 0 := by simp [sigma, hweight0, hzero]
    exact hsigma_pos.ne' hsig
  let c : Fin n → ℝ := fun i => weight i / mult
  have hc : ∀ i, 0 ≤ c i := fun i => div_nonneg (hweight_nonneg i) hmult_pos.le
  have hweight_c (i : Fin n) : weight i = c i * mult := by
    simp [c]
    field_simp
  have hlag_ge : ∀ z, A z = b → 0 ≤ ∑ i, c i * g i z + (f z - f x) := by
    intro z hz
    have hmem : ((fun i => g i z), f z - f x) ∈ S :=
      ⟨z, hz, fun _ => le_rfl, le_rfl⟩
    have hge := hSsep _ hmem
    rw [hlevel0, hsep_apply, hslope] at hge
    have hrew : ∑ i, weight i * g i z = mult * ∑ i, c i * g i z := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hweight_c i]
      ring
    have hnonneg : 0 ≤ mult * (∑ i, c i * g i z + (f z - f x)) := by
      have hident : ∑ i, weight i * g i z + (f z - f x) * mult =
          mult * (∑ i, c i * g i z + (f z - f x)) := by
        rw [hrew]
        ring
      linarith
    exact (mul_le_mul_iff_of_pos_left hmult_pos).mp (by simpa using hnonneg)
  have hcomp : ∀ i, c i * g i x = 0 := by
    have hsumge : 0 ≤ ∑ i, c i * g i x := by
      have hge := hlag_ge x hx.2
      simp at hge
      exact hge
    have hterm : ∀ i, c i * g i x ≤ 0 := fun i =>
      mul_nonpos_of_nonneg_of_nonpos (hc i) (hx.1 i)
    have hsumle : ∑ i, c i * g i x ≤ 0 := Finset.sum_nonpos fun i _ => hterm i
    have hsum0 : ∑ i, c i * g i x = 0 := le_antisymm hsumle hsumge
    have hterms : ∀ i ∈ Finset.univ, 0 ≤ -(c i * g i x) := fun i _ =>
      neg_nonneg.mpr (hterm i)
    have hsumneg : ∑ i, -(c i * g i x) = 0 := by
      rw [Finset.sum_neg_distrib, hsum0, neg_zero]
    have hzero_term := (Finset.sum_eq_zero_iff_of_nonneg hterms).1 hsumneg
    intro i
    linarith [hzero_term i (Finset.mem_univ i)]
  refine ⟨c, hc, hcomp, ?_⟩
  intro z hz
  have hsum0 : ∑ i, c i * g i x = 0 := Finset.sum_eq_zero fun i _ => hcomp i
  linarith [hlag_ge z hz]

/-- Minimizing the Lagrangian on the affine fiber produces KKT subgradients. -/
private lemma exists_kkt_from_lagrange [FiniteDimensional ℝ E] {m n : ℕ}
    (f : E → ℝ) (g : Fin n → E → ℝ)
    (A : E →L[ℝ] (Fin m → ℝ)) (b : Fin m → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hslater : ∃ x₀, A x₀ = b ∧ ∀ i, g i x₀ < 0) {x : E} (hxA : A x = b)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hminL : ∀ z, A z = b →
      f x + ∑ i, c i * g i x ≤ f z + ∑ i, c i * g i z) :
    ∃ u : StrongDual ℝ E, ∃ v : Fin n → StrongDual ℝ E,
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
    simpa [ell] using convex_epigraph_coe hlag_conv
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
theorem exists_convexKKTMultipliers_of_slater [FiniteDimensional ℝ E] {m n : ℕ}
    (f : E → ℝ)
    (g : Fin n → E → ℝ) (A : E →L[ℝ] (Fin m → ℝ)) (b : Fin m → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hslater : ∃ x₀, A x₀ = b ∧ ∀ i, g i x₀ < 0) {x : E}
    (hx : (∀ i, g i x ≤ 0) ∧ A x = b)
    (hmin : ∀ z, (∀ i, g i z ≤ 0) → A z = b → f x ≤ f z) :
    ∃ (c : Fin n → ℝ) (u : StrongDual ℝ E) (v : Fin n → StrongDual ℝ E)
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
