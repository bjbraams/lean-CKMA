/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Data.EReal.Operations
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Sequences

import CKMA.Analysis.Convex.Clarke.Representation

/-!
# Clarke directional derivatives and generalized gradients

The generalized directional derivative takes a joint limsup as the base point approaches the
given point and the positive step tends to zero. It takes values in the extended reals.
The generalized gradient consists of continuous linear functionals bounded above by this
directional derivative in every direction.

For a finite-dimensional real space and a function Lipschitz on a neighborhood, the gradient is
the closed convex hull of limits of ordinary derivatives. Rademacher's theorem, the fundamental
theorem along lines, and separation in the dual identify that hull with the subdifferential.
On any real normed space, the support
function of the generalized gradient of a locally Lipschitz function is the generalized
directional derivative. Source: GAPS 12.50.

The support-function proof builds a real sublinear function from the directional derivative and
extends a partial functional dominated by it, using Mathlib's Hahn–Banach theorem
`exists_extension_of_le_sublinear`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology Set Metric
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Clarke's generalized directional derivative, with a joint limit in base point and
positive step size. Extended reals avoid totalizing an unbounded real limsup. -/
def clarkeDirectionalDerivative (f : E → ℝ) (x d : E) : EReal :=
  limsup (fun p : E × ℝ ↦ (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal))
    (𝓝[Set.univ ×ˢ Set.Ioi 0] (x, 0))

/-- The Clarke generalized gradient in the continuous dual. -/
def clarkeSubdifferential (f : E → ℝ) (x : E) : Set (StrongDual ℝ E) :=
  {u | ∀ d : E, (u d : EReal) ≤ clarkeDirectionalDerivative f x d}

/-- Limits of ordinary derivatives at differentiability points approaching `x`. -/
def reachableDerivatives (f : E → ℝ) (x : E) : Set (StrongDual ℝ E) :=
  {u | ∃ y : ℕ → E, Tendsto y atTop (𝓝 x) ∧
    (∀ n, DifferentiableAt ℝ f (y n)) ∧
    Tendsto (fun n ↦ fderiv ℝ f (y n)) atTop (𝓝 u)}

/-- Difference quotient of `f` at base point `p.1` with positive step `p.2`, in direction `d`. -/
def clarkeQuotient (f : E → ℝ) (d : E) (p : E × ℝ) : ℝ :=
  (f (p.1 + p.2 • d) - f p.1) / p.2

/-- Neighborhoods of `(x, 0)` that retain only strictly positive steps. -/
def clarkeStepNhds (x : E) : Filter (E × ℝ) :=
  𝓝[Set.univ ×ˢ Set.Ioi 0] (x, 0)

/-- The positive-step filter is nontrivial: `(x, 0)` lies in the closure of `{t > 0}`. -/
instance clarkeStepNhds_neBot (x : E) : (clarkeStepNhds x).NeBot := by
  rw [clarkeStepNhds, ← mem_closure_iff_nhdsWithin_neBot, closure_prod_eq, closure_univ,
    closure_Ioi]
  exact mem_prod.mpr ⟨mem_univ x, le_rfl⟩

/-- The quotient in direction `d₁ + d₂` splits into successive increments of `d₁` and `d₂`. -/
lemma clarkeQuotient_add (f : E → ℝ) (d₁ d₂ : E) (p : E × ℝ) :
    clarkeQuotient f (d₁ + d₂) p =
      clarkeQuotient f d₁ p + clarkeQuotient f d₂ (p.1 + p.2 • d₁, p.2) := by
  unfold clarkeQuotient
  have hsm : p.1 + p.2 • (d₁ + d₂) = p.1 + p.2 • d₁ + p.2 • d₂ := by
    rw [smul_add, add_assoc]
  have hfst : (p.1 + p.2 • d₁, p.2).1 = p.1 + p.2 • d₁ := rfl
  have hsnd : (p.1 + p.2 • d₁, p.2).2 = p.2 := rfl
  rw [hsm, hfst, hsnd, ← add_div]
  refine congrArg (fun t : ℝ ↦ t / p.2) ?_
  set a : ℝ := f (p.1 + p.2 • d₁ + p.2 • d₂)
  set b : ℝ := f (p.1 + p.2 • d₁)
  set c : ℝ := f p.1
  have hsum : (a - b) + (b - c) = a - c := sub_add_sub_cancel a b c
  exact ((add_comm (b - c) (a - b)).trans hsum).symm

/-- Rescaling the direction by a nonzero scalar rescales the step in the quotient. -/
lemma clarkeQuotient_smul {c : ℝ} (hc : c ≠ 0) (f : E → ℝ) (d : E) (p : E × ℝ) :
    clarkeQuotient f (c • d) p = c * clarkeQuotient f d (p.1, c * p.2) := by
  unfold clarkeQuotient
  have hsm : p.2 • (c • d) = (c * p.2) • d := by rw [smul_smul, mul_comm]
  rw [hsm]
  set a : ℝ := f (p.1 + (c * p.2) • d) - f p.1
  rw [← mul_div_assoc, mul_div_mul_left a p.2 hc]

/-- The quotient in the zero direction vanishes for every step. -/
lemma clarkeQuotient_zero (f : E → ℝ) (p : E × ℝ) : clarkeQuotient f 0 p = 0 := by
  simp [clarkeQuotient]

omit [NormedSpace ℝ E] in
/-- Multiplying the step by `c > 0` preserves the positive-step filter. -/
lemma tendsto_clarkeRescale {c : ℝ} (hc : 0 < c) (x : E) :
    Tendsto (fun p : E × ℝ ↦ (p.1, c * p.2)) (clarkeStepNhds x) (clarkeStepNhds x) := by
  unfold clarkeStepNhds
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hcont : Continuous (fun p : E × ℝ ↦ (p.1, c * p.2)) :=
      continuous_fst.prodMk ((continuous_const_mul c).comp continuous_snd)
    have hnhds : Tendsto (fun p : E × ℝ ↦ (p.1, c * p.2)) (𝓝 (x, 0)) (𝓝 (x, 0)) := by
      simpa using hcont.tendsto (x, 0)
    exact hnhds.mono_left nhdsWithin_le_nhds
  · refine eventually_nhdsWithin_of_forall fun p hp ↦ ?_
    simp only [mem_prod, mem_univ, true_and, mem_Ioi] at hp ⊢
    exact mul_pos hc hp

omit [NormedSpace ℝ E] in
/-- Positive rescaling of the step induces the identity on the positive-step filter. -/
lemma map_clarkeRescale {c : ℝ} (hc : 0 < c) (x : E) :
    map (fun p : E × ℝ ↦ (p.1, c * p.2)) (clarkeStepNhds x) = clarkeStepNhds x := by
  set ρ : ℝ → E × ℝ → E × ℝ := fun a p ↦ (p.1, a * p.2)
  have hright : ρ c ∘ ρ c⁻¹ = id := by
    funext p
    ext
    · rfl
    · dsimp [ρ]
      rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  have h1 : map (ρ c) (clarkeStepNhds x) ≤ clarkeStepNhds x := tendsto_clarkeRescale hc x
  have h2 : map (ρ c⁻¹) (clarkeStepNhds x) ≤ clarkeStepNhds x :=
    tendsto_clarkeRescale (inv_pos.mpr hc) x
  refine le_antisymm h1 ?_
  calc clarkeStepNhds x
      = map id (clarkeStepNhds x) := map_id.symm
    _ = map (ρ c ∘ ρ c⁻¹) (clarkeStepNhds x) := by rw [hright]
    _ = map (ρ c) (map (ρ c⁻¹) (clarkeStepNhds x)) := by rw [← map_map]
    _ ≤ map (ρ c) (clarkeStepNhds x) := map_mono h2

/-- Shifting the base point by the current step in a fixed direction preserves the filter. -/
lemma tendsto_clarkeShift (d x : E) :
    Tendsto (fun p : E × ℝ ↦ (p.1 + p.2 • d, p.2)) (clarkeStepNhds x) (clarkeStepNhds x) := by
  unfold clarkeStepNhds
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hsmul : Continuous (fun p : E × ℝ ↦ p.2 • d) := continuous_snd.smul continuous_const
    have hcont : Continuous (fun p : E × ℝ ↦ (p.1 + p.2 • d, p.2)) :=
      (continuous_fst.add hsmul).prodMk continuous_snd
    have hnhds : Tendsto (fun p : E × ℝ ↦ (p.1 + p.2 • d, p.2)) (𝓝 (x, 0)) (𝓝 (x, 0)) := by
      simpa using hcont.tendsto (x, 0)
    exact hnhds.mono_left nhdsWithin_le_nhds
  · refine eventually_nhdsWithin_of_forall fun p hp ↦ ?_
    simpa [mem_prod, mem_Ioi] using hp

/-- Near `(x, 0)` with positive step, both sample points lie in the Lipschitz ball, so the
quotient is bounded by `L ‖d‖`. -/
lemma eventually_abs_clarkeQuotient_le {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Metric.ball x r)) (d : E) :
    ∀ᶠ p in clarkeStepNhds x, |clarkeQuotient f d p| ≤ (L : ℝ) * ‖d‖ := by
  set δ : ℝ := r / (2 * (1 + ‖d‖))
  have h1 : 0 < 1 + ‖d‖ := by linarith [norm_nonneg d]
  have hδ : 0 < δ := div_pos hr (mul_pos zero_lt_two h1)
  have hδmul : δ * (1 + ‖d‖) = r / 2 := by
    have hne : 1 + ‖d‖ ≠ 0 := ne_of_gt h1
    simp only [δ]
    field_simp [hne]
  have hδr : δ * (1 + ‖d‖) < r := by rw [hδmul]; linarith
  have hδ_lt_r : δ < r := by
    calc
      δ = δ * 1 := by ring
      _ ≤ δ * (1 + ‖d‖) := mul_le_mul_of_nonneg_left (by linarith [norm_nonneg d]) hδ.le
      _ = r / 2 := hδmul
      _ < r := by linarith
  rw [clarkeStepNhds, eventually_nhdsWithin_iff]
  refine eventually_of_mem (U := Metric.ball x δ ×ˢ Metric.ball (0 : ℝ) δ) ?_ ?_
  · rw [nhds_prod_eq]
    exact prod_mem_prod (ball_mem_nhds _ hδ) (ball_mem_nhds _ hδ)
  · intro p hp hs
    simp only [mem_prod, mem_ball, dist_eq_norm] at hp
    rw [sub_zero] at hp
    have ht0 : 0 < p.2 := by simpa [mem_prod, mem_Ioi] using hs
    have htδ : p.2 < δ := by
      rw [Real.norm_eq_abs, abs_of_pos ht0] at hp
      exact hp.2
    have hy : ‖p.1 - x‖ < δ := hp.1
    have hy_ball : p.1 ∈ Metric.ball x r := by
      rw [mem_ball, dist_eq_norm]
      exact hy.trans hδ_lt_r
    have hz_lt : ‖p.1 + p.2 • d - x‖ < r := by
      calc
        ‖p.1 + p.2 • d - x‖ = ‖(p.1 - x) + p.2 • d‖ := by rw [add_sub_right_comm]
        _ ≤ ‖p.1 - x‖ + ‖p.2 • d‖ := norm_add_le _ _
        _ < δ + p.2 * ‖d‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
          exact add_lt_add_left hy (p.2 * ‖d‖)
        _ ≤ δ + δ * ‖d‖ :=
          add_le_add_right (mul_le_mul_of_nonneg_right htδ.le (norm_nonneg d)) δ
        _ = δ * (1 + ‖d‖) := by ring
        _ < r := hδr
    have hz_ball : p.1 + p.2 • d ∈ Metric.ball x r := by
      rw [mem_ball, dist_eq_norm]
      exact hz_lt
    have hLip : |f (p.1 + p.2 • d) - f p.1| ≤ (L : ℝ) * (p.2 * ‖d‖) := by
      have hdist := hf.dist_le_mul (p.1 + p.2 • d) hz_ball p.1 hy_ball
      rw [Real.dist_eq] at hdist
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at hdist
      exact hdist
    rw [clarkeQuotient, abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
    calc
      |f (p.1 + p.2 • d) - f p.1| ≤ (L : ℝ) * (p.2 * ‖d‖) := hLip
      _ = (L : ℝ) * ‖d‖ * p.2 := by ring

/-- On a Lipschitz ball the Clarke derivative is finite and lies in `[-L‖d‖, L‖d‖]`. -/
lemma clarkeDirectionalDerivative_mem_Icc {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Metric.ball x r)) (d : E) :
    clarkeDirectionalDerivative f x d ∈
      Icc ((-((L : ℝ) * ‖d‖) : ℝ) : EReal) (((L : ℝ) * ‖d‖ : ℝ) : EReal) := by
  have h := eventually_abs_clarkeQuotient_le hr hf d
  have hle : ∀ᶠ p in clarkeStepNhds x,
      (clarkeQuotient f d p : EReal) ≤ (((L : ℝ) * ‖d‖ : ℝ) : EReal) :=
    h.mono fun _ hp ↦ EReal.coe_le_coe (abs_le.mp hp).2
  have hge : ∀ᶠ p in clarkeStepNhds x,
      (((-((L : ℝ) * ‖d‖) : ℝ) : EReal)) ≤ (clarkeQuotient f d p : EReal) :=
    h.mono fun _ hp ↦ EReal.coe_le_coe (abs_le.mp hp).1
  rw [clarkeDirectionalDerivative]
  have hfun : (fun p : E × ℝ ↦ (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal)) =
      fun p ↦ (clarkeQuotient f d p : EReal) := rfl
  rw [hfun]
  refine ⟨?_, ?_⟩
  · exact le_limsup_of_frequently_le hge.frequently
  · exact limsup_le_of_le (h := hle)

/-- Real limsup of the Clarke quotient. It agrees with the extended-real derivative once the
quotient is locally bounded. -/
def clarkeReal (f : E → ℝ) (x d : E) : ℝ :=
  limsup (clarkeQuotient f d) (clarkeStepNhds x)

/-- The Clarke quotient is eventually bounded above by the Lipschitz constant. -/
lemma clarkeQuotient_boundedAbove {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Metric.ball x r)) (d : E) :
    IsBoundedUnder (· ≤ ·) (clarkeStepNhds x) (clarkeQuotient f d) :=
  ⟨(L : ℝ) * ‖d‖,
    (eventually_abs_clarkeQuotient_le hr hf d).mono fun _ h ↦ (abs_le.mp h).2⟩

/-- The Clarke quotient is eventually bounded below by the negative Lipschitz constant. -/
lemma clarkeQuotient_boundedBelow {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Metric.ball x r)) (d : E) :
    IsBoundedUnder (· ≥ ·) (clarkeStepNhds x) (clarkeQuotient f d) :=
  ⟨-((L : ℝ) * ‖d‖),
    (eventually_abs_clarkeQuotient_le hr hf d).mono fun _ h ↦ (abs_le.mp h).1⟩

/-- Local boundedness below makes the Clarke quotient cobounded for real limsup lemmas. -/
lemma clarkeQuotient_cobounded {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Metric.ball x r)) (d : E) :
    IsCoboundedUnder (· ≤ ·) (clarkeStepNhds x) (clarkeQuotient f d) :=
  (clarkeQuotient_boundedBelow hr hf d).isCoboundedUnder_le

/-- The extended-real Clarke derivative is the coercion of its real limsup. -/
lemma clarkeDirectionalDerivative_eq_coe_clarkeReal {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r)
    {L : ℝ≥0} (hf : LipschitzOnWith L f (Metric.ball x r)) (d : E) :
    clarkeDirectionalDerivative f x d = clarkeReal f x d := by
  rw [clarkeDirectionalDerivative, clarkeReal]
  have hfun : (fun p : E × ℝ ↦ (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal)) =
      (fun t : ℝ ↦ (t : EReal)) ∘ clarkeQuotient f d := rfl
  rw [hfun]
  exact (EReal.coe_strictMono.monotone.map_limsup_of_continuousAt (clarkeQuotient f d)
    continuous_coe_real_ereal.continuousAt (clarkeQuotient_boundedAbove hr hf d)
    (clarkeQuotient_cobounded hr hf d)).symm

/-- The Clarke derivative of the zero direction is zero. -/
lemma clarkeReal_zero (f : E → ℝ) (x : E) : clarkeReal f x 0 = 0 := by
  have h0 : clarkeQuotient f 0 = fun _ ↦ (0 : ℝ) := by
    ext p
    exact clarkeQuotient_zero f p
  rw [clarkeReal, h0, limsup_const]

/-- The real Clarke derivative is bounded by the Lipschitz constant. -/
lemma clarkeReal_abs_le {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Metric.ball x r)) (d : E) :
    |clarkeReal f x d| ≤ (L : ℝ) * ‖d‖ := by
  rw [abs_le, clarkeReal]
  refine ⟨?_, ?_⟩
  · exact le_limsup_of_frequently_le
      ((eventually_abs_clarkeQuotient_le hr hf d).frequently.mono fun _ h ↦ (abs_le.mp h).1)
      (clarkeQuotient_boundedAbove hr hf d)
  · exact limsup_le_of_le (clarkeQuotient_cobounded hr hf d)
      ((eventually_abs_clarkeQuotient_le hr hf d).mono fun _ h ↦ (abs_le.mp h).2)

/-- The real Clarke derivative is positively homogeneous. -/
lemma clarkeReal_smul {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Metric.ball x r)) {c : ℝ} (hc : 0 < c) (d : E) :
    clarkeReal f x (c • d) = c * clarkeReal f x d := by
  set ρ : E × ℝ → E × ℝ := fun p ↦ (p.1, c * p.2)
  have hmap : map ρ (clarkeStepNhds x) = clarkeStepNhds x := map_clarkeRescale hc x
  have hpoint : ∀ p, clarkeQuotient f (c • d) p = c * clarkeQuotient f d (ρ p) :=
    fun p ↦ clarkeQuotient_smul hc.ne' f d p
  rw [clarkeReal, clarkeReal, limsup_congr (Eventually.of_forall hpoint)]
  have hcomp : limsup (fun p ↦ c * clarkeQuotient f d (ρ p)) (clarkeStepNhds x) =
      limsup (fun p ↦ c * clarkeQuotient f d p) (clarkeStepNhds x) := by
    have hform : (fun p ↦ c * clarkeQuotient f d (ρ p)) =
        (fun p ↦ c * clarkeQuotient f d p) ∘ ρ := rfl
    rw [hform, limsup_comp, hmap]
  rw [hcomp]
  have hmono : Monotone (fun t : ℝ ↦ c * t) :=
    fun _ _ hab ↦ mul_le_mul_of_nonneg_left hab hc.le
  exact (hmono.map_limsup_of_continuousAt (clarkeQuotient f d)
    (continuous_const_mul c).continuousAt (clarkeQuotient_boundedAbove hr hf d)
    (clarkeQuotient_cobounded hr hf d)).symm

/-- The real Clarke derivative is subadditive. -/
lemma clarkeReal_add {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Metric.ball x r)) (d₁ d₂ : E) :
    clarkeReal f x (d₁ + d₂) ≤ clarkeReal f x d₁ + clarkeReal f x d₂ := by
  let shift : E × ℝ → E × ℝ := fun p ↦ (p.1 + p.2 • d₁, p.2)
  have htend : Tendsto shift (clarkeStepNhds x) (clarkeStepNhds x) := tendsto_clarkeShift d₁ x
  have hpoint : ∀ p, clarkeQuotient f (d₁ + d₂) p =
      clarkeQuotient f d₁ p + clarkeQuotient f d₂ (shift p) :=
    fun p ↦ clarkeQuotient_add f d₁ d₂ p
  rw [clarkeReal, clarkeReal, clarkeReal, limsup_congr (Eventually.of_forall hpoint)]
  let u : E × ℝ → ℝ := clarkeQuotient f d₁
  let v : E × ℝ → ℝ := fun p ↦ clarkeQuotient f d₂ (shift p)
  have hu_ge : IsBoundedUnder (· ≥ ·) (clarkeStepNhds x) u :=
    clarkeQuotient_boundedBelow hr hf d₁
  have hu_le : IsBoundedUnder (· ≤ ·) (clarkeStepNhds x) u :=
    clarkeQuotient_boundedAbove hr hf d₁
  have hv_ge : IsBoundedUnder (· ≥ ·) (clarkeStepNhds x) v :=
    htend.isBoundedUnder_comp (clarkeQuotient_boundedBelow hr hf d₂)
  have hv_le : IsBoundedUnder (· ≤ ·) (clarkeStepNhds x) v :=
    htend.isBoundedUnder_comp (clarkeQuotient_boundedAbove hr hf d₂)
  have hv_co : IsCoboundedUnder (· ≤ ·) (clarkeStepNhds x) v := hv_ge.isCoboundedUnder_le
  refine le_trans (limsup_add_le hu_ge hu_le hv_co hv_le) ?_
  refine add_le_add_right ?_ (limsup u (clarkeStepNhds x))
  exact htend.limsup_comp_le_limsup hv_co (clarkeQuotient_boundedAbove hr hf d₂)

/-- A scalar multiple of the derivative lies below the derivative of the scaled direction. -/
lemma clarkeReal_smul_le {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Metric.ball x r)) (c : ℝ) (d : E) :
    c * clarkeReal f x d ≤ clarkeReal f x (c • d) := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have hadd := clarkeReal_add hr hf (c • d) ((-c) • d)
    have hsum : c • d + (-c) • d = 0 := by rw [← add_smul, add_neg_cancel, zero_smul]
    rw [hsum, clarkeReal_zero] at hadd
    have hpos := clarkeReal_smul hr hf (neg_pos.mpr hc) d
    have : -(clarkeReal f x ((-c) • d)) ≤ clarkeReal f x (c • d) := by linarith
    rw [hpos, neg_mul, neg_neg] at this
    exact this
  · simp [clarkeReal_zero, zero_smul]
  · exact le_of_eq (clarkeReal_smul hr hf hc d).symm

set_option backward.isDefEq.respectTransparency false in
/-- Hahn–Banach supplies a continuous linear functional in the subdifferential that attains the
directional derivative at `d`. -/
lemma exists_mem_clarkeSubdifferential_eq_clarkeReal {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r)
    {L : ℝ≥0} (hf : LipschitzOnWith L f (Metric.ball x r)) (d : E) :
    ∃ u : StrongDual ℝ E, u ∈ clarkeSubdifferential f x ∧ u d = clarkeReal f x d := by
  have H : ∀ c : ℝ, c • d = 0 → c • clarkeReal f x d = 0 := by
    intro c hc
    by_cases hc0 : c = 0
    · simp [hc0]
    · have hd0 : d = 0 := by
        calc
          d = (c⁻¹ * c) • d := by rw [inv_mul_cancel₀ hc0, one_smul]
          _ = c⁻¹ • (c • d) := by rw [mul_smul]
          _ = 0 := by simp [hc]
      simp [hd0, clarkeReal_zero]
  let fp : E →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' d (clarkeReal f x d) H
  have hdom : ∀ y : fp.domain, fp y ≤ clarkeReal f x (y : E) := by
    rintro ⟨y, hy⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [LinearPMap.mkSpanSingleton'_apply]
    simp only [RingHom.id_apply, smul_eq_mul]
    exact clarkeReal_smul_le hr hf c d
  obtain ⟨g, hg_eq, hg_le⟩ := exists_extension_of_le_sublinear fp (clarkeReal f x)
    (fun c hc y ↦ clarkeReal_smul hr hf hc y) (fun y z ↦ clarkeReal_add hr hf y z) hdom
  have hbound : ∀ y, ‖g y‖ ≤ (L : ℝ) * ‖y‖ := by
      intro y
      rw [Real.norm_eq_abs, abs_le]
      refine ⟨?_, ?_⟩
      · have hneg := hg_le (-y)
        rw [map_neg] at hneg
        have hpy : clarkeReal f x (-y) ≤ (L : ℝ) * ‖y‖ := by
          simpa [norm_neg] using (abs_le.mp (clarkeReal_abs_le hr hf (-y))).2
        linarith
      · exact (hg_le y).trans (abs_le.mp (clarkeReal_abs_le hr hf y)).2
  let u := g.mkContinuous ((L : ℝ)) hbound
  refine ⟨u, ?_, ?_⟩
  · intro e
    rw [clarkeDirectionalDerivative_eq_coe_clarkeReal hr hf e, LinearMap.mkContinuous_apply]
    exact EReal.coe_le_coe (hg_le e)
  · rw [LinearMap.mkContinuous_apply]
    have hd : d ∈ fp.domain := by
      unfold fp
      rw [LinearPMap.domain_mkSpanSingleton]
      exact Submodule.mem_span_singleton_self d
    rw [← congrArg g (fp.domain.coe_mk d hd), hg_eq]
    unfold fp
    rw [LinearPMap.mkSpanSingleton'_apply_self]

/-- A limit of derivatives at points tending to `x` lies in the Clarke subdifferential. -/
lemma reachableDerivatives_subset_clarkeSubdifferential
    {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (ball x r)) :
    reachableDerivatives f x ⊆ clarkeSubdifferential f x := by
  intro u hu d
  obtain ⟨y, hy, hdiff, htend⟩ := hu
  rw [clarkeDirectionalDerivative_eq_coe_clarkeReal hr hf d, EReal.coe_le_coe_iff]
  have hstep : ∀ n : ℕ, ∃ t : ℝ, 0 < t ∧ t < 1 / ((n : ℝ) + 1) ∧
      |clarkeQuotient f d (y n, t) - (fderiv ℝ f (y n)) d| < 1 / ((n : ℝ) + 1) := by
    intro n
    have hpath : HasDerivAt (fun t : ℝ => y n + t • d) d 0 := by
      simpa [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add (y n)
    have hF : HasFDerivAt f (fderiv ℝ f (y n)) (y n + (0 : ℝ) • d) := by
      simpa [zero_smul, add_zero] using (hdiff n).hasFDerivAt
    have hhas := hF.comp_hasDerivAt 0 hpath
    have hslope : Tendsto (fun t : ℝ => (f (y n + t • d) - f (y n)) / t) (𝓝[>] (0 : ℝ))
        (𝓝 ((fderiv ℝ f (y n)) d)) := by
      simpa [zero_add, zero_smul, add_zero, div_eq_inv_mul, smul_eq_mul] using
        hhas.tendsto_slope_zero_right
    have hε : 0 < 1 / ((n : ℝ) + 1) := div_pos one_pos (by linarith)
    have hclose : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        |(f (y n + t • d) - f (y n)) / t - (fderiv ℝ f (y n)) d| <
          1 / ((n : ℝ) + 1) := by
      simpa [Real.dist_eq] using Metric.tendsto_nhds.mp hslope _ hε
    have hsmall : ball (0 : ℝ) (1 / ((n : ℝ) + 1)) ∩ Ioi 0 ∈ 𝓝[>] (0 : ℝ) :=
      inter_mem (nhdsWithin_le_nhds (ball_mem_nhds _ hε)) self_mem_nhdsWithin
    obtain ⟨t, htset, htclose⟩ :=
      ((eventually_of_mem hsmall fun _ ht => ht).and hclose).exists
    rw [mem_inter_iff, mem_ball, mem_Ioi, dist_eq_norm, sub_zero, Real.norm_eq_abs] at htset
    have ht0 : 0 < t := htset.2
    rw [abs_of_pos ht0] at htset
    exact ⟨t, ht0, htset.1, by simpa [clarkeQuotient] using htclose⟩
  let t : ℕ → ℝ := fun n => (hstep n).choose
  have ht : ∀ n, 0 < t n ∧ t n < 1 / ((n : ℝ) + 1) ∧
      |clarkeQuotient f d (y n, t n) - (fderiv ℝ f (y n)) d| < 1 / ((n : ℝ) + 1) :=
    fun n => (hstep n).choose_spec
  let p : ℕ → E × ℝ := fun n => (y n, t n)
  have hp0 : Tendsto (fun n => t n) atTop (𝓝 (0 : ℝ)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_pos (ht n).1]
    exact (ht n).2.1.le
  have hptend : Tendsto p atTop (clarkeStepNhds x) := by
    rw [clarkeStepNhds, tendsto_nhdsWithin_iff]
    refine ⟨hy.prodMk_nhds hp0, ?_⟩
    exact Eventually.of_forall fun n => by simp [p, mem_prod, mem_Ioi, (ht n).1]
  have hpair : Tendsto (fun n => (fderiv ℝ f (y n)) d) atTop (𝓝 (u d)) := by
    have hcomp := ((ContinuousLinearMap.apply ℝ ℝ d).continuous.tendsto u).comp htend
    refine Tendsto.congr (f₁ := ⇑(ContinuousLinearMap.apply ℝ ℝ d) ∘
      fun n => fderiv ℝ f (y n)) (fun n => ?_) hcomp
    rw [Function.comp_apply]
    exact ContinuousLinearMap.apply_apply (𝕜 := ℝ) (Fₗ' := ℝ) d (fderiv ℝ f (y n))
  have hgap : Tendsto (fun n => |clarkeQuotient f d (p n) - (fderiv ℝ f (y n)) d|)
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) (fun n => (ht n).2.2.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hq : Tendsto (clarkeQuotient f d ∘ p) atTop (𝓝 (u d)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    filter_upwards [Metric.tendsto_nhds.mp hpair (ε / 2) hε2,
      Metric.tendsto_nhds.mp hgap (ε / 2) hε2] with n hn1 hn2
    rw [Real.dist_eq] at hn1 hn2 ⊢
    rw [sub_zero, abs_of_nonneg (abs_nonneg _)] at hn2
    rw [Function.comp_apply]
    have htri := dist_triangle (clarkeQuotient f d (p n)) ((fderiv ℝ f (y n)) d) (u d)
    rw [Real.dist_eq, Real.dist_eq, Real.dist_eq] at htri
    linarith
  have hlow : ∀ᶠ n in atTop, u d - 1 ≤ (clarkeQuotient f d ∘ p) n := by
    filter_upwards [Metric.tendsto_nhds.mp hq 1 one_pos] with n hn
    rw [Real.dist_eq] at hn
    rw [Function.comp_apply] at hn ⊢
    linarith [(abs_lt.mp hn).1]
  have hcob : (map p atTop).IsCoboundedUnder (· ≤ ·) (clarkeQuotient f d) := by
    simpa [IsCoboundedUnder, map_map] using
      isCoboundedUnder_le_of_eventually_le (f := clarkeQuotient f d ∘ p) atTop hlow
  have hup := hptend.limsup_comp_le_limsup hcob (clarkeQuotient_boundedAbove hr hf d)
  rw [hq.limsup_eq] at hup
  exact hup

/-- Every Clarke subgradient of a Lipschitz function is bounded by the Lipschitz constant. -/
lemma norm_le_of_mem_clarkeSubdifferential
    {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (ball x r)) {u : StrongDual ℝ E}
    (hu : u ∈ clarkeSubdifferential f x) : ‖u‖ ≤ (L : ℝ) := by
  refine u.opNorm_le_bound (NNReal.coe_nonneg L) fun d => ?_
  rw [Real.norm_eq_abs, abs_le]
  have hder (e : E) : u e ≤ clarkeReal f x e := by
    have h := hu e
    rw [clarkeDirectionalDerivative_eq_coe_clarkeReal hr hf e, EReal.coe_le_coe_iff] at h
    exact h
  refine ⟨?_, (hder d).trans (abs_le.mp (clarkeReal_abs_le hr hf d)).2⟩
  have hneg := hder (-d)
  rw [map_neg] at hneg
  have habs := (abs_le.mp (clarkeReal_abs_le hr hf (-d))).2
  rw [norm_neg] at habs
  linarith

/-- The Clarke subdifferential of a Lipschitz function is closed. -/
lemma isClosed_clarkeSubdifferential
    {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (ball x r)) : IsClosed (clarkeSubdifferential f x) := by
  have hEq : clarkeSubdifferential f x =
      ⋂ d : E, {u : StrongDual ℝ E | u d ≤ clarkeReal f x d} := by
    ext u
    rw [clarkeSubdifferential, mem_iInter]
    constructor
    · intro hu d
      have h := hu d
      rwa [clarkeDirectionalDerivative_eq_coe_clarkeReal hr hf d, EReal.coe_le_coe_iff] at h
    · intro hu d
      rw [clarkeDirectionalDerivative_eq_coe_clarkeReal hr hf d]
      exact EReal.coe_le_coe (hu d)
  rw [hEq]
  exact isClosed_iInter fun d =>
    isClosed_Iic.preimage (ContinuousLinearMap.apply ℝ ℝ d).continuous

/-- The Clarke subdifferential of a Lipschitz function is convex. -/
lemma convex_clarkeSubdifferential
    {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (ball x r)) : Convex ℝ (clarkeSubdifferential f x) := by
  intro u hu v hv a b ha hb hab d
  have hder (w : StrongDual ℝ E) (hw : w ∈ clarkeSubdifferential f x) :
      w d ≤ clarkeReal f x d := by
    have h := hw d
    rw [clarkeDirectionalDerivative_eq_coe_clarkeReal hr hf d, EReal.coe_le_coe_iff] at h
    exact h
  rw [clarkeDirectionalDerivative_eq_coe_clarkeReal hr hf d, EReal.coe_le_coe_iff]
  rw [add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
  have hpa : a * u d ≤ a * clarkeReal f x d := mul_le_mul_of_nonneg_left (hder u hu) ha
  have hqb : b * v d ≤ b * clarkeReal f x d := mul_le_mul_of_nonneg_left (hder v hv) hb
  calc
    a * u d + b * v d ≤ a * clarkeReal f x d + b * clarkeReal f x d := add_le_add hpa hqb
    _ = clarkeReal f x d := by rw [← add_mul, hab, one_mul]

/-- In finite dimensions the Clarke subdifferential of a Lipschitz function is compact. -/
lemma isCompact_clarkeSubdifferential [FiniteDimensional ℝ E]
    {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (ball x r)) : IsCompact (clarkeSubdifferential f x) := by
  have : FiniteDimensional ℝ (StrongDual ℝ E) := finiteDimensional_strongDual
  refine (isCompact_closedBall (0 : StrongDual ℝ E) (L : ℝ)).of_isClosed_subset
    (isClosed_clarkeSubdifferential hr hf) ?_
  intro u hu
  rw [mem_closedBall, dist_zero_right]
  exact norm_le_of_mem_clarkeSubdifferential hr hf hu

/-- Pairings of reachable derivatives against a fixed direction are bounded above. -/
lemma bddAbove_reachable_pairing
    {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (ball x r)) (d : E) :
    BddAbove ((fun u : StrongDual ℝ E => u d) '' reachableDerivatives f x) := by
  have hRsub := reachableDerivatives_subset_clarkeSubdifferential hr hf
  refine ⟨(L : ℝ) * ‖d‖, ?_⟩
  rintro a ⟨u, hu, rfl⟩
  have hnorm := norm_le_of_mem_clarkeSubdifferential hr hf (hRsub hu)
  calc
    u d ≤ |u d| := le_abs_self _
    _ ≤ ‖u‖ * ‖d‖ := by rw [← Real.norm_eq_abs]; exact u.le_opNorm d
    _ ≤ (L : ℝ) * ‖d‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

/-- The support function of the reachable derivatives is the Clarke directional derivative. -/
lemma sSup_reachableDerivatives_eq_clarkeReal [FiniteDimensional ℝ E]
    {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (ball x r)) (d : E) :
    sSup ((fun u : StrongDual ℝ E => u d) '' reachableDerivatives f x) =
      clarkeReal f x d := by
  have hRsub := reachableDerivatives_subset_clarkeSubdifferential hr hf
  obtain ⟨u0, y0, hy0, hdiff0, htend0, -⟩ := exists_tendsto_fderiv_of_lipschitzOn hr hf
  have hRne : (reachableDerivatives f x).Nonempty := ⟨u0, y0, hy0, hdiff0, htend0⟩
  have hbdd := bddAbove_reachable_pairing hr hf d
  set α : ℝ := sSup ((fun u : StrongDual ℝ E => u d) '' reachableDerivatives f x)
  have hαle : α ≤ clarkeReal f x d := by
    refine csSup_le (hRne.image fun u => u d) ?_
    rintro a ⟨u, hu, rfl⟩
    have h := hRsub hu d
    rw [clarkeDirectionalDerivative_eq_coe_clarkeReal hr hf d, EReal.coe_le_coe_iff] at h
    exact h
  have hle : clarkeReal f x d ≤ α := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hgrad : ∃ ρ, 0 < ρ ∧ ρ ≤ r ∧ ∀ y ∈ ball x ρ, DifferentiableAt ℝ f y →
        (fderiv ℝ f y) d ≤ α + ε := by
      by_contra hno
      have hex : ∀ ρ, 0 < ρ → ρ ≤ r → ∃ y, y ∈ ball x ρ ∧ DifferentiableAt ℝ f y ∧
          α + ε < (fderiv ℝ f y) d := by
        intro ρ hρ0 hρle
        by_contra hy
        have hy' : ∀ y ∈ ball x ρ, DifferentiableAt ℝ f y → (fderiv ℝ f y) d ≤ α + ε := by
          intro y hyb hdiff
          by_contra hgt
          exact hy ⟨y, hyb, hdiff, lt_of_not_ge hgt⟩
        exact hno ⟨ρ, hρ0, hρle, hy'⟩
      have hyn : ∀ n : ℕ, ∃ y : E, y ∈ ball x (min (r / 2) (1 / ((n : ℝ) + 1))) ∧
          DifferentiableAt ℝ f y ∧ α + ε < (fderiv ℝ f y) d := by
        intro n
        have hpos : 0 < min (r / 2) (1 / ((n : ℝ) + 1)) :=
          lt_min (div_pos hr zero_lt_two) (div_pos one_pos (by linarith))
        have hleρ : min (r / 2) (1 / ((n : ℝ) + 1)) ≤ r :=
          (min_le_left _ _).trans (half_le_self hr.le)
        exact hex _ hpos hleρ
      let y : ℕ → E := fun n => (hyn n).choose
      have hy : ∀ n : ℕ, y n ∈ ball x (min (r / 2) (1 / ((n : ℝ) + 1))) ∧
          DifferentiableAt ℝ f (y n) ∧ α + ε < (fderiv ℝ f (y n)) d :=
        fun n => (hyn n).choose_spec
      have hball : ∀ n, y n ∈ ball x r := fun n =>
        ball_subset_ball ((min_le_left _ _).trans (half_le_self hr.le)) (hy n).1
      have hfy : ∀ n, ‖fderiv ℝ f (y n)‖ ≤ (L : ℝ) := fun n =>
        norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds (hball n)) hf
      have : FiniteDimensional ℝ (StrongDual ℝ E) := finiteDimensional_strongDual
      obtain ⟨u, -, φ, hφ, hφtend⟩ :=
        (isCompact_closedBall (0 : StrongDual ℝ E) (L : ℝ)).tendsto_subseq fun n => by
          simpa [mem_closedBall, dist_zero_right] using hfy n
      have hytend : Tendsto (y ∘ φ) atTop (𝓝 x) := by
        rw [tendsto_iff_dist_tendsto_zero]
        refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
          tendsto_one_div_add_atTop_nhds_zero_nat
        have hdist : dist (y (φ n)) x < 1 / ((φ n : ℝ) + 1) :=
          lt_of_lt_of_le (mem_ball.mp (hy (φ n)).1) (min_le_right _ _)
        have hden : (n : ℝ) + 1 ≤ (φ n : ℝ) + 1 :=
          add_le_add_left (Nat.cast_le.mpr hφ.le_apply) 1
        have hdiv : 1 / ((φ n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
          one_div_le_one_div_of_le (by linarith) hden
        exact (hdist.trans_le hdiv).le
      have huR : u ∈ reachableDerivatives f x :=
        ⟨y ∘ φ, hytend, fun n => (hy (φ n)).2.1, hφtend⟩
      have hudle : u d ≤ α := le_csSup hbdd ⟨u, huR, rfl⟩
      have hpair : Tendsto (fun n => (fderiv ℝ f (y (φ n))) d) atTop (𝓝 (u d)) := by
        have hcomp :=
          ((ContinuousLinearMap.apply ℝ ℝ d).continuous.tendsto u).comp hφtend
        refine Tendsto.congr (f₁ := ⇑(ContinuousLinearMap.apply ℝ ℝ d) ∘
          fun n => fderiv ℝ f (y (φ n))) (fun n => ?_) hcomp
        rw [Function.comp_apply]
        exact ContinuousLinearMap.apply_apply (𝕜 := ℝ) (Fₗ' := ℝ) d
          (fderiv ℝ f (y (φ n)))
      have hge : α + ε ≤ u d :=
        ge_of_tendsto hpair (Eventually.of_forall fun n => ((hy (φ n)).2.2).le)
      linarith
    obtain ⟨ρ, hρ, hρr, hgrad⟩ := hgrad
    have hq := differenceQuotient_eventually_le_of_fderiv_le hf hρ hρr hgrad
    exact limsup_le_of_le (clarkeQuotient_cobounded hr hf d) hq
  exact le_antisymm hαle hle

/-- **12.50**: the finite-dimensional Clarke gradient is the closed convex hull of
reachable derivatives and is nonempty compact convex. Local Lipschitz control is
stated on one neighbourhood, not assumed globally. -/
theorem clarkeSubdifferential_representation [FiniteDimensional ℝ E]
    {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Metric.ball x r)) :
    (clarkeSubdifferential f x).Nonempty ∧ IsCompact (clarkeSubdifferential f x) ∧
      Convex ℝ (clarkeSubdifferential f x) ∧
      clarkeSubdifferential f x = closure (convexHull ℝ (reachableDerivatives f x)) := by
  have hRne : (reachableDerivatives f x).Nonempty := by
    obtain ⟨u, y, hy, hdiff, htend, -⟩ := exists_tendsto_fderiv_of_lipschitzOn hr hf
    exact ⟨u, y, hy, hdiff, htend⟩
  have hRsub := reachableDerivatives_subset_clarkeSubdifferential hr hf
  have hclosed := isClosed_clarkeSubdifferential hr hf
  have hconv := convex_clarkeSubdifferential hr hf
  have hcompact := isCompact_clarkeSubdifferential hr hf
  set R := reachableDerivatives f x
  set K := closure (convexHull ℝ R)
  have hKsub : K ⊆ clarkeSubdifferential f x :=
    closure_minimal (convexHull_min hRsub hconv) hclosed
  have hKconv : Convex ℝ K := (convex_convexHull ℝ R).closure
  have hKne : K.Nonempty := by
    obtain ⟨u, hu⟩ := hRne
    exact ⟨u, subset_closure ((subset_convexHull ℝ R) hu)⟩
  have hsupK : ∀ d : E,
      sSup ((fun u : StrongDual ℝ E => u d) '' K) = clarkeReal f x d := by
    intro d
    have hbdd := bddAbove_reachable_pairing hr hf d
    have hs := sSup_image_closure_convexHull_eq
      (φ := ContinuousLinearMap.apply ℝ ℝ d) hRne hbdd
    have hs' : sSup ((fun u : StrongDual ℝ E => u d) '' closure (convexHull ℝ R)) =
        sSup ((fun u : StrongDual ℝ E => u d) '' reachableDerivatives f x) := hs
    rw [sSup_reachableDerivatives_eq_clarkeReal hr hf d] at hs'
    simpa [K] using hs'
  refine ⟨?_, hcompact, hconv, ?_⟩
  · obtain ⟨u, hu⟩ := hRne
    exact ⟨u, hRsub hu⟩
  · refine Subset.antisymm ?_ hKsub
    intro u hu
    by_contra huK
    obtain ⟨ψ, c, hψ, hcu⟩ :=
      geometric_hahn_banach_closed_point hKconv isClosed_closure huK
    obtain ⟨d, hd⟩ := exists_strongDual_eq_apply ψ
    have hsuple : sSup ((fun v : StrongDual ℝ E => v d) '' K) ≤ c := by
      apply csSup_le (hKne.image fun v => v d)
      rintro a ⟨v, hv, rfl⟩
      have hvd : v d < c := by
        rw [← hd v]
        exact hψ v hv
      exact hvd.le
    rw [hsupK d] at hsuple
    have hud : u d ≤ clarkeReal f x d := by
      have h := hu d
      rw [clarkeDirectionalDerivative_eq_coe_clarkeReal hr hf d, EReal.coe_le_coe_iff] at h
      exact h
    have hcu' : c < u d := by
      rw [← hd u]
      exact hcu
    linarith [hud.trans hsuple]

/-- The support function of the generalized gradient is the generalized directional derivative.
Local Lipschitz control is the regularity hypothesis; finite dimensionality is not required. -/
theorem sSup_clarkeSubdifferential_eq
    {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Metric.ball x r)) (d : E) :
    ((sSup ((fun u ↦ u d) '' clarkeSubdifferential f x) : ℝ) : EReal) =
      clarkeDirectionalDerivative f x d := by
  obtain ⟨u, hu, hud⟩ := exists_mem_clarkeSubdifferential_eq_clarkeReal hr hf d
  have hder := clarkeDirectionalDerivative_eq_coe_clarkeReal hr hf d
  set S := (fun v : StrongDual ℝ E ↦ v d) '' clarkeSubdifferential f x
  have hle : ∀ a ∈ S, a ≤ clarkeReal f x d := by
    rintro a ⟨v, hv, rfl⟩
    have hv' := hv d
    rw [hder] at hv'
    exact EReal.coe_le_coe_iff.mp hv'
  have hne : S.Nonempty := ⟨u d, mem_image_of_mem _ hu⟩
  have hbdd : BddAbove S := ⟨clarkeReal f x d, hle⟩
  have hmem : clarkeReal f x d ∈ S := by
    rw [← hud]
    exact mem_image_of_mem (fun v ↦ v d) hu
  have hsup : sSup S = clarkeReal f x d :=
    le_antisymm (csSup_le hne hle) (le_csSup hbdd hmem)
  rw [hsup]
  exact hder.symm

end CKMA
