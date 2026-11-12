/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Group.ContinuousDiv
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Newton iteration and Kantorovich convergence

The Newton step uses the totalized inverse of the Fréchet derivative. Convergence statements
supply invertibility on the relevant iterates rather than assuming the totalized inverse always
behaves as an inverse.

The Kantorovich radius includes the affine `L=0` limit. The scalar field is real or complex.
The semilocal statement uses a normalized derivative Lipschitz bound and differentiability on an
open neighborhood of the majorant ball; the local statement gives quadratic convergence near a
regular zero. The initial step length is controlled by a norm bound. Source: GAPS 35.9.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped NNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The majorant root, including the affine `L=0` limit. -/
def kantorovichRadius (L η : ℝ) : ℝ :=
  if L = 0 then η else (1 - Real.sqrt (1 - 2 * L * η)) / L

/-- One Newton step, using Mathlib's totalized operator inverse. Results assert invertibility
on the relevant region; the definition does not invent an inverse when one is unavailable. -/
def newtonStep (F : E → E) (x : E) : E := x - (fderiv 𝕜 F x).inverse (F x)

/-- Newton iterates starting at `x₀`, indexed with the initial guess at zero.
The scalar is supplied explicitly because it does not appear in the iteration type. -/
def newtonIterate (F : E → E) (x₀ : E) (n : ℕ) : E := (newtonStep (𝕜 := 𝕜) F)^[n] x₀

/-- The zeroth iterate is the initial point. -/
@[simp]
theorem newtonIterate_zero (F : E → E) (x₀ : E) : newtonIterate (𝕜 := 𝕜) F x₀ 0 = x₀ := rfl

/-- The successor iterate takes one further Newton step. -/
theorem newtonIterate_succ (F : E → E) (x₀ : E) (n : ℕ) :
    newtonIterate (𝕜 := 𝕜) F x₀ (n + 1) =
      newtonStep (𝕜 := 𝕜) F (newtonIterate (𝕜 := 𝕜) F x₀ n) := by
  exact Function.iterate_succ_apply' _ _ _

/-- Quadratic Kantorovich majorant `φ(t) = (L / 2) * t ^ 2 - t + η`. -/
private def kantorovichQuadratic (L η t : ℝ) : ℝ := (L / 2) * t ^ 2 - t + η

/-- Scalar Newton sequence for `kantorovichQuadratic`, starting at `0`. -/
private def kantorovichMajorant (L η : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      kantorovichMajorant L η n +
        kantorovichQuadratic L η (kantorovichMajorant L η n) /
          (1 - L * kantorovichMajorant L η n)

/-- The majorant sequence begins at zero. -/
@[simp]
private lemma kantorovichMajorant_zero (L η : ℝ) : kantorovichMajorant L η 0 = 0 := rfl

/-- Each later majorant term is one Newton step of the quadratic. -/
private lemma kantorovichMajorant_succ (L η : ℝ) (n : ℕ) :
    kantorovichMajorant L η (n + 1) =
      kantorovichMajorant L η n +
        kantorovichQuadratic L η (kantorovichMajorant L η n) /
          (1 - L * kantorovichMajorant L η n) := by
  simp [kantorovichMajorant]

/-- The first majorant step equals the initial residual bound. -/
private lemma kantorovichMajorant_one (L η : ℝ) : kantorovichMajorant L η 1 = η := by
  simp [kantorovichMajorant_succ, kantorovichQuadratic]

/-- The discriminant of the Kantorovich quadratic is positive. -/
private lemma kantorovich_discriminant_pos {L η : ℝ} (_hL : 0 ≤ L) (_hη : 0 ≤ η)
    (hsmall : L * η < 1 / 2) : 0 < 1 - 2 * L * η := by
  linarith [hsmall]

/-- The Kantorovich radius is nonnegative. -/
private lemma kantorovichRadius_nonneg {L η : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (_hsmall : L * η < 1 / 2) : 0 ≤ kantorovichRadius L η := by
  by_cases hL0 : L = 0
  · simp [kantorovichRadius, hL0, hη]
  · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    have hle : 1 - 2 * L * η ≤ 1 := by nlinarith [hL, hη]
    have hs : Real.sqrt (1 - 2 * L * η) ≤ 1 := Real.sqrt_le_one.mpr hle
    rw [kantorovichRadius, ite_eq_right hL0]
    exact div_nonneg (sub_nonneg.mpr hs) hLpos.le

/-- The radius stays strictly below the pole `1 / L` of the majorant. -/
private lemma kantorovichRadius_mul_lt_one {L η : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hsmall : L * η < 1 / 2) : L * kantorovichRadius L η < 1 := by
  by_cases hL0 : L = 0
  · simp [kantorovichRadius, hL0]
  · have hdisc : 0 < 1 - 2 * L * η := kantorovich_discriminant_pos hL hη hsmall
    have hs : 0 < Real.sqrt (1 - 2 * L * η) := Real.sqrt_pos.mpr hdisc
    have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    rw [kantorovichRadius, ite_eq_right hL0]
    calc
      L * ((1 - Real.sqrt (1 - 2 * L * η)) / L) = 1 - Real.sqrt (1 - 2 * L * η) := by
        field_simp
      _ < 1 := by linarith

/-- The quadratic majorant vanishes at the Kantorovich radius. -/
private lemma kantorovichQuadratic_radius {L η : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hsmall : L * η < 1 / 2) :
    kantorovichQuadratic L η (kantorovichRadius L η) = 0 := by
  by_cases hL0 : L = 0
  · simp [kantorovichQuadratic, kantorovichRadius, hL0]
  · have hdisc : 0 ≤ 1 - 2 * L * η := (kantorovich_discriminant_pos hL hη hsmall).le
    have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    set s := Real.sqrt (1 - 2 * L * η) with hsdef
    have hs : s ^ 2 = 1 - 2 * L * η := Real.sq_sqrt hdisc
    rw [kantorovichRadius, ite_eq_right hL0, ← hsdef, kantorovichQuadratic]
    have hnum : (1 - s) ^ 2 - 2 * (1 - s) + 2 * L * η = 0 := by
      rw [show (1 - s) ^ 2 - 2 * (1 - s) + 2 * L * η = s ^ 2 - 1 + 2 * L * η by ring, hs]
      ring
    have hden : 2 * L ≠ 0 := mul_ne_zero (by norm_num) hLpos.ne'
    refine mul_left_cancel₀ hden ?_
    rw [mul_zero]
    have ha : (2 * L) * ((L / 2) * ((1 - s) / L) ^ 2) = (1 - s) ^ 2 := by
      field_simp [hLpos.ne']
    have hb : (2 * L) * ((1 - s) / L) = 2 * (1 - s) := by field_simp [hLpos.ne']
    rw [mul_add, mul_sub, ha, hb, hnum]

/-- The initial residual bound does not exceed the radius. -/
private lemma kantorovichRadius_ge_eta {L η : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hsmall : L * η < 1 / 2) : η ≤ kantorovichRadius L η := by
  have hroot := kantorovichQuadratic_radius hL hη hsmall
  simp only [kantorovichQuadratic] at hroot
  set ρ := kantorovichRadius L η
  have hηeq : η = ρ - (L / 2) * ρ ^ 2 := by linarith
  have hρ : 0 ≤ ρ := kantorovichRadius_nonneg hL hη hsmall
  have hLρ : L * ρ < 1 := kantorovichRadius_mul_lt_one hL hη hsmall
  rw [hηeq]
  nlinarith [sq_nonneg ρ, mul_nonneg hL hρ]

/-- Factor `φ(t)` through the root at the Kantorovich radius. -/
private lemma kantorovichQuadratic_factor {L η t : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hsmall : L * η < 1 / 2) :
    kantorovichQuadratic L η t =
      (kantorovichRadius L η - t) *
        (1 - (L / 2) * (kantorovichRadius L η + t)) := by
  have hroot := kantorovichQuadratic_radius hL hη hsmall
  simp only [kantorovichQuadratic] at hroot ⊢
  set ρ := kantorovichRadius L η
  have hηeq : η = ρ - (L / 2) * ρ ^ 2 := by linarith
  rw [hηeq]
  ring

/-- The quadratic majorant is nonnegative on the segment from `0` to the radius. -/
private lemma kantorovichQuadratic_nonneg {L η t : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hsmall : L * η < 1 / 2) (_ht0 : 0 ≤ t) (ht : t ≤ kantorovichRadius L η) :
    0 ≤ kantorovichQuadratic L η t := by
  rw [kantorovichQuadratic_factor hL hη hsmall]
  set ρ := kantorovichRadius L η
  have hLρ : L * ρ < 1 := kantorovichRadius_mul_lt_one hL hη hsmall
  have hsecond : 0 ≤ 1 - (L / 2) * (ρ + t) := by
    have : (L / 2) * (ρ + t) ≤ L * ρ := by nlinarith [sq_nonneg ρ]
    linarith
  exact mul_nonneg (by linarith) hsecond

/-- The quadratic majorant is positive before the radius. -/
private lemma kantorovichQuadratic_pos {L η t : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hsmall : L * η < 1 / 2) (_ht0 : 0 ≤ t) (ht : t < kantorovichRadius L η) :
    0 < kantorovichQuadratic L η t := by
  rw [kantorovichQuadratic_factor hL hη hsmall]
  set ρ := kantorovichRadius L η
  have hLρ : L * ρ < 1 := kantorovichRadius_mul_lt_one hL hη hsmall
  have hhalf : (L / 2) * (ρ + t) < 1 := by
    by_cases hL0 : L = 0
    · simp [hL0]
    · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
      have hpos : 0 < L / 2 := div_pos hLpos (by norm_num)
      calc
        (L / 2) * (ρ + t) < (L / 2) * (ρ + ρ) :=
          mul_lt_mul_of_pos_left (by linarith) hpos
        _ = L * ρ := by ring
        _ < 1 := hLρ
  exact mul_pos (by linarith) (by linarith)

/-- One Newton step of the quadratic, starting in `[0, radius]`, remains at most the radius. -/
private lemma kantorovich_newton_le_radius {L η s : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hsmall : L * η < 1 / 2) (_hs0 : 0 ≤ s) (hs : s ≤ kantorovichRadius L η)
    (hden : 0 < 1 - L * s) :
    s + kantorovichQuadratic L η s / (1 - L * s) ≤ kantorovichRadius L η := by
  set ρ := kantorovichRadius L η
  have hφ := kantorovichQuadratic_factor (t := s) hL hη hsmall
  rw [hφ]
  have hsub : 0 ≤ ρ - s := by linarith
  have hcd : 1 - (L / 2) * (ρ + s) ≤ 1 - L * s := by nlinarith
  have hle : (ρ - s) * (1 - (L / 2) * (ρ + s)) / (1 - L * s) ≤ ρ - s := by
    rw [div_le_iff₀ hden]
    exact mul_le_mul_of_nonneg_left hcd hsub
  linarith

/-- A Newton step of a quadratic sends the value to half the squared increment. -/
private lemma kantorovichQuadratic_newton_sq {L η s : ℝ} (hden : 1 - L * s ≠ 0) :
    kantorovichQuadratic L η (s + kantorovichQuadratic L η s / (1 - L * s)) =
      (L / 2) * (kantorovichQuadratic L η s / (1 - L * s)) ^ 2 := by
  set d := 1 - L * s
  have hd : d ≠ 0 := hden
  have hshift : ∀ s h : ℝ, kantorovichQuadratic L η (s + h) =
      kantorovichQuadratic L η s + (L * s - 1) * h + (L / 2) * h ^ 2 := by
    intro s h
    unfold kantorovichQuadratic
    ring
  set step := kantorovichQuadratic L η s / d with hstep
  have hlin : (L * s - 1) * step = -kantorovichQuadratic L η s := by
    have hderiv : L * s - 1 = -d := by simp [d]
    rw [hderiv, hstep]
    field_simp [hd]
  rw [hshift, hlin]
  ring

/-- Bounds for the scalar majorant: it increases and stays in `[0, radius]`. -/
private lemma kantorovichMajorant_bounds {L η : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hsmall : L * η < 1 / 2) (n : ℕ) :
    0 ≤ kantorovichMajorant L η n ∧
      kantorovichMajorant L η n ≤ kantorovichRadius L η ∧
        0 < 1 - L * kantorovichMajorant L η n ∧
          kantorovichMajorant L η n ≤ kantorovichMajorant L η (n + 1) := by
  induction n with
  | zero =>
    refine ⟨le_rfl, kantorovichRadius_nonneg hL hη hsmall, by simp, ?_⟩
    simpa [kantorovichMajorant_one] using hη
  | succ n ih =>
    rcases ih with ⟨hs0, hsle, hden, hmono⟩
    set s := kantorovichMajorant L η n
    set u := kantorovichMajorant L η (n + 1)
    have hu : u = s + kantorovichQuadratic L η s / (1 - L * s) := by
      simpa [s, u] using kantorovichMajorant_succ L η n
    have hφ : 0 ≤ kantorovichQuadratic L η s :=
      kantorovichQuadratic_nonneg hL hη hsmall hs0 hsle
    have hu0 : 0 ≤ u := by
      rw [hu]
      exact add_nonneg hs0 (div_nonneg hφ hden.le)
    have hule : u ≤ kantorovichRadius L η := by
      rw [hu]
      exact kantorovich_newton_le_radius hL hη hsmall hs0 hsle hden
    have hdenu : 0 < 1 - L * u := by
      have hLρ : L * kantorovichRadius L η < 1 := kantorovichRadius_mul_lt_one hL hη hsmall
      have : L * u ≤ L * kantorovichRadius L η := mul_le_mul_of_nonneg_left hule hL
      linarith
    have hφu : 0 ≤ kantorovichQuadratic L η u :=
      kantorovichQuadratic_nonneg hL hη hsmall hu0 hule
    refine ⟨hu0, hule, hdenu, ?_⟩
    rw [kantorovichMajorant_succ]
    exact le_add_of_nonneg_right (div_nonneg hφu hdenu.le)

/-- The squared majorant increment reproduces the quadratic at the next term. -/
private lemma kantorovichMajorant_sq {L η : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hsmall : L * η < 1 / 2) (n : ℕ) :
    kantorovichQuadratic L η (kantorovichMajorant L η (n + 1)) =
      (L / 2) * (kantorovichMajorant L η (n + 1) - kantorovichMajorant L η n) ^ 2 := by
  have hden : 1 - L * kantorovichMajorant L η n ≠ 0 :=
    ((kantorovichMajorant_bounds hL hη hsmall n).2.2.1).ne'
  have hstep := kantorovichMajorant_succ L η n
  have hsq := kantorovichQuadratic_newton_sq (L := L) (η := η)
    (s := kantorovichMajorant L η n) hden
  rw [← hstep] at hsq
  convert hsq using 2
  have hsub : kantorovichMajorant L η (n + 1) - kantorovichMajorant L η n =
      kantorovichQuadratic L η (kantorovichMajorant L η n) /
        (1 - L * kantorovichMajorant L η n) := by
    rw [hstep]
    ring
  rw [hsub]

/-- The scalar majorant converges to the Kantorovich radius. -/
private lemma tendsto_kantorovichMajorant {L η : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hsmall : L * η < 1 / 2) :
    Tendsto (kantorovichMajorant L η) atTop (𝓝 (kantorovichRadius L η)) := by
  set t := kantorovichMajorant L η
  set ρ := kantorovichRadius L η
  have hmono : Monotone t := monotone_nat_of_le_succ fun n =>
    (kantorovichMajorant_bounds hL hη hsmall n).2.2.2
  have hbdd : BddAbove (Set.range t) := by
    refine ⟨ρ, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (kantorovichMajorant_bounds hL hη hsmall n).2.1
  have htend : Tendsto t atTop (𝓝 (⨆ n, t n)) := tendsto_atTop_ciSup hmono hbdd
  set s := ⨆ n, t n
  have hs_le : s ≤ ρ := ciSup_le fun n => (kantorovichMajorant_bounds hL hη hsmall n).2.1
  have hs0 : 0 ≤ s := by
    have h0 : t 0 ≤ s := le_ciSup hbdd 0
    simpa [t] using h0
  have hshift : Tendsto (fun n => t (n + 1)) atTop (𝓝 s) :=
    (tendsto_add_atTop_iff_nat 1).mpr htend
  have hdiff0 : Tendsto (fun n => t (n + 1) - t n) atTop (𝓝 0) := by
    simpa [sub_self] using hshift.sub htend
  have hden_tend : Tendsto (fun n => 1 - L * t n) atTop (𝓝 (1 - L * s)) :=
    tendsto_const_nhds.sub ((tendsto_const_nhds (x := L)).mul htend)
  have hden_lim : 0 < 1 - L * s := by
    have hLρ : L * ρ < 1 := kantorovichRadius_mul_lt_one hL hη hsmall
    have : L * s ≤ L * ρ := mul_le_mul_of_nonneg_left hs_le hL
    linarith
  have hφlim : Tendsto (fun n => kantorovichQuadratic L η (t n)) atTop
      (𝓝 (kantorovichQuadratic L η s)) := by
    have hcont : Continuous (kantorovichQuadratic L η) := by
      unfold kantorovichQuadratic
      fun_prop
    exact hcont.continuousAt.tendsto.comp htend
  have hquot : Tendsto (fun n => kantorovichQuadratic L η (t n) / (1 - L * t n)) atTop
      (𝓝 (kantorovichQuadratic L η s / (1 - L * s))) :=
    hφlim.div hden_tend hden_lim.ne'
  have hquot_eq : ∀ n, t (n + 1) - t n =
      kantorovichQuadratic L η (t n) / (1 - L * t n) := by
    intro n
    rw [show t (n + 1) = t n + kantorovichQuadratic L η (t n) / (1 - L * t n) from
      kantorovichMajorant_succ L η n]
    ring
  have hquot0 : kantorovichQuadratic L η s / (1 - L * s) = 0 := by
    have hrewrite : Tendsto (fun n => t (n + 1) - t n) atTop
        (𝓝 (kantorovichQuadratic L η s / (1 - L * s))) := by
      simpa [hquot_eq] using hquot
    exact tendsto_nhds_unique hrewrite hdiff0
  have hφ0 : kantorovichQuadratic L η s = 0 := by
    have hmul := congrArg (fun x => x * (1 - L * s)) hquot0
    simpa [hden_lim.ne'] using hmul
  have hs_eq : s = ρ := by
    rcases eq_or_lt_of_le hs_le with h | h
    · exact h
    · exact absurd hφ0 (kantorovichQuadratic_pos hL hη hsmall hs0 h).ne'
  simpa [s, hs_eq, ρ] using htend

/-- If an endomorphism is within distance less than `1` of the identity, it is invertible and the
inverse is bounded by the Neumann series. -/
private lemma isInvertible_of_norm_sub_id_lt [CompleteSpace E] {f : E →L[𝕜] E}
    (hf : ‖f - ContinuousLinearMap.id 𝕜 E‖ < 1) :
    f.IsInvertible ∧ ‖f.inverse‖ ≤ (1 - ‖f - ContinuousLinearMap.id 𝕜 E‖)⁻¹ := by
  let t : E →L[𝕜] E := ContinuousLinearMap.id 𝕜 E - f
  have ht : ‖t‖ < 1 := by simpa [t, norm_sub_rev] using hf
  have hf' : f = 1 - t := by
    simp only [t, ContinuousLinearMap.one_def, sub_sub_cancel]
  have hsum : Summable fun n : ℕ => ‖t‖ ^ n :=
    summable_geometric_of_lt_one (norm_nonneg _) ht
  have hpow : ∀ n, ‖t ^ n‖ ≤ ‖t‖ ^ n := by
    intro n
    cases n with
    | zero =>
      simpa [ContinuousLinearMap.one_def] using
        ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := E)
    | succ n => simpa [pow_succ] using norm_pow_le' t n.succ_pos
  have hsum_pow : Summable fun n : ℕ => ‖t ^ n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpow hsum
  have hleft : f ∘L (∑' n : ℕ, t ^ n) = ContinuousLinearMap.id 𝕜 E := by
    have hmul := mul_neg_geom_series t ht
    simpa [hf', ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def] using hmul
  have hright : (∑' n : ℕ, t ^ n) ∘L f = ContinuousLinearMap.id 𝕜 E := by
    have hmul := geom_series_mul_neg t ht
    simpa [hf', ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def] using hmul
  refine ⟨ContinuousLinearMap.IsInvertible.of_inverse hleft hright, ?_⟩
  rw [ContinuousLinearMap.inverse_eq hleft hright]
  calc
    ‖∑' n : ℕ, t ^ n‖ ≤ ∑' n : ℕ, ‖t ^ n‖ := norm_tsum_le_tsum_norm hsum_pow
    _ ≤ ∑' n : ℕ, ‖t‖ ^ n := hsum_pow.tsum_le_tsum hpow hsum
    _ = (1 - ‖t‖)⁻¹ := tsum_geometric_of_lt_one (norm_nonneg _) ht
    _ = (1 - ‖f - ContinuousLinearMap.id 𝕜 E‖)⁻¹ := by simp [t, norm_sub_rev]

/-- Integral of the identity on `[0, 1]`. -/
private lemma integral_id_zero_one : ∫ t in (0 : ℝ)..1, t = 1 / 2 := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => t ^ 2 / 2) u u := by
    intro u _
    convert (hasDerivAt_pow 2 u).div_const 2 using 1
    rw [show (2 - 1 : ℕ) = 1 by rfl, pow_one]
    ring
  have hint : IntervalIntegrable (fun t : ℝ => t) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) hderiv hint
  simpa using hftc

/-- Quadratic Taylor remainder on a convex set, from a Lipschitz bound on the derivative. -/
private lemma norm_taylor_remainder_le [NormedSpace ℝ E] [CompleteSpace E] {G : E → E}
    {s : Set E} {K : ℝ}
    (hK : 0 ≤ K) (hs : Convex ℝ s) (hG : ∀ x ∈ s, DifferentiableAt 𝕜 G x)
    (hLip : ∀ x ∈ s, ∀ y ∈ s, ‖fderiv 𝕜 G x - fderiv 𝕜 G y‖ ≤ K * ‖x - y‖)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖G y - G x - (fderiv 𝕜 G x) (y - x)‖ ≤ (K / 2) * ‖y - x‖ ^ 2 := by
  open MeasureTheory intervalIntegral Set AffineMap in
  by_cases hxy : x = y
  · simp [hxy]
  · let γ : ℝ → E := lineMap x y
    let φ : ℝ → E := G ∘ γ
    let φ' : ℝ → E := fun t => (fderiv 𝕜 G (γ t)) (y - x)
    have hγ0 : γ 0 = x := by simp [γ, lineMap_apply_module]
    have hγ1 : γ 1 = y := by simp [γ, lineMap_apply_module]
    have hseg : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ s := fun t ht => hs.lineMap_mem hx hy ht
    have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ' t) t := by
      intro t ht
      have ht_mem : γ t ∈ s := hseg t ht
      have hFG : HasFDerivAt G (fderiv 𝕜 G (γ t)) (γ t) := (hG _ ht_mem).hasFDerivAt
      have hline : HasDerivAt γ (y - x) t := by
        simpa [γ] using (hasDerivAt_lineMap (a := x) (b := y) (x := t))
      have hcomp := (hFG.restrictScalars ℝ).comp_hasDerivAt t hline
      simpa [φ, φ', ContinuousLinearMap.coe_restrictScalars'] using hcomp
    have hLipOn : LipschitzOnWith (Real.toNNReal K) (fderiv 𝕜 G) s :=
      LipschitzOnWith.of_dist_le_mul fun a ha b hb => by
        rw [dist_eq_norm, dist_eq_norm]
        simpa [Real.coe_toNNReal' K, max_eq_left hK] using hLip a ha b hb
    have hγcont : Continuous γ := by
      unfold γ
      have heq : (lineMap x y : ℝ → E) = fun t => t • (y - x) + x := by
        ext t
        rw [lineMap_apply_module']
      rw [heq]
      exact (continuous_id.smul continuous_const).add continuous_const
    have hφ'cont : ContinuousOn φ' (Icc (0 : ℝ) 1) := by
      have hfd : ContinuousOn (fderiv 𝕜 G) s := hLipOn.continuousOn
      have hcomp : ContinuousOn (fun t => fderiv 𝕜 G (γ t)) (Icc (0 : ℝ) 1) :=
        hfd.comp hγcont.continuousOn fun t ht => hseg t ht
      exact ((ContinuousLinearMap.apply 𝕜 E (y - x)).continuous.comp_continuousOn hcomp)
    have huIcc : uIcc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := uIcc_of_le zero_le_one
    have hint : IntervalIntegrable φ' volume 0 1 := by
      rw [← huIcc] at hφ'cont
      exact hφ'cont.intervalIntegrable
    have hftc : ∫ t in (0 : ℝ)..1, φ' t = φ 1 - φ 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f' := φ')
        (fun u hu => hderiv u (by simpa [huIcc] using hu)) hint
    have hint0 : IntervalIntegrable (fun _ : ℝ => φ' 0) volume 0 1 :=
      intervalIntegrable_const
    have hsub : ∫ t in (0 : ℝ)..1, (φ' t - φ' 0) = (φ 1 - φ 0) - φ' 0 := by
      rw [intervalIntegral.integral_sub hint hint0, hftc, intervalIntegral.integral_const]
      simp [one_smul]
    have hpt : ∀ t ∈ Icc (0 : ℝ) 1, ‖φ' t - φ' 0‖ ≤ K * t * ‖y - x‖ ^ 2 := by
      intro t ht
      have hγt : γ t ∈ s := hseg t ht
      have hline_sub : γ t - x = t • (y - x) := by
        simp [γ, lineMap_apply_module']
      have hdiff : φ' t - φ' 0 = (fderiv 𝕜 G (γ t) - fderiv 𝕜 G x) (y - x) := by
        simp only [φ', hγ0, ← sub_apply]
      rw [hdiff]
      calc
        ‖(fderiv 𝕜 G (γ t) - fderiv 𝕜 G x) (y - x)‖
          ≤ ‖fderiv 𝕜 G (γ t) - fderiv 𝕜 G x‖ * ‖y - x‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (K * ‖γ t - x‖) * ‖y - x‖ :=
          mul_le_mul_of_nonneg_right (hLip _ hγt _ hx) (norm_nonneg _)
        _ = (K * ‖t • (y - x)‖) * ‖y - x‖ := by rw [hline_sub]
        _ = (K * (|t| * ‖y - x‖)) * ‖y - x‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ = K * t * ‖y - x‖ ^ 2 := by rw [abs_of_nonneg ht.1]; ring
    have hgcont : Continuous fun t : ℝ => K * t * ‖y - x‖ ^ 2 := by fun_prop
    have hintg : IntervalIntegrable (fun t : ℝ => K * t * ‖y - x‖ ^ 2) volume 0 1 :=
      hgcont.intervalIntegrable 0 1
    have hnorm : ‖∫ t in (0 : ℝ)..1, (φ' t - φ' 0)‖ ≤
        ∫ t in (0 : ℝ)..1, K * t * ‖y - x‖ ^ 2 := by
      refine norm_integral_le_of_norm_le (μ := volume) zero_le_one ?_ hintg
      refine Eventually.of_forall fun t ht => hpt t (Ioc_subset_Icc_self ht)
    have hint_eval : ∫ t in (0 : ℝ)..1, K * t * ‖y - x‖ ^ 2 =
        (K / 2) * ‖y - x‖ ^ 2 := by
      have hpull : ∫ t in (0 : ℝ)..1, (K * ‖y - x‖ ^ 2) * t =
          (K * ‖y - x‖ ^ 2) * ∫ t in (0 : ℝ)..1, t :=
        intervalIntegral.integral_const_mul (K * ‖y - x‖ ^ 2) (fun t : ℝ => t)
      calc
        ∫ t in (0 : ℝ)..1, K * t * ‖y - x‖ ^ 2
            = ∫ t in (0 : ℝ)..1, (K * ‖y - x‖ ^ 2) * t := by
              refine intervalIntegral.integral_congr fun t _ => ?_
              ring
        _ = (K * ‖y - x‖ ^ 2) * (1 / 2) := by rw [hpull, integral_id_zero_one]
        _ = (K / 2) * ‖y - x‖ ^ 2 := by ring
    have hrem : G y - G x - (fderiv 𝕜 G x) (y - x) =
        ∫ t in (0 : ℝ)..1, (φ' t - φ' 0) := by
      rw [hsub]
      simp [φ, φ', hγ0, hγ1]
    rw [hrem]
    exact hnorm.trans_eq hint_eval

/-- **35.9**: Kantorovich convergence under the normalized derivative Lipschitz bound.
Differentiability is at all points of an open neighbourhood of the majorant ball. -/
theorem newton_kantorovich [CompleteSpace E] {F : E → E} (x₀ : E) (S : E ≃L[𝕜] E)
    (hS : fderiv 𝕜 F x₀ = S.toContinuousLinearMap)
    {L η r : ℝ} (hL : 0 ≤ L) (hsmall : L * η < 1 / 2)
    (hr : kantorovichRadius L η ≤ r) (hrpos : 0 < r)
    (hfirst : ‖S.symm (F x₀)‖ ≤ η)
    {U : Set E} (hU : IsOpen U) (hsub : Metric.closedBall x₀ r ⊆ U)
    (hF : DifferentiableOn 𝕜 F U)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F x - fderiv 𝕜 F y)‖ ≤ L * ‖x - y‖) :
    ∃ z ∈ Metric.closedBall x₀ (kantorovichRadius L η), F z = 0 ∧
      Tendsto (newtonIterate (𝕜 := 𝕜) F x₀) atTop (𝓝 z) ∧
      ∀ n, (fderiv 𝕜 F (newtonIterate (𝕜 := 𝕜) F x₀ n)).IsInvertible := by
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have hη : 0 ≤ η := (norm_nonneg _).trans hfirst
  let t := kantorovichMajorant L η
  let ρ := kantorovichRadius L η
  let x : ℕ → E := newtonIterate (𝕜 := 𝕜) F x₀
  let G : E → E := S.symm.toContinuousLinearMap ∘ F
  have hGfun : ∀ y, G y = S.symm (F y) := fun y => rfl
  have hbounds := kantorovichMajorant_bounds hL hη hsmall
  have htend_t : Tendsto t atTop (𝓝 ρ) := tendsto_kantorovichMajorant hL hη hsmall
  have hLρ : L * ρ < 1 := kantorovichRadius_mul_lt_one hL hη hsmall
  have hGderiv : ∀ y ∈ Metric.closedBall x₀ r,
      fderiv 𝕜 G y = S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F y) := by
    intro y hy
    have hyU : y ∈ U := hsub hy
    have hdiff : DifferentiableAt 𝕜 F y := (hF y hyU).differentiableAt (hU.mem_nhds hyU)
    exact (S.symm.toContinuousLinearMap.hasFDerivAt.comp y hdiff.hasFDerivAt).fderiv
  have hGdiff : ∀ y ∈ Metric.closedBall x₀ r, DifferentiableAt 𝕜 G y := by
    intro y hy
    have hyU : y ∈ U := hsub hy
    exact S.symm.toContinuousLinearMap.differentiableAt.comp y
      ((hF y hyU).differentiableAt (hU.mem_nhds hyU))
  have hLipG : ∀ a ∈ Metric.closedBall x₀ r, ∀ b ∈ Metric.closedBall x₀ r,
      ‖fderiv 𝕜 G a - fderiv 𝕜 G b‖ ≤ L * ‖a - b‖ := by
    intro a ha b hb
    rw [hGderiv a ha, hGderiv b hb, ← ContinuousLinearMap.comp_sub]
    exact hLip a ha b hb
  have hball : Convex ℝ (Metric.closedBall x₀ r) := convex_closedBall x₀ r
  have invar : ∀ n,
      x n ∈ Metric.closedBall x₀ r ∧
        (fderiv 𝕜 F (x n)).IsInvertible ∧
          ‖S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F (x n)) -
              ContinuousLinearMap.id 𝕜 E‖ ≤ L * t n ∧
            ‖G (x n)‖ ≤ (t (n + 1) - t n) * (1 - L * t n) ∧
              ‖x n - x₀‖ ≤ t n := by
    intro n
    induction n with
    | zero =>
      refine ⟨Metric.mem_closedBall_self hrpos.le, ?_, ?_, ?_, ?_⟩
      · simp only [x, newtonIterate_zero]
        rw [hS]
        exact ContinuousLinearMap.isInvertible_equiv
      · have hid : S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F x₀) =
            ContinuousLinearMap.id 𝕜 E := by
          rw [hS]
          exact ContinuousLinearEquiv.coe_symm_comp_coe S
        simp [x, newtonIterate_zero, hid, t]
      · simpa [x, newtonIterate_zero, G, t, kantorovichMajorant_one] using hfirst
      · simp [x, newtonIterate_zero, t]
    | succ n ih =>
      rcases ih with ⟨hmem, hinv, hAnorm, hGnorm, hdist⟩
      have hden : 0 < 1 - L * t n := (hbounds n).2.2.1
      have htn : t n ≤ ρ := (hbounds n).2.1
      have hA : ‖S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F (x n)) -
          ContinuousLinearMap.id 𝕜 E‖ < 1 := by
        have : L * t n ≤ L * ρ := mul_le_mul_of_nonneg_left htn hL
        exact lt_of_le_of_lt hAnorm (by linarith)
      let A : E →L[𝕜] E := S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F (x n))
      have hAinv : A.IsInvertible ∧ ‖A.inverse‖ ≤ (1 - ‖A - ContinuousLinearMap.id 𝕜 E‖)⁻¹ :=
        isInvertible_of_norm_sub_id_lt hA
      have hAeq : (S : E →L[𝕜] E) ∘L A = fderiv 𝕜 F (x n) := by
        simp only [A]
        rw [← ContinuousLinearMap.comp_assoc]
        simp [ContinuousLinearMap.id_comp]
      have hFinv : (fderiv 𝕜 F (x n)).IsInvertible := by
        rw [← hAeq]
        exact (ContinuousLinearMap.isInvertible_equiv_comp).2 hAinv.1
      have hinv_formula : (fderiv 𝕜 F (x n)).inverse =
          A.inverse ∘L S.symm.toContinuousLinearMap := by
        rw [← hAeq]
        simp [ContinuousLinearMap.inverse_equiv_comp (e := S) (f := A)]
      have hstep_vec : x (n + 1) - x n = -((fderiv 𝕜 F (x n)).inverse (F (x n))) := by
        simp [x, newtonIterate_succ, newtonStep]
      have hstep_norm : ‖x (n + 1) - x n‖ ≤ t (n + 1) - t n := by
        have happly : (fderiv 𝕜 F (x n)).inverse (F (x n)) = A.inverse (G (x n)) := by
          rw [hinv_formula, hGfun]
          simp
        have hinv_le : ‖A.inverse‖ ≤ (1 - L * t n)⁻¹ := by
          refine hAinv.2.trans ?_
          have hgap : 0 < 1 - ‖A - ContinuousLinearMap.id 𝕜 E‖ := sub_pos.mpr hA
          have hcmp : 1 - L * t n ≤ 1 - ‖A - ContinuousLinearMap.id 𝕜 E‖ := by
            have : ‖A - ContinuousLinearMap.id 𝕜 E‖ ≤ L * t n := by simpa [A] using hAnorm
            linarith
          exact inv_anti₀ hden hcmp
        calc
          ‖x (n + 1) - x n‖ = ‖A.inverse (G (x n))‖ := by
            rw [hstep_vec, norm_neg, happly]
          _ ≤ ‖A.inverse‖ * ‖G (x n)‖ := A.inverse.le_opNorm _
          _ ≤ (1 - L * t n)⁻¹ * ‖G (x n)‖ :=
            mul_le_mul_of_nonneg_right hinv_le (norm_nonneg _)
          _ ≤ (1 - L * t n)⁻¹ * ((t (n + 1) - t n) * (1 - L * t n)) :=
            mul_le_mul_of_nonneg_left hGnorm (inv_nonneg.mpr hden.le)
          _ = t (n + 1) - t n := by field_simp [hden.ne']
      have hdist' : ‖x (n + 1) - x₀‖ ≤ t (n + 1) := by
        calc
          ‖x (n + 1) - x₀‖ ≤ ‖x (n + 1) - x n‖ + ‖x n - x₀‖ := by
            simpa [dist_eq_norm] using dist_triangle (x (n + 1)) (x n) x₀
          _ ≤ (t (n + 1) - t n) + t n := add_le_add hstep_norm hdist
          _ = t (n + 1) := by ring
      have htn1 : t (n + 1) ≤ ρ := (hbounds (n + 1)).2.1
      have hmem' : x (n + 1) ∈ Metric.closedBall x₀ r := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        exact hdist'.trans (htn1.trans hr)
      have hA' : ‖S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F (x (n + 1))) -
          ContinuousLinearMap.id 𝕜 E‖ ≤ L * t (n + 1) := by
        have hid : S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F x₀) =
            ContinuousLinearMap.id 𝕜 E := by
          rw [hS]
          exact ContinuousLinearEquiv.coe_symm_comp_coe S
        rw [← hid, ← ContinuousLinearMap.comp_sub]
        calc
          ‖S.symm.toContinuousLinearMap.comp
              (fderiv 𝕜 F (x (n + 1)) - fderiv 𝕜 F x₀)‖ ≤ L * ‖x (n + 1) - x₀‖ :=
            hLip _ hmem' _ (Metric.mem_closedBall_self hrpos.le)
          _ ≤ L * t (n + 1) := mul_le_mul_of_nonneg_left hdist' hL
      have hAlt : ‖S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F (x (n + 1))) -
          ContinuousLinearMap.id 𝕜 E‖ < 1 := by
        have : L * t (n + 1) ≤ L * ρ := mul_le_mul_of_nonneg_left htn1 hL
        exact lt_of_le_of_lt hA' (by linarith)
      have hFinv' : (fderiv 𝕜 F (x (n + 1))).IsInvertible := by
        let B : E →L[𝕜] E :=
          S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F (x (n + 1)))
        have hB : B.IsInvertible := (isInvertible_of_norm_sub_id_lt hAlt).1
        have hBeq : (S : E →L[𝕜] E) ∘L B = fderiv 𝕜 F (x (n + 1)) := by
          simp only [B]
          rw [← ContinuousLinearMap.comp_assoc]
          simp [ContinuousLinearMap.id_comp]
        rw [← hBeq]
        exact (ContinuousLinearMap.isInvertible_equiv_comp).2 hB
      have hnewton : F (x n) + (fderiv 𝕜 F (x n)) (x (n + 1) - x n) = 0 := by
        have happly := hFinv.self_apply_inverse (F (x n))
        rw [hstep_vec, map_neg, happly, add_neg_cancel]
      have hrem : ‖G (x (n + 1))‖ ≤ (L / 2) * ‖x (n + 1) - x n‖ ^ 2 := by
        have htail := norm_taylor_remainder_le (G := G) hL hball hGdiff hLipG hmem hmem'
        have hneg : (fderiv 𝕜 F (x n)) (x (n + 1) - x n) = -F (x n) :=
          eq_neg_of_add_eq_zero_right hnewton
        have hident : G (x (n + 1)) - G (x n) - (fderiv 𝕜 G (x n)) (x (n + 1) - x n) =
            G (x (n + 1)) := by
          rw [hGderiv _ hmem]
          simp only [ContinuousLinearMap.comp_apply, hneg, map_neg, sub_neg_eq_add]
          have hGy : S.symm.toContinuousLinearMap (F (x n)) = G (x n) := rfl
          rw [hGy, sub_add_cancel]
        rw [← hident]
        exact htail
      have hG' : ‖G (x (n + 1))‖ ≤ (t (n + 2) - t (n + 1)) * (1 - L * t (n + 1)) := by
        have hsq := kantorovichMajorant_sq hL hη hsmall n
        have hden1 : 0 < 1 - L * t (n + 1) := (hbounds (n + 1)).2.2.1
        have hinc : t (n + 2) - t (n + 1) =
            kantorovichQuadratic L η (t (n + 1)) / (1 - L * t (n + 1)) := by
          have := kantorovichMajorant_succ L η (n + 1)
          linarith
        calc
          ‖G (x (n + 1))‖ ≤ (L / 2) * ‖x (n + 1) - x n‖ ^ 2 := hrem
          _ ≤ (L / 2) * (t (n + 1) - t n) ^ 2 := by
            have hnonneg : 0 ≤ L / 2 := by linarith
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (norm_nonneg _) hstep_norm 2) hnonneg
          _ = kantorovichQuadratic L η (t (n + 1)) := by rw [hsq]
          _ = (t (n + 2) - t (n + 1)) * (1 - L * t (n + 1)) := by
            rw [hinc]
            field_simp [hden1.ne']
      exact ⟨hmem', hFinv', hA', hG', hdist'⟩
  have htele : ∀ {m n : ℕ}, n ≤ m → ‖x m - x n‖ ≤ t m - t n := by
    intro m n hnm
    induction m with
    | zero =>
      obtain rfl := Nat.eq_zero_of_le_zero hnm
      simp
    | succ m ih =>
      rcases lt_or_eq_of_le hnm with hlt | rfl
      · have hnm' : n ≤ m := Nat.le_of_lt_succ hlt
        calc
          ‖x (m + 1) - x n‖ = ‖(x (m + 1) - x m) + (x m - x n)‖ := by abel
          _ ≤ ‖x (m + 1) - x m‖ + ‖x m - x n‖ := norm_add_le _ _
          _ ≤ (t (m + 1) - t m) + (t m - t n) := by
            have hstep : ‖x (m + 1) - x m‖ ≤ t (m + 1) - t m := by
              have hmem := (invar m).1
              have hmem' := (invar (m + 1)).1
              have hden := (hbounds m).2.2.1
              have hAnorm := (invar m).2.2.1
              have hGnorm := (invar m).2.2.2.1
              have hA : ‖S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F (x m)) -
                  ContinuousLinearMap.id 𝕜 E‖ < 1 := by
                have : L * t m ≤ L * ρ :=
                  mul_le_mul_of_nonneg_left (hbounds m).2.1 hL
                exact lt_of_le_of_lt hAnorm (by linarith)
              let A : E →L[𝕜] E := S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F (x m))
              have hAinv := isInvertible_of_norm_sub_id_lt hA
              have hAeq : (S : E →L[𝕜] E) ∘L A = fderiv 𝕜 F (x m) := by
                simp only [A]
                rw [← ContinuousLinearMap.comp_assoc]
                simp [ContinuousLinearMap.id_comp]
              have hinv_formula : (fderiv 𝕜 F (x m)).inverse =
                  A.inverse ∘L S.symm.toContinuousLinearMap := by
                have hFinv : (fderiv 𝕜 F (x m)).IsInvertible := (invar m).2.1
                rw [← hAeq]
                simp [ContinuousLinearMap.inverse_equiv_comp (e := S) (f := A)]
              have hinv_le : ‖A.inverse‖ ≤ (1 - L * t m)⁻¹ := by
                refine hAinv.2.trans ?_
                have hcmp : 1 - L * t m ≤ 1 - ‖A - ContinuousLinearMap.id 𝕜 E‖ := by
                  have : ‖A - ContinuousLinearMap.id 𝕜 E‖ ≤ L * t m := by
                    simpa [A] using hAnorm
                  linarith
                exact inv_anti₀ hden hcmp
              have hstep_vec : x (m + 1) - x m =
                  -((fderiv 𝕜 F (x m)).inverse (F (x m))) := by
                simp [x, newtonIterate_succ, newtonStep]
              calc
                ‖x (m + 1) - x m‖ = ‖A.inverse (G (x m))‖ := by
                  rw [hstep_vec, norm_neg, hinv_formula]
                  simp [hGfun]
                _ ≤ ‖A.inverse‖ * ‖G (x m)‖ := A.inverse.le_opNorm _
                _ ≤ (1 - L * t m)⁻¹ * ‖G (x m)‖ :=
                  mul_le_mul_of_nonneg_right hinv_le (norm_nonneg _)
                _ ≤ (1 - L * t m)⁻¹ * ((t (m + 1) - t m) * (1 - L * t m)) :=
                  mul_le_mul_of_nonneg_left hGnorm (inv_nonneg.mpr hden.le)
                _ = t (m + 1) - t m := by
                  rw [mul_comm (t (m + 1) - t m) (1 - L * t m), ← mul_assoc,
                    inv_mul_cancel₀ hden.ne', one_mul]
            exact add_le_add hstep (ih hnm')
          _ = t (m + 1) - t n := by ring
      · simp
  have hcauchy : CauchySeq x := by
    refine cauchySeq_of_le_tendsto_0' (fun n => ρ - t n) ?_ ?_
    · intro n m hnm
      have hdist : dist (x n) (x m) ≤ t m - t n := by
        rw [dist_eq_norm, norm_sub_rev]
        exact htele hnm
      exact hdist.trans (by linarith [(hbounds m).2.1])
    · have hconst : Tendsto (fun _ : ℕ => ρ) atTop (𝓝 ρ) := tendsto_const_nhds
      simpa [sub_self] using Filter.Tendsto.sub hconst htend_t
  obtain ⟨z, hz⟩ := CompleteSpace.complete hcauchy
  have htend_x : Tendsto x atTop (𝓝 z) := hz
  have hz_dist : ‖z - x₀‖ ≤ ρ := by
    have hnorm : Tendsto (fun n => ‖x n - x₀‖) atTop (𝓝 ‖z - x₀‖) :=
      (continuous_norm.tendsto _).comp (Filter.Tendsto.sub htend_x tendsto_const_nhds)
    exact le_of_tendsto hnorm <| Eventually.of_forall fun n =>
      (invar n).2.2.2.2.trans (hbounds n).2.1
  have hzρ : z ∈ Metric.closedBall x₀ ρ := by rwa [Metric.mem_closedBall, dist_eq_norm]
  have hzU : z ∈ U := hsub (Metric.closedBall_subset_closedBall hr hzρ)
  have hFcont : ContinuousAt F z := hF.continuousOn.continuousAt (hU.mem_nhds hzU)
  have hdiff0 : Tendsto (fun n => t (n + 1) - t n) atTop (𝓝 0) := by
    have hshift : Tendsto (fun n => t (n + 1)) atTop (𝓝 ρ) :=
      (tendsto_add_atTop_iff_nat 1).mpr htend_t
    simpa [sub_self] using hshift.sub htend_t
  have hprod0 : Tendsto (fun n => (t (n + 2) - t (n + 1)) * (1 - L * t (n + 1))) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun n => t (n + 2) - t (n + 1)) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).mpr hdiff0
    have h2 : Tendsto (fun n => 1 - L * t (n + 1)) atTop (𝓝 (1 - L * ρ)) := by
      have hshift : Tendsto (fun n => t (n + 1)) atTop (𝓝 ρ) :=
        (tendsto_add_atTop_iff_nat 1).mpr htend_t
      simpa [sub_eq_add_neg] using
        tendsto_const_nhds.sub ((tendsto_const_nhds (x := L)).mul hshift)
    simpa [sub_self] using h1.mul h2
  have hG0 : Tendsto (fun n => G (x n)) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    refine squeeze_zero_norm (fun n => ?_) hprod0
    exact (invar (n + 1)).2.2.2.1
  have hF0 : Tendsto (fun n => F (x n)) atTop (𝓝 0) := by
    have hScont := (S : E →L[𝕜] E).continuous.tendsto 0
    have hcomp : Tendsto (fun n => S (G (x n))) atTop (𝓝 (S 0)) := hScont.comp hG0
    simpa [G, map_zero, ContinuousLinearEquiv.apply_symm_apply] using hcomp
  have hFz : F z = 0 := tendsto_nhds_unique (hFcont.tendsto.comp hz) hF0
  refine ⟨z, hzρ, hFz, hz, fun n => (invar n).2.1⟩

/-- Local quadratic convergence near a regular zero with Lipschitz derivative. -/
theorem newton_quadratic [CompleteSpace E] {F : E → E} {z : E} (hz : F z = 0)
    (S : E ≃L[𝕜] E) (hS : fderiv 𝕜 F z = S.toContinuousLinearMap)
    {r : ℝ} (hr : 0 < r) (hF : DifferentiableOn 𝕜 F (Metric.ball z r))
    {L : ℝ≥0} (hLip : LipschitzOnWith L (fderiv 𝕜 F) (Metric.ball z r)) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ x₀ ∈ Metric.ball z δ,
      Tendsto (newtonIterate (𝕜 := 𝕜) F x₀) atTop (𝓝 z) ∧
      ∀ n, ‖newtonIterate (𝕜 := 𝕜) F x₀ (n + 1) - z‖ ≤
        C * ‖newtonIterate (𝕜 := 𝕜) F x₀ n - z‖ ^ 2 := by
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let M : ℝ := ‖S.symm.toContinuousLinearMap‖
  let K : ℝ := M * (L : ℝ)
  let C : ℝ := K + 1
  let δ : ℝ := min (r / 2) (1 / (2 * C))
  have hK0 : 0 ≤ K := mul_nonneg (norm_nonneg _) (NNReal.coe_nonneg L)
  have hCpos : 0 < C := by dsimp [C]; linarith
  have hδpos : 0 < δ := lt_min (by linarith) (by positivity)
  have hδr : δ ≤ r / 2 := min_le_left _ _
  have hδC : δ ≤ 1 / (2 * C) := min_le_right _ _
  have hKδ : K * δ ≤ 1 / 2 := by
    have hKC : K ≤ C := by dsimp [C]; linarith
    calc
      K * δ ≤ K * (1 / (2 * C)) := mul_le_mul_of_nonneg_left hδC hK0
      _ ≤ C * (1 / (2 * C)) := mul_le_mul_of_nonneg_right hKC (by positivity)
      _ = 1 / 2 := by field_simp [hCpos.ne']
  have hball_sub : Metric.ball z δ ⊆ Metric.ball z r :=
    Metric.ball_subset_ball (by linarith : δ ≤ r)
  have hconv : Convex ℝ (Metric.ball z r) := convex_ball z r
  have hFdiff : ∀ y ∈ Metric.ball z r, DifferentiableAt 𝕜 F y := fun y hy =>
    (hF y hy).differentiableAt (Metric.isOpen_ball.mem_nhds hy)
  have hLipF : ∀ a ∈ Metric.ball z r, ∀ b ∈ Metric.ball z r,
      ‖fderiv 𝕜 F a - fderiv 𝕜 F b‖ ≤ (L : ℝ) * ‖a - b‖ := by
    intro a ha b hb
    simpa [dist_eq_norm] using (lipschitzOnWith_iff_dist_le_mul.mp hLip) a ha b hb
  refine ⟨δ, C, hδpos, hCpos, ?_⟩
  intro x₀ hx₀
  let x : ℕ → E := newtonIterate (𝕜 := 𝕜) F x₀
  have hstep : ∀ y, ‖y - z‖ < δ →
      (fderiv 𝕜 F y).IsInvertible ∧
        ‖newtonStep (𝕜 := 𝕜) F y - z‖ ≤ K * ‖y - z‖ ^ 2 := by
    intro y hyδ
    have hyδball : y ∈ Metric.ball z δ := by rwa [Metric.mem_ball, dist_eq_norm]
    have hy_ball : y ∈ Metric.ball z r := hball_sub hyδball
    have hz_ball : z ∈ Metric.ball z r := Metric.mem_ball_self hr
    let A : E →L[𝕜] E := S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F y)
    have hAsub : A - ContinuousLinearMap.id 𝕜 E =
        S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F y - fderiv 𝕜 F z) := by
      have hid : S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F z) =
          ContinuousLinearMap.id 𝕜 E := by
        rw [hS]
        exact ContinuousLinearEquiv.coe_symm_comp_coe S
      rw [← hid]
      simp [A, ContinuousLinearMap.comp_sub]
    have hAnorm : ‖A - ContinuousLinearMap.id 𝕜 E‖ ≤ K * ‖y - z‖ := by
      calc
        ‖A - ContinuousLinearMap.id 𝕜 E‖ =
            ‖S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F y - fderiv 𝕜 F z)‖ := by rw [hAsub]
        _ ≤ M * ‖fderiv 𝕜 F y - fderiv 𝕜 F z‖ := by
          simpa [M] using ContinuousLinearMap.opNorm_comp_le
            S.symm.toContinuousLinearMap (fderiv 𝕜 F y - fderiv 𝕜 F z)
        _ ≤ M * ((L : ℝ) * ‖y - z‖) :=
          mul_le_mul_of_nonneg_left (hLipF y hy_ball z hz_ball) (norm_nonneg _)
        _ = K * ‖y - z‖ := by ring
    have hAlt : ‖A - ContinuousLinearMap.id 𝕜 E‖ < 1 := by
      have hθ : ‖y - z‖ ≤ δ := le_of_lt hyδ
      have : K * ‖y - z‖ ≤ 1 / 2 := by
        calc
          K * ‖y - z‖ ≤ K * δ := mul_le_mul_of_nonneg_left hθ hK0
          _ ≤ 1 / 2 := hKδ
      exact lt_of_le_of_lt hAnorm (lt_of_le_of_lt this (by norm_num))
    have hAinv := isInvertible_of_norm_sub_id_lt hAlt
    have hAeq : (S : E →L[𝕜] E) ∘L A = fderiv 𝕜 F y := by
      simp only [A]
      rw [← ContinuousLinearMap.comp_assoc]
      simp [ContinuousLinearMap.id_comp]
    have hinv : (fderiv 𝕜 F y).IsInvertible := by
      rw [← hAeq]
      exact (ContinuousLinearMap.isInvertible_equiv_comp).2 hAinv.1
    have hformula : (fderiv 𝕜 F y).inverse = A.inverse ∘L S.symm.toContinuousLinearMap := by
      rw [← hAeq]
      simp [ContinuousLinearMap.inverse_equiv_comp (e := S) (f := A)]
    have hrem : ‖F y - F z - (fderiv 𝕜 F y) (y - z)‖ ≤
        ((L : ℝ) / 2) * ‖y - z‖ ^ 2 := by
      have htail := norm_taylor_remainder_le (G := F) (K := (L : ℝ)) (NNReal.coe_nonneg L)
        hconv hFdiff hLipF hy_ball hz_ball
      have hflip : F y - F z - (fderiv 𝕜 F y) (y - z) =
          -(F z - F y - (fderiv 𝕜 F y) (z - y)) := by
        rw [← neg_sub y z, map_neg, sub_neg_eq_add]
        abel_nf
      rw [hflip, norm_neg, norm_sub_rev y z]
      exact htail
    have hhalf : ‖A.inverse‖ ≤ 2 := by
      have hle_half : ‖A - ContinuousLinearMap.id 𝕜 E‖ ≤ 1 / 2 := by
        have hθ : ‖y - z‖ ≤ δ := le_of_lt hyδ
        exact hAnorm.trans <| by
          calc
            K * ‖y - z‖ ≤ K * δ := mul_le_mul_of_nonneg_left hθ hK0
            _ ≤ 1 / 2 := hKδ
      have hden : (0 : ℝ) < 1 / 2 := by norm_num
      have hcmp : (1 / 2 : ℝ) ≤ 1 - ‖A - ContinuousLinearMap.id 𝕜 E‖ := by
        linarith [hle_half]
      have hinv_le : ‖A.inverse‖ ≤ (1 - ‖A - ContinuousLinearMap.id 𝕜 E‖)⁻¹ := hAinv.2
      exact hinv_le.trans <| (inv_anti₀ hden hcmp).trans_eq (by norm_num)
    have hop : ‖(fderiv 𝕜 F y).inverse‖ ≤ 2 * M := by
      rw [hformula]
      calc
        ‖A.inverse ∘L S.symm.toContinuousLinearMap‖ ≤ ‖A.inverse‖ * M := by
          simpa [M] using ContinuousLinearMap.opNorm_comp_le A.inverse S.symm.toContinuousLinearMap
        _ ≤ 2 * M := mul_le_mul_of_nonneg_right hhalf (norm_nonneg _)
    have hEq : newtonStep (𝕜 := 𝕜) F y - z =
        -((fderiv 𝕜 F y).inverse (F y - F z - (fderiv 𝕜 F y) (y - z))) := by
      rw [newtonStep, hz, sub_zero]
      have hself := hinv.inverse_apply_self (y - z)
      have hdecomp : F y =
          (F y - (fderiv 𝕜 F y) (y - z)) + (fderiv 𝕜 F y) (y - z) := by abel
      rw [hdecomp, map_add, hself]
      abel
    refine ⟨hinv, ?_⟩
    calc
      ‖newtonStep (𝕜 := 𝕜) F y - z‖ =
          ‖(fderiv 𝕜 F y).inverse (F y - F z - (fderiv 𝕜 F y) (y - z))‖ := by
            rw [hEq, norm_neg]
      _ ≤ ‖(fderiv 𝕜 F y).inverse‖ *
          ‖F y - F z - (fderiv 𝕜 F y) (y - z)‖ :=
        (fderiv 𝕜 F y).inverse.le_opNorm _
      _ ≤ (2 * M) * (((L : ℝ) / 2) * ‖y - z‖ ^ 2) :=
        mul_le_mul hop hrem (norm_nonneg _)
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg _))
      _ = K * ‖y - z‖ ^ 2 := by ring
  have orbit : ∀ n, ‖x n - z‖ < δ ∧ ‖x (n + 1) - z‖ ≤ C * ‖x n - z‖ ^ 2 := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simpa [x, newtonIterate_zero, Metric.mem_ball, dist_eq_norm] using hx₀, ?_⟩
      have h0 : ‖x₀ - z‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hx₀
      exact (hstep x₀ h0).2.trans
        (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (sq_nonneg _))
    | succ n ih =>
      have hlt : ‖x (n + 1) - z‖ < δ := by
        have hθ : ‖x n - z‖ < δ := ih.1
        have hle : ‖x (n + 1) - z‖ ≤ K * ‖x n - z‖ ^ 2 := by
          have hnext := (hstep (x n) hθ).2
          simpa [x, newtonIterate_succ] using hnext
        have hhalf : K * ‖x n - z‖ ≤ 1 / 2 := by
          calc
            K * ‖x n - z‖ ≤ K * δ := mul_le_mul_of_nonneg_left hθ.le hK0
            _ ≤ 1 / 2 := hKδ
        calc
          ‖x (n + 1) - z‖ ≤ K * ‖x n - z‖ ^ 2 := hle
          _ = (K * ‖x n - z‖) * ‖x n - z‖ := by ring
          _ ≤ (1 / 2) * ‖x n - z‖ := mul_le_mul_of_nonneg_right hhalf (norm_nonneg _)
          _ ≤ (1 / 2) * δ :=
            mul_le_mul_of_nonneg_left hθ.le (by norm_num : (0 : ℝ) ≤ 1 / 2)
          _ < δ := by linarith [hδpos]
      refine ⟨hlt, ?_⟩
      have hquad := (hstep (x (n + 1)) hlt).2
      simpa [x, newtonIterate_succ] using hquad.trans
        (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (sq_nonneg _))
  have hquad : ∀ n, ‖x (n + 1) - z‖ ≤ C * ‖x n - z‖ ^ 2 := fun n => (orbit n).2
  have hgeom : ∀ n, ‖x n - z‖ ≤ ‖x₀ - z‖ * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero => simp [x]
    | succ n ih =>
      have hθ : ‖x n - z‖ < δ := (orbit n).1
      have hhalf : K * ‖x n - z‖ ≤ 1 / 2 := by
        calc
          K * ‖x n - z‖ ≤ K * δ := mul_le_mul_of_nonneg_left hθ.le hK0
          _ ≤ 1 / 2 := hKδ
      calc
        ‖x (n + 1) - z‖ ≤ K * ‖x n - z‖ ^ 2 := by
          simpa [x, newtonIterate_succ] using (hstep (x n) hθ).2
        _ = (K * ‖x n - z‖) * ‖x n - z‖ := by ring
        _ ≤ (1 / 2) * ‖x n - z‖ := mul_le_mul_of_nonneg_right hhalf (norm_nonneg _)
        _ ≤ (1 / 2) * (‖x₀ - z‖ * (1 / 2) ^ n) :=
          mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 1 / 2)
        _ = ‖x₀ - z‖ * (1 / 2) ^ (n + 1) := by ring
  have hnorm0 : Tendsto (fun n => ‖x n - z‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => norm_nonneg _) hgeom ?_
    have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 : ℝ) / 2 < 1)
    simpa using hpow.const_mul ‖x₀ - z‖
  have htend : Tendsto x atTop (𝓝 z) :=
    tendsto_sub_nhds_zero_iff.mp <| (tendsto_zero_iff_norm_tendsto_zero).2 hnorm0
  exact ⟨htend, hquad⟩

end CKMA
