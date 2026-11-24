/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Newton iteration and Kantorovich convergence

The Newton step uses the totalized inverse of the Fréchet derivative. Convergence statements
supply invertibility on the relevant iterates rather than assuming the totalized inverse always
behaves as an inverse.

The Kantorovich radius includes the affine `L=0` limit. The scalar field is real or complex.
The Semilocal statement uses a normalized derivative Lipschitz bound and differentiability on an
open neighborhood of the majorant ball; the local statement gives quadratic convergence near a
regular zero. The initial step length is controlled by a norm bound. Source: GAPS 35.9.

## Main definitions

* `CKMA.kantorovichRadius`: The majorant root, including the affine `L = 0` limit.
* `CKMA.newtonStep`: One Newton step using Mathlib's totalized operator inverse.
* `CKMA.newtonIterate`: Sequence of Newton iterates starting at `x₀`.

## Main results

* `CKMA.newtonIterate_zero`: The zeroth Newton iterate is the starting point.
* `CKMA.newtonIterate_succ`: Each subsequent iterate applies `newtonStep`.
* `CKMA.newton_kantorovich`: Semilocal Kantorovich convergence theorem (**35.9**).
* `CKMA.newton_quadratic`: Local quadratic convergence near a regular zero.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped NNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The majorant root, including the affine `L=0` limit. -/
@[expose]
def kantorovichRadius (L η : ℝ) : ℝ :=
  if L = 0 then η else (1 - Real.sqrt (1 - 2 * L * η)) / L

/-- One Newton step, using Mathlib's totalized operator inverse. Results assert invertibility
on the relevant region; the definition does not invent an inverse when one is unavailable. -/
@[expose]
def newtonStep (F : E → E) (x : E) : E := x - (fderiv 𝕜 F x).inverse (F x)

/-- Newton iterates starting at `x₀`, indexed with the initial guess at zero.
The scalar is supplied explicitly because it does not appear in the iteration type. -/
@[expose]
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
private lemma kantorovich_discriminant_pos {L η : ℝ}
    (hsmall : L * η < 1 / 2) : 0 < 1 - 2 * L * η := by
  linarith [hsmall]

/-- The Kantorovich radius is nonnegative. -/
private lemma kantorovichRadius_nonneg {L η : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η) :
    0 ≤ kantorovichRadius L η := by
  by_cases hL0 : L = 0
  · simp [kantorovichRadius, hL0, hη]
  · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    have hle : 1 - 2 * L * η ≤ 1 := by nlinarith [hL, hη]
    have hs : Real.sqrt (1 - 2 * L * η) ≤ 1 := Real.sqrt_le_one.mpr hle
    rw [kantorovichRadius, ite_eq_right hL0]
    exact div_nonneg (sub_nonneg.mpr hs) hLpos.le

/-- The radius stays strictly below the pole `1 / L` of the majorant. -/
private lemma kantorovichRadius_mul_lt_one {L η : ℝ} (hL : 0 ≤ L)
    (hsmall : L * η < 1 / 2) : L * kantorovichRadius L η < 1 := by
  by_cases hL0 : L = 0
  · simp [kantorovichRadius, hL0]
  · have hdisc : 0 < 1 - 2 * L * η := kantorovich_discriminant_pos hsmall
    have hs : 0 < Real.sqrt (1 - 2 * L * η) := Real.sqrt_pos.mpr hdisc
    have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    rw [kantorovichRadius, ite_eq_right hL0]
    calc
      L * ((1 - Real.sqrt (1 - 2 * L * η)) / L) = 1 - Real.sqrt (1 - 2 * L * η) := by
        field_simp
      _ < 1 := by linarith

/-- The quadratic majorant vanishes at the Kantorovich radius. -/
private lemma kantorovichQuadratic_radius {L η : ℝ} (hL : 0 ≤ L)
    (hsmall : L * η < 1 / 2) :
    kantorovichQuadratic L η (kantorovichRadius L η) = 0 := by
  by_cases hL0 : L = 0
  · simp [kantorovichQuadratic, kantorovichRadius, hL0]
  · have hdisc : 0 ≤ 1 - 2 * L * η := (kantorovich_discriminant_pos hsmall).le
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
  have hroot := kantorovichQuadratic_radius hL hsmall
  simp only [kantorovichQuadratic] at hroot
  set ρ := kantorovichRadius L η
  have hηeq : η = ρ - (L / 2) * ρ ^ 2 := by linarith
  have hρ : 0 ≤ ρ := kantorovichRadius_nonneg hL hη
  have hLρ : L * ρ < 1 := kantorovichRadius_mul_lt_one hL hsmall
  rw [hηeq]
  nlinarith [sq_nonneg ρ, mul_nonneg hL hρ]

/-- Factor `φ(t)` through the root at the Kantorovich radius. -/
private lemma kantorovichQuadratic_factor {L η t : ℝ} (hL : 0 ≤ L)
    (hsmall : L * η < 1 / 2) :
    kantorovichQuadratic L η t =
      (kantorovichRadius L η - t) *
        (1 - (L / 2) * (kantorovichRadius L η + t)) := by
  have hroot := kantorovichQuadratic_radius hL hsmall
  simp only [kantorovichQuadratic] at hroot ⊢
  set ρ := kantorovichRadius L η
  have hηeq : η = ρ - (L / 2) * ρ ^ 2 := by linarith
  rw [hηeq]
  ring

/-- The quadratic majorant is nonnegative on the segment from `0` to the radius. -/
private lemma kantorovichQuadratic_nonneg {L η t : ℝ} (hL : 0 ≤ L)
    (hsmall : L * η < 1 / 2) (ht : t ≤ kantorovichRadius L η) :
    0 ≤ kantorovichQuadratic L η t := by
  rw [kantorovichQuadratic_factor hL hsmall]
  set ρ := kantorovichRadius L η
  have hLρ : L * ρ < 1 := kantorovichRadius_mul_lt_one hL hsmall
  have hsecond : 0 ≤ 1 - (L / 2) * (ρ + t) := by
    have : (L / 2) * (ρ + t) ≤ L * ρ := by nlinarith [sq_nonneg ρ]
    linarith
  exact mul_nonneg (by linarith) hsecond

/-- The quadratic majorant is positive before the radius. -/
private lemma kantorovichQuadratic_pos {L η t : ℝ} (hL : 0 ≤ L)
    (hsmall : L * η < 1 / 2) (ht : t < kantorovichRadius L η) :
    0 < kantorovichQuadratic L η t := by
  rw [kantorovichQuadratic_factor hL hsmall]
  set ρ := kantorovichRadius L η
  have hLρ : L * ρ < 1 := kantorovichRadius_mul_lt_one hL hsmall
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
private lemma kantorovich_newton_le_radius {L η s : ℝ} (hL : 0 ≤ L)
    (hsmall : L * η < 1 / 2) (hs : s ≤ kantorovichRadius L η)
    (hden : 0 < 1 - L * s) :
    s + kantorovichQuadratic L η s / (1 - L * s) ≤ kantorovichRadius L η := by
  set ρ := kantorovichRadius L η
  have hφ := kantorovichQuadratic_factor (t := s) hL hsmall
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
    refine ⟨le_rfl, kantorovichRadius_nonneg hL hη, by simp, ?_⟩
    simpa [kantorovichMajorant_one] using hη
  | succ n ih =>
    rcases ih with ⟨hs0, hsle, hden, hmono⟩
    set s := kantorovichMajorant L η n
    set u := kantorovichMajorant L η (n + 1)
    have hu : u = s + kantorovichQuadratic L η s / (1 - L * s) := by
      simpa [s, u] using kantorovichMajorant_succ L η n
    have hφ : 0 ≤ kantorovichQuadratic L η s :=
      kantorovichQuadratic_nonneg hL hsmall hsle
    have hu0 : 0 ≤ u := by
      rw [hu]
      exact add_nonneg hs0 (div_nonneg hφ hden.le)
    have hule : u ≤ kantorovichRadius L η := by
      rw [hu]
      exact kantorovich_newton_le_radius hL hsmall hsle hden
    have hdenu : 0 < 1 - L * u := by
      have hLρ : L * kantorovichRadius L η < 1 := kantorovichRadius_mul_lt_one hL hsmall
      have : L * u ≤ L * kantorovichRadius L η := mul_le_mul_of_nonneg_left hule hL
      linarith
    have hφu : 0 ≤ kantorovichQuadratic L η u :=
      kantorovichQuadratic_nonneg hL hsmall hule
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
    have hLρ : L * ρ < 1 := kantorovichRadius_mul_lt_one hL hsmall
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
    · exact absurd hφ0 (kantorovichQuadratic_pos hL hsmall h).ne'
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
  have hleft : f ∘L (∑' n : ℕ, t ^ n) = ContinuousLinearMap.id 𝕜 E := by
    have hmul := mul_neg_geom_series t ht
    simpa [hf', ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def] using hmul
  have hright : (∑' n : ℕ, t ^ n) ∘L f = ContinuousLinearMap.id 𝕜 E := by
    have hmul := geom_series_mul_neg t ht
    simpa [hf', ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def] using hmul
  refine ⟨ContinuousLinearMap.IsInvertible.of_inverse hleft hright, ?_⟩
  rw [ContinuousLinearMap.inverse_eq hleft hright]
  have h1 : ‖(1 : E →L[𝕜] E)‖ ≤ 1 := by
    simpa [ContinuousLinearMap.one_def] using ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := E)
  have hle := tsum_geometric_le_of_norm_lt_one t ht
  rw [show ‖f - ContinuousLinearMap.id 𝕜 E‖ = ‖t‖ by simp [t, norm_sub_rev]]
  linarith

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
        _ = (K * ‖y - x‖ ^ 2) * ((1 ^ 2 - 0 ^ 2) / 2) := by rw [hpull, integral_id]
        _ = (K / 2) * ‖y - x‖ ^ 2 := by ring
    have hrem : G y - G x - (fderiv 𝕜 G x) (y - x) =
        ∫ t in (0 : ℝ)..1, (φ' t - φ' 0) := by
      rw [hsub]
      simp [φ, φ', hγ0, hγ1]
    rw [hrem]
    exact hnorm.trans_eq hint_eval

/-- If `S⁻¹ ∘ D` is within `θ < 1` of the identity, then `D` is invertible and its inverse is
bounded by `(1 - θ)⁻¹` times `S⁻¹`. -/
private lemma isInvertible_and_norm_inverse_apply_le [CompleteSpace E] (S : E ≃L[𝕜] E)
    {D : E →L[𝕜] E} {θ : ℝ} (hθ : θ < 1)
    (hD : ‖S.symm.toContinuousLinearMap.comp D - ContinuousLinearMap.id 𝕜 E‖ ≤ θ) :
    D.IsInvertible ∧ ∀ v, ‖D.inverse v‖ ≤ (1 - θ)⁻¹ * ‖S.symm v‖ := by
  set A : E →L[𝕜] E := S.symm.toContinuousLinearMap.comp D with hA
  have hAinv := isInvertible_of_norm_sub_id_lt (hD.trans_lt hθ)
  have hAeq : (S : E →L[𝕜] E) ∘L A = D := by
    rw [hA, ← ContinuousLinearMap.comp_assoc]
    simp [ContinuousLinearMap.id_comp]
  have hformula : D.inverse = A.inverse ∘L S.symm.toContinuousLinearMap := by
    rw [← hAeq]
    simp [ContinuousLinearMap.inverse_equiv_comp (e := S) (f := A)]
  have hDinv : D.IsInvertible := by
    rw [← hAeq]
    exact (ContinuousLinearMap.isInvertible_equiv_comp).2 hAinv.1
  have hinv_le : ‖A.inverse‖ ≤ (1 - θ)⁻¹ :=
    hAinv.2.trans (inv_anti₀ (by linarith) (by linarith))
  refine ⟨hDinv, fun v => ?_⟩
  rw [hformula]
  calc
    ‖(A.inverse ∘L S.symm.toContinuousLinearMap) v‖ = ‖A.inverse (S.symm v)‖ := rfl
    _ ≤ ‖A.inverse‖ * ‖S.symm v‖ := A.inverse.le_opNorm _
    _ ≤ (1 - θ)⁻¹ * ‖S.symm v‖ := mul_le_mul_of_nonneg_right hinv_le (norm_nonneg _)

/-- When `S = fderiv F x₀`, the deviation of `S⁻¹ ∘ fderiv F y` from the identity is
`S⁻¹ ∘ (fderiv F y - fderiv F x₀)`. -/
private lemma symm_comp_fderiv_sub_id {F : E → E} {x₀ : E} (S : E ≃L[𝕜] E)
    (hS : fderiv 𝕜 F x₀ = S.toContinuousLinearMap) (y : E) :
    S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F y) - ContinuousLinearMap.id 𝕜 E =
      S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F y - fderiv 𝕜 F x₀) := by
  have hid : S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F x₀) =
      ContinuousLinearMap.id 𝕜 E := by
    rw [hS]
    exact ContinuousLinearEquiv.coe_symm_comp_coe S
  rw [ContinuousLinearMap.comp_sub, hid]

/-- One Kantorovich step: if `S⁻¹ ∘ fderiv F y` is within `L * s < 1` of the identity and the
normalized residual `S⁻¹ (F y)` is at most `d * (1 - L * s)`, then `fderiv F y` is invertible and
the Newton step from `y` has length at most `d`. -/
private lemma norm_newtonStep_sub_le [CompleteSpace E] {F : E → E} (S : E ≃L[𝕜] E) {y : E}
    {L s d : ℝ} (hLs : L * s < 1)
    (hA : ‖S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F y) -
      ContinuousLinearMap.id 𝕜 E‖ ≤ L * s)
    (hres : ‖S.symm (F y)‖ ≤ d * (1 - L * s)) :
    (fderiv 𝕜 F y).IsInvertible ∧ ‖newtonStep (𝕜 := 𝕜) F y - y‖ ≤ d := by
  obtain ⟨hinv, hbound⟩ := isInvertible_and_norm_inverse_apply_le S hLs hA
  have hden : 0 < 1 - L * s := by linarith
  refine ⟨hinv, ?_⟩
  calc
    ‖newtonStep (𝕜 := 𝕜) F y - y‖ = ‖(fderiv 𝕜 F y).inverse (F y)‖ := by
      simp [newtonStep]
    _ ≤ (1 - L * s)⁻¹ * ‖S.symm (F y)‖ := hbound _
    _ ≤ (1 - L * s)⁻¹ * (d * (1 - L * s)) :=
      mul_le_mul_of_nonneg_left hres (inv_nonneg.mpr hden.le)
    _ = d := by field_simp [hden.ne']

/-- After a Newton step from `y` that stays in the ball, the normalized residual at the new point
is a Taylor remainder, hence at most `(L / 2) * ‖newtonStep F y - y‖ ^ 2`. -/
private lemma norm_symm_apply_newtonStep_le [CompleteSpace E] {F : E → E} {x₀ : E}
    (S : E ≃L[𝕜] E) {L r : ℝ} (hL : 0 ≤ L) {U : Set E} (hU : IsOpen U)
    (hsub : Metric.closedBall x₀ r ⊆ U) (hF : DifferentiableOn 𝕜 F U)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F x - fderiv 𝕜 F y)‖ ≤ L * ‖x - y‖)
    {y : E} (hy : y ∈ Metric.closedBall x₀ r)
    (hy' : newtonStep (𝕜 := 𝕜) F y ∈ Metric.closedBall x₀ r)
    (hinv : (fderiv 𝕜 F y).IsInvertible) :
    ‖S.symm (F (newtonStep (𝕜 := 𝕜) F y))‖ ≤
      (L / 2) * ‖newtonStep (𝕜 := 𝕜) F y - y‖ ^ 2 := by
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let G : E → E := S.symm.toContinuousLinearMap ∘ F
  have hGderiv : ∀ w ∈ Metric.closedBall x₀ r,
      fderiv 𝕜 G w = S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F w) := by
    intro w hw
    have hdiff : DifferentiableAt 𝕜 F w := (hF w (hsub hw)).differentiableAt
      (hU.mem_nhds (hsub hw))
    exact (S.symm.toContinuousLinearMap.hasFDerivAt.comp w hdiff.hasFDerivAt).fderiv
  have hGdiff : ∀ w ∈ Metric.closedBall x₀ r, DifferentiableAt 𝕜 G w := fun w hw =>
    S.symm.toContinuousLinearMap.differentiableAt.comp w
      ((hF w (hsub hw)).differentiableAt (hU.mem_nhds (hsub hw)))
  have hLipG : ∀ a ∈ Metric.closedBall x₀ r, ∀ b ∈ Metric.closedBall x₀ r,
      ‖fderiv 𝕜 G a - fderiv 𝕜 G b‖ ≤ L * ‖a - b‖ := by
    intro a ha b hb
    rw [hGderiv a ha, hGderiv b hb, ← ContinuousLinearMap.comp_sub]
    exact hLip a ha b hb
  set y' := newtonStep (𝕜 := 𝕜) F y with hy'_def
  have hnewton : (fderiv 𝕜 F y) (y' - y) = -F y := by
    have happly := hinv.self_apply_inverse (F y)
    simp only [hy'_def, newtonStep, sub_sub_cancel_left, map_neg, happly]
  have hident : G y' - G y - (fderiv 𝕜 G y) (y' - y) = G y' := by
    rw [hGderiv _ hy]
    simp only [ContinuousLinearMap.comp_apply, hnewton, map_neg, sub_neg_eq_add]
    have hGy : S.symm.toContinuousLinearMap (F y) = G y := rfl
    rw [hGy, sub_add_cancel]
  have htail := norm_taylor_remainder_le (G := G) hL (convex_closedBall x₀ r) hGdiff hLipG hy hy'
  rw [hident] at htail
  exact htail

/-- The Kantorovich majorant reproduces the residual bound at the next index:
`(L / 2) * (t (n + 1) - t n) ^ 2 = (t (n + 2) - t (n + 1)) * (1 - L * t (n + 1))`. -/
private lemma kantorovichMajorant_sq_eq_mul {L η : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hsmall : L * η < 1 / 2) (n : ℕ) :
    (L / 2) * (kantorovichMajorant L η (n + 1) - kantorovichMajorant L η n) ^ 2 =
      (kantorovichMajorant L η (n + 2) - kantorovichMajorant L η (n + 1)) *
        (1 - L * kantorovichMajorant L η (n + 1)) := by
  have hden1 := (kantorovichMajorant_bounds hL hη hsmall (n + 1)).2.2.1
  have hinc : kantorovichMajorant L η (n + 2) - kantorovichMajorant L η (n + 1) =
      kantorovichQuadratic L η (kantorovichMajorant L η (n + 1)) /
        (1 - L * kantorovichMajorant L η (n + 1)) := by
    have := kantorovichMajorant_succ L η (n + 1)
    linarith
  rw [← kantorovichMajorant_sq hL hη hsmall n, hinc]
  field_simp [hden1.ne']

/-- A sequence whose steps are dominated by the increments of a real sequence `t` converging to
`ρ` from below converges, and its limit lies within `ρ - t 0` of the starting point. -/
private lemma exists_tendsto_of_norm_sub_le_majorant [CompleteSpace E] {x : ℕ → E}
    {t : ℕ → ℝ} {ρ : ℝ} (hstep : ∀ n, ‖x (n + 1) - x n‖ ≤ t (n + 1) - t n)
    (hle : ∀ n, t n ≤ ρ) (ht : Tendsto t atTop (𝓝 ρ)) :
    ∃ z, Tendsto x atTop (𝓝 z) ∧ ‖z - x 0‖ ≤ ρ - t 0 := by
  have htele : ∀ {m n : ℕ}, n ≤ m → ‖x m - x n‖ ≤ t m - t n := by
    intro m n hnm
    induction m with
    | zero =>
      obtain rfl := Nat.eq_zero_of_le_zero hnm
      simp
    | succ m ih =>
      rcases lt_or_eq_of_le hnm with hlt | rfl
      · calc
          ‖x (m + 1) - x n‖ = ‖(x (m + 1) - x m) + (x m - x n)‖ := by abel_nf
          _ ≤ ‖x (m + 1) - x m‖ + ‖x m - x n‖ := norm_add_le _ _
          _ ≤ (t (m + 1) - t m) + (t m - t n) :=
            add_le_add (hstep m) (ih (Nat.le_of_lt_succ hlt))
          _ = t (m + 1) - t n := by ring
      · simp
  have hcauchy : CauchySeq x := by
    refine cauchySeq_of_le_tendsto_0' (fun n => ρ - t n) (fun n m hnm => ?_) ?_
    · rw [dist_eq_norm, norm_sub_rev]
      exact (htele hnm).trans (by linarith [hle m])
    · simpa [sub_self] using (tendsto_const_nhds (x := ρ)).sub ht
  obtain ⟨z, hz⟩ := CompleteSpace.complete hcauchy
  have hz : Tendsto x atTop (𝓝 z) := hz
  refine ⟨z, hz, ?_⟩
  have hnorm : Tendsto (fun n => ‖x n - x 0‖) atTop (𝓝 ‖z - x 0‖) :=
    (continuous_norm.tendsto _).comp (hz.sub tendsto_const_nhds)
  exact le_of_tendsto hnorm <| Eventually.of_forall fun n =>
    (htele (Nat.zero_le n)).trans (by linarith [hle n])

/-- **35.9**: Kantorovich convergence under the normalized derivative Lipschitz bound.
Differentiability is at all points of an open neighbourhood of the majorant ball. -/
theorem newton_kantorovich [CompleteSpace E] {F : E → E} (x₀ : E) (S : E ≃L[𝕜] E)
    (hS : fderiv 𝕜 F x₀ = S.toContinuousLinearMap)
    {L η r : ℝ} (hL : 0 ≤ L) (hsmall : L * η < 1 / 2)
    (hr : kantorovichRadius L η ≤ r)
    (hfirst : ‖S.symm (F x₀)‖ ≤ η)
    {U : Set E} (hU : IsOpen U) (hsub : Metric.closedBall x₀ r ⊆ U)
    (hF : DifferentiableOn 𝕜 F U)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F x - fderiv 𝕜 F y)‖ ≤ L * ‖x - y‖) :
    ∃ z ∈ Metric.closedBall x₀ (kantorovichRadius L η), F z = 0 ∧
      Tendsto (newtonIterate (𝕜 := 𝕜) F x₀) atTop (𝓝 z) ∧
      ∀ n, (fderiv 𝕜 F (newtonIterate (𝕜 := 𝕜) F x₀ n)).IsInvertible := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hfirst
  have hr0 : 0 ≤ r := (kantorovichRadius_nonneg hL hη).trans hr
  let t := kantorovichMajorant L η
  let ρ := kantorovichRadius L η
  let x : ℕ → E := newtonIterate (𝕜 := 𝕜) F x₀
  have hxs : ∀ n, x (n + 1) = newtonStep (𝕜 := 𝕜) F (x n) := newtonIterate_succ F x₀
  have hbounds := kantorovichMajorant_bounds hL hη hsmall
  have htend_t : Tendsto t atTop (𝓝 ρ) := tendsto_kantorovichMajorant hL hη hsmall
  have hLt : ∀ n, L * t n < 1 := fun n => by linarith [(hbounds n).2.2.1]
  have hx0 : x₀ ∈ Metric.closedBall x₀ r := Metric.mem_closedBall_self hr0
  -- Invariant: the iterates stay in the ball, are regular, and are majorized by `t`.
  have invar : ∀ n,
      x n ∈ Metric.closedBall x₀ r ∧ (fderiv 𝕜 F (x n)).IsInvertible ∧
        ‖S.symm (F (x n))‖ ≤ (t (n + 1) - t n) * (1 - L * t n) ∧
          ‖x n - x₀‖ ≤ t n ∧ ‖x (n + 1) - x n‖ ≤ t (n + 1) - t n := by
    intro n
    induction n with
    | zero =>
      have hA0 : ‖S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F (x 0)) -
          ContinuousLinearMap.id 𝕜 E‖ ≤ L * t 0 := by
        simp [x, symm_comp_fderiv_sub_id S hS, t]
      have hG0 : ‖S.symm (F (x 0))‖ ≤ (t 1 - t 0) * (1 - L * t 0) := by
        simpa [x, t, kantorovichMajorant_one] using hfirst
      obtain ⟨hinv0, hstep0⟩ := norm_newtonStep_sub_le S (hLt 0) hA0 hG0
      exact ⟨hx0, hinv0, hG0, by simp [x, t], by simpa [hxs] using hstep0⟩
    | succ n ih =>
      obtain ⟨hmem, hinv, -, hdist, hstep_norm⟩ := ih
      have hdist' : ‖x (n + 1) - x₀‖ ≤ t (n + 1) := by
        have := norm_sub_le_norm_sub_add_norm_sub (x (n + 1)) (x n) x₀
        linarith
      have hmem' : x (n + 1) ∈ Metric.closedBall x₀ r := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        exact hdist'.trans ((hbounds (n + 1)).2.1.trans hr)
      have hA' : ‖S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F (x (n + 1))) -
          ContinuousLinearMap.id 𝕜 E‖ ≤ L * t (n + 1) := by
        rw [symm_comp_fderiv_sub_id S hS]
        exact (hLip _ hmem' _ hx0).trans (mul_le_mul_of_nonneg_left hdist' hL)
      have hrem : ‖S.symm (F (x (n + 1)))‖ ≤ (L / 2) * ‖x (n + 1) - x n‖ ^ 2 := by
        rw [hxs] at hmem' ⊢
        exact norm_symm_apply_newtonStep_le S hL hU hsub hF hLip hmem hmem' hinv
      have hG' : ‖S.symm (F (x (n + 1)))‖ ≤ (t (n + 2) - t (n + 1)) * (1 - L * t (n + 1)) := by
        calc
          ‖S.symm (F (x (n + 1)))‖ ≤ (L / 2) * ‖x (n + 1) - x n‖ ^ 2 := hrem
          _ ≤ (L / 2) * (t (n + 1) - t n) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hstep_norm 2)
              (by linarith)
          _ = (t (n + 2) - t (n + 1)) * (1 - L * t (n + 1)) :=
            kantorovichMajorant_sq_eq_mul hL hη hsmall n
      obtain ⟨hinv', hstep'⟩ := norm_newtonStep_sub_le S (hLt (n + 1)) hA' hG'
      exact ⟨hmem', hinv', hG', hdist', by simpa [hxs] using hstep'⟩
  -- The iterates converge to a point of the majorant ball.
  obtain ⟨z, htend_x, hz_dist⟩ := exists_tendsto_of_norm_sub_le_majorant
    (fun n => (invar n).2.2.2.2) (fun n => (hbounds n).2.1) htend_t
  have hzρ : z ∈ Metric.closedBall x₀ ρ := by
    simpa [Metric.mem_closedBall, dist_eq_norm, x, t] using hz_dist
  have hzU : z ∈ U := hsub (Metric.closedBall_subset_closedBall hr hzρ)
  have hFcont : ContinuousAt F z := hF.continuousOn.continuousAt (hU.mem_nhds hzU)
  -- The limit is a zero: the residuals are squeezed by the vanishing majorant increments.
  have hshift : Tendsto (fun n => t (n + 1)) atTop (𝓝 ρ) :=
    (tendsto_add_atTop_iff_nat 1).mpr htend_t
  have hdiff0 : Tendsto (fun n => t (n + 1) - t n) atTop (𝓝 0) := by
    simpa [sub_self] using hshift.sub htend_t
  have hprod0 : Tendsto (fun n => (t (n + 2) - t (n + 1)) * (1 - L * t (n + 1))) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun n => t (n + 2) - t (n + 1)) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).mpr hdiff0
    have h2 : Tendsto (fun n => 1 - L * t (n + 1)) atTop (𝓝 (1 - L * ρ)) :=
      tendsto_const_nhds.sub ((tendsto_const_nhds (x := L)).mul hshift)
    simpa [sub_self] using h1.mul h2
  have hG0 : Tendsto (fun n => S.symm (F (x n))) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    exact squeeze_zero_norm (fun n => (invar (n + 1)).2.2.1) hprod0
  have hF0 : Tendsto (fun n => F (x n)) atTop (𝓝 0) := by
    have hcomp := ((S : E →L[𝕜] E).continuous.tendsto 0).comp hG0
    simpa [Function.comp_def, map_zero, ContinuousLinearEquiv.apply_symm_apply] using hcomp
  have hFz : F z = 0 := tendsto_nhds_unique (hFcont.tendsto.comp htend_x) hF0
  exact ⟨z, hzρ, hFz, htend_x, fun n => (invar n).2.1⟩

/-- One Newton step near a regular zero `z`: if `‖S⁻¹‖ * L * ‖y - z‖ ≤ 1 / 2`, then
`fderiv F y` is invertible and the error after the step is at most `‖S⁻¹‖ * L * ‖y - z‖ ^ 2`. -/
private lemma norm_newtonStep_sub_zero_le [CompleteSpace E] {F : E → E} {z : E} (hz : F z = 0)
    (S : E ≃L[𝕜] E) (hS : fderiv 𝕜 F z = S.toContinuousLinearMap)
    {r : ℝ} (hF : DifferentiableOn 𝕜 F (Metric.ball z r))
    {L : ℝ≥0} (hLip : LipschitzOnWith L (fderiv 𝕜 F) (Metric.ball z r))
    {y : E} (hy : y ∈ Metric.ball z r)
    (hyK : ‖S.symm.toContinuousLinearMap‖ * L * ‖y - z‖ ≤ 1 / 2) :
    (fderiv 𝕜 F y).IsInvertible ∧
      ‖newtonStep (𝕜 := 𝕜) F y - z‖ ≤ ‖S.symm.toContinuousLinearMap‖ * L * ‖y - z‖ ^ 2 := by
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  set M : ℝ := ‖S.symm.toContinuousLinearMap‖ with hM
  have hz_ball : z ∈ Metric.ball z r := Metric.mem_ball_self (Metric.pos_of_mem_ball hy)
  have hFdiff : ∀ w ∈ Metric.ball z r, DifferentiableAt 𝕜 F w := fun w hw =>
    (hF w hw).differentiableAt (Metric.isOpen_ball.mem_nhds hw)
  have hLipF : ∀ a ∈ Metric.ball z r, ∀ b ∈ Metric.ball z r,
      ‖fderiv 𝕜 F a - fderiv 𝕜 F b‖ ≤ (L : ℝ) * ‖a - b‖ := by
    intro a ha b hb
    simpa [dist_eq_norm] using (lipschitzOnWith_iff_dist_le_mul.mp hLip) a ha b hb
  have hA : ‖S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F y) -
      ContinuousLinearMap.id 𝕜 E‖ ≤ 1 / 2 := by
    rw [symm_comp_fderiv_sub_id S hS]
    calc
      ‖S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F y - fderiv 𝕜 F z)‖ ≤
          M * ‖fderiv 𝕜 F y - fderiv 𝕜 F z‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M * ((L : ℝ) * ‖y - z‖) :=
        mul_le_mul_of_nonneg_left (hLipF y hy z hz_ball) (norm_nonneg _)
      _ = M * L * ‖y - z‖ := by ring
      _ ≤ 1 / 2 := hyK
  obtain ⟨hinv, hbound⟩ := isInvertible_and_norm_inverse_apply_le S (by norm_num) hA
  have hrem : ‖F y - F z - (fderiv 𝕜 F y) (y - z)‖ ≤ ((L : ℝ) / 2) * ‖y - z‖ ^ 2 := by
    have htail := norm_taylor_remainder_le (G := F) (K := (L : ℝ)) (NNReal.coe_nonneg L)
      (convex_ball z r) hFdiff hLipF hy hz_ball
    have hflip : F y - F z - (fderiv 𝕜 F y) (y - z) =
        -(F z - F y - (fderiv 𝕜 F y) (z - y)) := by
      rw [← neg_sub y z, map_neg, sub_neg_eq_add]
      abel_nf
    rw [hflip, norm_neg, norm_sub_rev y z]
    exact htail
  have hEq : newtonStep (𝕜 := 𝕜) F y - z =
      -((fderiv 𝕜 F y).inverse (F y - F z - (fderiv 𝕜 F y) (y - z))) := by
    rw [newtonStep, hz, sub_zero]
    have hself := hinv.inverse_apply_self (y - z)
    have hdecomp : F y = (F y - (fderiv 𝕜 F y) (y - z)) + (fderiv 𝕜 F y) (y - z) := by abel
    rw [hdecomp, map_add, hself]
    abel_nf
  refine ⟨hinv, ?_⟩
  calc
    ‖newtonStep (𝕜 := 𝕜) F y - z‖ =
        ‖(fderiv 𝕜 F y).inverse (F y - F z - (fderiv 𝕜 F y) (y - z))‖ := by
      rw [hEq, norm_neg]
    _ ≤ (1 - 1 / 2)⁻¹ * ‖S.symm (F y - F z - (fderiv 𝕜 F y) (y - z))‖ := hbound _
    _ ≤ 2 * (M * ‖F y - F z - (fderiv 𝕜 F y) (y - z)‖) := by
      rw [show (1 - 1 / 2 : ℝ)⁻¹ = 2 by norm_num]
      exact mul_le_mul_of_nonneg_left (S.symm.toContinuousLinearMap.le_opNorm _) (by norm_num)
    _ ≤ 2 * (M * (((L : ℝ) / 2) * ‖y - z‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrem (norm_nonneg _)) (by norm_num)
    _ = M * L * ‖y - z‖ ^ 2 := by ring

/-- Local quadratic convergence near a regular zero with Lipschitz derivative. -/
theorem newton_quadratic [CompleteSpace E] {F : E → E} {z : E} (hz : F z = 0)
    (S : E ≃L[𝕜] E) (hS : fderiv 𝕜 F z = S.toContinuousLinearMap)
    {r : ℝ} (hr : 0 < r) (hF : DifferentiableOn 𝕜 F (Metric.ball z r))
    {L : ℝ≥0} (hLip : LipschitzOnWith L (fderiv 𝕜 F) (Metric.ball z r)) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ x₀ ∈ Metric.ball z δ,
      Tendsto (newtonIterate (𝕜 := 𝕜) F x₀) atTop (𝓝 z) ∧
      ∀ n, ‖newtonIterate (𝕜 := 𝕜) F x₀ (n + 1) - z‖ ≤
        C * ‖newtonIterate (𝕜 := 𝕜) F x₀ n - z‖ ^ 2 := by
  let M : ℝ := ‖S.symm.toContinuousLinearMap‖
  let K : ℝ := M * (L : ℝ)
  let C : ℝ := K + 1
  let δ : ℝ := min (r / 2) (1 / (2 * C))
  have hK0 : 0 ≤ K := mul_nonneg (norm_nonneg _) (NNReal.coe_nonneg L)
  have hKC : K ≤ C := by dsimp [C]; linarith
  have hCpos : 0 < C := by dsimp [C]; linarith
  have hδpos : 0 < δ := lt_min (by linarith) (by positivity)
  have hδr : δ ≤ r / 2 := min_le_left _ _
  have hδC : δ ≤ 1 / (2 * C) := min_le_right _ _
  have hKδ : K * δ ≤ 1 / 2 := by
    calc
      K * δ ≤ K * (1 / (2 * C)) := mul_le_mul_of_nonneg_left hδC hK0
      _ ≤ C * (1 / (2 * C)) := mul_le_mul_of_nonneg_right hKC (by positivity)
      _ = 1 / 2 := by field_simp [hCpos.ne']
  have hball_sub : Metric.ball z δ ⊆ Metric.ball z r :=
    Metric.ball_subset_ball (by linarith : δ ≤ r)
  refine ⟨δ, C, hδpos, hCpos, fun x₀ hx₀ => ?_⟩
  let x : ℕ → E := newtonIterate (𝕜 := 𝕜) F x₀
  have hx₀' : ‖x₀ - z‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hx₀
  -- Inside the `δ`-ball one Newton step squares the error and at least halves it.
  have hstep : ∀ n, ‖x n - z‖ < δ →
      ‖x (n + 1) - z‖ ≤ K * ‖x n - z‖ ^ 2 ∧ K * ‖x n - z‖ ≤ 1 / 2 := by
    intro n hn
    have hKn : K * ‖x n - z‖ ≤ 1 / 2 := (mul_le_mul_of_nonneg_left hn.le hK0).trans hKδ
    have hmem : x n ∈ Metric.ball z r := hball_sub (by rwa [Metric.mem_ball, dist_eq_norm])
    rw [show x (n + 1) = newtonStep (𝕜 := 𝕜) F (x n) from newtonIterate_succ F x₀ n]
    exact ⟨(norm_newtonStep_sub_zero_le hz S hS hF hLip hmem hKn).2, hKn⟩
  have hgeom_lt : ∀ n, ‖x₀ - z‖ * (1 / 2) ^ n < δ := fun n =>
    (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))).trans_lt
      hx₀'
  have hgeom : ∀ n, ‖x n - z‖ ≤ ‖x₀ - z‖ * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero => simp [x]
    | succ n ih =>
      obtain ⟨hq, hK⟩ := hstep n (ih.trans_lt (hgeom_lt n))
      calc
        ‖x (n + 1) - z‖ ≤ K * ‖x n - z‖ ^ 2 := hq
        _ = (K * ‖x n - z‖) * ‖x n - z‖ := by ring
        _ ≤ (1 / 2) * ‖x n - z‖ := mul_le_mul_of_nonneg_right hK (norm_nonneg _)
        _ ≤ (1 / 2) * (‖x₀ - z‖ * (1 / 2) ^ n) :=
          mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 1 / 2)
        _ = ‖x₀ - z‖ * (1 / 2) ^ (n + 1) := by ring
  have hquad : ∀ n, ‖x (n + 1) - z‖ ≤ C * ‖x n - z‖ ^ 2 := fun n =>
    (hstep n ((hgeom n).trans_lt (hgeom_lt n))).1.trans
      (mul_le_mul_of_nonneg_right hKC (sq_nonneg _))
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
