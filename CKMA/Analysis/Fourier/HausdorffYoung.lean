/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Algebra.Support

/-!
# Hausdorff–Young

At Mathlib's `exp(-2πi x·ξ)` normalization, the Fourier integral satisfies
Hausdorff–Young on `L¹ ∩ Lᵖ` for `1 ≤ p ≤ 2`. No finite constant gives the same
bound for an exponent above two, already on Schwartz functions in positive dimension.
Spatially separated modulated bumps have almost disjoint Fourier packets, so the
ratio of the two norms is unbounded.

Source: GAPS 27.4.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Complex Filter Finset FourierTransform MeasureTheory Metric Real Set Topology
open scoped BigOperators Complex ENNReal FourierTransform RealInnerProductSpace

/-- **27.4**: Hausdorff–Young on the dense intersection `L¹ ∩ Lᵖ`, with the `p=1` endpoint.
This formulation uses the Fourier integral; extension to all of `Lᵖ` needs a bounded-map
  construction. -/
theorem hausdorff_young {d : ℕ} {p q : ℝ≥0∞} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hpq : p⁻¹ + q⁻¹ = 1) {f : EuclideanSpace ℝ (Fin d) → ℂ}
    (hf1 : Integrable f volume) (hfp : MemLp f p volume) :
    eLpNorm (𝓕 f) q volume ≤ eLpNorm f p volume := by
  sorry

section NotHausdorffYoung

variable {d : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin d)

/-- The first coordinate axis, available in positive dimension. -/
private def hyAxis (hd : 0 < d) : Fin d := ⟨0, hd⟩

/-- The unit vector along `hyAxis`. -/
private def hyBasis (hd : 0 < d) : V := EuclideanSpace.single (hyAxis hd) 1

/-- The point at position `k * t` on the first coordinate axis. -/
private def hyOnAxis (hd : 0 < d) (t : ℝ) (k : ℕ) : V := ((k : ℝ) * t) • hyBasis hd

/-- A fixed smooth bump, equal to one on the closed unit ball and supported in radius two. -/
private def hyBump : ContDiffBump (0 : V) := ⟨1, 2, zero_lt_one, one_lt_two⟩

/-- The bump, viewed as a complex-valued test function. -/
private def hyPhi (x : V) : ℂ := hyBump x

/-- The complex character `exp(2πi t x₀)` along the first coordinate. -/
private def hyPhase (hd : 0 < d) (t : ℝ) (x : V) : ℂ :=
  cexp (↑(2 * π * t * x (hyAxis hd)) * I)

/-- One modulated translate of the bump. `R` is the spatial step and `T` the frequency step. -/
private def hyPacket (hd : 0 < d) (R T : ℝ) (k : ℕ) (x : V) : ℂ :=
  hyPhase hd ((k : ℝ) * T) x * hyPhi (x - hyOnAxis hd R k)

/-- Sum of the first `N` modulated translates, with spatial step `5`. -/
private def hyFun (hd : 0 < d) (T : ℝ) (N : ℕ) (x : V) : ℂ :=
  ∑ k ∈ range N, hyPacket hd 5 T k x

/-- The first basis vector has unit length. -/
private lemma hyBasis_norm (hd : 0 < d) : ‖hyBasis hd‖ = 1 := by
  simp [hyBasis, PiLp.norm_single]

/-- Distinct natural numbers differ by at least one as real numbers. -/
private lemma one_le_abs_sub_nat (j k : ℕ) (h : j ≠ k) : (1 : ℝ) ≤ |(j : ℝ) - k| := by
  rcases le_total k j with hle | hle
  · have hlt : k < j := lt_of_le_of_ne hle h.symm
    have hsub : (1 : ℕ) ≤ j - k := Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hlt)
    have hcast : (k : ℝ) ≤ j := Nat.cast_le.mpr hle
    rw [abs_of_nonneg (sub_nonneg.mpr hcast), ← Nat.cast_sub hle]
    exact_mod_cast hsub
  · have hlt : j < k := lt_of_le_of_ne hle h
    have hcast : (j : ℝ) ≤ k := Nat.cast_le.mpr hle
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hcast), ← Nat.cast_sub hle]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hlt)

/-- Distance between the axis points `j * t` and `k * t`. -/
private lemma norm_hyOnAxis_sub (hd : 0 < d) (t : ℝ) (j k : ℕ) :
    ‖hyOnAxis hd t j - hyOnAxis hd t k‖ = |(j : ℝ) - k| * |t| := by
  unfold hyOnAxis
  have hsub : ((j : ℝ) * t) • hyBasis hd - ((k : ℝ) * t) • hyBasis hd =
      (((j : ℝ) - k) * t) • hyBasis hd := by
    rw [← sub_smul]
    congr 1
    ring
  rw [hsub, norm_smul, Real.norm_eq_abs, hyBasis_norm hd, mul_one, abs_mul]

/-- The phase is the character of the inner product against `t • hyBasis`. -/
private lemma hyPhase_eq_inner (hd : 0 < d) (t : ℝ) (x : V) :
    hyPhase hd t x = cexp (↑(2 * π * ⟪x, t • hyBasis hd⟫) * I) := by
  rw [hyPhase]
  congr 1
  rw [inner_smul_right, hyBasis, EuclideanSpace.inner_single_right]
  simp [mul_assoc, mul_left_comm, mul_comm]

/-- Every phase factor has modulus one. -/
private lemma hyPhase_norm (hd : 0 < d) (t : ℝ) (x : V) : ‖hyPhase hd t x‖ = 1 := by
  simpa [hyPhase] using Complex.norm_exp_ofReal_mul_I (2 * π * t * x (hyAxis hd))

/-- The complex bump is smooth. -/
private lemma hyPhi_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (hyPhi : V → ℂ) := by
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Complex.ofReal ∘ (hyBump : V → ℝ))
  exact Complex.ofRealCLM.contDiff.comp hyBump.contDiff

/-- The complex bump is continuous. -/
private lemma hyPhi_continuous : Continuous (hyPhi : V → ℂ) :=
  hyPhi_contDiff.continuous

/-- The complex bump is compactly supported. -/
private lemma hyPhi_compact : HasCompactSupport (hyPhi : V → ℂ) := by
  change HasCompactSupport (Complex.ofReal ∘ (hyBump : V → ℝ))
  exact (hyBump.hasCompactSupport).comp_left Complex.ofReal_zero

/-- The bump vanishes precisely outside the open ball of radius two. -/
private lemma hyPhi_eq_zero_iff (x : V) : hyPhi x = 0 ↔ 2 ≤ ‖x‖ := by
  rw [hyPhi, Complex.ofReal_eq_zero]
  have hsup : Function.support (hyBump : V → ℝ) = ball (0 : V) 2 := by
    simpa [hyBump] using hyBump.support_eq
  constructor
  · intro hzero
    rw [← not_lt]
    intro hlt
    have hx : x ∈ Function.support (hyBump : V → ℝ) := by
      rw [hsup, mem_ball_zero_iff]
      exact hlt
    exact hx hzero
  · intro hge
    have hx : x ∉ ball (0 : V) 2 := by
      rw [mem_ball_zero_iff, not_lt]
      exact hge
    rw [← hsup, Function.mem_support] at hx
    simpa using hx

/-- The complex bump is integrable. -/
private lemma hyPhi_integrable : Integrable (hyPhi : V → ℂ) volume :=
  hyPhi_continuous.integrable_of_hasCompactSupport (μ := volume) hyPhi_compact

/-- Polynomial moments of derivatives of the bump are integrable. -/
private lemma hyPhi_moment_integrable (k n : ℕ) :
    Integrable (fun v : V ↦ ‖v‖ ^ k * ‖iteratedFDeriv ℝ n hyPhi v‖) volume := by
  have hC : Continuous (fun v : V ↦ ‖v‖ ^ k * ‖iteratedFDeriv ℝ n hyPhi v‖) :=
    (continuous_norm.pow k).mul
      ((hyPhi_contDiff.of_le
        (WithTop.coe_le_coe.mpr (le_top : (n : ℕ∞) ≤ ⊤))).continuous_iteratedFDeriv').norm
  have hK : HasCompactSupport (fun v : V ↦ ‖v‖ ^ k * ‖iteratedFDeriv ℝ n hyPhi v‖) :=
    ((hyPhi_compact.iteratedFDeriv n).norm).mul_left
  exact hC.integrable_of_hasCompactSupport (μ := volume) hK

/-- A constant controlling the decay `‖w‖ * ‖𝓕 hyPhi w‖`. -/
private def hyDecay : ℝ :=
  (2 * π) ^ (0 : ℕ) * (2 * (0 : ℕ) + 2) ^ 1 *
    ∑ p ∈ range (0 + 1) ×ˢ range (1 + 1),
      ∫ v : V, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 hyPhi v‖

/-- The decay constant is nonnegative. -/
private lemma hyDecay_nonneg : 0 ≤ (hyDecay (d := d)) := by
  unfold hyDecay
  refine mul_nonneg (mul_nonneg (by positivity) (by positivity)) ?_
  refine sum_nonneg fun p _ => ?_
  exact integral_nonneg fun v => mul_nonneg (by positivity) (norm_nonneg _)

/-- Pointwise decay of the Fourier transform of the bump. -/
private lemma hyPhi_fourier_decay (w : V) : ‖w‖ * ‖𝓕 hyPhi w‖ ≤ (hyDecay (d := d)) := by
  have hle := Real.pow_mul_norm_iteratedFDeriv_fourier_le (f := hyPhi) (K := 0) (N := 1)
    (hf := hyPhi_contDiff.of_le
      (WithTop.coe_le_coe.mpr (by simp : (1 : ℕ∞) ≤ ⊤)))
    (h'f := fun k n _ _ => hyPhi_moment_integrable k n)
    (k := 0) (n := 1) (hk := by simp) (hn := by simp) w
  simpa [hyDecay, norm_iteratedFDeriv_zero, pow_one] using hle

/-- The Fourier transform of the bump, evaluated at the origin. -/
private lemma hyPhi_fourier_zero : 𝓕 hyPhi (0 : V) = (∫ v : V, hyBump v : ℂ) := by
  rw [fourier_eq']
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul, hyPhi, integral_complex_ofReal]

/-- The bump has nonzero total mass, hence a nonzero Fourier transform at the origin. -/
private lemma hyPhi_fourier_zero_pos : 0 < ‖𝓕 hyPhi (0 : V)‖ := by
  rw [hyPhi_fourier_zero, integral_complex_ofReal,
    Complex.norm_of_nonneg (integral_nonneg hyBump.nonneg')]
  exact hyBump.integral_pos

/-- The Fourier transform of the bump is continuous. -/
private lemma hyPhi_fourier_continuous : Continuous (𝓕 (hyPhi : V → ℂ)) := by
  refine (contDiff_fourier (N := 0) ?_).continuous
  intro n hn
  have hn0 : n = 0 := by simpa using hn
  subst hn0
  simpa using hyPhi_integrable.norm

/-- A radius on which the Fourier transform of the bump stays near its value at the origin. -/
private lemma hyRadius_spec : ∃ r : ℝ, 0 < r ∧ ∀ w : V, ‖w‖ < r →
    ‖𝓕 hyPhi w - 𝓕 hyPhi (0 : V)‖ < ‖𝓕 hyPhi (0 : V)‖ / 4 := by
  have hcont : ContinuousAt (𝓕 hyPhi) (0 : V) := hyPhi_fourier_continuous.continuousAt
  rw [Metric.continuousAt_iff] at hcont
  simpa [dist_eq_norm] using
    hcont (‖𝓕 hyPhi (0 : V)‖ / 4) (div_pos hyPhi_fourier_zero_pos (by norm_num))

/-- The radius chosen from `hyRadius_spec`. -/
private def hyRadius : ℝ := Classical.choose (hyRadius_spec (d := d))

/-- The chosen radius is positive. -/
private lemma hyRadius_pos : 0 < (hyRadius (d := d)) :=
  (Classical.choose_spec hyRadius_spec).1

/-- Inside the chosen ball, the Fourier transform is within `δ / 4` of its value at zero. -/
private lemma hyRadius_close (w : V) (hw : ‖w‖ < (hyRadius (d := d))) :
    ‖𝓕 hyPhi w - 𝓕 hyPhi (0 : V)‖ < ‖𝓕 hyPhi (0 : V)‖ / 4 :=
  (Classical.choose_spec hyRadius_spec).2 w hw

/-- Inside the chosen ball, the Fourier transform is bounded below by three quarters of `δ`. -/
private lemma hyPhi_fourier_near (w : V) (hw : ‖w‖ < (hyRadius (d := d))) :
    3 / 4 * ‖𝓕 hyPhi (0 : V)‖ < ‖𝓕 hyPhi w‖ := by
  have hsub : ‖𝓕 hyPhi (0 : V)‖ < ‖𝓕 hyPhi w‖ + ‖𝓕 hyPhi (0 : V)‖ / 4 := by
    calc
      ‖𝓕 hyPhi (0 : V)‖ ≤ ‖𝓕 hyPhi w‖ + ‖𝓕 hyPhi (0 : V) - 𝓕 hyPhi w‖ := by
        simpa [sub_eq_add_neg, norm_neg] using
          norm_add_le (𝓕 hyPhi w) (𝓕 hyPhi (0 : V) - 𝓕 hyPhi w)
      _ = ‖𝓕 hyPhi w‖ + ‖𝓕 hyPhi w - 𝓕 hyPhi (0 : V)‖ := by rw [norm_sub_rev]
      _ < ‖𝓕 hyPhi w‖ + ‖𝓕 hyPhi (0 : V)‖ / 4 := by gcongr; exact hyRadius_close w hw
  linarith

/-- Frequency separation for `N` packets, large enough that tails of size `N` stay below `δ / 4`. -/
private def hyFreq (N : ℕ) : ℝ :=
  2 * (hyRadius (d := d)) + 1 + 4 * (N : ℝ) * (hyDecay (d := d)) / ‖𝓕 hyPhi (0 : V)‖

/-- The gap between the frequency step and the continuity radius dominates the tail. -/
private lemma hyFreq_gap (N : ℕ) :
    4 * (N : ℝ) * (hyDecay (d := d)) / ‖𝓕 hyPhi (0 : V)‖ ≤
      (hyFreq (d := d) N) - (hyRadius (d := d)) := by
  unfold hyFreq
  set A : ℝ := 4 * (N : ℝ) * (hyDecay (d := d)) / ‖𝓕 hyPhi (0 : V)‖
  have hR : 0 ≤ (hyRadius (d := d)) := (hyRadius_pos (d := d)).le
  linarith

/-- The frequency step is strictly larger than twice the continuity radius. -/
private lemma hyFreq_gt_two_radius (N : ℕ) : 2 * (hyRadius (d := d)) < (hyFreq (d := d) N) := by
  unfold hyFreq
  have hA : 0 ≤ 4 * (N : ℝ) * (hyDecay (d := d)) / ‖𝓕 hyPhi (0 : V)‖ :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (hyDecay_nonneg (d := d))) hyPhi_fourier_zero_pos.le
  linarith [hyRadius_pos (d := d)]

/-- The frequency gap is positive. -/
private lemma hyFreq_sub_radius_pos (N : ℕ) : 0 < (hyFreq (d := d) N) - (hyRadius (d := d)) := by
  linarith [hyFreq_gt_two_radius (d := d) N, hyRadius_pos (d := d)]

/-- Summing the `N` decay tails costs at most a quarter of the central mass. -/
private lemma hy_tail_budget (N : ℕ) :
    (N : ℝ) * (hyDecay (d := d)) / ((hyFreq (d := d) N) - (hyRadius (d := d))) ≤
      ‖𝓕 hyPhi (0 : V)‖ / 4 := by
  set δ : ℝ := ‖𝓕 hyPhi (0 : V)‖
  have hδ : 0 < δ := hyPhi_fourier_zero_pos
  have hgap : 0 < (hyFreq (d := d) N) - (hyRadius (d := d)) := hyFreq_sub_radius_pos (d := d) N
  have hge := hyFreq_gap (d := d) N
  by_cases hC : (hyDecay (d := d)) = 0
  · rw [hC, mul_zero, zero_div]
    positivity
  · have hCpos : 0 < (hyDecay (d := d)) :=
      lt_of_le_of_ne (hyDecay_nonneg (d := d)) (Ne.symm hC)
    have hmul : δ * (4 * (N : ℝ) * (hyDecay (d := d)) / δ) = 4 * (N : ℝ) * (hyDecay (d := d)) := by
      field_simp
    have hle : 4 * (N : ℝ) * (hyDecay (d := d)) ≤
        δ * ((hyFreq (d := d) N) - (hyRadius (d := d))) := by
      calc
        4 * (N : ℝ) * (hyDecay (d := d)) = δ * (4 * (N : ℝ) * (hyDecay (d := d)) / δ) := hmul.symm
        _ ≤ δ * ((hyFreq (d := d) N) - (hyRadius (d := d))) := by gcongr
    rw [div_le_div_iff₀ hgap (by norm_num : (0 : ℝ) < 4)]
    linarith

/-- Outside the continuity scale, the bump's Fourier transform is at most the decay budget. -/
private lemma hyPhi_fourier_tail {N : ℕ} {w : V}
    (hw : (hyFreq (d := d) N) - (hyRadius (d := d)) < ‖w‖) :
    ‖𝓕 hyPhi w‖ ≤ (hyDecay (d := d)) / ((hyFreq (d := d) N) - (hyRadius (d := d))) := by
  have hgap : 0 < (hyFreq (d := d) N) - (hyRadius (d := d)) := hyFreq_sub_radius_pos (d := d) N
  have hwpos : 0 < ‖w‖ := hgap.trans hw
  have hdiv : ‖𝓕 hyPhi w‖ ≤ (hyDecay (d := d)) / ‖w‖ := by
    rw [le_div_iff₀ hwpos, mul_comm]
    exact hyPhi_fourier_decay w
  exact hdiv.trans (div_le_div_of_nonneg_left hyDecay_nonneg hgap hw.le)

/-- Fourier transform of one modulated translate, up to a phase of modulus one. -/
private lemma fourier_hyPacket (hd : 0 < d) (R T : ℝ) (k : ℕ) (ξ : V) :
    𝓕 (hyPacket hd R T k) ξ =
      cexp (↑(-2 * π * ⟪hyOnAxis hd R k, ξ - hyOnAxis hd T k⟫) * I) *
        𝓕 hyPhi (ξ - hyOnAxis hd T k) := by
  set y : V := hyOnAxis hd R k
  set c : V := hyOnAxis hd T k
  set t : ℝ := (k : ℝ) * T
  have hc : c = t • hyBasis hd := by simp [c, t, hyOnAxis]
  rw [fourier_eq']
  have hpoint : ∀ x : V, cexp (↑(-2 * π * ⟪x, ξ⟫) * I) * hyPacket hd R T k x =
      cexp (↑(-2 * π * ⟪y, ξ - c⟫) * I) *
        (cexp (↑(-2 * π * ⟪x - y, ξ - c⟫) * I) * hyPhi (x - y)) := by
    intro x
    have hphase : hyPhase hd t x = cexp (↑(2 * π * ⟪x, c⟫) * I) := by
      simpa [hc] using hyPhase_eq_inner hd t x
    rw [hyPacket, hphase]
    rw [← mul_assoc (cexp (↑(-2 * π * ⟪x, ξ⟫) * I))]
    rw [← Complex.exp_add]
    rw [← mul_assoc (cexp (↑(-2 * π * ⟪y, ξ - c⟫) * I))]
    rw [← Complex.exp_add]
    refine congrArg (fun z : ℂ => z * hyPhi (x - y)) ?_
    refine congrArg cexp ?_
    rw [← add_mul, ← add_mul]
    refine congrArg (fun z : ℂ => z * I) ?_
    rw [← Complex.ofReal_add, ← Complex.ofReal_add]
    refine congrArg Complex.ofReal ?_
    have hsplit : ⟪x, ξ - c⟫ = ⟪x - y, ξ - c⟫ + ⟪y, ξ - c⟫ := by
      rw [← inner_add_left]
      congr 1
      abel
    calc
      -2 * π * ⟪x, ξ⟫ + 2 * π * ⟪x, c⟫
          = -2 * π * (⟪x, ξ⟫ - ⟪x, c⟫) := by ring
      _ = -2 * π * ⟪x, ξ - c⟫ := by rw [← inner_sub_right]
      _ = -2 * π * (⟪x - y, ξ - c⟫ + ⟪y, ξ - c⟫) := by rw [hsplit]
      _ = -2 * π * ⟪y, ξ - c⟫ + -2 * π * ⟪x - y, ξ - c⟫ := by ring
  simp_rw [smul_eq_mul, hpoint]
  rw [integral_const_mul]
  congr 1
  set fint : V → ℂ := fun x ↦ cexp (↑(-2 * π * ⟪x, ξ - c⟫) * I) * hyPhi x
  have hfun : (fun x : V ↦ cexp (↑(-2 * π * ⟪x - y, ξ - c⟫) * I) * hyPhi (x - y)) =
      fun x : V ↦ fint (x + -y) := by
    ext x
    unfold fint
    rw [sub_eq_add_neg]
  rw [hfun, integral_add_right_eq_self fint (-y), fourier_eq']
  simp [fint, smul_eq_mul]

/-- Modulation and translation preserve the modulus of the Fourier transform. -/
private lemma norm_fourier_hyPacket (hd : 0 < d) (R T : ℝ) (k : ℕ) (ξ : V) :
    ‖𝓕 (hyPacket hd R T k) ξ‖ = ‖𝓕 hyPhi (ξ - hyOnAxis hd T k)‖ := by
  rw [fourier_hyPacket, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- The packets are integrable. -/
private lemma hyPacket_integrable (hd : 0 < d) (R T : ℝ) (k : ℕ) :
    Integrable (hyPacket hd R T k) volume := by
  have hcont : Continuous (hyPacket hd R T k) := by
    unfold hyPacket
    refine Continuous.mul ?_ ?_
    · unfold hyPhase
      exact Complex.continuous_exp.comp <|
        ((continuous_ofReal.comp <|
          (continuous_const.mul ((EuclideanSpace.proj (hyAxis hd)).continuous))).mul_const I)
    · exact hyPhi_continuous.comp (continuous_id.sub continuous_const)
  have hcompact : HasCompactSupport (hyPacket hd R T k) := by
    unfold hyPacket
    refine HasCompactSupport.mul_left ?_
    exact hyPhi_compact.comp_isClosedEmbedding
      (Homeomorph.addRight (-hyOnAxis hd R k)).isClosedEmbedding
  exact hcont.integrable_of_hasCompactSupport (μ := volume) hcompact

/-- The Fourier transform passes inside the finite sum of packets. -/
private lemma fourier_hyFun (hd : 0 < d) (T : ℝ) (N : ℕ) (ξ : V) :
    𝓕 (hyFun hd T N) ξ = ∑ k ∈ range N, 𝓕 (hyPacket hd 5 T k) ξ := by
  unfold hyFun
  rw [fourier_eq]
  simp_rw [smul_sum]
  rw [integral_finsetSum]
  · simp_rw [← fourier_eq]
  · intro k hk
    exact (fourierIntegral_convergent_iff ξ).2 (hyPacket_integrable hd 5 T k)

/-- Translates of the bump supported at distinct axis points cannot both be nonzero. -/
private lemma hyPhi_translated_disjoint (hd : 0 < d) {j k : ℕ} (hjk : j ≠ k) (x : V) :
    hyPhi (x - hyOnAxis hd 5 j) = 0 ∨ hyPhi (x - hyOnAxis hd 5 k) = 0 := by
  by_contra h
  push Not at h
  have hj : ‖x - hyOnAxis hd 5 j‖ < 2 := lt_of_not_ge <| by
    rw [← hyPhi_eq_zero_iff]; exact h.1
  have hk : ‖x - hyOnAxis hd 5 k‖ < 2 := lt_of_not_ge <| by
    rw [← hyPhi_eq_zero_iff]; exact h.2
  have hdist : ‖hyOnAxis hd 5 j - hyOnAxis hd 5 k‖ < 4 := by
    calc
      ‖hyOnAxis hd 5 j - hyOnAxis hd 5 k‖
          = ‖(x - hyOnAxis hd 5 k) - (x - hyOnAxis hd 5 j)‖ := by
            congr 1
            abel
      _ ≤ ‖x - hyOnAxis hd 5 k‖ + ‖x - hyOnAxis hd 5 j‖ := norm_sub_le _ _
      _ < 2 + 2 := by gcongr
      _ = 4 := by norm_num
  have hge : (5 : ℝ) ≤ ‖hyOnAxis hd 5 j - hyOnAxis hd 5 k‖ := by
    rw [norm_hyOnAxis_sub]
    have habs := one_le_abs_sub_nat j k hjk
    calc
      (5 : ℝ) = 1 * 5 := by norm_num
      _ ≤ |(j : ℝ) - k| * 5 := by gcongr
      _ = |(j : ℝ) - k| * |(5 : ℝ)| := by simp
  linarith

/-- At a given point the sum reduces to at most one packet. -/
private lemma hyFun_cases (hd : 0 < d) (T : ℝ) (N : ℕ) (x : V) :
    hyFun hd T N x = 0 ∨ ∃ k ∈ range N, hyFun hd T N x = hyPacket hd 5 T k x ∧
      ∀ j ∈ range N, j ≠ k → hyPhi (x - hyOnAxis hd 5 j) = 0 := by
  classical
  by_cases h : ∃ k ∈ range N, hyPhi (x - hyOnAxis hd 5 k) ≠ 0
  · right
    obtain ⟨k, hk, hk0⟩ := h
    refine ⟨k, hk, ?_, ?_⟩
    · unfold hyFun
      refine sum_eq_single_of_mem k hk ?_
      intro j hj hjk
      rcases hyPhi_translated_disjoint hd hjk x with hz | hz
      · simp [hyPacket, hz]
      · exact (hk0 hz).elim
    · intro j hj hjk
      rcases hyPhi_translated_disjoint hd hjk x with hz | hz
      · exact hz
      · exact (hk0 hz).elim
  · left
    push Not at h
    unfold hyFun
    exact sum_eq_zero fun k hk => by simp [hyPacket, h k hk]

/-- The summed packets are pointwise bounded by one. -/
private lemma hyFun_norm_le_one (hd : 0 < d) (T : ℝ) (N : ℕ) (x : V) :
    ‖hyFun hd T N x‖ ≤ 1 := by
  rcases hyFun_cases hd T N x with h0 | ⟨k, hk, hkfun, _⟩
  · simp [h0]
  · rw [hkfun, hyPacket, norm_mul, hyPhase_norm, one_mul, hyPhi,
      Complex.norm_of_nonneg hyBump.nonneg]
    exact hyBump.le_one

/-- Raising the summed packets to a positive power splits across the disjoint supports. -/
private lemma hy_enorm_rpow (hd : 0 < d) (T : ℝ) (N : ℕ) (x : V) {α : ℝ} (hα : 0 < α) :
    ‖hyFun hd T N x‖ₑ ^ α =
      ∑ k ∈ range N, ‖hyPhi (x - hyOnAxis hd 5 k)‖ₑ ^ α := by
  classical
  by_cases h : ∃ k ∈ range N, hyPhi (x - hyOnAxis hd 5 k) ≠ 0
  · obtain ⟨k, hk, hk0⟩ := h
    have honly : ∀ j ∈ range N, j ≠ k → hyPhi (x - hyOnAxis hd 5 j) = 0 := by
      intro j hj hjk
      rcases hyPhi_translated_disjoint hd hjk x with hz | hz
      · exact hz
      · exact (hk0 hz).elim
    have hfun : hyFun hd T N x = hyPacket hd 5 T k x := by
      unfold hyFun
      refine sum_eq_single_of_mem k hk ?_
      intro j hj hjk
      simp [hyPacket, honly j hj hjk]
    rw [hfun, hyPacket, enorm_mul, ← ofReal_norm, hyPhase_norm, ENNReal.ofReal_one, one_mul]
    symm
    refine sum_eq_single_of_mem k hk ?_
    intro j hj hjk
    simp [honly j hj hjk, ENNReal.zero_rpow_of_pos hα]
  · push Not at h
    have hfun : hyFun hd T N x = 0 := by
      unfold hyFun
      exact sum_eq_zero fun k hk => by simp [hyPacket, h k hk]
    rw [hfun, enorm_zero, ENNReal.zero_rpow_of_pos hα]
    symm
    exact Finset.sum_eq_zero (s := range N)
      (f := fun k : ℕ => ‖hyPhi (x - hyOnAxis hd 5 k)‖ₑ ^ α) fun k hk => by
        rw [h k hk, enorm_zero, ENNReal.zero_rpow_of_pos hα]

/-- Translating the bump does not change the integral of a power of its norm. -/
private lemma hy_lintegral_translate (hd : 0 < d) (k : ℕ) {α : ℝ} :
    (∫⁻ x : V, ‖hyPhi (x - hyOnAxis hd 5 k)‖ₑ ^ α ∂volume) =
      ∫⁻ x : V, ‖hyPhi x‖ₑ ^ α ∂volume := by
  have htrans := lintegral_add_right_eq_self (μ := (volume : Measure V))
    (fun x : V ↦ ‖hyPhi x‖ₑ ^ α) (-hyOnAxis hd 5 k)
  have hfun : (fun x : V ↦ ‖hyPhi (x - hyOnAxis hd 5 k)‖ₑ ^ α) =
      fun x : V ↦ ‖hyPhi (x + -hyOnAxis hd 5 k)‖ₑ ^ α := by
    ext x
    simp [sub_eq_add_neg]
  rw [hfun]
  exact htrans

/-- The `Lᵖ` mass of the sum is `N` times the mass of one bump, for finite positive `p`. -/
private lemma hyFun_lintegral_pow (hd : 0 < d) (T : ℝ) (N : ℕ) {α : ℝ} (hα : 0 < α) :
    ∫⁻ x : V, ‖hyFun hd T N x‖ₑ ^ α ∂volume =
      (N : ℝ≥0∞) * ∫⁻ x : V, ‖hyPhi x‖ₑ ^ α ∂volume := by
  simp_rw [hy_enorm_rpow hd T N _ hα]
  rw [lintegral_finsetSum']
  · simp_rw [hy_lintegral_translate hd]
    simp [sum_const, card_range, nsmul_eq_mul]
  · intro k hk
    exact ((hyPhi_continuous.comp
      (continuous_id.sub continuous_const)).aestronglyMeasurable.enorm).pow_const α

/-- The bump has essential supremum one. -/
private lemma hyPhi_eLpNorm_top : eLpNorm (hyPhi : V → ℂ) ∞ volume = 1 := by
  have hm : AEStronglyMeasurable (hyPhi : V → ℂ) (volume : Measure V) :=
    hyPhi_continuous.aestronglyMeasurable
  rw [eLpNorm_exponent_top hm, eLpNormEssSup_eq_essSup_enorm]
  apply le_antisymm
  · refine essSup_le_of_ae_le 1 (Eventually.of_forall fun x => ?_)
    change ‖hyPhi x‖ₑ ≤ 1
    rw [← ofReal_norm, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hyPhi, Complex.norm_of_nonneg (hyBump.nonneg : 0 ≤ hyBump x)]
    exact hyBump.le_one
  · refine le_of_not_gt fun hlt => ?_
    have hae := ae_lt_of_essSup_lt hlt
    have hball : 0 < volume (ball (0 : V) 1) := measure_ball_pos volume (0 : V) zero_lt_one
    have hsub : ball (0 : V) 1 ⊆ {x | ¬ ‖hyPhi x‖ₑ < 1} := by
      intro x hx
      have hφ : hyBump x = 1 := hyBump.one_of_mem_closedBall (ball_subset_closedBall hx)
      simp [hyPhi, hφ, ← ofReal_norm]
    rw [ae_iff] at hae
    exact (lt_of_lt_of_le hball (measure_mono hsub)).ne' hae

/-- Each modulated translate is continuous. -/
private lemma hyPacket_continuous (hd : 0 < d) (R T : ℝ) (k : ℕ) :
    Continuous (hyPacket hd R T k) := by
  unfold hyPacket
  refine Continuous.mul ?_ (hyPhi_continuous.comp (continuous_id.sub continuous_const))
  unfold hyPhase
  exact Complex.continuous_exp.comp <|
    ((continuous_ofReal.comp <|
      (continuous_const.mul ((EuclideanSpace.proj (hyAxis hd)).continuous))).mul_const I)

/-- The packet sum is continuous. -/
private lemma hyFun_continuous (hd : 0 < d) (T : ℝ) (N : ℕ) : Continuous (hyFun hd T N) := by
  unfold hyFun
  induction N with
  | zero =>
    simp
    exact continuous_const
  | succ N ih =>
    have hfun : (fun x : V ↦ ∑ k ∈ range (N + 1), hyPacket hd 5 T k x) =
        (fun x : V ↦ ∑ k ∈ range N, hyPacket hd 5 T k x) +
          fun x : V ↦ hyPacket hd 5 T N x := by
      ext x
      simp [sum_range_succ]
    rw [hfun]
    exact ih.add (hyPacket_continuous hd 5 T N)

/-- The summed packets have essential supremum at most one. -/
private lemma hyFun_eLpNorm_top (hd : 0 < d) (T : ℝ) (N : ℕ) :
    eLpNorm (hyFun hd T N) ∞ volume ≤ 1 := by
  have hm : AEStronglyMeasurable (hyFun hd T N) volume :=
    (hyFun_continuous hd T N).aestronglyMeasurable
  rw [eLpNorm_exponent_top hm, eLpNormEssSup_eq_essSup_enorm]
  refine essSup_le_of_ae_le 1 (Eventually.of_forall fun x => ?_)
  change ‖hyFun hd T N x‖ₑ ≤ 1
  rw [← ofReal_norm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (hyFun_norm_le_one hd T N x)

/-- Spatial norm of the packet sum, including the endpoint `p = ∞`. -/
private lemma eLpNorm_hyFun_le (hd : 0 < d) (T : ℝ) (N : ℕ) {p : ℝ≥0∞} (hp : 2 < p) :
    eLpNorm (hyFun hd T N) p volume ≤
      (N : ℝ≥0∞) ^ (p.toReal)⁻¹ * eLpNorm (hyPhi : V → ℂ) p volume := by
  by_cases htop : p = ∞
  · subst htop
    simpa [hyPhi_eLpNorm_top, ENNReal.rpow_zero] using hyFun_eLpNorm_top hd T N
  · have hp0 : p ≠ 0 := (zero_lt_two.trans hp).ne'
    have hα : 0 < p.toReal := ENNReal.toReal_pos hp0 htop
    have hm : AEStronglyMeasurable (hyFun hd T N) volume :=
      (hyFun_continuous hd T N).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 htop hm, hyFun_lintegral_pow hd T N hα]
    have hmφ : AEStronglyMeasurable (hyPhi : V → ℂ) (volume : Measure V) :=
      hyPhi_continuous.aestronglyMeasurable
    have hφ := eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 htop hmφ
    have hI : (∫⁻ x : V, ‖hyPhi x‖ₑ ^ p.toReal ∂volume) =
        eLpNorm (hyPhi : V → ℂ) p volume ^ p.toReal := by
      rw [hφ, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hα.ne', ENNReal.rpow_one]
    rw [hI, show 1 / p.toReal = (p.toReal)⁻¹ from (inv_eq_one_div _).symm,
      ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hα.le), ← ENNReal.rpow_mul,
      mul_inv_cancel₀ hα.ne', ENNReal.rpow_one]

/-- For conjugate exponents with `p > 2`, the Fourier exponent is strictly larger than `1 / p`. -/
private lemma hy_exp_gap {p q : ℝ≥0∞} (hp : 2 < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    q ≠ 0 ∧ q ≠ ∞ ∧ (p.toReal)⁻¹ < (q.toReal)⁻¹ := by
  have : ENNReal.HolderConjugate p q := (ENNReal.holderConjugate_iff).mpr hpq
  have hp1 : (1 : ℝ≥0∞) < p := by
    have hone : (1 : ℝ≥0∞) < 2 := by norm_num
    exact hone.trans hp
  refine ⟨ENNReal.HolderConjugate.ne_zero q p,
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).2 hp1).ne, ?_⟩
  by_cases htop : p = ∞
  · have hq : q = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one p q).1 htop
    simp [htop, hq]
  · have hqinv : (q.toReal)⁻¹ = 1 - (p.toReal)⁻¹ := by
      have hle : p⁻¹ ≤ 1 := by
        simpa using ENNReal.inv_le_inv.mpr (ENNReal.HolderConjugate.one_le p q)
      rw [← ENNReal.toReal_inv, ← ENNReal.HolderConjugate.one_sub_inv p q,
        ENNReal.toReal_sub_of_le hle (by simp), ENNReal.toReal_one, ENNReal.toReal_inv]
    have hpt : 2 < p.toReal :=
      (ENNReal.toReal_lt_toReal (by simp) htop).2 hp
    have hinv : (p.toReal)⁻¹ < 1 / 2 := by
      have hlt : (p.toReal)⁻¹ < (2 : ℝ)⁻¹ :=
        (inv_lt_inv₀ (by linarith : 0 < p.toReal) (by norm_num)).mpr hpt
      have hhalf : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
      linarith
    rw [hqinv]
    linarith

/-- Frequency balls of radius `(hyRadius (d := d))` are pairwise disjoint. -/
private lemma hy_freqBalls_pairwise (hd : 0 < d) (N : ℕ) :
    PairwiseDisjoint (↑(range N))
      (fun k => ball (hyOnAxis hd ((hyFreq (d := d) N)) k) (hyRadius (d := d))) := by
  intro j hj k hk hjk
  apply ball_disjoint_ball
  rw [dist_eq_norm, norm_hyOnAxis_sub]
  have habs : 1 ≤ |(j : ℝ) - k| := one_le_abs_sub_nat j k hjk
  have hT : 0 ≤ (hyFreq (d := d) N) := by
    linarith [hyFreq_gt_two_radius (d := d) N, hyRadius_pos (d := d)]
  calc
    (hyRadius (d := d)) + (hyRadius (d := d)) = 2 * (hyRadius (d := d)) := by ring
    _ ≤ (hyFreq (d := d) N) := (hyFreq_gt_two_radius (d := d) N).le
    _ ≤ |(j : ℝ) - k| * (hyFreq (d := d) N) := by
      simpa using mul_le_mul_of_nonneg_right habs hT
    _ = |(j : ℝ) - k| * |(hyFreq (d := d) N)| := by rw [abs_of_nonneg hT]

/-- On each frequency ball the packet sum stays above half the central mass. -/
private lemma hyFun_fourier_lower (hd : 0 < d) (N : ℕ) (k : ℕ) (hk : k ∈ range N)
    (ξ : V) (hξ : ξ ∈ ball (hyOnAxis hd ((hyFreq (d := d) N)) k) (hyRadius (d := d))) :
    ‖𝓕 hyPhi (0 : V)‖ / 2 < ‖𝓕 (hyFun hd ((hyFreq (d := d) N)) N) ξ‖ := by
  set T : ℝ := (hyFreq (d := d) N)
  set δ : ℝ := ‖𝓕 hyPhi (0 : V)‖
  have hδ : 0 < δ := hyPhi_fourier_zero_pos
  have hgap : 0 < T - (hyRadius (d := d)) := hyFreq_sub_radius_pos (d := d) N
  rw [fourier_hyFun]
  let z : ℕ → ℂ := fun i => 𝓕 (hyPacket hd 5 T i) ξ
  have hsplit : ∑ i ∈ range N, z i = z k + ∑ i ∈ (range N).erase k, z i := by
    simpa [add_comm] using (Finset.sum_erase_add (range N) z hk).symm
  have hmain : 3 / 4 * δ < ‖z k‖ := by
    rw [show ‖z k‖ = ‖𝓕 hyPhi (ξ - hyOnAxis hd T k)‖ from norm_fourier_hyPacket hd 5 T k ξ]
    apply hyPhi_fourier_near
    simpa [mem_ball, dist_eq_norm, dist_eq_norm_sub] using hξ
  have htail : ∀ i ∈ (range N).erase k, ‖z i‖ ≤ (hyDecay (d := d)) / (T - (hyRadius (d := d))) := by
    intro i hi
    rw [show ‖z i‖ = ‖𝓕 hyPhi (ξ - hyOnAxis hd T i)‖ from norm_fourier_hyPacket hd 5 T i ξ]
    apply hyPhi_fourier_tail
    have hine : i ≠ k := ne_of_mem_erase hi
    have hdist : T ≤ ‖hyOnAxis hd T k - hyOnAxis hd T i‖ := by
      rw [norm_hyOnAxis_sub]
      have habs : 1 ≤ |(k : ℝ) - i| := one_le_abs_sub_nat k i hine.symm
      have hTnonneg : 0 ≤ T := by linarith [hyFreq_gt_two_radius (d := d) N, hyRadius_pos (d := d)]
      calc
        T = 1 * T := by ring
        _ ≤ |(k : ℝ) - i| * T := by gcongr
        _ = |(k : ℝ) - i| * |T| := by rw [abs_of_nonneg hTnonneg]
    have hξnorm : ‖ξ - hyOnAxis hd T k‖ < (hyRadius (d := d)) := by
      simpa [mem_ball, dist_eq_norm] using hξ
    have hrev : ‖hyOnAxis hd T k - hyOnAxis hd T i‖ - ‖ξ - hyOnAxis hd T k‖ ≤
        ‖ξ - hyOnAxis hd T i‖ := by
      have htri := norm_le_add_norm_add (hyOnAxis hd T k - hyOnAxis hd T i)
        (ξ - hyOnAxis hd T k)
      have hu : ‖hyOnAxis hd T k - hyOnAxis hd T i‖ ≤
          ‖ξ - hyOnAxis hd T i‖ + ‖ξ - hyOnAxis hd T k‖ := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, norm_neg] using htri
      linarith
    linarith
  have hsum : ∑ i ∈ (range N).erase k, ‖z i‖ ≤ δ / 4 := by
    calc
      ∑ i ∈ (range N).erase k, ‖z i‖
          ≤ ∑ i ∈ (range N).erase k, (hyDecay (d := d)) / (T - (hyRadius (d := d))) := by
            exact sum_le_sum htail
      _ = ((range N).erase k).card * ((hyDecay (d := d)) / (T - (hyRadius (d := d)))) := by
            simp [sum_const]
      _ ≤ (N : ℝ) * ((hyDecay (d := d)) / (T - (hyRadius (d := d)))) := by
            have hnonneg : 0 ≤ (hyDecay (d := d)) / (T - (hyRadius (d := d))) :=
              div_nonneg (hyDecay_nonneg (d := d)) hgap.le
            have hcard : ((range N).erase k).card ≤ N :=
              (card_erase_le (s := range N) (a := k)).trans (by simp [card_range])
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hnonneg
      _ = (N : ℝ) * (hyDecay (d := d)) / (T - (hyRadius (d := d))) := by ring
      _ ≤ δ / 4 := hy_tail_budget (d := d) N
  have htri : ‖z k‖ - ∑ i ∈ (range N).erase k, ‖z i‖ ≤ ‖∑ i ∈ range N, z i‖ := by
    have hsub : z k = ∑ i ∈ range N, z i - ∑ i ∈ (range N).erase k, z i := by
      rw [hsplit]
      abel
    calc
      ‖z k‖ - ∑ i ∈ (range N).erase k, ‖z i‖
          ≤ ‖∑ i ∈ range N, z i‖ + ‖∑ i ∈ (range N).erase k, z i‖ -
              ∑ i ∈ (range N).erase k, ‖z i‖ := by
            gcongr
            rw [hsub]
            exact norm_sub_le _ _
      _ ≤ ‖∑ i ∈ range N, z i‖ := by
            have hnorm := norm_sum_le ((range N).erase k) z
            linarith
  linarith

/-- The summed packets are smooth. -/
private lemma hyFun_contDiff (hd : 0 < d) (T : ℝ) (N : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (hyFun hd T N) := by
  unfold hyFun
  refine ContDiff.sum fun k _ => ?_
  unfold hyPacket
  refine ContDiff.mul ?_ (hyPhi_contDiff.comp (contDiff_id.sub contDiff_const))
  unfold hyPhase
  refine ContDiff.cexp ?_
  exact (Complex.ofRealCLM.contDiff.comp <|
    contDiff_const.mul ((EuclideanSpace.proj (hyAxis hd)).contDiff)).mul contDiff_const

/-- The summed packets are compactly supported. -/
private lemma hyFun_compact (hd : 0 < d) (T : ℝ) (N : ℕ) :
    HasCompactSupport (hyFun hd T N) := by
  unfold hyFun
  simp_rw [← Finset.sum_apply]
  exact HasCompactSupport.finset_sum fun k _ => by
    unfold hyPacket
    refine HasCompactSupport.mul_left ?_
    exact hyPhi_compact.comp_isClosedEmbedding
      (Homeomorph.addRight (-hyOnAxis hd 5 k)).isClosedEmbedding

/-- The packet sum as a Schwartz function. -/
private def hySchwartz (hd : 0 < d) (T : ℝ) (N : ℕ) : SchwartzMap V ℂ :=
  (hyFun_compact hd T N).toSchwartzMap (hyFun_contDiff hd T N)

/-- The underlying function of `hySchwartz` is the packet sum. -/
private lemma hySchwartz_coe (hd : 0 < d) (T : ℝ) (N : ℕ) :
    (hySchwartz hd T N : V → ℂ) = hyFun hd T N := by
  rfl

/-- The continuity ball has positive volume. -/
private lemma hy_ball_measure_pos : 0 < volume (ball (0 : V) (hyRadius (d := d))) :=
  measure_ball_pos volume (0 : V) (hyRadius_pos (d := d))

/-- The continuity ball has finite volume. -/
private lemma hy_ball_measure_ne_top : volume (ball (0 : V) (hyRadius (d := d))) ≠ ∞ :=
  measure_ball_ne_top

end NotHausdorffYoung

/-- No Hausdorff–Young bound exists above exponent two in positive Euclidean dimension,
already when tested on Schwartz functions. -/
theorem not_hausdorff_young {d : ℕ} (hd : 0 < d) {p q : ℝ≥0∞}
    (hp : 2 < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    ¬ ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ,
      eLpNorm (𝓕 (f : EuclideanSpace ℝ (Fin d) → ℂ)) q volume ≤
        C * eLpNorm f p volume := by
  intro ⟨C, hC, hbound⟩
  let V := EuclideanSpace ℝ (Fin d)
  have hgap := hy_exp_gap hp hpq
  have hq0 : q ≠ 0 := hgap.1
  have hqtop : q ≠ ∞ := hgap.2.1
  set β : ℝ := (q.toReal)⁻¹
  set γ : ℝ := (p.toReal)⁻¹
  have hβγ : γ < β := hgap.2.2
  have hβpos : 0 < β := by linarith [inv_nonneg.mpr (ENNReal.toReal_nonneg (a := p))]
  set δ : ℝ := ‖𝓕 (hyPhi : V → ℂ) (0 : V)‖
  have hδ : 0 < δ := hyPhi_fourier_zero_pos
  set v : ℝ≥0∞ := volume (ball (0 : V) (hyRadius (d := d)))
  have hvpos : 0 < v := hy_ball_measure_pos (d := d)
  have hvtop : v ≠ ∞ := hy_ball_measure_ne_top (d := d)
  have hvR : 0 < v.toReal := ENNReal.toReal_pos hvpos.ne' hvtop
  set K : ℝ≥0∞ := eLpNorm (hyPhi : V → ℂ) p volume
  have hK : K ≠ ∞ := by
    by_cases htop : p = ∞
    · simp [K, htop, hyPhi_eLpNorm_top]
    · exact (hyPhi_continuous.memLp_of_hasCompactSupport (μ := volume) hyPhi_compact).eLpNorm_ne_top
  have hρpos : 0 < δ / 2 * v.toReal ^ β := by positivity
  have hboundN : ∀ N : ℕ, 1 ≤ N →
      δ / 2 * v.toReal ^ β * (N : ℝ) ^ (β - γ) ≤ C.toReal * K.toReal := by
    intro N hN
    let T : ℝ := (hyFreq (d := d) N)
    let fS : SchwartzMap V ℂ := hySchwartz hd T N
    have hfS : (fS : V → ℂ) = hyFun hd T N := hySchwartz_coe hd T N
    have hspace : eLpNorm (hyFun hd T N) p volume ≤ (N : ℝ≥0∞) ^ γ * K := by
      simpa [K, γ] using eLpNorm_hyFun_le hd T N hp
    have hspace_fin : eLpNorm (fS : V → ℂ) p volume ≠ ∞ := by
      rw [hfS]
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (by finiteness) hK) hspace
    have hFT := hbound fS
    rw [hfS] at hFT
    set s : Set V := ⋃ k ∈ range N, ball (hyOnAxis hd T k) (hyRadius (d := d))
    have hsmeas : MeasurableSet s :=
      (isOpen_biUnion fun _ _ => isOpen_ball).measurableSet
    have hdisj := hy_freqBalls_pairwise hd N
    have hμs : volume s = (N : ℝ≥0∞) * v := by
      unfold s
      rw [measure_biUnion_finset hdisj fun _ _ => measurableSet_ball]
      simp_rw [Measure.addHaar_ball_center (volume : Measure V)]
      simp [sum_const, card_range, nsmul_eq_mul, v]
    have hpoint : ∀ ξ, s.indicator (fun _ => ENNReal.ofReal (δ / 2) ^ q.toReal) ξ ≤
        ‖𝓕 (hyFun hd T N) ξ‖ₑ ^ q.toReal := by
      intro ξ
      by_cases hξ : ξ ∈ s
      · rw [indicator_of_mem hξ]
        obtain ⟨k, hk, hkξ⟩ := mem_iUnion₂.1 hξ
        have hlow : δ / 2 ≤ ‖𝓕 (hyFun hd T N) ξ‖ :=
          le_of_lt <| by simpa [δ, T] using hyFun_fourier_lower hd N k hk ξ hkξ
        have hnorm : ENNReal.ofReal (δ / 2) ≤ ‖𝓕 (hyFun hd T N) ξ‖ₑ := by
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal hlow
        exact ENNReal.rpow_le_rpow hnorm (ENNReal.toReal_nonneg)
      · simp [hξ]
    have hmeas : AEStronglyMeasurable (𝓕 (hyFun hd T N)) volume :=
      aestronglyMeasurable_of_eLpNorm_ne_top <|
        ne_top_of_le_ne_top (ENNReal.mul_ne_top hC hspace_fin) hFT
    have hlin : ENNReal.ofReal (δ / 2) ^ q.toReal * volume s ≤
        ∫⁻ ξ, ‖𝓕 (hyFun hd T N) ξ‖ₑ ^ q.toReal ∂volume := by
      rw [← lintegral_indicator_const hsmeas]
      exact lintegral_mono hpoint
    have hlow : ENNReal.ofReal (δ / 2) * v ^ β * (N : ℝ≥0∞) ^ β ≤
        eLpNorm (𝓕 (hyFun hd T N)) q volume := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop hmeas]
      have hβeq : β = 1 / q.toReal := by simp only [β, inv_eq_one_div]
      rw [← hβeq]
      refine le_trans ?_ (ENNReal.rpow_le_rpow hlin hβpos.le)
      rw [hμs]
      refine le_of_eq ?_
      have hβq : q.toReal * β = 1 := by
        simpa [β] using mul_inv_cancel₀ (ENNReal.toReal_pos hq0 hqtop).ne'
      have hδpow : ENNReal.ofReal (δ / 2) =
          (ENNReal.ofReal (δ / 2) ^ q.toReal) ^ β := by
        rw [← ENNReal.rpow_mul, hβq, ENNReal.rpow_one]
      calc
        ENNReal.ofReal (δ / 2) * v ^ β * (N : ℝ≥0∞) ^ β
            = ENNReal.ofReal (δ / 2) * ((N : ℝ≥0∞) ^ β * v ^ β) := by ac_rfl
        _ = ENNReal.ofReal (δ / 2) * ((N : ℝ≥0∞) * v) ^ β := by
              rw [← ENNReal.mul_rpow_of_nonneg _ _ hβpos.le]
        _ = (ENNReal.ofReal (δ / 2) ^ q.toReal) ^ β * ((N : ℝ≥0∞) * v) ^ β := by
              nth_rw 1 [hδpow]
        _ = (ENNReal.ofReal (δ / 2) ^ q.toReal * ((N : ℝ≥0∞) * v)) ^ β := by
              rw [← ENNReal.mul_rpow_of_nonneg _ _ hβpos.le]
    have hup : eLpNorm (𝓕 (hyFun hd T N)) q volume ≤ C * (N : ℝ≥0∞) ^ γ * K := by
      calc
        eLpNorm (𝓕 (hyFun hd T N)) q volume ≤ C * eLpNorm (hyFun hd T N) p volume := hFT
        _ ≤ C * ((N : ℝ≥0∞) ^ γ * K) := by gcongr
        _ = C * (N : ℝ≥0∞) ^ γ * K := by rw [mul_assoc]
    have hcmp : ENNReal.ofReal (δ / 2) * (N : ℝ≥0∞) ^ β * v ^ β ≤
        C * (N : ℝ≥0∞) ^ γ * K := by
      calc
        ENNReal.ofReal (δ / 2) * (N : ℝ≥0∞) ^ β * v ^ β
            = ENNReal.ofReal (δ / 2) * v ^ β * (N : ℝ≥0∞) ^ β := by ac_rfl
        _ ≤ eLpNorm (𝓕 (hyFun hd T N)) q volume := hlow
        _ ≤ C * (N : ℝ≥0∞) ^ γ * K := hup
    have hleft_fin : ENNReal.ofReal (δ / 2) * (N : ℝ≥0∞) ^ β * v ^ β ≠ ∞ := by finiteness
    have hright_fin : C * (N : ℝ≥0∞) ^ γ * K ≠ ∞ := by finiteness
    have hreal := (ENNReal.toReal_le_toReal hleft_fin hright_fin).2 hcmp
    have hNcast : ((N : ℝ≥0∞)).toReal = (N : ℝ) := by simp
    have hL : (ENNReal.ofReal (δ / 2) * (N : ℝ≥0∞) ^ β * v ^ β).toReal =
        δ / 2 * (N : ℝ) ^ β * v.toReal ^ β := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ δ / 2), ← ENNReal.toReal_rpow, hNcast,
        ← ENNReal.toReal_rpow]
    have hR : (C * (N : ℝ≥0∞) ^ γ * K).toReal = C.toReal * (N : ℝ) ^ γ * K.toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, hNcast]
    rw [hL, hR] at hreal
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hN)
    have hsplit : (N : ℝ) ^ β = (N : ℝ) ^ γ * (N : ℝ) ^ (β - γ) := by
      rw [← Real.rpow_add hNpos, add_sub_cancel]
    have hpow : 0 < (N : ℝ) ^ γ := Real.rpow_pos_of_pos hNpos γ
    have hrearr : (N : ℝ) ^ γ * (δ / 2 * v.toReal ^ β * (N : ℝ) ^ (β - γ)) ≤
        (N : ℝ) ^ γ * (C.toReal * K.toReal) := by
      calc
        (N : ℝ) ^ γ * (δ / 2 * v.toReal ^ β * (N : ℝ) ^ (β - γ))
            = δ / 2 * ((N : ℝ) ^ γ * (N : ℝ) ^ (β - γ)) * v.toReal ^ β := by ring
        _ = δ / 2 * (N : ℝ) ^ β * v.toReal ^ β := by rw [← hsplit]
        _ ≤ C.toReal * (N : ℝ) ^ γ * K.toReal := hreal
        _ = (N : ℝ) ^ γ * (C.toReal * K.toReal) := by ring
    exact (mul_le_mul_iff_of_pos_left hpow).mp hrearr
  have htend : Tendsto (fun N : ℕ => (N : ℝ) ^ (β - γ)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hβγ)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := tendsto_atTop_atTop.mp htend
    (C.toReal * K.toReal / (δ / 2 * v.toReal ^ β) + 1)
  set M : ℕ := max N₀ 1
  have hsmall := hboundN M (le_max_right _ _)
  have hgrow := hN₀ M (le_max_left _ _)
  have hlt : C.toReal * K.toReal < δ / 2 * v.toReal ^ β * (M : ℝ) ^ (β - γ) := by
    have hdiv : C.toReal * K.toReal / (δ / 2 * v.toReal ^ β) < (M : ℝ) ^ (β - γ) := by
      linarith
    have hmul := (div_lt_iff₀ hρpos).mp hdiv
    rwa [mul_comm ((M : ℝ) ^ (β - γ))] at hmul
  exact lt_irrefl _ (hsmall.trans_lt hlt)

end CKMA
