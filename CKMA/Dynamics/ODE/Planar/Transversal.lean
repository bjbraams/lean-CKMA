/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.ODE.Planar.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Order.LeftRightNhds

import Mathlib.Tactic.Module

/-!
# Transverse segments for a planar flow

On the plane identified with `ℂ`, the signed height of a point relative to an oriented
segment is the real inner product against the rotate of the segment direction. A segment
is transverse when this height increases along every orbit that meets it. A regular point
lies on such a segment, an orbit meets the segment in isolated times, and every orbit that
passes close to an interior point crosses the open segment in a short time.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Metric Set Topology
open scoped ComplexConjugate InnerProductSpace

/-- Signed height of `z` from the oriented line through `a` and `b`. -/
def transverseSide (a b z : ℂ) : ℝ :=
  ⟪z - a, Complex.I * (b - a)⟫_ℝ

/-- Real coordinate of `z` along the direction `b - a`. -/
def lineParam (a b z : ℂ) : ℝ :=
  ((z - a) / (b - a)).re

/-- A segment meets `F` transversely when `F` has positive height derivative along it. -/
structure IsTransverseSegment (F : ℂ → ℂ) (a b : ℂ) : Prop where
  /-- The endpoints of a transverse segment are distinct. -/
  ne : a ≠ b
  /-- The generator points to the positive side of the segment. -/
  pos : ∀ z ∈ segment ℝ a b, 0 < ⟪F z, Complex.I * (b - a)⟫_ℝ

/-- The real inner product of a complex number with its rotate vanishes. -/
private theorem real_inner_I_mul_self (w : ℂ) : ⟪w, Complex.I * w⟫_ℝ = 0 := by
  rw [Complex.inner]
  have hmul : (Complex.I * w) * conj w = Complex.I * ↑(‖w‖ ^ 2) := by
    rw [show (Complex.I * w) * conj w = Complex.I * (w * conj w) by ring,
      Complex.mul_conj', ← Complex.ofReal_pow]
  rw [hmul, mul_comm, Complex.re_ofReal_mul, Complex.I_re, mul_zero]

/-- Height vanishes at every real multiple of the segment direction. -/
theorem transverseSide_line (a b : ℂ) (θ : ℝ) :
    transverseSide a b (a + θ • (b - a)) = 0 := by
  rw [transverseSide, add_sub_cancel_left, real_inner_smul_left, real_inner_I_mul_self,
    mul_zero]

/-- The line coordinate of a point displaced by `θ` along `b - a` is `θ`. -/
theorem lineParam_line {a b : ℂ} (hab : a ≠ b) (θ : ℝ) :
    lineParam a b (a + θ • (b - a)) = θ := by
  have hv : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  rw [lineParam, add_sub_cancel_left, Complex.real_smul, mul_div_cancel_right₀ _ hv,
    Complex.ofReal_re]

/-- Height is the squared length of `b - a` times the imaginary part of `(z - a) / (b - a)`. -/
theorem transverseSide_eq_normSq_mul_im (a b z : ℂ) :
    transverseSide a b z = ‖b - a‖ ^ 2 * ((z - a) / (b - a)).im := by
  by_cases hab : a = b
  · simp [hab, transverseSide, sub_self, mul_zero, inner_zero_right, div_zero,
      Complex.zero_im]
  · set v : ℂ := b - a
    have hv : v ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    set c : ℂ := (z - a) / v
    have hc : z - a = c * v := (div_mul_cancel₀ (z - a) hv).symm
    rw [transverseSide, Complex.inner, hc]
    have hmul : (Complex.I * v) * conj (c * v) =
        ↑(‖v‖ ^ 2) * (Complex.I * conj c) := by
      rw [map_mul]
      rw [show (Complex.I * v) * (conj c * conj v) =
          (Complex.I * conj c) * (v * conj v) by ring, Complex.mul_conj',
        ← Complex.ofReal_pow, mul_comm]
    rw [hmul, Complex.re_ofReal_mul]
    have him : (Complex.I * conj c).re = c.im := by
      rw [Complex.I_mul_re, Complex.conj_im, neg_neg]
    rw [him]

/-- A point of height zero lies on the real line through `a` and `b`. -/
theorem eq_add_lineParam_of_transverseSide_eq_zero {a b z : ℂ} (hab : a ≠ b)
    (hz : transverseSide a b z = 0) :
    z = a + lineParam a b z • (b - a) := by
  have hv : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  set v : ℂ := b - a
  set c : ℂ := (z - a) / v
  have hc : z - a = c * v := (div_mul_cancel₀ (z - a) hv).symm
  have him : c.im = 0 := by
    have hmul := transverseSide_eq_normSq_mul_im a b z
    rw [hz] at hmul
    have hnorm : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
    exact (mul_eq_zero.mp hmul.symm).resolve_left hnorm
  have hc' : c = (c.re : ℂ) := by
    conv_lhs => rw [← Complex.re_add_im c]
    rw [him, Complex.ofReal_zero, zero_mul, add_zero]
  rw [hc', ← Complex.real_smul] at hc
  have hre : lineParam a b z = c.re := by
    simp only [lineParam, c, v]
  calc
    z = a + (z - a) := by rw [add_sub_cancel]
    _ = a + c.re • v := by rw [hc]
    _ = a + lineParam a b z • v := by rw [← hre]

/-- Height vanishes on a closed segment. -/
theorem transverseSide_eq_zero_of_mem_segment {a b z : ℂ} (hz : z ∈ segment ℝ a b) :
    transverseSide a b z = 0 := by
  rw [segment_eq_image'] at hz
  obtain ⟨θ, _, rfl⟩ := hz
  exact transverseSide_line a b θ

/-- Height and the line coordinate describe the open segment. -/
theorem mem_openSegment_iff_lineParam {a b z : ℂ} (hab : a ≠ b) :
    z ∈ openSegment ℝ a b ↔
      transverseSide a b z = 0 ∧ lineParam a b z ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · intro hz
    rw [openSegment_eq_image'] at hz
    obtain ⟨θ, hθ, hzeq⟩ := hz
    have hpt : z = a + θ • (b - a) := by simpa using hzeq.symm
    rw [hpt, transverseSide_line, lineParam_line hab θ]
    exact ⟨rfl, hθ⟩
  · intro ⟨hside, hθ⟩
    rw [openSegment_eq_image']
    exact ⟨lineParam a b z, hθ,
      by simpa using (eq_add_lineParam_of_transverseSide_eq_zero hab hside).symm⟩

/-- Height and the line coordinate describe the closed segment. -/
theorem mem_segment_iff_lineParam {a b z : ℂ} (hab : a ≠ b) :
    z ∈ segment ℝ a b ↔
      transverseSide a b z = 0 ∧ lineParam a b z ∈ Icc (0 : ℝ) 1 := by
  constructor
  · intro hz
    rw [segment_eq_image'] at hz
    obtain ⟨θ, hθ, hzeq⟩ := hz
    have hpt : z = a + θ • (b - a) := by simpa using hzeq.symm
    rw [hpt, transverseSide_line, lineParam_line hab θ]
    exact ⟨rfl, hθ⟩
  · intro ⟨hside, hθ⟩
    rw [segment_eq_image']
    exact ⟨lineParam a b z, hθ,
      by simpa using (eq_add_lineParam_of_transverseSide_eq_zero hab hside).symm⟩

/-- A point of an open segment lies strictly between the endpoints in line coordinate. -/
theorem lineParam_mem_Ioo_of_mem_openSegment {a b z : ℂ} (hab : a ≠ b)
    (hz : z ∈ openSegment ℝ a b) : lineParam a b z ∈ Ioo (0 : ℝ) 1 :=
  ((mem_openSegment_iff_lineParam hab).mp hz).2

/-- Distance along a line is parameter separation times the direction length. -/
theorem dist_eq_abs_sub_mul_norm {a b p q : ℂ} (hab : a ≠ b)
    (hp : transverseSide a b p = 0) (hq : transverseSide a b q = 0) :
    dist p q = |lineParam a b p - lineParam a b q| * ‖b - a‖ := by
  set v : ℂ := b - a
  set sp : ℝ := lineParam a b p
  set sq : ℝ := lineParam a b q
  have hp' : p = a + sp • v := eq_add_lineParam_of_transverseSide_eq_zero hab hp
  have hq' : q = a + sq • v := eq_add_lineParam_of_transverseSide_eq_zero hab hq
  have hsub : p - q = (sp - sq) • v := by
    rw [hp', hq']
    module
  rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]

/-- The open segment from an interior point toward `b` stays inside the original segment. -/
theorem openSegment_subset_openSegment_right {a b u : ℂ} (hab : a ≠ b)
    (hu : u ∈ openSegment ℝ a b) :
    openSegment ℝ u b ⊆ openSegment ℝ a b := by
  intro z hz
  rw [openSegment_eq_image'] at hz
  obtain ⟨θ, hθ, hzeq⟩ := hz
  have hpt : z = u + θ • (b - u) := by simpa using hzeq.symm
  set sp : ℝ := lineParam a b u
  have hsp : sp ∈ Ioo (0 : ℝ) 1 := lineParam_mem_Ioo_of_mem_openSegment hab hu
  have hu' : u = a + sp • (b - a) :=
    eq_add_lineParam_of_transverseSide_eq_zero hab
      ((mem_openSegment_iff_lineParam hab).mp hu).1
  have hbp : b - u = (1 - sp) • (b - a) := by
    rw [hu']
    module
  have hz' : z = a + (sp + θ * (1 - sp)) • (b - a) := by
    rw [hpt, hbp, hu']
    module
  rw [hz', mem_openSegment_iff_lineParam hab]
  refine ⟨transverseSide_line a b _, ?_⟩
  rw [lineParam_line hab (sp + θ * (1 - sp))]
  constructor
  · have hpos : 0 < θ * (1 - sp) := mul_pos hθ.1 (sub_pos.mpr hsp.2)
    linarith [hsp.1]
  · have hden : 0 < 1 - sp := sub_pos.mpr hsp.2
    have hmul : θ * (1 - sp) < 1 - sp := by
      simpa [one_mul] using (mul_lt_mul_iff_of_pos_right hden).mpr hθ.2
    linarith

/-- The open segment from `a` to an interior point stays inside the original segment. -/
theorem openSegment_subset_openSegment_left {a b u : ℂ} (hab : a ≠ b)
    (hu : u ∈ openSegment ℝ a b) :
    openSegment ℝ a u ⊆ openSegment ℝ a b := by
  intro z hz
  rw [openSegment_eq_image'] at hz
  obtain ⟨θ, hθ, hzeq⟩ := hz
  have hpt : z = a + θ • (u - a) := by simpa using hzeq.symm
  set sp : ℝ := lineParam a b u
  have hsp : sp ∈ Ioo (0 : ℝ) 1 := lineParam_mem_Ioo_of_mem_openSegment hab hu
  have hu' : u = a + sp • (b - a) :=
    eq_add_lineParam_of_transverseSide_eq_zero hab
      ((mem_openSegment_iff_lineParam hab).mp hu).1
  have hz' : z = a + (θ * sp) • (b - a) := by
    rw [hpt, hu']
    module
  rw [hz', mem_openSegment_iff_lineParam hab]
  refine ⟨transverseSide_line a b _, ?_⟩
  rw [lineParam_line hab (θ * sp)]
  constructor
  · exact mul_pos hθ.1 hsp.1
  · have hmul : θ * sp < sp := by
      simpa [one_mul] using (mul_lt_mul_iff_of_pos_right hsp.1).mpr hθ.2
    exact hmul.trans hsp.2

/-- On one open segment, moving toward `b` is an increase of the line coordinate. -/
theorem mem_openSegment_right_iff {a b p q : ℂ} (hab : a ≠ b)
    (hp : p ∈ openSegment ℝ a b) (hq : q ∈ openSegment ℝ a b) :
    q ∈ openSegment ℝ p b ↔ lineParam a b p < lineParam a b q := by
  set sp : ℝ := lineParam a b p
  set sq : ℝ := lineParam a b q
  have hp' : p = a + sp • (b - a) :=
    eq_add_lineParam_of_transverseSide_eq_zero hab
      ((mem_openSegment_iff_lineParam hab).mp hp).1
  have hq' : q = a + sq • (b - a) :=
    eq_add_lineParam_of_transverseSide_eq_zero hab
      ((mem_openSegment_iff_lineParam hab).mp hq).1
  have hsp : sp ∈ Ioo (0 : ℝ) 1 := lineParam_mem_Ioo_of_mem_openSegment hab hp
  have hsq : sq ∈ Ioo (0 : ℝ) 1 := lineParam_mem_Ioo_of_mem_openSegment hab hq
  have hbp : b - p = (1 - sp) • (b - a) := by
    rw [hp']
    module
  constructor
  · intro hqpb
    rw [openSegment_eq_image'] at hqpb
    obtain ⟨θ, hθ, hθq⟩ := hqpb
    have hpt : q = p + θ • (b - p) := by simpa using hθq.symm
    have hz : q = a + (sp + θ * (1 - sp)) • (b - a) := by
      rw [hpt, hbp, hp']
      module
    have hlin : sq = sp + θ * (1 - sp) := by
      rw [← show lineParam a b q = sq from rfl, hz,
        lineParam_line hab (sp + θ * (1 - sp))]
    have hpos : 0 < θ * (1 - sp) := mul_pos hθ.1 (sub_pos.mpr hsp.2)
    linarith
  · intro hlt
    have hden : 0 < 1 - sp := sub_pos.mpr hsp.2
    have hsq1 : sq < 1 := hsq.2
    let θ : ℝ := (sq - sp) / (1 - sp)
    have hθ0 : 0 < θ := div_pos (sub_pos.mpr hlt) hden
    have hθ1 : θ < 1 := (div_lt_one hden).mpr (by linarith)
    rw [openSegment_eq_image']
    refine ⟨θ, ⟨hθ0, hθ1⟩, ?_⟩
    have hθmul : θ * (1 - sp) = sq - sp := by
      simpa [θ] using div_mul_cancel₀ (sq - sp) hden.ne'
    have hz : p + θ • (b - p) = q := by
      rw [hbp, hp', smul_smul, hθmul, add_assoc, ← add_smul]
      have hcoef : sp + (sq - sp) = sq := by ring
      rw [hcoef, ← hq']
    simpa using hz

/-- A point of the open segment whose line coordinate is smaller than `v` lies before `v`. -/
theorem mem_openSegment_of_lineParam_lt {a b v x : ℂ} (hab : a ≠ b)
    (hv : v ∈ openSegment ℝ a b) (hx : x ∈ openSegment ℝ a b)
    (hlt : lineParam a b x < lineParam a b v) : x ∈ openSegment ℝ a v := by
  set px : ℝ := lineParam a b x
  set pv : ℝ := lineParam a b v
  have hpv : 0 < pv := (lineParam_mem_Ioo_of_mem_openSegment hab hv).1
  have hpx : 0 < px := (lineParam_mem_Ioo_of_mem_openSegment hab hx).1
  have hx' : x = a + px • (b - a) :=
    eq_add_lineParam_of_transverseSide_eq_zero hab
      ((mem_openSegment_iff_lineParam hab).mp hx).1
  have hv' : v = a + pv • (b - a) :=
    eq_add_lineParam_of_transverseSide_eq_zero hab
      ((mem_openSegment_iff_lineParam hab).mp hv).1
  rw [openSegment_eq_image']
  refine ⟨px / pv, ⟨div_pos hpx hpv, (div_lt_one hpv).mpr hlt⟩, ?_⟩
  have hvsub : v - a = pv • (b - a) := by
    rw [hv']
    module
  have hz : a + (px / pv) • (v - a) = x := by
    rw [hvsub, smul_smul, div_mul_cancel₀ _ hpv.ne', hx']
  simpa using hz

/-- A point closer to `u` than `v` is, with `v` beyond `u`, still lies before `v`. -/
theorem openSegment_separate_left {a b u v x : ℂ} (hu : u ∈ openSegment ℝ a b)
    (hv : v ∈ openSegment ℝ u b) (hx : x ∈ openSegment ℝ a b)
    (hdist : dist x u < dist u v) : x ∈ openSegment ℝ a v := by
  have hab : a ≠ b := by
    intro hab
    have hu' : u = b := by
      rw [hab, openSegment_same] at hu
      exact mem_singleton_iff.mp hu
    have hv' : v = b := by
      rw [hu', openSegment_same] at hv
      exact mem_singleton_iff.mp hv
    exact (not_lt_of_ge dist_nonneg) (by simpa [hu', hv', dist_self] using hdist)
  have hvab : v ∈ openSegment ℝ a b := openSegment_subset_openSegment_right hab hu hv
  have hlt : lineParam a b u < lineParam a b v :=
    (mem_openSegment_right_iff hab hu hvab).mp hv
  have hsideu : transverseSide a b u = 0 :=
    ((mem_openSegment_iff_lineParam hab).mp hu).1
  have hsidev : transverseSide a b v = 0 :=
    ((mem_openSegment_iff_lineParam hab).mp hvab).1
  have hsidex : transverseSide a b x = 0 :=
    ((mem_openSegment_iff_lineParam hab).mp hx).1
  have hnorm : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hab))
  have hparam : |lineParam a b x - lineParam a b u| <
      lineParam a b v - lineParam a b u := by
    have hxu := dist_eq_abs_sub_mul_norm hab hsidex hsideu
    have huv := dist_eq_abs_sub_mul_norm hab hsideu hsidev
    rw [hxu, huv, abs_sub_comm (lineParam a b u) (lineParam a b v),
      abs_of_pos (sub_pos.mpr hlt)] at hdist
    exact (mul_lt_mul_iff_of_pos_right hnorm).mp hdist
  have hxlt : lineParam a b x < lineParam a b v := by
    have habs := abs_lt.mp hparam
    linarith
  exact mem_openSegment_of_lineParam_lt hab hvab hx hxlt

/-- A point closer to `u` than `v` is, with `v` before `u`, still lies after `v`. -/
theorem openSegment_separate_right {a b u v x : ℂ} (hu : u ∈ openSegment ℝ a b)
    (hv : v ∈ openSegment ℝ a u) (hx : x ∈ openSegment ℝ a b)
    (hdist : dist x u < dist u v) : x ∈ openSegment ℝ v b := by
  have hab : a ≠ b := by
    intro hab
    have hu' : u = b := by
      rw [hab, openSegment_same] at hu
      exact mem_singleton_iff.mp hu
    have hv' : v = b := by
      rw [hab, hu', openSegment_same] at hv
      exact mem_singleton_iff.mp hv
    exact (not_lt_of_ge dist_nonneg) (by simpa [hu', hv', dist_self] using hdist)
  have hvab : v ∈ openSegment ℝ a b := openSegment_subset_openSegment_left hab hu hv
  have hpv : lineParam a b v < lineParam a b u := by
    set sp : ℝ := lineParam a b u
    have hsp : sp ∈ Ioo (0 : ℝ) 1 := lineParam_mem_Ioo_of_mem_openSegment hab hu
    have hsideu : transverseSide a b u = 0 :=
      ((mem_openSegment_iff_lineParam hab).mp hu).1
    have hu' : u = a + sp • (b - a) :=
      eq_add_lineParam_of_transverseSide_eq_zero hab hsideu
    rw [openSegment_eq_image'] at hv
    obtain ⟨θ, hθ, hzeq⟩ := hv
    have hpt : v = a + θ • (u - a) := by simpa using hzeq.symm
    have hz : v = a + (θ * sp) • (b - a) := by
      rw [hpt, hu']
      module
    rw [hz, lineParam_line hab (θ * sp)]
    simpa [sp, one_mul] using (mul_lt_mul_iff_of_pos_right hsp.1).mpr hθ.2
  have hsideu : transverseSide a b u = 0 :=
    ((mem_openSegment_iff_lineParam hab).mp hu).1
  have hsidev : transverseSide a b v = 0 :=
    ((mem_openSegment_iff_lineParam hab).mp hvab).1
  have hsidex : transverseSide a b x = 0 :=
    ((mem_openSegment_iff_lineParam hab).mp hx).1
  have hnorm : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hab))
  have hparam : |lineParam a b x - lineParam a b u| <
      lineParam a b u - lineParam a b v := by
    have hxu := dist_eq_abs_sub_mul_norm hab hsidex hsideu
    have huv := dist_eq_abs_sub_mul_norm hab hsideu hsidev
    rw [hxu, huv, abs_of_pos (sub_pos.mpr hpv)] at hdist
    exact (mul_lt_mul_iff_of_pos_right hnorm).mp hdist
  have hxgt : lineParam a b v < lineParam a b x := by
    have habs := abs_lt.mp hparam
    linarith
  exact (mem_openSegment_right_iff hab hvab hx).mpr hxgt

/-- Height along an orbit is differentiable, with derivative the height of the generator. -/
theorem hasDerivAt_transverseSide {φ : Flow ℝ ℂ} {F : ℂ → ℂ}
    (hgen : FlowHasGenerator φ F) (x : ℂ) (t : ℝ) (a b : ℂ) :
    HasDerivAt (fun s ↦ transverseSide a b (φ s x))
      (⟪F (φ t x), Complex.I * (b - a)⟫_ℝ) t := by
  have hcurve : HasDerivAt (fun s ↦ φ s x - a) (F (φ t x)) t :=
    (hgen x t).sub_const a
  have hconst : HasDerivAt (fun _ : ℝ ↦ Complex.I * (b - a)) 0 t :=
    hasDerivAt_const t _
  simpa [transverseSide, inner_zero_right, zero_add] using
    HasDerivAt.inner ℝ hcurve hconst

/-- Height is continuous. -/
theorem continuous_transverseSide (a b : ℂ) :
    Continuous fun z : ℂ ↦ transverseSide a b z := by
  unfold transverseSide
  fun_prop

/-- A positive derivative makes a real function strictly larger on the right and smaller
on the left. -/
private theorem exists_sign_of_hasDerivAt_pos {f : ℝ → ℝ} {t c : ℝ}
    (hf : HasDerivAt f c t) (hc : 0 < c) :
    ∃ δ > 0, (∀ s, s ∈ Ioo t (t + δ) → f t < f s) ∧
      (∀ s, s ∈ Ioo (t - δ) t → f s < f t) := by
  have hpos : ∀ᶠ s in 𝓝[≠] t, 0 < slope f t s :=
    hf.tendsto_slope.eventually (Ioi_mem_nhds hc)
  rw [eventually_nhdsWithin_iff] at hpos
  obtain ⟨ε, hε0, hε⟩ := Metric.mem_nhds_iff.mp (eventually_iff.mp hpos)
  refine ⟨ε, hε0, ?_, ?_⟩
  · intro s hs
    have hsball : s ∈ ball t ε := by
      rw [mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hs.1)]
      linarith [hs.2]
    have hslope : 0 < slope f t s := (hε hsball) (ne_of_gt hs.1)
    rw [slope_def_field] at hslope
    have hsub : 0 < s - t := sub_pos.mpr hs.1
    have hmul : 0 < f s - f t := by
      have := mul_pos hslope hsub
      rwa [div_mul_cancel₀ _ hsub.ne'] at this
    linarith
  · intro s hs
    have hsball : s ∈ ball t ε := by
      rw [mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hs.2)]
      linarith [hs.1]
    have hslope : 0 < slope f t s := (hε hsball) (ne_of_lt hs.2)
    rw [slope_def_field] at hslope
    have hsub : f s - f t < 0 := by
      rcases div_pos_iff.mp hslope with hsame | hsame
      · exact absurd hsame.2 (not_lt_of_ge (sub_nonpos.mpr hs.2.le))
      · exact hsame.1
    linarith

/-- Every regular point is the midpoint of a transverse segment. -/
theorem exists_isTransverseSegment {F : ℂ → ℂ} (hF : Continuous F) {p : ℂ}
    (hp : F p ≠ 0) :
    ∃ a b : ℂ, p ∈ openSegment ℝ a b ∧ IsTransverseSegment F a b := by
  set v : ℂ := F p
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hp
  set u : ℂ := -Complex.I * v / (‖v‖ : ℂ)
  have hu : ‖u‖ = 1 := by
    rw [norm_div, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg hv0.le, div_self hv0.ne']
  have hinner : Continuous fun z : ℂ ↦ ⟪F z, v⟫_ℝ :=
    Complex.continuous_re.comp
      (continuous_const.mul (Complex.continuous_conj.comp hF))
  have hpos0 : 0 < ⟪v, v⟫_ℝ := real_inner_self_pos.mpr hp
  have hnhds : {z : ℂ | 0 < ⟪F z, v⟫_ℝ} ∈ 𝓝 p :=
    hinner.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hpos0)
  obtain ⟨r, hr0, hr⟩ := Metric.mem_nhds_iff.mp hnhds
  set δ : ℝ := r / 2
  have hδ0 : 0 < δ := half_pos hr0
  set a : ℂ := p - δ • u
  set b : ℂ := p + δ • u
  have hba : b - a = (2 * δ) • u := by
    simp only [a, b]
    module
  have hab : a ≠ b := by
    intro h
    have : ‖b - a‖ = 0 := by simp [h]
    rw [hba, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos two_pos hδ0), hu,
      mul_one] at this
    linarith
  have hseg : segment ℝ a b ⊆ ball p r := by
    intro z hz
    rw [segment_eq_image'] at hz
    obtain ⟨θ, hθ, hzeq⟩ := hz
    have hpt : z = a + θ • (b - a) := by simpa using hzeq.symm
    have hzp : z - p = (δ * (2 * θ - 1)) • u := by
      rw [hpt, hba, smul_smul]
      simp only [a]
      module
    rw [mem_ball, dist_eq_norm, hzp, norm_smul, Real.norm_eq_abs, hu, mul_one,
      abs_mul, abs_of_pos hδ0]
    have habs : |2 * θ - 1| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hθ.1, hθ.2]
    have hle : δ * |2 * θ - 1| ≤ δ := by
      have hmul := mul_le_mul_of_nonneg_right habs hδ0.le
      linarith
    have hδr : δ < r := by
      simp only [δ]
      linarith
    linarith
  have hpos : ∀ z ∈ segment ℝ a b, 0 < ⟪F z, v⟫_ℝ := by
    intro z hz
    exact hr (hseg hz)
  have hIu : Complex.I * u = v / (‖v‖ : ℂ) := by
    unfold u
    rw [div_eq_mul_inv, ← mul_assoc, ← mul_assoc]
    have hII : Complex.I * -Complex.I = (1 : ℂ) := by
      rw [mul_neg, Complex.I_mul_I, neg_neg]
    rw [hII, one_mul, ← div_eq_mul_inv]
  have hdir : Complex.I * (b - a) = ((2 * δ) / ‖v‖) • v := by
    rw [hba, Complex.real_smul, mul_left_comm, hIu, div_eq_mul_inv, mul_comm v,
      ← mul_assoc, ← div_eq_mul_inv, ← Complex.ofReal_div, ← Complex.real_smul]
  refine ⟨a, b, ?_, ?_⟩
  · simpa [a, b] using mem_openSegment_sub_add p (δ • u)
  · refine ⟨hab, ?_⟩
    intro z hz
    rw [hdir, real_inner_smul_right]
    exact mul_pos (div_pos (mul_pos two_pos hδ0) hv0) (hpos z hz)

/-- A small ball about an interior point meets the line only inside the open segment. -/
theorem exists_ball_subset_openSegment {a b p : ℂ} (hab : a ≠ b)
    (hp : p ∈ openSegment ℝ a b) :
    ∃ ρ > 0, ∀ z, dist z p < ρ → transverseSide a b z = 0 →
      z ∈ openSegment ℝ a b := by
  set s : ℝ := lineParam a b p
  have hs : s ∈ Ioo (0 : ℝ) 1 := lineParam_mem_Ioo_of_mem_openSegment hab hp
  have hnorm : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hab))
  set ρ : ℝ := min s (1 - s) * ‖b - a‖
  have hρ0 : 0 < ρ := mul_pos (lt_min hs.1 (sub_pos.mpr hs.2)) hnorm
  refine ⟨ρ, hρ0, ?_⟩
  intro z hz hside
  have hdist := dist_eq_abs_sub_mul_norm hab hside
    ((mem_openSegment_iff_lineParam hab).mp hp).1
  rw [hdist] at hz
  have hlt : |lineParam a b z - s| < min s (1 - s) :=
    (mul_lt_mul_iff_of_pos_right hnorm).mp hz
  have habs := abs_lt.mp hlt
  rw [mem_openSegment_iff_lineParam hab]
  refine ⟨hside, ?_⟩
  have hmin1 : min s (1 - s) ≤ s := min_le_left _ _
  have hmin2 : min s (1 - s) ≤ 1 - s := min_le_right _ _
  constructor <;> linarith [habs.1, habs.2, hmin1, hmin2]

/-- An orbit through a point sufficiently close to an interior point of a transverse segment
crosses that open segment within a prescribed short time, and the crossing stays close. -/
theorem exists_crossing_time {φ : Flow ℝ ℂ} {F : ℂ → ℂ} (hgen : FlowHasGenerator φ F)
    {a b : ℂ} (htr : IsTransverseSegment F a b) {p : ℂ}
    (hp : p ∈ openSegment ℝ a b) :
    ∀ ε > 0, ∃ δ > 0, ∀ z, dist z p < δ →
      ∃ t : ℝ, |t| < ε ∧ dist (φ t z) p < ε ∧ φ t z ∈ openSegment ℝ a b := by
  intro ε hε
  obtain ⟨ρ, hρ0, hρ⟩ := exists_ball_subset_openSegment htr.ne hp
  set ρ' : ℝ := min ρ ε
  have hρ' : 0 < ρ' := lt_min hρ0 hε
  set f : ℝ → ℝ := fun s ↦ transverseSide a b (φ s p)
  have hf0 : f 0 = 0 := by
    unfold f
    rw [φ.map_zero_apply p]
    exact transverseSide_eq_zero_of_mem_segment
      (openSegment_subset_segment _ _ _ hp)
  have hder : HasDerivAt f (⟪F p, Complex.I * (b - a)⟫_ℝ) 0 := by
    simpa [f, φ.map_zero_apply] using hasDerivAt_transverseSide hgen p 0 a b
  have hpos : 0 < ⟪F p, Complex.I * (b - a)⟫_ℝ :=
    htr.pos p (openSegment_subset_segment _ _ _ hp)
  obtain ⟨δs, hδs, hright, hleft⟩ := exists_sign_of_hasDerivAt_pos hder hpos
  have hcontp : Continuous fun t : ℝ ↦ φ t p := continuous_id.flow φ continuous_const
  obtain ⟨η0, hη00, hη0⟩ := Metric.continuousAt_iff.mp hcontp.continuousAt ρ' hρ'
  set η : ℝ := min (η0 / 2) (min (δs / 2) ε)
  have hη : 0 < η := lt_min (half_pos hη00) (lt_min (half_pos hδs) hε)
  have hη_η0 : η < η0 := by
    have : η ≤ η0 / 2 := min_le_left _ _
    linarith
  have hη_δs : η < δs := by
    have : η ≤ δs / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hη_ε : η ≤ ε := le_trans (min_le_right _ _) (min_le_right _ _)
  have hsignL : f (-η) < 0 := by
    rw [← hf0]
    exact hleft (-η) ⟨by linarith, by linarith⟩
  have hsignR : 0 < f η := by
    rw [← hf0]
    exact hright η ⟨by linarith, by linarith⟩
  have htube : Icc (-η) η ×ˢ {p} ⊆ {q | dist (φ q.1 q.2) p < ρ'} := by
    intro q hq
    have hdist0 : dist q.1 (0 : ℝ) < η0 := by
      rw [Real.dist_eq, sub_zero]
      have : |q.1| ≤ η := abs_le.mpr ⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩
      linarith
    simpa [mem_singleton_iff.mp hq.2] using hη0 hdist0
  have hn : IsOpen {q : ℝ × ℂ | dist (φ q.1 q.2) p < ρ'} :=
    isOpen_lt (φ.cont'.dist continuous_const) continuous_const
  obtain ⟨u, v, -, hv, hsu, hsv, huv⟩ :=
    generalized_tube_lemma (isCompact_Icc (a := -η) (b := η))
      (isCompact_singleton (x := p)) hn htube
  obtain ⟨δ1, hδ10, hδ1⟩ := Metric.mem_nhds_iff.mp (hv.mem_nhds (hsv (mem_singleton p)))
  have hcontL : Continuous fun z ↦ transverseSide a b (φ (-η) z) :=
    (continuous_transverseSide a b).comp (continuous_const.flow φ continuous_id)
  have hcontR : Continuous fun z ↦ transverseSide a b (φ η z) :=
    (continuous_transverseSide a b).comp (continuous_const.flow φ continuous_id)
  obtain ⟨δ2, hδ20, hδ2⟩ := Metric.mem_nhds_iff.mp
    (hcontL.continuousAt.preimage_mem_nhds (Iio_mem_nhds hsignL))
  obtain ⟨δ3, hδ30, hδ3⟩ := Metric.mem_nhds_iff.mp
    (hcontR.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hsignR))
  refine ⟨min δ1 (min δ2 δ3), lt_min hδ10 (lt_min hδ20 hδ30), ?_⟩
  intro z hz
  have hz1 : dist z p < δ1 := lt_of_lt_of_le hz (min_le_left _ _)
  have hz2 : dist z p < δ2 :=
    lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _))
  have hz3 : dist z p < δ3 :=
    lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_right _ _))
  have hL : transverseSide a b (φ (-η) z) < 0 := by
    have : z ∈ (fun w ↦ transverseSide a b (φ (-η) w)) ⁻¹' Iio 0 := hδ2 hz2
    simpa using this
  have hR : 0 < transverseSide a b (φ η z) := by
    have : z ∈ (fun w ↦ transverseSide a b (φ η w)) ⁻¹' Ioi 0 := hδ3 hz3
    simpa using this
  set g : ℝ → ℝ := fun t ↦ transverseSide a b (φ t z)
  have hg : ContinuousOn g (Icc (-η) η) :=
    ((continuous_transverseSide a b).comp
      (continuous_id.flow φ continuous_const)).continuousOn
  obtain ⟨t, ht, htg⟩ :=
    (intermediate_value_Ioo (by linarith : (-η) ≤ η) hg) ⟨hL, hR⟩
  have htI : t ∈ Icc (-η) η := ⟨ht.1.le, ht.2.le⟩
  have hdistz : dist (φ t z) p < ρ' := by
    have hmem : (t, z) ∈ u ×ˢ v := ⟨hsu htI, hδ1 (mem_ball.mpr hz1)⟩
    simpa using huv hmem
  refine ⟨t, ?_, lt_of_lt_of_le hdistz (min_le_right _ _), ?_⟩
  · rw [abs_lt]
    constructor <;> linarith [ht.1, ht.2, hη_ε]
  · exact hρ _ (lt_of_lt_of_le hdistz (min_le_left _ _)) htg

/-- A compact time interval meets a transverse segment in finitely many times. -/
theorem finite_orbit_segment {φ : Flow ℝ ℂ} {F : ℂ → ℂ} (hgen : FlowHasGenerator φ F)
    {a b : ℂ} (htr : IsTransverseSegment F a b) (x : ℂ) {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    {t : ℝ | t ∈ Icc t₁ t₂ ∧ φ t x ∈ segment ℝ a b}.Finite := by
  set S : Set ℝ := {t : ℝ | t ∈ Icc t₁ t₂ ∧ φ t x ∈ segment ℝ a b}
  have hcont : Continuous fun t : ℝ ↦ φ t x := continuous_id.flow φ continuous_const
  have hseg : IsClosed (segment ℝ a b) := by
    rw [segment_eq_image']
    exact (isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))).isClosed
  have hclosed : IsClosed S := by
    have hEq : S = (fun t : ℝ ↦ φ t x) ⁻¹' segment ℝ a b ∩ Icc t₁ t₂ := by
      ext t
      change (t ∈ Icc t₁ t₂ ∧ φ t x ∈ segment ℝ a b) ↔
        φ t x ∈ segment ℝ a b ∧ t ∈ Icc t₁ t₂
      exact and_comm
    rw [hEq]
    exact (hseg.preimage hcont).inter isClosed_Icc
  have hcomp : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hclosed (fun t htS ↦ htS.1)
  have hdisc : IsDiscrete S := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro t₀ ht₀
    have hside0 : transverseSide a b (φ t₀ x) = 0 :=
      transverseSide_eq_zero_of_mem_segment ht₀.2
    have hder := hasDerivAt_transverseSide hgen x t₀ a b
    have hpos : 0 < ⟪F (φ t₀ x), Complex.I * (b - a)⟫_ℝ := htr.pos _ ht₀.2
    obtain ⟨δ, hδ0, hright, hleft⟩ := exists_sign_of_hasDerivAt_pos hder hpos
    refine ⟨Ioo (t₀ - δ) (t₀ + δ), isOpen_Ioo, ?_⟩
    ext t
    constructor
    · intro ht
      rcases ht with ⟨htI, htS⟩
      rcases htI with ⟨hltδ, hgtδ⟩
      rcases htS with ⟨-, hsegmem⟩
      rcases lt_trichotomy t t₀ with hlt | rfl | hgt
      · have hzero := transverseSide_eq_zero_of_mem_segment hsegmem
        have hlt' := hleft t ⟨hltδ, hlt⟩
        rw [hzero, hside0] at hlt'
        exact absurd hlt' (lt_irrefl _)
      · rfl
      · have hzero := transverseSide_eq_zero_of_mem_segment hsegmem
        have hgt' := hright t ⟨hgt, hgtδ⟩
        rw [hside0, hzero] at hgt'
        exact absurd hgt' (lt_irrefl _)
    · intro ht
      have ht' : t = t₀ := by simpa using ht
      subst ht'
      exact ⟨⟨by linarith, by linarith⟩, ht₀⟩
  have _ : t₁ ≤ t₂ := ht
  exact hcomp.finite hdisc

end CKMA
