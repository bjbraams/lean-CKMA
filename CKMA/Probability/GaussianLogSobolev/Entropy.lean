/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.GaussianLogSobolev.OneDim

/-!
# Entropy derivative of the Ornstein–Uhlenbeck semigroup

For a smooth positive function with bounded derivatives, the Gaussian entropy along the
Ornstein–Uhlenbeck semigroup decreases at the rate of the Fisher information.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Real Topology

/-- Logarithms of the semigroup stay bounded when the integrand takes values in `[δ, M]`. -/
lemma abs_log_ouSemigroup_le {f : ℝ → ℝ} {s x δ M : ℝ} (hf : Continuous f) (hδ : 0 < δ)
    (hδf : ∀ y, δ ≤ f y) (hM : ∀ y, |f y| ≤ M) :
    |Real.log (ouSemigroup s f x)| ≤ max |Real.log δ| |Real.log M| := by
  have hpos : 0 < ouSemigroup s f x :=
    lt_of_lt_of_le hδ (ouSemigroup_lower hf ⟨M, hM⟩ hδf)
  have hu_le : ouSemigroup s f x ≤ M :=
    ouSemigroup_upper hf ⟨M, hM⟩ (fun y => (le_abs_self (f y)).trans (hM y))
  have hle1 := Real.log_le_log hδ (ouSemigroup_lower (t := s) (x := x) hf ⟨M, hM⟩ hδf)
  have hle2 := Real.log_le_log hpos hu_le
  refine abs_le.mpr ⟨?_, ?_⟩
  · exact ((neg_le_neg (le_max_left _ _)).trans (neg_abs_le _)).trans hle1
  · exact (hle2.trans (le_abs_self _)).trans (le_max_right _ _)

/-- The spatial integral of the semigroup time derivative vanishes. -/
lemma integral_timeDeriv_ouSemigroup {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (hf : ContDiff ℝ 2 f)
    (hB : ∃ B, ∀ y, |deriv f y| ≤ B) (hB2 : ∃ B2, ∀ y, |deriv (deriv f) y| ≤ B2)
    (hM : ∃ M, ∀ y, |f y| ≤ M) :
    ∫ x, deriv (fun s => ouSemigroup s f x) t ∂gaussianReal 0 1 = 0 := by
  obtain ⟨B, hB⟩ := hB
  obtain ⟨B2, hB2⟩ := hB2
  obtain ⟨M, hM⟩ := hM
  obtain ⟨hf1, hf'1⟩ := contDiff_one_deriv_of_two hf
  let γ : Measure ℝ := gaussianReal 0 1
  let sset : Set ℝ := Ioo (t / 2) (t + 1)
  have hs : sset ∈ nhds t := Ioo_mem_nhds (by linarith) (by linarith)
  let F : ℝ → ℝ → ℝ := fun s x => ouSemigroup s f x
  let F' : ℝ → ℝ → ℝ := fun s x => deriv (fun r => ouSemigroup r f x) s
  let C : ℝ := 1 / ouStdev (t / 2)
  let Iabs : ℝ := ∫ y, |y| ∂γ
  let bound : ℝ → ℝ := fun x => |B| * (|x| + C * Iabs)
  have hmeas : ∀ s, AEStronglyMeasurable (F s) γ := fun _ =>
    (continuous_ouSemigroup hf.continuous ⟨M, hM⟩).aestronglyMeasurable
  have hF_int : Integrable (F t) γ :=
    integrable_of_abs_le (hmeas t) (fun x => abs_ouSemigroup_le hf.continuous hM)
  have hdt_cont : Continuous (F' t) := by
    have hfun : F' t = fun x =>
        deriv (deriv (ouSemigroup t f)) x - x * deriv (ouSemigroup t f) x := by
      funext x
      exact deriv_ouSemigroup_eq_generator (x := x) ht hf ⟨B, hB⟩ ⟨B2, hB2⟩ ⟨M, hM⟩
    rw [hfun]
    have h1 : Continuous (deriv (ouSemigroup t f)) := by
      have hrew : deriv (ouSemigroup t f) = fun x =>
          ouScale t * ouSemigroup t (deriv f) x :=
        funext fun x => deriv_ouSemigroup_space hf1 ⟨B, hB⟩ ⟨M, hM⟩
      rw [hrew]
      exact continuous_const.mul (continuous_ouSemigroup hf1.continuous_deriv_one ⟨B, hB⟩)
    have h2 : Continuous (deriv (deriv (ouSemigroup t f))) := by
      have hrew : deriv (deriv (ouSemigroup t f)) = fun x =>
          ouScale t ^ 2 * ouSemigroup t (deriv (deriv f)) x :=
        funext fun x => deriv_ouSemigroup_space₂ hf ⟨B, hB⟩ ⟨B2, hB2⟩ ⟨M, hM⟩
      rw [hrew]
      exact continuous_const.mul (continuous_ouSemigroup hf'1.continuous_deriv_one ⟨B2, hB2⟩)
    exact h2.sub (continuous_id.mul h1)
  have hF'_meas : AEStronglyMeasurable (F' t) γ := hdt_cont.aestronglyMeasurable
  have h_bound : ∀ᵐ x ∂γ, ∀ s ∈ sset, ‖F' s x‖ ≤ bound x := by
    refine ae_of_all _ fun x s hsx => ?_
    rw [Real.norm_eq_abs]
    have hs1 : t / 2 < s := hsx.1
    exact abs_deriv_ouSemigroup_time_le (s := s) (x := x) (t0 := t / 2)
      (by linarith : 0 < t / 2) (le_of_lt hs1) hf1 hB ⟨M, hM⟩
  have hbound_int : Integrable bound γ := by
    have hfun : bound = fun x => |B| * |x| + |B| * C * Iabs := by
      funext x
      ring
    rw [hfun]
    exact (integrable_abs_gaussianReal.const_mul _).add (integrable_const _)
  have h_diff : ∀ᵐ x ∂γ, ∀ s ∈ sset, HasDerivAt (F · x) (F' s x) s := by
    refine ae_of_all _ fun x s hsx => ?_
    have hs0 : 0 < s := by
      have : t / 2 < s := hsx.1
      linarith
    have hAt := hasDerivAt_ouSemigroup_time (x := x) hs0 hf1 ⟨B, hB⟩ ⟨M, hM⟩
    exact hAt.congr_deriv hAt.deriv.symm
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := γ) (F := F) (F' := F') (bound := bound) (x₀ := t) (s := sset)
    hs (Filter.Eventually.of_forall hmeas) hF_int hF'_meas h_bound hbound_int h_diff
  have heq : (fun s => ∫ x, F s x ∂γ) =ᶠ[nhds t] fun _ => ∫ x, f x ∂γ := by
    filter_upwards [hs] with s hsx
    have hs0 : 0 < s := by
      have : t / 2 < s := hsx.1
      linarith
    simpa [F] using integral_ouSemigroup (le_of_lt hs0) hf.continuous ⟨M, hM⟩
  have hderiv0 : deriv (fun s => ∫ x, F s x ∂γ) t = 0 := by
    rw [heq.deriv_eq]
    simp [deriv_const']
  have hderiv_eq : deriv (fun s => ∫ x, F s x ∂γ) t = ∫ x, F' t x ∂γ := hderiv.2.deriv
  have hzero : ∫ x, F' t x ∂γ = 0 := by
    rw [← hderiv_eq, hderiv0]
  simpa [F', γ] using hzero

/-- The entropy integral decreases at the Fisher-information rate. -/
lemma hasDerivAt_entropy_ouSemigroup {f : ℝ → ℝ} {t δ : ℝ} (ht : 0 < t) (hf : ContDiff ℝ 2 f)
    (hδ : 0 < δ) (hδf : ∀ y, δ ≤ f y) (hB : ∃ B, ∀ y, |deriv f y| ≤ B)
    (hB2 : ∃ B2, ∀ y, |deriv (deriv f) y| ≤ B2) (hM : ∃ M, ∀ y, |f y| ≤ M) :
    HasDerivAt (fun s => ∫ x, ouSemigroup s f x * Real.log (ouSemigroup s f x)
        ∂gaussianReal 0 1)
      (-∫ x, (deriv (ouSemigroup t f) x) ^ 2 / ouSemigroup t f x ∂gaussianReal 0 1) t := by
  obtain ⟨B, hB⟩ := hB
  obtain ⟨B2, hB2⟩ := hB2
  obtain ⟨M, hM⟩ := hM
  obtain ⟨hf1, _⟩ := contDiff_one_deriv_of_two hf
  have hMpos : 0 < M := lt_of_lt_of_le hδ ((hδf 0).trans ((le_abs_self _).trans (hM 0)))
  let γ : Measure ℝ := gaussianReal 0 1
  let sset : Set ℝ := Ioo (t / 2) (t + 1)
  have hs : sset ∈ nhds t := Ioo_mem_nhds (by linarith) (by linarith)
  let F : ℝ → ℝ → ℝ := fun s x => ouSemigroup s f x * Real.log (ouSemigroup s f x)
  let F' : ℝ → ℝ → ℝ := fun s x =>
    (deriv (fun r => ouSemigroup r f x) s) * (Real.log (ouSemigroup s f x) + 1)
  let C : ℝ := 1 / ouStdev (t / 2)
  let Iabs : ℝ := ∫ y, |y| ∂γ
  let L : ℝ := max |Real.log δ| |Real.log M| + 1
  let bound : ℝ → ℝ := fun x => (|B| * (|x| + C * Iabs)) * L
  have hpos_s : ∀ s x, δ ≤ ouSemigroup s f x := fun s x =>
    ouSemigroup_lower hf.continuous ⟨M, hM⟩ hδf
  have hmeas : ∀ s, AEStronglyMeasurable (F s) γ := by
    intro s
    have hu : Continuous (ouSemigroup s f) := continuous_ouSemigroup hf.continuous ⟨M, hM⟩
    have hlog : Continuous (fun x => Real.log (ouSemigroup s f x)) :=
      hu.log (fun x => (lt_of_lt_of_le hδ (hpos_s s x)).ne')
    exact (hu.mul hlog).aestronglyMeasurable
  have hF_int : Integrable (F t) γ := by
    have hL0 : ∀ x, |F t x| ≤ M * (max |Real.log δ| |Real.log M|) + 1 := fun x => by
      have habs : |ouSemigroup t f x| ≤ M := abs_ouSemigroup_le hf.continuous hM
      have hlog := abs_log_ouSemigroup_le (s := t) (x := x) hf.continuous hδ hδf hM
      rw [abs_mul]
      have hmul := mul_le_mul habs hlog (abs_nonneg _) (le_trans (abs_nonneg _) (hM 0))
      exact hmul.trans (le_add_of_nonneg_right zero_le_one)
    exact integrable_of_abs_le (hmeas t) hL0
  have hdt_cont : Continuous (fun x => deriv (fun r => ouSemigroup r f x) t) := by
    have hfun : (fun x => deriv (fun r => ouSemigroup r f x) t) =
        fun x => deriv (deriv (ouSemigroup t f)) x - x * deriv (ouSemigroup t f) x := by
      funext x
      exact deriv_ouSemigroup_eq_generator (x := x) ht hf ⟨B, hB⟩ ⟨B2, hB2⟩ ⟨M, hM⟩
    rw [hfun]
    obtain ⟨hf1', hf'1⟩ := contDiff_one_deriv_of_two hf
    have h1 : Continuous (deriv (ouSemigroup t f)) := by
      have hrew : deriv (ouSemigroup t f) = fun x =>
          ouScale t * ouSemigroup t (deriv f) x :=
        funext fun x => deriv_ouSemigroup_space (t := t) (x := x) hf1' ⟨B, hB⟩ ⟨M, hM⟩
      rw [hrew]
      exact continuous_const.mul (continuous_ouSemigroup hf1'.continuous_deriv_one ⟨B, hB⟩)
    have h2 : Continuous (deriv (deriv (ouSemigroup t f))) := by
      have hrew : deriv (deriv (ouSemigroup t f)) = fun x =>
          ouScale t ^ 2 * ouSemigroup t (deriv (deriv f)) x :=
        funext fun x =>
          deriv_ouSemigroup_space₂ (t := t) (x := x) hf ⟨B, hB⟩ ⟨B2, hB2⟩ ⟨M, hM⟩
      rw [hrew]
      exact continuous_const.mul (continuous_ouSemigroup hf'1.continuous_deriv_one ⟨B2, hB2⟩)
    exact h2.sub (continuous_id.mul h1)
  have hlog_cont : Continuous (fun x => Real.log (ouSemigroup t f x)) := by
    exact (continuous_ouSemigroup hf.continuous ⟨M, hM⟩).log
      (fun x => (lt_of_lt_of_le hδ (hpos_s t x)).ne')
  have hF'_meas : AEStronglyMeasurable (F' t) γ :=
    (hdt_cont.mul (hlog_cont.add continuous_const)).aestronglyMeasurable
  have h_bound : ∀ᵐ x ∂γ, ∀ s ∈ sset, ‖F' s x‖ ≤ bound x := by
    refine ae_of_all _ fun x s hsx => ?_
    have hs1 : t / 2 < s := hsx.1
    have hdt := abs_deriv_ouSemigroup_time_le (s := s) (x := x) (t0 := t / 2)
      (by linarith : 0 < t / 2) (le_of_lt hs1) hf1 hB ⟨M, hM⟩
    have hlog := abs_log_ouSemigroup_le (s := s) (x := x) hf.continuous hδ hδf hM
    rw [Real.norm_eq_abs, abs_mul]
    have hlog1 : |Real.log (ouSemigroup s f x) + 1| ≤ L := by
      have hsum : |Real.log (ouSemigroup s f x) + 1| ≤
          |Real.log (ouSemigroup s f x)| + 1 := by
        simpa using abs_add_le (Real.log (ouSemigroup s f x)) (1 : ℝ)
      have hmax : |Real.log (ouSemigroup s f x)| + 1 ≤ L := by
        unfold L
        linarith [hlog]
      exact hsum.trans hmax
    have hlin : 0 ≤ |B| * (|x| + C * Iabs) := mul_nonneg (abs_nonneg _) (by
      have hC : 0 ≤ C := div_nonneg zero_le_one (le_of_lt (ouStdev_pos (by linarith : 0 < t / 2)))
      have hI : 0 ≤ Iabs := integral_nonneg fun y => abs_nonneg y
      nlinarith [abs_nonneg x, hC, hI])
    exact mul_le_mul hdt hlog1 (abs_nonneg _) hlin
  have hbound_int : Integrable bound γ := by
    have hlin : Integrable (fun x => |B| * |x| + |B| * C * Iabs) γ :=
      (integrable_abs_gaussianReal.const_mul _).add (integrable_const _)
    have hfun : bound = fun x => L * (|B| * |x| + |B| * C * Iabs) := by
      funext x
      ring
    rw [hfun]
    exact hlin.const_mul L
  have h_diff : ∀ᵐ x ∂γ, ∀ s ∈ sset, HasDerivAt (F · x) (F' s x) s := by
    refine ae_of_all _ fun x s hsx => ?_
    have hs0 : 0 < s := by
      have : t / 2 < s := hsx.1
      linarith
    exact hasDerivAt_ouSemigroup_mul_log (x := x) hs0 hf1 ⟨B, hB⟩ ⟨M, hM⟩ hδ hδf
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := γ) (F := F) (F' := F') (bound := bound) (x₀ := t) (s := sset)
    hs (Filter.Eventually.of_forall hmeas) hF_int hF'_meas h_bound hbound_int h_diff
  have hlin : Integrable (fun x => |B| * (|x| + C * Iabs)) γ := by
    have hfun : (fun x => |B| * (|x| + C * Iabs)) =
        fun x => |B| * |x| + |B| * C * Iabs := by
      funext x
      ring
    rw [hfun]
    exact (integrable_abs_gaussianReal.const_mul _).add (integrable_const _)
  have hdt_int : Integrable (fun x => deriv (fun r => ouSemigroup r f x) t) γ := by
    refine Integrable.mono' hlin hdt_cont.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact abs_deriv_ouSemigroup_time_le (s := t) (x := x) (t0 := t / 2)
      (by linarith : 0 < t / 2) (by linarith : t / 2 ≤ t) hf1 hB ⟨M, hM⟩
  let L0 : ℝ := max |Real.log δ| |Real.log M|
  have hprod_int : Integrable (fun x =>
      (deriv (fun r => ouSemigroup r f x) t) * Real.log (ouSemigroup t f x)) γ := by
    refine Integrable.mono' (hlin.const_mul |L0|)
      ((hdt_cont.mul hlog_cont).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    have hdt := abs_deriv_ouSemigroup_time_le (s := t) (x := x) (t0 := t / 2)
      (by linarith : 0 < t / 2) (by linarith : t / 2 ≤ t) hf1 hB ⟨M, hM⟩
    have hlog := abs_log_ouSemigroup_le (s := t) (x := x) hf.continuous hδ hδf hM
    have hlin0 : 0 ≤ |B| * (|x| + C * Iabs) := mul_nonneg (abs_nonneg _) (by
      have hC : 0 ≤ C :=
        div_nonneg zero_le_one (le_of_lt (ouStdev_pos (by linarith : 0 < t / 2)))
      have hI : 0 ≤ Iabs := integral_nonneg fun y => abs_nonneg y
      nlinarith [abs_nonneg x, hC, hI])
    calc |deriv (fun r => ouSemigroup r f x) t| * |Real.log (ouSemigroup t f x)|
        ≤ (|B| * (|x| + C * Iabs)) * |Real.log (ouSemigroup t f x)| :=
          mul_le_mul_of_nonneg_right hdt (abs_nonneg _)
      _ ≤ (|B| * (|x| + C * Iabs)) * L0 :=
          mul_le_mul_of_nonneg_left hlog hlin0
      _ = |L0| * (|B| * (|x| + C * Iabs)) := by
          rw [abs_of_nonneg (le_trans (abs_nonneg (Real.log δ)) (le_max_left _ _))]
          ring
  have hsplit : ∫ x, F' t x ∂γ =
      ∫ x, (deriv (fun r => ouSemigroup r f x) t) * Real.log (ouSemigroup t f x) ∂γ +
        ∫ x, deriv (fun r => ouSemigroup r f x) t ∂γ := by
    have hfun : F' t = fun x =>
        (deriv (fun r => ouSemigroup r f x) t) * Real.log (ouSemigroup t f x) +
        deriv (fun r => ouSemigroup r f x) t := by
      funext x
      ring
    rw [hfun, integral_add hprod_int hdt_int]
  have hzero : ∫ x, deriv (fun r => ouSemigroup r f x) t ∂γ = 0 := by
    simpa [γ] using integral_timeDeriv_ouSemigroup ht hf ⟨B, hB⟩ ⟨B2, hB2⟩ ⟨M, hM⟩
  have hfish := integral_generator_mul_log ht hf hδ hδf ⟨B, hB⟩ ⟨B2, hB2⟩ ⟨M, hM⟩
  refine hderiv.2.congr_deriv ?_
  rw [hsplit, hzero, add_zero]
  simpa [γ] using hfish

/-- Real form of the entropy derivative. -/
lemma deriv_entropy_ouSemigroup {f : ℝ → ℝ} {t δ : ℝ} (ht : 0 < t) (hf : ContDiff ℝ 2 f)
    (hδ : 0 < δ) (hδf : ∀ y, δ ≤ f y) (hB : ∃ B, ∀ y, |deriv f y| ≤ B)
    (hB2 : ∃ B2, ∀ y, |deriv (deriv f) y| ≤ B2) (hM : ∃ M, ∀ y, |f y| ≤ M) :
    deriv (fun s => ∫ x, ouSemigroup s f x * Real.log (ouSemigroup s f x) ∂gaussianReal 0 1) t =
      -∫ x, (deriv (ouSemigroup t f) x) ^ 2 / ouSemigroup t f x ∂gaussianReal 0 1 :=
  (hasDerivAt_entropy_ouSemigroup ht hf hδ hδf hB hB2 hM).deriv

/-- The Mehler gradient satisfies a pointwise Cauchy–Schwarz bound. -/
lemma fisher_ouSemigroup_le {f : ℝ → ℝ} {t x δ : ℝ} (hf : ContDiff ℝ 1 f) (hδ : 0 < δ)
    (hδf : ∀ y, δ ≤ f y) (hB : ∃ B, ∀ y, |deriv f y| ≤ B) (hM : ∃ M, ∀ y, |f y| ≤ M) :
    (deriv (ouSemigroup t f) x) ^ 2 / ouSemigroup t f x ≤
      ouScale t ^ 2 * ouSemigroup t (fun y => (deriv f y) ^ 2 / f y) x := by
  obtain ⟨B, hB⟩ := hB
  obtain ⟨M, hM⟩ := hM
  have hMpos : 0 < M := lt_of_lt_of_le hδ ((hδf 0).trans ((le_abs_self _).trans (hM 0)))
  have hB0 : 0 ≤ B := le_trans (abs_nonneg (deriv f 0)) (hB 0)
  let γ : Measure ℝ := gaussianReal 0 1
  let α : ℝ := ouScale t
  let σ : ℝ := ouStdev t
  let a : ℝ → ℝ := fun y =>
    deriv f (α * x + σ * y) / Real.sqrt (f (α * x + σ * y))
  let b : ℝ → ℝ := fun y => Real.sqrt (f (α * x + σ * y))
  have hposf : ∀ y, 0 < f (α * x + σ * y) := fun y => lt_of_lt_of_le hδ (hδf _)
  have ha : Continuous a := by
    have hinner : Continuous (fun y => α * x + σ * y) := by fun_prop
    exact ((hf.continuous_deriv_one.comp hinner).div
      ((Real.continuous_sqrt.comp (hf.continuous.comp hinner)))
      (fun y => (Real.sqrt_pos.mpr (hposf y)).ne'))
  have hb : Continuous b :=
    Real.continuous_sqrt.comp (hf.continuous.comp (by fun_prop : Continuous fun y => α * x + σ * y))
  have hA : ∀ y, |a y| ≤ B / Real.sqrt δ := by
    intro y
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hden : Real.sqrt δ ≤ Real.sqrt (f (α * x + σ * y)) := Real.sqrt_le_sqrt (hδf _)
    have hrec : 1 / Real.sqrt (f (α * x + σ * y)) ≤ 1 / Real.sqrt δ :=
      one_div_le_one_div_of_le (Real.sqrt_pos.mpr hδ) hden
    have hnum : |deriv f (α * x + σ * y)| ≤ B := hB _
    have hrew : |deriv f (α * x + σ * y)| / Real.sqrt (f (α * x + σ * y)) =
        |deriv f (α * x + σ * y)| * (1 / Real.sqrt (f (α * x + σ * y))) := by ring
    have hrew' : B / Real.sqrt δ = B * (1 / Real.sqrt δ) := by ring
    rw [hrew, hrew']
    exact mul_le_mul hnum hrec (div_nonneg zero_le_one (Real.sqrt_nonneg _)) hB0
  have hBb : ∀ y, |b y| ≤ Real.sqrt M := by
    intro y
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((le_abs_self (f _)).trans (hM _))
  have hcs := gaussian_cauchy_schwarz ha hb hA hBb
  have hab : ∀ y, a y * b y = deriv f (α * x + σ * y) := by
    intro y
    exact div_mul_cancel₀ _ (Real.sqrt_pos.mpr (hposf y)).ne'
  have ha2 : ∀ y, a y ^ 2 = (deriv f (α * x + σ * y)) ^ 2 / f (α * x + σ * y) := by
    intro y
    rw [div_pow, Real.sq_sqrt (le_of_lt (hposf y))]
  have hb2 : ∀ y, b y ^ 2 = f (α * x + σ * y) := fun y =>
    Real.sq_sqrt (le_of_lt (hposf y))
  have hint_ab : ∫ y, a y * b y ∂γ = ∫ y, deriv f (α * x + σ * y) ∂γ := by
    rw [show (fun y => a y * b y) = fun y => deriv f (α * x + σ * y) from funext hab]
  have hint_a2 : ∫ y, a y ^ 2 ∂γ =
      ∫ y, (deriv f (α * x + σ * y)) ^ 2 / f (α * x + σ * y) ∂γ := by
    rw [show (fun y => a y ^ 2) =
      fun y => (deriv f (α * x + σ * y)) ^ 2 / f (α * x + σ * y) from funext ha2]
  have hint_b2 : ∫ y, b y ^ 2 ∂γ = ∫ y, f (α * x + σ * y) ∂γ := by
    rw [show (fun y => b y ^ 2) = fun y => f (α * x + σ * y) from funext hb2]
  have hsq : (∫ y, a y * b y ∂γ) ^ 2 ≤
      (∫ y, a y ^ 2 ∂γ) * ∫ y, b y ^ 2 ∂γ := hcs
  have hspace := deriv_ouSemigroup_space (t := t) (x := x) hf ⟨B, hB⟩ ⟨M, hM⟩
  have hderiv : deriv (ouSemigroup t f) x = α * ∫ y, a y * b y ∂γ := by
    rw [hspace, hint_ab]
    simp [ouSemigroup, α, σ, γ]
  have hpos : 0 < ouSemigroup t f x :=
    lt_of_lt_of_le hδ (ouSemigroup_lower (t := t) (x := x) hf.continuous ⟨M, hM⟩ hδf)
  have hP : ouSemigroup t (fun y => (deriv f y) ^ 2 / f y) x = ∫ y, a y ^ 2 ∂γ := by
    rw [hint_a2]
    simp [ouSemigroup, α, σ, γ]
  rw [div_le_iff₀ hpos, hderiv, hP]
  have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg α)
  calc (α * ∫ y, a y * b y ∂γ) ^ 2
      = α ^ 2 * (∫ y, a y * b y ∂γ) ^ 2 := by ring
    _ ≤ α ^ 2 * ((∫ y, a y ^ 2 ∂γ) * ∫ y, b y ^ 2 ∂γ) := hmul
    _ = (α ^ 2 * ∫ y, a y ^ 2 ∂γ) * ouSemigroup t f x := by
        rw [hint_b2]
        simp [ouSemigroup, α, σ, γ]
        ring

/-- Integrated Fisher information contracts by the Mehler factor `e^{-2t}`. -/
lemma integral_sq_deriv_ouSemigroup_le {f : ℝ → ℝ} {t δ : ℝ} (ht : 0 ≤ t) (hf : ContDiff ℝ 1 f)
    (hδ : 0 < δ) (hδf : ∀ y, δ ≤ f y) (hB : ∃ B, ∀ y, |deriv f y| ≤ B)
    (hM : ∃ M, ∀ y, |f y| ≤ M) :
    ∫ x, (deriv (ouSemigroup t f) x) ^ 2 / ouSemigroup t f x ∂gaussianReal 0 1 ≤
      ouScale t ^ 2 * ∫ x, (deriv f x) ^ 2 / f x ∂gaussianReal 0 1 := by
  obtain ⟨B, hB⟩ := hB
  obtain ⟨M, hM⟩ := hM
  have hB0 : 0 ≤ B := le_trans (abs_nonneg (deriv f 0)) (hB 0)
  let γ : Measure ℝ := gaussianReal 0 1
  let g : ℝ → ℝ := fun y => (deriv f y) ^ 2 / f y
  have hposf : ∀ y, 0 < f y := fun y => lt_of_lt_of_le hδ (hδf y)
  have hg_cont : Continuous g :=
    ((hf.continuous_deriv_one.pow 2).div hf.continuous fun y => (hposf y).ne')
  have hg_nonneg : ∀ y, 0 ≤ g y := fun y => div_nonneg (sq_nonneg _) (le_of_lt (hposf y))
  have hg_le : ∀ y, g y ≤ B ^ 2 / δ := by
    intro y
    have hsq : (deriv f y) ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hB y) 2
    have hrec : (1 : ℝ) / f y ≤ 1 / δ := one_div_le_one_div_of_le hδ (hδf y)
    have hmul := mul_le_mul hsq hrec (div_nonneg zero_le_one (le_of_lt (hposf y))) (sq_nonneg _)
    have hrew : (deriv f y) ^ 2 / f y = (deriv f y) ^ 2 * (1 / f y) := by ring
    have hrew' : B ^ 2 / δ = B ^ 2 * (1 / δ) := by ring
    unfold g
    rw [hrew, hrew']
    exact hmul
  have hg_abs : ∀ y, |g y| ≤ B ^ 2 / δ := by
    intro y
    rw [abs_of_nonneg (hg_nonneg y)]
    exact hg_le y
  have hpoint : ∀ x, (deriv (ouSemigroup t f) x) ^ 2 / ouSemigroup t f x ≤
      ouScale t ^ 2 * ouSemigroup t g x := fun x =>
    fisher_ouSemigroup_le (t := t) (x := x) hf hδ hδf ⟨B, hB⟩ ⟨M, hM⟩
  have hspace_cont : Continuous (deriv (ouSemigroup t f)) := by
    have hrew : deriv (ouSemigroup t f) = fun x => ouScale t * ouSemigroup t (deriv f) x :=
      funext fun x => deriv_ouSemigroup_space (t := t) (x := x) hf ⟨B, hB⟩ ⟨M, hM⟩
    rw [hrew]
    exact continuous_const.mul (continuous_ouSemigroup hf.continuous_deriv_one ⟨B, hB⟩)
  have hu_cont : Continuous (ouSemigroup t f) := continuous_ouSemigroup hf.continuous ⟨M, hM⟩
  have hu_pos : ∀ x, 0 < ouSemigroup t f x := fun x =>
    lt_of_lt_of_le hδ (ouSemigroup_lower (t := t) (x := x) hf.continuous ⟨M, hM⟩ hδf)
  have hleft_cont : Continuous (fun x =>
      (deriv (ouSemigroup t f) x) ^ 2 / ouSemigroup t f x) :=
    ((hspace_cont.pow 2).div hu_cont fun x => (hu_pos x).ne')
  have hleft_le : ∀ x, |(deriv (ouSemigroup t f) x) ^ 2 / ouSemigroup t f x| ≤ B ^ 2 / δ := by
    intro x
    have hnonneg : 0 ≤ (deriv (ouSemigroup t f) x) ^ 2 / ouSemigroup t f x :=
      div_nonneg (sq_nonneg _) (le_of_lt (hu_pos x))
    rw [abs_of_nonneg hnonneg]
    have hP : ouSemigroup t g x ≤ B ^ 2 / δ :=
      ouSemigroup_upper (t := t) (x := x) hg_cont ⟨B ^ 2 / δ, fun y => hg_abs y⟩ hg_le
    have hα : ouScale t ^ 2 ≤ 1 := by
      have h1 := ouScale_le_one ht
      have h0 := ouScale_nonneg t
      nlinarith
    calc (deriv (ouSemigroup t f) x) ^ 2 / ouSemigroup t f x
        ≤ ouScale t ^ 2 * ouSemigroup t g x := hpoint x
      _ ≤ ouScale t ^ 2 * (B ^ 2 / δ) :=
          mul_le_mul_of_nonneg_left hP (sq_nonneg _)
      _ ≤ B ^ 2 / δ := by
          have := mul_le_mul_of_nonneg_right hα (div_nonneg (sq_nonneg B) (le_of_lt hδ))
          simpa using this
  have hleft_int : Integrable (fun x =>
      (deriv (ouSemigroup t f) x) ^ 2 / ouSemigroup t f x) γ :=
    integrable_of_abs_le hleft_cont.aestronglyMeasurable hleft_le
  have hright_int : Integrable (fun x => ouScale t ^ 2 * ouSemigroup t g x) γ := by
    have hbd : ∀ x, |ouScale t ^ 2 * ouSemigroup t g x| ≤ B ^ 2 / δ := by
      intro x
      rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg
        (ouSemigroup_lower (t := t) (x := x) hg_cont ⟨B ^ 2 / δ, fun y =>
          hg_abs y⟩ hg_nonneg)]
      have hP : ouSemigroup t g x ≤ B ^ 2 / δ :=
        ouSemigroup_upper (t := t) (x := x) hg_cont ⟨B ^ 2 / δ, fun y =>
          hg_abs y⟩ hg_le
      have hα : ouScale t ^ 2 ≤ 1 := by
        nlinarith [ouScale_le_one ht, ouScale_nonneg t]
      have hmul := (mul_le_mul_of_nonneg_left hP (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hα (div_nonneg (sq_nonneg B) (le_of_lt hδ)))
      simpa using hmul
    exact integrable_of_abs_le ((continuous_const.mul
      (continuous_ouSemigroup hg_cont ⟨B ^ 2 / δ, fun y => hg_abs y⟩)
      ).aestronglyMeasurable) hbd
  have hmono := integral_mono hleft_int hright_int hpoint
  have hinv := integral_ouSemigroup (t := t) ht hg_cont
    ⟨B ^ 2 / δ, fun y => hg_abs y⟩
  calc ∫ x, (deriv (ouSemigroup t f) x) ^ 2 / ouSemigroup t f x ∂gaussianReal 0 1
      ≤ ∫ x, ouScale t ^ 2 * ouSemigroup t g x ∂γ := hmono
    _ = ouScale t ^ 2 * ∫ x, ouSemigroup t g x ∂γ := integral_const_mul _ _
    _ = ouScale t ^ 2 * ∫ x, g x ∂γ := by rw [hinv]
    _ = ouScale t ^ 2 * ∫ x, (deriv f x) ^ 2 / f x ∂gaussianReal 0 1 := by simp [g, γ]

/-- The Mehler scale tends to zero at infinite time. -/
lemma tendsto_ouScale_atTop : Filter.Tendsto ouScale atTop (𝓝 0) := by
  unfold ouScale
  exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot

/-- The Mehler width tends to one at infinite time. -/
lemma tendsto_ouStdev_atTop : Filter.Tendsto ouStdev atTop (𝓝 1) := by
  unfold ouStdev
  have hexp : Filter.Tendsto (fun t : ℝ => Real.exp (-(2 * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (tendsto_id.const_mul_atTop (zero_lt_two : (0 : ℝ) < 2)))
  have hsub : Filter.Tendsto (fun t => 1 - Real.exp (-(2 * t))) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hexp
  simpa [Function.comp_def, Real.sqrt_one] using
    (Real.continuous_sqrt.tendsto (1 : ℝ)).comp hsub

/-- The semigroup converges to the Gaussian mean at infinite time. -/
lemma tendsto_ouSemigroup_atTop {f : ℝ → ℝ} {x : ℝ} (hf : Continuous f)
    (hM : ∃ M, ∀ y, |f y| ≤ M) :
    Filter.Tendsto (fun t => ouSemigroup t f x) atTop
      (𝓝 (∫ y, f y ∂gaussianReal 0 1)) := by
  obtain ⟨M, hM⟩ := hM
  let γ : Measure ℝ := gaussianReal 0 1
  unfold ouSemigroup
  refine tendsto_integral_filter_of_dominated_convergence (μ := γ) (l := atTop)
    (F := fun t y => f (ouScale t * x + ouStdev t * y)) (bound := fun _ => |M|)
    (Filter.Eventually.of_forall fun t => by
      have hcont : Continuous (fun y => ouScale t * x + ouStdev t * y) := by fun_prop
      exact (hf.comp hcont).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]
      exact (hM _).trans (le_abs_self M))
    (integrable_const _)
    (ae_of_all _ fun y => ?_)
  have harg : Filter.Tendsto (fun t => ouScale t * x + ouStdev t * y) atTop (𝓝 y) := by
    have h1 := tendsto_ouScale_atTop.mul_const x
    have h2 := tendsto_ouStdev_atTop.mul_const y
    simpa using h1.add h2
  exact (hf.tendsto y).comp harg

/-- The semigroup converges to the function itself at time zero from the right. -/
lemma tendsto_ouSemigroup_zero {f : ℝ → ℝ} {x : ℝ} (hf : Continuous f)
    (hM : ∃ M, ∀ y, |f y| ≤ M) :
    Filter.Tendsto (fun t => ouSemigroup t f x) (nhdsWithin 0 (Ioi 0)) (𝓝 (f x)) := by
  obtain ⟨M, hM⟩ := hM
  let γ : Measure ℝ := gaussianReal 0 1
  unfold ouSemigroup
  have hconst : ∫ y, f x ∂γ = f x := by
    rw [integral_const]
    simp [probReal_univ, smul_eq_mul, γ]
  suffices Filter.Tendsto (fun t => ∫ y, f (ouScale t * x + ouStdev t * y) ∂γ)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (f x)) by simpa [γ] using this
  rw [← hconst]
  refine tendsto_integral_filter_of_dominated_convergence (μ := γ)
    (l := nhdsWithin 0 (Ioi 0)) (f := fun _ => f x)
    (F := fun t y => f (ouScale t * x + ouStdev t * y)) (bound := fun _ => |M|)
    (Filter.Eventually.of_forall fun t => by
      have hcont : Continuous (fun y => ouScale t * x + ouStdev t * y) := by fun_prop
      exact (hf.comp hcont).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]
      exact (hM _).trans (le_abs_self M))
    (integrable_const _)
    (ae_of_all _ fun y => ?_)
  have hscale : Filter.Tendsto ouScale (nhdsWithin 0 (Ioi 0)) (𝓝 1) := by
    unfold ouScale
    have hneg : Filter.Tendsto (fun t : ℝ => -t) (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
      have hcont : Continuous (fun t : ℝ => -t) := by fun_prop
      simpa using (hcont.tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi 0) ≤ 𝓝 0)
    simpa [Function.comp_def, Real.exp_zero] using
      (Real.continuous_exp.tendsto (0 : ℝ)).comp hneg
  have hstdev : Filter.Tendsto ouStdev (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    unfold ouStdev
    have hexp : Filter.Tendsto (fun t : ℝ => Real.exp (-(2 * t)))
        (nhdsWithin 0 (Ioi 0)) (𝓝 1) := by
      have hneg : Filter.Tendsto (fun t : ℝ => -(2 * t)) (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
        have hcont : Continuous (fun t : ℝ => -(2 * t)) := by fun_prop
        simpa using (hcont.tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi 0) ≤ 𝓝 0)
      simpa [Function.comp_def, Real.exp_zero] using
        (Real.continuous_exp.tendsto (0 : ℝ)).comp hneg
    have hsub : Filter.Tendsto (fun t => 1 - Real.exp (-(2 * t)))
        (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
      have hdiff := (tendsto_const_nhds.sub hexp :
        Filter.Tendsto (fun t => (1 : ℝ) - Real.exp (-(2 * t)))
          (nhdsWithin 0 (Ioi 0)) (𝓝 ((1 : ℝ) - 1)))
      simpa using hdiff
    simpa [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsub
  have harg : Filter.Tendsto (fun t => ouScale t * x + ouStdev t * y)
      (nhdsWithin 0 (Ioi 0)) (𝓝 x) := by
    simpa using (hscale.mul_const x).add (hstdev.mul_const y)
  exact (hf.tendsto x).comp harg

/-- Entropy integrand of a uniformly positive bounded function along the semigroup. -/
def ouEntropy (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x, ouSemigroup t f x * Real.log (ouSemigroup t f x) ∂gaussianReal 0 1

/-- The entropy integrand converges to `f log f` as time tends to zero from the right. -/
lemma tendsto_ouEntropy_zero {f : ℝ → ℝ} {δ M : ℝ} (hf : Continuous f) (hδ : 0 < δ)
    (hδf : ∀ y, δ ≤ f y) (hM : ∀ y, |f y| ≤ M) :
    Filter.Tendsto (ouEntropy f) (nhdsWithin 0 (Ioi 0))
      (𝓝 (∫ x, f x * Real.log (f x) ∂gaussianReal 0 1)) := by
  let γ : Measure ℝ := gaussianReal 0 1
  let L : ℝ := M * max |Real.log δ| |Real.log M|
  unfold ouEntropy
  refine tendsto_integral_filter_of_dominated_convergence (μ := γ)
    (l := nhdsWithin 0 (Ioi 0)) (f := fun x => f x * Real.log (f x))
    (F := fun t x => ouSemigroup t f x * Real.log (ouSemigroup t f x))
    (bound := fun _ => L)
    (Filter.Eventually.of_forall fun t => by
      have hu := continuous_ouSemigroup (t := t) hf ⟨M, hM⟩
      have hlog := hu.log fun x => (lt_of_lt_of_le hδ
        (ouSemigroup_lower (t := t) (x := x) hf ⟨M, hM⟩ hδf)).ne'
      exact (hu.mul hlog).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      have habs := abs_ouSemigroup_le (t := t) (x := x) hf hM
      have hlog := abs_log_ouSemigroup_le (s := t) (x := x) hf hδ hδf hM
      have hmul := mul_le_mul habs hlog (abs_nonneg _) (le_trans (abs_nonneg _) (hM 0))
      simpa [L] using hmul)
    (integrable_const _)
    (ae_of_all _ fun x => ?_)
  have hu := tendsto_ouSemigroup_zero (x := x) hf ⟨M, hM⟩
  have hpos : 0 < f x := lt_of_lt_of_le hδ (hδf x)
  have hcont : ContinuousAt (fun z : ℝ => z * Real.log z) (f x) :=
    continuousAt_id.mul (continuousAt_id.log hpos.ne')
  exact hcont.tendsto.comp hu

/-- The entropy integrand converges to the entropy of the constant mean at infinite time. -/
lemma tendsto_ouEntropy_atTop {f : ℝ → ℝ} {δ M : ℝ} (hf : Continuous f) (hδ : 0 < δ)
    (hδf : ∀ y, δ ≤ f y) (hM : ∀ y, |f y| ≤ M) :
    Filter.Tendsto (ouEntropy f) atTop
      (𝓝 ((∫ x, f x ∂gaussianReal 0 1) * Real.log (∫ x, f x ∂gaussianReal 0 1))) := by
  let γ : Measure ℝ := gaussianReal 0 1
  let m : ℝ := ∫ x, f x ∂γ
  let L : ℝ := M * max |Real.log δ| |Real.log M|
  have hm_pos : 0 < m := by
    have hconst : ∫ x, δ ∂γ = δ := by
      rw [integral_const]
      simp [probReal_univ, smul_eq_mul, γ]
    have hint : Integrable f γ :=
      integrable_of_abs_le hf.aestronglyMeasurable fun y => hM y
    have hmono := integral_mono (integrable_const _) hint hδf
    rw [hconst] at hmono
    exact lt_of_lt_of_le hδ (by simpa [m] using hmono)
  unfold ouEntropy
  have hconst_int : ∫ x, m * Real.log m ∂γ = m * Real.log m := by
    rw [integral_const]
    simp [probReal_univ, smul_eq_mul, γ]
  suffices Filter.Tendsto (fun t => ∫ x, ouSemigroup t f x * Real.log (ouSemigroup t f x) ∂γ)
      atTop (𝓝 (m * Real.log m)) by simpa [γ, m] using this
  rw [← hconst_int]
  refine tendsto_integral_filter_of_dominated_convergence (μ := γ) (l := atTop)
    (f := fun _ => m * Real.log m)
    (F := fun t x => ouSemigroup t f x * Real.log (ouSemigroup t f x))
    (bound := fun _ => L)
    (Filter.Eventually.of_forall fun t => by
      have hu := continuous_ouSemigroup (t := t) hf ⟨M, hM⟩
      have hlog := hu.log fun x => (lt_of_lt_of_le hδ
        (ouSemigroup_lower (t := t) (x := x) hf ⟨M, hM⟩ hδf)).ne'
      exact (hu.mul hlog).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      have habs := abs_ouSemigroup_le (t := t) (x := x) hf hM
      have hlog := abs_log_ouSemigroup_le (s := t) (x := x) hf hδ hδf hM
      have hmul := mul_le_mul habs hlog (abs_nonneg _) (le_trans (abs_nonneg _) (hM 0))
      simpa [L] using hmul)
    (integrable_const _)
    (ae_of_all _ fun x => ?_)
  have hu := tendsto_ouSemigroup_atTop (x := x) hf ⟨M, hM⟩
  have hcont : ContinuousAt (fun z : ℝ => z * Real.log z) m :=
    continuousAt_id.mul (continuousAt_id.log hm_pos.ne')
  simpa [Function.comp_def, γ, m] using hcont.tendsto.comp hu

/-- Gaussian entropy of a smooth positive function with bounded derivatives. -/
lemma gaussian_entropy_le_half_fisher {f : ℝ → ℝ} {δ : ℝ} (hf : ContDiff ℝ 2 f) (hδ : 0 < δ)
    (hδf : ∀ x, δ ≤ f x) (hB : ∃ B, ∀ x, |deriv f x| ≤ B)
    (hB2 : ∃ B2, ∀ x, |deriv (deriv f) x| ≤ B2) (hM : ∃ M, ∀ x, |f x| ≤ M) :
    (∫ x, f x * Real.log (f x) ∂gaussianReal 0 1) -
        (∫ x, f x ∂gaussianReal 0 1) * Real.log (∫ x, f x ∂gaussianReal 0 1) ≤
      (1 / 2) * ∫ x, (deriv f x) ^ 2 / f x ∂gaussianReal 0 1 := by
  obtain ⟨B, hB⟩ := hB
  obtain ⟨B2, hB2⟩ := hB2
  obtain ⟨M, hM⟩ := hM
  obtain ⟨hf1, hf'1⟩ := contDiff_one_deriv_of_two hf
  let γ : Measure ℝ := gaussianReal 0 1
  let Fisher : ℝ := ∫ x, (deriv f x) ^ 2 / f x ∂γ
  have hF_nonneg : 0 ≤ Fisher := by
    refine integral_nonneg fun x => div_nonneg (sq_nonneg _) ?_
    exact le_of_lt (lt_of_lt_of_le hδ (hδf x))
  have hstep : ∀ ε T : ℝ, 0 < ε → ε ≤ T →
      ouEntropy f ε - ouEntropy f T ≤ (1 / 2) * Fisher := by
    intro ε T hε hεT
    have hcontE : ContinuousOn (ouEntropy f) (Icc ε T) := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hε ht.1
      exact (hasDerivAt_entropy_ouSemigroup ht0 hf hδ hδf ⟨B, hB⟩ ⟨B2, hB2⟩
        ⟨M, hM⟩).continuousAt.continuousWithinAt
    let I : ℝ → ℝ := fun t =>
      ∫ x, (deriv (ouSemigroup t f) x) ^ 2 / ouSemigroup t f x ∂γ
    have hderiv_eq : ∀ t ∈ Icc ε T, deriv (ouEntropy f) t = -(I t) := by
      intro t ht
      unfold ouEntropy
      simpa [I, γ] using deriv_entropy_ouSemigroup (lt_of_lt_of_le hε ht.1) hf hδ
        hδf ⟨B, hB⟩ ⟨B2, hB2⟩ ⟨M, hM⟩
    let φ : ℝ → ℝ := fun t => -Real.exp (-(2 * t)) * Fisher
    have hφ_le : ∀ t ∈ Ioo ε T, φ t ≤ deriv (ouEntropy f) t := by
      intro t ht
      have hI_le : I t ≤ Real.exp (-(2 * t)) * Fisher := by
        have hcontr := integral_sq_deriv_ouSemigroup_le (le_of_lt (hε.trans ht.1)) hf1 hδ hδf
          ⟨B, hB⟩ ⟨M, hM⟩
        simpa [I, Fisher, γ, ouScale_sq] using hcontr
      calc
        φ t = -(Real.exp (-(2 * t)) * Fisher) := by ring
        _ ≤ -(I t) := neg_le_neg hI_le
        _ = deriv (ouEntropy f) t := (hderiv_eq t (Ioo_subset_Icc_self ht)).symm
    have hφ_int : IntegrableOn φ (Icc ε T) volume := by
      rw [← uIcc_of_le hεT]
      exact (intervalIntegrable_iff' (μ := volume) (f := φ) (a := ε) (b := T)).1
        ((by fun_prop : Continuous φ).intervalIntegrable (μ := volume) ε T)
    have hderivAt : ∀ t ∈ Ioo ε T,
        HasDerivWithinAt (ouEntropy f) (deriv (ouEntropy f) t) (Ioi t) t := by
      intro t ht
      have hHA := hasDerivAt_entropy_ouSemigroup (hε.trans ht.1) hf hδ hδf
        ⟨B, hB⟩ ⟨B2, hB2⟩ ⟨M, hM⟩
      unfold ouEntropy
      exact (hHA.congr_deriv hHA.deriv.symm).hasDerivWithinAt
    have hmono := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hεT hcontE
      hderivAt hφ_int hφ_le
    have hint_exp : ∫ t in ε..T, Real.exp (-(2 * t)) =
        (1 / 2) * (Real.exp (-(2 * ε)) - Real.exp (-(2 * T))) := by
      have hanti : ∀ t, HasDerivAt (fun s => -((1 : ℝ) / 2) * Real.exp (-(2 * s)))
          (Real.exp (-(2 * t))) t := by
        intro t
        have hmul : HasDerivAt (fun s => 2 * s) 2 t := by
          simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
        have hlin : HasDerivAt (fun s => -(2 * s)) (-2) t := hmul.fun_neg
        have hexp : HasDerivAt (fun s => Real.exp (-(2 * s)))
            (Real.exp (-(2 * t)) * -2) t := by
          simpa [Function.comp_def] using (Real.hasDerivAt_exp (-(2 * t))).comp t hlin
        exact (hexp.const_mul (-((1 : ℝ) / 2))).congr_deriv (by ring)
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hεT
        ((by fun_prop : Continuous (fun s => -((1 : ℝ) / 2) * Real.exp (-(2 * s)))).continuousOn)
        (fun t _ => hanti t)
        ((by fun_prop : Continuous (fun t => Real.exp (-(2 * t)))).intervalIntegrable
          (μ := volume) ε T)
      rw [hFTC]
      ring
    have hintφ : ∫ t in ε..T, φ t =
        -((1 / 2) * (Real.exp (-(2 * ε)) - Real.exp (-(2 * T)))) * Fisher := by
      have hfun : (fun t => φ t) = fun t => (-Real.exp (-(2 * t))) * Fisher := by
        funext t
        ring
      rw [hfun, intervalIntegral.integral_mul_const, intervalIntegral.integral_neg, hint_exp]
    have hdiff_le : ouEntropy f ε - ouEntropy f T ≤
        ((1 / 2) * (Real.exp (-(2 * ε)) - Real.exp (-(2 * T)))) * Fisher := by
      calc
        ouEntropy f ε - ouEntropy f T = -(ouEntropy f T - ouEntropy f ε) := by ring
        _ ≤ -(∫ t in ε..T, φ t) := neg_le_neg hmono
        _ = ((1 / 2) * (Real.exp (-(2 * ε)) - Real.exp (-(2 * T)))) * Fisher := by
            rw [hintφ]
            ring
    have hc : (1 / 2) * (Real.exp (-(2 * ε)) - Real.exp (-(2 * T))) ≤ 1 / 2 := by
      have hexpε : Real.exp (-(2 * ε)) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by linarith)
      have hdiff : Real.exp (-(2 * ε)) - Real.exp (-(2 * T)) ≤ 1 := by
        linarith [hexpε, Real.exp_nonneg (-(2 * T))]
      have hmul := mul_le_mul_of_nonneg_left hdiff (by norm_num : (0 : ℝ) ≤ 1 / 2)
      simpa using hmul
    exact (hdiff_le.trans (mul_le_mul_of_nonneg_right hc hF_nonneg))
  have hε_le : ∀ ε, 0 < ε → ouEntropy f ε -
      (∫ x, f x ∂γ) * Real.log (∫ x, f x ∂γ) ≤ (1 / 2) * Fisher := by
    intro ε hε
    have htend : Tendsto (fun T => ouEntropy f ε - ouEntropy f T) atTop
        (𝓝 (ouEntropy f ε - (∫ x, f x ∂γ) * Real.log (∫ x, f x ∂γ))) := by
      simpa [γ] using tendsto_const_nhds.sub
        (tendsto_ouEntropy_atTop hf.continuous hδ hδf hM)
    have hle : (fun T => ouEntropy f ε - ouEntropy f T) ≤ᶠ[atTop]
        fun _ => (1 / 2) * Fisher := by
      filter_upwards [eventually_ge_atTop ε] with T hT
      exact hstep ε T hε hT
    exact le_of_tendsto_of_tendsto htend tendsto_const_nhds hle
  have htend0 : Tendsto (fun ε => ouEntropy f ε -
      (∫ x, f x ∂γ) * Real.log (∫ x, f x ∂γ)) (nhdsWithin 0 (Ioi 0))
      (𝓝 ((∫ x, f x * Real.log (f x) ∂γ) -
        (∫ x, f x ∂γ) * Real.log (∫ x, f x ∂γ))) := by
    simpa [γ] using (tendsto_ouEntropy_zero hf.continuous hδ hδf hM).sub tendsto_const_nhds
  have hle0 : (fun ε => ouEntropy f ε - (∫ x, f x ∂γ) * Real.log (∫ x, f x ∂γ))
      ≤ᶠ[nhdsWithin 0 (Ioi 0)] fun _ => (1 / 2) * Fisher := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hε_le ε hε
  simpa [Fisher, γ] using le_of_tendsto_of_tendsto htend0 tendsto_const_nhds hle0

end CKMA
