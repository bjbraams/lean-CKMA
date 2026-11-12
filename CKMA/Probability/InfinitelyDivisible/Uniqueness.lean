/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.InfinitelyDivisible.SecondDiff
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Uniqueness of a Lévy triplet

Equal exponentials of continuous branches vanishing at the origin are equal, because their
difference takes values in `2πiℤ` and the zero set is clopen. Second differences at steps `1` and
`√2` recover the Gaussian variance and the jump measure, and the drift is the remaining linear
term.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Complex Set Topology Filter
open scoped NNReal ENNReal

/-- An integer of absolute value less than one is zero. -/
lemma int_eq_zero_of_abs_cast_lt_one {n : ℤ} (h : |(n : ℝ)| < 1) : n = 0 := by
  rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at h
  exact h

/-- The modulus of an integral multiple of `2πi`. -/
lemma norm_int_mul_two_pi_I (n : ℤ) :
    ‖n * (2 * Real.pi * I)‖ = |(n : ℝ)| * (2 * Real.pi) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  calc
    ‖(n : ℂ) * ((2 : ℂ) * Real.pi * I)‖
        = ‖(n : ℂ)‖ * ‖(2 : ℂ) * Real.pi * I‖ := norm_mul _ _
    _ = |(n : ℝ)| * (‖(2 : ℂ) * (Real.pi : ℂ)‖ * ‖I‖) := by
        rw [norm_intCast, norm_mul]
    _ = |(n : ℝ)| * ((‖(2 : ℂ)‖ * ‖(Real.pi : ℂ)‖) * ‖I‖) := by
        rw [norm_mul]
    _ = |(n : ℝ)| * ((2 * Real.pi) * 1) := by
        simp [norm_real, Real.norm_eq_abs, abs_of_pos hpi, norm_I]
    _ = |(n : ℝ)| * (2 * Real.pi) := by ring

/-- Continuous logarithms of the same never-zero function, normalized at the origin, agree. -/
lemma eq_of_exp_eq_of_continuous {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (h : ∀ t, exp (f t) = exp (g t)) : f = g := by
  let δ : ℝ → ℂ := fun t => f t - g t
  have hδ : Continuous δ := hf.sub hg
  have hδ0 : δ 0 = 0 := by simp [δ, hf0, hg0]
  have hexp : ∀ t, exp (δ t) = 1 := by
    intro t
    exact (exp_eq_exp_iff_exp_sub_eq_one).mp (h t)
  let s : Set ℝ := {t | δ t = 0}
  have hs_closed : IsClosed s := isClosed_eq hδ continuous_const
  have hs_open : IsOpen s := by
    rw [isOpen_iff_mem_nhds]
    intro t0 ht0
    have h0 : δ t0 = 0 := ht0
    let u : Set ℝ := {t | ‖δ t‖ < 2 * Real.pi}
    have hu : IsOpen u := by
      have hc : Continuous fun t : ℝ => ‖δ t‖ := continuous_norm.comp hδ
      exact isOpen_lt hc continuous_const
    have hmem : t0 ∈ u := by
      simp [u, h0]
      positivity
    refine mem_of_superset (hu.mem_nhds hmem) ?_
    intro t ht
    obtain ⟨n, hn⟩ := exp_eq_one_iff.mp (hexp t)
    have hball : ‖n * (2 * Real.pi * I)‖ < 2 * Real.pi := by
      simpa [u, hn] using ht
    rw [norm_int_mul_two_pi_I] at hball
    have hpos : 0 < 2 * Real.pi := by positivity
    have hlt : |(n : ℝ)| < 1 :=
      (mul_lt_mul_iff_of_pos_right hpos).mp (by simpa [one_mul] using hball)
    have hδt : δ t = 0 := by
      rw [hn, int_eq_zero_of_abs_cast_lt_one hlt]
      simp
    simpa [s] using hδt
  have huniv : s = univ :=
    IsClopen.eq_univ ⟨hs_closed, hs_open⟩ ⟨0, hδ0⟩
  ext t
  have ht : δ t = 0 := by
    have : t ∈ s := by
      rw [huniv]
      exact mem_univ t
    simpa [s] using this
  exact sub_eq_zero.mp ht

/-- Exponents with the same exponential, both vanishing at zero, are equal. -/
lemma LevyTriplet.exponent_eq_of_exp_eq {L M : LevyTriplet}
    (h : ∀ t, exp (L.exponent t) = exp (M.exponent t)) :
    ∀ t, L.exponent t = M.exponent t := by
  have hfun := eq_of_exp_eq_of_continuous L.continuous_exponent M.continuous_exponent
    L.exponent_zero M.exponent_zero h
  intro t
  exact congrFun hfun t

/-- The nodal sets of `sin(x / 2)` and `sin(√2 x / 2)` cover every nonzero real. -/
lemma sineSet_one_union_sqrt_eq_compl :
    sineSet 1 ∪ sineSet (Real.sqrt 2) = {(0 : ℝ)}ᶜ := by
  ext x
  simp only [mem_union, mem_compl_iff, mem_singleton_iff]
  constructor
  · rintro (hx | hx) h0
    · exact zero_notMem_sineSet 1 (h0 ▸ hx)
    · exact zero_notMem_sineSet (Real.sqrt 2) (h0 ▸ hx)
  · intro hx
    by_contra hnot
    push Not at hnot
    have hsin1 : Real.sin (x / 2) = 0 := by
      simpa [sineSet, one_mul] using hnot.1
    have hsin2 : Real.sin (Real.sqrt 2 * x / 2) = 0 := by
      simpa [sineSet] using hnot.2
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin1
    obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hsin2
    have hxeq : x = 2 * ((n : ℝ) * Real.pi) := by
      calc
        x = 2 * (x / 2) := by ring
        _ = 2 * ((n : ℝ) * Real.pi) := by rw [← hn]
    have hm' : Real.sqrt 2 * x = 2 * ((m : ℝ) * Real.pi) := by
      calc
        Real.sqrt 2 * x = 2 * (Real.sqrt 2 * x / 2) := by ring
        _ = 2 * ((m : ℝ) * Real.pi) := by rw [← hm]
    have hmul : Real.sqrt 2 * (2 * ((n : ℝ) * Real.pi)) = 2 * ((m : ℝ) * Real.pi) := by
      rw [← hxeq]
      exact hm'
    have hn0 : (n : ℝ) ≠ 0 := by
      intro hn0
      apply hx
      rw [hxeq, hn0]
      ring
    have hcancel : (n : ℝ) * Real.sqrt 2 = (m : ℝ) := by
      have hmul' : 2 * Real.pi * ((n : ℝ) * Real.sqrt 2) =
          2 * Real.pi * (m : ℝ) := by
        calc
          2 * Real.pi * ((n : ℝ) * Real.sqrt 2)
              = Real.sqrt 2 * (2 * ((n : ℝ) * Real.pi)) := by ring
          _ = 2 * ((m : ℝ) * Real.pi) := hmul
          _ = 2 * Real.pi * (m : ℝ) := by ring
      exact mul_left_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero) hmul'
    have hrational : Real.sqrt 2 = (m : ℝ) / (n : ℝ) := by
      rw [eq_div_iff hn0, mul_comm]
      exact hcancel
    exact irrational_sqrt_two.ne_rational m n hrational

/-- Mass away from the origin is the sum of the two sine restrictions. -/
lemma measure_inter_compl_singleton (μ : Measure ℝ) {u : Set ℝ} (hu : MeasurableSet u) :
    μ (u ∩ {(0 : ℝ)}ᶜ) =
      μ.restrict (sineSet 1) u +
        μ.restrict (sineSet (Real.sqrt 2)) (u ∩ (sineSet 1)ᶜ) := by
  have hs1 : MeasurableSet (sineSet 1) := measurableSet_sineSet 1
  have hs2 : MeasurableSet (sineSet (Real.sqrt 2)) := measurableSet_sineSet (Real.sqrt 2)
  have hcov : {(0 : ℝ)}ᶜ = sineSet 1 ∪ sineSet (Real.sqrt 2) :=
    sineSet_one_union_sqrt_eq_compl.symm
  have hsplit : u ∩ {(0 : ℝ)}ᶜ =
      (u ∩ sineSet 1) ∪ ((u ∩ sineSet (Real.sqrt 2)) ∩ (sineSet 1)ᶜ) := by
    rw [hcov]
    ext x
    simp only [mem_inter_iff, mem_union, mem_compl_iff]
    constructor
    · rintro ⟨hxu, hx | hx⟩
      · exact Or.inl ⟨hxu, hx⟩
      · by_cases hmem : x ∈ sineSet 1
        · exact Or.inl ⟨hxu, hmem⟩
        · exact Or.inr ⟨⟨hxu, hx⟩, hmem⟩
    · rintro (⟨hxu, hx⟩ | ⟨⟨hxu, hx⟩, _⟩)
      · exact ⟨hxu, Or.inl hx⟩
      · exact ⟨hxu, Or.inr hx⟩
  have hdis : Disjoint (u ∩ sineSet 1) ((u ∩ sineSet (Real.sqrt 2)) ∩ (sineSet 1)ᶜ) := by
    refine disjoint_left.2 ?_
    intro x hx hx'
    simp only [mem_inter_iff, mem_compl_iff] at hx hx'
    exact hx'.2 hx.2
  have hmeas : MeasurableSet ((u ∩ sineSet (Real.sqrt 2)) ∩ (sineSet 1)ᶜ) :=
    (hu.inter hs2).inter hs1.compl
  rw [hsplit, measure_union hdis hmeas]
  have hA : μ (u ∩ sineSet 1) = μ.restrict (sineSet 1) u :=
    (Measure.restrict_apply hu).symm
  have hB : μ ((u ∩ sineSet (Real.sqrt 2)) ∩ (sineSet 1)ᶜ) =
      μ.restrict (sineSet (Real.sqrt 2)) (u ∩ (sineSet 1)ᶜ) := by
    rw [Measure.restrict_apply (hu.inter hs1.compl)]
    congr 1
    ext y
    simp only [mem_inter_iff, mem_compl_iff]
    constructor
    · rintro ⟨⟨hyu, hy2⟩, hy1⟩
      exact ⟨⟨hyu, hy1⟩, hy2⟩
    · rintro ⟨⟨hyu, hy1⟩, hy2⟩
      exact ⟨⟨hyu, hy2⟩, hy1⟩
  rw [hA, hB]

/-- A measure with no atom at the origin is determined by its mass off zero. -/
lemma measure_eq_inter_compl {μ : Measure ℝ} (h0 : μ {(0 : ℝ)} = 0) {u : Set ℝ}
    (hu : MeasurableSet u) : μ u = μ (u ∩ {(0 : ℝ)}ᶜ) := by
  have hdis : Disjoint (u ∩ {(0 : ℝ)}) (u ∩ {(0 : ℝ)}ᶜ) := by
    refine disjoint_left.2 ?_
    intro x hx hx'
    simp only [mem_inter_iff, mem_compl_iff, mem_singleton_iff] at hx hx'
    exact hx'.2 hx.2
  have hunion : u = (u ∩ {(0 : ℝ)}) ∪ (u ∩ {(0 : ℝ)}ᶜ) := by
    rw [← inter_union_distrib_left, union_compl_self, inter_univ]
  have hμ : μ ((u ∩ {(0 : ℝ)}) ∪ (u ∩ {(0 : ℝ)}ᶜ)) =
      μ (u ∩ {(0 : ℝ)}) + μ (u ∩ {(0 : ℝ)}ᶜ) :=
    measure_union hdis (hu.inter (measurableSet_singleton (0 : ℝ)).compl)
  calc
    μ u = μ ((u ∩ {(0 : ℝ)}) ∪ (u ∩ {(0 : ℝ)}ᶜ)) := congrArg μ hunion
    _ = μ (u ∩ {(0 : ℝ)}) + μ (u ∩ {(0 : ℝ)}ᶜ) := hμ
    _ = 0 + μ (u ∩ {(0 : ℝ)}ᶜ) := by
      rw [measure_mono_null (inter_subset_right : u ∩ {(0 : ℝ)} ⊆ {(0 : ℝ)}) h0]
    _ = μ (u ∩ {(0 : ℝ)}ᶜ) := by rw [zero_add]

/-- Agreement of the sine measures at steps `1` and `√2` determines the jump measure. -/
lemma jumpMeasure_eq_of_sineMeasures {L M : LevyTriplet}
    (h1 : sineMeasure L 1 = sineMeasure M 1)
    (h2 : sineMeasure L (Real.sqrt 2) = sineMeasure M (Real.sqrt 2)) :
    L.jumpMeasure = M.jumpMeasure := by
  have hrest1 : L.jumpMeasure.restrict (sineSet 1) = M.jumpMeasure.restrict (sineSet 1) := by
    rw [jumpMeasure_restrict_eq_inv_sine, jumpMeasure_restrict_eq_inv_sine, h1]
  have hrest2 : L.jumpMeasure.restrict (sineSet (Real.sqrt 2)) =
      M.jumpMeasure.restrict (sineSet (Real.sqrt 2)) := by
    rw [jumpMeasure_restrict_eq_inv_sine, jumpMeasure_restrict_eq_inv_sine, h2]
  apply Measure.ext
  intro u hu
  rw [measure_eq_inter_compl L.isLevyMeasure.1 hu, measure_eq_inter_compl M.isLevyMeasure.1 hu,
    measure_inter_compl_singleton L.jumpMeasure hu,
    measure_inter_compl_singleton M.jumpMeasure hu, hrest1, hrest2]

/-- The Gaussian coefficient is the atom of the sine measure at step `1`. -/
lemma gaussianVariance_eq_of_sineMeasure {L M : LevyTriplet}
    (h : sineMeasure L 1 = sineMeasure M 1) :
    L.gaussianVariance = M.gaussianVariance := by
  have hreal := congrArg (fun μ : Measure ℝ => μ.real {(0 : ℝ)}) h
  rw [sineMeasure_real_singleton, sineMeasure_real_singleton] at hreal
  exact Subtype.coe_injective (by simpa using hreal)

/-- Triplets with the same Gaussian coefficient, jump measure and exponent have the same drift. -/
lemma drift_eq_of_exponent_eq {L M : LevyTriplet}
    (hγ : L.gaussianVariance = M.gaussianVariance) (hν : L.jumpMeasure = M.jumpMeasure)
    (hexp : ∀ t, L.exponent t = M.exponent t) : L.drift = M.drift := by
  have h1 := hexp 1
  rw [LevyTriplet.exponent_eq_levyIntegrand, LevyTriplet.exponent_eq_levyIntegrand, hγ, hν] at h1
  set J : ℂ := ∫ x, levyIntegrand 1 x ∂M.jumpMeasure
  set G : ℂ := (M.gaussianVariance : ℂ) * ((1 : ℝ) : ℂ) ^ 2 / 2
  have hG : I * (L.drift : ℂ) * (1 : ℝ) - G = I * (M.drift : ℂ) * (1 : ℝ) - G := by
    simpa [J, G] using add_right_cancel h1
  have hsum : I * (L.drift : ℂ) * (1 : ℝ) + (-G) =
      I * (M.drift : ℂ) * (1 : ℝ) + (-G) := by
    simpa only [sub_eq_add_neg] using hG
  have hlin : I * (L.drift : ℂ) * (1 : ℝ) = I * (M.drift : ℂ) * (1 : ℝ) :=
    add_right_cancel hsum
  have hone : ((1 : ℝ) : ℂ) = 1 := Complex.ofReal_one
  rw [hone, mul_one, mul_one] at hlin
  have hcast : (L.drift : ℂ) = (M.drift : ℂ) := mul_left_cancel₀ I_ne_zero hlin
  exact ofReal_inj.mp hcast

/-- Lévy triplets with the same data are equal. -/
lemma LevyTriplet.ext {L M : LevyTriplet} (hγ : L.gaussianVariance = M.gaussianVariance)
    (hb : L.drift = M.drift) (hν : L.jumpMeasure = M.jumpMeasure) : L = M := by
  cases L
  cases M
  subst hγ
  subst hb
  subst hν
  rfl

/-- Characteristic exponents with the same exponential determine the same triplet. -/
lemma levyTriplet_eq_of_forall_charFun_eq {L M : LevyTriplet}
    (h : ∀ t, exp (L.exponent t) = exp (M.exponent t)) : L = M := by
  have hexp : ∀ t, L.exponent t = M.exponent t := LevyTriplet.exponent_eq_of_exp_eq h
  have hsine (a : ℝ) : sineMeasure L a = sineMeasure M a := by
    have hL : IsFiniteMeasure (sineMeasure L a) := isFiniteMeasure_sineMeasure L a
    have hM : IsFiniteMeasure (sineMeasure M a) := isFiniteMeasure_sineMeasure M a
    apply Measure.ext_of_charFun
    ext t
    rw [charFun_sineMeasure, charFun_sineMeasure]
    congr 1
    simp only [secondDiff]
    rw [hexp (t + a), hexp (t - a), hexp t]
  have hγ := gaussianVariance_eq_of_sineMeasure (hsine 1)
  have hν := jumpMeasure_eq_of_sineMeasures (hsine 1) (hsine (Real.sqrt 2))
  have hb := drift_eq_of_exponent_eq hγ hν hexp
  exact LevyTriplet.ext hγ hb hν

end CKMA
