/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.InfinitelyDivisible.CompoundPoisson
public import CKMA.Probability.InfinitelyDivisible.Convergence
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Logarithms of infinitely divisible characteristic functions

An infinitely divisible real probability has a nowhere-vanishing characteristic function. On the
line that function admits a continuous logarithm vanishing at the origin, and every convolution
root has characteristic function `exp` of that logarithm divided by the order of the root.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Complex Filter Topology Set Polynomial
open scoped NNReal ENNReal

/-- Reflection through the origin sends a characteristic function to its value at `-t`. -/
lemma charFun_reflect (μ : Measure ℝ) (t : ℝ) :
    charFun (μ.map Neg.neg) t = charFun μ (-t) := by
  rw [charFun_apply_real, charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  push_cast
  rw [mul_comm]
  ring_nf

/-- Convolution against the reflected law squares the modulus of the characteristic function. -/
lemma charFun_symmetrize (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    charFun (μ ∗ μ.map Neg.neg) t = (‖charFun μ t‖ ^ 2 : ℝ) := by
  have : IsProbabilityMeasure (μ.map Neg.neg) := inferInstance
  rw [charFun_conv, charFun_reflect, charFun_neg]
  simpa [normSq_eq_norm_sq] using mul_conj (charFun μ t)

/-- A positive convolution root of an infinitely divisible law. -/
def convolutionRoot {μ : Measure ℝ} (h : IsInfinitelyDivisible μ) (n : ℕ) (hn : 0 < n) :
    Measure ℝ :=
  Classical.choose (h.2 n hn)

/-- The chosen convolution root is a probability measure. -/
lemma isProbabilityMeasure_convolutionRoot {μ : Measure ℝ} (h : IsInfinitelyDivisible μ)
    {n : ℕ} (hn : 0 < n) : IsProbabilityMeasure (convolutionRoot h n hn) :=
  (Classical.choose_spec (h.2 n hn)).1

/-- The chosen root convolves to the original law. -/
lemma convolutionPower_convolutionRoot {μ : Measure ℝ} (h : IsInfinitelyDivisible μ)
    {n : ℕ} (hn : 0 < n) : convolutionPower (convolutionRoot h n hn) n = μ :=
  (Classical.choose_spec (h.2 n hn)).2

/-- The law of a root symmetrized by an independent copy of its reflection. -/
def symmetrizedRoot {μ : Measure ℝ} (h : IsInfinitelyDivisible μ) (n : ℕ) : Measure ℝ :=
  if hn : 0 < n then
    convolutionRoot h n hn ∗ (convolutionRoot h n hn).map Neg.neg
  else
    Measure.dirac 0

/-- Every symmetrized root is a probability measure. -/
lemma isProbabilityMeasure_symmetrizedRoot {μ : Measure ℝ} (h : IsInfinitelyDivisible μ)
    (n : ℕ) : IsProbabilityMeasure (symmetrizedRoot h n) := by
  by_cases hn : 0 < n
  · have := isProbabilityMeasure_convolutionRoot h hn
    rw [symmetrizedRoot, dite_eq_left hn]
    infer_instance
  · rw [symmetrizedRoot, dite_eq_right hn]
    infer_instance

/-- The characteristic function of a symmetrized root is the squared modulus of the root. -/
lemma charFun_symmetrizedRoot {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) {n : ℕ} (hn : 0 < n) (t : ℝ) :
    charFun (symmetrizedRoot h n) t =
      (‖charFun μ t‖ ^ (2 / (n : ℝ)) : ℝ) := by
  have hν : IsProbabilityMeasure (convolutionRoot h n hn) :=
    isProbabilityMeasure_convolutionRoot h hn
  have hpow : charFun (convolutionRoot h n hn) t ^ n = charFun μ t := by
    rw [← charFun_convolutionPower, convolutionPower_convolutionRoot h hn]
  have hnorm : ‖charFun (convolutionRoot h n hn) t‖ ^ n = ‖charFun μ t‖ := by
    rw [← norm_pow, hpow]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsq : ‖charFun (convolutionRoot h n hn) t‖ ^ 2 =
      ‖charFun μ t‖ ^ ((2 : ℝ) / (n : ℝ)) := by
    set x : ℝ := ‖charFun (convolutionRoot h n hn) t‖
    have hx : 0 ≤ x := norm_nonneg _
    have hmul : (n : ℝ) * ((2 : ℝ) / (n : ℝ)) = 2 := by
      rw [mul_comm]
      exact div_mul_cancel₀ 2 hn0
    calc
      x ^ 2 = x ^ (2 : ℝ) := (Real.rpow_natCast x 2).symm
      _ = x ^ ((n : ℝ) * ((2 : ℝ) / (n : ℝ))) := by rw [hmul]
      _ = (x ^ (n : ℝ)) ^ ((2 : ℝ) / (n : ℝ)) := Real.rpow_mul hx _ _
      _ = (x ^ n) ^ ((2 : ℝ) / (n : ℝ)) := by rw [Real.rpow_natCast]
      _ = ‖charFun μ t‖ ^ ((2 : ℝ) / (n : ℝ)) := by rw [hnorm]
  have : IsProbabilityMeasure (convolutionRoot h n hn) := hν
  rw [symmetrizedRoot, dite_eq_left hn, charFun_symmetrize]
  exact congrArg Complex.ofReal hsq

/-- Positive powers `r ^ (2 / n)` tend to `1`. -/
lemma tendsto_rpow_two_div (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n : ℕ => r ^ (2 / (n : ℝ))) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ => Real.log r * (2 / (n : ℝ))) atTop (𝓝 0) := by
    simpa [mul_div_assoc] using tendsto_const_div_atTop_nhds_zero_nat (Real.log r * 2)
  refine Tendsto.congr (fun n => (Real.rpow_def_of_pos hr (2 / (n : ℝ))).symm) ?_
  have hexp : Tendsto (Real.exp ∘ fun n : ℕ => Real.log r * (2 / (n : ℝ))) atTop (𝓝 1) := by
    rw [← Real.exp_zero]
    exact (Real.continuous_exp.tendsto (0 : ℝ)).comp hlog
  exact hexp.congr fun _ => rfl

/-- Symmetrized roots converge pointwise to the indicator of the non-vanishing set. -/
lemma tendsto_charFun_symmetrizedRoot {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) (t : ℝ) :
    Tendsto (fun n => charFun (symmetrizedRoot h n) t) atTop
      (𝓝 (if charFun μ t = 0 then 0 else 1)) := by
  by_cases hzero : charFun μ t = 0
  · have hif : (if charFun μ t = 0 then (0 : ℂ) else 1) = 0 := by simp [hzero]
    rw [hif]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hden : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [charFun_symmetrizedRoot h hn, hzero, norm_zero,
      Real.zero_rpow (div_ne_zero two_ne_zero hden), Complex.ofReal_zero]
  · have hr : 0 < ‖charFun μ t‖ := norm_pos_iff.mpr hzero
    have hif : (if charFun μ t = 0 then (0 : ℂ) else 1) = 1 := by simp [hzero]
    rw [hif]
    refine (continuous_ofReal.tendsto (1 : ℝ)).comp (tendsto_rpow_two_div _ hr) |>.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact (charFun_symmetrizedRoot h hn t).symm

/-- The real line is simply connected. -/
lemma isSimplyConnected_univ_real : IsSimplyConnected (univ : Set ℝ) :=
  @SimplyConnectedSpace.ofContractible (univ : Set ℝ) _
    (convex_univ.contractibleSpace univ_nonempty)

/-- A continuous function on `ℝ` taking values in the `n`th roots of unity is constant. -/
lemma eq_one_of_continuous_pow_eq_one {n : ℕ} (hn : 0 < n) {f : ℝ → ℂ} (hf : Continuous f)
    (hf0 : f 0 = 1) (hp : ∀ t, f t ^ n = 1) : ∀ t, f t = 1 := by
  let S : Set ℂ := {z | z ^ n = 1}
  have hp0 : (X ^ n - C (1 : ℂ)) ≠ 0 := X_pow_sub_C_ne_zero hn 1
  have hfin : S.Finite := by
    refine (finite_setOfPred_isRoot hp0).subset ?_
    intro z hz
    simpa [S, IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using hz
  have hdisc : DiscreteTopology S := hfin.isDiscrete.to_subtype
  let g : ℝ → S := fun t => ⟨f t, hp t⟩
  have hg : Continuous g := continuous_induced_rng.mpr hf
  let u : Set ℝ := {t | g t = g 0}
  have hu : IsClopen u := by
    refine ⟨isClosed_eq hg continuous_const, ?_⟩
    have hop : IsOpen ({g 0} : Set S) := isOpen_discrete _
    convert hop.preimage hg
    ext t
    simp [u]
  have huniv : u = univ := IsClopen.eq_univ hu ⟨0, rfl⟩
  intro t
  have ht : g t = g 0 := by
    have : t ∈ u := by
      rw [huniv]
      exact mem_univ t
    simpa [u] using this
  have hcoe : f t = f 0 := congrArg Subtype.val ht
  simpa [hf0] using hcoe

/-- An infinitely divisible characteristic function has no zero. -/
lemma charFun_ne_zero_of_isInfinitelyDivisible {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) (t : ℝ) : charFun μ t ≠ 0 := by
  by_contra ht
  have hprob : ∀ n, IsProbabilityMeasure (symmetrizedRoot h n) :=
    isProbabilityMeasure_symmetrizedRoot h
  let g : ℝ → ℂ := fun s => if charFun μ s = 0 then 0 else 1
  obtain ⟨ν, hν, hchar⟩ := exists_isProbabilityMeasure_of_tendsto_charFun
    (μ := symmetrizedRoot h) (f := g)
    (by
      have ht0pos : 0 < sInf {s : ℝ | 0 < s ∧ charFun μ s = 0} := by
        have hev : ∀ᶠ s in 𝓝 (0 : ℝ), charFun μ s ≠ 0 :=
          continuous_charFun.continuousAt.preimage_mem_nhds
            (isOpen_compl_singleton.mem_nhds (by simp))
        rw [Metric.eventually_nhds_iff] at hev
        obtain ⟨ε, hε, hεchar⟩ := hev
        let Z : Set ℝ := {s | 0 < s ∧ charFun μ s = 0}
        have hZne : Z.Nonempty := by
          have htne : t ≠ 0 := by
            intro h0
            simp [h0] at ht
          rcases lt_trichotomy t 0 with hneg | rfl | hpos
          · exact ⟨-t, neg_pos.mpr hneg, by simpa [charFun_neg] using ht⟩
          · exact absurd rfl htne
          · exact ⟨t, hpos, ht⟩
        have hlb : ∀ s ∈ Z, ε ≤ s := by
          intro s hs
          by_contra hlt
          have hlt' : s < ε := lt_of_not_ge hlt
          have : dist s 0 < ε := by
            rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]
            exact hlt'
          exact hεchar this hs.2
        exact hε.trans_le (le_csInf hZne hlb)
      have hgone : ∀ s, |s| < sInf {s : ℝ | 0 < s ∧ charFun μ s = 0} → g s = 1 := by
        intro s hs
        let Z : Set ℝ := {s | 0 < s ∧ charFun μ s = 0}
        let t0 : ℝ := sInf Z
        have hne : charFun μ s ≠ 0 := by
          intro hzero
          have hsne : s ≠ 0 := by
            intro h0
            simp [h0] at hzero
          have hposzero : 0 < |s| := abs_pos.mpr hsne
          have hmem : |s| ∈ Z := by
            refine ⟨hposzero, ?_⟩
            rcases le_or_gt 0 s with hpos | hneg
            · rw [abs_of_nonneg hpos]
              exact hzero
            · rw [abs_of_neg hneg, charFun_neg, hzero, map_zero]
          have hle : t0 ≤ |s| := csInf_le ⟨0, fun u hu => hu.1.le⟩ hmem
          exact not_lt_of_ge hle (by simpa [t0, Z] using hs)
        simp [g, hne]
      have hg0 : g 0 = 1 := by simp [g]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) ht0pos] with s hs
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
      rw [hgone s hs, hg0])
    (tendsto_charFun_symmetrizedRoot h)
  have hgcont : Continuous g := by
    simpa [hchar] using (continuous_charFun (μ := ν))
  let Z : Set ℝ := {s : ℝ | 0 < s ∧ charFun μ s = 0}
  have hZne : Z.Nonempty := by
    have htne : t ≠ 0 := by
      intro h0
      simp [h0] at ht
    rcases lt_trichotomy t 0 with hneg | rfl | hpos
    · exact ⟨-t, neg_pos.mpr hneg, by simpa [charFun_neg] using ht⟩
    · exact absurd rfl htne
    · exact ⟨t, hpos, ht⟩
  have hZbdd : BddBelow Z := ⟨0, fun s hs => hs.1.le⟩
  let t0 : ℝ := sInf Z
  have hclosed : IsClosed {s : ℝ | charFun μ s = 0} :=
    isClosed_eq continuous_charFun continuous_const
  have ht0mem : t0 ∈ closure Z := csInf_mem_closure hZne hZbdd
  have ht0zero : charFun μ t0 = 0 := by
    have hsub : closure Z ⊆ {s | charFun μ s = 0} := by
      rw [← hclosed.closure_eq]
      exact closure_mono fun s hs => hs.2
    exact hsub ht0mem
  have ht0pos : 0 < t0 := by
    have hev : ∀ᶠ s in 𝓝 (0 : ℝ), charFun μ s ≠ 0 :=
      continuous_charFun.continuousAt.preimage_mem_nhds
        (isOpen_compl_singleton.mem_nhds (by simp))
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hεchar⟩ := hev
    have hlb : ∀ s ∈ Z, ε ≤ s := by
      intro s hs
      by_contra hlt
      have : dist s 0 < ε := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]
        exact lt_of_not_ge hlt
      exact hεchar this hs.2
    exact hε.trans_le (le_csInf hZne hlb)
  have hbelow : ∀ s, 0 < s → s < t0 → charFun μ s ≠ 0 := by
    intro s hspos hsl hzero
    have hle : t0 ≤ s := csInf_le hZbdd ⟨hspos, hzero⟩
    exact not_lt_of_ge hle hsl
  have hgt0 : g t0 = 0 := by simp [g, ht0zero]
  have htend0 : Tendsto g (𝓝 t0) (𝓝 (0 : ℂ)) := by
    rw [← hgt0]
    exact hgcont.continuousAt
  have hev := htend0.eventually (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hεg⟩ := hev
  let s : ℝ := t0 - min (ε / 2) (t0 / 2)
  have hspos : 0 < s := by
    have hmin : min (ε / 2) (t0 / 2) ≤ t0 / 2 := min_le_right _ _
    linarith
  have hsl : s < t0 := by
    have hmin : 0 < min (ε / 2) (t0 / 2) := by positivity
    linarith
  have hdist : dist s t0 < ε := by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hsl)]
    have hmin : min (ε / 2) (t0 / 2) ≤ ε / 2 := min_le_left _ _
    linarith
  have hg1 : g s = 1 := by simp [g, hbelow s hspos hsl]
  have hball : ‖g s‖ < 1 / 2 := by
    simpa [dist_eq_norm, sub_zero] using hεg hdist
  rw [hg1, norm_one] at hball
  linarith

/-- A nowhere-zero characteristic function has a continuous logarithm vanishing at `0`. -/
lemma exists_continuous_charExponent {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hnez : ∀ t, charFun μ t ≠ 0) :
    ∃ ψ : ℝ → ℂ, Continuous ψ ∧ ψ 0 = 0 ∧ ∀ t, exp (ψ t) = charFun μ t := by
  obtain ⟨f, hf, hfeq⟩ := Complex.exists_continuousOn_eqOn_exp_comp isSimplyConnected_univ_real
    isOpen_univ continuous_charFun.continuousOn (by
      intro hmem
      rcases hmem with ⟨t, -, ht⟩
      exact hnez t ht)
  have hfcont : Continuous f := continuousOn_univ.mp hf
  have hfexp : ∀ t, exp (f t) = charFun μ t := fun t => hfeq (mem_univ t)
  refine ⟨fun t => f t - f 0, hfcont.sub continuous_const, sub_self _, ?_⟩
  intro t
  rw [exp_sub, hfexp t, hfexp 0, charFun_zero, probReal_univ, Complex.ofReal_one,
    div_one]

/-- A continuous logarithm of an infinitely divisible characteristic function, zero at `0`. -/
def charExponent {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ) :
    ℝ → ℂ :=
  Classical.choose
    (exists_continuous_charExponent (charFun_ne_zero_of_isInfinitelyDivisible h))

/-- The chosen logarithm is continuous. -/
lemma continuous_charExponent {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) : Continuous (charExponent h) :=
  (Classical.choose_spec
    (exists_continuous_charExponent (charFun_ne_zero_of_isInfinitelyDivisible h))).1

/-- The chosen logarithm vanishes at the origin. -/
lemma charExponent_zero {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) : charExponent h 0 = 0 :=
  (Classical.choose_spec
    (exists_continuous_charExponent (charFun_ne_zero_of_isInfinitelyDivisible h))).2.1

/-- Exponentiating the chosen logarithm recovers the characteristic function. -/
lemma exp_charExponent {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) (t : ℝ) : exp (charExponent h t) = charFun μ t :=
  (Classical.choose_spec
    (exists_continuous_charExponent (charFun_ne_zero_of_isInfinitelyDivisible h))).2.2 t

/-- Each convolution root has characteristic function `exp` of the exponent divided by `n`. -/
lemma charFun_convolutionRoot {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsInfinitelyDivisible μ) {n : ℕ} (hn : 0 < n) (t : ℝ) :
    charFun (convolutionRoot h n hn) t = exp (charExponent h t / (n : ℂ)) := by
  have hν : IsProbabilityMeasure (convolutionRoot h n hn) :=
    isProbabilityMeasure_convolutionRoot h hn
  have : IsProbabilityMeasure (convolutionRoot h n hn) := hν
  let θ : ℝ → ℂ := fun s =>
    charFun (convolutionRoot h n hn) s * exp (-(charExponent h s / (n : ℂ)))
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hθpow : ∀ s, θ s ^ n = 1 := by
    intro s
    have hpow : charFun (convolutionRoot h n hn) s ^ n = charFun μ s := by
      rw [← charFun_convolutionPower, convolutionPower_convolutionRoot h hn]
    have harg : charExponent h s + (n : ℂ) * -(charExponent h s / (n : ℂ)) = 0 := by
      rw [mul_neg, ← sub_eq_add_neg, mul_div_cancel₀ _ hnC, sub_self]
    simp only [θ]
    rw [mul_pow, hpow, ← exp_nat_mul, ← exp_charExponent h s, ← exp_add, harg, exp_zero]
  have hθ0 : θ 0 = 1 := by
    simp only [θ, charFun_zero, probReal_univ, charExponent_zero, zero_div, neg_zero,
      exp_zero, Complex.ofReal_one, mul_one]
  have hθcont : Continuous θ := by
    have hdiv : Continuous fun s => charExponent h s / (n : ℂ) :=
      (continuous_charExponent h).div_const _
    exact continuous_charFun.mul (continuous_exp.comp hdiv.neg)
  have hone : θ t = 1 := eq_one_of_continuous_pow_eq_one hn hθcont hθ0 hθpow t
  have hmul : charFun (convolutionRoot h n hn) t =
      θ t * exp (charExponent h t / (n : ℂ)) := by
    simp only [θ]
    rw [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
  rw [hmul, hone, one_mul]

end CKMA
