/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Prod
import CKMA.Probability.LimitTheorems.SteinSolution

/-!
# The Berry–Esseen bound by Stein's method

For independent centered real random variables `ξ i`, `i ∈ s`, with `∑ i ∈ s, E ξ i ^ 2 = 1`
and third absolute moments summing to `γ`, the distribution function of `W = ∑ i ∈ s, ξ i`
differs from the standard Gaussian distribution function by at most `40 γ` at every point.

The proof is Stein's method with the concentration-inequality argument of Chen and Shao
(L. H. Y. Chen, L. Goldstein, Q.-M. Shao, *Normal approximation by Stein's method*, Springer
2011, Sections 3.4.1 and 3.5). The Stein solution and its pointwise bounds are in
`CKMA.Probability.LimitTheorems.SteinSolution`. The constant `40` is not optimal.

## Main results

* `CKMA.integral_abs_mul_integral_sq_le`, `CKMA.integral_sq_pow_three_le`: Lyapunov-type
  moment inequalities `E|X| E X² ≤ E|X|³` and `(E X²)³ ≤ (E|X|³)²`.
* `CKMA.measureReal_abs_sum_sub_le`: the concentration inequality
  `P(|W - z| ≤ r) ≤ 4 r + 8 γ` for sums with second-moment sum between `1/2` and `1`.
* `CKMA.abs_measureReal_sum_le_sub_cdf_le`: the Berry–Esseen bound
  `|P(W ≤ z) - Φ z| ≤ 40 γ`.
* `CKMA.abs_measureReal_sum_div_le_sub_cdf_le`: the identically distributed case
  `|P(S_n / (σ √n) ≤ x) - Φ x| ≤ 40 E|X|³ / (σ³ √n)`.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

section Moments

variable [IsProbabilityMeasure μ] {X : Ω → ℝ}

private lemma integrable_abs_pow_three (hX : MemLp X 3 μ) :
    Integrable (fun ω ↦ |X ω| ^ 3) μ := by
  have := (show MemLp X ((3 : ℕ) : ENNReal) μ by exact_mod_cast hX).integrable_norm_pow'
  simpa using this

private lemma integrable_sq_of_memLp_three (hX : MemLp X 3 μ) :
    Integrable (fun ω ↦ X ω ^ 2) μ :=
  (hX.mono_exponent (by norm_num)).integrable_sq

/-- `E|Y| ≤ (E Y² / t + t) / 2` for every `t > 0`. -/
private lemma integral_abs_le_of_memLp_two {Y : Ω → ℝ} (hY : MemLp Y 2 μ) {t : ℝ} (ht : 0 < t) :
    ∫ ω, |Y ω| ∂μ ≤ ((∫ ω, Y ω ^ 2 ∂μ) / t + t) / 2 := by
  have hi := hY.integrable_sq
  calc ∫ ω, |Y ω| ∂μ ≤ ∫ ω, (Y ω ^ 2 / t + t) / 2 ∂μ := by
        refine integral_mono (hY.integrable one_le_two).abs
          (((hi.div_const t).add (integrable_const t)).div_const 2) fun ω ↦ ?_
        dsimp only
        rw [le_div_iff₀ two_pos, div_add' _ _ _ ht.ne', le_div_iff₀ ht]
        nlinarith [sq_abs (Y ω), sq_nonneg (|Y ω| - t)]
    _ = _ := by
        rw [integral_div, integral_add (hi.div_const t) (integrable_const t), integral_div,
          integral_const, probReal_univ, one_smul]

/-- `E|Y| ≤ m` when `m ≥ 0` and `m² = E Y²`. -/
private lemma integral_abs_le_of_sq_eq {Y : Ω → ℝ} (hY : MemLp Y 2 μ) {m : ℝ} (hm : 0 ≤ m)
    (hm2 : m ^ 2 = ∫ ω, Y ω ^ 2 ∂μ) : ∫ ω, |Y ω| ∂μ ≤ m := by
  rcases hm.eq_or_lt with rfl | hm
  · have h0 : ∫ ω, Y ω ^ 2 ∂μ = 0 := by rw [← hm2]; ring
    have hY0 : ∀ᵐ ω ∂μ, Y ω = 0 := by
      have := (integral_eq_zero_iff_of_nonneg (fun ω ↦ sq_nonneg (Y ω)) hY.integrable_sq).1 h0
      filter_upwards [this] with ω hω
      simpa using hω
    rw [integral_eq_zero_of_ae (by filter_upwards [hY0] with ω hω; simp [hω])]
  · have := integral_abs_le_of_memLp_two hY hm
    rw [← hm2] at this
    calc _ ≤ _ := this
      _ = m := by field_simp; ring

/-- `E|Y| ≤ √(E Y²)`. -/
private lemma integral_abs_le_sqrt {Y : Ω → ℝ} (hY : MemLp Y 2 μ) :
    ∫ ω, |Y ω| ∂μ ≤ √(∫ ω, Y ω ^ 2 ∂μ) :=
  integral_abs_le_of_sq_eq hY (Real.sqrt_nonneg _)
    (Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _))

private lemma pow_three_le_of_sq_eq (hX : MemLp X 3 μ) {m : ℝ} (hm : 0 ≤ m)
    (hm2 : m ^ 2 = ∫ ω, X ω ^ 2 ∂μ) : m ^ 3 ≤ ∫ ω, |X ω| ^ 3 ∂μ := by
  have hρ : 0 ≤ ∫ ω, |X ω| ^ 3 ∂μ := integral_nonneg fun _ ↦ by positivity
  rcases hm.eq_or_lt with rfl | hm
  · simpa using hρ
  have h3 := integrable_abs_pow_three hX
  have h2 := integrable_sq_of_memLp_three hX
  have hle : ∫ ω, X ω ^ 2 ∂μ ≤ ∫ ω, (2 * |X ω| ^ 3 + m ^ 3) / (3 * m) ∂μ := by
    refine integral_mono h2 (((h3.const_mul 2).add (integrable_const _)).div_const _)
      fun ω ↦ ?_
    dsimp only
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_abs (X ω), mul_nonneg (sq_nonneg (|X ω| - m))
      (by positivity : (0 : ℝ) ≤ 2 * |X ω| + m)]
  rw [integral_div, integral_add (h3.const_mul 2) (integrable_const _), integral_const_mul,
    integral_const, probReal_univ, one_smul, ← hm2, le_div_iff₀ (by positivity)] at hle
  nlinarith

/-- `(√(E X²))³ ≤ E|X|³`. -/
private lemma sqrt_integral_sq_pow_three_le (hX : MemLp X 3 μ) :
    √(∫ ω, X ω ^ 2 ∂μ) ^ 3 ≤ ∫ ω, |X ω| ^ 3 ∂μ :=
  pow_three_le_of_sq_eq hX (Real.sqrt_nonneg _)
    (Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _))

/-- Lyapunov-type inequality `E|X| · E X² ≤ E|X|³`. -/
theorem integral_abs_mul_integral_sq_le (hX : MemLp X 3 μ) :
    (∫ ω, |X ω| ∂μ) * ∫ ω, X ω ^ 2 ∂μ ≤ ∫ ω, |X ω| ^ 3 ∂μ := by
  have h1 := integral_abs_le_sqrt (hX.mono_exponent (by norm_num))
  have h3 := sqrt_integral_sq_pow_three_le hX
  have hm2 : √(∫ ω, X ω ^ 2 ∂μ) ^ 2 = ∫ ω, X ω ^ 2 ∂μ :=
    Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _)
  have h0 : 0 ≤ ∫ ω, X ω ^ 2 ∂μ := integral_nonneg fun _ ↦ sq_nonneg _
  calc _ ≤ √(∫ ω, X ω ^ 2 ∂μ) * ∫ ω, X ω ^ 2 ∂μ := mul_le_mul_of_nonneg_right h1 h0
    _ = √(∫ ω, X ω ^ 2 ∂μ) ^ 3 := by
      rw [show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one, hm2]
    _ ≤ _ := h3

/-- Lyapunov's inequality in the form `(E X²)³ ≤ (E|X|³)²`. -/
theorem integral_sq_pow_three_le (hX : MemLp X 3 μ) :
    (∫ ω, X ω ^ 2 ∂μ) ^ 3 ≤ (∫ ω, |X ω| ^ 3 ∂μ) ^ 2 := by
  have h3 := sqrt_integral_sq_pow_three_le hX
  have hm2 : √(∫ ω, X ω ^ 2 ∂μ) ^ 2 = ∫ ω, X ω ^ 2 ∂μ :=
    Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _)
  rw [← hm2]
  calc (√(∫ ω, X ω ^ 2 ∂μ) ^ 2) ^ 3 = (√(∫ ω, X ω ^ 2 ∂μ) ^ 3) ^ 2 := by ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity) h3 2

end Moments

section Independence

variable [IsProbabilityMeasure μ] {ι : Type*} [DecidableEq ι] {ξ : ι → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
/-- `ξ i` is independent of the sum of the `ξ j` over `s.erase i`. -/
private lemma indepFun_sum_erase (hmeas : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (s : Finset ι) (i : ι) : IndepFun (ξ i) (fun ω ↦ ∑ j ∈ s.erase i, ξ j ω) μ := by
  have := hind.indepFun_finsetSum_of_notMem hmeas (s := s.erase i) (notMem_erase i s)
  have h : (∑ j ∈ s.erase i, ξ j) = fun ω ↦ ∑ j ∈ s.erase i, ξ j ω := by
    ext ω; simp [Finset.sum_apply]
  rw [h] at this
  exact this.symm

omit [IsProbabilityMeasure μ] in
/-- Expectations of products of functions of `ξ i` and of the sum over `s.erase i` factor. -/
private lemma integral_comp_mul_comp_sum_erase (hmeas : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (s : Finset ι) (i : ι) {g h : ℝ → ℝ} (hg : Measurable g)
    (hh : Measurable h) :
    ∫ ω, g (ξ i ω) * h (∑ j ∈ s.erase i, ξ j ω) ∂μ =
      (∫ ω, g (ξ i ω) ∂μ) * ∫ ω, h (∑ j ∈ s.erase i, ξ j ω) ∂μ :=
  ((indepFun_sum_erase hmeas hind s i).comp hg hh).integral_fun_mul_eq_mul_integral
    (hg.comp (hmeas i)).aestronglyMeasurable
    (hh.comp (Finset.measurable_sum _ fun j _ ↦ hmeas j)).aestronglyMeasurable

omit [DecidableEq ι] in
/-- The second moment of a sum of independent centered variables is the sum of the second
moments. -/
private lemma integral_sum_sq (hmeas : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (J : Finset ι) (hL2 : ∀ j ∈ J, MemLp (ξ j) 2 μ) (hc : ∀ j ∈ J, ∫ ω, ξ j ω ∂μ = 0) :
    ∫ ω, (∑ j ∈ J, ξ j ω) ^ 2 ∂μ = ∑ j ∈ J, ∫ ω, ξ j ω ^ 2 ∂μ := by
  have hv := IndepFun.variance_sum hL2 fun i _ j _ hij ↦ hind.indepFun hij
  have hsum : (∑ j ∈ J, ξ j) = fun ω ↦ ∑ j ∈ J, ξ j ω := by ext; simp
  have h0 : ∫ ω, ∑ j ∈ J, ξ j ω ∂μ = 0 := by
    rw [integral_finsetSum _ fun j hj ↦ (hL2 j hj).integrable one_le_two]
    exact sum_eq_zero hc
  rw [hsum, variance_of_integral_eq_zero
    (Finset.measurable_sum _ fun j _ ↦ hmeas j).aemeasurable h0] at hv
  rw [hv]
  exact sum_congr rfl fun j hj ↦ variance_of_integral_eq_zero (hmeas j).aemeasurable (hc j hj)

end Independence

section Product

variable [IsProbabilityMeasure μ]

/-- For independent `X` and `Y` and a nonnegative weight `g`, the bound
`P(|Y - z| ≤ r) ≤ a r + b` for all `r ≥ 0` gives
`E[g(X) 1{|Y - z| ≤ |X|}] ≤ E[g(X) (a |X| + b)]`. -/
theorem integral_mul_ite_abs_sub_le_le {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y μ) {g : ℝ → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hgi : Integrable (fun ω ↦ g (X ω)) μ) (hgi' : Integrable (fun ω ↦ g (X ω) * |X ω|) μ)
    {z a b : ℝ} (hab : ∀ r, 0 ≤ r → μ.real {ω | |Y ω - z| ≤ r} ≤ a * r + b) :
    ∫ ω, g (X ω) * (if |Y ω - z| ≤ |X ω| then 1 else 0) ∂μ ≤
      ∫ ω, g (X ω) * (a * |X ω| + b) ∂μ := by
  let F : ℝ × ℝ → ℝ := fun p ↦ g p.1 * (if |p.2 - z| ≤ |p.1| then 1 else 0)
  have hF : Measurable F := (hg.comp measurable_fst).mul
    (Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) measurable_const
      measurable_const)
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hXY
  have hgPX : Integrable g (μ.map X) :=
    (integrable_map_measure hg.aestronglyMeasurable hX.aemeasurable).2 hgi
  have hFint : Integrable F ((μ.map X).prod (μ.map Y)) := by
    refine (hgPX.comp_fst (μ.map Y)).mono' hF.aestronglyMeasurable (ae_of_all _ fun p ↦ ?_)
    simp only [F, Real.norm_eq_abs]
    split_ifs <;> simp [abs_of_nonneg (hg0 _), hg0]
  have hlhs : ∫ ω, g (X ω) * (if |Y ω - z| ≤ |X ω| then 1 else 0) ∂μ =
      ∫ p, F p ∂((μ.map X).prod (μ.map Y)) := by
    rw [← hmap, integral_map (hX.prodMk hY).aemeasurable hF.aestronglyMeasurable]
  have hinner (x : ℝ) : ∫ y, F (x, y) ∂(μ.map Y) = g x * μ.real {ω | |Y ω - z| ≤ |x|} := by
    have hS : MeasurableSet {y : ℝ | |y - z| ≤ |x|} :=
      measurableSet_le (by fun_prop) measurable_const
    have : (fun y ↦ F (x, y)) = fun y ↦ g x * Set.indicator {y | |y - z| ≤ |x|} 1 y := by
      ext y; simp [F, Set.indicator_apply]
    rw [this, integral_const_mul, integral_indicator_one hS, map_measureReal_apply hY hS]
    rfl
  have hG : Integrable (fun x ↦ g x * (a * |x| + b)) (μ.map X) := by
    refine (integrable_map_measure ?_ hX.aemeasurable).2 ?_
    · exact (hg.mul ((measurable_const.mul measurable_id.norm).add measurable_const))
        |>.aestronglyMeasurable
    · have : (fun x ↦ g x * (a * |x| + b)) ∘ X =
          fun ω ↦ a * (g (X ω) * |X ω|) + b * g (X ω) := by
        ext ω; simp only [Function.comp_apply]; ring
      rw [this]
      exact (hgi'.const_mul a).add (hgi.const_mul b)
  rw [hlhs, integral_prod F hFint]
  calc ∫ x, ∫ y, F (x, y) ∂(μ.map Y) ∂(μ.map X)
      ≤ ∫ x, g x * (a * |x| + b) ∂(μ.map X) := by
        refine integral_mono hFint.integral_prod_left hG fun x ↦ ?_
        dsimp only
        rw [hinner]
        exact mul_le_mul_of_nonneg_left (hab _ (abs_nonneg x)) (hg0 x)
    _ = _ := integral_map hX.aemeasurable hG.aestronglyMeasurable

end Product

section Concentration

/-- The ramp `w ↦ max (-K) (min K (w - z))`. -/
private def ramp (z K w : ℝ) : ℝ := max (-K) (min K (w - z))

private lemma continuous_ramp (z K : ℝ) : Continuous (ramp z K) := by
  unfold ramp; fun_prop

private lemma abs_ramp_le (z K w : ℝ) (hK : 0 ≤ K) : |ramp z K w| ≤ K := by
  unfold ramp
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

/-- On `|s - z| ≤ r` the ramp at level `r + δ` increases at least by `min δ |x|` over an
increment `x`, so `x (f s - f (s - x)) ≥ |x| min δ |x|`. -/
private lemma abs_mul_min_le_ramp (z r δ s x : ℝ) (hδ : 0 ≤ δ) (hs : |s - z| ≤ r) :
    |x| * min δ |x| ≤ x * (ramp z (r + δ) s - ramp z (r + δ) (s - x)) := by
  rw [abs_le] at hs
  unfold ramp
  rcases abs_cases x with ⟨hx, hx0⟩ | ⟨hx, hx0⟩ <;> rw [hx] <;>
    rcases le_total δ |x| with h | h <;> rw [hx] at h <;>
    simp only [min_def, max_def] <;> split_ifs <;> nlinarith

private lemma ramp_mul_nonneg (z K s x : ℝ) :
    0 ≤ x * (ramp z K s - ramp z K (s - x)) := by
  unfold ramp
  rcases le_total 0 x with hx | hx
  · exact mul_nonneg hx (sub_nonneg.2 (max_le_max le_rfl (min_le_min le_rfl (by linarith))))
  · exact mul_nonneg_of_nonpos_of_nonpos hx
      (sub_nonpos.2 (max_le_max le_rfl (min_le_min le_rfl (by linarith))))

private lemma abs_mul_min_lower (γ x : ℝ) (hγ : 0 < γ) :
    x ^ 2 - |x| ^ 3 / (4 * γ) ≤ |x| * min γ |x| := by
  rcases le_total |x| γ with h | h
  · rw [min_eq_right h, ← sq, sq_abs]
    have : 0 ≤ |x| ^ 3 / (4 * γ) := by positivity
    linarith
  · rw [min_eq_left h, ← sq_abs x]
    have h4 : 0 < 4 * γ := by positivity
    have key : |x| ^ 2 * (4 * γ) - |x| ^ 3 ≤ |x| * γ * (4 * γ) := by
      nlinarith [mul_nonneg (abs_nonneg x) (sq_nonneg (|x| - 2 * γ))]
    have e : |x| ^ 2 - |x| ^ 3 / (4 * γ) = (|x| ^ 2 * (4 * γ) - |x| ^ 3) / (4 * γ) := by
      field_simp
    rw [e, div_le_iff₀ h4]
    exact key

private lemma sq_abs_mul_min_le (γ x : ℝ) (hγ : 0 ≤ γ) :
    (|x| * min γ |x|) ^ 2 ≤ γ * |x| ^ 3 := by
  have h1 : min γ |x| ≤ γ := min_le_left _ _
  have h2 : min γ |x| ≤ |x| := min_le_right _ _
  have h0 : 0 ≤ min γ |x| := le_min hγ (abs_nonneg x)
  have : min γ |x| ^ 2 ≤ γ * |x| := by nlinarith
  calc (|x| * min γ |x|) ^ 2 = |x| ^ 2 * min γ |x| ^ 2 := by ring
    _ ≤ |x| ^ 2 * (γ * |x|) := by gcongr
    _ = γ * |x| ^ 3 := by ring

variable [IsProbabilityMeasure μ] {ι : Type*} [DecidableEq ι] {ξ : ι → Ω → ℝ}

omit [DecidableEq ι] in
/-- `E|η - Eη| ≤ γ` for the sum `η` of the variables `|ξ j| min γ |ξ j|`. -/
private lemma integral_abs_sub_integral_le (hmeas : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (J : Finset ι) (hL3 : ∀ j ∈ J, MemLp (ξ j) 3 μ) {γ : ℝ}
    (hγ : 0 < γ) (hγJ : ∑ j ∈ J, ∫ ω, |ξ j ω| ^ 3 ∂μ ≤ γ) :
    ∫ ω, |∑ j ∈ J, |ξ j ω| * min γ |ξ j ω| -
      ∫ ω', ∑ j ∈ J, |ξ j ω'| * min γ |ξ j ω'| ∂μ| ∂μ ≤ γ := by
  set η : ι → Ω → ℝ := fun j ω ↦ |ξ j ω| * min γ |ξ j ω|
  have hηm (j : ι) : Measurable (η j) := by
    have := hmeas j
    simp only [η]
    fun_prop
  have hηL2 (j : ι) (hj : j ∈ J) : MemLp (η j) 2 μ := by
    refine (((hL3 j hj).mono_exponent (by norm_num)).const_mul γ).of_le
      (hηm j).aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
    simp only [η, Real.norm_eq_abs, abs_mul, abs_abs]
    rw [abs_of_nonneg (le_min hγ.le (abs_nonneg _)), abs_of_pos hγ, mul_comm]
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg _)
  have hS : MemLp (fun ω ↦ ∑ j ∈ J, η j ω) 2 μ := memLp_finsetSum J hηL2
  have hSm : Measurable (fun ω ↦ ∑ j ∈ J, η j ω) := Finset.measurable_sum _ fun j _ ↦ hηm j
  have hvar : variance (fun ω ↦ ∑ j ∈ J, η j ω) μ ≤ γ ^ 2 := by
    have hgm : Measurable fun x : ℝ ↦ |x| * min γ |x| := by fun_prop
    have hv := IndepFun.variance_sum hηL2 fun i _ j _ hij ↦
      (hind.indepFun hij).comp hgm hgm
    have hsum : (∑ j ∈ J, η j) = fun ω ↦ ∑ j ∈ J, η j ω := by ext; simp
    rw [hsum] at hv
    rw [hv]
    calc ∑ j ∈ J, variance (η j) μ ≤ ∑ j ∈ J, γ * ∫ ω, |ξ j ω| ^ 3 ∂μ := by
          refine sum_le_sum fun j hj ↦ (variance_le_expectation_sq
            (hηm j).aestronglyMeasurable).trans ?_
          rw [← integral_const_mul]
          exact integral_mono (hηL2 j hj).integrable_sq
            ((integrable_abs_pow_three (hL3 j hj)).const_mul γ)
            fun ω ↦ sq_abs_mul_min_le γ (ξ j ω) hγ.le
      _ = γ * ∑ j ∈ J, ∫ ω, |ξ j ω| ^ 3 ∂μ := by rw [mul_sum]
      _ ≤ γ * γ := by gcongr
      _ = γ ^ 2 := by ring
  have hc : MemLp (fun ω ↦ ∑ j ∈ J, η j ω - ∫ ω', ∑ j ∈ J, η j ω' ∂μ) 2 μ :=
    hS.sub (memLp_const _)
  have := integral_abs_le_of_memLp_two hc hγ
  rw [← variance_eq_integral hSm.aemeasurable] at this
  calc _ ≤ _ := this
    _ ≤ (γ ^ 2 / γ + γ) / 2 := by gcongr
    _ = γ := by field_simp; ring

/-- **Concentration inequality** for sums of independent centered variables whose second
moments sum to a value between `1 / 2` and `1`: if `γ > 0` bounds the sum of the third
absolute moments, then `P(|S - z| ≤ r) ≤ 4 r + 8 γ` for every `r ≥ 0`. -/
theorem measureReal_abs_sum_sub_le (hmeas : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (J : Finset ι) (hL3 : ∀ j ∈ J, MemLp (ξ j) 3 μ) (hc : ∀ j ∈ J, ∫ ω, ξ j ω ∂μ = 0)
    (hB : 1 / 2 ≤ ∑ j ∈ J, ∫ ω, ξ j ω ^ 2 ∂μ) (hB1 : ∑ j ∈ J, ∫ ω, ξ j ω ^ 2 ∂μ ≤ 1)
    {γ : ℝ} (hγ : 0 < γ) (hγJ : ∑ j ∈ J, ∫ ω, |ξ j ω| ^ 3 ∂μ ≤ γ) (z : ℝ) {r : ℝ}
    (hr : 0 ≤ r) : μ.real {ω | |∑ j ∈ J, ξ j ω - z| ≤ r} ≤ 4 * r + 8 * γ := by
  set S : Ω → ℝ := fun ω ↦ ∑ j ∈ J, ξ j ω with hS_def
  set f := ramp z (r + γ)
  set A := {ω | |S ω - z| ≤ r}
  set η : Ω → ℝ := fun ω ↦ ∑ j ∈ J, |ξ j ω| * min γ |ξ j ω|
  have hSm : Measurable S := Finset.measurable_sum _ fun j _ ↦ hmeas j
  have hAm : MeasurableSet A := measurableSet_le (by fun_prop) measurable_const
  have hfm : Measurable f := (continuous_ramp z (r + γ)).measurable
  have hK : 0 ≤ r + γ := by linarith
  have hL1 (j : ι) (hj : j ∈ J) : Integrable (ξ j) μ := (hL3 j hj).integrable (by norm_num)
  have hL2 (j : ι) (hj : j ∈ J) : MemLp (ξ j) 2 μ := (hL3 j hj).mono_exponent (by norm_num)
  have hSL2 : MemLp S 2 μ := memLp_finsetSum J hL2
  have hηj (j : ι) (hj : j ∈ J) : Integrable (fun ω ↦ |ξ j ω| * min γ |ξ j ω|) μ := by
    have := hmeas j
    refine ((hL1 j hj).abs.const_mul γ).mono' (by fun_prop) (ae_of_all _ fun ω ↦ ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_abs]
    rw [abs_of_nonneg (le_min hγ.le (abs_nonneg _)), mul_comm γ]
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (abs_nonneg _)
  have hη : Integrable η μ := integrable_finsetSum J hηj
  -- `f ∘ S` and `f ∘ S'` are bounded by `r + γ`
  have hbdd (j : ι) (hj : j ∈ J) (T : Ω → ℝ) (hT : Measurable T) :
      Integrable (fun ω ↦ ξ j ω * f (T ω)) μ := by
    refine ((hL1 j hj).abs.mul_const (r + γ)).mono'
      ((hmeas j).mul (hfm.comp hT)).aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_ramp_le z _ _ hK) (abs_nonneg _)
  have hSum' (j : ι) : Measurable fun ω ↦ ∑ k ∈ J.erase j, ξ k ω :=
    Finset.measurable_sum _ fun k _ ↦ hmeas k
  -- upper bound `E[S f(S)] ≤ r + γ`
  have hES : ∫ ω, |S ω| ∂μ ≤ 1 := by
    have h := integral_abs_le_of_memLp_two hSL2 one_pos
    have h2 : ∫ ω, S ω ^ 2 ∂μ = ∑ j ∈ J, ∫ ω, ξ j ω ^ 2 ∂μ := integral_sum_sq hmeas hind J hL2 hc
    rw [h2] at h
    linarith
  have hint_Sf : Integrable (fun ω ↦ S ω * f (S ω)) μ := by
    refine ((hSL2.integrable one_le_two).abs.mul_const (r + γ)).mono'
      (hSm.mul (hfm.comp hSm)).aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_ramp_le z _ _ hK) (abs_nonneg _)
  have hup : ∫ ω, S ω * f (S ω) ∂μ ≤ r + γ := by
    calc ∫ ω, S ω * f (S ω) ∂μ ≤ ∫ ω, |S ω| * (r + γ) ∂μ :=
          integral_mono hint_Sf ((hSL2.integrable one_le_two).abs.mul_const _) fun ω ↦
            (le_abs_self _).trans (by
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (abs_ramp_le z _ _ hK) (abs_nonneg _))
      _ = (∫ ω, |S ω| ∂μ) * (r + γ) := integral_mul_const _ _
      _ ≤ 1 * (r + γ) := by gcongr
      _ = r + γ := one_mul _
  -- decomposition `E[S f(S)] = ∑ E[ξ_j (f(S) - f(S'_j))]`
  have hdec : ∫ ω, S ω * f (S ω) ∂μ =
      ∑ j ∈ J, ∫ ω, ξ j ω * (f (S ω) - f (∑ k ∈ J.erase j, ξ k ω)) ∂μ := by
    have : (fun ω ↦ S ω * f (S ω)) = fun ω ↦ ∑ j ∈ J, ξ j ω * f (S ω) := by
      ext ω; simp only [S, sum_mul]
    rw [this, integral_finsetSum _ fun j hj ↦ hbdd j hj S hSm]
    refine sum_congr rfl fun j hj ↦ ?_
    have h0 : ∫ ω, ξ j ω * f (∑ k ∈ J.erase j, ξ k ω) ∂μ = 0 := by
      have := integral_comp_mul_comp_sum_erase hmeas hind J j measurable_id hfm
      simp only [id] at this
      rw [this, hc j hj, zero_mul]
    simp_rw [mul_sub]
    rw [integral_sub (hbdd j hj S hSm) (hbdd j hj _ (hSum' j)), h0, sub_zero]
  -- pointwise lower bound on `A`
  have hpt (ω : Ω) : A.indicator η ω ≤
      ∑ j ∈ J, ξ j ω * (f (S ω) - f (∑ k ∈ J.erase j, ξ k ω)) := by
    have herase (j : ι) (hj : j ∈ J) : ∑ k ∈ J.erase j, ξ k ω = S ω - ξ j ω := by
      rw [eq_sub_iff_add_eq, add_comm]
      exact add_sum_erase J (fun k ↦ ξ k ω) hj
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      refine sum_le_sum fun j hj ↦ ?_
      rw [herase j hj]
      exact abs_mul_min_le_ramp z r γ (S ω) (ξ j ω) hγ.le hω
    · rw [Set.indicator_of_notMem hω]
      refine sum_nonneg fun j hj ↦ ?_
      rw [herase j hj]
      exact ramp_mul_nonneg z _ (S ω) (ξ j ω)
  have hint_j (j : ι) (hj : j ∈ J) :
      Integrable (fun ω ↦ ξ j ω * (f (S ω) - f (∑ k ∈ J.erase j, ξ k ω))) μ := by
    simp_rw [mul_sub]
    exact (hbdd j hj S hSm).sub (hbdd j hj _ (hSum' j))
  have hlow : ∫ ω, A.indicator η ω ∂μ ≤ r + γ := by
    refine le_trans ?_ hup
    rw [hdec, ← integral_finsetSum _ hint_j]
    exact integral_mono (hη.indicator hAm) (integrable_finsetSum J hint_j) hpt
  -- the mean of `η`
  have hmean : 1 / 4 ≤ ∫ ω, η ω ∂μ := by
    have hint3 (j : ι) (hj : j ∈ J) := integrable_abs_pow_three (hL3 j hj)
    have hint2 (j : ι) (hj : j ∈ J) := integrable_sq_of_memLp_three (hL3 j hj)
    have h1 : ∑ j ∈ J, (∫ ω, ξ j ω ^ 2 ∂μ - (∫ ω, |ξ j ω| ^ 3 ∂μ) / (4 * γ)) ≤
        ∫ ω, η ω ∂μ := by
      rw [integral_finsetSum _ hηj]
      refine sum_le_sum fun j hj ↦ ?_
      rw [← integral_div, ← integral_sub (hint2 j hj) ((hint3 j hj).div_const _)]
      exact integral_mono ((hint2 j hj).sub ((hint3 j hj).div_const _)) (hηj j hj)
        fun ω ↦ abs_mul_min_lower γ (ξ j ω) hγ
    rw [sum_sub_distrib, ← sum_div] at h1
    have h2 : (∑ j ∈ J, ∫ ω, |ξ j ω| ^ 3 ∂μ) / (4 * γ) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  -- deviation of `η` from its mean
  have hdev : ∫ ω, |η ω - ∫ ω', η ω' ∂μ| ∂μ ≤ γ :=
    integral_abs_sub_integral_le hmeas hind J hL3 hγ hγJ
  set c := ∫ ω, η ω ∂μ
  have hpt2 (ω : Ω) : A.indicator 1 ω * c - |η ω - c| ≤ A.indicator η ω := by
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, Pi.one_apply, one_mul]
      linarith [neg_abs_le (η ω - c)]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul, zero_sub,
        neg_nonpos]
      exact abs_nonneg _
  have hint1 : Integrable (fun ω ↦ A.indicator (1 : Ω → ℝ) ω * c) μ :=
    ((integrable_const (1 : ℝ)).indicator hAm).mul_const c
  have hint4 : Integrable (fun ω ↦ |η ω - c|) μ := (hη.sub (integrable_const c)).abs
  have hfin : ∫ ω, (A.indicator 1 ω * c - |η ω - c|) ∂μ ≤ ∫ ω, A.indicator η ω ∂μ :=
    integral_mono (hint1.sub hint4) (hη.indicator hAm) hpt2
  rw [integral_sub hint1 hint4, integral_mul_const, integral_indicator_one hAm] at hfin
  have hA0 : 0 ≤ μ.real A := measureReal_nonneg
  nlinarith

end Concentration

section Stein

variable [IsProbabilityMeasure μ]

private lemma integrable_steinDeriv_comp (z : ℝ) {T : Ω → ℝ} (hT : Measurable T) :
    Integrable (fun ω ↦ steinDeriv z (T ω)) μ :=
  Integrable.of_bound ((measurable_steinDeriv z).comp hT).aestronglyMeasurable 3
    (ae_of_all _ fun ω ↦ abs_steinDeriv_le z (T ω))

omit [IsProbabilityMeasure μ] in
private lemma integrable_mul_steinSolution_comp (z : ℝ) {X T : Ω → ℝ} (hX : Integrable X μ)
    (hT : Measurable T) : Integrable (fun ω ↦ X ω * steinSolution z (T ω)) μ := by
  refine (hX.abs.mul_const 6).mono'
    (hX.aestronglyMeasurable.mul ((measurable_steinSolution z).comp hT).aestronglyMeasurable)
    (ae_of_all _ fun ω ↦ ?_)
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_steinSolution_le z _) (abs_nonneg _)

private lemma integrable_ite_abs_sub_le {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (z : ℝ) : Integrable (fun ω ↦ if |Y ω - z| ≤ |X ω| then (1 : ℝ) else 0) μ := by
  refine Integrable.of_bound (Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop))
    measurable_const measurable_const).aestronglyMeasurable 1 (ae_of_all _ fun ω ↦ ?_)
  split_ifs <;> simp

omit [IsProbabilityMeasure μ] in
private lemma integrable_sq_mul_steinDeriv_comp (z : ℝ) {X T : Ω → ℝ}
    (hX2 : Integrable (fun ω ↦ X ω ^ 2) μ) (hT : Measurable T) :
    Integrable (fun ω ↦ X ω ^ 2 * steinDeriv z (T ω)) μ :=
  (hX2.mul_const 3).mono' (hX2.aestronglyMeasurable.mul
    ((measurable_steinDeriv z).comp hT).aestronglyMeasurable) (ae_of_all _ fun ω ↦ by
      simp only [Real.norm_eq_abs, abs_mul, abs_pow, sq_abs]
      exact mul_le_mul_of_nonneg_left (abs_steinDeriv_le z _) (sq_nonneg _))

/-- One step of Stein's method: for independent `X` and `Y` with `E|Y| ≤ 1` and a concentration
bound for `Y`, the increments of `steinDeriv z` and the Taylor remainder of `steinSolution z`
are controlled by the moments of `X`. -/
private lemma stein_step {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y μ) (hX3 : MemLp X 3 μ) (hYi : Integrable Y μ)
    (hEY : ∫ ω, |Y ω| ∂μ ≤ 1) {z γ : ℝ}
    (hconc : ∀ r, 0 ≤ r → μ.real {ω | |Y ω - z| ≤ r} ≤ 4 * r + 8 * γ) :
    |∫ ω, steinDeriv z (Y ω + X ω) ∂μ - ∫ ω, steinDeriv z (Y ω) ∂μ| ≤
        12 * ∫ ω, |X ω| ∂μ + 8 * γ ∧
      |∫ ω, (X ω * (steinSolution z (Y ω + X ω) - steinSolution z (Y ω)) -
          X ω ^ 2 * steinDeriv z (Y ω)) ∂μ| ≤
        12 * ∫ ω, |X ω| ^ 3 ∂μ + 8 * γ * ∫ ω, X ω ^ 2 ∂μ := by
  have hX1 : Integrable X μ := hX3.integrable (by norm_num)
  have hX2 := integrable_sq_of_memLp_three hX3
  have hX3' := integrable_abs_pow_three hX3
  have hAXY : IndepFun (fun ω ↦ |Y ω|) (fun ω ↦ |X ω|) μ :=
    hXY.symm.comp (φ := fun y : ℝ ↦ |y|) (ψ := fun x : ℝ ↦ |x|) (by fun_prop) (by fun_prop)
  have hAXY3 : IndepFun (fun ω ↦ |Y ω|) (fun ω ↦ |X ω| ^ 3) μ :=
    hXY.symm.comp (φ := fun y : ℝ ↦ |y|) (ψ := fun x : ℝ ↦ |x| ^ 3) (by fun_prop) (by fun_prop)
  have hYX : Integrable (fun ω ↦ |Y ω| * |X ω|) μ := hAXY.integrable_mul hYi.abs hX1.abs
  have hYX3 : Integrable (fun ω ↦ |Y ω| * |X ω| ^ 3) μ := hAXY3.integrable_mul hYi.abs hX3'
  have hEYX : ∫ ω, |Y ω| * |X ω| ∂μ ≤ ∫ ω, |X ω| ∂μ := by
    rw [hAXY.integral_fun_mul_eq_mul_integral (by fun_prop) (by fun_prop)]
    have : 0 ≤ ∫ ω, |X ω| ∂μ := integral_nonneg fun _ ↦ abs_nonneg _
    nlinarith
  have hEYX3 : ∫ ω, |Y ω| * |X ω| ^ 3 ∂μ ≤ ∫ ω, |X ω| ^ 3 ∂μ := by
    rw [hAXY3.integral_fun_mul_eq_mul_integral (by fun_prop) (by fun_prop)]
    have : 0 ≤ ∫ ω, |X ω| ^ 3 ∂μ := integral_nonneg fun _ ↦ by positivity
    nlinarith
  have hI := integrable_ite_abs_sub_le (μ := μ) hX hY z
  have hYpX : Measurable fun ω ↦ Y ω + X ω := hY.add hX
  have hXI : Integrable (fun ω ↦ X ω ^ 2 * (if |Y ω - z| ≤ |X ω| then (1 : ℝ) else 0)) μ :=
    hX2.mono' (hX2.aestronglyMeasurable.mul hI.aestronglyMeasurable)
      (ae_of_all _ fun ω ↦ by
        simp only [Real.norm_eq_abs, abs_mul, abs_pow, sq_abs]
        split_ifs <;> simp [sq_nonneg])
  -- the two concentration terms
  have hC1 : ∫ ω, (if |Y ω - z| ≤ |X ω| then (1 : ℝ) else 0) ∂μ ≤
      4 * ∫ ω, |X ω| ∂μ + 8 * γ := by
    have := integral_mul_ite_abs_sub_le_le hX hY hXY (g := fun _ ↦ 1) measurable_const
      (fun _ ↦ zero_le_one) (integrable_const 1) (by simpa using hX1.abs) hconc
    simp only [one_mul] at this
    rwa [integral_add (hX1.abs.const_mul 4) (integrable_const _), integral_const_mul,
      integral_const, probReal_univ, one_smul] at this
  have hC2 : ∫ ω, X ω ^ 2 * (if |Y ω - z| ≤ |X ω| then (1 : ℝ) else 0) ∂μ ≤
      4 * ∫ ω, |X ω| ^ 3 ∂μ + 8 * γ * ∫ ω, X ω ^ 2 ∂μ := by
    have hsq (ω : Ω) : X ω ^ 2 * |X ω| = |X ω| ^ 3 := by rw [← sq_abs]; ring
    have := integral_mul_ite_abs_sub_le_le hX hY hXY (g := fun x ↦ x ^ 2) (by fun_prop)
      (fun x ↦ sq_nonneg x) hX2 (by simpa only [hsq] using hX3') hconc
    have e : (fun ω ↦ X ω ^ 2 * (4 * |X ω| + 8 * γ)) =
        fun ω ↦ 4 * |X ω| ^ 3 + 8 * γ * X ω ^ 2 := by
      ext ω; rw [← hsq]; ring
    rwa [e, integral_add (hX3'.const_mul 4) (hX2.const_mul _), integral_const_mul,
      integral_const_mul] at this
  constructor
  · rw [← integral_sub (integrable_steinDeriv_comp z hYpX)
      (integrable_steinDeriv_comp z hY)]
    have hB : Integrable (fun ω ↦ 2 * (|Y ω| * |X ω|) + 6 * |X ω| +
        (if |Y ω - z| ≤ |X ω| then (1 : ℝ) else 0)) μ :=
      ((hYX.const_mul 2).add (hX1.abs.const_mul 6)).add hI
    calc _ ≤ ∫ ω, |steinDeriv z (Y ω + X ω) - steinDeriv z (Y ω)| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, (2 * (|Y ω| * |X ω|) + 6 * |X ω| +
            (if |Y ω - z| ≤ |X ω| then (1 : ℝ) else 0)) ∂μ := by
          refine integral_mono ((integrable_steinDeriv_comp z hYpX).sub
            (integrable_steinDeriv_comp z hY)).abs hB fun ω ↦ ?_
          refine (abs_steinDeriv_add_sub_le z (Y ω) (X ω)).trans (le_of_eq ?_)
          ring
      _ = 2 * ∫ ω, |Y ω| * |X ω| ∂μ + 6 * ∫ ω, |X ω| ∂μ +
            ∫ ω, (if |Y ω - z| ≤ |X ω| then (1 : ℝ) else 0) ∂μ := by
          have h26 : Integrable (fun ω ↦ 2 * (|Y ω| * |X ω|) + 6 * |X ω|) μ :=
            (hYX.const_mul 2).add (hX1.abs.const_mul 6)
          rw [integral_add h26 hI,
            integral_add (hYX.const_mul 2) (hX1.abs.const_mul 6), integral_const_mul,
            integral_const_mul]
      _ ≤ _ := by linarith
  · have hR : Integrable (fun ω ↦ X ω * (steinSolution z (Y ω + X ω) - steinSolution z (Y ω)) -
        X ω ^ 2 * steinDeriv z (Y ω)) μ := by
      simp_rw [mul_sub]
      exact ((integrable_mul_steinSolution_comp z hX1 hYpX).sub
        (integrable_mul_steinSolution_comp z hX1 hY)).sub
        (integrable_sq_mul_steinDeriv_comp z hX2 hY)
    have hB : Integrable (fun ω ↦ 2 * (|Y ω| * |X ω| ^ 3) + 6 * |X ω| ^ 3 +
        X ω ^ 2 * (if |Y ω - z| ≤ |X ω| then (1 : ℝ) else 0)) μ :=
      ((hYX3.const_mul 2).add (hX3'.const_mul 6)).add hXI
    calc _ ≤ ∫ ω, |X ω * (steinSolution z (Y ω + X ω) - steinSolution z (Y ω)) -
          X ω ^ 2 * steinDeriv z (Y ω)| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (2 * (|Y ω| * |X ω| ^ 3) + 6 * |X ω| ^ 3 +
            X ω ^ 2 * (if |Y ω - z| ≤ |X ω| then (1 : ℝ) else 0)) ∂μ := by
          refine integral_mono hR.abs hB fun ω ↦ ?_
          have h := abs_steinSolution_add_sub_sub_le z (Y ω) (X ω)
          have e : X ω * (steinSolution z (Y ω + X ω) - steinSolution z (Y ω)) -
              X ω ^ 2 * steinDeriv z (Y ω) = X ω * (steinSolution z (Y ω + X ω) -
                steinSolution z (Y ω) - X ω * steinDeriv z (Y ω)) := by ring
          rw [e, abs_mul]
          refine (mul_le_mul_of_nonneg_left h (abs_nonneg _)).trans (le_of_eq ?_)
          rw [← sq_abs (X ω)]
          ring
      _ = 2 * ∫ ω, |Y ω| * |X ω| ^ 3 ∂μ + 6 * ∫ ω, |X ω| ^ 3 ∂μ +
            ∫ ω, X ω ^ 2 * (if |Y ω - z| ≤ |X ω| then (1 : ℝ) else 0) ∂μ := by
          have h26 : Integrable (fun ω ↦ 2 * (|Y ω| * |X ω| ^ 3) + 6 * |X ω| ^ 3) μ :=
            (hYX3.const_mul 2).add (hX3'.const_mul 6)
          rw [integral_add h26 hXI,
            integral_add (hYX3.const_mul 2) (hX3'.const_mul 6), integral_const_mul,
            integral_const_mul]
      _ ≤ _ := by linarith

end Stein

section BerryEsseen

variable [IsProbabilityMeasure μ] {ι : Type*} [DecidableEq ι] {ξ : ι → Ω → ℝ}

omit [DecidableEq ι] in
/-- In the nontrivial regime `40 γ < 1` the third-moment sum `γ` is positive and every second
moment is below `1 / 2`. -/
private lemma regime_facts (s : Finset ι) (hL3 : ∀ i ∈ s, MemLp (ξ i) 3 μ)
    (hv : ∑ i ∈ s, ∫ ω, ξ i ω ^ 2 ∂μ = 1) {γ : ℝ} (hρ0 : ∀ i, 0 ≤ ∫ ω, |ξ i ω| ^ 3 ∂μ)
    (hρle : ∀ i ∈ s, ∫ ω, |ξ i ω| ^ 3 ∂μ ≤ γ) (htriv : 40 * γ < 1) :
    0 < γ ∧ ∀ i ∈ s, ∫ ω, ξ i ω ^ 2 ∂μ < 1 / 2 := by
  constructor
  · by_contra hcon
    push Not at hcon
    have h0 (i : ι) (hi : i ∈ s) : ∫ ω, ξ i ω ^ 2 ∂μ ≤ 0 := by
      have h := integral_sq_pow_three_le (hL3 i hi)
      have : ∫ ω, |ξ i ω| ^ 3 ∂μ = 0 := le_antisymm ((hρle i hi).trans hcon) (hρ0 i)
      rw [this] at h
      by_contra h'
      push Not at h'
      have := pow_pos h' 3
      norm_num at h
      linarith
    have := sum_nonpos h0
    linarith
  · intro i hi
    have h := integral_sq_pow_three_le (hL3 i hi)
    by_contra hcon
    push Not at hcon
    have h1 : (1 / 2 : ℝ) ^ 3 ≤ (∫ ω, ξ i ω ^ 2 ∂μ) ^ 3 := pow_le_pow_left₀ (by norm_num) hcon 3
    have h2 : (∫ ω, |ξ i ω| ^ 3 ∂μ) ^ 2 ≤ γ ^ 2 := pow_le_pow_left₀ (hρ0 i) (hρle i hi) 2
    have hγ0 : 0 ≤ γ := (hρ0 i).trans (hρle i hi)
    nlinarith

/-- **Berry–Esseen bound** for independent, not necessarily identically distributed summands:
if the `ξ i`, `i ∈ s`, are independent and centered with finite third moments and
`∑ i ∈ s, E (ξ i)² = 1`, then the distribution function of `∑ i ∈ s, ξ i` differs from the
standard Gaussian distribution function by at most `40 ∑ i ∈ s, E|ξ i|³` at every point. -/
theorem abs_measureReal_sum_le_sub_cdf_le (hmeas : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (s : Finset ι) (hL3 : ∀ i ∈ s, MemLp (ξ i) 3 μ)
    (hc : ∀ i ∈ s, ∫ ω, ξ i ω ∂μ = 0) (hv : ∑ i ∈ s, ∫ ω, ξ i ω ^ 2 ∂μ = 1) (z : ℝ) :
    |μ.real {ω | ∑ i ∈ s, ξ i ω ≤ z} - cdf (gaussianReal 0 1) z| ≤
      40 * ∑ i ∈ s, ∫ ω, |ξ i ω| ^ 3 ∂μ := by
  set γ := ∑ i ∈ s, ∫ ω, |ξ i ω| ^ 3 ∂μ with hγ_def
  have hρ0 (i : ι) : 0 ≤ ∫ ω, |ξ i ω| ^ 3 ∂μ := integral_nonneg fun _ ↦ by positivity
  have hρle (i : ι) (hi : i ∈ s) : ∫ ω, |ξ i ω| ^ 3 ∂μ ≤ γ :=
    single_le_sum (fun j _ ↦ hρ0 j) hi
  have ha0 (i : ι) : 0 ≤ ∫ ω, ξ i ω ^ 2 ∂μ := integral_nonneg fun _ ↦ sq_nonneg _
  have hP0 : 0 ≤ μ.real {ω | ∑ i ∈ s, ξ i ω ≤ z} := measureReal_nonneg
  have hP1 : μ.real {ω | ∑ i ∈ s, ξ i ω ≤ z} ≤ 1 := measureReal_le_one
  have hΦ0 := cdf_nonneg (gaussianReal 0 1) z
  have hΦ1 := cdf_le_one (gaussianReal 0 1) z
  by_cases htriv : 1 ≤ 40 * γ
  · rw [abs_le]
    constructor <;> linarith
  push Not at htriv
  obtain ⟨hγpos, hsmall⟩ := regime_facts s hL3 hv hρ0 hρle htriv
  -- notation
  set W : Ω → ℝ := fun ω ↦ ∑ i ∈ s, ξ i ω with hW_def
  set V : ι → Ω → ℝ := fun i ω ↦ ∑ j ∈ s.erase i, ξ j ω with hV_def
  have hWm : Measurable W := Finset.measurable_sum _ fun j _ ↦ hmeas j
  have hVm (i : ι) : Measurable (V i) := Finset.measurable_sum _ fun j _ ↦ hmeas j
  have hWV (i : ι) (hi : i ∈ s) (ω : Ω) : W ω = V i ω + ξ i ω :=
    (sum_erase_add s (fun j ↦ ξ j ω) hi).symm
  have hL1 (i : ι) (hi : i ∈ s) : Integrable (ξ i) μ := (hL3 i hi).integrable (by norm_num)
  have hL2 (i : ι) (hi : i ∈ s) : MemLp (ξ i) 2 μ := (hL3 i hi).mono_exponent (by norm_num)
  have hWL1 : Integrable W μ := integrable_finsetSum s hL1
  -- one Stein step for each summand
  have hstep (i : ι) (hi : i ∈ s) := by
    have hL3' : ∀ j ∈ s.erase i, MemLp (ξ j) 3 μ := fun j hj ↦ hL3 j (mem_of_mem_erase hj)
    have hc' : ∀ j ∈ s.erase i, ∫ ω, ξ j ω ∂μ = 0 := fun j hj ↦ hc j (mem_of_mem_erase hj)
    have hB : ∑ j ∈ s.erase i, ∫ ω, ξ j ω ^ 2 ∂μ = 1 - ∫ ω, ξ i ω ^ 2 ∂μ := by
      rw [sum_erase_eq_sub hi, hv]
    have hγJ : ∑ j ∈ s.erase i, ∫ ω, |ξ j ω| ^ 3 ∂μ ≤ γ :=
      sum_le_sum_of_subset_of_nonneg (erase_subset i s) fun j _ _ ↦ hρ0 j
    have hVL2 : MemLp (V i) 2 μ :=
      memLp_finsetSum _ fun j hj ↦ hL2 j (mem_of_mem_erase hj)
    have hEV : ∫ ω, |V i ω| ∂μ ≤ 1 := by
      have h := integral_abs_le_of_memLp_two hVL2 one_pos
      have h2 : ∫ ω, V i ω ^ 2 ∂μ = ∑ j ∈ s.erase i, ∫ ω, ξ j ω ^ 2 ∂μ :=
        integral_sum_sq hmeas hind (s.erase i)
          (fun j hj ↦ hL2 j (mem_of_mem_erase hj)) hc'
      rw [h2, hB] at h
      linarith [ha0 i]
    exact stein_step (z := z) (γ := γ) (hmeas i) (hVm i) (indepFun_sum_erase hmeas hind s i)
      (hL3 i hi) (hVL2.integrable one_le_two) hEV fun r hr ↦
        measureReal_abs_sum_sub_le hmeas hind (s.erase i) hL3' hc'
          (by rw [hB]; linarith [hsmall i hi]) (by rw [hB]; linarith [ha0 i]) hγpos hγJ z hr
  -- the Stein identity
  have hI : Integrable (fun ω ↦ if W ω ≤ z then (1 : ℝ) else 0) μ :=
    Integrable.of_bound (Measurable.ite (measurableSet_le hWm measurable_const)
      measurable_const measurable_const).aestronglyMeasurable 1
      (ae_of_all _ fun ω ↦ by split_ifs <;> simp)
  have hWf : Integrable (fun ω ↦ W ω * steinSolution z (W ω)) μ :=
    integrable_mul_steinSolution_comp z hWL1 hWm
  have h1 : ∫ ω, steinDeriv z (W ω) ∂μ = ∫ ω, W ω * steinSolution z (W ω) ∂μ +
      μ.real {ω | W ω ≤ z} - cdf (gaussianReal 0 1) z := by
    simp only [steinDeriv_def]
    have hWfI : Integrable (fun ω ↦ W ω * steinSolution z (W ω) +
        if W ω ≤ z then (1 : ℝ) else 0) μ := hWf.add hI
    rw [integral_sub hWfI (integrable_const _), integral_add hWf hI, integral_const,
      probReal_univ, one_smul]
    have : (fun ω ↦ if W ω ≤ z then (1 : ℝ) else 0) = {ω | W ω ≤ z}.indicator 1 := by
      ext ω; simp [Set.indicator_apply]
    rw [this, integral_indicator_one (measurableSet_le hWm measurable_const)]
  have h2 : ∫ ω, W ω * steinSolution z (W ω) ∂μ =
      ∑ i ∈ s, ∫ ω, ξ i ω * steinSolution z (W ω) ∂μ := by
    rw [← integral_finsetSum _ fun i hi ↦ integrable_mul_steinSolution_comp z (hL1 i hi) hWm]
    congr 1
    ext ω
    simp only [W, sum_mul]
  set R : ι → Ω → ℝ := fun i ω ↦ ξ i ω * (steinSolution z (V i ω + ξ i ω) -
    steinSolution z (V i ω)) - ξ i ω ^ 2 * steinDeriv z (V i ω) with hR_def
  have h3 (i : ι) (hi : i ∈ s) : ∫ ω, ξ i ω * steinSolution z (W ω) ∂μ =
      ∫ ω, R i ω ∂μ + (∫ ω, ξ i ω ^ 2 ∂μ) * ∫ ω, steinDeriv z (V i ω) ∂μ := by
    have hA := integrable_mul_steinSolution_comp z (hL1 i hi) ((hVm i).add (hmeas i))
    have hB := integrable_mul_steinSolution_comp z (hL1 i hi) (hVm i)
    have hC := integrable_sq_mul_steinDeriv_comp z (integrable_sq_of_memLp_three (hL3 i hi))
      (hVm i)
    have hRi : Integrable (R i) μ := by
      simp only [R, mul_sub]
      exact (hA.sub hB).sub hC
    have e : (fun ω ↦ ξ i ω * steinSolution z (W ω)) =
        fun ω ↦ (R i ω + ξ i ω ^ 2 * steinDeriv z (V i ω)) +
          ξ i ω * steinSolution z (V i ω) := by
      ext ω
      rw [hWV i hi ω]
      simp only [R]
      ring
    have h0 : ∫ ω, ξ i ω * steinSolution z (V i ω) ∂μ = 0 := by
      have := integral_comp_mul_comp_sum_erase hmeas hind s i measurable_id
        (measurable_steinSolution z)
      simp only [id] at this
      rw [this, hc i hi, zero_mul]
    have hsq : ∫ ω, ξ i ω ^ 2 * steinDeriv z (V i ω) ∂μ =
        (∫ ω, ξ i ω ^ 2 ∂μ) * ∫ ω, steinDeriv z (V i ω) ∂μ :=
      integral_comp_mul_comp_sum_erase hmeas hind s i (g := fun x ↦ x ^ 2) (by fun_prop)
        (measurable_steinDeriv z)
    have hRC : Integrable (fun ω ↦ R i ω + ξ i ω ^ 2 * steinDeriv z (V i ω)) μ := hRi.add hC
    rw [e, integral_add hRC hB, integral_add hRi hC, h0, add_zero, hsq]
  have key : μ.real {ω | W ω ≤ z} - cdf (gaussianReal 0 1) z =
      ∑ i ∈ s, ((∫ ω, ξ i ω ^ 2 ∂μ) * (∫ ω, steinDeriv z (W ω) ∂μ -
        ∫ ω, steinDeriv z (V i ω) ∂μ) - ∫ ω, R i ω ∂μ) := by
    have hE : ∫ ω, steinDeriv z (W ω) ∂μ =
        ∑ i ∈ s, (∫ ω, ξ i ω ^ 2 ∂μ) * ∫ ω, steinDeriv z (W ω) ∂μ := by
      rw [← sum_mul, hv, one_mul]
    calc _ = ∫ ω, steinDeriv z (W ω) ∂μ - ∫ ω, W ω * steinSolution z (W ω) ∂μ := by
          rw [h1]; ring
      _ = ∫ ω, steinDeriv z (W ω) ∂μ - ∑ i ∈ s, (∫ ω, R i ω ∂μ +
          (∫ ω, ξ i ω ^ 2 ∂μ) * ∫ ω, steinDeriv z (V i ω) ∂μ) := by
          rw [h2, sum_congr rfl h3]
      _ = _ := by
          nth_rewrite 1 [hE]
          simp only [mul_sub, sum_sub_distrib, sum_add_distrib]
          ring
  -- the bound
  have hterm (i : ι) (hi : i ∈ s) :
      |(∫ ω, ξ i ω ^ 2 ∂μ) * (∫ ω, steinDeriv z (W ω) ∂μ - ∫ ω, steinDeriv z (V i ω) ∂μ) -
        ∫ ω, R i ω ∂μ| ≤ 24 * ∫ ω, |ξ i ω| ^ 3 ∂μ + 16 * γ * ∫ ω, ξ i ω ^ 2 ∂μ := by
    obtain ⟨hs1, hs2⟩ := hstep i hi
    have hWeq : ∫ ω, steinDeriv z (W ω) ∂μ = ∫ ω, steinDeriv z (V i ω + ξ i ω) ∂μ :=
      integral_congr_ae (ae_of_all _ fun ω ↦ by simp only [hWV i hi ω])
    rw [hWeq]
    have hly := integral_abs_mul_integral_sq_le (hL3 i hi)
    calc _ ≤ |(∫ ω, ξ i ω ^ 2 ∂μ) * (∫ ω, steinDeriv z (V i ω + ξ i ω) ∂μ -
            ∫ ω, steinDeriv z (V i ω) ∂μ)| + |∫ ω, R i ω ∂μ| := abs_sub _ _
      _ ≤ (∫ ω, ξ i ω ^ 2 ∂μ) * (12 * ∫ ω, |ξ i ω| ∂μ + 8 * γ) +
            (12 * ∫ ω, |ξ i ω| ^ 3 ∂μ + 8 * γ * ∫ ω, ξ i ω ^ 2 ∂μ) := by
          rw [abs_mul, abs_of_nonneg (ha0 i)]
          exact add_le_add (mul_le_mul_of_nonneg_left hs1 (ha0 i)) hs2
      _ ≤ _ := by nlinarith
  rw [key]
  calc _ ≤ ∑ i ∈ s, |(∫ ω, ξ i ω ^ 2 ∂μ) * (∫ ω, steinDeriv z (W ω) ∂μ -
        ∫ ω, steinDeriv z (V i ω) ∂μ) - ∫ ω, R i ω ∂μ| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, (24 * ∫ ω, |ξ i ω| ^ 3 ∂μ + 16 * γ * ∫ ω, ξ i ω ^ 2 ∂μ) := sum_le_sum hterm
    _ = 40 * γ := by rw [sum_add_distrib, ← mul_sum, ← mul_sum, hv]; ring

/-- **Berry–Esseen bound** for independent identically distributed summands: if `X 0` is
centered with variance `σ² > 0` and finite third absolute moment `ρ`, then for `n > 0` the
distribution function of `(∑ j < n, X j) / (σ √n)` differs from the standard Gaussian
distribution function by at most `40 ρ / (σ³ √n)` at every point. -/
theorem abs_measureReal_sum_div_le_sub_cdf_le (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (hLp : MemLp (X 0) 3 μ) (hc : ∫ ω, X 0 ω ∂μ = 0)
    {σ : ℝ} (hσ : 0 < σ) (hv : variance (X 0) μ = σ ^ 2) {n : ℕ} (hn : 0 < n) (x : ℝ) :
    |μ.real {ω | (∑ j ∈ Finset.range n, X j ω) / (σ * √n) ≤ x} - cdf (gaussianReal 0 1) x| ≤
      40 * (∫ ω, |X 0 ω| ^ 3 ∂μ) / (σ ^ 3 * √n) := by
  set c := σ * √(n : ℝ) with hc_def
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn'
  have hcpos : 0 < c := mul_pos hσ hsn
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn'.le
  set ξ : ℕ → Ω → ℝ := fun j ω ↦ X j ω / c with hξ_def
  have hmeas (j : ℕ) : Measurable (ξ j) := (hm j).div_const c
  have hind : iIndepFun ξ μ := hi.comp (fun _ x ↦ x / c) fun _ ↦ measurable_id.div_const c
  have hX3 (j : ℕ) : MemLp (X j) 3 μ := (hid j).memLp_iff.2 hLp
  have hL3 (j : ℕ) : MemLp (ξ j) 3 μ := by
    simpa only [hξ_def, div_eq_mul_inv] using (hX3 j).mul_const c⁻¹
  have hξc (j : ℕ) : ∫ ω, ξ j ω ∂μ = 0 := by
    simp only [hξ_def, integral_div, (hid j).integral_eq, hc, zero_div]
  have hX0sq : ∫ ω, X 0 ω ^ 2 ∂μ = σ ^ 2 := by
    rw [← hv, variance_of_integral_eq_zero (hm 0).aemeasurable hc]
  have hξ2 (j : ℕ) : ∫ ω, ξ j ω ^ 2 ∂μ = 1 / n := by
    have h := ((hid j).comp (measurable_id.pow_const 2)).integral_eq
    simp only [Function.comp_def, id] at h
    simp only [hξ_def, div_pow, integral_div, h, hX0sq, hc_def, mul_pow, hsq]
    field_simp
  have hξ3 (j : ℕ) : ∫ ω, |ξ j ω| ^ 3 ∂μ = (∫ ω, |X 0 ω| ^ 3 ∂μ) / c ^ 3 := by
    have h := ((hid j).comp (continuous_abs.measurable.pow_const 3)).integral_eq
    simp only [Function.comp_def] at h
    simp only [hξ_def, abs_div, abs_of_pos hcpos, div_pow, integral_div, h]
  have hv1 : ∑ j ∈ Finset.range n, ∫ ω, ξ j ω ^ 2 ∂μ = 1 := by
    simp only [hξ2, sum_const, card_range, nsmul_eq_mul]
    field_simp
  have h := abs_measureReal_sum_le_sub_cdf_le hmeas hind (Finset.range n) (fun j _ ↦ hL3 j)
    (fun j _ ↦ hξc j) hv1 x
  have hset : {ω | ∑ j ∈ Finset.range n, ξ j ω ≤ x} =
      {ω | (∑ j ∈ Finset.range n, X j ω) / c ≤ x} := by
    simp only [hξ_def, sum_div]
  rw [hset] at h
  refine h.trans (le_of_eq ?_)
  simp only [hξ3, sum_const, card_range, nsmul_eq_mul, hc_def, mul_pow]
  have : √(n : ℝ) ^ 3 = n * √(n : ℝ) := by rw [pow_succ, hsq]
  rw [this]
  field_simp

end BerryEsseen

end CKMA
