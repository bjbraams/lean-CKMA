/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Kolmogorov's convergence criterion and the three-series theorem (06.23)

For independent real random variables `Xₙ` and a threshold `A > 0`, the series `∑ Xₙ` converges
almost surely, as a limit of partial sums in the given order, exactly when
`∑ P(|Xₙ| > A) < ∞`, the means of the truncations `Xₙ 1{|Xₙ| ≤ A}` form an ordered convergent
series, and the variances of the truncations are summable.

Sufficiency uses the first Borel–Cantelli lemma and Kolmogorov's convergence criterion, proved
here from the martingale convergence theorem applied to the centred partial sums. Necessity uses
the second Borel–Cantelli lemma and a characteristic-function argument: for `|Y| ≤ A` and
`|t| A ≤ 1`, `‖φ_Y(t)‖² ≤ 1 - t² Var[Y] / 4`, so a.s. convergence of a series of independent
truncations bounds the partial sums of their variances.

## Main definitions

* `CKMA.IsOrderedSummable`: convergence of partial sums in their given order, Mathlib's
  `Summable` along `SummationFilter.conditional ℕ`. It is weaker than unconditional `Summable`
  for real sequences and is the correct mean-series condition in the three-series theorem.
* `CKMA.symmetricTruncation`: symmetric truncation of a real random variable at threshold `A`.
* `CKMA.HasThreeSeries`: the three series conditions of Kolmogorov's criterion.

## Main results

* `CKMA.ae_tendsto_sum_sub_integral_of_summable_variance`: Kolmogorov's convergence criterion.
* `CKMA.charFun_map_re`, `CKMA.charFun_map_im`: real and imaginary parts of the characteristic
  function of a real random variable.
* `CKMA.norm_charFun_map_sq_le_one_sub_variance`: the variance bound for bounded variables.
* `CKMA.summable_variance_of_ae_tendsto_sum`: a.s. convergence of a series of uniformly bounded
  independent variables forces summable variances.
* `CKMA.ae_summable_conditional_iff_threeSeries`: Kolmogorov's three-series theorem.
* `CKMA.kolmogorov_threeSeries`: the same theorem stated with `CKMA.IsOrderedSummable` (ordered
  convergence of partial sums) and `CKMA.HasThreeSeries` (**06.23**).

## References

* P. Billingsley, *Probability and Measure*, 3rd ed., Wiley, 1995, Section 22.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Kolmogorov's convergence criterion.** For independent square-integrable random variables
with summable variances, the series of centred terms converges almost surely, in the given
order. -/
theorem ae_tendsto_sum_sub_integral_of_summable_variance [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} (hm : ∀ n, Measurable (Y n)) (hi : iIndepFun Y μ)
    (hL : ∀ n, MemLp (Y n) 2 μ) (hv : Summable fun n ↦ Var[Y n; μ]) :
    ∀ᵐ ω ∂μ, ∃ l, Tendsto (fun n ↦ ∑ k ∈ range n, (Y k ω - μ[Y k])) atTop (𝓝 l) := by
  set Z : ℕ → Ω → ℝ := fun k ω ↦ Y k ω - μ[Y k] with hZ
  have hZm k : Measurable (Z k) := (hm k).sub_const _
  have hZi : iIndepFun Z μ := by
    have := hi.comp (fun k (x : ℝ) ↦ x - μ[Y k]) fun k ↦ measurable_id.sub_const _
    exact this
  have hZL k : MemLp (Z k) 2 μ := (hL k).sub (memLp_const _)
  have hZ0 k : μ[Z k] = 0 := by
    simp [hZ, integral_sub ((hL k).integrable one_le_two) (integrable_const _)]
  set ℱ := Filtration.natural Z fun k ↦ (hZm k).stronglyMeasurable
  set f : ℕ → Ω → ℝ := fun n ↦ ∑ k ∈ range (n + 1), Z k with hf
  have hadp : StronglyAdapted ℱ f := by
    intro n
    refine Finset.stronglyMeasurable_sum _ fun k hk ↦ ?_
    exact (Filtration.stronglyAdapted_natural (u := Z) _ k).mono
      (ℱ.mono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)))
  have hint n : Integrable (f n) μ :=
    integrable_finsetSum' _ fun k _ ↦ (hZL k).integrable one_le_two
  have hmart : Martingale f ℱ μ := by
    refine martingale_of_condExp_sub_eq_zero_nat hadp hint fun i ↦ ?_
    have hsub : f (i + 1) - f i = Z (i + 1) := by
      simp only [hf, Finset.sum_range_succ _ (i + 1)]
      abel
    rw [hsub]
    have hind : Indep (MeasurableSpace.comap (Z (i + 1)) inferInstance) (ℱ i) μ := by
      have h := indep_iSup_of_disjoint (fun k ↦ (hZm k).comap_le)
        ((iIndepFun_iff_iIndep _ _ _).1 hZi) (S := {i + 1}) (T := Set.Iic i)
        (Set.disjoint_singleton_left.2 (by simp))
      simp only [Set.mem_singleton_iff, iSup_iSup_eq_left, Set.mem_Iic] at h
      exact h
    refine (condExp_indep_eq (hZm (i + 1)).comap_le (ℱ.le i)
      (comap_measurable (Z (i + 1))).stronglyMeasurable hind).trans ?_
    simp only [hZ0]
    rfl
  have hsq n : ∫ ω, f n ω ^ 2 ∂μ ≤ ∑' k, Var[Y k; μ] := by
    have hvar : Var[f n; μ] = ∑ k ∈ range (n + 1), Var[Y k; μ] := by
      rw [hf, IndepFun.variance_sum (fun k _ ↦ hZL k)
        fun j _ k _ hjk ↦ hZi.indepFun hjk]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      exact variance_sub_const (hm k).aestronglyMeasurable _
    have h0 : μ[f n] = 0 := by
      simp only [hf, Finset.sum_apply]
      rw [integral_finsetSum _ fun k _ ↦ (hZL k).integrable one_le_two]
      simp [hZ0]
    rw [← variance_of_integral_eq_zero (hint n).aemeasurable h0, hvar]
    exact hv.sum_le_tsum _ fun k _ ↦ variance_nonneg _ _
  set V := ∑' k, Var[Y k; μ]
  have hbdd n : eLpNorm (f n) 1 μ ≤ Real.toNNReal ((1 + V) / 2) := by
    have hsqi : Integrable (fun ω ↦ (1 + f n ω ^ 2) / 2) μ := by
      have := (memLp_finsetSum' _ fun k _ ↦ hZL k : MemLp (f n) 2 μ).integrable_sq
      exact ((integrable_const 1).add this).div_const 2
    refine (eLpNorm_mono_real (hint n).aestronglyMeasurable (g := fun ω ↦ (1 + f n ω ^ 2) / 2)
      fun ω ↦ ?_).trans ?_
    · rw [Real.norm_eq_abs]
      nlinarith [sq_nonneg (|f n ω| - 1), sq_abs (f n ω)]
    · rw [eLpNorm_one_eq_lintegral_eNorm, ← ofReal_integral_norm_eq_lintegral_eNorm hsqi]
      refine (ENNReal.ofReal_le_ofReal ?_ : _ ≤ ENNReal.ofReal ((1 + V) / 2))
      have hnn : ∀ ω, ‖(1 + f n ω ^ 2) / 2‖ = (1 + f n ω ^ 2) / 2 := fun ω ↦
        Real.norm_of_nonneg (by positivity)
      simp_rw [hnn]
      rw [integral_div, integral_add (integrable_const 1)
        (memLp_finsetSum' _ fun k _ ↦ hZL k : MemLp (f n) 2 μ).integrable_sq]
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
      linarith [hsq n]
      exact hsqi.aestronglyMeasurable
  have hsup : ⨆ n, eLpNorm (f n) 1 μ < ⊤ :=
    lt_of_le_of_lt (iSup_le hbdd) ENNReal.coe_lt_top
  filter_upwards [hmart.submartingale.ae_tendsto_limitProcess hsup] with ω hω
  refine ⟨ℱ.limitProcess f μ ω, (tendsto_add_atTop_iff_nat 1).1 ?_⟩
  simpa [hf, hZ, Finset.sum_apply] using hω

private lemma charFun_map_eq_integral [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : AEMeasurable Y μ)
    (t : ℝ) :
    Integrable (fun ω ↦ Complex.exp (↑(t * Y ω) * Complex.I)) μ ∧
      charFun (μ.map Y) t = ∫ ω, Complex.exp (↑(t * Y ω) * Complex.I) ∂μ := by
  refine ⟨(integrable_const (1 : ℝ)).mono' (by fun_prop)
    (ae_of_all _ fun ω ↦ (Complex.norm_exp_ofReal_mul_I _).le), ?_⟩
  rw [charFun_apply_real, integral_map hY (by fun_prop)]
  simp

/-- The real part of the characteristic function of a real random variable is the expectation
of `cos (t Y)`. -/
theorem charFun_map_re [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : AEMeasurable Y μ) (t : ℝ) :
    (charFun (μ.map Y) t).re = ∫ ω, Real.cos (t * Y ω) ∂μ := by
  obtain ⟨hexp, hφ⟩ := charFun_map_eq_integral hY t
  rw [hφ]
  have := integral_re hexp
  simp only [RCLike.re_to_complex, Complex.exp_ofReal_mul_I_re] at this
  exact this.symm

/-- The imaginary part of the characteristic function of a real random variable is the
expectation of `sin (t Y)`. -/
theorem charFun_map_im [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : AEMeasurable Y μ) (t : ℝ) :
    (charFun (μ.map Y) t).im = ∫ ω, Real.sin (t * Y ω) ∂μ := by
  obtain ⟨hexp, hφ⟩ := charFun_map_eq_integral hY t
  rw [hφ]
  have := integral_im hexp
  simp only [RCLike.im_to_complex, Complex.exp_ofReal_mul_I_im] at this
  exact this.symm

/-- For a random variable bounded by `A`, the characteristic function at `t` with `|t| A ≤ 1`
satisfies `‖φ(t)‖² ≤ 1 - t² Var[Y] / 4`. -/
theorem norm_charFun_map_sq_le_one_sub_variance [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : Measurable Y) {A t : ℝ} (hA : ∀ ω, |Y ω| ≤ A) (ht : |t| * A ≤ 1) :
    ‖charFun (μ.map Y) t‖ ^ 2 ≤ 1 - t ^ 2 * Var[Y; μ] / 4 := by
  have hint : ∀ (g : Ω → ℝ) (C : ℝ), Measurable g → (∀ ω, |g ω| ≤ C) → Integrable g μ :=
    fun g C hg hC ↦ Integrable.of_bound hg.aestronglyMeasurable C
      (ae_of_all _ fun ω ↦ by simpa [Real.norm_eq_abs] using hC ω)
  have hc : Integrable (fun ω ↦ Real.cos (t * Y ω)) μ :=
    hint _ 1 (by fun_prop) fun ω ↦ Real.abs_cos_le_one _
  have hs : Integrable (fun ω ↦ Real.sin (t * Y ω)) μ :=
    hint _ 1 (by fun_prop) fun ω ↦ Real.abs_sin_le_one _
  have hY1 : Integrable Y μ := hint Y A hY hA
  have hY2 : Integrable (fun ω ↦ Y ω ^ 2) μ := hint _ (A ^ 2) (by fun_prop) fun ω ↦ by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hA ω) 2
  have h1 : Integrable (fun _ : Ω ↦ (1 : ℝ)) μ := integrable_const 1
  have hre := charFun_map_re hY.aemeasurable (μ := μ) t
  have him := charFun_map_im hY.aemeasurable (μ := μ) t
  have hvar : Var[Y; μ] = ∫ ω, Y ω ^ 2 ∂μ - (∫ ω, Y ω ∂μ) ^ 2 := by
    rw [variance_eq_sub (MemLp.of_bound hY.aestronglyMeasurable A
      (ae_of_all _ fun ω ↦ by simpa [Real.norm_eq_abs] using hA ω))]
    simp [Pi.pow_apply]
  have hP : ∀ f g : Ω → ℝ, Integrable f μ → Integrable g μ →
      Integrable (fun z : Ω × Ω ↦ f z.1 * g z.2) (μ.prod μ) :=
    fun f g hf hg ↦ hf.mul_prod hg
  have hpt : ∀ z : Ω × Ω,
      Real.cos (t * Y z.1) * Real.cos (t * Y z.2) + Real.sin (t * Y z.1) * Real.sin (t * Y z.2) ≤
        1 * 1 - t ^ 2 / 8 * (Y z.1 ^ 2 * 1 + 1 * Y z.2 ^ 2 - 2 * (Y z.1 * Y z.2)) := by
    intro z
    rw [← Real.cos_sub]
    have hab : |t * Y z.1 - t * Y z.2| ≤ Real.pi := by
      have h1 := hA z.1
      have h2 := hA z.2
      calc |t * Y z.1 - t * Y z.2| ≤ |t| * |Y z.1| + |t| * |Y z.2| := by
            rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
        _ ≤ |t| * A + |t| * A := by gcongr
        _ ≤ Real.pi := by linarith [Real.two_le_pi]
    refine (Real.cos_le_one_sub_mul_cos_sq hab).trans ?_
    have hπ : 2 / Real.pi ^ 2 ≥ 1 / 8 := by
      rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [Real.pi_le_four, Real.pi_pos]
    have hsq : (t * Y z.1 - t * Y z.2) ^ 2 =
        t ^ 2 * (Y z.1 ^ 2 * 1 + 1 * Y z.2 ^ 2 - 2 * (Y z.1 * Y z.2)) := by ring
    rw [hsq]
    have : 0 ≤ t ^ 2 * (Y z.1 ^ 2 * 1 + 1 * Y z.2 ^ 2 - 2 * (Y z.1 * Y z.2)) := by
      rw [← hsq]; positivity
    nlinarith
  have hQ1 : Integrable (fun z : Ω × Ω ↦ Y z.1 ^ 2 * 1 + 1 * Y z.2 ^ 2) (μ.prod μ) :=
    (hP _ _ hY2 h1).add (hP _ _ h1 hY2)
  have hQ : Integrable (fun z : Ω × Ω ↦ Y z.1 ^ 2 * 1 + 1 * Y z.2 ^ 2 - 2 * (Y z.1 * Y z.2))
      (μ.prod μ) := hQ1.sub ((hP _ _ hY1 hY1).const_mul 2)
  have hF : Integrable (fun z : Ω × Ω ↦ Real.cos (t * Y z.1) * Real.cos (t * Y z.2) +
      Real.sin (t * Y z.1) * Real.sin (t * Y z.2)) (μ.prod μ) :=
    (hP _ _ hc hc).add (hP _ _ hs hs)
  have hG : Integrable (fun z : Ω × Ω ↦ 1 * 1 - t ^ 2 / 8 *
      (Y z.1 ^ 2 * 1 + 1 * Y z.2 ^ 2 - 2 * (Y z.1 * Y z.2))) (μ.prod μ) :=
    (hP _ _ h1 h1).sub (hQ.const_mul (t ^ 2 / 8))
  have hmono := integral_mono hF hG hpt
  rw [integral_add (hP _ _ hc hc) (hP _ _ hs hs), integral_sub (hP _ _ h1 h1)
    (hQ.const_mul _), integral_const_mul (t ^ 2 / 8), integral_sub hQ1
    ((hP _ _ hY1 hY1).const_mul 2), integral_add (hP _ _ hY2 h1) (hP _ _ h1 hY2),
    integral_const_mul (2 : ℝ)] at hmono
  have hpm : ∀ f g : Ω → ℝ, ∫ z, f z.1 * g z.2 ∂(μ.prod μ) = (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ :=
    fun f g ↦ integral_prod_mul f g
  rw [hpm (fun ω ↦ Real.cos (t * Y ω)) (fun ω ↦ Real.cos (t * Y ω)),
    hpm (fun ω ↦ Real.sin (t * Y ω)) (fun ω ↦ Real.sin (t * Y ω)),
    hpm (fun ω ↦ Y ω ^ 2) (fun _ ↦ 1), hpm (fun _ ↦ 1) (fun ω ↦ Y ω ^ 2), hpm Y Y] at hmono
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, one_mul] at hmono
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him, hvar]
  linarith [sq (∫ ω, Y ω ∂μ)]

/-- `summable_variance_of_ae_tendsto_sum` at a positive bound. -/
private theorem summable_variance_of_ae_tendsto_sum_of_pos [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} (hm : ∀ n, Measurable (Y n)) (hi : iIndepFun Y μ) {A : ℝ} (hA0 : 0 < A)
    (hA : ∀ n ω, |Y n ω| ≤ A)
    (hc : ∀ᵐ ω ∂μ, ∃ l, Tendsto (fun n ↦ ∑ k ∈ range n, Y k ω) atTop (𝓝 l)) :
    Summable fun n ↦ Var[Y n; μ] := by
  set S : ℕ → Ω → ℝ := fun n ω ↦ ∑ k ∈ range n, Y k ω with hS
  have hSm n : Measurable (S n) := Finset.measurable_sum _ fun k _ ↦ hm k
  set L : Ω → ℝ := fun ω ↦ limUnder atTop fun n ↦ S n ω
  have hL : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ S n ω) atTop (𝓝 (L ω)) :=
    hc.mono fun ω ⟨_, h⟩ ↦ by simp only [L, S]; rwa [h.limUnder_eq]
  have hLm : AEMeasurable L μ :=
    aemeasurable_of_tendsto_metrizable_ae' (fun n ↦ (hSm n).aemeasurable) hL
  have hD := tendstoInDistribution_of_ae_tendsto (fun n ↦ (hSm n).aemeasurable) hLm hL
  -- a frequency `τ` at which the limit characteristic function stays away from zero
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ‖charFun (μ.map L) τ - 1‖ < 1 / 2 ∧ τ * A ≤ 1 := by
    refine Filter.Eventually.and (nhdsWithin_le_nhds ?_) (nhdsWithin_le_nhds ?_)
    · have h := (continuous_charFun (μ := μ.map L)).tendsto 0
      simp only [charFun_zero, probReal_univ, Complex.ofReal_one] at h
      exact (h.eventually (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 2))).mono
        fun τ hτ ↦ by rwa [dist_eq_norm] at hτ
    · have h : ∀ᶠ τ in 𝓝 (0 : ℝ), τ < 1 / A :=
        eventually_lt_nhds (by positivity)
      filter_upwards [h] with τ hτ
      rw [lt_div_iff₀ hA0] at hτ
      exact hτ.le
  obtain ⟨τ, ⟨hτ1, hτA⟩, hτ0 : 0 < τ⟩ := (hev.and self_mem_nhdsWithin).exists
  have hψ : 1 / 2 < ‖charFun (μ.map L) τ‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - charFun (μ.map L) τ)
    rw [norm_sub_rev] at hτ1
    simp only [norm_one, sub_sub_cancel] at this
    linarith
  -- the partial sums of the variances are eventually bounded
  have hprod n : ‖charFun (μ.map (S n)) τ‖ ^ 2 ≤
      Real.exp (-(τ ^ 2 / 4 * ∑ k ∈ range n, Var[Y k; μ])) := by
    rw [hS, (iIndepFun_iff_finset.1 hi (range n)).charFun_map_fun_finsetSum_eq_prod
      fun k _ ↦ (hm k).aemeasurable, Finset.prod_apply, norm_prod, ← Finset.prod_pow,
      Finset.mul_sum,
      ← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun k _ ↦ sq_nonneg _) fun k _ ↦ ?_
    refine (norm_charFun_map_sq_le_one_sub_variance (hm k) (hA k)
      (by rwa [abs_of_pos hτ0])).trans ?_
    have := Real.one_sub_le_exp_neg (τ ^ 2 / 4 * Var[Y k; μ])
    linarith
  have hlim := hD.tendsto_charFun τ
  have hevn : ∀ᶠ n in atTop, 1 / 2 < ‖charFun (μ.map (S n)) τ‖ :=
    (continuous_norm.tendsto _).comp hlim |>.eventually (lt_mem_nhds hψ)
  set C := 4 * Real.log 4 / τ ^ 2
  have hbound : ∀ᶠ n in atTop, ∑ k ∈ range n, Var[Y k; μ] ≤ C := by
    filter_upwards [hevn] with n hn
    have h1 : (1 / 4 : ℝ) < Real.exp (-(τ ^ 2 / 4 * ∑ k ∈ range n, Var[Y k; μ])) := by
      have := hprod n
      nlinarith
    rw [← Real.log_lt_iff_lt_exp (by norm_num), one_div, Real.log_inv] at h1
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbound
  refine summable_of_sum_range_le (c := C) (fun n ↦ variance_nonneg _ _) fun n ↦ ?_
  refine le_trans ?_ (hN (max n N) (le_max_right _ _))
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_max_left _ _))
    fun k _ _ ↦ variance_nonneg _ _


/-- If a series of independent random variables bounded by a common constant converges almost
surely in the given order, then their variances are summable. A bound `A ≤ 0` forces `Y = 0`. -/
theorem summable_variance_of_ae_tendsto_sum [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hm : ∀ n, Measurable (Y n)) (hi : iIndepFun Y μ) {A : ℝ} (hA : ∀ n ω, |Y n ω| ≤ A)
    (hc : ∀ᵐ ω ∂μ, ∃ l, Tendsto (fun n ↦ ∑ k ∈ range n, Y k ω) atTop (𝓝 l)) :
    Summable fun n ↦ Var[Y n; μ] := by
  rcases le_or_gt A 0 with hA0 | hA0
  · have hY : ∀ n, Y n = 0 := fun n ↦ funext fun ω ↦ abs_nonpos_iff.1 ((hA n ω).trans hA0)
    simp [hY]
  · exact summable_variance_of_ae_tendsto_sum_of_pos hm hi hA0 hA hc

/-- Convergence along `SummationFilter.conditional ℕ` is convergence of the partial sums over
`Finset.range n`. -/
private lemma summable_conditional_iff {f : ℕ → ℝ} :
    Summable f (SummationFilter.conditional ℕ) ↔
      ∃ l, Tendsto (fun n ↦ ∑ i ∈ range n, f i) atTop (𝓝 l) := by
  simp only [Summable, HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  rfl

/-- Changing finitely many terms preserves convergence of the partial sums. -/
private lemma exists_tendsto_sum_range_of_eventuallyEq {f g : ℕ → ℝ}
    (hfg : ∀ᶠ n in atTop, f n = g n)
    (hf : ∃ l, Tendsto (fun n ↦ ∑ i ∈ range n, f i) atTop (𝓝 l)) :
    ∃ l, Tendsto (fun n ↦ ∑ i ∈ range n, g i) atTop (𝓝 l) := by
  obtain ⟨l, hl⟩ := hf
  obtain ⟨N, hN⟩ := eventually_atTop.1 hfg
  refine ⟨l + ∑ i ∈ range N, (g i - f i), (hl.add tendsto_const_nhds).congr' ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  have hd : ∑ i ∈ range n, (g i - f i) = ∑ i ∈ range N, (g i - f i) := by
    refine (Finset.sum_subset (Finset.range_mono hn) fun i hi hiN ↦ ?_).symm
    rw [hN i (by simpa using hiN), sub_self]
  rw [← hd, Finset.sum_sub_distrib]
  ring

/-- **Kolmogorov's three-series theorem.** For independent real random variables and a
threshold `A > 0`, the series `∑ Xₙ` converges almost surely in the given order if and only if
`∑ P(|Xₙ| > A) < ∞`, the means of the truncations `Xₙ 1{|Xₙ| ≤ A}` form an ordered convergent
series, and the variances of the truncations are summable. -/
theorem ae_summable_conditional_iff_threeSeries [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hm : ∀ n, Measurable (X n)) (hi : iIndepFun X μ) {A : ℝ} (hA : 0 < A) :
    (∀ᵐ ω ∂μ, Summable (fun n ↦ X n ω) (SummationFilter.conditional ℕ)) ↔
      (∑' n, μ {ω | A < |X n ω|}) < ⊤ ∧
      Summable (fun n ↦ ∫ ω, (if |X n ω| ≤ A then X n ω else 0) ∂μ)
        (SummationFilter.conditional ℕ) ∧
      Summable (fun n ↦ Var[fun ω ↦ if |X n ω| ≤ A then X n ω else 0; μ]) := by
  set Y : ℕ → Ω → ℝ := fun n ω ↦ if |X n ω| ≤ A then X n ω else 0 with hY
  have hYm n : Measurable (Y n) :=
    Measurable.ite (measurableSet_le (continuous_abs.measurable.comp (hm n)) measurable_const)
      (hm n) measurable_const
  have hYi : iIndepFun Y μ := by
    have := hi.comp (fun _ (x : ℝ) ↦ if |x| ≤ A then x else 0) fun _ ↦
      Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const) measurable_id
        measurable_const
    exact this
  have hYb n ω : |Y n ω| ≤ A := by
    simp only [hY]
    split_ifs with h
    · exact h
    · simpa using hA.le
  have hYL n : MemLp (Y n) 2 μ :=
    MemLp.of_bound (hYm n).aestronglyMeasurable A
      (ae_of_all _ fun ω ↦ by simpa [Real.norm_eq_abs] using hYb n ω)
  have hXY : ∀ ω n, |X n ω| ≤ A → X n ω = Y n ω := fun ω n h ↦ by simp [hY, h]
  have hsm n : MeasurableSet {ω | A < |X n ω|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hm n))
  simp only [summable_conditional_iff]
  constructor
  · intro h
    -- the terms tend to zero, so eventually `|Xₙ| ≤ A`
    have hev : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, |X n ω| ≤ A := by
      filter_upwards [h] with ω ⟨l, hl⟩
      have h0 : Tendsto (fun n ↦ X n ω) atTop (𝓝 0) := by
        have := ((tendsto_add_atTop_iff_nat 1).2 hl).sub hl
        simpa [Finset.sum_range_succ] using this
      filter_upwards [Metric.tendsto_nhds.1 h0 A hA] with n hn
      rw [Real.dist_eq, sub_zero] at hn
      exact hn.le
    have h1 : (∑' n, μ {ω | A < |X n ω|}) < ⊤ := by
      by_contra hinf
      have hind : iIndepSet (fun n ↦ {ω | A < |X n ω|}) μ := by
        refine (iIndepSet_iff_meas_biInter hsm).2 fun S ↦ ?_
        exact iIndepFun_iff_measure_inter_preimage_eq_mul.1 hi S
          (sets := fun _ ↦ {x : ℝ | A < |x|})
          fun _ _ ↦ measurableSet_lt measurable_const continuous_abs.measurable
      have h1 := measure_limsup_eq_one hsm hind (not_lt_top_iff.1 hinf)
      have h0 : μ (limsup (fun n ↦ {ω | A < |X n ω|}) atTop) = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [hev] with ω hω
        rw [mem_limsup_iff_frequently_mem, not_frequently]
        filter_upwards [hω] with n hn
        simpa using hn
      simp [h0] at h1
    have hYc : ∀ᵐ ω ∂μ, ∃ l, Tendsto (fun n ↦ ∑ k ∈ range n, Y k ω) atTop (𝓝 l) := by
      filter_upwards [h, hev] with ω hω hev
      exact exists_tendsto_sum_range_of_eventuallyEq (hev.mono fun n hn ↦ hXY ω n hn) hω
    have hv := summable_variance_of_ae_tendsto_sum hYm hYi hYb hYc
    have hZ := ae_tendsto_sum_sub_integral_of_summable_variance hYm hYi hYL hv
    obtain ⟨ω, ⟨l₁, hl₁⟩, ⟨l₂, hl₂⟩⟩ := (hYc.and hZ).exists
    refine ⟨h1, ⟨l₁ - l₂, (hl₁.sub hl₂).congr fun n ↦ ?_⟩, hv⟩
    rw [← Finset.sum_sub_distrib]
    simp [hY]
  · rintro ⟨h1, ⟨m, hmean⟩, h3⟩
    have hZ := ae_tendsto_sum_sub_integral_of_summable_variance hYm hYi hYL h3
    filter_upwards [hZ, ae_eventually_notMem h1.ne] with ω ⟨l, hl⟩ hω
    refine exists_tendsto_sum_range_of_eventuallyEq
      (hω.mono fun n hn ↦ (hXY ω n (not_lt.1 hn)).symm) ⟨l + m, (hl.add hmean).congr fun n ↦ ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by simp [hY]

/-- Convergence of partial sums in their given order.
This is Mathlib conditional summability. For real sequences it allows conditional
convergence, unlike unconditional `Summable`. -/
abbrev IsOrderedSummable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] (a : ℕ → E) : Prop :=
  Summable a (SummationFilter.conditional ℕ)

/-- Unconditional summability implies ordered summability. -/
theorem Summable.isOrderedSummable {E : Type*} [TopologicalSpace E] [AddCommMonoid E]
    {a : ℕ → E} (ha : Summable a) : IsOrderedSummable a :=
  ha.mono_filter (SummationFilter.conditional ℕ).le_atTop

/-- Symmetric truncation of a real random variable at the threshold `A`. -/
@[expose]
def symmetricTruncation {Ω : Type*} (A : ℝ) (X : Ω → ℝ) (ω : Ω) : ℝ :=
  if |X ω| ≤ A then X ω else 0

/-- Defining formula of `symmetricTruncation`. -/
lemma symmetricTruncation_apply {Ω : Type*} (A : ℝ) (X : Ω → ℝ) (ω : Ω) :
    symmetricTruncation A X ω = if |X ω| ≤ A then X ω else 0 :=
  rfl

/-- The symmetric truncation at a nonnegative threshold is bounded by the threshold. -/
lemma abs_symmetricTruncation_le {Ω : Type*} {A : ℝ} (hA : 0 ≤ A) (X : Ω → ℝ) (ω : Ω) :
    |symmetricTruncation A X ω| ≤ A := by
  rw [symmetricTruncation_apply]
  split_ifs with h
  · exact h
  · simpa using hA

/-- The three conditions in Kolmogorov's theorem; only the mean series may converge
conditionally. -/
@[expose]
def HasThreeSeries {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (μ : Measure Ω) (A : ℝ) : Prop :=
  (∑' n, μ {ω | A < |X n ω|}) < ⊤ ∧
    IsOrderedSummable (fun n ↦ ∫ ω, symmetricTruncation A (X n) ω ∂μ) ∧
    Summable (fun n ↦ variance (symmetricTruncation A (X n)) μ)

/-- Defining property of `HasThreeSeries`. -/
lemma hasThreeSeries_iff {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}
    {A : ℝ} :
    HasThreeSeries X μ A ↔ (∑' n, μ {ω | A < |X n ω|}) < ⊤ ∧
      IsOrderedSummable (fun n ↦ ∫ ω, symmetricTruncation A (X n) ω ∂μ) ∧
      Summable (fun n ↦ variance (symmetricTruncation A (X n)) μ) :=
  Iff.rfl

/-- **06.23**: Kolmogorov's three-series characterization at every fixed positive threshold.
This is `ae_summable_conditional_iff_threeSeries`, restated with `IsOrderedSummable` and
`HasThreeSeries`. -/
theorem kolmogorov_threeSeries {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) {A : ℝ} (hA : 0 < A) :
    (∀ᵐ ω ∂μ, IsOrderedSummable (fun n ↦ X n ω)) ↔ HasThreeSeries X μ A :=
  ae_summable_conditional_iff_threeSeries X hm hi hA

end CKMA
