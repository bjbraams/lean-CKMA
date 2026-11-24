/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Tactic
import TauCeti.Probability.CentralLimitTheorem.Lindeberg
import CKMA.Probability.LimitTheorems.LindebergFeller
import CKMA.Probability.LimitTheorems.ThreeSeries
import CKMA.Probability.LimitTheorems.BerryEsseen

/-!
# Ordered random series, LIL and quantitative central limits (06.23, 06.27, 06.34, 06.36)

`IsOrderedSummable` is Mathlib's `Summable` along `SummationFilter.conditional`. On `ℕ`
that filter is the limit of sums over `Finset.range`, so it is convergence of partial sums
in their given order. This is weaker than unconditional `Summable` for real sequences and
is the correct mean-series condition in Kolmogorov's three-series criterion. Truncated
variances remain unconditionally summable.

The other main targets are Hartman–Wintner's iterated-logarithm law, the Lindeberg–Feller
central limit theorem and its converse under Feller's condition, and a Berry–Esseen bound.
Row second-moment sums are uncentered; they are variances under the centering hypothesis
of the limit theorems. The LIL index shift avoids the initial logarithmic singularities
without changing the limiting assertions.

## Main definitions

* `CKMA.IsOrderedSummable`: convergence of partial sums in their given order.
* `CKMA.symmetricTruncation`: symmetric truncation of a real random variable at threshold `A`.
* `CKMA.HasThreeSeries`: the three series conditions of Kolmogorov's criterion.
* `CKMA.iteratedLogScale`: the iterated-logarithm normalization `√(2 σ² n log log n)`.
* `CKMA.HasLindebergCondition`, `CKMA.HasFellerCondition`: Lindeberg's and Feller's conditions
  for a triangular array.
* `CKMA.kolmogorovDistance`: supremum distance between real distribution functions.

## Main results

* `CKMA.kolmogorov_threeSeries`: Kolmogorov's three-series theorem (**06.23**).
* `CKMA.hartman_wintner`: Hartman–Wintner law of the iterated logarithm (**06.27**).
* `CKMA.lindeberg_feller`: Lindeberg–Feller central limit theorem (**06.34**).
* `CKMA.lindeberg_feller_iff`: under Feller's condition, Lindeberg's condition is equivalent to
  the central limit theorem.
* `CKMA.berry_esseen`: Berry–Esseen theorem (**06.36**).
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

/-- Convergence of partial sums in their given order.
This is Mathlib conditional summability. For real sequences it allows conditional
convergence, unlike unconditional `Summable`. -/
@[expose]
abbrev IsOrderedSummable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] (a : ℕ → E) : Prop :=
  Summable a (SummationFilter.conditional ℕ)

/-- Unconditional summability implies ordered summability. -/
theorem Summable.isOrderedSummable {E : Type*} [TopologicalSpace E] [AddCommMonoid E]
    {a : ℕ → E} (ha : Summable a) : IsOrderedSummable a :=
  ha.mono_filter (SummationFilter.conditional ℕ).le_atTop

@[deprecated (since := "2026-11-15")]
alias isOrderedSummable_of_summable := Summable.isOrderedSummable

/-- Symmetric truncation of a real random variable. -/
@[expose]
def symmetricTruncation {Ω : Type*} (A : ℝ) (X : Ω → ℝ) (ω : Ω) : ℝ :=
  if |X ω| ≤ A then X ω else 0

/-- The three conditions in Kolmogorov's theorem; only the mean series may converge conditionally.
  -/
@[expose]
def HasThreeSeries {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (μ : Measure Ω) (A : ℝ) : Prop :=
  (∑' n, μ {ω | A < |X n ω|}) < ∞ ∧
    IsOrderedSummable (fun n ↦ ∫ ω, symmetricTruncation A (X n) ω ∂μ) ∧
    Summable (fun n ↦ variance (symmetricTruncation A (X n)) μ)

/-- **06.23**: Kolmogorov's three-series characterization at every fixed positive threshold. -/
theorem kolmogorov_threeSeries {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) {A : ℝ} (hA : 0 < A) :
    (∀ᵐ ω ∂μ, IsOrderedSummable (fun n ↦ X n ω)) ↔ HasThreeSeries X μ A :=
  ae_summable_conditional_iff_threeSeries X hm hi hA

/-- The iterated-logarithm normalization, totalized at the first few indices. -/
@[expose]
def iteratedLogScale (varianceParam : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * varianceParam * n * Real.log (Real.log n))

/-- **06.27**: the Hartman–Wintner law of the iterated logarithm.
The shift by three avoids exceptional small logarithm arguments without changing the limit. -/
theorem hartman_wintner {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (hX : MemLp (X 0) 2 μ) (hc : ∫ ω, X 0 ω ∂μ = 0) (hv : 0 < variance (X 0) μ) :
    ∀ᵐ ω ∂μ,
      limsup (fun n : ℕ ↦ (((∑ j ∈ Finset.range (n + 3), X j ω) /
        iteratedLogScale (variance (X 0) μ) (n + 3) : ℝ) : EReal)) atTop = 1 ∧
      liminf (fun n : ℕ ↦ (((∑ j ∈ Finset.range (n + 3), X j ω) /
        iteratedLogScale (variance (X 0) μ) (n + 3) : ℝ) : EReal)) atTop = -1 := by
  sorry

/-- The sum of the uncentered second moments of one row.
This is the row variance when every entry is centered. -/
@[expose]
def arrayRowVariance {Ω : Type*} [MeasurableSpace Ω] {k : ℕ → ℕ}
    (X : ∀ n, Fin (k n) → Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  ∑ i, ∫ ω, (X n i ω) ^ 2 ∂μ

/-- Lindeberg's negligible large-increment condition, normalized by the row second-moment sum. -/
@[expose]
def HasLindebergCondition {Ω : Type*} [MeasurableSpace Ω] {k : ℕ → ℕ}
    (X : ∀ n, Fin (k n) → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ (arrayRowVariance X μ n)⁻¹ *
    ∑ i, ∫ ω, if ε * Real.sqrt (arrayRowVariance X μ n) < |X n i ω|
      then (X n i ω) ^ 2 else 0 ∂μ) atTop (𝓝 0)

/-- No individual second moment contributes a positive fraction of the row second-moment sum. -/
@[expose]
def HasFellerCondition {Ω : Type*} [MeasurableSpace Ω] {k : ℕ → ℕ}
    (X : ∀ n, Fin (k n) → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i,
    (∫ ω, (X n i ω) ^ 2 ∂μ) / arrayRowVariance X μ n < ε

/-- Row sum normalized by the square root of the row second-moment sum.
The sum is centered when the separate centering hypothesis of the limit theorems holds. -/
@[expose]
def normalizedArraySum {Ω : Type*} [MeasurableSpace Ω] {k : ℕ → ℕ}
    (X : ∀ n, Fin (k n) → Ω → ℝ) (μ : Measure Ω) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i, X n i ω) / Real.sqrt (arrayRowVariance X μ n)

/-- **06.34**: the Lindeberg condition implies the central limit theorem for row-independent
arrays. The proof rescales each row and applies TauCeti's
`ProbabilityTheory.HasLaw.tendstoInDistribution_sum_of_lindeberg`. -/
theorem lindeberg_feller {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {k : ℕ → ℕ} (X : ∀ n, Fin (k n) → Ω → ℝ)
    (hi : ∀ n, iIndepFun (X n) μ)
    (hLp : ∀ n i, MemLp (X n i) 2 μ) (hc : ∀ n i, ∫ ω, X n i ω ∂μ = 0)
    (hv : ∀ n, 0 < arrayRowVariance X μ n) (hL : HasLindebergCondition X μ) :
    TendstoInDistribution (normalizedArraySum X μ) atTop id (fun _ ↦ μ) (gaussianReal 0 1) := by
  obtain ⟨v, hvv⟩ : ∃ v : ℕ → ℝ, v = arrayRowVariance X μ := ⟨_, rfl⟩
  rw [← hvv] at hv
  have hs n : 0 < Real.sqrt (v n) := Real.sqrt_pos.2 (hv n)
  have hsq n : Real.sqrt (v n) ^ 2 = v n := Real.sq_sqrt (hv n).le
  obtain ⟨Y, hY⟩ : ∃ Y : ∀ n, Fin (k n) → Ω → ℝ,
      Y = fun n i ω ↦ X n i ω / Real.sqrt (v n) := ⟨_, rfl⟩
  have hYL2 n i : MemLp (Y n i) 2 μ := by
    simpa only [hY, div_eq_mul_inv] using (hLp n i).mul_const (Real.sqrt (v n))⁻¹
  have hY0 n i : ∫ ω, Y n i ω ∂μ = 0 := by simp only [hY, integral_div, hc, zero_div]
  have hind n : iIndepFun (Y n) μ := by
    rw [hY]
    exact (hi n).comp (fun _ x ↦ x / Real.sqrt (v n)) fun _ ↦ measurable_id.div_const _
  have hvar : ∀ᶠ n in atTop, ∑ i, Var[Y n i; μ] = 1 := by
    refine Filter.Eventually.of_forall fun n ↦ ?_
    rw [Finset.sum_congr rfl fun i _ ↦
      variance_of_integral_eq_zero (hYL2 n i).aestronglyMeasurable.aemeasurable (hY0 n i)]
    simp only [hY, div_pow, hsq, integral_div]
    rw [← Finset.sum_div, div_eq_one_iff_eq (hv n).ne', hvv, arrayRowVariance]
  have hlind : ∀ ε > 0, Tendsto (fun n ↦ ∑ i,
      ∫ ω, {ω | ε ≤ |Y n i ω|}.indicator (fun ω ↦ Y n i ω ^ 2) ω ∂μ) atTop (𝓝 0) := by
    intro ε hε
    have hL' := hL (ε / 2) (half_pos hε)
    rw [← hvv] at hL'
    refine squeeze_zero (fun n ↦ ?_) (fun n ↦ ?_) hL'
    · exact Finset.sum_nonneg fun i _ ↦
        integral_nonneg fun ω ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [← integral_const_mul]
    have hφ : Measurable fun x : ℝ ↦ if ε / 2 * Real.sqrt (v n) < |x| then x ^ 2 else 0 :=
      Measurable.ite (measurableSet_lt measurable_const continuous_abs.measurable)
        (measurable_id.pow_const 2) measurable_const
    refine integral_mono_of_nonneg
      (ae_of_all _ fun ω ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _)
      (((hLp n i).integrable_sq.mono
        (hφ.comp_aemeasurable (hLp n i).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
        (ae_of_all _ fun ω ↦ ?_)).const_mul _) (ae_of_all _ fun ω ↦ ?_)
    · dsimp only [Function.comp_apply]
      split_ifs <;> simp [sq_nonneg]
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hY]
      have hεs := mul_pos hε (hs n)
      split_ifs with h1 h2
      · rw [div_pow, hsq, div_eq_inv_mul]
      · rw [abs_div, abs_of_pos (hs n), le_div_iff₀ (hs n)] at h1
        exact absurd (by linarith) h2
      · exact mul_nonneg (inv_nonneg.2 (hv n).le) (sq_nonneg _)
      · simp
  have hsum : normalizedArraySum X μ = fun n ω ↦ ∑ i, Y n i ω := by
    funext n ω
    simp only [normalizedArraySum, hY, Finset.sum_div, hvv]
  rw [hsum]
  exact HasLaw.tendstoInDistribution_sum_of_lindeberg (Ω := fun _ ↦ Ω) (P := fun _ ↦ μ)
    HasLaw.id hind hYL2 hY0 hvar hlind

/-- Under Feller's infinitesimality condition, normal convergence also implies Lindeberg's
  condition. -/
theorem lindeberg_feller_iff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {k : ℕ → ℕ} (X : ∀ n, Fin (k n) → Ω → ℝ)
    (hi : ∀ n, iIndepFun (X n) μ)
    (hLp : ∀ n i, MemLp (X n i) 2 μ) (hc : ∀ n i, ∫ ω, X n i ω ∂μ = 0)
    (hv : ∀ n, 0 < arrayRowVariance X μ n) (hF : HasFellerCondition X μ) :
    HasLindebergCondition X μ ↔
      TendstoInDistribution (normalizedArraySum X μ) atTop id (fun _ ↦ μ) (gaussianReal 0 1) :=
  ⟨lindeberg_feller μ X hi hLp hc hv,
    lindeberg_of_feller_of_tendstoInDistribution_div_sqrt hi hLp hc hv hF⟩

/-- Supremum of differences of the real CDFs. On probability measures this is the
Kolmogorov distance; the raw formula also accepts arbitrary measures. -/
@[expose]
def kolmogorovDistance (μ ν : Measure ℝ) : ℝ :=
  sSup (Set.range (fun x ↦ |cdf μ x - cdf ν x|))

/-- **06.36**: Berry–Esseen with an explicit, deliberately nonoptimal universal constant. -/
theorem berry_esseen {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (hLp : MemLp (X 0) 3 μ) (hc : ∫ ω, X 0 ω ∂μ = 0)
    {σ : ℝ} (hσ : 0 < σ) (hv : variance (X 0) μ = σ ^ 2)
    {n : ℕ} (hn : 0 < n) :
    kolmogorovDistance
      (μ.map (fun ω ↦ (∑ j ∈ Finset.range n, X j ω) / (σ * Real.sqrt n)))
      (gaussianReal 0 1) ≤
      100 * (∫ ω, |X 0 ω| ^ 3 ∂μ) / (σ ^ 3 * Real.sqrt n) := by
  have hW : Measurable fun ω ↦ (∑ j ∈ Finset.range n, X j ω) / (σ * Real.sqrt n) :=
    (Finset.measurable_sum _ fun j _ ↦ hm j).div_const _
  have hρ : 0 ≤ ∫ ω, |X 0 ω| ^ 3 ∂μ := integral_nonneg fun _ ↦ by positivity
  have hd : 0 < σ ^ 3 * Real.sqrt n := by
    have : 0 < Real.sqrt n := Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
    positivity
  refine csSup_le (Set.range_nonempty _) (Set.forall_mem_range.2 fun x ↦ ?_)
  rw [cdf_eq_real (μ.map _), map_measureReal_apply hW measurableSet_Iic]
  refine (abs_measureReal_sum_div_le_sub_cdf_le X hm hi hid hLp hc hσ hv hn x).trans ?_
  gcongr
  norm_num

end CKMA
