/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Tactic

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
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

/-- Convergence of partial sums in their given order.
This is Mathlib conditional summability. For real sequences it allows conditional
convergence, unlike unconditional `Summable`. -/
abbrev IsOrderedSummable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] (a : ℕ → E) : Prop :=
  Summable a (SummationFilter.conditional ℕ)

/-- Unconditional summability implies ordered summability. -/
theorem isOrderedSummable_of_summable {E : Type*} [TopologicalSpace E] [AddCommMonoid E]
    {a : ℕ → E} (ha : Summable a) : IsOrderedSummable a :=
  ha.mono_filter (SummationFilter.conditional ℕ).le_atTop

/-- Ordered summability is closed under addition in a topological additive monoid. -/
theorem IsOrderedSummable.add {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    [ContinuousAdd E] {a b : ℕ → E} (ha : IsOrderedSummable a) (hb : IsOrderedSummable b) :
    IsOrderedSummable (fun n ↦ a n + b n) :=
  Summable.add ha hb

/-- Symmetric truncation of a real random variable. -/
def symmetricTruncation {Ω : Type*} (A : ℝ) (X : Ω → ℝ) (ω : Ω) : ℝ :=
  if |X ω| ≤ A then X ω else 0

/-- The three conditions in Kolmogorov's theorem; only the mean series may converge conditionally.
  -/
def HasThreeSeries {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (μ : Measure Ω) (A : ℝ) : Prop :=
  (∑' n, μ {ω | A < |X n ω|}) < ∞ ∧
    IsOrderedSummable (fun n ↦ ∫ ω, symmetricTruncation A (X n) ω ∂μ) ∧
    Summable (fun n ↦ variance (symmetricTruncation A (X n)) μ)

/-- **06.23**: Kolmogorov's three-series characterization at every fixed positive threshold. -/
theorem kolmogorov_threeSeries {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) {A : ℝ} (hA : 0 < A) :
    (∀ᵐ ω ∂μ, IsOrderedSummable (fun n ↦ X n ω)) ↔ HasThreeSeries X μ A := by
  sorry

/-- The iterated-logarithm normalization, totalized at the first few indices. -/
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
def arrayRowVariance {Ω : Type*} [MeasurableSpace Ω] {k : ℕ → ℕ}
    (X : ∀ n, Fin (k n) → Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  ∑ i, ∫ ω, (X n i ω) ^ 2 ∂μ

/-- Lindeberg's negligible large-increment condition, normalized by the row second-moment sum. -/
def HasLindebergCondition {Ω : Type*} [MeasurableSpace Ω] {k : ℕ → ℕ}
    (X : ∀ n, Fin (k n) → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ (arrayRowVariance X μ n)⁻¹ *
    ∑ i, ∫ ω, if ε * Real.sqrt (arrayRowVariance X μ n) < |X n i ω|
      then (X n i ω) ^ 2 else 0 ∂μ) atTop (𝓝 0)

/-- No individual second moment contributes a positive fraction of the row second-moment sum. -/
def HasFellerCondition {Ω : Type*} [MeasurableSpace Ω] {k : ℕ → ℕ}
    (X : ∀ n, Fin (k n) → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i,
    (∫ ω, (X n i ω) ^ 2 ∂μ) / arrayRowVariance X μ n < ε

/-- Row sum normalized by the square root of the row second-moment sum.
The sum is centered when the separate centering hypothesis of the limit theorems holds. -/
def normalizedArraySum {Ω : Type*} [MeasurableSpace Ω] {k : ℕ → ℕ}
    (X : ∀ n, Fin (k n) → Ω → ℝ) (μ : Measure Ω) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i, X n i ω) / Real.sqrt (arrayRowVariance X μ n)

/-- **06.34**: the Lindeberg condition implies the central limit theorem for row-independent arrays.
  -/
theorem lindeberg_feller {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {k : ℕ → ℕ} (X : ∀ n, Fin (k n) → Ω → ℝ)
    (hm : ∀ n i, Measurable (X n i)) (hi : ∀ n, iIndepFun (X n) μ)
    (hLp : ∀ n i, MemLp (X n i) 2 μ) (hc : ∀ n i, ∫ ω, X n i ω ∂μ = 0)
    (hv : ∀ n, 0 < arrayRowVariance X μ n) (hL : HasLindebergCondition X μ) :
    TendstoInDistribution (normalizedArraySum X μ) atTop id (fun _ ↦ μ) (gaussianReal 0 1) := by
  sorry

/-- Under Feller's infinitesimality condition, normal convergence also implies Lindeberg's
  condition. -/
theorem lindeberg_feller_iff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {k : ℕ → ℕ} (X : ∀ n, Fin (k n) → Ω → ℝ)
    (hm : ∀ n i, Measurable (X n i)) (hi : ∀ n, iIndepFun (X n) μ)
    (hLp : ∀ n i, MemLp (X n i) 2 μ) (hc : ∀ n i, ∫ ω, X n i ω ∂μ = 0)
    (hv : ∀ n, 0 < arrayRowVariance X μ n) (hF : HasFellerCondition X μ) :
    HasLindebergCondition X μ ↔
      TendstoInDistribution (normalizedArraySum X μ) atTop id (fun _ ↦ μ) (gaussianReal 0 1) := by
  sorry

/-- Supremum of differences of the real CDFs. On probability measures this is the
Kolmogorov distance; the raw formula also accepts arbitrary measures. -/
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
  sorry

end CKMA
