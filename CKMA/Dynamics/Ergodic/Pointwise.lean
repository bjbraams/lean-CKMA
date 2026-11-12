/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Probability.Notation

import CKMA.Dynamics.Ergodic.Pointwise.Maximal
import CKMA.Dynamics.Ergodic.Pointwise.Birkhoff
import CKMA.Dynamics.Ergodic.Pointwise.KingmanClosure

/-!
# Pointwise and subadditive ergodic theorems (10.5, 10.7)

The finite maximal-positive Birkhoff set supports the maximal ergodic inequality.
Birkhoff's theorem uses conditional expectation onto the invariant sigma-algebra, with
a scalar-mean specialization for ergodic probability-preserving transformations.

`IsSubadditiveProcess` imposes almost-everywhere inequalities at positive lengths, leaving
the length-zero value unconstrained. Kingman's targets give an invariant integrable
limit, pointwise and L¹ convergence, and the infimum formula for its mean under a lower
bound on the normalized expectations.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The finite maximal-positive Birkhoff-sum set used by the maximal ergodic lemma. -/
def maximalErgodicSet (T : Ω → Ω) (f : Ω → ℝ) (N : ℕ) : Set Ω :=
  {ω | ∃ n : ℕ, 0 < n ∧ n ≤ N ∧ 0 < birkhoffSum T f n ω}

/-- **10.5**, the maximal ergodic inequality on a probability-preserving system. -/
theorem maximal_ergodic [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ) (N : ℕ) :
    0 ≤ ∫ ω in maximalErgodicSet T f N, f ω ∂μ := by
  simpa [maximalErgodicSet] using integral_nonneg_maximalErgodicSet hT hf N

/-- **10.5**, Birkhoff's pointwise theorem with the invariant conditional-expectation limit.
The result needs no standard-Borel restriction on the probability space. -/
theorem birkhoff_pointwise [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ birkhoffAverage ℝ T f n ω) atTop
      (𝓝 ((μ[f | MeasurableSpace.invariants T]) ω)) :=
  birkhoffAverage_ae_tendsto_condExp hT hf

/-- In an ergodic system the Birkhoff limit is the scalar mean. -/
theorem birkhoff_pointwise_of_ergodic [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : Ergodic T μ) {f : Ω → ℝ} (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ birkhoffAverage ℝ T f n ω) atTop
      (𝓝 (∫ ω, f ω ∂μ)) :=
  birkhoffAverage_ae_tendsto_integral_of_ergodic hT hf

/-- Subadditivity along a transformation, on positive lengths; no artificial value for `f₀`
is imposed. Almost-everywhere inequalities are used in each pair of lengths. -/
def IsSubadditiveProcess (T : Ω → Ω) (f : ℕ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
    f (n + m) ω ≤ f n ω + f m ((T^[n]) ω)

/-- The infimum of the normalized positive-length expectations in Kingman's theorem. -/
def subadditiveMeanRate (f : ℕ → Ω → ℝ) (μ : Measure Ω) : ℝ :=
  sInf {a : ℝ | ∃ n : ℕ, 0 < n ∧ a = (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ}

/-- **10.7**, Kingman's theorem: an invariant integrable limit, pointwise and L1 convergence,
and the Fekete infimum formula for its expectation. -/
theorem kingman_subadditive [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) (f : ℕ → Ω → ℝ)
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hsub : IsSubadditiveProcess T f μ)
    (hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ) :
    ∃ g : Ω → ℝ, Integrable g μ ∧ (g ∘ T =ᵐ[μ] g) ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹ * f (n + 1) ω) atTop (𝓝 (g ω))) ∧
      Tendsto (fun n : ℕ ↦ eLpNorm (fun ω ↦ (n + 1 : ℝ)⁻¹ * f (n + 1) ω - g ω) 1 μ)
        atTop (𝓝 0) ∧
      (∫ ω, g ω ∂μ) = subadditiveMeanRate f μ := by
  simpa [IsSubadditiveProcess, subadditiveMeanRate, kingmanFekete] using
    kingman_of_integrable hT hf hsub hlower

/-- The subadditive ergodic limit is constant and equal to the infimum mean rate. -/
theorem kingman_subadditive_of_ergodic [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : Ergodic T μ) (f : ℕ → Ω → ℝ)
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hsub : IsSubadditiveProcess T f μ)
    (hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹ * f (n + 1) ω) atTop
      (𝓝 (subadditiveMeanRate f μ)) := by
  simpa [IsSubadditiveProcess, subadditiveMeanRate, kingmanFekete] using
    kingman_ae_tendsto_of_ergodic hT hf hsub hlower

end CKMA
