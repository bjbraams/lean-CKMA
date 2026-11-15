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
public import CKMA.Dynamics.Ergodic.Pointwise.KingmanFull

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

## Main definitions

* `CKMA.maximalErgodicSet`: the finite maximal-positive Birkhoff-sum set.
* `CKMA.IsSubadditiveProcess`: subadditivity of a sequence of observables along `T`.
* `CKMA.subadditiveMeanRate` (from `Pointwise.KingmanFull`): the infimum of normalized
  positive-length expectations.

## Main results

* `CKMA.maximal_ergodic`: the maximal ergodic inequality.
* `CKMA.birkhoff_pointwise`: Birkhoff's pointwise ergodic theorem.
* `CKMA.birkhoff_pointwise_of_ergodic`: Birkhoff's theorem for ergodic transformations.
* `CKMA.kingman_subadditive`: Kingman's subadditive ergodic theorem.
* `CKMA.kingman_subadditive_of_ergodic`: Kingman's theorem for ergodic transformations.
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

/-- **10.5**, the maximal ergodic inequality on a measure-preserving system. -/
theorem maximal_ergodic {T : Ω → Ω}
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
      (𝓝 (∫ ω, f ω ∂μ)) := by
  have hconv := birkhoff_pointwise hT.toMeasurePreserving hf
  let cexp : Ω → ℝ := μ[f | MeasurableSpace.invariants T]
  have hmeas : Measurable[MeasurableSpace.invariants T] cexp :=
    stronglyMeasurable_condExp.measurable
  have hmeas0 : Measurable cexp := hmeas.mono (MeasurableSpace.invariants_le T) le_rfl
  have hinv : cexp ∘ T = cexp :=
    MeasurableSpace.comp_eq_of_measurable_invariants hmeas
  obtain ⟨c, hc⟩ := hT.ae_eq_const_of_ae_eq_comp₀ hmeas0.aemeasurable.nullMeasurable
    (EventuallyEq.of_eq hinv)
  have : SigmaFinite (μ.trim (MeasurableSpace.invariants_le T)) := inferInstance
  have hint : ∫ ω, cexp ω ∂μ = ∫ ω, f ω ∂μ :=
    integral_condExp (MeasurableSpace.invariants_le T)
  have hconst : ∫ ω, cexp ω ∂μ = c := by
    have heq : cexp =ᵐ[μ] fun _ : Ω => c := hc.mono fun _ hω => by
      simpa [Function.const_apply] using hω
    rw [integral_congr_ae heq, integral_const]
    simp [measureReal_def, IsProbabilityMeasure.measure_univ]
  filter_upwards [hconv, hc] with ω hω hcω
  have hval : (μ[f | MeasurableSpace.invariants T]) ω = ∫ η, f η ∂μ := by
    have hcval : (μ[f | MeasurableSpace.invariants T]) ω = c := by
      simpa [cexp, Function.const_apply] using hcω
    rw [hcval, ← hint, hconst]
  simpa [hval] using hω

@[deprecated (since := "2026-11-15")]
alias birkhoffAverage_ae_tendsto_integral_of_ergodic := birkhoff_pointwise_of_ergodic

/-- Subadditivity along a transformation, on positive lengths; no artificial value for `f₀`
is imposed. Almost-everywhere inequalities are used in each pair of lengths. -/
def IsSubadditiveProcess (T : Ω → Ω) (f : ℕ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
    f (n + m) ω ≤ f n ω + f m ((T^[n]) ω)

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
  have hf_int : ∀ n : ℕ, 0 < n → Integrable (kingmanMk hf n) μ :=
    fun n hn => integrable_kingmanMk hf hn
  have hf_meas : ∀ n : ℕ, 0 < n → Measurable (kingmanMk hf n) :=
    fun n hn => measurable_kingmanMk hf hn
  have hlower' : ∃ c : ℝ, ∀ n : ℕ, 0 < n →
      c ≤ (n : ℝ)⁻¹ * ∫ ω, kingmanMk hf n ω ∂μ := by
    obtain ⟨c, hc⟩ := hlower
    refine ⟨c, fun n hn => ?_⟩
    rw [kingmanMk_integral hf hn]
    exact hc n hn
  obtain ⟨g, hg_int, hinv, hconv, hL1, hint⟩ := kingman_of_measurable hT hf_int hf_meas
    (kingmanMk_subadditive hT hf hsub) hlower'
  refine ⟨g, hg_int, hinv, ?_, ?_, ?_⟩
  · have hae : ∀ᵐ ω ∂μ, ∀ n : ℕ, f (n + 1) ω = kingmanMk hf (n + 1) ω :=
      (ae_all_iff).2 fun n => kingmanMk_ae hf (Nat.succ_pos n)
    filter_upwards [hconv, hae] with ω hω hpt
    exact hω.congr fun n => by rw [hpt n]
  · refine hL1.congr fun n => ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [kingmanMk_ae hf (Nat.succ_pos n)] with ω hω
    rw [hω]
  · rw [← kingmanMk_fekete hf]
    exact hint

@[deprecated (since := "2026-11-15")] alias kingman_of_integrable := kingman_subadditive

/-- The subadditive ergodic limit is constant and equal to the infimum mean rate. -/
theorem kingman_subadditive_of_ergodic [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : Ergodic T μ) (f : ℕ → Ω → ℝ)
    (hf : ∀ n : ℕ, 0 < n → Integrable (f n) μ)
    (hsub : IsSubadditiveProcess T f μ)
    (hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹ * f (n + 1) ω) atTop
      (𝓝 (subadditiveMeanRate f μ)) := by
  obtain ⟨g, hg_int, hinv, hconv, -, hint⟩ :=
    kingman_subadditive hT.toMeasurePreserving f hf hsub hlower
  obtain ⟨c, hc⟩ := hT.ae_eq_const_of_ae_eq_comp_ae hg_int.aestronglyMeasurable hinv
  have hcL : c = subadditiveMeanRate f μ := by
    have heq : ∫ ω, g ω ∂μ = c := by
      rw [integral_congr_ae hc]
      simp only [Function.const]
      rw [integral_const]
      simp [measureReal_def, IsProbabilityMeasure.measure_univ, smul_eq_mul, one_mul]
    exact heq.symm.trans hint
  filter_upwards [hconv, hc] with ω hω hωc
  simpa [hωc, hcL] using hω

@[deprecated (since := "2026-11-15")]
alias kingman_ae_tendsto_of_ergodic := kingman_subadditive_of_ergodic

end CKMA
