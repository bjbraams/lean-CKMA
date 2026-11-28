/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Data.EReal.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.LiminfLimsup

/-!
# Definitions for Kingman's subadditive ergodic theorem

A subadditive process along `T` is a sequence `f n` of real observables with
`f (n + m) ≤ f n + f m ∘ T^[n]` almost everywhere at positive lengths. Its mean rate is the
Fekete infimum of the normalized expectations. The proof of Kingman's theorem works with the
normalized values `(n + 1)⁻¹ f (n + 1)`, their extended liminf and limsup, and the height
truncations `max (f n) (-K n)`.

## Main definitions

* `CKMA.IsSubadditiveProcess`: subadditivity of a sequence of observables along `T`.
* `CKMA.HasLinearLowerBound`: the pointwise bound `-C n ≤ f n` at positive lengths.
* `CKMA.subadditiveMeanRate`: the infimum of the normalized positive-length expectations.
* `CKMA.kingmanRatio`: the normalized values `(n + 1)⁻¹ * f (n + 1) ω`.
* `CKMA.kingmanLiminf`, `CKMA.kingmanLimsup`: their extended liminf and limsup.
* `CKMA.kingmanLiminfReal`, `CKMA.kingmanLimsupReal`: the real representatives.
* `CKMA.kingmanTrunc`: the height truncation `max (f n) (-K n)`.

## Main results

* `CKMA.IsSubadditiveProcess.ae_forall`: all pairs of lengths hold on one full-measure set.
* `CKMA.le_subadditiveMeanRate`, `CKMA.subadditiveMeanRate_le`: the infimum bounds.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

/-- Subadditivity along a transformation, on positive lengths; no artificial value for `f₀`
is imposed. Almost-everywhere inequalities are used in each pair of lengths. -/
@[expose]
def IsSubadditiveProcess (T : Ω → Ω) (f : ℕ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
    f (n + m) ω ≤ f n ω + f m ((T^[n]) ω)

/-- Unfolding of `IsSubadditiveProcess`. -/
lemma isSubadditiveProcess_iff {f : ℕ → Ω → ℝ} :
    IsSubadditiveProcess T f μ ↔ ∀ n m : ℕ, 0 < n → 0 < m → ∀ᵐ ω ∂μ,
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω) := Iff.rfl

/-- Every pair of positive lengths satisfies the subadditive inequality simultaneously. -/
lemma IsSubadditiveProcess.ae_forall {f : ℕ → Ω → ℝ} (hsub : IsSubadditiveProcess T f μ) :
    ∀ᵐ ω ∂μ, ∀ n m : ℕ, 0 < n → 0 < m →
      f (n + m) ω ≤ f n ω + f m ((T^[n]) ω) := by
  refine ae_all_iff.2 fun n => ae_all_iff.2 fun m => ?_
  by_cases hn : 0 < n
  · by_cases hm : 0 < m
    · exact (hsub n m hn hm).mono fun _ h _ _ => h
    · exact Eventually.of_forall fun _ _ hm' => (hm hm').elim
  · exact Eventually.of_forall fun _ hn' => (hn hn').elim

/-- A null-set property holds along almost every forward orbit. -/
lemma ae_forall_iterate (hT : MeasurePreserving T μ μ) {p : Ω → Prop}
    (hp : ∀ᵐ ω ∂μ, p ω) : ∀ᵐ ω ∂μ, ∀ i : ℕ, p ((T^[i]) ω) :=
  ae_all_iff.2 fun i => (hT.iterate i).quasiMeasurePreserving.ae hp

/-- The pointwise linear lower bound `-C n ≤ f n ω` at every positive length and every point. -/
@[expose]
def HasLinearLowerBound (f : ℕ → Ω → ℝ) (C : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω

omit [MeasurableSpace Ω] in
/-- Unfolding of `HasLinearLowerBound`. -/
lemma hasLinearLowerBound_iff {f : ℕ → Ω → ℝ} {C : ℝ} :
    HasLinearLowerBound f C ↔ ∀ n : ℕ, 0 < n → ∀ ω, -C * (n : ℝ) ≤ f n ω := Iff.rfl

/-- The infimum of the normalized positive-length expectations in Kingman's theorem
(the Fekete infimum). On `ℝ`, `sInf` of a set that is not bounded below is `0`. -/
@[expose]
def subadditiveMeanRate (f : ℕ → Ω → ℝ) (μ : Measure Ω) : ℝ :=
  sInf {a : ℝ | ∃ n : ℕ, 0 < n ∧ a = (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ}

/-- Defining equation of `subadditiveMeanRate`. -/
lemma subadditiveMeanRate_def (f : ℕ → Ω → ℝ) (μ : Measure Ω) :
    subadditiveMeanRate f μ = sInf {a : ℝ | ∃ n : ℕ, 0 < n ∧ a = (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ} :=
  rfl

/-- A lower bound for every normalized positive-length integral bounds the mean rate. -/
lemma le_subadditiveMeanRate {f : ℕ → Ω → ℝ} {c : ℝ}
    (hc : ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ) : c ≤ subadditiveMeanRate f μ := by
  refine le_csInf ⟨((1 : ℕ) : ℝ)⁻¹ * ∫ ω, f 1 ω ∂μ, ⟨1, Nat.one_pos, rfl⟩⟩ ?_
  rintro a ⟨n, hn, rfl⟩
  exact hc n hn

/-- Under a lower bound on the normalized integrals, the mean rate is at most each of them. -/
lemma subadditiveMeanRate_le {f : ℕ → Ω → ℝ}
    (hlower : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ) {n : ℕ} (hn : 0 < n) :
    subadditiveMeanRate f μ ≤ (n : ℝ)⁻¹ * ∫ ω, f n ω ∂μ := by
  obtain ⟨c, hc⟩ := hlower
  refine csInf_le ⟨c, ?_⟩ ⟨n, hn, rfl⟩
  rintro a ⟨m, hm, rfl⟩
  exact hc m hm

/-- Positive-length normalized values, in the indexing of the subadditive theorem. -/
@[expose]
def kingmanRatio (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (n + 1 : ℝ)⁻¹ * f (n + 1) ω

omit [MeasurableSpace Ω] in
/-- Defining equation of `kingmanRatio`. -/
lemma kingmanRatio_def (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    kingmanRatio f n ω = (n + 1 : ℝ)⁻¹ * f (n + 1) ω := rfl

/-- The extended liminf of the normalized subadditive process. -/
@[expose]
def kingmanLiminf (f : ℕ → Ω → ℝ) (ω : Ω) : EReal :=
  liminf (fun n => (kingmanRatio f n ω : EReal)) atTop

omit [MeasurableSpace Ω] in
/-- Defining equation of `kingmanLiminf`. -/
lemma kingmanLiminf_def (f : ℕ → Ω → ℝ) (ω : Ω) :
    kingmanLiminf f ω = liminf (fun n => (kingmanRatio f n ω : EReal)) atTop := rfl

/-- The extended limsup of the normalized subadditive process. -/
@[expose]
def kingmanLimsup (f : ℕ → Ω → ℝ) (ω : Ω) : EReal :=
  limsup (fun n => (kingmanRatio f n ω : EReal)) atTop

omit [MeasurableSpace Ω] in
/-- Defining equation of `kingmanLimsup`. -/
lemma kingmanLimsup_def (f : ℕ → Ω → ℝ) (ω : Ω) :
    kingmanLimsup f ω = limsup (fun n => (kingmanRatio f n ω : EReal)) atTop := rfl

/-- The real representative of the extended liminf. Infinities are sent to zero. -/
@[expose]
def kingmanLiminfReal (f : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  (kingmanLiminf f ω).toReal

omit [MeasurableSpace Ω] in
/-- Defining equation of `kingmanLiminfReal`. -/
lemma kingmanLiminfReal_def (f : ℕ → Ω → ℝ) (ω : Ω) :
    kingmanLiminfReal f ω = (kingmanLiminf f ω).toReal := rfl

/-- The real representative of the extended limsup. Infinities are sent to zero. -/
@[expose]
def kingmanLimsupReal (f : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  (kingmanLimsup f ω).toReal

omit [MeasurableSpace Ω] in
/-- Defining equation of `kingmanLimsupReal`. -/
lemma kingmanLimsupReal_def (f : ℕ → Ω → ℝ) (ω : Ω) :
    kingmanLimsupReal f ω = (kingmanLimsup f ω).toReal := rfl

/-- The height truncation `max(f n, -K n)`. -/
@[expose]
def kingmanTrunc (K : ℕ) (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  max (f n ω) (-(K : ℝ) * (n : ℝ))

omit [MeasurableSpace Ω] in
/-- Defining equation of `kingmanTrunc`. -/
lemma kingmanTrunc_apply (K : ℕ) (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    kingmanTrunc K f n ω = max (f n ω) (-(K : ℝ) * (n : ℝ)) := rfl

end CKMA
