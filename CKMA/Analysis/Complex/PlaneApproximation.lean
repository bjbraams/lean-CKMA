/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Plane approximation and prescribed analytic data

Plane domains and relatively locally finite sets support isolated-singularity and
prescribed-divisor interfaces. Great Picard describes essential singularities.
Runge approximation permits specified poles in bounded complementary components;
Mergelyan approximation permits compact sets with empty interior. Mittag–Leffler
principal parts and positive zero divisors are realized by meromorphic and holomorphic
functions, respectively.

Sources: GAPS 40.29 and 40.60–40.64.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology Polynomial

/-- A nonempty connected open subset of the complex plane. -/
def IsPlaneDomain (Ω : Set ℂ) : Prop := Ω.Nonempty ∧ IsOpen Ω ∧ IsPreconnected Ω

/-- Local finiteness relative to an open set, formulated on all compact subsets. -/
def IsLocallyFiniteIn (s Ω : Set ℂ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → (s ∩ K).Finite

/-- Restricting a locally finite set preserves local finiteness. -/
theorem IsLocallyFiniteIn.mono {s t Ω : Set ℂ} (hs : IsLocallyFiniteIn s Ω) (ht : t ⊆ s) :
    IsLocallyFiniteIn t Ω := by
  intro K hK hKΩ
  exact (hs K hK hKΩ).subset (Set.inter_subset_inter_left K ht)

/-- Finite sets are locally finite in any plane region. -/
theorem isLocallyFiniteIn_of_finite {s Ω : Set ℂ} (hs : s.Finite) :
    IsLocallyFiniteIn s Ω := by
  intro K hK hKΩ
  exact hs.inter_of_left K

/-- An essential isolated singularity, with the function holomorphic on its punctured disk. -/
def HasEssentialSingularityAt (f : ℂ → ℂ) (a : ℂ) (R : ℝ) : Prop :=
  0 < R ∧ DifferentiableOn ℂ f {z | 0 < ‖z - a‖ ∧ ‖z - a‖ < R} ∧ ¬ MeromorphicAt f a

/-- **40.29**, holomorphic Great Picard: all but at most one finite value have infinitely
many preimages in every punctured neighborhood. The meromorphic two-exception version remains. -/
theorem great_picard {f : ℂ → ℂ} {a : ℂ} {R : ℝ}
    (hf : HasEssentialSingularityAt f a R) :
    ∃ exceptional : ℂ, ∀ w : ℂ, w ≠ exceptional → ∀ r : ℝ, 0 < r → r < R →
      {z : ℂ | 0 < ‖z - a‖ ∧ ‖z - a‖ < r ∧ f z = w}.Infinite := by
  sorry

/-- Prescribed finite poles meet every bounded complementary component; the polynomial part
is allowed, which is the same as permitting a pole at infinity. -/
def MeetsBoundedComplementaryComponents (P K : Set ℂ) : Prop :=
  P ⊆ Kᶜ ∧ ∀ z ∈ Kᶜ, Bornology.IsBounded (connectedComponentIn Kᶜ z) →
    (P ∩ connectedComponentIn Kᶜ z).Nonempty

/-- **40.60**: Runge approximation when infinity is an allowed pole.
Every zero of the approximant's denominator lies in the prescribed finite-pole set. -/
theorem runge_approximation {K U P : Set ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hP : MeetsBoundedComplementaryComponents P K)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z : ℂ, q.eval z = 0 → z ∈ P) ∧
      ∀ z ∈ K, q.eval z ≠ 0 ∧ ‖f z - p.eval z / q.eval z‖ < ε := by
  sorry

/-- **40.62**: Mergelyan approximation, including compact sets with empty interior. -/
theorem mergelyan_approximation {K : Set ℂ} (hK : IsCompact K)
    (hconn : IsPreconnected Kᶜ) {f : ℂ → ℂ} (hc : ContinuousOn f K)
    (hf : DifferentiableOn ℂ f (interior K)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  sorry

/-- A finite principal part centered at a point, polynomial in the reciprocal coordinate.
The constant term is required to vanish by the Mittag–Leffler theorem's hypotheses. -/
def finitePrincipalPart (a : ℂ) (p : ℂ[X]) (z : ℂ) : ℂ := p.eval ((z - a)⁻¹)

/-- **40.63**: arbitrary locally finite principal parts on a plane domain are realized by
one meromorphic function. Equality to the principal part is modulo an analytic germ. -/
theorem exists_mittagLeffler {Ω A : Set ℂ} (hΩ : IsPlaneDomain Ω) (hAΩ : A ⊆ Ω)
    (hA : IsLocallyFiniteIn A Ω) (p : A → ℂ[X]) (hp : ∀ a, (p a).coeff 0 = 0) :
    ∃ f : ℂ → ℂ, MeromorphicOn f Ω ∧ DifferentiableOn ℂ f (Ω \ A) ∧
      ∀ a : A, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a.1 ∧
        ∀ᶠ z in 𝓝[≠] a.1, f z - finitePrincipalPart a.1 (p a) z = g z := by
  sorry

/-- **40.64**: every locally finite positive zero divisor on a plane domain is realized.
Orders use Mathlib's analytic order, not a separate multiplicity convention. -/
theorem exists_holomorphic_prescribed_zeros {Ω A : Set ℂ} (hΩ : IsPlaneDomain Ω)
    (hAΩ : A ⊆ Ω) (hA : IsLocallyFiniteIn A Ω) (m : A → ℕ) (hm : ∀ a, 0 < m a) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧
      (∀ z ∈ Ω, f z = 0 ↔ z ∈ A) ∧
      ∀ a : A, analyticOrderAt f a.1 = (m a : ℕ∞) := by
  sorry

end CKMA
