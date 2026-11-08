/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Accretive resolvents and nonlinear contraction semigroups

Accretive and m-accretive multivalued graphs on real normed spaces, their nonlinear
resolvents and implicit Euler products. The resolvent is the identity at scale zero
and a contraction at positive scales. In a Banach space, Crandall–Liggett convergence
generates a contraction semigroup on the closure of the graph domain, uniformly on
bounded time intervals for domain initial values. Source: GAPS 24.52.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped NNReal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The domain of a possibly multivalued operator graph. -/
def accretiveGraphDomain (G : Set (X × X)) : Set X := {x | ∃ u, (x, u) ∈ G}

/-- Accretivity of a graph in a real Banach space, stated by the resolvent norm inequality. -/
def IsAccretiveGraph (G : Set (X × X)) : Prop :=
  ∀ p ∈ G, ∀ q ∈ G, ∀ t : ℝ, 0 < t → ‖p.1 - q.1‖ ≤ ‖p.1 - q.1 + t • (p.2 - q.2)‖

/-- Maximal accretivity includes surjectivity of every positive resolvent. -/
def IsMAccretiveGraph (G : Set (X × X)) : Prop :=
  IsAccretiveGraph G ∧ ∀ t : ℝ, 0 < t → ∀ x : X, ∃ y u : X, (y, u) ∈ G ∧ x = y + t • u

/-- The nonlinear resolvent, with explicit totalizations: the identity at zero scale, and
zero if no graph preimage exists. Under maximal accretivity the latter branch is never used. -/
def accretiveResolvent (G : Set (X × X)) (t : ℝ) (x : X) : X := by
  classical
  exact if t = 0 then x else
    if h : ∃ y u : X, (y, u) ∈ G ∧ x = y + t • u then Classical.choose h else 0

/-- The implicit Euler product with `n+1` resolvent steps, including exact zero-time identity. -/
def accretiveEulerProduct (G : Set (X × X)) (t : ℝ≥0) (n : ℕ) (x : X) : X :=
  (accretiveResolvent G ((t : ℝ) / (n + 1 : ℝ)))^[n + 1] x

omit [CompleteSpace X] in
/-- The zero-scale totalization is the identity. -/
theorem accretiveResolvent_zero (G : Set (X × X)) (x : X) : accretiveResolvent G 0 x = x := by
  classical
  simp [accretiveResolvent]

omit [CompleteSpace X] in
/-- The resolvent of an m-accretive graph is a contraction at every positive scale. -/
theorem accretiveResolvent_lipschitz {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {t : ℝ} (ht : 0 < t) : LipschitzWith 1 (accretiveResolvent G t) := by
  classical
  have hr (x : X) : ∃ u, (accretiveResolvent G t x, u) ∈ G ∧
      x = accretiveResolvent G t x + t • u := by
    have hx := hG.2 t ht x
    simpa only [accretiveResolvent, ht.ne', ite_false, dite_eq_left hx] using
      Classical.choose_spec hx
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  obtain ⟨u, hu, hx⟩ := hr x
  obtain ⟨v, hv, hy⟩ := hr y
  have h := hG.1 _ hu _ hv t ht
  calc ‖accretiveResolvent G t x - accretiveResolvent G t y‖ ≤
      ‖accretiveResolvent G t x - accretiveResolvent G t y + t • (u - v)‖ := h
    _ = ‖x - y‖ := by
      congr 1
      calc accretiveResolvent G t x - accretiveResolvent G t y + t • (u-v) =
          (accretiveResolvent G t x + t • u) - (accretiveResolvent G t y + t • v) := by module
        _ = x-y := by rw [← hx, ← hy]

/-- **24.52**, Crandall–Liggett: implicit Euler products generate a nonlinear contraction
semigroup on the closure of the graph domain. Uniform time convergence is asserted on the domain,
and pointwise convergence is asserted for every initial value in its closure. -/
theorem crandall_liggett {G : Set (X × X)} (hG : IsMAccretiveGraph G) :
    ∃ S : ℝ≥0 → X → X,
      (∀ t, Set.MapsTo (S t) (closure (accretiveGraphDomain G)) (closure (accretiveGraphDomain G)))
        ∧
      (∀ x ∈ closure (accretiveGraphDomain G), S 0 x = x) ∧
      (∀ s t x, x ∈ closure (accretiveGraphDomain G) → S (s + t) x = S s (S t x)) ∧
      (∀ t x y, x ∈ closure (accretiveGraphDomain G) → y ∈ closure (accretiveGraphDomain G) →
        ‖S t x - S t y‖ ≤ ‖x - y‖) ∧
      (∀ x ∈ closure (accretiveGraphDomain G), Continuous (fun t ↦ S t x)) ∧
      (∀ x ∈ closure (accretiveGraphDomain G), ∀ t, Tendsto
        (fun n ↦ accretiveEulerProduct G t n x) atTop (𝓝 (S t x))) ∧
      ∀ x ∈ accretiveGraphDomain G, ∀ R : ℝ≥0, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ R → ‖accretiveEulerProduct G t n x - S t x‖ < ε := by
  sorry

end CKMA
