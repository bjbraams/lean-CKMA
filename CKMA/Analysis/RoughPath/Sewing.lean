/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Sewing and Young integration

Ordered partitions allow repeated nodes and degenerate intervals. Their mesh and
increment sums define sewing limits with a normalized continuous primitive and a
quantitative remainder for defect exponent greater than one. Young integration is
stated for Hölder paths and for continuous paths of complementary finite variation
exponents. Hölder predicates and compact continuous maps use Mathlib.
Sources: GAPS 09.21 and 09.22.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped BigOperators NNReal ENNReal

/-- An ordered finite partition, allowing repeated nodes and the degenerate interval. -/
structure OrderedIntervalPartition (a b : ℝ) where
  /-- Number of increments. -/
  size : ℕ
  /-- Nodes including both endpoints. -/
  node : Fin (size + 1) → ℝ
  /-- Nodes are ordered. -/
  monotone_node : Monotone node
  /-- Left endpoint. -/
  node_zero : node 0 = a
  /-- Right endpoint. -/
  node_last : node (Fin.last size) = b

/-- The maximal partition width. -/
def OrderedIntervalPartition.mesh {a b : ℝ} (π : OrderedIntervalPartition a b) : ℝ≥0 :=
  Finset.univ.sup (fun i : Fin π.size ↦ (π.node i.succ - π.node i.castSucc).toNNReal)

/-- The sum of two-parameter increments along a partition. -/
def OrderedIntervalPartition.incrementSum {a b : ℝ} {E : Type*} [AddCommMonoid E]
    (π : OrderedIntervalPartition a b) (A : ℝ → ℝ → E) : E :=
  ∑ i : Fin π.size, A (π.node i.castSucc) (π.node i.succ)

/-- Convergence of all ordered partition sums as their mesh tends to zero. -/
def PartitionSumsConverge {E : Type*} [NormedAddCommGroup E]
    (A : ℝ → ℝ → E) (a b : ℝ) (z : E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ π : OrderedIntervalPartition a b,
    (π.mesh : ℝ) < δ → ‖π.incrementSum A - z‖ < ε

/-- Geometric sewing constant, finite and positive for exponents strictly greater than one. -/
def sewingConstant (γ : ℝ) : ℝ := (1 - (2 : ℝ) ^ (1 - γ))⁻¹

/-- A continuous interval path is normalized at the left endpoint. -/
def IsLeftNormalized {E : Type*} [TopologicalSpace E] [Zero E] {a b : ℝ}
    (I : C(Set.Icc a b, E)) : Prop := ∀ x : Set.Icc a b, x.val = a → I x = 0

/-- A path's additive increments approximate a given increment field to order `γ`. -/
def HasSewingRemainder {E : Type*} [NormedAddCommGroup E] {a b : ℝ}
    (A : ℝ → ℝ → E) (I : C(Set.Icc a b, E)) (γ C : ℝ) : Prop :=
  ∀ s t : Set.Icc a b, s.val ≤ t.val →
    ‖(I t - I s) - A s.val t.val‖ ≤ C * |t.val - s.val| ^ γ

/-- The path's increments are limits of all partition sums on each subinterval. -/
def HasPartitionSumLimit {E : Type*} [NormedAddCommGroup E] {a b : ℝ}
    (A : ℝ → ℝ → E) (I : C(Set.Icc a b, E)) : Prop :=
  ∀ s t : Set.Icc a b, s.val ≤ t.val → PartitionSumsConverge A s.val t.val (I t - I s)

/-- **09.22**: the sewing lemma with a normalized continuous primitive.
Uniqueness is on the interval, so arbitrary extensions outside it cannot cause false uniqueness. -/
theorem sewing_lemma {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {a b γ C : ℝ} (hab : a ≤ b) (hγ : 1 < γ) (hC : 0 ≤ C) (A : ℝ → ℝ → E)
    (hcont : ContinuousOn (fun p : ℝ × ℝ ↦ A p.1 p.2)
      {p | a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b})
    (hdiag : ∀ s ∈ Set.Icc a b, A s s = 0)
    (hdefect : ∀ s u t : ℝ, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ‖A s t - A s u - A u t‖ ≤ C * |t - s| ^ γ) :
    ∃! I : C(Set.Icc a b, E), IsLeftNormalized I ∧
      HasSewingRemainder A I γ (sewingConstant γ * C) ∧ HasPartitionSumLimit A I := by
  sorry

/-- The field of left-point Young increments for an operator-valued integrand. -/
def youngIncrement {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (X : ℝ → E) (Y : ℝ → E →L[ℝ] F) (s t : ℝ) : F := Y s (X t - X s)

/-- **09.21**: Holder Young integration with the Young–Loeve remainder estimate. -/
theorem young_holder {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {a b : ℝ} (hab : a ≤ b) {α β Hx Hy : ℝ≥0}
    (hα : 0 < α) (hβ : 0 < β) (hαβ : 1 < α + β)
    (X : ℝ → E) (Y : ℝ → E →L[ℝ] F)
    (hX : HolderOnWith Hx α X (Set.Icc a b))
    (hY : HolderOnWith Hy β Y (Set.Icc a b)) :
    ∃! I : C(Set.Icc a b, F), IsLeftNormalized I ∧
      HasPartitionSumLimit (youngIncrement X Y) I ∧
      HasSewingRemainder (youngIncrement X Y) I (α + β : ℝ≥0)
        (sewingConstant (α + β : ℝ≥0) * Hx * Hy) := by
  sorry

/-- The `p`th power variation, retaining infinite variation. -/
def pathVariationPower {E : Type*} [SeminormedAddCommGroup E]
    (p : ℝ) (X : ℝ → E) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ π : OrderedIntervalPartition a b, ∑ i : Fin π.size,
    ENNReal.ofReal (‖X (π.node i.succ) - X (π.node i.castSucc)‖ ^ p)

/-- Young integration for continuous paths of complementary finite variation exponents. -/
theorem young_variation {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {a b p q : ℝ} (hab : a ≤ b) (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : 1 < p⁻¹ + q⁻¹)
    (X : ℝ → E) (Y : ℝ → E →L[ℝ] F)
    (hX : ContinuousOn X (Set.Icc a b)) (hY : ContinuousOn Y (Set.Icc a b))
    (hVp : pathVariationPower p X a b ≠ ∞) (hVq : pathVariationPower q Y a b ≠ ∞) :
    ∃! I : C(Set.Icc a b, F), IsLeftNormalized I ∧
      HasPartitionSumLimit (youngIncrement X Y) I ∧
      ∀ s t : Set.Icc a b, s.val ≤ t.val →
        ‖(I t - I s) - youngIncrement X Y s.val t.val‖ ≤
          sewingConstant (p⁻¹ + q⁻¹) *
            (pathVariationPower p X s.val t.val).toReal ^ p⁻¹ *
            (pathVariationPower q Y s.val t.val).toReal ^ q⁻¹ := by
  sorry

end CKMA
