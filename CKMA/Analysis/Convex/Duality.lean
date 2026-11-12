/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Convex.Basic
public import CKMA.Analysis.Convex.Duality.Choquet
public import CKMA.Analysis.Convex.Duality.KKT
public import TauCeti.Analysis.Convex.FenchelMoreau
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Tactic
public import Mathlib.Topology.Algebra.ContinuousAffineMap
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Choquet measures, convex duality, and multiplier conditions

Choquet representation uses probability measures on a compact metrizable convex set, carried
by its extreme points, and tests barycenters by continuous affine scalar functions. This avoids
assuming Bochner integrability of the ambient identity map.

Subdifferentials and Fenchel conjugates reuse TauCeti's continuous-dual pairing. Extended-real
properness and finite-domain continuity hypotheses control the sum rule and Fenchel–Rockafellar
dual attainment. The finite-dimensional KKT interface separates feasibility from nonnegative
multipliers, stationarity, and complementary slackness; sufficiency holds in any normed space.
Sources: GAPS 12.9, 12.21, 12.39, and 12.40.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped BigOperators Pointwise

/-- **12.9**: every point of a compact metrizable convex set has a probability
representation carried by its extreme points. Evaluation uses continuous affine maps,
so no Bochner integrability of the ambient identity map is silently assumed. -/
theorem exists_choquetMeasure {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    [LocallyConvexSpace ℝ V] [T2Space V]
    (K : Set V) (hK : IsCompact K) (hc : Convex ℝ K)
    [TopologicalSpace.MetrizableSpace K] [MeasurableSpace K] [BorelSpace K] (x : K) :
    ∃ μ : Measure K, IsProbabilityMeasure μ ∧
      μ {y : K | y.1 ∉ Set.extremePoints ℝ K} = 0 ∧
      ∀ a : V →ᴬ[ℝ] ℝ, (∫ y : K, a y.1 ∂μ) = a x.1 :=
  exists_choquetMeasure_of_compact K hK hc x

section Banach

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The dual-valued subdifferential of an extended-real function, reusing TauCeti's
pairing-based definition. The pairing is evaluation by the continuous dual. -/
def dualSubdifferential (f : E → EReal) (x : E) : Set (StrongDual ℝ E) :=
  TauCeti.subdifferential (topDualPairing ℝ E).flip f x

/-- Real-valued convex subgradients, expressed as a specialization of the same definition. -/
def realSubdifferential (f : E → ℝ) (x : E) : Set (StrongDual ℝ E) :=
  dualSubdifferential (fun y ↦ (f y : EReal)) x

/-- Real-valued subgradients satisfy the ordinary real supporting-line inequality.
This adapter is TauCeti's `mem_subdifferential_coe_iff` at the continuous-dual pairing. -/
theorem mem_realSubdifferential_iff {f : E → ℝ} {x : E} {u : StrongDual ℝ E} :
    u ∈ realSubdifferential f x ↔ ∀ z, f x + u (z - x) ≤ f z :=
  TauCeti.mem_subdifferential_coe_iff (topDualPairing ℝ E).flip f

/-- **12.21**: the Banach-space sum rule with a common finite-domain continuity point.
The relative-interior alternative in finite dimensions is a separate target. -/
theorem dualSubdifferential_add [CompleteSpace E] {f g : E → EReal}
    (hf : IsProperERealFunction f) (hg : IsProperERealFunction g)
    (hlf : LowerSemicontinuous f) (hlg : LowerSemicontinuous g)
    (hcf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hcg : Convex ℝ {p : E × ℝ | g p.1 ≤ p.2})
    {x₀ : E} (hfin : f x₀ ≠ ⊤ ∧ g x₀ ≠ ⊤) (hcont : ContinuousAt g x₀) (x : E) :
    dualSubdifferential (fun y ↦ f y + g y) x =
      dualSubdifferential f x + dualSubdifferential g x := by
  let _ := hlf
  let _ := hlg
  have _ := ‹CompleteSpace E›
  simpa [dualSubdifferential] using
    subdifferential_add_eq hf hg hcf hcg hfin hcont x

/-- The primal Fenchel value, in extended reals. -/
def fenchelPrimalValue (f : E → EReal) (g : F → EReal) (A : E →L[ℝ] F) : EReal :=
  ⨅ x, f x + g (A x)

/-- The Fenchel dual objective. The sign is on the pulled-back dual variable,
matching `-f*(-A* u)-g*(u)`. -/
def fenchelDualValue (f : E → EReal) (g : F → EReal) (A : E →L[ℝ] F)
    (u : StrongDual ℝ F) : EReal :=
  -TauCeti.fenchelConjugate (topDualPairing ℝ E).flip f ((-u).comp A) -
    TauCeti.fenchelConjugate (topDualPairing ℝ F).flip g u

/-- **12.39**: Fenchel–Rockafellar equality and dual attainment.
Primal attainment is deliberately not asserted. The continuity point belongs to both
finite domains, and the primal infimum is a finite real value. -/
theorem exists_fenchelDual_maximizer [CompleteSpace E] [CompleteSpace F]
    {f : E → EReal} {g : F → EReal} (A : E →L[ℝ] F)
    (hf : IsProperERealFunction f) (hg : IsProperERealFunction g)
    (hlf : LowerSemicontinuous f) (hlg : LowerSemicontinuous g)
    (hcf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hcg : Convex ℝ {p : F × ℝ | g p.1 ≤ p.2})
    {x₀ : E} (hfin : f x₀ ≠ ⊤ ∧ g (A x₀) ≠ ⊤) (hcont : ContinuousAt g (A x₀))
    (hval : fenchelPrimalValue f g A ≠ ⊥ ∧ fenchelPrimalValue f g A ≠ ⊤) :
    ∃ u : StrongDual ℝ F, fenchelPrimalValue f g A = fenchelDualValue f g A u ∧
      ∀ v, fenchelDualValue f g A v ≤ fenchelDualValue f g A u := by
  let _ := hlf
  let _ := hlg
  have _ := ‹CompleteSpace E›
  have _ := ‹CompleteSpace F›
  have hval' : marginalValue f g A 0 ≠ ⊥ ∧ marginalValue f g A 0 ≠ ⊤ := by
    have hEq : marginalValue f g A 0 = fenchelPrimalValue f g A := by
      simp [marginalValue, fenchelPrimalValue, add_zero]
    rw [hEq]
    exact hval
  simpa [fenchelPrimalValue, fenchelDualValue, marginalValue, add_zero] using
    exists_fenchelDual_maximizer_of_qual A hf hg hcf hcg hfin hcont hval'

/-- Feasibility for finitely many convex inequalities and affine equalities. -/
def convexFeasibleSet {m n : ℕ} (g : Fin n → E → ℝ)
    (A : E →L[ℝ] (Fin m → ℝ)) (b : Fin m → ℝ) : Set E :=
  {x | (∀ i, g i x ≤ 0) ∧ A x = b}

/-- Subgradient KKT data, including nonnegative multipliers, stationarity and
complementary slackness. Feasibility is kept separate. -/
def HasConvexKKTMultipliers {m n : ℕ} (f : E → ℝ) (g : Fin n → E → ℝ)
    (A : E →L[ℝ] (Fin m → ℝ)) (x : E) : Prop :=
  ∃ (c : Fin n → ℝ) (u : StrongDual ℝ E)
    (v : Fin n → StrongDual ℝ E) (y : StrongDual ℝ (Fin m → ℝ)),
    (∀ i, 0 ≤ c i) ∧ u ∈ realSubdifferential f x ∧
    (∀ i, v i ∈ realSubdifferential (g i) x) ∧
    u + (∑ i, c i • v i) + y.comp A = 0 ∧ ∀ i, c i * g i x = 0

/-- **12.40**: strict feasibility gives KKT multipliers at every finite-dimensional minimizer.
The objective and inequality constraints are finite convex functions. -/
theorem exists_convexKKTMultipliers [FiniteDimensional ℝ E] {m n : ℕ}
    (f : E → ℝ) (g : Fin n → E → ℝ) (A : E →L[ℝ] (Fin m → ℝ)) (b : Fin m → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hslater : ∃ x₀, A x₀ = b ∧ ∀ i, g i x₀ < 0) {x : E}
    (hx : x ∈ convexFeasibleSet g A b)
    (hmin : ∀ z ∈ convexFeasibleSet g A b, f x ≤ f z) :
    HasConvexKKTMultipliers f g A x := by
  obtain ⟨c, u, v, y, hc, hu, hv, hstat, hcomp⟩ :=
    exists_convexKKTMultipliers_of_slater f g A b hf hg hslater
      (by simpa [convexFeasibleSet] using hx)
      (by
        intro z hgz hAz
        exact hmin z (by simpa [convexFeasibleSet] using And.intro hgz hAz))
  refine ⟨c, u, v, y, hc, ?_, ?_, hstat, hcomp⟩
  · simpa [realSubdifferential, dualSubdifferential] using hu
  · intro i
    simpa [realSubdifferential, dualSubdifferential] using hv i

/-- KKT conditions are sufficient even without Slater's condition, in any normed space. -/
theorem HasConvexKKTMultipliers.isMinOn {m n : ℕ}
    {f : E → ℝ} {g : Fin n → E → ℝ} {A : E →L[ℝ] (Fin m → ℝ)} {b : Fin m → ℝ}
    {x : E} (hKKT : HasConvexKKTMultipliers f g A x) (hx : x ∈ convexFeasibleSet g A b) :
    ∀ z ∈ convexFeasibleSet g A b, f x ≤ f z := by
  obtain ⟨c, u, v, y, hc, hu, hv, hstat, hcomp⟩ := hKKT
  intro z hz
  have hobj := (mem_realSubdifferential_iff.mp hu) z
  have hver : ∀ i, c i * v i (z - x) ≤ 0 := by
    intro i
    have hsub := (mem_realSubdifferential_iff.mp (hv i)) z
    have hscaled := mul_le_mul_of_nonneg_left hsub (hc i)
    have hfeas := mul_nonpos_of_nonneg_of_nonpos (hc i) (hz.1 i)
    have hcompl := hcomp i
    nlinarith
  have hsum : (∑ i, c i * v i (z - x)) ≤ 0 :=
    Finset.sum_nonpos (fun i _ ↦ hver i)
  have heq : u (z - x) + (∑ i, c i * v i (z - x)) = 0 := by
    have heval := congrArg (fun ℓ : StrongDual ℝ E ↦ ℓ (z - x)) hstat
    simp [map_sub, hx.2, hz.2] at heval
    simp only [map_sub, mul_sub, Finset.sum_sub_distrib]
    linarith
  linarith

end Banach

end CKMA
