/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.FunctionalAnalysis.Basic
public import Mathlib.Analysis.Convex.Uniform
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import CKMA.Analysis.FunctionalAnalysis.WeakCompactness.DunfordPettis.Converse
public import CKMA.Analysis.FunctionalAnalysis.WeakCompactness.EberleinSmulian
public import CKMA.Analysis.FunctionalAnalysis.WeakCompactness.LpUniform

/-!
# Weak compactness and scalar Lp geometry

Weak convergence and weak Cauchy sequences are tested by continuous scalar-valued linear
functionals. Relative weak compactness retains limits in the ambient space, so an original set
need not contain its subsequential limits. Eberlein–Šmulian relates these notions; James's
criterion concerns attainment of real continuous linear functionals on closed convex sets.

Scalar Lp uniform convexity includes every exponent strictly between one and infinity, including
two. On finite measure spaces, Dunford–Pettis uses Mathlib's uniform-integrability predicate,
which includes a uniform L1 bound. Sources: GAPS 15.28, 15.29, 15.33, and 17.23.

## Main results

* `CKMA.eberlein_smulian`: weak relative compactness is equivalent to weak sequential relative
  compactness (**15.28**).
* `CKMA.isCompact_toWeakSpace_image_of_forall_exists_max`: James's weak compactness criterion
  (**15.29**).
* `CKMA.uniformConvexSpace_lp`: uniform convexity of `Lp 𝕜 p μ` for `1 < p < ∞` (**15.33**).
* `CKMA.dunford_pettis`: Dunford–Pettis characterization of relative weak compactness in `L¹`
  (**17.23**).
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology MeasureTheory
open scoped ENNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **15.28**, Eberlein–Šmulian: weak relative compactness is weak sequential relative compactness.
The subsequence limit is in the ambient Banach space, not necessarily in `s`. -/
theorem eberlein_smulian [CompleteSpace E] (s : Set E) :
    IsRelativelyWeaklyCompact 𝕜 s ↔
      ∀ u : ℕ → E, (∀ n, u n ∈ s) →
        ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ x : E, WeaklyConverges 𝕜 (u ∘ r) x := by
  simpa [IsRelativelyWeaklyCompact, WeaklyConverges, weaklyTendsto_iff_tendsto] using
    EberleinSmulian.eberlein_smulian (𝕜 := 𝕜) s

omit [NormedSpace 𝕜 E] in
/-- **15.29**, the sufficiency direction of James's compactness theorem over the real scalars.
Attainment of every real functional supplies boundedness, so no separate bound is assumed. -/
theorem isCompact_toWeakSpace_image_of_forall_exists_max [NormedSpace ℝ E]
    [CompleteSpace E] {s : Set E}
    (hc : IsClosed s) (hv : Convex ℝ s)
    (hattain : ∀ ℓ : E →L[ℝ] ℝ, ∃ x ∈ s, ∀ y ∈ s, ℓ y ≤ ℓ x) :
    IsCompact (toWeakSpace ℝ E '' s) := by
  sorry

/-- **15.33**: scalar Lp is uniformly convex for every exponent strictly between one and infinity.
The Hilbert exponent is included in the interface rather than unnecessarily excluded. -/
theorem uniformConvexSpace_lp {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p < ∞) :
    UniformConvexSpace (Lp 𝕜 p μ) :=
  WeakCompactness.uniformConvexSpace_lp (μ := μ) hp hp_top

/-- **17.23**, Dunford–Pettis: relative weak compactness of an L1 family on a finite measure
space is precisely uniform integrability, including the uniform L1 bound in Mathlib's predicate. -/
theorem dunford_pettis {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (s : Set (Lp 𝕜 1 μ)) :
    IsRelativelyWeaklyCompact 𝕜 s ↔
      UniformIntegrable (fun f : s ↦ (f.1 : X → 𝕜)) 1 μ := by
  simpa [IsRelativelyWeaklyCompact] using
    WeakCompactness.dunford_pettis (μ := μ) s

end CKMA
