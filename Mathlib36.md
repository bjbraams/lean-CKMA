# 36. Calculus of Variations, Γ-Convergence, and Homogenization

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. Relevant foundations include `Mathlib.Analysis.Calculus.LagrangeMultipliers`, `Mathlib.Analysis.Calculus.LocalExtr.Basic`, and `Mathlib.Topology.Semicontinuity.Basic`.

**Namespaces.** `IsLocalExtrOn` for constrained extrema and `LowerSemicontinuousOn` for compact minimization.

The checkout contains variational foundations, including constrained-extremum theorems, but no developed calculus of integral functionals. No direct-method package, Palais–Smale condition, Γ-convergence, homogenization theorem, Young measure, or general weak lower-semicontinuity theorem for convex integral functionals was found.

## Constrained extrema and compact minimization

Lagrange multipliers are proved for strictly differentiable maps on real Banach spaces (`Analysis/Calculus/LagrangeMultipliers.lean`). If \(\varphi:E\to\mathbb R\) has a local extremum at \(x_0\) subject to \(f(x)=f(x_0)\), where \(f:E\to F\) and \(F\) is Banach, the derivative of \((f,\varphi)\) is not surjective. There exist an algebraic linear functional \(\Lambda\) on \(F\) and a scalar \(\Lambda_0\), not both zero, with
\[
\Lambda\circ Df(x_0)+\Lambda_0D\varphi(x_0)=0.
\]
For finitely many scalar constraints this says that the constraint differentials and the objective differential are linearly dependent. The theorem allows abnormal multipliers \(\Lambda_0=0\); it does not silently assume a constraint qualification. Karush–Kuhn–Tucker is a TODO.

Fermat’s vanishing-derivative condition for an unconstrained local extremum is in `Analysis/Calculus/LocalExtr/Basic.lean`. The general compactness library supplies attainment of minima for lower-semicontinuous real functions on nonempty compact sets (`Topology/Semicontinuity/Basic.lean`, `LowerSemicontinuousOn.exists_isMinOn`). These can support variational arguments, but do not establish weak compactness and weak lower semicontinuity for a particular integral functional. The lower semicontinuity of path variation under pointwise convergence is another relevant special case (Section 37).

## Sion's minimax theorem

Sion's theorem is already proved in this Mathlib revision (`Topology/Sion.lean`). For nonempty convex sets \(X,Y\) in real topological vector spaces, with \(X\) compact, lower-semicontinuous quasiconvex sections in \(x\) and upper-semicontinuous quasiconcave sections in \(y\) give the minimax equality, formulated using order bounds and complete-order versions. When both sets are compact, the corresponding saddle-point existence theorem is available. This is a convex minimax theorem, not the mountain-pass theorem for critical points of a nonlinear functional.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

A Morse–Palais normal-form theorem is proved for smooth real functions on a Banach space: when the Hessian at a critical point is a continuous linear equivalence to the dual, a smooth local coordinate change makes the function exactly its Hessian quadratic form plus its critical value ([Morse lemma](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Calculus/Morse/NormalForm.lean)). For finite-dimensional negative-gradient flows, local stable/unstable sets are Lipschitz graphs tangent to the Hessian spectral subspaces; the file does not establish smoothness of those graphs away from the critical point ([local invariant sets](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Calculus/Morse/LocalInvariantManifold.lean)).

The direct method is carried out for the Kantorovich transport problem: weak compactness of the coupling set and lower semicontinuity of the integral cost give an optimal plan for lower-semicontinuous extended-nonnegative cost on Polish spaces ([optimal-plan existence](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/MeasureTheory/OptimalTransport/Existence.lean)). This is a concrete variational existence theorem, not a general theory of weak lower semicontinuity of integral functionals, Γ-convergence, or homogenization. Fenchel conjugates and subdifferentials are recorded in Section 12.

## Topics of Section 36 not found in either inspected library

- A general direct-method theory for integral functionals, weak lower semicontinuity under quasiconvexity, and related relaxation theorems. Optimal-transport minimization is proved in TauCeti.
- The Palais–Smale condition and mountain-pass critical-point theorems. Sion’s convex minimax theorem is already in Mathlib.
- Γ-convergence and homogenization.
- Young measures.
