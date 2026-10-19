# Structure 36: Calculus of variations, Γ-convergence, and homogenization

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS36.md); [bibliographical scope](CKMA-bib.md#ckma-36); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.Calculus.LagrangeMultipliers`, `Mathlib.Analysis.Calculus.LocalExtr.Basic`, `Mathlib.Analysis.Calculus.DerivativeTest`, `Mathlib.Topology.Semicontinuity.Basic`, `Mathlib.Analysis.LocallyConvex.WeakSpace`, `Mathlib.Topology.Sion`.

**Namespaces.** `IsLocalExtrOn` for constrained extrema and `LowerSemicontinuousOn` for compact minimization; Sion's theorem is in `Sion`. In TauCeti, Γ-convergence is `TauCeti.TendstoGamma` with `TauCeti.Equicoercive`, and the Morse lemma is `TauCeti.IsNondegenerateCriticalPoint.exists_morse_chart`.

## First and second variations

[Mathematical scope](SYNOPSIS36.md#first-and-second-variations).

### Mathlib

**Constrained extrema.** Lagrange multipliers are proved for strictly differentiable maps on real Banach spaces (`Analysis/Calculus/LagrangeMultipliers.lean`). If \(\varphi:E\to\mathbb R\) has a local extremum at \(x_0\) subject to \(f(x)=f(x_0)\), where \(f:E\to F\) and \(F\) is Banach, the derivative of \((f,\varphi)\) is not surjective (`IsLocalExtrOn.range_ne_top_of_hasStrictFDerivAt`). There exist an algebraic linear functional \(\Lambda\) on \(F\) and a scalar \(\Lambda_0\), not both zero, with
\[
\Lambda\circ Df(x_0)+\Lambda_0D\varphi(x_0)=0
\]
(`IsLocalExtrOn.exists_linear_map_of_hasStrictFDerivAt`). For finitely many scalar constraints this says that the constraint differentials and the objective differential are linearly dependent (`IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt`, `IsLocalExtrOn.linear_dependent_of_hasStrictFDerivAt`). The theorem allows abnormal multipliers \(\Lambda_0=0\); the normal form \(D\varphi=\lambda\circ Df\) under a surjective constraint derivative is not stated separately.

**Extremum tests.** Fermat's vanishing-derivative condition for an unconstrained local extremum is in `Analysis/Calculus/LocalExtr/Basic.lean`. The first- and second-derivative tests for real functions of one real variable are in `Analysis/Calculus/DerivativeTest.lean` (`isLocalMin_of_deriv_deriv_pos`).

### TauCeti

The necessary second-order condition is proved on real normed spaces: at a local minimum of a function that is \(C^2\) at the point, \(D^2f(x)[w,w]\ge0\) for every \(w\) (`TauCeti.fderiv_fderiv_self_nonneg_of_isLocalMin`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/DerivativeTest.lean)). No sufficient second-order condition in several variables is proved.

In Riemannian geometry, the first variation formula for the energy of a curve is proved, and a curve is a critical point of the energy among variations with fixed endpoints exactly when it is a geodesic (`TauCeti.Manifold.isEnergyCritical_iff_isGeodesicCurveOn`; [first variation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Manifold/Riemannian/FirstVariation.lean), [geodesics](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Manifold/Riemannian/Geodesic/FirstVariation.lean)). This is the Euler–Lagrange equation for one particular one-dimensional Lagrangian. The first-order condition of a Jordan–Kinderlehrer–Otto step on Wasserstein space is derived by perturbing the minimizer along vector fields ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/EulerLagrange.lean)). A general Euler–Lagrange equation for integral functionals \(\int f(x,u,Du)\) is not present.

Two classical variational principles for quadratic forms are proved. The Rayleigh principle: for a bounded coercive symmetric form \(B\) on a Hilbert space \(V\) and a nonzero compact \(J:V\to H\), the least variational eigenvalue is the minimum of \(B(v,v)/\|Jv\|^2\); without compactness it is still the best constant in \(C\|Jv\|^2\le B(v,v)\) (`IsCoercive.isLeast_rayleighQuotient` in TauCeti; [Rayleigh principle](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/Variational/Rayleigh.lean)). This gives the variational characterization of the first Dirichlet eigenvalue in Section 22.

**Synopsis entries.** Partly covered: 36.1 (energy of curves on a Riemannian manifold, whose critical points are the geodesics, and the JKO step only), 36.3 (multiplier rule with a possibly abnormal multiplier, Mathlib), 36.4 (necessary condition for \(C^2\) functions on real normed spaces, TauCeti; sufficient condition only for real functions of one variable, Mathlib). Not covered: 36.2, 36.5–36.9.

## The direct method and lower semicontinuity

[Mathematical scope](SYNOPSIS36.md#the-direct-method-and-lower-semicontinuity).

### Mathlib

The general compactness library supplies attainment of minima for lower-semicontinuous functions on nonempty compact sets (`LowerSemicontinuousOn.exists_isMinOn` in `Topology/Semicontinuity/Basic.lean`); applied to a nonempty compact sublevel set this is the abstract direct method, in its topological rather than sequential form. One ingredient of weak lower semicontinuity is present: in a real locally convex space the weak closure of a convex set equals its closure, and the weak closed convex hull equals the closed convex hull (`Convex.toWeakSpace_closure`, `toWeakSpace_closedConvexHull_eq` in `Analysis/LocallyConvex/WeakSpace.lean`), so norm-closed convex sublevel sets are weakly closed. These support variational arguments but do not establish weak compactness or weak lower semicontinuity for a particular integral functional. The lower semicontinuity of path variation under pointwise convergence is another relevant special case (Section 37).

### TauCeti

The direct method is carried out for the Kantorovich transport problem: weak compactness of the coupling set and lower semicontinuity of the integral cost give an optimal plan for lower-semicontinuous extended-nonnegative cost on Polish spaces (`TauCeti.exists_isOptimalCoupling`; [optimal-plan existence](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/OptimalTransport/Existence/Basic.lean)). This is a concrete variational existence theorem, not a general theory of weak lower semicontinuity of integral functionals. Fenchel conjugates and subdifferentials are recorded in Section 12. The abstract functional-analytic ingredients of the direct method are present: in a reflexive Banach space, closed bounded convex sets are weakly compact (`TauCeti.isCompact_toWeakSpace_of_isClosed_of_convex_of_isBounded`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/Dual/Reflexive/WeakCompact.lean)), and Mazur's lemma turns weak convergence into norm convergence of convex combinations of tails (`TauCeti.exists_tendsto_sum_smul_of_tendsto_weak`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Normed/Module/Mazur.lean)). Reflexivity of \(W^{1,p}\) is not established, so these do not yet give weak Sobolev compactness. Existence and uniqueness of weak solutions of coercive linear Dirichlet problems are obtained from Lax–Milgram, not by minimization (Section 33).

**Synopsis entries.** Covered: 36.10 (Mathlib, topological form). Not covered: 36.11–36.15.

## Quasiconvexity, minors, and relaxation

[Mathematical scope](SYNOPSIS36.md#quasiconvexity-minors-and-relaxation).

**Synopsis entries.** Not covered: 36.16–36.24.

## Young measures and concentration

[Mathematical scope](SYNOPSIS36.md#young-measures-and-concentration).

**Synopsis entries.** Not covered: 36.25–36.29, 36.31, 36.32.

## Critical points and minimax methods

[Mathematical scope](SYNOPSIS36.md#critical-points-and-minimax-methods).

### Mathlib

**Sion's minimax theorem.** Sion's theorem is proved (`Sion.minimax`, `Sion.exists_isSaddlePointOn'`; `Topology/Sion.lean`). For nonempty convex sets \(X,Y\) in real topological vector spaces, with \(X\) compact, lower-semicontinuous quasiconvex sections in \(x\) and upper-semicontinuous quasiconcave sections in \(y\) give the minimax equality, formulated using order bounds and complete-order versions. When both sets are compact, the corresponding saddle-point existence theorem is available. This is a convex minimax theorem, not a critical-point theorem for a nonlinear functional.

### TauCeti

A Morse–Palais normal-form theorem is proved for real functions of class \(C^{n+2}\) on a Banach space: when the Hessian at a critical point is a continuous linear equivalence to the dual, a \(C^n\) local coordinate change makes the function exactly its critical value plus half its Hessian quadratic form (`TauCeti.IsNondegenerateCriticalPoint.exists_morse_chart`, with a local version `TauCeti.IsNondegenerateCriticalPoint.exists_morse_chart_of_contDiffOn`; [Morse lemma](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/Morse/NormalForm.lean)). For negative-gradient flows at a nondegenerate critical point on a finite-dimensional real Hilbert space, the local stable and unstable sets are graphs of Lipschitz \(C^1\) maps tangent at the origin to the Hessian spectral subspaces, homeomorphic to closed balls whose dimensions are the complementary index and the Morse index; their embedded-submanifold structure and globalization along the flow are not established ([local invariant sets](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/Morse/LocalInvariantManifold.lean)). Critical groups are not defined. Real-valued helpers for applying Sion's theorem are in [TauCeti/Topology/Sion.lean](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Topology/Sion.lean).

**Synopsis entries.** Partly covered: 36.66 (Morse–Palais lemma on Banach spaces, TauCeti; critical groups not defined). Not covered: 36.34–36.42, 36.67, 36.68.

## Γ-convergence and variational limits

[Mathematical scope](SYNOPSIS36.md#γ-convergence-and-variational-limits).

### TauCeti

Abstract Γ-convergence is developed for sequences \(F_n:X\to\overline{\mathbb R}\) on a topological space ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Topology/Semicontinuity/GammaConvergence.lean)). `TauCeti.TendstoGamma F f` is the sequential definition (liminf inequality along every convergent sequence and existence of recovery sequences); the lower and upper Γ-limits are defined through neighbourhoods, are lower semicontinuous, and on a first-countable space Γ-convergence is equivalent to both equalling \(f\) (`TauCeti.tendstoGamma_iff_gammaLiminf_eq_and_gammaLimsup_eq`), so a Γ-limit is unique and lower semicontinuous (`TauCeti.TendstoGamma.gammaLiminf_eq`, `TauCeti.TendstoGamma.lowerSemicontinuous`). Γ-convergence passes to subsequences and is stable under adding real functions \(g_n\) that converge continuously to \(g_0\), in particular a fixed continuous function or perturbations tending uniformly to zero (`TauCeti.TendstoGamma.add_tendsto`, `TauCeti.TendstoGamma.add_continuous`). A constant sequence of lower semicontinuous functionals Γ-converges to its value (`LowerSemicontinuous.tendstoGamma_const`). Cluster points of exact minimizers of \(F_n\) minimize \(f\) (`TauCeti.TendstoGamma.isMinOn_of_tendsto`), and the fundamental theorem holds: if the sequence is equicoercive (all sublevel sets \(\{F_n\le t\}\) lie in one compact set) on a first-countable space, then \(\inf F_n\to\inf f\) and, for nonempty \(X\), \(\inf f\) is attained (`TauCeti.TendstoGamma.tendsto_iInf`, `TauCeti.TendstoGamma.exists_isMinOn`).

As an application, if energies \(\Phi_n\) on a pseudometric space Γ-converge to \(\varphi\) and base points converge, the Moreau–Yosida approximations converge and cluster points of resolvent steps are resolvent steps of the limit, under equicoercivity of the penalized energies (`TauCeti.TendstoGamma.tendsto_moreauYosida`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/GradientFlow/MoreauYosida/GammaConvergence.lean)). Mosco convergence is not defined. No concrete Γ-limit (Modica–Mortola, homogenized integrands, Ginzburg–Landau, dimension reduction) is computed.

**Synopsis entries.** Covered: 36.43, 36.47 (TauCeti). Partly covered: 36.44 (convergence of infima and attainment on first-countable spaces; the cluster-point statement is proved for exact minimizers only), 36.48 (only that a lower semicontinuous functional is its own constant-sequence Γ-limit; the lower semicontinuous envelope is not identified), 36.49 (Γ-convergence with equicoercivity gives convergence of Moreau–Yosida values and of cluster points of resolvent steps; no Mosco convergence or Hilbert-space resolvent convergence). Not covered: 36.45, 36.46, 36.50–36.52, 36.69.

## Periodic and stochastic homogenization

[Mathematical scope](SYNOPSIS36.md#periodic-and-stochastic-homogenization).

**Synopsis entries.** Not covered: 36.53–36.63, 36.70.

## Shape optimization

[Mathematical scope](SYNOPSIS36.md#shape-optimization).

**Synopsis entries.** Not covered: 36.71, 36.72.

## Rate-independent evolution

[Mathematical scope](SYNOPSIS36.md#rate-independent-evolution).

**Synopsis entries.** Not covered: 36.73.

## Optimal control as variational continuation

[Mathematical scope](SYNOPSIS36.md#optimal-control-as-variational-continuation).

**Synopsis entries.** Not covered: 36.64, 36.65.
