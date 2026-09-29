# 45. Several Complex Variables, Complex Manifolds, Pluripotential Theory, and CR Analysis

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** The foundations include `Mathlib.Analysis.Analytic.Basic`, `Mathlib.Analysis.Analytic.Composition`, `Mathlib.Analysis.Analytic.Inverse`, `Mathlib.Analysis.Calculus.FDeriv.Analytic`, `Mathlib.Geometry.Manifold.IsManifold.Basic`, and `Mathlib.Geometry.Manifold.Complex`.

**Namespaces.** Analytic maps use `FormalMultilinearSeries`, `HasFPowerSeriesAt`, `AnalyticAt`, and `AnalyticOnNhd`. Complex differentiability uses `DifferentiableAt` and `DifferentiableOn` with scalar field \(\mathbb C\). On manifolds the corresponding predicates are `MDifferentiable`, `MDifferentiableOn`, and `ContMDiff`.

There are foundations for analysis in several complex variables: analytic maps and Fréchet differentiation on complex normed spaces, including \(\mathbb C^n\), and holomorphic maps on complex manifolds. The specialized SCV theory of Hartogs extension, pseudoconvexity, the \(\overline\partial\) equation, and pluripotential theory was not found.

## Analytic maps in arbitrary dimension

Analyticity is defined by locally convergent series of continuous multilinear maps:
\[
f(x+h)=\sum_{n\ge0}p_n(h,\ldots,h).
\]
This works in finite or infinite dimension, not just for functions of a single scalar variable (`Analysis/Analytic/Basic.lean`). Analytic maps are stable under composition (`Analysis/Analytic/Composition.lean`). The calculus connects these series with Fréchet derivatives: an analytic map is differentiable, and the first multilinear term gives its derivative (`Analysis/Calculus/FDeriv/Analytic.lean`). The spaces of multilinear coefficients need not be restricted to symmetric representatives in the underlying definition.

The analytic inverse theory constructs inverse power series with positive convergence radius when the linear term is invertible. For an open partial homeomorphism with such an expansion, its local inverse is analytic (`Analysis/Analytic/Inverse.lean`, `OpenPartialHomeomorph.hasFPowerSeriesAt_symm`; `Analysis/Calculus/FDeriv/Analytic.lean`, `OpenPartialHomeomorph.analyticAt_symm`). The Banach-space inverse and implicit function theorems are described in Section 35.

These foundations should not be confused with a proof of every classical characterization of holomorphy in several variables. In particular, the one-variable Cauchy-integral proof of differentiability implying a power-series expansion does not by itself establish Hartogs’s theorem on separate holomorphy.

## Complex manifolds and the maximum principle

The general atlas and smooth-map framework can be used over \(\mathbb C\), with boundaryless models such as \(\mathbb C^n\) (`Geometry/Manifold/IsManifold/Basic.lean`, `Geometry/Manifold/ContMDiff/Defs.lean`). Products of complex manifolds are covered by this framework.

`Geometry/Manifold/Complex.lean` proves maximum-principle statements for maps into complex normed spaces on boundaryless complex manifolds. A local maximum of the norm of a holomorphic map makes its norm locally constant. On a preconnected open set, a maximum propagates throughout the set; with a strictly convex codomain the map itself is constant. A holomorphic map on a compact complex manifold is locally constant, and is constant when the manifold is preconnected. These results apply to higher-dimensional complex models as well as to Riemann surfaces.

The upper half-plane supplies a concrete one-dimensional complex manifold (`Analysis/Complex/UpperHalfPlane/Manifold.lean`). The half-space and quadrant models for manifolds with boundary or corners are real models; they are not a theory of CR boundaries of complex domains.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

The sheaf of holomorphic functions on open subsets of \(\mathbb C\) is constructed, with its étalé space of germs, a local-homeomorphism projection, and a separated-map property. Equality of germs is identified with equality of functions near the point ([holomorphic sheaf](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Complex/HolomorphicSheaf.lean)). The domain here is the complex plane; this does not fill the general holomorphic/meromorphic sheaf and vector-bundle theory on complex manifolds.

TauCeti also constructs particular complex one-dimensional manifolds from Fuchsian quotients (Section 44). No Hartogs extension, several-variable integral formula, pluripotential theory, or \(\overline\partial\)-solvability theorem was located.

## Topics of Section 45 not found in either inspected library

- The Cauchy integral formula over a polydisc, Hartogs extension, and separate holomorphy implying joint holomorphy.
- Plurisubharmonic functions, the complex Monge–Ampère equation, and pluripotential theory.
- Domains of holomorphy, pseudoconvexity, and holomorphic convexity.
- The \(\overline\partial\) equation and the CR geometry of real hypersurfaces.
- Holomorphic vector bundles and general holomorphic/meromorphic sheaf theory on complex manifolds. TauCeti constructs the holomorphic-function sheaf and its étalé space on the complex plane.
