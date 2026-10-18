# 45. Several Complex Variables, Complex Manifolds, Pluripotential Theory, and CR Analysis

Checked against Mathlib commit `f039e1b8a616d45782a5c7fc5e7909249c36b8ea` (2026-10-18, Lean `v4.36.0-rc1`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

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

These foundations should not be confused with a proof of every classical characterization of holomorphy in several variables. Mathlib proves that a complex-differentiable map is analytic only on open subsets of \(\mathbb C\) (`analyticOnNhd_iff_differentiableOn` in `Analysis/Complex/CauchyIntegral.lean`); the several-variable version is in TauCeti (below). Neither gives Hartogs’s theorem on separate holomorphy.

## Torus integrals and formal Weierstrass theory

`MeasureTheory/Integral/TorusIntegral.lean` defines the integral over the distinguished boundary \(T(c,R)=\{z:\lvert z_i-c_i\rvert=R_i\}\) of a polydisc in \(\mathbb C^n\), with linearity, a norm bound, and the reduction to iterated circle integrals (`torusIntegral_succ`, `torusIntegral_succAbove`). The Cauchy formula on a polydisc is not proved there.

`RingTheory/PowerSeries/WeierstrassPreparation.lean` proves Weierstrass division and preparation for formal power series in one variable over an adically complete local ring (`PowerSeries.IsWeierstrassDivisionAt`). This is algebraic; it does not treat convergent germs of holomorphic functions of several variables, and `Geometry/Manifold/Complex.lean` lists the analytic Weierstrass preparation theorem for stalks as future work.

## Complex manifolds and the maximum principle

The general atlas and smooth-map framework can be used over \(\mathbb C\), with boundaryless models such as \(\mathbb C^n\) (`Geometry/Manifold/IsManifold/Basic.lean`, `Geometry/Manifold/ContMDiff/Defs.lean`). Products of complex manifolds are covered by this framework.

`Geometry/Manifold/Complex.lean` proves maximum-principle statements for maps into complex normed spaces on boundaryless complex manifolds. A local maximum of the norm of a holomorphic map makes its norm locally constant. On a preconnected open set, a maximum propagates throughout the set; with a strictly convex codomain the map itself is constant. A holomorphic map on a compact complex manifold is locally constant, and is constant when the manifold is preconnected. These results apply to higher-dimensional complex models as well as to Riemann surfaces.

The upper half-plane supplies a concrete one-dimensional complex manifold (`Analysis/Complex/UpperHalfPlane/Manifold.lean`). The half-space and quadrant models for manifolds with boundary or corners are real models; they are not a theory of CR boundaries of complex domains.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6ebb29f84b4d`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

The iterated Cauchy integral formula on polydiscs is proved: if \(f:\mathbb C^n\to E\) is complex differentiable on the closed polydisc with center \(c\) and polyradius \(R\), then for \(w\) in the open polydisc \(\oint_{T(c,R)}\prod_i(z_i-w_i)^{-1}f(z)\,dz=(2\pi i)^n f(w)\) (`DifferentiableOn.torusIntegral_prod_sub_inv_smul`). Consequently, on an open subset of a finite-dimensional complex normed space, complex differentiability and analyticity coincide (`TauCeti.analyticOnNhd_iff_differentiableOn_of_finiteDimensional`), and a contour integral whose integrand is jointly analytic in a finite-dimensional parameter and the integration variable is analytic in the parameter ([polydisc Cauchy formula](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Complex/CauchyIntegralPolydisc.lean)). Cauchy estimates, convergence theorems of Weierstrass type in several variables, and Hartogs's theorems are not part of this file.

The Cauchy–Pompeiu formula holds for compactly supported \(C^1\) maps \(u:\mathbb C\to F\) into a complex Banach space: \(u\) is the Cauchy transform of \(2\bar\partial u\). Conversely, the Cauchy transform of a compactly supported \(C^1\) map \(f\) is differentiable and solves \(2\bar\partial v=f\) ([Cauchy–Pompeiu](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Complex/Pompeiu.lean)). With a cutoff this gives the local solvability of \(\bar\partial\) in one variable; no Dolbeault complex of \((p,q)\)-forms on \(\mathbb C^n\) was found.

The Levi form of a real function on a complex normed space is defined from its real second derivative; for \(C^2\) functions it is Hermitian, with sum, product and composition rules and invariance under holomorphic maps ([Levi form](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Complex/LeviForm.lean)). Strict plurisubharmonicity (positive definite Levi form) and strong \(q\)-pseudoconvexity are defined pointwise; a strongly \(q\)-pseudoconvex function has real Morse index at most \(n+q\), both conditions are preserved by holomorphic immersions and increasing convex postcomposition, and they are stable under \(C^2\) perturbations ([pseudoconvexity](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Complex/Pseudoconvex.lean)). This is pointwise calculus for \(C^2\) functions, not a theory of (upper semicontinuous) plurisubharmonic functions or pseudoconvex domains.

The sheaf of holomorphic functions on open subsets of \(\mathbb C\) is constructed, with its étalé space of germs, a local-homeomorphism projection, and a separated-map property. Equality of germs is identified with equality of functions near the point ([holomorphic sheaf](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Complex/HolomorphicSheaf.lean)). The domain here is the complex plane; this does not fill the general holomorphic/meromorphic sheaf and vector-bundle theory on complex manifolds.

Weierstrass preparation and division for restricted power series over complete nonarchimedean rings are proved ([preparation](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/RingTheory/PowerSeries/Weierstrass/Preparation.lean), [division](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/RingTheory/PowerSeries/Weierstrass/Division.lean)); like the Mathlib version, they do not treat convergent complex germs. The Monge–Ampère material in TauCeti is the real one for convex functions ([Monge–Ampère measures](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Convex/MongeAmpere/Basic.lean)). TauCeti also constructs particular complex one-dimensional manifolds from Fuchsian quotients (Section 44). No Hartogs extension, Stein or coherent analytic sheaf theory, pluripotential theory, or \(L^2\) \(\overline\partial\)-estimate was located.

## Topics of Section 45 not found in either inspected library

- Hartogs extension, and separate holomorphy implying joint holomorphy. Analyticity of jointly complex-differentiable maps on open subsets of \(\mathbb C^n\) and the polydisc Cauchy formula are proved in TauCeti; Cauchy estimates, Weierstrass-type convergence theorems in several variables, and the theorem on complex Banach spaces of infinite dimension were not found.
- Weierstrass preparation and division for convergent power series in several complex variables, Oka's coherence theorem, and Cartan's Theorems A and B for Stein spaces.
- Plurisubharmonic functions in the upper semicontinuous sense, the Poincaré–Lelong formula, Bedford–Taylor products, the complex Monge–Ampère equation, and pluripotential theory. TauCeti has only pointwise strict plurisubharmonicity of \(C^2\) functions and the real Monge–Ampère theory.
- Domains of holomorphy, pseudoconvex domains, the Levi problem, holomorphic convexity, polynomial convexity and the Oka–Weil theorem.
- The \(\overline\partial\) equation in several variables (the local Dolbeault lemma is available only in the one-variable form given by the Cauchy transform in TauCeti), Hörmander's \(L^2\) estimates, the Ohsawa–Takegoshi extension theorem, the \(\overline\partial\)-Neumann problem and subelliptic estimates, integral representations (Bochner–Martinelli, Henkin–Ramírez), and the CR geometry of real hypersurfaces.
- Kähler geometry, the Calabi–Yau theorem, currents on complex manifolds, Dolbeault cohomology and Dolbeault's theorem, the Kodaira–Nakano vanishing theorem, and the Kodaira embedding theorem.
- Holomorphic vector bundles and general holomorphic/meromorphic sheaf theory on complex manifolds. TauCeti constructs the holomorphic-function sheaf and its étalé space on the complex plane.
