# Structure 45: Several complex variables, complex manifolds, pluripotential theory, and CR analysis

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS45.md); [bibliographical scope](CKMA-bib.md#ckma-45); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.Analytic.Basic`, `Mathlib.Analysis.Analytic.Composition`, `Mathlib.Analysis.Analytic.Inverse`, `Mathlib.Analysis.Calculus.FDeriv.Analytic`, `Mathlib.Analysis.Analytic.Uniqueness`, `Mathlib.Analysis.Complex.AbsMax`, `Mathlib.Analysis.Complex.OpenMapping`, `Mathlib.Analysis.Complex.Schwarz`, `Mathlib.MeasureTheory.Integral.TorusIntegral`, `Mathlib.RingTheory.PowerSeries.WeierstrassPreparation`, `Mathlib.Geometry.Manifold.IsManifold.Basic`, `Mathlib.Geometry.Manifold.Complex`.

**Namespaces.** Analytic maps use `FormalMultilinearSeries`, `HasFPowerSeriesAt`, `AnalyticAt`, and `AnalyticOnNhd`. Complex differentiability uses `DifferentiableAt` and `DifferentiableOn` with scalar field \(\mathbb C\). On manifolds the corresponding predicates are `MDifferentiable`, `MDifferentiableOn`, and `ContMDiff`. TauCeti results are in the `TauCeti` namespace or extend Mathlib namespaces such as `DifferentiableOn`.

<a id="structure-45a"></a>

## 45A. Functions, Domains, and the d-bar Equation

Analytic maps, the polydisc Cauchy formula, one-variable Cauchy–Pompeiu solvability, the Schwarz lemma for balls, and Levi-form calculus are grouped in this subdivision.

### Local holomorphic function theory

[Mathematical scope](SYNOPSIS45.md#local-holomorphic-function-theory).

#### Mathlib

**Analytic maps in arbitrary dimension.**

Analyticity is defined by locally convergent series of continuous multilinear maps:
\[
f(x+h)=\sum_{n\ge0}p_n(h,\ldots,h).
\]
This works in finite or infinite dimension, not just for functions of a single scalar variable (`Analysis/Analytic/Basic.lean`). Analytic maps are stable under composition (`Analysis/Analytic/Composition.lean`). The calculus connects these series with Fréchet derivatives: an analytic map is differentiable, and the first multilinear term gives its derivative (`Analysis/Calculus/FDeriv/Analytic.lean`). The spaces of multilinear coefficients need not be restricted to symmetric representatives in the underlying definition.

Mathlib proves that a complex-differentiable map is analytic only on open subsets of \(\mathbb C\) (`analyticOnNhd_iff_differentiableOn` in `Analysis/Complex/CauchyIntegral.lean`); the several-variable version is in TauCeti.

**Identity, maximum, and open mapping principles.**

These are stated for maps between normed spaces, so they apply on domains in \(\mathbb C^n\). An analytic map on a preconnected open set vanishing near one point vanishes on the set (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` and `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` in `Analysis/Analytic/Uniqueness.lean`). For a complex-differentiable map on a preconnected open subset of a complex normed space, an interior maximum of the norm propagates, and the map is constant when the codomain is strictly convex (`Complex.norm_eqOn_of_isPreconnected_of_isMaxOn`, `Complex.eqOn_of_isPreconnected_of_isMaxOn_norm` in `Analysis/Complex/AbsMax.lean`). A scalar-valued analytic map on a preconnected open subset of a complex normed space is constant or open (`AnalyticOnNhd.is_constant_or_isOpen` in `Analysis/Complex/OpenMapping.lean`).

**Inverse functions.**

The analytic inverse theory constructs inverse power series with positive convergence radius when the linear term is invertible. For an open partial homeomorphism with such an expansion, its local inverse is analytic (`Analysis/Analytic/Inverse.lean`, `OpenPartialHomeomorph.hasFPowerSeriesAt_symm`; `Analysis/Calculus/FDeriv/Analytic.lean`, `OpenPartialHomeomorph.analyticAt_symm`). Combined with the \(C^1\) inverse function theorem, a holomorphic map with invertible derivative is a local biholomorphism. The Banach-space inverse and implicit function theorems are described in Section 35. A holomorphic constant-rank theorem was not found.

**Torus integrals.**

`MeasureTheory/Integral/TorusIntegral.lean` defines the integral over the distinguished boundary \(T(c,R)=\{z:\lvert z_i-c_i\rvert=R_i\}\) of a polydisc in \(\mathbb C^n\), with linearity, a norm bound, and the reduction to iterated circle integrals (`torusIntegral_succ`, `torusIntegral_succAbove`).

#### TauCeti

The iterated Cauchy integral formula on polydiscs is proved: if \(f:\mathbb C^n\to E\) is complex differentiable on the closed polydisc with center \(c\) and polyradius \(R\), then for \(w\) in the open polydisc \(\oint_{T(c,R)}\prod_i(z_i-w_i)^{-1}f(z)\,dz=(2\pi i)^n f(w)\) (`DifferentiableOn.torusIntegral_prod_sub_inv_smul`). Consequently, on an open subset of a finite-dimensional complex normed space, complex differentiability and analyticity coincide (`TauCeti.analyticOnNhd_iff_differentiableOn_of_finiteDimensional`), and a contour integral whose integrand is jointly analytic in a finite-dimensional parameter and the integration variable is analytic in the parameter ([polydisc Cauchy formula](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/CauchyIntegralPolydisc.lean)). Cauchy estimates and convergence theorems of Weierstrass type in several variables are not part of this file. With this result the Mathlib identity theorem applies to every holomorphic function on a domain in \(\mathbb C^n\).

**Synopsis entries.** Covered: 45.3 (Mathlib, with TauCeti for analyticity of holomorphic functions). Partly covered: 45.2 (polydisc Cauchy formula and local analyticity in TauCeti; convergence of the Taylor series on the whole polydisc, Cauchy estimates and normal convergence are not stated), 45.4 (invertible-derivative case only). Not covered: 45.1, 45.5, 45.6.

### Pseudoconvexity and domains of holomorphy

[Mathematical scope](SYNOPSIS45.md#pseudoconvexity-and-domains-of-holomorphy).

#### TauCeti

Supporting material only. The Levi form of a real function on a complex normed space is defined from its real second derivative; for \(C^2\) functions it is Hermitian, with sum, product and composition rules and invariance under holomorphic maps ([Levi form](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/LeviForm.lean), [bilinear-form version](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/LinearAlgebra/Complex/LeviForm.lean)). Strict plurisubharmonicity (positive definite Levi form, `TauCeti.IsStrictlyPlurisubharmonicAt`) and strong \(q\)-pseudoconvexity (`TauCeti.IsStronglyPseudoconvexAt`) are defined pointwise; a strongly \(q\)-pseudoconvex function has real Morse index at most \(n+q\), both conditions are preserved by holomorphic immersions and increasing convex postcomposition, and they are stable under \(C^2\) perturbations ([pseudoconvexity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Pseudoconvex.lean)). This is pointwise calculus for \(C^2\) functions, not a theory of pseudoconvex domains, boundary Levi forms, or domains of holomorphy.

**Synopsis entries.** Not covered: 45.14–45.19.

### The d-bar equation and the Neumann problem

[Mathematical scope](SYNOPSIS45.md#the-d-bar-equation-and-the-neumann-problem).

#### TauCeti

The Cauchy–Pompeiu formula holds for compactly supported \(C^1\) maps \(u:\mathbb C\to F\) into a complex Banach space: \(u\) is the Cauchy transform of \(2\bar\partial u\). Conversely, the Cauchy transform of a compactly supported \(C^1\) map \(f\) is differentiable and solves \(2\bar\partial v=f\) (`HasCompactSupport.hasFDerivAt_integral_sub_inv_smul`, [Cauchy–Pompeiu](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Pompeiu.lean)). With a cutoff this gives the local solvability of \(\bar\partial\) in one variable. There is no Dolbeault complex of \((p,q)\)-forms on \(\mathbb C^n\).

**Synopsis entries.** Partly covered: 45.30 (one complex variable, functions only, via the Cauchy transform). Not covered: 45.31–45.43.

### Invariant metrics and bounded-domain rigidity

[Mathematical scope](SYNOPSIS45.md#invariant-metrics-and-bounded-domain-rigidity).

#### Mathlib

The Schwarz lemma is proved for complex-differentiable maps between balls in complex normed spaces: if \(f\) maps the ball of radius \(R\) about \(0\) into the closed ball of radius \(R\) and \(f(0)=0\), then \(\|f(z)\|\leq\|z\|\) (`Complex.norm_le_norm_of_mapsTo_ball`, with the two-radius version `Complex.dist_le_div_mul_dist_of_mapsTo_ball`, in `Analysis/Complex/Schwarz.lean`). For the Euclidean norm on \(\mathbb C^n\) this is the first sentence of 45.71. The invariant distance of the ball is not defined.

#### TauCeti

In one variable, TauCeti has the Poincaré distance of the disc and the Schwarz–Pick contraction for holomorphic self-maps of the disc (Section 44); the Carathéodory and Kobayashi pseudodistances of general domains are not defined.

**Synopsis entries.** Partly covered: 45.71 (Euclidean-norm Schwarz lemma for balls; no invariant distance). Not covered: 45.70, 45.72–45.75.

<a id="structure-45b"></a>

## 45B. Complex Manifolds, Stein Spaces, and Oka Theory

The atlas framework for complex manifolds, specific one-dimensional quotients, the sheaf of holomorphic functions on the plane, and formal or nonarchimedean Weierstrass theory are recorded here with their dimensional scope.

### Complex structures and cohomology

[Mathematical scope](SYNOPSIS45.md#complex-structures-and-cohomology).

#### Mathlib

The general atlas and smooth-map framework can be used over \(\mathbb C\), with boundaryless models such as \(\mathbb C^n\) (`Geometry/Manifold/IsManifold/Basic.lean`, `Geometry/Manifold/ContMDiff/Defs.lean`). Products of complex manifolds are covered by this framework.

`Geometry/Manifold/Complex.lean` proves maximum-principle statements for maps into complex normed spaces on boundaryless complex manifolds. A local maximum of the norm of a holomorphic map makes its norm locally constant. On a preconnected open set, a maximum propagates throughout the set; with a strictly convex codomain the map itself is constant. A holomorphic map on a compact complex manifold is locally constant, and is constant when the manifold is preconnected (`MDifferentiable.apply_eq_of_compactSpace`). These results apply to higher-dimensional complex models as well as to Riemann surfaces.

The upper half-plane supplies a concrete one-dimensional complex manifold (`Analysis/Complex/UpperHalfPlane/Manifold.lean`). The half-space and quadrant models for manifolds with boundary or corners are real models; they are not a theory of CR boundaries of complex domains.

#### TauCeti

TauCeti also constructs particular complex one-dimensional manifolds from Fuchsian quotients (Section 44). Its almost complex structures belong to linear symplectic geometry ([almost complex structures](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Symplectic/AlmostComplex.lean)); integrability and the Nijenhuis tensor are not treated.

**Synopsis entries.** Not covered: 45.59–45.62.

### Local analytic algebra and analytic sets

[Mathematical scope](SYNOPSIS45.md#local-analytic-algebra-and-analytic-sets).

#### Mathlib

Supporting material only. `RingTheory/PowerSeries/WeierstrassPreparation.lean` proves Weierstrass division and preparation for formal power series in one variable over an adically complete local ring (`PowerSeries.IsWeierstrassDivisionAt`). This is an algebraic formal-power-series theorem; convergent germs of holomorphic functions of several variables are not treated, and `Geometry/Manifold/Complex.lean` lists the analytic Weierstrass preparation theorem for stalks as future work.

#### TauCeti

Weierstrass preparation and division for restricted power series over complete nonarchimedean rings are proved ([preparation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/RingTheory/PowerSeries/Weierstrass/Preparation.lean), [division](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/RingTheory/PowerSeries/Weierstrass/Division.lean)); like the Mathlib version, they do not treat convergent complex germs.

**Synopsis entries.** Not covered: 45.7–45.13.

### Stein approximation, coherent sheaves, and Oka theory

[Mathematical scope](SYNOPSIS45.md#stein-approximation-coherent-sheaves-and-oka-theory).

#### TauCeti

Supporting material only. The sheaf of holomorphic functions on open subsets of \(\mathbb C\) is constructed, with its étalé space of germs, a local-homeomorphism projection, and a separated-map property. Equality of germs is identified with equality of functions near the point ([holomorphic sheaf](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/HolomorphicSheaf.lean)). The domain here is the complex plane; this does not supply coherent analytic sheaves, holomorphic vector bundles, or Stein theory.

**Synopsis entries.** Not covered: 45.20–45.29.

### Projective analytic and algebraic geometry

[Mathematical scope](SYNOPSIS45.md#projective-analytic-and-algebraic-geometry).

**Synopsis entries.** Not covered: 45.69.

<a id="structure-45c"></a>

## 45C. Pluripotential Theory and Kähler Analysis

The pointwise Levi-form calculus relevant here is recorded in 45A. The real Monge–Ampère construction noted below is a related convex-analytic formalization, with real rather than complex hypotheses.

### Positive currents and pluripotential theory

[Mathematical scope](SYNOPSIS45.md#positive-currents-and-pluripotential-theory).

#### TauCeti

Supporting material only. Plurisubharmonic functions in the upper semicontinuous sense, currents, and the complex Monge–Ampère operator are absent; TauCeti has the pointwise strict plurisubharmonicity of \(C^2\) functions (45A). The Monge–Ampère material in TauCeti is the real one for convex functions ([Monge–Ampère measures](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/MongeAmpere/Basic.lean)).

**Synopsis entries.** Not covered: 45.46–45.57, 45.83, 45.84.

### Kähler geometry, Hodge theory, and positive bundles

[Mathematical scope](SYNOPSIS45.md#kähler-geometry-hodge-theory-and-positive-bundles).

**Synopsis entries.** Not covered: 45.63–45.68.

### Multiplier ideals and vanishing

[Mathematical scope](SYNOPSIS45.md#multiplier-ideals-and-vanishing).

**Synopsis entries.** Not covered: 45.44, 45.45.

### Canonical volume forms and Kähler metrics

[Mathematical scope](SYNOPSIS45.md#canonical-volume-forms-and-kähler-metrics).

**Synopsis entries.** Not covered: 45.58.

<a id="structure-45d"></a>

## 45D. CR Geometry and Analysis

Reusable differential-geometric infrastructure includes real derivatives of holomorphic maps in [Section 40](STRUCTURE40.md), complex manifold charts in 45B, and differential forms and tangent bundles in [Section 52](STRUCTURE52.md). These provide ambient structures for CR formulations.

### CR geometry and boundary analysis

[Mathematical scope](SYNOPSIS45.md#cr-geometry-and-boundary-analysis).

**Synopsis entries.** Not covered: 45.76–45.82, 45.85–45.87.
