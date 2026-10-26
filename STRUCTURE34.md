# Structure 34: Hyperbolic equations, conservation laws, dispersive PDE, fluids, and kinetic theory

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS34.md); [bibliographical scope](CKMA-bib.md#ckma-34); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.InformationTheory.KullbackLeibler` (relative entropy `InformationTheory.klDiv`, used by the TauCeti Pinsker inequality); as supporting material only, `Mathlib.MeasureTheory.Integral.DivergenceTheorem` and `Mathlib.Analysis.BoxIntegral.DivergenceTheorem`. No wave equation, conservation law, shock, Burgers equation, Euler or Navier–Stokes equation, Boltzmann or Vlasov equation, dispersive or Strichartz estimate, or KdV equation is formalized in Mathlib.

**Namespaces.** The transport predicate is `TauCeti.IsContinuityEquation`; the scalar-envelope derivative is `TauCeti.hasDerivAt_toReal_moreauYosida`; Pinsker's inequality is `TauCeti.totalVariation_sq_le_two_mul_klDiv`. The unitary-group and generator declarations are named in their entries.

<a id="structure-34a"></a>

## 34A. Hyperbolic Systems and Conservation Laws

[Mathematical scope](SYNOPSIS34.md#synopsis-34a).

The scalar-envelope calculation below and the general evolution tools in [Section 24](STRUCTURE24.md) are reusable ingredients. The latter apply after a generator has been identified.

### Quasilinear hyperbolicity and the formation of shocks

[Mathematical scope](SYNOPSIS34.md#quasilinear-hyperbolicity-and-the-formation-of-shocks).

**Synopsis entries.** Not covered: 34.1–34.8.

### Scalar entropy solutions and one-dimensional systems

[Mathematical scope](SYNOPSIS34.md#scalar-entropy-solutions-and-one-dimensional-systems).

#### TauCeti

Close to the Hopf–Lax formula, the metric Moreau–Yosida envelope $\varphi_t(x)=\inf_y\bigl(\varphi(y)+d(x,y)^2/2t\bigr)$ satisfies $\partial_t\varphi_t(x)=-d(x,y_t)^2/2t^2$ at a time $t>0$ near which minimizers $y_s$ exist with $s\mapsto d(x,y_s)$ continuous at $t$ and $\varphi_t(x)$ finite (`TauCeti.hasDerivAt_toReal_moreauYosida`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/GradientFlow/MoreauYosida/Derivative.lean)). This is the time derivative of a quadratic Hopf–Lax envelope, without a viscosity-solution theory of the Hamilton–Jacobi equation and without the Lax–Oleinik link to entropy solutions.

**Synopsis entries.** Partly covered: 34.14 (quadratic Hamiltonian only: the Moreau–Yosida envelope on a metric space and its time derivative; no viscosity-solution or entropy-solution statement). Not covered: 34.9–34.13, 34.15–34.22.

<a id="structure-34b"></a>

## 34B. Dispersive Equations and Nonlinear Waves

[Mathematical scope](SYNOPSIS34.md#synopsis-34b).

Abstract unitary groups and their self-adjoint generators supply linear evolution infrastructure; the scope is specified below.

### Dispersive estimates and nonlinear Schrödinger equations

[Mathematical scope](SYNOPSIS34.md#dispersive-estimates-and-nonlinear-schrödinger-equations).

#### TauCeti

The abstract evolution theory also covers groups. Strongly continuous groups on real Banach spaces ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Semigroups/Group/Basic.lean)) and the Lumer–Phillips theorem (a densely defined m-dissipative operator generates a contraction semigroup; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Semigroups/Generation/LumerPhillips.lean)) lead to Stone's theorem: the generator of a unitary group on a complex Hilbert space is skew-adjoint ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Semigroups/Group/Unitary.lean)), and conversely a self-adjoint operator $A$ has exactly one unitary group with complex generator $iA$ (`IsSelfAdjoint.existsUnique_isUnitary_complexGenerator_eq_I_smul`, `LinearPMap.isSelfAdjoint_iff_exists_isUnitary_complexGenerator_eq_I_smul`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Semigroups/Group/Stone/Unbounded.lean)). This gives the abstract unitary propagator $e^{-itH}$ of a self-adjoint Hamiltonian, with the generator specified abstractly. No free Schrödinger or wave propagator on $\mathbb R^d$ is identified, and no dispersive, Strichartz, or local-smoothing estimate is proved.

**Synopsis entries.** Not covered: 34.23–34.34, 34.83.

### Nonlinear waves and KdV

[Mathematical scope](SYNOPSIS34.md#nonlinear-waves-and-kdv).

**Synopsis entries.** Not covered: 34.35–34.42, 34.84–34.86.

### Critical Schrödinger evolution and geometric hyperbolic equations

[Mathematical scope](SYNOPSIS34.md#critical-schrödinger-evolution-and-geometric-hyperbolic-equations).

**Synopsis entries.** Not covered: 34.80–34.82.

<a id="structure-34c"></a>

## 34C. Mathematical Fluid Dynamics

[Mathematical scope](SYNOPSIS34.md#synopsis-34c).

The distributional continuity equation and transport interpolation are grouped here, with the integrability and continuity hypotheses of their formal statements.

### Incompressible Euler flow

[Mathematical scope](SYNOPSIS34.md#incompressible-euler-flow).

**Synopsis entries.** Not covered: 34.43–34.52.

### Navier–Stokes and compressible flow

[Mathematical scope](SYNOPSIS34.md#navierstokes-and-compressible-flow).

The TauCeti continuity-equation predicate recorded in the next section concerns transport of measures by a given velocity field; it is not a statement about compressible-flow solutions.

**Synopsis entries.** Not covered: 34.53–34.64.

### Transport renormalization, energy, and inviscid limits

[Mathematical scope](SYNOPSIS34.md#transport-renormalization-energy-and-inviscid-limits).

#### TauCeti

For transport, `TauCeti.IsContinuityEquation` defines distributional solutions of $\partial_t\mu_t+\mathop{\mathrm{div}}(v_t\mu_t)=0$ for a measurable family of measures on a finite-dimensional space with integrable mass and integrable $\int\|v_t\|\,d\mu_t$ ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/OptimalTransport/ContinuityEquation/Basic.lean)). For narrowly continuous curves of finite measures the identity extends to bounded $C^1$ test functions with boundary-time terms (`TauCeti.IsContinuityEquation.intervalIntegral_integral_fderiv_eq_sub`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/OptimalTransport/ContinuityEquation/Endpoint.lean)), and displacement interpolations of transport plans and maps solve it with the barycentric velocity, whose $p$-action is bounded by the $p$-th moment of the displacement ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/OptimalTransport/ContinuityEquation/PlanInterpolation.lean), [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/OptimalTransport/ContinuityEquation/MapInterpolation.lean)). There is no uniqueness or renormalization theory for transport by Sobolev or BV fields.

**Synopsis entries.** Not covered: 34.77–34.79.

<a id="structure-34d"></a>

## 34D. Kinetic Equations

[Mathematical scope](SYNOPSIS34.md#synopsis-34d).

The Boltzmann entropy of densities on Wasserstein space and Pinsker's inequality are relevant entropy tools for kinetic analysis. Transport-plan interpolations solving the continuity equation are described in 34C and [Section 39C](STRUCTURE39.md#structure-39c).

### Transport and kinetic equations

[Mathematical scope](SYNOPSIS34.md#transport-and-kinetic-equations).

#### Mathlib

Relative entropy of measures is `InformationTheory.klDiv` (`InformationTheory/KullbackLeibler/Basic.lean`), extended-valued and equal to $\int f\log(f/g)$ in the absolutely continuous case.

#### TauCeti

Pinsker's inequality: for probability measures $\mu,\nu$ on any measurable space, the total variation $|\mu-\nu|(X)$ of the signed measure $\mu-\nu$ satisfies $|\mu-\nu|(X)^2\le2\,\mathrm{KL}(\mu\,\|\,\nu)$ (`TauCeti.totalVariation_sq_le_two_mul_klDiv`), with an equal-mass finite-measure version and event forms ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/InformationTheory/KullbackLeibler/Pinsker.lean)). For probability densities $f,M$ this is $\|f-M\|_1^2\le2\int f\log(f/M)$.

The Boltzmann entropy on Wasserstein space ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/BoltzmannEntropy.lean)) is a functional of densities, expressed through relative entropy with respect to a tilted reference measure, with lower semicontinuity and tightness of sublevel sets; no collision operator is defined.

**Synopsis entries.** Covered: 34.74 (TauCeti). Not covered: 34.65–34.73, 34.75, 34.76.

## Supporting structures and related formalizations

The following entries supply additional foundations or related constructions. Their stated scope determines how they can be used in this sub-area.

### Mathlib

The divergence theorem on rectangular boxes (`MeasureTheory/Integral/DivergenceTheorem.lean`, `Analysis/BoxIntegral/DivergenceTheorem.lean`; see [Section 32](STRUCTURE32.md)) is the nearest integral identity to a conservation-law balance; it is not itself a conservation law.

### TauCeti

TauCeti adds general Banach-space semigroup generation and unique mild/classical solutions of an autonomous abstract Cauchy problem ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Semigroups/CauchyProblem/Basic.lean), [uniqueness](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Semigroups/CauchyProblem/Uniqueness.lean), `IsMildSolution.unique`, `IsClassicalSolution.unique`; Section 24). Application of this theorem requires an identified generator; its role here is abstract evolution infrastructure.
