# Structure 53: Elliptic operators on manifolds, index theory, and spectral geometry

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS53.md); [bibliographical scope](CKMA-bib.md#ckma-53); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.Normed.Operator.Fredholm.Basic`, `Mathlib.Analysis.Normed.Operator.Fredholm.Open`, `Mathlib.Analysis.Distribution.DerivNotation`, `Mathlib.Analysis.InnerProductSpace.Spectrum`, `Mathlib.LinearAlgebra.ExteriorPower.HodgeStar`. There is no root for elliptic operators on manifolds, the Atiyah–Singer index theorem, Hodge theory, or spectral geometry.

**Namespaces.** `ContinuousLinearMap.IsFredholm` is the abstract Fredholm condition of Section 21, and TauCeti states its index results in the `ContinuousLinearMap` namespace. `Laplacian` is the notation typeclass with a Euclidean instance. The TauCeti Dirichlet spectral theory is in `TauCeti.PDE`. There is no namespace for the Laplace–Beltrami operator on forms, the Dirac operator, or an analytic index of an elliptic operator.

A search of both libraries for elliptic differential operators between bundles, pseudodifferential operators on manifolds, Hodge representatives, Weyl laws, heat-trace expansions, spectral zeta and eta functions, analytic torsion, Dirac operators, index theorems, nodal domains, trace formulas, and X-ray transforms on manifolds found no development of these theories.

## Elliptic operators and global analysis

[Mathematical scope](SYNOPSIS53.md#elliptic-operators-and-global-analysis).

### Mathlib

**Supporting foundations.** Fredholm operators, as in Section 21, are continuous linear maps that are strict, with closed finite-codimension range and finite-dimensional topologically complemented kernel (`Analysis/Normed/Operator/Fredholm/Basic.lean`); the index of a composition of Fredholm operators is the sum of the indices (`ContinuousLinearMap.IsFredholm.index_comp`). When the scalar field and the domain are complete, the set of Fredholm operators is open in the operator norm and the index is locally constant (`ContinuousLinearMap.IsFredholm.eventually_nhds_index_eq`, `Analysis/Normed/Operator/Fredholm/Open.lean`). That is the operator-theoretic index, not the index of an elliptic operator on a manifold.

The spectral theorem for compact self-adjoint operators on an inner-product space is proved: the eigenspaces span a dense subspace, since their joint orthogonal complement is zero, and each eigenspace at a nonzero eigenvalue is finite-dimensional (`Analysis/InnerProductSpace/Spectrum.lean`). It is the abstract input to any discrete-spectrum theorem for an elliptic operator with compact resolvent.

The Euclidean Laplacian is the notation \(\Delta\) of `Analysis/Distribution/DerivNotation.lean`. On an inner-product space it is realised as the sum of second directional derivatives along an orthonormal basis, and the sum does not depend on the basis. It is not the Laplace–Beltrami operator of a Riemannian metric.

### TauCeti

TauCeti proves that the Fredholm property and the index are invariant under compact perturbations (`ContinuousLinearMap.index_add_of_isCompactOperator`, [compact perturbations](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fredholm/CompactPerturbation.lean)), that on Hilbert spaces the adjoint of a Fredholm operator is Fredholm with the opposite index (`ContinuousLinearMap.index_adjoint`, [adjoints](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fredholm/Adjoint.lean)), and that a self-adjoint Fredholm operator has index zero (`ContinuousLinearMap.index_eq_zero_of_isSelfAdjoint`, [self-adjoint operators](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fredholm/SelfAdjoint.lean)). Local constancy of the index is already in Mathlib; TauCeti restates it in \(\varepsilon\)-form ([small perturbations](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fredholm/SmallPerturbation.lean)) and deduces that the index of a continuous family of Fredholm operators is constant on a preconnected parameter space ([continuous families](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fredholm/ContinuousFamily.lean)). This is an integer-valued invariant, not an index class in \(K\)-theory; no elliptic operator on a manifold is shown to be Fredholm. The nonlinear Fredholm theory of Section 35, including the Sard–Smale theorem, is functional-analytic input, not an index theorem.

**Supporting material.** For the shifted Dirichlet problem \(B(u,v)-\kappa\langle u,v\rangle=\langle f,v\rangle\) of a coercive divergence-form operator with bounded measurable coefficients on a bounded open set in \(\mathbb R^n\), either the homogeneous problem has a nonzero solution, in a finite-dimensional solution space, or every \(L^2\) forcing has a unique weak solution (`TauCeti.PDE.fredholmAlternative_isWeakSolutionDirichlet_sub_const`, [Fredholm alternative](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/FredholmAlternative.lean)). This is the Euclidean-domain analogue of entry 53.5, not the closed-manifold statement.

**Synopsis entries.** Partly covered: 53.6 (the abstract parts: invariance of the Fredholm index under compact perturbations and along continuous families, and additivity under composition; no elliptic operator, Sobolev scale, or symbol homotopy). Not covered: 53.1, 53.3–53.5, 53.7–53.11.

## Elliptic complexes and Hodge theory

[Mathematical scope](SYNOPSIS53.md#elliptic-complexes-and-hodge-theory).

### Mathlib

**Supporting foundations.** The algebraic Hodge star is an isomorphism \(\bigwedge^k\simeq\bigwedge^{n-k}\) attached to a nondegenerate bilinear form and a volume element (`LinearAlgebra/ExteriorPower/HodgeStar.lean`); it is not stated on a manifold.

### TauCeti

**Supporting material.** The manifold-side ingredients recorded in [Section 52](STRUCTURE52.md#symplectic-gauge-and-sub-riemannian-analysis) are present: the de Rham complex of a manifold with corners and its cohomology, Stokes’ theorem on oriented manifolds with boundary, and the Laplace–Beltrami operator \(\operatorname{div}\circ\operatorname{grad}\) on functions. No Hodge Laplacian on forms, harmonic representative, or Hodge decomposition is proved. The files under `Geometry/Hodge` concern algebraic Hodge structures, not harmonic forms.

For entry 53.20, critical points of a smooth function on a manifold are counted in total and by Morse index; for a Morse function on a compact manifold the counts are finite, and replacing \(f\) by \(-f\) exchanges the indices \(j\) and \(\dim M-j\) (`TauCeti.IsMorse.criticalCount_neg`, [critical points](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Manifold/Morse/CriticalPoints.lean)). If a band \(f^{-1}[a,b]\) of a smooth function on a boundaryless finite-dimensional manifold is compact and free of critical points, the sublevel \(\{f\le b\}\) deformation retracts onto \(\{f\le a\}\) (`TauCeti.exists_sublevelDeformation`, [deformation lemma](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Manifold/Morse/Deformation.lean)). The Witten deformation and the Morse inequalities are not proved.

**Synopsis entries.** Not covered: 53.12–53.17, 53.20.

## Heat coefficients, Weyl laws, and spectral invariants

[Mathematical scope](SYNOPSIS53.md#heat-coefficients-weyl-laws-and-spectral-invariants).

### TauCeti

**Supporting material.** The Euclidean heat kernel \(K_t(x)=(4\pi t)^{-n/2}e^{-\|x\|^2/(4t)}\) on a finite-dimensional real inner-product space is smooth, positive, of mass one, solves the heat equation, satisfies \(K_t\star K_s=K_{t+s}\), and has Fourier transform \(e^{-4\pi^2t\|\xi\|^2}\) ([heat kernel](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/HeatKernel/Basic.lean)). No heat kernel on a manifold, heat-trace expansion, or eigenvalue asymptotics is proved.

**Synopsis entries.** Not covered: 53.21–53.34.

## Dirac operators and index theorems

[Mathematical scope](SYNOPSIS53.md#dirac-operators-and-index-theorems).

### Mathlib

**Supporting foundations.** The spin group of a quadratic form is the even part of the pin group inside the Clifford algebra (`LinearAlgebra/CliffordAlgebra/SpinGroup.lean`); it is not stated on a manifold.

### TauCeti

**Supporting material.** The Euler class of a real vector bundle is defined from a Thom class, is natural under pullback, and vanishes for a bundle with a nowhere-vanishing section (`TauCeti.eulerClass_pullback`, `TauCeti.eulerClass_eq_zero_of_forall_ne_zero`, [Euler class](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Topology/VectorBundle/EulerClass.lean)); the Thom isomorphism is not formalized, and no curvature form represents the class. A compact convex hyperbolic polygon with \(n\) vertices and interior angles \(\alpha_i\) has area \((n-2)\pi-\sum\alpha_i\) (`TauCeti.UpperHalfPlane.CompactConvexPolygon.volume_carrier`, [compact polygons](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/UpperHalfPlane/Polygon/GaussBonnet.lean)), and the same holds with ideal vertices of angle zero ([ideal vertices](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/UpperHalfPlane/Polygon/Convex/GaussBonnet.lean)). For a Fuchsian group with a locally finite convex fundamental polygon, the covolume is \(2\pi\bigl((n-k)/2-1-V+\sum_e(1-1/m_e)\bigr)\), the orbifold area formula ([fundamental polygons](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Fuchsian/Polygon/Area.lean)). These are polygonal hyperbolic area identities, not the Chern–Gauss–Bonnet theorem. Clifford algebras, spin groups, and spin representations are developed algebraically (for instance under `LinearAlgebra/CliffordAlgebra/`), without spinor bundles or Dirac operators.

**Synopsis entries.** Not covered: 53.35–53.50.

## Boundary operators, spectral flow, coverings, and positive bundles

[Mathematical scope](SYNOPSIS53.md#boundary-operators-spectral-flow-coverings-and-positive-bundles).

**Synopsis entries.** Not covered: 53.51–53.60, 53.84.

## Eigenvalue inequalities and nodal geometry

[Mathematical scope](SYNOPSIS53.md#eigenvalue-inequalities-and-nodal-geometry).

### TauCeti

**Supporting material.** For a divergence-form operator \(Lu=-\partial_j(a^{ij}\partial_iu)+b^i\partial_iu+cu\) on an open set \(\Omega\subset\mathbb R^n\) whose energy form is coercive on \(H^1_0(\Omega)\), the \(L^2\) solution operator is compact when \(\Omega\) is bounded (by Rellich–Kondrachov) and symmetric when the form is; its nonzero eigenvalues are the reciprocals of the Dirichlet eigenvalues, the Dirichlet eigenfunctions contain a Hilbert basis of \(L^2(\Omega)\), and the first eigenvalue is the minimum of the Rayleigh quotient ([Dirichlet spectrum](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Spectrum/Basic.lean)). No boundary regularity is assumed. On an interval \((a,b)\), the Dirichlet eigenvalues of \(-d^2/dx^2\) are exactly \((k\pi/(b-a))^2\), \(k\ge1\), with sine eigenfunctions, which gives the sharp Poincaré constant (`TauCeti.PDE.isDirichletEigenvalue_laplacian_intervalDomain_iff`, [interval spectrum](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Spectrum/Interval.lean)). In finite dimensions, the Courant–Fischer min–max characterization of the eigenvalues of a symmetric operator, their monotonicity under form domination, and Weyl’s perturbation inequality are proved ([Courant–Fischer](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/CourantFischer.lean)). Domain monotonicity of Dirichlet eigenvalues, Hadamard variation, Steklov spectra, nodal domains, unique continuation, and eigenfunction bounds are not proved.

**Synopsis entries.** Not covered: 53.62, 53.63, 53.68–53.73.

## Geodesic dynamics, trace formulas, and scattering

[Mathematical scope](SYNOPSIS53.md#geodesic-dynamics-trace-formulas-and-scattering).

**Synopsis entries.** Not covered: 53.74, 53.76–53.83.
