# 32. Partial Differential Equations: General and Linear Theory

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. The roots for this section are `Mathlib.Analysis.BoxIntegral.DivergenceTheorem`, `Mathlib.MeasureTheory.Integral.DivergenceTheorem`, and `Mathlib.Analysis.InnerProductSpace.LaxMilgram`.

**Namespaces.** The Henstock–Kurzweil divergence theorem is `BoxIntegral`. The Bochner form is `MeasureTheory`. Coercivity and the Lax–Milgram equivalence are `IsCoercive`.

The direct PDE-related results described here are the divergence theorem on rectangular boxes and Lax–Milgram on a real Hilbert space. Distribution theory, Fourier analysis, and Sobolev inequalities provide further foundations in Sections 16, 26, 27, and 30. There is no theory of general linear partial differential equations.

## The divergence theorem on a box

The Henstock–Kurzweil form uses a non-standard gauge integral on a closed rectangular box \(I\) in \(\mathbb{R}^{n+1}\), identified with \(\mathrm{Fin}(n+1)\to\mathbb{R}\). Tags must lie in their boxes, the partition must be subordinate to a gauge, and every box is required to have bounded eccentricity: the ratios of its side lengths are at most a prescribed constant. In dimension one that eccentricity restriction is automatic for constants at least \(1\), so the integral reduces to the ordinary Henstock–Kurzweil integral (`Analysis/BoxIntegral/DivergenceTheorem.lean`).

If \(f\) takes values in \(E^{n+1}\), with \(E\) a real normed space, and \(f\) is continuous on \(I\) and Fréchet differentiable within \(I\) off a countable set, then the divergence \(\sum_i \partial_i f_i\), formed by applying the derivative to the \(i\)-th basis vector and reading the \(i\)-th component, is integrable in this gauge sense. Its integral equals the sum, over the \(n+1\) coordinate directions, of the integrals of the corresponding component of \(f\) over the upper face minus the integral over the lower face. The file describes this identity as a divergence theorem and tags it as Stokes’ theorem, but the statement is the rectangular divergence theorem, not Stokes’ theorem for differential forms.

The Bochner form assumes \(a\le b\) in \(\mathbb{R}^{n+1}\) and a map \(f\) into \(E^{n+1}\) that is continuous on the closed box \([a,b]\), Fréchet differentiable on the interior off a countable set, and whose divergence is Bochner-integrable on the box (`MeasureTheory/Integral/DivergenceTheorem.lean`). The integral of the divergence over \([a,b]\) then equals the same alternating sum of face integrals. If some pair of opposite faces coincides, both sides are zero. An equivalent statement is given for a family of scalar-valued component functions. The same identity is rewritten for a linearly ordered normed space affinely identified with \(\mathbb{R}^{n+1}\) by a volume-preserving equivalence, and there are two-dimensional specializations along rectangles in the plane, with and without a countable exceptional set. A version that assumes only partial derivatives, rather than the full Fréchet derivative, is marked as not yet proved.

No divergence theorem on a manifold, on a domain with smooth boundary, or for a differential form was found. Partitions of unity are available for manifolds, and alternating multilinear algebra is available, but neither is an integral Stokes theorem.

## Lax–Milgram

Let \(V\) be a real Hilbert space and let \(B:V\times V\to\mathbb{R}\) be a continuous bilinear form. The form is coercive when some \(C>0\) satisfies \(C\|u\|^2\le B(u,u)\) for every \(u\). Coercivity implies that the bounded operator \(B^\sharp:V\to V\) defined by \(\langle B^\sharp v,w\rangle=B(v,w)\) is bounded below, hence injective, has closed range, and is surjective. It is therefore a continuous linear automorphism of \(V\): for every \(\ell\in V^*\) there is a unique \(u\in V\) with \(B(u,w)=\ell(w)\) for every \(w\), and \(u\) depends continuously and linearly on \(\ell\). This follows by applying its inverse to the Riesz representative of \(\ell\) (`Analysis/InnerProductSpace/LaxMilgram.lean`). The scalar field is \(\mathbb{R}\). This is the nearest existence theorem for a linear elliptic variational equation; harmonic functions are section 33, where the same statement is repeated.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

TauCeti defines weak divergence-form Dirichlet equations on \(H^1_0(\Omega)\). For bounded measurable coefficients and a coercive energy form, every \(L^2\) forcing has a unique weak solution, with an energy estimate. Concrete sufficient ellipticity, drift, and mass conditions imply coercivity; in particular the zero-boundary Poisson problem is solved on bounded open domains, without a smooth-boundary hypothesis ([Dirichlet problem](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/PDE/DirichletProblem.lean)).

On bounded domains the solution operator is compact on \(L^2\), and a scalar mass shift satisfies the Fredholm alternative ([alternative](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/PDE/FredholmAlternative.lean)). With symmetric coercive energy form, Dirichlet eigenfunctions form an orthonormal basis of \(L^2\), with finite-dimensional eigenspaces and a Rayleigh characterization of the first eigenvalue ([spectrum](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/PDE/Spectrum.lean)). Interior \(H^2\) regularity is proved for a uniformly elliptic **constant principal matrix**, bounded measurable lower-order coefficients, and \(L^2\) forcing ([regularity](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/PDE/Regularity/Interior.lean)).

The Laplacian has implemented distributional fundamental solutions (Section 38), while semigroup generation and the autonomous abstract Cauchy problem are covered in Section 24. These are concrete PDE results beyond the abstract Lax–Milgram theorem; they do not constitute a general linear PDE or hypoellipticity theory.

## Topics of Section 32 not found in either inspected library

- The Cauchy–Kowalevski theorem and a general weak/distributional theory for arbitrary linear PDE, beyond the coercive elliptic and semigroup results above.
- Stokes’ theorem for differential forms, and the divergence theorem on manifolds or on domains other than rectangular boxes.
- The four model equations of Evans's first part beyond the Laplacian: the transport equation, the heat equation and its fundamental solution, the wave equation with d'Alembert's and Kirchhoff's formulas; the method of characteristics for first-order nonlinear equations, and Hamilton–Jacobi equations with the Hopf–Lax formula.
- Boundary value problems with nonzero boundary data, traces, and regularity up to the boundary (Lions–Magenes, Grisvard). The Dirichlet problem in TauCeti is posed in \(H^1_0\).
- General higher-order variable-coefficient PDE and hypoellipticity. Coercive second-order divergence-form equations with measurable coefficients, and fundamental solutions of the Laplacian, are present in TauCeti.
