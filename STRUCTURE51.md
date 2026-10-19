# Structure 51: Integrable systems and Riemann–Hilbert methods

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS51.md); [bibliographical scope](CKMA-bib.md#ckma-51); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.MeasureTheory.Measure.ResolventTransform`, `Mathlib.LinearAlgebra.SymplecticGroup`, `Mathlib.Algebra.Lie.Sl2`. There is no root for integrable systems or for Riemann–Hilbert problems.

**Namespaces.** `IsSl2Triple` is the algebraic predicate for the \(\mathfrak{sl}_2\) relations; it is not a namespace of integrable systems. The TauCeti declarations are in `TauCeti` and are identified by name below.

Searches of both libraries for Riemann–Hilbert problems, Plemelj–Sokhotski formulas, Wiener–Hopf or Birkhoff factorization, the Korteweg–de Vries equation, solitons, Lax pairs, the Toda lattice, Jost solutions and inverse scattering, Poisson brackets and action–angle variables, isomonodromy and the Painlevé equations, Christoffel–Darboux kernels, equilibrium measures, and Tracy–Widom distributions found no development of these theories. The recorded material consists of Hardy-space and Toeplitz operator theory on the circle, transforms of measures, and Hamiltonian prerequisites on symplectic vector spaces.

## Cauchy operators and analytic factorization

[Mathematical scope](SYNOPSIS51.md#cauchy-operators-and-analytic-factorization).

### Mathlib

**Supporting foundations.** For a measure \(\mu\) on a normed field \(\Bbbk\) and an element \(a\) of a normed \(\Bbbk\)-algebra, the resolvent transform \(\int(x-a)^{-1}\,d\mu(x)\) (`resolventTransform`) specializes to the Stieltjes transform (\(\Bbbk=\mathbb R\), values in \(\mathbb C\)) and to the Cauchy transform of a measure on \(\mathbb C\); for a finite measure and values in \(\mathbb R\) or \(\mathbb C\) it is differentiable off the image of the support of \(\mu\), with derivative \(\int(x-a)^{-2}\,d\mu(x)\) (`hasDerivAt_resolventTransform`), and holomorphic there when the values are in \(\mathbb C\) (`analyticOn_resolventTransform`, `MeasureTheory/Measure/ResolventTransform.lean`). These are transforms of measures, not Cauchy operators on contours, and no Plemelj–Sokhotski boundary-value formula is proved. Liouville’s theorem, used in the uniqueness argument of entry 51.5, is in `Analysis/Complex/Liouville.lean`.

### TauCeti

The boundary Hardy space \(H^2\) is the closed subspace of \(L^2\) of the circle spanned by the nonnegative Fourier modes, with the orthogonal (Riesz) projection onto it and the complementary negative modes ([Hardy space](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/Hardy/Basic.lean)). A Hardy function \(x\) defines the holomorphic function \(F_x(w)=\sum_{n\ge0}\hat x(n)w^n\) on the unit disc, with \(|F_x(w)|\le\|x\|/\sqrt{1-|w|^2}\), and the circle restrictions \(t\mapsto F_x(re(t))\) converge to \(x\) in \(L^2\) as \(r\to1^-\) (`TauCeti.HardySpace.tendsto_eLpNorm_diskFunction_sub`, [disc function](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/Hardy/DiskFunction.lean)). This is the \(L^2\) circle case of the statement that \(C_+\) is the Hardy projection with boundary values of the Cauchy integral; the Cauchy integral on contours, the principal-value operator, the Plemelj–Sokhotski formulas, \(L^p\) and Hölder bounds, and the line case are absent.

On the operator side, the Toeplitz operator \(T_a=PM_a|_{H^2}\) of an essentially bounded symbol \(a\) on the circle is a bounded linear function of \(a\), with matrix entries \(\hat a(i-j)\) in the Hardy basis, adjoint \(T_{\bar a}\), norm at most \(\|a\|_\infty\), and injective symbol map ([Toeplitz operators](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/Hardy/Toeplitz.lean)). The semicommutator \(T_{ab}-T_aT_b\) is a product of Hankel operators, and vanishes when \(b\) is analytic or \(a\) coanalytic ([Hankel operators](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/Hardy/Hankel.lean)). These are the scalar ingredients of Wiener–Hopf theory, but no factorization theorem or matrix partial indices are proved.

**Supporting foundations.** Calderón–Zygmund operators on \(\mathbb R^n\) that are bounded on \(L^2\) and satisfy a Hörmander-type cancellation condition are of weak type \((1,1)\) and, by interpolation and duality, bounded in the \(L^p\) norm on \(L^2\cap L^p\) for \(1<p<\infty\) ([strong type](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/CalderonZygmund/StrongType.lean)); this is the general mechanism behind the \(L^p\) boundedness of the Cauchy operator on the line, not that theorem. Stability of the Fredholm property and index under small and compact perturbations is recorded in Section 50.

**Synopsis entries.** Partly covered: 51.1 (the Hardy projection on \(L^2\) of the unit circle and \(L^2\) boundary values of the holomorphic extension, TauCeti; no Cauchy integral on contours, Plemelj formulas, or \(L^p\) and Hölder theory). Not covered: 51.2–51.11.

## Nonlinear steepest descent

[Mathematical scope](SYNOPSIS51.md#nonlinear-steepest-descent).

**Synopsis entries.** Not covered: 51.12–51.15.

## Direct and inverse scattering on the line

[Mathematical scope](SYNOPSIS51.md#direct-and-inverse-scattering-on-the-line).

**Synopsis entries.** Not covered: 51.16–51.25, 51.68, 51.26–51.29, 51.69, 51.30, 51.70, 51.31–51.34.

## Hamiltonian structure, finite-gap solutions, and lattices

[Mathematical scope](SYNOPSIS51.md#hamiltonian-structure-finite-gap-solutions-and-lattices).

### Mathlib

**Supporting foundations.** The symplectic group of matrices preserving the standard form \(J\) is defined in `LinearAlgebra/SymplecticGroup.lean`; it is linear algebra, not Hamiltonian dynamics. `Algebra/Lie/Sl2.lean` defines an \(\mathfrak{sl}_2\) triple \((h,e,f)\) in a Lie algebra by \(h\neq 0\), \([e,f]=h\), \([h,e]=2e\), and \([h,f]=-2f\) (`IsSl2Triple`), and studies primitive vectors in finite-dimensional representations. That is the representation theory of \(\mathfrak{sl}_2\), not an integrable system or a classical \(r\)-matrix.

### TauCeti

TauCeti contains geometric prerequisites for Hamiltonian analysis. On the linear cotangent space \(V\times V'\), with continuous dual \(V'\), it constructs the Liouville one-form \(\lambda_{(q,p)}(\delta q,\delta p)=p(\delta q)\) and proves that the canonical symplectic form is \(-d\lambda\), without a finite-dimensional restriction ([linear cotangent model](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Symplectic/Cotangent/Liouville.lean)). This is an exact symplectic construction, not an integrable Hamiltonian system. On a finite-dimensional real vector space with a constant symplectic form \(\omega\), the Hamiltonian vector field \(X_H\) of a differentiable \(H\) is the unique field with \(\omega(X_H(x),v)=dH(x)v\); for \(\omega=dq\wedge dp\) these are Hamilton’s equations, and for \(C^2\) \(H\) the linearization of \(X_H\) is infinitesimally symplectic ([Hamiltonian vector fields](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Symplectic/Hamiltonian/Basic.lean)). If \(X_H\) is globally Lipschitz, its global flow conserves \(H\) along each orbit, and for \(C^2\) \(H\) every time-\(t\) map preserves \(\omega\) on tangent vectors ([Hamiltonian flows](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Symplectic/Hamiltonian/Flow.lean)). Smooth two-forms on manifolds and their closedness are defined as a layer beneath the symplectic constructions ([two-form module](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Manifold/TwoForm/Basic.lean)), with fiberwise nondegenerate, tame, and compatible two-forms on manifolds ([manifold two-forms](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/Symplectic/Manifold/TwoForm.lean)); Hamiltonian dynamics on symplectic manifolds, Poisson brackets, and first integrals in involution are not developed. The linear symplectic algebra around these files (Lagrangian subspaces, compatible almost complex structures) and \(J\)-holomorphic maps with their energy identity are also developed, as geometric rather than integrable-systems content.

**Synopsis entries.** Not covered: 51.35–51.49, 51.71.

## Isomonodromy and Painlevé equations

[Mathematical scope](SYNOPSIS51.md#isomonodromy-and-painlevé-equations).

**Synopsis entries.** Not covered: 51.50–51.57, 51.72.

## Orthogonal polynomials, kernels, and boundary transforms

[Mathematical scope](SYNOPSIS51.md#orthogonal-polynomials-kernels-and-boundary-transforms).

### TauCeti

**Supporting foundations.** For the combinatorial side of entry 51.66, Schensted’s theorem is proved: the first row of the Robinson–Schensted insertion tableau of a word has the length of a longest weakly increasing subsequence, and for permutations of a longest increasing subsequence ([Schensted’s theorem](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Combinatorics/Young/LongestSubsequence.lean)). No asymptotic or distributional statement about \(L_N\) is proved.

**Synopsis entries.** Not covered: 51.58–51.67.
