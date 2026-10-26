# Structure 47: Approximation theory

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS47.md); [bibliographical scope](CKMA-bib.md#ckma-47); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Topology.ContinuousMap.StoneWeierstrass`, `Mathlib.Topology.ContinuousMap.Weierstrass`, `Mathlib.Analysis.SpecialFunctions.Bernstein`, `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal`, `Mathlib.Analysis.Normed.Lp.SmoothApprox`, `Mathlib.Analysis.Convolution`, `Mathlib.Analysis.Calculus.BumpFunction.Convolution`, `Mathlib.Analysis.Fourier.AddCircle`, `Mathlib.Analysis.InnerProductSpace.Projection.Basic`, `Mathlib.Topology.MetricSpace.HausdorffDistance`, `Mathlib.LinearAlgebra.Lagrange`, `Mathlib.RingTheory.Polynomial.Bernstein`, `Mathlib.LinearAlgebra.Matrix.Determinant.TotallyNonneg`, `Mathlib.Analysis.InnerProductSpace.Reproducing`.

**Namespaces.** `ContinuousMap`, with the real subalgebra form and the `RCLike` star-subalgebra form of Stone–Weierstrass, and `polynomialFunctions` for polynomial subalgebras of continuous functions. Bernstein polynomials on the unit interval sit in `bernstein`, and the approximations themselves in `bernsteinApproximation`. Compactly supported smooth approximation in \(L^p\) is `HasCompactSupport` and `MeasureTheory.MemLp`. Convolution against smooth bumps is `ContDiffBump`. Orthogonal projections are `Submodule.starProjection`, Lagrange interpolation is `Lagrange.interpolate`, and reproducing kernel Hilbert spaces are `RKHS`. TauCeti's approximation numbers extend `ContinuousLinearMap`; its kernel and Bochner results are in the `TauCeti` namespace.

## Best approximation and alternation

[Mathematical scope](SYNOPSIS47.md#best-approximation-and-alternation).

### Mathlib

**Existence and Hilbert projection.**

In a proper metric space, for instance a finite-dimensional normed space, every nonempty closed set contains a point nearest to a given point (`IsClosed.exists_infDist_eq_dist` in `Topology/MetricSpace/HausdorffDistance.lean`); for a compact set no properness is needed (`IsCompact.exists_infDist_eq_dist`). A best approximant from a finite-dimensional subspace of an arbitrary normed space is not stated.

In an inner product space, a nonempty complete convex set contains a unique nearest point (`exists_norm_eq_iInf_of_complete_convex` in `Analysis/InnerProductSpace/Projection/Minimal.lean`), characterized by a variational inequality (`norm_eq_iInf_iff_real_inner_le_zero`); for a complete subspace, by orthogonality of the residual (`Submodule.norm_eq_iInf_iff_inner_eq_zero`). The orthogonal projection realizes the minimum (`Submodule.starProjection_minimal`), has norm at most one (`Submodule.starProjection_norm_le`), and satisfies the Pythagorean identity \(\|x\|^2=\|Px\|^2+\|P^\perp x\|^2\) (`Submodule.norm_sq_eq_add_norm_sq_starProjection`, `Analysis/InnerProductSpace/Projection/Basic.lean`).

**Chebyshev extremal property.**

For \(n\ge1\), among real polynomials of degree at most \(n\) that are bounded by \(1\) on \([-1,1]\), the leading coefficient is at most \(2^{n-1}\), and for \(n\geq 2\) equality holds precisely for the Chebyshev polynomial \(T_n\) (`Polynomial.Chebyshev.leadingCoeff_le_of_forall_abs_le_one`, `Polynomial.Chebyshev.leadingCoeff_eq_iff_of_forall_abs_le_one` in `Analysis/SpecialFunctions/Trigonometric/Chebyshev/Extremal.lean`). By scaling, this is the statement that \(2^{1-n}T_n\) is the unique monic polynomial of degree \(n\) of least uniform norm on \([-1,1]\). These are extremal properties of \(T_n\), not a general equioscillation theorem.

**Interpolation.**

Over a field, distinct nodes determine a unique interpolating polynomial of degree less than the number of nodes (`Lagrange.interpolate`, `Lagrange.eval_interpolate_at_node`, `Lagrange.eq_interpolate_of_eval_eq` in `LinearAlgebra/Lagrange.lean`). This is algebra; the interpolation error formula and Lebesgue constants are not present.

**Synopsis entries.** Covered: 47.3, 47.8 (Mathlib). Partly covered: 47.1 (nearest points in proper spaces and compact sets; not for a finite-dimensional subspace of an arbitrary normed space), 47.9 (existence and uniqueness of the interpolant; no error formula). Not covered: 47.2, 47.4–47.7, 47.10.

## Density and positive approximation operators

[Mathematical scope](SYNOPSIS47.md#density-and-positive-approximation-operators).

### Mathlib

**Stone–Weierstrass.**

Let \(X\) be a compact topological space. The lattice form is the engine of the proof. If \(L\subseteq C(X,\mathbb{R})\) is nonempty, closed under pointwise minimum and pointwise maximum, and separates points strongly — for every continuous real \(f\) and every pair of points there is an element of \(L\) taking the same values as \(f\) at those two points — then the uniform closure of \(L\) is all of \(C(X,\mathbb{R})\) (`Topology/ContinuousMap/StoneWeierstrass.lean`, `ContinuousMap.sublattice_closure_eq_top`).

The real Stone–Weierstrass theorem follows. A subalgebra \(A\subseteq C(X,\mathbb{R})\) that separates points has uniform closure equal to \(C(X,\mathbb{R})\). The closure of a subalgebra is a sublattice, because the absolute value of each of its elements lies in the closure, by polynomial approximation of the absolute value on a compact interval of \(\mathbb{R}\). Epsilon forms are recorded: every continuous real function is within any prescribed \(\varepsilon>0\), in the uniform norm, of an element of \(A\).

If \(X\) is not assumed compact, the same separation hypothesis gives uniform approximation on compact subsets: for every compact \(K\subseteq X\), every continuous real \(f\), and every \(\varepsilon>0\), some \(g\in A\) satisfies \(\|g(x)-f(x)\|<\varepsilon\) for all \(x\in K\).

For \(\mathbb{R}\) or \(\mathbb{C}\), the scalar field being `RCLike`, a star subalgebra of \(C(X,\mathbb{k})\) that separates points is uniformly dense. The reduction passes to the real subalgebra of modulus-squared elements \(\lvert F\rvert^2\), and then applies the real theorem. On a compact \(s\subseteq\mathbb{R}\), polynomial functions are uniformly dense in \(C(s,\mathbb{R})\). On a compact \(s\subseteq\mathbb{k}\), the star closure of the polynomial functions is uniformly dense in \(C(s,\mathbb{k})\), and the closed star subalgebra generated by the identity function is all of \(C(s,\mathbb{k})\).

On the circle \(\mathbb R/T\mathbb Z\), the span of the characters \(e_n\) is dense in \(C(\mathbb R/T\mathbb Z,\mathbb C)\) (`fourierSubalgebra_closure_eq_top`, `span_fourier_closure_eq_top` in `Analysis/Fourier/AddCircle.lean`): trigonometric polynomials are uniformly dense among continuous periodic functions.

**Bernstein polynomials and Weierstrass on an interval.**

On the unit interval \(I=[0,1]\), the Bernstein basis polynomials are
\[
b_{n,\nu}(x)=\binom{n}{\nu}x^\nu(1-x)^{n-\nu}.
\]
They are nonnegative (`bernstein_nonneg`) and sum to \(1\) (`bernsteinPolynomial.sum`), and \(\sum_\nu\nu\,b_{n,\nu}=nX\) (`bernsteinPolynomial.sum_smul` in `RingTheory/Polynomial/Bernstein.lean`), so the operators are positive, reproduce affine functions, and are contractions in the uniform norm. For a continuous \(f:I\to E\) with values in a locally convex real topological vector space, the Bernstein approximation is
\[
B_n f=\sum_{k=0}^n b_{n,k}\cdot f(k/n).
\]
As \(n\to\infty\), \(B_n f\) converges to \(f\) in the topology of uniform convergence (`Analysis/SpecialFunctions/Bernstein.lean`, `bernsteinApproximation_uniform`). The argument is the usual second-moment estimate: the probability that \(k/n\) differs from \(x\) by more than \(\delta\) is at most \((4n\delta^2)^{-1}\). It uses uniform continuity, not a modulus-of-continuity rate.

This is the Weierstrass theorem on \([0,1]\): the uniform closure of the polynomial functions is all of \(C(I,\mathbb{R})\). Transport by an affine homeomorphism gives the same statement on every compact interval \([a,b]\subseteq\mathbb{R}\) (`Topology/ContinuousMap/Weierstrass.lean`). The Stone–Weierstrass proof uses this interval case, because it approximates the absolute value by polynomials. Epsilon forms give a polynomial uniformly within \(\varepsilon\) of a given continuous real function on \([a,b]\), and the corresponding statement for a function merely continuous on the interval.

**Smooth functions in \(L^p\), and convolution.**

Let \(E\) be a finite-dimensional real normed space with its Borel \(\sigma\)-algebra, let \(F\) be a real normed space, and let \(\mu\) be a measure on \(E\) that is finite on compact sets. Every continuous compactly supported \(F\)-valued function can be approximated in the \(L^p(\mu)\) norm, for every \(p\in[0,\infty]\), by a smooth compactly supported function: the support of the approximant is contained in the support of the original function (`Analysis/Normed/Lp/SmoothApprox.lean`). The same approximation holds for an arbitrary class in \(L^p\) when \(p\neq\infty\) and \(1\leq p\). Consequently, when \(p\neq\infty\) and \(1\leq p\), the smooth compactly supported functions are dense in \(L^p(E,F;\mu)\) (`MeasureTheory.Lp.dense_hasCompactSupport_contDiff`). The argument calls the manifold approximation theorem of Section 52, specialised to the normed space.

Convolution is developed for a bilinear multiplication against a Haar measure (`Analysis/Convolution.lean`). On a finite-dimensional real normed space with a Haar measure, if \(\varphi_i\) is a family of smooth bumps at the origin whose outer radii tend to \(0\) along a filter, and \(g\) is continuous with values in a complete real normed space, then the normalised convolution \((\varphi_i\star g)(x_0)\) tends to \(g(x_0)\) (`Analysis/Calculus/BumpFunction/Convolution.lean`). If \(g\) is only locally integrable, and the ratio of outer radius to inner radius stays bounded, the same convergence holds for almost every \(x_0\).

Arzelà–Ascoli supplies compactness of equicontinuous families with pointwise relatively compact ranges in the uniform topology on a compact domain (`Topology/UniformSpace/Ascoli.lean`; see Section 15). This is supporting function-space infrastructure.

### TauCeti

Normalized smooth bumps define continuous linear averaging operators of norm at most one, converging strongly to the identity as their support radii shrink, for \(1\le p<\infty\), including Banach-valued functions ([approximate identities](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Function/Lp/ApproximateIdentity.lean)). Dilated smooth compact cutoffs also converge to a Schwartz function in every Schwartz seminorm ([Schwartz approximation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Distribution/SchwartzSpace/Cutoff.lean)). Fejér means of a positive-definite sequence on \(\mathbb Z\) appear in the proof of Herglotz's theorem ([Herglotz](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Bochner/Herglotz.lean)); they are not developed as a trigonometric approximation scheme with rates.

**Synopsis entries.** Covered: 47.11, 47.12, 47.14 (Mathlib). Not covered: 47.13, 47.15–47.18.

## Smoothness, direct estimates, and inverse estimates

[Mathematical scope](SYNOPSIS47.md#smoothness-direct-estimates-and-inverse-estimates).

### Mathlib

The comparison for iterated derivatives beyond the interval in `Analysis/SpecialFunctions/Trigonometric/Chebyshev/Extremal.lean` states: if \(\deg P\le n\) and \(\lvert P\rvert\le1\) on \([-1,1]\), then \(P^{(k)}(x)\le T_n^{(k)}(x)\) for every \(x\ge1\) and every \(k\), with equality for \(0<k\le n\) only when \(P=T_n\) (`Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one`, `Polynomial.Chebyshev.eval_iterate_derivative_eq_iff_of_bounded`). Applied also to \(-P\), and combined with \(T_n'(1)=n^2\) (`Polynomial.Chebyshev.derivative_T_eval_one` in `RingTheory/Polynomial/Chebyshev.lean`), this gives Markov's inequality \(\lvert P'(\pm1)\rvert\le n^2\) at the endpoints; the bound at interior points of \([-1,1]\) is not proved. Moduli of smoothness, \(K\)-functionals, Jackson and Bernstein-type theorems are absent.

**Synopsis entries.** Partly covered: 47.24 (at the endpoints \(\pm1\) only). Not covered: 47.19–47.23, 47.25–47.30.

## Chebyshev, analytic, and rational approximation

[Mathematical scope](SYNOPSIS47.md#chebyshev-analytic-and-rational-approximation).

### TauCeti

Supporting material only. The normalized Chebyshev polynomials form a Hilbert basis of \(L^2\) for the weight \((1-x^2)^{-1/2}\) on \([-1,1]\), with coefficient, Parseval and reconstruction identities ([Chebyshev basis](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Trigonometric/Chebyshev/HilbertBasis.lean), [Parseval](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Parseval.lean)). The same basis is transported to the normalized cosines on \((0,\pi]\) ([cosine basis](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Cosine/Parseval.lean)) and, with the weight moved into the functions, to an orthonormal basis of unweighted \(L^2((-1,1])\) ([envelope basis](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Envelope.lean)). Hermite bases are in Section 48. These give \(L^2\) convergence of Chebyshev expansions, but no coefficient decay or rate in terms of the smoothness or analyticity of the function.

**Synopsis entries.** Not covered: 47.31–47.40, 47.72, 47.73.

## Splines and total positivity

[Mathematical scope](SYNOPSIS47.md#splines-and-total-positivity).

### Mathlib

Supporting material only. Totally nonnegative matrices (all minors nonnegative) are defined, with closure under submatrices, nonnegative diagonal matrices and nonnegative scalars (`Matrix.IsTotallyNonneg` in `LinearAlgebra/Matrix/Determinant/TotallyNonneg.lean`). Splines and B-splines are not defined.

**Synopsis entries.** Not covered: 47.41–47.51.

## Kernel and scattered-data approximation

[Mathematical scope](SYNOPSIS47.md#kernel-and-scattered-data-approximation).

### Mathlib

Reproducing kernel Hilbert spaces are defined for vector-valued functions, with density of the kernel functions and Moore's construction of the RKHS of a positive semidefinite kernel (`RKHS`, `RKHS.kerFun_dense`, `RKHS.OfKernel`, `RKHS.kernel_ofKernel` in `Analysis/InnerProductSpace/Reproducing.lean`). This supplies the native space; kernel interpolation, its minimum-norm property, and power-function bounds are not stated.

### TauCeti

Bochner's theorem is proved: a function on a finite-dimensional real inner product space is continuous and positive definite exactly when it is the Fourier transform of a unique finite Borel measure (`TauCeti.bochner`, `TauCeti.bochner_posSemidef`, [Bochner's theorem](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Bochner/BochnerTheorem.lean)). Supporting kernel material includes the minimal Kolmogorov decomposition of a positive-definite kernel ([Kolmogorov decomposition](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PositiveDefinite/Kernel/Kolmogorov.lean)) and universal kernels, whose sections span a dense subspace of \(C(X)\) ([universal kernels](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PositiveDefinite/Kernel/Universal.lean)).

**Synopsis entries.** Partly covered: 47.56 (Bochner's characterization; the strict positive definiteness criterion is not stated). Not covered: 47.52–47.55, 47.57, 47.58.

## Nonlinear approximation, widths, and dimension

[Mathematical scope](SYNOPSIS47.md#nonlinear-approximation-widths-and-dimension).

### TauCeti

For a bounded operator \(T\) between normed spaces, the approximation numbers \(a_n(T)=\inf\{\lVert T-R\rVert:\mathop{\mathrm{rank}}R\le n\}\) are developed, with additive and multiplicative index laws and the ideal inequality ([approximation numbers](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean)). On finite-dimensional inner product spaces they equal the singular values (Eckart–Young, `ContinuousLinearMap.singularValue_eq_linearMap_singularValues`, [Eckart–Young](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/EckartYoung.lean)), and the best rank-\(n\) approximation is attained by projecting onto the first right singular vectors ([attainment](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Attainment.lean)); min–max bounds through coercive subspaces and orthogonal tails hold in general ([min–max](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMax.lean)). For a diagonal operator on \(\ell^p\), \(1\le p\le\infty\), with decreasing coefficient magnitudes, \(a_n\) is the magnitude of the \(n\)-th coefficient and truncation attains it ([diagonal operators](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Diagonal.lean)). A bounded operator into a Hilbert space is compact exactly when its approximation numbers tend to zero ([compactness](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Compact.lean)). These are linear widths of a single operator; Kolmogorov and Gelfand widths of sets, and widths of function classes such as Sobolev balls, are not defined.

**Synopsis entries.** Partly covered: 47.64 (best rank-\(m\) approximation error equals the singular value, between finite-dimensional inner product spaces and for decreasing diagonal operators on \(\ell^p\); Kolmogorov widths not defined). Not covered: 47.59–47.63, 47.65–47.71.

## Discrepancy, ridge functions, and tractability

[Mathematical scope](SYNOPSIS47.md#discrepancy-ridge-functions-and-tractability).

**Synopsis entries.** Not covered: 47.74–47.77.
