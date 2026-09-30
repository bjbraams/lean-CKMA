# 40. One Complex Variable: Graduate Courses

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. The roots for this section are `Mathlib.Analysis.Complex.CauchyIntegral`, `Mathlib.Analysis.Complex.HasPrimitives`, `Mathlib.Analysis.Complex.TaylorSeries`, `Mathlib.Analysis.Complex.RemovableSingularity`, `Mathlib.Analysis.Complex.LocallyUniformLimit`, `Mathlib.Analysis.Complex.Liouville`, `Mathlib.Analysis.Complex.OpenMapping`, `Mathlib.Analysis.Complex.AbsMax`, `Mathlib.Analysis.Complex.Schwarz`, `Mathlib.Analysis.Complex.PhragmenLindelof`, `Mathlib.Analysis.Complex.JensenFormula`, `Mathlib.Analysis.Complex.BorelCaratheodory`, `Mathlib.Analysis.Complex.Hadamard`, `Mathlib.Analysis.Complex.MeanValue`, `Mathlib.Analysis.Complex.RealDeriv`, `Mathlib.Analysis.Complex.Poisson`, `Mathlib.Analysis.Complex.Polynomial.Basic`, `Mathlib.Analysis.Complex.Polynomial.GaussLucas`, `Mathlib.Analysis.Complex.BranchLogRoot`, `Mathlib.Analysis.Complex.Harmonic.Analytic`, `Mathlib.Analysis.Complex.Harmonic.MeanValue`, `Mathlib.Analysis.Complex.Harmonic.Liouville`, `Mathlib.Analysis.Complex.Harmonic.Poisson`, `Mathlib.Analysis.Complex.UnitDisc.Basic`, `Mathlib.Analysis.Complex.UpperHalfPlane.Basic`, `Mathlib.Analysis.Complex.UpperHalfPlane.Metric`, `Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction`, `Mathlib.Analysis.Complex.UpperHalfPlane.Measure`, `Mathlib.Analysis.Complex.RiemannMapping`, `Mathlib.Analysis.Analytic.IsolatedZeros`, `Mathlib.Analysis.Analytic.Uniqueness`, and `Mathlib.Analysis.Meromorphic.Basic`.

**Namespaces.** `Complex`, with nested `HadamardThreeLines` and `UnitDisc`. The Phragmén–Lindelöf statements are `PhragmenLindelof`. Liouville’s theorem for maps on a complex normed space is `Differentiable`. Harmonic functions are `InnerProductSpace`, with `HarmonicAt`, `HarmonicOnNhd`, and `HarmonicContOnCl`. Polynomials are `Polynomial`, with nested `Gal` for Galois-theoretic counts of roots. The upper half-plane is `UpperHalfPlane`, with nested `GLAction`, `PGLAction`, and `SLAction`, and `ModularGroup` for the integral modular action. Meromorphic functions are `MeromorphicAt`, `MeromorphicOn`, and `Meromorphic`. The identity theorem is `AnalyticAt`, `AnalyticOnNhd`, and `HasFPowerSeriesAt`.

This note records the graduate theorems of one complex variable that are proved in this checkout: the Cauchy theory and its consequences, the maximum principle and the Schwarz lemma, harmonic functions, the disc and the half-plane, and the calculus of meromorphic functions. The residue theorem is not here. The Riemann mapping theorem is not claimed; the file that bears its name says that it holds only lemmas strictly weaker than the theorem.

## The Cauchy integral formula

The integral theorems allow a countable exceptional set. Throughout, \(E\) is a complex normed space. Where a value is recovered from a circle integral, or a power series is summed, \(E\) is complete. The introductory comment of the Cauchy file also speaks of a second-countable topology on \(E\); that hypothesis is not written on the theorems below (`Analysis/Complex/CauchyIntegral.lean`).

On a closed rectangle, if \(f\) is continuous up to the boundary and real-differentiable off a countable set in the open rectangle, and if the Cauchy–Riemann defect is integrable, the integral of \(f\) over the boundary equals the integral of \(2i\,\partial f/\partial\bar z\) over the rectangle. If instead \(f\) is complex-differentiable off a countable set, the boundary integral vanishes. This is the Cauchy–Goursat theorem for a rectangle. The same vanishing holds for a function complex-differentiable on the whole closed rectangle, and that case does not use completeness of \(E\).

On a closed annulus \(r\le |z-c|\le R\), continuity on the closed annulus and complex-differentiability off a countable set in the open annulus make the integrals of \((z-c)^{-1}f(z)\) over the two boundary circles equal. Letting the inner radius tend to zero gives the Cauchy formula at the center: if \(f\) is continuous on the closed disc except possibly at the center, complex-differentiable off a countable set in the punctured disc, and tends to a value \(y\) at the center, then
\[
\oint_{|z-c|=R}\frac{f(z)}{z-c}\,dz = 2\pi i\, y.
\]
If \(f\) is continuous on the whole closed disc, the same formula holds with \(y=f(c)\). Consequently the integral of \(f\) itself over the circle vanishes.

For a point \(w\) inside the disc, not merely the center,
\[
\frac{1}{2\pi i}\oint_{|z-c|=R}\frac{f(z)}{z-w}\,dz = f(w),
\]
again with continuity on the closed disc and complex differentiability off a countable set in the open disc. The same identity holds when \(f\) is complex-differentiable on the open disc and continuous on the closure, and when it is complex-differentiable on the closed disc. For scalar-valued \(f\) the integrand may be written as ordinary division.

The circle integral depends holomorphically on the point \(w\) off the circle of integration. Expanding it produces a power series. Thus a function continuous on a closed disc of positive radius and complex-differentiable off a countable set in the open disc is analytic on the open disc, with coefficients given by the Cauchy integrals. Complex differentiability on an open set in \(\mathbb{C}\) is therefore equivalent to complex analyticity on that set, the derivative is again complex-differentiable, and the function is continuously differentiable of every finite order. An entire function, meaning a function complex-differentiable on all of \(\mathbb{C}\), is given by its Cauchy series on every disc, and that series has infinite radius.

At the center, the derivatives themselves are circle integrals. If \(f\) is continuous on the closed disc and complex-differentiable off a countable set inside, then
\[
\oint_{|z-c|=R}\frac{f(z)}{(z-c)^{n+1}}\,dz = \frac{2\pi i}{n!}\,f^{(n)}(c).
\]
The file notes that the corresponding formula for a point other than the center is not included. The first derivative at a general interior point is recovered later, after the removable-singularity theorem, as the circle integral of \((z-w)^{-2}f(z)\) (`Analysis/Complex/RemovableSingularity.lean`).

Cauchy’s estimates follow. If \(|f|\le C\) on the circle of radius \(R\) about \(c\), and \(f\) is holomorphic inside and continuous up to the boundary, then \(\|f^{(n)}(c)\|\le n!\,C/R^n\). The first-derivative bound \(\|f'(c)\|\le C/R\) does not need completeness of the codomain; the higher-derivative bound does (`Analysis/Complex/Liouville.lean`).

## Primitives, Taylor series, and removable singularities

A function is conservative on a set when its integrals over rectangles contained in the set vanish, and exact when it is the complex derivative of some map on that set. Every complex-differentiable function is conservative. On a disc, a continuous conservative function is exact: this is Morera’s theorem for a disc, and it uses completeness of the codomain. In particular, a holomorphic function on a disc has a primitive, and an entire function has a primitive on \(\mathbb{C}\). The file says explicitly that the extension to a general simply connected domain is still to be done (`Analysis/Complex/HasPrimitives.lean`). Branches of the logarithm on simply connected domains are proved by a different route, below.

On any open disc on which \(f\) is complex-differentiable, with values in a complex Banach space, the Taylor series at the center converges to \(f\):
\[
f(z)=\sum_{n=0}^\infty\frac{f^{(n)}(c)}{n!}(z-c)^n.
\]
The same holds on a disc of infinite radius, and therefore for every entire function at every center (`Analysis/Complex/TaylorSeries.lean`).

Riemann’s removable-singularity theorem: if \(f\) is complex-differentiable on a punctured neighborhood of \(c\) and \(f(z)-f(c)=o\bigl((z-c)^{-1}\bigr)\), then \(f\) has a limit at \(c\), and redefining \(f\) at \(c\) to be that limit makes it complex-differentiable on the full neighborhood. Boundedness on the punctured neighborhood is enough for the same conclusion. If \(f\) is already continuous at \(c\) and holomorphic off \(c\), it is analytic at \(c\) (`Analysis/Complex/RemovableSingularity.lean`).

## Locally uniform limits

On an open set in the plane, a locally uniform limit of holomorphic functions with values in a complex Banach space is holomorphic. The derivatives converge locally uniformly to the derivative of the limit. A series of holomorphic functions dominated on the set by a summable sequence of constants may be differentiated termwise. Logarithmic derivatives pass to the limit at any point where the limit function does not vanish (`Analysis/Complex/LocallyUniformLimit.lean`).

## Liouville’s theorem and polynomials

A bounded complex-differentiable map from a complex normed space into a complex normed space is constant. The same conclusion holds, when the domain is nontrivial, if the map tends to a finite limit along the filter of complements of compact sets. The proof reduces to the plane by restricting to complex lines, and then uses Cauchy’s estimate on larger and larger circles (`Analysis/Complex/Liouville.lean`).

The fundamental theorem of algebra is the case of a nonconstant polynomial. If a nonconstant \(f\in\mathbb{C}[X]\) had no root, \(1/f\) would be entire and would tend to zero at infinity, hence would vanish, which is absurd. Thus every nonconstant complex polynomial has a root, and \(\mathbb{C}\) is algebraically closed. An algebraic extension of \(\mathbb{R}\) is isomorphic, as an \(\mathbb{R}\)-algebra, to \(\mathbb{R}\) or to \(\mathbb{C}\). An irreducible polynomial over \(\mathbb{R}\) has degree at most two (`Analysis/Complex/Polynomial/Basic.lean`).

The Gauss–Lucas theorem: the roots of the derivative of a nonconstant complex polynomial lie in the convex hull of the roots of the polynomial. The proof writes a root of the derivative as an explicit convex combination of the roots, with nonnegative weights built from the multiplicities (`Analysis/Complex/Polynomial/GaussLucas.lean`).

## Open mapping and the maximum modulus

A function analytic at a point of a complex normed space, with values in \(\mathbb{C}\), is either eventually constant there, or else it carries every neighborhood of the point onto a neighborhood of the value. On a preconnected set, an analytic function is either constant or open. A nonconstant complex polynomial is an open quotient map of the plane, and so are the maps \(z\mapsto z^n\) for \(n\neq 0\), including on the punctured plane for integer powers (`Analysis/Complex/OpenMapping.lean`).

If a holomorphic function on a connected open subset of the plane has constant real part, or constant imaginary part, then it is constant.

The maximum modulus principle is stated for maps between complex normed spaces. If the norm attains a maximum at an interior point, the norm is constant on any closed ball about that point that stays in the domain of differentiability, and constant on any preconnected open set on which the maximum is attained. If the codomain is strictly convex over \(\mathbb{R}\), as \(\mathbb{C}\) is, the function itself is constant, not merely of constant norm. A local maximum of the norm is therefore a point of local constancy. A local minimum of the norm of a holomorphic function with values in \(\mathbb{C}\) forces the function to be locally constant or to vanish at the point. On a nonempty bounded set in a finite-dimensional complex space, a function holomorphic inside and continuous up to the closure attains its maximum modulus on the frontier. Two such functions that agree on the frontier agree on the closure (`Analysis/Complex/AbsMax.lean`).

## Schwarz, Borel–Carathéodory, Phragmén–Lindelöf, and the three-lines theorem

The Schwarz lemma is stated for analytic maps between complex normed spaces. If \(f\) sends the open ball of radius \(R_1\) about \(c\) into the closed ball of radius \(R_2\) about \(f(c)\), then \(\operatorname{dist}(f(z),f(c))\le (R_2/R_1)\operatorname{dist}(z,c)\) on the open ball, and the operator norm of the derivative at \(c\) is at most \(R_2/R_1\). If the two radii agree, distances to the center do not increase and the derivative at the center has norm at most one. If in addition the center is the origin, \(f(0)=0\), and the target ball is centered at the origin, then \(\|f(z)\|\le\|z\|\). A vanishing of order \(n\) improves the estimate by an extra factor \(\operatorname{dist}(z,c)/R_1\). If the norm of the difference quotient attains the bound \(R_2/R_1\) at even one interior point, and the codomain is strictly convex over \(\mathbb{R}\), then \(f\) is affine on the ball, with slope of that norm. Strict convexity is necessary: the map \(z\mapsto (z,z^2)\) from \(\mathbb{C}\) to \(\mathbb{C}\times\mathbb{C}\) sends the open unit ball into the closed unit ball, has derivative of norm one at the origin, and is not affine (`Analysis/Complex/Schwarz.lean`).

The Borel–Carathéodory theorem: if \(f\) is holomorphic on \(|z|<R\), the real part of \(f\) is at most \(M>0\) there, and \(R>0\), then for \(|z|<R\)
\[
\|f(z)\|\le \frac{2M\|z\|}{R-\|z\|}+\|f(0)\|\frac{R+\|z\|}{R-\|z\|}.
\]
If \(f(0)=0\), the second term drops. The proof applies the Schwarz lemma to \(f(z)/(2M-f(z))\) (`Analysis/Complex/BorelCaratheodory.lean`).

The Phragmén–Lindelöf principle extends the maximum modulus principle to unbounded domains, for maps into a complex normed space. In the horizontal strip \(a<\operatorname{Im} z<b\), a function holomorphic inside and continuous up to the closure, bounded by a constant \(C\) on the two boundary lines, and of growth \(O\bigl(\exp(B\exp(c|\operatorname{Re} z|))\bigr)\) for some \(c<\pi/(b-a)\), is bounded by the same \(C\) throughout the closed strip. It is enough to check the growth for large \(|\operatorname{Re} z|\). The vertical strip \(a<\operatorname{Re} z<b\) is the same statement after swapping real and imaginary parts. In each coordinate quadrant, growth \(O\bigl(\exp(B\|z\|^c)\bigr)\) for some \(c<2\), together with a bound \(C\) on the two boundary rays, gives the bound \(C\) on the closed quadrant. In the open right half-plane, the same growth, a bound on the imaginary axis, and either a bound or a limit zero along the positive real axis, give the bound on the closed half-plane. Differences of two functions obeying the growth hypotheses still obey them, so functions that agree on the boundary and are not too large agree throughout the closed region (`Analysis/Complex/PhragmenLindelof.lean`).

The Hadamard three-lines theorem is the convexity of the logarithm of the maximum modulus across a vertical strip. It is not a factorization theorem. If \(f\), with values in a complex normed space, is bounded and continuous on the closed strip \(l\le\operatorname{Re} z\le u\), holomorphic on the open strip, and bounded by \(A\) on the left edge and by \(B\) on the right edge, then on the closed strip
\[
\|f(z)\|\le A^{1-t}B^{t},\qquad t=\frac{\operatorname{Re} z-l}{u-l}.
\]
The proof reduces the strip to \(0\le\operatorname{Re} z\le 1\) and applies Phragmén–Lindelöf (`Analysis/Complex/Hadamard.lean`).

## Mean value, the Poisson formula, and real derivatives

If \(f\) takes values in a complex Banach space, is continuous on a closed disc, and is complex-differentiable off a countable set inside, its circle average on the boundary equals its value at the center. More generally, for \(w\) inside the disc the circle average of \(\frac{z-c}{z-w}f(z)\) equals \(f(w)\) (`Analysis/Complex/MeanValue.lean`).

The same value is a weighted average. The Herglotz–Riesz kernel is \(((z-c)+(w-c))/((z-c)-(w-c))\), and its real part agrees on the circle of integration with the Poisson kernel. If \(f\) is holomorphic on a disc and continuous on the closure, with Banach values, the circle average of the Poisson kernel against \(f\) equals \(f(w)\) at every interior point (`Analysis/Complex/Poisson.lean`).

Complex differentiability implies real differentiability of the underlying map of real planes. The real derivative is multiplication by the complex derivative. Restricting a holomorphic function to the real axis, the derivative of the real part is the real part of the complex derivative (`Analysis/Complex/RealDeriv.lean`).

## Isolated zeros and the identity theorem

These are theorems about analytic functions of one variable, on a nontrivially normed field, and they apply to holomorphic functions because complex differentiability on an open set is analyticity (`Analysis/Analytic/IsolatedZeros.lean`, `Analysis/Analytic/Uniqueness.lean`).

A function analytic at a point is either identically zero on a neighborhood of the point, or else has no zero in some punctured neighborhood. Equivalently, unless it vanishes identically nearby, it has the form \((z-z_0)^n g(z)\) with \(g\) analytic and nonzero at \(z_0\), and the exponent is unique. On a preconnected set, if an analytic function vanishes on a set that accumulates at a point of the set, it vanishes throughout the set. Two analytic functions on a preconnected set that agree on such an accumulating set agree throughout the set. The corresponding statements in several variables require agreement on a whole neighborhood; the form that uses an accumulation point is one-variable. If a product of two analytic functions vanishes on a preconnected open set, one of the factors vanishes on that set.

The order of vanishing is the extended natural number in this factorization, with the value infinity when the function vanishes on a neighborhood. If the function is not analytic at the point, the order is a junk value zero (`Analysis/Analytic/Order.lean`).

## Branches of the logarithm and of roots

On a locally path-connected space, if \(g\) is continuous on an open simply connected set \(U\) and does not take the value \(0\) on \(U\), then \(g\) has a continuous logarithm on \(U\): a function \(f\), continuous on \(U\), with \(\exp(f(x))=g(x)\) for every \(x\in U\). For every positive integer \(n\) it likewise has a continuous \(n\)th root. If \(g\) takes values in the open unit disc, the root may be taken with values in the open unit disc (`Analysis/Complex/BranchLogRoot.lean`). This is the input to the partial Riemann-mapping argument below. It is not the missing construction of primitives on a general simply connected domain.

## Harmonic functions

A function on a finite-dimensional real inner-product space, with values in a real normed space, is harmonic at a point when it is twice continuously real-differentiable and its Laplacian vanishes on a neighborhood of the point (`Analysis/InnerProductSpace/Harmonic/Basic.lean`).

On the complex plane, if a real-valued function is harmonic at a point, then \(\partial f/\partial x-i\,\partial f/\partial y\) is holomorphic at that point. On an open disc, a real-valued harmonic function is the real part of a holomorphic function, and the same holds for a harmonic function on the whole plane. Harmonic functions \(\mathbb{C}\to\mathbb{R}\) are therefore real-analytic. The file notes that real-analyticity on a general finite-dimensional inner-product space, rather than only on \(\mathbb{C}\), is not proved (`Analysis/Complex/Harmonic/Analytic.lean`).

Harmonic functions on \(\mathbb{C}\) with values in a real Banach space have the mean-value property: the circle average equals the value at the center, either when the function is harmonic on a neighborhood of the closed disc, or when it is harmonic on the open disc and continuous on the closure. Completeness of the codomain is used because the circle average is a Bochner integral (`Analysis/Complex/Harmonic/MeanValue.lean`). For real-valued functions the Poisson integral formula holds in the same two settings: the circle average of the Poisson kernel, or of the real part of the Herglotz–Riesz kernel, against \(f\) equals \(f(w)\) inside the disc. The extension of this formula to vector-valued harmonic functions is marked as not yet done (`Analysis/Complex/Harmonic/Poisson.lean`).

A bounded harmonic function on the whole plane, with values in a real normed space, is constant. The real-valued case is reduced to Liouville’s theorem by passing to the exponential of a holomorphic function with the given real part (`Analysis/Complex/Harmonic/Liouville.lean`).

## The disc and the upper half-plane

The open unit disc is the open unit ball of \(\mathbb{C}\), made into a cancellative commutative semigroup by the multiplication of \(\mathbb{C}\). The closed unit disc is the corresponding monoid. The file is titled as the Poincaré disc, but what it contains is this algebraic and topological structure, together with the branch of an \(n\)th root already cited. It does not construct a hyperbolic metric on the disc (`Analysis/Complex/UnitDisc/Basic.lean`).

The upper half-plane is the set of complex numbers with positive imaginary part. The group \(\mathrm{GL}(2,\mathbb{R})\) acts by fractional linear transformations. The action is extended from the positive-determinant subgroup by complex conjugation, so that the matrix \(\operatorname{diag}(-1,1)\) acts by \(z\mapsto -\overline{z}\) (`Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`).

The Poincaré distance is
\[
\operatorname{dist}(z,w)=2\operatorname{arsinh}\Bigl(\frac{|z-w|}{2\sqrt{\operatorname{Im} z\cdot\operatorname{Im} w}}\Bigr).
\]
It induces the Euclidean topology. Hyperbolic balls, closed balls, and spheres are Euclidean balls, closed balls, and spheres with a different center and radius. The group \(\mathrm{SL}(2,\mathbb{R})\) acts by isometries (`Analysis/Complex/UpperHalfPlane/Metric.lean`).

The measure \(dx\,dy/y^2\), obtained by weighting Lebesgue measure on the half-plane by the reciprocal square of the imaginary part, is invariant under \(\mathrm{GL}(2,\mathbb{R})\) (`Analysis/Complex/UpperHalfPlane/Measure.lean`). The half-plane carries the structure of a complex manifold, and Möbius transformations of positive determinant act holomorphically (`Analysis/Complex/UpperHalfPlane/Manifold.lean`).

## Meromorphic functions

Meromorphy is developed for maps from a nontrivially normed field into a normed space over that field, and then used on \(\mathbb{C}\). A function is meromorphic at a point when, after multiplication by a high enough power of \((z-x)\), it agrees on a punctured neighborhood with a function analytic at the point. The original value at the point itself does not matter. Sums, products, inverses, integer powers, and compositions on the right with analytic functions preserve meromorphy. Near the point, a meromorphic function is analytic except possibly at the point itself, once the codomain is complete (`Analysis/Meromorphic/Basic.lean`).

The order at a point lies in \(\mathbb{Z}\cup\{\infty\}\). It is infinite precisely when the function vanishes on a punctured neighborhood, and otherwise it is the unique integer \(n\) such that \(f(z)=(z-x)^n g(z)\) with \(g\) analytic and nonzero at \(x\). If the function is not meromorphic at the point, the order is a junk value zero. The order is additive for products, is multiplied by \(n\) under the \(n\)th power, and changes sign under inversion. A negative order is a pole, a positive order is a zero, and order zero is a nonzero finite limit (`Analysis/Meromorphic/Order.lean`).

The divisor of a function meromorphic on a set sends each point to this order, with the infinite order replaced by zero, and vanishes off the set. It is a locally finite integer-valued function. It is additive for products, and the divisor of an inverse is the negative. On a set where the function is analytic the divisor is nonnegative (`Analysis/Meromorphic/Divisor.lean`).

A meromorphic function can be altered on a locally finite subset of its domain and remain meromorphic. The normal form picks, in each such class, a representative that near every point has the shape \((z-x)^n g(z)\) with \(g\) analytic and nonvanishing at \(x\) (`Analysis/Meromorphic/NormalForm.lean`). The value \(g(x)\) is the trailing coefficient (`Analysis/Meromorphic/TrailingCoefficient.lean`). Zeros are isolated in the sense that a meromorphic function which is not locally zero vanishes off a discrete subset of its domain, and two meromorphic functions that agree on a set accumulating at a non-isolated point of a domain agree on a punctured neighborhood of that point (`Analysis/Meromorphic/IsolatedZeros.lean`).

On a set with compact closure, or more generally when only finitely many zeros and poles are present, a meromorphic scalar function differs from an analytic function without zeros by a finite product \(\prod (z-u)^{d(u)}\) (`Analysis/Meromorphic/FactorizedRational.lean`). The logarithmic derivative turns products into sums off a discrete set, provided no factor is locally zero (`Analysis/Meromorphic/LogDeriv.lean`). The gamma function is meromorphic on the plane (`Analysis/Meromorphic/Complex.lean`).

Jensen’s formula belongs to this calculus and is the start of the value-distribution theory in the next section. If \(f\) is meromorphic on the closed disc of radius \(|R|\) about \(c\), and \(R\neq 0\), the circle average of \(\log\|f\|\) equals \(\log\) of the norm of the trailing coefficient at \(c\), plus a sum over the divisor that accounts for the zeros and poles inside the disc (`Analysis/Complex/JensenFormula.lean`).

## Further classical results

Abel's limit theorem: if a power series of radius \(1\) converges at \(1\), its sum is the limit of the function as \(z\to1\) within a Stolz angle (`Analysis/Complex/AbelLimit.lean`). The exponential, and \(z\mapsto z^n\) for \(n\neq0\), are covering maps of \(\mathbb{C}\setminus\{0\}\), and a complex polynomial is a covering map over its regular values (`Analysis/Complex/CoveringMap.lean`). A function meromorphic on a closed disc is a finite Blaschke-type product of canonical factors, of modulus one on the boundary circle, times an analytic function without zeros; this is the finite canonical decomposition used in Jensen's formula (`Analysis/Complex/CanonicalDecomposition.lean`).

## Toward the Riemann mapping theorem

The file states that it contains partial results toward the Riemann mapping theorem. The pinned module comment refers to an external proof in community pull request `33505` and describes a staged integration. This is a report of that comment, not a theorem in the checkout or a check of the current pull-request status. For now, the file says, all lemmas in it are strictly weaker than the final theorem, so they are private (`Analysis/Complex/RiemannMapping.lean`).

The Riemann mapping theorem is therefore not a theorem of this checkout. What the file actually contains are two steps, both for an open simply connected set \(U\subset\mathbb{C}\) that is not the whole plane. First, there is a complex-differentiable function on \(U\), injective, with nonvanishing derivative, whose image is not dense in \(\mathbb{C}\). It is obtained by choosing a point outside \(U\) and taking a continuous square root of \(z-a\), which exists by the branch theorem above. Second, there is a complex-differentiable function carrying \(U\) into the open unit disc, injective on \(U\), with nonvanishing derivative. The comment on the second statement says that once the proof of the Riemann mapping theorem is merged, that lemma will be made private. Neither statement produces a bijection onto the disc, a holomorphic inverse, or a normalization at a chosen point.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

TauCeti supplies much of the missing classical one-variable theory. It defines contour winding numbers, proves their integrality for closed curves off the curve, and proves residue and argument-principle identities, including a residue theorem for meromorphic functions on a closed disc with no boundary poles ([winding numbers](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Contour/Winding/Number/Basic.lean), [integrality](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Contour/Winding/Integer.lean), [residues](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Contour/Residue/Theorem.lean), [argument principle](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Contour/Argument/Principle.lean)). Meromorphic functions have canonical finite principal parts plus analytic remainders near a point ([local Laurent data](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Contour/MeromorphicLaurent.lean)); this is not a Laurent-series theorem for an arbitrary holomorphic function on an annulus.

The homology form of Cauchy's theorem is proved by Dixon's argument: for a closed piecewise-\(C^1\) curve null-homologous in an open set \(\Omega\), the integral of every function holomorphic on \(\Omega\) vanishes, and Cauchy's formula holds with the winding number as multiplicity ([homology Cauchy theorem](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Contour/HomologyCauchy.lean)). Rouché's theorem in Estermann's symmetric form and Hurwitz's theorem on zeros of locally uniform limits are proved ([Rouché](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Complex/Conformal/Rouche.lean), [Hurwitz](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Complex/Conformal/Hurwitz.lean)), as are Morera's theorem ([Morera](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Complex/Conformal/Morera.lean)) and the Schwarz reflection principle across a circle, through Painlevé removability ([reflection](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Complex/Conformal/Reflection/Circle/Principle.lean)).

Montel's selection theorem is proved for locally bounded holomorphic families, with proper complex normed target, and holomorphic locally uniform limits ([Montel](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Complex/Conformal/Montel/Basic.lean)). The Riemann mapping theorem produces a biholomorphism of any nonempty simply connected proper plane domain with the disc ([existence](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Complex/Conformal/RiemannMapping/Existence.lean), [equivalence](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Complex/Conformal/RiemannMapping/Conformal.lean)). Vitali's convergence theorem upgrades pointwise convergence on a set with an accumulation point to locally uniform convergence for locally bounded sequences ([Vitali](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Complex/Conformal/Vitali.lean)). Analytic continuation along every path gives a single global holomorphic branch on a simply connected domain ([monodromy](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Complex/Conformal/GlobalBranch.lean)).

The disc has a Poincaré metric and Schwarz–Pick theory ([metric](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Complex/Conformal/Poincare/MetricSpace.lean), [Schwarz–Pick](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Complex/Conformal/Poincare/SchwarzPick.lean)). Harnack and mean-value results beyond the plane are recorded in Section 33. The conformal boundary-correspondence results are recorded in Section 43.

An explicit global primitive for a holomorphic function on the upper half-plane is constructed by integration along horizontal–vertical paths ([primitive](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Complex/UpperHalfPlane/Primitive.lean)).

The residue theorem also holds for finite integer contour cycles that are null-homologous in the open domain and avoid the finite singularity set. Each residue is weighted by the cycle's winding number. The same file proves Cauchy's formula for iterated derivatives at any point off the cycle, so the higher-derivative Cauchy-formula gap is filled ([cycle residues and derivative formulas](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Contour/Cycle/Residue.lean)). A principal-value version permits poles on suitable piecewise-\(C^1\) immersed contours under explicit local regularity conditions ([generalized residue theorem](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Contour/Cycle/HungerbuhlerWasem.lean)).

## Topics of Section 40 not found in either inspected library

- The Weierstrass and Mittag-Leffler theorems on prescribed zeros and poles, and Runge's approximation theorem.
- The little and great Picard theorems.
- A Laurent-series expansion for an arbitrary holomorphic function on an annulus. TauCeti proves local finite principal-part decompositions at meromorphic singularities, as well as residue and argument-principle theorems.
- A directly stated primitive-existence theorem on every simply connected plane domain. Primitive constructions on discs, the whole plane, and the upper half-plane, and the monodromy theorem, are available.
- Real-analyticity of harmonic functions on a finite-dimensional real inner-product space other than \(\mathbb{C}\), and the Poisson formula for vector-valued harmonic functions. They are marked as not yet proved in the Mathlib source. TauCeti proves mean-value properties on Euclidean balls and spheres in arbitrary finite dimension, including Banach-valued harmonic functions.
