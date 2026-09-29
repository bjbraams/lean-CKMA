# 49. Special Functions, Integral Transforms, and Classical Formulae

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. Some roots below are directory prefixes; the individual `.lean` files cited are the importable modules. The roots for this section are `Mathlib.Analysis.SpecialFunctions.Gamma.Basic`, `Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup`, `Mathlib.Analysis.SpecialFunctions.Gamma.Beta`, `Mathlib.Analysis.SpecialFunctions.Gamma.Digamma`, `Mathlib.Analysis.SpecialFunctions.Stirling`, `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`, `Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform`, `Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation`, `Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric`, `Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric`, `Mathlib.Analysis.SpecialFunctions.Bessel`, `Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass`, `Mathlib.Analysis.MellinTransform`, `Mathlib.Analysis.MellinInversion`, `Mathlib.Analysis.SpecialFunctions.FrullaniIntegral`, `Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd`, and `Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric`.

**Namespaces.** `Complex` and `Real` for \(\Gamma\), the Beta integral, the digamma function, and the Gaussian evaluations; `Real.BohrMollerup` for the auxiliary limit in the uniqueness argument; `Stirling` for the sequence and the asymptotic comparison; `Frullani` for Frullani’s integral; `PeriodPair` for the Weierstrass \(\wp\)-function; `Polynomial` is not the home of these analytic formulae. The exponential and the trigonometric functions live under `Mathlib.Analysis.SpecialFunctions` and `Mathlib.Analysis.Complex.Trigonometric`.

The classical formulae that are proved are the Gamma function with Bohr–Mollerup, reflection, and Legendre doubling; Stirling’s asymptotic; the Gaussian integral and its Fourier transform; a theta transformation; the hypergeometric series and the Bessel function of the first kind as a regularised series; the Weierstrass \(\wp\)-function and its differential equation; Mellin inversion; Frullani’s integral; Euler’s sine product; and \(\int\log\sin\).

## The exponential and the trigonometric functions

The complex and real exponential functions satisfy \(\frac{d}{dx}\exp x=\exp x\) (`Analysis/SpecialFunctions/ExpDeriv.lean`). Euler’s formula is \(\exp(x I)=\cos x+\sin x\cdot I\) (`Analysis/Complex/Trigonometric.lean`). The real and complex logarithm and the inverse trigonometric functions are developed in the same directory; this note does not catalogue them.

## Gamma, Beta, and digamma

Euler’s integral \(\Gamma(s)=\int_0^\infty e^{-x}x^{s-1}\,dx\) converges for real \(s>0\) and for complex \(s\) with positive real part. The function \(\Gamma\) is the unique extension of that integral by the recurrence \(\Gamma(s+1)=s\Gamma(s)\) for \(s\neq 0\). At the nonpositive integers, where the recurrence does not determine a value, the function is set equal to \(0\) by convention, and it is not continuous there. One has \(\Gamma(1)=1\) and \(\Gamma(n+1)=n!\). The reciprocal \(1/\Gamma\) is entire. Complex conjugation passes inside \(\Gamma\) (`Analysis/SpecialFunctions/Gamma/Basic.lean`, `Analysis/SpecialFunctions/Gamma/Beta.lean`).

On the positive reals, \(\Gamma\) is positive, and both \(\Gamma\) and \(\log\circ\Gamma\) are convex. The Bohr–Mollerup theorem is the uniqueness statement: a function \(f:(0,\infty)\to\mathbb{R}\) which is positive, whose logarithm is convex, and which satisfies \(f(1)=1\) and \(f(y+1)=y\,f(y)\) for every \(y>0\), agrees with \(\Gamma\) on \((0,\infty)\) (`Analysis/SpecialFunctions/Gamma/BohrMollerup.lean`, `eq_Gamma_of_log_convex`). The same argument yields a logarithmic Euler limit: for \(x>0\),
\[
x\log n+\log n!-\sum_{m=0}^{n}\log(x+m)\to\log\Gamma(x).
\]
For every complex \(s\), the sequence \(n^s\,n!/\bigl(s(s+1)\cdots(s+n)\bigr)\) tends to \(\Gamma(s)\) (`Analysis/SpecialFunctions/Gamma/Beta.lean`). On \((0,1]\), \(\Gamma\) is strictly decreasing, and on \([2,\infty)\) it is strictly increasing. A global minimum on \((0,\infty)\) exists and lies in \((1,2)\); uniqueness of that minimiser is marked as future work.

Legendre’s doubling formula is proved, first for positive real \(s\) by Bohr–Mollerup and then for every real and every complex \(s\) by continuation, using that \(1/\Gamma\) is entire:
\[
\Gamma(s)\,\Gamma\bigl(s+\tfrac12\bigr)=\Gamma(2s)\,2^{1-2s}\sqrt{\pi}.
\]
The general Gauss multiplication formula for an integer \(k\geq 3\) is a header TODO in the Bohr–Mollerup file, not a theorem.

The Beta integral \(B(u,v)=\int_0^1 x^{u-1}(1-x)^{v-1}\,dx\) converges when the real parts of \(u\) and \(v\) are positive, and it is symmetric. In that range, \(\Gamma(u)\Gamma(v)=\Gamma(u+v)\,B(u,v)\), hence \(B(u,v)=\Gamma(u)\Gamma(v)/\Gamma(u+v)\). Euler’s reflection formula, for every complex \(z\) and every real \(s\), is \(\Gamma(z)\Gamma(1-z)=\pi/\sin(\pi z)\). Combined with the convention at the poles, \(\Gamma(z)=0\) if and only if \(z\) is a nonpositive integer. The Gaussian integral below gives \(\Gamma(1/2)=\sqrt{\pi}\).

The digamma function is the logarithmic derivative \(\psi=\Gamma'/\Gamma\). At \(0\), where \(\Gamma\) is not differentiable, the logarithmic derivative is \(0\). Off the nonpositive integers, \(\psi(s+1)=\psi(s)+1/s\), and \(\psi(n+1)=H_n-\gamma\) with \(H_n\) the \(n\)-th harmonic number, so \(\psi(1)=-\gamma\). Also \(\psi(1/2)=-2\log 2-\gamma\). For nonintegral \(s\), \(\psi(1-s)=\psi(s)+\pi\cot(\pi s)\). The duplication formula \(\psi(2s)=\tfrac12\bigl(\psi(s)+\psi(s+1/2)\bigr)+\log 2\) holds when \(2s\) avoids the nonpositive integers. The function is meromorphic. Gauss’s integral representation of \(\psi\) is a TODO (`Analysis/SpecialFunctions/Gamma/Digamma.lean`).

## Stirling

Write
\[
s_n=\frac{n!}{\sqrt{2n}\,(n/e)^n}
\]
for \(n\geq 1\), and \(s_0=0\). Then \(s_n\to\sqrt{\pi}\). Equivalently, along the filter of large natural numbers,
\[
n!\;\sim\;\sqrt{2\pi n}\,(n/e)^n
\]
(`Analysis/SpecialFunctions/Stirling.lean`, `factorial_isEquivalent_stirling`). The comparison \(s_n\geq\sqrt{\pi}\) for every \(n\geq 1\) rearranges to a lower bound valid for every \(n\), including \(n=0\):
\[
\sqrt{2\pi n}\,(n/e)^n\leq n!.
\]
The file records this as a lower bound only: the asymptotic equivalence supplies the matching upper bound for all sufficiently large \(n\), and the inequality above does not. Successive logarithms satisfy Robbins’ stepwise bound \(\log s_n-\log s_{n+1}\leq 1/(12n(n+1))\) for every natural number \(n\).

## The Gaussian integral, its Fourier transform, and a theta identity

For real \(b\), \(\int_{-\infty}^{\infty}\exp(-b x^2)\,dx=\sqrt{\pi/b}\), both sides being \(0\) when \(b\leq 0\). For complex \(b\) with positive real part, \(\int_{-\infty}^{\infty}\exp(-b x^2)\,dx=(\pi/b)^{1/2}\). The integral over \((0,\infty)\) is half of the full integral. In particular \(\Gamma(1/2)=\sqrt{\pi}\) (`Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`).

For \(\operatorname{Re} b>0\) and complex \(t\),
\[
\int_{-\infty}^{\infty}\exp(I t x)\exp(-b x^2)\,dx=(\pi/b)^{1/2}\exp\bigl(-t^2/(4b)\bigr).
\]
In the symmetric normalisation, the Fourier transform of \(x\mapsto\exp(-\pi b x^2)\) is \(t\mapsto b^{-1/2}\exp(-\pi t^2/b)\). On a finite-dimensional real inner product space of dimension \(d\), \(\int\exp(-b\|v\|^2)\,dv=(\pi/b)^{d/2}\), and the Fourier transform of \(v\mapsto\exp(-b\|v\|^2)\) at \(w\) is \((\pi/b)^{d/2}\exp(-\pi^2\|w\|^2/b)\) (`Analysis/SpecialFunctions/Gaussian/FourierTransform.lean`).

Jacobi’s transformation of the quadratic theta series follows: for \(\operatorname{Re} a>0\) and complex \(b\),
\[
\sum_{n\in\mathbb{Z}}\exp(-\pi a n^2+2\pi b n)=a^{-1/2}\sum_{n\in\mathbb{Z}}\exp\bigl(-\pi a^{-1}(n+Ib)^2\bigr),
\]
and the case \(b=0\) is the usual identity for \(\sum\exp(-\pi a n^2)\). The argument calls a Poisson summation theorem for functions of polynomial decay; this file states the theta identity (`Analysis/SpecialFunctions/Gaussian/PoissonSummation.lean`).

## Hypergeometric series and the Bessel function

The ordinary hypergeometric function \({}_2F_1(a,b;c;x)\) is the sum of the series with coefficients \((a)_n(b)_n/((c)_n\,n!)\), in a topological algebra over a field. The definition uses a totalized infinite sum, returning \(0\) if the series is not summable. This does not force zero at every boundary point, where convergence may occur. Division by zero is also totalized: if \(c\) is a nonpositive integer, sufficiently late coefficients vanish and the definition becomes a polynomial, rather than a meromorphic continuation in \(c\). In particular the value at \(x=0\) is always \(1\). When the scalar field is \(\mathbb{R}\) or \(\mathbb{C}\) and none of \(a\), \(b\), \(c\) is a nonpositive integer, the radius of convergence is \(1\); if any of the three parameters is a nonpositive integer, the coefficients eventually vanish and the radius is infinite (`Analysis/SpecialFunctions/OrdinaryHypergeometric.lean`). No differential equation is claimed.

The regularised hypergeometric series puts a Gamma value in the denominator of each lower parameter, so a nonpositive integer among the lower parameters does not create a pole. With no upper and no lower parameters, the regularised function is the exponential. If there are strictly fewer upper parameters than one plus the number of lower parameters, the radius is infinite; if the upper count is one more than the lower count, the radius is \(1\) unless an upper parameter is a nonpositive integer, in which case the series terminates (`Analysis/SpecialFunctions/RegularizedHypergeometric.lean`).

The Bessel function of the first kind is defined from that series:
\[
J_a(x)=\Bigl(\frac{x}{2}\Bigr)^a\cdot{}_0\widetilde{F}_1(-;a+1;-(x/2)^2),
\]
where the tilde denotes the regularised function, equal to \({}_0F_1(-;a+1;\,\cdot\,)/\Gamma(a+1)\) when the denominator is meaningful. For each complex order \(a\), \(J_a\) is analytic on the slit plane. For integer order it is entire. One has \(J_a(0)=1\) if \(a=0\) and \(J_a(0)=0\) otherwise. For integer \(a\), \(J_a\) is even or odd with \(a\), and \(J_{-a}(x)=(-1)^a J_a(x)\) (`Analysis/SpecialFunctions/Bessel.lean`). The differential equation, the second kind, generating functions, and integral representations are TODOs in that file. The Bessel potential space is a Fourier-theoretic Sobolev space (`Analysis/FunctionalSpaces/BesselPotentialSpace.lean`), and the orthonormal Bessel inequality is an inner-product estimate (`Analysis/InnerProductSpace/Orthonormal.lean`); neither is the function \(J_a\).

## The Weierstrass \(\wp\)-function

A period pair is a pair of \(\mathbb{R}\)-linearly independent complex numbers. They span a lattice \(L\subset\mathbb{C}\). The Weierstrass function is the lattice sum
\[
\wp_L(z)=\sum_{\ell\in L}\Bigl(\frac{1}{(z-\ell)^2}-\frac{1}{\ell^2}\Bigr),
\]
with the usual convention that the \(\ell=0\) summand omits the second term. The sum of the differentiated terms defines \(\wp'_L(z)=-\sum_{\ell\in L} 2/(z-\ell)^3\). Both functions are periodic with respect to \(L\). The function \(\wp_L\) is even and \(\wp'_L\) is odd. Each is meromorphic on \(\mathbb{C}\), analytic off \(L\), and \(\wp_L\) has a pole of order \(-2\) at every lattice point. The totalized summands (using \(1/0=0\)) are summable even at lattice points (`hasSum_weierstrassP`), and the resulting value there is \(0\) (`weierstrassP_coe`). This is a convention at the poles, not continuity there; the order is determined by behavior on punctured neighborhoods. The derivative of \(\wp_L\) equals \(\wp'_L\) globally, again because of those values (`Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`).

The Eisenstein sums \(G_n(L)=\sum_{\ell\in L}\ell^{-n}\) vanish for odd \(n\). The invariants are \(g_2=60\,G_4\) and \(g_3=140\,G_6\). Off the lattice,
\[
\bigl(\wp'_L(z)\bigr)^2=4\wp_L(z)^3-g_2\wp_L(z)-g_3.
\]
Connecting \(G_n\) with the modular-forms library is a TODO. An addition formula for \(\wp_L\) is not in the file.

## Zeta functions and Jacobi theta functions

Relevant special functions also live under `NumberTheory`. The Riemann zeta function agrees with \(\sum_{n\ge1}n^{-s}\) for \(\operatorname{Re}s>1\), is holomorphic away from \(s=1\), has residue \(1\) there, and satisfies the functional equation; its trivial zeros at the negative even integers are proved (`NumberTheory/LSeries/RiemannZeta.lean`). The completed zeta function satisfies the symmetry \(s\leftrightarrow1-s\). Special values are developed in `NumberTheory/ZetaValues.lean` and `NumberTheory/LSeries/HurwitzZetaValues.lean`.

The Hurwitz zeta development includes its Dirichlet-series formula, continuation, residue at \(1\), and functional equations relating it to the exponential zeta series. Its parameter is taken modulo \(1\); the usual series comparison is stated for a representative in \([0,1]\) (`NumberTheory/LSeries/HurwitzZeta.lean`).

Jacobi theta functions of one and two variables are defined, with convergence, differentiability, periodicity and quasiperiodicity, and the transformation under \(\tau\mapsto-1/\tau\) (`NumberTheory/ModularForms/JacobiTheta/OneVariable.lean`, `NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean`). These are analytic special-function results even though their source directory is number theory.

## Mellin transform, Frullani, the sine product, and \(\int\log\sin\)

The Mellin transform of an \(E\)-valued function on \((0,\infty)\), with \(E\) a complex normed space, is \(\int_0^\infty t^{s-1}f(t)\,dt\). The inverse transform at height \(\sigma\) is
\[
(\mathcal{M}^{-1}_\sigma F)(x)=\frac{1}{2\pi}\int_{-\infty}^{\infty} x^{-(\sigma+iy)} F(\sigma+iy)\,dy.
\]
If \(f\) is \(O(x^{-a})\) at infinity and \(O(x^{-b})\) at \(0\), the transform is holomorphic on the strip \(b<\operatorname{Re} s<a\) (`Analysis/MellinTransform.lean`). Inversion: if \(E\) is complete, \(x>0\), the integral converges at the real value \(\sigma\), the transform is integrable on the vertical line \(\operatorname{Re} s=\sigma\), and \(f\) is continuous at \(x\), then the inverse transform of the transform recovers \(f(x)\). The proof is Fourier inversion after the change of variables \(t=e^{-u}\) (`Analysis/MellinInversion.lean`).

Frullani’s integral, for a complete real normed space \(E\): if \(f:(0,\infty)\to E\) is locally integrable, \(f(x)\to L\) as \(x\to 0^+\) and \(f(x)\to R\) as \(x\to\infty\), and \(a,b>0\), then
\[
\int_\varepsilon^r x^{-1}\bigl(f(ax)-f(bx)\bigr)\,dx\to\log(b/a)\,(L-R)
\]
as \(\varepsilon\to 0^+\) and \(r\to\infty\). If in addition \(x\mapsto x^{-1}(f(ax)-f(bx))\) is integrable on \((0,\infty)\), the improper integral equals \(\log(b/a)\,(L-R)\) (`Analysis/SpecialFunctions/FrullaniIntegral.lean`).

Euler’s sine product: for every complex \(z\), and likewise for every real \(x\),
\[
\pi z\prod_{j=0}^{n-1}\Bigl(1-\frac{z^2}{(j+1)^2}\Bigr)\to\sin(\pi z)
\]
as \(n\to\infty\). A finite identity expresses \(\sin(\pi z)\) as that partial product times a ratio of integrals of \(\cos(2zx)\cos^{2n}x\) and \(\cos^{2n}x\) over \([0,\pi/2]\) (`Analysis/SpecialFunctions/Trigonometric/EulerSineProd.lean`).

The logarithmic integrals are
\[
\int_0^{\pi/2}\log(\sin x)\,dx=-\frac{\pi}{2}\log 2,\qquad\int_0^{\pi}\log(\sin x)\,dx=-\pi\log 2
\]
(`Analysis/SpecialFunctions/Integrals/LogTrigonometric.lean`).

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

TauCeti defines the real error function and its complement and proves their derivative, monotonicity, symmetry, and limits ([error function](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/SpecialFunctions/Erf.lean)). It develops lower incomplete gamma and regularized incomplete beta functions for positive shape parameters, including integral formulas, differentiation, continuity, and range/limit properties ([incomplete gamma](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/SpecialFunctions/IncompleteGamma.lean), [incomplete beta](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/SpecialFunctions/IncompleteBeta.lean)). The multivariate gamma integral over the cone of positive-definite real symmetric matrices is evaluated for the convergent parameter range, with its scale-matrix dependence ([cone integral](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/SpecialFunctions/MultivariateGamma/Integral.lean)).

The Hausdorff–Bernstein–Widder theorem identifies functions continuous on \([0,\infty)\) and completely monotone on \((0,\infty)\) with Laplace transforms of unique finite positive measures ([representation](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/CompletelyMonotone/Bernstein/HausdorffBernsteinWidder.lean)). Bernstein functions have a proved Lévy–Khintchine representation by killing, drift, and a positive Lévy measure ([Bernstein representation](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/CompletelyMonotone/Bernstein/LevyKhintchine/Representation.lean)). This is the representation theory of Bernstein functions, not a general Lévy-process construction. Hermite functions and their oscillator/Fourier identities are recorded in Sections 22, 27, and 48.

## Topics of Section 49 not found in either inspected library

- The Airy function, the Whittaker function, and the Mathieu equation. A citation of Whittaker and Watson, and an author named Mathieu, are not these functions.
- Jacobi elliptic functions \(\operatorname{sn}\), \(\operatorname{cn}\), \(\operatorname{dn}\), beyond the Weierstrass \(\wp\)-function.
- An addition formula for \(\wp\).
- Gauss’s multiplication formula for \(\Gamma\) at an integer \(k\geq 3\). Legendre doubling is proved.
- Gauss’s integral representation of the digamma function.
- The Bessel equation, the Bessel function of the second kind, and the generating function for \(J_n\).
- A differential equation for \({}_2F_1\).
