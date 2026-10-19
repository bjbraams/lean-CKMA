# Structure 49: Special functions, integral transforms, and classical formulae

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS49.md); [bibliographical scope](CKMA-bib.md#ckma-49); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.SpecialFunctions.Gamma` (the modules `Basic`, `Deriv`, `Beta`, `BohrMollerup`, `Digamma`), `Mathlib.Analysis.SpecialFunctions.Stirling`, `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`, `Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform`, `Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation`, `Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric`, `Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric`, `Mathlib.Analysis.SpecialFunctions.Bessel`, `Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass`, `Mathlib.Analysis.MellinTransform`, `Mathlib.Analysis.MellinInversion`, `Mathlib.Analysis.SpecialFunctions.FrullaniIntegral`, `Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd`, `Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent`, `Mathlib.Analysis.SpecialFunctions.Integrals.Log`, `Mathlib.RingTheory.Polynomial.Chebyshev`, `Mathlib.RingTheory.Polynomial.ShiftedLegendre`, `Mathlib.RingTheory.Polynomial.Hermite.Gaussian`, the directory `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev`, the zeta-function modules under `Mathlib.NumberTheory.LSeries`, `Mathlib.NumberTheory.ZetaValues`, `Mathlib.NumberTheory.EulerProduct.DirichletLSeries`, the directory `Mathlib.NumberTheory.ModularForms.JacobiTheta`, and `Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction`.

**Namespaces.** `Complex` and `Real` for \(\Gamma\), the Beta integral, the digamma function, the hypergeometric and Bessel functions, and the Gaussian evaluations; `Real.BohrMollerup` for the auxiliary limit in the uniqueness argument; `Stirling` for the sequence and the asymptotic comparison; `HurwitzZeta` for the Hurwitz zeta function; `Frullani` for Frullani’s integral; `PeriodPair` for the Weierstrass \(\wp\)-function; `Pentagonal` for the pentagonal number theorem. The TauCeti declarations are in `TauCeti`, `Real`, `Complex`, and `ProbabilityTheory`, and are identified by name below.

## Gamma, beta, and zeta functions

[Mathematical scope](SYNOPSIS49.md#gamma-beta-and-zeta-functions).

### Mathlib

**Gamma, Beta, and digamma.**

Euler’s integral \(\Gamma(s)=\int_0^\infty e^{-x}x^{s-1}\,dx\) converges for real \(s>0\) and for complex \(s\) with positive real part. The function \(\Gamma\) is the unique extension of that integral by the recurrence \(\Gamma(s+1)=s\Gamma(s)\) for \(s\neq 0\). At the nonpositive integers, where the recurrence does not determine a value, the function is set equal to \(0\) by convention, and it is not continuous there (`Complex.not_continuousAt_Gamma_neg_nat`). One has \(\Gamma(1)=1\) and \(\Gamma(n+1)=n!\). The function is differentiable off the nonpositive integers, it is meromorphic on \(\mathbb C\) (`Meromorphic.Gamma`, `Analysis/Meromorphic/Complex.lean`), and at \(0\) it has a simple pole with residue \(1\) (`Complex.tendsto_self_mul_Gamma_nhds_zero`, `Analysis/SpecialFunctions/Gamma/Deriv.lean`); the residues at the other nonpositive integers are not stated. The reciprocal \(1/\Gamma\) is entire (`Complex.differentiable_one_div_Gamma`), and \(\Gamma(s)\neq0\) off the nonpositive integers (`Complex.Gamma_ne_zero`). Complex conjugation passes inside \(\Gamma\) (`Analysis/SpecialFunctions/Gamma/Basic.lean`, `Analysis/SpecialFunctions/Gamma/Beta.lean`).

On the positive reals, \(\Gamma\) is positive, and both \(\Gamma\) and \(\log\circ\Gamma\) are convex. The Bohr–Mollerup theorem is the uniqueness statement: a function \(f:(0,\infty)\to\mathbb{R}\) which is positive, whose logarithm is convex, and which satisfies \(f(1)=1\) and \(f(y+1)=y\,f(y)\) for every \(y>0\), agrees with \(\Gamma\) on \((0,\infty)\) (`Analysis/SpecialFunctions/Gamma/BohrMollerup.lean`, `Real.eq_Gamma_of_log_convex`). The same argument yields a logarithmic Euler limit: for \(x>0\),
\[
x\log n+\log n!-\sum_{m=0}^{n}\log(x+m)\to\log\Gamma(x).
\]
For every complex \(s\), the sequence \(n^s\,n!/\bigl(s(s+1)\cdots(s+n)\bigr)\) tends to \(\Gamma(s)\) (`Complex.GammaSeq_tendsto_Gamma`, `Analysis/SpecialFunctions/Gamma/Beta.lean`). On \((0,1]\), \(\Gamma\) is strictly decreasing, and on \([2,\infty)\) it is strictly increasing. A global minimum on \((0,\infty)\) exists and lies in \((1,2)\); uniqueness of that minimiser is marked as future work. The Weierstrass product for \(1/\Gamma\) is not stated.

Legendre’s doubling formula is proved, first for positive real \(s\) by Bohr–Mollerup and then for every real and every complex \(s\) by continuation, using that \(1/\Gamma\) is entire (`Complex.Gamma_mul_Gamma_add_half`):
\[
\Gamma(s)\,\Gamma\bigl(s+\tfrac12\bigr)=\Gamma(2s)\,2^{1-2s}\sqrt{\pi}.
\]
The general Gauss multiplication formula for an integer \(m\geq 3\) is a header TODO in the Bohr–Mollerup file, not a theorem.

The Beta integral \(B(u,v)=\int_0^1 x^{u-1}(1-x)^{v-1}\,dx\) converges when the real parts of \(u\) and \(v\) are positive, and it is symmetric. In that range, \(\Gamma(u)\Gamma(v)=\Gamma(u+v)\,B(u,v)\) (`Complex.Gamma_mul_Gamma_eq_betaIntegral`), hence \(B(u,v)=\Gamma(u)\Gamma(v)/\Gamma(u+v)\). Euler’s reflection formula, for every complex \(z\) and every real \(s\), is \(\Gamma(z)\Gamma(1-z)=\pi/\sin(\pi z)\) (`Complex.Gamma_mul_Gamma_one_sub`). Combined with the convention at the poles, \(\Gamma(z)=0\) if and only if \(z\) is a nonpositive integer. The Gaussian integral (next sections) gives \(\Gamma(1/2)=\sqrt{\pi}\).

The digamma function is the logarithmic derivative \(\psi=\Gamma'/\Gamma\) (`Complex.digamma`). At \(0\), where \(\Gamma\) is not differentiable, the logarithmic derivative is \(0\). Off the nonpositive integers, \(\psi(s+1)=\psi(s)+1/s\) and its iterate \(\psi(s+n)=\psi(s)+\sum_{k<n}(s+k)^{-1}\) hold, and \(\psi(n+1)=H_n-\gamma\) with \(H_n\) the \(n\)-th harmonic number, so \(\psi(1)=-\gamma\). Also \(\psi(1/2)=-2\log 2-\gamma\). For nonintegral \(s\), \(\psi(1-s)=\psi(s)+\pi\cot(\pi s)\). The duplication formula \(\psi(2s)=\tfrac12\bigl(\psi(s)+\psi(s+1/2)\bigr)+\log 2\) holds when \(2s\) avoids the nonpositive integers. The function is meromorphic. Sources: `Analysis/SpecialFunctions/Gamma/Digamma.lean`. The series \(\psi(z)=-\gamma+\sum_{n\ge0}(1/(n+1)-1/(n+z))\), the polygamma series, and Gauss’s integral representation (a header TODO) are not proved.

**Stirling.**

Write
\[
s_n=\frac{n!}{\sqrt{2n}\,(n/e)^n}
\]
for \(n\geq 1\), and \(s_0=0\). Then \(s_n\to\sqrt{\pi}\). Equivalently, along the filter of large natural numbers,
\[
n!\;\sim\;\sqrt{2\pi n}\,(n/e)^n
\]
(`Analysis/SpecialFunctions/Stirling.lean`, `Stirling.factorial_isEquivalent_stirling`). The comparison \(s_n\geq\sqrt{\pi}\) for every \(n\geq 1\) rearranges to a lower bound valid for every \(n\), including \(n=0\):
\[
\sqrt{2\pi n}\,(n/e)^n\leq n!.
\]
The file records this as a lower bound only: the asymptotic equivalence supplies the matching upper bound for all sufficiently large \(n\), and the inequality above does not. Successive logarithms satisfy Robbins’ stepwise bound \(\log s_n-\log s_{n+1}\leq 1/(12n(n+1))\) for every natural number \(n\). This is Stirling’s formula at the integers; the asymptotic expansion of \(\log\Gamma(z)\) in a sector, with Bernoulli-number coefficients, is not proved.

**Zeta functions.**

The Riemann zeta function agrees with \(\sum_{n\ge1}n^{-s}\) for \(\operatorname{Re}s>1\) (`zeta_eq_tsum_one_div_nat_cpow`), is holomorphic away from \(s=1\), and has residue \(1\) there (`riemannZeta_residue_one`, `NumberTheory/LSeries/RiemannZeta.lean`). For \(\operatorname{Re}s>1\) it equals its Euler product over the primes (`riemannZeta_eulerProduct_tprod`, `NumberTheory/EulerProduct/DirichletLSeries.lean`) and does not vanish (`riemannZeta_ne_zero_of_one_lt_re`, `NumberTheory/LSeries/Dirichlet.lean`). The completed zeta function \(\Lambda(s)=\pi^{-s/2}\Gamma(s/2)\zeta(s)\) (`completedRiemannZeta`) is the entire function `completedRiemannZeta₀` minus \(1/s+1/(1-s)\), so its only poles are simple poles at \(0\) and \(1\), and it satisfies \(\Lambda(1-s)=\Lambda(s)\) (`completedRiemannZeta_one_sub`). The trivial zeros at \(-2,-4,\ldots\) are `riemannZeta_neg_two_mul_nat_add_one`. The formula \(\zeta(2k)=(-1)^{k+1}2^{2k-1}\pi^{2k}B_{2k}/(2k)!\) for \(k\ge1\) is `riemannZeta_two_mul_nat`, and \(\zeta(-k)=(-1)^kB_{k+1}/(k+1)\) is `riemannZeta_neg_nat_eq_bernoulli` (`NumberTheory/LSeries/HurwitzZetaValues.lean`, `NumberTheory/ZetaValues.lean`; Bernoulli numbers and polynomials are in `NumberTheory/Bernoulli.lean` and `NumberTheory/BernoulliPolynomials.lean`).

The Hurwitz zeta development includes its Dirichlet-series formula, continuation, residue at \(1\), and functional equations relating it to the exponential zeta series. Its parameter is taken modulo \(1\); the series comparison \(\zeta(s,a)=\sum_{n\ge0}(n+a)^{-s}\) for \(\operatorname{Re}s>1\) is stated for a representative \(a\in[0,1]\) (`HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re`, `HurwitzZeta.hurwitzZeta_residue_one`, `NumberTheory/LSeries/HurwitzZeta.lean`). For \(k\ge1\) and \(a\in[0,1]\), \(\zeta(-k,a)=-B_{k+1}(a)/(k+1)\) (`HurwitzZeta.hurwitzZeta_neg_nat`); the case \(k=0\) is left as a TODO. The continuation is built from Mellin transforms of theta-type kernels, not from the integral \(\int_0^\infty t^{s-1}e^{-at}/(1-e^{-t})\,dt\).

**Euler’s sine product and related evaluations.**

Euler’s sine product: for every complex \(z\), and likewise for every real \(x\),
\[
\pi z\prod_{j=0}^{n-1}\Bigl(1-\frac{z^2}{(j+1)^2}\Bigr)\to\sin(\pi z)
\]
as \(n\to\infty\). A finite identity expresses \(\sin(\pi z)\) as that partial product times a ratio of integrals of \(\cos(2zx)\cos^{2n}x\) and \(\cos^{2n}x\) over \([0,\pi/2]\) (`Analysis/SpecialFunctions/Trigonometric/EulerSineProd.lean`). Logarithmic differentiation gives the partial-fraction expansion of the cotangent: for complex \(x\) not an integer, \(\pi\cot(\pi x)=1/x+\sum_{n\ge1}\bigl(1/(x-n)+1/(x+n)\bigr)\) (`Analysis/SpecialFunctions/Trigonometric/Cotangent.lean`, `cot_series_rep`). The logarithmic integrals are
\[
\int_0^{\pi/2}\log(\sin x)\,dx=-\frac{\pi}{2}\log 2,\qquad\int_0^{\pi}\log(\sin x)\,dx=-\pi\log 2
\]
(`Analysis/SpecialFunctions/Integrals/Log.lean`, `integral_log_sin_zero_pi_div_two`, `integral_log_sin_zero_pi`).

**Supporting material.** The complex and real exponential functions satisfy \(\frac{d}{dx}\exp x=\exp x\) (`Analysis/SpecialFunctions/ExpDeriv.lean`), and Euler’s formula is \(\exp(x I)=\cos x+\sin x\cdot I\) (`Analysis/Complex/Trigonometric.lean`). The real and complex logarithm and the inverse trigonometric functions are developed in the same directories; this note does not catalogue them.

### TauCeti

Euler’s two real beta integrals are recorded with sharp integrability criteria: \(\int_0^1t^{a-1}(1-t)^{b-1}dt=B(a,b)\) and \(\int_0^\infty x^{a-1}(1+x)^{-(a+b)}dx=B(a,b)\) for \(a,b>0\) (`TauCeti.integral_rpow_mul_one_sub_rpow`, `TauCeti.integral_rpow_mul_one_add_rpow`), with the specialization to \(\int_{\mathbb R}(1+x^2/\nu)^{-s}dx\) ([beta integrals](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Beta.lean)). The lower incomplete gamma function \(\gamma(s,x)=\int_0^xt^{s-1}e^{-t}dt\) and its regularization \(P(s,x)=\gamma(s,x)/\Gamma(s)\) are developed for real \(s>0\) and real \(x\): integral formulas, continuity, monotonicity, differentiation, the recurrence in \(s\), and the limit \(P(s,x)\to1\) as \(x\to\infty\) (`TauCeti.lowerIncompleteGamma`, `TauCeti.regularizedGamma`, [incomplete gamma](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/IncompleteGamma.lean)); the regularized incomplete beta function is developed alongside ([incomplete beta](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/IncompleteBeta.lean)). The upper incomplete gamma function, the exponential integral \(E_1\), the confluent representations, and the large-\(z\) expansion are absent. Further special functions: the offset logarithmic integral \(\operatorname{Li}(x)=\int_2^x dt/\log t\), with \(\operatorname{Li}(x)\sim x/\log x\) (`TauCeti.Real.logIntegral_isEquivalent_div_log`, [logarithmic integral](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/LogIntegral.lean)); and the multivariate Gamma integral over the cone of positive-definite real symmetric matrices, evaluated for the convergent parameter range \(a>(p-1)/2\) with its scale-matrix dependence, and in Cholesky coordinates ([multivariate Gamma](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/MultivariateGamma/Integral.lean), [Cholesky coordinates](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/MultivariateGamma/Cholesky.lean)). For real \(y\), \((\pi/2)\tanh(\pi y/2)=\sum_{n\ge0}2y/(y^2+(2n+1)^2)\), derived from Mathlib’s cotangent expansion ([tanh series](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Trigonometric/TanhSeries.lean)). The real Gamma function is Borel measurable and \(1/\Gamma\) is continuous on \(\mathbb R\) and bounded on half-lines \([a,\infty)\) (`Real.measurable_Gamma`, `Real.continuous_inv_Gamma`, [Gamma](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Gamma.lean)).

**Synopsis entries.** Covered: 49.1, 49.4, 49.5, 49.7 (Mathlib; the half-line form for real parameters in TauCeti), 49.11 (Mathlib). Partly covered: 49.2 (meromorphy, no zeros, and the residue \(1\) at \(0\); residues at \(-n\), \(n\ge1\), not stated), 49.3 (\(1/\Gamma\) entire and Euler’s limit; no Weierstrass product), 49.6 (the case \(m=2\) only), 49.8 (recurrence, values at integers and at \(1/2\), reflection and duplication; not the series or polygamma formulas), 49.9 (Stirling’s formula for \(n!\) only), 49.10 (Hurwitz zeta continuation, simple pole with residue \(1\), and \(\zeta(-n,a)\) for \(n\ge1\); not the Mellin representation or \(n=0\)), 49.82 (real lower incomplete gamma function for positive shape, and \(\operatorname{erf}x=P(1/2,x^2)\), TauCeti).

## Hypergeometric and confluent hypergeometric functions

[Mathematical scope](SYNOPSIS49.md#hypergeometric-and-confluent-hypergeometric-functions).

### Mathlib

**Hypergeometric series.**

The ordinary hypergeometric function \({}_2F_1(a,b;c;x)\) is the sum of the series with coefficients \((a)_n(b)_n/((c)_n\,n!)\), in a topological algebra over a field (`ordinaryHypergeometric`). The definition uses a totalized infinite sum, returning \(0\) if the series is not summable. This does not force zero at every boundary point, where convergence may occur. Division by zero is also totalized: if \(c\) is a nonpositive integer, sufficiently late coefficients vanish and the definition becomes a polynomial, rather than a meromorphic continuation in \(c\). In particular the value at \(x=0\) is always \(1\). When the scalar field is \(\mathbb{R}\) or \(\mathbb{C}\) and none of \(a\), \(b\), \(c\) is a nonpositive integer, the radius of convergence is \(1\) (`ordinaryHypergeometricSeries_radius_eq_one`); if any of the three parameters is a nonpositive integer, the coefficients eventually vanish and the radius is infinite (`Analysis/SpecialFunctions/OrdinaryHypergeometric.lean`). No differential equation, integral representation, summation formula, or transformation formula is proved.

The regularised generalized hypergeometric series, with upper and lower parameters given as multisets of complex numbers, puts a Gamma value \(\Gamma(b_j+n)\) in the denominator of each lower parameter, so a nonpositive integer among the lower parameters does not create a pole (`Complex.regularizedHGFun`). With no upper and no lower parameters, the regularised function is the exponential. If the number of upper parameters is at most the number of lower parameters, the radius is infinite (`radius_regularizedHGFunSeries_eq_top`); if the upper count is one more than the lower count, the radius is \(1\) unless an upper parameter is a nonpositive integer, in which case the series terminates (`radius_regularizedHGFunSeries_eq_one`, `Analysis/SpecialFunctions/RegularizedHypergeometric.lean`). For the Gaussian case, multiplying the regularised function by \(\Gamma(c)\) recovers \({}_2F_1\) when \(c\) is not a nonpositive integer (`Complex.ordinaryHypergeometric_div_Gamma_eq`). Divergence when there are at least two more upper than lower parameters, and convergence at \(z=1\), are not stated.

### TauCeti

For the regularised series \({}_0\widetilde F_1(-;b;z)=\sum_n z^n/(n!\,\Gamma(b+n))\), TauCeti proves, for every complex \(b\), the contiguous relation \({}_0\widetilde F_1(-;b;z)=b\,{}_0\widetilde F_1(-;b+1;z)+z\,{}_0\widetilde F_1(-;b+2;z)\) (`Complex.regularizedHGFun_zero_singleton_eq_mul_add_mul`); for real \(b\) and real \(y\) the value is given by the real series, is jointly continuous in \((b,y)\), and has derivative \({}_0\widetilde F_1(-;b+1;y)\) in \(y\) ([₀F₁](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/RegularizedHypergeometric.lean)). This is a \({}_0F_1\) relation; contiguous relations for \({}_2F_1\) are absent.

**Synopsis entries.** Partly covered: 49.12 (radius of convergence for \(p\le q\) and \(p=q+1\); no divergence statement for \(p>q+1\) and no convergence at \(z=1\)). Not covered: 49.13–49.20, 49.83, 49.84, 49.21–49.24, 49.81.

## Bessel, Airy, and Gaussian functions

[Mathematical scope](SYNOPSIS49.md#bessel-airy-and-gaussian-functions).

### Mathlib

**The Bessel function of the first kind.**

The Bessel function of the first kind is defined from the regularised series:
\[
J_a(x)=\Bigl(\frac{x}{2}\Bigr)^a\cdot{}_0\widetilde{F}_1(-;a+1;-(x/2)^2),
\]
where the tilde denotes the regularised function, equal to \({}_0F_1(-;a+1;\,\cdot\,)/\Gamma(a+1)\) when the denominator is meaningful (`Complex.besselJ`). For each complex order \(a\), \(J_a\) is analytic on the slit plane. For integer order it is entire. One has \(J_a(0)=1\) if \(a=0\) and \(J_a(0)=0\) otherwise. For integer \(a\), \(J_a\) is even or odd with \(a\), and \(J_{-a}(x)=(-1)^a J_a(x)\) (`Analysis/SpecialFunctions/Bessel.lean`). The differential equation, the second kind, generating functions, and Bessel’s integrals are header TODOs in that file. The Bessel potential space (`Analysis/FunctionalSpaces/BesselPotentialSpace.lean`) and the orthonormal Bessel inequality (`Analysis/InnerProductSpace/Orthonormal.lean`) are unrelated to \(J_a\).

**The Gaussian integral, its Fourier transform, and a theta identity.**

For real \(b\), \(\int_{-\infty}^{\infty}\exp(-b x^2)\,dx=\sqrt{\pi/b}\), both sides being \(0\) when \(b\leq 0\). For complex \(b\) with positive real part, \(\int_{-\infty}^{\infty}\exp(-b x^2)\,dx=(\pi/b)^{1/2}\). The integral over \((0,\infty)\) is half of the full integral. In particular \(\Gamma(1/2)=\sqrt{\pi}\) (`Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`).

For \(\operatorname{Re} b>0\) and complex \(t\),
\[
\int_{-\infty}^{\infty}\exp(I t x)\exp(-b x^2)\,dx=(\pi/b)^{1/2}\exp\bigl(-t^2/(4b)\bigr).
\]
In the symmetric normalisation, the Fourier transform of \(x\mapsto\exp(-\pi b x^2)\) is \(t\mapsto b^{-1/2}\exp(-\pi t^2/b)\). On a finite-dimensional real inner product space of dimension \(d\), \(\int\exp(-b\|v\|^2)\,dv=(\pi/b)^{d/2}\), and the Fourier transform of \(v\mapsto\exp(-b\|v\|^2)\) at \(w\) is \((\pi/b)^{d/2}\exp(-\pi^2\|w\|^2/b)\) (`Analysis/SpecialFunctions/Gaussian/FourierTransform.lean`). Jacobi’s transformation of the quadratic theta series, which also follows from these, is recorded under elliptic and theta functions below.

### TauCeti

The modified Bessel function of the first kind \(I_\nu(x)=(x/2)^\nu\,{}_0\widetilde F_1(-;\nu+1;x^2/4)\) is defined for real order and real argument (`Real.besselI`). For \(x>0\) it is the series \(\sum_j(x/2)^{2j+\nu}/(j!\,\Gamma(j+\nu+1))\). It is positive for \(\nu>-1\), \(x>0\) (`Real.besselI_pos`), and \((x/2)^{-\nu}I_\nu(x)\to1/\Gamma(\nu+1)\) as \(x\to0^+\). Further, \(I_\nu'(x)=I_{\nu+1}(x)+(\nu/x)I_\nu(x)\) and \(I_{\nu-1}(x)-I_{\nu+1}(x)=(2\nu/x)I_\nu(x)\) for \(x\neq0\) ([modified Bessel function](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/BesselI.lean)). The modified Bessel equation, \(K_\nu\), the Wronskian, and the large-argument asymptotics are not stated.

TauCeti defines the real error function and its complement and proves their derivative, oddness, strict monotonicity, and limits \(\pm1\); \(\operatorname{erf}\) is an order isomorphism onto \((-1,1)\), with a differentiable inverse \(\operatorname{erf}^{-1}\) tending to \(\pm\infty\) at \(\pm1\) ([error function](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Erf.lean)). The error function is real-variable only (not the entire function of the synopsis), and the asymptotic \(\operatorname{erfc}x\sim e^{-x^2}/(\sqrt\pi x)\) is not stated. Owen’s \(T\) function \(T(h,a)=(2\pi)^{-1}\int_0^a e^{-h^2(1+t^2)/2}(1+t^2)^{-1}dt\) has its parities, \(T(0,a)=\arctan(a)/(2\pi)\), its \(a\)-derivative, and the bound \(|T(h,a)|\le|a|e^{-h^2/2}/(2\pi)\) ([Owen’s T](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/OwensT.lean)).

**Synopsis entries.** Partly covered: 49.25 (the series definition of \(J_\nu\), Mathlib; no differential equation), 49.29 (\(I_\nu\) for real order and argument, its positivity for \(\nu>-1\), derivative formula and recurrence, TauCeti; no \(K_\nu\) or Wronskian), 49.38 (the Gaussian integral, Mathlib; the real error function, TauCeti; not the entire function or the \(\operatorname{erfc}\) asymptotic). Not covered: 49.26–49.28, 49.30, 49.86, 49.31–49.37.

## Classical polynomial families and spherical functions

[Mathematical scope](SYNOPSIS49.md#classical-polynomial-families-and-spherical-functions).

### Mathlib

**Classical orthogonal polynomials.**

The Chebyshev polynomials \(T_n\) and \(U_n\) are defined over any commutative ring for integer \(n\) (`RingTheory/Polynomial/Chebyshev.lean`), with \(T_n(\cos\theta)=\cos(n\theta)\) and the corresponding formulas for \(U_n\), \(\cosh\), and complex arguments (`Analysis/SpecialFunctions/Trigonometric/Chebyshev/Basic.lean`). For the weight \((1-x^2)^{-1/2}\) on \((-1,1]\), \(\int T_mT_n=0\) for \(m\neq n\), \(\int T_0^2=\pi\), and \(\int T_n^2=\pi/2\) for \(n\neq0\) (`Chebyshev/Orthogonality.lean`); orthogonality of the \(U_n\) is a TODO there. These are the Jacobi relations of entry 49.40 at \(\alpha=\beta=-\tfrac12\). The Chebyshev–Gauss rule is exact: for a real polynomial \(P\) of degree \(<2n\), \(\int_{-1}^1P(x)(1-x^2)^{-1/2}\,dx\) is \(\pi\) times the average of \(P\) over the nodes \(\cos((2i+1)\pi/(2n))\), \(0\le i<n\) (`Chebyshev/ChebyshevGauss.lean`, `integral_eq_sumZeroes`). The same directory locates the roots of \(T_n\) and \(U_n\) and the extrema of \(T_n\), and proves the extremal property: a real polynomial of degree at most \(n\) bounded by \(1\) on \([-1,1]\) has leading coefficient at most \(2^{n-1}\), with equality for \(n\ge2\) only for \(T_n\), and analogous bounds for iterated derivatives at points \(x\ge1\) (`RootsExtrema.lean`, `Extremal.lean`).

The probabilists' Hermite polynomials satisfy the Rodrigues-type identity \(\frac{d^n}{dx^n}e^{-x^2/2}=(-1)^nH_n(x)e^{-x^2/2}\) (`RingTheory/Polynomial/Hermite/Gaussian.lean`, `Polynomial.deriv_gaussian_eq_hermite_mul_gaussian`); no orthogonality relation is proved in Mathlib. The shifted Legendre polynomial \(\tilde P_n(x)=\sum_k(-1)^k\binom nk\binom{n+k}{n}x^k\) has degree \(n\), satisfies the Rodrigues formula \(n!\,\tilde P_n=\frac{d^n}{dx^n}\bigl(x^n(1-x)^n\bigr)\) (`Polynomial.factorial_mul_shiftedLegendre_eq`), and \(\tilde P_n(1-x)=(-1)^n\tilde P_n(x)\) (`RingTheory/Polynomial/ShiftedLegendre.lean`); its orthogonality on \([0,1]\) is not proved. The Jacobi, Laguerre, Gegenbauer, and (unshifted) Legendre families are not defined.

### TauCeti

The probabilists’ Hermite polynomials satisfy \(\int_{\mathbb R}H_mH_ne^{-x^2/2}dx=n!\sqrt{2\pi}\,\delta_{mn}\) ([Hermite orthogonality](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Hermite/Orthogonality.lean)), and \(H_n/\sqrt{n!}\) is a Hilbert basis of \(L^2\) of the standard Gaussian measure ([Gaussian Hermite basis](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Distributions/Gaussian/Hermite/Basis.lean)). The Hermite functions \(\psi_n(x)=H_n(x\sqrt2)e^{-x^2/2}/\sqrt{n!\sqrt\pi}\), where \(H_n(x\sqrt2)=2^{-n/2}\) times the physicists’ polynomial, form an orthonormal system and a Hilbert basis of \(L^2(\mathbb R)\) (`TauCeti.integral_hermiteFunction_mul_hermiteFunction`, `TauCeti.hermiteHilbertBasis`, [Hilbert basis](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Hermite/Function/HilbertBasis.lean)); they satisfy the oscillator equation \(-\psi_n''+x^2\psi_n=(2n+1)\psi_n\) (`TauCeti.hermiteFunction_oscillator`, [oscillator](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Oscillator.lean)); and after the rescaling adapted to Mathlib’s \(e^{-2\pi ix\xi}\) Fourier convention they are eigenfunctions of the Fourier transform with eigenvalue \((-i)^n\) (`TauCeti.fourier_twoPiHermiteFunction`, [Fourier eigenfunctions](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Fourier/Basic.lean)). The physicists’ generating function is not stated. Further Hermite-function material is recorded in Sections 22, 27, and 48.

The normalized Chebyshev polynomials \(T_n/\sqrt{c_n}\) (\(c_0=\pi\), \(c_n=\pi/2\)) form a Hilbert basis of \(L^2((-1,1],(1-x^2)^{-1/2}dx)\), and the envelopes \(T_n(x)(1-x^2)^{-1/4}/\sqrt{c_n}\) a Hilbert basis of \(L^2((-1,1],dx)\), with Parseval and expansion statements ([Chebyshev basis](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Trigonometric/Chebyshev/HilbertBasis.lean), [envelope basis](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Envelope.lean), [Parseval](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Parseval.lean)).

**Synopsis entries.** Partly covered: 49.40 (the Chebyshev case \(\alpha=\beta=-\tfrac12\) only, Mathlib, with completeness in TauCeti), 49.41 (Rodrigues formula for the shifted Legendre polynomials only, Mathlib), 49.43 (Hermite orthogonality, completeness of the Hermite functions, oscillator equation, and Fourier eigenvalues, TauCeti, in the probabilists’ normalization; no generating function). Not covered: 49.39, 49.42, 49.44, 49.45, 49.79, 49.80.

## Elliptic integrals, elliptic functions, and theta functions

[Mathematical scope](SYNOPSIS49.md#elliptic-integrals-elliptic-functions-and-theta-functions).

### Mathlib

**The Weierstrass \(\wp\)-function.**

A period pair is a pair of \(\mathbb{R}\)-linearly independent complex numbers. They span a lattice \(L\subset\mathbb{C}\). The Weierstrass function is the lattice sum
\[
\wp_L(z)=\sum_{\ell\in L}\Bigl(\frac{1}{(z-\ell)^2}-\frac{1}{\ell^2}\Bigr),
\]
with the usual convention that the \(\ell=0\) summand omits the second term (`PeriodPair.weierstrassP`). The sum of the differentiated terms defines \(\wp'_L(z)=-\sum_{\ell\in L} 2/(z-\ell)^3\). Both functions are periodic with respect to \(L\). The function \(\wp_L\) is even and \(\wp'_L\) is odd. Each is meromorphic on \(\mathbb{C}\), analytic off \(L\), and \(\wp_L\) has meromorphic order \(-2\), that is a double pole, at every lattice point (`PeriodPair.order_weierstrassP`). The totalized summands (using \(1/0=0\)) are summable even at lattice points (`hasSum_weierstrassP`), and the resulting value there is \(0\) (`weierstrassP_coe`). This is a convention at the poles, not continuity there; the order is determined by behavior on punctured neighborhoods. The derivative of \(\wp_L\) equals \(\wp'_L\) globally, again because of those values (`Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`).

The Eisenstein sums \(G_n(L)=\sum_{\ell\in L}\ell^{-n}\) vanish for odd \(n\). The invariants are \(g_2=60\,G_4\) and \(g_3=140\,G_6\). Off the lattice (`PeriodPair.derivWeierstrassP_sq`),
\[
\bigl(\wp'_L(z)\bigr)^2=4\wp_L(z)^3-g_2\wp_L(z)-g_3.
\]
The addition theorem for \(\wp\), the Liouville theorems for general elliptic functions, and the description of the field of elliptic functions are not in the library.

**Jacobi theta functions.**

Jacobi theta functions of one and two variables are defined, with \(\vartheta(z,\tau)=\sum_{n\in\mathbb Z}\exp(2\pi inz+\pi in^2\tau)\) (`jacobiTheta₂`) and \(\theta(\tau)=\vartheta(0,\tau)\) (`jacobiTheta`): convergence exactly for \(\operatorname{Im}\tau>0\), differentiability, periodicity \(\vartheta(z+1,\tau)=\vartheta(z,\tau)\), quasiperiodicity under \(z\mapsto z+\tau\) (`jacobiTheta₂_add_left'`), and the transformation under \(\tau\mapsto-1/\tau\) (`jacobiTheta₂_functional_equation`, `jacobiTheta_S_smul`) (`NumberTheory/ModularForms/JacobiTheta/OneVariable.lean`, `NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean`). In the synopsis notation, \(\vartheta_3(\pi z,e^{\pi i\tau})=\vartheta(z,\tau)\). These are analytic special-function results even though their source directory is number theory.

Jacobi’s transformation of the quadratic theta series also appears as a Poisson-summation consequence: for \(\operatorname{Re} a>0\) and complex \(b\),
\[
\sum_{n\in\mathbb{Z}}\exp(-\pi a n^2+2\pi b n)=a^{-1/2}\sum_{n\in\mathbb{Z}}\exp\bigl(-\pi a^{-1}(n+Ib)^2\bigr),
\]
and the case \(b=0\) is the usual identity for \(\sum\exp(-\pi a n^2)\) (`Analysis/SpecialFunctions/Gaussian/PoissonSummation.lean`).

### TauCeti

On the imaginary axis, \(\theta(iy)=\theta(i/y)/\sqrt y\) for \(y>0\) (`TauCeti.jacobiTheta_I_mul`), and \(\theta(\tau)\to1\) as \(\operatorname{Im}\tau\to\infty\) ([theta identities](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean)).

**Synopsis entries.** Covered: 49.53, 49.54 (Mathlib). Partly covered: 49.51 (\(\wp\) is elliptic and satisfies the differential equation; no addition theorem). Not covered: 49.46–49.49, 49.85, 49.50, 49.52, 49.55.

## Basic hypergeometric series and q-products

[Mathematical scope](SYNOPSIS49.md#basic-hypergeometric-series-and-q-products).

### Mathlib

The only q-product identity present is Euler’s pentagonal number theorem, the specialization of the Jacobi triple product to \(\prod_{n\ge1}(1-x^n)=\sum_{k\in\mathbb Z}(-1)^kx^{k(3k-1)/2}\): it is proved for \(\|x\|<1\) in a complete normed ring (`Pentagonal.eulerFunction_eq_tprod`, `Pentagonal.eulerFunction_eq_tsum_pentagonal_pair`, `Combinatorics/Enumerative/Pentagonal/EulerFunction.lean`) and for formal power series (`Combinatorics/Enumerative/Pentagonal/PowerSeries.lean`). Partition generating functions as formal infinite products are in `Combinatorics/Enumerative/Partition/GenFun.lean`; this is combinatorial supporting material, not q-series analysis.

**Synopsis entries.** Partly covered: 49.59 (the pentagonal number theorem only). Not covered: 49.56–49.58, 49.60–49.64.

## Laplace, Mellin, and positivity representations

[Mathematical scope](SYNOPSIS49.md#laplace-mellin-and-positivity-representations).

### Mathlib

**Mellin transform and Frullani’s integral.**

The Mellin transform of an \(E\)-valued function on \((0,\infty)\), with \(E\) a complex normed space, is \(\int_0^\infty t^{s-1}f(t)\,dt\) (`mellin`). The inverse transform at height \(\sigma\) is
\[
(\mathcal{M}^{-1}_\sigma F)(x)=\frac{1}{2\pi}\int_{-\infty}^{\infty} x^{-(\sigma+iy)} F(\sigma+iy)\,dy.
\]
If \(f\) is \(O(x^{-a})\) at infinity and \(O(x^{-b})\) at \(0\), the transform is holomorphic on the strip \(b<\operatorname{Re} s<a\) (`mellin_differentiableAt_of_isBigO_rpow`, `Analysis/MellinTransform.lean`). Inversion: if \(E\) is complete, \(x>0\), the integral converges at the real value \(\sigma\), the transform is integrable on the vertical line \(\operatorname{Re} s=\sigma\), and \(f\) is continuous at \(x\), then the inverse transform of the transform recovers \(f(x)\) (`mellinInv_mellin_eq`). The proof is Fourier inversion after the change of variables \(t=e^{-u}\) (`Analysis/MellinInversion.lean`). A Mellin–Plancherel theorem on \(L^2(dx/x)\) is not stated, and there is no separate Laplace transform of functions.

Frullani’s integral, for a complete real normed space \(E\): if \(f:(0,\infty)\to E\) is locally integrable, \(f(x)\to L\) as \(x\to 0^+\) and \(f(x)\to R\) as \(x\to\infty\), and \(a,b>0\), then
\[
\int_\varepsilon^r x^{-1}\bigl(f(ax)-f(bx)\bigr)\,dx\to\log(b/a)\,(L-R)
\]
as \(\varepsilon\to 0^+\) and \(r\to\infty\). If in addition \(x\mapsto x^{-1}(f(ax)-f(bx))\) is integrable on \((0,\infty)\), the improper integral equals \(\log(b/a)\,(L-R)\) (`Frullani.integral_Ioi_eq`, `Analysis/SpecialFunctions/FrullaniIntegral.lean`).

**Supporting material.** Absolutely monotone functions (all derivatives nonnegative) are defined, with smoothness and closure properties (`AbsolutelyMonotoneOn`, `Analysis/Calculus/AbsolutelyMonotone.lean`); Bernstein’s representation theorem is not proved there.

### TauCeti

The Hausdorff–Bernstein–Widder theorem identifies functions continuous on \([0,\infty)\) and completely monotone on \((0,\infty)\) with Laplace transforms of unique finite positive measures (`TauCeti.hausdorff_bernstein_widder_existsUnique`, [representation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/CompletelyMonotone/Bernstein/HausdorffBernsteinWidder.lean)). On the open half-line, a function completely monotone on \((0,\infty)\) is the Laplace transform of a unique positive measure on \([0,\infty)\) with integrable kernel at every positive parameter, which need not be finite (`TauCeti.hausdorff_bernstein_widder_onIoi_existsUnique`, [open half-line](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/CompletelyMonotone/Bernstein/OpenHalfLine.lean)). A finite measure on \([0,\infty)\) is determined by the values of its Laplace transform at the natural numbers ([Laplace determinacy](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Moments/LaplaceDeterminacy.lean)), and the Laplace transform of a measure takes additive convolution to the product of transforms (`TauCeti.laplaceTransform_conv`, [convolution](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/CompletelyMonotone/Laplace/Convolution.lean)). These are statements about measures; holomorphy of the transform of a function, uniqueness for locally integrable functions of exponential order, the derivative rule, and Bromwich inversion are absent.

Bernstein functions (continuous and nonnegative on \([0,\infty)\), smooth on \((0,\infty)\), with completely monotone derivative) have a Lévy–Khintchine representation by killing, drift, and a positive Lévy measure, with all three data unique (`TauCeti.IsBernsteinFunction.existsUnique_eqOn_bernsteinLevyKhintchineExponent`, [Bernstein representation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/CompletelyMonotone/Bernstein/LevyKhintchine/Representation.lean), [uniqueness](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/CompletelyMonotone/Bernstein/LevyKhintchine/Uniqueness.lean)). This is the representation theory of Bernstein functions, not a general Lévy-process construction. Stieltjes functions are defined by the representation \(a/x+b+\int(x+t)^{-1}d\sigma(t)\), with uniqueness of the data ([Stieltjes uniqueness](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/CompletelyMonotone/Stieltjes/Uniqueness.lean)); a function is Stieltjes exactly when \(x\mapsto xf(x)\) extends to a complete Bernstein function, complete Bernstein functions being defined by the representation \(a+bx+\int x/(x+t)\,d\mu(t)\) ([complete Bernstein functions](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/CompletelyMonotone/Stieltjes/CompleteBernstein.lean)), and the Pick characterization of complete Bernstein functions is proved ([Pick characterization](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/CompletelyMonotone/Stieltjes/Pick.lean)). The characterization of complete Bernstein functions by a completely monotone Lévy density is not stated.

The half-line beta integral recorded in the first section, \(\int_0^\infty x^{a-1}(1+x)^{-(a+b)}dx=\Gamma(a)\Gamma(b)/\Gamma(a+b)\) for real \(a,b>0\), is the real-parameter case of the Mellin pair in entry 49.70.

**Synopsis entries.** Covered: 49.68 (Mathlib), 49.71, 49.72 (TauCeti). Partly covered: 49.65 (Laplace transforms of finite measures are determined by their values, TauCeti; not holomorphy or uniqueness for functions), 49.67 (convolution of measures only, TauCeti), 49.70 (the Mellin pair \(\int_0^\infty x^{s-1}(1+x)^{-a}dx\) for real parameters only, TauCeti; no Barnes integral), 49.73 (the Stieltjes–complete Bernstein correspondence through representations, TauCeti; not the Lévy-density characterization). Not covered: 49.66, 49.69.

## Fractional integrals and Mittag–Leffler functions

[Mathematical scope](SYNOPSIS49.md#fractional-integrals-and-mittagleffler-functions).

Neither library defines Riemann–Liouville or Caputo operators or the Mittag–Leffler functions. The nearest supporting material is the regularised hypergeometric series of Mathlib, whose coefficients carry reciprocal Gamma factors, and TauCeti’s complete-monotonicity theory recorded in the previous section.

**Synopsis entries.** Not covered: 49.74–49.78.
