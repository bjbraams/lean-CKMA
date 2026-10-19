# Structure 48: Orthogonal polynomials, moment problems, and spectral recurrences

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS48.md); [bibliographical scope](CKMA-bib.md#ckma-48); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.RingTheory.Polynomial.Chebyshev`, `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic`, `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality`, `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema`, `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss`, `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal`, `Mathlib.RingTheory.Polynomial.Hermite.Basic`, `Mathlib.RingTheory.Polynomial.Hermite.Gaussian`, `Mathlib.RingTheory.Polynomial.ShiftedLegendre`, `Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho`.

**Namespaces.** `Polynomial.Chebyshev` contains the families \(T,U,C,S\), the orthogonality measure `measureT`, and the extremal results; `Polynomial.hermite` and `Polynomial.shiftedLegendre` are the algebraic families; `InnerProductSpace.gramSchmidt` is the abstract orthogonalization. TauCeti results are in the namespace `TauCeti` (with some `_root_.Polynomial` and `MeasureTheory.Measure` extensions).

## Orthogonality, recurrence, and zeros

[Mathematical scope](SYNOPSIS48.md#orthogonality-recurrence-and-zeros).

### Mathlib

**General orthogonalization.** The Gram–Schmidt process `InnerProductSpace.gramSchmidt` turns a family indexed by a well-ordered locally finite type in an inner product space into an orthogonal family with the same initial spans (`gramSchmidt_orthogonal`, `span_gramSchmidt_Iic`, `gramSchmidtNormed`; `Analysis/InnerProductSpace/GramSchmidtOrtho.lean`). It is supporting material for 48.1: it is not specialized to polynomials in \(L^2(\mu)\), and there is no general theory of orthogonal polynomials of a measure.

**Chebyshev polynomials.**

Over any commutative ring \(R\), the Chebyshev polynomials of the first kind \(T_n\in R[X]\), indexed by \(n\in\mathbb{Z}\), are defined by \(T_0=1\), \(T_1=X\), and \(T_{n+2}=2XT_{n+1}-T_n\), with the same recurrence run backwards for negative indices. They are even in the index: \(T_{-n}=T_n\). The second kind starts with \(U_0=1\), \(U_1=2X\), and the same recurrence; \(U_{-1}=0\). Rescalings satisfy \(C_n(2X)=2T_n(X)\) and \(S_n(2X)=U_n(X)\). The product identity is \(2T_m T_k=T_{m+k}+T_{m-k}\), and composition is \(T_{mn}=T_m\circ T_n\). The formal derivative is \((T_n)'=n\,U_{n-1}\), and the iterated derivatives at \(1\) are given explicitly, in particular \(T_n'(1)=n^2\) (`RingTheory/Polynomial/Chebyshev.lean`, `derivative_T_eval_one`, `iterate_derivative_T_eval_one`). The three-term recurrence is thus present as the defining relation of \(T_n\) and \(U_n\); the file records that relating the definition to the general `LinearRecurrence` API is future work, and the recurrence is not given a spectral interpretation.

Over an integral domain in which \(2\neq 0\), \(T_n\) has degree \(\lvert n\rvert\) and leading coefficient \(2^{\lvert n\rvert-1}\), the case \(n=0\) being the constant \(1\).

On the complex and real trigonometric functions, \(T_n(\cos\theta)=\cos(n\theta)\) and \(U_n(\cos\theta)\sin\theta=\sin((n+1)\theta)\), with the analogous identities for \(\cosh\) and \(\sinh\) (`Analysis/SpecialFunctions/Trigonometric/Chebyshev/Basic.lean`).

The orthogonality measure `measureT` is Lebesgue measure on \((-1,1]\) with density \((1-x^2)^{-1/2}\). For a real function,
\[
\int f\,d\mu_T=\int_{-1}^{1} f(x)\,(1-x^2)^{-1/2}\,dx=\int_0^\pi f(\cos\theta)\,d\theta,
\]
and every function continuous on \([-1,1]\) is integrable. The polynomials of the first kind are orthogonal for this measure: \(\int T_0\,d\mu_T=\pi\) and \(\int T_n\,d\mu_T=0\) for \(n\neq 0\); \(\int T_n T_m\,d\mu_T=0\) for distinct natural numbers \(n,m\); \(\int T_0^2\,d\mu_T=\pi\); and \(\int T_n^2\,d\mu_T=\pi/2\) for \(n\neq 0\) (`Analysis/SpecialFunctions/Trigonometric/Chebyshev/Orthogonality.lean`). Orthogonality of \(U_n\) against the weight \(\sqrt{1-x^2}\), and the statement that the \(T_n\) form a Hilbert basis of \(L^2(\mu_T)\), are marked as future work in that file.

For \(n\neq 0\), \(\lvert T_n(x)\rvert\leq 1\) if and only if \(\lvert x\rvert\leq 1\). The roots of \(T_n\) are the simple points \(\cos\bigl((2k+1)\pi/(2n)\bigr)\) for \(k=0,\ldots,n-1\). The roots of \(U_n\) are the simple points \(\cos\bigl((k+1)\pi/(n+1)\bigr)\) for \(k=0,\ldots,n-1\). The local extrema of \(T_n\) on \((-1,1)\) occur at \(\cos(k\pi/n)\). A nonzero root of \(T_n\) is irrational. On \([-1,1]\), the \(k\)-th derivative of \(T_n\) is bounded by its value at \(1\) (`Analysis/SpecialFunctions/Trigonometric/Chebyshev/RootsExtrema.lean`).

**Hermite and shifted Legendre.**

The probabilists’ Hermite polynomials are the integer polynomials defined by \(He_0=1\) and \(He_{n+1}=X\,He_n-(He_n)'\) (`hermite_succ`). Each \(He_n\) is monic of degree \(n\), with an explicit coefficient formula, and the coefficient of \(X^k\) vanishes when \(n+k\) is odd (`RingTheory/Polynomial/Hermite/Basic.lean`). Analytically, the only identity proved is the Gaussian derivative (Rodrigues) formula: the \(n\)-th derivative of \(\exp(-y^2/2)\) at \(x\) equals \((-1)^n He_n(x)\exp(-x^2/2)\) (`RingTheory/Polynomial/Hermite/Gaussian.lean`).

The shifted Legendre polynomials are
\[
P_n(X)=\sum_{k=0}^n (-1)^k\binom{n}{k}\binom{n+k}{n} X^k\in\mathbb{Z}[X],
\]
of degree \(n\). Rodrigues’ formula is \(n!\,P_n=\frac{d^n}{dX^n}\bigl(X^n(1-X)^n\bigr)\), and evaluation satisfies \(P_n(x)=(-1)^n P_n(1-x)\) (`RingTheory/Polynomial/ShiftedLegendre.lean`). Their orthogonality on \([0,1]\) is not proved; the file only remarks that these polynomials appear in the theory of orthogonal polynomials.

The extremal property of \(T_n\) among polynomials bounded by \(1\) on \([-1,1]\) is recorded under [Asymptotics and potential theory](#asymptotics-and-potential-theory).

### TauCeti

The Hermite lowering identity \(He_n'=n\,He_{n-1}\) and the three-term recurrence \(He_{n+2}=X\,He_{n+1}-(n+1)He_n\) are proved (`Polynomial.derivative_hermite`, `Polynomial.hermite_add_two`; [Hermite derivative](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/RingTheory/Polynomial/Hermite/Derivative.lean)); the normalized Hermite functions satisfy the corresponding recurrence with coefficients \(\sqrt{(n+1)/2}\) and \(\sqrt{n/2}\) ([ladder](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Ladder.lean)). Orthogonality is proved by the Rodrigues-type integration by parts \(\int p\,He_{n+1}e^{-x^2/2}=\int p'\,He_n e^{-x^2/2}\), giving \(\int He_m He_n e^{-x^2/2}\,dx=\delta_{mn}\,n!\sqrt{2\pi}\) (`TauCeti.integral_aeval_mul_hermite_succ`, `TauCeti.integral_hermite_mul_hermite_mul_gaussian`; [orthogonality](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Hermite/Orthogonality.lean)). The normalized Hermite functions form a Hilbert basis of \(L^2(\mathbb R)\), with creation/annihilation identities and the harmonic-oscillator differential equation ([basis](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Hermite/Function/HilbertBasis.lean), [oscillator](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Oscillator.lean)). With the weight in the measure, \(He_n/\sqrt{n!}\) is an orthonormal basis of \(L^2\) of the standard Gaussian measure ([Gaussian Hermite basis](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Distributions/Gaussian/Hermite/Basis.lean)).

The normalized Chebyshev \(T_n\) form a Hilbert basis for the weighted \(L^2\) space with weight \((1-x^2)^{-1/2}\) on \([-1,1]\), with Parseval identities ([Chebyshev basis](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Trigonometric/Chebyshev/HilbertBasis.lean), [Parseval](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Parseval.lean)); cosine and unweighted forms of this basis are described in Section 47.

A general completeness criterion connects the two: if a weighted measure on \(\mathbb{R}\) has a finite exponential moment, any orthogonal family of polynomials of exact degrees is a Hilbert basis of \(L^2\) of that measure, because a function orthogonal to every monomial vanishes by moment determinacy ([polynomial completeness](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/PolynomialCompleteness.lean), [weighted bases](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/WeightedOrthogonalBasis.lean)). Laguerre and general Jacobi weights are not treated.

**Synopsis entries.** Partly covered: 48.3 (the recurrences of the Chebyshev and Hermite families only), 48.6 (explicit simple zeros in \((-1,1)\) of \(T_n\) and \(U_n\) only), 48.11 (Hermite weight and the Chebyshev weight \(\alpha=\beta=-1/2\); Laguerre and general Jacobi weights absent), 48.12 (Rodrigues formulas for Hermite and shifted Legendre polynomials, and Hermite orthogonality by integration by parts). Not covered: 48.1, 48.2, 48.4, 48.5, 48.7–48.10, 48.13.

## Gaussian quadrature and Cauchy transforms

[Mathematical scope](SYNOPSIS48.md#gaussian-quadrature-and-cauchy-transforms).

### Mathlib

Chebyshev–Gauss quadrature is the equal-weight rule at the roots of \(T_n\). For \(n\neq 0\) and a real polynomial \(P\) of degree less than \(2n\),
\[
\int P\,d\mu_T=\frac{\pi}{n}\sum_{i=0}^{n-1} P\Bigl(\cos\frac{(2i+1)\pi}{2n}\Bigr)
\]
(`Analysis/SpecialFunctions/Trigonometric/Chebyshev/ChebyshevGauss.lean`). This is quadrature for the single weight \((1-x^2)^{-1/2}\), not a general Gauss quadrature theorem.

**Synopsis entries.** Partly covered: 48.14 (Chebyshev–Gauss rule for the weight \((1-x^2)^{-1/2}\) only). Not covered: 48.15–48.20.

## Jacobi operators and spectral measures

[Mathematical scope](SYNOPSIS48.md#jacobi-operators-and-spectral-measures).

**Synopsis entries.** Not covered: 48.22–48.31.

## Moment existence, uniqueness, and positivity

[Mathematical scope](SYNOPSIS48.md#moment-existence-uniqueness-and-positivity).

### TauCeti

**Determinacy.** Two finite measures on \(\mathbb R\) with the same polynomial moments are equal when both have finite exponential moments near \(0\) (`TauCeti.Measure.ext_of_forall_integral_pow_eq`), in particular when \(e^{a\lvert x\rvert}\) is integrable for some \(a>0\) for each measure (`TauCeti.Measure.ext_of_forall_integral_pow_eq_of_exists_integrable_exp`; [determinacy](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Moments/Determinacy.lean)). Correspondingly, a function in \(L^2(\nu)\) orthogonal to all monomials vanishes when \(e^{a\lvert x\rvert}\in L^1(\nu)\) for some \(a>0\) ([vanishing moments](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Moments/VanishingMoments.lean)). Finite measures on \([0,\infty)\) are determined by their Laplace transform, even by its values at the nonnegative integers ([Laplace uniqueness](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Moments/LaplaceDeterminacy.lean)). Two finite measures carried by a compact subset \(K\) of \(\mathbb R^\iota\), \(\iota\) finite, with the same mixed monomial moments are equal (`TauCeti.Measure.ext_of_forall_integral_monomial_eq_of_support`; [compact determinacy](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Moments/CompactDeterminacy.lean)); this is the uniqueness half of the Hausdorff moment problem, in several variables, and it covers measures of compact support on \(\mathbb R\). Exponential integrability is strictly stronger than the Carleman condition, and none of these theorems solves the Hamburger, Stieltjes or Hausdorff existence problem for a prescribed moment sequence.

**Indeterminacy.** The Stieltjes lognormal family is formalized: for \(\lvert\varepsilon\rvert\le1\) the probability measure with density \(e^{-(\log x)^2/2}\bigl(1+\varepsilon\sin(2\pi\log x)\bigr)/(x\sqrt{2\pi})\) on \(x>0\) has \(n\)-th moment \(e^{n^2/2}\), and distinct parameters in \([-1,1]\) give distinct measures (`TauCeti.Probability.logNormalMomentPerturbation`, `integral_pow_logNormalMomentPerturbation`, `injOn_logNormalMomentPerturbation`; [lognormal indeterminacy](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Distributions/LogNormal/MomentIndeterminacy.lean)).

**Related positivity results (supporting).** The Hausdorff–Bernstein–Widder theorem characterizes the functions continuous on \([0,\infty)\) and completely monotone on \((0,\infty)\) as Laplace transforms of finite measures on \([0,\infty)\), with uniqueness ([Bernstein's theorem](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/CompletelyMonotone/Bernstein/HausdorffBernsteinWidder.lean)); this is the continuous analogue of the Hausdorff theorem, not the moment-sequence statement. A positive-semidefinite Hankel sequence \((a_{m+n})\) that is bounded above satisfies \(a_1\le a_0\) (`TauCeti.sub_nonneg_of_posSemidef_hankel`; [Hankel estimate](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Matrix/PosSemidef.lean)), a Cauchy–Schwarz consequence rather than a moment existence theorem. Stieltjes functions determine their representing data uniquely ([Stieltjes uniqueness](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/CompletelyMonotone/Stieltjes/Uniqueness.lean)), and the boundary Cayley map transports Herglotz representations to Nevanlinna representations on the real line ([Nevanlinna transport](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Pick/Nevanlinna.lean)); neither is the Nevanlinna parametrization of an indeterminate moment problem.

**Synopsis entries.** Covered: 48.38 (TauCeti). Partly covered: 48.34 (uniqueness of the representing measure only; the difference criterion is absent), 48.35 (determinacy for compact support; the support bound from \(s_{2n}\le CR^{2n}\) is not stated). Not covered: 48.32, 48.33, 48.36, 48.37, 48.39–48.46.

## Orthogonal polynomials on the unit circle

[Mathematical scope](SYNOPSIS48.md#orthogonal-polynomials-on-the-unit-circle).

### TauCeti

Supporting material only. Herglotz's theorem is proved: a positive-definite function \(\varphi\) on \(\mathbb Z\) is the moment sequence \(\varphi(n)=\int z^n\,d\mu(z)\) of a finite positive measure on the unit circle (`TauCeti.exists_isFiniteMeasure_integral_zpow_eq`, via Fejér densities; [Herglotz](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Bochner/Herglotz.lean)). This is the trigonometric moment problem, not the Verblunsky or Szegő theory of the associated orthogonal polynomials. Toeplitz operators on the boundary Hardy space are defined ([Toeplitz](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/Hardy/Toeplitz.lean)), but Toeplitz determinants and their asymptotics are not.

**Synopsis entries.** Not covered: 48.47–48.58, 48.76.

## Asymptotics and potential theory

[Mathematical scope](SYNOPSIS48.md#asymptotics-and-potential-theory).

### Mathlib

Supporting material only. The Chebyshev extremal comparison is proved: if \(n\ge1\), \(\deg P\leq n\), and \(\lvert P\rvert\leq 1\) on \([-1,1]\), then the leading coefficient of \(P\) is at most \(2^{n-1}\), with equality for \(n\geq 2\) if and only if \(P=T_n\); under the same hypotheses \(P^{(k)}(x)\le T_n^{(k)}(x)\) for \(x\ge1\) (`leadingCoeff_le_of_forall_abs_le_one`, `leadingCoeff_eq_iff_of_forall_abs_le_one`, `eval_iterate_derivative_le_of_forall_abs_le_one`; `Analysis/SpecialFunctions/Trigonometric/Chebyshev/Extremal.lean`; see Section 47). This is the sup-norm extremal problem on \([-1,1]\), not \(L^2(\mu)\) norm asymptotics or regularity.

**Synopsis entries.** Not covered: 48.59–48.68.

## Multivariate structure and modified measures

[Mathematical scope](SYNOPSIS48.md#multivariate-structure-and-modified-measures).

### TauCeti

For finitely many σ-finite measures \(\mu_i\), coordinatewise Hilbert bases of \(L^2(\mu_i)\) multiply to a Hilbert basis of \(L^2\bigl(\prod_i\mu_i\bigr)\), with product coordinates (`TauCeti.piHilbertBasis`, `piHilbertBasis_repr_L2piMul`; [product bases](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/L2/Pi.lean)). Applied to complete one-variable orthonormal polynomial systems this gives the completeness of tensor-product systems; the multi-index Hermite bases of \(L^2(\mathbb R^\iota)\) and of the standard Gaussian measure on \(\mathbb R^\iota\) are constructed this way ([Hermite functions](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Pi/Basis.lean), [Gaussian Hermite](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Distributions/Gaussian/Hermite/Pi/Basis.lean)). The multivariate compact moment determinacy theorem is recorded under [Moment existence, uniqueness, and positivity](#moment-existence-uniqueness-and-positivity).

**Synopsis entries.** Covered: 48.72 (TauCeti, in orthonormal form for finitely many factors). Not covered: 48.70, 48.71, 48.73–48.75, 48.21, 48.77–48.79.
