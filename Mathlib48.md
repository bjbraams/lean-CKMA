# 48. Orthogonal Polynomials, Moment Problems, and Spectral Recurrences

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. The roots for this section are `Mathlib.RingTheory.Polynomial.Chebyshev`, `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic`, `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality`, `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema`, `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss`, `Mathlib.RingTheory.Polynomial.Hermite.Basic`, `Mathlib.RingTheory.Polynomial.Hermite.Gaussian`, and `Mathlib.RingTheory.Polynomial.ShiftedLegendre`.

**Namespaces.** `Polynomial.Chebyshev` for the four families \(T\), \(U\), \(C\), and \(S\), including the real orthogonality measure `measureT`. `Polynomial.hermite` and `Polynomial.shiftedLegendre` are the algebraic families. There is no module for the Hamburger or Stieltjes moment problem, and none for Jacobi operators.

Chebyshev polynomials of both kinds are available algebraically and, on the interval, analytically. Hermite and shifted Legendre polynomials are algebraic. The spectral theory of moment problems and of three-term recurrences was not found.

## Chebyshev polynomials

Over any commutative ring \(R\), the Chebyshev polynomials of the first kind \(T_n\in R[X]\), indexed by \(n\in\mathbb{Z}\), are defined by \(T_0=1\), \(T_1=X\), and \(T_{n+2}=2XT_{n+1}-T_n\), with the same recurrence run backwards for negative indices. They are even in the index: \(T_{-n}=T_n\). The second kind starts with \(U_0=1\), \(U_1=2X\), and the same recurrence; \(U_{-1}=0\). Rescalings satisfy \(C_n(2X)=2T_n(X)\) and \(S_n(2X)=U_n(X)\). The product identity is \(2T_m T_k=T_{m+k}+T_{m-k}\), and composition is \(T_{mn}=T_m\circ T_n\). The formal derivative is \((T_n)'=n\,U_{n-1}\) (`RingTheory/Polynomial/Chebyshev.lean`).

Over an integral domain in which \(2\neq 0\), \(T_n\) has degree \(\lvert n\rvert\) and leading coefficient \(2^{\lvert n\rvert-1}\), the case \(n=0\) being the constant \(1\).

On the complex and real trigonometric functions, \(T_n(\cos\theta)=\cos(n\theta)\) and \(U_n(\cos\theta)\sin\theta=\sin((n+1)\theta)\), with the analogous identities for \(\cosh\) and \(\sinh\) (`Analysis/SpecialFunctions/Trigonometric/Chebyshev/Basic.lean`).

The orthogonality measure `measureT` is Lebesgue measure on \((-1,1]\) with density \((1-x^2)^{-1/2}\). For a real function,
\[
\int f\,d\mu_T=\int_{-1}^{1} f(x)\,(1-x^2)^{-1/2}\,dx=\int_0^\pi f(\cos\theta)\,d\theta,
\]
and every function continuous on \([-1,1]\) is integrable. The polynomials of the first kind are orthogonal for this measure: \(\int T_0\,d\mu_T=\pi\) and \(\int T_n\,d\mu_T=0\) for \(n\neq 0\); \(\int T_n T_m\,d\mu_T=0\) for distinct natural numbers \(n,m\); \(\int T_0^2\,d\mu_T=\pi\); and \(\int T_n^2\,d\mu_T=\pi/2\) for \(n\neq 0\) (`Analysis/SpecialFunctions/Trigonometric/Chebyshev/Orthogonality.lean`). Orthogonality of \(U_n\) against the weight \(\sqrt{1-x^2}\), and the statement that the \(T_n\) form a Hilbert basis of \(L^2(\mu_T)\), are marked as future work in that file.

For \(n\neq 0\), \(\lvert T_n(x)\rvert\leq 1\) if and only if \(\lvert x\rvert\leq 1\). The roots of \(T_n\) are the simple points \(\cos\bigl((2k+1)\pi/(2n)\bigr)\) for \(k=0,\ldots,n-1\). The roots of \(U_n\) are the simple points \(\cos\bigl((k+1)\pi/(n+1)\bigr)\) for \(k=0,\ldots,n-1\). The local extrema of \(T_n\) on \((-1,1)\) occur at \(\cos(k\pi/n)\). A nonzero root of \(T_n\) is irrational. On \([-1,1]\), the \(k\)-th derivative of \(T_n\) is bounded by its value at \(1\) (`Analysis/SpecialFunctions/Trigonometric/Chebyshev/RootsExtrema.lean`).

Chebyshev–Gauss quadrature is the equal-weight rule at the roots of \(T_n\). For \(n\neq 0\) and a real polynomial \(P\) of degree less than \(2n\),
\[
\int P\,d\mu_T=\frac{\pi}{n}\sum_{i=0}^{n-1} P\Bigl(\cos\frac{(2i+1)\pi}{2n}\Bigr)
\]
(`Analysis/SpecialFunctions/Trigonometric/Chebyshev/ChebyshevGauss.lean`). This is quadrature for the single weight \((1-x^2)^{-1/2}\), not a general Gauss quadrature theorem.

The extremal comparison used in approximation theory is in the same directory: if \(n\ge1\), \(\deg P\leq n\), and \(\lvert P\rvert\leq 1\) on \([-1,1]\), then the leading coefficient of \(P\) is at most \(2^{n-1}\), with equality for \(n\geq 2\) if and only if \(P=T_n\) (`Analysis/SpecialFunctions/Trigonometric/Chebyshev/Extremal.lean`).

## Hermite and shifted Legendre

The probabilists’ Hermite polynomials are the integer polynomials defined by \(He_0=1\) and \(He_{n+1}=X\,He_n-(He_n)'\). Each \(He_n\) is monic of degree \(n\), with an explicit coefficient formula, and the coefficient of \(X^k\) vanishes when \(n+k\) is odd (`RingTheory/Polynomial/Hermite/Basic.lean`). Analytically, the only identity proved is the Gaussian derivative formula: the \(n\)-th derivative of \(\exp(-y^2/2)\) at \(x\) equals \((-1)^n He_n(x)\exp(-x^2/2)\) (`RingTheory/Polynomial/Hermite/Gaussian.lean`). No integral orthogonality for the Gaussian weight is proved.

The shifted Legendre polynomials are
\[
P_n(X)=\sum_{k=0}^n (-1)^k\binom{n}{k}\binom{n+k}{n} X^k\in\mathbb{Z}[X],
\]
of degree \(n\). Rodrigues’ formula is \(n!\,P_n=\frac{d^n}{dX^n}\bigl(X^n(1-X)^n\bigr)\), and evaluation satisfies \(P_n(x)=(-1)^n P_n(1-x)\) (`RingTheory/Polynomial/ShiftedLegendre.lean`). The file remarks that these polynomials appear in the theory of orthogonal polynomials. No integral orthogonality on \([0,1]\) is proved. The classical (unshifted) Legendre polynomials were not found; the Legendre symbol of number theory is a different object.

## Moment problems and recurrences

The three-term recurrence is present as the defining relation of \(T_n\) and \(U_n\), and the file records that relating the definition to the general `LinearRecurrence` API is future work. That recurrence is not given a spectral theorem.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

Hermite polynomial/function orthogonality and completeness are implemented. The normalized Hermite functions form a Hilbert basis of \(L^2(\mathbb R)\), with creation/annihilation identities and the harmonic-oscillator differential equation ([orthogonality](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/SpecialFunctions/Hermite/Orthogonality.lean), [basis](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/SpecialFunctions/Hermite/Function/HilbertBasis.lean), [oscillator](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Oscillator.lean)). The normalized Chebyshev \(T_n\) form a Hilbert basis for the weighted \(L^2\) space with weight \((1-x^2)^{-1/2}\) on \([-1,1]\), with Parseval identities ([Chebyshev basis](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/SpecialFunctions/Trigonometric/Chebyshev/HilbertBasis.lean), [Parseval](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Parseval.lean)).

Finite measures on \(\mathbb R\) are determined by their polynomial moments under a finite exponential-moment hypothesis ([determinacy](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Probability/Moments/Determinacy.lean)). Finite measures on \([0,\infty)\) are determined by their Laplace transform, even its values at the nonnegative integers ([Laplace uniqueness](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Probability/Moments/LaplaceDeterminacy.lean)). These are determinacy theorems; they do not solve the Hamburger or Stieltjes existence problem for an arbitrary prescribed moment sequence.

A general completeness criterion connects the two: if a weighted measure on \(\mathbb{R}\) has a finite exponential moment, any orthogonal family of polynomials of exact degrees is a Hilbert basis of \(L^2\) of that measure, because a function orthogonal to every monomial vanishes by moment determinacy ([polynomial completeness](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/InnerProductSpace/PolynomialCompleteness.lean), [weighted bases](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/InnerProductSpace/WeightedOrthogonalBasis.lean)). A multivariate determinacy theorem for finite measures on a compact set is also proved ([compact determinacy](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Probability/Moments/CompactDeterminacy.lean)).

## Topics of Section 48 not found in either inspected library

- Existence criteria for prescribed Hamburger or Stieltjes moment sequences. TauCeti proves moment determinacy under exponential integrability and uniqueness from Laplace transforms.
- Jacobi operators, and a spectral theorem for three-term recurrences.
- Integral orthogonality of the shifted Legendre polynomials and of \(U_n\). Hermite orthogonality is proved in TauCeti.
- The classical Legendre polynomials on \([-1,1]\), as opposed to the shifted family, and the Laguerre, Jacobi, and Gegenbauer families.
- General orthogonal polynomials with respect to a measure: the Christoffel–Darboux formula, zeros and interlacing, Gauss quadrature for a general weight, Szegő's theory on the circle, and Favard's theorem.
