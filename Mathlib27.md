# 27. Fourier Analysis and Real-Variable Harmonic Analysis

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. The roots for this section are `Mathlib.Analysis.Fourier.FourierTransform`, `Mathlib.Analysis.Fourier.FourierTransformDeriv`, `Mathlib.Analysis.Fourier.Inversion`, `Mathlib.Analysis.Fourier.RiemannLebesgueLemma`, `Mathlib.Analysis.Fourier.Convolution`, `Mathlib.Analysis.Fourier.PoissonSummation`, `Mathlib.Analysis.Fourier.LpSpace`, `Mathlib.Analysis.Fourier.AddCircle`, `Mathlib.Analysis.Fourier.AddCircleMulti`, `Mathlib.Analysis.Fourier.Notation`, `Mathlib.Analysis.Fourier.ZMod`, `Mathlib.Analysis.Distribution.SchwartzSpace.Fourier`, and `Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform`.

**Namespaces.** The general integral is `VectorFourier`; the inner-product-space transform, and its specializations to \(\mathbb{R}\), is `Real`. Notation for \(\mathcal{F}\) and \(\mathcal{F}^{-1}\), and the typeclasses expressing linearity and inversion, is `FourierTransform`. Schwartz space is `SchwartzMap`. Gaussians are `GaussianFourier`. Fourier series on the circle are `AddCircle`, and on a finite product of circles `UnitAddTorus`. The discrete transform is `ZMod`, with a statement for `DirichletCharacter`. Characters as bounded continuous functions are `BoundedContinuousFunction`. The \(L^2\) transform is `MeasureTheory.Lp`.

This note records the Euclidean Fourier transform in the unitary normalization, Fourier series on the circle and the torus, and the discrete transform on \(\mathbb{Z}/N\mathbb{Z}\). Real-variable singular-integral theory was not found.

## The Euclidean transform

Let \(V\) be a finite-dimensional real inner product space and let \(E\) be a normed space over \(\mathbb{C}\). The Fourier transform and its inverse are
\[
\mathcal{F}f(w)=\int_V e^{-2\pi i\langle v,w\rangle}f(v)\,dv,
\qquad
\mathcal{F}^{-1}f(w)=\int_V e^{2\pi i\langle v,w\rangle}f(v)\,dv,
\]
with Lebesgue measure, so that \(\mathcal{F}^{-1}f(w)=\mathcal{F}f(-w)\). The same pattern is available for a continuous bilinear pairing and a Haar measure, as an integral against a unitary additive character (`Analysis/Fourier/FourierTransform.lean`, `Analysis/Fourier/Notation.lean`).

The transform of an integrable function is continuous and bounded, and \(\|\mathcal{F}f(w)\|\leq\|f\|_{L^1}\). On \(L^1\), this is a continuous linear map into the bounded continuous functions, of operator norm at most \(1\). Translation becomes modulation by a character. The transform commutes with linear isometric equivalences of the domain. If the codomain is a space of continuous linear or multilinear maps and \(f\) is integrable, the transform may be evaluated pointwise on vectors.

If \(f\) and \(v\mapsto\|v\|\|f(v)\|\) are integrable, then \(\mathcal{F}f\) is differentiable and its Fréchet derivative is the transform of \(v\mapsto -(2\pi i)\langle v,\cdot\rangle f(v)\). If \(\|v\|^n\|f(v)\|\) is integrable for all \(n\leq N\), then \(\mathcal{F}f\) is of class \(C^N\), and the derivatives are transforms of the corresponding polynomial multipliers. In the other direction, if \(f\) is differentiable, both \(f\) and \(Df\) are integrable, and the codomain conventions of the file apply, the transform of \(Df\) is multiplication of \(\mathcal{F}f\) by \(2\pi i\langle v,\cdot\rangle\). On \(\mathbb{R}\),
\[
(\mathcal{F}f)'=\mathcal{F}(-2\pi i\, x f(x)),
\qquad
\mathcal{F}(f')(x)=(2\pi i x)\,\mathcal{F}f(x),
\]
under the corresponding integrability hypotheses, and likewise for higher derivatives with \((-2\pi i x)^n\) and \((2\pi i x)^n\) (`Analysis/Fourier/FourierTransformDeriv.lean`).

On Schwartz space the transform is a continuous linear endomorphism, and it is inverted by \(\mathcal{F}^{-1}\). Thus it is a continuous linear equivalence of Schwartz space onto itself. Differentiation and multiplication by the inner product pass through the transform as above (`Analysis/Distribution/SchwartzSpace/Fourier.lean`).

A function of temperate growth defines a Fourier multiplier on Schwartz functions and on tempered distributions by \(\mathcal{F}^{-1}(g\cdot\mathcal{F}f)\). Directional derivatives and the Laplacian are multipliers of this kind (`Analysis/Distribution/FourierMultiplier.lean`). This is an algebraic operation on the Schwartz calculus. It is not a multiplier theorem on \(L^p\).

## Inversion, the Gaussian, and the Riemann–Lebesgue lemma

Inversion uses an explicit Gaussian (`Analysis/SpecialFunctions/Gaussian/FourierTransform.lean`, `Analysis/Fourier/Inversion.lean`). For \(b\in\mathbb{C}\) with positive real part,
\[
\mathcal{F}\bigl(e^{-\pi b x^2}\bigr)(t)=b^{-1/2}e^{-\pi t^2/b}
\]
on \(\mathbb{R}\), and more generally
\[
\mathcal{F}\bigl(e^{-\pi b x^2+2\pi c x}\bigr)(t)=b^{-1/2}e^{-\pi(t+ic)^2/b}.
\]
In particular \(e^{-\pi x^2}\) is its own Fourier transform. On a finite-dimensional real inner product space of dimension \(n\),
\[
\mathcal{F}\bigl(e^{-b\|v\|^2}\bigr)(w)=\Bigl(\frac{\pi}{b}\Bigr)^{n/2}e^{-\pi^2\|w\|^2/b}.
\]
The case \(b=\pi\) says that \(v\mapsto e^{-\pi\|v\|^2}\) is its own Fourier transform.

If \(f\) and \(\mathcal{F}f\) are integrable and the codomain is complete, then \(\mathcal{F}^{-1}(\mathcal{F}f)(v)=f(v)\) at every point of continuity of \(f\). If \(f\) itself is continuous, the identity holds everywhere. The symmetric statement \(\mathcal{F}(\mathcal{F}^{-1}f)=f\) is proved under the same hypotheses. Schwartz functions satisfy the hypotheses, which is why inversion holds on Schwartz space.

The Riemann–Lebesgue lemma: the Fourier transform of an integrable function on a finite-dimensional real inner product space tends to \(0\) at infinity. On a general finite-dimensional real vector space the same vanishing holds for the integral against the duality pairing, with respect to any Haar measure (`Analysis/Fourier/RiemannLebesgueLemma.lean`).

For Schwartz functions valued in a complete complex normed space, \(\int \langle\mathcal{F}f,\mathcal{F}g\rangle=\int\langle f,g\rangle\) whenever the bracket is a continuous sesquilinear form, and in particular the \(L^2\) inner product and the \(L^2\) norm are preserved. The transform is self-adjoint against a continuous bilinear pairing: \(\int B(\mathcal{F}f,g)=\int B(f,\mathcal{F}g)\). The operator norm from \(L^1\) into \(L^\infty\) is at most \(1\) on Schwartz functions (`Analysis/Distribution/SchwartzSpace/Fourier.lean`).

## What `LpSpace.lean` proves

The file `Analysis/Fourier/LpSpace.lean` treats only \(L^2\). The domain is a finite-dimensional real inner product space and the codomain is a complete complex inner product space. The Schwartz transform preserves the \(L^2\) norm, and Schwartz functions are dense in \(L^2\), so the transform extends to a linear isometric equivalence of \(L^2\) onto itself. Its inverse is the inverse Fourier transform. It preserves inner products, it is continuous, and it agrees on \(L^2\) both with the Schwartz transform and with the Fourier transform of tempered distributions. That is Plancherel’s theorem for \(L^2\).

The file does not define a Fourier transform on \(L^p\) for any \(p\) other than \(2\), and it does not prove the Hausdorff–Young inequality. The endpoint bound \(\|\mathcal{F}f\|_\infty\leq\|f\|_1\), as a map from \(L^1\) into the bounded continuous functions, is the theorem in `Analysis/Fourier/FourierTransform.lean` recorded above. No intermediate exponent is treated.

## Convolution and Poisson summation

On a finite-dimensional real inner product space, if \(f_1\) and \(f_2\) are integrable and \(B\) is a continuous bilinear map on their complete codomains, the Fourier transform of the convolution \(f_1\star_B f_2\) is the pointwise pairing \(B(\mathcal{F}f_1,\mathcal{F}f_2)\). For scalar multiplication and for multiplication in a complete normed algebra this is the usual product formula. Convolution of Schwartz functions is defined by transporting the pointwise pairing through the Fourier transform, and it agrees with the convolution of the underlying functions (`Analysis/Fourier/Convolution.lean`).

Poisson summation on \(\mathbb{R}\), for a continuous function \(f:\mathbb{R}\to\mathbb{C}\): if \(\sum_n\mathcal{F}f(n)\) converges, and if for every compact \(K\subset\mathbb{R}\) the sum \(\sum_n\|f(\cdot+n)\|_K\) converges, then
\[
\sum_{n\in\mathbb{Z}} f(x+n)=\sum_{n\in\mathbb{Z}}\mathcal{F}f(n)\,e^{2\pi i n x}.
\]
The identity holds in particular when both \(f\) and \(\mathcal{F}f\) decay as \(|x|^{-b}\) for some \(b>1\), and it holds for every Schwartz function \(\mathbb{R}\to\mathbb{C}\) (`Analysis/Fourier/PoissonSummation.lean`).

## The circle and the torus

Let \(T>0\) and write \(\mathbb{R}/T\mathbb{Z}\) for the additive circle. The Haar measure used here is normalized to total mass \(1\), not to length \(T\). The characters are the maps \(x\mapsto e^{2\pi i n x/T}\) for \(n\in\mathbb{Z}\). Their linear span is a conjugation-invariant subalgebra separating points, so by Stone–Weierstrass it is dense in the continuous complex functions. For \(1\leq p<\infty\) the characters are dense in \(L^p\). In \(L^2\) they are orthonormal, and they form a Hilbert basis indexed by \(\mathbb{Z}\). The Fourier coefficient of an integrable \(E\)-valued function is
\[
\widehat f(n)=\int e^{-2\pi i n t/T}f(t)\,d\mu,
\]
equivalently \((1/T)\) times the integral of the same integrand over any interval of length \(T\).

For \(f\in L^2\), the symmetric series \(\sum_n\widehat f(n)e^{2\pi i n t/T}\) converges to \(f\) in \(L^2\), and Parseval’s identity says \(\sum_n\|\widehat f(n)\|^2=\int\|f\|^2\). The same Parseval identity holds for a function that is square-integrable on a bounded interval, after passing to the periodic extension. If \(f\) is continuous and \(\sum_n\widehat f(n)\) converges absolutely, the Fourier series converges to \(f\) uniformly, hence pointwise. The characters are eigenfunctions of differentiation, and an integration by parts formula expresses the coefficients of a \(C^1\) function on an interval in terms of the coefficients of its derivative, for every nonzero frequency (`Analysis/Fourier/AddCircle.lean`).

On the \(d\)-dimensional unit torus \((\mathbb{R}/\mathbb{Z})^d\), with the probability Haar measure, the characters are the products \(\prod_{j\in d}e^{2\pi i n_j x_j}\). Their span is dense in the continuous functions and, for \(1\leq p<\infty\), dense in \(L^p\). They form an orthonormal Hilbert basis of \(L^2\) indexed by \(\mathbb{Z}^d\). The Fourier series of an \(L^2\) function converges to it in \(L^2\). Parseval’s identity holds both for the inner product and for the squared norm. Absolute summability of the coefficients of a continuous function gives uniform and pointwise convergence (`Analysis/Fourier/AddCircleMulti.lean`).

Fejér means are not constructed. Pointwise convergence of the partial sums for a general continuous or \(L^1\) function is not proved; the pointwise theorem in the library assumes summable coefficients.

The phase functions \(v\mapsto e(L(v,w))\), for a continuous unitary character \(e\) and a continuous bilinear pairing \(L\), are bounded continuous, and nontrivial data separate points. Finite linear combinations are closed under conjugation. The file presents them as the functions used to define characteristic functions of measures (`Analysis/Fourier/BoundedContinuousFunctionChar.lean`).

## The cyclic transform

On \(\mathbb{Z}/N\mathbb{Z}\), with \(N\neq 0\) and with values in a complex vector space, the discrete Fourier transform is the linear equivalence
\[
\mathcal{F}\Phi(k)=\sum_{j\bmod N}e^{-2\pi i jk/N}\Phi(j).
\]
Inversion reads \(\mathcal{F}(\mathcal{F}\Phi)(j)=N\,\Phi(-j)\), so the inverse transform carries the factor \(N^{-1}\) and the opposite sign in the character. The transform preserves parity. For a primitive Dirichlet character \(\chi\), one has \(\mathcal{F}\chi(k)=\chi^{-1}(-k)\) times the Gauss sum of \(\chi\) against the standard additive character (`Analysis/Fourier/ZMod.lean`).

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

The centred Hardy–Littlewood maximal function has weak \((1,1)\), strong \((p,p)\) for \(1<p<\infty\), and \(L^\infty\) bounds on finite-dimensional real normed spaces with additive Haar measure ([maximal inequalities](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/MeasureTheory/Integral/MaximalFunction.lean)). Diagonal Marcinkiewicz interpolation between finite weak-type endpoints is proved; the off-diagonal theorem is not ([interpolation](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/MeasureTheory/Integral/Marcinkiewicz/General.lean)). Smooth approximate identities converge strongly on \(L^p\) for \(1\le p<\infty\) ([source](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/MeasureTheory/Function/Lp/ApproximateIdentity.lean)).

TauCeti also constructs the Hermite-function Hilbert basis and its Fourier eigenfunction description ([Fourier–Hermite basis](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Fourier/HilbertBasis.lean)), and proves finite-dimensional Bochner representation for positive-definite functions (Section 28). No Calderón–Zygmund singular-integral theory, Littlewood–Paley theory, or Carleson theorem was located.

The Wiener–Ikehara Tauberian theorem is proved by Fourier analysis: if \(a_n\ge0\), the Dirichlet series \(F(s)=\sum a_nn^{-s}\) converges for \(\operatorname{Re}s>1\), and \(F(s)-\kappa/(s-1)\) extends continuously to \(\operatorname{Re}s\ge1\), then \(x^{-1}\sum_{n\le x}a_n\to\kappa\) ([Wiener–Ikehara](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/NumberTheory/LSeries/WienerIkehara/SharpCutoff.lean), `wienerIkehara`; the Fourier-analytic core is in [Fourier](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/NumberTheory/LSeries/WienerIkehara/Fourier.lean) and [Riemann–Lebesgue on a vertical line](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Fourier/RiemannLebesgue.lean)). This is the Tauberian theorem behind the prime number theorem; Wiener's general Tauberian theorem for \(L^1(\mathbb{R})\) is not proved. TauCeti also identifies the continuous characters of the circle with the Fourier monomials ([circle characters](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Fourier/AddCircle.lean)).

## Topics of Section 27 not found in either inspected library

- The Hausdorff–Young inequality for \(1<p<2\). The bounds at the endpoints are the \(L^1\to L^\infty\) estimate and the \(L^2\) isometry.
- A Fourier transform defined on \(L^p\) for an exponent other than \(1\) and \(2\).
- Calderón–Zygmund decomposition, Calderón–Zygmund operators, and singular integrals. A Fourier multiplier on Schwartz functions is defined and is not this theory.
- Littlewood–Paley theory.
- Functions of bounded mean oscillation.
- Carleson’s theorem, and pointwise convergence of Fourier series beyond the case of summable coefficients.
- The Hilbert transform.
- The Mihlin multiplier theorem, and any \(L^p\) boundedness theorem for Fourier multipliers.
- Fejér’s kernel and Cesàro summation of Fourier series, the Dirichlet kernel, and the classical pointwise convergence tests of Dini and Dirichlet–Jordan.
- Uncertainty principles, the Paley–Wiener theorems, and Wiener's general Tauberian theorem. The Wiener–Ikehara theorem is in TauCeti, as recorded above.
- Oscillatory integrals, stationary phase, and Fourier restriction theory.
