# 27. Fourier Analysis and Real-Variable Harmonic Analysis

Checked against Mathlib commit `f039e1b8a616d45782a5c7fc5e7909249c36b8ea` (2026-10-18, Lean `v4.36.0-rc1`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. The roots for this section are `Mathlib.Analysis.Fourier.FourierTransform`, `Mathlib.Analysis.Fourier.FourierTransformDeriv`, `Mathlib.Analysis.Fourier.Inversion`, `Mathlib.Analysis.Fourier.RiemannLebesgueLemma`, `Mathlib.Analysis.Fourier.Convolution`, `Mathlib.Analysis.Fourier.PoissonSummation`, `Mathlib.Analysis.Fourier.LpSpace`, `Mathlib.Analysis.Fourier.AddCircle`, `Mathlib.Analysis.Fourier.AddCircleMulti`, `Mathlib.Analysis.Fourier.Notation`, `Mathlib.Analysis.Fourier.ZMod`, `Mathlib.Analysis.Distribution.SchwartzSpace.Fourier`, and `Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform`.

**Namespaces.** The general integral is `VectorFourier`; the inner-product-space transform, and its specializations to \(\mathbb{R}\), is `Real`. Notation for \(\mathcal{F}\) and \(\mathcal{F}^{-1}\), and the typeclasses expressing linearity and inversion, is `FourierTransform`. Schwartz space is `SchwartzMap`. Gaussians are `GaussianFourier`. Fourier series on the circle are `AddCircle`, and on a finite product of circles `UnitAddTorus`. The discrete transform is `ZMod`, with a statement for `DirichletCharacter`. Characters as bounded continuous functions are `BoundedContinuousFunction`. The \(L^2\) transform is `MeasureTheory.Lp`.

This note records the Euclidean Fourier transform in the unitary normalization, Fourier series on the circle and the torus, and the discrete transform on \(\mathbb{Z}/N\mathbb{Z}\). Real-variable singular-integral theory is not in Mathlib; the TauCeti supplement below records it.

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

The following additions were checked in TauCeti revision `6ebb29f84b4d`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

The centred Hardy–Littlewood maximal function has weak \((1,1)\), strong \((p,p)\) for \(1<p<\infty\), and \(L^\infty\) bounds on finite-dimensional real normed spaces with additive Haar measure ([maximal inequalities](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/MeasureTheory/Integral/MaximalFunction.lean)). Diagonal Marcinkiewicz interpolation between finite weak-type endpoints is proved; the off-diagonal theorem is not ([interpolation](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/MeasureTheory/Integral/Marcinkiewicz/General.lean)). The Riesz–Thorin theorem is proved for complex-linear operators on simple functions, with \(\|Tf\|_q\le M_0^{1-\theta}M_1^\theta\|f\|_p\) at the intermediate exponents, source exponents in \((0,\infty]\) and target exponents in \([1,\infty]\) ([Riesz–Thorin](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/MeasureTheory/Integral/RieszThorin.lean)); the Hausdorff–Young inequality is mentioned there as a consequence but not stated. Smooth approximate identities converge strongly on \(L^p\) for \(1\le p<\infty\) ([source](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/MeasureTheory/Function/Lp/ApproximateIdentity.lean)).

The Calderón–Zygmund decomposition is proved on \(\mathbb R^n\) with dyadic cubes: for integrable \(f\) and \(t>0\), \(f=g+\sum_Qb_Q\) over disjoint maximal dyadic cubes with \(t<⨍_Q\|f\|\le2^nt\) and \(t|\bigcup Q|\le\int_{\bigcup Q}\|f\|\), where \(\|g\|\le2^nt\) a.e., \(\|g\|_1\le\|f\|_1\), and each \(b_Q\) is supported on \(Q\) with mean zero and \(\|b_Q\|_1\le2\int_Q\|f\|\) ([decomposition](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/MeasureTheory/Integral/CalderonZygmund/Decomposition.lean)). The Calderón–Zygmund theorem follows: an operator bounded on \(L^2(\mathbb R^n)\) whose kernel satisfies Hörmander's condition (in particular a standard kernel with \(\|K(x,y)-K(x,y')\|\le C|y-y'|^\delta/|x-y'|^{n+\delta}\)) is of weak type \((1,1)\) and of strong type \((p,p)\) for \(1<p<2\), with explicit constants, and for \(2<p<\infty\) when the adjoint satisfies the condition, the estimates being proved on \(L^2\cap L^p\) ([weak type](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/MeasureTheory/Integral/CalderonZygmund/WeakType.lean), [standard kernels](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/MeasureTheory/Integral/CalderonZygmund/StandardKernel.lean), [strong type](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/MeasureTheory/Integral/CalderonZygmund/StrongType.lean)). Under Hörmander's condition in the first variable such operators map \(L^\infty\cap L^2\) into BMO, with \(⨍_Q\|Tf-(Tf)_Q\|\le2(\sqrt D\|T\|+B)\|f\|_\infty\) ([BMO bound](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/MeasureTheory/Integral/CalderonZygmund/BoundedMeanOscillation.lean)). The John–Nirenberg inequality \(|\{x\in Q:\|f-f_Q\|>s\}|\le2e^{-cs/M}|Q|\) for mean oscillation at most \(M\) is proved on dyadic cubes and on all cubes, with the resulting exponential integrability ([John–Nirenberg](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/MeasureTheory/Integral/JohnNirenberg.lean)). No BMO space, Hardy space \(H^1\), or duality between them is defined.

For essentially bounded symbols, the Fourier multiplier \(\mathcal F^{-1}(m\,\mathcal Ff)\) on \(L^2\) is defined with \(\|T_m\|\le\|m\|_\infty\) ([\(L^2\) multipliers](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Fourier/L2Multiplier.lean)). The Mihlin–Hörmander theorem is proved: on a real inner product space of dimension \(n\) with complex Hilbert-space values, if \(m\) is smooth away from \(0\) and \(\|D^km(\xi)\|\le A\|\xi\|^{-k}\) for \(k\le N\), \(2N>n\), then \(T_m\) is bounded on \(L^p\), \(1<p<\infty\), with norm at most \(CA\) ([Mihlin–Hörmander](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Fourier/MihlinHormander.lean)). This covers the Riesz transforms and the symbol \(-i\operatorname{sgn}\xi\) of the Hilbert transform as multipliers; no principal-value singular integral is defined. The proof uses smooth dyadic Littlewood–Paley cutoffs and the corresponding pieces of Mihlin symbols ([cutoffs](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Calculus/BumpFunction/LittlewoodPaley.lean), [pieces](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Distribution/SchwartzSpace/LittlewoodPaley.lean)), but no square-function theorem.

TauCeti also constructs the Hermite-function Hilbert basis and its Fourier eigenfunction description ([Fourier–Hermite basis](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Fourier/HilbertBasis.lean)), and proves Herglotz's theorem, Bochner's theorem on \(\mathbb R^n\), and Bochner's theorem on locally compact abelian groups (Section 28); Herglotz's proof uses Fejér means of measures ([Herglotz](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Bochner/Herglotz.lean)), but Fejér summation of Fourier series of functions is not proved. On the circle, the sharp Wirtinger inequality \(\int\|f-\bar f\|^2\le((b-a)/2\pi)^2\int\|f'\|^2\) for absolutely continuous periodic \(f\), with its equality case, is proved by Fourier coefficients ([Wirtinger](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Fourier/Wirtinger.lean)). No Carleson theorem was located.

The Wiener–Ikehara Tauberian theorem is proved by Fourier analysis: if \(a_n\ge0\), the Dirichlet series \(F(s)=\sum a_nn^{-s}\) converges for \(\operatorname{Re}s>1\), and \(F(s)-\kappa/(s-1)\) extends continuously to \(\operatorname{Re}s\ge1\), then \(x^{-1}\sum_{n\le x}a_n\to\kappa\) ([Wiener–Ikehara](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/NumberTheory/LSeries/WienerIkehara/SharpCutoff.lean), `wienerIkehara`; the Fourier-analytic core is in [Fourier](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/NumberTheory/LSeries/WienerIkehara/Fourier.lean) and [Riemann–Lebesgue on a vertical line](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Fourier/RiemannLebesgue.lean)). This is the Tauberian theorem behind the prime number theorem; Wiener's general Tauberian theorem for \(L^1(\mathbb{R})\) is not proved. TauCeti also identifies the continuous characters of the circle with the Fourier monomials ([circle characters](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Fourier/AddCircle.lean)).

## Topics of Section 27 not found in either inspected library

- The Hausdorff–Young inequality for \(1<p<2\), and its failure for \(p>2\). The bounds at the endpoints are the \(L^1\to L^\infty\) estimate and the \(L^2\) isometry; TauCeti's Riesz–Thorin theorem is the interpolation ingredient.
- A Fourier transform defined on \(L^p\) for an exponent other than \(1\) and \(2\).
- The Hilbert transform as a principal-value integral \(\operatorname{pv}\,\pi^{-1}\int f(y)/(x-y)\,dy\), its almost-everywhere existence, and its weak type \((1,1)\) bound. Its \(L^p\) boundedness as the multiplier \(-i\operatorname{sgn}\xi\) follows from TauCeti's Mihlin–Hörmander theorem.
- The Littlewood–Paley square-function theorem \(\|f\|_p\asymp\|(\sum_j|\Delta_jf|^2)^{1/2}\|_p\). TauCeti has the dyadic cutoffs only.
- Muckenhoupt \(A_p\) weights and weighted norm inequalities. TauCeti's maximal inequalities are unweighted.
- The real-variable Hardy space \(H^1(\mathbb R^d)\), atomic decompositions, and Hardy–BMO duality. TauCeti has the John–Nirenberg inequality and the \(L^\infty\to\mathrm{BMO}\) bound, without a BMO space.
- Carleson’s theorem, and pointwise convergence of Fourier series beyond the case of summable coefficients.
- Fejér’s kernel and Cesàro summation of Fourier series, the Dirichlet kernel, and the classical pointwise convergence tests of Dini and Dirichlet–Jordan.
- Uncertainty principles (Heisenberg's inequality), the Paley–Wiener theorems, and Wiener's general Tauberian theorem. The Wiener–Ikehara theorem is in TauCeti, as recorded above.
- Oscillatory integrals, stationary phase, and Fourier restriction theory (the Stein–Tomas theorem).
