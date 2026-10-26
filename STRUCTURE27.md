# Structure 27: Fourier analysis and real-variable harmonic analysis

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS27.md); [bibliographical scope](CKMA-bib.md#ckma-27); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.Fourier.FourierTransform`, `Mathlib.Analysis.Fourier.FourierTransformDeriv`, `Mathlib.Analysis.Fourier.Inversion`, `Mathlib.Analysis.Fourier.RiemannLebesgueLemma`, `Mathlib.Analysis.Fourier.Convolution`, `Mathlib.Analysis.Fourier.PoissonSummation`, `Mathlib.Analysis.Fourier.LpSpace`, `Mathlib.Analysis.Fourier.AddCircle`, `Mathlib.Analysis.Fourier.AddCircleMulti`, `Mathlib.Analysis.Fourier.BoundedContinuousFunctionChar`, `Mathlib.Analysis.Fourier.Notation`, `Mathlib.Analysis.Fourier.ZMod`, `Mathlib.Analysis.Distribution.SchwartzSpace.Fourier`, `Mathlib.Analysis.Distribution.FourierMultiplier`, `Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform`, `Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation`, `Mathlib.Analysis.Calculus.BumpFunction.Convolution`, `Mathlib.MeasureTheory.Covering.DensityTheorem`, `Mathlib.MeasureTheory.Covering.Differentiation`.

**Namespaces.** In Mathlib, the general integral is `VectorFourier`; the inner-product-space transform, and its specializations to \(\mathbb{R}\), is `Real`. Notation for \(\mathcal{F}\) and \(\mathcal{F}^{-1}\), and the typeclasses expressing linearity and inversion, is `FourierTransform`. Schwartz space is `SchwartzMap`, Gaussians are `GaussianFourier`, Fourier series on the circle are `AddCircle`, and on a finite product of circles `UnitAddTorus`. The discrete transform is `ZMod`, with a statement for `DirichletCharacter`. The \(L^2\) transform is `MeasureTheory.Lp`. Lebesgue differentiation is in `VitaliFamily` and `IsUnifLocDoublingMeasure`, and mollifier convergence in `ContDiffBump`. In TauCeti, the maximal function, the Calderón–Zygmund decomposition, the John–Nirenberg inequality, the Mihlin–Hörmander theorem and \(L^p\) convolution are in `TauCeti`. The Calderón–Zygmund theorems are in `ContinuousLinearMap`, \(L^2\) Fourier multipliers in `MeasureTheory.Lp`, and the Wiener–Ikehara theorem in `TauCeti.LSeries`.

## The Fourier transform and translation-invariant operators

[Mathematical scope](SYNOPSIS27.md#the-fourier-transform-and-translation-invariant-operators).

### Mathlib

**The Euclidean transform.** Let \(V\) be a finite-dimensional real inner product space and \(E\) a normed space over \(\mathbb C\). The transform and its inverse are
\[
\mathcal{F}f(w)=\int_V e^{-2\pi i\langle v,w\rangle}f(v)\,dv,
\qquad
\mathcal{F}^{-1}f(w)=\int_V e^{2\pi i\langle v,w\rangle}f(v)\,dv,
\]
with Lebesgue measure. The same pattern is available for a continuous bilinear pairing and a Haar measure, as an integral against a unitary additive character (`Analysis/Fourier/FourierTransform.lean`, `Analysis/Fourier/Notation.lean`).

The transform of an integrable function is continuous and bounded, with \(\|\mathcal{F}f\|_\infty\leq\|f\|_{L^1}\). On \(L^1\) it is a continuous linear map into the bounded continuous functions, of operator norm at most \(1\). Translation becomes modulation by a character (`VectorFourier.fourierIntegral_comp_add_right`), and the transform commutes with linear isometric equivalences of the domain. The Riemann–Lebesgue lemma states that the transform of an integrable function tends to \(0\) at infinity (`Real.zero_at_infty_fourier`, and the Haar-measure form `Real.zero_at_infty_vector_fourierIntegral`) (`Analysis/Fourier/RiemannLebesgueLemma.lean`).

If \(f\) and \(\|v\|^n\|f(v)\|\) are integrable for \(n\leq N\), then \(\mathcal{F}f\) is \(C^N\), and its derivatives are transforms of polynomial multiples of \(f\). Conversely, the transform of \(Df\) is multiplication of \(\mathcal{F}f\) by \(2\pi i\langle v,\cdot\rangle\), under integrability of \(f\) and \(Df\). On \(\mathbb R\) this reads \((\mathcal{F}f)'=\mathcal{F}(-2\pi i\,xf)\) and \(\mathcal{F}(f')=2\pi i x\,\mathcal{F}f\), with the higher-order analogues (`Analysis/Fourier/FourierTransformDeriv.lean`).

**Schwartz space and inversion.** On Schwartz space the transform is a continuous linear equivalence, inverted by \(\mathcal{F}^{-1}\). On Schwartz functions it preserves the \(L^2\) inner product and is self-adjoint against continuous bilinear pairings (`Analysis/Distribution/SchwartzSpace/Fourier.lean`). If \(f\) and \(\mathcal{F}f\) are integrable and the codomain is complete, then \(\mathcal{F}^{-1}\mathcal{F}f=f\) at every continuity point of \(f\), and everywhere when \(f\) is continuous (`MeasureTheory.Integrable.fourierInv_fourier_eq`, `Continuous.fourierInv_fourier_eq`, `Analysis/Fourier/Inversion.lean`). Functions of temperate growth define Fourier multipliers \(\mathcal{F}^{-1}(g\cdot\mathcal{F}f)\) on Schwartz functions and on tempered distributions (`Analysis/Distribution/FourierMultiplier.lean`).

**Plancherel.** `Analysis/Fourier/LpSpace.lean` treats \(L^2\) only. For a complete complex inner-product codomain, the Schwartz transform extends to a linear isometric equivalence of \(L^2\) (`MeasureTheory.Lp.fourierTransformₗᵢ`). Its inverse is the inverse transform, it preserves inner products, and it agrees with the Schwartz transform and with the transform of tempered distributions.

**The Gaussian.** For \(\mathop{\mathrm{Re}}b>0\), \(\mathcal{F}(e^{-\pi bx^2})(t)=b^{-1/2}e^{-\pi t^2/b}\) on \(\mathbb R\), and \(\mathcal{F}(e^{-\pi bx^2+2\pi cx})(t)=b^{-1/2}e^{-\pi(t+ic)^2/b}\). On a space of dimension \(n\), \(\mathcal{F}(e^{-b\|v\|^2})(w)=(\pi/b)^{n/2}e^{-\pi^2\|w\|^2/b}\) (`Analysis/SpecialFunctions/Gaussian/FourierTransform.lean`).

**Convolution.** If \(f_1,f_2\) are integrable and \(B\) is a continuous bilinear map on complete codomains, then \(\mathcal{F}(f_1\star_Bf_2)=B(\mathcal{F}f_1,\mathcal{F}f_2)\) (`Real.fourier_bilin_convolution_eq`, with scalar and algebra specializations). Convolution of Schwartz functions is defined through the transform and agrees with the classical convolution (`Analysis/Fourier/Convolution.lean`). For a family of normalized smooth bumps with shrinking support, convolutions converge at every continuity point of a continuous function and almost everywhere for a locally integrable function (`ContDiffBump.convolution_tendsto_right_of_continuous`, `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`, `Analysis/Calculus/BumpFunction/Convolution.lean`).

**Poisson summation.** For continuous \(f:\mathbb R\to\mathbb C\) with \(\sum_n\mathcal{F}f(n)\) convergent and \(\sum_n\|f(\cdot+n)\|_K\) convergent on compacts, \(\sum_nf(x+n)=\sum_n\mathcal{F}f(n)e^{2\pi inx}\) (`Real.tsum_eq_tsum_fourier`). This holds in particular under decay \(|x|^{-b}\), \(b>1\), of \(f\) and \(\mathcal{F}f\), and for every Schwartz function (`SchwartzMap.tsum_eq_tsum_fourier`) (`Analysis/Fourier/PoissonSummation.lean`). The Jacobi theta transformation follows (`Analysis/SpecialFunctions/Gaussian/PoissonSummation.lean`). Poisson summation on \(\mathbb R^d\), \(d\geq2\), and for Dirac combs, is not stated.

### TauCeti

For essentially bounded symbols \(m\), the \(L^2\) Fourier multiplier \(T_mf=\mathcal{F}^{-1}(m\,\mathcal{F}f)\) is defined, with \(\|T_m\|\leq\|m\|_\infty\) (`MeasureTheory.Lp.fourierMultiplierCLM`). Composition multiplies symbols, the adjoint has the conjugate symbol, and the multiplier agrees with Mathlib's Schwartz multipliers ([\(L^2\) multipliers](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/L2Multiplier.lean)). The converse, that every translation-invariant bounded operator on \(L^2\) is such a multiplier, and the norm identity are not proved.

Convolution with an integrable kernel is a bounded operator on \(L^p\), \(1\leq p<\infty\), with \(\|k\star f\|_p\leq\|k\|_1\|f\|_p\) (`TauCeti.norm_convolutionLp_le`) ([convolution on \(L^p\)](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Function/Lp/Convolution.lean)). Young's inequality for integral kernels, \(L^p\to L^q\) with general exponents, is recorded in Section 25 ([Schur test](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/SchurTest.lean)); the convolution form with general exponents is not stated separately.

Smooth normalized approximate identities converge strongly to the identity on \(L^p\), \(1\leq p<\infty\), for Banach-valued functions on any additive Haar space ([approximate identities](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Function/Lp/ApproximateIdentity.lean)). General integrable kernels \(\phi\) with \(\int\phi=1\) are not treated.

On \(\mathbb R\), \(\mathcal{F}(e^{-a|x|})(\xi)=2a/(a^2+(2\pi\xi)^2)\), the transform behind the Poisson kernel ([two-sided exponential](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/ExpNegAbs.lean)). Continuity, decay and integrability of transforms of smooth compactly supported functions are packaged separately ([continuity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/Continuous.lean), [decay](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/Decay.lean), [integrability](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/Integrable.lean)). The Hermite functions form a Hilbert basis of \(L^2(\mathbb R)\) of Fourier eigenfunctions ([Fourier–Hermite basis](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Fourier/HilbertBasis.lean)).

The Riesz–Thorin theorem of Section 26 is the interpolation ingredient of Hausdorff–Young, but the Hausdorff–Young inequality itself is not stated ([Riesz–Thorin](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/RieszThorin.lean)).

The Wiener–Ikehara Tauberian theorem is proved by Fourier analysis (`TauCeti.LSeries.wienerIkehara`). If \(a_n\geq0\), the Dirichlet series \(\sum a_nn^{-s}\) converges for \(\mathop{\mathrm{Re}}s>1\), and \(F(s)-\kappa/(s-1)\) extends continuously to \(\mathop{\mathrm{Re}}s\geq1\), then \(x^{-1}\sum_{n\leq x}a_n\to\kappa\) ([Wiener–Ikehara](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/NumberTheory/LSeries/WienerIkehara/SharpCutoff.lean), [Fourier core](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/NumberTheory/LSeries/WienerIkehara/Fourier.lean), [Riemann–Lebesgue on a vertical line](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/RiemannLebesgue.lean)). This is supporting material; it is not an entry of this synopsis.

**Synopsis entries.** Covered: 27.1–27.3 (Mathlib). Partly covered: 27.5 (translation, differentiation and linear isometries; not general linear changes of variables), 27.6 (the convolution theorem for integrable functions, and Young's inequality with an \(L^1\) kernel), 27.7 (smooth bumps: \(L^p\) convergence, convergence at continuity points, and almost-everywhere convergence), 27.9 (the Gaussian transform; the semigroup statements are absent), 27.10 (dimension one), 27.11 (\(L^\infty\) symbols give \(L^2\) multipliers of norm at most \(\|m\|_\infty\); not the converse). Not covered: 27.4, 27.12, 27.13.

## Fourier series, summation, and convergence

[Mathematical scope](SYNOPSIS27.md#fourier-series-summation-and-convergence).

### Mathlib

**The circle and the torus.** On \(\mathbb R/T\mathbb Z\), with Haar measure of total mass \(1\), the characters \(x\mapsto e^{2\pi inx/T}\) span a dense subalgebra of the continuous functions (Stone–Weierstrass), are dense in \(L^p\) for \(1\leq p<\infty\), and form a Hilbert basis of \(L^2\) indexed by \(\mathbb Z\) (`fourierBasis`). For \(f\in L^2\) the Fourier series converges to \(f\) in \(L^2\), and Parseval's identity holds, also for square-integrable functions on a bounded interval. If \(f\) is continuous and its coefficients are absolutely summable, the series converges uniformly. An integration-by-parts formula expresses the coefficients of a \(C^1\) function on an interval through those of its derivative (`fourierCoeffOn_of_hasDerivAt`) (`Analysis/Fourier/AddCircle.lean`). On the torus \((\mathbb R/\mathbb Z)^d\), the product characters form a Hilbert basis of \(L^2\) indexed by \(\mathbb Z^d\), with \(L^2\) convergence, Parseval and the absolutely summable case (`Analysis/Fourier/AddCircleMulti.lean`).

The phase functions \(v\mapsto e(L(v,w))\) are bounded continuous and separate points (`Analysis/Fourier/BoundedContinuousFunctionChar.lean`). On \(\mathbb Z/N\mathbb Z\) the discrete transform is a linear equivalence with \(\mathcal{F}\mathcal{F}\Phi(j)=N\Phi(-j)\), and primitive Dirichlet characters transform to Gauss-sum multiples of their inverses (`Analysis/Fourier/ZMod.lean`).

The Poisson integral formula for harmonic functions on disks is proved (`Analysis/Complex/Harmonic/Poisson.lean`). This is supporting material for Abel summation; Poisson means of Fourier series of \(L^p\) functions are not treated.

### TauCeti

Functions continuous on \([a,b]\) are determined there by their Fourier coefficients (`TauCeti.eqOn_Icc_of_fourierCoeffOn_eq`) ([coefficients on an interval](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/FourierCoeffOn.lean)). Square-integrable functions on \((a,b]\) with vanishing coefficients vanish almost everywhere, and the sine system is complete in \(L^2(a,b)\) ([sine series](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/SineSeries.lean)). Uniqueness for \(L^1\) functions and for measures is not stated.

For absolutely continuous functions on an interval, integration by parts identifies the coefficients of the almost-everywhere derivative, and Parseval gives the derivative energy as a weighted sum of coefficients ([absolutely continuous functions](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/AbsolutelyContinuous.lean)). On this basis TauCeti proves the sharp spectral gap on the circle and the sharp Wirtinger inequality \(\int\|f-\bar f\|^2\leq((b-a)/2\pi)^2\int\|f'\|^2\), with equality cases ([spectral gap](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/SpectralGap.lean), [Wirtinger](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/Wirtinger.lean)). It also proves the sharp area–energy inequality for closed plane curves ([area–energy](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/AreaEnergy.lean)). The continuous characters of the circle are exactly the Fourier monomials ([circle characters](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/AddCircle.lean)).

Herglotz's theorem, that positive-definite sequences are moment sequences of finite measures on the circle, is proved through Fejér means of measures ([Herglotz](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Bochner/Herglotz.lean)). Fejér summation of Fourier series of functions is not proved.

**Synopsis entries.** Covered: 27.15 (Mathlib). Partly covered: 27.16 (square-integrable and continuous functions), 27.19 (coefficients of derivatives for \(C^1\) and absolutely continuous functions, and uniform convergence under absolute summability). Not covered: 27.17, 27.18, 27.20–27.25.

## Maximal functions and fractional integration

[Mathematical scope](SYNOPSIS27.md#maximal-functions-and-fractional-integration).

### Mathlib

Lebesgue differentiation holds for every Vitali family (`VitaliFamily.ae_tendsto_average`, `MeasureTheory/Covering/Differentiation.lean`). In particular it holds for balls and a uniformly locally doubling measure, such as an additive Haar measure (`IsUnifLocDoublingMeasure.ae_tendsto_average`, `MeasureTheory/Covering/DensityTheorem.lean`). On finite-dimensional spaces the Besicovitch covering theorem supplies a Vitali family for every locally finite measure (`Besicovitch.vitaliFamily`).

### TauCeti

The centred Hardy–Littlewood maximal function over balls is defined on finite-dimensional real normed spaces with an additive Haar measure. It satisfies the weak \((1,1)\) bound \(t\,\mu\{Mf>t\}\leq4^n\|f\|_1\) and the strong \((p,p)\) bound for \(1<p<\infty\) (`TauCeti.eLpNorm_maximalFunction_le`), and it is bounded on \(L^\infty\) ([maximal inequalities](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/MaximalFunction.lean)). Cubes and balls give comparable maximal functions, so this is the synopsis statement up to constants. A \(W^{1,p}\) function agrees almost everywhere with its precise representative, the limit of its ball averages (Section 26).

The Calderón–Zygmund decomposition is proved on \(\mathbb R^n\) with dyadic cubes. For integrable \(f\) and \(t>0\), \(f=g+\sum_Qb_Q\) over disjoint maximal dyadic cubes with \(t<⨍_Q\|f\|\leq2^nt\) and \(t|\bigcup Q|\leq\int_{\bigcup Q}\|f\|\). Here \(\|g\|\leq2^nt\) almost everywhere and \(\|g\|_1\leq\|f\|_1\), and each \(b_Q\) is supported on \(Q\), has mean zero and satisfies \(\|b_Q\|_1\leq2\int_Q\|f\|\) ([decomposition](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/CalderonZygmund/Decomposition.lean)).

Riesz potentials are bounded from \(L^p\) to \(L^q\) on sets of finite measure (Section 26, [Riesz potentials](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/RieszPotential.lean)). That is supporting material; the Hardy–Littlewood–Sobolev theorem on \(\mathbb R^d\) is not proved. The Poisson integrals of the ball and the half-space have Poisson kernels of mass one, and they solve the Dirichlet problem ([ball](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/PoissonIntegral/Ball.lean), [half-space](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/PoissonIntegral/HalfSpace.lean)). Nontangential convergence for \(L^p\) data is not proved.

**Synopsis entries.** Covered: 27.26 (TauCeti), 27.27 (Mathlib), 27.28 (TauCeti). Not covered: 27.29–27.32.

## Singular integrals and Fourier multipliers

[Mathematical scope](SYNOPSIS27.md#singular-integrals-and-fourier-multipliers).

### TauCeti

The Calderón–Zygmund theorem is proved for operators bounded on \(L^2(\mathbb R^n)\) whose kernel satisfies Hörmander's condition. Such an operator has weak type \((1,1)\) (`ContinuousLinearMap.mul_volume_lt_enorm_le_of_hormander`). It has strong type \((p,p)\) for \(1<p<2\) (`ContinuousLinearMap.eLpNorm_le_of_hormander`), and for \(2<p<\infty\) when the adjoint satisfies the condition (`ContinuousLinearMap.eLpNorm_le_of_hormander_adjoint`), with explicit constants. The estimates are proved on \(L^2\cap L^p\) ([weak type](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/CalderonZygmund/WeakType.lean), [strong type](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/CalderonZygmund/StrongType.lean)). The standard smoothness estimate \(\|K(x,y)-K(x,y')\|\leq C|y-y'|^\delta/|x-y'|^{n+\delta}\) implies Hörmander's condition, so standard Calderón–Zygmund operators are covered ([standard kernels](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/CalderonZygmund/StandardKernel.lean)).

The Mihlin–Hörmander theorem is proved on a real inner product space of dimension \(n\), with complex Hilbert-space values (`TauCeti.exists_eLpNorm_fourierMultiplierCLM_le_of_norm_iteratedFDeriv_le`). If \(m\) is smooth away from \(0\) and \(\|D^km(\xi)\|\leq A\|\xi\|^{-k}\) for \(k\leq N\) with \(2N>n\), then \(T_m\) is bounded on \(L^p\), \(1<p<\infty\), with norm at most \(CA\) ([Mihlin–Hörmander](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/MihlinHormander.lean)). The proof uses smooth dyadic Littlewood–Paley cutoffs and the corresponding pieces of Mihlin symbols ([cutoffs](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/BumpFunction/LittlewoodPaley.lean), [pieces](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Distribution/SchwartzSpace/LittlewoodPaley.lean)). The theorem covers the symbol \(-i\mathop{\mathrm{sgn}}\xi\) of the Hilbert transform and the symbols \(-i\xi_j/|\xi|\) of the Riesz transforms, as \(L^p\) multipliers. The principal-value integral form of these operators, their weak type \((1,1)\) bounds, and the identities \(H^2=-I\) and \(\sum_jR_j^2=-I\) are not stated. The operators \(\partial_v\partial_w\Delta^{-1}\) are treated as \(L^2\) multipliers ([Hessian multiplier](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/HessianMultiplier.lean)).

**Synopsis entries.** Covered: 27.33, 27.38 (TauCeti). Partly covered: 27.35, 27.36 (\(L^p\) boundedness of the multipliers, \(1<p<\infty\)). Not covered: 27.34, 27.37, 27.39–27.43, 27.69.

## Weights and endpoint spaces

[Mathematical scope](SYNOPSIS27.md#weights-and-endpoint-spaces).

### TauCeti

The John–Nirenberg inequality \(|\{x\in Q_0:\|f-f_{Q_0}\|>s\}|\leq2e^{-cs/M}|Q_0|\) is proved for mean oscillation at most \(M\), on dyadic cubes and on all cubes, with the resulting exponential integrability (`TauCeti.volume_lt_norm_sub_setAverage_le`, `TauCeti.setLIntegral_exp_mul_norm_sub_setAverage_le`) ([John–Nirenberg](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/JohnNirenberg.lean)). The equivalence of the mean-oscillation seminorms for different exponents is not stated.

Under Hörmander's condition in the first variable, an \(L^2\)-bounded singular integral maps \(L^\infty\cap L^2\) into BMO, with \(⨍_Q\|Tf-(Tf)_Q\|\leq2(\sqrt D\|T\|+B)\|f\|_\infty\) (`ContinuousLinearMap.setLAverage_enorm_sub_setAverage_le_of_hormander`) ([BMO bound](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/CalderonZygmund/BoundedMeanOscillation.lean)). No BMO space, real Hardy space \(H^1(\mathbb R^d)\), \(A_p\) weight or sharp maximal function is defined.

**Synopsis entries.** Covered: 27.49 (TauCeti). Partly covered: 27.50 (the \(L^\infty\to\mathrm{BMO}\) bound). Not covered: 27.44–27.48, 27.51–27.55.

## Frequency decompositions and oscillation

[Mathematical scope](SYNOPSIS27.md#frequency-decompositions-and-oscillation).

### TauCeti

The smooth dyadic Littlewood–Paley cutoffs \(\psi_j(\xi)=\varphi(2^{-j}\xi)-\varphi(2^{1-j}\xi)\) form a partition of unity of \(E\setminus\{0\}\) with \(\|D^k\psi_j\|\leq B2^{-jk}\) ([Littlewood–Paley cutoffs](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/BumpFunction/LittlewoodPaley.lean)). This is supporting material only. No square-function theorem, Bernstein inequality, bilinear multiplier theorem, oscillatory-integral estimate or restriction theorem is proved in either library.

**Synopsis entries.** Not covered: 27.56–27.61, 27.63, 27.65–27.68.

## Geometric maximal functions, restriction, and decoupling

[Mathematical scope](SYNOPSIS27.md#geometric-maximal-functions-restriction-and-decoupling).

### Mathlib

Neither library treats Kakeya sets, Kakeya or spherical maximal functions, restriction, Bochner–Riesz means or decoupling. Mathlib's Besicovitch covering theorem (`MeasureTheory/Covering/Besicovitch.lean`) is a covering lemma; it is unrelated to Besicovitch sets.

**Synopsis entries.** Not covered: 27.70–27.75.
