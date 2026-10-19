# Structure 41: Classical function theory — entire and meromorphic functions, value distribution

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS41.md); [bibliographical scope](CKMA-bib.md#ckma-41); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; the **Synopsis entries** line at the end of each section states which numbered results are covered.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.Complex.JensenFormula`, `Mathlib.Analysis.Complex.CanonicalDecomposition`, `Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic`, `Mathlib.Analysis.Complex.ValueDistribution.Proximity.IntegralPresentation`, `Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic`, `Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Asymptotic`, `Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Truncated`, `Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction`, `Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem`, `Mathlib.Analysis.Complex.ValueDistribution.Cartan`, `Mathlib.Analysis.Complex.ValueDistribution.SecondMainTheorem`, `Mathlib.Analysis.Complex.Liouville`, `Mathlib.Analysis.Complex.PhragmenLindelof`, `Mathlib.Analysis.Complex.BorelCaratheodory`, `Mathlib.Analysis.Complex.Polynomial.GaussLucas`, `Mathlib.Analysis.Calculus.LogDerivUniformlyOn`, `Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd`, `Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent`.

**Namespaces.** `ValueDistribution`, with nested `Cartan` for the kernel used in the integral form of the proximity function. The counting function of a locally finite divisor, before it is specialized to a meromorphic function, is `Function.locallyFinsuppWithin`. Jensen’s formula is `MeromorphicOn` and `AnalyticOnNhd`. The separation lemma sits in `Real` but is stated for a finite subset of any normed field. Canonical factors are `Complex`. Liouville’s theorem with polynomial growth is `Differentiable`; the Phragmén–Lindelöf principles are `PhragmenLindelof`; the Gauss–Lucas theorem is `Polynomial`. TauCeti declarations are in `TauCeti`.

## Growth, zeros, and canonical products

[Mathematical scope](SYNOPSIS41.md#growth-zeros-and-canonical-products).

### Mathlib

**Polynomial growth.** An entire function \(f:\mathbb{C}\to\mathbb{C}\) is \(O(|z|^n)\) at infinity if and only if it is a polynomial of degree at most \(n\) (`Differentiable.isBigO_pow_iff_exists_eq_polynomial_eval`, `Analysis/Complex/Liouville.lean`). The growth order \(\rho\) and type \(\tau\) of an entire function are not defined; the order that is defined is the order of a zero or a pole. The convexity of \(\log M(r)\) in \(\log r\) is not stated.

**Jensen’s formula.** If \(f:\mathbb{C}\to\mathbb{C}\) is meromorphic on the closed disc of center \(c\) and radius \(|R|\), and \(R\neq 0\), the circle average of \(\log\|f\|\) equals the logarithm of the norm of the trailing coefficient of \(f\) at \(c\), plus a correction from the zeros and poles. With \(D\) the divisor of \(f\) on that closed disc,
\[
\operatorname{circleAverage}(\log\|f\|,c,R)
= \sum_u D(u)\log\bigl(R\,\|c-u\|^{-1}\bigr) + D(c)\log R + \log\|\text{trailing coefficient of }f\text{ at }c\|.
\]
The sum is finite. The term \(D(c)\log R\) compensates for the convention that \(\log(R\,\|c-u\|^{-1})\) is interpreted as zero when \(u=c\). If the order is infinite at even one point of the disc, \(f\) vanishes off a discrete set, the divisor is zero, and both sides are the value attached to the zero function (`MeromorphicOn.circleAverage_log_norm`, `Analysis/Complex/JensenFormula.lean`).

If \(f\) is analytic on the closed disc and \(f(c)\neq 0\), the order at the center vanishes, the trailing coefficient is \(f(c)\), and the formula reduces to the circle average of \(\log\|f\|\) equal to \(\log\|f(c)\|\) plus the sum of \(D(u)\log(R/\|c-u\|)\) over the zeros (`AnalyticOnNhd.circleAverage_log_norm`).

Jensen’s inequality bounds the number of zeros. If \(0<|r|<|R|\), \(f\) is analytic on the closed disc of radius \(|R|\), \(f(c)\neq 0\), and \(\|f\|\le M\) on the circle of radius \(|R|\) with \(M\ge 1\), then the sum of the divisor of \(f\) on the closed disc of radius \(|r|\) is at most \(\log(M/\|f(c)\|)/\log(|R|/|r|)\) (`AnalyticOnNhd.sum_divisor_le`).

**Products and logarithmic derivatives.** If a product \(\prod_i f_i\) of holomorphic functions converges locally uniformly on an open set, its logarithmic derivative at a point where no factor and not the product vanish is the sum of the logarithmic derivatives of the factors, provided that sum converges (`logDeriv_tprod_eq_tsum`, `Analysis/Calculus/LogDerivUniformlyOn.lean`). This is the general mechanism behind logarithmic differentiation of canonical products; the Weierstrass primary factors \(E_p\) and canonical products themselves are not defined.

**Explicit instances.** Explicit infinite products and partial-fraction expansions are proved for particular functions: Euler’s product for \(\sin\pi z\) (`Complex.tendsto_euler_sin_prod`, `Analysis/SpecialFunctions/Trigonometric/EulerSineProd.lean`), the Euler–Gauss limit formula for \(\Gamma\) (`Complex.GammaSeq_tendsto_Gamma`, `Analysis/SpecialFunctions/Gamma/Beta.lean`; see Section 49), and the partial-fraction expansion of \(\pi\cot\pi z\) (`cot_series_rep` in `Analysis/SpecialFunctions/Trigonometric/Cotangent.lean`). These are instances of the Weierstrass and Mittag-Leffler theorems, not the general theorems.

**Supporting growth tools.** The Borel–Carathéodory inequality (`Complex.borelCaratheodory`, `Analysis/Complex/BorelCaratheodory.lean`), the Phragmén–Lindelöf principles (next section), and Hadamard’s three-lines theorem (`Analysis/Complex/Hadamard.lean`) are the standard inputs to Hadamard factorization; they are recorded in Section 40.

### TauCeti

The argument-principle file identifies the principal part of \(f'/f\) at a zero or pole of order \(n\) as \(n/(z-z_0)\), so multiplicities are residues of the logarithmic derivative (`TauCeti.Contour.logDeriv_eventuallyEq_principalPart`, [argument principle](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Contour/Argument/Principle.lean)); local Laurent data are in [MeromorphicLaurent](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Contour/MeromorphicLaurent.lean). The partial-fraction expansion of \((\pi/2)\tanh(\pi y/2)\) over the odd integers is derived from the cotangent expansion ([tanh series](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/Trigonometric/TanhSeries.lean)). The monodromy theorem, giving global branches from pathwise analytic continuation on simply connected domains ([global branches](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/GlobalBranch.lean)), is Section 40 material. None of these is a general factorization theorem.

**Synopsis entries.** Covered: 41.5 (Mathlib). Partly covered: 41.1 (polynomial-growth characterization only; transcendental growth and log-convexity of \(M\) absent), 41.15 (logarithmic derivative of a locally uniformly convergent product, and multiplicities as residues of \(f'/f\); canonical products not defined). Not covered: 41.2–41.4, 41.6–41.14, 41.16.

## Angular growth and exponential type

[Mathematical scope](SYNOPSIS41.md#angular-growth-and-exponential-type).

### Mathlib

The Phragmén–Lindelöf principle is proved in horizontal and vertical strips, in each of the four coordinate quadrants under a growth bound \(A\exp(B|z|^c)\) with \(c<2\), and in the right half-plane, including uniqueness versions under superexponential decay on the real axis (`PhragmenLindelof.quadrant_I`, `PhragmenLindelof.horizontal_strip`, `PhragmenLindelof.right_half_plane_of_bounded_on_real`, `PhragmenLindelof.eq_zero_on_right_half_plane_of_superexponential_decay`, `Analysis/Complex/PhragmenLindelof.lean`). The quadrant case is the sector of opening \(\pi/2\) with the sharp exponent \(c<\pi/\alpha=2\); sectors of general opening are not treated. Indicators, exponential type, the Paley–Wiener space and the Cartwright class are not defined.

**Synopsis entries.** Partly covered: 41.17 (strips, quadrants with the sharp exponent, and the right half-plane; general sectors absent). Not covered: 41.18–41.21, 41.23, 41.25–41.29, 41.56.

## Quasi-analyticity and completeness of exponentials

[Mathematical scope](SYNOPSIS41.md#quasi-analyticity-and-completeness-of-exponentials).

Neither library defines Denjoy–Carleman classes or treats completeness of exponential systems.

**Synopsis entries.** Not covered: 41.70–41.72.

## Real zeros, Hermite–Biehler functions, and de Branges spaces

[Mathematical scope](SYNOPSIS41.md#real-zeros-hermitebiehler-functions-and-de-branges-spaces).

### Mathlib

The Gauss–Lucas theorem is proved: for a complex polynomial \(P\) of positive degree, the roots of \(P'\) lie in the convex hull of the roots of \(P\) (`Polynomial.rootSet_derivative_subset_convexHull_rootSet`, `Analysis/Complex/Polynomial/GaussLucas.lean`). The Grace–Walsh–Szegő coincidence theorem, the Laguerre–Pólya class, Hermite–Biehler functions and de Branges spaces are not present in either library.

**Synopsis entries.** Partly covered: 41.73 (Gauss–Lucas only). Not covered: 41.74–41.77.

## Nevanlinna characteristic and the first main theorem

[Mathematical scope](SYNOPSIS41.md#nevanlinna-characteristic-and-the-first-main-theorem).

### Mathlib

**The three Nevanlinna functions.** The logarithmic counting function is defined first for an integer-valued function of locally finite support on a proper normed space, and then for a meromorphic function. For a divisor \(D\) and a radius \(r\), it is the sum of \(D(z)\log(r/\|z\|)\) over the closed disc of radius \(|r|\), with the value at the origin separated so that the formula stays consistent with Jensen’s formula. For a meromorphic \(f\) and a finite value \(a\), the counting function of \(f\) at \(a\) is this construction applied to the positive part of the divisor of \(f-a\), so it counts zeros of \(f-a\) with multiplicity. At the value infinity it is applied to the negative part of the divisor of \(f\), so it counts poles. It is even in the radius, nonnegative for radii at least one, and monotone. Subtracting a constant does not change the counting function at infinity. For radii at least one, the counting function of a product at zero or at infinity is at most the sum of the counting functions of the factors, for factors not locally identically zero; the counting functions of \(f^n\) are \(n\) times those of \(f\) (`Analysis/Complex/ValueDistribution/LogCounting/Basic.lean`). The divisor counting function is related to Jensen’s formula as a circle average minus a constant (`Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const`).

Asymptotically, a nonnegative locally finite divisor has finite support if and only if its counting function is \(O(\log r)\) as \(r\to\infty\). A meromorphic function on a nontrivially normed proper field has only removable singularities, in the sense that its normal-form representative is analytic on the whole field, if and only if the counting function of its poles is \(O(1)\). It has finitely many poles if and only if that counting function is \(O(\log r)\) (`ValueDistribution.logCounting_isBigO_one_iff_analyticOnNhd`, `ValueDistribution.logCounting_isBigO_log_iff_finite_support`, `Analysis/Complex/ValueDistribution/LogCounting/Asymptotic.lean`).

The truncated logarithmic counting function counts each zero of \(f-a\), or each pole when \(a=\infty\), once regardless of multiplicity; it is the counting function of the divisor truncated at one. It is bounded by the ordinary counting function and is nonnegative for radii at least one, it is monotone, and it depends on \(f\) only off a discrete set (`Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean`).

The proximity function of a meromorphic \(f:\mathbb{C}\to E\), with \(E\) a complex normed space, measures how close \(f\) comes to a value on the circle of radius \(r\). At infinity it is the circle average of \(\log^+\|f\|\). At a finite value \(a\) it is the circle average of \(\log^+\|f-a\|^{-1}\). Large values mean a close approach. It depends on \(f\) only through its values off a discrete subset of the circle (`Analysis/Complex/ValueDistribution/Proximity/Basic.lean`). For scalar \(f\), the proximity to infinity is also an iterated circle average: the average over the unit circle, in the variable \(a\), of the circle average of \(\log\|f-a\|\) on \(|z|=R\) (`ValueDistribution.circleAverage_circleAverage_eq_proximity_top`, `Analysis/Complex/ValueDistribution/Proximity/IntegralPresentation.lean`).

The characteristic function \(T(r,f,a)\), also called the Nevanlinna height, is defined as the sum of the proximity function and the logarithmic counting function, at any value \(a\) in the codomain extended by a point at infinity (`ValueDistribution.characteristic`, `Analysis/Complex/ValueDistribution/CharacteristicFunction.lean`). It is even in the radius and nonnegative for radii at least one. The module lists the characterization of rational functions by the growth of the characteristic as a TODO.

**Characteristic calculus.** For radii at least one: the characteristic at infinity of a finite sum of meromorphic functions is at most the sum of the characteristics plus the logarithm of the number of terms, so \(T(r,f+g)\le T(r,f)+T(r,g)+\log 2\) (`characteristic_add_top_le`, `characteristic_sum_top_le`); for complex-valued \(f,g\) whose meromorphic order is nowhere infinite, \(T(r,fg,\infty)\le T(r,f,\infty)+T(r,g,\infty)\) and the same at the value \(0\) (`characteristic_mul_top_le`, `characteristic_mul_zero_le`). Moreover \(T(r,f^n,\infty)=n\,T(r,f,\infty)\) and \(T(r,f^n,0)=n\,T(r,f,0)\) exactly (`characteristic_pow_top`, `characteristic_pow_zero`), and multiplication by a nonzero constant changes \(T(r,f,\infty)\) by \(O(1)\) (`isBigO_characteristic_sub_characteristic_const_mul`).

**Cartan’s formula.** For \(f:\mathbb{C}\to\mathbb{C}\) meromorphic on the plane and \(R\neq 0\), Cartan’s formula writes the characteristic at infinity as two circle averages over the unit circle:
\[
T(R,f,\infty)
= \operatorname{circleAverage}\bigl(a\mapsto N(R,f,a)\bigr)
+ \operatorname{circleAverage}\bigl(a\mapsto \log\|\text{trailing coefficient of }f-a\text{ at }0\|\bigr).
\]
Both integrands are circle-integrable. Away from radius zero, the second average is a constant, so the characteristic differs from the average of the counting function by a constant. As a consequence the characteristic at infinity is monotone on \((0,\infty)\) (`characteristic_top_eq_circleAverage_add_circleAverage`, `characteristic_monotoneOn`, `Analysis/Complex/ValueDistribution/Cartan.lean`). The file notes that this monotonicity is not obvious from the definition, because the proximity function need not be monotone.

**Canonical decomposition on a disc.** The canonical factor of radius \(R\) at a point \(w\) is \((R^2-\overline{w}\,z)/(R(z-w))\) (`Complex.canonicalFactor`). It is meromorphic and, for \(|w|<R\), has a single pole at \(w\), no zeros, and modulus one on the circle of radius \(R\). A meromorphic function on a closed disc, not locally identically zero, equals off a discrete set a product of integer powers of canonical factors times a function without zeros or poles in the open disc (`MeromorphicOn.exists_canonicalDecomp`); an extended version also accounts for zeros and poles on the boundary circle and expresses \(\log\|g(w)\|\) for the zero-free factor through the divisor (`MeromorphicOn.exists_ecanonicalDecomp`, `Complex.ECanonicalDecomp.log_norm_eq`, `Analysis/Complex/CanonicalDecomposition.lean`). The file calls the finite product a finite Blaschke product. This is the decomposition step of the Poisson–Jensen formula; the formula itself, at an arbitrary interior point, is not stated. Jensen’s formula (previous section) is its value at the center.

**The first main theorem.** The equality \(T=m+N\) is a definition. The theorem that is proved is the invariance of the characteristic at infinity, in a quantitative form (`Analysis/Complex/ValueDistribution/FirstMainTheorem.lean`). If \(f:\mathbb{C}\to\mathbb{C}\) is meromorphic on the plane, then for every real radius \(R\)
\[
\bigl|T(R,f,\infty)-T(R,f^{-1},\infty)\bigr|
\le \max\bigl\{\bigl|\log\|f(0)\|\bigr|,\,\bigl|\log\|\text{trailing coefficient of }f\text{ at }0\|\bigr|\bigr\}
\]
(`characteristic_sub_characteristic_inv_le`). For \(R\neq 0\) the difference equals the logarithm of the norm of the trailing coefficient at the origin, and at \(R=0\) it equals \(\log\|f(0)\|\). In particular the difference is \(O(1)\) as \(R\to\infty\) (`isBigO_characteristic_sub_characteristic_inv`).

If \(f\) is meromorphic on the plane with values in a complex normed space, and \(a\) is a point of that space, then for every radius
\[
\bigl|T(R,f,\infty)-T(R,f-a,\infty)\bigr|\le \log^+\|a\|+\log 2
\]
(`abs_characteristic_sub_characteristic_shift_le`). The counting functions at infinity agree, because subtracting a constant does not move the poles, and the inequality is an estimate of the proximity functions.

The definitional identities \(m(r,f,a)=m(r,f-a,0)\), \(N(r,f,a)=N(r,f-a,0)\), \(m(r,g^{-1},\infty)=m(r,g,0)\) and \(N(r,g^{-1},\infty)=N(r,g,0)\) are stated (`proximity_coe_eq_proximity_sub_const_zero`, `logCounting_coe_eq_logCounting_sub_const_zero`, `proximity_inv`, `logCounting_inv`). Combined with the two invariance theorems they give \(T(r,f,a)=T(r,f,\infty)+O(1)\) for every finite \(a\), which is the classical first main theorem. Postcomposition with any Möbius transformation \(w\mapsto(aw+b)/(cw+d)\), \(ad-bc\neq0\), changes \(T(R,f,\infty)\) by \(O(1)\) as \(R\to\infty\) (`isBigO_characteristic_sub_characteristic_moebius`).

### TauCeti

The Herglotz representation theorem characterizes holomorphic disc functions with nonnegative real part as transforms of finite positive circle measures, up to an imaginary constant (`TauCeti.differentiableOn_and_re_nonneg_iff_exists_eq_herglotzTransform_add`, [representation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Herglotz.lean)). Through the Cayley transform it gives the Pick (Nevanlinna) representation of holomorphic functions on the upper half-plane with nonnegative imaginary part, with the atom of the circle measure at \(1\) producing the linear term ([Pick functions](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Pick/Basic.lean), [Nevanlinna transport](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Pick/Nevanlinna.lean)). This concerns functions of positive imaginary part, not Nevanlinna’s value-distribution theory, and is recorded here only to prevent confusion of the names.

**Synopsis entries.** Covered: 41.31, 41.32 (Mathlib). Partly covered: 41.30 (Jensen’s formula at the center and the finite canonical decomposition on a disc; the Poisson–Jensen formula at an arbitrary interior point is not stated), 41.33 (the cases \(R(w)=w^n\), exactly, and Möbius maps, up to \(O(1)\); general rational \(R\) absent). Not covered: 41.34–41.37.

## The second main theorem, defects, and uniqueness

[Mathematical scope](SYNOPSIS41.md#the-second-main-theorem-defects-and-uniqueness).

### Mathlib

The module `Analysis/Complex/ValueDistribution/SecondMainTheorem.lean` states that it will in the future establish the second main theorem and at present collects material for its proof; it points to an external formalization (`https://github.com/kebekus/ProjectVD`) that is not part of this audit. What the file contains is a separation lemma on a normed field. For a finite set \(s\), there is a constant \(C\), depending only on \(s\), such that for every point \(w\)
\[
\sum_{a\in s}\log^+\|w-a\|^{-1}
\le \log^+\Bigl\|\sum_{a\in s}(w-a)^{-1}\Bigr\|+C
\]
(`Real.exists_sum_posLog_inv_norm_sub_le`). Closeness to some point of \(s\), measured by the sum of truncated logarithms, is detected by the single function \(\log^+\bigl\|\sum (w-a)^{-1}\bigr\|\). The truncated counting function of the previous section is the other prepared ingredient. Logarithmic differentiation of finite products of integer powers of meromorphic functions, off a discrete set, is in `Analysis/Meromorphic/LogDeriv.lean` (`Meromorphic.logDeriv_finprod_zpow_eventuallyEq`), described there as the shape used in the differentiated Poisson–Jensen formula; the logarithmic derivative lemma itself is not proved.

**Synopsis entries.** Not covered: 41.38–41.50.

## Normality, rescaling, and uniqueness sets

[Mathematical scope](SYNOPSIS41.md#normality-rescaling-and-uniqueness-sets).

### TauCeti

Normal families appear only for holomorphic maps with the locally uniform (not spherical) topology. Locally bounded families of holomorphic functions are equicontinuous, as are their derivatives (`TauCeti.IsLocallyBoundedOn.equicontinuousOn`, [normal families](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/NormalFamilies.lean)), and Montel’s selection theorem gives a locally uniformly convergent subsequence with holomorphic limit (`TauCeti.montel`, [Montel](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/Montel/Basic.lean)); this is Section 40 material and supporting here. Hurwitz’s theorem in counting form is proved for holomorphic functions: on a disc whose boundary circle avoids the zeros of the locally uniform limit, the approximants eventually have the same number of zeros with multiplicity, and limits of zero-free or injective functions are zero-free or injective unless constant (`TauCeti.eventually_finsum_analyticOrderNatAt_ball_eq`, `TauCeti.hurwitz`, [Hurwitz](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/Hurwitz.lean), [zero count](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/ZeroCount.lean)). The spherical derivative, normality of meromorphic families and Zalcman rescaling are absent from both libraries.

**Synopsis entries.** Partly covered: 41.54 (holomorphic functions under locally uniform convergence, zeros only; poles and spherical convergence not treated). Not covered: 41.51–41.53, 41.55, 41.57, 41.58.

## Growth methods for complex differential equations

[Mathematical scope](SYNOPSIS41.md#growth-methods-for-complex-differential-equations).

Neither library contains the maximum term, central index, Wiman–Valiron theory, Clunie or Malmquist theorems, global existence for linear equations with entire coefficients, or the Schwarzian derivative (TauCeti has only the pre-Schwarzian \(f''/f'\), Section 43).

**Synopsis entries.** Not covered: 41.59–41.67, 41.69.
