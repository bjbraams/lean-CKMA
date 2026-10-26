# Structure 50: Asymptotic analysis, resurgence, and perturbation

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS50.md); [bibliographical scope](CKMA-bib.md#ckma-50); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.Asymptotics.Defs`, `Mathlib.Analysis.Asymptotics.AsymptoticEquivalent`, `Mathlib.Analysis.Asymptotics.Theta`, `Mathlib.Analysis.Asymptotics.ExpGrowth`, `Mathlib.Analysis.Asymptotics.LinearGrowth`, `Mathlib.Analysis.Asymptotics.SuperpolynomialDecay`, `Mathlib.Analysis.Asymptotics.SpecificAsymptotics`, `Mathlib.Analysis.Calculus.Taylor`, `Mathlib.Analysis.Analytic.Inverse`, `Mathlib.Analysis.SpecialFunctions.SmoothTransition`, `Mathlib.MeasureTheory.Integral.Gamma`, `Mathlib.MeasureTheory.Integral.CircleIntegral`, `Mathlib.Analysis.Fourier.RiemannLebesgueLemma`, `Mathlib.NumberTheory.AbelSummation`, `Mathlib.NumberTheory.ZetaValues`, `Mathlib.Tactic.ComputeAsymptotics`. There is no aggregate module for this subject.

**Namespaces.** `Asymptotics` contains the Landau relations, with the notation \(f=O[l]g\), \(f=\Theta[l]g\), \(f=o[l]g\), and \(f\sim[l]g\); `ExpGrowth` and `LinearGrowth` the growth rates of sequences; `FormalMultilinearSeries` the formal inverse of a power series; and `Tactic.ComputeAsymptotics` the multiseries support lemmas. There is no namespace for resurgence. The TauCeti declarations are in `TauCeti` and `ODE` and are identified by name below.

## Expansions, realization, and nonuniqueness

[Mathematical scope](SYNOPSIS50.md#expansions-realization-and-nonuniqueness).

### Mathlib

**Little-o, big-O, and equivalence.**

The relations are indexed by a filter \(l\) on the common domain. They are not restricted to \(x\to\infty\). For normed codomains, \(f\) is big-O of \(g\) along \(l\) with constant \(c\), written as the relation `IsBigOWith`, when \(\|f(x)\|\leq c\,\|g(x)\|\) holds for all \(x\) in some set belonging to \(l\). Then \(f=O[l]g\) means that some real constant \(c\) works. One writes \(f=\Theta[l]g\) when each of \(f\) and \(g\) is big-O of the other along \(l\), and \(f=o[l]g\) when every positive constant works (`Analysis/Asymptotics/Defs.lean`, `Analysis/Asymptotics/Theta.lean`).

Asymptotic equivalence \(f\sim[l]g\) means \((f-g)=o[l]g\) (`Analysis/Asymptotics/AsymptoticEquivalent.lean`). It is an equivalence relation. When the codomain is a normed field and \(g\) is eventually nonvanishing, equivalence is the same as \(f/g\to 1\) along \(l\). More generally, over a normed field, \(f\sim[l]g\) if and only if \(f=\varphi g\) eventually, for some \(\varphi\to 1\) along \(l\).

The same relations specialise to the usual filters: a neighbourhood of a point, a punctured neighbourhood, `atTop`, and the filter of cobounded sets. Concrete comparisons are collected separately. A function bounded in a punctured neighbourhood of \(a\) is little-o of \((x-a)^{-1}\) there. On a normed ring, \(x\mapsto x^p\) is little-o of \(x\mapsto x^q\) along the cobounded filter whenever \(p<q\), and the same comparison holds at \(+\infty\) in a normed ordered field (`Analysis/Asymptotics/SpecificAsymptotics.lean`).

Linear growth of a sequence is the \(\liminf\) or \(\limsup\) of \(u_n/n\), developed mainly for extended-real sequences (`Analysis/Asymptotics/LinearGrowth.lean`), and exponential growth of a sequence \(u:\mathbb{N}\to[0,\infty]\) is the extended-real \(\liminf\) or \(\limsup\) of \((\log u_n)/n\) (`Analysis/Asymptotics/ExpGrowth.lean`). Superpolynomial decay of \(f\) relative to a parameter \(k\), along a filter \(l\), means that \(k^n f\to 0\) along \(l\) for every natural number \(n\). This is equivalent to \(f\) being little-o, and also big-O, of every integer power of \(k\) (`Analysis/Asymptotics/SuperpolynomialDecay.lean`). There is no notion of an asymptotic expansion with respect to an asymptotic scale.

**Taylor remainders.**

The calculus library proves Taylor approximation in little-o form (`taylor_isLittleO`) and Taylor’s theorem with Lagrange, Cauchy, and integral remainders. There are vector-valued remainder bounds as well (`Analysis/Calculus/Taylor.lean`). An integral remainder formula using iterated Fréchet derivatives also applies along segments in normed spaces (`Analysis/Calculus/TaylorIntegral.lean`). These are finite-order expansions with controlled remainders, the real-variable starting point for power-asymptotic expansions.

**Flat functions and analytic inversion.**

The function `expNegInvGlue`, equal to \(e^{-1/x}\) for \(x>0\) and to \(0\) for \(x\le0\), is \(C^\infty\) on \(\mathbb R\) (`expNegInvGlue.contDiff`), satisfies \(p(1/x)e^{-1/x}\to0\) as \(x\to0\) for every polynomial \(p\) (`expNegInvGlue.tendsto_polynomial_inv_mul_zero`), and is not analytic at \(0\) (`expNegInvGlue.not_analyticAt_zero`) (`Analysis/SpecialFunctions/SmoothTransition.lean`). This is the real-variable flat function; the sectorial complex statement is not formulated.

A formal multilinear series with invertible linear term has a formal left and right inverse, which coincide (`FormalMultilinearSeries.leftInv_eq_rightInv`), the inverse series has positive radius when the original one does, and the inverse of an analytic open partial homeomorphism with invertible derivative has the inverse series as its power series (`OpenPartialHomeomorph.hasFPowerSeriesAt_symm`, `Analysis/Analytic/Inverse.lean`). Composition of convergent power series is in `Analysis/Analytic/Composition.lean`. These are the convergent cases of composition and inversion; the divergent asymptotic versions are absent.

**Supporting material: the asymptotics procedure.**

`Mathlib.Tactic.ComputeAsymptotics` is a directory of support lemmas, not a resurgence theory. The lemmas reduce goals of the form “a limit along a one-sided or punctured neighbourhood”, and goals of big-O, little-o, and equivalence, to a limit along `atTop` (`Tactic/ComputeAsymptotics/Lemmas.lean`). The accompanying multiseries are lazy series of real monomials in a chosen well-formed basis of functions \(\mathbb{R}\to\mathbb{R}\) (`Multiseries/Basis.lean`), nested so that a series in \(b_1,\ldots,b_n\) is a series in \(b_1\) whose coefficients are series in the remaining basis. A coinductive predicate `Approximates` says that such a series approximates its attached function at \(+\infty\), after a trimming condition that isolates the leading monomial (`Tactic/ComputeAsymptotics/Multiseries/Defs.lean`, `Trimming.lean`). The order bound in that predicate is `Majorized`: \(f\) is majorized by \(b^e\) when \(f=o(b^{e'})\) at \(+\infty\) for every \(e'>e\) (`Multiseries/Majorized.lean`). Constant and monomial multiseries, including real powers of basis functions, are constructed and shown to approximate their functions in `Multiseries/Basic.lean` and `Multiseries/Monomial`, and a corecursion principle for lazy sequences supports products and power-series substitution (`Multiseries/Corecursion.lean`); approximation theorems for sums and products of multiseries are not in the library. No syntax declaration of a tactic named `compute_asymptotics` appears in the library; the file describes the procedure those lemmas serve.

**Synopsis entries.** Partly covered: 50.7 (the real flat function \(e^{-1/x}\), smooth with all derivatives zero at \(0\) and not analytic; not the sectorial statement), 50.8 (composition and inversion of convergent power series, with the analytic local inverse; not asymptotic expansions). Not covered: 50.1–50.6.

## Laplace, oscillatory, and uniform integral methods

[Mathematical scope](SYNOPSIS50.md#laplace-oscillatory-and-uniform-integral-methods).

### Mathlib

The model integral of entry 50.15 is evaluated for real parameters: for \(p>0\), \(q>-1\), \(b>0\), \(\int_0^\infty x^qe^{-bx^p}dx=b^{-(q+1)/p}p^{-1}\Gamma((q+1)/p)\) (`integral_rpow_mul_exp_neg_mul_rpow`, `MeasureTheory/Integral/Gamma.lean`), and for complex \(a\) with \(\mathop{\mathrm{Re}}a>0\) and \(r>0\), \(\int_0^\infty t^{a-1}e^{-rt}dt=r^{-a}\Gamma(a)\) (`Complex.integral_cpow_mul_exp_neg_mul_Ioi`, `Analysis/SpecialFunctions/Gamma/Basic.lean`). The Gaussian integrals of Section 49 are the corresponding evaluations at a nondegenerate quadratic phase.

The Cauchy coefficient estimate \(|f^{(n)}(c)|\le n!\,C/R^n\) for \(f\) holomorphic on a disc and bounded by \(C\) on the circle of radius \(R\) is `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` (`Analysis/Complex/Liouville.lean`; see also `norm_cauchyPowerSeries_le`, `MeasureTheory/Integral/CircleIntegral.lean`). For nonnegative coefficients it gives the saddle-point bound \([z^n]f\le f(r)/r^n\).

**Supporting material.** The Riemann–Lebesgue lemma on finite-dimensional real inner product spaces, \(\int e^{-2\pi i\langle v,w\rangle}f(v)\,dv\to0\) as \(\|w\|\to\infty\) for integrable \(f\) (`tendsto_integral_exp_inner_smul_cocompact`, `Analysis/Fourier/RiemannLebesgueLemma.lean`), is the qualitative statement that nonstationary phase sharpens to rapid decay; no rate is proved.

### TauCeti

The local geometry behind Laplace-type and perturbative analysis is partly present. The Morse–Palais lemma: if \(f\) is \(C^{n+2}\) (\(1\le n\le\infty\)) on a Banach space near a critical point \(x\) whose second derivative is a linear homeomorphism onto the dual, there is a \(C^n\) chart \(\psi\) with \(\psi(x)=0\) and \(f(y)=f(x)+\tfrac12 D^2f(x)(\psi y,\psi y)\) on its source ([Morse lemma](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/Morse/NormalForm.lean), [local form](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/Morse/LocalNormalForm.lean)). This is the change of variables used in entries 50.11, 50.12, and 50.14; the resulting integral asymptotics are not proved.

**Synopsis entries.** Partly covered: 50.15 (the model integral for real \(\alpha\) and \(m\), and for complex \(\alpha\) when \(m=1\)), 50.73 (the Cauchy coefficient bound, which gives the saddle-point bound; no Hayman theorem). Not covered: 50.9–50.14, 50.16–50.19, 50.74, 50.20–50.22.

## Summation, Mellin transforms, and regular variation

[Mathematical scope](SYNOPSIS50.md#summation-mellin-transforms-and-regular-variation).

### Mathlib

**Summation, Abelian and Tauberian theorems.**

Abel's summation formula, the discrete integration by parts that converts asymptotics of partial sums into asymptotics of weighted sums, is proved in several forms (`NumberTheory/AbelSummation.lean`). Bernoulli polynomials, their periodizations, and the Fourier expansions of the periodized polynomials are in `NumberTheory/ZetaValues.lean`; they are the ingredients of the Euler–Maclaurin remainder, but the formula itself is not stated. Abel's limit theorem, the prototype Abelian theorem, is recorded in Section 40 (`Analysis/Complex/AbelLimit.lean`). Mellin inversion (`mellinInv_mellin_eq`, `Analysis/MellinInversion.lean`; see Section 49) is the supporting result for the Mellin method; contour displacement, pole-term asymptotics, and the Mellin convolution theorem are not stated. No Euler–Maclaurin formula with remainder, and no Tauberian theorem of Hardy–Littlewood or Karamata type or theory of regular variation, is in Mathlib.

### TauCeti

On the Tauberian side, TauCeti proves the Wiener–Ikehara theorem: for nonnegative coefficients whose Dirichlet series converges on \(\mathop{\mathrm{Re}}s>1\) and minus \(\kappa/(s-1)\) agrees there with a function continuous on \(\mathop{\mathrm{Re}}s\ge1\), the averages \(x^{-1}\sum_{n\le x}a_n\) tend to \(\kappa\) ([Wiener–Ikehara](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/NumberTheory/LSeries/WienerIkehara/SharpCutoff.lean); see Section 27). Abel summation is supplemented by a transfer of linear growth to power weights: if \(x^{-1}\sum_{n\le x}c_n\to\kappa\) and \(\tau>-1\), then \(x^{-\tau-1}\sum_{n\le x}c_nn^\tau\to\kappa/(\tau+1)\) (`TauCeti.tendsto_rpow_inv_mul_sum_Icc_rpow_mul`, [Abel summation consequences](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/NumberTheory/AbelSummation.lean)). It also proves \(\mathop{\mathrm{Li}}(x)\sim x/\log x\) for the logarithmic integral (Section 49). These are Tauberian and summation results outside the synopsis entries; Karamata’s theorem is not among them.

**Synopsis entries.** Not covered: 50.23, 50.24, 50.26–50.29.

## Differential equations, irregular singularities, and WKB

[Mathematical scope](SYNOPSIS50.md#differential-equations-irregular-singularities-and-wkb).

Neither library treats regular or irregular singular points of linear differential equations, formal or sectorial fundamental solutions, Stokes data, or WKB and turning-point approximations. The nearest supporting material is Grönwall’s inequality (`Analysis/ODE/Gronwall.lean`) and the Picard–Lindelöf theorem (`Analysis/ODE/PicardLindelof.lean`) in Mathlib, the supporting tools for Volterra-type error bounds such as entry 50.41.

**Synopsis entries.** Not covered: 50.30–50.41.

## Gevrey series, Borel summation, and resurgence

[Mathematical scope](SYNOPSIS50.md#gevrey-series-borel-summation-and-resurgence).

Neither library defines Gevrey classes, the formal Borel transform, Borel–Laplace summation, multisummability, or resurgent functions.

**Synopsis entries.** Not covered: 50.42–50.50, 50.72, 50.51–50.56.

## Regular and singular perturbation of differential equations

[Mathematical scope](SYNOPSIS50.md#regular-and-singular-perturbation-of-differential-equations).

### TauCeti

For a parameterized autonomous ODE with a globally \(C^{n+1}\) field on complete spaces (\(n\) finite or infinite), there is a \(C^{n+1}\) family of local solutions on an open parameter neighbourhood (`ODE.exists_contDiffOn_picard_solution_of_contDiff`, [smooth parameter dependence](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/SmoothParameter.lean)), and the global solution of a globally Lipschitz \(C^{n+1}\) field is \(C^{n+1}\) jointly in time and initial condition (`ODE.contDiff_globalSolution`, [initial conditions](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/InitialCondition.lean)). This is smooth, not analytic, dependence on the parameter.

For hyperbolic equilibria: for a symmetric operator on a finite-dimensional space, the flow of its negative contracts at a common positive exponential rate on the positive spectral subspace forward in time and on the negative one backward in time, which gives an exponential dichotomy when the kernel is zero ([exponential dichotomy](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/ExponentialDichotomy.lean)). The Lyapunov–Perron method: for \(y'=Ay+N(y)\) on a Banach space with a projection \(P\) satisfying forward and backward exponential estimates (constant \(K\), rate \(\alpha\)) and a nonlinearity small near \(0\) compared with \(\alpha/K\), the initial values of forward solutions confined to a small ball form the graph of a Lipschitz map over a ball in the range of \(P\), tangent to that range at \(0\) when \(DN(0)=0\), and the Lyapunov–Perron solutions depend \(C^1\) on the parameter where \(N\) is \(C^1\) ([local stable sets](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/LyapunovPerron/Local.lean), [smooth dependence](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/LyapunovPerron/Smooth.lean)). At a nondegenerate critical point of a \(C^2\) function on a finite-dimensional Hilbert space, the local stable and unstable sets of the negative gradient flow are \(C^1\) graphs tangent to the Hessian spectral subspaces ([local invariant manifolds](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/Morse/LocalInvariantManifold.lean)). These concern hyperbolic equilibria, not normally hyperbolic slow manifolds; the Tikhonov and Fenichel theorems are absent.

Operator perturbation theory is present in forms adjacent to entry 50.68. A bounded perturbation of a strongly continuous semigroup generator again generates a semigroup on the same domain, with growth bound \(M\exp((\omega+M\|B\|)t)\) when the original bound is \(M e^{\omega t}\) ([bounded perturbation theorem](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Semigroups/Generation/BoundedPerturbation.lean)). Fredholmness and index are stable under sufficiently small operator-norm perturbations and under compact perturbations ([small perturbations](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fredholm/SmallPerturbation.lean), [compact perturbations](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fredholm/CompactPerturbation.lean)). The Kato–Rellich theorem (a symmetric perturbation relatively bounded with bound \(<1\) preserves self-adjointness) is `IsSelfAdjoint.add_of_isRelativelyBounded` ([Kato–Rellich](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/LinearPMap/KatoRellich.lean)). Analytic perturbation of an isolated simple eigenvalue and the Rayleigh–Schrödinger coefficients are not proved.

**Synopsis entries.** Partly covered: 50.57 (\(C^{n+1}\) dependence on parameters and initial data, TauCeti; not analytic dependence or the perturbation expansion). Not covered: 50.58–50.62, 50.69, 50.70, 50.63, 50.65, 50.67, 50.71, 50.68.
