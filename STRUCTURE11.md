# Structure 11: Classical inequalities, means, majorization, and rearrangement

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS11.md); [bibliographical scope](CKMA-bib.md#ckma-11); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.MeanInequalities`, `Mathlib.Analysis.MeanInequalitiesPow`, `Mathlib.MeasureTheory.Integral.MeanInequalities`, `Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp`, `Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality`, `Mathlib.Analysis.InnerProductSpace.Basic`, `Mathlib.Algebra.Order.BigOperators.Ring.Finset`, `Mathlib.Algebra.Order.Chebyshev`, `Mathlib.Algebra.Order.Rearrangement`, `Mathlib.Analysis.Convex.Jensen`, `Mathlib.Analysis.Convex.Integral`, `Mathlib.Analysis.Convex.DoublyStochasticMatrix`, `Mathlib.Analysis.Convex.Birkhoff`, `Mathlib.Probability.Moments.Variance`, `Mathlib.InformationTheory.KullbackLeibler.Basic`, `Mathlib.InformationTheory.KullbackLeibler.DataProcessing`, `Mathlib.Analysis.ODE.Gronwall`, `Mathlib.MeasureTheory.Integral.Layercake`, `Mathlib.Analysis.SpecialFunctions.Pow.Integral`, `Mathlib.Analysis.Complex.Hadamard`, `Mathlib.Basic.Real.ConjExponents`, `Mathlib.Data.Real.ConjExponents`. `Mathlib.Data.Real.ConjExponents` is deprecated and re-exports `Mathlib.Basic.Real.ConjExponents`.

**Namespaces.** `Real`, `NNReal`, and `ENNReal` carry the mean, Young, Hölder, Minkowski, and power-mean inequalities, including the Lebesgue-integral Hölder and Minkowski inequalities in `ENNReal`. The Cauchy–Schwarz inequality for inner products is at the root, its finite-sum forms and Abel's inequality are in `Finset`, and the \(L^p\) seminorm comparisons are in `MeasureTheory`. Chebyshev and rearrangement are theorems about the predicates `Monovary`, `Antivary`, `MonovaryOn`, and `AntivaryOn`. Finite Jensen is stated on `ConvexOn`, `ConcaveOn`, `StrictConvexOn`, and `StrictConcaveOn`. Birkhoff’s theorem is at the root of its file. Relative entropy is in `InformationTheory`, Popoviciu's variance bound in `ProbabilityTheory`, the layer-cake formulas in `MeasureTheory`, and the three-lines theorem in `Complex.HadamardThreeLines`. TauCeti declarations are in `TauCeti`, `TauCeti.PDE`, `Real`, `Seminorm`, `Matrix`, and the dot-notation namespaces named below.

## Convexity and means

[Mathematical scope](SYNOPSIS11.md#convexity-and-means).

### Mathlib

**AM-GM, HM-GM, and Young.**

Weighted AM-GM, for nonnegative weights summing to \(1\) and a nonnegative function \(z\) on a finite set \(s\):
\[
\prod_{i\in s} z_i^{w_i}\le\sum_{i\in s} w_i z_i.
\]
If the total weight \(W\) is positive, the normalized form compares \(\bigl(\prod z_i^{w_i}\bigr)^{1/W}\) with \(\bigl(\sum w_i z_i\bigr)/W\). Two-, three-, and four-term weighted forms are included. The statements are given for \(\mathbb{R}\) and for \(\mathbb{R}_{\ge 0}\) (`Real.geom_mean_le_arith_mean_weighted`, `Analysis/MeanInequalities.lean`).

Equality, for strictly positive weights summing to \(1\) and nonnegative \(z\), holds if and only if every value of \(z\) equals the weighted mean, and equivalently if and only if those values all agree. For nonnegative weights the same criterion is imposed only on the coordinates of positive weight. The inequality is strict precisely when that agreement fails (`Real.geom_mean_eq_arith_mean_weighted_iff_of_pos`, `Real.geom_mean_lt_arith_mean_weighted_iff_of_pos`, and their nonnegative-weight variants).

Weighted HM-GM, for a nonempty finite set, strictly positive weights summing to \(1\), and strictly positive \(z\):
\[
\Bigl(\sum_{i\in s}\frac{w_i}{z_i}\Bigr)^{-1}\le\prod_{i\in s} z_i^{w_i}.
\]
The form with an arbitrary positive total weight normalizes both sides in the same way. This is proved for real values, as a corollary of weighted AM-GM (`Real.harm_mean_le_geom_mean_weighted`).

Young’s inequality, for Hölder conjugates \(p\) and \(q\):
\[
ab\le\frac{|a|^p}{p}+\frac{|b|^q}{q}.
\]
For nonnegative \(a\) and \(b\), equality holds if and only if \(a^p=b^q\) (`Real.young_inequality`, `Real.young_inequality_eq_iff_of_nonneg`). The inequality and its equality case are also stated for \(\mathbb{R}_{\ge 0}\) and \(\mathbb{R}_{\ge 0}\infty\). The conjugate-function form \(st\le\phi(s)+\phi^*(t)\) is the Fenchel–Young inequality of [Section 12](STRUCTURE12.md).

**Power means.**

For nonnegative weights summing to \(1\), a nonnegative function \(z\), and a natural number \(n\),
\[
\Bigl(\sum_{i\in s} w_i z_i\Bigr)^n\le\sum_{i\in s} w_i z_i^n.
\]
An even natural exponent drops the sign hypothesis on \(z\), by even-power convexity on \(\mathbb{R}\). Integer exponents require \(z>0\). For a real exponent \(p\ge 1\) the same weighted inequality holds, together with
\[
\sum_{i\in s} w_i z_i\le\Bigl(\sum_{i\in s} w_i z_i^p\Bigr)^{1/p}
\]
(`Real.rpow_arith_mean_le_arith_mean_rpow`, `Real.arith_mean_le_rpow_mean`). These are the cases of the weighted power-mean comparison in which the smaller exponent is \(1\). Both files list the comparison for a general pair of exponents, including negative exponents, the convergence of the power mean to the geometric mean, and equality criteria for every inequality, as future work (`Analysis/MeanInequalities.lean`, `Analysis/MeanInequalitiesPow.lean`).

For two nonnegative numbers and \(0<p\le q\),
\[
(a^q+b^q)^{1/q}\le(a^p+b^p)^{1/p}.
\]
For \(p\ge 1\), \(a^p+b^p\le(a+b)^p\) and \((a+b)^p\le 2^{p-1}(a^p+b^p)\). For \(0\le p\le 1\) the first of these reverses: \((a+b)^p\le a^p+b^p\). The extended-nonnegative constant `LpAddConst` equals \(1\) for exponent \(0\) or at least \(1\), and equals \(2^{1/p-1}\) on \((0,1)\); it is the constant in the corresponding quasi-triangle inequality.

**Jensen.**

Over a field that is a strict ordered ring, and an ordered module over that field, a convex function on a convex set satisfies
\[
f\Bigl(\sum_{i\in t} w_i\cdot p_i\Bigr)\le\sum_{i\in t} w_i\cdot f(p_i)
\]
whenever the weights are nonnegative and sum to \(1\) and the points lie in the set (`ConvexOn.map_sum_le`). If the total weight is merely positive, the same comparison holds for centers of mass. Concave functions reverse the inequality. For a strictly convex function and strictly positive weights, the inequality is strict unless the points are constant, and equality holds if and only if every point equals the center of mass. For nonnegative weights, equality holds if and only if the points of nonzero weight all equal the center of mass. The strict inequality holds if and only if some point differs from the center of mass (`StrictConvexOn.map_sum_eq_iff`, `StrictConvexOn.map_sum_lt_iff_of_pos`). The concave statements are dual (`Analysis/Convex/Jensen.lean`).

A convex function on the convex hull of a set attains its maximum on that set: the value at a point of the hull is at most the value at some point of the set. On a segment, and on a real interval, the maximum is attained at an endpoint. Concave functions have the corresponding minimum principles.

The integral form needs a complete normed real space. If \(g\) is continuous and convex on a closed convex set, \(\mu\) is a finite nonzero measure, \(f\) and \(g\circ f\) are integrable, and \(f\) takes values in the set almost everywhere, then
\[
g\Bigl(\fint f\,d\mu\Bigr)\le\fint (g\circ f)\,d\mu
\]
(`ConvexOn.map_average_le`). On a probability space the averages may be written as integrals (`ConvexOn.map_integral_le`). The same comparison holds for the average over a subset of positive finite measure. If \(g\) is strictly convex, either \(f\) equals its average almost everywhere or the inequality is strict (`StrictConvexOn.ae_eq_const_or_map_average_lt`). If the set itself is strictly convex and closed, an integrable function valued almost everywhere in the set is either almost everywhere equal to its average or has average in the interior. In a complete strictly convex normed space, a function with \(\|f(x)\|\le C\) almost everywhere is either almost everywhere equal to its average or satisfies \(\|\fint f\|<C\) (`Analysis/Convex/Integral.lean`). Continuity of convex functions, gauges, and the extreme-point theory are in [Section 12](STRUCTURE12.md).

**Interpolation of moments.** For nonnegative measurable \(f,g\) and exponents \(a,b\ge0\) with \(a+b=1\), \(\int f^ag^b\le(\int f)^a(\int g)^b\) in the lower Lebesgue integral (`ENNReal.lintegral_mul_norm_pow_le`). Applied to \(f^r\) and \(f^s\) this is the interpolation inequality \(\int f^{(1-t)r+ts}\le(\int f^r)^{1-t}(\int f^s)^t\); the log-convexity of \(r\mapsto\log\sum_iw_ix_i^r\) is not stated.

### TauCeti

An operator version of the arithmetic–geometric mean inequality is proved for positive elements in the continuous-functional-calculus setting: the geometric mean satisfies \(2(a\#b)\le a+b\) for strictly positive \(a\) and nonnegative \(b\) ([geometric mean](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/GeometricMean.lean); see [Section 13](STRUCTURE13.md) for its construction).

For nonnegative weights summing to \(1\), the weighted geometric mean \(G(a)=\prod_i a_i^{w_i}\) of nonnegative families is superadditive, \(G(a)+G(b)\le G(a+b)\), hence concave on the nonnegative orthant (`Real.prod_rpow_add_prod_rpow_le_prod_add_rpow`, [superadditivity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/MeanInequalities.lean)); with equal weights on eigenvalues it gives the core of Minkowski's determinant inequality ([Section 13](STRUCTURE13.md)).

**Synopsis entries.** Covered: 11.1, 11.2, 11.4 (Mathlib). Partly covered: 11.3 (only the comparisons with smaller exponent \(1\) and the two-point comparison for \(0<p\le q\)), 11.5 (strictly convex case, finite and integral; the supporting-affine-function description is not stated), 11.7 (the integral interpolation inequality as an instance of two-function Hölder; log-convexity of the finite moment function is not stated). Not covered: 11.6, 11.8–11.11.

## Norm inequalities and finite rearrangements

[Mathematical scope](SYNOPSIS11.md#norm-inequalities-and-finite-rearrangements).

### Mathlib

**Conjugate exponents.**

Positive reals \(p\), \(q\), and \(r\) form a Hölder triple when \(p^{-1}+q^{-1}=r^{-1}\). They are Hölder conjugates when the triple has third exponent \(1\), which forces \(p>1\) and \(q>1\). The conjugate exponent of \(p\) is \(p/(p-1)\). The same language is available for nonnegative and extended-nonnegative exponents (`Basic/Real/ConjExponents.lean`).

Two functions monovary on a set when a strict increase of the second forces a weak increase of the first, and they antivary when that conclusion is reversed (`Order/Monotone/Monovary.lean`).

**Cauchy–Schwarz and Bergström.**

In a real or complex inner product space, \(\|\langle x,y\rangle\|\le\|x\|\,\|y\|\) (`norm_inner_le_norm`, `inner_mul_inner_self_le`). Equality holds if and only if \(x=0\) or \(y\) is a scalar multiple of \(x\) (`norm_inner_eq_norm_tfae`, `norm_inner_eq_norm_iff` for nonzero vectors), which is the linear-dependence criterion including the zero cases (`Analysis/InnerProductSpace/Basic.lean`). For finite sums over a linearly ordered commutative semiring, \((\sum f_ig_i)^2\le(\sum f_i^2)(\sum g_i^2)\) (`Finset.sum_mul_sq_le_sq_mul_sq`). Bergström's inequality (Sedrakyan's or Titu's lemma) \((\sum_i f_i)^2/\sum_i g_i\le\sum_i f_i^2/g_i\) for \(g_i>0\) is `Finset.sq_sum_div_le_sum_sq_div` (`Algebra/Order/BigOperators/Ring/Finset.lean`); its equality case is not stated.

**Hölder and Minkowski for finite sums.**

For a finite set and real functions, Hölder conjugates give
\[
\sum_{i\in s} f_i g_i\le\Bigl(\sum_{i\in s}|f_i|^p\Bigr)^{1/p}\Bigl(\sum_{i\in s}|g_i|^q\Bigr)^{1/q}.
\]
For a Hölder triple,
\[
\sum_{i\in s}|f_i g_i|^r\le\Bigl(\sum_{i\in s}|f_i|^p\Bigr)^{r/p}\Bigl(\sum_{i\in s}|g_i|^q\Bigr)^{r/q}.
\]
The same comparisons are proved for nonnegative and extended-nonnegative values (`Real.inner_le_Lp_mul_Lq`, `Real.Lr_rpow_le_Lp_mul_Lq`). A weighted form, for \(p\ge 1\) and nonnegative weights and values, reads
\[
\sum_{i\in s} w_i f_i\le\Bigl(\sum_{i\in s} w_i\Bigr)^{1-1/p}\Bigl(\sum_{i\in s} w_i f_i^p\Bigr)^{1/p}.
\]
If the series of \(p\)-th and \(q\)-th powers are summable, the Hölder and Minkowski comparisons extend to the corresponding series.

Minkowski’s inequality, for \(p\ge 1\),
\[
\Bigl(\sum_{i\in s}|f_i+g_i|^p\Bigr)^{1/p}\le\Bigl(\sum_{i\in s}|f_i|^p\Bigr)^{1/p}+\Bigl(\sum_{i\in s}|g_i|^p\Bigr)^{1/p},
\]
is deduced from the fact that the \(\ell^p\) norm is the maximum of the pairing against vectors of conjugate norm at most \(1\) (`Real.Lp_add_le`; the maximality statement is `NNReal.isGreatest_Lp`). For the same range of \(p\),
\[
\Bigl(\sum_{i\in s}|f_i|\Bigr)^p\le(\#s)^{p-1}\sum_{i\in s}|f_i|^p.
\]

**Integral forms.** Hölder's inequality for the lower Lebesgue integral with conjugate real exponents is `ENNReal.lintegral_mul_le_Lp_mul_Lq`, and for real nonnegative integrands `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`. In seminorm form, \(\|\varphi f\|_r\le\|\varphi\|_p\|f\|_q\) for every Hölder triple of extended exponents, including the endpoints \(1\) and \(\infty\) (`MeasureTheory.eLpNorm_smul_le_mul_eLpNorm`). For finitely many nonnegative functions and nonnegative weights \(p_i\) summing to \(1\), \(\int\prod_if_i^{p_i}\le\prod_i(\int f_i)^{p_i}\) (`ENNReal.lintegral_prod_norm_pow_le`), which is the generalized Hölder inequality with finite exponents \(1/p_i\). Minkowski's inequality \(\|f+g\|_p\le\|f\|_p+\|g\|_p\) holds for \(1\le p\le\infty\) (`MeasureTheory.eLpNorm_add_le`, and `ENNReal.lintegral_Lp_add_le` for the integral); for \(0<p<1\) Mathlib has only the quasi-triangle inequality with constant \(2^{1/p-1}\) (`ENNReal.lintegral_Lp_add_le_of_le_one`). Lyapunov's inequality \(\|f\|_p\le\|f\|_q\) for \(p\le q\) on a probability space is `MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le`, and on a finite measure space the factor \(\mu(X)^{1/p-1/q}\) appears in `MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ` (`MeasureTheory/Function/LpSeminorm/CompareExp.lean`). Equality cases of Hölder and Minkowski are not stated. The \(L^p\) spaces themselves are recorded in [Section 04](STRUCTURE04.md).

**Chebyshev and Abel.**

On a linear strict ordered semiring in which \(a\le b\) yields some \(c\) with \(a+c=b\), functions that monovary on a finite set satisfy
\[
\Bigl(\sum_{i\in s} f_i\Bigr)\Bigl(\sum_{i\in s} g_i\Bigr)\le(\#s)\sum_{i\in s} f_i g_i,
\]
and antivarying functions satisfy the reverse inequality (`MonovaryOn.sum_mul_sum_le_card_mul_sum`, `AntivaryOn.card_mul_sum_le_sum_mul_sum`). The scalar form, with values in an ordered cancellative module and a positive-scalar action, is the statement actually proved; multiplication is the special case. Only uniform weights occur. A function monovaries with itself, so
\[
\Bigl(\sum_{i\in s} f_i\Bigr)^2\le(\#s)\sum_{i\in s} f_i^2
\]
needs no extra monotonicity hypothesis, and the same bound holds for a multiset. If \(f\) is nonnegative on \(s\), then
\[
\Bigl(\sum_{i\in s} f_i\Bigr)^{n+1}\le(\#s)^n\sum_{i\in s} f_i^{n+1},
\]
recorded in the file as a special case of Jensen (`Algebra/Order/Chebyshev.lean`).

Abel’s inequality is an ordered-ring statement about sequences indexed by \(\mathbb{N}\). If every partial sum of \(f\) up to an index at most \(n\) is at most the corresponding partial sum of \(c\), and \(g\) is nonnegative and antitone on \(\{k:k<n\}\), then
\[
\sum_{i<n} f_i g_i\le\sum_{i<n} c_i g_i
\]
(`Finset.sum_mul_le_sum_mul_of_sum_range_le`). If every partial sum of \(f\) is at most \(M\), the weighted sum is at most \(M\,g_0\); the empty partial sum forces \(M\ge 0\). If every partial sum is at least \(m\), then \(m\,g_0\) is a lower bound and \(m\le 0\). In a linear ordered ring, a uniform bound \(M\) on the absolute values of the partial sums yields \(\bigl|\sum_{i<n} f_i g_i\bigr|\le M\,g_0\) (`Finset.abs_sum_mul_le_mul_of_abs_sum_range_le`).

**Popoviciu's variance bound.** A real random variable with \(a\le X\le b\) almost surely on a probability space satisfies \(\operatorname{Var}X\le((b-a)/2)^2\) (`ProbabilityTheory.variance_le_sq_of_bounded`, `Probability/Moments/Variance.lean`). The covariance (Grüss) form is not stated.

**Rearrangement.**

In the same ordered-module setting, if \(f\) and \(g\) monovary on \(s\) and a permutation \(\sigma\) moves only points of \(s\), then
\[
\sum_{i\in s} f_i\cdot g_{\sigma i}\le\sum_{i\in s} f_i g_i
\]
(`MonovaryOn.sum_smul_comp_perm_le_sum_smul`). If they antivary, the inequality reverses, so the sum is minimized by an antivarying rearrangement. Under a strictly positive scalar action, equality holds if and only if \(g\circ\sigma\) still monovaries with \(f\), or still antivaries with \(f\) in the dual case, and the inequality is strict precisely when that fails. The multiplication form is included. The equality criterion for an injective rearranged sequence is recorded as future work (`Algebra/Order/Rearrangement.lean`).

**Synopsis entries.** Covered: 11.12, 11.16, 11.18, 11.73 (Mathlib). Partly covered: 11.13 and 11.14 (the inequalities, with endpoints for Hölder and \(1\le p\le\infty\) for Minkowski; no equality cases), 11.15 (finitely many functions with finite exponents; two factors with arbitrary extended exponents), 11.17 (uniform weights only), 11.64 (Popoviciu's variance bound only), 11.19 (inequality without the equality case). Not covered: 11.65, 11.20, 11.21.

## Majorization, convex order, and entropy

[Mathematical scope](SYNOPSIS11.md#majorization-convex-order-and-entropy).

### Mathlib

**Doubly stochastic matrices and Birkhoff.**

A square matrix over an ordered semiring is doubly stochastic when its entries are nonnegative and every row sum and every column sum equals \(1\). The set of such matrices is convex, and every permutation matrix is doubly stochastic (`Analysis/Convex/DoublyStochasticMatrix.lean`).

Birkhoff’s theorem, over a linear ordered field and a finite index: the doubly stochastic matrices are exactly the convex hull of the permutation matrices, their extreme points are exactly the permutation matrices, and every doubly stochastic matrix is a convex combination of permutation matrices (`doublyStochastic_eq_convexHull_permMatrix`, `extremePoints_doublyStochastic`, `exists_eq_sum_perm_of_mem_doublyStochastic`, `Analysis/Convex/Birkhoff.lean`). A real doubly stochastic matrix has \(\ell^2\) operator norm at most \(1\) (`Matrix.l2_opNorm_le_one_of_mem_doublyStochastic`). The module documentation lists the characterization of majorization by doubly stochastic matrices as future work.

**Relative entropy.** For finite measures \(\mu,\nu\), the Kullback–Leibler divergence `InformationTheory.klDiv` (with the mass correction \(\nu(X)-\mu(X)\)) is nonnegative, and its real form is nonnegative (`InformationTheory.integral_llr_add_sub_measure_univ_nonneg`, Gibbs' inequality); it vanishes exactly when \(\mu=\nu\) (`InformationTheory.klDiv_eq_zero_iff`). On probability vectors this is Gibbs' inequality with its equality case. The data-processing inequality \(\mathrm{KL}(\mu\circ g^{-1}\|\nu\circ g^{-1})\le\mathrm{KL}(\mu\|\nu)\) holds for measurable \(g\) (`InformationTheory.klDiv_map_le`, `InformationTheory/KullbackLeibler/DataProcessing.lean`). Applied to finite measures on a finite type and the map to a point, it yields the log-sum inequality; the finite-sum statement and its equality case are not stated. The binary entropy is bounded by \(\log2\) (`Real.binEntropy_le_log_two`); Schur-concavity of Shannon entropy is not stated.

### TauCeti

Majorization through doubly stochastic matrices is developed in one direction. For a doubly stochastic real matrix \(D\) and a function \(\phi\) convex on a set containing the entries of \(y\), \(\sum_i\phi((Dy)_i)\le\sum_i\phi(y_i)\), and for monovarying \(x\) and \(y\), \(x\cdot Dy\le x\cdot y\) (`ConvexOn.sum_map_mulVec_le_of_mem_doublyStochastic`, `Monovary.dotProduct_mulVec_le_of_mem_doublyStochastic`, [doubly stochastic averaging](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/DoublyStochasticMatrix.lean)). This is Karamata's inequality with the hypothesis \(x=Dy\) in place of the partial-sum hypothesis; with \(\phi=|\cdot|^p\) it gives \(\|Dy\|_p\le\|y\|_p\) for \(1\le p<\infty\). By Birkhoff's theorem, \(Dy\) lies in the convex hull of the rearrangements of \(y\) (`Matrix.mulVec_mem_convexHull_range_comp_perm`, [permutation orbit](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/PermutationOrbit.lean)); with Mathlib's Birkhoff theorem this identifies the vectors \(Dy\) with the permutohedron of \(y\). Contraction of a general permutation-invariant norm under \(D\) follows from this membership but is not stated.

For real tuples, weak majorization of antitone nonnegative tuples is defined by prefix sums (`TauCeti.IsWeaklyMajorizedBy`), and the transfer descent is proved: a convex set invariant under coordinate permutations and single sign changes that contains \(y\) contains every antitone nonnegative \(z\) whose prefix sums are bounded by those of \(y\). Hence every symmetric gauge, including every \(\ell^p\) norm with \(p\ge 1\), is monotone for weak majorization (`TauCeti.IsSymmetricConvex.mem_of_prefixSum_le`, `Seminorm.IsSymmetricGauge.apply_le_of_prefixSum_le`, `TauCeti.IsWeaklyMajorizedBy.apply_le`, [weak majorization](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/Majorization.lean)). The characterizations of weak majorization by increasing convex functions and by doubly substochastic matrices are not stated.

The forward Schur–Horn theorem is proved: the diagonal of a symmetric operator on a finite-dimensional real or complex inner product space, in any orthonormal basis, is the image of its spectrum under a doubly stochastic matrix, lies in the convex hull of the rearrangements of the spectrum, and satisfies \(\sum_k\phi(d_k)\le\sum_i\phi(\lambda_i)\) for convex \(\phi\) ([Schur–Horn](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/InnerProductSpace/SchurHorn.lean)). The construction of \(D\) from the partial-sum inequalities \(x\prec y\) is not proved.

There is also a specific majorization rigidity lemma for an antitone integer sequence: prefix sums bounded by those of the finite staircase, equality of the total sum, and equality of a specified quadratic statistic force the sequence to equal the staircase ([staircase criterion](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Combinatorics/Majorization.lean)). This is a special-purpose majorization rigidity lemma.

Pinsker's inequality is proved with natural logarithms: for probability measures, the total variation \(\|\mu-\nu\|\) of the signed measure \(\mu-\nu\) satisfies \(\|\mu-\nu\|^2\le2\,\mathrm{KL}(\mu\|\nu)\), with infinite divergence allowed (`TauCeti.totalVariation_sq_le_two_mul_klDiv`, [Pinsker](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/InformationTheory/KullbackLeibler/Pinsker.lean)). On probability vectors this is \(D(p\|q)\ge\frac12\|p-q\|_1^2\).

**Synopsis entries.** Covered: 11.23 (Mathlib), 11.30 (Mathlib, TauCeti). Partly covered: 11.22 (the direction \(x=Dy\Rightarrow x\in\operatorname{conv}\{y\circ\sigma\}\) and its converse via Birkhoff; the equivalence with the partial-sum inequalities is not proved), 11.24 (the inequality under the hypothesis \(x=Dy\); no partial-sum hypothesis and no equality case), 11.71 (monotonicity of symmetric gauges and symmetric convex sets under weak majorization of antitone nonnegative tuples), 11.26 (\(\ell^p\) norms, \(1\le p<\infty\), and the \(\ell^2\) operator norm; general permutation-invariant norms not stated), 11.29 (obtainable from the data-processing inequality; not stated in finite-sum form, no equality case). Not covered: 11.72, 11.25, 11.27, 11.28, 11.31.

## Hardy, Hilbert, and differential inequalities

[Mathematical scope](SYNOPSIS11.md#hardy-hilbert-and-differential-inequalities).

### Mathlib

Mathlib's Grönwall inequality is the differential form: if \(\|f(a)\|\le\delta\) and \(\|f'(x)\|\le K\|f(x)\|+\varepsilon\) on \([a,b)\), then \(\|f(x)\|\) is bounded by `gronwallBound` \(\delta\) \(K\) \(\varepsilon\) \((x-a)\) (`norm_le_gronwallBound_of_norm_deriv_right_le`, `le_gronwallBound_of_liminf_deriv_right_le`, `Analysis/ODE/Gronwall.lean`), with applications to the distance between approximate solutions of ordinary differential equations.

### TauCeti

The integral form of Grönwall's inequality with a constant rate is proved: if \(\varphi\) is continuous on \([a,b]\), \(K\ge0\), and \(\varphi(t)\le c+K\int_a^t\varphi\) for \(t\in[a,b]\), then \(\varphi(t)\le c\,e^{K(t-a)}\) (`TauCeti.le_mul_exp_of_le_add_mul_integral`, [integral Grönwall](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/ODE/Gronwall.lean)).

Wirtinger's inequality for periodic functions is proved with the sharp constant and its equality case: for an absolutely continuous \(f\) on \([a,b]\) with \(f(a)=f(b)\), values in a finite-dimensional real inner product space, and square-integrable derivative, \(\int_a^b\|f-\bar f\|^2\le((b-a)/2\pi)^2\int_a^b\|f'\|^2\), with equality exactly when \(f-\bar f\) is a first harmonic (`TauCeti.integral_norm_sub_average_sq_le`, `TauCeti.integral_norm_sub_average_sq_eq_iff`, [Wirtinger](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Fourier/Wirtinger.lean)). The Dirichlet form is the sharp Poincaré inequality on an interval: \((\pi/(b-a))^2\int_a^bu^2\le\int_a^b|u'|^2\) for \(u\in H^1_0(a,b)\), with \((\pi/(b-a))^2\) the largest such constant and equal to the first Dirichlet eigenvalue, whose eigenfunctions are the sine modes (`TauCeti.PDE.isGreatest_mul_norm_value_sq_le_energyFormH1_intervalDomain`, `TauCeti.PDE.isDirichletEigenvalue_laplacian_intervalDomain_iff`, [interval spectrum](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/PDE/Spectrum/Interval.lean)). The equality case of the Dirichlet inequality is not stated as such.

**Synopsis entries.** Partly covered: 11.40 (differential form in Mathlib; integral form with constant rate and continuous \(u\) in TauCeti), 11.43 (both inequalities with sharp constants; equality characterized in the periodic case). Not covered: 11.32–11.35, 11.37–11.39, 11.41, 11.42.

## Rearrangement and symmetrization

[Mathematical scope](SYNOPSIS11.md#rearrangement-and-symmetrization).

### Mathlib

The layer-cake formula is proved for nonnegative almost-everywhere measurable real functions on an arbitrary measure space: \(\int f\,d\mu=\int_0^\infty\mu\{f>t\}\,dt\) (`MeasureTheory.lintegral_eq_lintegral_meas_lt`, with the \(\{f\ge t\}\) variant), more generally \(\int G\circ f\,d\mu=\int_0^\infty g(t)\,\mu\{f>t\}\,dt\) for \(G\) a primitive of a nonnegative locally integrable \(g\) (`MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul`, `MeasureTheory/Integral/Layercake.lean`), and in particular \(\int f^p=p\int_0^\infty t^{p-1}\mu\{f>t\}\,dt\) for \(p>0\) (`MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul`, `Analysis/SpecialFunctions/Pow/Integral.lean`).

### TauCeti

For a measure on a normed space, the Schwarz (symmetric decreasing) rearrangement of an \([0,\infty]\)-valued function is defined from its distribution function (`TauCeti.schwarzRearrangement`); for an additive Haar measure on a finite-dimensional real normed space it is radially nonincreasing, equimeasurable with \(f\), monotone, idempotent, and preserves every \(L^p\) norm, \(0<p\le\infty\) (`TauCeti.addHaar_setOf_lt_schwarzRearrangement`, `TauCeti.eLpNorm_schwarzRearrangement`, [Schwarz rearrangement](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Function/SchwarzRearrangement.lean)). The Hardy–Littlewood and Riesz inequalities and the \(L^p\) contraction are not proved for it.

Steiner symmetrization of subsets of a real inner product space in a unit direction is defined by replacing each line section with the centered open interval of the same length (`TauCeti.steinerSymmetrization`). For Lebesgue-measurable sets the symmetral is measurable and has the same volume, depends only on the null-set class of the input, is monotone and idempotent, and does not increase the volume of symmetric differences (`TauCeti.volume_steinerSymmetrization`, `TauCeti.volume_steinerSymmetrization_symmDiff_le`, [Steiner symmetrization](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Measure/Lebesgue/Steiner.lean)). Preservation of convexity, monotonicity of perimeter and energy, and convergence of iterated symmetrizations to a ball are not proved.

A special case of the maximal-integral characterization is proved: in a pseudometric measure space, a radially nonincreasing kernel integrates over a measurable set to at most its integral over a closed ball of no smaller finite measure (`TauCeti.setLIntegral_le_setLIntegral_closedBall_of_antitone`, [Riesz potentials](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/RieszPotential.lean)).

**Synopsis entries.** Covered: 11.44 (Mathlib). Partly covered: 11.48 (measurability, volume preservation, monotonicity, idempotence, and symmetric-difference contraction for sets), 11.49 (for radially nonincreasing kernels and balls only). Not covered: 11.45, 11.46, 11.62, 11.50.

## Geometric and convolution consequences

[Mathematical scope](SYNOPSIS11.md#geometric-and-convolution-consequences).

### Mathlib

Mathlib has only the pointwise Hölder bound for the convolution integrand and existence of the convolution of \(L^p\) and \(L^q\) functions (`Analysis/Convolution.lean`).

### TauCeti

Schur's test for nonnegative kernels is proved in the lower Lebesgue integral for s-finite measures: row and column integrals bounded by \(A\) and \(B\) give an \(L^p\) bound with constant \(A^{1-1/p}B^{1/p}\) (`TauCeti.lintegral_rpow_lintegral_mul_le`). The same file proves Young's inequality for integral kernels: for \(1\le p\le q\), \(p^{-1}+r^{-1}=1+q^{-1}\), and row and column integrals of \(k^r\) bounded by \(A\) and \(B\), one has \(\int(\int k(x,y)g(y)\,dy)^q\,dx\le A^{q(1-1/p)}B\,(\int g^p)^{q/p}\) (`TauCeti.lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq`, [Schur test](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/SchurTest.lean); also recorded in [Section 04](STRUCTURE04.md)). For a translation-invariant kernel \(k(x-y)\) with finite exponents this is Young's convolution inequality \(\|k*g\|_q\le\|k\|_r\|g\|_p\), although it is not stated for convolutions. The pointwise step is a three-exponent Hölder inequality ([Hölder with Young's exponents](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/MeanInequalities.lean)), and convolution with an \(L^1\) kernel on a finite-dimensional real normed space with an additive Haar measure is bundled as a bounded operator on \(L^p\), \(p<\infty\), with norm at most \(\|k\|_1\) (`TauCeti.norm_convolutionLp_le`, [convolution on \(L^p\)](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Function/Lp/Convolution.lean)).

The Prékopa–Leindler and Brunn–Minkowski inequalities for Lebesgue measure on finite-dimensional real spaces are proved in TauCeti and recorded in [Section 14](STRUCTURE14.md); they are the natural starting point for Prékopa's marginal theorem, which is not stated.

**Synopsis entries.** Partly covered: 11.56 (as Young's inequality for integral kernels with finite exponents, and for convolution with an \(L^1\) kernel; not stated for general convolutions). Not covered: 11.57, 11.60.

## Iterative means, moment inequalities, and interpolation

[Mathematical scope](SYNOPSIS11.md#iterative-means-moment-inequalities-and-interpolation).

### Mathlib

Hadamard's three-lines theorem is proved: if \(f\) is bounded on the closed strip \(l\le\operatorname{Re}z\le u\), continuous there, and complex differentiable in the open strip, then \(\|f(z)\|\le M(l)^{1-\theta}M(u)^{\theta}\) with \(\theta=(\operatorname{Re}z-l)/(u-l)\), where \(M(x)\) is the supremum of \(\|f\|\) on the line \(\operatorname{Re}z=x\) (`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip`, with the variant `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'` stated directly with bounds \(a\), \(b\) on the boundary lines, `Analysis/Complex/Hadamard.lean`). Clarkson's inequalities are not stated.

### TauCeti

The Riesz–Thorin interpolation theorem for complex-linear operators on simple functions, derived from Mathlib's three-lines theorem, is proved in [Riesz–Thorin](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/RieszThorin.lean) (`TauCeti.eLpNorm_le_rpow_mul_rpow_mul_eLpNorm`); it is recorded in [Section 04](STRUCTURE04.md) and [Section 27](STRUCTURE27.md).

**Synopsis entries.** Covered: 11.69 (Mathlib). Not covered: 11.66.
