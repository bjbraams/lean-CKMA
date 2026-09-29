# 11. Classical Inequalities, Means, Majorization, and Rearrangement

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. The roots for this section are `Mathlib.Analysis.MeanInequalities`, `Mathlib.Analysis.MeanInequalitiesPow`, `Mathlib.MeasureTheory.Integral.MeanInequalities`, `Mathlib.Algebra.Order.Chebyshev`, `Mathlib.Algebra.Order.Rearrangement`, `Mathlib.Analysis.Convex.Jensen`, `Mathlib.Analysis.Convex.Integral`, `Mathlib.Analysis.Convex.DoublyStochasticMatrix`, and `Mathlib.Analysis.Convex.Birkhoff`. Hölder triples are `Mathlib.Basic.Real.ConjExponents`.

**Namespaces.** `Real`, `NNReal`, and `ENNReal` carry the mean, Young, Hölder, Minkowski, and power-mean inequalities. Abel’s inequality is in `Finset`. Chebyshev and rearrangement are theorems about the predicates `Monovary`, `Antivary`, `MonovaryOn`, and `AntivaryOn`. Finite Jensen is stated on `ConvexOn`, `ConcaveOn`, `StrictConvexOn`, and `StrictConcaveOn`. Birkhoff’s theorem is at the root of its file.

This note records the finite-sum classical inequalities, Chebyshev and rearrangement, Jensen’s inequality, and Birkhoff’s theorem. The development of convexity itself is Section 12.

## Conjugate exponents

Positive reals \(p\), \(q\), and \(r\) form a Hölder triple when \(p^{-1}+q^{-1}=r^{-1}\). They are Hölder conjugates when the triple has third exponent \(1\), which forces \(p>1\) and \(q>1\). The conjugate exponent of \(p\) is \(p/(p-1)\). The same language is available for nonnegative and extended-nonnegative exponents (`Basic/Real/ConjExponents.lean`).

Two functions monovary on a set when a strict increase of the second forces a weak increase of the first, and they antivary when that conclusion is reversed (`Order/Monotone/Monovary.lean`).

## AM-GM, HM-GM, and Young

Weighted AM-GM, for nonnegative weights summing to \(1\) and a nonnegative function \(z\) on a finite set \(s\):
\[
\prod_{i\in s} z_i^{w_i}\le\sum_{i\in s} w_i z_i.
\]
If the total weight \(W\) is positive, the normalized form compares \(\bigl(\prod z_i^{w_i}\bigr)^{1/W}\) with \(\bigl(\sum w_i z_i\bigr)/W\). Two-, three-, and four-term weighted forms are included. The statements are given for \(\mathbb{R}\) and for \(\mathbb{R}_{\ge 0}\) (`Analysis/MeanInequalities.lean`).

Equality, for strictly positive weights summing to \(1\) and nonnegative \(z\), holds if and only if every value of \(z\) equals the weighted mean, and equivalently if and only if those values all agree. For nonnegative weights the same criterion is imposed only on the coordinates of positive weight. The inequality is strict precisely when that agreement fails.

Weighted HM-GM, for a nonempty finite set, strictly positive weights summing to \(1\), and strictly positive \(z\):
\[
\Bigl(\sum_{i\in s}\frac{w_i}{z_i}\Bigr)^{-1}\le\prod_{i\in s} z_i^{w_i}.
\]
The form with an arbitrary positive total weight normalizes both sides in the same way. This is proved for real values, as a corollary of weighted AM-GM.

Young’s inequality, for Hölder conjugates \(p\) and \(q\):
\[
ab\le\frac{|a|^p}{p}+\frac{|b|^q}{q}.
\]
For nonnegative \(a\) and \(b\), equality holds if and only if \(a^p=b^q\). The inequality is also stated for \(\mathbb{R}_{\ge 0}\) and \(\mathbb{R}_{\ge 0}\infty\).

## Hölder and Minkowski for finite sums

For a finite set and real functions, Hölder conjugates give
\[
\sum_{i\in s} f_i g_i\le\Bigl(\sum_{i\in s}|f_i|^p\Bigr)^{1/p}\Bigl(\sum_{i\in s}|g_i|^q\Bigr)^{1/q}.
\]
For a Hölder triple,
\[
\sum_{i\in s}|f_i g_i|^r\le\Bigl(\sum_{i\in s}|f_i|^p\Bigr)^{r/p}\Bigl(\sum_{i\in s}|g_i|^q\Bigr)^{r/q}.
\]
The same comparisons are proved for nonnegative and extended-nonnegative values. A weighted form, for \(p\ge 1\) and nonnegative weights and values, reads
\[
\sum_{i\in s} w_i f_i\le\Bigl(\sum_{i\in s} w_i\Bigr)^{1-1/p}\Bigl(\sum_{i\in s} w_i f_i^p\Bigr)^{1/p}.
\]
If the series of \(p\)-th and \(q\)-th powers are summable, the Hölder and Minkowski comparisons extend to the corresponding series.

Minkowski’s inequality, for \(p\ge 1\),
\[
\Bigl(\sum_{i\in s}|f_i+g_i|^p\Bigr)^{1/p}\le\Bigl(\sum_{i\in s}|f_i|^p\Bigr)^{1/p}+\Bigl(\sum_{i\in s}|g_i|^p\Bigr)^{1/p},
\]
is deduced from the fact that the \(\ell^p\) norm is the maximum of the pairing against vectors of conjugate norm at most \(1\). For the same range of \(p\),
\[
\Bigl(\sum_{i\in s}|f_i|\Bigr)^p\le(\#s)^{p-1}\sum_{i\in s}|f_i|^p.
\]
The integral forms of Hölder and Minkowski, and the triangle inequality in \(L^p\), are recorded in `Mathlib04.md`.

## Power means

For nonnegative weights summing to \(1\), a nonnegative function \(z\), and a natural number \(n\),
\[
\Bigl(\sum_{i\in s} w_i z_i\Bigr)^n\le\sum_{i\in s} w_i z_i^n.
\]
An even natural exponent drops the sign hypothesis on \(z\), by even-power convexity on \(\mathbb{R}\). Integer exponents require \(z>0\). For a real exponent \(p\ge 1\) the same weighted inequality holds, together with
\[
\sum_{i\in s} w_i z_i\le\Bigl(\sum_{i\in s} w_i z_i^p\Bigr)^{1/p}.
\]
These are the cases of the weighted power-mean comparison in which the smaller exponent is \(1\). The files record the comparison for a general pair of exponents, including negative exponents, and the convergence of the power mean to the geometric mean, as future work (`Analysis/MeanInequalitiesPow.lean`).

For two nonnegative numbers and \(0<p\le q\),
\[
(a^q+b^q)^{1/q}\le(a^p+b^p)^{1/p}.
\]
For \(p\ge 1\), \(a^p+b^p\le(a+b)^p\) and \((a+b)^p\le 2^{p-1}(a^p+b^p)\). For \(0\le p\le 1\) the first of these reverses: \((a+b)^p\le a^p+b^p\). The extended-nonnegative constant `LpAddConst` equals \(1\) for exponent \(0\) or at least \(1\), and equals \(2^{1/p-1}\) on \((0,1)\); it is the constant in the corresponding quasi-triangle inequality.

## Chebyshev and Abel

On a linear strict ordered semiring in which \(a\le b\) yields some \(c\) with \(a+c=b\), functions that monovary on a finite set satisfy
\[
\Bigl(\sum_{i\in s} f_i\Bigr)\Bigl(\sum_{i\in s} g_i\Bigr)\le(\#s)\sum_{i\in s} f_i g_i,
\]
and antivarying functions satisfy the reverse inequality. The scalar form, with values in an ordered cancellative module and a positive-scalar action, is the statement actually proved; multiplication is the special case. A function monovaries with itself, so
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
\sum_{i<n} f_i g_i\le\sum_{i<n} c_i g_i.
\]
If every partial sum of \(f\) is at most \(M\), the weighted sum is at most \(M\,g_0\); the empty partial sum forces \(M\ge 0\). If every partial sum is at least \(m\), then \(m\,g_0\) is a lower bound and \(m\le 0\). In a linear ordered ring, a uniform bound \(M\) on the absolute values of the partial sums yields \(\bigl|\sum_{i<n} f_i g_i\bigr|\le M\,g_0\).

## Rearrangement

In the same ordered-module setting, if \(f\) and \(g\) monovary on \(s\) and a permutation \(\sigma\) moves only points of \(s\), then
\[
\sum_{i\in s} f_i\cdot g_{\sigma i}\le\sum_{i\in s} f_i g_i.
\]
If they antivary, the inequality reverses, so the sum is minimized by an antivarying rearrangement. Under a strictly positive scalar action, equality holds if and only if \(g\circ\sigma\) still monovaries with \(f\), or still antivaries with \(f\) in the dual case, and the inequality is strict precisely when that fails. The multiplication form is included. The equality criterion for an injective rearranged sequence is recorded as future work (`Algebra/Order/Rearrangement.lean`).

## Jensen

Over a field that is a strict ordered ring, and an ordered module over that field, a convex function on a convex set satisfies
\[
f\Bigl(\sum_{i\in t} w_i\cdot p_i\Bigr)\le\sum_{i\in t} w_i\cdot f(p_i)
\]
whenever the weights are nonnegative and sum to \(1\) and the points lie in the set. If the total weight is merely positive, the same comparison holds for centers of mass. Concave functions reverse the inequality. For a strictly convex function and strictly positive weights, the inequality is strict unless the points are constant, and equality holds if and only if every point equals the center of mass. For nonnegative weights, equality holds if and only if the points of nonzero weight all equal the center of mass. The strict inequality holds if and only if some point differs from the center of mass. The concave statements are dual (`Analysis/Convex/Jensen.lean`).

A convex function on the convex hull of a set attains its maximum on that set: the value at a point of the hull is at most the value at some point of the set. On a segment, and on a real interval, the maximum is attained at an endpoint. Concave functions have the corresponding minimum principles.

The integral form needs a complete normed real space. If \(g\) is continuous and convex on a closed convex set, \(\mu\) is a finite nonzero measure, \(f\) and \(g\circ f\) are integrable, and \(f\) takes values in the set almost everywhere, then
\[
g\Bigl(\fint f\,d\mu\Bigr)\le\fint (g\circ f)\,d\mu.
\]
On a probability space the averages may be written as integrals. The same comparison holds for the average over a subset of positive finite measure. If \(g\) is strictly convex, either \(f\) equals its average almost everywhere or the inequality is strict. If the set itself is strictly convex and closed, an integrable function valued almost everywhere in the set is either almost everywhere equal to its average or has average in the interior. In a complete strictly convex normed space, a function with \(\|f(x)\|\le C\) almost everywhere is either almost everywhere equal to its average or satisfies \(\|\fint f\|<C\) (`Analysis/Convex/Integral.lean`). Continuity of convex functions, gauges, and the extreme-point theory are in Section 12.

## Doubly stochastic matrices and Birkhoff

A square matrix over an ordered semiring is doubly stochastic when its entries are nonnegative and every row sum and every column sum equals \(1\). The set of such matrices is convex, and every permutation matrix is doubly stochastic (`Analysis/Convex/DoublyStochasticMatrix.lean`).

Birkhoff’s theorem, over a linear ordered field and a finite index: the doubly stochastic matrices are exactly the convex hull of the permutation matrices, their extreme points are exactly the permutation matrices, and every doubly stochastic matrix is a convex combination of permutation matrices (`Analysis/Convex/Birkhoff.lean`). A real doubly stochastic matrix has \(\ell^2\) operator norm at most \(1\).

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

An operator version of the arithmetic–geometric mean inequality is proved for positive elements in the continuous-functional-calculus setting: the geometric mean satisfies \(2(a\#b)\le a+b\) for strictly positive \(a\) and nonnegative \(b\) ([geometric mean](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/GeometricMean.lean); see Section 13 for its construction).

There is also a specific majorization rigidity lemma for an antitone integer sequence: prefix sums bounded by those of the finite staircase, equality of the total sum, and equality of a specified quadratic statistic force the sequence to equal the staircase ([staircase criterion](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Combinatorics/Majorization.lean)). This is a proved special-purpose lemma, not a general vector-majorization theory or Karamata's inequality.

## Topics of Section 11 not found in either inspected library

- The weighted power-mean comparison for a general pair of exponents \(p\le q\), including negative exponents, and the convergence of power means to the geometric mean. Both are marked as future work in `Analysis/MeanInequalities.lean` and `Analysis/MeanInequalitiesPow.lean`. The case of smaller exponent \(1\), and the two-point comparison for \(0<p\le q\), are proved.
- Equality criteria for every classical inequality in those files. Equality is proved for weighted AM-GM, for Young’s inequality on nonnegative numbers, for strictly convex and strictly concave Jensen, and for rearrangement under a strictly positive scalar action.
- The rearrangement equality criterion restricted to injective permutations. It is a TODO in `Algebra/Order/Rearrangement.lean`.
- Karamata’s inequality, Muirhead’s inequality, Maclaurin’s inequality, and Schur-concavity.
- Majorization of vectors. Birkhoff’s file asks for the equivalence between majorization of \(x\) by \(y\) and the existence of a doubly stochastic matrix \(M\) with \(M y=x\), and leaves it unproved.
- Schur–Horn. The eigenvalue ordering in `Analysis/InnerProductSpace/Spectrum.lean` mentions it as motivation.
