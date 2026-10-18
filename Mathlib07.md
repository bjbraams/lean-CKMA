# 7. Concentration, high-dimensional probability, and empirical processes

Checked against Mathlib commit `f039e1b8a616d45782a5c7fc5e7909249c36b8ea` (2026-10-18, Lean `v4.36.0-rc1`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. The roots for this section are `Mathlib.Probability.Moments.SubGaussian`, `Mathlib.Probability.Moments.Basic`, `Mathlib.Probability.Distributions.Gaussian.Fernique`, and `Mathlib.Topology.MetricSpace.CoveringNumbers`.

**Namespaces.** `ProbabilityTheory`, with the sub-Gaussian predicate `HasSubgaussianMGF` and its kernel form `Kernel.HasSubgaussianMGF`. Covering and packing numbers are `Metric.externalCoveringNumber`, `Metric.coveringNumber`, and `Metric.packingNumber`.

This note records the part of high-dimensional probability that the library has formalized: sub-Gaussian bounds, Hoeffding and Azuma–Hoeffding inequalities, Fernique’s integrability theorem, and covering and packing numbers. Chaining lemmas are present as ingredients, but no chaining bound, and the analytic theory of empirical processes was not found.

## Sub-Gaussian moment-generating functions

A real random variable has a sub-Gaussian moment-generating function with parameter \(c\geq 0\) when \(e^{tX}\) is integrable for every real \(t\) and
\[
\mathbb{E}[e^{tX}]\leq\exp(c\,t^2/2).
\]
The comparison function is the moment-generating function of a centered Gaussian of variance \(c\). The bound forces \(\mathbb{E}[X]=0\) (`Probability/Moments/SubGaussian.lean`).

The same bound is available conditionally. On a standard Borel space with a finite measure, \(X\) is conditionally sub-Gaussian given a sub-σ-algebra when the bound holds for the conditional moment-generating function, expressed through the conditional-expectation kernel. For independent variables, the parameters add. Without independence the proved bound for two variables uses \((\sqrt{c_X}+\sqrt{c_Y})^2\), rather than \(c_X+c_Y\).

Vershynin’s five formulations — a sub-Gaussian tail, a growth bound on \(L^p\) norms, two Orlicz-type exponential moments, and the moment-generating bound above — are discussed in that file. The moment-generating bound is the definition that is formalized. Two implications from it are proved: the Gaussian tail bound below (`HasSubgaussianMGF.measure_ge_le`) and membership of \(X\) in every \(L^p\) (`HasSubgaussianMGF.memLp`). The file leaves the other four definitions, the \(\psi_2\) Orlicz norm, and the comparison constants between the conditions as a TODO.

## Hoeffding and Azuma–Hoeffding inequalities

The same file proves the sub-Gaussian tail estimate
\[
\mathbb P(X\ge r)\le \exp(-r^2/(2c))\qquad(r\ge0,\ c>0).
\]
For independent sub-Gaussian variables \(X_i\), the sum has parameter \(\sum_i c_i\), giving the corresponding bound for its upper tail (`HasSubgaussianMGF.measure_ge_le`, `sum_of_iIndepFun`, `measure_sum_ge_le_of_iIndepFun`). Applying the estimate to the negatives gives lower-tail bounds.

Hoeffding’s lemma is proved: if \(X\in[a,b]\) almost surely on a probability space, then \(X-\mathbb E X\) is sub-Gaussian with parameter \((b-a)^2/4\) (`hasSubgaussianMGF_of_mem_Icc`). Consequently independent bounded summands satisfy Hoeffding’s inequality, with upper-tail bound \(\exp(-2r^2/\sum_i(b_i-a_i)^2)\) when the denominator is positive.

There is also an Azuma–Hoeffding estimate for adapted sums on a standard Borel probability space. If the initial summand is sub-Gaussian and each subsequent summand is conditionally sub-Gaussian given the preceding σ-algebra, the parameters add and the same exponential tail estimate holds (`sum_of_hasCondSubgaussianMGF`, `measure_sum_ge_le_of_hasCondSubgaussianMGF`). Thus martingale concentration is present, although a broader concentration-of-measure theory is not.

## Chernoff’s bound and Fernique’s theorem

On a finite measure, if \(t\geq 0\) and \(e^{tX}\) is integrable, the upper tail satisfies
\[
\mu\{X\geq\varepsilon\}\leq\exp(-t\varepsilon+\operatorname{cgf}_X(t)),
\]
where \(\operatorname{cgf}_X\) is the cumulant-generating function. For \(t\leq 0\) the same expression bounds the lower tail \(\mu\{X\leq\varepsilon\}\) (`Probability/Moments/Basic.lean`). This is the estimate one feeds with a sub-Gaussian moment-generating function.

Fernique’s theorem supplies the Gaussian case of a square-exponential tail. For a Gaussian measure on a second-countable normed space there exists \(C>0\) such that \(\exp(C\|x\|^2)\) is integrable, and on a second-countable Banach space every moment is finite (`Probability/Distributions/Gaussian/Fernique.lean`). The Gaussian measures themselves are described in `Mathlib06.md`.

## Covering and packing numbers

In a pseudo-metric space, the external covering number of a set \(A\) at scale \(\varepsilon\) is the least cardinality of an \(\varepsilon\)-cover of \(A\) by closed balls. The internal covering number requires the centers to lie in \(A\). The packing number is the greatest cardinality of an \(\varepsilon\)-separated subset of \(A\). Finite minimal covers and maximal separated sets are constructed when the cardinalities are finite (`Topology/MetricSpace/CoveringNumbers.lean`).

The comparisons proved there are the standard ones. The external covering number is at most the internal covering number. The packing number at scale \(2\varepsilon\) is at most the external covering number at scale \(\varepsilon\). The internal covering number is at most the packing number, and the internal covering number at scale \(2\varepsilon\) is at most the external covering number at scale \(\varepsilon\). Internal covering numbers are not monotone under inclusion; if \(A\subseteq B\), the covering number of \(A\) at scale \(\varepsilon\) is at most the covering number of \(B\) at scale \(\varepsilon/2\).

Two chaining ingredients, introduced for the Kolmogorov–Chentsov theorem, are also present. A set has covering exponent \(d\) with constant \(c\) when it has finite diameter and its covering number at every scale \(\varepsilon\le\operatorname{diam}\) is at most \(c\,\varepsilon^{-d}\); the property passes to subsets with constant \(2^dc\) (`Topology/MetricSpace/CoveringExponent.lean`). The pair-reduction lemma, an extension by Krätschmer and Urusov of a lemma in Talagrand's *Upper and Lower Bounds for Stochastic Processes*, is proved: for a finite set \(J\) with \(|J|\le a^n\) there is a set \(K\) of at most \(a|J|\) pairs at distance at most \(cn\), such that for every function \(f\), the supremum of \(d(f(s),f(t))\) over pairs in \(J\) at distance at most \(c\) is bounded by twice its supremum over \(K\) (`EMetric.pair_reduction` in `Topology/EMetricSpace/PairReduction.lean`). No chaining bound for the supremum of a process is assembled from these ingredients in this revision.

## Combinatorial VC theory

Shattering and VC dimension of finite set families are defined in `Combinatorics/SetFamily/Shatter.lean`. The Sauer–Shelah bound is proved: a family on an \(n\)-element ground set with VC dimension \(d\) has at most \(\sum_{k=0}^d\binom nk\) members. `Combinatorics/SetFamily/DualVC.lean` also proves Assouad’s bound \(\operatorname{VCdim}(\mathcal A^*)\le 2^{d+1}-1\). These are combinatorial ingredients for empirical-process theory; uniform laws of large numbers for VC classes are not developed here.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6ebb29f84b4d`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

McDiarmid's bounded-differences theorem is proved for measurable functions on a finite product of copies of a probability space. If changing coordinate \(i\) changes \(f\) by at most \(c_i\), the centred function has the sub-Gaussian moment-generating bound with parameter \(\sum_i c_i^2/4\). Combined with the sub-Gaussian tail theorem this gives the usual upper-tail estimate \(\exp(-2r^2/\sum_i c_i^2)\) when the denominator is positive ([McDiarmid](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Probability/McDiarmid.lean)). This includes bounded-difference functions on finite product spaces such as the discrete cube, beyond the sum estimates in Mathlib.

The Prékopa–Leindler inequality is proved: if \(0\le\theta\le1\) and measurable \(f,g,h\ge0\) satisfy \(h((1-\theta)x+\theta y)\ge f(x)^{1-\theta}g(y)^\theta\), then \(\int h\ge(\int f)^{1-\theta}(\int g)^\theta\), for Lebesgue measure on \(\mathbb{R}^n\) and on finite-dimensional real inner product spaces; the property tensorizes over products and is transported by measure-preserving affine maps ([Prékopa–Leindler](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/MeasureTheory/Integral/PrekopaLeindler.lean), `TauCeti.hasPrekopaLeindler_volume`). The Brunn–Minkowski inequality \(|A+B|^{1/n}\ge|A|^{1/n}+|B|^{1/n}\) follows, for Lebesgue-measurable \(A,B\) and outer measure of the sum, with the multiplicative and weighted forms ([Brunn–Minkowski](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Basic.lean)). No Gaussian isoperimetric or functional inequality is derived from them.

For random matrices, an entrywise Chebyshev and union bound gives \(\mu\{\exists k,l:\ |S_{kl}-A_{kl}|>\eta\}\le mnv/\eta^2\) when every entry deviation has second moment at most \(v\), and this is transferred to simultaneous control of the sorted eigenvalues and of the operator norm of \(S-A\), with dimension factors ([matrix concentration](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Probability/Moments/MatrixConcentration.lean)). These are polynomial, not exponential, bounds. For a centred multivariate Gaussian with covariance \(S\) and a symmetric \(\Theta\), the quadratic form \(\langle x,\Theta x\rangle\) has a finite moment-generating function at \(t\) exactly when \(1-2t\sqrt S\Theta\sqrt S\) is positive definite, and there it equals \(\det(1-2t\sqrt S\Theta\sqrt S)^{-1/2}\) ([Gaussian quadratic forms](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Probability/Distributions/Gaussian/QuadraticForm.lean)). Empirical measures of finite samples are defined, with their integration and measurability API, but no uniform deviation bound is proved for them ([empirical measures](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Probability/Process/EmpiricalMeasure.lean)).

The Wasserstein and Kantorovich–Rubinstein developments in Section 39 add the transport distance and its Lipschitz dual formula. A transportation-cost concentration inequality, a logarithmic Sobolev inequality, or a generic-chaining theorem was not located. The Wishart laws recorded in Section 6 are exact finite-dimensional distributions of Gaussian Gram matrices; no asymptotic random-matrix theorem accompanies them.

## Topics of Section 7 not found in either inspected library

- The \(\psi_2\) Orlicz norm and the remaining implications among Vershynin’s five sub-Gaussian conditions. Only the moment-generating bound is defined, with its consequences the Gaussian tail bound and finiteness of all moments.
- Concentration on the sphere and Gaussian isoperimetry (Borell, Sudakov–Tsirelson), and product-space concentration beyond the sub-Gaussian, bounded-sum, conditional-sum, and McDiarmid bounded-difference estimates recorded here.
- Logarithmic Sobolev inequalities, hypercontractivity, and the Herbst argument. The Gaussian Hermite basis and its Parseval identity are in TauCeti, but no entropy inequality.
- Generic chaining, Dudley’s entropy integral, and the majorizing-measure theorem. Covering and packing numbers, covering exponents, and Talagrand's pair-reduction lemma are present, and no chaining inequality for the supremum of a process was found.
- Bernstein's inequality and sub-exponential variables, Hanson–Wright inequality for quadratic forms, and the Paley–Zygmund inequality. Exact moment-generating functions of Gaussian quadratic forms are in TauCeti.
- Random matrix theory: Wigner's semicircle law, the Marchenko–Pastur law, exponential (matrix Bernstein or Chernoff) and sharp norm bounds for random matrices, and the orthogonal-polynomial and Riemann–Hilbert methods of Mehta and Deift. TauCeti has only the entrywise Chebyshev bounds and exact Wishart laws recorded above.
- Asymptotic geometric analysis: Dvoretzky's theorem and the Johnson–Lindenstrauss lemma.
- Symmetrization and Rademacher complexity, empirical-process bounds for VC classes, and Glivenko–Cantelli or Donsker theorems. Combinatorial VC dimension and Sauer–Shelah are present, and TauCeti defines empirical measures.
- Transportation-cost methods for concentration. Conditional sub-Gaussian sums and Azuma–Hoeffding are present.
