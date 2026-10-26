# Structure 07: Concentration, high-dimensional probability, and empirical processes

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS07.md); [bibliographical scope](CKMA-bib.md#ckma-07); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; the **Synopsis entries** line at the end of each section states which numbered results are covered.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Probability.Moments.SubGaussian`, `Mathlib.Probability.Moments.Basic`, `Mathlib.Probability.Distributions.Gaussian.Fernique`, `Mathlib.Topology.MetricSpace.CoveringNumbers`, `Mathlib.Topology.MetricSpace.CoveringExponent`, `Mathlib.Topology.EMetricSpace.PairReduction`, `Mathlib.Combinatorics.SetFamily.Shatter`, `Mathlib.Combinatorics.SetFamily.DualVC`, `Mathlib.MeasureTheory.Measure.ResolventTransform`.

**Namespaces.** `ProbabilityTheory`, with the sub-Gaussian predicate `HasSubgaussianMGF` and its kernel form `Kernel.HasSubgaussianMGF`. Covering and packing numbers are `Metric.externalCoveringNumber`, `Metric.coveringNumber`, and `Metric.packingNumber`. Shattering and VC dimension are in `Finset`. TauCeti declarations are in `TauCeti` and `TauCeti.Probability`.

<a id="structure-07a"></a>

## 07A. Concentration, Empirical Processes, and High-Dimensional Geometry

Sub-Gaussian moment bounds, concentration estimates, metric covering numbers, and finite-sample constructions are grouped in this subdivision.

### Exponential moments and scalar deviations

[Mathematical scope](SYNOPSIS07.md#exponential-moments-and-scalar-deviations).

#### Mathlib

**Chernoff’s bound.** On a finite measure, if \(t\geq 0\) and \(e^{tX}\) is integrable, the upper tail satisfies
\[
\mu\{X\geq\varepsilon\}\leq\exp(-t\varepsilon+\mathop{\mathrm{cgf}}\nolimits_X(t)),
\]
where \(\mathop{\mathrm{cgf}}_X\) is the cumulant-generating function. For \(t\leq 0\) the same expression bounds the lower tail \(\mu\{X\leq\varepsilon\}\) (`measure_ge_le_exp_cgf`, `measure_le_le_exp_cgf`, `Probability/Moments/Basic.lean`). For independent variables the moment-generating functions multiply and the cumulant-generating functions add (`IndepFun.cgf_add`, `iIndepFun.cgf_sum`). Taking the infimum over \(t\) is immediate.

**Sub-Gaussian moment-generating functions.** A real random variable has a sub-Gaussian moment-generating function with parameter \(c\geq 0\) when \(e^{tX}\) is integrable for every real \(t\) and
\[
\mathbb{E}[e^{tX}]\leq\exp(c\,t^2/2).
\]
The comparison function is the moment-generating function of a centered Gaussian of variance \(c\). The bound forces \(\mathbb{E}[X]=0\) (`Probability/Moments/SubGaussian.lean`).

The same bound is available conditionally. On a standard Borel space with a finite measure, \(X\) is conditionally sub-Gaussian given a sub-σ-algebra when the bound holds for the conditional moment-generating function, expressed through the conditional-expectation kernel. For independent variables, the parameters add. Without independence the proved bound for two variables uses \((\sqrt{c_X}+\sqrt{c_Y})^2\), rather than \(c_X+c_Y\).

The moment-generating bound is the definition that is formalized. Two implications from it are proved: the Gaussian tail bound below (`HasSubgaussianMGF.measure_ge_le`) and membership of \(X\) in every \(L^p\) (`HasSubgaussianMGF.memLp`). The \(\psi_2\) Orlicz norm and the converse implications are listed in the source as future work.

**Hoeffding inequalities.** The same file proves the sub-Gaussian tail estimate
\[
\mathbb P(X\ge r)\le \exp(-r^2/(2c))\qquad(r\ge0,\ c>0).
\]
For independent sub-Gaussian variables \(X_i\), the sum has parameter \(\sum_i c_i\), giving the corresponding bound for its upper tail (`HasSubgaussianMGF.measure_ge_le`, `sum_of_iIndepFun`, `measure_sum_ge_le_of_iIndepFun`). Applying the estimate to the negatives gives lower-tail bounds, and hence the two-sided bound with a factor \(2\). Since \(\mathbb{E}e^{taX}=\mathbb{E}e^{(at)X}\), a multiple \(aX\) has parameter \(a^2c\) directly from the definition.

Hoeffding’s lemma is proved: if \(X\in[a,b]\) almost surely on a probability space, then \(X-\mathbb E X\) is sub-Gaussian with parameter \((b-a)^2/4\) (`hasSubgaussianMGF_of_mem_Icc`, `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`). Consequently independent bounded summands satisfy Hoeffding’s inequality, with upper-tail bound \(\exp(-2r^2/\sum_i(b_i-a_i)^2)\) when the denominator is positive.

**Fernique’s theorem.** Fernique’s theorem supplies the Gaussian case of a square-exponential tail. For a Gaussian measure on a second-countable normed space there exists \(C>0\) such that \(\exp(C\|x\|^2)\) is integrable, and on a second-countable Banach space every moment is finite (`Probability/Distributions/Gaussian/Fernique.lean`). The Gaussian measures themselves are described in [Section 06](STRUCTURE06.md).

**Synopsis entries.** Covered: 07.1–07.3, 07.7 (Mathlib). Partly covered: 07.6 (the moment-generating bound implies the tail bound and finiteness of all moments; Orlicz norms and the converses are absent). Not covered: 07.4, 07.5, 07.8–07.11, 07.63, 07.64.

### Product spaces, entropy, and geometric concentration

[Mathematical scope](SYNOPSIS07.md#product-spaces-entropy-and-geometric-concentration).

#### Mathlib

Azuma–Hoeffding estimate for adapted sums on a standard Borel probability space: if the initial summand is sub-Gaussian and each subsequent summand is conditionally sub-Gaussian given the preceding σ-algebra, the parameters add and the same exponential tail estimate holds (`HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF`, `measure_sum_ge_le_of_hasCondSubgaussianMGF`, `Probability/Moments/SubGaussian.lean`). A conditional Hoeffding lemma, which would turn bounded martingale differences into this hypothesis, is not stated.

#### TauCeti

McDiarmid's bounded-differences theorem is proved for measurable functions on a finite product of copies of a probability space. If changing coordinate \(i\) changes \(f\) by at most \(c_i\), the centred function has the sub-Gaussian moment-generating bound with parameter \(\sum_i c_i^2/4\). Combined with the sub-Gaussian tail theorem this gives the usual upper-tail estimate \(\exp(-2r^2/\sum_i c_i^2)\) when the denominator is positive, and the two-sided bound by symmetry ([McDiarmid](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/McDiarmid.lean), `TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences`). This includes bounded-difference functions on finite product spaces such as the discrete cube, beyond the sum estimates in Mathlib.

The Prékopa–Leindler inequality is proved: if \(0\le\theta\le1\) and measurable \(f,g,h\ge0\) satisfy \(h((1-\theta)x+\theta y)\ge f(x)^{1-\theta}g(y)^\theta\), then \(\int h\ge(\int f)^{1-\theta}(\int g)^\theta\), for Lebesgue measure on \(\mathbb{R}^n\) and on finite-dimensional real inner product spaces; the property tensorizes over products and is transported by measure-preserving affine maps ([Prékopa–Leindler](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/PrekopaLeindler.lean), `TauCeti.hasPrekopaLeindler_volume`). The Brunn–Minkowski inequality \(|A+B|^{1/n}\ge|A|^{1/n}+|B|^{1/n}\) follows, for Lebesgue-measurable \(A,B\) and outer measure of the sum, with the multiplicative and weighted forms ([Brunn–Minkowski](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Basic.lean)). No Gaussian isoperimetric, Poincaré, or logarithmic Sobolev inequality is derived from them.

**Synopsis entries.** Covered: 07.13 (TauCeti). Partly covered: 07.12 (conditionally sub-Gaussian increments; the bounded-difference hypothesis needs a conditional Hoeffding lemma that is not stated). Not covered: 07.53, 07.14–07.17, 07.19, 07.20, 07.22, 07.24.

### Further concentration, hypercontractivity, and Gaussian comparison

[Mathematical scope](SYNOPSIS07.md#further-concentration-hypercontractivity-and-gaussian-comparison).

The normalized Hermite polynomials form a Hilbert basis of \(L^2\) of the standard Gaussian in TauCeti, with the Parseval expansion ([Hermite basis](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Distributions/Gaussian/Hermite/Parseval.lean)); this is the nearest supporting material, and no hypercontractive estimate is stated.

**Synopsis entries.** Not covered: 07.55–07.57.

### Metric entropy, Gaussian comparison, and chaining

[Mathematical scope](SYNOPSIS07.md#metric-entropy-gaussian-comparison-and-chaining).

#### Mathlib

**Covering and packing numbers.** In a pseudo-metric space, the external covering number of a set \(A\) at scale \(\varepsilon\) is the least cardinality of an \(\varepsilon\)-cover of \(A\) by closed balls. The internal covering number requires the centers to lie in \(A\). The packing number is the greatest cardinality of an \(\varepsilon\)-separated subset of \(A\). Finite minimal covers and maximal separated sets are constructed when the cardinalities are finite (`Topology/MetricSpace/CoveringNumbers.lean`).

The comparisons proved there are the standard ones. The external covering number is at most the internal covering number. The packing number at scale \(2\varepsilon\) is at most the external covering number at scale \(\varepsilon\). The internal covering number is at most the packing number, and the internal covering number at scale \(2\varepsilon\) is at most the external covering number at scale \(\varepsilon\). Internal covering numbers are not monotone under inclusion; if \(A\subseteq B\), the covering number of \(A\) at scale \(\varepsilon\) is at most the covering number of \(B\) at scale \(\varepsilon/2\). The volumetric bound for balls in finite-dimensional spaces is not stated.

Two chaining ingredients, introduced for the Kolmogorov–Chentsov theorem, are also present. A set has covering exponent \(d\) with constant \(c\) when it has finite diameter and its covering number at every scale \(\varepsilon\le\mathop{\mathrm{diam}}\) is at most \(c\,\varepsilon^{-d}\); the property passes to subsets with constant \(2^dc\) (`Topology/MetricSpace/CoveringExponent.lean`). The pair-reduction lemma, an extension by Krätschmer and Urusov of a lemma in Talagrand's *Upper and Lower Bounds for Stochastic Processes*, is proved: for a finite set \(J\) with \(|J|\le a^n\) there is a set \(K\) of at most \(a|J|\) pairs at distance at most \(cn\), such that for every function \(f\), the supremum of \(d(f(s),f(t))\) over pairs in \(J\) at distance at most \(c\) is bounded by twice its supremum over \(K\) (`EMetric.pair_reduction` in `Topology/EMetricSpace/PairReduction.lean`). No chaining bound for the supremum of a process is stated.

**Synopsis entries.** Not covered: 07.25–07.32, 07.58, 07.61.

### Empirical processes, combinatorial dimension, and uniform laws

[Mathematical scope](SYNOPSIS07.md#empirical-processes-combinatorial-dimension-and-uniform-laws).

#### Mathlib

Shattering and VC dimension of finite set families are defined in `Combinatorics/SetFamily/Shatter.lean`. The Sauer–Shelah bound is proved: a family on an \(n\)-element ground set with VC dimension \(d\) has at most \(\sum_{k=0}^d\binom nk\) members (`Finset.card_le_card_shatterer`, `Finset.card_shatterer_le_sum_vcDim`). Applied to the traces of a set class on \(n\) points this is the synopsis bound; the estimate \((en/v)^v\) is not stated. `Combinatorics/SetFamily/DualVC.lean` also proves Assouad’s bound \(\mathop{\mathrm{VCdim}}(\mathcal A^*)\le 2^{d+1}-1\) (`vcDim_dualFamily_le`).

#### TauCeti

Empirical measures of finite samples are defined, with their integration and measurability API, but no uniform deviation bound is proved for them ([empirical measures](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Process/EmpiricalMeasure.lean)).

**Synopsis entries.** Covered: 07.35 (Mathlib). Not covered: 07.33, 07.34, 07.36–07.42.

### Matrix concentration and high-dimensional geometry

[Mathematical scope](SYNOPSIS07.md#matrix-concentration-and-high-dimensional-geometry).

#### TauCeti

For random matrices, an entrywise Chebyshev and union bound gives \(\mu\{\exists k,l:\ |S_{kl}-A_{kl}|>\eta\}\le mnv/\eta^2\) when every entry deviation has second moment at most \(v\), and this is transferred to simultaneous control of the sorted eigenvalues and of the operator norm of \(S-A\), with dimension factors ([matrix concentration](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Moments/MatrixConcentration.lean)). These are polynomial, not exponential, bounds. For a centred multivariate Gaussian with covariance \(S\) and a symmetric \(\Theta\), the quadratic form \(\langle x,\Theta x\rangle\) has a finite moment-generating function at \(t\) exactly when \(1-2t\sqrt S\Theta\sqrt S\) is positive definite, and there it equals \(\det(1-2t\sqrt S\Theta\sqrt S)^{-1/2}\) ([Gaussian quadratic forms](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Distributions/Gaussian/QuadraticForm.lean)). This is the exact Gaussian case behind the Hanson–Wright inequality, which is not stated.

The Wasserstein and Kantorovich–Rubinstein developments in Section 39 add the transport distance and its Lipschitz dual formula. The Wishart laws recorded in Section 6 are exact finite-dimensional distributions of Gaussian Gram matrices.

**Synopsis entries.** Not covered: 07.43, 07.65, 07.44–07.48, 07.54, 07.59, 07.60, 07.62.

<a id="structure-07b"></a>

## 07B. Random Matrix Theory

The finite-dimensional matrix ingredients are the entrywise second-moment bounds and Gaussian quadratic-form transforms recorded in 07A. The Wishart laws in [Section 06](STRUCTURE06.md) are exact laws of Gaussian Gram matrices; their role here is finite-dimensional distributional input. No asymptotic random-matrix theorem is stated in either library.

### Spectral laws and edges

[Mathematical scope](SYNOPSIS07.md#spectral-laws-and-edges).

The Stieltjes transform of a measure on \(\mathbb{R}\) is the case \(A=\mathbb{C}\) of Mathlib's resolvent transform, which is holomorphic off the support (`analyticOn_resolventTransform`, `MeasureTheory/Measure/ResolventTransform.lean`); this is supporting material for 07.66.

**Synopsis entries.** Not covered: 07.50–07.52, 07.66.

### Gaussian ensembles and determinantal structure

[Mathematical scope](SYNOPSIS07.md#gaussian-ensembles-and-determinantal-structure).

**Synopsis entries.** Not covered: 07.67–07.69.

### Non-Hermitian matrices

[Mathematical scope](SYNOPSIS07.md#non-hermitian-matrices).

**Synopsis entries.** Not covered: 07.70.
