# Structure 05: Differentiation and the fine structure of real functions

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS05.md); [bibliographical scope](CKMA-bib.md#ckma-05); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; the **Synopsis entries** line at the end of each section states which numbered results are covered.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Analysis.Calculus.Deriv`, `Mathlib.Analysis.Calculus.FDeriv`, `Mathlib.Analysis.Calculus.Taylor`, `Mathlib.Analysis.Calculus.TaylorIntegral`, `Mathlib.Analysis.Calculus.Darboux`, `Mathlib.Analysis.Calculus.Monotone`, `Mathlib.Analysis.Calculus.Rademacher`, `Mathlib.Analysis.Convex.Continuous`, `Mathlib.Analysis.BoundedVariation`, `Mathlib.Analysis.BoxIntegral`, `Mathlib.Topology.EMetricSpace.BoundedVariation`, `Mathlib.Topology.EMetricSpace.VariationOnFromTo`, `Mathlib.Topology.EMetricSpace.Lipschitz`, `Mathlib.Topology.MetricSpace.Lipschitz`, `Mathlib.Topology.UniformSpace.Dini`, `Mathlib.MeasureTheory.Function.AbsolutelyContinuous`, `Mathlib.MeasureTheory.Integral.IntervalIntegral`, `Mathlib.MeasureTheory.Integral.DivergenceTheorem`, `Mathlib.MeasureTheory.Covering`, `Mathlib.MeasureTheory.VectorMeasure.BoundedVariation`.

**Namespaces.** `LipschitzWith` and `LipschitzOnWith`; `eVariationOn` and `variationOnFromTo`; `BoundedVariationOn` and `LocallyBoundedVariationOn`; `AbsolutelyContinuousOnInterval`; `intervalIntegral`; `BoxIntegral`; `Vitali`, `VitaliFamily`, `Besicovitch`, and `IsUnifLocDoublingMeasure`. Monotonicity theorems are declared on `Monotone` and `MonotoneOn`. The one-variable derivative is `deriv` and `HasDerivAt`, and the Fréchet derivative is `fderiv` and `HasFDerivAt`. TauCeti declarations are mostly in `TauCeti`, with extensions of Mathlib namespaces such as `AbsolutelyContinuousOnInterval`, `LocallyLipschitzOn`, and `ConvexOn`.

## Classical derivatives and smooth maps

[Mathematical scope](SYNOPSIS05.md#classical-derivatives-and-smooth-maps).

### Mathlib

**Derivatives.** The derivative of a map from a normed field into a normed space is the element \(f'\) for which the increment is \(f'(y-x)\) up to a little-o error. The predicates record a derivative at a point, within a set, along a filter, and in the strict sense \(f(y)-f(z)=(y-z)\cdot f'+o(y-z)\) as \(y,z\to x\). If no derivative exists, the functional `deriv` returns zero (`Analysis/Calculus/Deriv/Basic.lean`). The Fréchet derivative of a map between normed spaces is a continuous linear map, again in the pointwise, restricted, and strict senses. The one-variable derivative coincides with the Fréchet derivative (`Analysis/Calculus/FDeriv/Basic.lean`).

**Taylor's theorem.** For a function of one real variable with values in a real normed space, Taylor's theorem is proved with the Peano remainder \(o(|h|^n)\) (`taylor_isLittleO`), with the Lagrange, Cauchy, and general mean-value remainders for real-valued functions, and with the integral remainder, including for absolutely continuous derivatives (`Analysis/Calculus/Taylor.lean`). In several variables, the formula with integral remainder
\[
f(x+y)=\sum_{k\le n}\frac1{k!}D^kf(x)[y^k]+\frac1{n!}\int_0^1(1-t)^nD^{n+1}f(x+ty)[y^{n+1}]\,dt
\]
holds when \(f\) is \(C^{n+1}\) at every point of the segment (`map_add_eq_sum_add_integral_iteratedFDeriv`, `Analysis/Calculus/TaylorIntegral.lean`). The multivariable Peano form for a \(C^k\) map is not stated.

**Easy cases of Sard's theorem.** A map that is differentiable on a set of Hausdorff dimension less than the dimension of the target has an image with dense complement; in particular a differentiable map into a space of larger dimension has a range with dense complement (`Topology/MetricSpace/HausdorffDimension.lean`). In equal dimensions, the image of the set where the Jacobian determinant vanishes has measure zero (`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` in `MeasureTheory/Function/Jacobian.lean`).

### TauCeti

TauCeti proves the Morse–Sard theorem with a non-sharp smoothness threshold: for a map between finite-dimensional real normed spaces that is \(C^k\) on an open set, with \(k\ge(\dim E)^2+1\), the image of the set of points where the derivative is not surjective has Haar measure zero, and the regular values are dense ([Morse–Sard](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/Sard/OutermostStratum.lean), `TauCeti.addHaar_image_criticalPoints_eq_zero`, `ContDiff.addHaar_image_criticalPoints_eq_zero`). The source states that the sharp threshold \(k>\max(n-m,0)\) is not reached. For differentiable maps the equal-dimension case and the case \(\dim E<\dim F\) are proved separately with first derivatives only (`Differentiable.addHaar_image_criticalPoints_eq_zero` in `TauCeti/Analysis/Calculus/Sard/EqualDimension.lean`; `Differentiable.addHaar_image_not_surjective_fderiv_eq_zero_of_finrank_lt_finrank` in `TauCeti/Analysis/Calculus/Sard/LowDimension.lean`), so Sard's theorem holds in the sharp form whenever \(n\le m\), and for \(C^\infty\) maps in all dimensions.

**Synopsis entries.** Partly covered: 05.2 (one-variable Peano and all remainders; several variables only with integral remainder for \(C^{k+1}\)), 05.5 (sharp for \(n\le m\) and for \(C^\infty\) maps; for \(n>m\) only with \(k\ge n^2+1\)).

## Derivatives as real functions: continuity, category, and Dini derivatives

[Mathematical scope](SYNOPSIS05.md#derivatives-as-real-functions-continuity-category-and-dini-derivatives).

### Mathlib

Darboux's theorem: the derivative of a function differentiable on an interval takes every intermediate value, so a derivative has the intermediate value property even when it is discontinuous (`Analysis/Calculus/Darboux.lean`). A derivative is the limit of difference quotients (`hasDerivAt_iff_tendsto_slope`, `hasDerivAt_iff_tendsto_slope_zero` in `Analysis/Calculus/Deriv/Slope.lean`); composing the quotients with increments tending to zero continuously in \(x\) exhibits the derivative on an open interval as a pointwise limit of continuous functions, so the Baire-class-one property is a short consequence, although no Baire-class predicate is defined.

A comparison principle of Dini type is proved: if \(f\) is continuous on \([a,b]\), \(f(a)\le B(a)\), and at every \(x\in[a,b)\) with \(f(x)=B(x)\) the lower right difference quotients of \(f\) stay below \(B'(x)\), then \(f\le B\) on \([a,b]\) (`image_le_of_liminf_slope_right_lt_deriv_boundary` in `Analysis/Calculus/MeanValue.lean`). This is supporting material; Dini derivatives are not defined, and no monotonicity criterion with a countable exceptional set is stated.

Dini's theorem on uniform convergence, a different result: if a monotone sequence of continuous functions on a compact set, with values in a normed lattice, converges pointwise to a continuous limit, then the convergence is uniform (`Topology/UniformSpace/Dini.lean`).

**Synopsis entries.** Covered: 05.6 (Mathlib). Partly covered: 05.7 (derivative as a limit of difference quotients; no Baire-class notion). Not covered: 05.8, 05.63, 05.9–05.11.

## Bounded variation and absolute continuity on the line

[Mathematical scope](SYNOPSIS05.md#bounded-variation-and-absolute-continuity-on-the-line).

### Mathlib

**Bounded variation.** The variation of \(f\) on a linearly ordered set \(s\), with values in an extended pseudo-metric space, is the supremum of sums of successive distances along finite increasing sequences in \(s\). The function has bounded variation on \(s\) when that supremum is finite, and locally bounded variation when the variation is finite on \(s\cap[a,b]\) for all endpoints \(a,b\in s\). Variation adds over adjacent compact intervals, and it is lower semicontinuous under pointwise convergence (`eVariationOn.lowerSemicontinuous`). A real-valued locally BV function on a subset of the line is a difference of two monotone functions (`LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn`). A BV function into a complete space has one-sided limits at every point (`BoundedVariationOn.exists_tendsto_left`, `BoundedVariationOn.exists_tendsto_right`). A Lipschitz function has locally bounded variation (`Topology/EMetricSpace/BoundedVariation.lean`). The signed variation function \(x\mapsto\operatorname{Var}(f;[a,x])\) is continuous exactly where \(f\) is, and a BV function on the whole order has at most countably many discontinuities (`variationOnFromTo.continuousAt_variationOnFromTo_iff`, `variationOnFromTo.countable_not_continuousAt`, `Topology/EMetricSpace/VariationOnFromTo.lean`).

**Monotone and BV functions are differentiable almost everywhere.** A monotone function \(f:\mathbb{R}\to\mathbb{R}\) is differentiable almost everywhere, and its derivative is almost everywhere the Radon–Nikodym derivative of its Stieltjes measure with respect to Lebesgue measure (`Monotone.ae_hasDerivAt`, `StieltjesFunction.ae_hasDerivAt`). On a set, a function monotone on that set is differentiable almost everywhere within the set (`Analysis/Calculus/Monotone.lean`). A function of bounded variation on an interval of \(\mathbb{R}\), with values in a finite-dimensional real vector space, is differentiable almost everywhere on that interval. A locally BV function on \(\mathbb{R}\) with finite-dimensional real values is differentiable almost everywhere. The same conclusion holds for a Lipschitz map from an interval, or from the line, into a finite-dimensional space (`Analysis/BoundedVariation.lean`). The derivative of a monotone function, of a BV function, and of an absolutely continuous function is interval-integrable. For a monotone function the integral of the derivative lies between \(0\) and \(f(b)-f(a)\) (`MonotoneOn.intervalIntegral_deriv_mem_uIcc`, `MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`). Termwise differentiation of series of monotone functions is not stated.

If \(f\) has bounded variation and takes values in a complete normed additive group, it induces a vector-valued Stieltjes measure. The measure of an interval is a difference of one-sided limits of \(f\). Its total variation is finite and is controlled by the variation of \(f\) (`MeasureTheory/VectorMeasure/BoundedVariation.lean`), with integration by parts formulas using left and right limits (`MeasureTheory/VectorMeasure/IntegrationByParts.lean`). This is the measure-valued derivative of a BV function, although it is not identified with the distributional derivative. With the Lebesgue decomposition of measures (Section 04), it supplies the ingredients of the decomposition of the derivative measure; the decomposition into absolutely continuous, jump, and singular continuous parts is not stated for BV functions.

**Absolute continuity and the fundamental theorem.** A function on a compact interval is absolutely continuous when, for every \(\varepsilon>0\), some \(\delta>0\) controls the sum of increments of \(f\) by \(\varepsilon\) whenever a finite collection of disjoint subintervals has total length less than \(\delta\). Absolutely continuous functions are uniformly continuous and have bounded variation. For real-valued functions they form an algebra (`AbsolutelyContinuousOnInterval.mul`); for finite-dimensional real values, bounded variation gives almost-everywhere differentiability. A Lipschitz function on the interval is absolutely continuous, a function Lipschitz on the range composed with an absolutely continuous function is absolutely continuous (`LipschitzOnWith.comp_absolutelyContinuousOnInterval`), and so is a \(C^1\) function on the interval. The indefinite integral of an integrable function is absolutely continuous (`IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`) (`MeasureTheory/Function/AbsolutelyContinuous.lean`).

If \(f:\mathbb{R}\to\mathbb{R}\) is absolutely continuous on the interval with endpoints \(a\) and \(b\), then
\[
\int_a^b f'(x)\,dx = f(b)-f(a).
\]
Integration by parts holds for two such functions (`MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`).

The first fundamental theorem, for a Banach-valued integrand: if \(f\) is locally integrable on \(\mathbb{R}\), then for almost every \(x\) and every basepoint \(c\),
\[
\frac{d}{dx}\int_c^x f = f(x).
\]
On a compact interval the same holds for almost every point of the interval (`MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean`). If \(f\) is continuous at an endpoint, the indefinite interval integral is differentiable there with derivative \(f\). A variant assumes a finite limit of \(f\) at the endpoint in place of continuity. Strict differentiability holds under the corresponding strict hypotheses (`MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`).

The second fundamental theorem, for a Banach-valued \(f\): if \(f\) is continuous on \([a,b]\), has a right derivative \(f'\) at every point of \((a,b)\), and \(f'\) is interval-integrable, then \(\int_a^b f' = f(b)-f(a)\). The same identity holds when \(f\) is differentiable at every point of the interval and the derivative is interval-integrable, and when the values at the endpoints are recovered as one-sided limits. Integration by parts and integration by substitution are deduced from this form (`MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`, `MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean`).

### TauCeti

The variation of an absolutely continuous curve in a pseudometric space on \([a,b]\) equals the integral of its metric derivative, and, in a finite-dimensional normed space, the integral of the norm of its derivative ([metric derivative](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Function/MetricDerivative/Variation.lean), `AbsolutelyContinuousOnInterval.eVariationOn_eq_lintegral_metricDerivative`, `AbsolutelyContinuousOnInterval.eVariationOn_eq_lintegral_enorm_deriv`). For real \(F\) this is \(\operatorname{Var}(F)=\int_a^b|F'|\); for a curve it is the length formula.

For a Lipschitz curve the Banach indicatrix formula holds: the variation on \([a,b]\) is the integral, against one-dimensional Hausdorff measure, of the number of preimages ([curves](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Function/AreaFormula/Curve.lean), `eVariationOn_eq_lintegral_encard`). The indicatrix theorem for an arbitrary continuous function is not stated.

Calculus along absolutely continuous curves: a map that is \(C^1\) near the trace of an absolutely continuous curve preserves absolute continuity ([composition](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Function/AbsolutelyContinuous/Comp.lean)); for a \(C^1\) function \(\varphi\), \(\int_a^b\varphi'(\gamma)\gamma'=\varphi(\gamma(b))-\varphi(\gamma(a))\), and integration by parts holds with almost-everywhere derivatives ([calculus](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean), `AbsolutelyContinuousOnInterval.integral_fderiv_apply_eq_sub`, `AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul_of_ae_hasDerivAt`). Change of variables by absolutely continuous monotone substitutions is also proved ([substitution](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousSubstitution/Basic.lean)).

An eventual bound on the total variations of a family of maps bounds the total variation of a pointwise limit by the liminf of the bounds ([variation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Topology/EMetricSpace/BoundedVariation.lean), `TauCeti.eVariationOn_le_liminf_of_eventually_le`). This is the lower-semicontinuity half of Helly's theorem; the selection theorem itself is not stated in either library.

**Synopsis entries.** Covered: 05.12 (Mathlib), 05.15 (Mathlib and TauCeti), 05.20 (Mathlib, with TauCeti for curves). Partly covered: 05.13 (almost-everywhere differentiability and the integral inequality; termwise differentiation absent), 05.14 (almost-everywhere differentiability, integrability of the derivative, and the vector Stieltjes measure; the inequality \(\int|F'|\le\operatorname{Var}F\) and the identification with the distributional derivative are not stated), 05.17 (the derivative of a monotone function is the density of its Stieltjes measure; the three-part decomposition is not assembled), 05.19 (lower semicontinuity of variation; the selection theorem is absent), 05.58 (length of absolutely continuous curves; the indicatrix formula for Lipschitz curves only). Not covered: 05.62, 05.16, 05.18.

## Coverings, maximal functions, and differentiation bases

[Mathematical scope](SYNOPSIS05.md#coverings-maximal-functions-and-differentiation-bases).

### Mathlib

The topological Vitali covering lemma extracts, from a family of balls of bounded radii in a metric space, a disjoint subfamily such that every ball of the original family is contained in the five-times enlargement of some selected ball (`Vitali.exists_disjoint_subfamily_covering_enlargement`, `Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall`). The measurable form, for a doubling measure and a fine family of closed balls (more generally closed sets occupying a definite fraction of a comparable ball), extracts a countable disjoint subfamily covering almost every point of an arbitrary set at which the family is fine (`Vitali.exists_disjoint_covering_ae`, `MeasureTheory/Covering/Vitali.lean`).

The Besicovitch covering theorem applies in a metric space that admits no satellite configuration of \(N+1\) balls, a condition satisfied by finite-dimensional real normed spaces. From any family of balls of bounded radii one can extract \(N\) disjoint subfamilies whose union covers every center. The measurable form covers almost every point by disjoint admissible balls, for any s-finite measure, and small closed balls form a Vitali family for every locally finite measure (`Besicovitch.exists_disjoint_closedBall_covering_ae`, `Besicovitch.vitaliFamily`, `MeasureTheory/Covering/Besicovitch.lean`).

Differentiation of measures along a Vitali family, on a second-countable metric space: for almost every point, as the sets of the family shrink to the point, the ratio of two measures tends to the Radon–Nikodym derivative. Almost every point of a measurable set is a density point along the family, and the average oscillation \(\frac1{\mu(B)}\int_B|f-f(x)|\,d\mu\) of a locally integrable function tends to zero (`VitaliFamily.ae_tendsto_rnDeriv`, `VitaliFamily.ae_tendsto_measure_inter_div`, `VitaliFamily.ae_tendsto_average_norm_sub`, `MeasureTheory/Covering/Differentiation.lean`). On finite-dimensional real normed spaces, for locally finite measures \(\mu,\rho\), \(\rho(\bar B(x,r))/\mu(\bar B(x,r))\to\frac{d\rho}{d\mu}(x)\) for \(\mu\)-almost every \(x\) (`Besicovitch.ae_tendsto_rnDeriv`), with the corresponding density theorem for arbitrary sets (`Besicovitch.ae_tendsto_measure_inter_div`). For a locally finite, uniformly locally doubling measure on a σ-compact metric space, in particular Lebesgue measure, the density and Lebesgue-point statements hold along closed balls \(\bar B(w_j,\delta_j)\) with \(x\in\bar B(w_j,K\delta_j)\), so sets of bounded eccentricity such as cubes are included (`IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div`, `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub`, `MeasureTheory/Covering/DensityTheorem.lean`).

Approximate continuity is not defined. Almost-everywhere approximate continuity of a finite measurable function follows in a few lines from the Lebesgue point and density theorems above, applied to a bounded reparametrization such as \(\arctan\circ f\), but it is not stated.

### TauCeti

The centred Hardy–Littlewood maximal function on a finite-dimensional real normed space with additive Haar measure is defined and shown to be lower semicontinuous and measurable. It satisfies the weak-type bound \(t\,\mu\{Mf>t\}\le4^n\int|f|\,d\mu\), the \(L^\infty\) bound, and the strong \((p,p)\) bound for \(1<p<\infty\) ([maximal function](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/MaximalFunction.lean), `TauCeti.mul_measure_lt_maximalFunction_le`, `TauCeti.maximalFunction_le_eLpNormEssSup`, `TauCeti.eLpNorm_maximalFunction_le`). The constant is \(4^n\), from Mathlib's covering lemma with fourfold enlargements, rather than \(3^n\).

A one-dimensional Lebesgue differentiation theorem for extended nonnegative densities with finite lower integral is also proved ([densities](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean), `TauCeti.ae_tendsto_setLIntegral_uIoc_div`). Dyadic cubes in \(\mathbb R^n\), their nesting, and the Lebesgue differentiation theorem along dyadic cubes are developed as supporting material for the Calderón–Zygmund decomposition ([dyadic cubes](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Measure/Lebesgue/DyadicCube.lean), `TauCeti.ae_tendsto_setLAverage_dyadicCube`); the Whitney decomposition of an open set is not stated.

**Synopsis entries.** Covered: 05.21–05.23, 05.27–05.29 (Mathlib), 05.25, 05.26 (TauCeti). Partly covered: 05.30 (a short consequence of the Lebesgue point theorem; not stated). Not covered: 05.24, 05.31, 05.65.

## Lipschitz functions and approximate differentiation

[Mathematical scope](SYNOPSIS05.md#lipschitz-functions-and-approximate-differentiation).

### Mathlib

A map between extended metric spaces is Lipschitz with constant \(K\geq 0\) when distances in the target are at most \(K\) times distances in the source. The inequality may be required only on a subset, and a map is locally Lipschitz when every point has a neighborhood on which some constant works (`Topology/EMetricSpace/Lipschitz.lean`, `Topology/MetricSpace/Lipschitz.lean`).

Lipschitz extension, in the McShane form: a real-valued map that is \(K\)-Lipschitz on a subset of a pseudometric space extends to a \(K\)-Lipschitz map on the whole space, by the infimal formula. The same holds coordinatewise for maps into \(\mathbb{R}^n\) with the sup norm, and for maps into any finite-dimensional real normed space with a constant multiplied by a factor depending only on the target (`LipschitzOnWith.extend_real`, `LipschitzOnWith.extend_pi` in `Topology/MetricSpace/Lipschitz.lean`; `LipschitzOnWith.extend_finite_dimension` in `Analysis/Normed/Module/FiniteDimension.lean`). Kirszbraun's extension with the same constant between Hilbert spaces is not stated.

Rademacher’s theorem: a Lipschitz map between finite-dimensional real vector spaces is differentiable almost everywhere for Lebesgue measure. A map that is Lipschitz on a set is differentiable almost everywhere within that set. The proof reduces to real-valued maps, uses almost-everywhere differentiability along lines from the one-variable BV theorem and Fubini, and then upgrades line derivatives to a Fréchet derivative by Morrey’s duality argument (`Analysis/Calculus/Rademacher.lean`). Where the derivative of a \(K\)-Lipschitz map exists, its norm is at most \(K\) (`norm_fderiv_le_of_lipschitz`, `Analysis/Calculus/FDeriv/Basic.lean`). A convex function on a convex set of a finite-dimensional space is locally Lipschitz on the interior (`ConvexOn.locallyLipschitzOn_interior`, `Analysis/Convex/Continuous.lean`).

### TauCeti

Rademacher's theorem is localized: a function locally Lipschitz on a set is differentiable within the set at almost every point of it, and differentiable at almost every point of an open set; a convex function is differentiable at almost every point of its convex domain ([Rademacher](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Calculus/Rademacher.lean), `LocallyLipschitzOn.ae_differentiableAt_of_mem`, `ConvexOn.ae_differentiableAt_of_mem`).

Alexandrov's theorem is proved: a convex function on a finite-dimensional real inner product space, possibly with values in the extended reals, has at almost every point of its effective domain a second-order Taylor expansion with a unique positive semidefinite symmetric Hessian, and its subdifferential is differentiable there ([Alexandrov](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Convex/Alexandrov.lean), `ConvexOn.ae_existsUnique_isPositive_isLittleO`). The distributional Hessian as a matrix of measures, and the identification of the Alexandrov Hessian with the density of its absolutely continuous part, are not stated.

Weak derivatives of Lipschitz functions: if \(u\) is locally Lipschitz on an open subset of a finite-dimensional space, its almost-everywhere Fréchet derivative is its weak derivative, with a local bound by the Lipschitz constant ([Lipschitz](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Sobolev/WeakDeriv/Lipschitz.lean), `LocallyLipschitzOn.hasWeakFDerivOn_fderiv`). Conversely, the precise representative of a function in \(W^{1,\infty}(\Omega)\) is Lipschitz on every compact subset of \(\Omega\) ([interior Morrey](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Sobolev/W1p/InteriorMorrey.lean), `TauCeti.W1p.exists_lipschitzOnWith_preciseRepresentative_of_isCompact`); the global constant \(\|\nabla f\|_\infty\) on a convex set is not stated. The same file proves local Hölder continuity of the precise representative for \(p>n\) (supporting for 05.39; almost-everywhere differentiability is not stated).

On an interval, a locally integrable \(u\) has weak derivative \(u'\) exactly when \(u\) is almost everywhere a constant plus the primitive of \(u'\), so \(W^{1,1}(a,b)\) consists of absolutely continuous functions ([interval](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Sobolev/WeakDeriv/Interval.lean)). This is the one-dimensional case of absolute continuity on lines; the several-variable characterization is not stated.

**Area formula (supporting; stated in Section 37).** For finite-dimensional real inner product spaces \(U,V\) with \(m=\dim U\), and \(J f=\) the \(m\)-dimensional Jacobian \(\sqrt{\det(Df^*Df)}\), an injective map that is differentiable with injective derivative on a measurable set \(s\) satisfies \(\int_s Jf=\mathcal H^m(f(s))\) ([area formula](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Function/AreaFormula/Basic.lean)). Points where \(Jf=0\) have \(\mathcal H^m\)-null image, and for a Lipschitz map injective on a measurable set the same formula holds without differentiability assumptions ([Lipschitz case](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Function/AreaFormula/Lipschitz.lean), `lintegral_normDet_fderiv_eq_euclideanHausdorffMeasure_image`). For a general Lipschitz map, \(\int_s g\,Jf\) equals the integral over the target of the fiber sums of \(g\), so \(\int_s Jf=\int\#(s\cap f^{-1}(y))\,d\mathcal H^m(y)\) ([multiplicity](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Function/AreaFormula/Multiplicity.lean), `lintegral_normDet_fderiv_eq_lintegral_encard`).

**Synopsis entries.** Covered: 05.32 (Mathlib). Partly covered: 05.34 (locally Lipschitz maps and the derivative bound; \(C^1\) approximation absent), 05.36 (one dimension), 05.37 (Lipschitz functions are weakly differentiable; \(W^{1,\infty}\) functions are Lipschitz on compact sets, without the sharp constant), 05.38 (local Lipschitz continuity, almost-everywhere differentiability, and Alexandrov's theorem; the Hessian measure is absent). Not covered: 05.33, 05.64, 05.35, 05.39–05.41.

## Fine properties of $BV$ functions in several variables

[Mathematical scope](SYNOPSIS05.md#fine-properties-of-bv-functions-in-several-variables).

### TauCeti

Supporting definitions: the total variation \(|Du|(\Omega)=\sup\{\int u\operatorname{div}\varphi:\varphi\in C_c^\infty(\Omega;E),\ \|\varphi\|\le1\}\) on an open set of a finite-dimensional inner product space and De Giorgi's perimeter \(P(s;\Omega)=|D1_s|(\Omega)\) are defined, with invariance under null modifications, subadditivity, and lower semicontinuity under \(L^1_{\mathrm{loc}}\) convergence and local convergence in measure respectively ([total variation](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/BoundedVariation/TotalVariation.lean), `TauCeti.totalVariationOn_le_liminf`; [perimeter](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/BoundedVariation/Perimeter.lean), `TauCeti.perimeter_le_liminf`). Approximate differentiability and the Federer–Vol'pert decomposition are not present.

**Synopsis entries.** Not covered: 05.49.

## Nonabsolute integration and reconstruction of primitives

[Mathematical scope](SYNOPSIS05.md#nonabsolute-integration-and-reconstruction-of-primitives).

### Mathlib

**Gauge integrals.** A box in \(\mathbb{R}^n\), represented as functions from a finite index type to \(\mathbb{R}\), is a half-open rectangle. An integral over a box is a limit of tagged Riemann sums for a box-additive volume. Three Boolean parameters select the filter of tagged partitions and thereby the integration theory (`Analysis/BoxIntegral/Basic.lean`, `Analysis/BoxIntegral/Partition/Filter.lean`).

- The Riemann integral asks for a uniform bound on the diameters of the boxes, with each tag in its own closed box.
- The Henstock–Kurzweil integral lets the diameter bound depend on the tag: the partition is subordinate to a positive gauge, and each tag lies in its box.
- The McShane integral is the same, except that a tag need only lie in the ambient box.
- A fourth filter, strictly finer in higher dimension and equal to the Henstock filter in dimension one, also controls the eccentricity of the boxes.

Cousin's lemma is proved: for every positive gauge a box has a Henstock tagged partition subordinate to it (`BoxIntegral.Prepartition.exists_taggedPartition_isHenstock_isSubordinate_homothetic`, `Analysis/BoxIntegral/Partition/SubboxInduction.lean`). The integral is unique when it exists (`BoxIntegral.HasIntegral.unique`) and is additive over partitions of a box. Continuous functions are integrable for these theories. A Henstock–Sacks inequality controls the oscillation of integral sums (`Analysis/BoxIntegral/Basic.lean`).

Every Bochner-integrable function on a box, for a locally finite measure, is McShane integrable, hence Henstock integrable, with the same integral; the proof follows Gordon's *The Integrals of Lebesgue, Denjoy, Perron, and Henstock*. Continuous functions, and bounded functions continuous almost everywhere, are Riemann integrable with integral equal to the Bochner integral (`Analysis/BoxIntegral/Integrability.lean`, `IntegrableOn.hasBoxIntegral`, `AEContinuous.hasBoxIntegral`). The converse characterization, that \(f\) and \(|f|\) are both gauge integrable only for Lebesgue integrable \(f\), is not stated.

**Integration of derivatives.** For the fourth filter, a function continuous on a closed box and differentiable off a countable set has partial derivatives integrable on the box, with integral equal to the difference of the face integrals (`BoxIntegral.hasIntegral_GP_pderiv`, `BoxIntegral.hasIntegral_GP_divergence_of_forall_hasDerivWithinAt`, `Analysis/BoxIntegral/DivergenceTheorem.lean`). In dimension one this filter is the Henstock–Kurzweil filter, so a continuous function differentiable off a countable set has a Henstock–Kurzweil integrable derivative with \(\int_a^bF'=F(b)-F(a)\). For the Lebesgue integral, \(\int_a^bF'=F(b)-F(a)\) holds when \(F\) is continuous, differentiable off a countable set, and \(F'\) is integrable (`integral_eq_of_hasDerivAt_off_countable_of_le`, `MeasureTheory/Integral/DivergenceTheorem.lean`). The indefinite gauge integral, the \(ACG_*\) characterization of its primitives, and the Denjoy and Perron integrals are not developed.

**Synopsis entries.** Covered: 05.51, 05.53 (Mathlib). Partly covered: 05.52 (Lebesgue integrable functions are gauge integrable with the same integral; the converse characterization is absent). Not covered: 05.54, 05.55.

## Extension, traces, and further fine properties

[Mathematical scope](SYNOPSIS05.md#extension-traces-and-further-fine-properties).

Whitney's \(C^1\) extension theorem is not stated in either library. The nearest material is the McShane extension of Lipschitz functions recorded above.

**Synopsis entries.** Not covered: 05.56.
