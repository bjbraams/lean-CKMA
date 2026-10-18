# 5. Differentiation and the fine structure of real functions

Checked against Mathlib commit `f039e1b8a616d45782a5c7fc5e7909249c36b8ea` (2026-10-18, Lean `v4.36.0-rc1`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. Some roots below are directory prefixes; the individual `.lean` files cited are the importable modules. The roots for this section are `Mathlib.Analysis.Calculus.Deriv`, `Mathlib.Analysis.Calculus.FDeriv`, `Mathlib.Analysis.Calculus.Monotone`, `Mathlib.Analysis.Calculus.Rademacher`, `Mathlib.Analysis.BoundedVariation`, `Mathlib.Analysis.BoxIntegral`, `Mathlib.Topology.EMetricSpace.BoundedVariation`, `Mathlib.Topology.EMetricSpace.Lipschitz`, `Mathlib.Topology.MetricSpace.Lipschitz`, `Mathlib.Topology.UniformSpace.Dini`, `Mathlib.MeasureTheory.Function.AbsolutelyContinuous`, `Mathlib.MeasureTheory.Integral.IntervalIntegral`, `Mathlib.MeasureTheory.Covering`, and `Mathlib.MeasureTheory.VectorMeasure.BoundedVariation`.

**Namespaces.** `LipschitzWith` and `LipschitzOnWith`; `eVariationOn`; `AbsolutelyContinuousOnInterval`; `intervalIntegral`; `BoxIntegral`; `Vitali`, `VitaliFamily`, and `Besicovitch`. Monotonicity theorems are declared on `Monotone` and `MonotoneOn`. The one-variable derivative is `deriv` and `HasDerivAt`, and the Fréchet derivative is `fderiv` and `HasFDerivAt`.

This note records differentiation of real functions of one variable, bounded variation, absolute continuity, the fundamental theorem of calculus, Lipschitz differentiability, and the gauge integrals. Differentiation of measures in metric spaces is stated in full in `Mathlib04.md`; the statements used here are repeated only as far as the one-variable theory needs them.

## Derivatives

The derivative of a map from a normed field into a normed space is the element \(f'\) for which the increment is \(f'(y-x)\) up to a little-o error. The predicates record a derivative at a point, within a set, along a filter, and in the strict sense \(f(y)-f(z)=(y-z)\cdot f'+o(y-z)\) as \(y,z\to x\). If no derivative exists, the functional `deriv` returns zero (`Analysis/Calculus/Deriv/Basic.lean`).

The Fréchet derivative of a map between normed spaces is a continuous linear map, again in the pointwise, restricted, and strict senses. The one-variable derivative coincides with the Fréchet derivative (`Analysis/Calculus/FDeriv/Basic.lean`).

Darboux's theorem: the derivative of a function differentiable on an interval takes every intermediate value, so a derivative has the intermediate value property even when it is discontinuous (`Analysis/Calculus/Darboux.lean`). This is the first of the classical facts about the structure of derivatives. A derivative is the limit of difference quotients (`hasDerivAt_iff_tendsto_slope`, `hasDerivAt_iff_tendsto_slope_zero` in `Analysis/Calculus/Deriv/Slope.lean`); composing the quotients with increments tending to zero continuously in \(x\) exhibits the derivative on an open interval as a pointwise limit of continuous functions, so the Baire-class-one property is a short consequence, although no Baire-class predicate is defined. The Zahorski description listed below is absent.

## Monotone functions and bounded variation

A monotone function \(f:\mathbb{R}\to\mathbb{R}\) is differentiable almost everywhere. On a set, a function monotone on that set is differentiable almost everywhere within the set. The argument compares difference quotients with the Radon–Nikodym derivative of the Stieltjes measure of \(f\), using one-sided limits where \(f\) jumps (`Analysis/Calculus/Monotone.lean`).

The variation of \(f\) on a linearly ordered set \(s\), with values in an extended pseudo-metric space, is the supremum of sums of successive distances along finite increasing sequences in \(s\). The function has bounded variation on \(s\) when that supremum is finite, and locally bounded variation when the variation is finite on \(s\cap[a,b]\) for all endpoints \(a,b\in s\). Variation adds over adjacent compact intervals. A real-valued locally BV function on a subset of the line is a difference of two monotone functions. A Lipschitz function has locally bounded variation (`Topology/EMetricSpace/BoundedVariation.lean`).

A function of bounded variation on an interval of \(\mathbb{R}\), with values in a finite-dimensional real vector space, is differentiable almost everywhere on that interval. A locally BV function on \(\mathbb{R}\) with finite-dimensional real values is differentiable almost everywhere. The same conclusion holds for a Lipschitz map from an interval, or from the line, into a finite-dimensional space (`Analysis/BoundedVariation.lean`).

If \(f\) has bounded variation and takes values in a complete normed additive group, it induces a vector-valued Stieltjes measure. The measure of an interval is a difference of one-sided limits of \(f\). Its total variation is finite and is controlled by the variation of \(f\) (`MeasureTheory/VectorMeasure/BoundedVariation.lean`).

## Absolute continuity and the fundamental theorem

A function on a compact interval is absolutely continuous when, for every \(\varepsilon>0\), some \(\delta>0\) controls the sum of increments of \(f\) by \(\varepsilon\) whenever a finite collection of disjoint subintervals has total length less than \(\delta\). Absolutely continuous functions are uniformly continuous and have bounded variation. For real-valued functions they form an algebra; for finite-dimensional real values, bounded variation gives almost-everywhere differentiability. A Lipschitz function on the interval is absolutely continuous. The indefinite integral of an integrable function is absolutely continuous (`MeasureTheory/Function/AbsolutelyContinuous.lean`).

If \(f:\mathbb{R}\to\mathbb{R}\) is absolutely continuous on the interval with endpoints \(a\) and \(b\), then
\[
\int_a^b f'(x)\,dx = f(b)-f(a).
\]
Integration by parts holds for two such functions (`MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`). The derivative of a monotone function, of a BV function, and of an absolutely continuous function is interval-integrable. For a monotone function the integral of the derivative lies between \(0\) and \(f(b)-f(a)\) (`MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`).

The first fundamental theorem, for a Banach-valued integrand: if \(f\) is locally integrable on \(\mathbb{R}\), then for almost every \(x\) and every basepoint \(c\),
\[
\frac{d}{dx}\int_c^x f = f(x).
\]
On a compact interval the same holds for almost every point of the interval (`MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean`). If \(f\) is continuous at an endpoint, the indefinite interval integral is differentiable there with derivative \(f\). A variant assumes a finite limit of \(f\) at the endpoint in place of continuity. Strict differentiability holds under the corresponding strict hypotheses (`MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`).

The second fundamental theorem, for a Banach-valued \(f\): if \(f\) is continuous on \([a,b]\), has a right derivative \(f'\) at every point of \((a,b)\), and \(f'\) is interval-integrable, then \(\int_a^b f' = f(b)-f(a)\). The same identity holds when \(f\) is differentiable at every point of the interval and the derivative is interval-integrable, and when the values at the endpoints are recovered as one-sided limits. Integration by parts and integration by substitution are deduced from this form (`MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`, `MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean`).

## Lipschitz maps and Rademacher’s theorem

A map between extended metric spaces is Lipschitz with constant \(K\geq 0\) when distances in the target are at most \(K\) times distances in the source. The inequality may be required only on a subset, and a map is locally Lipschitz when every point has a neighborhood on which some constant works (`Topology/EMetricSpace/Lipschitz.lean`, `Topology/MetricSpace/Lipschitz.lean`).

Rademacher’s theorem: a Lipschitz map between finite-dimensional real vector spaces is differentiable almost everywhere for Lebesgue measure. A map that is Lipschitz on a set is differentiable almost everywhere within that set. The proof reduces to real-valued maps, uses almost-everywhere differentiability along lines from the one-variable BV theorem and Fubini, and then upgrades line derivatives to a Fréchet derivative by Morrey’s duality argument (`Analysis/Calculus/Rademacher.lean`).

Lipschitz extension, in the McShane form: a real-valued map that is \(K\)-Lipschitz on a subset of a pseudometric space extends to a \(K\)-Lipschitz map on the whole space. The same holds coordinatewise for maps into \(\mathbb{R}^n\) with the sup norm, and for maps into any finite-dimensional real normed space with a constant multiplied by a factor depending only on the target (`LipschitzOnWith.extend_real`, `LipschitzOnWith.extend_pi` in `Topology/MetricSpace/Lipschitz.lean`; `LipschitzOnWith.extend_finite_dimension` in `Analysis/Normed/Module/FiniteDimension.lean`). The isometric Kirszbraun extension between Hilbert spaces was not found.

Two easy cases of Sard's theorem are proved. A map that is differentiable on a set of Hausdorff dimension less than the dimension of the target has an image with dense complement; in particular a differentiable map into a space of larger dimension has a range with dense complement (`Topology/MetricSpace/HausdorffDimension.lean`). In equal dimensions, the image of the set where the Jacobian determinant vanishes has measure zero (`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` in `MeasureTheory/Function/Jacobian.lean`).

## Covering lemmas

The one-variable theory relies on the differentiation theory of measures. In a metric space, Vitali’s covering lemma extracts a disjoint subfamily of balls whose five-times enlargements cover the original family. Besicovitch’s theorem, in spaces without a satellite configuration and in particular in finite-dimensional normed spaces, covers the centers by finitely many disjoint subfamilies. Along a Vitali family, ratios of measures converge almost everywhere to the Radon–Nikodym derivative, and almost every point of a measurable set is a density point. The full statements are in `Mathlib04.md` (`MeasureTheory/Covering/Vitali.lean`, `MeasureTheory/Covering/Besicovitch.lean`, `MeasureTheory/Covering/Differentiation.lean`, `MeasureTheory/Covering/DensityTheorem.lean`).

## Dini’s theorem

If a monotone sequence of continuous functions on a compact set, with values in a normed lattice, converges pointwise to a continuous limit, then the convergence is uniform (`Topology/UniformSpace/Dini.lean`).

## Gauge integrals

A box in \(\mathbb{R}^n\), represented as functions from a finite index type to \(\mathbb{R}\), is a half-open rectangle. An integral over a box is a limit of tagged Riemann sums for a box-additive volume. Three Boolean parameters select the filter of tagged partitions and thereby the integration theory (`Analysis/BoxIntegral/Basic.lean`, `Analysis/BoxIntegral/Partition/Filter.lean`).

- The Riemann integral asks for a uniform bound on the diameters of the boxes, with each tag in its own closed box.
- The Henstock–Kurzweil integral lets the diameter bound depend on the tag: the partition is subordinate to a positive gauge, and each tag lies in its box.
- The McShane integral is the same, except that a tag need only lie in the ambient box.
- A fourth filter, strictly finer in higher dimension and equal to the Henstock filter in dimension one, also controls the eccentricity of the boxes. For that filter, the divergence of a Fréchet differentiable vector field is integrable on a box, and its integral equals the flux through the faces (`Analysis/BoxIntegral/DivergenceTheorem.lean`).

Continuous functions are integrable for these theories. A Henstock–Sacks inequality controls the oscillation of integral sums (`Analysis/BoxIntegral/Basic.lean`).

Every Bochner-integrable function on a box, for a locally finite measure, is McShane integrable, hence Henstock integrable, with the same integral; the proof follows Gordon's *The Integrals of Lebesgue, Denjoy, Perron, and Henstock*. Continuous functions, and bounded functions continuous almost everywhere, are Riemann integrable with integral equal to the Bochner integral (`Analysis/BoxIntegral/Integrability.lean`, `IntegrableOn.hasBoxIntegral`, `AEContinuous.hasBoxIntegral`). The converse direction, that a Henstock integrable function need not be Lebesgue integrable, and the absolute-integrability characterization of the McShane integral, were not found.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6ebb29f84b4d`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

The Hardy–Littlewood maximal function and its weak \((1,1)\) and strong \((p,p)\), \(1<p<\infty\), inequalities are implemented for finite-dimensional real normed spaces with additive Haar measure ([source](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/MeasureTheory/Integral/MaximalFunction.lean)). This is real-variable differentiation infrastructure; no Denjoy–Young–Saks, Zahorski, or approximate-differentiation theory was located in TauCeti. A one-dimensional Lebesgue differentiation theorem for extended nonnegative densities with finite lower integral is also proved ([densities](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean), `TauCeti.ae_tendsto_setLIntegral_uIoc_div`).

The Morse–Sard theorem is proved in full: for a \(C^k\) map between finite-dimensional real normed spaces, with \(k\) large enough relative to the dimensions, the set of critical values has Haar measure zero, and the regular values are dense ([Morse–Sard](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Calculus/Sard/OutermostStratum.lean), `ContDiff.addHaar_image_criticalPoints_eq_zero`). This goes beyond the equal-dimension and smaller-source cases in Mathlib recorded above. Lower semicontinuity of total variation under pointwise convergence is also recorded ([variation](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Topology/EMetricSpace/BoundedVariation.lean)).

The area formula is proved for Lipschitz maps. For finite-dimensional real inner product spaces \(U,V\) with \(m=\dim U\), and \(J f=\) the \(m\)-dimensional Jacobian \(\sqrt{\det(Df^*Df)}\), an injective map that is differentiable with injective derivative on a measurable set \(s\) satisfies \(\int_s Jf=\mathcal H^m(f(s))\) ([area formula](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/MeasureTheory/Function/AreaFormula/Basic.lean)). Points where \(Jf=0\) have \(\mathcal H^m\)-null image, and for a Lipschitz map injective on a measurable set the same formula holds without differentiability assumptions ([Lipschitz case](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/MeasureTheory/Function/AreaFormula/Lipschitz.lean), `lintegral_normDet_fderiv_eq_euclideanHausdorffMeasure_image`). For a general Lipschitz map, \(\int_s g\,Jf\) equals the integral over the target of the fiber sums of \(g\), so \(\int_s Jf=\int\#(s\cap f^{-1}(y))\,d\mathcal H^m(y)\) ([multiplicity](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/MeasureTheory/Function/AreaFormula/Multiplicity.lean), `lintegral_normDet_fderiv_eq_lintegral_encard`). For a Lipschitz curve this gives the Banach indicatrix formula: the variation on \([a,b]\) is the integral of the number of preimages ([curves](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/MeasureTheory/Function/AreaFormula/Curve.lean), `eVariationOn_eq_lintegral_encard`). The coarea formula was not found.

The variation of an absolutely continuous curve in a pseudometric space on \([a,b]\) equals the integral of its metric derivative, and, in a finite-dimensional normed space, the integral of the norm of its derivative ([metric derivative](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/MeasureTheory/Function/MetricDerivative/Variation.lean), `eVariationOn_eq_lintegral_metricDerivative`, `eVariationOn_eq_lintegral_enorm_deriv`). Alexandrov's theorem is proved: a convex function on a finite-dimensional real inner product space, possibly with values in the extended reals, has at almost every point of its effective domain a second-order Taylor expansion with a unique positive semidefinite symmetric Hessian, and its subdifferential is differentiable there ([Alexandrov](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Convex/Alexandrov.lean), `ConvexOn.ae_existsUnique_isPositive_isLittleO`).

For several variables, the total variation \(|Du|(\Omega)=\sup\{\int u\operatorname{div}\varphi:\varphi\in C_c^\infty(\Omega;E),\ \|\varphi\|\le1\}\) on an open set of a finite-dimensional inner product space and De Giorgi's perimeter \(P(s;\Omega)=|D1_s|(\Omega)\) are defined, with invariance under null modifications, subadditivity, and lower semicontinuity under \(L^1_{\mathrm{loc}}\) convergence and local convergence in measure respectively ([total variation](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/BoundedVariation/TotalVariation.lean), `TauCeti.totalVariationOn_le_liminf`; [perimeter](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/BoundedVariation/Perimeter.lean), `TauCeti.perimeter_le_liminf`). The structure theory of \(BV\) functions (smooth approximation, compactness, coarea, De Giorgi's structure theorem, traces) was not found.

## Topics of Section 5 not found in either inspected library

- The four Dini derivates, and the Denjoy–Young–Saks theorem. The Dini theorem that is proved is the uniform-convergence theorem above.
- Approximate differentiability and approximate derivatives. No approximate-continuity predicate is defined, but almost-everywhere approximate continuity of a finite measurable function follows in a few lines from Mathlib's Lebesgue point and density theorems along Vitali families (`VitaliFamily.ae_tendsto_average_norm_sub`, `ae_tendsto_measure_inter_div` in `MeasureTheory/Covering/Differentiation.lean`), applied to a bounded reparametrization such as \(\arctan\circ f\).
- Zahorski’s characterization of derivatives. The Baire-class-one property follows from the difference-quotient characterization recorded above.
- Kirszbraun's theorem on Lipschitz extension with the same constant between Hilbert spaces.
- Differentiation bases in the sense of de Guzmán (the strong maximal function, the Jessen–Marcinkiewicz–Zygmund theorem, and the Busemann–Feller counterexamples), and Garsia's almost-everywhere convergence methods beyond the maximal inequalities recorded above.
- The Denjoy and Perron integrals as descriptive theories. The Henstock–Kurzweil and McShane integrals are the gauge integrals above.
