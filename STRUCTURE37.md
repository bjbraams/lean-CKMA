# Structure 37: Geometric measure theory, BV, rectifiability, and currents

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS37.md); [bibliographical scope](CKMA-bib.md#ckma-37); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.MeasureTheory.Measure.Hausdorff`, `Mathlib.Topology.MetricSpace.HausdorffDimension`, `Mathlib.Topology.MetricSpace.GromovHausdorff`, `Mathlib.Topology.EMetricSpace.BoundedVariation`, `Mathlib.Analysis.BoundedVariation`, `Mathlib.MeasureTheory.VectorMeasure.BoundedVariation`, `Mathlib.MeasureTheory.Covering.Besicovitch`, `Mathlib.MeasureTheory.Covering.Differentiation`, `Mathlib.Geometry.Euclidean.Volume.Measure`, `Mathlib.Analysis.InnerProductSpace.NormDet`, `Mathlib.Analysis.Calculus.Rademacher`, `Mathlib.MeasureTheory.Function.Jacobian`, `Mathlib.MeasureTheory.Integral.DivergenceTheorem`.

**Namespaces.** Hausdorff measure and Hausdorff dimension are `MeasureTheory`, with the outer-measure predicate `MeasureTheory.OuterMeasure.IsMetric`. The Gromov–Hausdorff space is `GromovHausdorff`. Bounded variation is `BoundedVariationOn`, and the extended variation is `eVariationOn`. Differentiation of measures uses `VitaliFamily` and `Besicovitch`; the linear Jacobian is `LinearMap.normDet`. In TauCeti, rectifiability is `TauCeti.CountablyRectifiable`, total variation and perimeter are `TauCeti.totalVariationOn` and `TauCeti.perimeter`, and the area formula is stated in the `LipschitzWith` namespace.

## Hausdorff measure, dimension, and density

[Mathematical scope](SYNOPSIS37.md#hausdorff-measure-dimension-and-density).

### Mathlib

**Hausdorff measure.**

On an extended metric space, an outer measure is metric when it is additive on pairs of sets separated by a positive distance. A metric outer measure on a Borel extended metric space measures every Borel set (`MeasureTheory/Measure/Hausdorff.lean`). The constructions that send a gauge of the diameter, or more generally a gauge of the set, to an outer measure produce metric outer measures. The same measures, restricted to the Borel σ-algebra, are the corresponding Borel measures.

The \(d\)-dimensional Hausdorff measure \(\mu^H_d\), written \(\mu H[d]\) in the library, is the case of the gauge \(r\mapsto r^d\). For an arbitrary set \(s\), and for \(0<d\),
\[
\mu^H_d(s)=\sup_{r>0}\inf\sum_n\mathop{\mathrm{ediam}}(t_n)^d,
\]
the infimum running over countable covers of \(s\) by sets of extended diameter at most \(r\). At \(d=0\) the same formula inserts a factor that drops empty pieces of the cover, so that a singleton is not assigned measure zero. Precisely: \(\mu^H_0(\{x\})=1\), while \(\mu^H_d(\{x\})=0\) whenever \(d>0\). A nonempty set has \(\mu^H_0\) at least \(1\). The same measure is the one recorded in [Section 04](STRUCTURE04.md); the normalization and the comparison theorems in this topic are what this checkout proves.

If \(d_1<d_2\), then for every set either \(\mu^H_{d_2}\) vanishes or \(\mu^H_{d_1}\) is infinite. As a function of \(d\), Hausdorff measure is antitone. A set of finite \(d\)-dimensional measure is separable.

Hölder maps distort the measure by the exponent. If \(f\) is Hölder of exponent \(r>0\) and constant \(C\) on \(s\), and \(d\ge 0\), then \(\mu^H_d(f(s))\le C^d\,\mu^H_{rd}(s)\). A \(K\)-Lipschitz map therefore multiplies \(\mu^H_d\) by at most \(K^d\).

On a nonempty finite product \(\iota\to\mathbb{R}\) with its coordinate sup norm, Hausdorff measure of dimension \(\lvert\iota\rvert\) coincides with Lebesgue measure.

**Hausdorff dimension.**

The Hausdorff dimension \(\dim_H s\in[0,\infty]\) is defined so that \(\mu^H_d(s)=\infty\) whenever \(d<\dim_H s\), and \(\mu^H_d(s)=0\) whenever \(\dim_H s<d\). The value of \(\mu^H_d\) at the critical dimension is not constrained. Equivalently, \(\dim_H s\) is the supremum of those \(d\) for which \(\mu^H_d(s)\) is infinite, and also the infimum of those \(d\) for which it vanishes (`Topology/MetricSpace/HausdorffDimension.lean`).

Dimension is monotone. The dimension of a countable union is the supremum of the dimensions, so a countable set has dimension zero, and the dimension of a union of two sets is the maximum. A Hölder map of exponent \(r>0\) sends \(s\) to a set of dimension at most \((\dim_H s)/r\), and a Lipschitz map does not increase dimension. An isometry, and a continuous linear equivalence, preserve dimension. A differentiable map on a set does not increase the dimension of that set.

In \(\mathbb{R}^n\), identified with \(\mathrm{Fin}\,n\to\mathbb{R}\), the whole space and every nonempty open ball have dimension \(n\). In a finite-dimensional real normed space, any set with nonempty interior, and in particular the whole space, has dimension equal to the rank, and any set of strictly smaller dimension has dense complement. A nontrivial line segment has dimension \(1\). A convex set has dimension equal to the rank of its direction. Every subset of a finite-dimensional real normed space has finite Hausdorff dimension.

**Normalization and null sets.** The normalized Euclidean Hausdorff measure \(\mu^{HE}_n\) equals Lebesgue measure on an \(n\)-dimensional inner product space (`InnerProductSpace.euclideanHausdorffMeasure_eq_volume`; see the next topic), and on \(\iota\to\mathbb R\) with the sup norm the unnormalized \(\mu^H_{|\iota|}\) is already Lebesgue measure (`MeasureTheory.hausdorffMeasure_pi_real`). Since a \(K\)-Lipschitz map multiplies \(\mu^H_d\) by at most \(K^d\) (`LipschitzOnWith.hausdorffMeasure_image_le`), Lipschitz maps \(\mathbb R^n\to\mathbb R^n\) have Lusin's property (N); more generally a map differentiable on a Lebesgue-null set maps it to a null set (`MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` in `MeasureTheory/Function/Jacobian.lean`).

**Differentiation of measures.** A finite-dimensional real normed space has the Besicovitch covering property (`Besicovitch.instHasBesicovitchCovering` in `MeasureTheory/Covering/BesicovitchVectorSpace.lean`). For locally finite measures \(\rho,\mu\) on a space with this property, \(\rho(\overline B(x,r))/\mu(\overline B(x,r))\to d\rho/d\mu(x)\) as \(r\downarrow0\) for \(\mu\)-almost every \(x\) (`Besicovitch.ae_tendsto_rnDeriv`), with the density-theorem versions `Besicovitch.ae_tendsto_measure_inter_div` (`MeasureTheory/Covering/Besicovitch.lean`). Averages of \(f\in L^1_{\mathrm{loc}}(\mu)\) along the Besicovitch Vitali family converge to \(f\) almost everywhere (`VitaliFamily.ae_tendsto_average` in `MeasureTheory/Covering/Differentiation.lean`), and that family's filter is generated by centred closed balls (`Besicovitch.tendsto_filterAt`).

### TauCeti

Zero-dimensional Hausdorff measure is counting measure (`TauCeti.hausdorffMeasure_zero_eq_count`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Measure/Hausdorff.lean)).

**Synopsis entries.** Covered: 37.1 (Mathlib; \(\mathcal H^0\) as counting measure in TauCeti), 37.2, 37.3, 37.6 (Mathlib). Not covered: 37.4, 37.5, 37.7, 37.8, 37.70.

## Rectifiable sets, tangents, and integration

[Mathematical scope](SYNOPSIS37.md#rectifiable-sets-tangents-and-integration).

### Mathlib

**Euclidean Hausdorff measure and the linear area formula.**

The normalized Euclidean Hausdorff measure \(\mu^{HE}_d\), written `μHE[d]` (`MeasureTheory.Measure.euclideanHausdorffMeasure`), is \(\mu^H_d\) rescaled so that it equals Lebesgue measure on a \(d\)-dimensional inner product space (`InnerProductSpace.euclideanHausdorffMeasure_eq_volume`). It is preserved by isometries and by inclusion of affine subspaces, scales by \(|c|^d\) under homotheties, and on a Euclidean affine space with an affine subspace \(s\) it satisfies the slicing formula \(\mu^{HE}_n(t)=\int_s\mu^{HE}_{n-k}\bigl(t\cap(x+s^\perp)\bigr)\,d\mu^{HE}_k(x)\) for measurable \(t\) (`AffineSubspace.euclideanHausdorffMeasure_eq_lintegral`; `Geometry/Euclidean/Volume/Measure.lean`). The norm determinant \(\mathop{\mathrm{normDet}}T=\sqrt{\det(T^*T)}\) of a linear map \(T:U\to V\) between inner product spaces (`LinearMap.normDet`, also the product of the singular values) is the volume factor: \(\mu^{HE}_{\dim U}(T(s))=\mathop{\mathrm{normDet}}T\cdot\mathop{\mathrm{vol}}(s)\) for every set \(s\subseteq U\), and likewise for raw Hausdorff measure (`LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume`, `LinearMap.hausdorffMeasure_image`; `Analysis/InnerProductSpace/NormDet.lean`). This is the linear case of the area formula; the nonlinear case is in TauCeti. Rademacher's theorem, that Lipschitz maps between finite-dimensional spaces are differentiable almost everywhere, is `LipschitzWith.ae_differentiableAt` (`Analysis/Calculus/Rademacher.lean`).

An injective change-of-variables theorem with the absolute determinant of the derivative is proved in `MeasureTheory/Function/Jacobian.lean` (`MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image`); see Section 4. This covers the equal-dimensional injective case of an area formula.

### TauCeti

A holomorphic specialization of the area/change-of-variables theorem is implemented: for a holomorphic map injective on the set in question, the area of its image is the integral of \(|f'|^2\), with weighted versions ([holomorphic area formula](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Complex/Conformal/Area.lean)). This makes the conformal area identity directly available, as an injective equal-dimensional change-of-variables result.

The general area formula for Lipschitz maps is proved ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Function/AreaFormula/Multiplicity.lean)). Let \(f:U\to V\) be Lipschitz between finite-dimensional real inner product spaces, \(J f=\mathop{\mathrm{normDet}}Df\) its geometric Jacobian, \(s\subseteq U\) Lebesgue null-measurable and \(g\ge0\) measurable. Then
\[
\int_s J f(x)\,g(x)\,dx=\int_V\sum_{x\in s\cap f^{-1}(y)}g(x)\,d\mu^{HE}_{\dim U}(y),
\]
with extended sums, so that infinite fibers count as infinity; for \(g=1\) the integrand on the right is the cardinality of the fiber (`LipschitzWith.lintegral_normDet_fderiv_mul_eq_lintegral_tsum`, `LipschitzWith.lintegral_normDet_fderiv_eq_lintegral_encard`). The supporting files prove the injective area formula and the null image of the set where the Jacobian vanishes (`LipschitzWith.lintegral_normDet_fderiv_eq_euclideanHausdorffMeasure_image`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Function/AreaFormula/Lipschitz.lean)), weighted surface integration over injective regular parametrizations in any codimension ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Function/AreaFormula/Integral.lean)), comparison of surface measure on a Lipschitz graph with volume in the parameter space ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Function/AreaFormula/Graph.lean)), and, for a curve Lipschitz on \([a,b]\), the identity of its variation with the \(\mu^{HE}_1\)-integral of the fiber cardinality (`eVariationOn_eq_lintegral_encard`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Function/AreaFormula/Curve.lean)).

Countably \(k\)-rectifiable sets are defined: sets covered, up to a \(\mu^{HE}_k\)-null set, by countably many Lipschitz images of subsets of \(\mathbb R^k\) (`TauCeti.CountablyRectifiable`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Geometry/MeasureTheory/Rectifiable.lean)). The class contains null sets and subsets of \(\mathbb R^k\), and is closed under subsets, null modification, countable unions, Lipschitz images and isometries.

A set is called Lipschitz parametrizable in dimension \(d\) when finitely many Lipschitz images of the unit \(d\)-cube cover it; the class is stable under Lipschitz images, products, and finite unions, contains \(C^1\) images of cubes, and a Lipschitz-parametrizable set of dimension less than the ambient dimension has Haar measure zero ([Lipschitz-parametrizable sets](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Topology/MetricSpace/LipschitzParametrizable.lean)). This is a finite-union special case of the parametrized sets used to define rectifiability, introduced for lattice-point counting; countable rectifiability is treated separately in this topic. The Morse–Sard theorem of Section 5 is also relevant here. No tangent-plane, density, or projection characterization of rectifiability is proved, and no coarea formula is present.

**Synopsis entries.** Covered: 37.13 (TauCeti). Not covered: 37.12, 37.14–37.22.

## BV functions, traces, and jump structure

[Mathematical scope](SYNOPSIS37.md#bv-functions-traces-and-jump-structure).

### Mathlib

**Bounded variation.**

The variation of a function on a subset of a linear order, with values in an extended pseudo-metric space, is the supremum of the sums of successive extended distances along finite increasing sequences in the set. The function has bounded variation when that supremum is finite, and locally bounded variation when the restriction to the intersection of the set with every compact interval between points of the set has finite variation (`Topology/EMetricSpace/BoundedVariation.lean`). Variation is monotone in the set, and it is lower semicontinuous under pointwise convergence in the target. This lower semicontinuity is a fact about the variation of a path, not a theorem about integral functionals.

On a densely ordered, second-countable linear order whose closed intervals are compact — in particular on \(\mathbb{R}\) — a function of bounded variation with values in a complete normed group determines a vector measure. The construction dominates the increments of the right-limit function by the Stieltjes measure of the variation of that right-limit function, extends the resulting content, and corrects the value at a bottom element by a Dirac mass if one exists. The vector measure assigns to \((a,b]\) the difference of right limits, and to a closed interval \([a,b]\) the right limit at \(b\) minus the left limit at \(a\). Its total variation is finite and is controlled by the variation of the function (`MeasureTheory/VectorMeasure/BoundedVariation.lean`).

A real function of bounded variation into a finite-dimensional real vector space is differentiable almost everywhere. That differentiation theory, including the Lipschitz case, is the subject of [Section 05](STRUCTURE05.md) and is not restated here. Nothing in these theorems identifies the distributional derivative of a BV function with a measure in the sense of sets of finite perimeter, and bounded variation is not used as a substitute for that theory.

### TauCeti

For BV theory, the total variation of \(u\) on an open set \(\Omega\) of a finite-dimensional inner product space is defined by duality, \(|Du|(\Omega)=\sup\{\int u\mathop{\mathrm{div}}\varphi:\varphi\in C^\infty_c(\Omega;E),\ \|\varphi\|\le1\}\) (`TauCeti.totalVariationOn`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/BoundedVariation/TotalVariation.lean)). It is a seminorm that sees \(u\) only almost everywhere, is monotone in \(\Omega\), vanishes on constants against Haar measure, is bounded by \(\int_\Omega|\nabla u|\) for weakly differentiable \(u\), and is lower semicontinuous under distributional and \(L^1_{\mathrm{loc}}(\Omega)\) convergence (`TauCeti.totalVariationOn_le_liminf`). De Giorgi's perimeter \(P(s;\Omega)\) is the total variation of the indicator (`TauCeti.perimeter`, `TauCeti.perimeter_eq_iSup`; [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/BoundedVariation/Perimeter.lean)); it is invariant under null modification and complementation and lower semicontinuous under local convergence in measure (`TauCeti.perimeter_le_liminf`).

**Synopsis entries.** Partly covered: 37.23 (lower semicontinuity of the variation under \(L^1_{\mathrm{loc}}\) convergence, TauCeti; no weak-* compactness of the derivative measures). Not covered: 37.24–37.35.

## Sets of finite perimeter and geometric minimization

[Mathematical scope](SYNOPSIS37.md#sets-of-finite-perimeter-and-geometric-minimization).

### TauCeti

Gauss–Green formulas are available beyond boxes in special geometries: the divergence of a compactly supported \(C^1\) field integrates to zero, and on a coordinate half-space the divergence integral equals the boundary flux for fields \(C^1\) on the closed half-space with compact support ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/DivergenceTheorem/CompactSupport.lean), [source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/DivergenceTheorem/HalfSpace.lean)); for \(u\in H^1\) of a half-space the formula holds with the trace as boundary term ([source](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Analysis/Sobolev/Trace/IntegrationByParts.lean)).

The perimeter itself, with its invariance under null modification and complementation and its lower semicontinuity, is recorded in the previous topic. No reduced boundary, structure theorem, or compactness theorem for sets of finite perimeter is present.

**Synopsis entries.** Partly covered: 37.39 (the whole space and a coordinate half-space only, for compactly supported \(C^1\) fields; TauCeti). Not covered: 37.36–37.38, 37.40, 37.42–37.46.

## Currents, compactness, and Plateau's problem

[Mathematical scope](SYNOPSIS37.md#currents-compactness-and-plateaus-problem).

**Synopsis entries.** Not covered: 37.47–37.57.

## Varifolds and geometric regularity

[Mathematical scope](SYNOPSIS37.md#varifolds-and-geometric-regularity).

**Synopsis entries.** Not covered: 37.58–37.63.

## Quantitative rectifiability and analytic capacity

[Mathematical scope](SYNOPSIS37.md#quantitative-rectifiability-and-analytic-capacity).

**Synopsis entries.** Not covered: 37.64–37.69.

## Integral geometry and tomography

[Mathematical scope](SYNOPSIS37.md#integral-geometry-and-tomography).

**Synopsis entries.** Not covered: 37.71–37.76.

## Supporting structures and related formalizations

The following entries supply additional foundations or related constructions. Their stated scope determines how they can be used in this sub-area.

### Mathlib

**Gromov–Hausdorff distance.** The Gromov–Hausdorff space is the space of nonempty compact metric spaces up to isometry. It is realized as the quotient of the nonempty compact subsets of \(\ell^\infty(\mathbb{R})\) by isometry, using the Kuratowski embedding of separable metric spaces (`Topology/MetricSpace/GromovHausdorff.lean`). The distance between two classes is the infimum of Hausdorff distances between isometric copies in \(\ell^\infty(\mathbb{R})\); the infimum is attained, the resulting function is a metric, and it vanishes exactly for isometric spaces. The distance is at most the Hausdorff distance of any pair of isometric embeddings into a common metric space. The Gromov–Hausdorff space is complete and second countable. A set of classes is totally bounded if the representatives have uniformly bounded diameter and, along some sequence of radii tending to zero, there is a uniform bound on the number of balls of that radius needed to cover each representative; the converse and the packaging as a compactness criterion are not stated.

The divergence theorem on rectangular boxes (`MeasureTheory/Integral/DivergenceTheorem.lean`) is the Mathlib form of Gauss–Green; see [Section 32](STRUCTURE32.md).
