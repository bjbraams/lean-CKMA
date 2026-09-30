# 37. Geometric Measure Theory, BV, Rectifiability, and Currents

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. The roots for this section are `Mathlib.MeasureTheory.Measure.Hausdorff`, `Mathlib.Topology.MetricSpace.HausdorffDimension`, `Mathlib.Topology.MetricSpace.GromovHausdorff`, `Mathlib.Topology.EMetricSpace.BoundedVariation`, `Mathlib.Analysis.BoundedVariation`, and `Mathlib.MeasureTheory.VectorMeasure.BoundedVariation`.

**Namespaces.** Hausdorff measure and Hausdorff dimension are `MeasureTheory`, with the outer-measure predicate `MeasureTheory.OuterMeasure.IsMetric`. The Gromov–Hausdorff space is `GromovHausdorff`. Bounded variation is `BoundedVariationOn`, and the extended variation is `eVariationOn`.

Hausdorff measure, Hausdorff dimension, the Gromov–Hausdorff distance, and the variation of a path are present. Geometric measure theory in the sense of perimeters, rectifiability, and currents is not.

## Hausdorff measure

On an extended metric space, an outer measure is metric when it is additive on pairs of sets separated by a positive distance. A metric outer measure on a Borel extended metric space measures every Borel set (`MeasureTheory/Measure/Hausdorff.lean`). The constructions that send a gauge of the diameter, or more generally a gauge of the set, to an outer measure produce metric outer measures. The same measures, restricted to the Borel σ-algebra, are the corresponding Borel measures.

The \(d\)-dimensional Hausdorff measure \(\mu^H_d\), written \(\mu H[d]\) in the library, is the case of the gauge \(r\mapsto r^d\). For an arbitrary set \(s\), and for \(0<d\),
\[
\mu^H_d(s)=\sup_{r>0}\inf\sum_n\operatorname{ediam}(t_n)^d,
\]
the infimum running over countable covers of \(s\) by sets of extended diameter at most \(r\). At \(d=0\) the same formula inserts a factor that drops empty pieces of the cover, so that a singleton is not assigned measure zero. Precisely: \(\mu^H_0(\{x\})=1\), while \(\mu^H_d(\{x\})=0\) whenever \(d>0\). A nonempty set has \(\mu^H_0\) at least \(1\). The same measure is the one recorded in `Mathlib04.md`; the normalization and the comparison theorems below are what this checkout proves.

If \(d_1<d_2\), then for every set either \(\mu^H_{d_2}\) vanishes or \(\mu^H_{d_1}\) is infinite. As a function of \(d\), Hausdorff measure is antitone. A set of finite \(d\)-dimensional measure is separable.

Hölder maps distort the measure by the exponent. If \(f\) is Hölder of exponent \(r>0\) and constant \(C\) on \(s\), and \(d\ge 0\), then \(\mu^H_d(f(s))\le C^d\,\mu^H_{rd}(s)\). A \(K\)-Lipschitz map therefore multiplies \(\mu^H_d\) by at most \(K^d\).

On a nonempty finite product \(\iota\to\mathbb{R}\) with its coordinate sup norm, Hausdorff measure of dimension \(\lvert\iota\rvert\) coincides with Lebesgue measure.

## Hausdorff dimension

The Hausdorff dimension \(\dim_H s\in[0,\infty]\) is defined so that \(\mu^H_d(s)=\infty\) whenever \(d<\dim_H s\), and \(\mu^H_d(s)=0\) whenever \(\dim_H s<d\). The value of \(\mu^H_d\) at the critical dimension is not constrained. Equivalently, \(\dim_H s\) is the supremum of those \(d\) for which \(\mu^H_d(s)\) is infinite, and also the infimum of those \(d\) for which it vanishes (`Topology/MetricSpace/HausdorffDimension.lean`).

Dimension is monotone. The dimension of a countable union is the supremum of the dimensions, so a countable set has dimension zero, and the dimension of a union of two sets is the maximum. A Hölder map of exponent \(r>0\) sends \(s\) to a set of dimension at most \((\dim_H s)/r\), and a Lipschitz map does not increase dimension. An isometry, and a continuous linear equivalence, preserve dimension. A differentiable map on a set does not increase the dimension of that set.

In \(\mathbb{R}^n\), identified with \(\mathrm{Fin}\,n\to\mathbb{R}\), the whole space and every nonempty open ball have dimension \(n\). In a finite-dimensional real normed space, any set with nonempty interior, and in particular the whole space, has dimension equal to the rank, and any set of strictly smaller dimension has dense complement. A nontrivial line segment has dimension \(1\). A convex set has dimension equal to the rank of its direction. Every subset of a finite-dimensional real normed space has finite Hausdorff dimension.

## Gromov–Hausdorff distance

The Gromov–Hausdorff space is the space of nonempty compact metric spaces up to isometry. It is realized as the quotient of the nonempty compact subsets of \(\ell^\infty(\mathbb{R})\) by isometry, using the Kuratowski embedding of separable metric spaces (`Topology/MetricSpace/GromovHausdorff.lean`). The distance between two classes is the infimum of Hausdorff distances between isometric copies in \(\ell^\infty(\mathbb{R})\). The infimum is attained: some pair of isometric embeddings into \(\ell^\infty(\mathbb{R})\) realizes it. The resulting function is a metric. Two nonempty compact metric spaces determine the same point if and only if they are isometric, so the distance vanishes if and only if the spaces are isometric.

The distance is at most the Hausdorff distance of any pair of isometric embeddings into a common metric space. The Gromov–Hausdorff space is complete, and it is second countable. A set of classes is totally bounded if the representatives have uniformly bounded diameter and, along some sequence of radii tending to zero, there is a uniform bound on the number of balls of that radius needed to cover each representative. The file calls this the interesting direction of the Gromov compactness criterion and proves total boundedness; it does not state a converse, and it does not package the criterion as compactness of a closed subset.

## Bounded variation

The variation of a function on a subset of a linear order, with values in an extended pseudo-metric space, is the supremum of the sums of successive extended distances along finite increasing sequences in the set. The function has bounded variation when that supremum is finite, and locally bounded variation when the restriction to the intersection of the set with every compact interval between points of the set has finite variation (`Topology/EMetricSpace/BoundedVariation.lean`). Variation is monotone in the set, and it is lower semicontinuous under pointwise convergence in the target. This lower semicontinuity is a fact about the variation of a path, not a theorem about integral functionals.

On a densely ordered, second-countable linear order whose closed intervals are compact — in particular on \(\mathbb{R}\) — a function of bounded variation with values in a complete normed group determines a vector measure. The construction dominates the increments of the right-limit function by the Stieltjes measure of the variation of that right-limit function, extends the resulting content, and corrects the value at a bottom element by a Dirac mass if one exists. The vector measure assigns to \((a,b]\) the difference of right limits, and to a closed interval \([a,b]\) the right limit at \(b\) minus the left limit at \(a\). Its total variation is finite and is controlled by the variation of the function (`MeasureTheory/VectorMeasure/BoundedVariation.lean`).

A real function of bounded variation into a finite-dimensional real vector space is differentiable almost everywhere. That differentiation theory, including the Lipschitz case, is the subject of `Mathlib05.md` and is not restated here. Nothing in these theorems identifies the distributional derivative of a BV function with a measure in the sense of sets of finite perimeter, and bounded variation is not used as a substitute for that theory.

An injective change-of-variables theorem with the absolute determinant of the derivative is proved in `MeasureTheory/Function/Jacobian.lean`; see Section 4. This covers the equal-dimensional injective case of an area formula. It does not give the general area formula with multiplicities or the coarea formula for fibers of positive dimension.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

A holomorphic specialization of the area/change-of-variables theorem is implemented: for a holomorphic map injective on the set in question, the area of its image is the integral of \(|f'|^2\), with weighted versions ([holomorphic area formula](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Complex/Conformal/Area.lean)). This makes the conformal area identity directly available, but remains an injective equal-dimensional change-of-variables result. No general multiplicity area formula, coarea formula, finite-perimeter theory, currents, or varifold theory was located.

A set is called Lipschitz parametrizable in dimension \(d\) when finitely many Lipschitz images of the unit \(d\)-cube cover it; the class is stable under Lipschitz images, products, and finite unions, contains \(C^1\) images of cubes, and a Lipschitz-parametrizable set of dimension less than the ambient dimension has Haar measure zero ([Lipschitz-parametrizable sets](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Topology/MetricSpace/LipschitzParametrizable.lean)). This is a finite-union special case of the parametrized sets used to define rectifiability, introduced for lattice-point counting; countable rectifiability and its measure-theoretic characterizations are not developed. The Morse–Sard theorem of Section 5 is also relevant here.

## Topics of Section 37 not found in either inspected library

- Sets of finite perimeter, the De Giorgi perimeter, and the reduced boundary.
- Rectifiable sets, rectifiable currents, and varifolds.
- Allard’s regularity theorem, and the deformation theorem.
- The general area formula with multiplicities, and the coarea formula. The injective equal-dimensional Jacobian theorem is present.
- Densities and tangent measures in the sense of Mattila and De Lellis, the Besicovitch–Federer projection theorem, and uniform rectifiability.
- Fractal geometry beyond Hausdorff dimension: box-counting and packing dimensions, self-similar sets and the Moran–Hutchinson theory, Frostman's lemma, and Marstrand's projection theorem.
- Analytic capacity and the Cauchy transform on rectifiable sets.
