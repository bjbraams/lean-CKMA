# 39. Metric Measure Spaces, Dirichlet Forms, Heat Kernels, Optimal Transport, and Fractals

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. The roots for the metric ingredients that exist are `Mathlib.MeasureTheory.Measure.Doubling`, `Mathlib.MeasureTheory.Measure.Hausdorff`, `Mathlib.Topology.MetricSpace.HausdorffDimension`, `Mathlib.Topology.MetricSpace.GromovHausdorff`, and `Mathlib.Analysis.AperiodicOrder.Delone.Basic`. Gaussian measures and Fernique’s theorem are `Mathlib.Probability.Distributions.Gaussian.Fernique`, recorded in `Mathlib06.md`.

**Namespaces.** Uniformly locally doubling measures are `IsUnifLocDoublingMeasure`. Hausdorff measure and dimension are `MeasureTheory`, as in section 37. The Gromov–Hausdorff space is `GromovHausdorff`. Delone sets are `Delone`, with the structure `DeloneSet`. Fernique’s theorem for Gaussian measures is `ProbabilityTheory.IsGaussian`.

The library has doubling, Hausdorff dimension, the Gromov–Hausdorff distance, Delone sets, and Gaussian integrability. It does not have Dirichlet forms, heat kernels, curvature-dimension conditions, optimal transport, or a general analytic theory of fractals. A concrete Cantor-set construction is present.

## Doubling, dimension, and Gromov–Hausdorff distance

A measure on a pseudo-metric space is uniformly locally doubling when some constant \(C\) controls all sufficiently small scales: for every center, the measure of the closed ball of radius \(2\varepsilon\) is at most \(C\) times the measure of the closed ball of radius \(\varepsilon\), once \(\varepsilon>0\) is small enough (`MeasureTheory/Measure/Doubling.lean`). The small-scale restriction is essential; the definition is written so that exponential volume growth, as in hyperbolic space, is not forbidden. From one doubling constant one obtains constants that absorb a fixed bound on the ratio of radii. A finite product of uniformly locally doubling measures is uniformly locally doubling.

Every Haar measure on a finite-dimensional real normed space is uniformly locally doubling. The constant may be taken to be \(2\) raised to the rank, because the measure of a closed ball scales by the rank-th power of the radius (`MeasureTheory/Measure/Lebesgue/EqHaar.lean`). Haar measure on the circle \(\mathbb{R}/T\mathbb{Z}\), for \(T>0\), is uniformly locally doubling as well (`MeasureTheory/Integral/IntervalIntegral/Periodic.lean`).

Hausdorff measure and Hausdorff dimension are those of section 37. Nothing further about dimension is special to a metric measure space: the dimension of a countable union, the Lipschitz bound, and the dimension of \(\mathbb{R}^n\) are already stated there.

The Gromov–Hausdorff distance on nonempty compact metric spaces, the completeness and second countability of that space, and the covering criterion for total boundedness are stated in section 37 (`Topology/MetricSpace/GromovHausdorff.lean`).

## Delone sets

A Delone set in a metric space is a set bundled with two positive radii: a packing radius, strictly separating distinct points, and a covering radius, such that every point of the space lies at most that far from the set (`Analysis/AperiodicOrder/Delone/Basic.lean`). Distinct points are therefore farther apart than the packing radius, and every point of the space is within the covering radius of some point of the set. Any ball of radius at most half the packing radius contains at most one point of the set. A bilipschitz equivalence transports a Delone set to a Delone set, scaling the packing radius by the inverse of the anti-Lipschitz constant and the covering radius by the Lipschitz constant. An isometry preserves both radii. No diffraction, hull, or patch-counting theorem is proved.

## Gaussian measures

Fernique’s theorem, that a Gaussian measure on a second-countable real normed space admits some \(C>0\) for which \(x\mapsto\exp(C\|x\|^2)\) is integrable, is the statement recorded in `Mathlib06.md`. It is not a theory of Dirichlet forms or heat kernels.

## Cantor set and a metric on probability measures

The ternary Cantor set is constructed by repeated removal of middle thirds. It is compact, and its points are characterized by ternary expansions using only the digits \(0\) and \(2\) (`Topology/Instances/CantorSet.lean`). This concrete fractal example belongs alongside the general Hausdorff-dimension theory, although it supplies no heat kernel or analysis on fractals.

The Lévy–Prokhorov metric on probability measures is constructed, and on a separable metric Borel space it induces weak convergence (`MeasureTheory/Measure/LevyProkhorovMetric.lean`). This is relevant metric-measure infrastructure; it is distinct from Wasserstein distance and optimal transport.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

TauCeti contains an actual Kantorovich optimal-transport development: couplings, gluing, cost minimization, and existence of an optimal plan for lower-semicontinuous extended-nonnegative cost and Polish marginals. The existence statement allows infinite optimal value ([existence](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/MeasureTheory/OptimalTransport/Existence.lean)). Strong duality for general lower-semicontinuous cost is proved on **compact metrizable** spaces ([compact duality](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/MeasureTheory/OptimalTransport/Duality/LowerSemicontinuous.lean)). A differentiable twisted cost and a dual contact certificate yield a measurable optimal transport map and its almost-everywhere uniqueness; the existence of that certificate is a hypothesis of this theorem ([twist mechanism](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/MeasureTheory/OptimalTransport/Twist/Map.lean)).

The \(p\)-Wasserstein spaces of probability measures with finite \(p\)-moment are constructed. For \(1\le p<\infty\), they are complete over a complete separable ground metric space ([completeness](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Complete.lean)), and Wasserstein convergence implies weak convergence ([comparison](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/WeakConvergence.lean)). Kantorovich–Rubinstein duality is proved for finite-first-moment probability measures on separable metric spaces with standard Borel measurable structure, in particular Polish spaces: \(W_1\) is the supremum of differences of integrals against real 1-Lipschitz functions ([duality](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/KantorovichRubinstein.lean)).

These additions do not supply Dirichlet forms, heat-kernel bounds, curvature-dimension conditions, or metric gradient flows.

For finite \(1\le p<\infty\), the finite-moment Wasserstein space is separable when the ground space is separable with its standard Borel metric structure; combined with completeness this gives a Polish Wasserstein space over a Polish ground space ([separability](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Separable.lean)). On the real line, the \(W_1\) distance is the integral of the absolute difference of the cumulative distribution functions, as an extended-real identity without moment assumptions ([one-dimensional formula](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/OneDimensional.lean)).

## Topics of Section 39 not found in either inspected library

- Dirichlet forms, carré du champ, and heat kernels.
- Curvature-dimension conditions and the Bakry–Émery criterion.
- General Polish-space Kantorovich duality for arbitrary lower-semicontinuous costs, beyond the compact-space theorem and the noncompact Kantorovich–Rubinstein theorem described above.
- Gradient flows in metric spaces.
- A general theory of self-similar fractals and analysis on fractals, beyond the Hausdorff-dimension infrastructure and the concrete Cantor set above.
