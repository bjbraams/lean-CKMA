# 18. Vector-Valued Analysis and Analysis in Banach Spaces

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. Some roots below are directory prefixes; the individual `.lean` files cited are the importable modules. The roots for this section are `Mathlib.MeasureTheory.Integral.Bochner`, `Mathlib.MeasureTheory.Integral.DominatedConvergence`, and `Mathlib.MeasureTheory.VectorMeasure`.

**Namespaces.** Integration and vector measures are `MeasureTheory`, with nested `VectorMeasure` and `SignedMeasure`. Continuous linear maps act on the integral in `ContinuousLinearMap`.

This note records the Bochner integral, dominated convergence, and vector measures as they stand in the checkout, including semivariation and the bilinear integral against a vector measure. The scalar theory and the identifications already written in `Mathlib04.md` are not repeated.

## The Bochner integral and dominated convergence

The Bochner integral extends Lebesgue integration to Banach-valued functions by passing through integrable equivalence classes. A function that is not integrable is assigned integral zero. On integrable functions the integral is linear, and its norm is at most the integral of the norm. The construction and the norm inequality are stated in `Mathlib04.md` (`MeasureTheory/Integral/Bochner/Basic.lean`).

Dominated convergence: almost-everywhere strongly measurable functions with values in a real normed space, dominated in norm by one integrable real function and convergent almost everywhere, have integrals convergent to the integral of the limit. The same conclusion holds along a countably generated filter, and for a series whose norms are dominated by a summable family of integrable functions (`MeasureTheory/Integral/DominatedConvergence.lean`). `Mathlib04.md` records this theorem together with Fubini for second-countable Banach-valued integrands.

A continuous linear map between Banach spaces over \(\mathbb{R}\) or \(\mathbb{C}\) passes inside the Bochner integral of an integrable function. A continuous semilinear map does as well when both spaces are complete and the scalar homomorphism commutes with real scalars. For a fixed continuous semilinear map, the integral of the image of an \(L^1\) class depends continuously on that class; that continuity statement does not add a completeness hypothesis on the codomain. When the target is complete, evaluation of an integrable map with values in continuous linear operators passes inside the integral (`MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`).

## Strong measurability and Banach-valued function spaces

Pettis's measurability theorem is proved in the form used by Hytönen–van Neerven–Veraar–Weis: a function into a pseudometrizable space is strongly measurable if and only if it is measurable and has separable range, and almost everywhere strongly measurable if and only if it is almost everywhere measurable and almost everywhere separably valued (`stronglyMeasurable_iff_measurable_separable` in `MeasureTheory/Function/StronglyMeasurable/Basic.lean`, `aestronglyMeasurable_iff_aemeasurable_separable` in `MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`). The version with measurability tested only against continuous linear functionals, weak measurability, was not found.

The Lebesgue–Bochner spaces \(L^p(\mu;E)\) are the \(L^p\) spaces of `Mathlib04.md` with a Banach space \(E\) of values: they are complete, simple functions are dense for \(p<\infty\), and a continuous bilinear map induces the Hölder pairing. Conditional expectation is Banach-valued (`Mathlib06.md`), and the definition of a martingale allows Banach values, but the martingale convergence theorems of `Mathlib08.md` are stated for real-valued processes. Complex analysis in Mathlib is largely Banach-valued, including the Cauchy integral formula and analyticity of complex-differentiable maps (`Mathlib40.md`).

## Vector measures

A vector measure is a countably additive map from a σ-algebra into a topological additive monoid. Signed measures are the real-valued case. Hahn’s decomposition, the Jordan decomposition into a unique pair of mutually singular finite measures, and the Radon–Nikodym theorem for a signed measure absolutely continuous with respect to a σ-finite measure are proved and are recorded in `Mathlib04.md` (`MeasureTheory/VectorMeasure/Decomposition/Hahn.lean`, `MeasureTheory/VectorMeasure/Decomposition/Jordan.lean`, `MeasureTheory/VectorMeasure/Decomposition/RadonNikodym.lean`). Transport of a Banach-valued density along a scalar absolute continuity is proved there as well. It is not a Radon–Nikodym theorem for a general Banach-valued vector measure.

The variation of a vector measure is the supremum of sums of norms over measurable partitions, and it dominates the norm of the measure of each set (`MeasureTheory/VectorMeasure/Variation/Basic.lean`). For a vector measure with values in a real normed space, not necessarily complete, the semivariation of a set is the supremum of the variations of the real pushforwards by continuous linear forms of norm at most \(1\). The norm of \(\mu(s)\) is at most the semivariation of \(s\), which is at most the variation. Any number strictly below the semivariation of a measurable set is strictly below twice the norm of the measure of some measurable subset. The semivariation of the whole space is finite, so \(\|\mu(s)\|\) is bounded independently of \(s\). The comparison uses the norm-controlled dual vector from the Hahn–Banach theorem (`MeasureTheory/VectorMeasure/Variation/Semivariation.lean`).

An \(E\)-valued function that is integrable with respect to the total variation of an \(F\)-valued vector measure may be integrated through a continuous bilinear pairing \(E \times F \to G\), provided \(G\) is complete. The integral is \(G\)-valued (`MeasureTheory/VectorMeasure/Integral.lean`).

The strong law has a Banach-valued form, obtained by approximation with simple functions. It is stated in `Mathlib06.md` (`Probability/StrongLaw.lean`).

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

For functions valued in an arbitrary real Banach space, TauCeti constructs normalized smooth averaging operators on \(L^p\), proves their norms are at most one, and proves strong convergence to the identity for \(1\le p<\infty\). The domain is a proper real normed space with additive Haar measure ([Banach-valued approximate identities](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/MeasureTheory/Function/Lp/ApproximateIdentity.lean)).

Its Banach-space evolution theory is also substantial: strongly continuous semigroups, generators, generation theorems, and unique mild and classical solutions of the associated abstract Cauchy problem are described in Section 24. These results use Bochner integration and do not provide the Pettis integral, UMD theory, or the vector-measure Radon–Nikodym theorem.

## Topics of Section 18 not found in either inspected library

- The Pettis integral.
- UMD spaces, radonifying operators, Banach-valued martingale convergence, and Littlewood–Paley theory for Banach-valued functions.
- The vector-valued Laplace transform and its inversion in the sense of Arendt–Batty–Hieber–Neubrander.
- Sectorial operators, the holomorphic \(H^\infty\) functional calculus, \(R\)-boundedness, and maximal \(L^p\)-regularity.
- The Diestel–Uhl Radon–Nikodym theorem for vector measures with values in a general Banach space, relative weak compactness of ranges of vector measures, and Lyapunov’s convexity theorem. Semivariation, boundedness, and the bilinear integral are present; the signed and σ-finite scalar Radon–Nikodym theorems are in `Mathlib04.md`.
