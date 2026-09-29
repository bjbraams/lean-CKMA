# 30. Distributions, Pseudodifferential Operators, Microlocal and Semiclassical Analysis

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. Some roots below are directory prefixes; the individual `.lean` files cited are the importable modules. The roots for the distributional half of this section are `Mathlib.Analysis.Distribution` and, for the duality used to topologize test functions and operator spaces, `Mathlib.Analysis.LocallyConvex`. The locally convex dual theory is written in the section 16 note and is not repeated here.

**Namespaces.** Test functions are `TestFunction` and `ContDiffMapSupportedIn`, distributions are `Distribution`, Schwartz functions are `SchwartzMap`, and tempered distributions are `TemperedDistribution`. Temperate growth is `Function.HasTemperateGrowth` and `MeasureTheory.Measure.HasTemperateGrowth`.

This note records the distribution theory found in the checkout. No pseudodifferential, microlocal, or semiclassical calculus was found.

## Distributions

A test function of order \(n\) on an open set \(\Omega\) in a real normed space is a \(C^n\) map of compact support contained in \(\Omega\). Functions supported in a fixed compact carry the locally convex topology of uniform convergence of derivatives. The full test-function space carries the finest locally convex topology making every inclusion of such a subspace continuous, and a linear map into a locally convex space is continuous exactly when each of those restrictions is continuous (`Analysis/Distribution/TestFunction.lean`, `Analysis/Distribution/ContDiffMapSupportedIn.lean`).

An \(F\)-valued distribution on \(\Omega\) is a continuous real-linear map from the real test functions into a real topological vector space \(F\), with the topology of compact convergence. The text of the file specializes to finite-dimensional domains and locally convex values; those hypotheses are not part of the type. They are used where stated below. Distributions of order at most \(n\) form a separate space. The file's comparison of this topology with the strong dual topology assumes that the test functions are a Montel space and is not a theorem here (`Analysis/Distribution/Distribution.lean`).

The Dirac mass evaluates at a point, and vanishes if the point lies outside \(\Omega\). The directional derivative satisfies \(\langle\partial_v T,\varphi\rangle=\langle T,-\partial_v\varphi\rangle\), and the operator from order \(k\) to order \(n\) is zero unless \(k+1\le n\). A locally integrable function induces a distribution by integration against test functions, the zero distribution if it is not locally integrable. On a finite-dimensional Borel domain, with complete normed values, the distribution determines the function almost everywhere on \(\Omega\). The same almost-everywhere conclusion holds for a locally integrable function on a finite-dimensional real manifold. The support is the smallest closed set outside which the distribution vanishes; differentiation does not enlarge it; and in finite dimensions the support of a Dirac mass in \(\Omega\) is the point (`Analysis/Distribution/Distribution.lean`, `Analysis/Distribution/AEEqOfIntegralContDiff.lean`, `Analysis/Distribution/Support.lean`).

There is no space of distributions on a manifold, and the Schwartz kernel theorem is not proved. Both are named, the second as future work, in `Analysis/Distribution/Distribution.lean`.

## Schwartz space and tempered distributions

A Schwartz function is a smooth function between real normed spaces whose derivatives decay faster than every power of the norm. The countable family of seminorms expressing those bounds makes the space a first countable locally convex space. Completeness, the Fréchet property, and the Montel property are not proved. Smooth compactly supported functions are Schwartz. Against a measure of temperate growth — some negative power of \(1+\lVert x\rVert\) is integrable — Schwartz functions are integrable, the integral is continuous and linear, and for \(p\ge 1\) they map continuously into \(L^p\). On a finite-dimensional domain, with the measure finite on compact sets, they are dense in \(L^p\) for finite \(p\) (`Analysis/Distribution/SchwartzSpace/Basic.lean`, `Analysis/Distribution/TemperateGrowth.lean`).

On a finite-dimensional real inner product space the Fourier transform is a continuous linear endomorphism of Schwartz space. If the values are complete, inversion holds and the transform is a continuous linear equivalence. Derivatives pass through the transform as multiplication by \(\pm 2\pi i\langle\cdot,m\rangle\). Plancherel for Schwartz functions with values in a complete complex inner product space preserves the integrated inner product, and the \(L^2\) norms. The pointwise bound is the \(L^1\) norm (`Analysis/Distribution/SchwartzSpace/Fourier.lean`).

A tempered distribution is a continuous complex-linear map on complex Schwartz space, topologized by pointwise convergence rather than by the strong dual topology. Temperate measures, temperate functions, Schwartz functions, and \(L^p\) functions for \(p\ge 1\) embed into tempered distributions; the \(L^p\) embedding is injective in finite dimensions when the measure is locally finite. The Fourier transform, defined by transposition, is a continuous linear equivalence of tempered distributions and agrees on Schwartz functions with the function transform. The transform of the Dirac mass at the origin is Lebesgue measure. Multiplication by a temperate function, differentiation, and the Laplacian are continuous, and the first two do not enlarge support (`Analysis/Distribution/TemperedDistribution.lean`, `Analysis/Distribution/Support.lean`).

A Fourier multiplier by a scalar function \(g\) is \(\mathcal{F}^{-1}\circ(g\cdot)\circ\mathcal{F}\), on Schwartz functions and on tempered distributions. The multiplication is zero unless \(g\) has temperate growth. Multipliers compose by multiplication of symbols. The directional derivative and the Laplacian are multipliers, by \(2\pi i\langle\cdot,m\rangle\) and by \(-(2\pi)^2\lVert x\rVert^2\) respectively (`Analysis/Distribution/FourierMultiplier.lean`). Fourier multipliers with suitable symbol estimates are translation-invariant pseudodifferential operators; polynomial symbols already give differential operators of positive order. What is missing here is the general theory of symbol classes, quantization of symbols depending on both position and frequency, and the associated composition formula.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

TauCeti proves convergence of compactly supported smooth cutoffs in the Schwartz topology, including explicit estimates in each Schwartz seminorm ([cutoff approximation](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Distribution/SchwartzSpace/Cutoff.lean)). It also develops weak Sobolev spaces and proves distributional fundamental-solution identities for the Euclidean Laplacian; see Sections 26 and 38. These extend distributional analysis, but no symbol classes, pseudodifferential quantization, wavefront sets, or Fourier integral operator calculus were located.

## Topics of Section 30 not found in either inspected library

No file defines a pseudodifferential operator, a symbol class \(S^m_{\rho,\delta}\), a Kohn–Nirenberg quantization, or a Weyl quantization. Searches for pseudodifferential operators, \(\Psi\)DO, wavefront set, Fourier integral operator, microlocal analysis, semiclassical analysis, Weyl quantization, and Kohn–Nirenberg found nothing in this subject. The name of the Weyl group occurs in the Lie-theory files and is unrelated.

In particular, the following are absent:

- Symbol estimates, asymptotic summation of symbols, and the polyhomogeneous symbol calculus.
- Kohn–Nirenberg and Weyl quantization, the operator product, and the asymptotic expansion of a composition.
- Elliptic parametrices, essential support, and the continuity of pseudodifferential operators on Sobolev or Hölder scales.
- The singular support of a distribution in the base space, its wavefront set in the cotangent bundle with the zero section removed, and propagation of singularities.
- Oscillatory integrals, Lagrangian distributions, canonical relations, and Fourier integral operators.
- Microlocal defect measures, semiclassical measures, the semiclassical pseudodifferential calculus, and semiclassical defect measures.
- Paradifferential operators and any calculus adapted to low regularity.
- Distributions, pseudodifferential operators, or Fourier integral operators on manifolds, and the Schwartz kernel theorem.

The distributional constructions that do exist are those of the section 16 note: test functions, distributions on open sets of real vector spaces, Schwartz space, tempered distributions, and Fourier multipliers.
