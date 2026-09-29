# 53. Elliptic Operators on Manifolds, Index Theory, and Spectral Geometry

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. Some roots below are directory prefixes; the individual `.lean` files cited are the importable modules. There is no root for elliptic operators on manifolds, the Atiyah–Singer index theorem, Hodge theory, or spectral geometry. The two neighbouring theories named below are `Mathlib.Analysis.Normed.Operator.Fredholm` and `Mathlib.Analysis.Distribution.DerivNotation`.

**Namespaces.** There is no namespace for the Laplace–Beltrami operator, the Dirac operator, or an analytic index. `ContinuousLinearMap.IsFredholm` is the Fredholm condition of Section 21. `Laplacian` is the notation typeclass whose Euclidean instance is a sum of second derivatives.

Elliptic theory on manifolds was not found. A search through `Geometry` for an elliptic operator, the Atiyah–Singer theorem, Hodge theory, a Weyl law, spectral geometry, a Dirac operator, and the Laplace–Beltrami operator returns nothing in that sense.

Fredholm operators, as in Section 21, are continuous linear maps that are strict, with closed finite-codimension range and finite-dimensional topologically complemented kernel (`Analysis/Normed/Operator/Fredholm/Basic.lean`). When the scalar field and the domain are complete and the codomain is normed, the set of Fredholm operators is open in the operator norm, and the index is locally constant (`Analysis/Normed/Operator/Fredholm/Open.lean`). That is the operator-theoretic index, not the index of an elliptic complex on a manifold.

The Euclidean Laplacian is the notation \(\Delta\) of `Analysis/Distribution/DerivNotation.lean`. On an inner-product space it is realised as the sum of second directional derivatives along an orthonormal basis, and the sum does not depend on the basis. It is not the Laplace–Beltrami operator of a Riemannian metric.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

The abstract index-theory foundations are appreciably stronger: TauCeti proves Fredholm stability and index invariance under compact perturbations, local constancy of the index, and the adjoint index identity on Hilbert spaces ([compact perturbations](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Fredholm/CompactPerturbation.lean), [local constancy](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Fredholm/SmallPerturbation.lean), [adjoints](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Fredholm/Adjoint.lean)).

For bounded Euclidean domains and a symmetric coercive divergence-form energy form on \(H^1_0\), it constructs a compact \(L^2\) solution operator, a Dirichlet eigenfunction Hilbert basis, and a Rayleigh characterization of the first eigenvalue ([Dirichlet spectrum](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/PDE/Spectrum.lean)). This is elliptic spectral theory on domains, without a smooth-boundary assumption, but not a Weyl asymptotic law or an elliptic-operator theory on general manifolds. TauCeti's files under `Geometry/Hodge` concern algebraic Hodge structures; they do not establish harmonic representatives or the Hodge theorem on compact Riemannian manifolds.

## Topics of Section 53 not found in either inspected library

- Elliptic differential operators on manifolds, and their symbols.
- The Atiyah–Singer index theorem, and Hodge theory on a compact Riemannian manifold.
- The Dirac operator, the spin Laplacian, and the Laplace–Beltrami operator.
- A Weyl law and general manifold spectral geometry. TauCeti proves the Dirichlet spectral theorem for symmetric coercive forms on bounded Euclidean domains.
