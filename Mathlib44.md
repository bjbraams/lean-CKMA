# 44. Riemann Surfaces, Quasiconformal Mappings, and Teichmüller Theory

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** The relevant foundations are `Mathlib.Geometry.Manifold.IsManifold.Basic`, `Mathlib.Geometry.Manifold.ContMDiff.Defs`, `Mathlib.Geometry.Manifold.Complex`, and `Mathlib.Analysis.Complex.UpperHalfPlane.Manifold`.

**Namespaces.** `IsManifold`, `ContMDiff`, `MDifferentiable`, and `UpperHalfPlane`.

The general manifold framework supports complex atlases and holomorphic maps. A boundaryless manifold modeled on \(\mathbb C\), with complex-smooth transition maps, provides the atlas structure underlying a Riemann surface. Hausdorffness and second countability are separate hypotheses, as in the general manifold library. It would therefore be too strong to say that holomorphic atlases are absent. What was not found is a dedicated global theory of Riemann surfaces, quasiconformal mappings, or their moduli.

## Complex-manifold foundations

The upper half-plane is a one-dimensional complex manifold via its inclusion in \(\mathbb C\). Möbius transformations of positive determinant act holomorphically (`Analysis/Complex/UpperHalfPlane/Manifold.lean`). Its hyperbolic metric and invariant measure are described in Section 40; infinitesimal conformality is Section 43.

The maximum principle is proved on boundaryless complex manifolds, including constancy of holomorphic functions into a complex normed space on a connected compact complex manifold (`Geometry/Manifold/Complex.lean`; see Section 45). These are genuine complex-manifold results, though they do not provide uniformization or a classification of surfaces.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

TauCeti develops concrete Riemann surfaces from discrete subgroups of \(\mathrm{PSL}_2(\mathbb R)\): coarse upper-half-plane quotients and their cusp extensions have complex-manifold atlases, including the cusp charts ([cusp-extended quotient](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Complex/Fuchsian/Compactification/Manifold.lean)). Despite the type name `CompactifiedQuotient`, compactness is a further theorem under a compact-truncation condition and finiteness of cusp orbits; it should not be asserted for every discrete subgroup ([compactness criterion](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Complex/Fuchsian/Compactification/Compactness.lean)).

For holomorphic maps between Riemann surfaces, local multiplicity is defined independently of charts and proved multiplicative under composition; multiplicity one characterizes local injectivity ([multiplicity](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Complex/RiemannSurface/LocalMultiplicity.lean)). The holomorphic-germ sheaf on the plane and monodromy are also implemented (Sections 40 and 45). These are substantial surface constructions, but no general uniformization theorem, Beltrami-equation theory, or Teichmüller theory was located.

## Topics of Section 44 not found in either inspected library

- General uniformization and global classification of Riemann surfaces, beyond the Fuchsian-quotient constructions and local multiplicity theory described above.
- Quasiconformal mappings, the Beltrami equation, and holomorphic motions.
- Teichmüller space, the Teichmüller metric, and quadratic differentials. The order-theoretic Teichmüller–Tukey lemma and the Teichmüller representatives in Witt vectors are unrelated to this subject.
