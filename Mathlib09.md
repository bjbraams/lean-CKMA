# 9. Malliavin Calculus, Rough Paths, and Stochastic PDE

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. There is no import root for this subject.

**Namespaces.** None are declared for this subject.

Filename and text searches for Malliavin calculus, rough paths, regularity structures, paracontrolled distributions, stochastic PDE, and Hairer found no development of this theory. The string Hairer occurs only as a bibliographic citation of an introduction to stochastic PDE in the Gaussian and Fernique files, and as `Archive/Hairer.lean`, which constructs a compactly supported smooth function whose integral against a polynomial of bounded degree recovers the value of the polynomial at the origin. Neither is stochastic PDE. Real Brownian motion is described in `Mathlib08.md`, and Fernique’s theorem in `Mathlib06.md`.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

One finite-dimensional ingredient of Gaussian analysis is present. The normalized Hermite polynomials form a Hilbert basis of \(L^2(\gamma)\) for the standard Gaussian measure \(\gamma\) on the line, with Parseval's identity and expansions, and their tensor products form a Hilbert basis of \(L^2(\gamma^{\otimes n})\) on a finite product ([one dimension](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Probability/Distributions/Gaussian/Hermite/Basis.lean), [finite products](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Probability/Distributions/Gaussian/Hermite/Pi/Basis.lean)). This is the finite-dimensional Wiener chaos decomposition. Mathlib has the Hermite polynomials and their Gaussian-derivative formula (`RingTheory/Polynomial/Hermite/Gaussian.lean`), but not the basis property. The infinite-dimensional chaos decomposition, the Cameron–Martin space, and the Ornstein–Uhlenbeck semigroup were not found.

No additional implemented Malliavin calculus, rough-path integration, regularity structures, paracontrolled calculus, or stochastic PDE theory was located in the inspected TauCeti library. The probability, Sobolev, and deterministic semigroup results recorded in Sections 6, 8, 24, and 26 are relevant prerequisites, but do not establish any of these theories.

## Topics of Section 9 not found in either inspected library

- Malliavin calculus: the Malliavin derivative, the Skorokhod integral, and the integration-by-parts formula on Wiener space.
- Infinite-dimensional Gaussian analysis in the sense of Bogachev and Da Prato: the Cameron–Martin space and theorem, the Wiener chaos decomposition beyond finitely many coordinates, and the Ornstein–Uhlenbeck semigroup and Mehler's formula. Gaussian measures on Banach spaces and Fernique's theorem are in Mathlib (Section 6).
- Rough paths, controlled paths, and the rough integral, including Young integration as used in that theory.
- Regularity structures and paracontrolled distributions.
- Stochastic partial differential equations, their well-posedness, and renormalisation.
