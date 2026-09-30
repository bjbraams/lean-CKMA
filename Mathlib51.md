# 51. Integrable Systems and Riemann–Hilbert Methods

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. There is no root for integrable systems or for Riemann–Hilbert problems. The Lie-algebra file that the name \(\mathfrak{sl}_2\) suggests is `Mathlib.Algebra.Lie.Sl2`.

**Namespaces.** `IsSl2Triple` is the predicate that three elements of a Lie algebra satisfy the \(\mathfrak{sl}_2\) relations. It is not a namespace of integrable systems.

A search for Riemann–Hilbert problems, integrable systems, the Korteweg–de Vries equation, solitons, Lax pairs, and isomonodromy returns nothing in that sense.

`Algebra/Lie/Sl2.lean` defines an \(\mathfrak{sl}_2\) triple \((h,e,f)\) in a Lie algebra by \(h\neq 0\), \([e,f]=h\), \([h,e]=2e\), and \([h,f]=-2f\), and studies primitive vectors in finite-dimensional representations. That is the representation theory of \(\mathfrak{sl}_2\), not an integrable system.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

TauCeti contains geometric prerequisites for Hamiltonian analysis. On the linear cotangent space \(V\times V'\), with continuous dual \(V'\), it constructs the Liouville one-form \(\lambda_{(q,p)}(\delta q,\delta p)=p(\delta q)\) and proves that the canonical symplectic form is \(-d\lambda\), without a finite-dimensional restriction ([linear cotangent model](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Geometry/Symplectic/Cotangent/Liouville.lean)). This is an exact symplectic construction, not an integrable Hamiltonian system. The linear symplectic algebra around it (Lagrangian subspaces, compatible almost complex structures) and constant-structure \(J\)-holomorphic maps with their energy identity are also developed, as geometric rather than integrable-systems content. No Riemann–Hilbert boundary-value problem, isomonodromy, Lax-pair, or soliton theorem was located.

## Topics of Section 51 not found in either inspected library

- Riemann–Hilbert boundary-value problems, and isomonodromy.
- The Korteweg–de Vries equation, solitons, and Lax pairs.
- Any other integrable Hamiltonian system, in finite or infinite dimensions: Poisson brackets, Hamiltonian vector fields on symplectic manifolds, the Liouville–Arnold theorem and action–angle variables.
- Inverse scattering, Painlevé transcendents, and the nonlinear steepest-descent method of Deift–Zhou.
