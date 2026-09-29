# 22. Unbounded Operators, Spectral Theory, and Mathematical Physics

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. The roots for this section are `Mathlib.Analysis.InnerProductSpace.LinearPMap`, `Mathlib.Analysis.InnerProductSpace.Laplacian`, `Mathlib.Analysis.InnerProductSpace.LaxMilgram`, and `Mathlib.Topology.Algebra.Module.LinearPMap`.

**Namespaces.** `LinearPMap`, `ContinuousLinearMap`, `Submodule`, `InnerProductSpace`, `Laplacian`, and `IsCoercive`.

This note records partially defined operators and their adjoints, the Euclidean Laplacian as a pointwise differential operator, and the Lax–Milgram theorem.

## Partially defined operators

A partially defined linear map carries a domain. It is closed when its graph is closed, and closable when the closure of the graph is still a graph (`Topology/Algebra/Module/LinearPMap.lean`).

On inner product spaces, \(T\) is a formal adjoint of \(S\) when \(\langle Tx, y\rangle = \langle x, Sy\rangle\) for \(x\) in the domain of \(T\) and \(y\) in the domain of \(S\). The adjoint \(T^\dagger\) is defined for every partially defined map. Its domain consists of those vectors \(y\) for which \(z\mapsto\langle y, Tz\rangle\) is continuous on the domain of \(T\). If the domain of \(T\) is dense and the source is a Hilbert space, the adjoint is the Riesz representative of that functional: it is a formal adjoint, it contains every formal adjoint, and its graph is closed. If the domain is not dense, the adjoint is defined to be the zero map on its domain. A self-adjoint partially defined operator is closed (`Analysis/InnerProductSpace/LinearPMap.lean`).

The bounded adjoint and this adjoint agree when the bounded operator is viewed as a partially defined operator with dense domain.

## The Laplacian

For a function from a finite-dimensional real inner product space into a real normed space, the Laplacian is the second derivative contracted against the canonical covariant tensor of the domain. It equals the sum of the second directional derivatives along any orthonormal basis. On \(\mathbb{R}\) it is the ordinary second derivative. A constant function has Laplacian zero. Functions that agree on a neighborhood have Laplacians that agree at the point. On twice continuously differentiable functions the Laplacian is \(\mathbb{R}\)-linear: it preserves addition, subtraction, negation, and scalar multiplication, and it commutes with postcomposition by a continuous linear map (`Analysis/InnerProductSpace/Laplacian.lean`).

This is a pointwise differential operator. The file does not realize the Laplacian as an unbounded operator on \(L^2\), and it does not prove self-adjointness or a spectral theorem.

## Lax–Milgram

Let \(V\) be a real Hilbert space, and let \(B\) be a bounded bilinear form \(V\times V\to\mathbb{R}\). The form is coercive when some constant \(C>0\) satisfies \(C\lVert u\rVert^2\le B(u,u)\) for every \(u\). After the Riesz identification \(V^*\cong V\), the operator \(B^\sharp\) defined by \(\langle B^\sharp v,w\rangle=B(v,w)\) is a continuous linear automorphism of \(V\). Thus, for every continuous linear functional \(\ell\in V^*\), there is a unique \(u\in V\) satisfying \(B(u,w)=\ell(w)\) for every \(w\), and the solution depends continuously and linearly on \(\ell\) (`Analysis/InnerProductSpace/LaxMilgram.lean`, `Analysis/Normed/Operator/NormedSpace.lean`).

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

Stone's theorem is proved: a self-adjoint partially defined operator on a complex Hilbert space gives a unique strongly continuous unitary group whose complex generator is \(iA\); conversely the unitary-group generator is skew-self-adjoint ([unbounded Stone theorem](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Semigroups/Group/Stone/Unbounded.lean), [unitary generators](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Semigroups/Group/Stone/Basic.lean)). The general closed-generator, resolvent, and generation results are described in Section 24.

The normalized Hermite functions form a Hilbert basis of \(L^2(\mathbb R)\) and satisfy the pointwise harmonic-oscillator equation \(-\psi_n''+x^2\psi_n=(2n+1)\psi_n\) ([basis](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/SpecialFunctions/Hermite/Function/HilbertBasis.lean), [eigen-equation](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Oscillator.lean)). These files do not identify a self-adjoint realization of the oscillator differential expression or prove a general Schrödinger spectral theorem.

## Topics of Section 22 not found in either inspected library

- A spectral theorem for unbounded self-adjoint operators, and a spectral measure in that setting.
- Deficiency indices and essential self-adjointness.
- Scattering theory.
- The Schrödinger operator as a self-adjoint operator.
- Self-adjointness, or a spectrum, for the Euclidean Laplacian defined above.
