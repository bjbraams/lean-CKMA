# 25. Integral Equations and Classical Operator Methods

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. Some roots below are directory prefixes; the individual `.lean` files cited are the importable modules. No root in this checkout develops integral equations. The related root is `Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative`, together with `Mathlib.Analysis.ODE` for the integral form of an ordinary differential equation.

**Namespaces.** None in this checkout are devoted to integral equations. The Fredholm alternative of section 21 lies in `IsCompactOperator`. The Picard–Lindelöf theorem lies in `IsPicardLindelof`.

This note records that classical integral-equation theory was not found, and points to the compact-operator theorem that shares Fredholm’s name.

## What is present nearby

The Fredholm alternative for a compact operator on a Banach space is section 21. If \(T\) is compact and \(\mu\neq 0\), then \(\mu\) is an eigenvalue or \(\mu\) is in the resolvent set (`Analysis/Normed/Operator/Compact/FredholmAlternative.lean`).

The integral equation attached to a Lipschitz vector field is the integral form of an ordinary differential equation. Existence and uniqueness for that equation are the Picard–Lindelöf theorem, in section 31 (`Analysis/ODE/PicardLindelof.lean`, `Analysis/ODE/ExistUnique.lean`).

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

Schur's test is proved for a measurable nonnegative kernel whose row integrals are bounded by \(A\) and column integrals by \(B\): for finite \(1\le p\), its integral operator has the \(L^p\) estimate with constant \(A^{1-1/p}B^{1/p}\). The formal statement is a nonnegative extended-integral inequality, with the bounds required almost everywhere ([Schur's test](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/MeasureTheory/Integral/SchurTest.lean)).

For compact operators on Banach spaces, TauCeti proves the finite-dimensional kernel/cokernel and closed-range assertions for \(I-K\) ([Riesz theory](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Normed/Operator/Compact/RieszTheory.lean)). This supplies abstract Fredholm tools for integral equations. A theorem verifying compactness and solving a stated general class of Fredholm integral-kernel equations, a Volterra resolvent-kernel theory, or a Fredholm determinant was not located.

## Topics of Section 25 not found in either inspected library

- Volterra integral equations and resolvent kernels. The Gronwall inequality, which bounds solutions of Volterra-type integral inequalities, is proved in `Analysis/ODE/Gronwall.lean`, with a discrete form in `Analysis/ODE/DiscreteGronwall.lean`.
- Fredholm integral equations of the first or second kind, beyond the spectral alternative for compact operators in section 21.
- The Fredholm determinant.
- Nyström methods, and any other numerical method for integral equations.
- Singular integral equations with Cauchy kernel, the Riemann–Hilbert boundary problems of Muskhelishvili and Gakhov, and boundary integral operators (layer potentials) for elliptic boundary value problems. Cauchy principal values of contour integrals are present in TauCeti (Section 40), but not as a singular-integral-operator theory.
