# 42. Hardy, Bergman, and Model Spaces; Operators on Analytic Function Spaces

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. Some roots below are directory prefixes; the individual `.lean` files cited are the importable modules. The only files in this checkout that touch the words of this section are `Mathlib.Analysis.Complex.CanonicalDecomposition`, `Mathlib.Analysis.InnerProductSpace.Reproducing`, and `Mathlib.Analysis.InnerProductSpace.Symmetric`. None of them is a development of Hardy or Bergman spaces.

**Namespaces.** Canonical factors are `Complex`. Reproducing-kernel Hilbert spaces are `RKHS`. The Hellinger–Toeplitz theorem is the statement about symmetric operators in `Analysis/InnerProductSpace/Symmetric.lean`, not an operator on a space of analytic functions.

The operator theory of analytic function spaces was not found. The disc and the upper half-plane, including the Poincaré metric and the invariant measure on the half-plane, are Section 40. Reproducing-kernel Hilbert spaces, in the abstract sense of a Hilbert space of functions whose kernel functions are dense and whose kernel is a positive semidefinite matrix, are Section 29 (`Analysis/InnerProductSpace/Reproducing.lean`).

The one construction that uses the name of a Blaschke product is the finite canonical decomposition of a meromorphic function on a disc. The factor \((R^2-\overline{w}\,z)/(R(z-w))\) is meromorphic and, for \(R>0\) and \(|w|<R\), has a single pole at \(w\) and modulus one on the circle of radius \(R\). A finite product of such factors rewrites a meromorphic function on a disc, up to an analytic factor without zeros. The file calls this a finite Blaschke product and uses it for the counting formulae of Section 41. It does not define an infinite Blaschke product, an inner function, or a factorization of a function in a Hardy space (`Analysis/Complex/CanonicalDecomposition.lean`).

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

The Herglotz representation is proved: if \(F\) is holomorphic on the unit disc with nonnegative real part, then
\[
 F(w)=\int_{|z|=1}\frac{z+w}{z-w}\,d\mu(z)+i\operatorname{Im}F(0)
\]
for a finite positive measure \(\mu\), and conversely such transforms have those properties ([Herglotz](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Complex/Herglotz.lean)). This is relevant boundary-measure theory for analytic functions. Its half-plane counterpart, the Nevanlinna representation of Pick functions, is recorded in Section 13 ([Pick functions](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Complex/Pick/Basic.lean)). TauCeti also develops disc automorphisms and Schwarz–Pick contraction (Section 43), but no Hardy/Bergman normed spaces, infinite Blaschke products, Toeplitz/Hankel operators, or Beurling invariant-subspace theorem were located.

## Topics of Section 42 not found in either inspected library

- The Hardy spaces \(H^p\), the Bergman spaces, and the model spaces of Sz.-Nagy–Foiaș. The name Hardy, where it occurs, belongs to real-variable inequalities and is not this theory.
- Inner functions, infinite Blaschke products, and singular inner functions. Only the finite canonical factors above are present.
- Toeplitz operators, Hankel operators, and Beurling’s theorem on invariant subspaces. The Hellinger–Toeplitz theorem, that a symmetric everywhere-defined operator on a Hilbert space is continuous, is a theorem of unbounded-operator theory and is not an operator on a space of holomorphic functions.
- Boundary behaviour: Fatou's theorem on nontangential limits, the Poisson integral of an \(L^p\) boundary function, and the F. and M. Riesz theorem.
- Carleson measures, the corona theorem, BMOA, interpolating sequences, and Nevanlinna–Pick interpolation.
- Composition operators, the disc algebra, and Fock spaces.
- The shift, the compressed shift, and reproducing kernels specialized to the disc or the half-plane. The abstract reproducing-kernel Hilbert space is Section 29, and the geometry of the disc and the half-plane is Section 40.
