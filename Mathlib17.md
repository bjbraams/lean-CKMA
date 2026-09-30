# 17. Banach Space Geometry, Bases, and Operator Ideals

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. The material that belongs to this section and is present in the checkout is reached through `Mathlib.Analysis.Normed.Module.Bases`, `Mathlib.Analysis.Convex.Uniform`, and `Mathlib.Analysis.InnerProductSpace.Convex`. Compact and Fredholm operators are imported with Sections 15 and 21.

**Namespaces.** Bases are `GeneralSchauderBasis`, `SchauderBasis`, `UnconditionalSchauderBasis`, and `RankOneDecomposition`. Uniform convexity is `UniformConvexSpace`.

This note records the basis theory that the checkout actually contains, and neighboring convexity and tensor-product constructions. Type, cotype, and operator ideals were not found.

## Bases

Classical Schauder bases and unconditional Schauder bases are constructed in Section 15. A basis consists of vectors and continuous coordinate functionals, biorthogonal, with every vector equal to the corresponding sum. On a Banach space the finite-rank projections attached to the basis are uniformly bounded. Nested finite-rank projections converging pointwise to the identity, with rank-one successive differences, produce a classical Schauder basis. A Hilbert basis is an unconditional Schauder basis, and a Hilbert basis indexed by \(\mathbb{N}\) is a classical one (`Analysis/Normed/Module/Bases.lean`, `Analysis/InnerProductSpace/l2Space.lean`).

## A neighbouring convexity statement

A real seminormed group is uniformly convex when, for every \(\varepsilon > 0\), some \(\delta > 0\) forces \(\|x+y\| \le 2-\delta\) whenever \(x\) and \(y\) are unit vectors at least \(\varepsilon\) apart. A real inner product space is uniformly convex. The file marks the Milman–Pettis theorem and Hanner’s inequalities as not proved. The development belongs with Section 12 (`Analysis/Convex/Uniform.lean`, `Analysis/InnerProductSpace/Convex.lean`).

Compact operators and Fredholm operators, including the index and its local constancy, are Sections 15 and 21.

The algebraic tensor product of a finite family of normed spaces carries a projective seminorm, with the isometric universal property for continuous multilinear maps and norm bounds for tensor products of operators (`Analysis/Normed/Module/PiTensorProduct/ProjectiveSeminorm.lean`). Section 16 gives its scope and limitations. It does not provide a theory of nuclear or summing operators.

## Complemented subspaces, L-projections, and isometries

A closed subspace of a Banach space is complemented when it is the range of a continuous linear projection. In a Banach space, algebraic complements that are both closed are topological complements, by the open mapping theorem; finite-dimensional subspaces and closed subspaces of finite codimension are complemented (`Analysis/Normed/Module/Complemented.lean`, `Topology/Algebra/Module/FiniteDimension.lean`). Sobczyk's and Pełczyński's theorems on complementation in \(c_0\) and \(\ell^p\) were not found.

An L-projection on a normed space is a projection \(P\) with \(\|x\|=\|Px\|+\|(1-P)x\|\), and an M-projection one with \(\|x\|=\max(\|Px\|,\|(1-P)x\|)\). The L-projections commute and form a Boolean algebra (`Analysis/Normed/Module/MStructure.lean`). The Boolean algebra of M-projections, completeness of the L-projection algebra, and M-ideals are listed there as motivation, not proved.

The Mazur–Ulam theorem, the starting point of the nonlinear classification theory of Benyamini–Lindenstrauss: a surjective isometry between real normed spaces is affine (`Analysis/Normed/Affine/MazurUlam.lean`). Lipschitz and uniform classification of Banach spaces beyond this were not found.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

TauCeti proves a part of compact-operator and Fredholm theory useful alongside operator ideals. For a compact operator \(K\) on a Banach space, \(I-K\) has finite-dimensional kernel, closed range, and finite-dimensional cokernel ([Riesz theory](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Normed/Operator/Compact/RieszTheory.lean)). Compact perturbations preserve the Fredholm index ([source](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Fredholm/CompactPerturbation.lean)). These are operator-theoretic additions; no general approximation-property theory, type/cotype, nuclear-operator ideal, or Schatten-class construction was located.

## Topics of Section 17 not found in either inspected library

- Rademacher type and cotype, Khintchine's and Kahane's inequalities, and Grothendieck's inequality.
- Banach–Mazur distance, John's ellipsoid theorem, and the local theory of finite-dimensional normed spaces.
- The Radon–Nikodým property, smoothness and renorming theory, and the classical structure theory of \(c_0\), \(\ell^p\), and \(L^p\) (Pitt's theorem, Pełczyński's decomposition method).
- The approximation property.
- Schatten classes.
- Nuclear operators and operator ideals.
- A geometry of bases beyond the Schauder and unconditional bases of Section 15. The Milman–Pettis theorem is a stated omission in the uniform-convexity file, not a theorem of this section.
