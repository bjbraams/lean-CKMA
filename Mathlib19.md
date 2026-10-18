# 19. Banach Lattices, Positive Operators, and Ordered Structures

Checked against Mathlib commit `f039e1b8a616d45782a5c7fc5e7909249c36b8ea` (2026-10-18, Lean `v4.36.0-rc1`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. The root for the ordered-norm material in this section is `Mathlib.Analysis.Normed.Order.Lattice`.

**Namespaces.** The solid-norm axiom is `HasSolidNorm`. Consequences for the lattice operations use `LatticeOrderedAddCommGroup`.

This note records the solid-norm axiom on a normed lattice-ordered group, and the ordered-vector-space facts that support it. Combined with the usual real vector-lattice and completeness structures, it expresses the basic Banach-lattice setting. A developed Banach-lattice theory was not found.

## Solid norms

A norm on a normed additive group which is a lattice is solid when \(|x| \le |y|\) implies \(\|x\| \le \|y\|\). Balls about the origin are then solid. The real numbers, the rationals, the integers, and finite products \(\iota\to\mathbb R\) with the sup norm carry solid norms, and the order dual of a solid normed lattice is again solid (`Analysis/Normed/Order/Lattice.lean`).

If the group is also an ordered additive monoid, a solid norm makes the norm topology a topological lattice. The supremum and the infimum are \(1\)-Lipschitz in each argument, and so are the positive and negative parts. The nonnegative cone is closed, and the order is closed. The module docstring speaks of a class `NormedLatticeAddCommGroup`; the class actually declared is the solid-norm axiom `HasSolidNorm`, used together with the separate lattice and normed-group structures. The references point to Meyer-Nieberg’s treatment of Banach lattices. No representation theorem is proved (`Analysis/Normed/Order/Lattice.lean`).

Bounded continuous functions with values in a solid normed lattice also carry a solid sup norm (`Topology/ContinuousMap/Bounded/Normed.lean`, `BoundedContinuousFunction.instHasSolidNorm`). The Lebesgue spaces \(L^p(\mu;E)\), \(1\le p\le\infty\), with values in a solid normed lattice \(E\), are lattices under the almost-everywhere order, with \(\sup\), \(\inf\) and \(|\cdot|\) computed pointwise almost everywhere; their norm is solid, and the order is closed when the positive cone of \(E\) is closed (`MeasureTheory/Function/LpOrder.lean`, `MeasureTheory.Lp.instLattice`, `MeasureTheory.Lp.instHasSolidNorm`). Thus the standard function-space Banach lattices \(C_b\) and \(L^p\) exist as instances, even without a single bundled class named “Banach lattice”.

## Ordered vector spaces and positive functionals

The algebra of lattice-ordered groups supplies the elementary Riesz-space identities: absolute value, positive and negative parts with \(a=a^+-a^-\) and \(|a|=a^++a^-\), and the lattice inequalities between them (`Algebra/Order/Group/Lattice.lean`, `Algebra/Order/Group/PosPart.lean`, `Algebra/Order/Group/Unbundled/Abs.lean`). Positive linear maps between ordered modules are bundled as linear order homomorphisms, with a continuous variant (`Algebra/Order/Module/PositiveLinearMap.lean`, `Topology/Algebra/Module/ContinuousLinearMap/Positive.lean`).

The M. Riesz extension theorem, basic to ordered vector spaces and to the moment problem: if \(s\) is a convex cone in a real vector space \(E\), \(p\) a subspace with \(p+s=E\), and \(f\) a linear functional on \(p\) nonnegative on \(p\cap s\), then \(f\) extends to a linear functional on \(E\) nonnegative on \(s\). The Hahn–Banach dominated extension is deduced from it (`Analysis/Convex/Cone/Extension.lean`).

For nonnegative square matrices, irreducibility (strong connectivity of the associated quiver) and primitivity are defined, with the path characterization of positive entries of powers and the implication primitive \(\Rightarrow\) irreducible (`LinearAlgebra/Matrix/Irreducible/Defs.lean`, `Matrix.IsIrreducible`, `Matrix.IsPrimitive`, `Matrix.isIrreducible_iff_exists_pow_pos`). The Perron–Frobenius eigenvalue theorem itself is not proved.

Positive maps and completely positive maps of \(C^\star\)-algebras are operators of Section 23. They are not a lattice theory of positive operators on ordered Banach spaces.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6ebb29f84b4d`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

A small positive-operator addition is the Koopman operator on almost-everywhere equivalence classes of measurable real functions. Composition with a measure-preserving transformation is bundled as a real-linear operator, proved positive and monotone, shown to preserve multiplication and the constant one, and compatible with composition and iteration of the transformation; its fixed points are the classes of \(T\)-invariant functions ([Koopman–Markov operator](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Probability/Ergodic/KoopmanMarkov.lean)). The file works on measurable-function classes; it does not construct an abstract Banach-lattice theory or prove an AL/AM representation theorem.

## Topics of Section 19 not found in either inspected library

- A developed theory of Banach lattices, including AL-spaces and AM-spaces, beyond the solid-norm and lattice infrastructure above.
- The Kakutani representation of AL-spaces and AM-spaces.
- A lattice-theoretic calculus of positive operators: order continuity, bands and band projections, Dedekind completeness of Riesz spaces, and the Freudenthal spectral theorem.
- Spectral theory of positive operators: the Krein–Rutman theorem, Perron–Frobenius theory beyond the matrix definitions of irreducibility and primitivity noted above, and positive semigroups in the sense of Nagel and Engel–Nagel.
