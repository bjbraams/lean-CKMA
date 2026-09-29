# 19. Banach Lattices, Positive Operators, and Ordered Structures

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. The root for the ordered-norm material in this section is `Mathlib.Analysis.Normed.Order.Lattice`.

**Namespaces.** The solid-norm axiom is `HasSolidNorm`. Consequences for the lattice operations use `LatticeOrderedAddCommGroup`.

This note records the solid-norm axiom on a normed lattice-ordered group. Combined with the usual real vector-lattice and completeness structures, it expresses the basic Banach-lattice setting. A developed Banach-lattice theory was not found.

## Solid norms

A norm on a normed additive group which is a lattice is solid when \(|x| \le |y|\) implies \(\|x\| \le \|y\|\). Balls about the origin are then solid. The real numbers, the rationals, and the integers carry solid norms (`Analysis/Normed/Order/Lattice.lean`).

If the group is also an ordered additive monoid, a solid norm makes the norm topology a topological lattice. The supremum and the infimum are \(1\)-Lipschitz in each argument, and so are the positive and negative parts. The nonnegative cone is closed, and the order is closed. The opening comment of the file says that a class of normed lattice-ordered groups will be defined; the class that is declared is the solid-norm axiom. The references point to Meyer-Nieberg’s treatment of Banach lattices. No representation theorem is proved (`Analysis/Normed/Order/Lattice.lean`).

Bounded continuous functions with values in a solid normed lattice also carry a solid sup norm (`Topology/ContinuousMap/Bounded/Normed.lean`, `BoundedContinuousFunction.instHasSolidNorm`). Thus function-space examples exist, even without a single bundled class named “Banach lattice”.

Positive maps and completely positive maps of \(C^\star\)-algebras are operators of Section 23. They are not a lattice theory of positive operators on ordered Banach spaces.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

A small positive-operator addition is the Koopman operator on almost-everywhere equivalence classes of measurable real functions. Composition with a measure-preserving transformation is bundled as a real-linear operator, proved positive and monotone, and shown to preserve multiplication and the constant one ([Koopman–Markov operator](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Probability/Ergodic/KoopmanMarkov.lean)). The file works on measurable-function classes; it does not construct an abstract Banach-lattice theory or prove an AL/AM representation theorem.

## Topics of Section 19 not found in either inspected library

- A developed theory of Banach lattices, including AL-spaces and AM-spaces, beyond the solid-norm and lattice infrastructure above.
- The Kakutani representation of AL-spaces and AM-spaces.
- A lattice-theoretic calculus of positive operators.
