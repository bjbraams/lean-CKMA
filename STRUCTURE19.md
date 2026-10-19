# Structure 19: Banach lattices, positive operators, and ordered structures

Part of the [Mathlib and TauCeti coverage series](STRUCTURE.md).
[Mathematical inventory](SYNOPSIS19.md); [bibliographical scope](CKMA-bib.md#ckma-19); [MSC2020 index](CKMA-MSC2020.md).

This file follows the thematic order and lettered subdivisions of the mathematical inventory. It records definitions, structures, and proved results, with supporting material identified separately. A topic heading locates the recorded statements; it does not assert coverage of every result in the corresponding synopsis.

**Source baseline.** Mathlib `911003dd6dea5df215dff57f2717be762e11a6ca` and TauCeti `5cdecf40e99d5a5ad0833afff31f5b007d68a149`, both of 2026-10-18, checked against local checkouts on 2026-10-19. See the [revision and source conventions](STRUCTURE.md#source-baseline-and-conventions).

**Mathlib source areas.** `Mathlib.Algebra.Order.Group` (lattice-ordered groups), `Mathlib.Analysis.Normed.Order.Lattice`, `Mathlib.Algebra.Order.Module.PositiveLinearMap`, `Mathlib.Analysis.Convex.Cone.Extension`, `Mathlib.Analysis.CStarAlgebra.PositiveLinearMap`, `Mathlib.Topology.ContinuousMap.Ideals`, `Mathlib.MeasureTheory.Function.LpOrder`, `Mathlib.MeasureTheory.Function.ConditionalExpectation`, and `Mathlib.LinearAlgebra.Matrix.Irreducible`.

**Namespaces.** The solid-norm axiom is `HasSolidNorm`. Consequences for the lattice operations use `LatticeOrderedAddCommGroup`. Positive maps are `PositiveLinearMap` and `PositiveContinuousLinearMap`. The TauCeti projective-metric material uses `TauCeti` and `Matrix`.

## Lattice structure, ideals, and bands

[Mathematical scope](SYNOPSIS19.md#lattice-structure-ideals-and-bands).

### Mathlib

**Lattice-ordered groups.** The algebra of lattice-ordered commutative groups supplies the elementary Riesz-space identities, stated multiplicatively and transferred to the additive setting: \(a^+-a^-=a\) (`posPart_sub_negPart`), \(a^++a^-=|a|\) (`posPart_add_negPart`), \(a^+\wedge a^-=0\) (`posPart_inf_negPart_eq_zero`), \(2(a\vee b)=a+b+|b-a|\) and \(2(a\wedge b)=a+b-|b-a|\) (`two_nsmul_sup_eq_add_add_abs_sub`, `two_nsmul_inf_eq_add_sub_abs_sub`), the triangle inequality \(|a+b|\le|a|+|b|\) (`abs_add_le`) and \(\bigl||a|-|b|\bigr|\le|a-b|\) (`abs_abs_sub_abs_le`). Every lattice-ordered commutative group is a distributive lattice (`AddCommGroup.toDistribLattice`). Sources: `Algebra/Order/Group/Lattice.lean`, `Algebra/Order/Group/PosPart.lean`, `Algebra/Order/Group/Unbundled/Abs.lean`. Solid sets (\(|y|\le|x|\), \(x\in s\Rightarrow y\in s\)) are defined as `LatticeOrderedAddCommGroup.IsSolid`; ideals, bands, disjoint complements, and Riesz decomposition are not developed.

The Dedekind–MacNeille completion of a partial order exists (`DedekindCut`, `Order/Completion.lean`). It is order-theoretic supporting material, not the vector-lattice Dedekind completion of result 7.

**Synopsis entries.** Covered: 19.1 (Mathlib, stated for lattice-ordered additive groups). Not covered: 19.2–19.8.

## Norms, order continuity, and monotone completeness

[Mathematical scope](SYNOPSIS19.md#norms-order-continuity-and-monotone-completeness).

### Mathlib

**Solid norms.** A norm on a normed additive group which is a lattice is solid when \(|x| \le |y|\) implies \(\|x\| \le \|y\|\) (`HasSolidNorm`). Balls about the origin are then solid (`LatticeOrderedAddCommGroup.isSolid_ball`). The real numbers, the rationals, the integers, and finite products \(\iota\to\mathbb R\) with the sup norm carry solid norms, and the order dual of a solid normed lattice is again solid (`Analysis/Normed/Order/Lattice.lean`).

If the group is also an ordered additive monoid, a solid norm makes the norm topology a topological lattice (`HasSolidNorm.toTopologicalLattice`). One has \(\||a|-|b|\|\le\|a-b\|\) (`norm_abs_sub_abs`); the supremum and the infimum are \(1\)-Lipschitz in each argument, and so are the positive and negative parts (`lipschitzWith_posPart`, `lipschitzWith_negPart`). The nonnegative cone is closed (`isClosed_nonneg`), and the order is closed (`HasSolidNorm.orderClosedTopology`). The module docstring speaks of a class `NormedLatticeAddCommGroup`; the class actually declared is the solid-norm axiom `HasSolidNorm`, used together with the separate lattice and normed-group structures. The references point to Meyer-Nieberg’s treatment of Banach lattices. Sources: `Analysis/Normed/Order/Lattice.lean`.

**Function-space instances.** Bounded continuous functions with values in a solid normed lattice also carry a solid sup norm (`Topology/ContinuousMap/Bounded/Normed.lean`, `BoundedContinuousFunction.instHasSolidNorm`). The Lebesgue spaces \(L^p(\mu;E)\), \(1\le p\le\infty\), with values in a solid normed lattice \(E\), are lattices under the almost-everywhere order, with \(\sup\), \(\inf\) and \(|\cdot|\) computed pointwise almost everywhere; their norm is solid, and the order is closed when the positive cone of \(E\) is closed (`MeasureTheory/Function/LpOrder.lean`, `MeasureTheory.Lp.instLattice`, `MeasureTheory.Lp.instHasSolidNorm`). Thus the standard function-space Banach lattices \(C_b\) and \(L^p\) exist as instances, even without a single bundled class named “Banach lattice”. Order continuity of the norm, KB spaces, and the characterizations of results 11–17 are not formalized.

**Synopsis entries.** Partly covered: 19.9 (the two norm inequalities and continuity of the lattice operations for solid norms; closures of sublattices and ideals are not treated). Not covered: 19.10–19.17.

## Order duality and positive operators

[Mathematical scope](SYNOPSIS19.md#order-duality-and-positive-operators).

### Mathlib

**Positive maps.** Positive linear maps between ordered modules are bundled as linear order homomorphisms (`PositiveLinearMap`, notation `E →ₚ[R] F`), with a continuous variant (`PositiveContinuousLinearMap`, notation `E →P[R] F`) (`Algebra/Order/Module/PositiveLinearMap.lean`, `Topology/Algebra/Module/ContinuousLinearMap/Positive.lean`). The order dual, regular operators, and the Riesz–Kantorovich formulas are not formalized.

**M. Riesz extension theorem.** If \(s\) is a pointed convex cone in a real vector space \(E\), \(f\) a linear functional on a subspace \(p\) nonnegative on \(p\cap s\), and for every \(y\in E\) some \(x\in p\) has \(x+y\in s\), then \(f\) extends to a linear functional on \(E\) nonnegative on \(s\) (`riesz_extension`). The hypothesis says exactly that \(p\) is majorizing for the order defined by \(s\). The Hahn–Banach dominated extension is deduced from it (`exists_extension_of_le_sublinear`). Source: `Analysis/Convex/Cone/Extension.lean`.

### TauCeti

The Koopman operator on almost-everywhere equivalence classes of measurable real functions is a positive operator: composition with a measure-preserving transformation is bundled as a real-linear operator, proved positive and monotone, shown to preserve multiplication and the constant one, and compatible with composition and iteration of the transformation; its fixed points are the classes of \(T\)-invariant functions (`TauCeti.Probability.koopmanMarkov`, `TauCeti.Probability.koopmanMarkov_nonneg`, `TauCeti.Probability.koopmanMarkov_eq_self_iff`; [Koopman–Markov operator](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Probability/Ergodic/KoopmanMarkov.lean)). It is an example of a positive lattice homomorphism on a function lattice, not part of an abstract theory.

**Synopsis entries.** Partly covered: 19.25 (scalar case \(F=\mathbb R\), the M. Riesz extension theorem). Not covered: 19.18–19.24, 19.26.

## Ordered vector spaces and cones

[Mathematical scope](SYNOPSIS19.md#ordered-vector-spaces-and-cones).

### Mathlib

Positive linear maps between \(C^\star\)-algebras are bounded (`PositiveLinearMap.exists_norm_apply_le`, `Analysis/CStarAlgebra/PositiveLinearMap.lean`), which is the automatic-continuity statement for that class of ordered Banach spaces; positive and completely positive maps of \(C^\star\)-algebras are recorded in Section 23. Proper cones and their inner duals in real inner-product spaces are in `Analysis/Convex/Cone/InnerDual.lean` (`ProperCone.innerDual`); normality and generation of cones and their duality are not formalized.

For the normed-lattice case of result 69, solid balls, closedness of the positive cone, and uniform (Lipschitz) continuity of the lattice operations for a solid norm are recorded under “Norms, order continuity, and monotone completeness” above.

**Synopsis entries.** Partly covered: 19.66 (positive linear maps between \(C^\star\)-algebras), 19.69 (solid-norm topologies only; general locally solid topologies and Riesz seminorms are not defined). Not covered: 19.64, 19.65, 19.67, 19.68.

## Representation and lattice functional calculus

[Mathematical scope](SYNOPSIS19.md#representation-and-lattice-functional-calculus).

### Mathlib

**Ideals of \(C(K)\).** For compact Hausdorff \(X\) and \(\mathbb K=\mathbb R\) or \(\mathbb C\), the closed ring ideals of \(C(X,\mathbb K)\) are exactly the ideals \(\{f:f|_F=0\}\) of closed sets \(F\) (`ContinuousMap.idealOfSet`, `ContinuousMap.idealOfSet_ofIdeal_isClosed`, and the Galois insertion `ContinuousMap.idealOpensGI` with open sets; `Topology/ContinuousMap/Ideals.lean`). These are ring ideals; the coincidence with closed lattice ideals is not stated. The \(L^p\) part of result 36 is not formalized.

**Conditional expectation.** For a sub-\(\sigma\)-algebra \(m\), the conditional expectation \(\mu[f\mid m]\) is monotone and positive (`MeasureTheory.condExp_mono`, `MeasureTheory.condExp_nonneg`), contractive on \(L^p\) for \(1\le p\le\infty\) (`MeasureTheory.eLpNorm_condExp_le_eLpNorm`, with `MeasureTheory.MemLp.condExp`), fixes constants on a finite measure (`MeasureTheory.condExp_const`) and \(m\)-measurable integrable functions (`MeasureTheory.condExp_of_stronglyMeasurable`), is idempotent (`MeasureTheory.condExp_condExp_of_le`), and preserves integrals (`MeasureTheory.integral_condExp`) (`MeasureTheory/Function/ConditionalExpectation/Basic.lean`, `MeasureTheory/Function/ConditionalExpectation/Real.lean`).

AM and AL spaces, Kakutani representation, the Krivine calculus, convexity and concavity of lattices, and lattice homomorphisms are not formalized. The Riesz–Markov–Kakutani representation of positive functionals on \(C_c(X)\) (Section 4) is the nearest supporting material for the measure dual of \(C(K)\) in result 31.

**Synopsis entries.** Covered: 19.37 (Mathlib). Partly covered: 19.36 (closed ring ideals of \(C(K)\); the \(L^p\) case is absent). Not covered: 19.27–19.35.

## Weak compactness and domination

[Mathematical scope](SYNOPSIS19.md#weak-compactness-and-domination).

**Synopsis entries.** Not covered: 19.38–19.45.

## Positive spectra and Perron–Frobenius theory

[Mathematical scope](SYNOPSIS19.md#positive-spectra-and-perronfrobenius-theory).

### Mathlib

For nonnegative square matrices, irreducibility (strong connectivity of the associated quiver) and primitivity are defined, with the path characterization of positive entries of powers, the characterization of irreducibility by positivity of some power entry, invariance of irreducibility under transposition, and the implication primitive \(\Rightarrow\) irreducible (`LinearAlgebra/Matrix/Irreducible/Defs.lean`, `Matrix.IsIrreducible`, `Matrix.IsPrimitive`, `Matrix.pow_apply_pos_iff_nonempty_path`, `Matrix.isIrreducible_iff_exists_pow_pos`, `Matrix.IsPrimitive.isIrreducible`). This is supporting material only: the Perron–Frobenius eigenvalue theorems, the period, and spectral statements for positive operators are not proved.

**Synopsis entries.** Not covered: 19.46–19.53, 19.70.

## Nonlinear Perron–Frobenius theory

[Mathematical scope](SYNOPSIS19.md#nonlinear-perronfrobenius-theory).

### TauCeti

**Hilbert's projective metric on the positive orthant.** For vectors \(x,y\in\mathbb R^\iota\) over a finite index type, Hilbert's projective metric is defined as \(\sup_{i,j}\log\bigl(x_iy_j/(y_ix_j)\bigr)\) (`TauCeti.hilbertProjectiveDist`). It is nonnegative, symmetric, satisfies the triangle inequality, and vanishes on strictly positive vectors exactly when they are positive multiples of each other (`TauCeti.hilbertProjectiveDist_triangle`, `TauCeti.hilbertProjectiveDist_comm`, `TauCeti.hilbertProjectiveDist_eq_zero_iff`); it is invariant under rescaling, diagonal scaling, and entrywise inversion.

**Birkhoff contraction for positive matrices.** For a matrix \(K\) with strictly positive entries, the projective diameter \(\Delta(K)=\sup\log\bigl(K_{ij}K_{i'j'}/(K_{ij'}K_{i'j})\bigr)\) is defined (`Matrix.projectiveDiameter`), images of nonnegative vectors lie within \(\Delta(K)\) of each other, \(\Delta(K)\le2\log(M/m)\) when the entries lie in \([m,M]\), and \(d_H(Kx,Ky)\le\tanh(\Delta(K)/4)\,d_H(x,y)\) for strictly positive \(x,y\) (`Matrix.hilbertProjectiveDist_mulVec_le`). The contraction is applied to the Sinkhorn iteration in `TauCeti/Data/Matrix/Sinkhorn/`. Sources: [Birkhoff contraction](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Data/Matrix/BirkhoffContraction.lean), [Sinkhorn rate](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/Data/Matrix/Sinkhorn/Rate.lean).

**Synopsis entries.** Partly covered: 19.71 (Hilbert's metric on the positive orthant of \(\mathbb R^n\): metric laws and zero set; Thompson's metric, completeness, and nonexpansiveness of general order-preserving homogeneous maps are absent), 19.72 (the contraction inequality with ratio \(\tanh(\Delta/4)\) for entrywise positive matrices on the orthant; the existence of an interior eigenvector and convergence of normalized iterates are not derived). Not covered: 19.73, 19.74.

## Positive semigroups and approximation

[Mathematical scope](SYNOPSIS19.md#positive-semigroups-and-approximation).

### Mathlib

For a positive continuous linear functional \(f\) on a unital \(C^\star\)-algebra, \(\|f\|=f(1)\) (`PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one`, `Analysis/CStarAlgebra/PositiveLinearFunctional.lean`); with \(A=C(K,\mathbb C)\) this is the scalar case of result 61.

### TauCeti

**Riesz–Thorin.** For a complex-linear operator from simple functions bounded \(L^{p_0}\to L^{q_0}\) and \(L^{p_1}\to L^{q_1}\), the interpolated bound \(\|Tf\|_q\le M_0^{1-\theta}M_1^\theta\|f\|_p\) holds for simple \(f\) (`TauCeti.eLpNorm_le_rpow_mul_rpow_mul_eLpNorm`, [Riesz–Thorin](https://github.com/TauCetiProject/TauCeti/blob/5cdecf40e99d5a5ad0833afff31f5b007d68a149/TauCeti/MeasureTheory/Integral/RieszThorin.lean)). This is the complex-scalar route to result 60; the real positive case is not derived.

**Synopsis entries.** Partly covered: 19.60 (complex-scalar Riesz–Thorin on simple functions, TauCeti), 19.61 (positive functionals on unital \(C^\star\)-algebras, Mathlib). Not covered: 19.56, 19.59, 19.63.
