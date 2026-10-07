# 21. Operator Theory: Bounded Operators, Spectra, and Model Theory

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. Some roots below are directory prefixes; the individual `.lean` files cited are the importable modules. The roots for this section are `Mathlib.Analysis.Normed.Operator`, `Mathlib.Analysis.InnerProductSpace.Spectrum`, `Mathlib.Analysis.InnerProductSpace.Rayleigh`, `Mathlib.Analysis.InnerProductSpace.SingularValues`, `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus`, and `Mathlib.Algebra.Module.LinearMap.Index`.

**Namespaces.** `ContinuousLinearMap`, `IsCompactOperator`, `SeparatingDual`, `LinearMap` with nested `IsSymmetric`, `IsSelfAdjoint`, `FredholmDecomposition`, `StarAlgebra.elemental`, `ContinuousMap`, and `ContinuousMapZero`.

This note records bounded and compact operators, the Fredholm alternative and the Fredholm index, the spectral theorem available for self-adjoint operators, and the continuous functional calculus. Further C⋆-algebra structure is section 23.

## Bounded operators

A continuous linear map between normed spaces carries the operator norm, and composition is submultiplicative (`Analysis/Normed/Operator/Basic.lean`). If the domain is a nontrivial normed space over a nontrivially normed field and has a separating dual, the space of continuous linear maps into a normed codomain is complete if and only if the codomain is complete (`Analysis/Normed/Operator/CompleteCodomain.lean`).

On a complete normed space over a nontrivially normed field, a continuous endomorphism is a unit of the operator algebra if and only if it is bijective. The spectrum of the operator as a Banach-algebra element therefore agrees with its spectrum as a linear endomorphism (`Analysis/Normed/Operator/Banach.lean`). The spectrum of an element of a Banach algebra is section 20. On a complete complex inner product space, the bounded endomorphisms form a C⋆-algebra (`Analysis/CStarAlgebra/ContinuousLinearMap.lean`).

## Compact operators

A map is a compact operator when the preimage of some compact set is a neighborhood of the origin. From a normed space into a Hausdorff topological vector space, this is equivalent to the closure of the image of a ball being compact. For linear maps between normed spaces over \(\mathbb{R}\) or \(\mathbb{C}\), compactness implies continuity. They form a submodule of the continuous linear maps, and the submodule is closed in the operator norm. Precomposition and postcomposition with a continuous linear map preserve compactness (`Analysis/Normed/Operator/Compact/Basic.lean`).

The identity is a compact operator if and only if the space is finite-dimensional, when the scalar field is complete and locally compact and the space is a Hausdorff topological vector space over that field (`Analysis/Normed/Operator/Compact/FiniteDimension.lean`).

If two continuous linear maps into a Hausdorff space differ by a finite-rank map, one is strict and has closed range if and only if the other is. This is Bourbaki’s finite-rank perturbation lemma (`Analysis/Normed/Operator/Perturbation/StrictByFinite.lean`).

## The Fredholm alternative

Let \(T\) be a compact endomorphism of a Banach space over a nontrivially normed field, and let \(\mu\neq 0\). Either \(\mu\) is an eigenvalue of \(T\), or \(\mu\) lies in the resolvent set. Equivalently, the nonzero eigenvalues are exactly the nonzero points of the spectrum. The preliminary statement that \(T-\mu\) is antilipschitz whenever \(\mu\neq 0\) is not an eigenvalue does not use completeness of the space. The field need not be \(\mathbb{R}\) or \(\mathbb{C}\) (`Analysis/Normed/Operator/Compact/FredholmAlternative.lean`).

## Fredholm operators and the index

Over a complete nontrivially normed field, a continuous linear map between Hausdorff topological vector spaces is Fredholm when it is strict, its range is closed and of finite codimension, and its kernel is finite-dimensional and topologically complemented. Four conditions are equivalent: that definition; the existence of a continuous quasi-inverse; the existence of an isomorphism between closed finite-codimension subspaces; and a Fredholm package, a topological splitting in which the operator is invertible on the essential summand and zero on a finite-dimensional complement. For maps between Banach or Fréchet spaces over \(\mathbb{R}\) or \(\mathbb{C}\), the file records that finite-dimensional kernel and cokernel ought to imply the remaining conditions, and that this implication is not yet proved (`Analysis/Normed/Operator/Fredholm/Basic.lean`).

The index is \(\operatorname{rank}\ker - \operatorname{rank}\operatorname{coker}\), an integer. If either rank is infinite, the formula does not carry a separate infinite value (`Algebra/Module/LinearMap/Index.lean`).

The set of Fredholm operators is open in the operator norm, and the index is locally constant on that set, when the scalar field and the domain are complete and the codomain is a normed space. The codomain is not required to be complete, although the module commentary describes the result as a theorem about two Banach spaces (`Analysis/Normed/Operator/Fredholm/Open.lean`).

## Self-adjoint operators

On an inner product space over \(\mathbb{R}\) or \(\mathbb{C}\), a symmetric linear endomorphism has real eigenvalues, its eigenspaces are mutually orthogonal, and the orthogonal complement of the sum of the eigenspaces is invariant and contains no eigenvector (`Analysis/InnerProductSpace/Spectrum.lean`).

In finite dimension that orthogonal complement is zero. The operator is orthogonally equivalent to a diagonal operator on the orthogonal sum of its eigenspaces, and the space has an orthonormal basis of eigenvectors whose eigenvalues are listed in decreasing order.

On a complete inner product space, a compact self-adjoint operator has the same conclusion for the orthogonal complement: it is zero. Each nonzero eigenspace is finite-dimensional. The file calls this the spectral theorem for compact self-adjoint operators, and it records the spectral theory of a general bounded self-adjoint operator as future work (`Analysis/InnerProductSpace/Spectrum.lean`).

For a self-adjoint continuous operator on a complete inner product space, the spectral radius equals the operator norm (`Analysis/InnerProductSpace/Rayleigh.lean`).

## Continuous functional calculus

Let \(a\) be a normal element of a unital complex C⋆-algebra. The continuous functional calculus is a star-algebra equivalence from the continuous complex functions on the spectrum of \(a\) onto the unital C⋆-subalgebra generated by \(a\). It sends the restricted identity function to \(a\), and therefore extends the polynomial calculus. A star-algebra equivalence of C⋆-algebras is an isometry, so the calculus is isometric (`Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Basic.lean`).

Uniqueness is Stone–Weierstrass. On a compact subset of \(\mathbb{R}\) or of \(\mathbb{C}\), a continuous star-algebra homomorphism out of the continuous functions is determined by its value on the identity function. The same uniqueness holds for the non-unital calculus, and for nonnegative scalars when the target is an \(\mathbb{R}\)-algebra (`Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unique.lean`).

The generic calculus is instantiated for normal elements of a unital complex C⋆-algebra, for normal elements of a non-unital complex C⋆-algebra by passage through the unitization, and for self-adjoint elements by restriction of scalars along the real part (`Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Basic.lean`, `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Instances.lean`). The order, positivity, and the rest of the C⋆-package that use this calculus are section 23.

## Reproducing kernel Hilbert spaces

Reproducing kernel Hilbert spaces, the setting of Paulsen–Raghupathi and Agler–McCarthy, are defined for vector-valued functions: point evaluations are continuous, the kernel is positive semidefinite and its kernel functions are dense, and every positive semidefinite kernel determines such a space (`Analysis/InnerProductSpace/Reproducing.lean`). Multipliers, Pick interpolation, and operators on specific kernel spaces were not found; Section 42 treats the function spaces.

## Singular values

On finite-dimensional inner product spaces over \(\mathbb{R}\) or \(\mathbb{C}\), the singular values of a linear map \(T\) are the square roots of the eigenvalues of \(T^\ast\circ T\), arranged in decreasing order and repeated by multiplicity. The sequence is indexed by the nonnegative integers and is finitely supported. Its support is the initial segment of length equal to the rank of \(T\): the first \(\operatorname{rank}(T)\) singular values are positive, and the rest are zero (`Analysis/InnerProductSpace/SingularValues.lean`).

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

The additions include the Banach-space Fredholm criterion from finite-dimensional kernel and cokernel, the Hilbert-space adjoint closed-range theorem, and invariance of index under compact perturbations. Openness of the Fredholm locus and local constancy of the index are already in Mathlib, as recorded above; TauCeti restates them in \(\varepsilon\)-form ([Fredholm criterion](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Fredholm/ClosedRange.lean), [adjoints](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Fredholm/Adjoint.lean), [compact perturbations](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Fredholm/CompactPerturbation.lean)). For compact \(K\), TauCeti proves finite-dimensionality of the kernel and cokernel of \(I-K\), together with closedness of its range ([Riesz theory](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Normed/Operator/Compact/RieszTheory.lean)).

A self-adjoint Fredholm operator on a Hilbert space has index zero, and more generally so does any Fredholm operator with the same kernel as its adjoint ([self-adjoint Fredholm](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Fredholm/SelfAdjoint.lean)). The compact self-adjoint spectral theorem is repackaged as the existence of a Hilbert basis of eigenvectors ([eigenbasis](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/InnerProductSpace/Spectrum.lean)); in Mathlib the conclusion is stated as the vanishing of the orthogonal complement of the eigenspaces.

Stone's theorem is available in the unbounded-operator development of Section 22. This should not be confused with a projection-valued spectral-measure construction for arbitrary bounded normal operators, which was not located.

## Topics of Section 21 not found in either inspected library

- Approximation of a compact operator on a Hilbert space by finite-rank operators. Approximation numbers, proposed as the infinite-dimensional extension of singular values, are marked as future work.
- Hilbert–Schmidt operators and Schatten classes.
- The spectral theorem for a general bounded self-adjoint or normal operator.
- A projection-valued measure, or a spectral measure, for a general normal operator. The continuous functional calculus supplies a star-isometric map from \(C(\sigma(a))\). This note does not treat that map as a spectral measure.
- The essential spectrum, Weyl's theorem on its stability, and the Calkin algebra.
- Toeplitz and Hankel operators, the unilateral shift and Beurling's invariant-subspace theorem, the Wold decomposition, von Neumann's inequality, subnormal operators, and the invariant-subspace results of Lomonosov type.
- The model theory of contractions, the characteristic function of a contraction, and the Sz.-Nagy dilation.
- The deduction, recorded as a comment in the Rayleigh file, of the equality of spectral radius and norm from the corresponding C⋆-identity by complexification. The equality itself is proved directly.
- The finite-kernel/cokernel criterion for Fredholmness on general Fréchet spaces. The Banach-space criterion is proved in TauCeti.
