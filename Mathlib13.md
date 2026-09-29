# 13. Matrix Analysis, Operator Monotonicity, and Noncommutative Inequalities

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. Some roots below are directory prefixes; the individual `.lean` files cited are the importable modules. The roots for this section are `Mathlib.Analysis.InnerProductSpace.SingularValues`, `Mathlib.Analysis.InnerProductSpace.Positive`, `Mathlib.Analysis.Matrix.Order`, `Mathlib.Analysis.CStarAlgebra.Matrix`, `Mathlib.Analysis.CStarAlgebra.CStarMatrix`, `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order`, `Mathlib.Analysis.CStarAlgebra.ApproximateUnit`, and the order files under `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus`.

**Namespaces.** Singular values and the Loewner order on algebraic operators are `LinearMap`. The Loewner order on bounded operators and the star-ordered ring of operators on a complex Hilbert space are `ContinuousLinearMap`. Powers, logarithms, and positive parts through the functional calculus are `CFC`. Norm comparisons, inverses, and integer powers are `CStarAlgebra`. Matrices over a C⋆-algebra are `CStarMatrix`. The matrix order is `Matrix`, installed by opening the scope `MatrixOrder`; the \(\ell^2\) operator norm is the scope `Matrix.Norms.L2Operator`.

This note records the Loewner order, singular values of finite-dimensional maps, and the operator inequalities proved through the continuous functional calculus. The general theory of C⋆-algebras is Section 23. Birkhoff’s theorem on doubly stochastic matrices is stated in Section 11.

## The Loewner order

On a Hilbert space over \(\mathbb{R}\) or \(\mathbb{C}\), a linear endomorphism is positive when it is symmetric and \(\operatorname{re}\langle Tx,x\rangle\ge 0\) for every vector \(x\). In finite dimension a positive algebraic endomorphism is self-adjoint. A bounded endomorphism is positive under the same symmetry and quadratic-form hypotheses; on a complete space this is equivalent to self-adjointness together with the quadratic-form bound. The Loewner order is \(f\le g\) if and only if \(g-f\) is positive. The same definition is given for bounded operators (`Analysis/InnerProductSpace/Positive.lean`).

Bounded operators on a complex Hilbert space, with this order, form a star-ordered ring, and a nonnegative operator has nonnegative real spectrum (`Analysis/InnerProductSpace/StarOrder.lean`). The operator-monotone functions below are monotone in this order.

For square matrices over \(\mathbb{R}\) or \(\mathbb{C}\), a matrix is positive semidefinite when it is Hermitian and \(x^*Mx\ge 0\) for every finitely supported vector \(x\). The scoped matrix order declares \(A\le B\) when \(B-A\) is positive semidefinite. The positive-semidefinite matrices are closed in the usual topology on matrix entries. When the index is finite, a nonnegative matrix has nonnegative real spectrum and the matrices form a star-ordered ring, so the functional calculus applies to them (`LinearAlgebra/Matrix/PosDef.lean`, `Analysis/Matrix/Order.lean`). A diagonal matrix is positive semidefinite if and only if its diagonal is nonnegative.

The Kronecker product of two positive-semidefinite matrices is positive semidefinite. So is their entrywise (Hadamard) product: this is the Schur product theorem (`Analysis/Matrix/Order.lean`, `Matrix.PosSemidef.kronecker`, `Matrix.PosSemidef.hadamard`).

## Singular values

For a linear map \(T\) between finite-dimensional inner product spaces over \(\mathbb{R}\) or \(\mathbb{C}\), the singular values are the square roots of the eigenvalues of \(T^*T\), arranged in decreasing order and repeated by multiplicity, then extended by zeros. The sequence is indexed by \(\mathbb{N}\), starting at \(0\), and only finitely many terms are nonzero. They are nonnegative and antitone. The support is exactly the initial segment of length \(\operatorname{rank} T\): the \(n\)th singular value is positive if and only if \(n<\operatorname{rank} T\), and the singular-value sequence vanishes if and only if \(T\) does. The map is injective if and only if every singular value before the dimension of the domain is positive (`Analysis/InnerProductSpace/SingularValues.lean`). Approximation numbers for maps between infinite-dimensional spaces are a TODO, and no von Neumann or Schatten comparison of singular values is proved.

## Matrices as C⋆-algebras

`CStarMatrix m n A` is a type copy of the matrices with entries in a C⋆-algebra \(A\). The operator norm coming from the action on \(C^\star\)-valued functions of the columns makes the square matrices a non-unital C⋆-algebra when \(A\) is non-unital, and a unital C⋆-algebra when \(A\) is unital (`Analysis/CStarAlgebra/CStarMatrix.lean`).

Complex square matrices, with the \(\ell^2\) operator norm obtained by identifying a matrix with an endomorphism of Euclidean space, form a C⋆-algebra. The norm and the C⋆-identity are scoped so that they do not choose a global norm on all matrices. Every entry of a unitary matrix has norm at most \(1\) (`Analysis/CStarAlgebra/Matrix.lean`). A real doubly stochastic matrix has \(\ell^2\) operator norm at most \(1\), by the argument in Section 11.

## Positive and negative parts, exponential, and logarithm

In a non-unital algebra with the non-unital real continuous functional calculus on self-adjoint elements, the positive and negative parts of an element are the functional calculi of the real positive and negative parts. For a self-adjoint element, \(a^+-a^-=a\) and \(a^+a^-=a^-a^+=0\). In the presence of the star order, \(a\le a^+\) and \(-a^-\le a\). If the nonnegative elements are exactly those with nonnegative real spectrum, then \(a^+=a\) if and only if \(0\le a\), and \(a^-=0\) under the same condition. In a Hausdorff semitopological ring, the decomposition is unique: if \(a=b-c\) with \(b,c\ge 0\) and \(bc=0\), then \(b=a^+\) and \(c=a^-\) (`Analysis/SpecialFunctions/ContinuousFunctionalCalculus/PosPart/Basic.lean`).

On a real normed algebra with the real functional calculus, the exponential of a self-adjoint element is nonnegative for the star order, and \(\log(\exp a)=a\). If \(a\) is strictly positive and the nonnegative elements have nonnegative spectrum, then \(\exp(\log a)=a\). The exponential and logarithm are inverses in that sense (`Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Basic.lean`).

## Operator monotonicity and operator concavity

Throughout this section the order is the star order: the nonnegative elements are those of the form \(b^*b\), arranged so that the Loewner order on operators and the positive-semidefinite order on matrices are instances.

On a non-unital C⋆-algebra, \(a\mapsto a^p\) is monotone for every real exponent \(p\in[0,1]\), the square root is monotone, and both are concave on the positive cone. On a unital C⋆-algebra the real powers \(a\mapsto a^p\) for \(p\in[0,1]\) are monotone and concave on the positive cone (`Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Order.lean`). The file leaves unproved the operator antitonicity and operator convexity of these powers on \((-1,0]\), and the operator convexity on \([1,2]\).

On a unital C⋆-algebra the logarithm is monotone and concave on the strictly positive elements (`Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Order.lean`). Operator convexity of \(x\log x\) is a TODO.

On a non-unital C⋆-algebra, \(x\mapsto 1-(1+x)^{-1}\) is monotone on the positive cone, both for the nonnegative calculus and for the real calculus (`Analysis/CStarAlgebra/ApproximateUnit.lean`).

On a unital C⋆-algebra, a self-adjoint element satisfies \(-\|a\|\cdot 1\le a\le\|a\|\cdot 1\), and both \(a a^*\) and \(a^* a\) are at most \(\|a\|^2\cdot 1\). For nonnegative \(a\) in a nontrivial algebra, \(\|a\|\) lies in the real spectrum, and \(\|a\|\le r\) for \(r\ge 0\) if and only if \(a\) is at most the scalar \(r\). In particular \(\|a\|\le 1\) if and only if \(a\le 1\). If \(0\le a\le b\), then \(\|a\|\le\|b\|\). If \(a\) is strictly positive and \(a\le b\), then \(b\) is invertible. For nonnegative invertible elements, \(0\le a\le b\) implies \(b^{-1}\le a^{-1}\), and the real powers of exponent \(-1\) satisfy the same reverse comparison. Inversion is antitone, and operator convex, on the strictly positive elements. For nonnegative \(a\) and strictly positive \(b\),
\[
a\le b\quad\text{if and only if}\quad\bigl\|\sqrt{a}\,b^{-1/2}\bigr\|\le 1
\]
(`Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean`, `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/RingInverseOrder.lean`).

If \(0\le e\) and \(\|e\|\le 1\), then \(e^n\le e^m\) whenever \(0<m\le n\) in \(\mathbb{R}_{\ge 0}\), and in particular \(e^2\le e\le\sqrt{e}\). On a unital C⋆-algebra, \(0\le a\) implies \(0\le a^n\) for every natural number \(n\); if \(1\le a\) then \(n\mapsto a^n\) is monotone, and if \(0\le a\le 1\) then \(n\mapsto a^n\) is antitone.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

TauCeti constructs the geometric mean
\[
 a\#b=a^{1/2}(a^{-1/2}ba^{-1/2})^{1/2}a^{1/2}
\]
for strictly positive \(a\) and nonnegative \(b\) in the continuous-functional-calculus setting. It characterizes this as the unique nonnegative solution of \(xa^{-1}x=b\), and proves symmetry and inversion identities under strict positivity, together with the operator arithmetic–geometric mean inequality ([functional-calculus construction](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/GeometricMean.lean)).

For positive-definite \(S\) and positive-semidefinite \(T\), it consequently constructs the unique positive-semidefinite solution of \(ASA=T\), namely \(S^{-1}\#T\); the matrix file gives the square-root formula and congruence identity ([matrix specialization](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/Matrix/GeometricMean.lean)). This adds a concrete matrix mean, not Löwner's characterization theorem or a Schatten-norm theory.

## Topics of Section 13 not found in either inspected library

- Löwner’s theorem characterizing operator-monotone functions. The Loewner order is defined, and the functions listed above are proved monotone or concave in that order.
- The Golden–Thompson inequality and the Lieb–Thirring inequality.
- The von Neumann trace inequality and Schatten norms. Singular values of finite-dimensional maps are defined; their trace and norm inequalities are not.
- Operator convexity of \(x\log x\), operator antitonicity and operator convexity of real powers on \((-1,0]\), and operator convexity of real powers on \([1,2]\). Each is a TODO.
- Approximation numbers in infinite dimension. They are a TODO in `Analysis/InnerProductSpace/SingularValues.lean`.
- Schur–Horn, and the majorization form of Birkhoff’s theorem. Both are discussed in Section 11.
