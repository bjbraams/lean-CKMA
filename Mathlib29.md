# 29. Wavelets, Frames, Time–Frequency Analysis, and Sampling

Checked against Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (2026-09-16, Lean `v4.35.0-rc2`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. Some roots below are directory prefixes; the individual `.lean` files cited are the importable modules. The roots for this section are `Mathlib.Analysis.InnerProductSpace.Reproducing` and `Mathlib.Analysis.InnerProductSpace.Reproducing.Operations`.

**Namespaces.** The reproducing-kernel theory is `RKHS`, with the kernel construction in `RKHS.OfKernel` and the sum of kernels in `RKHS.Add'`.

This note records reproducing-kernel Hilbert spaces. Wavelets, Gabor analysis, and the sampling theorem were not found.

## Reproducing-kernel Hilbert spaces

A reproducing-kernel Hilbert space on a set \(X\), with values in a Hilbert space \(V\) over \(\mathbb{R}\) or \(\mathbb{C}\), is a Hilbert space \(H\) of functions \(X\to V\) in the following sense: the inclusion of \(H\) into the space of all functions is an injective continuous linear map. Point evaluation is then continuous (`Analysis/InnerProductSpace/Reproducing.lean`).

The kernel function at \(x\in X\) is the adjoint of evaluation at \(x\), a continuous linear map \(V\to H\). The kernel is the matrix of operators \(V\to V\) whose \((x,y)\)-entry is the composite of the kernel function at \(y\) with the adjoint of the kernel function at \(x\). The reproducing identity is
\[
\langle k_x v,\, f\rangle_H=\langle v,\, f(x)\rangle_V.
\]
Evaluation is bounded by the diagonal of the kernel, \(\|f(x)\|\leq\|f\|\sqrt{\|K(x,x)\|}\). If the kernel functions are uniformly bounded on a set, norm convergence in \(H\) implies uniform convergence of the functions on that set. The linear span of the kernel functions is dense. The kernel is a positive semidefinite, Hermitian matrix of operators.

Moore’s theorem, in the form proved here: every positive semidefinite matrix \(K\) of continuous linear maps \(V\to V\), indexed by \(X\times X\), is the kernel of a reproducing-kernel Hilbert space. The space is the completion of the finitely supported functions \(X\times V\to\mathbb{k}\) for the seminorm coming from \(K\), and the kernel of this space is exactly \(K\). If two such spaces have the same kernel, they are linearly isometric by an isometry that matches kernel functions with kernel functions.

A closed subspace of a reproducing-kernel Hilbert space, with the restricted inclusion, is again a reproducing-kernel Hilbert space. Its kernel functions are the orthogonal projections of the original kernel functions, and its kernel is obtained by inserting the corresponding orthogonal projection. A function \(f:X\to V\) determines a rank-one positive semidefinite kernel with entries \(\langle f(y),\cdot\rangle f(x)\).

The sum of two kernels is treated in `Analysis/InnerProductSpace/Reproducing/Operations.lean`. The reproducing-kernel space of \(K+K'\) is isometrically isomorphic to a quotient of the product of the spaces of \(K\) and of \(K'\), by the relation that identifies pairs of functions with the same sum as functions on \(X\).

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6e53de0d3ce9`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

TauCeti adds a concrete orthogonal decomposition relevant to time–frequency analysis: the normalized Hermite functions form a Hilbert basis of \(L^2(\mathbb R)\), with Fourier eigenfunction identities and a corresponding complex \(L^2\) basis ([Hermite basis](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/SpecialFunctions/Hermite/Function/HilbertBasis.lean), [Fourier basis description](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Fourier/HilbertBasis.lean)). This is an orthonormal basis, not a Gabor-frame or sampling theorem.

For scalar positive-definite kernels it packages a minimal Kolmogorov Hilbert-space realization and its universal isometry, using Mathlib's RKHS construction ([kernel realization](https://github.com/TauCetiProject/TauCeti/blob/6e53de0d3ce9ea24d7d487e656ac4590b0c45b3a/TauCeti/Analysis/PositiveDefinite/Kernel/Kolmogorov.lean)). No wavelet, frame-bound, or Shannon sampling theorem was located.

## Topics of Section 29 not found in either inspected library

- Wavelets, multiresolution analyses, and wavelet bases.
- The short-time Fourier transform, Gabor frames, and time–frequency analysis.
- The Shannon, Nyquist, and Whittaker–Kotelnikov–Shannon sampling theorems.
- Frames of a Hilbert space, frame operators, and frame bounds. The word “frame” occurs elsewhere for an order-theoretic frame and for a local frame of a vector bundle; neither is a Hilbert-space frame.
- Sampling expansions and band-limited functions, beyond the Fourier analysis of the circle and of Euclidean space recorded in Sections 27 and 28.

Reproducing-kernel Hilbert spaces and the Hermite orthogonal bases are neighbouring formalized theories; neither supplies the missing wavelet, general-frame, or sampling theorems.
