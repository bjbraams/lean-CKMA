# 29. Wavelets, Frames, Time–Frequency Analysis, and Sampling

Checked against Mathlib commit `f039e1b8a616d45782a5c7fc5e7909249c36b8ea` (2026-10-18, Lean `v4.36.0-rc1`). The checkout was only read. The survey below concerns this Mathlib revision; the TauCeti supplement and final gap list also use the [TauCeti source audit](TauCetiCoverage.md).

**Imports.** There is no aggregate module. A file `Mathlib/A/B/C.lean` is imported as `import Mathlib.A.B.C`. Some roots below are directory prefixes; the individual `.lean` files cited are the importable modules. The roots for this section are `Mathlib.Analysis.InnerProductSpace.Reproducing`, `Mathlib.Analysis.InnerProductSpace.Reproducing.Operations`, `Mathlib.Analysis.Normed.Module.Bases`, `Mathlib.Analysis.InnerProductSpace.l2Space`, and `Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc`.

**Namespaces.** The reproducing-kernel theory is `RKHS`, with the kernel construction in `RKHS.OfKernel` and the sum of kernels in `RKHS.Add'`. Bases in normed spaces are `GeneralSchauderBasis`, with the abbreviations `SchauderBasis` and `UnconditionalSchauderBasis`; the sinc function is `Real.sinc`.

This note records reproducing-kernel Hilbert spaces, Schauder bases, and the sinc function. Wavelets, frames, Gabor analysis, and the sampling theorem were not found.

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

## Schauder bases and the sinc function

`Analysis/Normed/Module/Bases.lean` defines a generalized Schauder basis of a normed space \(X\), indexed by a type \(\beta\) and a summation filter: a family \(b_i\) with continuous coordinate functionals \(b_i^*\) such that \(b_i^*(b_j)=\delta_{ij}\) and \(x=\sum_ib_i^*(x)b_i\) along the filter. The classical Schauder basis (`SchauderBasis`) uses partial sums along \(\mathbb N\), and the unconditional basis (`UnconditionalSchauderBasis`) uses the net of finite subsets. The finite coordinate projections \(P_A\) satisfy \(P_AP_B=P_{A\cap B}\), have range the span of \(\{b_i:i\in A\}\), and converge strongly to the identity. In a Banach space they are uniformly bounded (the basis constant, by Banach–Steinhaus). Conversely, projections \(P_n\) of rank \(n\) with \(P_0=0\), \(P_nP_m=P_{\min(n,m)}\) and \(P_n\to I\) strongly yield a Schauder basis (`RankOneDecomposition.basis`). In `Analysis/InnerProductSpace/l2Space.lean`, a Hilbert basis is an unconditional Schauder basis with coordinates \(x\mapsto\langle b_i,x\rangle\) (`HilbertBasis.toUnconditionalSchauderBasis`, and `HilbertBasis.toSchauderBasis` for index \(\mathbb N\)). Frames, Riesz bases, and bases of exponentials or wavelets are not treated.

`Real.sinc` is defined as \(\sin x/x\) with value \(1\) at \(0\) (`Analysis/SpecialFunctions/Trigonometric/Sinc.lean`), with continuity, evenness, and the bounds \(|\operatorname{sinc}x|\le1\) and \(\sin x/x\le|x|^{-1}\). No interpolation series of sinc translates is formalized.

## Additional coverage in TauCeti

The following additions were checked in TauCeti revision `6ebb29f84b4d`; see the [revision, build evidence, and comparison scope](TauCetiCoverage.md). Source links below are pinned to that revision.

TauCeti adds a concrete orthogonal decomposition relevant to time–frequency analysis: the normalized Hermite functions form a Hilbert basis of \(L^2(\mathbb R)\), with Fourier eigenfunction identities and a corresponding complex \(L^2\) basis ([Hermite basis](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/SpecialFunctions/Hermite/Function/HilbertBasis.lean), [Fourier basis description](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Fourier/HilbertBasis.lean)). This is an orthonormal basis, not a Gabor-frame or sampling theorem.

For scalar positive-definite kernels it packages a minimal Kolmogorov Hilbert-space realization and its universal isometry, using Mathlib's RKHS construction ([kernel realization](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/PositiveDefinite/Kernel/Kolmogorov.lean)). No wavelet, frame-bound, or Shannon sampling theorem was located.

TauCeti develops finite frames in an inner product space ([finite frames](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/InnerProductSpace/Frame.lean)). For a finite family \((v_i)\), the analysis map \(x\mapsto(\langle v_i,x\rangle)_i\) and the synthesis map \(a\mapsto\sum_ia_iv_i\) are mutually adjoint; the frame operator \(S=\sum_i\langle v_i,\cdot\rangle v_i\) and the Gram operator are positive, an orthonormal basis has \(S=I\), and for finite-dimensional \(E\) the sorted spectra of \(S\) and of the Gram operator agree through the smaller dimension. A lower frame bound \(a\|x\|^2\le\sum_i|\langle v_i,x\rangle|^2\) holds for all \(x\) exactly when the Gram eigenvalues below \(\dim E\) are at least \(a\), provided the family has at least \(\dim E\) members (`TauCeti.le_eigenvalues_gramOperator`, `TauCeti.mul_norm_sq_le_sum_norm_inner_sq_of_le_eigenvalues_gramOperator`). Infinite frames, the dual frame \(S^{-1}v_i\), and frame reconstruction are absent.

On top of Mathlib's Schauder bases, TauCeti proves the principle of small perturbations: if \(b\) is a generalized Schauder basis of a Banach space and \(\delta=\sum_i\|b_i^*\|\,\|b_i-c_i\|<1\), then a bounded linear equivalence of norm at most \(1+\delta\), with inverse of norm at most \((1-\delta)^{-1}\), maps \(b_i\) to \(c_i\), so \((c_i)\) is a basis with the same summation filter ([perturbation](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Normed/Module/Bases/Perturbation.lean)). It also treats transport of bases ([transport](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Normed/Module/Bases/Map.lean)), subsequences as bases of their closed span ([subsequences](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Normed/Module/Bases/Subsequence.lean)), monotone renorming ([renorming](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Normed/Module/Bases/Monotone.lean)), the dual basic sequence ([duality](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Normed/Module/Bases/Dual.lean)), James's characterization of reflexivity by shrinking and boundedly complete bases ([reflexivity](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Normed/Module/Bases/Reflexive.lean)), and the bounded approximation property of spaces with a basis ([approximation](https://github.com/TauCetiProject/TauCeti/blob/6ebb29f84b4d6e2019233da0718776a6e32e1526/TauCeti/Analysis/Normed/Module/Bases/Approximation.lean)). These are abstract results; no system of exponentials, Haar functions, or wavelets is shown to be a basis, and Kadec's quarter theorem is not derived.

## Topics of Section 29 not found in either inspected library

- Wavelets, multiresolution analyses, wavelet bases, and compactly supported (Daubechies) wavelets.
- The short-time Fourier transform and its orthogonality relations, Gabor frames, density obstructions, and the Balian–Low theorem.
- The Shannon, Nyquist, and Whittaker–Kotelnikov–Shannon sampling theorems.
- Infinite frames of a Hilbert space, the frame-operator invertibility criterion, and canonical dual frames; TauCeti covers only finite families (frame and Gram operators, lower frame bounds via the Gram spectrum). The word “frame” occurs elsewhere for an order-theoretic frame and for a local frame of a vector bundle; neither is a Hilbert-space frame.
- Riesz bases and nonharmonic Fourier series, including Kadec's quarter theorem (only the abstract small-perturbation principle for Schauder bases is present), and Landau's necessary density conditions; the Haar and Walsh systems, and wavelets, as unconditional bases of \(L^p\).
- Compressive sensing: the restricted isometry property and sparse recovery guarantees.
- Sampling expansions and band-limited (Paley–Wiener) functions, beyond `Real.sinc` and the Fourier analysis of the circle and of Euclidean space recorded in Sections 27 and 28.

Reproducing-kernel Hilbert spaces, Schauder bases, finite frames, and the Hermite orthogonal bases are neighbouring formalized theories; none supplies the missing wavelet, general-frame, or sampling theorems.
